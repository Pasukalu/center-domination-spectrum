import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic.DeriveFintype
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Graph centers are defined through closed metric balls. The bridge to mathlib's
shortest-path distance holds for arbitrary connected graphs. -/
namespace CenterDomination

variable {V : Type*}

/-- A walk of at most the specified length, expressed in single-edge steps. -/
def Within (G : SimpleGraph V) : ℕ → V → V → Prop
  | 0, x, y => x = y
  | n + 1, x, y => Within G n x y ∨ ∃ z, G.Adj x z ∧ Within G n z y

theorem within_iff_walk (G : SimpleGraph V) (n : ℕ) (x y : V) :
    Within G n x y ↔ ∃ w : G.Walk x y, w.length ≤ n := by
  induction n generalizing x y with
  | zero =>
    constructor
    · intro h
      change x = y at h
      subst y
      exact ⟨.nil, by simp⟩
    · rintro ⟨w, hw⟩
      cases w with
      | nil => rfl
      | cons e w => simp at hw
  | succ n ih =>
    change (Within G n x y ∨ ∃ z, G.Adj x z ∧ Within G n z y) ↔ _
    constructor
    · rintro (h | ⟨z, e, h⟩)
      · obtain ⟨w, hw⟩ := (ih x y).1 h
        exact ⟨w, by omega⟩
      · obtain ⟨w, hw⟩ := (ih z y).1 h
        exact ⟨.cons e w, by simpa using hw⟩
    · rintro ⟨w, hw⟩
      cases w with
      | nil => exact Or.inl ((ih _ _).2 ⟨.nil, by simp⟩)
      | cons e w =>
        exact Or.inr ⟨_, e, (ih _ _).2 ⟨w, by simpa using hw⟩⟩

theorem within_iff_dist {G : SimpleGraph V} (hc : G.Connected) (n : ℕ) (x y : V) :
    Within G n x y ↔ G.dist x y ≤ n := by
  rw [within_iff_walk]
  constructor
  · rintro ⟨w, hw⟩
    exact (SimpleGraph.dist_le w).trans hw
  · intro h
    obtain ⟨w, hw⟩ := hc.exists_walk_length_eq_dist x y
    exact ⟨w, hw ▸ h⟩

def Covers (G : SimpleGraph V) (r : ℕ) (x : V) := ∀ y, Within G r x y
def Central (G : SimpleGraph V) (x : V) :=
  ∀ r, (∃ w, Covers G r w) → Covers G r x

theorem central_iff_metric {G : SimpleGraph V} (hc : G.Connected) (x : V) :
    Central G x ↔ ∀ r, (∃ w, ∀ y, G.dist w y ≤ r) → ∀ y, G.dist x y ≤ r := by
  simp only [Central, Covers, within_iff_dist hc]

def DomEdge (G : SimpleGraph V) (u v : V) :=
  G.Adj u v ∧ ∀ z, G.Adj u z ∨ G.Adj v z

def Short (G : SimpleGraph V) (x y : V) :=
  x = y ∨ G.Adj x y ∨ ∃ z, G.Adj x z ∧ G.Adj z y

theorem within_one {G : SimpleGraph V} {x y : V} :
    Within G 1 x y ↔ x = y ∨ G.Adj x y := by simp [Within]

theorem within_two {G : SimpleGraph V} {x y : V} :
    Within G 2 x y ↔ Short G x y := by
  change ((Within G 1 x y) ∨ ∃ z, G.Adj x z ∧ Within G 1 z y) ↔ _
  simp only [within_one, Short]
  constructor
  · rintro ((h | h) | ⟨z, hx, hz | hz⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · subst z
      exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr ⟨z, hx, hz⟩)
  · rintro (h | h | ⟨z, hx, hy⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨z, hx, Or.inr hy⟩

theorem short_symm {G : SimpleGraph V} {x y : V} (h : Short G x y) : Short G y x := by
  rcases h with h | h | ⟨z, hx, hy⟩
  · exact Or.inl h.symm
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr ⟨z, hy.symm, hx.symm⟩)

theorem covers_mono {G : SimpleGraph V} {x : V} {s t : ℕ}
    (hs : Covers G s x) (hst : s ≤ t) : Covers G t x := by
  intro y
  obtain ⟨w, hw⟩ := (within_iff_walk G s x y).1 (hs y)
  exact (within_iff_walk G t x y).2 ⟨w, hw.trans hst⟩

theorem central_of_two {G : SimpleGraph V} {x : V} (h2 : Covers G 2 x)
    (h1 : ¬ ∃ w, Covers G 1 w) : Central G x := by
  intro r hex
  by_cases h : 2 ≤ r
  · exact covers_mono h2 h
  · obtain ⟨w, hw⟩ := hex
    exact False.elim (h1 ⟨w, covers_mono hw (by omega)⟩)

theorem short_of_one {G : SimpleGraph V} {w : V} (h : Covers G 1 w) (x y : V) :
    Short G x y := by
  rcases within_one.1 (h x) with hx | hx
  · subst x
    rcases within_one.1 (h y) with hy | hy
    · exact Or.inl hy
    · exact Or.inr (Or.inl hy)
  · rcases within_one.1 (h y) with hy | hy
    · subst y
      exact Or.inr (Or.inl hx.symm)
    · exact Or.inr (Or.inr ⟨w, hx.symm, hy⟩)

theorem endpoints_cover_two {G : SimpleGraph V} {u v : V} (h : DomEdge G u v) :
    Covers G 2 u ∧ Covers G 2 v := by
  constructor
  · intro z
    apply within_two.2
    rcases h.2 z with e | e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr ⟨v, h.1, e⟩)
  · intro z
    apply within_two.2
    rcases h.2 z with e | e
    · exact Or.inr (Or.inr ⟨u, h.1.symm, e⟩)
    · exact Or.inr (Or.inl e)

/-- A center with at least two vertices inherits a dominating edge. -/
theorem center_dominating_edge {G : SimpleGraph V} {u v a b : V}
    (h : DomEdge G u v) (ha : Central G a) (hb : Central G b) (hab : a ≠ b) :
    ∃ p q, Central G p ∧ Central G q ∧ G.Adj p q ∧
      ∀ x, Central G x → G.Adj p x ∨ G.Adj q x := by
  by_cases h1 : ∃ w, Covers G 1 w
  · have ac := ha 1 h1
    have ab : G.Adj a b := (within_one.1 (ac b)).resolve_left hab
    refine ⟨a, b, ha, hb, ab, ?_⟩
    intro x _
    rcases within_one.1 (ac x) with e | e
    · subst x
      exact Or.inr ab.symm
    · exact Or.inl e
  · obtain ⟨hu, hv⟩ := endpoints_cover_two h
    exact ⟨u, v, central_of_two hu h1, central_of_two hv h1, h.1, fun x _ => h.2 x⟩

/-- The four new vertices are the helpers P,Q and guards A,B of the paper. -/
inductive Ext (V : Type*) where
  | old : V → Ext V
  | left | right | guardA | guardB
  deriving DecidableEq, Fintype

namespace Ext
variable {H : SimpleGraph V} {u v : V}

def rel (H : SimpleGraph V) (u v : V) : Ext V → Ext V → Prop
  | .old x, .old y => H.Adj x y
  | .old x, .left | .left, .old x => x ≠ v
  | .old x, .right | .right, .old x => x ≠ u
  | .old x, .guardA | .guardA, .old x => x = v
  | .old x, .guardB | .guardB, .old x => x = u
  | .left, .guardB | .guardB, .left | .right, .guardA | .guardA, .right => True
  | _, _ => False

def extend (H : SimpleGraph V) (u v : V) : SimpleGraph (Ext V) where
  Adj := rel H u v
  symm := by
    intro x y h
    cases x <;> cases y <;> first | exact h | exact H.symm h
  loopless := by
    constructor
    intro x
    cases x <;> simp [rel]

theorem unchanged (x y : V) :
    (extend H u v).Adj (.old x) (.old y) ↔ H.Adj x y := Iff.rfl

theorem keeps_edge (h : DomEdge H u v) : DomEdge (extend H u v) (.old u) (.old v) := by
  refine ⟨h.1, ?_⟩
  intro z
  cases z with
  | old x => exact h.2 x
  | left => exact Or.inl h.1.ne
  | right => exact Or.inr h.1.ne.symm
  | guardA => exact Or.inr rfl
  | guardB => exact Or.inl rfl

theorem old_short (h : H.Adj u v) (x : V) (z : Ext V) :
    Short (extend H u v) (.old x) z := by
  cases z with
  | old y =>
    by_cases hx : x = v
    · subst x
      by_cases hy : y = u
      · subst y
        exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr ⟨.right, h.ne.symm, hy⟩)
    · by_cases hy : y = v
      · subst y
        by_cases xu : x = u
        · subst x
          exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨.right, xu, h.ne.symm⟩)
      · exact Or.inr (Or.inr ⟨.left, hx, hy⟩)
  | left =>
    by_cases hx : x = v
    · subst x
      exact Or.inr (Or.inr ⟨.old u, h.symm, h.ne⟩)
    · exact Or.inr (Or.inl hx)
  | right =>
    by_cases hx : x = u
    · subst x
      exact Or.inr (Or.inr ⟨.old v, h, h.ne.symm⟩)
    · exact Or.inr (Or.inl hx)
  | guardA =>
    by_cases hx : x = u
    · subst x
      exact Or.inr (Or.inr ⟨.old v, h, rfl⟩)
    · exact Or.inr (Or.inr ⟨.right, hx, True.intro⟩)
  | guardB =>
    by_cases hx : x = v
    · subst x
      exact Or.inr (Or.inr ⟨.old u, h.symm, rfl⟩)
    · exact Or.inr (Or.inr ⟨.left, hx, True.intro⟩)

theorem far_left : ¬ Short (extend H u v) .left .guardA := by
  rintro (h | h | ⟨z, hz, ha⟩)
  · cases h
  · exact h
  · cases z <;> simp_all [extend, rel]

theorem far_right : ¬ Short (extend H u v) .right .guardB := by
  rintro (h | h | ⟨z, hz, hb⟩)
  · cases h
  · exact h
  · cases z <;> simp_all [extend, rel]

theorem exact_centers (h : H.Adj u v) (z : Ext V) :
    Central (extend H u v) z ↔ ∃ x, z = .old x := by
  have oldCover (x : V) : Covers (extend H u v) 2 (.old x) :=
    fun w => within_two.2 (old_short h x w)
  have noOne : ¬ ∃ w, Covers (extend H u v) 1 w := by
    rintro ⟨w, hw⟩
    exact far_left (short_of_one hw .left .guardA)
  constructor
  · intro hc
    have hz := hc 2 ⟨.old u, oldCover u⟩
    cases z with
    | old x => exact ⟨x, rfl⟩
    | left => exact False.elim (far_left (within_two.1 (hz .guardA)))
    | right => exact False.elim (far_right (within_two.1 (hz .guardB)))
    | guardA => exact False.elim (far_left (short_symm (within_two.1 (hz .left))))
    | guardB => exact False.elim (far_right (short_symm (within_two.1 (hz .right))))
  · rintro ⟨x, rfl⟩
    exact central_of_two (oldCover x) noOne

/-- The label map is injective, preserves all and only old edges, has image
exactly the center, and takes the specified edge to a dominating edge. -/
theorem realizes_center (h : DomEdge H u v) :
    Function.Injective (@old V) ∧
    (∀ x y, (extend H u v).Adj (.old x) (.old y) ↔ H.Adj x y) ∧
    (∀ z, Central (extend H u v) z ↔ ∃ x, z = .old x) ∧
    DomEdge (extend H u v) (.old u) (.old v) := by
  exact ⟨fun _ _ e => by cases e; rfl, fun _ _ => Iff.rfl,
    exact_centers h.1, keeps_edge h⟩

end Ext
end CenterDomination

#print axioms CenterDomination.within_iff_walk
#print axioms CenterDomination.within_iff_dist
#print axioms CenterDomination.central_iff_metric
#print axioms CenterDomination.center_dominating_edge
#print axioms CenterDomination.Ext.exact_centers
#print axioms CenterDomination.Ext.realizes_center
#eval Lean.versionString


import CenterRealization

namespace CenterDomination
variable {W : Type*} {G : SimpleGraph W}

noncomputable def outside [Fintype W] (G : SimpleGraph W) : Finset W := by
  classical
  exact Finset.univ.filter (fun w => ¬ Central G w)

/-- A leaf of the graph induced on the center, with its unique neighbor named. -/
def CenterLeaf (G : SimpleGraph W) (x u : W) : Prop :=
  Central G x ∧ Central G u ∧ G.Adj x u ∧
    ∀ z, Central G z → G.Adj x z → z = u

private theorem far_partner {u p : W} (hu : Covers G 2 u)
    (noOne : ¬ ∃ w, Covers G 1 w) (hp : ¬ Central G p) :
    ∃ q, ¬ Central G q ∧ ¬ Short G p q := by
  classical
  have hh : ¬ ∀ q, Within G 2 p q := fun cov => hp (central_of_two cov noOne)
  push_neg at hh
  obtain ⟨q, hq⟩ := hh
  refine ⟨q, ?_, fun e => hq (within_two.2 e)⟩
  intro hc
  exact hq (within_two.2 (short_symm (within_two.1 ((hc 2 ⟨u, hu⟩) p))))

private theorem four_from_leaf [Fintype W] {u x p : W}
    (hu : Covers G 2 u) (noOne : ¬ ∃ w, Covers G 1 w)
    (hx : CenterLeaf G x u) (hp : ¬ Central G p)
    (xp : G.Adj x p) (up : G.Adj u p) : 4 ≤ (outside G).card := by
  classical
  obtain ⟨q, hq, far⟩ := far_partner hu noOne hp
  have pq : p ≠ q := fun e => far (Or.inl e)
  have pq' : ¬ G.Adj p q := fun e => far (Or.inr (Or.inl e))
  have uq : ¬ G.Adj u q := fun e => far (Or.inr (Or.inr ⟨u, up.symm, e⟩))
  have xq : ¬ G.Adj x q := fun e => far (Or.inr (Or.inr ⟨x, xp.symm, e⟩))
  have xne : x ≠ q := by rintro rfl; exact hq hx.1
  obtain eq | adj | ⟨t, xt, tq⟩ := within_two.1 ((hx.1 2 ⟨u, hu⟩) q)
  · exact (xne eq).elim
  · exact (xq adj).elim
  have ht : ¬ Central G t := by
    intro ct
    have eq := hx.2.2.2 t ct xt
    exact uq (eq ▸ tq)
  have pt : p ≠ t := by rintro rfl; exact pq' tq
  obtain ⟨z, hz, zfar⟩ := far_partner hu noOne ht
  have pz : p ≠ z := by rintro rfl; exact zfar (Or.inr (Or.inr ⟨x, xt.symm, xp⟩))
  have qz : q ≠ z := by rintro rfl; exact zfar (Or.inr (Or.inl tq))
  have tz : t ≠ z := fun e => zfar (Or.inl e)
  have sub : ({p, q, t, z} : Finset W) ⊆ outside G := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> simp_all [outside]
  have count : ({p, q, t, z} : Finset W).card = 4 := by
    simp [pq, pt, pz, tq.ne.symm, qz, tz]
  exact count ▸ Finset.card_le_card sub

/-- Two leaves on opposite ends of a dominating edge in the induced center force
at least four noncentral vertices in the ambient graph. -/
theorem opposite_leaves_force_four [Fintype W] {u v x y : W}
    (h : DomEdge G u v) (hx : CenterLeaf G x u) (hy : CenterLeaf G y v)
    (hxy : x ≠ y) (hyu : y ≠ u) : 4 ≤ (outside G).card := by
  have nxy : ¬ G.Adj x y := fun e => hyu (hx.2.2.2 y hy.1 e)
  have noOne : ¬ ∃ w, Covers G 1 w := fun c =>
    nxy ((within_one.1 ((hx.1 1 c) y)).resolve_left hxy)
  obtain ⟨hu, hv⟩ := endpoints_cover_two h
  obtain eq | adj | ⟨p, xp, py⟩ := within_two.1 ((hx.1 2 ⟨u, hu⟩) y)
  · exact (hxy eq).elim
  · exact (nxy adj).elim
  have hp : ¬ Central G p := fun cp =>
    h.1.ne ((hx.2.2.2 p cp xp).symm.trans (hy.2.2.2 p cp py.symm))
  rcases h.2 p with up | vp
  · exact four_from_leaf hu noOne hx hp xp up
  · exact four_from_leaf hv noOne hy hp py.symm vp

theorem Ext.four_outside {V : Type*} [Fintype V] {H : SimpleGraph V} {u v : V}
    (h : DomEdge H u v) : (outside (Ext.extend H u v)).card = 4 := by
  classical
  have eq : outside (Ext.extend H u v) =
      ({Ext.left, Ext.right, Ext.guardA, Ext.guardB} : Finset (Ext V)) := by
    ext z
    cases z <;> simp [outside, Ext.exact_centers h.1]
  rw [eq]
  simp

end CenterDomination
#print axioms CenterDomination.opposite_leaves_force_four
#print axioms CenterDomination.Ext.four_outside



namespace CenterDomination

/-- The marked partition criterion in the paper. Ordinary domination includes
the vertex itself. A pair not joined by a walk of length at most two must
lie on the same side. -/
structure MarkedPartition {V : Type*} (H : SimpleGraph V) (u v : V)
    (A : V → Prop) : Prop where
  leftEndpoint : A u
  rightEndpoint : ¬ A v
  leftCover : ∀ x, ∃ y, A y ∧ (x = y ∨ H.Adj x y)
  rightCover : ∀ x, ∃ y, (¬ A y) ∧ (x = y ∨ H.Adj x y)
  sameSide : ∀ x y, ¬ Short H x y → (A x ↔ A y)

inductive TwoExt (V : Type*) where
  | old : V → TwoExt V
  | left | right
  deriving DecidableEq, Fintype

namespace TwoExt
variable {V : Type*} {H : SimpleGraph V} {u v : V} {A : V → Prop}

def rel (H : SimpleGraph V) (A : V → Prop) : TwoExt V → TwoExt V → Prop
  | .old x, .old y => H.Adj x y
  | .old x, .left | .left, .old x => A x
  | .old x, .right | .right, .old x => ¬ A x
  | _, _ => False

def extend (H : SimpleGraph V) (A : V → Prop) : SimpleGraph (TwoExt V) where
  Adj := rel H A
  symm := by
    intro x y h
    cases x <;> cases y <;> first | exact h | exact H.symm h
  loopless := by
    constructor
    intro x
    cases x <;> simp [rel]

theorem keeps_edge (h : DomEdge H u v) (part : MarkedPartition H u v A) :
    DomEdge (extend H A) (.old u) (.old v) := by
  refine ⟨h.1, ?_⟩
  intro z
  cases z with
  | old x => exact h.2 x
  | left => exact Or.inl part.leftEndpoint
  | right => exact Or.inr part.rightEndpoint

theorem far : ¬ Short (extend H A) .left .right := by
  rintro (h | h | ⟨z, hl, hr⟩)
  · cases h
  · exact h
  · cases z <;> simp_all [extend, rel]

theorem old_short (part : MarkedPartition H u v A) (x : V) (z : TwoExt V) :
    Short (extend H A) (.old x) z := by
  classical
  cases z with
  | old y =>
    by_cases hs : Short H x y
    · rcases hs with e | e | ⟨w, ex, ey⟩
      · subst y
        exact Or.inl rfl
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr ⟨.old w, ex, ey⟩)
    · have same := part.sameSide x y hs
      by_cases hx : A x
      · exact Or.inr (Or.inr ⟨.left, hx, same.mp hx⟩)
      · exact Or.inr (Or.inr ⟨.right, hx, fun hy => hx (same.mpr hy)⟩)
  | left =>
    obtain ⟨y, hy, e | e⟩ := part.leftCover x
    · subst y
      exact Or.inr (Or.inl hy)
    · exact Or.inr (Or.inr ⟨.old y, e, hy⟩)
  | right =>
    obtain ⟨y, hy, e | e⟩ := part.rightCover x
    · subst y
      exact Or.inr (Or.inl hy)
    · exact Or.inr (Or.inr ⟨.old y, e, hy⟩)

theorem exact_centers (part : MarkedPartition H u v A) (z : TwoExt V) :
    Central (extend H A) z ↔ ∃ x, z = .old x := by
  have oldCover (x : V) : Covers (extend H A) 2 (.old x) :=
    fun w => within_two.2 (old_short part x w)
  have noOne : ¬ ∃ w, Covers (extend H A) 1 w := by
    rintro ⟨w, hw⟩
    exact far (short_of_one hw .left .right)
  constructor
  · intro hc
    have hz := hc 2 ⟨.old u, oldCover u⟩
    cases z with
    | old x => exact ⟨x, rfl⟩
    | left => exact False.elim (far (within_two.1 (hz .right)))
    | right => exact False.elim (far (short_symm (within_two.1 (hz .left))))
  · rintro ⟨x, rfl⟩
    exact central_of_two (oldCover x) noOne

theorem two_outside [Fintype V] (part : MarkedPartition H u v A) :
    (outside (extend H A)).card = 2 := by
  classical
  have eq : outside (extend H A) = ({TwoExt.left, TwoExt.right} : Finset (TwoExt V)) := by
    ext z
    cases z <;> simp [outside, exact_centers part]
  rw [eq]
  simp

/-- Sufficiency of the partition criterion, including the entire induced
center, the marked edge and the exact number of additional vertices. -/
theorem realizes_two [Fintype V] (h : DomEdge H u v)
    (part : MarkedPartition H u v A) :
    Function.Injective (@old V) ∧
    (∀ x y, (extend H A).Adj (.old x) (.old y) ↔ H.Adj x y) ∧
    (∀ z, Central (extend H A) z ↔ ∃ x, z = .old x) ∧
    DomEdge (extend H A) (.old u) (.old v) ∧
    (outside (extend H A)).card = 2 := by
  exact ⟨fun _ _ e => by cases e; rfl, fun _ _ => Iff.rfl,
    exact_centers part, keeps_edge h part, two_outside part⟩

end TwoExt

/-- No three vertices can be pairwise at distance greater than two
in a graph with a dominating edge. -/
theorem no_three_pairwise_far {V : Type*} {G : SimpleGraph V} {u v p q z : V}
    (h : DomEdge G u v) (hpq : ¬ Short G p q)
    (hpz : ¬ Short G p z) (hqz : ¬ Short G q z) : False := by
  rcases h.2 p with hp | hp <;>
    rcases h.2 q with hq | hq <;>
    rcases h.2 z with hz | hz
  · exact hpq (Or.inr (Or.inr ⟨u, hp.symm, hq⟩))
  · exact hpq (Or.inr (Or.inr ⟨u, hp.symm, hq⟩))
  · exact hpz (Or.inr (Or.inr ⟨u, hp.symm, hz⟩))
  · exact hqz (Or.inr (Or.inr ⟨v, hq.symm, hz⟩))
  · exact hqz (Or.inr (Or.inr ⟨u, hq.symm, hz⟩))
  · exact hpz (Or.inr (Or.inr ⟨v, hp.symm, hz⟩))
  · exact hpq (Or.inr (Or.inr ⟨v, hp.symm, hq⟩))
  · exact hpq (Or.inr (Or.inr ⟨v, hp.symm, hq⟩))

end CenterDomination
#print axioms CenterDomination.TwoExt.keeps_edge
#print axioms CenterDomination.TwoExt.far
#print axioms CenterDomination.TwoExt.old_short
#print axioms CenterDomination.TwoExt.exact_centers
#print axioms CenterDomination.TwoExt.two_outside
#print axioms CenterDomination.TwoExt.realizes_two
#print axioms CenterDomination.no_three_pairwise_far


namespace CenterDomination

/-- The partition criterion is necessary given two exhaustive outside labels,
their far relation and the orientation of the marked endpoints.  The
complement of the first outside neighborhood absorbs unassigned vertices. -/
theorem marked_partition_of_two_labels {V W : Type*}
    {H : SimpleGraph V} {G : SimpleGraph W} {u v : V}
    {i : V → W} {p q : W}
    (inj : Function.Injective i)
    (edges : ∀ x y, G.Adj (i x) (i y) ↔ H.Adj x y)
    (allLabels : ∀ z, (∃ y, z = i y) ∨ z = p ∨ z = q)
    (hp : ∀ x, i x ≠ p) (hq : ∀ x, i x ≠ q)
    (far : ¬ Short G p q)
    (covers : ∀ x, Covers G 2 (i x))
    (up : G.Adj (i u) p) (vq : G.Adj (i v) q) :
    MarkedPartition H u v (fun x => G.Adj (i x) p) := by
  have disjoint (x : V) (b : G.Adj (i x) q) : ¬ G.Adj (i x) p :=
    fun a => far (Or.inr (Or.inr ⟨i x, a.symm, b⟩))
  have npq : ¬ G.Adj p q := fun e => far (Or.inr (Or.inl e))
  refine ⟨up, disjoint v vq, ?_, ?_, ?_⟩
  · intro x
    rcases within_two.1 (covers x p) with e | e | ⟨z, xz, zp⟩
    · exact (hp x e).elim
    · exact ⟨x, e, Or.inl rfl⟩
    · rcases allLabels z with ⟨y, rfl⟩ | rfl | rfl
      · exact ⟨y, zp, Or.inr ((edges x y).1 xz)⟩
      · exact (zp.ne rfl).elim
      · exact (npq zp.symm).elim
  · intro x
    rcases within_two.1 (covers x q) with e | e | ⟨z, xz, zq⟩
    · exact (hq x e).elim
    · exact ⟨x, disjoint x e, Or.inl rfl⟩
    · rcases allLabels z with ⟨y, rfl⟩ | rfl | rfl
      · exact ⟨y, disjoint y zq, Or.inr ((edges x y).1 xz)⟩
      · exact (npq zq).elim
      · exact (zq.ne rfl).elim
  · intro x y hfar
    rcases within_two.1 (covers x (i y)) with e | e | ⟨z, xz, zy⟩
    · exact (hfar (Or.inl (inj e))).elim
    · exact (hfar (Or.inr (Or.inl ((edges x y).1 e)))).elim
    · rcases allLabels z with ⟨w, rfl⟩ | rfl | rfl
      · exact (hfar (Or.inr (Or.inr ⟨w, (edges x w).1 xz, (edges w y).1 zy⟩))).elim
      · exact ⟨fun _ => zy.symm, fun _ => xz⟩
      · exact ⟨fun a => (disjoint x xz a).elim,
          fun b => (disjoint y zy.symm b).elim⟩

/-- Orient the two outside labels using the marked dominating edge. -/
theorem marked_partition_exists_of_two_labels {V W : Type*}
    {H : SimpleGraph V} {G : SimpleGraph W} {u v : V}
    {i : V → W} {p q : W}
    (inj : Function.Injective i)
    (edges : ∀ x y, G.Adj (i x) (i y) ↔ H.Adj x y)
    (allLabels : ∀ z, (∃ y, z = i y) ∨ z = p ∨ z = q)
    (hp : ∀ x, i x ≠ p) (hq : ∀ x, i x ≠ q)
    (far : ¬ Short G p q)
    (covers : ∀ x, Covers G 2 (i x))
    (mark : DomEdge G (i u) (i v)) :
    ∃ A : V → Prop, MarkedPartition H u v A := by
  rcases mark.2 p with up | vp
  · rcases mark.2 q with uq | vq
    · exact (far (Or.inr (Or.inr ⟨i u, up.symm, uq⟩))).elim
    · exact ⟨_, marked_partition_of_two_labels inj edges allLabels hp hq far covers up vq⟩
  · rcases mark.2 q with uq | vq
    · have swapLabels : ∀ z, (∃ y, z = i y) ∨ z = q ∨ z = p := by
        intro z
        rcases allLabels z with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl h)
      have swapFar : ¬ Short G q p := fun h => far (short_symm h)
      exact ⟨_, marked_partition_of_two_labels inj edges swapLabels hq hp swapFar covers uq vp⟩
    · exact (far (Or.inr (Or.inr ⟨i v, vp.symm, vq⟩))).elim

end CenterDomination
#print axioms CenterDomination.marked_partition_of_two_labels
#print axioms CenterDomination.marked_partition_exists_of_two_labels

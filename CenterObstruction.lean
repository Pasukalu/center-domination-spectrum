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


namespace CenterDomination
universe u

/-- The finite ambient graph has precisely two distinct extra labels, its
entire center is the old image, and the marked edge remains dominating. -/
def MarkedTwoRealizable {V : Type u} (H : SimpleGraph V) (a b : V) : Prop :=
  ∃ (W : Type u) (_fin : Finite W) (G : SimpleGraph W) (i : V → W) (p q : W),
    Function.Injective i ∧
    (∀ x y, G.Adj (i x) (i y) ↔ H.Adj x y) ∧
    (∀ z, Central G z ↔ ∃ x, z = i x) ∧
    (∀ x, i x ≠ p) ∧ (∀ x, i x ≠ q) ∧ p ≠ q ∧
    (∀ z, (∃ x, z = i x) ∨ z = p ∨ z = q) ∧
    DomEdge G (i a) (i b)

/-- Equivalence for noncomplete old graphs. This proves the two-appendage
criterion at the graph level; the three-to-two reduction is separate. -/
theorem marked_two_realizable_iff {V : Type u} [Fintype V]
    {H : SimpleGraph V} {a b : V} (h : DomEdge H a b)
    (noncomplete : ∃ x y, x ≠ y ∧ ¬ H.Adj x y) :
    MarkedTwoRealizable H a b ↔ ∃ A : V → Prop, MarkedPartition H a b A := by
  constructor
  · rintro ⟨W, _, G, i, p, q, inj, edges, image, hp, hq, _, labels, mark⟩
    obtain ⟨x, y, hxy, hnxy⟩ := noncomplete
    have cx : Central G (i x) := (image (i x)).2 ⟨x, rfl⟩
    have noOne : ¬ ∃ w, Covers G 1 w := by
      intro hex
      rcases within_one.1 ((cx 1 hex) (i y)) with e | e
      · exact hxy (inj e)
      · exact hnxy ((edges x y).1 e)
    have hu := (endpoints_cover_two mark).1
    have cov (z : V) : Covers G 2 (i z) :=
      ((image (i z)).2 ⟨z, rfl⟩) 2 ⟨i a, hu⟩
    have pnc : ¬ Central G p := by
      intro cp
      obtain ⟨z, hz⟩ := (image p).1 cp
      exact hp z hz.symm
    obtain ⟨t, tnc, tfar⟩ := far_partner hu noOne pnc
    rcases labels t with ⟨z, rfl⟩ | rfl | rfl
    · exact (tnc ((image (i z)).2 ⟨z, rfl⟩)).elim
    · exact (tfar (Or.inl rfl)).elim
    · exact marked_partition_exists_of_two_labels inj edges labels hp hq tfar cov mark
  · rintro ⟨A, part⟩
    obtain ⟨inj, edges, image, mark, _⟩ := TwoExt.realizes_two h part
    refine ⟨TwoExt V, inferInstance, TwoExt.extend H A, TwoExt.old,
      TwoExt.left, TwoExt.right, inj, edges, image, ?_, ?_, ?_, ?_, mark⟩
    · intro x e
      cases e
    · intro x e
      cases e
    · intro e
      cases e
    · intro z
      cases z with
      | old x => exact Or.inl ⟨x, rfl⟩
      | left => exact Or.inr (Or.inl rfl)
      | right => exact Or.inr (Or.inr rfl)

end CenterDomination
#print axioms CenterDomination.marked_two_realizable_iff


namespace CenterDomination

/-- Swapping the parts swaps the designated endpoints. -/
theorem MarkedPartition.complement {V : Type*} {H : SimpleGraph V}
    {u v : V} {A : V → Prop} (part : MarkedPartition H v u A) :
    MarkedPartition H u v (fun x => ¬ A x) := by
  refine ⟨part.rightEndpoint, fun hn => hn part.leftEndpoint,
    part.rightCover, ?_, ?_⟩
  · intro x
    obtain ⟨y, hy, hxy⟩ := part.leftCover x
    exact ⟨y, fun hn => hn hy, hxy⟩
  · intro x y far
    exact not_congr (part.sameSide x y far)

/-- Merge the two end labels of the auxiliary far path at the level of
their old neighborhoods. The result is a marked partition. -/
theorem marked_partition_of_three_path {V W : Type*}
    {H : SimpleGraph V} {G : SimpleGraph W} {u v : V}
    {i : V → W} {p q z : W}
    (inj : Function.Injective i)
    (edges : ∀ x y, G.Adj (i x) (i y) ↔ H.Adj x y)
    (labels : ∀ w, (∃ y, w = i y) ∨ w = p ∨ w = q ∨ w = z)
    (hp : ∀ x, i x ≠ p) (hq : ∀ x, i x ≠ q)
    (fpq : ¬ Short G p q) (fzq : ¬ Short G z q)
    (covers : ∀ x, Covers G 2 (i x))
    (up : G.Adj (i u) p) (vq : G.Adj (i v) q) :
    MarkedPartition H u v (fun x => G.Adj (i x) p ∨ G.Adj (i x) z) := by
  have disjoint (x : V) (e : G.Adj (i x) q) :
      ¬ (G.Adj (i x) p ∨ G.Adj (i x) z) := by
    rintro (a | a)
    · exact fpq (Or.inr (Or.inr ⟨i x, a.symm, e⟩))
    · exact fzq (Or.inr (Or.inr ⟨i x, a.symm, e⟩))
  have npq : ¬ G.Adj p q := fun e => fpq (Or.inr (Or.inl e))
  have nzq : ¬ G.Adj z q := fun e => fzq (Or.inr (Or.inl e))
  refine ⟨Or.inl up, disjoint v vq, ?_, ?_, ?_⟩
  · intro x
    rcases within_two.1 (covers x p) with e | e | ⟨w, xw, wp⟩
    · exact (hp x e).elim
    · exact ⟨x, Or.inl e, Or.inl rfl⟩
    · rcases labels w with ⟨y, rfl⟩ | rfl | rfl | rfl
      · exact ⟨y, Or.inl wp, Or.inr ((edges x y).1 xw)⟩
      · exact (wp.ne rfl).elim
      · exact (npq wp.symm).elim
      · exact ⟨x, Or.inr xw, Or.inl rfl⟩
  · intro x
    rcases within_two.1 (covers x q) with e | e | ⟨w, xw, wq⟩
    · exact (hq x e).elim
    · exact ⟨x, disjoint x e, Or.inl rfl⟩
    · rcases labels w with ⟨y, rfl⟩ | rfl | rfl | rfl
      · exact ⟨y, disjoint y wq, Or.inr ((edges x y).1 xw)⟩
      · exact (npq wq).elim
      · exact (wq.ne rfl).elim
      · exact (nzq wq).elim
  · intro x y hf
    rcases within_two.1 (covers x (i y)) with e | e | ⟨w, xw, wy⟩
    · exact (hf (Or.inl (inj e))).elim
    · exact (hf (Or.inr (Or.inl ((edges x y).1 e)))).elim
    · rcases labels w with ⟨a, rfl⟩ | rfl | rfl | rfl
      · exact (hf (Or.inr (Or.inr ⟨a, (edges x a).1 xw, (edges a y).1 wy⟩))).elim
      · exact ⟨fun _ => Or.inl wy.symm, fun _ => Or.inl xw⟩
      · exact ⟨fun a => (disjoint x xw a).elim,
          fun b => (disjoint y wy.symm b).elim⟩
      · exact ⟨fun _ => Or.inr wy.symm, fun _ => Or.inr xw⟩

theorem marked_partition_exists_of_three_path {V W : Type*}
    {H : SimpleGraph V} {G : SimpleGraph W} {u v : V}
    {i : V → W} {p q z : W}
    (inj : Function.Injective i)
    (edges : ∀ x y, G.Adj (i x) (i y) ↔ H.Adj x y)
    (labels : ∀ w, (∃ y, w = i y) ∨ w = p ∨ w = q ∨ w = z)
    (hp : ∀ x, i x ≠ p) (hq : ∀ x, i x ≠ q)
    (fpq : ¬ Short G p q) (fzq : ¬ Short G z q)
    (covers : ∀ x, Covers G 2 (i x))
    (mark : DomEdge G (i u) (i v)) :
    ∃ A : V → Prop, MarkedPartition H u v A := by
  rcases mark.2 q with uq | vq
  · have vp : G.Adj (i v) p := (mark.2 p).resolve_left
      (fun up => fpq (Or.inr (Or.inr ⟨i u, up.symm, uq⟩)))
    have part : MarkedPartition H v u (fun x => G.Adj (i x) p ∨ G.Adj (i x) z) :=
      marked_partition_of_three_path inj edges labels hp hq fpq fzq covers vp uq
    exact ⟨_, part.complement⟩
  · have up : G.Adj (i u) p := (mark.2 p).resolve_right
      (fun vp => fpq (Or.inr (Or.inr ⟨i v, vp.symm, vq⟩)))
    exact ⟨_, marked_partition_of_three_path inj edges labels hp hq fpq fzq covers up vq⟩

universe u

/-- A realization with three extra labels. Disjointness and exhaustiveness
are explicit so the statement does not merely assert an upper bound. -/
def MarkedThreeRealizable {V : Type u} (H : SimpleGraph V) (a b : V) : Prop :=
  ∃ (W : Type u) (_fin : Finite W) (G : SimpleGraph W) (i : V → W) (p q z : W),
    Function.Injective i ∧
    (∀ x y, G.Adj (i x) (i y) ↔ H.Adj x y) ∧
    (∀ w, Central G w ↔ ∃ x, w = i x) ∧
    (∀ x, i x ≠ p) ∧ (∀ x, i x ≠ q) ∧ (∀ x, i x ≠ z) ∧
    p ≠ q ∧ p ≠ z ∧ q ≠ z ∧
    (∀ w, (∃ x, w = i x) ∨ w = p ∨ w = q ∨ w = z) ∧
    DomEdge G (i a) (i b)

/-- The three-to-two reduction for the marked appendage number. The proof
extracts a far path and constructs a two-part partition. -/
theorem marked_three_implies_two {V : Type u} [Fintype V]
    {H : SimpleGraph V} {a b : V} (h : DomEdge H a b)
    (noncomplete : ∃ x y, x ≠ y ∧ ¬ H.Adj x y)
    (three : MarkedThreeRealizable H a b) :
    MarkedTwoRealizable H a b := by
  obtain ⟨W, _, G, i, p, q, z, inj, edges, image, hp, hq, hz, _, _, _, labels, mark⟩ := three
  obtain ⟨x, y, hxy, hnxy⟩ := noncomplete
  have cx : Central G (i x) := (image (i x)).2 ⟨x, rfl⟩
  have noOne : ¬ ∃ w, Covers G 1 w := by
    intro hex
    rcases within_one.1 ((cx 1 hex) (i y)) with e | e
    · exact hxy (inj e)
    · exact hnxy ((edges x y).1 e)
  have hu := (endpoints_cover_two mark).1
  have cov (w : V) : Covers G 2 (i w) :=
    ((image (i w)).2 ⟨w, rfl⟩) 2 ⟨i a, hu⟩
  have outsideLabel (t : W) (ht : ∀ w, i w ≠ t) : ¬ Central G t := by
    intro ct
    obtain ⟨w, hw⟩ := (image t).1 ct
    exact ht w hw.symm
  have farLabel (t : W) (ht : ∀ w, i w ≠ t) :
      (¬ Short G t p) ∨ (¬ Short G t q) ∨ (¬ Short G t z) := by
    obtain ⟨s, snc, sf⟩ := far_partner hu noOne (outsideLabel t ht)
    rcases labels s with ⟨w, rfl⟩ | rfl | rfl | rfl
    · exact (snc ((image (i w)).2 ⟨w, rfl⟩)).elim
    · exact Or.inl sf
    · exact Or.inr (Or.inl sf)
    · exact Or.inr (Or.inr sf)
  have pFar : (¬ Short G p q) ∨ (¬ Short G p z) :=
    (farLabel p hp).resolve_left (fun f => f (Or.inl rfl))
  have qFar : (¬ Short G q p) ∨ (¬ Short G q z) := by
    rcases farLabel q hq with f | f | f
    · exact Or.inl f
    · exact (f (Or.inl rfl)).elim
    · exact Or.inr f
  have zFar : (¬ Short G z p) ∨ (¬ Short G z q) := by
    rcases farLabel z hz with f | f | f
    · exact Or.inl f
    · exact Or.inr f
    · exact (f (Or.inl rfl)).elim
  apply (marked_two_realizable_iff h ⟨x, y, hxy, hnxy⟩).2
  rcases pFar with fpq | fpz
  · rcases zFar with fzp | fzq
    · have perm : ∀ w, (∃ t, w = i t) ∨ w = q ∨ w = p ∨ w = z := by
        intro w
        rcases labels w with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr h))
      exact marked_partition_exists_of_three_path inj edges perm hq hp
        (fun e => fpq (short_symm e)) fzp cov mark
    · exact marked_partition_exists_of_three_path inj edges labels hp hq fpq fzq cov mark
  · rcases qFar with fqp | fqz
    · have perm : ∀ w, (∃ t, w = i t) ∨ w = q ∨ w = p ∨ w = z := by
        intro w
        rcases labels w with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr h))
      exact marked_partition_exists_of_three_path inj edges perm hq hp
        fqp (fun e => fpz (short_symm e)) cov mark
    · have perm : ∀ w, (∃ t, w = i t) ∨ w = p ∨ w = z ∨ w = q := by
        intro w
        rcases labels w with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inr (Or.inr (Or.inl h))
      exact marked_partition_exists_of_three_path inj edges perm hp hz fpz fqz cov mark

end CenterDomination
#print axioms CenterDomination.MarkedPartition.complement
#print axioms CenterDomination.marked_partition_of_three_path
#print axioms CenterDomination.marked_partition_exists_of_three_path
#print axioms CenterDomination.marked_three_implies_two


namespace CenterDomination
universe u

/-- A realization with exactly n noncentral vertices, counted in the finite
ambient graph rather than in a preselected list of labels. -/
def MarkedAppendage {V : Type u} (H : SimpleGraph V) (a b : V) (n : ℕ) : Prop :=
  ∃ (W : Type u) (fin : Fintype W) (G : SimpleGraph W) (i : V → W),
    Function.Injective i ∧
    (∀ x y, G.Adj (i x) (i y) ↔ H.Adj x y) ∧
    (∀ w, Central G w ↔ ∃ x, w = i x) ∧
    DomEdge G (i a) (i b) ∧ (@outside W fin G).card = n

def MarkedMinimum {V : Type u} (H : SimpleGraph V) (a b : V) (n : ℕ) : Prop :=
  MarkedAppendage H a b n ∧ ∀ k, MarkedAppendage H a b k → n ≤ k

private theorem splitFinset {W : Type*} (s : Finset W) (h : 0 < s.card) :
    ∃ p : W, ∃ t : Finset W, p ∈ s ∧ p ∉ t ∧ t.card + 1 = s.card ∧
      ∀ w, w ∈ s ↔ w = p ∨ w ∈ t := by
  classical
  obtain ⟨p, hp⟩ := Finset.card_pos.mp h
  refine ⟨p, s.erase p, hp, by simp, ?_, ?_⟩
  · have e := Finset.card_erase_of_mem hp
    omega
  · intro w
    by_cases e : w = p
    · subst w
      simp [hp]
    · simp [Finset.mem_erase, e]

private theorem outside_mem_iff {W : Type*} [Fintype W] (G : SimpleGraph W) (w : W) :
    w ∈ outside G ↔ ¬ Central G w := by
  classical
  simp [outside]

private theorem old_not_outside {V W : Type*} [Fintype W] {G : SimpleGraph W}
    {i : V → W} (image : ∀ w, Central G w ↔ ∃ x, w = i x) (x : V) :
    i x ∉ outside G :=
  fun e => (outside_mem_iff G _).1 e ((image _).2 ⟨x, rfl⟩)

private theorem old_ne_of_outside {V W : Type*} [Fintype W] {G : SimpleGraph W}
    {i : V → W} (image : ∀ w, Central G w ↔ ∃ x, w = i x)
    {p : W} (hp : p ∈ outside G) : ∀ x, i x ≠ p := by
  intro x e
  exact old_not_outside image x (e.symm ▸ hp)

/-- Zero additions are equivalent to self-centeredness. -/
theorem marked_zero_iff {V : Type u} [Fintype V] {H : SimpleGraph V} {a b : V}
    (h : DomEdge H a b) :
    MarkedAppendage H a b 0 ↔ ∀ x, Central H x := by
  classical
  constructor
  · rintro ⟨W, fin, G, i, inj, edges, image, mark, card⟩
    letI : Fintype W := fin
    have surj : Function.Surjective i := by
      intro w
      have central : Central G w := by
        by_contra hn
        have mem := (outside_mem_iff G w).2 hn
        have empty : outside G = ∅ := Finset.card_eq_zero.mp card
        rw [empty] at mem
        simp at mem
      obtain ⟨x, e⟩ := (image w).1 central
      exact ⟨x, e.symm⟩
    have bridge (k : ℕ) (x y : V) : Within H k x y ↔ Within G k (i x) (i y) := by
      induction k generalizing x y with
      | zero =>
        change x = y ↔ i x = i y
        exact ⟨congrArg i, inj⟩
      | succ k ih =>
        change (Within H k x y ∨ ∃ z, H.Adj x z ∧ Within H k z y) ↔
          (Within G k (i x) (i y) ∨ ∃ z, G.Adj (i x) z ∧ Within G k z (i y))
        constructor
        · rintro (e | ⟨z, e, w⟩)
          · exact Or.inl ((ih x y).1 e)
          · exact Or.inr ⟨i z, (edges x z).2 e, (ih z y).1 w⟩
        · rintro (e | ⟨z, e, w⟩)
          · exact Or.inl ((ih x y).2 e)
          · obtain ⟨z, rfl⟩ := surj z
            exact Or.inr ⟨z, (edges x z).1 e, (ih z y).2 w⟩
    intro x k hex y
    obtain ⟨w, cov⟩ := hex
    have ambientCover : Covers G k (i w) := by
      intro z
      obtain ⟨z, rfl⟩ := surj z
      exact (bridge k w z).1 (cov z)
    exact (bridge k x y).2 (((image _).2 ⟨x, rfl⟩) k ⟨i w, ambientCover⟩ (i y))
  · intro all
    refine ⟨V, inferInstance, H, id, fun _ _ e => e, fun _ _ => Iff.rfl,
      ?_, h, ?_⟩
    · intro w
      exact ⟨fun _ => ⟨w, rfl⟩, fun _ => all w⟩
    · have empty : outside H = ∅ := by
        ext w
        simp [outside, all w]
      simp [empty]

/-- A noncomplete induced center cannot have exactly one outside vertex
when the marked dominating edge is preserved. -/
theorem marked_one_impossible {V : Type u} {H : SimpleGraph V} {a b : V}
    (nc : ∃ x y, x ≠ y ∧ ¬ H.Adj x y) : ¬ MarkedAppendage H a b 1 := by
  classical
  rintro ⟨W, fin, G, i, inj, edges, image, mark, card⟩
  letI : Fintype W := fin
  obtain ⟨x, y, ne, na⟩ := nc
  have noOne : ¬ ∃ w, Covers G 1 w := by
    intro hex
    rcases within_one.1 (((image _).2 ⟨x, rfl⟩) 1 hex (i y)) with e | e
    · exact ne (inj e)
    · exact na ((edges x y).1 e)
  obtain ⟨p, t, hp, _, ct, labels⟩ := splitFinset (outside G) (by omega)
  have empty : t = ∅ := Finset.card_eq_zero.mp (by omega)
  obtain ⟨q, qnc, far⟩ := far_partner (endpoints_cover_two mark).1 noOne
    ((outside_mem_iff G p).1 hp)
  rcases (labels q).1 ((outside_mem_iff G q).2 qnc) with e | e
  · exact far (Or.inl e.symm)
  · simpa [empty] using e

theorem marked_two_of_card {V : Type u} {H : SimpleGraph V} {a b : V}
    (real : MarkedAppendage H a b 2) : MarkedTwoRealizable H a b := by
  classical
  obtain ⟨W, fin, G, i, inj, edges, image, mark, card⟩ := real
  letI : Fintype W := fin
  obtain ⟨p, t, hp, hpt, ct, lp⟩ := splitFinset (outside G) (by omega)
  obtain ⟨q, s, hq, _, cs, lq⟩ := splitFinset t (by omega)
  have empty : s = ∅ := Finset.card_eq_zero.mp (by omega)
  have hq' : q ∈ outside G := (lp q).2 (Or.inr hq)
  have pq : p ≠ q := fun e => hpt (e.symm ▸ hq)
  refine ⟨W, inferInstance, G, i, p, q, inj, edges, image,
    old_ne_of_outside image hp, old_ne_of_outside image hq', pq, ?_, mark⟩
  intro w
  by_cases hc : Central G w
  · exact Or.inl ((image w).1 hc)
  · rcases (lp w).1 ((outside_mem_iff G w).2 hc) with e | e
    · exact Or.inr (Or.inl e)
    · rcases (lq w).1 e with e | e
      · exact Or.inr (Or.inr e)
      · simpa [empty] using e

theorem marked_three_of_card {V : Type u} {H : SimpleGraph V} {a b : V}
    (real : MarkedAppendage H a b 3) : MarkedThreeRealizable H a b := by
  classical
  obtain ⟨W, fin, G, i, inj, edges, image, mark, card⟩ := real
  letI : Fintype W := fin
  obtain ⟨p, t, hp, hpt, ct, lp⟩ := splitFinset (outside G) (by omega)
  obtain ⟨q, s, hq, hqs, cs, lq⟩ := splitFinset t (by omega)
  obtain ⟨z, r, hz, _, cr, lz⟩ := splitFinset s (by omega)
  have empty : r = ∅ := Finset.card_eq_zero.mp (by omega)
  have hzt : z ∈ t := (lq z).2 (Or.inr hz)
  have hq' : q ∈ outside G := (lp q).2 (Or.inr hq)
  have hz' : z ∈ outside G := (lp z).2 (Or.inr hzt)
  have pq : p ≠ q := fun e => hpt (e.symm ▸ hq)
  have pz : p ≠ z := fun e => hpt (e.symm ▸ hzt)
  have qz : q ≠ z := fun e => hqs (e.symm ▸ hz)
  refine ⟨W, inferInstance, G, i, p, q, z, inj, edges, image,
    old_ne_of_outside image hp, old_ne_of_outside image hq',
    old_ne_of_outside image hz', pq, pz, qz, ?_, mark⟩
  intro w
  by_cases hc : Central G w
  · exact Or.inl ((image w).1 hc)
  · rcases (lp w).1 ((outside_mem_iff G w).2 hc) with e | e
    · exact Or.inr (Or.inl e)
    · rcases (lq w).1 e with e | e
      · exact Or.inr (Or.inr (Or.inl e))
      · rcases (lz w).1 e with e | e
        · exact Or.inr (Or.inr (Or.inr e))
        · simpa [empty] using e

theorem marked_appendage_two_of_partition {V : Type u} [Fintype V]
    {H : SimpleGraph V} {a b : V} {A : V → Prop}
    (h : DomEdge H a b) (part : MarkedPartition H a b A) :
    MarkedAppendage H a b 2 := by
  obtain ⟨inj, edges, image, mark, count⟩ := TwoExt.realizes_two h part
  exact ⟨TwoExt V, inferInstance, TwoExt.extend H A, TwoExt.old,
    inj, edges, image, mark, count⟩

theorem marked_appendage_four {V : Type u} [Fintype V]
    {H : SimpleGraph V} {a b : V} (h : DomEdge H a b) :
    MarkedAppendage H a b 4 := by
  obtain ⟨inj, edges, image, mark⟩ := Ext.realizes_center h
  exact ⟨Ext V, inferInstance, Ext.extend H a b, Ext.old,
    inj, edges, image, mark, Ext.four_outside h⟩

private theorem noncomplete_of_not_self_centered {V : Type*}
    {H : SimpleGraph V} (notSelf : ¬ ∀ x, Central H x) :
    ∃ x y, x ≠ y ∧ ¬ H.Adj x y := by
  classical
  by_contra hn
  apply notSelf
  intro x r hex
  by_cases small : r = 0
  · subst r
    obtain ⟨w, cov⟩ := hex
    intro y
    exact (cov x).symm.trans (cov y)
  · have h1 : Covers H 1 x := by
      intro y
      apply within_one.2
      by_cases eq : x = y
      · exact Or.inl eq
      · exact Or.inr (by
          by_contra na
          exact hn ⟨x, y, eq, na⟩)
    exact covers_mono h1 (by omega)

/-- Integrated minimum theorem: the least actual outside cardinality is
zero for self-centered H, two for the partition case, and four otherwise.
No hypothesis about a preselected list of outside labels is required. -/
theorem marked_minimum_classification {V : Type u} [Fintype V]
    {H : SimpleGraph V} {a b : V} (h : DomEdge H a b) :
    ((∀ x, Central H x) ∧ MarkedMinimum H a b 0) ∨
    ((¬ ∀ x, Central H x) ∧ (∃ A : V → Prop, MarkedPartition H a b A) ∧
      MarkedMinimum H a b 2) ∨
    ((¬ ∀ x, Central H x) ∧ (¬ ∃ A : V → Prop, MarkedPartition H a b A) ∧
      MarkedMinimum H a b 4) := by
  classical
  by_cases self : ∀ x, Central H x
  · exact Or.inl ⟨self, (marked_zero_iff h).2 self, fun _ _ => Nat.zero_le _⟩
  · have nc := noncomplete_of_not_self_centered self
    have noZero : ¬ MarkedAppendage H a b 0 := fun r => self ((marked_zero_iff h).1 r)
    have noOne := marked_one_impossible (a := a) (b := b) nc
    by_cases partition : ∃ A : V → Prop, MarkedPartition H a b A
    · obtain ⟨A, part⟩ := partition
      refine Or.inr (Or.inl ⟨self, ⟨A, part⟩, marked_appendage_two_of_partition h part, ?_⟩)
      intro k r
      by_contra hn
      have cases : k = 0 ∨ k = 1 := by omega
      rcases cases with rfl | rfl
      · exact noZero r
      · exact noOne r
    · have noTwo : ¬ MarkedAppendage H a b 2 := fun r =>
        partition ((marked_two_realizable_iff h nc).1 (marked_two_of_card r))
      have noThree : ¬ MarkedAppendage H a b 3 := fun r =>
        partition ((marked_two_realizable_iff h nc).1
          (marked_three_implies_two h nc (marked_three_of_card r)))
      refine Or.inr (Or.inr ⟨self, partition, marked_appendage_four h, ?_⟩)
      intro k r
      by_contra hn
      have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl
      · exact noZero r
      · exact noOne r
      · exact noTwo r
      · exact noThree r

end CenterDomination
#print axioms CenterDomination.marked_zero_iff
#print axioms CenterDomination.marked_one_impossible
#print axioms CenterDomination.marked_two_of_card
#print axioms CenterDomination.marked_three_of_card
#print axioms CenterDomination.marked_appendage_two_of_partition
#print axioms CenterDomination.marked_appendage_four
#print axioms CenterDomination.marked_minimum_classification

import CenterRealization

namespace CenterDomination
variable {W : Type*} {G : SimpleGraph W}

noncomputable def outside [Fintype W] (G : SimpleGraph W) : Finset W := by
  classical
  exact Finset.univ.filter (fun w => ¬ Central G w)

/-- A proper center leaves at least two vertices outside it (Theorem 3.1). -/
theorem two_outside_of_noncentral [Fintype W] (hc : G.Connected)
    {x : W} (hx : ¬ Central G x) : 2 ≤ (outside G).card := by
  classical
  have hfail := hx
  unfold Central at hfail
  obtain ⟨r, hr⟩ := Classical.not_forall.mp hfail
  have hex : ∃ w, Covers G r w := by
    by_contra hnone
    exact hr (fun h => False.elim (hnone h))
  have hnoc : ¬ Covers G r x := fun h => hr (fun _ => h)
  obtain ⟨y, hy⟩ := Classical.not_forall.mp hnoc
  have hfar : ¬ G.dist x y ≤ r := fun hle => hy ((within_iff_dist hc r x y).2 hle)
  have hne : x ≠ y := by
    rintro rfl
    exact hfar (by simp)
  have hyn : ¬ Central G y := by
    intro cy
    have hle := (within_iff_dist hc r y x).1 (cy r hex x)
    have hsymm : G.dist x y = G.dist y x := SimpleGraph.dist_comm
    exact hfar (hsymm.le.trans hle)
  have sub : ({x, y} : Finset W) ⊆ outside G := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> simp_all [outside]
  simpa [hne] using Finset.card_le_card sub

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
#print axioms CenterDomination.two_outside_of_noncentral


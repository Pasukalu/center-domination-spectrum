import CenterFan

namespace CenterDomination
universe u

/-- Isomorphic to the entire induced center of a finite connected graph
having a dominating edge. The ambient type is part of the witness. -/
def Realizable {V : Type u} (H : SimpleGraph V) : Prop :=
  ∃ (W : Type u) (_fin : Finite W) (G : SimpleGraph W) (i : V → W),
    Function.Injective i ∧ G.Connected ∧ (∃ a b, DomEdge G a b) ∧
    (∀ x y, G.Adj (i x) (i y) ↔ H.Adj x y) ∧
    (∀ w, Central G w ↔ ∃ x, w = i x)

theorem realization_iff {V : Type u} [Fintype V] (H : SimpleGraph V)
    {a b : V} (hab : a ≠ b) : Realizable H ↔ ∃ u v, DomEdge H u v := by
  constructor
  · rintro ⟨W, _, G, i, inj, _, ⟨l, r, de⟩, hi, image⟩
    have ha := (image (i a)).2 ⟨a, rfl⟩
    have hb := (image (i b)).2 ⟨b, rfl⟩
    have hne : i a ≠ i b := fun h => hab (inj h)
    obtain ⟨p, q, hp, hq, e, cover⟩ := center_dominating_edge de ha hb hne
    obtain ⟨u, rfl⟩ := (image p).1 hp
    obtain ⟨v, rfl⟩ := (image q).1 hq
    refine ⟨u, v, (hi u v).1 e, ?_⟩
    intro x
    have hx := (image (i x)).2 ⟨x, rfl⟩
    exact (cover _ hx).imp (hi u x).1 (hi v x).1
  · rintro ⟨u, v, h⟩
    obtain ⟨hinj, he, hc, hde⟩ := Ext.realizes_center h
    exact ⟨Ext V, inferInstance, Ext.extend H u v, Ext.old, hinj,
      connected_of_domEdge hde, ⟨.old u, .old v, hde⟩, he, hc⟩

theorem extension_radius_and_diameter {V : Type u} {H : SimpleGraph V} {u v : V}
    (h : DomEdge H u v) :
    let G := Ext.extend H u v
    (∃ x, Covers G 2 x) ∧ (¬ ∃ x, Covers G 1 x) ∧
    (∀ x y, Within G 3 x y) ∧ ∃ x y, ¬ Within G 2 x y := by
  dsimp only
  let hde := Ext.keeps_edge h
  obtain ⟨hu, hv⟩ := endpoints_cover_two hde
  refine ⟨⟨.old u, hu⟩, ?_, ?_, ⟨.left, .guardA, ?_⟩⟩
  · rintro ⟨x, hx⟩
    exact Ext.far_left (short_of_one hx .left .guardA)
  · intro x y
    rcases hde.2 x with hx | hx
    · exact Or.inr ⟨.old u, hx.symm, hu y⟩
    · exact Or.inr ⟨.old v, hx.symm, hv y⟩
  · exact fun hw => Ext.far_left (within_two.1 hw)

end CenterDomination
#print axioms CenterDomination.realization_iff
#print axioms CenterDomination.extension_radius_and_diameter


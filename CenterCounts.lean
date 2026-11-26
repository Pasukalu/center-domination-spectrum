import CenterDomination

namespace CenterDomination
open Finset
variable {V : Type*}

theorem connected_of_domEdge {G : SimpleGraph V} {u v : V} (h : DomEdge G u v) :
    G.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable G).2
  refine ⟨u, ?_⟩
  intro z
  obtain ⟨p, _⟩ := (within_iff_walk G 2 u z).1 ((endpoints_cover_two h).1 z)
  exact ⟨p⟩

noncomputable def centerPairs [Fintype V] (G : SimpleGraph V) : Finset (V × V) := by
  classical
  exact Finset.univ.filter (fun p => Central G p.1 ∧ Central G p.2 ∧ p.1 ≠ p.2)

noncomputable def meanCenter [Fintype V] (G : SimpleGraph V) : ℚ :=
  (∑ p ∈ centerPairs G, (G.dist p.1 p.2 : ℚ)) / (centerPairs G).card

/-- A formulation for every total dominating set avoids assigning a finite
minimum to a graph with no such set. On nontrivial connected graphs this is
the conjectured floor inequality by taking a minimum set. -/
def Claim268 (G : SimpleGraph V) [Fintype V] : Prop :=
  G.Connected → ∀ D : Finset V, (∀ x, ∃ d ∈ D, G.Adj d x) → meanCenter G < D.card

theorem center_distance_one_or_two {G : SimpleGraph V} {u v x y : V}
    (h : DomEdge G u v) (hx : Central G x) (hne : x ≠ y) :
    G.dist x y = 1 ∨ G.dist x y = 2 := by
  have hc := connected_of_domEdge h
  have pos := (hc x y).pos_dist_of_ne hne
  have le2 := (within_iff_dist hc 2 x y).1 ((hx 2 ⟨u, (endpoints_cover_two h).1⟩) y)
  omega

/-- Count oriented pairs throughout. Dividing both counts by two yields the
unordered-pair identity of Theorem 3.1. -/
theorem center_distance_sum [Fintype V] {G : SimpleGraph V} {u v : V}
    (h : DomEdge G u v) :
    (∑ p ∈ centerPairs G, G.dist p.1 p.2) +
      (∑ p ∈ centerPairs G, (@ite ℕ (G.Adj p.1 p.2) (Classical.propDecidable _) 1 0)) =
      2 * (centerPairs G).card := by
  classical
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ _p ∈ centerPairs G, (2 : ℕ) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hp' : Central G p.1 ∧ Central G p.2 ∧ p.1 ≠ p.2 := by
        simpa [centerPairs] using hp
      rcases center_distance_one_or_two h hp'.1 hp'.2.2 with hd | hd
      · have he : G.Adj p.1 p.2 := SimpleGraph.dist_eq_one_iff_adj.1 hd
        simp [hd, he]
      · have he : ¬ G.Adj p.1 p.2 := fun he => by
          have hh := SimpleGraph.dist_eq_one_iff_adj.2 he
          omega
        simp [hd, he]
    _ = _ := by simp [Nat.mul_comm]

/-- The strict-average step, with the geometric input explicitly exposed.
This lemma does not assert that the input holds for every total dominating set. -/
theorem strict_mean_of_close_pair [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (hb : ∀ p ∈ centerPairs G, G.dist p.1 p.2 ≤ k)
    (hs : ∃ p ∈ centerPairs G, G.dist p.1 p.2 < k) :
    meanCenter G < k := by
  classical
  obtain ⟨p, hp, hlt⟩ := hs
  have hc : (0 : ℚ) < (centerPairs G).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨p, hp⟩
  unfold meanCenter
  apply (div_lt_iff₀ hc).2
  have hh : (∑ z ∈ centerPairs G, (G.dist z.1 z.2 : ℚ)) <
      ∑ _z ∈ centerPairs G, (k : ℚ) := by
    apply Finset.sum_lt_sum
    · intro z hz
      exact_mod_cast hb z hz
    · exact ⟨p, hp, by exact_mod_cast hlt⟩
  simpa [mul_comm] using hh

end CenterDomination
#print axioms CenterDomination.connected_of_domEdge
#print axioms CenterDomination.center_distance_one_or_two
#print axioms CenterDomination.center_distance_sum
#print axioms CenterDomination.strict_mean_of_close_pair


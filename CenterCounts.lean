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



namespace CenterDomination
variable {V : Type*}

/-- Handles the singleton-center convention as well as nonempty pair sets. -/
theorem strict_mean_of_all_dist_lt [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (hk : 0 < k) (h : ∀ p ∈ centerPairs G, G.dist p.1 p.2 < k) :
    meanCenter G < k := by
  classical
  by_cases he : (centerPairs G).card = 0
  · have empty := Finset.card_eq_zero.mp he
    have hkq : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
    simpa [meanCenter, empty] using hkq
  · obtain ⟨p, hp⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero he)
    exact strict_mean_of_close_pair (fun z hz => (h z hz).le) ⟨p, hp, h p hp⟩

/-- Metric reduction of the conjecture to the two alternatives supplied by
the paper's spanning-tree argument. The spanning-tree construction is not
an assumption-free consequence of this lemma. -/
theorem strict_mean_of_geometric_alternatives [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (hc : G.Connected) (hk : 0 < k)
    (h : (∃ w, Covers G (k - 1) w) ∨
      ((∃ w, Covers G k w) ∧
        ∃ x y, Central G x ∧ Central G y ∧ x ≠ y ∧ G.dist x y < k)) :
    meanCenter G < k := by
  classical
  rcases h with small | ⟨cover, x, y, cx, cy, ne, close⟩
  · apply strict_mean_of_all_dist_lt hk
    intro p hp
    have hp' : Central G p.1 ∧ Central G p.2 ∧ p.1 ≠ p.2 := by
      simpa [centerPairs] using hp
    have hb := (within_iff_dist hc (k - 1) p.1 p.2).1 ((hp'.1 (k - 1) small) p.2)
    omega
  · apply strict_mean_of_close_pair
    · intro p hp
      have hp' : Central G p.1 ∧ Central G p.2 ∧ p.1 ≠ p.2 := by
        simpa [centerPairs] using hp
      exact (within_iff_dist hc k p.1 p.2).1 ((hp'.1 k cover) p.2)
    · exact ⟨(x, y), by simp [centerPairs, cx, cy, ne], close⟩

/-- The remaining input is precisely the graph-geometric alternatives for
an arbitrary total dominating set; this is an interface, not a proof of
those alternatives. -/
theorem claim268_of_geometric_input [Fintype V] {G : SimpleGraph V}
    (geom : G.Connected → ∀ D : Finset V,
      (∀ x, ∃ d ∈ D, G.Adj d x) →
      0 < D.card ∧
      ((∃ w, Covers G (D.card - 1) w) ∨
        ((∃ w, Covers G D.card w) ∧
          ∃ x y, Central G x ∧ Central G y ∧ x ≠ y ∧ G.dist x y < D.card))) :
    Claim268 G := by
  intro hc D hd
  obtain ⟨hk, h⟩ := geom hc D hd
  exact strict_mean_of_geometric_alternatives hc hk h

end CenterDomination
#print axioms CenterDomination.strict_mean_of_all_dist_lt
#print axioms CenterDomination.strict_mean_of_geometric_alternatives
#print axioms CenterDomination.claim268_of_geometric_input


namespace CenterDomination
variable {V : Type*}

/-- Absence of a simple four-cycle. Adjacent vertices are distinct by
looplessness, so the two diagonal inequalities suffice. Chords are allowed. -/
def NoFourCycle (G : SimpleGraph V) : Prop :=
  ∀ a b c d : V, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
    a ≠ c → b ≠ d → False

private theorem exclusive_far {G : SimpleGraph V} {u v x y : V}
    (h : DomEdge G u v) (free : NoFourCycle G)
    (ux : G.Adj u x) (nvx : ¬ G.Adj v x) (xv : x ≠ v)
    (vy : G.Adj v y) (nuy : ¬ G.Adj u y) (yu : y ≠ u) :
    ¬ Short G x y := by
  rintro (eq | e | ⟨w, xw, wy⟩)
  · exact nuy (eq ▸ ux)
  · exact free u x y v ux e vy.symm h.1.symm yu.symm xv
  · have wv : w ≠ v := by
      intro eq
      exact nvx ((eq ▸ xw).symm)
    have wu : w ≠ u := by
      intro eq
      exact nuy (eq ▸ wy)
    rcases h.2 w with uw | vw
    · exact free u w y v uw wy vy.symm h.1.symm yu.symm wv
    · exact free v w x u vw xw.symm ux.symm h.1 xv.symm wu

private theorem not_cover_one_witness {G : SimpleGraph V} {u : V}
    (hn : ¬ Covers G 1 u) : ∃ y, y ≠ u ∧ ¬ G.Adj u y := by
  classical
  by_contra h
  apply hn
  intro y
  apply within_one.2
  by_cases e : u = y
  · exact Or.inl e
  · exact Or.inr (by
      by_contra na
      exact h ⟨y, e.symm, na⟩)

/-- A center in a graph with a dominating edge and no simple four-cycle
is a clique. This is the geometric part of the k = 2 ceiling result. -/
theorem center_clique_of_noFourCycle {G : SimpleGraph V} {u v : V}
    (h : DomEdge G u v) (free : NoFourCycle G) :
    ∀ x y, Central G x → Central G y → x ≠ y → G.Adj x y := by
  classical
  by_cases one : ∃ w, Covers G 1 w
  · intro x y cx _ ne
    exact (within_one.1 ((cx 1 one) y)).resolve_left ne
  · obtain ⟨s, sv, nvs⟩ := not_cover_one_witness
      (fun cov : Covers G 1 v => one ⟨v, cov⟩)
    obtain ⟨t, tu, nut⟩ := not_cover_one_witness
      (fun cov : Covers G 1 u => one ⟨u, cov⟩)
    have us := (h.2 s).resolve_right nvs
    have vt := (h.2 t).resolve_left nut
    have hu := (endpoints_cover_two h).1
    have common (x : V) (cx : Central G x) (xu : x ≠ u) (xv : x ≠ v) :
        G.Adj u x ∧ G.Adj v x := by
      constructor
      · by_contra nux
        have vx := (h.2 x).resolve_left nux
        have far := exclusive_far h free us nvs sv vx nux xu
        exact far (short_symm (within_two.1 ((cx 2 ⟨u, hu⟩) s)))
      · by_contra nvx
        have ux := (h.2 x).resolve_right nvx
        exact exclusive_far h free ux nvx xv vt nut tu
          (within_two.1 ((cx 2 ⟨u, hu⟩) t))
    intro x y cx cy ne
    by_cases xu : x = u
    · subst x
      by_cases yv : y = v
      · subst y
        exact h.1
      · exact (common y cy ne.symm yv).1
    · by_cases xv : x = v
      · subst x
        by_cases yu : y = u
        · subst y
          exact h.1.symm
        · exact (common y cy yu ne.symm).2
      · have xc := common x cx xu xv
        by_cases yu : y = u
        · subst y
          exact xc.1.symm
        · by_cases yv : y = v
          · subst y
            exact xc.2.symm
          · have yc := common y cy yu yv
            exact (free u x v y xc.1 xc.2.symm yc.2 yc.1.symm h.1.ne ne).elim

/-- The actual rational average is at most one, including an empty set of
distinct center pairs. Thus the paper's ceiling inequality holds for k=2. -/
theorem mean_center_le_one_of_noFourCycle [Fintype V] {G : SimpleGraph V}
    {u v : V} (h : DomEdge G u v) (free : NoFourCycle G) :
    meanCenter G ≤ 1 := by
  classical
  by_cases he : (centerPairs G).card = 0
  · have empty := Finset.card_eq_zero.mp he
    simp [meanCenter, empty]
  · have pos : (0 : ℚ) < (centerPairs G).card := by
      exact_mod_cast Nat.pos_of_ne_zero he
    unfold meanCenter
    apply (div_le_iff₀ pos).2
    have total : (∑ p ∈ centerPairs G, (G.dist p.1 p.2 : ℚ)) =
        ∑ _p ∈ centerPairs G, (1 : ℚ) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hp' : Central G p.1 ∧ Central G p.2 ∧ p.1 ≠ p.2 := by
        simpa [centerPairs] using hp
      rw [SimpleGraph.dist_eq_one_iff_adj.2
        (center_clique_of_noFourCycle h free p.1 p.2 hp'.1 hp'.2.1 hp'.2.2)]
      norm_num
    rw [total]
    simp

end CenterDomination
#print axioms CenterDomination.center_clique_of_noFourCycle
#print axioms CenterDomination.mean_center_le_one_of_noFourCycle

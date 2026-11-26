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
      exact h ⟨y, fun eq => e eq.symm, na⟩)

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
      simp
    rw [total]
    simp

end CenterDomination
#print axioms CenterDomination.center_clique_of_noFourCycle
#print axioms CenterDomination.mean_center_le_one_of_noFourCycle


namespace CenterDomination
variable {V : Type*}

/-- A covering ball gives a non-strict upper bound for the actual mean. -/
theorem mean_center_le_of_cover [Fintype V] {G : SimpleGraph V}
    (hc : G.Connected) {r : ℕ} (cover : ∃ w, Covers G r w) :
    meanCenter G ≤ r := by
  classical
  by_cases he : (centerPairs G).card = 0
  · have empty := Finset.card_eq_zero.mp he
    simp [meanCenter, empty]
  · have pos : (0 : ℚ) < (centerPairs G).card := by
      exact_mod_cast Nat.pos_of_ne_zero he
    unfold meanCenter
    apply (div_le_iff₀ pos).2
    have bound : (∑ p ∈ centerPairs G, (G.dist p.1 p.2 : ℚ)) ≤
        ∑ _p ∈ centerPairs G, (r : ℚ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' : Central G p.1 ∧ Central G p.2 ∧ p.1 ≠ p.2 := by
        simpa [centerPairs] using hp
      have le := (within_iff_dist hc r p.1 p.2).1 ((hp'.1 r cover) p.2)
      exact_mod_cast le
    simpa [mul_comm] using bound

/-- If no smaller ball covers the graph, every vertex with a radius-k
cover is central. No assumption that k is the graph radius is hidden. -/
theorem central_of_minimal_cover {G : SimpleGraph V} {k : ℕ} {x : V}
    (cov : Covers G k x) (minimal : ¬ ∃ w, Covers G (k - 1) w) :
    Central G x := by
  intro r hex
  by_cases ge : k ≤ r
  · exact covers_mono cov ge
  · obtain ⟨w, hw⟩ := hex
    exact False.elim (minimal ⟨w, covers_mono hw (by omega)⟩)

/-- Adjacent covering vertices suffice for the strict mean inequality.
This is the equality-case argument of the spanning-tree proof. -/
theorem strict_mean_of_adjacent_covers [Fintype V] {G : SimpleGraph V}
    (hc : G.Connected) {k : ℕ} (hk : 2 ≤ k) {u v : V}
    (edge : G.Adj u v) (cu : Covers G k u) (cv : Covers G k v) :
    meanCenter G < k := by
  classical
  apply strict_mean_of_geometric_alternatives hc (by omega)
  by_cases smaller : ∃ w, Covers G (k - 1) w
  · exact Or.inl smaller
  · refine Or.inr ⟨⟨u, cu⟩, u, v, central_of_minimal_cover cu smaller,
      central_of_minimal_cover cv smaller, edge.ne, ?_⟩
    rw [SimpleGraph.dist_eq_one_iff_adj.2 edge]
    omega

/-- A bounded walk in a spanning subgraph remains bounded in the original
graph. The proof works with the recursive walk predicate directly. -/
theorem within_of_edge_inclusion {T G : SimpleGraph V}
    (inc : ∀ x y, T.Adj x y → G.Adj x y)
    (n : ℕ) (x y : V) (hw : Within T n x y) : Within G n x y := by
  induction n generalizing x y with
  | zero => exact hw
  | succ n ih =>
    change (Within T n x y ∨ ∃ z, T.Adj x z ∧ Within T n z y) at hw
    change (Within G n x y ∨ ∃ z, G.Adj x z ∧ Within G n z y)
    rcases hw with h | ⟨z, e, h⟩
    · exact Or.inl (ih x y h)
    · exact Or.inr ⟨z, inc x z e, ih z y h⟩

/-- The spanning-tree construction need only produce either a smaller
covering ball or adjacent radius-k covering vertices in a spanning subgraph.
This proves the entire transfer and equality-case step, not existence of T. -/
theorem strict_mean_of_spanning_midpoints [Fintype V] {T G : SimpleGraph V}
    (hc : G.Connected) (inc : ∀ x y, T.Adj x y → G.Adj x y)
    {k : ℕ} (hk : 2 ≤ k)
    (mid : (∃ w, Covers T (k - 1) w) ∨
      ∃ u v, T.Adj u v ∧ Covers T k u ∧ Covers T k v) :
    meanCenter G < k := by
  rcases mid with ⟨w, cov⟩ | ⟨u, v, e, cu, cv⟩
  · exact strict_mean_of_geometric_alternatives hc (by omega)
      (Or.inl ⟨w, fun y => within_of_edge_inclusion inc _ _ _ (cov y)⟩)
  · exact strict_mean_of_adjacent_covers hc hk (inc u v e)
      (fun y => within_of_edge_inclusion inc _ _ _ (cu y))
      (fun y => within_of_edge_inclusion inc _ _ _ (cv y))

/-- Unconditional k=2 case of No. 268, for an actual dominating edge. -/
theorem mean_center_lt_two_of_domEdge [Fintype V] {G : SimpleGraph V}
    {u v : V} (h : DomEdge G u v) : meanCenter G < 2 :=
  strict_mean_of_adjacent_covers (connected_of_domEdge h) (by decide) h.1
    (endpoints_cover_two h).1 (endpoints_cover_two h).2

end CenterDomination
#print axioms CenterDomination.mean_center_le_of_cover
#print axioms CenterDomination.central_of_minimal_cover
#print axioms CenterDomination.strict_mean_of_adjacent_covers
#print axioms CenterDomination.within_of_edge_inclusion
#print axioms CenterDomination.strict_mean_of_spanning_midpoints
#print axioms CenterDomination.mean_center_lt_two_of_domEdge


namespace CenterDomination
variable {V : Type*}

/-- A finite connected spine, certified by an insertion history. Repeated
insertions are harmless. No connectivity or size assertion is assumed. -/
inductive SpineBuilt (G : SimpleGraph V) [DecidableEq V] : Finset V → Prop
  | single (x : V) : SpineBuilt G {x}
  | grow {K : Finset V} {x y : V} :
      SpineBuilt G K → x ∈ K → G.Adj x y → SpineBuilt G (insert y K)

private theorem spine_card_insert_le [DecidableEq V] (K : Finset V) (x : V) :
    (insert x K).card ≤ K.card + 1 := by
  by_cases hx : x ∈ K
  · simp [hx]
  · simp [hx]

private theorem spine_walk_cross {G : SimpleGraph V} {x y : V}
    (w : G.Walk x y) (P : V → Prop) (hx : P x) (hy : ¬ P y) :
    ∃ a b, P a ∧ ¬ P b ∧ G.Adj a b := by
  classical
  revert hx hy
  induction w with
  | nil =>
    intro hx hy
    exact (hy hx).elim
  | @cons a b c e w ih =>
    intro ha hc
    by_cases hb : P b
    · exact ih hb hc
    · exact ⟨a, b, ha, hb, e⟩

private theorem spine_insert_near [DecidableEq V] {G : SimpleGraph V}
    {K : Finset V} {x : V} (built : SpineBuilt G K)
    (near : x ∈ K ∨ ∃ y ∈ K, G.Adj y x) :
    SpineBuilt G (insert x K) := by
  rcases near with hx | ⟨y, hy, e⟩
  · simpa [hx] using built
  · exact SpineBuilt.grow built hy e

/-- The connected dominating spine exists with the parity-sensitive bound.
A processed set S is charged at most two vertices per member, minus two
for the initial edge, and minus one more for odd cardinality. A one-member
step adds at most one vertex; a two-member step adds at most four. -/
theorem exists_bounded_spine [DecidableEq V] {G : SimpleGraph V}
    (hc : G.Connected) (D : Finset V)
    (dom : ∀ x, ∃ d ∈ D, G.Adj d x) :
    ∃ K : Finset V, SpineBuilt G K ∧ D ⊆ K ∧
      K.card + 2 + D.card % 2 ≤ 2 * D.card := by
  classical
  obtain ⟨root, _⟩ := (SimpleGraph.connected_iff_exists_forall_reachable G).1 hc
  obtain ⟨a, ha, _⟩ := dom root
  obtain ⟨b, hb, ba⟩ := dom a
  let S0 : Finset V := insert a {b}
  have S0card : S0.card = 2 := by simp [S0, ba.ne.symm]
  have S0D : S0 ⊆ D := by
    intro x hx
    simp only [S0, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have S0built : SpineBuilt G S0 :=
    SpineBuilt.grow (SpineBuilt.single b) (by simp) ba
  have finish : ∀ fuel : ℕ, ∀ S K : Finset V,
      D.card - S.card = fuel → S.Nonempty → S ⊆ D → S ⊆ K →
      SpineBuilt G K → K.card + 2 + S.card % 2 ≤ 2 * S.card →
      ∃ L : Finset V, SpineBuilt G L ∧ D ⊆ L ∧
        L.card + 2 + D.card % 2 ≤ 2 * D.card := by
    intro fuel
    induction fuel using Nat.strong_induction_on with
    | h fuel ih =>
      intro S K hfuel hs hSD hSK built budget
      by_cases all : D ⊆ S
      · have eq : S.card = D.card :=
          Nat.le_antisymm (Finset.card_le_card hSD) (Finset.card_le_card all)
        exact ⟨K, built, fun _ hx => hSK (all hx), by simpa [eq] using budget⟩
      · have remaining : ∃ x ∈ D, x ∉ S := by
          by_contra hn
          apply all
          intro x hx
          by_contra hnx
          exact hn ⟨x, hx, hnx⟩
        by_cases near : ∃ x ∈ D, x ∉ S ∧
            (x ∈ K ∨ ∃ y ∈ K, G.Adj y x)
        · obtain ⟨x, hx, nx, close⟩ := near
          let S' := insert x S
          let K' := insert x K
          have cs : S'.card = S.card + 1 := by simp [S', nx]
          have ck : K'.card ≤ K.card + 1 := spine_card_insert_le K x
          have sd : S' ⊆ D := by
            intro z hz
            rcases Finset.mem_insert.1 hz with rfl | hz
            · exact hx
            · exact hSD hz
          have sk : S' ⊆ K' := by
            intro z hz
            rcases Finset.mem_insert.1 hz with rfl | hz
            · exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (hSK hz)
          have le := Finset.card_le_card sd
          exact ih (D.card - S'.card) (by omega) S' K' rfl
            ⟨x, Finset.mem_insert_self _ _⟩ sd sk
            (spine_insert_near built close) (by omega)
        · obtain ⟨x0, hx0, nx0⟩ := remaining
          obtain ⟨s0, hs0⟩ := hs
          let P : V → Prop := fun x => ∃ s ∈ S, x = s ∨ G.Adj s x
          have ps : P s0 := ⟨s0, hs0, Or.inl rfl⟩
          have px : ¬ P x0 := by
            rintro ⟨s, hs, e | e⟩
            · exact nx0 (e.symm ▸ hs)
            · exact near ⟨x0, hx0, nx0, Or.inr ⟨s, hSK hs, e⟩⟩
          obtain ⟨walk⟩ := hc s0 x0
          obtain ⟨y, z, py, nz, yz⟩ := spine_walk_cross walk P ps px
          obtain ⟨x, hx, xz⟩ := dom z
          have nx : x ∉ S := fun e => nz ⟨x, e, Or.inr xz⟩
          obtain ⟨t, ht, tx⟩ := dom x
          have nt : t ∉ S := fun e =>
            near ⟨x, hx, nx, Or.inr ⟨t, hSK e, tx⟩⟩
          have xt : x ≠ t := tx.ne.symm
          let S' := insert t (insert x S)
          let K' := insert t (insert x (insert z (insert y K)))
          have cs : S'.card = S.card + 2 := by
            simp [S', nx, nt, xt.symm] <;> omega
          have ck : K'.card ≤ K.card + 4 := by
            have h1 := spine_card_insert_le K y
            have h2 := spine_card_insert_le (insert y K) z
            have h3 := spine_card_insert_le (insert z (insert y K)) x
            have h4 := spine_card_insert_le (insert x (insert z (insert y K))) t
            dsimp [K']
            omega
          have sd : S' ⊆ D := by
            intro w hw
            rcases Finset.mem_insert.1 hw with rfl | hw
            · exact ht
            · rcases Finset.mem_insert.1 hw with rfl | hw
              · exact hx
              · exact hSD hw
          have sk : S' ⊆ K' := by
            intro w hw
            rcases Finset.mem_insert.1 hw with rfl | hw
            · exact Finset.mem_insert_self _ _
            · rcases Finset.mem_insert.1 hw with rfl | hw
              · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
              · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                  (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hSK hw))))
          have by' : SpineBuilt G (insert y K) := by
            apply spine_insert_near built
            obtain ⟨s, hs, e | e⟩ := py
            · exact Or.inl (e.symm ▸ hSK hs)
            · exact Or.inr ⟨s, hSK hs, e⟩
          have bz := SpineBuilt.grow by' (Finset.mem_insert_self y K) yz
          have bx := SpineBuilt.grow bz (Finset.mem_insert_self z (insert y K)) xz.symm
          have bt := SpineBuilt.grow bx (Finset.mem_insert_self x (insert z (insert y K))) tx.symm
          have le := Finset.card_le_card sd
          exact ih (D.card - S'.card) (by omega) S' K' rfl
            ⟨t, Finset.mem_insert_self _ _⟩ sd sk bt (by omega)
  exact finish (D.card - S0.card) S0 S0 rfl
    ⟨a, Finset.mem_insert_self _ _⟩ S0D (fun _ hx => hx) S0built (by omega)

end CenterDomination
#print axioms CenterDomination.exists_bounded_spine

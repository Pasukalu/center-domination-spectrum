import CenterCounts

namespace CenterDomination
/-- The two vertices outside the center are shadow and pendant. -/
inductive Fan (S : Type*) where
  | hub | shadow | pendant | spoke (s : S)
  deriving DecidableEq, Fintype

namespace Fan
variable {S : Type*} {H : SimpleGraph S}

def rel (H : SimpleGraph S) : Fan S → Fan S → Prop
  | .hub, .pendant | .pendant, .hub => True
  | .hub, .spoke _ | .spoke _, .hub => True
  | .shadow, .spoke _ | .spoke _, .shadow => True
  | .spoke x, .spoke y => H.Adj x y
  | _, _ => False

def graph (H : SimpleGraph S) : SimpleGraph (Fan S) where
  Adj := rel H
  symm := by
    intro x y h
    cases x <;> cases y <;> first | exact h | exact H.symm h
  loopless := ⟨by intro x; cases x <;> simp [rel]⟩

theorem pair_dominates (a : S) : DomEdge (graph H) .hub (.spoke a) := by
  refine ⟨True.intro, ?_⟩
  intro x
  cases x with
  | hub => exact Or.inr True.intro
  | shadow => exact Or.inr True.intro
  | pendant => exact Or.inl True.intro
  | spoke s => exact Or.inl True.intro

theorem far : ¬ Short (graph H) .shadow .pendant := by
  rintro (h | h | ⟨z, h₁, h₂⟩)
  · cases h
  · exact h
  · cases z <;> simp_all [graph, rel]

theorem spoke_cover (a : S) : Covers (graph H) 2 (.spoke a) := by
  intro y
  apply within_two.2
  cases y with
  | hub => exact Or.inr (Or.inl True.intro)
  | shadow => exact Or.inr (Or.inl True.intro)
  | pendant => exact Or.inr (Or.inr ⟨.hub, True.intro, True.intro⟩)
  | spoke s => exact Or.inr (Or.inr ⟨.hub, True.intro, True.intro⟩)

theorem centers (a : S) (x : Fan S) :
    Central (graph H) x ↔ x = .hub ∨ ∃ s, x = .spoke s := by
  have hh := (endpoints_cover_two (pair_dominates (H := H) a)).1
  have hn : ¬ ∃ w, Covers (graph H) 1 w := by
    rintro ⟨w, hw⟩
    exact far (short_of_one hw .shadow .pendant)
  constructor
  · intro hc
    have hx := hc 2 ⟨.hub, hh⟩
    cases x with
    | hub => exact Or.inl rfl
    | spoke s => exact Or.inr ⟨s, rfl⟩
    | shadow => exact False.elim (far (within_two.1 (hx .pendant)))
    | pendant => exact False.elim (far (short_symm (within_two.1 (hx .shadow))))
  · rintro (rfl | ⟨s, rfl⟩)
    · exact central_of_two hh hn
    · exact central_of_two (spoke_cover _) hn

theorem spoke_distance (x y : S) (hne : x ≠ y) :
    (graph H).dist (.spoke x) (.spoke y) =
      @ite ℕ (H.Adj x y) (Classical.propDecidable _) 1 2 := by
  classical
  obtain hd | hd := center_distance_one_or_two (pair_dominates (H := H) x)
    ((centers x _).2 (Or.inr ⟨x, rfl⟩)) (show spoke x ≠ spoke y by simpa)
  · have he' : (graph H).Adj (.spoke x) (.spoke y) := SimpleGraph.dist_eq_one_iff_adj.1 hd
    have he : H.Adj x y := he'
    simp [hd, he]
  · have he : ¬ H.Adj x y := fun e => by
      have he' : (graph H).Adj (.spoke x) (.spoke y) := e
      have hd' := SimpleGraph.dist_eq_one_iff_adj.2 he'
      omega
    simp [hd, he]

theorem hub_distance (s : S) : (graph H).dist .hub (.spoke s) = 1 :=
  SimpleGraph.dist_eq_one_iff_adj.2 True.intro

end Fan
end CenterDomination
#print axioms CenterDomination.Fan.pair_dominates
#print axioms CenterDomination.Fan.centers
#print axioms CenterDomination.Fan.spoke_distance
#print axioms CenterDomination.Fan.hub_distance



namespace CenterDomination
namespace Fan
variable {S : Type*} {H : SimpleGraph S}

/-- The hub and all spokes form the actual finite center. -/
theorem center_card [Fintype S] (a : S) :
    (centerVertices (graph H)).card = Fintype.card S + 1 := by
  classical
  let F : Finset (Fan S) := Finset.univ.image Fan.spoke
  have eq : centerVertices (graph H) = insert .hub F := by
    ext x
    simp only [centerVertices, Finset.mem_filter, Finset.mem_univ, true_and,
      centers a, Finset.mem_insert, F, Finset.mem_image]
    simp only [Finset.mem_univ, true_and]
    exact or_congr Iff.rfl (exists_congr fun _ => eq_comm)
  have notHub : (.hub : Fan S) ∉ F := by simp [F]
  rw [eq, Finset.card_insert_of_notMem notHub]
  simp [F, Finset.card_image_of_injective, Fan.spoke.inj]

/-- Count the two orientations of each hub-spoke edge and each spoke edge
in the actual ambient center, then divide the equality by two. -/
theorem center_edge_card [Fintype S] (a : S) :
    centerEdgeCount (graph H) = Fintype.card S + Nat.card H.edgeSet := by
  classical
  let A : Finset (S × S) := Finset.univ.filter (fun p => H.Adj p.1 p.2)
  let L : Finset (Fan S × Fan S) := Finset.univ.image (fun s : S => (.hub, .spoke s))
  let R : Finset (Fan S × Fan S) := Finset.univ.image (fun s : S => (.spoke s, .hub))
  let E : Finset (Fan S × Fan S) := A.image (fun p => (.spoke p.1, .spoke p.2))
  have eq : centerRelPairs (graph H) (graph H).Adj = L ∪ R ∪ E := by
    ext p
    obtain ⟨x,y⟩ := p
    cases x <;> cases y <;>
      simp [centerRelPairs, centers a, graph, rel, L, R, E, A]
  have dLR : Disjoint L R := by
    rw [Finset.disjoint_left]
    intro p hp hq
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.1 hp
    simpa [R] using hq
  have dE : Disjoint (L ∪ R) E := by
    rw [Finset.disjoint_left]
    intro p hp hq
    rcases Finset.mem_union.1 hp with hl | hr
    · obtain ⟨s, _, rfl⟩ := Finset.mem_image.1 hl
      simpa [E] using hq
    · obtain ⟨s, _, rfl⟩ := Finset.mem_image.1 hr
      simpa [E] using hq
  have lc : L.card = Fintype.card S := by
    unfold L
    rw [Finset.card_image_of_injective _ (fun x y e => Fan.spoke.inj (congrArg Prod.snd e))]
    simp
  have rc : R.card = Fintype.card S := by
    unfold R
    rw [Finset.card_image_of_injective _ (fun x y e => Fan.spoke.inj (congrArg Prod.fst e))]
    simp
  have ec : E.card = A.card := by
    unfold E
    apply Finset.card_image_of_injective
    intro x y e
    exact Prod.ext (Fan.spoke.inj (congrArg Prod.fst e)) (Fan.spoke.inj (congrArg Prod.snd e))
  have ac : A.card = 2 * Nat.card H.edgeSet := by
    dsimp [A]
    rw [← SimpleGraph.two_mul_card_edgeFinset, Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card]
  have count := center_adj_pairs_card (graph H)
  rw [eq, Finset.card_union_of_disjoint dE, Finset.card_union_of_disjoint dLR,
    lc, rc, ec, ac] at count
  omega

/-- Exactly the two named vertices are outside the center. -/
theorem ambient_card [Fintype S] (a : S) :
    Fintype.card (Fan S) = (centerVertices (graph H)).card + 2 := by
  classical
  let F : Finset (Fan S) := Finset.univ.image Fan.spoke
  have eq : (Finset.univ : Finset (Fan S)) = insert .hub (insert .shadow (insert .pendant F)) := by
    ext x
    cases x <;> simp [F]
  have p : (.pendant : Fan S) ∉ F := by simp [F]
  have q : (.shadow : Fan S) ∉ insert .pendant F := by simp [F]
  have h : (.hub : Fan S) ∉ insert .shadow (insert .pendant F) := by simp [F]
  have card := congrArg Finset.card eq
  rw [Finset.card_insert_of_notMem h, Finset.card_insert_of_notMem q,
    Finset.card_insert_of_notMem p] at card
  have fc : F.card = Fintype.card S := by
    simp [F, Finset.card_image_of_injective, Fan.spoke.inj]
  rw [Finset.card_univ, fc] at card
  rw [center_card a]
  omega

end Fan

/-- Every admissible edge count is realized by a finite simple graph:
choose an arbitrary subset of the complete graph's edge finset. -/
theorem exists_graph_with_edge_count (n t : ℕ) (h : t ≤ n.choose 2) :
    ∃ H : SimpleGraph (Fin n), Nat.card H.edgeSet = t := by
  classical
  let K : SimpleGraph (Fin n) := ⊤
  have bound : t ≤ K.edgeFinset.card := by
    simpa [K, SimpleGraph.card_edgeFinset_top_eq_card_choose_two] using h
  obtain ⟨s, sub, card⟩ := Finset.exists_subset_card_eq bound
  let H : SimpleGraph (Fin n) := SimpleGraph.fromEdgeSet (↑s : Set (Sym2 (Fin n)))
  have edges : H.edgeFinset = s := by
    ext e
    rw [SimpleGraph.mem_edgeFinset]
    change e ∈ (SimpleGraph.fromEdgeSet (↑s : Set (Sym2 (Fin n)))).edgeSet ↔ e ∈ s
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    constructor
    · intro he
      exact he.1
    · intro he
      exact ⟨he, SimpleGraph.not_isDiag_of_mem_edgeFinset (sub he)⟩
  refine ⟨H, ?_⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, edges, card]

/-- Every integer in the predicted edge interval has a realization on
exactly m+2 vertices, with a dominating edge and the actual rational mean. -/
theorem spectrum_attainment (m j : ℕ) (hm : 2 ≤ m)
    (lo : m - 1 ≤ j) (hi : j ≤ m.choose 2) :
    ∃ G : SimpleGraph (Fan (Fin (m - 1))),
      (∃ a b, DomEdge G a b) ∧ (centerVertices G).card = m ∧
      Fintype.card (Fan (Fin (m - 1))) = m + 2 ∧
      centerEdgeCount G = j ∧ meanCenter G = 2 - (j : ℚ) / (m.choose 2 : ℚ) := by
  classical
  have em : m - 1 + 1 = m := by omega
  have choose : m.choose 2 = (m - 1) + (m - 1).choose 2 := by
    conv_lhs => rw [← em]
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
  obtain ⟨H, edges⟩ := exists_graph_with_edge_count (m - 1) (j - (m - 1)) (by omega)
  let a : Fin (m - 1) := ⟨0, by omega⟩
  let G := Fan.graph H
  have de : DomEdge G .hub (.spoke a) := Fan.pair_dominates a
  have cm : (centerVertices G).card = m := by
    simpa [G, em] using Fan.center_card (H := H) a
  have ce : centerEdgeCount G = j := by
    have h := Fan.center_edge_card (H := H) a
    rw [Fintype.card_fin, edges] at h
    change centerEdgeCount G = j
    omega
  refine ⟨G, ⟨_, _, de⟩, cm, ?_, ce, ?_⟩
  · simpa [G, cm] using Fan.ambient_card (H := H) a
  · rw [center_mean_edge_formula de (by omega), cm, ce]

end CenterDomination
#print axioms CenterDomination.Fan.center_card
#print axioms CenterDomination.Fan.center_edge_card
#print axioms CenterDomination.Fan.ambient_card
#print axioms CenterDomination.exists_graph_with_edge_count
#print axioms CenterDomination.spectrum_attainment


namespace CenterDomination

/-- The full set of attainable rational means on finite graphs with
a dominating edge and m central vertices, in the universe of Fin n. -/
theorem spectrum_exact (m : ℕ) (hm : 2 ≤ m) (a : ℚ) :
    (∃ (W : Type) (fin : Fintype W) (G : SimpleGraph W),
      (∃ u v, DomEdge G u v) ∧ (@centerVertices W fin G).card = m ∧
      @meanCenter W fin G = a) ↔
    ∃ j : ℕ, m - 1 ≤ j ∧ j ≤ m.choose 2 ∧
      a = 2 - (j : ℚ) / (m.choose 2 : ℚ) := by
  classical
  constructor
  · rintro ⟨W, fin, G, ⟨u,v,h⟩, cm, mean⟩
    letI : Fintype W := fin
    have hm' : 2 ≤ (centerVertices G).card := by rw [cm]; exact hm
    obtain ⟨j, lo, hi, eq⟩ := spectrum_necessity h hm'
    rw [cm] at lo hi eq
    exact ⟨j, lo, hi, mean.symm.trans eq⟩
  · rintro ⟨j, lo, hi, rfl⟩
    obtain ⟨G, de, cm, _, _, eq⟩ := spectrum_attainment m j hm lo hi
    exact ⟨Fan (Fin (m - 1)), inferInstance, G, de, cm, eq⟩

/-- The simplified sharp maximum is attained on exactly m+2 vertices. -/
theorem spectrum_max_attained (m : ℕ) (hm : 2 ≤ m) :
    ∃ G : SimpleGraph (Fan (Fin (m - 1))),
      (∃ u v, DomEdge G u v) ∧ (centerVertices G).card = m ∧
      Fintype.card (Fan (Fin (m - 1))) = m + 2 ∧
      meanCenter G = 2 - 2 / (m : ℚ) ∧ (centerGraph G).IsTree := by
  have em : m - 1 + 1 = m := by omega
  have choose : m.choose 2 = (m - 1) + (m - 1).choose 2 := by
    conv_lhs => rw [← em]
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
  obtain ⟨G, ⟨u, v, de⟩, cm, card, _, mean⟩ :=
    spectrum_attainment m (m - 1) hm (by omega) (by omega)
  have eq : meanCenter G = 2 - 2 / (m : ℚ) := by
    rw [mean, minimum_edge_density m hm]
  have hm' : 2 ≤ (centerVertices G).card := by rw [cm]; exact hm
  have tree := (spectrum_max_iff_tree de hm').1 (by simpa only [cm] using eq)
  exact ⟨G, ⟨u,v,de⟩, cm, card, eq, tree⟩

end CenterDomination
#print axioms CenterDomination.spectrum_exact
#print axioms CenterDomination.spectrum_max_attained

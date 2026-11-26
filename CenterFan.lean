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


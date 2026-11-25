import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-7864`: the circuit has a second gate, or it does not. -/
theorem PEqualNP.Outside.R_meta_7864_1 :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : DecidableRel x2.Adj) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : Fin x1) (x6 : x2.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → PEqualNP.TopForm.junk x2 x4 = ∅ → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x4.gates[1]? = Option.some g) → PEqualNP.TopForm.Ustar x2 x4 = ∅) →
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : DecidableRel x2.Adj) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : Fin x1) (x6 : x2.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → PEqualNP.TopForm.junk x2 x4 = ∅ → ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x4.gates[1]? = Option.some g) → PEqualNP.TopForm.Ustar x2 x4 = ∅) →
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : Fin x1) (x6 : x2.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → PEqualNP.TopForm.junk x2 x4 = ∅ → PEqualNP.TopForm.Ustar x2 x4 = ∅) := by
  classical
  intro h1 h2 x1 x2 x3 x4
  intros
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x4.gates[1]? = Option.some g)
  · apply h1 <;> assumption
  · apply h2 <;> assumption

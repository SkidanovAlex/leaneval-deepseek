import Mathlib
import Submission.Work.KMTAreas.A8Defs

namespace Work.KMTAreas.A8

open scoped BigOperators

/-- The `varK` summand attached to a single clamped chain pattern `p : Chain K`, extracted as a
standalone function so that `Work.KMTAreas.varK r K a` is *definitionally* the `sup'` of it over
`Finset.univ`. -/
private noncomputable def varKterm (r : NNReal) (a : ℕ → ℂ) {K : ℕ}
    (p : Work.KMTAreas.Chain K) : ℝ :=
  (∑ i : Fin p.1.1, ‖a (p.2.1 i.succ) - a (p.2.1 i.castSucc)‖ ^ (r : ℝ)) ^ (1 / (r : ℝ))

/-- `varK` is by definition the supremum of `varKterm` over the (nonempty, finite) set of chain
patterns. -/
private lemma varK_eq_sup' (r : NNReal) (K : ℕ) (a : ℕ → ℂ) :
    Work.KMTAreas.varK r K a
      = (Finset.univ : Finset (Work.KMTAreas.Chain K)).sup' Finset.univ_nonempty
          (varKterm r a) :=
  rfl

/-- A chain pattern with all indices `≤ K` is also a chain pattern with all indices `≤ K'` when
`K ≤ K'`: the canonical inclusion `Chain K → Chain K'`. -/
private def chainEmb {K K' : ℕ} (h : K ≤ K') (p : Work.KMTAreas.Chain K) :
    Work.KMTAreas.Chain K' :=
  ⟨⟨p.1.1, by have := p.1.2; omega⟩,
   ⟨fun i => ⟨(p.2.1 i).1, by have := (p.2.1 i).2; omega⟩,
    fun i j hij => p.2.2 hij⟩⟩

/-- The `varK` summand is unaffected by the inclusion `Chain K → Chain K'`. -/
private lemma chainEmb_term (r : NNReal) (a : ℕ → ℂ) {K K' : ℕ} (h : K ≤ K')
    (p : Work.KMTAreas.Chain K) :
    varKterm r a p = varKterm r a (chainEmb h p) := by
  simp only [varKterm, chainEmb, Fin.val_mk]
  rfl

theorem varK_basic (r : NNReal) (a : ℕ → ℂ) :
    (∀ K, 0 ≤ Work.KMTAreas.varK r K a) ∧
    (∀ K K', K ≤ K' → Work.KMTAreas.varK r K a ≤ Work.KMTAreas.varK r K' a) := by
  constructor
  · -- Nonnegativity: `varK` is a supremum of nonnegative terms over a nonempty finite set.
    intro K
    rw [varK_eq_sup' r K a]
    rw [Finset.le_sup'_iff]
    refine ⟨⟨⟨0, Nat.succ_pos K⟩, fun _ => 0, fun _ _ _ => le_rfl⟩, Finset.mem_univ _, ?_⟩
    exact Real.rpow_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _) _
  · -- Monotonicity in `K`: every chain pattern for `K` maps to one for `K'` with the same term.
    intro K K' hKK'
    rw [varK_eq_sup' r K a, varK_eq_sup' r K' a]
    rw [Finset.sup'_le_iff]
    intro p _
    rw [chainEmb_term r a hKK' p]
    exact Finset.le_sup' (varKterm r a) (Finset.mem_univ (chainEmb hKK' p))

end Work.KMTAreas.A8

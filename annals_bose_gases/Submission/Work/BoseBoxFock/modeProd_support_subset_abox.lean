import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.SliceBadAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- **The mode product is supported in the configuration box.**
`modeProd e d α` is the finite sum over labellings `σ : Fin d → Fin m` with `modeMult σ = α` of the products `∏ j, e (σ j) (x j)`. If any coordinate `x j` lies outside `acube ℓ = boxL ℓ`, then `e l (x j) = 0` for every mode `l` (`hsupp`), hence every term vanishes, so `support (modeProd e d α) ⊆ abox d ℓ`.
⚠ the file must NOT import `Submission.Work.BoseBoxFock.slotSum_sectorPointwise` (a `update_pairCoord` clash). -/
theorem modeProd_support_subset_abox {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (d : ℕ) (α : Fin m →₀ ℕ) :
    Function.support (Work.BoseDict.modeProd e d α) ⊆ Submission.BoseGases.abox d ℓ := by
  intro x hx
  rw [Submission.BoseGases.mem_abox_iff]
  intro i
  -- `x i` cannot lie outside the box: otherwise every summand of `modeProd` vanishes.
  by_contra hi
  have hout : x i ∉ Work.BoseK15.corpusBox.boxL ℓ :=
    fun h => hi ((corpusBox_boxL_eq_acube hℓ).le h)
  have hzero : Work.BoseDict.modeProd e d α x = 0 := by
    rw [Work.BoseDict.modeProd]
    refine Finset.sum_eq_zero (fun σ _ => ?_)
    have he : e (σ i) (x i) = 0 := by
      by_contra hne
      exact hout (hsupp (σ i) (Function.mem_support.mpr hne))
    rw [Finset.prod_eq_zero (Finset.mem_univ i) he, mul_zero]
  exact hx hzero

end Work.BoseBoxFock

/-
# The global cutoff on a polydisc, and globalisation of locally smooth data

`polydiscCut A B` is a smooth function on `ℂⁿ` which is `1` on `polydisc 0 A`, vanishes
outside `polydisc 0 B` (componentwise `0 < A j < B j`) and is bounded by `1`.

The point is `contDiff_polydiscCut_mul`: if `f` is `C^m` on an open set `U` containing the
open polydisc `polydisc 0 B` which contains the support of `χ`, then `z ↦ χ z * f z` is
*globally* `C^m`.  This is what turns a datum which is only smooth on a polydisc into a
globally smooth one.
-/
import Mathlib
import Submission.Work.NN.Ratio.Cut
import Submission.Work.CR.Flat.Holder.holderNorm_zero_comp_le
import Submission.Work.CR.Flat.Holder.holderNorm_smul

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set MeasureTheory Filter

namespace Work.NN.Ratio

/-- The product of one-variable flexible cutoffs: `1` on `polydisc 0 A`, `0` outside
`polydisc 0 B`. -/
def polydiscCut {n : ℕ} (A B : Fin n → ℝ) : (Fin n → ℂ) → ℂ :=
  fun z => ∏ j : Fin n, rCut (A j) (B j) (z j)

private lemma contDiff_single_rCut {n : ℕ} (A B : Fin n → ℝ) (j : Fin n) :
    ContDiff ℝ ∞ (fun z : Fin n → ℂ => rCut (A j) (B j) (z j)) :=
  (contDiff_rCut (A j) (B j)).comp (contDiff_apply ℝ ℂ j)

lemma contDiff_polydiscCut {n : ℕ} (A B : Fin n → ℝ) : ContDiff ℝ ∞ (polydiscCut A B) := by
  rw [show polydiscCut A B = fun z : Fin n → ℂ => ∏ j : Fin n, rCut (A j) (B j) (z j) from rfl]
  revert A B
  refine Finset.induction_on (Finset.univ : Finset (Fin n)) ?_ ?_
  · intro A B
    simp only [Finset.prod_empty]
    exact contDiff_const
  · intro a s ha ih A B
    simp only [Finset.prod_insert ha]
    exact (contDiff_single_rCut A B a).mul (ih A B)

lemma polydiscCut_eq_one {n : ℕ} {A B : Fin n → ℝ} (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, A j < B j)
    {z : Fin n → ℂ} (hz : ∀ j, ‖z j‖ ≤ A j) : polydiscCut A B z = 1 := by
  rw [polydiscCut, Finset.prod_eq_one]
  intro j _
  exact rCut_eq_one_of_norm_le (hA j) (hB j) (hz j)

lemma polydiscCut_eq_zero {n : ℕ} {A B : Fin n → ℝ} (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, A j < B j)
    {z : Fin n → ℂ} (hz : ∃ j, B j ≤ ‖z j‖) : polydiscCut A B z = 0 := by
  obtain ⟨j, hj⟩ := hz
  rw [polydiscCut]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (rCut_eq_zero_of_le_norm (hA j) (hB j) hj)

lemma polydiscCut_ne_zero_imp {n : ℕ} {A B : Fin n → ℝ} (hA : ∀ j, 0 ≤ A j)
    (hB : ∀ j, A j < B j) {z : Fin n → ℂ} (hz : polydiscCut A B z ≠ 0) :
    ∀ j, ‖z j‖ < B j := by
  intro j
  by_contra hcon
  exact hz (polydiscCut_eq_zero hA hB ⟨j, not_lt.mp hcon⟩)

private lemma norm_prod_le_one {n : ℕ} (g : Fin n → ℝ) (h0 : ∀ j, 0 ≤ g j)
    (h1 : ∀ j, g j ≤ 1) : (∏ j : Fin n, g j) ≤ 1 := by
  revert h0 h1
  refine Finset.induction_on (Finset.univ : Finset (Fin n)) ?_ ?_
  · intro _ _; simp
  · intro a s ha ih h0 h1
    rw [Finset.prod_insert ha]
    refine mul_le_one₀ (h1 a) ?_ (ih (fun j => h0 j) (fun j => h1 j))
    exact Finset.prod_nonneg fun j _ => h0 j

lemma norm_polydiscCut_le_one {n : ℕ} (A B : Fin n → ℝ) (z : Fin n → ℂ) :
    ‖polydiscCut A B z‖ ≤ 1 := by
  rw [polydiscCut, norm_prod]
  exact norm_prod_le_one (fun j => ‖rCut (A j) (B j) (z j)‖)
    (fun j => norm_nonneg _) (fun j => norm_rCut_le_one _ _ _)

/-- The (closed) support of the polydisc cutoff is contained in the closed polydisc of
multi-radius `B`. -/
lemma tsupport_polydiscCut_subset {n : ℕ} {A B : Fin n → ℝ} (hA : ∀ j, 0 ≤ A j)
    (hB : ∀ j, A j < B j) :
    tsupport (polydiscCut A B) ⊆ {z : Fin n → ℂ | ∀ j, ‖z j‖ ≤ B j} := by
  rw [tsupport]
  refine closure_minimal ?_ ?_
  · rw [Function.support_subset_iff]
    intro z hz
    exact fun j => le_of_lt (polydiscCut_ne_zero_imp hA hB hz j)
  · have hset : {z : Fin n → ℂ | ∀ j, ‖z j‖ ≤ B j} = ⋂ j, {z | ‖z j‖ ≤ B j} := by
      ext z; simp
    rw [hset]
    exact isClosed_iInter fun j => isClosed_le ((continuous_apply j).norm) continuous_const

/-- **Globalisation.**  If `f` is `C^m` on an open set `U` containing the (closed) support of the
smooth function `χ`, then `z ↦ χ z * f z` is globally `C^m`. -/
theorem contDiff_mul_of_tsupport_subset {n : ℕ} {m : ℕ} {χ f : (Fin n → ℂ) → ℂ}
    (hχ : ContDiff ℝ ∞ χ) {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hχU : tsupport χ ⊆ U)
    (hf : ContDiffOn ℝ m f U) : ContDiff ℝ m (fun z => χ z * f z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ U
  · have hfz : ContDiffAt ℝ m f z := hf.contDiffAt (hU.mem_nhds hz)
    exact ((hχ.contDiffAt).of_le (le_infty m)).mul hfz
  · have hcomp : (tsupport χ)ᶜ ∈ 𝓝 z :=
      (isClosed_tsupport χ).compl_mem_nhds (fun h => hz (hχU h))
    have hev : (fun z => χ z * f z) =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
      filter_upwards [hcomp] with w hw
      have hw0 : χ w = 0 := by
        by_contra h
        exact hw (subset_tsupport χ (Function.mem_support.mpr h))
      rw [hw0, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- The globalisation lemma in the form used for the polydisc cutoff. -/
theorem contDiff_polydiscCut_mul {n : ℕ} {m : ℕ} {A B : Fin n → ℝ} (hA : ∀ j, 0 ≤ A j)
    (hB : ∀ j, A j < B j) {f : (Fin n → ℂ) → ℂ} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (hUB : ∀ z, (∀ j, ‖z j‖ ≤ B j) → z ∈ U)
    (hf : ContDiffOn ℝ m f U) :
    ContDiff ℝ m (fun z => polydiscCut A B z * f z) :=
  contDiff_mul_of_tsupport_subset (contDiff_polydiscCut A B) hU
    (fun z hz => hUB z (tsupport_polydiscCut_subset hA hB hz)) hf

end Work.NN.Ratio

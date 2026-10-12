import ChallengeDeps
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.latRow_le_sharp_ae
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/All/sharpRowLabNAe.lean` — the sharp finite-cube weighted lattice row
at an a.e.-nonnegative `W₁`

This is `Work.BoseFixR.All.sharpRowLabN` with the pointwise hypothesis `0 ≤ W1fun v h ℓ` replaced by
the a.e. hypothesis `0 ≤ᵐ[volume] W1fun v h ℓ` (the only form available in the corpus:
`W1fun = wScaled ℓ (g0 v h)` and only `0 ≤ᵐ g0` is known).  The proof is identical to
`sharpRowLabN`'s — the lattice row, the cube sub-summing and the un-halving are all
nonnegativity-free — except that the input chain now enters through the a.e. full-lattice row
`Work.BoseFixR.lwsq_lattice_row_sharp_ae`.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR.All

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox
open Work.BoseBoxFix Work.BoseBoxFock Work.BoseB7 Work.BoseB7A

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The sharp weighted sampling row on the honest cube** (constant `1`, a.e.-nonnegativity
form of `W₁`). -/
theorem sharpRowLabNAe {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : BoseGases.IsRadial v) {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) (hreg : 100 * R ≤ ℓ)
    (hW : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ))
    (hWae : 0 ≤ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))]
      (Work.BoseFixR.W1fun v h ℓ))
    (N : ℕ) :
    (∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)
            (Work.BoseBoxFock.kmomLab ℓ N k)) ^ 2
          / ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2)
      ≤ 2 * ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
          ∫ q : EuclideanSpace ℝ (Fin 3),
            (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2) := by
  classical
  have hsum := Work.BoseFixR.chat_sq_div_summable h hv hvrad hR hℓ hv_supp hRℓ
  have hkey := Work.BoseFixR.lwsq_lattice_row_sharp_ae h hv hvrad hR hℓ hv_supp hRℓ hreg hW hWae
  set F : (Fin 3 → ℤ) → ℝ := fun m => if m = 0 then 0
      else (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)
          (ℓ⁻¹ • Work.BoseB4.vec m)) ^ 2
        / ‖ℓ⁻¹ • Work.BoseB4.vec m‖ ^ 2 with hF
  set T : Finset (Fin 3 → ℤ) :=
    ((Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0).image
      (Work.BoseBoxFock.labVec N) with hT
  have hFnn : ∀ m : Fin 3 → ℤ, 0 ≤ F m := by
    intro m
    rw [hF]
    by_cases hm : m = 0
    · simp [hm]
    · simp only [hm, if_false]
      exact div_nonneg (sq_nonneg _) (by positivity)
  have hlabVec_zero : Work.BoseBoxFock.labVec N (0 : Work.BoseBoxFock.Lab N) = 0 := by
    funext i
    simp [Work.BoseBoxFock.labVec]
  have hT0 : (0 : Fin 3 → ℤ) ∉ T := by
    rw [hT, Finset.mem_image]
    rintro ⟨k, hk, hk0⟩
    rw [Finset.mem_erase] at hk
    exact hk.1 (Work.BoseFixR.labVec_injective N (by rw [hk0, hlabVec_zero]))
  have hsumF : Summable F := by rw [hF]; exact hsum
  have hTsummand : ∀ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
      (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)
          (Work.BoseBoxFock.kmomLab ℓ N k)) ^ 2
          / (2 * ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2)
        = (1 / 2) * F (Work.BoseBoxFock.labVec N k) := by
    intro k hk
    have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
    have hlv : Work.BoseBoxFock.labVec N k ≠ 0 := by
      intro hh
      exact hk0 (Work.BoseFixR.labVec_injective N (by rw [hh, hlabVec_zero]))
    rw [hF]
    simp only [hlv, if_false]
    rw [Work.BoseBoxFock.GramLab.kmomLab_eq_smul_vec]
    ring
  have hcube : (∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)
            (Work.BoseBoxFock.kmomLab ℓ N k)) ^ 2
          / (2 * ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2))
      = (1 / 2) * ∑ m ∈ T, F m := by
    rw [hT, Finset.mul_sum]
    rw [Finset.sum_image (f := fun m => (1 / 2) * F m)
      (g := Work.BoseBoxFock.labVec N)
      (fun x _ y _ hxy => Work.BoseFixR.labVec_injective N hxy)]
    exact Finset.sum_congr rfl fun k hk => hTsummand k hk
  have hle : (∑ m ∈ T, F m) ≤ ∑' m : Fin 3 → ℤ, F m :=
    Summable.sum_le_tsum T (fun i _ => hFnn i) hsumF
  have hInt : 0 ≤ ∫ q : E3,
      (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2) :=
    integral_nonneg fun q => div_nonneg (sq_nonneg _) (by positivity)
  have hkey' : (∑' m : Fin 3 → ℤ, F m) ≤ 2 * ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
      ∫ q : E3, (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2) := by
    rw [hF]; exact hkey
  -- the *halved* finite-cube row with constant `1`
  have hhalf : (∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)
            (Work.BoseBoxFock.kmomLab ℓ N k)) ^ 2
          / (2 * ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2))
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
          ∫ q : E3, (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2) := by
    calc (∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
          (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)
              (Work.BoseBoxFock.kmomLab ℓ N k)) ^ 2
            / (2 * ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2))
        = (1 / 2) * ∑ m ∈ T, F m := hcube
      _ ≤ (1 / 2) * ∑' m : Fin 3 → ℤ, F m :=
          mul_le_mul_of_nonneg_left hle (by norm_num)
      _ ≤ (1 / 2) * (2 * ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
            ∫ q : E3, (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2
              / (2 * ‖q‖ ^ 2)) := mul_le_mul_of_nonneg_left hkey' (by norm_num)
      _ = ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
            ∫ q : E3, (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2
              / (2 * ‖q‖ ^ 2) := by ring
  -- un-halve
  have hpt : ∀ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
      (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)
          (Work.BoseBoxFock.kmomLab ℓ N k)) ^ 2
          / ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2
        = 2 * ((Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)
              (Work.BoseBoxFock.kmomLab ℓ N k)) ^ 2
            / (2 * ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2)) := by
    intro k hk
    by_cases hy : ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2 = 0
    · simp [hy]
    · field_simp
  calc (∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)
            (Work.BoseBoxFock.kmomLab ℓ N k)) ^ 2
          / ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2)
      = 2 * (∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
          (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)
              (Work.BoseBoxFock.kmomLab ℓ N k)) ^ 2
            / (2 * ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k hk => (hpt k hk).trans (by ring)
    _ ≤ 2 * (((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
          ∫ q : E3, (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hhalf (by norm_num)
    _ = 2 * ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
          ∫ q : E3, (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2) := by
        ring

end Work.BoseFixR.All

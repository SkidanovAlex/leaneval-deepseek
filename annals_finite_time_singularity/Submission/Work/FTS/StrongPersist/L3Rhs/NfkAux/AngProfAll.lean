import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row25
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row21 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Open

open scoped Real Topology
open MeasureTheory Set Filter

set_option linter.unusedVariables false

/-! ## The continuity of the angular and radial iterates of the two factors -/




end Work.FTS.Nonlinear.Open
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row24Aux.RnLeRadial =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Open.Row24Aux


end Work.FTS.Nonlinear.Open.Row24Aux
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row24Aux.angMulScaledOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Open.Row24Aux

theorem angMulScaledOpen {α₂ Ci α c B : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hB : 0 < B) (hcB : c * B = Ci)
    (hSmoothInt : Work.Spaces.SmoothInt (fun _ (θ : ℝ) => -((Real.sin θ)^2)))
    (hbound : ∀ θ ∈ Work.Spaces.Iθ, |(-((Real.sin θ)^2))| ≤ B)
    (hdth : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ : ℝ) => -((Real.sin θ)^2)) 0 θ| ≤ B * Real.sin (2*θ))
    {g : Work.FTS.Galerkin.Fn} (hsm : Work.FTS.EllipticEst.SmoothOpen g)
    (hmem : Work.Spaces.HkMem α 4 g) (hIoc : α ∈ Set.Ioc 0 α₂) :
    Work.Spaces.HkMem α 4 (fun z θ => c * (-((Real.sin θ)^2)) * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => c * (-((Real.sin θ)^2)) * g z θ) ≤ Ci * Ci * Work.FTS.Nonlin.Xn α g := by
  have hci : 0 < Ci := hN.pos.1
  -- `c` is positive because `c * B = Ci > 0` and `B > 0`
  have hc : 0 < c := by
    by_contra hc
    push_neg at hc
    nlinarith [hci, hB]
  -- the scaled angular profile is still `SmoothInt`, hence `SmoothOpen`
  have hSI : Work.Spaces.SmoothInt (fun _ (θ : ℝ) => c * (-((Real.sin θ)^2))) := by
    constructor
    · change ContDiffOn ℝ ⊤ (fun x : ℝ × ℝ => c * -Real.sin x.2 ^ 2)
        (Set.Ioi (-1) ×ˢ Set.Ioo 0 (Real.pi / 2))
      exact (contDiffOn_const (𝕜 := ℝ) (c := c)).mul hSmoothInt.1
    · intro θ hθ
      simpa only [Pi.mul_apply] using
        (contDiffOn_const (𝕜 := ℝ) (c := c)).mul (hSmoothInt.2 θ hθ)
  have hSO : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => c * (-((Real.sin θ)^2))) :=
    Work.FTS.EllipticEst.smoothOpen_of_smoothInt hSI
  -- boundedness of the scaled profile
  have hb1 : ∀ θ ∈ Work.Spaces.Iθ, |c * (-((Real.sin θ)^2))| ≤ Ci := by
    intro θ hθ
    rw [abs_mul, abs_of_pos hc]
    calc c * |(-((Real.sin θ)^2))| ≤ c * B := mul_le_mul_of_nonneg_left (hbound θ hθ) hc.le
      _ = Ci := hcB
  -- the `D_θ`-iterates of the scaled profile vanish like `sin 2θ`
  have hb2 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ : ℝ) => c * (-((Real.sin θ)^2))) 0 θ|
        ≤ Ci * Real.sin (2*θ) := by
    intro i hi1 hi4 θ hθ
    rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.DthIter_const_mul i c
      (fun _ (θ : ℝ) => -((Real.sin θ)^2))]
    rw [abs_mul, abs_of_pos hc]
    calc c * |Work.Spaces.DthIter i (fun _ (θ : ℝ) => -((Real.sin θ)^2)) 0 θ|
        ≤ c * (B * Real.sin (2*θ)) := mul_le_mul_of_nonneg_left (hdth i hi1 hi4 θ hθ) hc.le
      _ = Ci * Real.sin (2*θ) := by rw [← hcB]; ring
  exact hN.angmul α hIoc (fun θ => c * (-((Real.sin θ)^2))) g hSO hb1 hb2 hsm hmem

end Work.FTS.Nonlinear.Open.Row24Aux
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row24Aux.qgSliceAe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Open.Row24Aux

open scoped Real Topology
open MeasureTheory Set Filter


end Work.FTS.Nonlinear.Open.Row24Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.AngProfAll =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs.NfkAux

set_option maxHeartbeats 1600000

theorem AngProfAll : ∃ K₀ K₁ K₂ K : ℝ, 0 < K₀ ∧ 0 ≤ K₁ ∧ 0 < K₂ ∧ 0 < K ∧
    ∀ α : ℝ, 0 < α → α ≤ 1 →
      (∀ i : ℕ, i ≤ 4 → ContinuousOn (fun θ : ℝ =>
          Work.Spaces.DthIter i (fun _ (θ' : ℝ) =>
            Work.FTS.StrongPersist.L3Rhs.NfkAux.aProf α θ') 0 θ)
        (Set.Ioo 0 (Real.pi / 2))) ∧
      (∀ θ ∈ Work.Spaces.Iθ, |Work.FTS.StrongPersist.L3Rhs.NfkAux.aProf α θ| ≤ K₀ * α) ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ' : ℝ) =>
            Work.FTS.StrongPersist.L3Rhs.NfkAux.aProf α θ') 0 θ|
          ≤ K₁ * α * Work.FTS.StrongPersist.L3Rhs.NfkAux.Gprof α θ) ∧
      (∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Work.FTS.StrongPersist.L3Rhs.NfkAux.Gprof α θ) ∧
      MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (Work.FTS.StrongPersist.L3Rhs.NfkAux.Gprof α θ) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Work.FTS.StrongPersist.L3Rhs.NfkAux.Gprof α θ) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ) ≤ K₂ / α ∧
      (∀ r : ℝ → ℝ, Work.Spaces.HkMem α 4 (fun z _ => r z) →
        Work.FTS.Nonlin.Xn α
            (fun z θ => Work.FTS.StrongPersist.L3Rhs.NfkAux.aProf α θ * r z)
          ≤ K * Work.FTS.Nonlin.Xn α (fun z θ => r z)) := by
  obtain ⟨Cg, hCgpos, hCg⟩ := Work.FTS.Nonlinear.Pieces.RNP.dthU_pow_Gam_sharp
  obtain ⟨Ms, hMspos, hMs⟩ := Work.FTS.Nonlinear.Pieces.RNP.gamWeightInt
  obtain ⟨Bs, hBspos, hBs⟩ := Work.FTS.Nonlinear.Pieces.RNP.dthSinSqGam_le
  refine ⟨34, 10 * (Cg + 2 * Bs) + 1, 2 * Ms + 2000,
    Real.sqrt (34 ^ 2 * 10000 + 4 * (10 * (Cg + 2 * Bs) + 1) ^ 2 * (2 * Ms + 2000)) + 1,
    by norm_num, by positivity, by positivity, by positivity, ?_⟩
  intro α hα hα1
  have hc := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith [hc.1]
  have hdivnn : 0 ≤ α / Work.Spaces.c α := div_nonneg hα.le hcpos.le
  have hdivle : α / Work.Spaces.c α ≤ 10 * α := by
    rw [div_le_iff₀ hcpos]; nlinarith [hc.1, hα]
  have hGam := contDiffOn_Gam_Ioo α
  have hsinNN : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) :=
    fun θ hθ => Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
  -- ## Conjunct 1: continuity of the `DthIter`s on the open interval
  have hcont : ∀ i : ℕ, i ≤ 4 → ContinuousOn (fun θ : ℝ =>
      Work.Spaces.DthIter i (fun _ (θ' : ℝ) =>
        Work.FTS.StrongPersist.L3Rhs.NfkAux.aProf α θ') 0 θ) (Set.Ioo 0 (Real.pi / 2)) := by
    intro i _
    have h := (contDiffOn_dthU_iter_open isOpen_Ioo (contDiffOn_aProf α) i).continuousOn
    refine h.congr (fun θ _ => ?_)
    rw [Work.FTS.LocData.DthIter_rad_eq]
  -- ## Conjunct 2: `|aProf α θ| ≤ 34 α`
  have hb0 : ∀ θ ∈ Work.Spaces.Iθ, |aProf α θ| ≤ 34 * α := by
    intro θ hθ
    have hΓ := Work.Spaces.Gam_bounds α θ hα hθ
    have hdth := Work.FTS.Nonlinear.Pieces.RNP.dthIter_one_Gam_le hα hα1 θ hθ
    have hrepr : Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ
        = Work.Spaces.DthIter 1 (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ := by
      rw [Work.FTS.LocData.DthIter_rad_eq 1 (fun t => Work.Spaces.Gam α t) 0 θ,
        Function.iterate_one]
    have hdth' : |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
        ≤ (4 / 3) * α * Work.Spaces.Gam α θ := by rw [hrepr]; exact hdth
    have hs2 : Real.sin θ ^ 2 ≤ 1 := by
      calc Real.sin θ ^ 2 = |Real.sin θ| ^ 2 := by rw [sq_abs]
        _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sin_le_one θ) 2
        _ = 1 := by norm_num
    have hb1 : |2 * Real.sin θ ^ 2 * Work.Spaces.Gam α θ| ≤ 2 * Work.Spaces.Gam α θ := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (sq_nonneg _), abs_of_nonneg hΓ.1]
      nlinarith [mul_le_mul_of_nonneg_right hs2 hΓ.1]
    have hsum : |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ
        + 2 * Real.sin θ ^ 2 * Work.Spaces.Gam α θ| ≤ 10 / 3 := by
      calc |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ
            + 2 * Real.sin θ ^ 2 * Work.Spaces.Gam α θ|
          ≤ |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
            + |2 * Real.sin θ ^ 2 * Work.Spaces.Gam α θ| := abs_add_le _ _
        _ ≤ (4 / 3) * α * Work.Spaces.Gam α θ + 2 * Work.Spaces.Gam α θ :=
            add_le_add hdth' hb1
        _ = ((4 / 3) * α + 2) * Work.Spaces.Gam α θ := by ring
        _ ≤ ((4 / 3) * 1 + 2) * 1 :=
            mul_le_mul (by linarith [hα1]) hΓ.2 hΓ.1 (by linarith [hα])
        _ = 10 / 3 := by norm_num
    rw [aProf, abs_mul, abs_neg, abs_of_nonneg hdivnn]
    calc (α / Work.Spaces.c α) * |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ
          + 2 * Real.sin θ ^ 2 * Work.Spaces.Gam α θ|
        ≤ (10 * α) * (10 / 3) := mul_le_mul hdivle hsum (abs_nonneg _) (by positivity)
      _ = 100 / 3 * α := by ring
      _ ≤ 34 * α := by linarith [hα]
  -- ## Conjunct 3: `|D_θ^i aProf| ≤ K₁ α Gprof`
  have hb1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) =>
        Work.FTS.StrongPersist.L3Rhs.NfkAux.aProf α θ') 0 θ|
        ≤ (10 * (Cg + 2 * Bs) + 1) * α * Gprof α θ := by
    intro i hi1 hi4 θ hθ
    have hΓ := Work.Spaces.Gam_bounds α θ hα hθ
    have hs := hsinNN θ hθ
    have hsα5 : 0 ≤ (Real.sin (2 * θ)) ^ (α / 5) := Real.rpow_nonneg hs _
    have hjet : |Work.Spaces.dthU^[i + 1] (fun t => Work.Spaces.Gam α t) θ|
        ≤ Cg * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) :=
      hCg α hα hα1 θ hθ (i + 1) (by omega) (by omega)
    have hs2 : |Work.Spaces.dthU^[i]
        (fun θ' : ℝ => Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') θ|
        ≤ Bs * (Real.sin (2 * θ)) ^ (α / 5) := by
      have h := hBs α hα hα1 i hi1 hi4 θ hθ
      rwa [Work.FTS.LocData.DthIter_rad_eq] at h
    -- additivity on the open interval
    have hUf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun θ' : ℝ => Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ')
        (Set.Ioo 0 (Real.pi / 2)) :=
      (contDiffOn_dthU_open isOpen_Ioo hGam).congr (fun θ' _ => rfl)
    have hUg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun θ' : ℝ => 2 * Real.sin θ' ^ 2 * Work.Spaces.Gam α θ')
        (Set.Ioo 0 (Real.pi / 2)) := by
      have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun θ' : ℝ => 2 * Real.sin θ' ^ 2)
          (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
      exact h1.mul hGam
    have hinterior : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
        |Work.Spaces.DthIter i (fun _ (θ' : ℝ) =>
          Work.FTS.StrongPersist.L3Rhs.NfkAux.aProf α θ') 0 θ|
          ≤ (10 * (Cg + 2 * Bs) + 1) * α * Gprof α θ := by
      intro hioo
      rw [Work.FTS.LocData.DthIter_rad_eq]
      have hsplit : aProf α = fun θ' : ℝ => -(α / Work.Spaces.c α) *
          (Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ'
            + 2 * Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') := by
        funext θ'; simp only [aProf]
      have hcore : Work.Spaces.dthU^[i]
            (fun θ' : ℝ => Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ'
              + 2 * Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') θ
          = Work.Spaces.dthU^[i + 1] (fun t => Work.Spaces.Gam α t) θ
            + 2 * Work.Spaces.dthU^[i]
                (fun θ' : ℝ => Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') θ := by
        have h1 : (fun θ' : ℝ => Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ'
              + 2 * Real.sin θ' ^ 2 * Work.Spaces.Gam α θ')
            = (fun θ' : ℝ => Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ')
              + (fun θ' : ℝ => 2 * Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') := by
          funext θ'; simp only [Pi.add_apply]
        rw [h1, dthU_iter_add_eqOn isOpen_Ioo hUf hUg i θ hioo]
        rw [show Work.Spaces.dthU^[i] (fun θ' : ℝ =>
              Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ') θ
            = Work.Spaces.dthU^[i + 1] (fun t => Work.Spaces.Gam α t) θ from by
          rw [show (fun θ' : ℝ => Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ')
              = Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) from rfl,
            Work.Spaces.dthU_iter_comp]]
        rw [show Work.Spaces.dthU^[i]
              (fun θ' : ℝ => 2 * Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') θ
            = 2 * Work.Spaces.dthU^[i]
                (fun θ' : ℝ => Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') θ from by
          rw [show (fun θ' : ℝ => 2 * Real.sin θ' ^ 2 * Work.Spaces.Gam α θ')
              = fun θ' : ℝ => 2 * (Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') from by
                funext θ'; ring,
            Work.Spaces.dthU_iter_const_mul]]
      rw [hsplit, Work.Spaces.dthU_iter_const_mul]
      dsimp only
      rw [hcore, abs_mul, abs_neg, abs_of_nonneg hdivnn]
      have hsum : |Work.Spaces.dthU^[i + 1] (fun t => Work.Spaces.Gam α t) θ
            + 2 * Work.Spaces.dthU^[i]
              (fun θ' : ℝ => Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') θ|
          ≤ Cg * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))
            + 2 * (Bs * (Real.sin (2 * θ)) ^ (α / 5)) := by
        have h2 : |2 * Work.Spaces.dthU^[i]
            (fun θ' : ℝ => Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') θ|
            ≤ 2 * (Bs * (Real.sin (2 * θ)) ^ (α / 5)) := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          linarith [hs2]
        calc |Work.Spaces.dthU^[i + 1] (fun t => Work.Spaces.Gam α t) θ
              + 2 * Work.Spaces.dthU^[i]
                (fun θ' : ℝ => Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') θ|
            ≤ |Work.Spaces.dthU^[i + 1] (fun t => Work.Spaces.Gam α t) θ|
              + |2 * Work.Spaces.dthU^[i]
                (fun θ' : ℝ => Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') θ| := abs_add_le _ _
          _ ≤ _ := add_le_add hjet h2
      have hAnn : 0 ≤ Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) :=
        mul_nonneg hΓ.1 (by linarith [hα, hs])
      have hBn : 0 ≤ (Real.sin (2 * θ)) ^ (α / 5) := hsα5
      have hgoal : (10 * α) * (Cg * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))
            + 2 * (Bs * (Real.sin (2 * θ)) ^ (α / 5)))
          ≤ (10 * (Cg + 2 * Bs) + 1) * α * Gprof α θ := by
        rw [Gprof]
        have hS : 0 ≤ Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) := hAnn
        have hαS : 0 ≤ α * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) :=
          mul_nonneg hα.le hS
        have hαB : 0 ≤ α * (Real.sin (2 * θ)) ^ (α / 5) := mul_nonneg hα.le hBn
        have hkey1 : 10 * Cg * α * (α * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))))
            ≤ 10 * Cg * α * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_of_le_one_left hS hα1
        have hkey2 : 20 * α * Bs * (Real.sin (2 * θ)) ^ (α / 5)
            ≤ (10 * (Cg + 2 * Bs) + 1)
              * (α * (Real.sin (2 * θ)) ^ (α / 5)) := by
          have hc : 20 * Bs ≤ 10 * (Cg + 2 * Bs) + 1 := by linarith [hCgpos, hBspos]
          calc 20 * α * Bs * (Real.sin (2 * θ)) ^ (α / 5)
              = (20 * Bs) * (α * (Real.sin (2 * θ)) ^ (α / 5)) := by ring
            _ ≤ (10 * (Cg + 2 * Bs) + 1)
                  * (α * (Real.sin (2 * θ)) ^ (α / 5)) :=
                mul_le_mul_of_nonneg_right hc hαB
        have hkey3 : 10 * Cg * α * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)))
            ≤ (10 * (Cg + 2 * Bs) + 1)
              * (α * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)))) := by
          have hc : 10 * Cg ≤ 10 * (Cg + 2 * Bs) + 1 := by linarith [hCgpos, hBspos]
          calc 10 * Cg * α * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)))
              = (10 * Cg) * (α * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)))) := by ring
            _ ≤ (10 * (Cg + 2 * Bs) + 1)
                  * (α * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)))) :=
                mul_le_mul_of_nonneg_right hc hαS
        have hexp : (10 * α) * (Cg * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))
              + 2 * (Bs * (Real.sin (2 * θ)) ^ (α / 5)))
            = 10 * Cg * α * (α * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))))
              + 20 * α * Bs * (Real.sin (2 * θ)) ^ (α / 5) := by ring
        have hexp2 : (10 * (Cg + 2 * Bs) + 1)
              * α * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))
                + (Real.sin (2 * θ)) ^ (α / 5))
            = (10 * (Cg + 2 * Bs) + 1)
                * (α * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))))
              + (10 * (Cg + 2 * Bs) + 1) * (α * (Real.sin (2 * θ)) ^ (α / 5)) := by ring
        rw [hexp, hexp2]
        linarith [hkey1, hkey2, hkey3]
      calc (α / Work.Spaces.c α) * |Work.Spaces.dthU^[i + 1] (fun t => Work.Spaces.Gam α t) θ
            + 2 * Work.Spaces.dthU^[i]
              (fun θ' : ℝ => Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') θ|
          ≤ (10 * α) * (Cg * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))
              + 2 * (Bs * (Real.sin (2 * θ)) ^ (α / 5))) :=
            mul_le_mul hdivle hsum (abs_nonneg _) (by positivity)
        _ ≤ (10 * (Cg + 2 * Bs) + 1) * α * Gprof α θ := hgoal
    -- assemble, handling the two endpoints separately
    rcases lt_or_eq_of_le hθ.1 with h0 | h0
    · rcases lt_or_eq_of_le hθ.2 with h1 | h1
      · exact hinterior ⟨h0, h1⟩
      · subst h1
        rw [Work.FTS.LocData.DthIter_rad_eq]
        rw [show Work.Spaces.dthU^[i] (aProf α) (Real.pi / 2) = 0 from ?_,
          abs_zero]
        · have hs0 : Real.sin (2 * (Real.pi / 2)) = 0 := by
            rw [show 2 * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi]
          rw [Gprof, Work.Spaces.Gam_zero_right α (ne_of_gt hα), hs0]
          norm_num [Real.zero_rpow (show α / 5 ≠ 0 by positivity)]
        · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hi1)
          subst hj
          rw [Function.iterate_succ_apply']
          exact dthU_zero_right _
    · subst h0
      rw [Work.FTS.LocData.DthIter_rad_eq]
      rw [show Work.Spaces.dthU^[i] (aProf α) 0 = 0 from ?_, abs_zero]
      · have hs0 : Real.sin (2 * (0 : ℝ)) = 0 := by
          rw [show 2 * (0 : ℝ) = 0 from by ring, Real.sin_zero]
        rw [Gprof, Work.Spaces.Gam_zero_left α (ne_of_gt hα), hs0]
        norm_num [Real.zero_rpow (show α / 5 ≠ 0 by positivity)]
      · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hi1)
        subst hj
        rw [Function.iterate_succ_apply']
        exact dthU_zero_left _
  -- ## Conjunct 4: nonnegativity of `Gprof`
  have hgnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Gprof α θ := by
    intro θ hθ
    have hΓ := Work.Spaces.Gam_bounds α θ hα hθ
    have hs := hsinNN θ hθ
    rw [Gprof]
    exact add_nonneg (mul_nonneg hΓ.1 (by linarith [hα, hs])) (Real.rpow_nonneg hs _)
  -- ## Conjuncts 5 and 6: the angular mass of `Gprof`
  have hp1 : -1 < α / 5 - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hp2 : α / 5 - Work.Spaces.gam α ≤ 0 := by rw [Work.Spaces.gam]; linarith
  have hpne : α / 5 - Work.Spaces.gam α ≠ 0 := by
    rw [Work.Spaces.gam]; intro h; linarith
  obtain ⟨hIntS, hBdS⟩ := Work.Spaces.sin_two_rpow (α / 5 - Work.Spaces.gam α) hp1 hp2
  obtain ⟨hIntG, hBdG⟩ := hMs α hα hα1
  have hBdS' : (∫ θ in Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (α / 5 - Work.Spaces.gam α)) ≤ 1000 / α := by
    have h := hBdS
    have hden : α / 5 - Work.Spaces.gam α + 1 = α / 10 := by rw [Work.Spaces.gam]; ring
    rw [hden] at h
    have h2 : (100 : ℝ) / (α / 10) = 1000 / α := by
      field_simp
      ring
    linarith [h, le_of_eq h2]
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      (Gprof α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ
        ≤ 2 * ((Work.Spaces.Gam α θ) ^ 2 * (α + Real.sin (2 * θ)) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smG α θ)
          + 2 * (Real.sin (2 * θ)) ^ (α / 5 - Work.Spaces.gam α) := by
    intro θ hθ
    have hs := hsinNN θ hθ
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (α / 5) := Real.rpow_nonneg hs _
    have hsle1 : (Real.sin (2 * θ)) ^ (α / 5) ≤ 1 :=
      Real.rpow_le_one hs hs1 (by positivity)
    have hsmnn : 0 ≤ Work.FTS.Nonlinear.RadialProd.smG α θ :=
      Work.FTS.Nonlinear.RadialProd.smG_nonneg hθ
    -- the square of the `sin`-factor against the weight
    have hsq : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
        * Work.FTS.Nonlinear.RadialProd.smG α θ
        ≤ (Real.sin (2 * θ)) ^ (α / 5 - Work.Spaces.gam α) := by
      show ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          ≤ (Real.sin (2 * θ)) ^ (α / 5 - Work.Spaces.gam α)
      have h1 : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 ≤ (Real.sin (2 * θ)) ^ (α / 5) := by
        have h2 := mul_le_mul_of_nonneg_right hsle1 hsnn
        calc ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
            = (Real.sin (2 * θ)) ^ (α / 5) * (Real.sin (2 * θ)) ^ (α / 5) := by ring
          _ ≤ 1 * (Real.sin (2 * θ)) ^ (α / 5) := h2
          _ = (Real.sin (2 * θ)) ^ (α / 5) := one_mul _
      calc ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          ≤ (Real.sin (2 * θ)) ^ (α / 5)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hs _)
        _ = (Real.sin (2 * θ)) ^ (α / 5 - Work.Spaces.gam α) :=
            (Real.rpow_add' hs hpne).symm
    have hexp : (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))
          + (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
        = (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) ^ 2
          + 2 * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) * (Real.sin (2 * θ)) ^ (α / 5)
          + ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 := by ring
    have hcross : 2 * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)))
          * (Real.sin (2 * θ)) ^ (α / 5) * Work.FTS.Nonlinear.RadialProd.smG α θ
        ≤ (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smG α θ
          + ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smG α θ := by
      have h2ab : 2 * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)))
          * (Real.sin (2 * θ)) ^ (α / 5)
          ≤ (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) ^ 2
            + ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 := by
        nlinarith [sq_nonneg (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))
          - (Real.sin (2 * θ)) ^ (α / 5))]
      calc 2 * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) * (Real.sin (2 * θ)) ^ (α / 5)
            * Work.FTS.Nonlinear.RadialProd.smG α θ
          = (2 * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)))
              * (Real.sin (2 * θ)) ^ (α / 5)) * Work.FTS.Nonlinear.RadialProd.smG α θ := by ring
        _ ≤ ((Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) ^ 2
              + ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2)
              * Work.FTS.Nonlinear.RadialProd.smG α θ :=
            mul_le_mul_of_nonneg_right h2ab hsmnn
        _ = _ := by ring
    rw [Gprof]
    rw [hexp]
    have hstep : ((Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) ^ 2
          + 2 * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) * (Real.sin (2 * θ)) ^ (α / 5)
          + ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2) * Work.FTS.Nonlinear.RadialProd.smG α θ
        = (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smG α θ
          + 2 * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) * (Real.sin (2 * θ)) ^ (α / 5)
            * Work.FTS.Nonlinear.RadialProd.smG α θ
          + ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smG α θ := by ring
    rw [hstep]
    have hb : 2 * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ
        = 2 * ((Work.Spaces.Gam α θ) ^ 2 * (α + Real.sin (2 * θ)) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smG α θ) := by ring
    rw [← hb]
    linarith [hcross, hsq]
  -- measurability and integrability
  have hIntF : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      2 * ((Work.Spaces.Gam α θ) ^ 2 * (α + Real.sin (2 * θ)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ)
        + 2 * (Real.sin (2 * θ)) ^ (α / 5 - Work.Spaces.gam α)) Work.Spaces.Iθ :=
    (hIntG.const_mul 2).add (hIntS.const_mul 2)
  have hmeas : AEStronglyMeasurable (fun θ : ℝ =>
      (Gprof α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine Measurable.aestronglyMeasurable ?_
    simp only [Gprof, Work.FTS.Nonlinear.RadialProd.smG, Work.Spaces.Gam]
    fun_prop
  have hIntGp : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.FTS.StrongPersist.L3Rhs.NfkAux.Gprof α θ) ^ 2
        * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ := by
    refine hIntF.mono' hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
      (Work.FTS.Nonlinear.RadialProd.smG_nonneg hθ))]
    exact hpt θ hθ
  have hIntFval : (∫ θ in Work.Spaces.Iθ,
        2 * ((Work.Spaces.Gam α θ) ^ 2 * (α + Real.sin (2 * θ)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ)
        + 2 * (Real.sin (2 * θ)) ^ (α / 5 - Work.Spaces.gam α))
      = 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ) ^ 2 * (α + Real.sin (2 * θ)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ)
        + 2 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (α / 5 - Work.Spaces.gam α)) := by
    rw [MeasureTheory.integral_add (hIntG.const_mul 2) (hIntS.const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hmain : (∫ θ in Work.Spaces.Iθ, (Gprof α θ) ^ 2
        * Work.FTS.Nonlinear.RadialProd.smG α θ) ≤ (2 * Ms + 2000) / α := by
    have hstep : (∫ θ in Work.Spaces.Iθ, (Gprof α θ) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ)
        ≤ ∫ θ in Work.Spaces.Iθ, 2 * ((Work.Spaces.Gam α θ) ^ 2
            * (α + Real.sin (2 * θ)) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
          + 2 * (Real.sin (2 * θ)) ^ (α / 5 - Work.Spaces.gam α) :=
      MeasureTheory.integral_mono_of_nonneg
        (by filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
            exact mul_nonneg (sq_nonneg _) (Work.FTS.Nonlinear.RadialProd.smG_nonneg hθ))
        hIntF (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hpt)
    have hstep2 : (∫ θ in Work.Spaces.Iθ, 2 * ((Work.Spaces.Gam α θ) ^ 2
          * (α + Real.sin (2 * θ)) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
        + 2 * (Real.sin (2 * θ)) ^ (α / 5 - Work.Spaces.gam α))
        ≤ 2 * Ms + 2000 / α := by
      rw [hIntFval]
      have h1 : 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ) ^ 2
            * (α + Real.sin (2 * θ)) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) ≤ 2 * Ms :=
        mul_le_mul_of_nonneg_left hBdG (by norm_num)
      have h2 : 2 * (∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (α / 5 - Work.Spaces.gam α)) ≤ 2 * (1000 / α) :=
        mul_le_mul_of_nonneg_left hBdS' (by norm_num)
      have hEq : 2 * (1000 / α) = 2000 / α := by
        rw [← mul_div_assoc]
        norm_num
      linarith
    refine hstep.trans (hstep2.trans ?_)
    rw [le_div_iff₀ hα]
    have hmul : (2 * Ms + 2000 / α) * α = 2 * Ms * α + 2000 := by
      rw [add_mul, div_mul_cancel₀ 2000 (ne_of_gt hα)]
    rw [hmul]
    nlinarith [hMspos.le, hα1, hα]
  -- ## Conjunct 7: the `ℋ⁴`-operator norm of `aProf`
  have hfin : ∀ r : ℝ → ℝ, Work.Spaces.HkMem α 4 (fun z _ => r z) →
      Work.FTS.Nonlin.Xn α (fun z θ => aProf α θ * r z)
        ≤ (Real.sqrt (34 ^ 2 * 10000 + 4 * (10 * (Cg + 2 * Bs) + 1) ^ 2 * (2 * Ms + 2000)) + 1)
          * Work.FTS.Nonlin.Xn α (fun z θ => r z) := by
    intro r hrmem
    have hXn := Work.FTS.Nonlinear.Pieces.RNP.Xn_ang_rad_le_gen α hα
      (fun θ => aProf α θ) r (fun θ => Gprof α θ)
      (B0 := 34 * α) (B1 := (10 * (Cg + 2 * Bs) + 1) * α) (M1 := (2 * Ms + 2000) / α)
      (by positivity) (by positivity) (by positivity) hgnn hb0 hb1 hIntGp hmain hrmem
    have hsqrt : Real.sqrt ((34 * α) ^ 2 * 10000
          + 4 * ((10 * (Cg + 2 * Bs) + 1) * α) ^ 2 * ((2 * Ms + 2000) / α))
        ≤ Real.sqrt (34 ^ 2 * 10000 + 4 * (10 * (Cg + 2 * Bs) + 1) ^ 2 * (2 * Ms + 2000)) := by
      apply Real.sqrt_le_sqrt
      have heq : ((10 * (Cg + 2 * Bs) + 1) * α) ^ 2 * ((2 * Ms + 2000) / α)
          = (10 * (Cg + 2 * Bs) + 1) ^ 2 * (α * (2 * Ms + 2000)) := by
        field_simp
        try ring
      have hK2 : 0 ≤ 2 * Ms + 2000 := by linarith [hMspos]
      have hK1 : 0 ≤ (10 * (Cg + 2 * Bs) + 1) ^ 2 := by positivity
      have hb : 4 * (((10 * (Cg + 2 * Bs) + 1) * α) ^ 2 * ((2 * Ms + 2000) / α))
          ≤ 4 * ((10 * (Cg + 2 * Bs) + 1) ^ 2 * (2 * Ms + 2000)) := by
        rw [heq]
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 4)
        exact mul_le_mul_of_nonneg_left (by nlinarith [hK2, hα, hα1]) hK1
      have ha : (34 * α) ^ 2 * 10000 ≤ 34 ^ 2 * 10000 := by
        have e1 : (34 * α) ^ 2 = 34 ^ 2 * α ^ 2 := by ring
        rw [e1]
        nlinarith [hα, hα1, sq_nonneg (34 : ℝ)]
      calc (34 * α) ^ 2 * 10000
            + 4 * ((10 * (Cg + 2 * Bs) + 1) * α) ^ 2 * ((2 * Ms + 2000) / α)
          = (34 * α) ^ 2 * 10000
              + 4 * (((10 * (Cg + 2 * Bs) + 1) * α) ^ 2 * ((2 * Ms + 2000) / α)) := by ring
        _ ≤ 34 ^ 2 * 10000 + 4 * ((10 * (Cg + 2 * Bs) + 1) ^ 2 * (2 * Ms + 2000)) :=
            add_le_add ha hb
        _ = 34 ^ 2 * 10000 + 4 * (10 * (Cg + 2 * Bs) + 1) ^ 2 * (2 * Ms + 2000) := by ring
    calc Work.FTS.Nonlin.Xn α (fun z θ => aProf α θ * r z)
        ≤ Real.sqrt ((34 * α) ^ 2 * 10000
            + 4 * ((10 * (Cg + 2 * Bs) + 1) * α) ^ 2 * ((2 * Ms + 2000) / α))
          * Work.FTS.Nonlin.Xn α (fun z θ => r z) := hXn
      _ ≤ Real.sqrt (34 ^ 2 * 10000 + 4 * (10 * (Cg + 2 * Bs) + 1) ^ 2 * (2 * Ms + 2000))
            * Work.FTS.Nonlin.Xn α (fun z θ => r z) :=
          mul_le_mul_of_nonneg_right hsqrt (Work.Spaces.HkNorm_nonneg α 4 _)
      _ ≤ (Real.sqrt (34 ^ 2 * 10000 + 4 * (10 * (Cg + 2 * Bs) + 1) ^ 2 * (2 * Ms + 2000)) + 1)
            * Work.FTS.Nonlin.Xn α (fun z θ => r z) := by
          have := Work.Spaces.HkNorm_nonneg α 4 (fun z θ => r z)
          nlinarith
  exact ⟨hcont, hb0, hb1, hgnn, hIntGp, hmain, hfin⟩

end Work.FTS.StrongPersist.L3Rhs.NfkAux
end
end

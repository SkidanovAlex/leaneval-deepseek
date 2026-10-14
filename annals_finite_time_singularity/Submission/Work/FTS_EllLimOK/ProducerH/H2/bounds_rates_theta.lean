import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2EgRate
import Submission.Work.FTS_EllLimOK.ProducerH.MixedJets.mixed_jets_le_Xn6
import Submission.Work.FTS_EllLimOK.ProducerH.SecondDeriv.second_theta_deriv_le_Xn6
import Submission.Work.FTS_EllLimOK.ProducerH.SecondDeriv.slice_package_bounds
import Submission.Work.FTS_EllLimOK.ProducerH.SecondDerivDz.second_theta_deriv_DzIter_le_Xn6
import Submission.Work.FTS_EllLimOK.ProducerH.slotBd_phiTil
import Submission.Work.FTS_EllLimOK.RulingELF

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.H2

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The `∂_θ`-clauses of `bounds_rates`.

The plain angular derivatives of orders `1`, `2` and of the mixed quantities are all obtained by
combining

* their value at the midpoint `θ = π/4` (where `sin 2θ = 1`, so the normalised mixed jets
  `D_z^j D_θ^i` of `mixed_jets_le_Xn6` — a single, uniform-in-`z` bound — control the plain
  derivatives), and
* the interpolation inequality `br_slice_interp` with the *plain* second angular derivative of the
  relevant quantity, which is supplied by `second_theta_deriv_le_Xn6`
  (`|∂_θ² (E g)| ≤ Ks·𝓧`) and `second_theta_deriv_DzIter_le_Xn6`
  (`|∂_θ² (D_z^a (E g))| ≤ K·𝓧`, `a ≤ 2`).

The two rate clauses are the hypothesis `hmod` itself, rewritten with `min θ (π/2-θ) ≤ θ` and
`min θ (π/2-θ) ≤ π/2-θ`. -/
theorem bounds_rates_theta {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : Work.FTS_EllLimOK.ProducerH.H2.Ctx α Ce E) {a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hab : a₀ ≤ b₀)
    {K β : ℝ} (hK : 0 < K) (hβ : 0 < β)
    (hmod : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g → ∀ z ∈ Set.Icc a₀ b₀,
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |deriv (deriv (fun θ' => (E g) z θ')) θ|
          ≤ K * Work.FTS.StrongGlobal.Xn6 α g * (min θ (Real.pi / 2 - θ)) ^ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      ∀ z ∈ Set.Icc a₀ b₀, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Work.Spaces.pth (E g) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
        |Work.Spaces.pth (Work.Spaces.pz (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
        |Work.Spaces.pz (Work.Spaces.pth (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
        |Work.Spaces.pth (Work.Spaces.pth (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
        |Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pz (E g))) z θ|
          ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
        |Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz (E g))) z θ|
          ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
        |Work.Spaces.pth (Work.Spaces.pth (E g)) z θ|
          ≤ C * Work.FTS.StrongGlobal.Xn6 α g * θ ^ β ∧
        |Work.Spaces.pth (Work.Spaces.pth (E g)) z θ|
          ≤ C * Work.FTS.StrongGlobal.Xn6 α g * (Real.pi / 2 - θ) ^ β := by
  obtain ⟨Km, hKmpos, hKm⟩ := Work.FTS_EllLimOK.ProducerH.MixedJets.mixed_jets_le_Xn6 hα hα4 hE
  obtain ⟨Ks, hKspos, hKs⟩ :=
    Work.FTS_EllLimOK.ProducerH.SecondDeriv.second_theta_deriv_le_Xn6 hα hα4 hE ha₀ hab
  obtain ⟨K1, hK1pos, hK1⟩ :=
    Work.FTS_EllLimOK.ProducerH.SecondDerivDz.second_theta_deriv_DzIter_le_Xn6 hα hα4 hE 1
      (by norm_num) ha₀ hab
  obtain ⟨K2, hK2pos, hK2⟩ :=
    Work.FTS_EllLimOK.ProducerH.SecondDerivDz.second_theta_deriv_DzIter_le_Xn6 hα hα4 hE 2
      (by norm_num) ha₀ hab
  set D : ℝ := Km + Ks * (π / 2) + (Km + K1 * (π / 2)) + Ks
      + (2 * Km + (π / 2) * (K1 + K2)) + K1 + K + 1 with hDdef
  have hDpos : 0 < D := by rw [hDdef]; positivity
  set C : ℝ := (1 + 1 / a₀ + 1 / a₀ ^ 2) * D with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hb1 : (0 : ℝ) ≤ Ks * (π / 2) := by positivity
  have hb2 : (0 : ℝ) ≤ Km + K1 * (π / 2) := by positivity
  have hb3 : (0 : ℝ) ≤ Ks := hKspos.le
  have hb4 : (0 : ℝ) ≤ 2 * Km + (π / 2) * (K1 + K2) := by positivity
  have hA2D : Km + Ks * (π / 2) ≤ D := by rw [hDdef]; linarith
  have hA5D : Km + K1 * (π / 2) ≤ D := by rw [hDdef]; linarith
  have hKsD : Ks ≤ D := by rw [hDdef]; linarith
  have hA7D : 2 * Km + (π / 2) * (K1 + K2) ≤ D := by rw [hDdef]; linarith
  have hK1D : K1 ≤ D := by rw [hDdef]; linarith
  have hKD : K ≤ D := by rw [hDdef]; linarith
  have h1a0 : (0 : ℝ) ≤ 1 / a₀ := by positivity
  have h1a02 : (0 : ℝ) ≤ 1 / a₀ ^ 2 := by positivity
  have hfac1 : (1 : ℝ) ≤ 1 + 1 / a₀ + 1 / a₀ ^ 2 := by linarith
  have hfacA : 1 / a₀ ≤ 1 + 1 / a₀ + 1 / a₀ ^ 2 := by linarith
  have hfacA2 : 1 / a₀ ^ 2 ≤ 1 + 1 / a₀ + 1 / a₀ ^ 2 := by linarith
  have hCA2 : Km + Ks * (π / 2) ≤ C := by
    rw [hCdef]
    calc Km + Ks * (π / 2) ≤ D := hA2D
      _ ≤ (1 + 1 / a₀ + 1 / a₀ ^ 2) * D := by
          nth_rewrite 1 [show D = 1 * D from (one_mul D).symm]
          exact mul_le_mul_of_nonneg_right hfac1 hDpos.le
  have hCA5 : (Km + K1 * (π / 2)) / a₀ ≤ C := by
    rw [hCdef]
    calc (Km + K1 * (π / 2)) / a₀ = (Km + K1 * (π / 2)) * (1 / a₀) := by ring
      _ ≤ D * (1 / a₀) := mul_le_mul_of_nonneg_right hA5D h1a0
      _ ≤ D * (1 + 1 / a₀ + 1 / a₀ ^ 2) := mul_le_mul_of_nonneg_left hfacA hDpos.le
      _ = (1 + 1 / a₀ + 1 / a₀ ^ 2) * D := by ring
  have hCA6 : Ks ≤ C := by
    rw [hCdef]
    calc Ks ≤ D := hKsD
      _ ≤ (1 + 1 / a₀ + 1 / a₀ ^ 2) * D := by
          nth_rewrite 1 [show D = 1 * D from (one_mul D).symm]
          exact mul_le_mul_of_nonneg_right hfac1 hDpos.le
  have hCA7 : (2 * Km + (π / 2) * (K1 + K2)) / a₀ ^ 2 ≤ C := by
    rw [hCdef]
    calc (2 * Km + (π / 2) * (K1 + K2)) / a₀ ^ 2
        = (2 * Km + (π / 2) * (K1 + K2)) * (1 / a₀ ^ 2) := by ring
      _ ≤ D * (1 / a₀ ^ 2) := mul_le_mul_of_nonneg_right hA7D h1a02
      _ ≤ D * (1 + 1 / a₀ + 1 / a₀ ^ 2) := mul_le_mul_of_nonneg_left hfacA2 hDpos.le
      _ = (1 + 1 / a₀ + 1 / a₀ ^ 2) * D := by ring
  have hCA8 : K1 / a₀ ≤ C := by
    rw [hCdef]
    calc K1 / a₀ = K1 * (1 / a₀) := by ring
      _ ≤ D * (1 / a₀) := mul_le_mul_of_nonneg_right hK1D h1a0
      _ ≤ D * (1 + 1 / a₀ + 1 / a₀ ^ 2) := mul_le_mul_of_nonneg_left hfacA hDpos.le
      _ = (1 + 1 / a₀ + 1 / a₀ ^ 2) * D := by ring
  have hCK : K ≤ C := by
    rw [hCdef]
    calc K ≤ D := hKD
      _ ≤ (1 + 1 / a₀ + 1 / a₀ ^ 2) * D := by
          nth_rewrite 1 [show D = 1 * D from (one_mul D).symm]
          exact mul_le_mul_of_nonneg_right hfac1 hDpos.le
  refine ⟨C, hCpos, ?_⟩
  intro g hg z hz θ hθ
  have hzpos : 0 < z := lt_of_lt_of_le ha₀ hz.1
  have hX0 : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g := Xn6_nonneg α g
  have hΨsm : Work.FTS.EllipticEst.SmoothOpen (E g) := (hE g hg).1.2.1
  have hm0 : 0 ≤ min θ (π / 2 - θ) := le_of_lt (mm_pos hθ)
  have hmθ : min θ (π / 2 - θ) ≤ θ := mm_le_theta θ
  have hmπ : min θ (π / 2 - θ) ≤ π / 2 - θ := mm_le_pi_sub θ
  -- ## the plain second angular derivative of `E g`
  have hpth2 : |Work.Spaces.pth (Work.Spaces.pth (E g)) z θ|
      ≤ Ks * Work.FTS.StrongGlobal.Xn6 α g := by
    rw [show Work.Spaces.pth (Work.Spaces.pth (E g)) z θ
        = deriv (deriv (fun θ' => (E g) z θ')) θ from rfl]
    exact hKs g hg z hz θ hθ
  -- ## the second angular derivative of `∂_z (E g)`
  have hDth2pz : ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
      |deriv (deriv (fun θ'' => Work.Spaces.pz (E g) z θ'')) θ'|
        ≤ K1 * Work.FTS.StrongGlobal.Xn6 α g / a₀ := by
    intro θ' hθ'
    have h := hK1 g hg z hz θ' hθ'
    have hident : deriv (deriv (fun θ'' => Work.Spaces.DzIter 1 (E g) z θ'')) θ'
        = z * deriv (deriv (fun θ'' => Work.Spaces.pz (E g) z θ'')) θ' :=
      br_deriv_deriv_const_mul z z θ' (Work.Spaces.pz (E g))
    rw [hident, abs_mul, abs_of_pos hzpos] at h
    exact br_le_div_const hzpos (by positivity) ha₀ hz.1 h
  -- ## the plain angular derivative of `E g`
  have hval2 : |Work.Spaces.pth (E g) z (π / 4)| ≤ Km * Work.FTS.StrongGlobal.Xn6 α g := by
    have h := hKm g hg 0 1 (by norm_num) z (π / 4) ⟨hzpos, br_quarter_mem⟩
    rwa [← br_pth_quarter_eq (E g) z] at h
  have hpth1 : |Work.Spaces.pth (E g) z θ|
      ≤ (Km + Ks * (π / 2)) * Work.FTS.StrongGlobal.Xn6 α g := by
    have hd : ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
        DifferentiableAt ℝ (fun θ'' => Work.Spaces.pth (E g) z θ'') θ' :=
      fun θ' hθ' => (hΨsm.pth).curry_θ hzpos |>.differentiableOn (by simp) |>.differentiableAt
        (isOpen_Ioo.mem_nhds hθ')
    have hb : ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
        |deriv (fun θ'' => Work.Spaces.pth (E g) z θ'') θ'|
          ≤ Ks * Work.FTS.StrongGlobal.Xn6 α g := by
      intro θ' hθ'
      rw [show deriv (fun θ'' => Work.Spaces.pth (E g) z θ'') θ'
          = deriv (deriv (fun θ'' => (E g) z θ'')) θ' from rfl]
      exact hKs g hg z hz θ' hθ'
    have h := br_slice_interp (f := fun θ'' => Work.Spaces.pth (E g) z θ'')
      (C := Ks * Work.FTS.StrongGlobal.Xn6 α g) hd hb hθ
    calc |Work.Spaces.pth (E g) z θ|
        ≤ |Work.Spaces.pth (E g) z (π / 4)|
            + Ks * Work.FTS.StrongGlobal.Xn6 α g * (π / 2) := h
      _ ≤ Km * Work.FTS.StrongGlobal.Xn6 α g
            + Ks * Work.FTS.StrongGlobal.Xn6 α g * (π / 2) := by linarith
      _ = (Km + Ks * (π / 2)) * Work.FTS.StrongGlobal.Xn6 α g := by ring
  -- ## the angular derivative of `∂_z (E g)`
  have hthpzeq : ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
      Work.Spaces.pth (Work.Spaces.pz (E g)) z θ'
        = Work.Spaces.pz (Work.Spaces.pth (E g)) z θ' :=
    fun θ' hθ' => (br_pz_pth_eq_of_smoothOpen hΨsm hzpos hθ').symm
  have hpzpth : |Work.Spaces.pz (Work.Spaces.pth (E g)) z θ|
      ≤ (Km + K1 * (π / 2)) / a₀ * Work.FTS.StrongGlobal.Xn6 α g := by
    have hval : |Work.Spaces.pz (Work.Spaces.pth (E g)) z (π / 4)|
        ≤ Km * Work.FTS.StrongGlobal.Xn6 α g / a₀ := by
      have h := hKm g hg 1 1 (by norm_num) z (π / 4) ⟨hzpos, br_quarter_mem⟩
      have hident : Work.Spaces.mixed 1 1 (E g) z (π / 4)
          = z * Work.Spaces.pz (Work.Spaces.pth (E g)) z (π / 4) := by
        have hq := br_mixed_quarter_eq (E g) 1 z
        rw [show Work.Spaces.DzIter 1 (Work.Spaces.pth (E g)) z (π / 4)
            = z * Work.Spaces.pz (Work.Spaces.pth (E g)) z (π / 4) from rfl] at hq
        exact hq
      rw [hident, abs_mul, abs_of_pos hzpos] at h
      exact br_le_div_const hzpos (by positivity) ha₀ hz.1 h
    have hd : ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
        DifferentiableAt ℝ (fun θ'' => Work.Spaces.pz (Work.Spaces.pth (E g)) z θ'') θ' :=
      fun θ' hθ' => (hΨsm.pth.pz).curry_θ hzpos |>.differentiableOn (by simp) |>.differentiableAt
        (isOpen_Ioo.mem_nhds hθ')
    have hb : ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
        |deriv (fun θ'' => Work.Spaces.pz (Work.Spaces.pth (E g)) z θ'') θ'|
          ≤ K1 * Work.FTS.StrongGlobal.Xn6 α g / a₀ := by
      intro θ' hθ'
      rw [br_deriv_congr_slice (fun θ'' hθ'' => (hthpzeq θ'' hθ'').symm) hθ']
      exact hDth2pz θ' hθ'
    have h := br_slice_interp (f := fun θ'' => Work.Spaces.pz (Work.Spaces.pth (E g)) z θ'')
      (C := K1 * Work.FTS.StrongGlobal.Xn6 α g / a₀) hd hb hθ
    calc |Work.Spaces.pz (Work.Spaces.pth (E g)) z θ|
        ≤ |Work.Spaces.pz (Work.Spaces.pth (E g)) z (π / 4)|
            + K1 * Work.FTS.StrongGlobal.Xn6 α g / a₀ * (π / 2) := h
      _ ≤ Km * Work.FTS.StrongGlobal.Xn6 α g / a₀
            + K1 * Work.FTS.StrongGlobal.Xn6 α g / a₀ * (π / 2) := by linarith
      _ = (Km + K1 * (π / 2)) / a₀ * Work.FTS.StrongGlobal.Xn6 α g := by ring
  -- ## the angular derivative of `∂_z² (E g)`
  have hpzzpth : |Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pz (E g))) z θ|
      ≤ (2 * Km + (π / 2) * (K1 + K2)) / a₀ ^ 2 * Work.FTS.StrongGlobal.Xn6 α g := by
    -- Clairaut: `∂_θ ∂_z² Ψ = ∂_z² ∂_θ Ψ`
    have hclai : ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
        Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pz (E g))) z θ'
          = Work.Spaces.pzIter 2 (Work.Spaces.pth (E g)) z θ' :=
      fun θ' hθ' => (br_pzIter_two_pth_comm_of_smoothOpen hΨsm hzpos hθ').symm
    -- Clairaut: `∂_z² ∂_θ Ψ = ∂_θ (∂_z² Ψ)`
    have hclai2 : ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
        Work.Spaces.pzIter 2 (Work.Spaces.pth (E g)) z θ'
          = Work.Spaces.pth (Work.Spaces.pzIter 2 (E g)) z θ' :=
      fun θ' hθ' => br_pzIter_two_pth_comm_of_smoothOpen hΨsm hzpos hθ'
    -- the pointwise identity `z² ∂_z² = D_z² - D_z` for the slice `∂_θ Ψ`
    have hslice : ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
        ContDiffOn ℝ 2 (fun z' => Work.Spaces.pth (E g) z' θ') (Set.Ioi 0) :=
      fun θ' hθ' => (hΨsm.pth).curry_z hθ' |>.of_le (by norm_num)
    have hsq : ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
        z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pth (E g)) z θ'
          = Work.Spaces.DzIter 2 (Work.Spaces.pth (E g)) z θ'
            - Work.Spaces.DzIter 1 (Work.Spaces.pth (E g)) z θ' := by
      intro θ' hθ'
      have h := Work.FTS_EllLimOK.ProducerH.SecondDeriv.zsq_pzIter_two_eq
        (h := Work.Spaces.pth (E g)) hslice hzpos hθ'
      simpa only [Work.Spaces.mixed_zero_right] using h
    -- the value at the midpoint
    have hval : |Work.Spaces.pzIter 2 (Work.Spaces.pth (E g)) z (π / 4)|
        ≤ 2 * Km * Work.FTS.StrongGlobal.Xn6 α g / a₀ ^ 2 := by
      have h1 := hKm g hg 2 1 (by norm_num) z (π / 4) ⟨hzpos, br_quarter_mem⟩
      have h2 := hKm g hg 1 1 (by norm_num) z (π / 4) ⟨hzpos, br_quarter_mem⟩
      have hz2 : 0 < z ^ 2 := by positivity
      have hbound : z ^ 2 * |Work.Spaces.pzIter 2 (Work.Spaces.pth (E g)) z (π / 4)|
          ≤ 2 * Km * Work.FTS.StrongGlobal.Xn6 α g := by
        calc z ^ 2 * |Work.Spaces.pzIter 2 (Work.Spaces.pth (E g)) z (π / 4)|
            = |z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pth (E g)) z (π / 4)| := by
              rw [abs_mul, abs_of_pos hz2]
          _ = |Work.Spaces.DzIter 2 (Work.Spaces.pth (E g)) z (π / 4)
                - Work.Spaces.DzIter 1 (Work.Spaces.pth (E g)) z (π / 4)| := by
              rw [hsq (π / 4) br_quarter_mem]
          _ ≤ |Work.Spaces.DzIter 2 (Work.Spaces.pth (E g)) z (π / 4)|
                + |Work.Spaces.DzIter 1 (Work.Spaces.pth (E g)) z (π / 4)| :=
              br_abs_sub_le_abs_add_abs _ _
          _ = |Work.Spaces.mixed 2 1 (E g) z (π / 4)|
                + |Work.Spaces.mixed 1 1 (E g) z (π / 4)| := by
              rw [← br_mixed_quarter_eq (E g) 2 z, ← br_mixed_quarter_eq (E g) 1 z]
          _ ≤ Km * Work.FTS.StrongGlobal.Xn6 α g + Km * Work.FTS.StrongGlobal.Xn6 α g :=
              add_le_add h1 h2
          _ = 2 * Km * Work.FTS.StrongGlobal.Xn6 α g := by ring
      exact br_le_div_const (x := |Work.Spaces.pzIter 2 (Work.Spaces.pth (E g)) z (π / 4)|)
        (A := 2 * Km * Work.FTS.StrongGlobal.Xn6 α g) (z := z ^ 2) (c := a₀ ^ 2)
        (by positivity) (by positivity) (by positivity) (by nlinarith [ha₀, hz.1]) hbound
    -- the second angular derivative of `∂_z² Ψ`
    have hder : ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
        |deriv (deriv (fun θ'' => Work.Spaces.pzIter 2 (E g) z θ'')) θ'|
          ≤ (K1 + K2) * Work.FTS.StrongGlobal.Xn6 α g / a₀ ^ 2 := by
      intro θ' hθ'
      have hpoint : ∀ θ'' ∈ Set.Ioo (0 : ℝ) (π / 2),
          Work.Spaces.DzIter 2 (E g) z θ''
            = z ^ 2 * Work.Spaces.pzIter 2 (E g) z θ'' + z * Work.Spaces.pz (E g) z θ'' := by
        intro θ'' hθ''
        have h := Work.FTS_EllLimOK.ProducerH.SecondDeriv.zsq_pzIter_two_eq (h := E g)
          (fun θ3 h3 => (hΨsm.curry_z h3).of_le (by norm_num)) hzpos hθ''
        simp only [Work.Spaces.mixed_zero_right] at h
        have h1 : Work.Spaces.DzIter 1 (E g) z θ'' = z * Work.Spaces.pz (E g) z θ'' := rfl
        linarith [h, h1]
      have hsecond : deriv (deriv (fun θ'' => z ^ 2 * Work.Spaces.pzIter 2 (E g) z θ''
              + z * Work.Spaces.pz (E g) z θ'')) θ'
          = z ^ 2 * deriv (deriv (fun θ'' => Work.Spaces.pzIter 2 (E g) z θ'')) θ'
            + z * deriv (deriv (fun θ'' => Work.Spaces.pz (E g) z θ'')) θ' := by
        have hinner : ∀ θ3 ∈ Set.Ioo (0 : ℝ) (π / 2),
            deriv (fun θ'' => z ^ 2 * Work.Spaces.pzIter 2 (E g) z θ''
              + z * Work.Spaces.pz (E g) z θ'') θ3
            = z ^ 2 * deriv (fun θ'' => Work.Spaces.pzIter 2 (E g) z θ'') θ3
              + z * deriv (fun θ'' => Work.Spaces.pz (E g) z θ'') θ3 := by
          intro θ3 hθ3
          have hd2 : DifferentiableAt ℝ
              (fun θ'' => z ^ 2 * Work.Spaces.pzIter 2 (E g) z θ'') θ3 :=
            ((hΨsm.pzIter 2).curry_θ hzpos |>.differentiableOn (by simp)).differentiableAt
              (isOpen_Ioo.mem_nhds hθ3) |>.const_mul (z ^ 2)
          have hd1 : DifferentiableAt ℝ
              (fun θ'' => z * Work.Spaces.pz (E g) z θ'') θ3 :=
            ((hΨsm.pz).curry_θ hzpos |>.differentiableOn (by simp)).differentiableAt
              (isOpen_Ioo.mem_nhds hθ3) |>.const_mul z
          rw [show (fun θ'' => z ^ 2 * Work.Spaces.pzIter 2 (E g) z θ''
                + z * Work.Spaces.pz (E g) z θ'')
              = (fun θ'' => z ^ 2 * Work.Spaces.pzIter 2 (E g) z θ'')
                + (fun θ'' => z * Work.Spaces.pz (E g) z θ'') from rfl,
            deriv_add hd2 hd1, deriv_const_mul_field, deriv_const_mul_field]
        rw [br_deriv_congr_slice hinner hθ']
        have hd2' : DifferentiableAt ℝ (fun θ3 => z ^ 2 * deriv
            (fun θ'' => Work.Spaces.pzIter 2 (E g) z θ'') θ3) θ' :=
          ((hΨsm.pzIter 2).pth.curry_θ hzpos |>.differentiableOn (by simp)).differentiableAt
            (isOpen_Ioo.mem_nhds hθ') |>.const_mul (z ^ 2)
        have hd1' : DifferentiableAt ℝ (fun θ3 => z * deriv
            (fun θ'' => Work.Spaces.pz (E g) z θ'') θ3) θ' :=
          ((hΨsm.pz).pth.curry_θ hzpos |>.differentiableOn (by simp)).differentiableAt
            (isOpen_Ioo.mem_nhds hθ') |>.const_mul z
        rw [show (fun θ3 => z ^ 2 * deriv (fun θ'' => Work.Spaces.pzIter 2 (E g) z θ'') θ3
              + z * deriv (fun θ'' => Work.Spaces.pz (E g) z θ'') θ3)
            = (fun θ3 => z ^ 2 * deriv (fun θ'' => Work.Spaces.pzIter 2 (E g) z θ'') θ3)
              + (fun θ3 => z * deriv (fun θ'' => Work.Spaces.pz (E g) z θ'') θ3) from rfl,
            deriv_add hd2' hd1', deriv_const_mul_field, deriv_const_mul_field]
      have hexp : deriv (deriv (fun θ'' => Work.Spaces.DzIter 2 (E g) z θ'')) θ'
          = z ^ 2 * deriv (deriv (fun θ'' => Work.Spaces.pzIter 2 (E g) z θ'')) θ'
            + z * deriv (deriv (fun θ'' => Work.Spaces.pz (E g) z θ'')) θ' := by
        rw [br_deriv_deriv_congr_slice hpoint hθ', hsecond]
      have hK2' := hK2 g hg z hz θ' hθ'
      rw [hexp] at hK2'
      have hK1' := hDth2pz θ' hθ'
      have hz2 : 0 < z ^ 2 := by positivity
      let A : ℝ := deriv (deriv (fun θ'' => Work.Spaces.pzIter 2 (E g) z θ'')) θ'
      let B : ℝ := deriv (deriv (fun θ'' => Work.Spaces.pz (E g) z θ'')) θ'
      have h1 : |z ^ 2 * A| ≤ |z ^ 2 * A + z * B| + |z * B| := by
        have h := br_abs_sub_le_abs_add_abs (z ^ 2 * A + z * B) (z * B)
        have he : z ^ 2 * A + z * B - z * B = z ^ 2 * A := by ring
        rwa [he] at h
      have h4 : |z ^ 2 * A + z * B| ≤ K2 * Work.FTS.StrongGlobal.Xn6 α g := hK2'
      have h5 : z * |B| ≤ z * (K1 * Work.FTS.StrongGlobal.Xn6 α g / a₀) :=
        mul_le_mul_of_nonneg_left hK1' hzpos.le
      have h2 : |z ^ 2 * A| = z ^ 2 * |A| := by rw [abs_mul, abs_of_pos hz2]
      have h3 : |z * B| = z * |B| := by rw [abs_mul, abs_of_pos hzpos]
      rw [h2, h3] at h1
      have hmain : z ^ 2 * |A| ≤ K2 * Work.FTS.StrongGlobal.Xn6 α g
          + z * (K1 * Work.FTS.StrongGlobal.Xn6 α g / a₀) := by linarith [h1, h4, h5]
      have hAa : |A| * a₀ ^ 2 ≤ (K1 + K2) * Work.FTS.StrongGlobal.Xn6 α g := by
        have htz : a₀ ^ 2 / z ^ 2 ≤ 1 := by
          rw [div_le_one hz2]; nlinarith [ha₀, hz.1]
        have hta : a₀ / z ≤ 1 := by
          rw [div_le_one hzpos]; exact hz.1
        calc |A| * a₀ ^ 2 = (z ^ 2 * |A|) * (a₀ ^ 2 / z ^ 2) := by field_simp
          _ ≤ (K2 * Work.FTS.StrongGlobal.Xn6 α g
                + z * (K1 * Work.FTS.StrongGlobal.Xn6 α g / a₀)) * (a₀ ^ 2 / z ^ 2) :=
              mul_le_mul_of_nonneg_right hmain (by positivity)
          _ = K2 * Work.FTS.StrongGlobal.Xn6 α g * (a₀ ^ 2 / z ^ 2)
                + K1 * Work.FTS.StrongGlobal.Xn6 α g * (a₀ / z) := by field_simp
          _ ≤ K2 * Work.FTS.StrongGlobal.Xn6 α g * 1
                + K1 * Work.FTS.StrongGlobal.Xn6 α g * 1 := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left htz (by positivity)
              · exact mul_le_mul_of_nonneg_left hta (by positivity)
          _ = (K1 + K2) * Work.FTS.StrongGlobal.Xn6 α g := by ring
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < a₀ ^ 2)]
      exact hAa
    -- the derivative of `θ'' ↦ ∂_z² ∂_θ Ψ`
    have hb : ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
        |deriv (fun θ'' => Work.Spaces.pzIter 2 (Work.Spaces.pth (E g)) z θ'') θ'|
          ≤ (K1 + K2) * Work.FTS.StrongGlobal.Xn6 α g / a₀ ^ 2 := by
      intro θ' hθ'
      rw [br_deriv_congr_slice hclai2 hθ']
      exact hder θ' hθ'
    have hd : ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
        DifferentiableAt ℝ
          (fun θ'' => Work.Spaces.pzIter 2 (Work.Spaces.pth (E g)) z θ'') θ' :=
      fun θ' hθ' => (((hΨsm.pth).pzIter 2).curry_θ hzpos |>.differentiableOn (by simp))
        |>.differentiableAt (isOpen_Ioo.mem_nhds hθ')
    have h := br_slice_interp
      (f := fun θ'' => Work.Spaces.pzIter 2 (Work.Spaces.pth (E g)) z θ'')
      (C := (K1 + K2) * Work.FTS.StrongGlobal.Xn6 α g / a₀ ^ 2) hd hb hθ
    calc |Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pz (E g))) z θ|
        = |Work.Spaces.pzIter 2 (Work.Spaces.pth (E g)) z θ| := by rw [hclai θ hθ]
      _ ≤ |Work.Spaces.pzIter 2 (Work.Spaces.pth (E g)) z (π / 4)|
            + (K1 + K2) * Work.FTS.StrongGlobal.Xn6 α g / a₀ ^ 2 * (π / 2) := h
      _ ≤ 2 * Km * Work.FTS.StrongGlobal.Xn6 α g / a₀ ^ 2
            + (K1 + K2) * Work.FTS.StrongGlobal.Xn6 α g / a₀ ^ 2 * (π / 2) := by linarith
      _ = (2 * Km + (π / 2) * (K1 + K2)) / a₀ ^ 2 * Work.FTS.StrongGlobal.Xn6 α g := by ring
  -- ## the second angular derivative of `∂_z (E g)`
  have hth2pzeq : Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz (E g))) z θ
      = deriv (deriv (fun θ'' => Work.Spaces.pz (E g) z θ'')) θ := rfl
  have hpth2pz : |Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz (E g))) z θ|
      ≤ K1 * Work.FTS.StrongGlobal.Xn6 α g / a₀ := by
    have h := hK1 g hg z hz θ hθ
    have hident : deriv (deriv (fun θ'' => Work.Spaces.DzIter 1 (E g) z θ'')) θ
        = z * deriv (deriv (fun θ'' => Work.Spaces.pz (E g) z θ'')) θ :=
      br_deriv_deriv_const_mul z z θ (Work.Spaces.pz (E g))
    rw [hident, abs_mul, abs_of_pos hzpos] at h
    rw [hth2pzeq]
    exact br_le_div_const hzpos (by positivity) ha₀ hz.1 h
  -- ## the two rate clauses, from the hypothesis
  have hder2 : |deriv (deriv (fun θ' => (E g) z θ')) θ|
      ≤ K * Work.FTS.StrongGlobal.Xn6 α g * (min θ (π / 2 - θ)) ^ β := hmod g hg z hz θ hθ
  have hpowθ : (min θ (π / 2 - θ)) ^ β ≤ θ ^ β := Real.rpow_le_rpow hm0 hmθ hβ.le
  have hpowπ : (min θ (π / 2 - θ)) ^ β ≤ (π / 2 - θ) ^ β := Real.rpow_le_rpow hm0 hmπ hβ.le
  have hth2eq : Work.Spaces.pth (Work.Spaces.pth (E g)) z θ
      = deriv (deriv (fun θ' => (E g) z θ')) θ := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact br_squeeze_plain hpth1 (by positivity) hCA2 hX0
  · have := hpzpth
    rw [← hthpzeq θ hθ] at this
    exact br_squeeze_plain this (by positivity) hCA5 hX0
  · exact br_squeeze_plain hpzpth (by positivity) hCA5 hX0
  · exact br_squeeze_plain hpth2 (by positivity) hCA6 hX0
  · exact br_squeeze_plain hpzzpth (by positivity) hCA7 hX0
  · rw [hth2pzeq]
    have he : K1 * Work.FTS.StrongGlobal.Xn6 α g / a₀
        = (K1 / a₀) * Work.FTS.StrongGlobal.Xn6 α g := by ring
    rw [he] at hpth2pz
    exact br_squeeze_plain hpth2pz (by positivity) hCA8 hX0
  · rw [hth2eq]
    calc |deriv (deriv (fun θ' => (E g) z θ')) θ|
        ≤ K * Work.FTS.StrongGlobal.Xn6 α g * (min θ (π / 2 - θ)) ^ β := hder2
      _ ≤ K * Work.FTS.StrongGlobal.Xn6 α g * θ ^ β := by
          apply mul_le_mul_of_nonneg_left hpowθ
          positivity
      _ ≤ C * Work.FTS.StrongGlobal.Xn6 α g * θ ^ β := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hθ.1.le β)
          exact mul_le_mul_of_nonneg_right hCK hX0
  · rw [hth2eq]
    calc |deriv (deriv (fun θ' => (E g) z θ')) θ|
        ≤ K * Work.FTS.StrongGlobal.Xn6 α g * (min θ (π / 2 - θ)) ^ β := hder2
      _ ≤ K * Work.FTS.StrongGlobal.Xn6 α g * (π / 2 - θ) ^ β := by
          apply mul_le_mul_of_nonneg_left hpowπ
          positivity
      _ ≤ C * Work.FTS.StrongGlobal.Xn6 α g * (π / 2 - θ) ^ β := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith [hθ.2]) β)
          exact mul_le_mul_of_nonneg_right hCK hX0

end Work.FTS_EllLimOK.ProducerH.H2

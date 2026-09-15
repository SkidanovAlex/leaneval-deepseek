import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.UniformSpace.Uniformizable

open MeasureTheory Metric
open scoped ENNReal Topology

namespace Commons.MeasureTheory.Integral

/-! ## A radial smooth bump on `ℂ`

We build a smooth, nonnegative, compactly supported function `phi : ℂ → ℝ` that is invariant
under multiplication by unit complex numbers of modulus `1`, is nonzero at `0`, and vanishes
outside the closed unit ball.  It is obtained by composing a `ContDiffBump` on `ℝ` with the
smooth function `Complex.normSq`.
-/

private lemma contDiff_normSq : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => Complex.normSq z) := by
  have h : (fun z : ℂ => Complex.normSq z) =
      fun z : ℂ => (Complex.reCLM z) * (Complex.reCLM z) +
        (Complex.imCLM z) * (Complex.imCLM z) := by
    funext z; rw [Complex.normSq_apply, Complex.reCLM_apply, Complex.imCLM_apply]
  rw [h]
  exact ((Complex.reCLM.contDiff (𝕜 := ℝ) (n := (⊤ : ℕ∞))).mul
      (Complex.reCLM.contDiff (𝕜 := ℝ) (n := (⊤ : ℕ∞)))).add
    ((Complex.imCLM.contDiff (𝕜 := ℝ) (n := (⊤ : ℕ∞))).mul
      (Complex.imCLM.contDiff (𝕜 := ℝ) (n := (⊤ : ℕ∞))))

private noncomputable def baseBump : ContDiffBump (0 : ℝ) :=
  { rIn := 1 / 2, rOut := 1, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }

private noncomputable def phi : ℂ → ℝ := fun z => baseBump (Complex.normSq z)

private lemma phi_contDiff : ContDiff ℝ (⊤ : ℕ∞) phi := by
  have hb : ContDiff ℝ (⊤ : ℕ∞) (baseBump : ℝ → ℝ) := baseBump.contDiff (n := ⊤)
  exact hb.comp contDiff_normSq

private lemma phi_nonneg (z : ℂ) : 0 ≤ phi z := baseBump.nonneg

private lemma phi_zero : phi 0 = 1 := by
  simp only [phi, Complex.normSq_zero]
  exact baseBump.one_of_mem_closedBall (mem_closedBall_self baseBump.rIn_pos.le)

private lemma phi_support_le (z : ℂ) (h : phi z ≠ 0) : ‖z‖ ≤ 1 := by
  have hmem : Complex.normSq z ∈ Function.support baseBump := by
    rw [Function.mem_support]
    simpa only [phi] using h
  rw [baseBump.support_eq, mem_ball, Real.dist_eq, sub_zero,
    abs_of_nonneg (Complex.normSq_nonneg z)] at hmem
  rw [Complex.normSq_eq_norm_sq] at hmem
  have hlt : ‖z‖ ^ 2 < 1 := by simpa only [baseBump] using hmem
  have : ‖z‖ < 1 := by nlinarith [norm_nonneg z]
  linarith

private lemma phi_radial (z c : ℂ) (hc : ‖c‖ = 1) : phi (c * z) = phi z := by
  have h : Complex.normSq (c * z) = Complex.normSq z := by
    rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq, hc, one_pow, one_mul]
  simp only [phi, h]

private lemma phi_hasCompactSupport : HasCompactSupport phi := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) 1) (fun z hz => ?_)
  by_contra h
  exact hz (by rw [mem_closedBall, dist_zero_right]; exact phi_support_le z h)

private lemma phi_integrable : Integrable phi volume :=
  phi_contDiff.continuous.integrable_of_hasCompactSupport phi_hasCompactSupport

private lemma phi_integral_pos : 0 < ∫ z : ℂ, phi z :=
  integral_pos_of_integrable_nonneg_nonzero phi_contDiff.continuous phi_integrable
    (fun z => phi_nonneg z) (x := 0) (by rw [phi_zero]; norm_num)

/-! ## The scaled family -/

private noncomputable def aa (n : ℕ) : ℝ := (n : ℝ) + 1

private noncomputable def A : ℝ := ∫ z : ℂ, phi z

private lemma A_pos : 0 < A := by
  simpa only [A] using phi_integral_pos

private lemma aa_pos (n : ℕ) : 0 < aa n := by
  unfold aa; positivity

private noncomputable def kf (n : ℕ) (s : ℂ) : ℝ :=
  (aa n ^ 2 / A) * phi (aa n • s)

private noncomputable def Kf (d : ℕ) (n : ℕ) (s : Fin d → ℂ) : ℝ := ∏ j, kf n (s j)

private lemma one_div_nat_succ (n : ℕ) : (1 : ℝ) / (n + 1) = (aa n)⁻¹ := by
  simp only [one_div, aa]

private lemma kf_nonneg (n : ℕ) (s : ℂ) : 0 ≤ kf n s := by
  rw [kf]
  exact mul_nonneg (div_nonneg (sq_nonneg _) A_pos.le) (phi_nonneg _)

private lemma kf_contDiff (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (kf n) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun s : ℂ => (aa n ^ 2 / A) * phi (aa n • s))
  have hscale : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℂ => aa n • s) := by
    have h : (fun s : ℂ => aa n • s) = fun s : ℂ => (aa n : ℂ) * s := by
      funext s; rw [Complex.real_smul]
    rw [h]
    exact (contDiff_const (c := (aa n : ℂ))).mul contDiff_id
  have hphi : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℂ => phi (aa n • s)) := phi_contDiff.comp hscale
  have h2 := hphi.const_smul (aa n ^ 2 / A)
  simpa only [smul_eq_mul] using h2

private lemma kf_continuous (n : ℕ) : Continuous (kf n) := (kf_contDiff n).continuous

private lemma kf_radial (n : ℕ) (s c : ℂ) (hc : ‖c‖ = 1) : kf n (c * s) = kf n s := by
  have h1 : aa n • (c * s) = c * (aa n • s) := by
    rw [Complex.real_smul, Complex.real_smul]
    ring
  have : phi (aa n • (c * s)) = phi (aa n • s) := by
    rw [h1, phi_radial (aa n • s) c hc]
  simp only [kf]
  rw [this]

private lemma kf_support_bound (n : ℕ) (s : ℂ) (h : kf n s ≠ 0) :
    ‖s‖ ≤ 1 / (n + 1) := by
  have ha := aa_pos n
  have hphi : phi (aa n • s) ≠ 0 := by
    intro hc
    exact h (by simp only [kf, hc, mul_zero])
  have hnorm : ‖aa n • s‖ ≤ 1 := phi_support_le _ hphi
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha] at hnorm
  have hle : ‖s‖ ≤ (aa n)⁻¹ := by
    have : ‖s‖ ≤ 1 / (aa n) := (le_div_iff₀ ha).mpr (by linarith)
    simpa only [one_div] using this
  rwa [one_div_nat_succ n]

private lemma kf_support_subset (n : ℕ) :
    Function.support (kf n) ⊆ Metric.closedBall 0 (1 / (n + 1)) := by
  intro s hs
  rw [Function.mem_support] at hs
  rw [mem_closedBall, dist_zero_right]
  exact kf_support_bound n s hs

private lemma kf_hasCompactSupport (n : ℕ) : HasCompactSupport (kf n) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (1 / (n + 1)))
    (fun s hs => ?_)
  by_contra h
  exact hs (kf_support_subset n (Function.mem_support.mpr h))

private lemma kf_integral (n : ℕ) : ∫ s : ℂ, kf n s = 1 := by
  have ha := aa_pos n
  have hcomp : ∫ s : ℂ, phi (aa n • s) = (aa n ^ 2)⁻¹ * A := by
    rw [Measure.integral_comp_smul_of_nonneg (μ := volume) (f := phi) (R := aa n) (hR := ha.le),
      Complex.finrank_real_complex, smul_eq_mul]
    simp only [A]
  have h1 : ∫ s : ℂ, kf n s = (aa n ^ 2 / A) * ∫ s : ℂ, phi (aa n • s) := by
    simp only [kf]
    exact MeasureTheory.integral_const_mul _ _
  rw [h1, hcomp]
  have hAne : A ≠ 0 := A_pos.ne'
  have hane : aa n ≠ 0 := ha.ne'
  field_simp

private lemma Kf_nonneg (d n : ℕ) (s : Fin d → ℂ) : 0 ≤ Kf d n s := by
  have := Finset.prod_nonneg (s := Finset.univ) (f := fun j : Fin d => kf n (s j))
    (fun j _ => kf_nonneg n (s j))
  simpa only [Kf] using this

private lemma Kf_integral (d n : ℕ) : ∫ s : Fin d → ℂ, Kf d n s = 1 := by
  change ∫ s : Fin d → ℂ, (∏ j, kf n (s j)) = 1
  rw [integral_fintype_prod_volume_eq_prod (𝕜 := ℝ) (f := fun (_ : Fin d) => kf n)]
  simp [kf_integral]

private lemma Kf_support_subset (d n : ℕ) :
    Function.support (Kf d n) ⊆ Metric.closedBall 0 (1 / (n + 1)) := by
  intro s hs
  rw [Function.mem_support] at hs
  have hprod : ∏ j, kf n (s j) ≠ 0 := by simpa only [Kf] using hs
  have hcoord : ∀ j : Fin d, kf n (s j) ≠ 0 := by
    intro j
    exact (Finset.prod_ne_zero_iff (s := Finset.univ) (f := fun j : Fin d => kf n (s j))).mp
      hprod j (Finset.mem_univ j)
  rw [mem_closedBall, dist_zero_right]
  exact (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (n + 1))).mpr
    (fun j => kf_support_bound n (s j) (hcoord j))

private lemma Kf_contDiff (d n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (Kf d n) := by
  have hproj : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun s : Fin d → ℂ => s i) := by
    intro i
    have hfun : (fun s : Fin d → ℂ => s i) =
        ⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℂ) i) := by
      funext s; rw [ContinuousLinearMap.proj_apply]
    rw [hfun]
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℂ) i).contDiff
      (𝕜 := ℝ) (n := (⊤ : ℕ∞))
  have hf : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun s : Fin d → ℂ => kf n (s i)) :=
    fun i => (kf_contDiff n).comp (hproj i)
  have h := contDiff_prod (𝕜 := ℝ) (n := (⊤ : ℕ∞)) (t := Finset.univ)
    (f := fun i : Fin d => fun s : Fin d → ℂ => kf n (s i)) (fun i _ => hf i)
  change ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin d → ℂ => ∏ i, kf n (y i))
  exact h

private lemma Kf_hasCompactSupport (d n : ℕ) : HasCompactSupport (Kf d n) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin d → ℂ) (1 / (n + 1)))
    (fun s hs => ?_)
  by_contra h
  exact hs (Kf_support_subset d n (Function.mem_support.mpr h))

theorem exists_product_approximate_identity_complex (d : ℕ) :
    ∃ (k : ℕ → ℂ → ℝ) (K : ℕ → (Fin d → ℂ) → ℝ),
      (∀ (n : ℕ) (s : ℂ), 0 ≤ k n s) ∧
      (∀ n : ℕ, ∫ s : ℂ, k n s = 1) ∧
      (∀ n : ℕ, Continuous (k n)) ∧
      (∀ n : ℕ, HasCompactSupport (k n)) ∧
      (∀ (n : ℕ) (s c : ℂ), ‖c‖ = 1 → k n (c * s) = k n s) ∧
      (∀ (n : ℕ) (s : ℂ), Function.support (k n) ⊆ Metric.closedBall 0 (1 / (n + 1))) ∧
      (∀ (n : ℕ) (s : Fin d → ℂ), K n s = ∏ j, k n (s j)) ∧
      (∀ (n : ℕ) (s : Fin d → ℂ), 0 ≤ K n s) ∧
      (∀ n : ℕ, ∫ s : Fin d → ℂ, K n s = 1) ∧
      (∀ n : ℕ, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (K n)) ∧
      (∀ n : ℕ, HasCompactSupport (K n)) ∧
      (∀ n : ℕ, Function.support (K n) ⊆ Metric.closedBall 0 (1 / (n + 1))) := by
  refine ⟨kf, Kf d, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n s; exact kf_nonneg n s
  · intro n; exact kf_integral n
  · intro n; exact kf_continuous n
  · intro n; exact kf_hasCompactSupport n
  · intro n s c hc; exact kf_radial n s c hc
  · intro n s; exact kf_support_subset n
  · intro n s; rfl
  · intro n s; exact Kf_nonneg d n s
  · intro n; exact Kf_integral d n
  · intro n; exact Kf_contDiff d n
  · intro n; exact Kf_hasCompactSupport d n
  · intro n; exact Kf_support_subset d n

end Commons.MeasureTheory.Integral
/-
# `Work.FTS.PhiStar.Basic` — elementary API of the `Φ_*` decomposition

Everything in this file is unconditional (no `sorry`, no new axioms):

* the moment identity `∫ Γ̄ sinθcos²θ = 0` that makes the angular model solvable;
* the explicit value `F_*(Construction.Fstar α) = α φ/3` of the `sinθcos²θ`-moment of the
  profile, and hence `Θ = ThetaProfile·sin 2θ`, so that
  `Φ̃_* = Aprof·sin 2θ + αφψ + R`;
* the explicit form, the bounds and the decay of `φ = 2z/(1+z)²` and of
  `𝒜φ = αz²φ'' + (5+α)zφ'`;
* the **structural decomposition of `bslOp` on separable products**, which is the algebraic
  content of the telescoping identity `phiStar_remainder_source`:
  `bslOp α (A(z)·ψ(θ)) = A(z)·L₀ψ(θ) − (αz²A'' + (5+α)zA')·ψ(θ)` (`bslOp_sep`), and its
  radial specialisation `bslOp α (A(z)·sin 2θ) = −(αz²A'' + (5+α)zA')·sin 2θ` (`bslOp_radial`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.Elliptic.integral_sin_two_mul_sinCos2
import Submission.Work.Elliptic.Algebra
import Submission.Work.Elliptic.bslOp_add
import Submission.Work.Elliptic.L12_profile
import Submission.Work.Construction.L12_Fstar_eq
import Submission.Work.FTS.H2.PhiStarE.Gbar_wiln
import Submission.Work.Spaces.c_bounds
import Submission.Work.Spaces.CAux.integrableOn_GamK
import Submission.Work.Spaces.Gamma_WlInf

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Rational decay helpers -/

/-- `z^k/(1+z)^m → 0` for `k < m`: eventually equal to
`(z/(1+z))^k · ((1+z)^{-1})^{m-k}`, a product of a quantity tending to `1` and one to `0`. -/
theorem tendsto_pow_div_pow_atTop {k m : ℕ} (h : k < m) :
    Tendsto (fun z : ℝ => z ^ k / (1 + z) ^ m) atTop (𝓝 0) := by
  have hz1 : Tendsto (fun z : ℝ => (1 + z)) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1 tendsto_id
  have hinv : Tendsto (fun z : ℝ => (1 + z)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hz1
  have hratio : Tendsto (fun z : ℝ => z / (1 + z)) atTop (𝓝 1) := by
    have hsub : Tendsto (fun z : ℝ => 1 - (1 + z)⁻¹) atTop (𝓝 (1 - 0)) :=
      (tendsto_const_nhds (x := (1 : ℝ))).sub hinv
    rw [sub_zero] at hsub
    refine hsub.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with z hz
    have h1 : (1 : ℝ) + z ≠ 0 := by linarith
    rw [div_eq_mul_inv]
    field_simp
    ring
  have hzero : Tendsto (fun z : ℝ => ((1 + z)⁻¹) ^ (m - k)) atTop (𝓝 0) := by
    have hp := hinv.pow (m - k)
    rw [zero_pow (by omega : m - k ≠ 0)] at hp
    exact hp
  have hprod : Tendsto (fun z : ℝ => (z / (1 + z)) ^ k * ((1 + z)⁻¹) ^ (m - k)) atTop (𝓝 0) := by
    have hh := (hratio.pow k).mul hzero
    simpa using hh
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with z hz
  have h1 : (1 : ℝ) + z ≠ 0 := by linarith
  rw [div_pow, inv_pow, div_eq_mul_inv, mul_assoc, ← mul_inv, ← pow_add,
    Nat.add_sub_cancel' h.le, div_eq_mul_inv]

/-! ## The angular moment of `Γ̄` -/

/-- `∫_0^{π/2} Γ(θ) sin θ cos²θ dθ = c/3`, because `K = 3 sin θ cos²θ`. -/
theorem integral_Gam_sinCos2 (α : ℝ) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.Gam α θ * Work.Elliptic.sinCos2 θ)
      = Work.Spaces.c α / 3 := by
  have hK : Work.Spaces.K = fun θ : ℝ => 3 * Work.Elliptic.sinCos2 θ := by
    funext θ; simp only [Work.Spaces.K, Work.Elliptic.sinCos2]; ring
  have h1 : Work.Spaces.c α
      = ∫ θ in Work.Spaces.Iθ, 3 * (Work.Spaces.Gam α θ * Work.Elliptic.sinCos2 θ) := by
    rw [Work.Spaces.c, hK]
    refine setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
    ring
  rw [h1, MeasureTheory.integral_const_mul]
  ring

/-- **The moment condition of the angular model**: `∫_0^{π/2} Γ̄(θ) sin θ cos²θ dθ = 0`, where
`Γ̄ = Γ/c − (5/4) sin 2θ`.  This is the solvability condition of `L₀ψ = Γ̄` with Dirichlet data
(`sin θ cos²θ` spans the kernel of the formal adjoint of `L₀`), and it is also what makes the
remainder source `α²(𝒜φ)ψ` orthogonal to `sin θ cos²θ`. -/
theorem GamBar_moment {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.VocabO.GamBar α θ * Work.Elliptic.sinCos2 θ) = 0 := by
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0; rw [h0] at h; norm_num at h
  have hGK : IntegrableOn (fun θ : ℝ => Work.Spaces.Gam α θ * Work.Spaces.K θ)
      Work.Spaces.Iθ := Work.Spaces.CAux.integrableOn_GamK α hα
  have hsin : IntegrableOn (fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := by
    have hcont : Continuous fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ := by
      simp only [Work.Elliptic.sinCos2]; fun_prop
    exact hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hpt : ∀ θ : ℝ, Work.FTS.VocabO.GamBar α θ * Work.Elliptic.sinCos2 θ
      = (1 / (3 * Work.Spaces.c α)) * (Work.Spaces.Gam α θ * Work.Spaces.K θ)
        - (5 / 4) * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ) := by
    intro θ
    rw [Work.FTS.VocabO.GamBar, Work.Spaces.K, Work.Elliptic.sinCos2]
    field_simp
  rw [setIntegral_congr_fun (s := Work.Spaces.Iθ) measurableSet_Icc fun θ _ => hpt θ]
  rw [integral_sub (hGK.const_mul _) (hsin.const_mul _), MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul]
  rw [show (∫ θ in Work.Spaces.Iθ, Work.Spaces.Gam α θ * Work.Spaces.K θ)
        = Work.Spaces.c α from rfl, Work.Elliptic.integral_sin_two_mul_sinCos2]
  have hone : (1 / (3 * Work.Spaces.c α)) * Work.Spaces.c α = 1 / 3 := by
    field_simp
  rw [hone]
  norm_num

/-! ## The profile `φ` and the source `𝒜φ` -/

/-- The profile `φ = VocabO.phiR` is `Work.FM.Fstar` (definitional). -/
theorem phiR_eq_FM_Fstar : Work.FTS.VocabO.phiR = Work.FM.Fstar := rfl

/-- Positivity of `φ` on `z > 0`. -/
theorem phiR_pos {z : ℝ} (hz : 0 < z) : 0 < Work.FTS.VocabO.phiR z := by
  rw [Work.FTS.VocabO.phiR]
  positivity

/-- `φ(z) ≤ 1/2` on `z ≥ 0` (it is `2z/(1+z)² ≤ 1/2 ⟺ 0 ≤ (z−1)²`). -/
theorem phiR_le_half {z : ℝ} (hz : 0 ≤ z) : Work.FTS.VocabO.phiR z ≤ 1 / 2 := by
  rw [Work.FTS.VocabO.phiR, div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
  nlinarith [sq_nonneg (1 - z)]

/-- `φ(z) ≤ 2/z` for `z > 0`. -/
theorem phiR_le_two_div {z : ℝ} (hz : 0 < z) : Work.FTS.VocabO.phiR z ≤ 2 / z := by
  rw [Work.FTS.VocabO.phiR, div_le_div_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 2) hz]
  nlinarith [sq_nonneg (1 + z), hz]

/-- `φ(z) → 0` as `z → ∞`. -/
theorem tendsto_phiR_atTop : Tendsto Work.FTS.VocabO.phiR atTop (𝓝 0) := by
  have h := (tendsto_pow_div_pow_atTop (k := 1) (m := 2) (by norm_num)).const_mul (2 : ℝ)
  rw [mul_zero] at h
  have hfe : (fun z : ℝ => 2 * (z ^ 1 / (1 + z) ^ 2)) = Work.FTS.VocabO.phiR := by
    funext z; rw [Work.FTS.VocabO.phiR, pow_one]; ring
  rwa [hfe] at h

/-- The derivative of `φ`: `φ'(z) = 2(1−z)/(1+z)³`. -/
theorem deriv_phiR {z : ℝ} (hz : z ≠ -1) :
    deriv Work.FTS.VocabO.phiR z = 2 * (1 - z) / (1 + z) ^ 3 := by
  have hden : (1 + z) ≠ 0 := by
    intro h; exact hz (by linarith)
  have hnum : HasDerivAt (fun z : ℝ => 2 * z) 2 z := by
    simpa using (hasDerivAt_id z).const_mul (2 : ℝ)
  have hden' : HasDerivAt (fun z : ℝ => (1 + z) ^ 2) (2 * (1 + z)) z := by
    have h1 : HasDerivAt (fun z : ℝ => 1 + z) 1 z := (hasDerivAt_id z).const_add 1
    have h2 := h1.pow 2
    convert h2 using 1
    ring
  change deriv ((fun z : ℝ => 2 * z) / fun z => (1 + z) ^ 2) z = 2 * (1 - z) / (1 + z) ^ 3
  rw [(hnum.div hden' (pow_ne_zero 2 hden)).deriv]
  field_simp
  ring

/-- The derivative of `z ↦ 2(1−z)/(1+z)³`: `4(z−2)/(1+z)⁴`. -/
theorem deriv_phiR' {z : ℝ} (hz : z ≠ -1) :
    deriv (fun z : ℝ => 2 * (1 - z) / (1 + z) ^ 3) z = 4 * (z - 2) / (1 + z) ^ 4 := by
  have hden : (1 + z) ≠ 0 := by
    intro h; exact hz (by linarith)
  have hnum : HasDerivAt (fun z : ℝ => 2 * (1 - z)) (-2 : ℝ) z := by
    have h1 : HasDerivAt (fun z : ℝ => 1 - z) (-1 : ℝ) z := by
      simpa using (hasDerivAt_id z).const_sub 1
    have h2 := h1.const_mul (2 : ℝ)
    convert h2 using 1
    ring
  have hden' : HasDerivAt (fun z : ℝ => (1 + z) ^ 3) (3 * (1 + z) ^ 2) z := by
    have h1 : HasDerivAt (fun z : ℝ => 1 + z) 1 z := (hasDerivAt_id z).const_add 1
    have h2 := h1.pow 3
    convert h2 using 1
    ring
  change deriv ((fun z : ℝ => 2 * (1 - z)) / fun z => (1 + z) ^ 3) z
      = 4 * (z - 2) / (1 + z) ^ 4
  rw [(hnum.div hden' (pow_ne_zero 3 hden)).deriv]
  field_simp
  ring

/-- The second derivative of `φ`: `φ''(z) = 4(z−2)/(1+z)⁴`. -/
theorem iteratedDeriv_two_phiR {z : ℝ} (hz : z ≠ -1) :
    iteratedDeriv 2 Work.FTS.VocabO.phiR z = 4 * (z - 2) / (1 + z) ^ 4 := by
  have hopen : ∀ᶠ z' in 𝓝 z, z' ≠ -1 := by
    filter_upwards [isOpen_ne.mem_nhds (show z ≠ -1 from hz)] with z' hz'
    exact hz'
  have hderiv : deriv Work.FTS.VocabO.phiR
      =ᶠ[𝓝 z] fun z' => 2 * (1 - z') / (1 + z') ^ 3 := by
    filter_upwards [hopen] with z' hz'
    exact deriv_phiR hz'
  have h2 : iteratedDeriv 2 Work.FTS.VocabO.phiR = deriv (deriv Work.FTS.VocabO.phiR) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2, hderiv.deriv_eq]
  exact deriv_phiR' hz

/-- **The explicit form of `𝒜φ = α z²φ'' + (5+α) z φ'`**. -/
theorem phiA_eq (α z : ℝ) (hz : z ≠ -1) :
    Work.FTS.VocabO.phiA α z
      = 4 * α * z ^ 2 * (z - 2) / (1 + z) ^ 4 + 2 * (5 + α) * z * (1 - z) / (1 + z) ^ 3 := by
  rw [Work.FTS.VocabO.phiA, iteratedDeriv_two_phiR hz, deriv_phiR hz]
  ring

/-- The source coefficient `𝒜φ` is bounded by `20` on `z ≥ 0`, uniformly for `0 < α ≤ 1`. -/
theorem phiA_abs_le {α z : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 ≤ z) :
    |Work.FTS.VocabO.phiA α z| ≤ 20 := by
  have hz1 : z ≠ -1 := by intro h; rw [h] at hz; norm_num at hz
  have hp : (0 : ℝ) < 1 + z := by linarith
  have hz2 : (0 : ℝ) ≤ z ^ 2 := sq_nonneg z
  have habs1 : |z - 2| ≤ z + 2 := by rw [abs_le]; constructor <;> linarith [hz]
  have habs2 : |1 - z| ≤ 1 + z := by rw [abs_le]; constructor <;> linarith [hz]
  have hP : z ^ 2 * (z + 2) ≤ 2 * (1 + z) ^ 4 := by
    have hexp : 2 * (1 + z) ^ 4 - z ^ 2 * (z + 2)
        = 2 * z ^ 4 + 7 * z ^ 3 + 10 * z ^ 2 + 8 * z + 2 := by ring
    have hkey : (0 : ℝ) ≤ 2 * z ^ 4 + 7 * z ^ 3 + 10 * z ^ 2 + 8 * z + 2 := by positivity
    linarith
  have hQ : z * (1 + z) ≤ (1 + z) ^ 3 := by
    have hexp : (1 + z) ^ 3 - z * (1 + z) = (1 + z) * (1 + z + z ^ 2) := by ring
    have hkey : (0 : ℝ) ≤ (1 + z) * (1 + z + z ^ 2) := by positivity
    linarith
  have hnum1 : 4 * α * z ^ 2 * |z - 2| ≤ 8 * (1 + z) ^ 4 := by
    have h5 : z ^ 2 * |z - 2| ≤ z ^ 2 * (z + 2) := mul_le_mul_of_nonneg_left habs1 hz2
    have h6 : 4 * α * (z ^ 2 * |z - 2|) ≤ 4 * α * (2 * (1 + z) ^ 4) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h7 : 4 * α * (2 * (1 + z) ^ 4) ≤ 8 * (1 + z) ^ 4 := by
      have h8 : α * (8 * (1 + z) ^ 4) ≤ 1 * (8 * (1 + z) ^ 4) :=
        mul_le_mul_of_nonneg_right hα1 (by positivity)
      linarith
    calc 4 * α * z ^ 2 * |z - 2| = 4 * α * (z ^ 2 * |z - 2|) := by ring
      _ ≤ 4 * α * (2 * (1 + z) ^ 4) := h6
      _ ≤ 8 * (1 + z) ^ 4 := h7
  have hnum2 : 2 * (5 + α) * z * |1 - z| ≤ 12 * (1 + z) ^ 3 := by
    have hsa : 2 * (5 + α) ≤ 12 := by linarith
    have hzab : z * |1 - z| ≤ z * (1 + z) := mul_le_mul_of_nonneg_left habs2 hz
    have h6 : 2 * (5 + α) * z * |1 - z| ≤ 12 * (z * (1 + z)) := by
      have hh : 2 * (5 + α) * (z * |1 - z|) ≤ 12 * (z * (1 + z)) :=
        mul_le_mul hsa hzab (by positivity) (by positivity)
      calc 2 * (5 + α) * z * |1 - z| = 2 * (5 + α) * (z * |1 - z|) := by ring
        _ ≤ 12 * (z * (1 + z)) := hh
    have h7 : 12 * (z * (1 + z)) ≤ 12 * (1 + z) ^ 3 :=
      mul_le_mul_of_nonneg_left hQ (by norm_num)
    linarith
  have h4 : (0 : ℝ) < (1 + z) ^ 4 := by positivity
  have h3 : (0 : ℝ) < (1 + z) ^ 3 := by positivity
  have hterm1 : |4 * α * z ^ 2 * (z - 2) / (1 + z) ^ 4| ≤ 8 := by
    rw [abs_div, abs_of_pos h4, div_le_iff₀ h4]
    have habs : |4 * α * z ^ 2 * (z - 2)| = 4 * α * z ^ 2 * |z - 2| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos hα,
        abs_of_nonneg hz2]
    rw [habs]
    exact hnum1
  have hterm2 : |2 * (5 + α) * z * (1 - z) / (1 + z) ^ 3| ≤ 12 := by
    rw [abs_div, abs_of_pos h3, div_le_iff₀ h3]
    have habs : |2 * (5 + α) * z * (1 - z)| = 2 * (5 + α) * z * |1 - z| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos (by linarith : (0 : ℝ) < 5 + α), abs_of_nonneg hz]
    rw [habs]
    exact hnum2
  rw [phiA_eq α z hz1]
  calc |4 * α * z ^ 2 * (z - 2) / (1 + z) ^ 4 + 2 * (5 + α) * z * (1 - z) / (1 + z) ^ 3|
      ≤ |4 * α * z ^ 2 * (z - 2) / (1 + z) ^ 4|
        + |2 * (5 + α) * z * (1 - z) / (1 + z) ^ 3| := abs_add_le _ _
    _ ≤ 20 := by linarith

/-- **The source coefficient `𝒜φ` vanishes at infinity** (used for the decay of `RemSource`). -/
theorem tendsto_phiA_atTop (α : ℝ) :
    Tendsto (fun z => Work.FTS.VocabO.phiA α z) atTop (𝓝 0) := by
  have h3 := (tendsto_pow_div_pow_atTop (k := 3) (m := 4) (by norm_num)).const_mul (4 * α)
  have h2 := (tendsto_pow_div_pow_atTop (k := 2) (m := 4) (by norm_num)).const_mul (8 * α)
  have h3b := (tendsto_pow_div_pow_atTop (k := 1) (m := 3) (by norm_num)).const_mul (2 * (5 + α))
  have h2b := (tendsto_pow_div_pow_atTop (k := 2) (m := 3) (by norm_num)).const_mul (2 * (5 + α))
  have h := (h3.sub h2).add (h3b.sub h2b)
  simp only [mul_zero, sub_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with z hz
  have hz1 : z ≠ -1 := by intro hh; rw [hh] at hz; norm_num at hz
  rw [phiA_eq α z hz1]
  ring_nf

/-- The remainder source `α²(𝒜φ)ψ` decays at infinity. -/
theorem tendsto_RemSource_atTop (α : ℝ) (ψ : ℝ → ℝ) (θ : ℝ) :
    Tendsto (fun z => RemSource α ψ z θ) atTop (𝓝 0) := by
  have h := (tendsto_phiA_atTop α).const_mul (α ^ 2 * ψ θ)
  simp only [mul_zero] at h
  refine h.congr' ?_
  filter_upwards with z
  simp only [RemSource, mul_assoc, mul_comm]

/-! ## The moment of the profile, and the singular part -/

/-- The angular moment of the profile: `F_*(Construction.Fstar α) = α φ / 3`. -/
theorem Fstar_profile {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Elliptic.Fstar (Work.Construction.Fstar α)
      = fun z => α * Work.FTS.VocabO.phiR z / 3 := by
  rw [Work.FTS.H2.PhiStarE.EllFstar_Fstar α hα hα1]
  funext z
  rw [Work.FTS.VocabO.phiR, Work.FM.Fstar]

/-- `L₁₂(F_*)(z) = 2α/(1+z)` for `z ≥ 0`. -/
theorem L12_profile_eq {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    Work.Construction.L12 (Work.Construction.Fstar α) z = 2 * α / (1 + z) :=
  Work.Construction.L12_Fstar_eq hα hα1 hz

/-- The singular part `Θ = (1/4α) sin 2θ L₁₂(F_*)` is the explicit
`ThetaProfile z · sin 2θ = sin 2θ/(2(1+z))`. -/
theorem Theta_eq_thetaProfile {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {z : ℝ} (hz : 0 ≤ z)
    (θ : ℝ) :
    Work.Construction.Theta α (Work.Construction.Fstar α) z θ
      = ThetaProfile z * Real.sin (2 * θ) := by
  rw [Work.Construction.Theta, Work.Construction.s2, L12_profile_eq hα hα1 hz, ThetaProfile]
  have hαne : α ≠ 0 := ne_of_gt hα
  have hz1 : (1 + z) ≠ 0 := by linarith
  field_simp
  ring

/-! ## The structural decomposition of `bslOp` on separable products -/

/-- `∂_z(A(z)·ψ(θ)) = A'(z)·ψ(θ)` (unconditional in `A`). -/
theorem pz_sep (A : ℝ → ℝ) (ψ : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pz (fun z θ => A z * ψ θ) z θ = deriv A z * ψ θ := by
  rw [Work.Spaces.pz]
  exact Work.Spaces.deriv_mul_const' (ψ θ) z A

/-- `∂_z²(A(z)·ψ(θ)) = A''(z)·ψ(θ)` (unconditional in `A`). -/
theorem pzIter_two_sep (A : ℝ → ℝ) (ψ : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pzIter 2 (fun z θ => A z * ψ θ) z θ = iteratedDeriv 2 A z * ψ θ := by
  have h2 : iteratedDeriv 2 A z = deriv (deriv A) z := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have h1 : Work.Spaces.pzIter 2 (fun z θ => A z * ψ θ)
      = Work.Spaces.pz (Work.Spaces.pz (fun z θ => A z * ψ θ)) := rfl
  rw [h2, h1, Work.Spaces.pz]
  have hfun : (fun z' : ℝ => Work.Spaces.pz (fun z θ => A z * ψ θ) z' θ)
      = fun z' : ℝ => deriv A z' * ψ θ := by
    funext z'; exact pz_sep A ψ z' θ
  rw [hfun]
  exact Work.Spaces.deriv_mul_const' (ψ θ) z (deriv A)

/-- `∂_θ²(A(z)·ψ(θ)) = A(z)·ψ''(θ)`. -/
theorem pthIter_two_sep (A : ℝ → ℝ) (ψ : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter 2 (fun z θ => A z * ψ θ) z θ
      = A z * deriv (fun θ' => deriv ψ θ') θ := by
  have h1 : Work.Spaces.pthIter 2 (fun z θ => A z * ψ θ)
      = Work.Spaces.pth (Work.Spaces.pth (fun z θ => A z * ψ θ)) := rfl
  rw [h1, Work.Spaces.pth]
  have hfun : (fun θ' : ℝ => Work.Spaces.pth (fun z θ => A z * ψ θ) z θ')
      = fun θ' : ℝ => A z * deriv ψ θ' := by
    funext θ'
    rw [Work.Spaces.pth]
    exact Work.Spaces.deriv_const_mul' (A z) θ' ψ
  rw [hfun, Work.Spaces.deriv_const_mul' (A z) θ (deriv ψ)]

/-- `L₀(A(z)ψ(θ)) = A(z)·L₀ψ(θ)`: the `θ`-operator does not see the radial factor. -/
theorem Lzero_sep (A : ℝ → ℝ) (ψ : ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.Lzero (fun z θ => A z * ψ θ) z θ
      = A z * Work.FTS.EllipticEst.Lzero1 ψ θ := by
  have hmid : Work.Spaces.pth (fun z θ => Real.tan θ * (A z * ψ θ)) z θ
      = A z * deriv (fun θ' => Real.tan θ' * ψ θ') θ := by
    rw [Work.Spaces.pth]
    have hfun : (fun θ' : ℝ => Real.tan θ' * (A z * ψ θ'))
        = fun θ' : ℝ => A z * (Real.tan θ' * ψ θ') := by
      funext θ'; ring
    rw [hfun]
    exact Work.Spaces.deriv_const_mul' (A z) θ (fun θ' => Real.tan θ' * ψ θ')
  rw [Work.Elliptic.Lzero, pthIter_two_sep, hmid, Work.FTS.EllipticEst.Lzero1]
  ring

/-- **The separable decomposition of `bslOp`** (the algebraic core of the telescoping
identity): for `Ψ(z,θ) = A(z)·ψ(θ)`,
`bslOp α Ψ = A(z)·L₀ψ(θ) − (α z²A''(z) + (5+α) z A'(z))·ψ(θ)`. -/
theorem bslOp_sep (α : ℝ) (A : ℝ → ℝ) (ψ : ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.bslOp α (fun z θ => A z * ψ θ) z θ
      = A z * Work.FTS.EllipticEst.Lzero1 ψ θ
        - (α ^ 2 * z ^ 2 * iteratedDeriv 2 A z + α * (5 + α) * z * deriv A z) * ψ θ := by
  rw [Work.Elliptic.bslOp_apply, pzIter_two_sep, pz_sep, Lzero_sep]
  ring

/-- **The radial specialisation**: for `Ψ(z,θ) = A(z)·sin 2θ`,
`bslOp α Ψ = −(α z²A'' + (5+α) z A')·sin 2θ` (`sin 2θ` lies in the kernel of `L₀`). -/
theorem bslOp_radial (α : ℝ) (A : ℝ → ℝ) (z θ : ℝ) (hθ : Real.cos θ ≠ 0) :
    Work.Elliptic.bslOp α (fun z θ => A z * Real.sin (2 * θ)) z θ
      = -(α ^ 2 * z ^ 2 * iteratedDeriv 2 A z + α * (5 + α) * z * deriv A z)
          * Real.sin (2 * θ) := by
  rw [Work.Elliptic.bslOp_apply, pzIter_two_sep, pz_sep,
    Work.Elliptic.Lzero_sin_two_mul A z θ hθ]
  ring

end Work.FTS.PhiStar

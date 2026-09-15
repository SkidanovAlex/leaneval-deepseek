import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_bound_m1
import Submission.Commons.NumberTheory.Zeta.zeta_bound_m_v2

namespace Commons.NumberTheory.Zeta

open Complex MeasureTheory
open scoped Topology

open Commons.Analysis.Complex

/-- **Containment of a Green–Tao zero-free region in a fixed strip.**  If `β / log 2 < σ` then
every `z` in the logarithmic region `ZetaReg β` (`-(β/log(|Im z|+2)) ≤ Re z ≤ 1`) satisfies
`-σ < Re z < 100`.  This is the (only) place where the choice of `σ` enters: the logarithmic
region of a *small* `β` is shallow enough to sit inside the fixed strip of width `σ`. -/
lemma ZetaReg_subset_strip {β σ : ℝ} (hβ : 0 ≤ β) (hβσ : β / Real.log 2 < σ) {z : ℂ}
    (hz : ZetaReg β z) : -σ < z.re ∧ z.re < 100 := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hle2 : Real.log 2 ≤ Real.log (|z.im| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg z.im])
  have hle : β / Real.log (|z.im| + 2) ≤ β / Real.log 2 :=
    div_le_div_of_nonneg_left hβ hlog2pos hle2
  constructor
  · have : -(β / Real.log 2) ≤ -(β / Real.log (|z.im| + 2)) := by linarith
    linarith [hz.1]
  · linarith [hz.2]

/-- **`ZetaAux` propagates to every smaller admissible `β`.**

Given the number-theoretic data `D₀ : ZetaAux β₀` at a constant `β₀ ∈ (0, 1/10]`, every
`β ∈ (0, β₀]` again carries such data: the zero-free region for `β` is *contained* in the one for
`β₀`, so the pointwise reciprocal-zeta bound transfers with the same constant `C₁`, while the
remaining fields are produced by the general-purpose commons lemmas (which hold for every
`β ≤ 1/10`). -/
lemma zetaAux_le {β₀ : ℝ} (D₀ : ZetaAux β₀) (hβ₀ : 0 < β₀) (hβ₀10 : β₀ ≤ 1 / 10)
    {β : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1 / 10) (hβle : β ≤ β₀) :
    Nonempty (ZetaAux β) := by
  have hreg : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
      riemannZeta (1 + z) ≠ 0 ∧
      DifferentiableAt ℂ (fun u : ℂ => (riemannZeta (1 + u))⁻¹) z ∧
      ‖(riemannZeta (1 + z))⁻¹‖ ≤ D₀.C₁ * (Real.log (|z.im| + 2) + 1) := by
    intro z hz h1 h2
    have hlogpos : 0 < Real.log (|z.im| + 2) := Real.log_pos (by linarith [abs_nonneg z.im])
    have h1' : -(β₀ / Real.log (|z.im| + 2)) ≤ z.re := by
      have h : β / Real.log (|z.im| + 2) ≤ β₀ / Real.log (|z.im| + 2) :=
        div_le_div_of_nonneg_right hβle hlogpos.le
      linarith
    exact D₀.hreg z hz h1' h2
  have hinvb : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
      ‖(riemannZeta (1 + z))⁻¹‖ ≤ D₀.C₁ * (Real.log (|z.im| + 2) + 1) :=
    fun z hz h1 h2 => (hreg z hz h1 h2).2.2
  obtain ⟨Cn, hCnpos, hCn⟩ := zeta_one_add_add_bound_curve_sqrt_curve (β := β) hβ hβ10
  obtain ⟨Cs, hCspos, hCs⟩ := norm_riemannZeta_le_const_of_one_lt_re (σ := 3 / 2) (by norm_num)
  obtain ⟨Ku, hKupos, hUint, hUle⟩ := Commons.Analysis.Integral.uScaleHalf_integrable
  obtain ⟨Cq, hCqpos, hQle⟩ :=
    gam0_zeta_quartic_integral_le (β := β) hβ hβ10 D₀.C₁ D₀.hC₁pos hinvb
  have hQint := gam0_zeta_quartic_integrable (β := β) hβ hβ10 D₀.C₁ D₀.hC₁pos hinvb
  have hgam_lo : ∀ s : ℝ, -(β / Real.log 2) ≤ (gam β s).re := by
    intro s
    rw [gam_re β s]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hle : β / Real.log (|s| + 2) ≤ β / Real.log 2 :=
      div_le_div_of_nonneg_left hβ.le hlog2
        (Real.log_le_log (by norm_num) (by linarith [abs_nonneg s]))
    linarith
  have hgam_reg' : ∀ s : ℝ, (gam β s).re ≤ -(β / Real.log (|(gam β s).im| + 2)) := by
    intro s; rw [gam_re β s, gam_im]
  have hnum : ∀ t t' : ℝ, ‖riemannZeta (1 + gam β t + gam β t')‖
      ≤ Cn * (|t| + |t'| + 3) ^ ((1:ℝ)/2) := by
    intro t t'
    have h := hCn (gam β t) (gam β t') (hgam_lo t) (hgam_reg' t) (hgam_lo t') (hgam_reg' t')
    simpa [gam_im] using h
  exact ⟨⟨D₀.C₁, Cs, Cn, Ku, Cq, D₀.hC₁pos, hCspos, hCnpos, hKupos, hCqpos, hreg, hCs, hCn,
    hnum, hUint, hUle, hQint, hQle⟩⟩

/-- **Green–Tao's (10.4) contour lemma, in the shape in which Green–Tao use it** (their p. 46).

For every `m ≥ 1` there are constants `σ, δ, C > 0` (depending on `m` only) such that for every
`R ≥ 3` and every `F` on `(ℂ^m)²` that is continuous, holomorphic in each variable on the FIXED
STRIP `S_σ := {z | ∀ j, -σ < Re z_j < 100}`, and bounded there by `B`, the `2m`-fold contour
integral over `Γ₁^{2m}` (`Γ₁ = {Re z = 1/log R}`, parametrised by `zetaM1Eta R`) of the kernel
`F(z,z') · ∏_j [ζ(1+z_j+z'_j)/(ζ(1+z_j)ζ(1+z'_j))·R^{z_j+z'_j}·(z_j²z'_j²)⁻¹]` equals
`F(0,0)(log R)^m` up to the displayed error, uniformly in `F` and `B`.

THIS IS THE VERSION NEEDED FOR THE GREEN–TAO §10 APPLICATION, and it differs from the already
proved `Commons.NumberTheory.Zeta.zeta_bound_m_v2` (which uses the *logarithmic* region
`-(β/log(|Im z_j|+2)) ≤ Re z_j ≤ 1`): that region is deeper than `Re ≥ -0.15` at `Im z ≈ 0`, while
the function actually fed into the contraption is `F = G₁G₂` from Green–Tao's 10.3, which is only
controlled on a FIXED strip `-1/(6m) < Re z_j < 100` (the Euler product `G₁ = ∏_p E_p^{(1)}`
converges there because `E_p^{(1)} = 1 + O(p^{-2+1/(3m)})` on that strip).  So `zeta_bound_m_v2` is
**not applicable** with `F = G₁G₂` for `m ≥ 4`; this fixed-strip version is.

PARSING: in Lean `∏ j, X * Y` parses as `∏ j, (X * Y)` because a big-operator body is parsed at
precedence 67 while `*` is at 70 — a product body swallows the following factors.  Every big
operator below is explicitly parenthesised.  (Sanity check: for `m = 1` the integrand is
`rfl`-equal to the integrand of `zeta_bound_m1` and `(2πi)^{-1}∫_{Γ₁} … = F 0 0 log R + ∂_{z'}F(0,0)
+ error` with `|∂_{z'}F(0,0)| ≤ B/σ` by Cauchy on the strip; the extra Cauchy factors are absorbed
into `C`.)

**Proof sketch (Green–Tao's Appendix A, verbatim strategy).**  Induct on `m`.  The case `m = 1` is
`zeta_bound_m1` (whose region is *contained* in the strip for `σ ≤ β/log 2`) plus the Cauchy
estimate `|∂_{z'}F(0,0)| ≤ B/σ`.  For the induction step apply the `m = 1` case in the variables
`(z_{m+1}, z'_{m+1})` to the function
`g(z,z') := (2πi)^{-2m}∫∫_{Γ₁^{2m}} F(z,z',w,w')∏_{j≤m}(kernel_j)` (Fubini for the absolutely
convergent integral), giving `I_m(F) = g(0,0) log R + ∂_{z'}g(0,0) + O(B_g) + O(B_g e^{-δ√log R})`,
then apply the induction hypothesis to `g` at `(0,0)`.  Two points: `g` is holomorphic on the strip
(differentiate under the integral sign — dominated convergence, the integrand being holomorphic in
the parameter and dominated by an integrable function), and the derivative term `∂_{z'}g(0,0)` is
an `m`-fold integral of `∂_{z'}F`, bounded by `(C/σ)^m B` via Cauchy on the strip (a disc of radius
`σ/2` stays inside `Re < 100`).  All constants depend on `m` and `σ` only. -/
theorem zeta_bound_m_strip (m : ℕ) (hm : 1 ≤ m) :
    ∃ σ δ C : ℝ, 0 < σ ∧ 0 < δ ∧ 0 < C ∧
      ∀ R : ℝ, 3 ≤ R → ∀ F : (Fin m → ℂ) → (Fin m → ℂ) → ℂ, ∀ B : ℝ, 0 ≤ B →
      Continuous (Function.uncurry F) →
      (∀ (j : Fin m) (z z' : Fin m → ℂ),
        (∀ i, -σ < (z i).re ∧ (z i).re < 100) →
        (∀ i, -σ < (z' i).re ∧ (z' i).re < 100) →
        DifferentiableAt ℂ (fun u : ℂ => F (Function.update z j u) z') (z j)) →
      (∀ (j : Fin m) (z z' : Fin m → ℂ),
        (∀ i, -σ < (z i).re ∧ (z i).re < 100) →
        (∀ i, -σ < (z' i).re ∧ (z' i).re < 100) →
        DifferentiableAt ℂ (fun u : ℂ => F z (Function.update z' j u)) (z' j)) →
      (∀ z z' : Fin m → ℂ,
        (∀ i, -σ < (z i).re ∧ (z i).re < 100) →
        (∀ i, -σ < (z' i).re ∧ (z' i).re < 100) →
        ‖F z z'‖ ≤ B) →
      ‖((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ (2 * m) *
          (∫ t : Fin m → ℝ, ∫ t' : Fin m → ℝ,
            F (fun j => Commons.NumberTheory.Zeta.zetaM1Eta R (t j))
              (fun j => Commons.NumberTheory.Zeta.zetaM1Eta R (t' j))
            * (∏ j, (riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta R (t j)
                    + Commons.NumberTheory.Zeta.zetaM1Eta R (t' j))
                  / (riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta R (t j))
                      * riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta R (t' j)))))
            * (R : ℂ) ^ (∑ j, (Commons.NumberTheory.Zeta.zetaM1Eta R (t j)
                + Commons.NumberTheory.Zeta.zetaM1Eta R (t' j)))
            * (∏ j, ((Commons.NumberTheory.Zeta.zetaM1Eta R (t j)) ^ 2
                  * (Commons.NumberTheory.Zeta.zetaM1Eta R (t' j)) ^ 2)⁻¹)
            * Complex.I ^ m * Complex.I ^ m)
        - F 0 0 * (Real.log R) ^ m‖
        ≤ C ^ m * B * (1 + (Real.log R) ^ (m - 1))
          + C ^ m * B * Real.exp (-(δ * Real.sqrt (Real.log R))) := by
  obtain ⟨β₀, D₀, hβ₀pos, hβ₀10⟩ := zetaAux_exists
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmR : (0:ℝ) < (m:ℝ) := Nat.cast_pos.mpr (by omega)
  set β : ℝ := min β₀ (Real.log 2 / (12 * (m:ℝ))) with hβdef
  have hβpos : 0 < β := by
    rw [hβdef]; exact lt_min hβ₀pos (div_pos hlog2pos (by positivity))
  have hβle : β ≤ β₀ := by rw [hβdef]; exact min_le_left _ _
  have hβ10 : β ≤ 1 / 10 := le_trans hβle hβ₀10
  have hβσ : β / Real.log 2 < 1 / (6 * (m:ℝ)) := by
    rw [hβdef, div_lt_iff₀ hlog2pos]
    calc min β₀ (Real.log 2 / (12 * (m:ℝ))) ≤ Real.log 2 / (12 * (m:ℝ)) := min_le_right _ _
      _ < Real.log 2 / (6 * (m:ℝ)) :=
          div_lt_div_of_pos_left hlog2pos (by positivity) (by nlinarith [hmR])
      _ = (1 / (6 * (m:ℝ))) * Real.log 2 := by ring
  obtain ⟨hD⟩ : Nonempty (ZetaAux β) := zetaAux_le D₀ hβ₀pos hβ₀10 hβpos hβ10 hβle
  obtain ⟨C, hC1, hCbound⟩ := zetaMmf_bound hD hβpos hβ10
  refine ⟨1 / (6 * (m:ℝ)), 1, C, by positivity, one_pos,
    lt_of_lt_of_le one_pos hC1, ?_⟩
  intro R hR F B hB hcont hd1 hd2 hbound
  have hRne : (R : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by linarith : (0:ℝ) < R))
  have hF : ZetaAdm β m F B := by
    refine ⟨hcont, ?_, ?_, ?_⟩
    · intro j z z' hz hz'
      exact hd1 j z z' (fun i => ZetaReg_subset_strip hβpos.le hβσ (hz i))
        (fun i => ZetaReg_subset_strip hβpos.le hβσ (hz' i))
    · intro j z z' hz hz'
      exact hd2 j z z' (fun i => ZetaReg_subset_strip hβpos.le hβσ (hz i))
        (fun i => ZetaReg_subset_strip hβpos.le hβσ (hz' i))
    · intro z z' hz hz'
      exact hbound z z' (fun i => ZetaReg_subset_strip hβpos.le hβσ (hz i))
        (fun i => ZetaReg_subset_strip hβpos.le hβσ (hz' i))
  have hb := hCbound R hR m hm F B hB hF
  rw [← zetaMmf_eq_explicit hRne m F]
  have hnonneg : 0 ≤ C ^ m * B * Real.exp (-(1 * Real.sqrt (Real.log R))) :=
    mul_nonneg (mul_nonneg (pow_nonneg (le_of_lt (lt_of_lt_of_le one_pos hC1)) m) hB)
      (Real.exp_pos _).le
  exact le_trans hb (le_add_of_nonneg_right hnonneg)

end Commons.NumberTheory.Zeta

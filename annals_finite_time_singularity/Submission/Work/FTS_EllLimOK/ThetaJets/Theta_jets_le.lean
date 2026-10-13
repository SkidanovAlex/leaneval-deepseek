/-
# `Theta_jets_le` — the pointwise jet bound for the singular part `Θ`

`Work.Construction.Theta α g` is the *singular part* of the stream function of the fundamental
model, `Θ α F = (1/(4α)) · sin(2θ) · L₁₂(F)(z)`: a product of a function of `z` alone
(`L₁₂ F`) and a function of `θ` alone.  This file proves

  `|D_z^j D_θ^i (Θ α g) (z,θ)| ≤ C(α) · |g|_{ℋ⁶}`  for `j + i ≤ 4`, `z > 0`, `θ ∈ (0,π/2)`,

for every `g` in the class `Work.FTS.ClassC.ClassC α g`, and for **every** `α > 0`.

## The route (three steps, each resting on proved material)

1. **Factorisation.**  Because `Θ` is a separated product, `D_z` only differentiates the
   `z`-factor and `D_θ` only the `θ`-factor, so with `A_i(θ) := D_θ^i ((1/(4α)) sin 2·)(θ)`
   (`Work.FTS_RegExport.RXT.velPertAux.theta_mixed_factor`),

     `mixed j i (Θ α g) z θ = A_i(θ) · D_z^j (L₁₂ g)(z)`.

   The angular factor is bounded by `384/(4α)` (`DthIter1_theta_factor`): `D_θ^r(sin 2·)` is an
   explicit polynomial `sin 2θ · q_r(cos 2θ, sin 2θ)` (`Work.FTS.H2.DthIter_four_Sfun`) whose
   coefficients sum to at most `384` in absolute value, which is the already-proved
   `Work.FTS.H2.abs_DthIter_Sfun_le`.

2. **The radial factor for `α ≤ 1`** is the proved sibling
   `Work.FTS_EllLimOK.PkgJets.L12jets_classC`:

     `∃ C, ∀ g, ClassC α g → ∀ j ≤ 4, ∀ z > 0, |D_z^j (L₁₂ g)(z)| ≤ C · |g|_{ℋ⁶}`.

   Its own route (for the reader): `D_z^j (L₁₂ g) = -Qang g (j-1)` for `j ≥ 1`
   (`PkgJets.DzdIter_L12_eq_neg_Qang`, differentiating the angular moment under the `θ`-integral
   via `Pieces.qang_deriv_classC`), the angular moment being bounded by `4√3·|g|_{ℋ⁶}` through
   the slice bound `∫_θ sin(2θ)^{-η} (D_z^j g z θ)² ≤ 3 HkSq α 6 g` of
   `Pieces.ang_moment_sup`; `j = 0` is the tail Cauchy–Schwarz bound `Pieces.L12_sup_six`.

3. **The radial factor for `α > 1`** is reduced to the case `α = 1` by `ClassC_le.lean`: on the
   angular interval `0 ≤ sin(2θ) ≤ 1`, so every weight of `Work.Spaces.HkIntegrand` and every
   `BdryTraces` exponent grows with `α`, whence `ClassC α g → ClassC 1 g` (`classC_one_of`) and
   `Xn6 1 g ≤ Xn6 α g` (`Xn6_one_le`) for `α ≥ 1`.  Hence the `α = 1` instance of step 2 bounds
   the radial factor by `C·|g|_{ℋ⁶}` **at level `α`** as well.

`Theta_jets_le_of_radial` isolates the assembly of steps 1 and 2/3, and `Theta_jets_le` performs
the case split.

## The (unused) `α`-free route

Sections 2–5 below also contain a self-contained, entirely `α`-free treatment of the radial
factor: `KthetaBound`/`L12_dzIter_abs_le` (the Cauchy–Schwarz bound of the sibling
`integral_Ktheta_dzIter_le`, applied to `L₁₂ (D_z^j g)`) and `L12_abs_le_HkNorm` (`j = 0`).
Turning those into the bound of the target needs the identity `L₁₂ (D_z^{j+1} g) z = -Qang g j z`
for general `α` (the Fubini/FTC step), which is the target of the sibling module
`L12_dzIter_succ_eq_neg_Qang_hk`; that route is not used by the proof below.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Elliptic.L12Aux
import Submission.Work.FM.Core2
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.OpenPkg.QangOpen
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.GalBasis.cc.abs_L12_le_HkNorm
import Submission.Work.FTS.GalBasis.cc.integral_abs_L12dens_le_Ioi
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.FTS.StrongLWP.Basic
import Submission.Work.FTS_RegExport.RXT.velPertAux.thetaJetsTendsto
import Submission.Work.FTS_EllLimOK.ThetaJets.integral_Ktheta_dzIter_le
import Submission.Work.FTS_EllLimOK.ThetaJets.ClassC_le
import Submission.Work.FTS_EllLimOK.PkgJets.L12jets_classC

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ThetaJets

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## 1. The angular factor `A_i = D_θ^i ((1/(4α)) sin 2·)` -/

/-- `DthIter1` is homogeneous in the scalar. -/
theorem DthIter1_const_mul (i : ℕ) (c : ℝ) (b : ℝ → ℝ) :
    Work.FTS_RegExport.RXT.velPertAux.DthIter1 i (fun θ => c * b θ)
      = fun θ => c * Work.FTS_RegExport.RXT.velPertAux.DthIter1 i b θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      funext θ
      have hstep : Work.FTS_RegExport.RXT.velPertAux.DthIter1 (i + 1) (fun θ => c * b θ) θ
          = Real.sin (2 * θ) * deriv (Work.FTS_RegExport.RXT.velPertAux.DthIter1 i
              (fun θ => c * b θ)) θ := rfl
      have hstep2 : Work.FTS_RegExport.RXT.velPertAux.DthIter1 (i + 1) b θ
          = Real.sin (2 * θ)
              * deriv (Work.FTS_RegExport.RXT.velPertAux.DthIter1 i b) θ := rfl
      rw [hstep, hstep2, ih, deriv_const_mul_field]
      ring

/-- `|D_θ^i (sin 2·)| ≤ 384` on `(0,π/2)` for `i ≤ 4`. -/
theorem DthIter1_sin_le (i : ℕ) (hi : i ≤ 4) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.FTS_RegExport.RXT.velPertAux.DthIter1 i (fun θ' => Real.sin (2 * θ')) θ| ≤ 384 := by
  have hmem : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have heq : Work.FTS_RegExport.RXT.velPertAux.DthIter1 i (fun θ' => Real.sin (2 * θ')) θ
      = Work.Spaces.DthIter i Work.FTS.H2.Sfun 0 θ := by
    have h := congrFun (congrFun
      (Work.FTS_RegExport.RXT.velPertAux.DthIter_const i (fun θ' => Real.sin (2 * θ'))) 0) θ
    exact h.symm
  rw [heq]
  have h2 := Work.FTS.H2.abs_DthIter_Sfun_le i hi 0 hmem
  have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsin0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_Iθ hmem
  have hA : Work.FTS.H2.Asin i ≤ 384 := by
    rcases i with _ | _ | _ | _ | i <;> norm_num [Work.FTS.H2.Asin]
  calc |Work.Spaces.DthIter i Work.FTS.H2.Sfun 0 θ|
      ≤ Work.FTS.H2.Asin i * Real.sin (2 * θ) := h2
    _ ≤ 384 * 1 := mul_le_mul hA hsin1 hsin0 (by norm_num)
    _ = 384 := by ring

/-- **The angular-factor bound**: for `i ≤ 4` and `θ ∈ (0,π/2)`,
`|D_θ^i ((1/(4α)) sin 2·)(θ)| ≤ 384/(4α)`. -/
theorem DthIter1_theta_factor (α : ℝ) (hα : 0 < α) (i : ℕ) (hi : i ≤ 4) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.FTS_RegExport.RXT.velPertAux.DthIter1 i
        (fun θ' => (1 / (4 * α)) * Work.Construction.s2 θ') θ| ≤ 384 / (4 * α) := by
  have hc : (0 : ℝ) < 1 / (4 * α) := by positivity
  have hfun : (fun θ' => (1 / (4 * α)) * Work.Construction.s2 θ')
      = fun θ' => (1 / (4 * α)) * Real.sin (2 * θ') := by
    funext θ'; rw [Work.Construction.s2_eq]
  rw [hfun, DthIter1_const_mul, abs_mul, abs_of_pos hc]
  have h2 := DthIter1_sin_le i hi hθ
  calc (1 / (4 * α)) * |Work.FTS_RegExport.RXT.velPertAux.DthIter1 i
        (fun θ' => Real.sin (2 * θ')) θ|
      ≤ (1 / (4 * α)) * 384 := mul_le_mul_of_nonneg_left h2 hc.le
    _ = 384 / (4 * α) := by ring

/-! ## 2. The decay of the pure `D_z`-iterates at `∞`, from `BdryTraces` -/

/-- **`BdryTraces` gives the decay of the pure `D_z`-iterates at `∞`.** -/
theorem tendsto_DzIter_atTop_zero {α : ℝ} {g : ℝ → ℝ → ℝ} {m : ℕ}
    (htr : Work.FTS.Nonlin.BdryTraces α m g) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Tendsto (fun z => Work.Spaces.DzIter m g z θ) atTop (nhds 0) := by
  have h0 : Tendsto (fun z => z * (Work.Spaces.mixed m 0 g z θ * Work.Spaces.w z) ^ 2)
      atTop (nhds 0) := ((htr 0 m (by omega)).1 θ hθ).2
  have h0' : Tendsto (fun z => z * (Work.Spaces.DzIter m g z θ * Work.Spaces.w z) ^ 2)
      atTop (nhds 0) := by
    simpa only [Work.Spaces.mixed_zero_right] using h0
  have h1 : Tendsto (fun z => Real.sqrt
      (z * (Work.Spaces.DzIter m g z θ * Work.Spaces.w z) ^ 2)) atTop (nhds 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp h0'
    rw [Real.sqrt_zero] at h
    exact h
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  refine squeeze_zero' (Eventually.of_forall (fun z => norm_nonneg _)) ?_ h1
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
  have hz0 : (0 : ℝ) < z := lt_of_lt_of_le one_pos hz
  have hw1 : 1 ≤ z * Work.Spaces.w z ^ 2 := by
    have h : z * Work.Spaces.w z ^ 2 = (1 + z) ^ 4 / z ^ 3 := by
      rw [Work.Spaces.w]
      field_simp
      try ring
    rw [h, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 3)]
    have h4 : z ^ 3 ≤ (1 + z) ^ 4 := by
      have h23 : z ^ 3 ≤ z ^ 4 := by
        calc z ^ 3 = z ^ 3 * 1 := by ring
          _ ≤ z ^ 3 * z := mul_le_mul_of_nonneg_left hz (by positivity)
          _ = z ^ 4 := by ring
      have h34 : z ^ 4 ≤ (1 + z) ^ 4 :=
        pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ z) (by linarith) 4
      linarith
    linarith
  have hsq : (Work.Spaces.DzIter m g z θ) ^ 2
      ≤ z * (Work.Spaces.DzIter m g z θ * Work.Spaces.w z) ^ 2 := by
    have h : (Work.Spaces.DzIter m g z θ) ^ 2 * 1
        ≤ (Work.Spaces.DzIter m g z θ) ^ 2 * (z * Work.Spaces.w z ^ 2) :=
      mul_le_mul_of_nonneg_left hw1 (sq_nonneg _)
    calc (Work.Spaces.DzIter m g z θ) ^ 2
        = (Work.Spaces.DzIter m g z θ) ^ 2 * 1 := by ring
      _ ≤ (Work.Spaces.DzIter m g z θ) ^ 2 * (z * Work.Spaces.w z ^ 2) := h
      _ = z * (Work.Spaces.DzIter m g z θ * Work.Spaces.w z) ^ 2 := by ring
  calc ‖Work.Spaces.DzIter m g z θ‖
      = Real.sqrt ((Work.Spaces.DzIter m g z θ) ^ 2) := by
        rw [Real.norm_eq_abs]
        exact (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (z * (Work.Spaces.DzIter m g z θ * Work.Spaces.w z) ^ 2) :=
        Real.sqrt_le_sqrt hsq

/-! ## 3. The `Π`-data of the sibling `integral_Ktheta_dzIter_le`, and its consequences -/

/-- **The `K_θ`-Cauchy–Schwarz datum**: the conclusion of `integral_Ktheta_dzIter_le` for a
fixed `g`, packaged as a predicate. -/
def KthetaBound (α : ℝ) (g : ℝ → ℝ → ℝ) (C : ℝ) : Prop :=
  ∀ j : ℕ, j ≤ 6 →
    MeasureTheory.IntegrableOn (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
      |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g s θ| / s) (Set.Ioi 0) ∧
    (∫ s in Set.Ioi (0 : ℝ), (∫ θ in Work.Spaces.Iθ,
      |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g s θ| / s))
      ≤ C * Work.Spaces.HkNorm α 6 g

/-- `Ktheta = Spaces.K`. -/
theorem Ktheta_eq_K : Work.Elliptic.Ktheta = Work.Spaces.K := by
  funext θ
  simp only [Work.Elliptic.Ktheta, Work.Spaces.K]

/-- The `L₁₂`-density of `D_z^j g` is dominated pointwise by the angular `K_θ`-integral. -/
theorem L12dens_dzIter_le {g : ℝ → ℝ → ℝ} {j : ℕ} {s : ℝ} (hs : 0 < s) :
    |Work.Construction.L12dens (fun r θ => Work.Spaces.DzIter j g r θ) s|
      ≤ ∫ θ in Work.Spaces.Iθ,
          |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g s θ| / s := by
  have h1 : Work.Construction.L12dens (fun r θ => Work.Spaces.DzIter j g r θ) s
      = ∫ θ in Work.Spaces.Iθ,
          Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g s θ / s := by
    show (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.DzIter j g s θ / s) = _
    refine integral_congr_ae (Eventually.of_forall (fun θ => ?_))
    rw [Ktheta_eq_K]
  rw [h1]
  calc |∫ θ in Work.Spaces.Iθ,
          Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g s θ / s|
      ≤ ∫ θ in Work.Spaces.Iθ,
          |Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g s θ / s| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ = ∫ θ in Work.Spaces.Iθ,
          |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g s θ| / s := by
        refine integral_congr_ae (Eventually.of_forall (fun θ => ?_))
        simp only [abs_div, abs_mul, abs_of_pos hs]

/-- **Integrability of the density of `D_z^j g`**, `j ≤ 4`, from the `K_θ`-C-S datum. -/
theorem integrableOn_L12dens_dzIter {α : ℝ} {g : ℝ → ℝ → ℝ} {j : ℕ} {C : ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen g) (hK : KthetaBound α g C) (hj : j ≤ 4) :
    MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (fun r θ => Work.Spaces.DzIter j g r θ)) (Set.Ioi 0) := by
  obtain ⟨hint, -⟩ := hK j (by omega)
  have haesm : AEStronglyMeasurable
      (Work.Construction.L12dens (fun r θ => Work.Spaces.DzIter j g r θ))
      (volume.restrict (Set.Ioi 0)) :=
    Work.FTS.GalBasis.cc.aesm_L12dens_of_SmoothOpen (hsm.DzIter j)
  exact hint.mono' haesm (ae_restrict_of_forall_mem measurableSet_Ioi
    (fun s hs => L12dens_dzIter_le hs))

/-- **The `L₁₂`-jet bound**: `|L₁₂ (D_z^j g) z| ≤ C |g|_{ℋ⁶}` for `j ≤ 4`, `z > 0`, from the
`K_θ`-C-S datum. -/
theorem L12_dzIter_abs_le {α : ℝ} {g : ℝ → ℝ → ℝ} {j : ℕ} {C : ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen g) (hK : KthetaBound α g C) (hj : j ≤ 4)
    {z : ℝ} (hz : 0 < z) :
    |Work.Construction.L12 (fun r θ => Work.Spaces.DzIter j g r θ) z|
      ≤ C * Work.Spaces.HkNorm α 6 g := by
  obtain ⟨hint, hbd⟩ := hK j (by omega)
  have hint' : MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (fun r θ => Work.Spaces.DzIter j g r θ)) (Set.Ioi 0) :=
    integrableOn_L12dens_dzIter hsm hK hj
  have hintabs : MeasureTheory.IntegrableOn
      (fun s => |Work.Construction.L12dens (fun r θ => Work.Spaces.DzIter j g r θ) s|)
      (Set.Ioi 0) := by
    change MeasureTheory.Integrable
      (fun s => |Work.Construction.L12dens (fun r θ => Work.Spaces.DzIter j g r θ) s|)
      (volume.restrict (Set.Ioi 0))
    simpa only [Real.norm_eq_abs] using hint'.norm
  calc |Work.Construction.L12 (fun r θ => Work.Spaces.DzIter j g r θ) z|
      = |∫ s in Set.Ioi z,
          Work.Construction.L12dens (fun r θ => Work.Spaces.DzIter j g r θ) s| := rfl
    _ ≤ ∫ s in Set.Ioi z,
          |Work.Construction.L12dens (fun r θ => Work.Spaces.DzIter j g r θ) s| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ s in Set.Ioi (0 : ℝ),
          |Work.Construction.L12dens (fun r θ => Work.Spaces.DzIter j g r θ) s| :=
        MeasureTheory.setIntegral_mono_set hintabs
          (Eventually.of_forall (fun x => abs_nonneg _))
          (Eventually.of_forall (fun x hx => by
            simp only [Set.mem_Ioi] at hx ⊢; linarith))
    _ ≤ ∫ s in Set.Ioi (0 : ℝ), (∫ θ in Work.Spaces.Iθ,
          |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g s θ| / s) :=
        MeasureTheory.integral_mono_ae hintabs hint
          (ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs => L12dens_dzIter_le hs))
    _ ≤ C * Work.Spaces.HkNorm α 6 g := hbd

/-! ## 4. The `L₁₂`-bound for `j = 0` (the tail C-S bound of the `GalBasis/cc` chain) -/

/-- **`|L₁₂ g z| ≤ C |g|_{ℋ⁶}`** uniformly in `z > 0`, for `g` smooth on the open quadrant and
honestly in `ℋ⁶` (no `α`-restriction: the Cauchy–Schwarz weights `1/(z w z) = z/(1+z)²` and
`sin(2θ)^{η/2}` are both `α`-free). -/
theorem L12_abs_le_HkNorm {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen g) (hmem6 : Work.Spaces.HkMem α 6 g) :
    ∀ z : ℝ, 0 < z → |Work.Construction.L12 g z|
      ≤ (Work.FTS.GalBasis.cc.BK * Real.sqrt Work.FTS.GalBasis.cc.W2 + 1)
          * Work.Spaces.HkNorm α 6 g := by
  have hmem4 : Work.Spaces.HkMem α 4 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm 4 (by norm_num) hmem6
  have hint : MeasureTheory.IntegrableOn (Work.Construction.L12dens g) (Set.Ioi 0) :=
    Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem hsm hmem4
  have hintabs : MeasureTheory.IntegrableOn (fun s => |Work.Construction.L12dens g s|)
      (Set.Ioi 0) := by
    change MeasureTheory.Integrable (fun s => |Work.Construction.L12dens g s|)
      (volume.restrict (Set.Ioi 0))
    simpa only [Real.norm_eq_abs] using hint.norm
  have hbd : ∀ s ∈ Set.Ioi (0 : ℝ), |Work.Construction.L12dens g s|
      ≤ Work.FTS.GalBasis.cc.Wlam s * (Work.FTS.GalBasis.cc.BK * Real.sqrt
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)) :=
    fun s hs => Work.FTS.GalBasis.cc.abs_L12dens_le α g hmem4 hs
  have htail := Work.FTS.GalBasis.cc.integral_abs_L12dens_le_Ioi α 4 g hmem4 (le_refl 0) hbd
  intro z hz
  have h1 : (∫ s in Set.Ioi z, |Work.Construction.L12dens g s|)
      ≤ ∫ s in Set.Ioi (0 : ℝ), |Work.Construction.L12dens g s| :=
    MeasureTheory.setIntegral_mono_set hintabs (Eventually.of_forall (fun x => abs_nonneg _))
      (Eventually.of_forall (fun x hx => by simp only [Set.mem_Ioi] at hx ⊢; linarith))
  have h2 : Real.sqrt (Work.Spaces.HkSq α 4 g) ≤ Work.Spaces.HkNorm α 6 g := by
    rw [Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt
      (Work.FTS.StrongLWP.HkSq_mono_of_mem (α := α) (k := 6) (k' := 4) (by norm_num) hmem6)
  have h3 : (0 : ℝ) ≤ Work.FTS.GalBasis.cc.BK * Real.sqrt Work.FTS.GalBasis.cc.W2 :=
    mul_nonneg Work.FTS.GalBasis.cc.BK_nonneg (Real.sqrt_nonneg _)
  calc |Work.Construction.L12 g z|
      = |∫ s in Set.Ioi z, Work.Construction.L12dens g s| := rfl
    _ ≤ ∫ s in Set.Ioi z, |Work.Construction.L12dens g s| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ s in Set.Ioi (0 : ℝ), |Work.Construction.L12dens g s| := h1
    _ ≤ Work.FTS.GalBasis.cc.BK * Real.sqrt Work.FTS.GalBasis.cc.W2
          * Real.sqrt (Work.Spaces.HkSq α 4 g) := htail
    _ ≤ Work.FTS.GalBasis.cc.BK * Real.sqrt Work.FTS.GalBasis.cc.W2
          * Work.Spaces.HkNorm α 6 g := mul_le_mul_of_nonneg_left h2 h3
    _ ≤ (Work.FTS.GalBasis.cc.BK * Real.sqrt Work.FTS.GalBasis.cc.W2 + 1)
          * Work.Spaces.HkNorm α 6 g := by
        refine mul_le_mul_of_nonneg_right ?_ (Work.Spaces.HkNorm_nonneg α 6 g)
        linarith

/-! ## 6. The target -/

/-- **The angular-factor step of the target.**  Given the radial bound
`|D_z^j (L₁₂ g)(z)| ≤ C |g|_{ℋ⁶}` for `j ≤ 4`, `z > 0` and every `g` of class `ClassC α`, the
separated-product factorisation of `Θ` together with the bound `384/(4α)` on the angular factor
gives the target with the constant `(384/(4α))·C`. -/
theorem Theta_jets_le_of_radial {α : ℝ} (hα : 0 < α) {C : ℝ} (hCpos : 0 < C)
    (hC : ∀ (g : Work.FTS.Galerkin.Fn), Work.FTS.ClassC.ClassC α g →
      ∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 0 < z →
        |Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 g z) z 0|
          ≤ C * Work.FTS.StrongGlobal.Xn6 α g) :
    ∀ (g : Work.FTS.Galerkin.Fn), Work.FTS.ClassC.ClassC α g →
      ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
        |Work.Spaces.mixed j i (Work.Construction.Theta α g) z θ|
          ≤ (384 / (4 * α)) * C * Work.FTS.StrongGlobal.Xn6 α g := by
  intro g hg j i hji z θ hz hθ
  have hfac : Work.Spaces.mixed j i (Work.Construction.Theta α g) z θ
      = Work.FTS_RegExport.RXT.velPertAux.DthIter1 i
          (fun θ' => (1 / (4 * α)) * Work.Construction.s2 θ') θ
        * Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 g z) z 0 :=
    Work.FTS_RegExport.RXT.velPertAux.theta_mixed_factor α g j i z θ
  rw [hfac, abs_mul]
  have hA := DthIter1_theta_factor α hα i (by omega) hθ
  have hR := hC g hg j (by omega) z hz
  have hAnn : (0 : ℝ) ≤ 384 / (4 * α) := by positivity
  calc |Work.FTS_RegExport.RXT.velPertAux.DthIter1 i
          (fun θ' => (1 / (4 * α)) * Work.Construction.s2 θ') θ|
        * |Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 g z) z 0|
      ≤ (384 / (4 * α)) * (C * Work.FTS.StrongGlobal.Xn6 α g) :=
        mul_le_mul hA hR (abs_nonneg _) hAnn
    _ = (384 / (4 * α)) * C * Work.FTS.StrongGlobal.Xn6 α g := by ring

theorem Theta_jets_le : ∀ (α : ℝ), 0 < α → ∃ C : ℝ, 0 < C ∧ ∀ (g : Work.FTS.Galerkin.Fn),
    Work.FTS.ClassC.ClassC α g →
    ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      |Work.Spaces.mixed j i (Work.Construction.Theta α g) z θ|
        ≤ C * Work.FTS.StrongGlobal.Xn6 α g := by
  intro α hα
  by_cases hα1 : α ≤ 1
  · -- the range `α ≤ 1` is the proved sibling `PkgJets.L12jets_classC`
    obtain ⟨C1, hC1pos, hC1⟩ := Work.FTS_EllLimOK.PkgJets.L12jets_classC (α := α) hα hα1
    refine ⟨(384 / (4 * α)) * C1, by positivity, ?_⟩
    intro g hg j i hji z θ hz hθ
    exact Theta_jets_le_of_radial hα hC1pos hC1 g hg j i hji z θ hz hθ
  · -- the range `α > 1` reduces to the case `α = 1` (`ClassC α g → ClassC 1 g`)
    have hge : 1 ≤ α := le_of_lt (lt_of_not_ge hα1)
    obtain ⟨C1, hC1pos, hC1⟩ := Work.FTS_EllLimOK.PkgJets.L12jets_classC (α := 1) one_pos le_rfl
    have hC1' : ∀ (g : Work.FTS.Galerkin.Fn), Work.FTS.ClassC.ClassC α g →
        ∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 0 < z →
          |Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 g z) z 0|
            ≤ C1 * Work.FTS.StrongGlobal.Xn6 α g := by
      intro g hg j hj z hz
      refine le_trans (hC1 g (classC_one_of hge hg) j hj z hz) ?_
      exact mul_le_mul_of_nonneg_left (Xn6_one_le hge hg) hC1pos.le
    refine ⟨(384 / (4 * α)) * C1, by positivity, ?_⟩
    intro g hg j i hji z θ hz hθ
    exact Theta_jets_le_of_radial hα hC1pos hC1' g hg j i hji z θ hz hθ

end Work.FTS_EllLimOK.ThetaJets
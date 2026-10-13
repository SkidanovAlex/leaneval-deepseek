/-
# The honest (open-quadrant) growth bounds on `L₁₂(g)`

The estimate proved here is the pair of `z`-pointwise bounds

  `(L₁₂ g z)² ≤ C·|g|²_{ℋ⁴}·z³`     and     `(L₁₂ g z)² ≤ C·|g|²_{ℋ⁴}/z`     `(z > 0)`,

with the explicit constant `C = max(K₁/3, K₁) + 1`, `K₁ = ∫_θ K(θ)² dθ`, for a datum `g`
which is `C^∞` on the *open* quadrant (`Work.FTS.EllipticEst.SmoothOpen g`) and honestly in
`ℋ⁴` (`Work.Spaces.HkMem α 4 g`), together with the normalisation `L₁₂(g)(0) = 0`.

This is the open-quadrant version of `Work.FTS.Nonlinear.Pieces.L12_sq_le_growth`
(`Submission/Work/FTS/Nonlinear/Pieces/rowsN0Q.lean`), whose hypothesis is the stronger
interior class `Work.FTS.LocData.SmoothQuad g` (`C^∞` on the strip `z > -1`).  Two inputs of
that proof are replaced:

* the integrability of the `L₁₂`-density on `(0,∞)` (`Work.FTS.H2.L12densIntegrable`) is now
  supplied by `Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn`,
  which only needs *continuity* of `g` on the open quadrant;
* the `z`-pointwise bound on the density `L₁₂dens g s` is derived *directly* from
  Cauchy–Schwarz in `θ` (`Work.FTS.OpenPkg.QangOpen.Qang_sq_leQ_open`) combined with the
  pointwise domination of the angular slice by the `ℋ⁴`-integrand
  (`Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq`), rather than from the iterated moment
  identity `D_z^{k+1}L₁₂(g) = -Q_k(g)` (`L12_dzdIter_moment`, `L12_iterate_sq_slot_le`,
  `Qang_sq_le_const`), whose proofs need the *interior* class.

Nothing else changes: the two Cauchy–Schwarz steps in `s` against the weight
`u(s) = s/(1+s)²`, the two elementary integrals `∫_{(0,z)}u² ≤ z³/3` and
`∫_{(z,∞)}u² ≤ 1/z`, and the final arithmetic with `C = max(K₁/3,K₁)+1` are those of the
interior-class proof.

Route in one line: `L₁₂(g)(z) = -∫_{(0,z)}L₁₂dens` (for the small-`z` bound) and
`L₁₂(g)(z) = ∫_{(z,∞)}L₁₂dens` (large `z`); the density is
`≤ √K₁·u(s)·√(B s)` with `B(s) = ∫_θ HkIntegrand α 4 g s θ`; Cauchy–Schwarz in `s` against
`u` and `∫_{Iz}B = HkSq α 4 g = Xn α g ²` finish.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Submission.Work.FTS.OpenPkg.QangOpen
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q
import Submission.Work.FTS.StrongEps.E4R3.Qang_sq_le_const_open
import Submission.Work.FTS.StrongEps.E4R3.L12_dzdIter_moment_honest

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## Two elementary one-dimensional tools -/

/-- Cauchy–Schwarz in the form `(∫ √B·u)² ≤ (∫B)(∫u²)`, for `B ≥ 0`. -/
private theorem cs_sqrt_mul_gen {B u : ℝ → ℝ} {s : Set ℝ} (hBnn : ∀ x, 0 ≤ B x)
    (hBint : MeasureTheory.IntegrableOn B s)
    (hBaesm : MeasureTheory.AEStronglyMeasurable B (MeasureTheory.volume.restrict s))
    (huint : MeasureTheory.IntegrableOn (fun x => (u x) ^ 2) s)
    (huaesm : MeasureTheory.AEStronglyMeasurable u (MeasureTheory.volume.restrict s)) :
    (∫ x in s, Real.sqrt (B x) * u x) ^ 2 ≤ (∫ x in s, B x) * (∫ x in s, (u x) ^ 2) := by
  have h1 : MeasureTheory.MemLp (fun x => Real.sqrt (B x)) 2 (MeasureTheory.volume.restrict s) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hBaesm)]
    exact hBint.congr (Filter.Eventually.of_forall fun x => (Real.sq_sqrt (hBnn x)).symm)
  have h2 : MeasureTheory.MemLp u 2 (MeasureTheory.volume.restrict s) :=
    (MeasureTheory.memLp_two_iff_integrable_sq huaesm).mpr huint
  have h := Work.Spaces.cs_integral h1 h2
  rw [show (∫ x in s, (Real.sqrt (B x)) ^ 2) = ∫ x in s, B x from
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x => Real.sq_sqrt (hBnn x))] at h
  exact h

/-- `∫_{(0,z)} (x/(1+x)²)² ≤ z³/3`. -/
private theorem u_sq_Ioc_le {z : ℝ} (hz : 0 ≤ z) :
    ∫ x in Set.Ioc 0 z, (x / (1 + x) ^ 2) ^ 2 ≤ z ^ 3 / 3 := by
  have hle : ∀ x ∈ Set.Ioc 0 z, (x / (1 + x) ^ 2) ^ 2 ≤ x ^ 2 := by
    intro x hx
    have hx0 : 0 < x := hx.1
    rw [div_pow, div_le_iff₀ (by positivity : (0:ℝ) < ((1 + x) ^ 2) ^ 2)]
    have h2 : (1:ℝ) ≤ (1 + x) ^ 4 := by
      nlinarith [hx0.le, sq_nonneg x, sq_nonneg (1 + x)]
    nlinarith [sq_nonneg x, sq_nonneg (1 + x), sq_nonneg ((1 + x) * (1 + x))]
  have hint : MeasureTheory.IntegrableOn (fun x : ℝ => x ^ 2) (Set.Ioc 0 z) := by
    refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ (z ^ 2) ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · exact (continuousOn_id.pow 2).aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with x hx
      rw [Real.norm_of_nonneg (sq_nonneg x)]
      exact pow_le_pow_left₀ hx.1.le hx.2 2
  have h := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun x => sq_nonneg (x / (1 + x) ^ 2)) hint
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc hle)
  refine h.trans ?_
  rw [← intervalIntegral.integral_of_le hz, integral_pow]
  norm_num

/-- `∫_{(z,∞)} (x/(1+x)²)² ≤ 1/z` for `z > 0`. -/
private theorem u_sq_Ioi_le {z : ℝ} (hz : 0 < z) :
    ∫ x in Set.Ioi z, (x / (1 + x) ^ 2) ^ 2 ≤ 1 / z := by
  have hle : ∀ x ∈ Set.Ioi z, (x / (1 + x) ^ 2) ^ 2 ≤ x ^ (-(2 : ℝ)) := by
    intro x hx
    have hx0 : 0 < x := lt_trans hz hx
    rw [div_pow, Real.rpow_neg hx0.le, Real.rpow_two, inv_eq_one_div,
      le_div_iff₀ (by positivity : (0:ℝ) < x ^ 2), div_mul_eq_mul_div, div_le_one (by positivity)]
    nlinarith [sq_nonneg x, sq_nonneg (1 + x), sq_nonneg ((1 + x) * (1 + x)), sq_nonneg (x * x)]
  have hint : MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (-(2 : ℝ))) (Set.Ioi z) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hz
  have h := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun x => sq_nonneg (x / (1 + x) ^ 2)) hint
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hle)
  refine h.trans ?_
  rw [integral_Ioi_rpow_of_lt (by norm_num) hz,
    show ((-2:ℝ) + 1) = -1 by norm_num, Real.rpow_neg_one]
  norm_num

/-! ## The growth bounds -/

/-- **The `z`-pointwise growth bounds for `L₁₂(g)` in the open-quadrant class.**

For `g` of class `C^∞` on the open quadrant and `g ∈ ℋ⁴`, with `L₁₂(g)(0) = 0`, and for
`K₁ = ∫_θ K(θ)² dθ`, `X = |g|_{ℋ⁴}`:

  `(L₁₂ g z)² ≤ (max(K₁/3, K₁) + 1)·X²·z³`  and  `(L₁₂ g z)² ≤ (max(K₁/3, K₁) + 1)·X²/z`.

The first bound covers the behaviour near `z = 0` (where `L₁₂(g)` vanishes at least like
`z^{3/2}` because of the normalisation `L₁₂(g)(0) = 0`), the second the behaviour at infinity
(where `L₁₂(g)` decays at least like `z^{-1/2}`); the two together give
`|L₁₂(g)(z)| ≤ √C·X·min(z^{3/2}, z^{-1/2})`. -/
theorem L12_sq_le_growth_honest (α : ℝ) {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    (h0 : Work.Construction.L12 g 0 = 0) :
    (∀ z : ℝ, 0 < z → (Work.Construction.L12 g z) ^ 2
        ≤ (max ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) / 3)
              (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1)
          * (Work.FTS.Nonlin.Xn α g) ^ 2 * z ^ 3)
    ∧ (∀ z : ℝ, 0 < z → (Work.Construction.L12 g z) ^ 2
        ≤ (max ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) / 3)
              (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1)
          * (Work.FTS.Nonlin.Xn α g) ^ 2 / z) := by
  have hEE : Work.Construction.L12 g = Work.Elliptic.L12 g :=
    Work.FTS.H2.constructionL12_eq_ellipticL12 g
  -- integrability of the density, from *continuity* on the open quadrant only
  have hintL : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens g) (Set.Ioi 0) :=
    Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn
      hsm.continuousOn hmem
  have h0' : Work.Elliptic.L12 g 0 = 0 := by rw [← hEE]; exact h0
  obtain ⟨hval, -, -⟩ := Work.Elliptic.L12_values g hintL h0'
  set K1 : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 with hK1def
  have hK1nn : 0 ≤ K1 := by
    rw [hK1def]; exact MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  set X : ℝ := Work.FTS.Nonlin.Xn α g with hXdef
  have hXnn : 0 ≤ X := by
    rw [hXdef]; exact Work.Spaces.HkNorm_nonneg α 4 g
  set B : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ
    with hBdef
  set u : ℝ → ℝ := fun s => s / (1 + s) ^ 2 with hudef
  have hBnn : ∀ s, 0 ≤ B s := fun s => MeasureTheory.integral_nonneg fun θ =>
    Work.Spaces.HkIntegrand_nonneg α 4 g s θ
  have hu0 : ∀ s, 0 < s → 0 ≤ u s := by
    intro s hs; rw [hudef]; positivity
  have hBint : MeasureTheory.IntegrableOn B Work.Spaces.Iz := hmem.2
  -- (1) the pointwise bound on the density
  have hdens : ∀ s : ℝ, 0 < s → (Work.Elliptic.L12dens g s) ^ 2 ≤ K1 * B s * (u s) ^ 2 := by
    intro s hs
    -- the angular Cauchy--Schwarz at slot `0`
    have hQ : (Work.Elliptic.Qang g 0 s) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2) := by
      have h := Work.FTS.OpenPkg.QangOpen.Qang_sq_leQ_open α g hsm hmem 0 (by norm_num) hs
      simpa only [Work.Spaces.DzIter_zero] using h
    -- the angular slice of `g` is dominated by the `ℋ⁴`-integrand
    have hslice : (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2) * (Work.Spaces.w s) ^ 2 ≤ B s := by
      have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          (g s θ) ^ 2 * (Work.Spaces.w s) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g s θ := by
        rw [Work.Spaces.Iθ]
        rw [MeasureTheory.Measure.restrict_congr_set
          (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := π / 2)).symm]
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => by
          have h2 := Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq α 4 g 0 (by norm_num) hs hθ
          simp only [Work.Spaces.DzIter_zero] at h2
          have h3 := mul_le_mul_of_nonneg_right h2 (sq_nonneg (Work.Spaces.w s))
          rwa [div_mul_cancel₀ _ (pow_ne_zero 2 (ne_of_gt (Work.FTS.H2.w_pos hs)))] at h3)
      have hmono := MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (hmem.1 s (le_of_lt hs)) hae
      simpa only [MeasureTheory.integral_mul_const] using hmono
    have hw2 : 0 < (Work.Spaces.w s) ^ 2 := pow_pos (Work.FTS.H2.w_pos hs) 2
    -- the `b = 1` slot bound `(Q₀)² ≤ K₁·(s⁴/(1+s)⁴)·B(s)`
    have hb : (Work.Elliptic.Qang g 0 s) ^ 2 ≤ K1 * (s ^ 4 / (1 + s) ^ 4) * B s := by
      have hK1nn' : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 :=
        MeasureTheory.integral_nonneg fun θ => sq_nonneg _
      calc (Work.Elliptic.Qang g 0 s) ^ 2
          ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
              * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2) := hQ
        _ = (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
              * (((∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2) * (Work.Spaces.w s) ^ 2)
                  / (Work.Spaces.w s) ^ 2) := by
              rw [mul_div_cancel_right₀ _ (ne_of_gt hw2)]
        _ ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
              * (B s / (Work.Spaces.w s) ^ 2) :=
              mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hslice hw2.le) hK1nn'
        _ = K1 * (s ^ 4 / (1 + s) ^ 4) * B s := by
              have hwinv : ((Work.Spaces.w s) ^ 2)⁻¹ = s ^ 4 / (1 + s) ^ 4 := by
                rw [Work.Spaces.w, div_pow, inv_div]
                congr 1 <;> ring
              rw [hK1def, div_eq_mul_inv, hwinv]
              ring
    rw [Work.Elliptic.L12dens_eq_Qang_div g s, div_pow, div_le_iff₀ (pow_pos hs 2)]
    refine hb.trans (le_of_eq ?_)
    rw [hK1def, hBdef, hudef]
    field_simp
  -- (2) the pointwise bound on the density, in absolute value
  have hdens' : ∀ s : ℝ, 0 < s → |Work.Elliptic.L12dens g s|
      ≤ Real.sqrt K1 * (Real.sqrt (B s) * u s) := by
    intro s hs
    have hKb : 0 ≤ K1 * B s := mul_nonneg hK1nn (hBnn s)
    have h := Real.sqrt_le_sqrt (hdens s hs)
    rw [Real.sqrt_mul hKb] at h
    rw [Real.sqrt_sq_eq_abs] at h
    rw [Real.sqrt_mul hK1nn] at h
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (hu0 s hs)] at h
    simpa only [mul_assoc] using h
  -- (3) measurability and integrability of the auxiliary functions
  have hu_cont : ContinuousOn u (Set.Ioi (0:ℝ)) := by
    rw [hudef]
    refine ContinuousOn.div continuousOn_id ((continuousOn_const.add continuousOn_id).pow 2) ?_
    intro x hx
    have hx' : (0:ℝ) < x := hx
    have : (0:ℝ) < 1 + x := by linarith
    positivity
  have hu_aesm : ∀ {s : Set ℝ}, s ⊆ Set.Ioi (0:ℝ) →
      MeasureTheory.AEStronglyMeasurable u (MeasureTheory.volume.restrict s) := by
    intro s hs
    exact (hu_cont.aestronglyMeasurable measurableSet_Ioi).mono_measure
      (MeasureTheory.Measure.restrict_mono hs le_rfl)
  have hu_int_Ioc : ∀ z : ℝ, MeasureTheory.IntegrableOn (fun x => (u x) ^ 2) (Set.Ioc 0 z) := by
    intro z
    refine MeasureTheory.IntegrableOn.of_bound ?_
      ((hu_aesm (s := Set.Ioc 0 z) (fun x hx => hx.1)).pow 2) 1 ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with x hx
      have hx0 : 0 < x := hx.1
      rw [Real.norm_of_nonneg (sq_nonneg _), hudef, div_pow,
        div_le_one (by
          have h2 : (1:ℝ) ≤ (1 + x) ^ 2 := by nlinarith [hx0.le]
          exact pow_pos (lt_of_lt_of_le one_pos h2) 2)]
      nlinarith [hx0.le, sq_nonneg x, sq_nonneg (1 + x), sq_nonneg ((1 + x) * (1 + x)),
        sq_nonneg (1 + x * x + x)]
  have hu_int_Ioi : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun x => (u x) ^ 2) (Set.Ioi z) := by
    intro z hz
    refine MeasureTheory.Integrable.mono'
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hz)
      ((hu_aesm (s := Set.Ioi z) (fun x hx => lt_trans hz hx)).pow 2) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans hz hx
    rw [Real.norm_of_nonneg (sq_nonneg _), hudef, div_pow, Real.rpow_neg hx0.le,
      Real.rpow_two, inv_eq_one_div, le_div_iff₀ (by positivity : (0:ℝ) < x ^ 2),
      div_mul_eq_mul_div, div_le_one (by positivity)]
    nlinarith [sq_nonneg x, sq_nonneg (1 + x), sq_nonneg ((1 + x) * (1 + x)), sq_nonneg (x * x)]
  -- (4) integrability of `√B · u`
  have hsqu : ∀ {s : Set ℝ}, MeasureTheory.IntegrableOn B s →
      MeasureTheory.IntegrableOn (fun x => (u x) ^ 2) s →
      MeasureTheory.AEStronglyMeasurable B (MeasureTheory.volume.restrict s) →
      MeasureTheory.AEStronglyMeasurable u (MeasureTheory.volume.restrict s) →
      MeasureTheory.IntegrableOn (fun x => Real.sqrt (B x) * u x) s := by
    intro s hBi hui hBa hua
    refine MeasureTheory.Integrable.mono' ((hBi.add hui).const_mul (1/2))
      ((Real.continuous_sqrt.comp_aestronglyMeasurable hBa).mul hua) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg (B x))]
    show Real.sqrt (B x) * |u x| ≤ 1 / 2 * (B x + (u x) ^ 2)
    nlinarith [sq_nonneg (Real.sqrt (B x) - |u x|), Real.sq_sqrt (hBnn x), sq_abs (u x)]
  have hHk : Work.Spaces.HkSq α 4 g = X ^ 2 := by
    have h0H : (0:ℝ) ≤ Work.Spaces.HkSq α 4 g :=
      MeasureTheory.integral_nonneg fun z =>
        MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ
    rw [hXdef, show Work.FTS.Nonlin.Xn α g = Real.sqrt (Work.Spaces.HkSq α 4 g) from rfl]
    exact (Real.sq_sqrt h0H).symm
  refine ⟨?_, ?_⟩
  · -- the small-`z` bound, from `L₁₂(g)(z) = -∫_{(0,z)}L₁₂dens`
    intro z hz
    have hB_ioc : MeasureTheory.IntegrableOn B (Set.Ioc 0 z) :=
      hBint.mono_set (fun s hs => hs.1.le)
    have hI_int : MeasureTheory.IntegrableOn (fun x => Real.sqrt (B x) * u x) (Set.Ioc 0 z) :=
      hsqu hB_ioc (hu_int_Ioc z) hB_ioc.aestronglyMeasurable
        (hu_aesm (s := Set.Ioc 0 z) (fun x hx => hx.1))
    have hcs := cs_sqrt_mul_gen hBnn hB_ioc hB_ioc.aestronglyMeasurable (hu_int_Ioc z)
      (hu_aesm (s := Set.Ioc 0 z) (fun x hx => hx.1))
    have hBle : (∫ s in Set.Ioc 0 z, B s) ≤ X ^ 2 := by
      have h := MeasureTheory.setIntegral_mono_set hBint
        (Filter.Eventually.of_forall fun s => hBnn s)
        (Filter.Eventually.of_forall fun s (hs : s ∈ Set.Ioc 0 z) => hs.1.le)
      have hvalB : (∫ s in Work.Spaces.Iz, B s) = Work.Spaces.HkSq α 4 g := by
        simp only [hBdef, Work.Spaces.HkSq]
      rwa [hvalB, hHk] at h
    have hI2 : (∫ s in Set.Ioc 0 z, Real.sqrt (B s) * u s) ^ 2 ≤ X ^ 2 * z ^ 3 := by
      refine hcs.trans ?_
      have hule := u_sq_Ioc_le hz.le
      have h1 : (∫ s in Set.Ioc 0 z, B s) * (∫ s in Set.Ioc 0 z, (u s) ^ 2)
          ≤ X ^ 2 * (z ^ 3 / 3) :=
        mul_le_mul hBle hule (MeasureTheory.integral_nonneg fun x => sq_nonneg _) (sq_nonneg X)
      have h2 : X ^ 2 * (z ^ 3 / 3) ≤ X ^ 2 * z ^ 3 := by
        have : (0:ℝ) ≤ z ^ 3 / 3 := by positivity
        nlinarith [sq_nonneg X]
      linarith
    have h1 : |Work.Elliptic.L12 g z| ≤ Real.sqrt K1
        * ∫ s in Set.Ioc 0 z, Real.sqrt (B s) * u s := by
      have habs : |Work.Elliptic.L12 g z| = |∫ s in (0)..z, Work.Elliptic.L12dens g s| := by
        rw [hval z hz.le]; simp
      rw [habs]
      refine (intervalIntegral.abs_integral_le_integral_abs hz.le).trans ?_
      rw [intervalIntegral.integral_of_le hz.le]
      refine (MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun s => abs_nonneg _)
        (hI_int.const_mul (Real.sqrt K1)) ?_).trans
        (le_of_eq (MeasureTheory.integral_const_mul _ _))
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
        (fun s hs => hdens' s hs.1)
    have h2 : (Work.Elliptic.L12 g z) ^ 2 ≤ K1 * (X ^ 2 * z ^ 3) := by
      rw [← sq_abs]
      calc |Work.Elliptic.L12 g z| ^ 2
          ≤ (Real.sqrt K1 * ∫ s in Set.Ioc 0 z, Real.sqrt (B s) * u s) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = K1 * (∫ s in Set.Ioc 0 z, Real.sqrt (B s) * u s) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hK1nn]
        _ ≤ K1 * (X ^ 2 * z ^ 3) := mul_le_mul_of_nonneg_left hI2 hK1nn
    rw [hEE]
    refine h2.trans ?_
    have hC : K1 ≤ max (K1 / 3) K1 + 1 :=
      le_trans (le_max_right _ _) (le_add_of_nonneg_right zero_le_one)
    have hXz : (0:ℝ) ≤ X ^ 2 * z ^ 3 := by positivity
    simpa [mul_assoc, ← hK1def] using mul_le_mul_of_nonneg_right hC hXz
  · -- the large-`z` bound, from `L₁₂(g)(z) = ∫_{(z,∞)}L₁₂dens`
    intro z hz
    have hB_ioi : MeasureTheory.IntegrableOn B (Set.Ioi z) :=
      hBint.mono_set (fun s hs => (lt_trans hz hs).le)
    have huioi := hu_int_Ioi z hz
    have hI_int : MeasureTheory.IntegrableOn (fun x => Real.sqrt (B x) * u x) (Set.Ioi z) :=
      hsqu hB_ioi huioi hB_ioi.aestronglyMeasurable
        (hu_aesm (s := Set.Ioi z) (fun x hx => lt_trans hz hx))
    have hcs := cs_sqrt_mul_gen hBnn hB_ioi hB_ioi.aestronglyMeasurable huioi
      (hu_aesm (s := Set.Ioi z) (fun x hx => lt_trans hz hx))
    have hBle : (∫ s in Set.Ioi z, B s) ≤ X ^ 2 := by
      have h := MeasureTheory.setIntegral_mono_set hBint
        (Filter.Eventually.of_forall fun s => hBnn s)
        (Filter.Eventually.of_forall fun s (hs : s ∈ Set.Ioi z) => (lt_trans hz hs).le)
      have hvalB : (∫ s in Work.Spaces.Iz, B s) = Work.Spaces.HkSq α 4 g := by
        simp only [hBdef, Work.Spaces.HkSq]
      rwa [hvalB, hHk] at h
    have hI2 : (∫ s in Set.Ioi z, Real.sqrt (B s) * u s) ^ 2 ≤ X ^ 2 / z := by
      refine hcs.trans ?_
      have hule := u_sq_Ioi_le hz
      have h1 : (∫ s in Set.Ioi z, B s) * (∫ s in Set.Ioi z, (u s) ^ 2)
          ≤ X ^ 2 / z := by
        have h2 := mul_le_mul hBle hule
          (MeasureTheory.integral_nonneg fun x => sq_nonneg _) (sq_nonneg X)
        simpa only [hudef, mul_one_div] using h2
      exact h1
    have h1 : |Work.Elliptic.L12 g z| ≤ Real.sqrt K1
        * ∫ s in Set.Ioi z, Real.sqrt (B s) * u s := by
      have habs : |Work.Elliptic.L12 g z| = |∫ s in Set.Ioi z, Work.Elliptic.L12dens g s| := by
        rw [show Work.Elliptic.L12 g z = ∫ s in Set.Ioi z, Work.Elliptic.L12dens g s from rfl]
      rw [habs]
      refine (MeasureTheory.abs_integral_le_integral_abs).trans ?_
      refine (MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun s => abs_nonneg _)
        (hI_int.const_mul (Real.sqrt K1)) ?_).trans
        (le_of_eq (MeasureTheory.integral_const_mul _ _))
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
        (fun s hs => hdens' s (lt_trans hz hs))
    have h2 : (Work.Elliptic.L12 g z) ^ 2 ≤ K1 * (X ^ 2 / z) := by
      rw [← sq_abs]
      calc |Work.Elliptic.L12 g z| ^ 2
          ≤ (Real.sqrt K1 * ∫ s in Set.Ioi z, Real.sqrt (B s) * u s) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = K1 * (∫ s in Set.Ioi z, Real.sqrt (B s) * u s) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hK1nn]
        _ ≤ K1 * (X ^ 2 / z) := mul_le_mul_of_nonneg_left hI2 hK1nn
    rw [hEE]
    refine h2.trans ?_
    have hC : K1 ≤ max (K1 / 3) K1 + 1 :=
      le_trans (le_max_right _ _) (le_add_of_nonneg_right zero_le_one)
    have hXz : (0:ℝ) ≤ X ^ 2 / z := by positivity
    simpa [mul_div_assoc, ← hK1def] using mul_le_mul_of_nonneg_right hC hXz

end Work.FTS.StrongEps.E4R3

import Mathlib
import Submission.Commons.Analysis.Convex.convex_potential_one_dim_poincare
import Submission.Commons.Analysis.Convex.logconcave_marginal_prod
import Submission.Commons.Analysis.Convex.fderiv2_nonneg_of_convexOn
import Submission.Commons.Analysis.Convex.deriv2_nonneg_of_convexOn_real
import Submission.Commons.Analysis.Inequalities.sq_div_sub_sq_div_le
import Submission.Commons.Analysis.InnerProductSpace.isometry_equiv_real_of_finrank_one
import Submission.Commons.Analysis.InnerProductSpace.euclidean_split_isometry
import Submission.Commons.Analysis.Calculus.hasDerivAt_integral_slice
import Submission.Commons.Analysis.Calculus.continuousAt_integral_slice
import Submission.Commons.Measure.Integral.integrable_rexp_neg_mul_sq_norm
import Submission.Commons.Analysis.Calculus.fderiv_fderiv_comp_continuousLinearMap
import Submission.Commons.Analysis.Calculus.fderiv_fderiv_comp_add
import Submission.Commons.Analysis.Calculus.fderiv_comp_toLp_prod
import Submission.Commons.Analysis.InnerProductSpace.schur_block_energy
import Submission.Commons.Analysis.Asymptotics.integrable_pow_mul_exp_neg_sq
import Submission.Commons.Analysis.Convex.brascamp_lieb_one_dim_sharp
import Submission.Commons.Analysis.Convex.contDiff_logLaplace_penalty
import Submission.Commons.Analysis.Convex.convexOn_logLaplace
import Submission.Commons.Analysis.Asymptotics.growth_fderiv_logLaplace
import Submission.Commons.Analysis.Asymptotics.growth_fderiv2_logLaplace
import Submission.Commons.Analysis.Calculus.FDeriv.hessianWithin_add_quadratic
import Submission.Commons.Analysis.Measure.integral_smul_add_eq

/-!
## Towards the truncated Brascamp–Lieb inequality

Target: `Commons.Analysis.GaussianMeasure.brascamp_lieb_truncated` (bottom of this file).

### Overall strategy

The `n`-dimensional Brascamp–Lieb (variance) inequality for the Gaussian truncated to a convex
set `A` is proved in two stages.

**Stage 1 (whole space, smooth strongly convex potential).**  Prove, by induction on the dimension,
the Brascamp–Lieb inequality for `f : E → ℝ` of class `C²` on a finite-dimensional real inner
product space `E` with `D²f ⪰ 2π·Id`:

  `Var_{e^{-f}}(h) ≤ ∫ ⟪(D²f(x))⁻¹ ∇h(x), ∇h(x)⟫ e^{-f(x)} dx`.

The induction follows Brascamp–Lieb (1976), Theorem 4.1, in the form reproduced in the appendix of
Carlen–Cordero-Erausquin–Lieb, *Asymmetric covariance estimates of Brascamp–Lieb type*,
arXiv:1106.0709.  Slicing `E = G × ℝ` at height `y` and writing `W(y) = ∫_G e^{-f(z,y)} dz`,
`ν_y = e^{-f(·,y)}/W(y)`, `F(y) = ∫ h dν_y`, one has the law of total variance

  `Var_μ(h) = ∫ var_{ν_y}(h) dν̂(y) + Var_{ν̂}(F)`,   `ν̂ = W·Leb/(∫W)`,

and then

* (slices) the induction hypothesis applied to the slice potentials `z ↦ f(z,y)` bounds
  `var_{ν_y}(h)` by the slice Hessian form, and applied to `z ↦ λ h(z,y) + μ ∂_y f(z,y)` gives the
  `2×2` Loewner inequality
  `[[var_z h, cov_z(h,f_y)],[cov_z(h,f_y), var_z f_y]] ≤ [[A11, A12],[A12, A22]]`
  where `A11 = ⟨⟨∇_z h, Hess_z⁻¹ ∇_z h⟩⟩_z`, `A12 = ⟨⟨∇_z h, Hess_z⁻¹ ∇_z f_y⟩⟩_z`,
  `A22 = ⟨⟨∇_z f_y, Hess_z⁻¹ ∇_z f_y⟩⟩_z` (conditional averages over the slices);
* (marginal) the **sharp** one-dimensional Brascamp–Lieb inequality applied to `F` w.r.t. the
  one-dimensional measure `ν̂ = e^{-U}`, `U = -log W`, gives
  `Var_{ν̂}(F) ≤ ∫ (F')²/U'' dν̂`, where `F' = ⟨∂_y h⟩_z - cov_z(h, ∂_y f)` and
  `U'' = ⟨∂_y² f⟩_z - var_z(∂_y f)`;
* the two are combined with the elementary inequality
  `a²/α - b²/β ≤ (a-b)²/(α-β)` (`α > β > 0`, commons: `sq_div_sub_sq_div_le`) applied to
  `a = F'`, `b = A12 - cov_z(h,f_y)`, `α = U''`, `β = A22 - var_z(f_y)`, yielding
  `Var_μ(h) ≤ ∫ ⟨⟨∇_z h, Hess_z⁻¹ ∇_z h⟩⟩_z dν̂ + ∫ (a-b)²/(α-β) dν̂`;
  finally the block/Schur formula for the inverse of the full Hessian and a conditional
  Cauchy–Schwarz comparison identify the right-hand side with `∫ ⟪Hess⁻¹∇h, ∇h⟫ dμ`.

**Stage 2 (truncation).**  A convex set `A` is approximated in the exponent by
`f_ε(x) = π‖x‖² + φ_ε(x)` where `φ_ε ≥ 0` is a smooth convex penalty vanishing on `A` and growing
like `dist(x,A)²/ε`; then `D²f_ε ⪰ 2π·Id`, the measures `e^{-f_ε}dx` converge to `1_A e^{-π‖x‖²}dx`
and Stage 1 passes to the limit by dominated convergence.

### Status of this file (updated)

The file is COMPLETE: the target `brascamp_lieb_truncated` is proved (Session 7).  The whole
development decomposes as
* Stage 1 (whole space, smooth strongly convex potential): `blon_holds`/`brascamp_lieb_smooth`,
  by Brascamp–Lieb's dimensional induction (`blon_euclid` ← `bl_zero`, `bl_one_dim`,
  `bl_product_step`);
* Stage 2 (truncation): the log-Laplace penalty `penPot`/`penF` (`ε → 0`, `bl_cut_stage`) and the
  smooth cutoff `cut`/`uPark` (`R → ∞`, `bl_final`), combined in the target.
(`bl_product_step` — the induction step `BLon G → BLon (WithLp 2 (G × ℝ))` — is PROVED, so the
whole-space Brascamp–Lieb theorem `brascamp_lieb_smooth` is complete.)  See the STATUS / PLAN
block below for the truncation stage.

(`bl_real : BLon ℝ` is PROVED, together with a large amount of the product-step infrastructure.)

### Session 6 additions (all PROVED)

**Type-class fix (IMPORTANT).**  Instance search cannot synthesise
`Norm ((G × ℝ) →L[ℝ] ((G × ℝ) →L[ℝ] ℝ))` because the search for `NormedSpace ℝ (G × ℝ)` gets lost.
The `Product` section now declares three `local instance`s that pin the path down:

```
noncomputable local instance instNormedSpaceProd : NormedSpace ℝ (G × ℝ) := Prod.normedSpace
noncomputable local instance instNormedSpaceDual : NormedSpace ℝ ((G × ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
noncomputable local instance instSeminormedCLM :
    SeminormedAddCommGroup ((G × ℝ) →L[ℝ] ((G × ℝ) →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
```

With these, operator-norm arguments on `fderiv ℝ (fderiv ℝ F)` work normally.

**Measurability / continuity of slice `hessInv`** (this was the previous blocker for the
measure-theoretic assembly):
* `continuous_hessInv_pair` (`E`-section): `Continuous (fun p : E × E => hessInv f p.1 p.2)`
  for a fixed `C²` `f` with `D²f ⪰ 2π`.
* `continuous_inverse_family` (`E`-section): the abstract ε-δ engine (a continuous family of
  operators with a uniform `2π` lower bound and a norm bound `‖I i u‖ ≤ ‖u‖/(2π)` has a continuous
  family of inverses).
* `continuous_grad_of_contDiff`, `norm_hessOp_slice_sub_le`, `continuous_hessOp_slice`,
  `continuous_hessInv_pair_y` (joint continuity of `(z,y,u) ↦ hessInv (slicePot F y) z u`),
  `gradSlice` (def), `continuous_gradSlice`, `continuous_gradSlice_fixed`,
  `continuous_slice_hessInv_apply`, `continuous_slice_hessInv_bilin`.

**Integrability of the slice Hessian energies**:
`integrable_slice_hessInv_pair`, `integrable_gradSlice_bilin`,
`integrable_gradSlice_bilin_y` (the `y`-integral version, via Fubini).

**The Loewner (2×2) inequality** — the analytic heart of the induction step:
`grad_slice_add_smul`, `slice_deriv_growth_test`, `sliceGrowth_test` (value + derivative growth of
the test function `slicePot H y + t · mixPot F y`), and

```
bl_slice_quad (IH : BLon G) (F H) ... (y : ℝ) :
  ∀ t, 0 ≤ (sliceEnergy F y (slicePot H y) / sliceMass F y - condVar F H y)
     + 2 * t * (sliceCrossEnergy F y (slicePot H y) (mixPot F y) / sliceMass F y
                - condCov F H (fun p => dY F p) y)
     + t ^ 2 * (sliceEnergy F y (mixPot F y) / sliceMass F y
                - condVar F (fun p => dY F p) y)
```

This is obtained by applying `slice_BL` to `slicePot H y + t · mixPot F y`, expanding both sides
with `wVar_quad` and `sliceEnergy_add_smul`, and dividing by `sliceMass F y > 0`.

**Marginal-setup lemmas** (for the sharp 1D Brascamp–Lieb on the marginal `marg F`):
* defs `sliceEnergyFn` (`= ⟪(Hess_z)⁻¹ ∇_z∂_yF, ∇_z∂_yF⟫` as a function of the point) and
  `schurPot` (`= d2Y F - sliceEnergyFn F`, the Schur complement),
* `d2Y_eq_hess`, `schurPot_ge_two_pi` (`2π ≤ schurPot`),
* `condMean_sliceEnergyFn` (the conditional mean of `sliceEnergyFn` is the slice energy divided by
  the slice mass), `margD2_eq_schur`
  (`margD2 F y = condMean F (schurPot F) y + (sliceEnergy F y (mixPot F y)/W - condVar F (dY F) y)`),
* `mixPot_growth`, `sliceEnergy_mix_sub_condVar_nonneg` (the `β ≥ 0` half, from `slice_BL` applied
  to `mixPot F y`), `two_pi_le_condMean_schurPot`, and
* **`two_pi_le_margD2`** (`2π ≤ margD2 F y`, for a `BLon G`-style `IH`).

### What remains in `bl_product_step`

1. **Marginal (sharp 1D BL).**  Apply `Commons.Analysis.Convex.brascamp_lieb_one_dim_sharp` to
   `V := marg F`, `u := Ξ := condMean F H`, using `contDiff_marg`, `deriv_deriv_marg`,
   `two_pi_le_margD2` (so `0 < deriv (deriv (marg F))`), `tendsto_marg_atTop/atBot`,
   `contDiff_condMean`, and the four integrability conditions
   (`integrable_condMean_mul_sliceMass`, `integrable_condMean_sq_mul_sliceMass`, and two more
   obtained from `condMeanDeriv_sq_mul_sliceMass_le` plus the *finiteness of the ambient target
   integral* — see the note below).  Conclusion (with `e^{-marg F y} = sliceMass F y`):
   `(∫ y, Ξ y² W y) - (∫ y, Ξ y W y)²/(∫ y, W y) ≤ ∫ y, (Ξ' y)²/margD2 F y * W y`.
   The convexity of `marg F` follows from `0 ≤ deriv (deriv (marg F))` (via
   `deriv_deriv_marg`); this still needs a small lemma ("`f` differentiable with monotone `deriv`
   ⟹ convex").
2. **Identifications.**  `a - b = condMean F φ y` and `α - β = condMean F (schurPot F) y` where
   `a = Ξ'`, `b = A12 - B12`, `α = margD2 F y`, `β = A22 - B22` and
   `φ p = dY H p - ⟪(Hess_z)⁻¹ ∇_z∂_yF, ∇_z H⟫`.
3. **Combine** via `bl_combine` / `bl_combine_zero` and `condMean_sq_div_le`, then identify with
   `hessInv_energy_eq` and assemble with `wVar_prod_eq` and Fubini.

**Also PROVED in Session 6 (marginal step, continued).**
* `exp_neg_marg_apply` (`Real.exp (-(marg F y)) = sliceMass F y` for `W > 0`), `continuous_margD2`,
  `convexOn_marg` (convexity of the marginal, from `deriv (deriv (marg F)) > 0` via
  `strictMono_of_deriv_pos` + `Monotone.convexOn_univ_of_deriv`),
  `integrable_condMean_mul_exp_neg_marg`, `integrable_condMean_sq_mul_exp_neg_marg`,
  `integrable_condMean_sq_div_margD2` (the `huw` condition of the sharp 1D inequality).
* **`marg_variance_le`**: the sharp one-dimensional Brascamp–Lieb inequality
  (`Commons.Analysis.Convex.brascamp_lieb_one_dim_sharp`) applied to `V := marg F`, `u := Ξ`, with
  the four integrability conditions as explicit hypotheses (`hu1`, `hu2`, `huw` proved above,
  `hud` still to be discharged — see the plan below).  `marg_variance_le_sliceMass` is the same
  statement with `e^{-marg F}` rewritten as `sliceMass F`.
* `crossFn` / `schurPhi` (`schurPhi F H p = dY H p - crossFn F H p`) and
  `condMean_crossFn` (the conditional mean of `crossFn` is `sliceCrossEnergy ... / W`),
  `crossFn_eq_swapped` (self-adjointness rewrites it into the Schur-form pairing), `continuous_crossFn`,
  and **`condMeanDeriv_sub_eq`**:
  `deriv (condMean F H) y - (sliceCrossEnergy F y (slicePot H y) (mixPot F y)/W - condCov F H (dYF) y)
     = condMean F (schurPhi F H) y`,
  i.e. `a - b = ⟨schurPhi⟩`.

**The `hud` condition and the slice-level assembly are DONE (Session 6).**

* `integrable_condMeanDeriv_sq_div_margD2` — `Integrable (fun y => (Ξ')²/margD2 · W)`, the last
  hypothesis of the sharp 1D inequality.  Route: `a_sq_div_le_combined` (pointwise
  `a²/α·W ≤ (α₁ + γ)·W`) with `γ·W ≤ ∫ z schurPhi²/schurPot e^{-F}` (conditional Cauchy–Schwarz
  `condMeanDeriv_sq_div_mul_sliceMass_le`) and `α₁·W ≤ sliceEnergy F y (slicePot H y)`
  (`alpha1_mul_sliceMass_le`), with the dominating function
  `sliceEnergy F y (slicePot H y) + ∫ z schurPhi²/schurPot e^{-F(z,y)}`.
* Supporting lemmas: `gradSlice_le_poly`, `gradSlice_dY_le_poly` (polynomial growth in the point),
  `schurPot_pos`, `continuous_schurPot`, `continuous_schurPhi`, `wVar_nonneg`,
  `integrable_slice_exp_neg`, `condVar_mul_sliceMass_nonneg`, `integrable_schurPot_slice`,
  `continuous_schurPhi_sq_div_slice`, `integrable_schurPhi_sq_div_slice`,
  `schurPhi_sq_div_le`, `integrable_schurPhi_sq_div_joint`, `integrable_schurPhi_sq_div_y`,
  `HGrowth0_of_HGrowth`, `HGrowth0_sq`, `continuous_condVar`,
  `condMeanDeriv_sq_div_mul_sliceMass_le`, `integrable_alpha1_mul_sliceMass`,
  `alpha1_mul_sliceMass_le`, `condVar_mul_sliceMass_le_sliceEnergy`, `deriv_condMean_sq_div_le`,
  `integrable_condVar_mul_sliceMass`.
* **`marg_variance_le_margD2`** — the complete marginal step (`TVar ≤ ∫ (Ξ')²/margD2 · W`), with
  every hypothesis of the sharp 1D inequality now discharged.
* **`bl_slice_level`** —
  `wVar (e^{-F}) H ≤ (∫ y, sliceEnergy F y (slicePot H y)) + ∫ y, ∫ z, schurPhi F H (z,y)²/schurPot F (z,y) · e^{-F(z,y)}`.

**`bl_product_step` IS PROVED (Session 6).**  The `G × ℝ`-level identification was closed by:
`fubini_sliceEnergy`, `fubini_schurPhi` (the two Fubini identifications, by
`Measure.volume_eq_prod` + `integral_prod_symm`), `EN_eq_slice'` (the `p`-indexed wrapper around
`EN_eq_slice`), `bl_ambient` (merges the two integrals with `integral_add` and identifies the
integrand with `∫ ⟪hessInv f (toLp p) (grad h (toLp p)), …⟫` by `integral_congr_ae` + `ring`), and
finally the hypothesis transfers (`contDiff_comp_toLp`, `hessian_comp_toLp_l2`,
`convexOn_comp_toLp`, `growth_comp_toLp`, `potGrowth_comp_toLp`, `hgrowth_comp_toLp`,
`growth_comp_toLp_h`) plus `integral_comp_toLp` to move the variance and the energy integral across
`WithLp.toLp`.  (Snag worth remembering: at that point the goal's `wVar` is already displayed
unfolded, so a `show` was needed to re-present it in `wVar` form before the transfer identity could
fire.)

**Session 7: the truncation stage is DONE.**  The proof of the target is

1. `volume_pos_of_integral_pos`: `0 < volume A` from `0 < ∫_A exp(-π‖x‖²)`.
2. For each `R ≥ 1`, `bl_cut_stage`: applying `brascamp_lieb_smooth` to the potential
   `penF n A ε = π‖x‖² + penPot n A ε` (where `penPot = -log ((∫_{y∈A} exp(-‖x-y‖²/ε²))/gaussNorm)`,
   a smooth convex `≥ 0` penalty tending to `0` on `A°` and `+∞` off `closure A`) and to the
   compactly supported test function `uPark n w R = cut n R * w`, using `hessInv_energy`
   (`⟪hessInv ∇u,∇u⟫ ≤ ‖∇u‖²/2π`) and letting `ε → 0` by dominated convergence
   (`tendsto_integral_penF_mul`, `ae_tendsto_exp_penF`).
3. `bl_final`: letting `R → ∞` in `bl_cut_stage` by dominated convergence
   (`tendsto_integral_cut_mul`), using `fderiv_uPark` (`∇(cut_R w) = cut_R ∇w + w ∇cut_R`),
   `cut_tendsto`/`fderiv_cut_tendsto_zero` and the uniform bound `exists_bound_fderiv_cut`.

The historical description of the truncation stage (kept for reference):

Let `φ_ε x = -Real.log ((∫ y ∈ A, exp (-‖x-y‖²/ε²)) / (∫ exp (-‖y‖²/ε²)))` (the normalisation
makes `φ_ε → 0` on `A°` and `→ +∞` off `A` as `ε → 0`; note `ε^n = ∫ exp(-‖y‖²/ε²)`), and
`f_ε = π‖·‖² + φ_ε`.  Then `f_ε` is `C²`, its excess over `π‖·‖²` is `φ_ε` (convex), and
`D²f_ε ⪰ 2π`, so `brascamp_lieb_smooth` applies to `f_ε` and `w`.  Letting `ε → 0` by dominated
convergence (`φ_ε ≥ 0` gives `e^{-f_ε} ≤ e^{-π‖·‖²}`; only the `≤ (1/(2π))∫‖∇w‖²` bound is needed
on the right, via `hessInv_energy`) gives the target.

Pieces of this that are DELEGATED (pure Mathlib, independent of everything in this file):
* `Commons.Analysis.Convex.contDiff_logLaplace_penalty` — smoothness of `φ_ε`.  **PROVED**
* `Commons.Analysis.Convex.convexOn_logLaplace` — convexity of `φ_ε`.  **PROVED**
* `Commons.Analysis.Asymptotics.growth_fderiv_logLaplace` — polynomial growth of `∇φ_ε`
  (the first half of `BLon`'s growth hypothesis for `f_ε`).  **PROVED**
* `Commons.Analysis.Asymptotics.growth_fderiv2_logLaplace` — quadratic-form bound on `D²φ_ε`
  (`0 ⪯ D²φ_ε ⪯ (2/ε²)·I`; the second half of `BLon`'s growth hypothesis for `f_ε`).  **PROVED**

Once those land, the remaining file-local work is:
1. assemble the growth hypotheses for `f_ε = π‖·‖² + φ_ε` from those of `φ_ε` and the explicit
   `∇(π‖·‖²) = 2π·id`, `D²(π‖·‖²) = 2π·I`;
2. `φ_ε ≥ 0` (it is `-log` of a probability: `∫_{y∈A} … ≤ ∫_y …`);
3. the two pointwise limits `φ_ε → 0` on `A°` and `φ_ε → +∞` off `A` (as `ε → 0`), plus
   `Convex.addHaar_frontier` for the null boundary;
4. the DCT assembly: apply `brascamp_lieb_smooth`/`blon_holds` to `f_ε`, bound the right-hand side
   by `(1/(2π))∫‖fderiv w‖²e^{-f_ε}` via `hessInv_energy`, and pass to the limit using the
   domination `e^{-f_ε} ≤ e^{-π‖·‖²}` (`φ_ε ≥ 0`), recovering the target (the normalisation of
   `φ_ε` by `∫ exp (-‖y‖²/ε²) = ε^n ∫ exp (-‖z‖²)` is what makes the limit on `A°` equal to `0`).


**The `hud` integrability — settled plan (Session 6).**

 The pointwise combination step, PROVED:
```
lemma a_sq_div_le_combined (IH : BLon G) (F H) ... (y : ℝ) :
  (deriv (condMean F H) y)^2 / margD2 F y * sliceMass F y
    ≤ (sliceEnergy F y (slicePot H y) / sliceMass F y - condVar F H y
       + (deriv (condMean F H) y
           - (sliceCrossEnergy F y (slicePot H y) (mixPot F y) / sliceMass F y
              - condCov F H (fun p => dY F p) y))^2 / condMean F (schurPot F) y)
      * sliceMass F y
```
It is `bl_slice_quad` (`hquad`) combined with `bl_combine` (`0 < β`) / `bl_combine_zero` (`β = 0`)
and the identity `margD2 F y - β = condMean F (schurPot F) y` (`margD2_sub_beta`).  This is exactly
the domination needed to prove `Integrable (fun y => a²/α · W)` (item 1 of the `hud` plan below).

**The `hud` integrability — settled plan (Session 6).**

The sharp 1D inequality (`marg_variance_le`, `marg_variance_le_sliceMass`, PROVED above) needs
`Integrable (fun y => (deriv (condMean F H) y)^2 / margD2 F y * sliceMass F y)` — i.e. `a²/α · W`
with `a = Ξ'`, `α = margD2 F y`.  The earlier "polynomial growth of `Ξ`" route is WRONG (see the
abandoned block at p. 2995); the correct route is:

1. `bl_combine` (pointwise, for every `y`) gives `a²/α ≤ α₁ + (a-b)²/(α-β)` where
   `α₁ = A11 - B11`, `b = A12 - B12`, `β = A22 - B22`.  Hence pointwise
   `a²/α · W ≤ A11·W + ((a-b)²/(α-β))·W`.
2. The right-hand side is integrable in `y`:
   * `A11·W = sliceEnergy F y (slicePot H y)` is integrable in `y` by
     `integrable_gradSlice_bilin_y` (applied with `A = B = H`);
   * `((a-b)²/(α-β))·W` is dominated by `∫ z, schurPhi²/schurPot · e^{-F(z,y)}` — this is the
     pointwise conditional Cauchy–Schwarz `condMean_sq_div_le` applied to
     `schurPhi / schurPot`, and the `y`-integral of that is finite because
     `Integrable (fun p => schurPhi(p)²/schurPot(p) * e^{-F p})` follows from the pointwise
     identity `hessInv_energy_eq` together with the integrability of
     `sliceE(p) e^{-F p}` (`integrable_gradSlice_bilin` with `A = B = H`) and of
     `EN(p) e^{-F p}` (`Integrable`, from the `hessInv_energy` bound
     `EN(p) ≤ ‖grad h (toLp p)‖²/(2π)` and `integrable_mul_exp_neg_potGrowth`).
3. `Integrable (fun y => a²/α · W)` then follows from points 1–2 by `Integrable.mono'`, since
   `y ↦ a²/α·W` is continuous (`deriv Ξ` is continuous, `margD2` is continuous).

Here `schurPhi F H p := dY H p - ⟪hessInv (slicePot F p.2) p.1 (gradSlice (dY F) p), gradSlice H p⟫`
—— the `hessInv_energy_eq` correction term.  (Note `⟨schurPhi⟩ = a - b`, whereas
`condMeanDeriv_mul_sliceMass` uses the equivalent function `dY H - (H - Ξ)·dY F`.)

Everything else is proved.  In particular:
-/

/-
### Roadmap: the remaining pieces, with their intended Lean statements

**Setting.**  `G` is a finite-dimensional real inner product space (with `MeasureSpace`/`BorelSpace`);
`V := WithLp 2 (G × ℝ)`.  For a weight `w` and a function `F` on a measure space,
`wVar w F := ∫ F ^ 2 * w - (∫ F * w) ^ 2 / (∫ w)` — the (unnormalized) weighted variance; the
left-hand side of the Brascamp–Lieb inequality is `wVar (fun x => exp (-(f x))) h`.  All statements
below are invariant under adding a constant to the potential `f`, so in proofs one may assume the
normalisation `∫ exp (-(f x)) dx = 1`.

**(P1) Slice mass, conditional means and the law of total variance.**
For `g : G × ℝ → ℝ` put `sliceMass g y = ∫ z, Real.exp (-(g (z, y)))` (over `G`) and, assuming
`0 < sliceMass g y`,

  `condMean g h y = (∫ z, h (z, y) * Real.exp (-(g (z, y)))) / sliceMass g y`,
  `condVar  g h y = (∫ z, h (z, y) ^ 2 * Real.exp (-(g (z, y)))) / sliceMass g y - condMean g h y ^ 2`.

Then (Fubini/Tonelli, `integral_prod_symm`) for `h : G × ℝ → ℝ` with `h ^ 2 e^{-g}`,
`h e^{-g}`, `e^{-g}` all integrable on `G × ℝ`:

  `wVar (fun x => Real.exp (-(g x))) h`
    `= ∫ y, condVar g h y * sliceMass g y`
      `+ (∫ y, condMean g h y ^ 2 * sliceMass g y`
          `- (∫ y, condMean g h y * sliceMass g y) ^ 2 / (∫ y, sliceMass g y))`.

**(P2) Differentiation formulas.**  For `g : G × ℝ → ℝ` of class `C²` with
`∀ y, Integrable (fun z => Real.exp (-(g (z, y))))` and polynomial growth of `g` and its first
derivatives (so that all the following integrals converge and differentiation under the integral
sign is legitimate, using `hasDerivAt_integral_of_dominated_loc_of_deriv_le`):

  `HasDerivAt (sliceMass g) (-(∫ z, ∂_y g (z, y) * Real.exp (-(g (z, y))))) y`,
  `HasDerivAt (condMean g h) (condMean g (∂_y h) y - (condCov g h (∂_y g) y)) y`,
  `HasDerivAt (fun y => condMean g (∂_y g) y) (condMean g (∂_y² g) y - condVar g (∂_y g) y) y`.

Writing `U y := - Real.log (sliceMass g y)` these give `U' = condMean g (∂_y g)` and
`U'' = condMean g (∂_y² g) - condVar g (∂_y g)`.

**(P3) Positivity of `U''`.**  If `g - π‖·‖²` is convex on `G × ℝ`, then `U := -log sliceMass g`
satisfies `U'' ≥ 2π`; equivalently `U - π y²` is convex.  Proof: `U y - π y² = -log (∫ z,
exp (-(g (z,y) - π y²)) dz)` and the integrand is jointly log-concave, so its marginal is
log-concave by `Commons.Analysis.Convex.logconcave_marginal_prod`; conclude by the
one-dimensional "convex ⟹ second derivative ≥ 0" fact
(`ConvexOn.monotoneOn_deriv` + `Monotone.deriv_nonneg`).

**(P4) Product step.**  Assuming the Brascamp–Lieb inequality on `G` for all potentials
`F : G → ℝ` of class `C²` with `D²F ⪰ 2π·Id` (`Gcom`-hypotheses) and all `H : G → ℝ` of class `C¹`
with polynomial growth, prove it on `V = WithLp 2 (G × ℝ)`:
  * apply the induction hypothesis on the slices to `z ↦ h (z, y)` and to
    `z ↦ (λ * h (z, y) + μ * ∂_y g (z, y))` (for all `λ μ : ℝ`) to obtain the `2×2` Loewner
    inequality between `[[condVar g h, condCov g h (∂_y g)], [·, condVar g (∂_y g)]]` and the
    matrix of slice Hessian energies;
  * apply the sharp one-dimensional inequality (`brascamp_lieb_one_dim_sharp`) to `condMean g h`
    with potential `U` from (P3): `Var_{e^{-U}}(condMean g h) ≤ ∫ (condMean g h)'² / U'' e^{-U}`;
  * conclude with the algebra lemma `sq_div_sub_sq_div_le` and a conditional Cauchy–Schwarz
    comparison;
  * finally rewrite the result as the Hessian form on `V` using the block form of the inverse of a
    positive definite self-adjoint operator on `G × ℝ` (Schur complement): for
    `A : G →L[ℝ] G`, `b : G`, `c : ℝ` the blocks of `hessOp f x`, and `Ab := A⁻¹ b`,
    `s := c - ⟪Ab, b⟫`,
      `⟪hessInv f x (u, t), (u, t)⟫ = ⟪A⁻¹ u, u⟫ + (t - ⟪Ab, u⟫) ^ 2 / s`.

**(P5) Transport along a linear isometry.**  For `e : E ≃ₗᵢ[ℝ] F` and `f h : E → ℝ`,
`wVar (fun x => exp (-(f x))) h = wVar (fun y => exp (-(f (e.symm y)))) (h ∘ e.symm)` and
`grad (h ∘ e.symm) y = e (grad h (e.symm y))`,
`hessInv (f ∘ e.symm) y = e ∘ hessInv f (e.symm y) ∘ e.symm`, so the Brascamp–Lieb inequality for
`f ∘ e.symm` on `F` implies the one for `f` on `E` (`LinearIsometryEquiv.measurePreserving`).

**(P6) Induction.**  `brascamp_lieb_smooth` is proved by induction on `n` for
`EuclideanSpace ℝ (Fin n)`:  `n = 0` is trivial; `n = 1` follows from the sharp one-dimensional
inequality on `ℝ` and the isometry `ℝ ≃ₗᵢ EuclideanSpace ℝ (Fin 1)`; the step `n → n + 1` uses
`Commons.Analysis.InnerProductSpace.euclidean_split_isometry` and (P4) + (P5).

**(P7) Truncation.**  Let `A` be convex and let `φ_ε ≥ 0` be smooth convex with `φ_ε = 0` on `A`
and `φ_ε ≥ dist (·, A)² / ε - o(1)`; set `f_ε := π‖·‖² + φ_ε`.  Then `D²f_ε ⪰ 2π·Id` (by
`Commons.Analysis.Convex.fderiv2_nonneg_of_convexOn`) and `f_ε - π‖·‖²` is convex, so (P6) applies;
passing to the limit `ε → 0` with dominated convergence (`exp (-(f_ε x)) ≤ exp (-π‖x‖²)`)
gives the target.

-/

open MeasureTheory Set Real Filter
open scoped Real Topology InnerProductSpace

namespace Commons.Analysis.GaussianMeasure

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

noncomputable section

/-! ### The `π`-normalised Gaussian density on `ℝ` -/

/-- `π`-normalised Gaussian density. -/
noncomputable def pgaus (x : ℝ) : ℝ := Real.exp (-Real.pi * x ^ 2)

lemma pgaus_pos (x : ℝ) : 0 < pgaus x := Real.exp_pos _
lemma pgaus_cont : Continuous pgaus := by unfold pgaus; fun_prop
lemma pgaus_nonneg (x : ℝ) : 0 ≤ pgaus x := (pgaus_pos x).le

lemma pgaus_int : Integrable pgaus := by
  rw [show pgaus = fun x : ℝ => Real.exp (-Real.pi * x ^ 2) from rfl]
  exact integrable_exp_neg_mul_sq (by positivity)

lemma integral_pgaus : ∫ x, pgaus x = 1 := by
  rw [show pgaus = fun x : ℝ => Real.exp (-Real.pi * x ^ 2) from rfl, integral_gaussian]
  norm_num

/-! ### Riesz representation infrastructure

For a finite-dimensional real inner product space `E` and `f : E → ℝ` we package the gradient and
the Hessian of `f` as an element of `E` and an operator `E →L[ℝ] E` respectively, via the Riesz
representation theorem.  These are the objects appearing in the statement of the Brascamp–Lieb
inequality. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

/-- The gradient of `f` at `x`, defined through the Riesz representation theorem
(`InnerProductSpace.toDual`), so that `⟪grad f x, v⟫ = fderiv ℝ f x v`. -/
noncomputable def grad (f : E → ℝ) (x : E) : E :=
  (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)

lemma grad_spec (f : E → ℝ) (x v : E) : ⟪grad f x, v⟫_ℝ = fderiv ℝ f x v := by
  simp [grad, InnerProductSpace.toDual_symm_apply]

/-- The gradient is the Riesz vector of the derivative, so the norms agree. -/
lemma grad_norm_eq (f : E → ℝ) (x : E) : ‖grad f x‖ = ‖fderiv ℝ f x‖ := by
  rw [grad]
  exact (InnerProductSpace.toDual ℝ E).symm.norm_map _

/-- The Hessian of `f` at `x`, viewed as a continuous linear operator `E →L[ℝ] E` through the
Riesz representation theorem: `⟪hessOp f x v, w⟫ = D²f(x)(v,w)`. -/
noncomputable def hessOp (f : E → ℝ) (x : E) : E →L[ℝ] E :=
  ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap).comp (fderiv ℝ (fderiv ℝ f) x)

lemma hessOp_spec (f : E → ℝ) (x v w : E) :
    ⟪hessOp f x v, w⟫_ℝ = fderiv ℝ (fderiv ℝ f) x v w := by
  simp [hessOp, InnerProductSpace.toDual_symm_apply]

/-- The Hessian operator of a `C²` function is self-adjoint. -/
lemma hessOp_symm (f : E → ℝ) (hf : ContDiff ℝ 2 f) (x v w : E) :
    ⟪hessOp f x v, w⟫_ℝ = ⟪v, hessOp f x w⟫_ℝ := by
  rw [hessOp_spec f x v w]
  have h : ⟪v, hessOp f x w⟫_ℝ = fderiv ℝ (fderiv ℝ f) x w v := by
    rw [real_inner_comm]
    exact hessOp_spec f x w v
  rw [h]
  exact ContDiffAt.isSymmSndFDerivAt hf.contDiffAt (by simp) v w

/-- If the Hessian of `f` dominates `2π·Id` (as a quadratic form), then `hessOp f x` is injective;
in particular it is invertible when `E` is finite-dimensional. -/
lemma hessOp_injective (f : E → ℝ) (x : E)
    (hH : ∀ v : E, 2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v) :
    Function.Injective (hessOp f x) := by
  intro u v huv
  have h1 : fderiv ℝ (fderiv ℝ f) x (u - v) (u - v) = 0 := by
    have h0 : hessOp f x (u - v) = 0 := by simp [huv]
    rw [← hessOp_spec, h0]; simp
  have h2 := hH (u - v)
  rw [h1] at h2
  have h3 : ‖u - v‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖u - v‖, h2, Real.pi_pos]
  have h4 : ‖u - v‖ = 0 := by nlinarith [sq_nonneg ‖u - v‖, norm_nonneg (u - v), h3]
  exact sub_eq_zero.mp (norm_eq_zero.mp h4)

/-- The inverse of the Hessian operator `hessOp f x`, as a linear map (with the value `0` when the
Hessian is not injective; the lemmas below are stated under the injectivity hypothesis). -/
noncomputable def hessInv (f : E → ℝ) (x : E) : E →ₗ[ℝ] E := by
  classical
  exact if h : Function.Injective (hessOp f x) then
    ((LinearEquiv.ofInjectiveEndo ((hessOp f x).toLinearMap) h).symm : E →ₗ[ℝ] E)
  else 0

lemma hessInv_apply_of_injective (f : E → ℝ) (x : E) (hinj : Function.Injective (hessOp f x)) :
    hessInv f x = ((LinearEquiv.ofInjectiveEndo ((hessOp f x).toLinearMap) hinj).symm : E →ₗ[ℝ] E) := by
  rw [hessInv, dif_pos hinj]

lemma hessInv_left (f : E → ℝ) (x : E) (hinj : Function.Injective (hessOp f x)) (v : E) :
    hessInv f x (hessOp f x v) = v := by
  rw [hessInv_apply_of_injective f x hinj]
  exact LinearEquiv.symm_apply_apply (LinearEquiv.ofInjectiveEndo ((hessOp f x).toLinearMap) hinj) v

lemma hessInv_right (f : E → ℝ) (x : E) (hinj : Function.Injective (hessOp f x)) (u : E) :
    hessOp f x (hessInv f x u) = u := by
  rw [hessInv_apply_of_injective f x hinj]
  exact LinearEquiv.apply_symm_apply (LinearEquiv.ofInjectiveEndo ((hessOp f x).toLinearMap) hinj) u

/-- Energy estimate for the inverse Hessian: if `D²f(x) ⪰ 2π·Id` then
`⟪hessInv u, u⟫ ≤ ‖u‖²/(2π)`. -/
lemma hessInv_energy (f : E → ℝ) (x : E) (hinj : Function.Injective (hessOp f x))
    (hH : ∀ v : E, 2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v) (u : E) :
    ⟪hessInv f x u, u⟫_ℝ ≤ ‖u‖ ^ 2 / (2 * Real.pi) := by
  set w : E := hessInv f x u with hwdef
  have hw' : hessOp f x w = u := hessInv_right f x hinj u
  have h1 : 2 * Real.pi * ‖w‖ ^ 2 ≤ ⟪u, w⟫_ℝ := by
    have h := hH w
    have h2 : fderiv ℝ (fderiv ℝ f) x w w = ⟪hessOp f x w, w⟫_ℝ := (hessOp_spec f x w w).symm
    rw [h2] at h
    rwa [hw'] at h
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  have h4 : ⟪u, w⟫_ℝ ≤ ‖u‖ * ‖w‖ := real_inner_le_norm u w
  have h5 : (2 * Real.pi) * ‖w‖ ≤ ‖u‖ := by
    by_cases hw0 : ‖w‖ = 0
    · rw [hw0, mul_zero]; exact norm_nonneg u
    · have hwpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hw0)
      have h6 : (2 * Real.pi) * ‖w‖ * ‖w‖ ≤ ‖u‖ * ‖w‖ := by nlinarith [h1, h4]
      exact le_of_mul_le_mul_right h6 hwpos
  have h8 : ‖w‖ ≤ ‖u‖ / (2 * Real.pi) := by
    rw [le_div_iff₀ hpi]; linarith
  calc ⟪w, u⟫_ℝ ≤ ‖w‖ * ‖u‖ := real_inner_le_norm w u
    _ ≤ (‖u‖ / (2 * Real.pi)) * ‖u‖ := mul_le_mul_of_nonneg_right h8 (norm_nonneg u)
    _ = ‖u‖ ^ 2 / (2 * Real.pi) := by ring




/-- Linearity of the gradient in the function argument. -/
lemma grad_add (f g : E → ℝ) (x : E) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) : grad (f + g) x = grad f x + grad g x := by
  refine ext_inner_right ℝ (fun v => ?_)
  rw [grad_spec, inner_add_left, grad_spec, grad_spec, fderiv_add hf hg]
  rfl

/-- The gradient commutes with multiplication by a constant. -/
lemma grad_const_mul (c : ℝ) (f : E → ℝ) (x : E) (hf : DifferentiableAt ℝ f x) :
    grad (fun z => c * f z) x = c • grad f x := by
  refine ext_inner_right ℝ (fun v => ?_)
  rw [grad_spec]
  rw [show (fun z : E => c * f z) = fun z : E => c • f z from rfl,
    fderiv_fun_const_smul hf c]
  rw [smul_apply, smul_eq_mul, inner_smul_left, grad_spec]
  simp

/-- The inverse Hessian of a `C²` function with `D²f ⪰ 2π·Id` is self-adjoint. -/
lemma hessInv_symm (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (hH : ∀ x v : E, 2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v) (x u v : E) :
    ⟪hessInv f x u, v⟫_ℝ = ⟪u, hessInv f x v⟫_ℝ := by
  have hinj : Function.Injective (hessOp f x) := hessOp_injective f x (hH x)
  have hAL : ∀ u, hessInv f x (hessOp f x u) = u := fun u => hessInv_left f x hinj u
  have hAR : ∀ u, hessOp f x (hessInv f x u) = u := fun u => hessInv_right f x hinj u
  have hAsym : ∀ u v, ⟪hessOp f x u, v⟫_ℝ = ⟪u, hessOp f x v⟫_ℝ :=
    fun u v => hessOp_symm f hf x u v
  have h1 : ⟪hessInv f x u, v⟫_ℝ = ⟪hessInv f x u, hessOp f x (hessInv f x v)⟫_ℝ := by rw [hAR v]
  have h2 : ⟪hessInv f x u, hessOp f x (hessInv f x v)⟫_ℝ
      = ⟪hessOp f x (hessInv f x u), hessInv f x v⟫_ℝ := (hAsym _ _).symm
  have h3 : ⟪hessOp f x (hessInv f x u), hessInv f x v⟫_ℝ = ⟪u, hessInv f x v⟫_ℝ := by rw [hAR u]
  rw [h1, h2, h3]

/-- Norm bound for the inverse Hessian: `‖(D²f)⁻¹u‖ ≤ ‖u‖/(2π)` when `D²f ⪰ 2π·Id`. -/
lemma hessInv_norm_le (f : E → ℝ) (x : E) (hinj : Function.Injective (hessOp f x))
    (hH : ∀ v : E, 2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v) (u : E) :
    ‖hessInv f x u‖ ≤ ‖u‖ / (2 * Real.pi) := by
  set w : E := hessInv f x u with hwdef
  have hw' : hessOp f x w = u := hessInv_right f x hinj u
  have h1 : 2 * Real.pi * ‖w‖ ^ 2 ≤ ⟪u, w⟫_ℝ := by
    have h := hH w
    have h2 : fderiv ℝ (fderiv ℝ f) x w w = ⟪hessOp f x w, w⟫_ℝ := (hessOp_spec f x w w).symm
    rw [h2] at h
    rwa [hw'] at h
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  have h4 : ⟪u, w⟫_ℝ ≤ ‖u‖ * ‖w‖ := real_inner_le_norm u w
  have h5 : (2 * Real.pi) * ‖w‖ ≤ ‖u‖ := by
    by_cases hw0 : ‖w‖ = 0
    · rw [hw0, mul_zero]; exact norm_nonneg u
    · have hwpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hw0)
      have h6 : (2 * Real.pi) * ‖w‖ * ‖w‖ ≤ ‖u‖ * ‖w‖ := by nlinarith [h1, h4]
      exact le_of_mul_le_mul_right h6 hwpos
  rw [hwdef]
  rw [le_div_iff₀ hpi]
  linarith

/-- The tangent-line lower bound for a convex differentiable function on a real normed space. -/
lemma convexOn_tangent_le {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    (g : E₀ → ℝ) (hconv : ConvexOn ℝ Set.univ g) (hd : DifferentiableAt ℝ g 0) (p : E₀) :
    g 0 + fderiv ℝ g 0 p ≤ g p := by
  have hψconv : ConvexOn ℝ Set.univ (fun t : ℝ => g (t • p)) := by
    refine ⟨convex_univ, fun s _ t _ a b ha hb hab => ?_⟩
    have h1 := hconv.2 (Set.mem_univ (s • p)) (Set.mem_univ (t • p)) ha hb hab
    have h2 : (a * s + b * t : ℝ) • p = a • (s • p) + b • (t • p) := by
      simp only [add_smul, smul_smul]
    simp only [smul_eq_mul]
    rw [h2]
    simpa using h1
  have h1 : HasDerivAt (fun t : ℝ => t • p) p 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).smul_const p
  have hd' : DifferentiableAt ℝ g ((0:ℝ) • p) := by simpa using hd
  have h2 : HasDerivAt (fun t : ℝ => g (t • p)) (fderiv ℝ g ((0:ℝ) • p) p) 0 :=
    hd'.hasFDerivAt.comp_hasDerivAt 0 h1
  simp only [zero_smul] at h2
  have hderiv : deriv (fun t : ℝ => g (t • p)) 0 = fderiv ℝ g 0 p := h2.deriv
  have htan := hψconv.deriv_le_slope (Set.mem_univ 0) (Set.mem_univ 1) (by norm_num)
    h2.differentiableAt
  rw [slope_def_field, hderiv] at htan
  have hpos : (0:ℝ) < 1 - 0 := by norm_num
  have h3 := mul_le_mul_of_nonneg_right htan hpos.le
  rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at h3
  simp only [one_smul, zero_smul, sub_zero, mul_one] at h3
  linarith [h3]

lemma continuous_hessInv_pair (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (hH : ∀ x v : E, 2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v) :
    Continuous fun p : E × E => hessInv f p.1 p.2 := by
  have hD : Continuous (fun z : E => fderiv ℝ (fderiv ℝ f) z) := by
    have h2 : ContDiff ℝ 1 (fderiv ℝ f) :=
      ((contDiff_succ_iff_fderiv (𝕜 := ℝ) (n := 1) (f := f)).mp hf).2.2
    exact h2.continuous_fderiv (by norm_num)
  have hcontH : Continuous (fun z : E => hessOp f z) := by
    have h2 : hessOp f = fun z : E =>
        ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap).comp
          (fderiv ℝ (fderiv ℝ f) z) := rfl
    rw [h2]
    exact continuous_const.clm_comp hD
  rw [Metric.continuous_iff]
  rintro ⟨z₀, u₀⟩ ε hε
  have hπ : (0:ℝ) < 2 * Real.pi := by positivity
  have hden : (0:ℝ) < ‖u₀‖ + 1 := by positivity
  have hcH : ∀ δ₂ : ℝ, 0 < δ₂ → ∃ η : ℝ, 0 < η ∧ ∀ z : E, ‖z - z₀‖ < η →
      ‖hessOp f z - hessOp f z₀‖ < δ₂ := by
    intro δ₂ hδ₂
    obtain ⟨η, hη0, hη⟩ := (Metric.continuous_iff.mp hcontH) z₀ δ₂ hδ₂
    exact ⟨η, hη0, fun z hz => by
      have h := hη z (by rw [dist_eq_norm]; exact hz)
      rwa [dist_eq_norm] at h⟩
  obtain ⟨η, hη0, hη⟩ := hcH (2 * Real.pi ^ 2 * ε / (‖u₀‖ + 1)) (by positivity)
  refine ⟨min η (min 1 (Real.pi * ε)),
    lt_min hη0 (lt_min one_pos (by positivity)), ?_⟩
  rintro ⟨z, u⟩ hp
  rw [dist_eq_norm] at hp
  have hz1 : ‖z - z₀‖ ≤ ‖(z, u) - (z₀, u₀)‖ := by
    rw [Prod.norm_def]; exact le_max_left _ _
  have hu1 : ‖u - u₀‖ ≤ ‖(z, u) - (z₀, u₀)‖ := by
    rw [Prod.norm_def]; exact le_max_right _ _
  have hzlt : ‖z - z₀‖ < η := lt_of_le_of_lt hz1 (lt_of_lt_of_le hp (min_le_left _ _))
  have hult : ‖u - u₀‖ < Real.pi * ε := lt_of_le_of_lt hu1 (lt_of_lt_of_le hp
    (le_trans (min_le_right _ _) (min_le_right _ _)))
  have huone : ‖u - u₀‖ < 1 := lt_of_le_of_lt hu1 (lt_of_lt_of_le hp
    (le_trans (min_le_right _ _) (min_le_left _ _)))
  set w : E := hessInv f z u with hwdef
  set w₀ : E := hessInv f z₀ u₀ with hw₀def
  have hinjz : Function.Injective (hessOp f z) := hessOp_injective f z (hH z)
  have hinj0 : Function.Injective (hessOp f z₀) := hessOp_injective f z₀ (hH z₀)
  have hw : hessOp f z w = u := hessInv_right f z hinjz u
  have hw₀ : hessOp f z₀ w₀ = u₀ := hessInv_right f z₀ hinj0 u₀
  have hquad : 2 * Real.pi * ‖w - w₀‖ ^ 2 ≤ ⟪hessOp f z₀ (w - w₀), w - w₀⟫_ℝ := by
    have h1 := hH z₀ (w - w₀)
    rwa [← hessOp_spec] at h1
  have hsplit : hessOp f z₀ (w - w₀) = (u - u₀) + (hessOp f z₀ - hessOp f z) w := by
    have e1 : hessOp f z₀ (w - w₀) = hessOp f z₀ w - u₀ := by rw [map_sub, hw₀]
    have e2 : (hessOp f z₀ - hessOp f z) w = hessOp f z₀ w - u := by
      rw [sub_apply, hw]
    rw [e1, e2]; abel
  have hbound : 2 * Real.pi * ‖w - w₀‖ ^ 2
      ≤ (‖u - u₀‖ + ‖hessOp f z₀ - hessOp f z‖ * ‖w‖) * ‖w - w₀‖ := by
    calc 2 * Real.pi * ‖w - w₀‖ ^ 2 ≤ ⟪hessOp f z₀ (w - w₀), w - w₀⟫_ℝ := hquad
      _ = ⟪(u - u₀) + (hessOp f z₀ - hessOp f z) w, w - w₀⟫_ℝ := by rw [hsplit]
      _
        ≤ ‖(u - u₀) + (hessOp f z₀ - hessOp f z) w‖ * ‖w - w₀‖ := real_inner_le_norm _ _
      _ ≤ (‖u - u₀‖ + ‖(hessOp f z₀ - hessOp f z) w‖) * ‖w - w₀‖ := by
          gcongr
          exact norm_add_le _ _
      _ ≤ (‖u - u₀‖ + ‖hessOp f z₀ - hessOp f z‖ * ‖w‖) * ‖w - w₀‖ := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
  have hstep : 2 * Real.pi * ‖w - w₀‖ ≤ ‖u - u₀‖ + ‖hessOp f z₀ - hessOp f z‖ * ‖w‖ := by
    rcases eq_or_lt_of_le (norm_nonneg (w - w₀)) with h | h
    · rw [← h]; simp only [mul_zero]; positivity
    · have h2 : 2 * Real.pi * ‖w - w₀‖ * ‖w - w₀‖
          ≤ (‖u - u₀‖ + ‖hessOp f z₀ - hessOp f z‖ * ‖w‖) * ‖w - w₀‖ := by
        calc 2 * Real.pi * ‖w - w₀‖ * ‖w - w₀‖ = 2 * Real.pi * ‖w - w₀‖ ^ 2 := by ring
          _ ≤ _ := hbound
      exact le_of_mul_le_mul_right h2 h
  have hwbound : ‖w‖ ≤ (‖u₀‖ + 1) / (2 * Real.pi) := by
    have h1 : ‖w‖ ≤ ‖u‖ / (2 * Real.pi) := hessInv_norm_le f z hinjz (hH z) u
    have h2 : ‖u‖ ≤ ‖u₀‖ + 1 := by
      calc ‖u‖ ≤ ‖u₀‖ + ‖u - u₀‖ := by
            calc ‖u‖ = ‖u₀ + (u - u₀)‖ := by rw [add_sub_cancel]
              _ ≤ ‖u₀‖ + ‖u - u₀‖ := norm_add_le _ _
        _ ≤ ‖u₀‖ + 1 := by linarith
    calc ‖w‖ ≤ ‖u‖ / (2 * Real.pi) := h1
      _ ≤ (‖u₀‖ + 1) / (2 * Real.pi) := by gcongr
  have hΔ : ‖hessOp f z₀ - hessOp f z‖ < 2 * Real.pi ^ 2 * ε / (‖u₀‖ + 1) := by
    rw [norm_sub_rev (hessOp f z₀) (hessOp f z)]
    exact hη z hzlt
  have key : 2 * Real.pi * ‖w - w₀‖ ≤ ‖u - u₀‖ + ‖hessOp f z₀ - hessOp f z‖ * ((‖u₀‖ + 1) / (2 * Real.pi)) := by
    calc 2 * Real.pi * ‖w - w₀‖ ≤ ‖u - u₀‖ + ‖hessOp f z₀ - hessOp f z‖ * ‖w‖ := hstep
      _ ≤ ‖u - u₀‖ + ‖hessOp f z₀ - hessOp f z‖ * ((‖u₀‖ + 1) / (2 * Real.pi)) := by
          gcongr
  have hfin : 2 * Real.pi * ‖w - w₀‖ < 2 * Real.pi * ε := by
    have h3 : ‖hessOp f z₀ - hessOp f z‖ * ((‖u₀‖ + 1) / (2 * Real.pi))
        < (2 * Real.pi ^ 2 * ε / (‖u₀‖ + 1)) * ((‖u₀‖ + 1) / (2 * Real.pi)) := by
      refine mul_lt_mul_of_pos_right hΔ (by positivity)
    have h4 : (2 * Real.pi ^ 2 * ε / (‖u₀‖ + 1)) * ((‖u₀‖ + 1) / (2 * Real.pi))
        = Real.pi * ε := by
      field_simp; try ring
    linarith [key, hult, h3, le_of_eq h4]
  have hfin2 : ‖w - w₀‖ < ε := by nlinarith [hπ, hfin]
  show dist (hessInv f z u) (hessInv f z₀ u₀) < ε
  rw [dist_eq_norm]
  exact hfin2

lemma continuous_grad_of_contDiff (A : E → ℝ) (hA : ContDiff ℝ 1 A) :
    Continuous (fun z : E => grad A z) := by
  have h := hA.continuous_fderiv (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  exact ((InnerProductSpace.toDual ℝ E).symm.continuous).comp h

lemma continuous_inverse_family {ι : Type*} [PseudoMetricSpace ι]
    (H : ι → (E →L[ℝ] E)) (I : ι → E → E) (hHc : Continuous H)
    (hquad : ∀ (i : ι) (v : E), 2 * Real.pi * ‖v‖ ^ 2 ≤ ⟪H i v, v⟫_ℝ)
    (hleft : ∀ i u, I i (H i u) = u) (hright : ∀ i u, H i (I i u) = u)
    (hbdd : ∀ i u, ‖I i u‖ ≤ ‖u‖ / (2 * Real.pi)) :
    Continuous (fun q : ι × E => I q.1 q.2) := by
  rw [Metric.continuous_iff]
  rintro ⟨i₀, u₀⟩ ε hε
  have hπ : (0:ℝ) < 2 * Real.pi := by positivity
  have hden : (0:ℝ) < ‖u₀‖ + 1 := by positivity
  obtain ⟨η, hη0, hη⟩ := (Metric.continuous_iff.mp hHc) i₀ (2 * Real.pi ^ 2 * ε / (‖u₀‖ + 1))
    (by positivity)
  refine ⟨min η (Real.pi * ε), lt_min hη0 (by positivity), ?_⟩
  rintro ⟨i, u⟩ hq
  have hi1 : dist i i₀ ≤ dist (i, u) (i₀, u₀) := by
    rw [Prod.dist_eq]; exact le_max_left _ _
  have hu1 : dist u u₀ ≤ dist (i, u) (i₀, u₀) := by
    rw [Prod.dist_eq]; exact le_max_right _ _
  have hilt : dist i i₀ < η := lt_of_le_of_lt hi1 (lt_of_lt_of_le hq (min_le_left _ _))
  have hult : ‖u - u₀‖ < Real.pi * ε := by
    rw [dist_eq_norm] at hu1
    exact lt_of_le_of_lt hu1 (lt_of_lt_of_le hq (min_le_right _ _))
  have hΔ : ‖H i - H i₀‖ < 2 * Real.pi ^ 2 * ε / (‖u₀‖ + 1) := by
    have h := hη i hilt
    rwa [dist_eq_norm] at h
  set w : E := I i u with hwdef
  set w₀ : E := I i₀ u₀ with hw₀def
  have hw : H i w = u := hright i u
  have hw₀ : H i₀ w₀ = u₀ := hright i₀ u₀
  have hkey : H i (w - w₀) = (u - u₀) - (H i - H i₀) w₀ := by
    rw [map_sub, hw, ← hw₀, sub_apply]
    abel
  have hbound : 2 * Real.pi * ‖w - w₀‖ ^ 2
      ≤ (‖u - u₀‖ + ‖H i - H i₀‖ * ‖w₀‖) * ‖w - w₀‖ := by
    calc 2 * Real.pi * ‖w - w₀‖ ^ 2 ≤ ⟪H i (w - w₀), w - w₀⟫_ℝ := hquad i (w - w₀)
      _ = ⟪(u - u₀) - (H i - H i₀) w₀, w - w₀⟫_ℝ := by rw [hkey]
      _ ≤ ‖(u - u₀) - (H i - H i₀) w₀‖ * ‖w - w₀‖ := real_inner_le_norm _ _
      _ ≤ (‖u - u₀‖ + ‖(H i - H i₀) w₀‖) * ‖w - w₀‖ := by
          gcongr
          exact norm_sub_le _ _
      _ ≤ (‖u - u₀‖ + ‖H i - H i₀‖ * ‖w₀‖) * ‖w - w₀‖ := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
  have hw₀b : ‖w₀‖ ≤ ‖u₀‖ / (2 * Real.pi) := hbdd i₀ u₀
  have hstep : 2 * Real.pi * ‖w - w₀‖ ≤ ‖u - u₀‖ + ‖H i - H i₀‖ * (‖u₀‖ / (2 * Real.pi)) := by
    have hA : 0 ≤ ‖u - u₀‖ + ‖H i - H i₀‖ * ‖w₀‖ := by positivity
    rcases eq_or_lt_of_le (norm_nonneg (w - w₀)) with h | h
    · rw [← h]; simp only [mul_zero]; positivity
    · have h2 : 2 * Real.pi * ‖w - w₀‖ * ‖w - w₀‖
          ≤ (‖u - u₀‖ + ‖H i - H i₀‖ * ‖w₀‖) * ‖w - w₀‖ := by
        calc 2 * Real.pi * ‖w - w₀‖ * ‖w - w₀‖ = 2 * Real.pi * ‖w - w₀‖ ^ 2 := by ring
          _ ≤ _ := hbound
      have h3 : 2 * Real.pi * ‖w - w₀‖ ≤ ‖u - u₀‖ + ‖H i - H i₀‖ * ‖w₀‖ :=
        le_of_mul_le_mul_right h2 h
      calc 2 * Real.pi * ‖w - w₀‖ ≤ ‖u - u₀‖ + ‖H i - H i₀‖ * ‖w₀‖ := h3
        _ ≤ ‖u - u₀‖ + ‖H i - H i₀‖ * (‖u₀‖ / (2 * Real.pi)) := by gcongr
  have hfin : 2 * Real.pi * ‖w - w₀‖ < 2 * Real.pi * ε := by
    have h3 : ‖H i - H i₀‖ * (‖u₀‖ / (2 * Real.pi))
        ≤ (2 * Real.pi ^ 2 * ε / (‖u₀‖ + 1)) * (‖u₀‖ / (2 * Real.pi)) :=
      mul_le_mul_of_nonneg_right hΔ.le (by positivity)
    have h4 : (2 * Real.pi ^ 2 * ε / (‖u₀‖ + 1)) * (‖u₀‖ / (2 * Real.pi)) < Real.pi * ε := by
      have h1 : (2 * Real.pi ^ 2 * ε / (‖u₀‖ + 1)) * (‖u₀‖ / (2 * Real.pi))
          = Real.pi * ε * (‖u₀‖ / (‖u₀‖ + 1)) := by
        field_simp
        try ring
      rw [h1]
      have h2 : ‖u₀‖ / (‖u₀‖ + 1) < 1 := by
        rw [div_lt_one (by positivity)]
        linarith
      calc Real.pi * ε * (‖u₀‖ / (‖u₀‖ + 1)) < Real.pi * ε * 1 :=
            mul_lt_mul_of_pos_left h2 (by positivity)
        _ = Real.pi * ε := by ring
    linarith [hstep, hult, h3, h4]
  rw [dist_eq_norm]
  nlinarith [hπ, hfin]

/-! ### Brascamp–Lieb on an abstract finite-dimensional inner product space,
and its transport along a linear isometry -/

/-- **Brascamp–Lieb inequality on a finite-dimensional real inner product space `E`.**
For a `C²` potential `f` with `D²f ⪰ 2π·Id` whose excess `f - π‖·‖²` is convex, and a `C¹`
function `h`, both of polynomial growth, the variance of `h` with respect to the measure
`exp (-f) dx` is bounded by the Hessian energy `∫ ⟪(D²f)⁻¹ ∇h, ∇h⟫ exp (-f)`.

The growth hypotheses are stated in the weak "quadratic form" form, which makes the statement
invariant under linear isometries. -/
def BLon (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] : Prop :=
  ∀ (f h : E → ℝ), ContDiff ℝ 2 f →
    (∀ x v : E, 2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v) →
    ConvexOn ℝ Set.univ (fun x => f x - Real.pi * ‖x‖ ^ 2) →
    (∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E,
      |fderiv ℝ f x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ f) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2) →
    ContDiff ℝ 1 h →
    (∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E,
      |h x| ≤ C * (1 + ‖x‖) ^ N ∧
      |fderiv ℝ h x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖) →
    (∫ x, h x ^ 2 * Real.exp (-(f x)))
        - (∫ x, h x * Real.exp (-(f x))) ^ 2 / (∫ x, Real.exp (-(f x)))
      ≤ ∫ x, ⟪hessInv f x (grad h x), grad h x⟫_ℝ * Real.exp (-(f x))

section IsometryTransport

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F] [MeasurableSpace F] [BorelSpace F]

/-- First derivative chain rule for the composition with a linear isometry. -/
lemma fderiv_comp_isometry (e : E ≃ₗᵢ[ℝ] F) (g : F → ℝ) (x : E)
    (hg : DifferentiableAt ℝ g (e x)) :
    fderiv ℝ (fun y : E => g (e y)) x = (fderiv ℝ g (e x)).comp (↑↑e : E →L[ℝ] F) := by
  have he : DifferentiableAt ℝ (⇑e) x := e.differentiable.differentiableAt
  have h1 : fderiv ℝ (fun y : E => g (e y)) x
      = (fderiv ℝ g (e x)).comp (fderiv ℝ (⇑e) x) := by
    have h := fderiv_comp (𝕜 := ℝ) x (f := (⇑e : E → F)) (g := g) (hg := hg) (hf := he)
    simpa [Function.comp_def] using h
  rw [h1, show fderiv ℝ (⇑e) x = (↑↑e : E →L[ℝ] F) from (e.hasFDerivAt).fderiv]

/-- The gradient is natural under a linear isometry. -/
lemma grad_comp_isometry (e : E ≃ₗᵢ[ℝ] F) (g : F → ℝ) (x : E)
    (hg : DifferentiableAt ℝ g (e x)) :
    grad (fun y : E => g (e y)) x = e.symm (grad g (e x)) := by
  have hd := fderiv_comp_isometry e g x hg
  refine ext_inner_right ℝ (fun v => ?_)
  rw [grad_spec, hd, ContinuousLinearMap.comp_apply]
  rw [show ⟪e.symm (grad g (e x)), v⟫_ℝ = ⟪grad g (e x), e v⟫_ℝ from by
    rw [← e.inner_map_map (e.symm (grad g (e x))) v, e.apply_symm_apply]]
  rw [grad_spec]
  rfl

/-- Convexity of `f - π‖·‖²` is preserved by precomposition with a linear isometry. -/
lemma convexOn_comp_linearIsometryEquiv (e : E ≃ₗᵢ[ℝ] F) (f : F → ℝ)
    (h : ConvexOn ℝ Set.univ (fun y => f y - Real.pi * ‖y‖ ^ 2)) :
    ConvexOn ℝ Set.univ (fun x : E => f (e x) - Real.pi * ‖x‖ ^ 2) := by
  have h1 : ConvexOn ℝ Set.univ ((fun y : F => f y - Real.pi * ‖y‖ ^ 2) ∘ (⇑e)) :=
    h.comp_linearMap (e.toLinearEquiv.toLinearMap)
  simpa [Function.comp_def, LinearIsometryEquiv.norm_map] using h1

/-- Change of variables for the integral along a linear isometry. -/
lemma integral_comp_isometry (e : E ≃ₗᵢ[ℝ] F) (G : F → ℝ) :
    (∫ x : E, G (e x)) = ∫ y : F, G y :=
  (e.measurePreserving).integral_comp e.toHomeomorph.toMeasurableEquiv.measurableEmbedding G

/-- First derivative chain rule for the composition with a linear isometry, in applied form. -/
lemma fderiv_comp_isometry_apply (e : E ≃ₗᵢ[ℝ] F) (g : F → ℝ) (x : E)
    (hg : DifferentiableAt ℝ g (e x)) (v : E) :
    fderiv ℝ (fun y : E => g (e y)) x v = fderiv ℝ g (e x) (e v) := by
  rw [fderiv_comp_isometry e g x hg]
  rfl

/-- Second derivative chain rule for the composition with a linear isometry. -/
lemma fderiv_fderiv_comp_isometry (e : E ≃ₗᵢ[ℝ] F) (g : F → ℝ) (hg : ContDiff ℝ 2 g)
    (x v w : E) :
    fderiv ℝ (fderiv ℝ (fun y : E => g (e y))) x v w
      = fderiv ℝ (fderiv ℝ g) (e x) (e v) (e w) :=
  Commons.Analysis.Calculus.fderiv_fderiv_comp_continuousLinearMap (↑↑e : E →L[ℝ] F) g hg x v w

/-- The Hessian operator is natural under a linear isometry. -/
lemma hessOp_comp_isometry (e : E ≃ₗᵢ[ℝ] F) (g : F → ℝ) (hg : ContDiff ℝ 2 g) (x : E) :
    hessOp (fun y : E => g (e y)) x
      = (↑↑e.symm : F →L[ℝ] E).comp ((hessOp g (e x)).comp (↑↑e : E →L[ℝ] F)) := by
  ext v
  refine ext_inner_right ℝ (fun w => ?_)
  rw [hessOp_spec, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  have hstep : ⟪(↑↑e.symm : F →L[ℝ] E) ((hessOp g (e x)) ((↑↑e : E →L[ℝ] F) v)), w⟫_ℝ
      = ⟪(hessOp g (e x)) (e v), e w⟫_ℝ := by
    rw [show (↑↑e.symm : F →L[ℝ] E) ((hessOp g (e x)) ((↑↑e : E →L[ℝ] F) v))
          = e.symm (hessOp g (e x) (e v)) from rfl,
      ← e.inner_map_map (e.symm (hessOp g (e x) (e v))) w, e.apply_symm_apply]
  rw [hstep, hessOp_spec]
  exact fderiv_fderiv_comp_isometry e g hg x v w

/-- The inverse Hessian is natural under a linear isometry. -/
lemma hessInv_comp_isometry (e : E ≃ₗᵢ[ℝ] F) (g : F → ℝ) (hg : ContDiff ℝ 2 g) (x : E)
    (hH : ∀ y v : F, 2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ g) y v v) :
    hessInv (fun y : E => g (e y)) x
      = (↑↑e.symm : F →ₗ[ℝ] E).comp ((hessInv g (e x)).comp (↑↑e : E →ₗ[ℝ] F)) := by
  have hinj : Function.Injective (hessOp g (e x)) := hessOp_injective g (e x) (hH (e x))
  have hH' : ∀ v : E, 2 * Real.pi * ‖v‖ ^ 2
      ≤ fderiv ℝ (fderiv ℝ (fun y : E => g (e y))) x v v := by
    intro v
    rw [fderiv_fderiv_comp_isometry e g hg x v v]
    have h1 : ‖e v‖ = ‖v‖ := e.norm_map v
    have h2 := hH (e x) (e v)
    rwa [h1] at h2
  have hinj' : Function.Injective (hessOp (fun y : E => g (e y)) x) :=
    hessOp_injective _ x hH'
  ext u
  have hval : hessOp (fun y : E => g (e y)) x (e.symm (hessInv g (e x) (e u))) = u := by
    rw [hessOp_comp_isometry e g hg x, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply]
    rw [show (↑↑e : E →L[ℝ] F) (e.symm (hessInv g (e x) (e u)))
          = e (e.symm (hessInv g (e x) (e u))) from rfl, e.apply_symm_apply]
    rw [show (↑↑e.symm : F →L[ℝ] E) ((hessOp g (e x)) ((hessInv g (e x)) (e u)))
          = e.symm ((hessOp g (e x)) ((hessInv g (e x)) (e u))) from rfl,
      hessInv_right g (e x) hinj (e u), e.symm_apply_apply]
  have h2 : hessInv (fun y : E => g (e y)) x u
      = hessInv (fun y : E => g (e y)) x
          (hessOp (fun y : E => g (e y)) x (e.symm (hessInv g (e x) (e u)))) := by
    rw [hval]
  rw [h2, hessInv_left _ _ hinj']
  rfl

/-- **Transport of the Brascamp–Lieb inequality along a linear isometry.** -/
theorem bl_transport (e : E ≃ₗᵢ[ℝ] F) (hF : BLon F) : BLon E := by
  intro f h hf hH hconv hgf hh hgh
  set g : F → ℝ := fun y => f (e.symm y) with hg_def
  set k : F → ℝ := fun y => h (e.symm y) with hk_def
  have hge : ∀ x : E, g (e x) = f x := fun x => by simp [hg_def]
  have hke : ∀ x : E, k (e x) = h x := fun x => by simp [hk_def]
  have hg_cd : ContDiff ℝ 2 g := by
    have h1 : ContDiff ℝ 2 (fun y : F => f (e.symm y)) := hf.comp (e.symm.contDiff)
    exact h1
  have hg_hess : ∀ y v : F, 2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ g) y v v := by
    intro y v
    have h1 : fderiv ℝ (fderiv ℝ g) y v v
        = fderiv ℝ (fderiv ℝ f) (e.symm y) (e.symm v) (e.symm v) := by
      have h2 : g = fun z : F => f (e.symm z) := hg_def
      rw [h2]
      exact fderiv_fderiv_comp_isometry e.symm f hf y v v
    rw [h1]
    have h3 : ‖e.symm v‖ = ‖v‖ := e.symm.norm_map v
    have h4 := hH (e.symm y) (e.symm v)
    rwa [h3] at h4
  have hg_conv : ConvexOn ℝ Set.univ (fun y : F => g y - Real.pi * ‖y‖ ^ 2) := by
    have h1 : g = fun z : F => f (e.symm z) := hg_def
    rw [h1]
    exact convexOn_comp_linearIsometryEquiv e.symm f hconv
  obtain ⟨C, hC0, N, hCN⟩ := hgf
  have hg_growth : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ y v : F,
      |fderiv ℝ g y v| ≤ C * (1 + ‖y‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ g) y v v| ≤ C * (1 + ‖y‖) ^ N * ‖v‖ ^ 2 := by
    refine ⟨C, hC0, N, fun y v => ⟨?_, ?_⟩⟩
    · have h1 : fderiv ℝ g y v = fderiv ℝ f (e.symm y) (e.symm v) := by
        have h1' := fderiv_comp_isometry_apply e.symm f y
          (hf.contDiffAt.differentiableAt (by norm_num)) v
        simpa [hg_def] using h1'
      rw [h1]
      have h3 := (hCN (e.symm y) (e.symm v)).1
      have h4 : (1 + ‖e.symm y‖) ^ N = (1 + ‖y‖) ^ N := by rw [e.symm.norm_map]
      have h5 : ‖e.symm v‖ = ‖v‖ := e.symm.norm_map v
      rwa [h4, h5] at h3
    · have h1 : fderiv ℝ (fderiv ℝ g) y v v
          = fderiv ℝ (fderiv ℝ f) (e.symm y) (e.symm v) (e.symm v) := by
        have h2 : g = fun z : F => f (e.symm z) := hg_def
        rw [h2]
        exact fderiv_fderiv_comp_isometry e.symm f hf y v v
      rw [h1]
      have h3 := (hCN (e.symm y) (e.symm v)).2
      have h4 : (1 + ‖e.symm y‖) ^ N = (1 + ‖y‖) ^ N := by rw [e.symm.norm_map]
      have h5 : ‖e.symm v‖ = ‖v‖ := e.symm.norm_map v
      rwa [h4, h5] at h3
  have hk_cd : ContDiff ℝ 1 k := by
    have h1 : ContDiff ℝ 1 (fun y : F => h (e.symm y)) := hh.comp (e.symm.contDiff)
    exact h1
  obtain ⟨C₂, hC₂0, N₂, hCN₂⟩ := hgh
  have hk_growth : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ y v : F,
      |k y| ≤ C * (1 + ‖y‖) ^ N ∧
      |fderiv ℝ k y v| ≤ C * (1 + ‖y‖) ^ N * ‖v‖ := by
    refine ⟨C₂, hC₂0, N₂, fun y v => ⟨?_, ?_⟩⟩
    · have h1 : k y = h (e.symm y) := by simp [hk_def]
      rw [h1]
      have h3 := (hCN₂ (e.symm y) (0 : E)).1
      have h4 : (1 + ‖e.symm y‖) ^ N₂ = (1 + ‖y‖) ^ N₂ := by rw [e.symm.norm_map]
      rwa [h4] at h3
    · have h1 : fderiv ℝ k y v = fderiv ℝ h (e.symm y) (e.symm v) := by
        have h1' := fderiv_comp_isometry_apply e.symm h y
          (hh.contDiffAt.differentiableAt (by norm_num)) v
        simpa [hk_def] using h1'
      rw [h1]
      have h3 := (hCN₂ (e.symm y) (e.symm v)).2
      have h4 : (1 + ‖e.symm y‖) ^ N₂ = (1 + ‖y‖) ^ N₂ := by rw [e.symm.norm_map]
      have h5 : ‖e.symm v‖ = ‖v‖ := e.symm.norm_map v
      rwa [h4, h5] at h3
  have key := hF g k hg_cd hg_hess hg_conv hg_growth hk_cd hk_growth
  have hone : (∫ y : F, k y ^ 2 * Real.exp (-(g y))) = ∫ x : E, h x ^ 2 * Real.exp (-(f x)) := by
    rw [← integral_comp_isometry e (fun y : F => k y ^ 2 * Real.exp (-(g y)))]
    simp only [hke, hge]
  have htwo : (∫ y : F, k y * Real.exp (-(g y))) = ∫ x : E, h x * Real.exp (-(f x)) := by
    rw [← integral_comp_isometry e (fun y : F => k y * Real.exp (-(g y)))]
    simp only [hke, hge]
  have hthree : (∫ y : F, Real.exp (-(g y))) = ∫ x : E, Real.exp (-(f x)) := by
    rw [← integral_comp_isometry e (fun y : F => Real.exp (-(g y)))]
    simp only [hge]
  have hfour : (∫ y : F, ⟪hessInv g y (grad k y), grad k y⟫_ℝ * Real.exp (-(g y)))
      = ∫ x : E, ⟪hessInv f x (grad h x), grad h x⟫_ℝ * Real.exp (-(f x)) := by
    rw [← integral_comp_isometry e
      (fun y : F => ⟪hessInv g y (grad k y), grad k y⟫_ℝ * Real.exp (-(g y)))]
    have hpt : ∀ x : E, (fun y : F => ⟪hessInv g y (grad k y), grad k y⟫_ℝ * Real.exp (-(g y))) (e x)
        = ⟪hessInv f x (grad h x), grad h x⟫_ℝ * Real.exp (-(f x)) := by
      intro x
      dsimp only
      have hgk : grad k (e x) = e (grad h x) := by
        have h1' := grad_comp_isometry e.symm h (e x)
          (hh.contDiffAt.differentiableAt (by norm_num))
        simpa [hk_def] using h1'
      have hhi : hessInv g (e x)
          = (↑↑e : E →ₗ[ℝ] F).comp ((hessInv f x).comp (↑↑e.symm : F →ₗ[ℝ] E)) := by
        have h1' := hessInv_comp_isometry e.symm f hf (e x) hH
        simpa [hg_def] using h1'
      have hinner : ⟪hessInv g (e x) (grad k (e x)), grad k (e x)⟫_ℝ
          = ⟪hessInv f x (grad h x), grad h x⟫_ℝ := by
        rw [hhi, hgk]
        simp only [LinearMap.comp_apply]
        rw [show (↑↑e.symm : F →ₗ[ℝ] E) (e (grad h x)) = grad h x from by
            rw [show (↑↑e.symm : F →ₗ[ℝ] E) (e (grad h x)) = e.symm (e (grad h x)) from rfl,
              e.symm_apply_apply],
          show (↑↑e : E →ₗ[ℝ] F) (hessInv f x (grad h x)) = e (hessInv f x (grad h x)) from rfl,
          e.inner_map_map]
      rw [hinner, hge x]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [hone, htwo, hthree, hfour] at key
  exact key

end IsometryTransport

/-
### Session notes (useful for continuing)

* The induction step of (P4) needs only the hypotheses `D²f ⪰ 2π·Id` and `f - π‖·‖²` convex for
  the *ambient* potential `f` on `G × ℝ`:  restricting to the slices `z ↦ f (z,y)` preserves both
  (`D²_z f` is the restriction of the quadratic form to `G × {0}`), so the induction hypothesis
  applies to the slice potentials without extra work.
* `U'' ≥ 2π` for the marginal potential `U = -log sliceMass g` follows from the convexity of
  `(z,y) ↦ g (z,y) - π‖z‖² - π y²`:  `U y - π y² = -log (∫ z, Real.exp (-(g (z,y) - π y²)))` and
  `(z,y) ↦ Real.exp (-(g (z,y) - π y²)) = Real.exp (-(π‖z‖² + (g (z,y) - π‖z‖² - π y²)))` is
  jointly log-concave, so its marginal is log-concave by
  `Commons.Analysis.Convex.logconcave_marginal_prod`; then apply
  `Commons.Analysis.Convex.deriv2_nonneg_of_convexOn_real`.
* For (P7) a convenient penalty is the *log-Laplace* penalty
  `φ_ε x = -Real.log (∫ y in A, Real.exp (-‖x - y‖² / ε ^ 2))` (well, with the appropriate
  normalisation):  it is `C^∞` (no mollification needed), convex (it is minus the log of a
  log-concave function, by Prékopa–Leindler), has `0 ⪯ D²φ_ε ⪯ ε⁻² • Id`, tends to `+∞` off `A`
  and to a constant on `A`, so the measures `Real.exp (-(π‖x‖² + φ_ε x)) dx`, normalised, converge
  to `1_A Real.exp (-π‖x‖²) dx`.
* The algebraic chain of (P4) was checked numerically (two random smooth convex potentials on `ℝ²`,
  quadrature):  the variance identity, the inequality (4.9) `Var ≤ ∫ (condVar + a²/U'')`, the
  `2×2` determinant inequality (ind2), the inequality (goal) and the final comparison with the
  Hessian form all hold.
* Delegating lemmas whose statements quantify over a `MeasureSpace` seems to fail in the checker
  (`invalid binder annotation, type is not a class instance` for `[MeasureSpace G]`, `Function
  expected at` for an explicit `(μ : Measure α)` argument); statements using the canonical volume
  of `ℝ`, `EuclideanSpace ℝ (Fin n)`, ... work fine.  So pieces phrased over a general measure space
  have to be proved locally instead of delegated.
-/

/-! ### Weighted variances and slices of a potential on a product

For the induction step of `brascamp_lieb_smooth` one slices `G × ℝ` at height `y` and uses the
distribution of `y` (with density `sliceMass g y`) together with the conditional distributions on
the slices (`condMean`, `condVar`).  This section records the corresponding definitions and the
Fubini decompositions. -/

section Slice

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [CompleteSpace G] [MeasureSpace G] [BorelSpace G] [SigmaFinite (volume : Measure G)]

/-- Weighted variance of `F` with respect to the weight `w`:
`∫ F ^ 2 * w - (∫ F * w) ^ 2 / (∫ w)`. -/
noncomputable def wVar {α : Type*} [MeasureSpace α] (w F : α → ℝ) : ℝ :=
  (∫ x, F x ^ 2 * w x) - (∫ x, F x * w x) ^ 2 / (∫ x, w x)

/-- Mass of the slice `{x.2 = y}` for the (unnormalised) measure `exp (-g (z,y)) dz`. -/
noncomputable def sliceMass (g : G × ℝ → ℝ) (y : ℝ) : ℝ := ∫ z, Real.exp (-(g (z, y)))

/-- Conditional mean of `h` on the slice at height `y`. -/
noncomputable def condMean (g h : G × ℝ → ℝ) (y : ℝ) : ℝ :=
  (∫ z, h (z, y) * Real.exp (-(g (z, y)))) / sliceMass g y

/-- Conditional variance of `h` on the slice at height `y`. -/
noncomputable def condVar (g h : G × ℝ → ℝ) (y : ℝ) : ℝ :=
  (∫ z, h (z, y) ^ 2 * Real.exp (-(g (z, y)))) / sliceMass g y - condMean g h y ^ 2

lemma condVar_mul (g h : G × ℝ → ℝ) {y : ℝ} (hW : sliceMass g y ≠ 0) :
    condVar g h y * sliceMass g y
      = (∫ z, h (z, y) ^ 2 * Real.exp (-(g (z, y))))
        - (∫ z, h (z, y) * Real.exp (-(g (z, y)))) ^ 2 / sliceMass g y := by
  unfold condVar condMean
  field_simp

lemma condMean_mul (g h : G × ℝ → ℝ) {y : ℝ} (hW : sliceMass g y ≠ 0) :
    condMean g h y * sliceMass g y = ∫ z, h (z, y) * Real.exp (-(g (z, y))) := by
  unfold condMean
  field_simp

lemma condMean_sq_mul (g h : G × ℝ → ℝ) {y : ℝ} (hW : sliceMass g y ≠ 0) :
    condMean g h y ^ 2 * sliceMass g y
      = (∫ z, h (z, y) * Real.exp (-(g (z, y)))) ^ 2 / sliceMass g y := by
  unfold condMean
  field_simp

/-- Fubini: the total mass is the integral of the slice masses. -/
lemma fubini_exp (g : G × ℝ → ℝ)
    (hint : Integrable (fun x : G × ℝ => Real.exp (-(g x)))) :
    ∫ x : G × ℝ, Real.exp (-(g x)) = ∫ y, sliceMass g y := by
  rw [Measure.volume_eq_prod G ℝ] at hint ⊢
  rw [integral_prod_symm _ hint]
  rfl

/-- Fubini: the second moment is the integral of the slice second moments. -/
lemma fubini_sq (g h : G × ℝ → ℝ)
    (hint : Integrable (fun x : G × ℝ => h x ^ 2 * Real.exp (-(g x)))) :
    ∫ x : G × ℝ, h x ^ 2 * Real.exp (-(g x))
      = ∫ y, ∫ z, h (z, y) ^ 2 * Real.exp (-(g (z, y))) := by
  rw [Measure.volume_eq_prod G ℝ] at hint ⊢
  rw [integral_prod_symm _ hint]

/-- Fubini: the first moment is the integral of the slice first moments. -/
lemma fubini_lin (g h : G × ℝ → ℝ)
    (hint : Integrable (fun x : G × ℝ => h x * Real.exp (-(g x)))) :
    ∫ x : G × ℝ, h x * Real.exp (-(g x))
      = ∫ y, ∫ z, h (z, y) * Real.exp (-(g (z, y))) := by
  rw [Measure.volume_eq_prod G ℝ] at hint ⊢
  rw [integral_prod_symm _ hint]



/-- Cauchy–Schwarz for weighted integrals over an arbitrary measure space. -/
lemma sq_integral_mul_le_integral_sq_mul_meas {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (a b w : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (ha : Integrable (fun x => a x ^ 2 * w x) μ)
    (hb : Integrable (fun x => b x ^ 2 * w x) μ) :
    (∫ x, a x * b x * w x ∂μ) ^ 2
      ≤ (∫ x, a x ^ 2 * w x ∂μ) * (∫ x, b x ^ 2 * w x ∂μ) := by
  by_cases hCint : Integrable (fun x => a x * b x * w x) μ
  · set A : ℝ := ∫ x, a x ^ 2 * w x ∂μ with hAdef
    set B : ℝ := ∫ x, b x ^ 2 * w x ∂μ with hBdef
    set C : ℝ := ∫ x, a x * b x * w x ∂μ with hCdef
    have hA0 : 0 ≤ A := by
      rw [hAdef]; exact integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hw x))
    have hB0 : 0 ≤ B := by
      rw [hBdef]; exact integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hw x))
    have hquad : ∀ t : ℝ, 0 ≤ A + 2 * t * C + t ^ 2 * B := by
      intro t
      have hg : Integrable (fun x => (2 * t) * (a x * b x * w x)) μ := hCint.const_mul (2 * t)
      have hh : Integrable (fun x => t ^ 2 * (b x ^ 2 * w x)) μ := hb.const_mul (t ^ 2)
      have hcongr : (fun x => (a x + t * b x) ^ 2 * w x)
          =ᵐ[μ] fun x => a x ^ 2 * w x + (2 * t) * (a x * b x * w x)
            + t ^ 2 * (b x ^ 2 * w x) := by
        filter_upwards with x
        ring
      have hval : (∫ x, (a x + t * b x) ^ 2 * w x ∂μ) = A + 2 * t * C + t ^ 2 * B := by
        rw [integral_congr_ae hcongr]
        rw [show (∫ x, a x ^ 2 * w x + (2 * t) * (a x * b x * w x)
              + t ^ 2 * (b x ^ 2 * w x) ∂μ)
            = ∫ x, ((fun y => a y ^ 2 * w y) + (fun y => (2 * t) * (a y * b y * w y))) x
                + (fun y => t ^ 2 * (b y ^ 2 * w y)) x ∂μ from rfl]
        rw [integral_add (ha.add hg) hh, integral_add' ha hg]
        rw [integral_const_mul, integral_const_mul, ← hAdef, ← hCdef, ← hBdef]
      have hnonneg : 0 ≤ ∫ x, (a x + t * b x) ^ 2 * w x ∂μ :=
        integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hw x))
      rw [hval] at hnonneg
      exact hnonneg
    have hmain : C ^ 2 ≤ A * B := by
      by_cases hBzero : B = 0
      · have hC0 : C = 0 := by
          by_contra hCne
          have h2C : (2 : ℝ) * C ≠ 0 := mul_ne_zero (by norm_num) hCne
          have h := hquad (-(A + 1) / (2 * C))
          have heq : A + 2 * (-(A + 1) / (2 * C)) * C + (-(A + 1) / (2 * C)) ^ 2 * B = -1 := by
            rw [hBzero]
            field_simp
            ring
          linarith [h, heq]
        rw [hC0, hBzero]
        norm_num
      · have hBpos : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hBzero)
        have h := hquad (-(C / B))
        have heq : A + 2 * (-(C / B)) * C + (-(C / B)) ^ 2 * B = A - C ^ 2 / B := by
          field_simp
          ring
        have hstep : 0 ≤ A - C ^ 2 / B := by linarith [h, heq]
        have h3 : C ^ 2 / B ≤ A := by linarith [hstep]
        exact (div_le_iff₀ hBpos).mp h3
    exact hmain
  · rw [integral_undef hCint]
    have hA0 : 0 ≤ ∫ x, a x ^ 2 * w x ∂μ :=
      integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hw x))
    have hB0 : 0 ≤ ∫ x, b x ^ 2 * w x ∂μ :=
      integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hw x))
    have hmul : 0 ≤ (∫ x, a x ^ 2 * w x ∂μ) * (∫ x, b x ^ 2 * w x ∂μ) := mul_nonneg hA0 hB0
    simpa using hmul

/-- Conditional covariance of `h` and `k` on the slice at height `y`. -/
noncomputable def condCov (g h k : G × ℝ → ℝ) (y : ℝ) : ℝ :=
  (∫ z, h (z, y) * k (z, y) * Real.exp (-(g (z, y)))) / sliceMass g y
    - condMean g h y * condMean g k y

lemma condCov_mul (g h k : G × ℝ → ℝ) {y : ℝ} (hW : sliceMass g y ≠ 0) :
    condCov g h k y * sliceMass g y
      = (∫ z, h (z, y) * k (z, y) * Real.exp (-(g (z, y))))
        - (∫ z, h (z, y) * Real.exp (-(g (z, y))))
          * (∫ z, k (z, y) * Real.exp (-(g (z, y)))) / sliceMass g y := by
  unfold condCov condMean
  field_simp

lemma condCov_self (g h : G × ℝ → ℝ) (y : ℝ) : condCov g h h y = condVar g h y := by
  unfold condCov condVar
  rw [show (fun z => h (z, y) * h (z, y) * Real.exp (-(g (z, y))))
        = (fun z => h (z, y) ^ 2 * Real.exp (-(g (z, y)))) from funext (fun z => by ring)]
  ring

lemma condCov_comm (g h k : G × ℝ → ℝ) (y : ℝ) : condCov g h k y = condCov g k h y := by
  unfold condCov
  rw [show (fun z => h (z, y) * k (z, y) * Real.exp (-(g (z, y))))
        = (fun z => k (z, y) * h (z, y) * Real.exp (-(g (z, y)))) from funext (fun z => by ring)]
  ring

/-- A.e.-measurability of the "left" partial integral of an a.e.-strongly-measurable function. -/
lemma aestronglyMeasurable_integral_prod_left' {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] {f : α × β → ℝ}
    (hf : AEStronglyMeasurable f (μ.prod ν)) :
    AEMeasurable (fun y => ∫ x, f (x, y) ∂μ) ν := by
  have hmap : Measure.map (Prod.swap : β × α → α × β) (ν.prod μ) = μ.prod ν :=
    Measure.prod_swap
  have hf' := hf
  rw [← hmap] at hf'
  have h2 : AEStronglyMeasurable (fun p : β × α => f (p.2, p.1)) (ν.prod μ) :=
    hf'.comp_measurable measurable_swap
  exact (h2.integral_prod_right' (μ := ν) (ν := μ)).aemeasurable

/-- **Law of total variance** for the product decomposition `G × ℝ` (un-normalised form). -/
lemma wVar_prod_eq (g h : G × ℝ → ℝ) (hW : ∀ y, 0 < sliceMass g y)
    (hintE : Integrable (fun x : G × ℝ => Real.exp (-(g x))))
    (hint2 : Integrable (fun x : G × ℝ => h x ^ 2 * Real.exp (-(g x))))
    (hint1 : Integrable (fun x : G × ℝ => h x * Real.exp (-(g x))))
    (hsl2 : ∀ y, Integrable (fun z => h (z, y) ^ 2 * Real.exp (-(g (z, y)))))
    (hslE : ∀ y, Integrable (fun z => Real.exp (-(g (z, y))))) :
    wVar (fun x => Real.exp (-(g x))) h
      = (∫ y, condVar g h y * sliceMass g y)
        + ((∫ y, condMean g h y ^ 2 * sliceMass g y)
            - (∫ y, condMean g h y * sliceMass g y) ^ 2 / (∫ y, sliceMass g y)) := by
  set A : ℝ → ℝ := fun y => ∫ z, h (z, y) ^ 2 * Real.exp (-(g (z, y))) with hAdef
  set B : ℝ → ℝ := fun y => ∫ z, h (z, y) * Real.exp (-(g (z, y))) with hBdef
  have hWne : ∀ y, sliceMass g y ≠ 0 := fun y => ne_of_gt (hW y)
  have hAint : Integrable A := by
    rw [hAdef]
    have h2 := hint2
    rw [Measure.volume_eq_prod G ℝ] at h2
    exact h2.integral_prod_right
  have hmB : AEMeasurable B := by
    rw [hBdef]
    have h1 := hint1
    rw [Measure.volume_eq_prod G ℝ] at h1
    exact aestronglyMeasurable_integral_prod_left' h1.aestronglyMeasurable
  have hmW : AEMeasurable (sliceMass g) := by
    have h1 := hintE
    rw [Measure.volume_eq_prod G ℝ] at h1
    exact aestronglyMeasurable_integral_prod_left' h1.aestronglyMeasurable
  have hDint : Integrable (fun y => B y ^ 2 / sliceMass g y) := by
    have hmD : AEMeasurable (fun y => B y ^ 2 / sliceMass g y) :=
      (hmB.pow aemeasurable_const).div hmW
    refine Integrable.mono' hAint hmD.aestronglyMeasurable ?_
    filter_upwards with y
    have hbE : Integrable (fun z : G => (1 : ℝ) ^ 2 * Real.exp (-(g (z, y)))) := by
      simpa using hslE y
    have hcs := sq_integral_mul_le_integral_sq_mul_meas (fun z : G => h (z, y)) (fun _ => (1 : ℝ))
      (fun z => Real.exp (-(g (z, y)))) (fun z => (Real.exp_pos _).le) (hsl2 y) hbE
    have hcs' : B y ^ 2 ≤ A y * sliceMass g y := by
      simpa only [hAdef, hBdef, sliceMass, mul_one, one_mul, one_pow, Pi.one_apply] using hcs
    have hWy := hW y
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hWy.le), div_le_iff₀ hWy]
    linarith [hcs']
  have e1 : (∫ y, condMean g h y * sliceMass g y) = ∫ y, B y := by
    refine integral_congr_ae ?_
    filter_upwards with y
    rw [condMean_mul g h (hWne y)]
  have e2 : (∫ y, condMean g h y ^ 2 * sliceMass g y) = ∫ y, B y ^ 2 / sliceMass g y := by
    refine integral_congr_ae ?_
    filter_upwards with y
    rw [condMean_sq_mul g h (hWne y)]
  have e3 : (∫ y, condVar g h y * sliceMass g y)
      = ∫ y, (A y - B y ^ 2 / sliceMass g y) := by
    refine integral_congr_ae ?_
    filter_upwards with y
    rw [condVar_mul g h (hWne y)]
  have hvar : wVar (fun x => Real.exp (-(g x))) h
      = (∫ x, h x ^ 2 * Real.exp (-(g x)))
        - (∫ x, h x * Real.exp (-(g x))) ^ 2 / (∫ x, Real.exp (-(g x))) := by
    rfl
  rw [hvar, fubini_exp g hintE, fubini_sq g h hint2, fubini_lin g h hint1, e1, e2, e3,
    integral_sub hAint hDint]
  ring


/-- The final algebraic combination step of the Brascamp–Lieb dimensional induction
(Brascamp–Lieb 1976, passage from (4.9) to (4.10), as reproduced in Carlen–Cordero-Erausquin–Lieb,
arXiv:1106.0709, appendix). -/
lemma bl_combine {α₁ b β a α : ℝ} (hβ : 0 < β) (hβα : β < α)
    (hquad : ∀ t : ℝ, 0 ≤ α₁ + 2 * b * t + β * t ^ 2) :
    a ^ 2 / α - (a - b) ^ 2 / (α - β) ≤ α₁ := by
  have hmin : 0 ≤ α₁ - b ^ 2 / β := by
    have h := hquad (-b / β)
    have heq : α₁ + 2 * b * (-b / β) + β * (-b / β) ^ 2 = α₁ - b ^ 2 / β := by
      field_simp
      ring
    linarith [h, heq]
  have h1 : b ^ 2 ≤ α₁ * β := by
    have h := sub_nonneg.mp hmin
    rw [div_le_iff₀ hβ] at h
    linarith
  have h2 := Commons.Analysis.Inequalities.sq_div_sub_sq_div_le (a := a) (b := b)
    (α := α) (β := β) hβ hβα
  have h4 : b ^ 2 / β ≤ α₁ := by rw [div_le_iff₀ hβ]; linarith
  linarith

/-- Degenerate form of `bl_combine` for `β = 0`. -/
lemma bl_combine_zero {α₁ b a α : ℝ} (hα : 0 < α)
    (hquad : ∀ t : ℝ, 0 ≤ α₁ + 2 * b * t) :
    a ^ 2 / α - (a - b) ^ 2 / (α - 0) ≤ α₁ := by
  have hb : b = 0 := by
    by_contra hb
    have h := hquad (-(α₁ + 1) / (2 * b))
    have h2 : (2 * b) * (-(α₁ + 1) / (2 * b)) = -(α₁ + 1) := by
      field_simp
    linarith [h, h2]
  subst hb
  have h0 : 0 ≤ α₁ := by simpa using hquad 0
  have h1 : a ^ 2 / α - (a - 0) ^ 2 / (α - 0) = 0 := by ring
  linarith

/-- Conditional Cauchy–Schwarz on a slice: `⟨φ⟩² / ⟨s⟩ ≤ ⟨φ²/s⟩` for `s > 0`. -/
lemma condMean_sq_div_le (g φ s : G × ℝ → ℝ) (y : ℝ)
    (hW : 0 < sliceMass g y) (hs : ∀ z, 0 < s (z, y))
    (hsI : Integrable (fun z => s (z, y) * Real.exp (-(g (z, y)))))
    (htI : Integrable (fun z => φ (z, y) ^ 2 / s (z, y) * Real.exp (-(g (z, y))))) :
    condMean g φ y ^ 2 / condMean g s y
      ≤ (∫ z, φ (z, y) ^ 2 / s (z, y) * Real.exp (-(g (z, y)))) / sliceMass g y := by
  have ha : Integrable (fun z : G => (Real.sqrt (s (z, y))) ^ 2 * Real.exp (-(g (z, y)))) := by
    refine hsI.congr ?_
    filter_upwards with z
    rw [Real.sq_sqrt (hs z).le]
  have hb : Integrable (fun z : G => (φ (z, y) / Real.sqrt (s (z, y))) ^ 2
      * Real.exp (-(g (z, y)))) := by
    refine htI.congr ?_
    filter_upwards with z
    rw [div_pow, Real.sq_sqrt (hs z).le]
  have hcs := sq_integral_mul_le_integral_sq_mul_meas
    (fun z : G => Real.sqrt (s (z, y))) (fun z : G => φ (z, y) / Real.sqrt (s (z, y)))
    (fun z => Real.exp (-(g (z, y)))) (fun z => (Real.exp_pos _).le) ha hb
  have h1 : (∫ z, Real.sqrt (s (z, y)) * (φ (z, y) / Real.sqrt (s (z, y)))
      * Real.exp (-(g (z, y)))) = ∫ z, φ (z, y) * Real.exp (-(g (z, y))) := by
    refine integral_congr_ae ?_
    filter_upwards with z
    have hz : Real.sqrt (s (z, y)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hs z))
    field_simp
  have h2 : (∫ z, (Real.sqrt (s (z, y))) ^ 2 * Real.exp (-(g (z, y))))
      = ∫ z, s (z, y) * Real.exp (-(g (z, y))) := by
    refine integral_congr_ae ?_
    filter_upwards with z
    rw [Real.sq_sqrt (hs z).le]
  have h3 : (∫ z, (φ (z, y) / Real.sqrt (s (z, y))) ^ 2 * Real.exp (-(g (z, y))))
      = ∫ z, φ (z, y) ^ 2 / s (z, y) * Real.exp (-(g (z, y))) := by
    refine integral_congr_ae ?_
    filter_upwards with z
    rw [div_pow, Real.sq_sqrt (hs z).le]
  rw [h1, h2, h3] at hcs
  rw [condMean, condMean]
  by_cases hS0 : (∫ z, s (z, y) * Real.exp (-(g (z, y)))) = 0
  · have hden : (∫ z, s (z, y) * Real.exp (-(g (z, y)))) / sliceMass g y = 0 := by
      rw [hS0, zero_div]
    rw [hden, div_zero]
    have hT0 : 0 ≤ ∫ z, φ (z, y) ^ 2 / s (z, y) * Real.exp (-(g (z, y))) :=
      integral_nonneg fun z =>
        mul_nonneg (div_nonneg (sq_nonneg _) (hs z).le) (Real.exp_pos _).le
    exact div_nonneg hT0 hW.le
  · have hSle : 0 ≤ ∫ z, s (z, y) * Real.exp (-(g (z, y))) :=
      integral_nonneg fun z => mul_nonneg (hs z).le (Real.exp_pos _).le
    have hSpos : 0 < ∫ z, s (z, y) * Real.exp (-(g (z, y))) :=
      lt_of_le_of_ne hSle (Ne.symm hS0)
    have hW' : ((∫ z, φ (z, y) * Real.exp (-(g (z, y)))) / sliceMass g y) ^ 2
        / ((∫ z, s (z, y) * Real.exp (-(g (z, y)))) / sliceMass g y)
        = (∫ z, φ (z, y) * Real.exp (-(g (z, y)))) ^ 2
          / ((∫ z, s (z, y) * Real.exp (-(g (z, y)))) * sliceMass g y) := by
      have h1 : sliceMass g y ≠ 0 := ne_of_gt hW
      have h2 : (∫ z, s (z, y) * Real.exp (-(g (z, y)))) ≠ 0 := hS0
      field_simp
    rw [hW']
    rw [div_le_iff₀ (mul_pos hSpos hW)]
    have hTS : (∫ z, φ (z, y) ^ 2 / s (z, y) * Real.exp (-(g (z, y)))) / sliceMass g y
        * ((∫ z, s (z, y) * Real.exp (-(g (z, y)))) * sliceMass g y)
        = (∫ z, φ (z, y) ^ 2 / s (z, y) * Real.exp (-(g (z, y))))
          * (∫ z, s (z, y) * Real.exp (-(g (z, y)))) := by
      have h1 : sliceMass g y ≠ 0 := ne_of_gt hW
      field_simp
    rw [hTS]
    linarith [hcs]
end Slice
section Product

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [CompleteSpace G] [MeasurableSpace G] [BorelSpace G]

/-- The product normed-space structure on `G × ℝ` (the sup norm), pinned down so that
type-class search does not get lost in the two competing paths to `NormedSpace ℝ (G × ℝ)`. -/
noncomputable local instance instNormedSpaceProd : NormedSpace ℝ (G × ℝ) := Prod.normedSpace
/-- Pinning down the normed-space structure on the dual of `G × ℝ`. -/
noncomputable local instance instNormedSpaceDual : NormedSpace ℝ ((G × ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
/-- Pinning down the seminormed-group structure on the space of second derivatives. -/
noncomputable local instance instSeminormedCLM :
    SeminormedAddCommGroup ((G × ℝ) →L[ℝ] ((G × ℝ) →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

/-- The partial derivative of `F` in the second (real) variable. -/
noncomputable def dY (F : G × ℝ → ℝ) (p : G × ℝ) : ℝ := fderiv ℝ F p (0, 1)

/-- The second partial derivative of `F` in the second (real) variable. -/
noncomputable def d2Y (F : G × ℝ → ℝ) (p : G × ℝ) : ℝ := fderiv ℝ (dY F) p (0, 1)

/-- The line `t ↦ F (z, t)`. -/
noncomputable def line (F : G × ℝ → ℝ) (z : G) : ℝ → ℝ := fun t => F (z, t)

lemma dY_eq_deriv (F : G × ℝ → ℝ) (z : G) (y : ℝ) (hF : DifferentiableAt ℝ F (z, y)) :
    dY F (z, y) = deriv (line F z) y := by
  change fderiv ℝ F (z, y) (0, 1) = deriv (line F z) y
  have hc : HasFDerivAt (fun t : ℝ => (z, t))
      ((0 : ℝ →L[ℝ] G).prod (1 : ℝ →L[ℝ] ℝ)) y := by
    have h1 : HasFDerivAt (fun _ : ℝ => z) (0 : ℝ →L[ℝ] G) y := hasFDerivAt_const z y
    have h2 : HasFDerivAt (fun t : ℝ => t) (1 : ℝ →L[ℝ] ℝ) y := hasFDerivAt_id y
    simpa using h1.prodMk h2
  have hcomp := hF.hasFDerivAt.comp_hasDerivAt y hc.hasDerivAt
  have h2 : fderiv ℝ F (z, y) (0, 1)
      = fderiv ℝ F (z, y) (((0 : ℝ →L[ℝ] G).prod (1 : ℝ →L[ℝ] ℝ)) 1) := by
    simp [ContinuousLinearMap.prod_apply]
  have hcomp' : deriv (line F z) y
      = fderiv ℝ F (z, y) (((0 : ℝ →L[ℝ] G).prod (1 : ℝ →L[ℝ] ℝ)) 1) := by
    show deriv (fun t : ℝ => F (z, t)) y = _
    simpa only [Function.comp_def] using hcomp.deriv
  rw [h2, hcomp']

lemma contDiff_dY (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) : ContDiff ℝ 1 (dY F) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ F) := (contDiff_succ_iff_fderiv.mp hF).2.2
  have h2 : ContDiff ℝ 1 (fun _ : G × ℝ => ((0, 1) : G × ℝ)) := contDiff_const
  have h3 := h1.clm_apply h2
  change ContDiff ℝ 1 fun x : G × ℝ => fderiv ℝ F x (0, 1)
  exact h3

/-- A Gaussian-type growth condition on `G × ℝ`: both `Φ` and its partial `y`-derivative are
dominated by `C (1 + ‖z‖ + |y|)^N exp (-π ‖z‖²/2)`. -/
def SliceGrowth (Φ : G × ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ z : G, ∀ y : ℝ,
    ‖Φ (z, y)‖ ≤ C * (1 + ‖z‖ + |y|) ^ N * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) ∧
    ‖fderiv ℝ Φ (z, y) (0, 1)‖ ≤ C * (1 + ‖z‖ + |y|) ^ N
      * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)

lemma pow_one_add_norm_add_abs_le (z : G) (y : ℝ) (N : ℕ) :
    (1 + ‖z‖ + |y|) ^ N ≤ (1 + |y| + 1) ^ N * (1 + ‖z‖) ^ N := by
  have h1 : 1 + ‖z‖ + |y| ≤ (1 + |y|) * (1 + ‖z‖) := by
    nlinarith [abs_nonneg y, norm_nonneg z]
  have h2 : (0 : ℝ) ≤ 1 + |y| := by positivity
  calc (1 + ‖z‖ + |y|) ^ N ≤ ((1 + |y|) * (1 + ‖z‖)) ^ N :=
        pow_le_pow_left₀ (by positivity) h1 N
    _ = (1 + |y|) ^ N * (1 + ‖z‖) ^ N := by rw [mul_pow]
    _ ≤ (1 + |y| + 1) ^ N * (1 + ‖z‖) ^ N := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact pow_le_pow_left₀ h2 (by linarith) N

lemma integrable_gauss_poly (B : ℝ) (N : ℕ) :
    Integrable (fun z : G => B * (1 + ‖z‖) ^ N * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  set Kc : ℝ := Real.exp ((N : ℝ) ^ 2 / Real.pi) with hKdef
  have hbase : Integrable (fun z : G => Kc * Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2)) :=
    (Commons.Measure.Integral.integrable_rexp_neg_mul_sq_norm (Real.pi / 4)
      (by positivity)).const_mul Kc
  refine Integrable.mono' (hbase.const_mul |B|) ?_ ?_
  · have hcont : Continuous (fun z : G => B * (1 + ‖z‖) ^ N
        * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)) := by fun_prop
    exact Continuous.aestronglyMeasurable hcont
  · filter_upwards with z
    have h1 : (1 + ‖z‖) ^ N ≤ Kc * Real.exp ((Real.pi / 4) * ‖z‖ ^ 2) := by
      have h2 : 1 + ‖z‖ ≤ Real.exp ‖z‖ := by
        simpa [add_comm] using Real.add_one_le_exp ‖z‖
      have h3 : (1 + ‖z‖) ^ N ≤ (Real.exp ‖z‖) ^ N :=
        pow_le_pow_left₀ (by positivity) h2 N
      have h4 : (Real.exp ‖z‖) ^ N = Real.exp ((N : ℝ) * ‖z‖) := by
        rw [← Real.exp_nat_mul]
      have h5 : (N : ℝ) * ‖z‖ ≤ (N : ℝ) ^ 2 / Real.pi + (Real.pi / 4) * ‖z‖ ^ 2 := by
        have h6 : (Real.pi / 4) * (‖z‖ - 2 * (N : ℝ) / Real.pi) ^ 2
            = (Real.pi / 4) * ‖z‖ ^ 2 - (N : ℝ) * ‖z‖ + (N : ℝ) ^ 2 / Real.pi := by
          field_simp
          ring
        have h7 := mul_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 4)
          (sq_nonneg (‖z‖ - 2 * (N : ℝ) / Real.pi))
        rw [h6] at h7
        linarith
      calc (1 + ‖z‖) ^ N ≤ Real.exp ((N : ℝ) * ‖z‖) := by rw [← h4]; exact h3
        _ ≤ Real.exp ((N : ℝ) ^ 2 / Real.pi + (Real.pi / 4) * ‖z‖ ^ 2) :=
            Real.exp_le_exp.mpr h5
        _ = Kc * Real.exp ((Real.pi / 4) * ‖z‖ ^ 2) := by rw [Real.exp_add, hKdef]
    have hexp : Real.exp ((Real.pi / 4) * ‖z‖ ^ 2) * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)
        = Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring_nf
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (pow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖z‖) N),
      abs_of_nonneg (Real.exp_pos _).le]
    calc |B| * (1 + ‖z‖) ^ N * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)
        ≤ |B| * (Kc * Real.exp ((Real.pi / 4) * ‖z‖ ^ 2))
            * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left h1 (abs_nonneg B)
      _ = |B| * (Kc * Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2)) := by
          rw [show |B| * (Kc * Real.exp ((Real.pi / 4) * ‖z‖ ^ 2))
                * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)
              = |B| * (Kc * (Real.exp ((Real.pi / 4) * ‖z‖ ^ 2)
                * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2))) from by ring, hexp]

lemma hasDerivAt_integral_slice_of_growth (Φ : G × ℝ → ℝ) (hΦ : ContDiff ℝ 1 Φ)
    (hg : SliceGrowth Φ) (y₀ : ℝ) :
    HasDerivAt (fun y => ∫ z, Φ (z, y)) (∫ z, fderiv ℝ Φ (z, y₀) (0, 1)) y₀ := by
  obtain ⟨C, hC0, N, hC⟩ := hg
  set bound : G → ℝ := fun z => C * (3 + |y₀|) ^ N * (1 + ‖z‖) ^ N
    * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) with hbounddef
  have hbound_int : Integrable bound := by
    rw [hbounddef]
    exact integrable_gauss_poly (C * (3 + |y₀|) ^ N) N
  have hmono : ∀ z : G, C * (1 + ‖z‖ + |y₀|) ^ N
      * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) ≤ bound z := by
    intro z
    have h2b : (1 + ‖z‖ + |y₀|) ^ N ≤ (3 + |y₀|) ^ N * (1 + ‖z‖) ^ N := by
      calc (1 + ‖z‖ + |y₀|) ^ N ≤ (1 + |y₀| + 1) ^ N * (1 + ‖z‖) ^ N :=
            pow_one_add_norm_add_abs_le (G := G) z y₀ N
        _ ≤ (3 + |y₀|) ^ N * (1 + ‖z‖) ^ N := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact pow_le_pow_left₀ (by positivity) (by linarith) N
    rw [hbounddef]
    calc C * (1 + ‖z‖ + |y₀|) ^ N * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)
        ≤ C * ((3 + |y₀|) ^ N * (1 + ‖z‖) ^ N)
              * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left h2b hC0
      _ = C * (3 + |y₀|) ^ N * (1 + ‖z‖) ^ N
              * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := by ring
  refine Commons.Analysis.Calculus.hasDerivAt_integral_slice Φ y₀ bound hΦ hbound_int ?_ ?_
  · refine Integrable.mono' hbound_int ?_ ?_
    · exact Continuous.aestronglyMeasurable
        (hΦ.continuous.comp (continuous_id.prodMk continuous_const))
    · filter_upwards with z
      exact le_trans (hC z y₀).1 (hmono z)
  · intro z y hy
    have hy1 : |y| ≤ |y₀| + 1 := by
      rw [abs_le]
      exact ⟨by linarith [hy.1, neg_le_abs y₀], by linarith [hy.2, le_abs_self y₀]⟩
    have h3 : (1 + ‖z‖ + |y|) ^ N ≤ (3 + |y₀|) ^ N * (1 + ‖z‖) ^ N := by
      calc (1 + ‖z‖ + |y|) ^ N ≤ (1 + |y| + 1) ^ N * (1 + ‖z‖) ^ N :=
            pow_one_add_norm_add_abs_le (G := G) z y N
        _ ≤ (3 + |y₀|) ^ N * (1 + ‖z‖) ^ N := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact pow_le_pow_left₀ (by positivity) (by linarith) N
    rw [show bound z = C * (3 + |y₀|) ^ N * (1 + ‖z‖) ^ N
      * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) from by rw [hbounddef]]
    calc ‖fderiv ℝ Φ (z, y) (0, 1)‖
        ≤ C * (1 + ‖z‖ + |y|) ^ N * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := (hC z y).2
      _ ≤ C * ((3 + |y₀|) ^ N * (1 + ‖z‖) ^ N)
            * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left h3 hC0
      _ = C * (3 + |y₀|) ^ N * (1 + ‖z‖) ^ N
            * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := by ring

lemma continuousAt_integral_slice_of_growth (Φ : G × ℝ → ℝ) (hΦ : Continuous Φ)
    (hg : SliceGrowth Φ) (y₀ : ℝ) :
    ContinuousAt (fun y => ∫ z, Φ (z, y)) y₀ := by
  obtain ⟨C, hC0, N, hC⟩ := hg
  set bound : G → ℝ := fun z => C * (3 + |y₀|) ^ N * (1 + ‖z‖) ^ N
    * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) with hbounddef
  have hbound_int : Integrable bound := by
    rw [hbounddef]
    exact integrable_gauss_poly (C * (3 + |y₀|) ^ N) N
  have hmono : ∀ z : G, C * (1 + ‖z‖ + |y₀|) ^ N
      * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) ≤ bound z := by
    intro z
    have h2b : (1 + ‖z‖ + |y₀|) ^ N ≤ (3 + |y₀|) ^ N * (1 + ‖z‖) ^ N := by
      calc (1 + ‖z‖ + |y₀|) ^ N ≤ (1 + |y₀| + 1) ^ N * (1 + ‖z‖) ^ N :=
            pow_one_add_norm_add_abs_le (G := G) z y₀ N
        _ ≤ (3 + |y₀|) ^ N * (1 + ‖z‖) ^ N := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact pow_le_pow_left₀ (by positivity) (by linarith) N
    rw [hbounddef]
    calc C * (1 + ‖z‖ + |y₀|) ^ N * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)
        ≤ C * ((3 + |y₀|) ^ N * (1 + ‖z‖) ^ N)
              * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left h2b hC0
      _ = C * (3 + |y₀|) ^ N * (1 + ‖z‖) ^ N
              * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := by ring
  refine Commons.Analysis.Calculus.continuousAt_integral_slice Φ y₀ bound hΦ hbound_int ?_ ?_
  · refine Integrable.mono' hbound_int ?_ ?_
    · exact Continuous.aestronglyMeasurable
        (hΦ.comp (continuous_id.prodMk continuous_const))
    · filter_upwards with z
      exact le_trans (hC z y₀).1 (hmono z)
  · intro z y hy
    rw [abs_lt] at hy
    have hy1 : |y| ≤ |y₀| + 1 := by
      rw [abs_le]
      exact ⟨by linarith [hy.1, neg_le_abs y₀], by linarith [hy.2, le_abs_self y₀]⟩
    have h3 : (1 + ‖z‖ + |y|) ^ N ≤ (3 + |y₀|) ^ N * (1 + ‖z‖) ^ N := by
      calc (1 + ‖z‖ + |y|) ^ N ≤ (1 + |y| + 1) ^ N * (1 + ‖z‖) ^ N :=
            pow_one_add_norm_add_abs_le (G := G) z y N
        _ ≤ (3 + |y₀|) ^ N * (1 + ‖z‖) ^ N := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact pow_le_pow_left₀ (by positivity) (by linarith) N
    rw [show bound z = C * (3 + |y₀|) ^ N * (1 + ‖z‖) ^ N
      * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) from by rw [hbounddef]]
    calc ‖Φ (z, y)‖
        ≤ C * (1 + ‖z‖ + |y|) ^ N * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := (hC z y).1
      _ ≤ C * ((3 + |y₀|) ^ N * (1 + ‖z‖) ^ N)
            * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left h3 hC0
      _ = C * (3 + |y₀|) ^ N * (1 + ‖z‖) ^ N
            * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := by ring


lemma dY_neg (A : G × ℝ → ℝ) (z : G) (y : ℝ) (hA : DifferentiableAt ℝ A (z, y)) :
    dY (fun p => -(A p)) (z, y) = -(dY A (z, y)) := by
  show fderiv ℝ (-A) (z, y) (0, 1) = -(fderiv ℝ A (z, y) (0, 1))
  rw [hA.hasFDerivAt.neg.fderiv, ContinuousLinearMap.neg_apply]

lemma dY_mul (A B : G × ℝ → ℝ) (z : G) (y : ℝ)
    (hA : DifferentiableAt ℝ A (z, y)) (hB : DifferentiableAt ℝ B (z, y)) :
    dY (fun p => A p * B p) (z, y) = dY A (z, y) * B (z, y) + A (z, y) * dY B (z, y) := by
  show fderiv ℝ (A * B) (z, y) (0, 1) = dY A (z, y) * B (z, y) + A (z, y) * dY B (z, y)
  rw [(hA.hasFDerivAt.mul hB.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, dY]
  ring

lemma dY_exp_neg (F : G × ℝ → ℝ) (z : G) (y : ℝ) (hF : DifferentiableAt ℝ F (z, y)) :
    dY (fun p => Real.exp (-(F p))) (z, y) = -Real.exp (-(F (z, y))) * dY F (z, y) := by
  have hexp := (hF.hasFDerivAt.neg).exp
  show fderiv ℝ (fun x : G × ℝ => rexp ((-F) x)) (z, y) (0, 1)
      = -rexp (-F (z, y)) * fderiv ℝ F (z, y) (0, 1)
  rw [hexp.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, smul_eq_mul,
    Pi.neg_apply]
  ring

lemma d2Y_exp_neg (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (z : G) (y : ℝ) :
    d2Y (fun p => Real.exp (-(F p))) (z, y)
      = Real.exp (-(F (z, y))) * (dY F (z, y)) ^ 2
        - Real.exp (-(F (z, y))) * d2Y F (z, y) := by
  have hd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have h1 : dY (fun p => Real.exp (-(F p))) = fun p => -Real.exp (-(F p)) * dY F p := by
    funext p
    exact dY_exp_neg F p.1 p.2 (hd p)
  have hdY : Differentiable ℝ (dY F) := (contDiff_dY F hF).differentiable (by norm_num)
  have hde : Differentiable ℝ (fun p : G × ℝ => Real.exp (-(F p))) := fun p => (hd p).neg.exp
  show dY (dY (fun p => Real.exp (-(F p)))) (z, y) = _
  rw [h1, dY_mul (fun p => -Real.exp (-(F p))) (dY F) z y
    (hde (z, y)).neg (hdY (z, y))]
  rw [show dY (dY F) (z, y) = d2Y F (z, y) from rfl]
  rw [dY_neg (fun p => Real.exp (-(F p))) z y (hde (z, y)),
    dY_exp_neg F z y (hd (z, y))]
  ring





/-- Growth hypotheses on the potential `F : G × ℝ → ℝ`: polynomial growth of the partial
`y`-derivatives of order one and two, and a quadratic lower bound with rate `π/2`. -/
def PotGrowth (F : G × ℝ → ℝ) : Prop :=
  (∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p : G × ℝ,
      |dY F p| ≤ C * (1 + ‖p‖) ^ N ∧ |d2Y F p| ≤ C * (1 + ‖p‖) ^ N)
  ∧ (∃ D : ℝ, ∀ p : G × ℝ, (Real.pi / 2) * ‖p‖ ^ 2 - D ≤ F p)

lemma norm_pair_le (z : G) (y : ℝ) : ‖(z, y)‖ ≤ ‖z‖ + |y| := by
  rw [Prod.norm_def, Real.norm_eq_abs]
  exact max_le (le_add_of_nonneg_right (abs_nonneg y)) (le_add_of_nonneg_left (norm_nonneg z))

lemma sliceGrowth_exp_neg (F : G × ℝ → ℝ) (hF : Differentiable ℝ F) (hg : PotGrowth F) :
    SliceGrowth (fun p => Real.exp (-(F p))) := by
  obtain ⟨⟨C, hC0, N, hC⟩, ⟨D, hD⟩⟩ := hg
  set K : ℝ := Real.exp D with hKdef
  set Cc : ℝ := max 1 C * (K + 1) with hCcdef
  set Cf : ℝ := Cc * max 1 C with hCfdef
  have hK0 : 0 < K := by rw [hKdef]; exact Real.exp_pos D
  have hm1 : (1 : ℝ) ≤ max 1 C := le_max_left _ _
  have hmC : C ≤ max 1 C := le_max_right _ _
  have hCc0 : 0 ≤ Cc := by rw [hCcdef]; positivity
  have hCf0 : 0 ≤ Cf := by rw [hCfdef]; positivity
  have hKi : K ≤ Cc := by
    rw [hCcdef]; nlinarith [hK0, hm1]
  have hKCf : K ≤ Cf := by
    rw [hCfdef]; nlinarith [hKi, hm1, hCc0]
  have hCcCf : Cc ≤ Cf := by
    rw [hCfdef]; nlinarith [hm1, hCc0]
  have hCineq : Cc * C ≤ Cf := by
    rw [hCfdef]; exact mul_le_mul_of_nonneg_left hmC hCc0
  have hlow : ∀ (z : G) (y : ℝ), -(F (z, y)) ≤ D - (Real.pi / 2) * ‖z‖ ^ 2 := by
    intro z y
    have h3 := hD (z, y)
    have h4 : ‖z‖ ^ 2 ≤ ‖(z, y)‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg z) (norm_fst_le (z, y)) 2
    have h5 : (Real.pi / 2) * ‖z‖ ^ 2 ≤ (Real.pi / 2) * ‖(z, y)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    linarith
  have hexpD : ∀ (z : G) (y : ℝ),
      Real.exp (-(F (z, y))) ≤ K * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := by
    intro z y
    calc Real.exp (-(F (z, y))) ≤ Real.exp (D - (Real.pi / 2) * ‖z‖ ^ 2) :=
          Real.exp_le_exp.mpr (hlow z y)
      _ = K * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := by
          rw [hKdef, ← Real.exp_add]; ring_nf
  refine ⟨Cf, hCf0, N, fun z y => ⟨?_, ?_⟩⟩
  · have h9 : (1 : ℝ) ≤ (1 + ‖z‖ + |y|) ^ N :=
      one_le_pow₀ (by linarith [norm_nonneg z, abs_nonneg y] : (1 : ℝ) ≤ 1 + ‖z‖ + |y|)
    have h10 : (0 : ℝ) < Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := Real.exp_pos _
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    have h11 : K * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) ≤ Cf * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hKCf h10.le
    have h12 : Cf * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)
        ≤ Cf * (1 + ‖z‖ + |y|) ^ N * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := by
      have h14 : Cf * 1 ≤ Cf * (1 + ‖z‖ + |y|) ^ N :=
        mul_le_mul_of_nonneg_left h9 hCf0
      calc Cf * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)
          = Cf * 1 * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := by ring
        _ ≤ Cf * (1 + ‖z‖ + |y|) ^ N * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) :=
            mul_le_mul_of_nonneg_right h14 h10.le
    linarith [hexpD z y]
  · have h2 : fderiv ℝ (fun p : G × ℝ => Real.exp (-(F p))) (z, y) (0, 1)
        = -Real.exp (-(F (z, y))) * dY F (z, y) := dY_exp_neg F z y (hF (z, y))
    have h3 : |dY F (z, y)| ≤ C * (1 + ‖z‖ + |y|) ^ N :=
      le_trans (hC (z, y)).1 (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (by linarith [norm_pair_le z y]) N) hC0)
    have h5 : Real.exp (-(F (z, y))) ≤ Cc * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := by
      have h10 : (0 : ℝ) < Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := Real.exp_pos _
      exact le_trans (hexpD z y) (mul_le_mul_of_nonneg_right hKi h10.le)
    rw [h2, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (Real.exp_pos _).le]
    have hstep : Real.exp (-(F (z, y))) * |dY F (z, y)|
        ≤ Cc * C * (1 + ‖z‖ + |y|) ^ N * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := by
      calc Real.exp (-(F (z, y))) * |dY F (z, y)|
          ≤ (Cc * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)) * (C * (1 + ‖z‖ + |y|) ^ N) :=
            mul_le_mul h5 h3 (abs_nonneg _) (mul_nonneg hCc0 (Real.exp_pos _).le)
        _ = Cc * C * (1 + ‖z‖ + |y|) ^ N * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := by ring
    refine le_trans hstep ?_
    have h8 : (0 : ℝ) ≤ (1 + ‖z‖ + |y|) ^ N := by positivity
    have h9 : (0 : ℝ) < Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := Real.exp_pos _
    have h13 : Cc * C * (1 + ‖z‖ + |y|) ^ N * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)
        ≤ Cf * (1 + ‖z‖ + |y|) ^ N * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := by
      have h14 : Cc * C * (1 + ‖z‖ + |y|) ^ N ≤ Cf * (1 + ‖z‖ + |y|) ^ N :=
        mul_le_mul_of_nonneg_right hCineq h8
      exact mul_le_mul_of_nonneg_right h14 h9.le
    exact h13

/-! #### Growth of test functions and differentiation of the slice integrals -/

/-- Polynomial growth of a function `H : G × ℝ → ℝ` and of its partial `y`-derivative. -/
def HGrowth (H : G × ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p : G × ℝ,
    |H p| ≤ C * (1 + ‖p‖) ^ N ∧ |dY H p| ≤ C * (1 + ‖p‖) ^ N

lemma dY_const (c : ℝ) (p : G × ℝ) : dY (fun _ : G × ℝ => c) p = 0 := by
  show fderiv ℝ (fun _ : G × ℝ => c) p (0, 1) = 0
  rw [fderiv_const_apply]
  rfl

lemma hgrowth_dY {F : G × ℝ → ℝ} (hF : PotGrowth F) : HGrowth (dY F) := by
  obtain ⟨⟨C, hC0, N, hC⟩, _⟩ := hF
  exact ⟨C, hC0, N, fun p => hC p⟩

lemma hgrowth_const (c : ℝ) : HGrowth (fun _ : G × ℝ => c) := by
  have h0 : (0 : ℝ) ≤ |c| + 1 := by positivity
  refine ⟨|c| + 1, h0, 1, fun p => ⟨?_, ?_⟩⟩
  · calc |c| ≤ |c| + 1 := by linarith [abs_nonneg c]
      _ = (|c| + 1) * 1 := by ring
      _ ≤ (|c| + 1) * (1 + ‖p‖) ^ 1 := by
          refine mul_le_mul_of_nonneg_left ?_ h0
          rw [pow_one]; linarith [norm_nonneg p]
  · rw [dY_const, abs_zero]; positivity

lemma exp_neg_half_pi_norm_sq_le_fst (z : G) (y : ℝ) :
    Real.exp (-(Real.pi / 2) * ‖(z, y)‖ ^ 2) ≤ Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := by
  apply Real.exp_le_exp.mpr
  have h : ‖z‖ ≤ ‖(z, y)‖ := by rw [Prod.norm_def]; exact le_max_left _ _
  have h2 : ‖z‖ ^ 2 ≤ ‖(z, y)‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg z) h 2
  nlinarith [Real.pi_pos]

lemma sliceGrowth_mul_exp_neg (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 1 F) (hp : PotGrowth F)
    (hH : ContDiff ℝ 1 H) (hg : HGrowth H) :
    SliceGrowth (fun p => H p * Real.exp (-(F p))) := by
  obtain ⟨⟨C, hC0, N, hC⟩, ⟨D, hD⟩⟩ := hp
  obtain ⟨C₂, hC₂0, N₂, hC₂⟩ := hg
  set K : ℝ := Real.exp D with hKdef
  have hK0 : 0 < K := Real.exp_pos D
  have h1C : (1 : ℝ) ≤ 1 + C := by linarith
  have hC₂K0 : (0 : ℝ) ≤ C₂ * K := mul_nonneg hC₂0 hK0.le
  have hexp : ∀ z : G, ∀ y : ℝ,
      Real.exp (-(F (z, y))) ≤ K * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := by
    intro z y
    calc Real.exp (-(F (z, y))) ≤ Real.exp (D - (Real.pi / 2) * ‖(z, y)‖ ^ 2) := by
          apply Real.exp_le_exp.mpr
          have h := hD (z, y); linarith
      _ = K * Real.exp (-(Real.pi / 2) * ‖(z, y)‖ ^ 2) := by
          rw [hKdef, ← Real.exp_add]; ring_nf
      _ ≤ K * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (exp_neg_half_pi_norm_sq_le_fst z y) hK0.le
  have hC' : C₂ * K ≤ max 1 (C₂ * K * (1 + C)) := by
    calc C₂ * K ≤ C₂ * K * (1 + C) := by
          nth_rewrite 1 [← mul_one (C₂ * K)]
          exact mul_le_mul_of_nonneg_left h1C hC₂K0
      _ ≤ max 1 (C₂ * K * (1 + C)) := le_max_right _ _
  have hmax0 : (0 : ℝ) ≤ max 1 (C₂ * K * (1 + C)) := by positivity
  refine ⟨max 1 (C₂ * K * (1 + C)), hmax0, N₂ + N, fun z y => ⟨?_, ?_⟩⟩
  · have hQ : (1 : ℝ) ≤ 1 + ‖z‖ + |y| := by
      linarith [norm_nonneg z, abs_nonneg y]
    have he0 : (0 : ℝ) < Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := Real.exp_pos _
    have hP : (1 + ‖(z, y)‖) ^ N₂ ≤ (1 + ‖z‖ + |y|) ^ N₂ :=
      pow_le_pow_left₀ (by positivity) (by linarith [norm_pair_le z y]) N₂
    have hQN : (1 + ‖z‖ + |y|) ^ N₂ ≤ (1 + ‖z‖ + |y|) ^ (N₂ + N) :=
      pow_le_pow_right₀ hQ (Nat.le_add_right _ _)
    have h1 : |H (z, y)| ≤ C₂ * (1 + ‖z‖ + |y|) ^ N₂ :=
      le_trans (hC₂ (z, y)).1 (mul_le_mul_of_nonneg_left hP hC₂0)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    calc |H (z, y)| * Real.exp (-(F (z, y)))
        ≤ (C₂ * (1 + ‖z‖ + |y|) ^ N₂) * (K * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)) :=
          mul_le_mul h1 (hexp z y) (Real.exp_pos _).le (by positivity)
      _ = (C₂ * K) * ((1 + ‖z‖ + |y|) ^ N₂ * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)) := by ring
      _ ≤ (max 1 (C₂ * K * (1 + C))) * ((1 + ‖z‖ + |y|) ^ (N₂ + N)
            * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)) :=
          mul_le_mul hC' (mul_le_mul_of_nonneg_right hQN he0.le)
            (mul_nonneg (by positivity) he0.le) (by positivity)
      _ = (max 1 (C₂ * K * (1 + C))) * (1 + ‖z‖ + |y|) ^ (N₂ + N)
            * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := by ring
  · rw [show fderiv ℝ (fun p => H p * Real.exp (-(F p))) (z, y) (0, 1)
        = dY (fun p => H p * Real.exp (-(F p))) (z, y) from rfl, Real.norm_eq_abs]
    have hdH : DifferentiableAt ℝ H (z, y) := hH.differentiable (by norm_num) (z, y)
    have hdF : DifferentiableAt ℝ F (z, y) := hF.differentiable (by norm_num) (z, y)
    have hde : DifferentiableAt ℝ (fun p : G × ℝ => Real.exp (-(F p))) (z, y) := hdF.neg.exp
    have hval : |dY (fun p => H p * Real.exp (-(F p))) (z, y)|
        ≤ (|dY H (z, y)| + |H (z, y)| * |dY F (z, y)|) * Real.exp (-(F (z, y))) := by
      rw [dY_mul H (fun p => Real.exp (-(F p))) z y hdH hde, dY_exp_neg F z y hdF]
      have he : (0 : ℝ) < Real.exp (-(F (z, y))) := Real.exp_pos _
      calc |dY H (z, y) * Real.exp (-(F (z, y)))
            + H (z, y) * (-Real.exp (-(F (z, y))) * dY F (z, y))|
          ≤ |dY H (z, y) * Real.exp (-(F (z, y)))|
            + |H (z, y) * (-Real.exp (-(F (z, y))) * dY F (z, y))| := abs_add_le _ _
        _ = (|dY H (z, y)| + |H (z, y)| * |dY F (z, y)|) * Real.exp (-(F (z, y))) := by
            rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos he]; ring
    refine le_trans hval ?_
    have hQ : (1 : ℝ) ≤ 1 + ‖z‖ + |y| := by linarith [norm_nonneg z, abs_nonneg y]
    have he0 : (0 : ℝ) < Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := Real.exp_pos _
    have hA1 : (1 : ℝ) ≤ (1 + ‖z‖ + |y|) ^ N := one_le_pow₀ hQ
    have hP : (1 + ‖(z, y)‖) ^ N ≤ (1 + ‖z‖ + |y|) ^ N :=
      pow_le_pow_left₀ (by positivity) (by linarith [norm_pair_le z y]) N
    have hP₂ : (1 + ‖(z, y)‖) ^ N₂ ≤ (1 + ‖z‖ + |y|) ^ N₂ :=
      pow_le_pow_left₀ (by positivity) (by linarith [norm_pair_le z y]) N₂
    have h1 : |dY H (z, y)| ≤ C₂ * (1 + ‖z‖ + |y|) ^ N₂ :=
      le_trans (hC₂ (z, y)).2 (mul_le_mul_of_nonneg_left hP₂ hC₂0)
    have h2 : |H (z, y)| ≤ C₂ * (1 + ‖z‖ + |y|) ^ N₂ :=
      le_trans (hC₂ (z, y)).1 (mul_le_mul_of_nonneg_left hP₂ hC₂0)
    have h3 : |dY F (z, y)| ≤ C * (1 + ‖z‖ + |y|) ^ N :=
      le_trans (hC (z, y)).1 (mul_le_mul_of_nonneg_left hP hC0)
    have h4 : |H (z, y)| * |dY F (z, y)|
        ≤ (C₂ * (1 + ‖z‖ + |y|) ^ N₂) * (C * (1 + ‖z‖ + |y|) ^ N) :=
      mul_le_mul h2 h3 (abs_nonneg _) (by positivity)
    have h5 : |dY H (z, y)| + |H (z, y)| * |dY F (z, y)|
        ≤ C₂ * (1 + ‖z‖ + |y|) ^ N₂ * (1 + C * (1 + ‖z‖ + |y|) ^ N) := by
      refine le_trans (add_le_add h1 h4) (le_of_eq ?_)
      ring
    have key : (C₂ * (1 + ‖z‖ + |y|) ^ N₂ * (1 + C * (1 + ‖z‖ + |y|) ^ N))
          * (K * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2))
        ≤ (max 1 (C₂ * K * (1 + C))) * (1 + ‖z‖ + |y|) ^ (N₂ + N)
            * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := by
      set Q : ℝ := 1 + ‖z‖ + |y| with hQdef
      set e : ℝ := Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) with hedef
      have hQ1 : (1 : ℝ) ≤ Q := hQ
      have he1 : (0 : ℝ) < e := he0
      have hA1' : (1 : ℝ) ≤ Q ^ N := one_le_pow₀ hQ1
      have hprod : Q ^ N₂ ≤ Q ^ N₂ * Q ^ N := by
        nth_rewrite 1 [← mul_one (Q ^ N₂)]
        exact mul_le_mul_of_nonneg_left hA1' (by positivity)
      have hL : C₂ * Q ^ N₂ * (K * e) ≤ C₂ * (Q ^ N₂ * Q ^ N) * (K * e) := by
        have h₁ : C₂ * Q ^ N₂ ≤ C₂ * (Q ^ N₂ * Q ^ N) :=
          mul_le_mul_of_nonneg_left hprod hC₂0
        exact mul_le_mul_of_nonneg_right h₁ (by positivity)
      have hmax : C₂ * K * (1 + C) ≤ max 1 (C₂ * K * (1 + C)) := le_max_right _ _
      rw [pow_add]
      calc C₂ * Q ^ N₂ * (1 + C * Q ^ N) * (K * e)
          = C₂ * Q ^ N₂ * (K * e) + C₂ * C * (Q ^ N₂ * Q ^ N) * (K * e) := by ring
        _ ≤ C₂ * (Q ^ N₂ * Q ^ N) * (K * e)
              + C₂ * C * (Q ^ N₂ * Q ^ N) * (K * e) := by linarith [hL]
        _ = (C₂ * K * (1 + C)) * (Q ^ N₂ * Q ^ N) * e := by ring
        _ ≤ (max 1 (C₂ * K * (1 + C))) * (Q ^ N₂ * Q ^ N) * e :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmax (by positivity)) he1.le
    calc (|dY H (z, y)| + |H (z, y)| * |dY F (z, y)|) * Real.exp (-(F (z, y)))
        ≤ (C₂ * (1 + ‖z‖ + |y|) ^ N₂ * (1 + C * (1 + ‖z‖ + |y|) ^ N))
            * (K * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)) :=
          mul_le_mul h5 (hexp z y) (Real.exp_pos _).le (by positivity)
      _ ≤ (max 1 (C₂ * K * (1 + C))) * (1 + ‖z‖ + |y|) ^ (N₂ + N)
            * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := key

/-! #### Differentiation of the slice mass and the marginal potential -/

/-- The derivative of the slice mass `W(y) = ∫ z, exp (-(F (z,y)))`. -/
noncomputable def massDeriv (F : G × ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ z, -(dY F (z, y)) * Real.exp (-(F (z, y)))

/-- The second derivative of the slice mass. -/
noncomputable def massDeriv2 (F : G × ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ z, ((dY F (z, y)) ^ 2 - d2Y F (z, y)) * Real.exp (-(F (z, y)))

/-- The derivative of `y ↦ ∫ z, H (z,y) exp (-(F (z,y)))`. -/
noncomputable def mixDeriv (F H : G × ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ z, (dY H (z, y) - H (z, y) * dY F (z, y)) * Real.exp (-(F (z, y)))

/-- The marginal potential `U y = -log (sliceMass F y)`. -/
noncomputable def marg (F : G × ℝ → ℝ) : ℝ → ℝ := fun y => -Real.log (sliceMass F y)

/-- The value of the second derivative of the marginal potential. -/
noncomputable def margD2 (F : G × ℝ → ℝ) (y : ℝ) : ℝ :=
  (-(massDeriv2 F y) * sliceMass F y + (massDeriv F y) ^ 2) / (sliceMass F y) ^ 2

lemma hgrowth_neg_dY {F : G × ℝ → ℝ} (hF : PotGrowth F) : HGrowth (fun p => -(dY F p)) := by
  obtain ⟨⟨C, hC0, N, hC⟩, _⟩ := hF
  refine ⟨C, hC0, N, fun p => ⟨?_, ?_⟩⟩
  · rw [abs_neg]; exact (hC p).1
  · show |dY (fun p : G × ℝ => -(dY F p)) p| ≤ C * (1 + ‖p‖) ^ N
    have : dY (fun p : G × ℝ => -(dY F p)) p = -(d2Y F p) := by
      show fderiv ℝ (fun p : G × ℝ => -(dY F p)) p (0, 1) = -(fderiv ℝ (dY F) p (0, 1))
      rw [show (fun p : G × ℝ => -(dY F p)) = -(fun p : G × ℝ => dY F p) from rfl,
        fderiv_neg]
      exact ContinuousLinearMap.neg_apply _ _
    rw [this, abs_neg]; exact (hC p).2

lemma hasDerivAt_sliceMass (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F) (y₀ : ℝ) :
    HasDerivAt (sliceMass F) (massDeriv F y₀) y₀ := by
  have hdiff : Differentiable ℝ F := hF.differentiable (by norm_num)
  have h := hasDerivAt_integral_slice_of_growth (fun p => Real.exp (-(F p)))
    ((hF.neg).exp.of_le (by norm_num)) (sliceGrowth_exp_neg F hdiff hp) y₀
  have hkey : (∫ z, fderiv ℝ (fun p => Real.exp (-(F p))) (z, y₀) (0, 1))
      = massDeriv F y₀ := by
    rw [show massDeriv F y₀ = ∫ z, -(dY F (z, y₀)) * Real.exp (-(F (z, y₀))) from rfl]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    show fderiv ℝ (fun p => Real.exp (-(F p))) (z, y₀) (0, 1)
      = -(dY F (z, y₀)) * Real.exp (-(F (z, y₀)))
    show dY (fun p => Real.exp (-(F p))) (z, y₀) = -(dY F (z, y₀)) * Real.exp (-(F (z, y₀)))
    rw [dY_exp_neg F z y₀ (hdiff (z, y₀))]
    ring
  exact h.congr_deriv hkey

lemma hasDerivAt_massDeriv (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F) (y₀ : ℝ) :
    HasDerivAt (massDeriv F) (massDeriv2 F y₀) y₀ := by
  have hdY1 : ContDiff ℝ 1 (fun p : G × ℝ => -(dY F p)) := (contDiff_dY F hF).neg
  have h := hasDerivAt_integral_slice_of_growth (fun p => -(dY F p) * Real.exp (-(F p)))
    (hdY1.mul ((hF.neg).exp.of_le (by norm_num))) (sliceGrowth_mul_exp_neg F (fun p => -(dY F p))
      (hF.of_le (by norm_num)) hp hdY1 (hgrowth_neg_dY hp)) y₀
  have hdiff : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hdYdiff : Differentiable ℝ (dY F) := (contDiff_dY F hF).differentiable (by norm_num)
  have hkey : (∫ z, fderiv ℝ (fun p => -(dY F p) * Real.exp (-(F p))) (z, y₀) (0, 1))
      = massDeriv2 F y₀ := by
    rw [show massDeriv2 F y₀
      = ∫ z, ((dY F (z, y₀)) ^ 2 - d2Y F (z, y₀)) * Real.exp (-(F (z, y₀))) from rfl]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    show fderiv ℝ (fun p => -(dY F p) * Real.exp (-(F p))) (z, y₀) (0, 1)
      = ((dY F (z, y₀)) ^ 2 - d2Y F (z, y₀)) * Real.exp (-(F (z, y₀)))
    show dY (fun p => -(dY F p) * Real.exp (-(F p))) (z, y₀) = _
    have h1 : dY (fun p : G × ℝ => -(dY F p)) (z, y₀) = -(d2Y F (z, y₀)) := by
      show fderiv ℝ (fun p : G × ℝ => -(dY F p)) (z, y₀) (0, 1)
        = -(fderiv ℝ (dY F) (z, y₀) (0, 1))
      rw [show (fun p : G × ℝ => -(dY F p)) = -(fun p : G × ℝ => dY F p) from rfl,
        fderiv_neg]
      exact ContinuousLinearMap.neg_apply _ _
    rw [dY_mul (fun p => -(dY F p)) (fun p => Real.exp (-(F p))) z y₀
        (hdYdiff (z, y₀)).neg ((hdiff (z, y₀)).neg.exp), h1, dY_exp_neg F z y₀ (hdiff (z, y₀))]
    ring
  exact h.congr_deriv hkey

lemma hasDerivAt_mixDeriv (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hH : ContDiff ℝ 1 H) (hg : HGrowth H) (y₀ : ℝ) :
    HasDerivAt (fun y => ∫ z, H (z, y) * Real.exp (-(F (z, y)))) (mixDeriv F H y₀) y₀ := by
  have h := hasDerivAt_integral_slice_of_growth (fun p => H p * Real.exp (-(F p)))
    (hH.mul ((hF.neg).exp.of_le (by norm_num))) (sliceGrowth_mul_exp_neg F H (hF.of_le (by norm_num)) hp hH hg) y₀
  have hdiff : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hkey : (∫ z, fderiv ℝ (fun p => H p * Real.exp (-(F p))) (z, y₀) (0, 1))
      = mixDeriv F H y₀ := by
    rw [show mixDeriv F H y₀
      = ∫ z, (dY H (z, y₀) - H (z, y₀) * dY F (z, y₀)) * Real.exp (-(F (z, y₀))) from rfl]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    show fderiv ℝ (fun p => H p * Real.exp (-(F p))) (z, y₀) (0, 1)
      = (dY H (z, y₀) - H (z, y₀) * dY F (z, y₀)) * Real.exp (-(F (z, y₀)))
    show dY (fun p => H p * Real.exp (-(F p))) (z, y₀) = _
    rw [dY_mul H (fun p => Real.exp (-(F p))) z y₀
        (hH.differentiable (by norm_num) (z, y₀)) ((hdiff (z, y₀)).neg.exp),
      dY_exp_neg F z y₀ (hdiff (z, y₀))]
    ring
  exact h.congr_deriv hkey

lemma hasDerivAt_marg (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F) (y₀ : ℝ)
    (hW : sliceMass F y₀ ≠ 0) :
    HasDerivAt (marg F) (-(massDeriv F y₀ / sliceMass F y₀)) y₀ := by
  have h1 : HasDerivAt (fun y => Real.log (sliceMass F y))
      (massDeriv F y₀ / sliceMass F y₀) y₀ :=
    (hasDerivAt_sliceMass F hF hp y₀).log hW
  have h2 : HasDerivAt (fun y => -Real.log (sliceMass F y))
      (-(massDeriv F y₀ / sliceMass F y₀)) y₀ := h1.neg
  exact h2

lemma hasDerivAt_margDeriv (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F) (y₀ : ℝ)
    (hW : sliceMass F y₀ ≠ 0) :
    HasDerivAt (fun y => -(massDeriv F y) / sliceMass F y) (margD2 F y₀) y₀ := by
  have hnum : HasDerivAt (fun y => -(massDeriv F y)) (-(massDeriv2 F y₀)) y₀ :=
    (hasDerivAt_massDeriv F hF hp y₀).neg
  have hq := hnum.div (hasDerivAt_sliceMass F hF hp y₀) hW
  have hval : (-(massDeriv2 F y₀) * sliceMass F y₀ - (-(massDeriv F y₀)) * massDeriv F y₀)
      / (sliceMass F y₀) ^ 2 = margD2 F y₀ := by
    rw [show margD2 F y₀
      = (-(massDeriv2 F y₀) * sliceMass F y₀ + (massDeriv F y₀) ^ 2) / (sliceMass F y₀) ^ 2
        from rfl]
    ring
  exact hq.congr_deriv hval

/-! #### Regularity of the marginal potential -/

/-- Value-only growth condition: sufficient for continuity of slice integrals. -/
def ValGrowth (Φ : G × ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ z : G, ∀ y : ℝ,
    ‖Φ (z, y)‖ ≤ C * (1 + ‖z‖ + |y|) ^ N * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)

lemma sliceGrowth_valGrowth {Φ : G × ℝ → ℝ} (h : SliceGrowth Φ) : ValGrowth Φ := by
  obtain ⟨C, hC0, N, hC⟩ := h
  exact ⟨C, hC0, N, fun z y => (hC z y).1⟩

lemma continuousAt_sliceIntegral_of_valGrowth (Φ : G × ℝ → ℝ) (hΦ : Continuous Φ)
    (hg : ValGrowth Φ) (y₀ : ℝ) :
    ContinuousAt (fun y => ∫ z, Φ (z, y)) y₀ := by
  obtain ⟨C, hC0, N, hC⟩ := hg
  set bound : G → ℝ := fun z => C * (3 + |y₀|) ^ N * (1 + ‖z‖) ^ N
    * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) with hbounddef
  have hbound_int : Integrable bound := by
    rw [hbounddef]
    exact integrable_gauss_poly (C * (3 + |y₀|) ^ N) N
  have hmono : ∀ z : G, C * (1 + ‖z‖ + |y₀|) ^ N
      * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) ≤ bound z := by
    intro z
    have h2b : (1 + ‖z‖ + |y₀|) ^ N ≤ (3 + |y₀|) ^ N * (1 + ‖z‖) ^ N := by
      calc (1 + ‖z‖ + |y₀|) ^ N ≤ (1 + |y₀| + 1) ^ N * (1 + ‖z‖) ^ N :=
            pow_one_add_norm_add_abs_le (G := G) z y₀ N
        _ ≤ (3 + |y₀|) ^ N * (1 + ‖z‖) ^ N := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact pow_le_pow_left₀ (by positivity) (by linarith) N
    rw [hbounddef]
    calc C * (1 + ‖z‖ + |y₀|) ^ N * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)
        ≤ C * ((3 + |y₀|) ^ N * (1 + ‖z‖) ^ N)
              * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left h2b hC0
      _ = C * (3 + |y₀|) ^ N * (1 + ‖z‖) ^ N
              * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := by ring
  refine Commons.Analysis.Calculus.continuousAt_integral_slice Φ y₀ bound hΦ hbound_int ?_ ?_
  · refine Integrable.mono' hbound_int ?_ ?_
    · exact Continuous.aestronglyMeasurable (hΦ.comp (continuous_id.prodMk continuous_const))
    · filter_upwards with z
      exact le_trans (hC z y₀) (hmono z)
  · intro z y hy
    rw [abs_lt] at hy
    have hy1 : |y| ≤ |y₀| + 1 := by
      rw [abs_le]
      exact ⟨by linarith [hy.1, neg_le_abs y₀], by linarith [hy.2, le_abs_self y₀]⟩
    have h3 : (1 + ‖z‖ + |y|) ^ N ≤ (3 + |y₀|) ^ N * (1 + ‖z‖) ^ N := by
      calc (1 + ‖z‖ + |y|) ^ N ≤ (1 + |y| + 1) ^ N * (1 + ‖z‖) ^ N :=
            pow_one_add_norm_add_abs_le (G := G) z y N
        _ ≤ (3 + |y₀|) ^ N * (1 + ‖z‖) ^ N := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact pow_le_pow_left₀ (by positivity) (by linarith) N
    rw [show bound z = C * (3 + |y₀|) ^ N * (1 + ‖z‖) ^ N
      * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) from by rw [hbounddef]]
    calc ‖Φ (z, y)‖
        ≤ C * (1 + ‖z‖ + |y|) ^ N * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := hC z y
      _ ≤ C * ((3 + |y₀|) ^ N * (1 + ‖z‖) ^ N)
            * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left h3 hC0
      _ = C * (3 + |y₀|) ^ N * (1 + ‖z‖) ^ N
            * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := by ring

/-- Value growth of a function `H` (no derivative bound). -/
def HGrowth0 (H : G × ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p : G × ℝ, |H p| ≤ C * (1 + ‖p‖) ^ N

lemma ValGrowth_mul_exp_neg (F H : G × ℝ → ℝ) (hp : PotGrowth F) (hh : HGrowth0 H) :
    ValGrowth (fun p => H p * Real.exp (-(F p))) := by
  obtain ⟨⟨C, hC0, N, hC⟩, ⟨D, hD⟩⟩ := hp
  obtain ⟨C₂, hC₂0, N₂, hC₂⟩ := hh
  set K : ℝ := Real.exp D with hKdef
  have hK0 : 0 < K := Real.exp_pos D
  refine ⟨max 1 (C₂ * K), by positivity, N₂ + N, fun z y => ?_⟩
  have hQ : (1 : ℝ) ≤ 1 + ‖z‖ + |y| := by linarith [norm_nonneg z, abs_nonneg y]
  have he0 : (0 : ℝ) < Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := Real.exp_pos _
  have hP₂ : (1 + ‖(z, y)‖) ^ N₂ ≤ (1 + ‖z‖ + |y|) ^ N₂ :=
    pow_le_pow_left₀ (by positivity) (by linarith [norm_pair_le z y]) N₂
  have hQN : (1 + ‖z‖ + |y|) ^ N₂ ≤ (1 + ‖z‖ + |y|) ^ (N₂ + N) :=
    pow_le_pow_right₀ hQ (Nat.le_add_right _ _)
  have hbound : |H (z, y)| ≤ C₂ * (1 + ‖z‖ + |y|) ^ N₂ :=
    le_trans (hC₂ (z, y)) (mul_le_mul_of_nonneg_left hP₂ hC₂0)
  have hexp : Real.exp (-(F (z, y))) ≤ K * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := by
    calc Real.exp (-(F (z, y))) ≤ Real.exp (D - (Real.pi / 2) * ‖(z, y)‖ ^ 2) := by
          apply Real.exp_le_exp.mpr
          have h := hD (z, y); linarith
      _ = K * Real.exp (-(Real.pi / 2) * ‖(z, y)‖ ^ 2) := by
          rw [hKdef, ← Real.exp_add]; ring_nf
      _ ≤ K * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (exp_neg_half_pi_norm_sq_le_fst z y) hK0.le
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
  calc |H (z, y)| * Real.exp (-(F (z, y)))
      ≤ (C₂ * (1 + ‖z‖ + |y|) ^ N₂) * (K * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)) :=
        mul_le_mul hbound hexp (Real.exp_pos _).le (by positivity)
    _ = (C₂ * K) * ((1 + ‖z‖ + |y|) ^ N₂ * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)) := by ring
    _ ≤ (max 1 (C₂ * K)) * ((1 + ‖z‖ + |y|) ^ N₂ * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)) := by
        refine mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    _ ≤ (max 1 (C₂ * K)) * ((1 + ‖z‖ + |y|) ^ (N₂ + N)
          * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right hQN he0.le
    _ = (max 1 (C₂ * K)) * (1 + ‖z‖ + |y|) ^ (N₂ + N)
          * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := by ring

lemma hgrowth0_sq_sub {F : G × ℝ → ℝ} (hp : PotGrowth F) :
    HGrowth0 (fun p => (dY F p) ^ 2 - d2Y F p) := by
  obtain ⟨⟨C, hC0, N, hC⟩, _⟩ := hp
  refine ⟨C ^ 2 + C, by positivity, 2 * N, fun p => ?_⟩
  have hP : (1 : ℝ) ≤ 1 + ‖p‖ := by linarith [norm_nonneg p]
  have h1 : (1 + ‖p‖) ^ N ≤ (1 + ‖p‖) ^ (2 * N) :=
    pow_le_pow_right₀ hP (by omega)
  have h2 : (0 : ℝ) ≤ (1 + ‖p‖) ^ (2 * N) := by positivity
  have h4 : (dY F p) ^ 2 ≤ C ^ 2 * (1 + ‖p‖) ^ (2 * N) := by
    have h5 : (dY F p) ^ 2 = |dY F p| ^ 2 := by rw [sq_abs]
    rw [h5]
    calc |dY F p| ^ 2 ≤ (C * (1 + ‖p‖) ^ N) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (hC p).1 2
      _ = C ^ 2 * (1 + ‖p‖) ^ (2 * N) := by rw [mul_pow, ← pow_mul, Nat.mul_comm]
  have h6 : |d2Y F p| ≤ C * (1 + ‖p‖) ^ (2 * N) :=
    le_trans (hC p).2 (mul_le_mul_of_nonneg_left h1 hC0)
  calc |(dY F p) ^ 2 - d2Y F p| ≤ |(dY F p) ^ 2| + |d2Y F p| := abs_sub _ _
    _ = (dY F p) ^ 2 + |d2Y F p| := by rw [abs_of_nonneg (sq_nonneg _)]
    _ ≤ C ^ 2 * (1 + ‖p‖) ^ (2 * N) + C * (1 + ‖p‖) ^ (2 * N) := add_le_add h4 h6
    _ = (C ^ 2 + C) * (1 + ‖p‖) ^ (2 * N) := by ring

lemma valGrowth_phi3 (F : G × ℝ → ℝ) (hp : PotGrowth F) :
    ValGrowth (fun p => ((dY F p) ^ 2 - d2Y F p) * Real.exp (-(F p))) :=
  ValGrowth_mul_exp_neg F (fun p => (dY F p) ^ 2 - d2Y F p) hp (hgrowth0_sq_sub hp)

/-- Continuity of the second derivative of the slice mass. -/
lemma continuous_massDeriv2 (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F) :
    Continuous (massDeriv2 F) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hdY1 : ContDiff ℝ 1 (dY F) := contDiff_dY F hF
  have hcont : Continuous
      (fun p : G × ℝ => ((dY F p) ^ 2 - d2Y F p) * Real.exp (-(F p))) := by
    have h1 : Continuous (fun p : G × ℝ => dY F p) := hdY1.continuous
    have h2 : Continuous (fun p : G × ℝ => d2Y F p) :=
      (hdY1.continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact ((h1.pow 2).sub h2).mul (Real.continuous_exp.comp hF.continuous.neg)
  exact continuousAt_sliceIntegral_of_valGrowth
    (fun p : G × ℝ => ((dY F p) ^ 2 - d2Y F p) * Real.exp (-(F p))) hcont (valGrowth_phi3 F hp) y

lemma deriv_sliceMass (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F) :
    deriv (sliceMass F) = massDeriv F := by
  funext y
  exact (hasDerivAt_sliceMass F hF hp y).deriv

lemma deriv_massDeriv (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F) :
    deriv (massDeriv F) = massDeriv2 F := by
  funext y
  exact (hasDerivAt_massDeriv F hF hp y).deriv

lemma contDiff_sliceMass (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F) :
    ContDiff ℝ 2 (sliceMass F) := by
  have hd1 : Differentiable ℝ (sliceMass F) :=
    fun y => (hasDerivAt_sliceMass F hF hp y).differentiableAt
  have hd2 : Differentiable ℝ (massDeriv F) :=
    fun y => (hasDerivAt_massDeriv F hF hp y).differentiableAt
  have hcont : Continuous (massDeriv2 F) := continuous_massDeriv2 F hF hp
  refine (contDiff_succ_iff_deriv (n := 1)).mpr ⟨hd1, ?_, ?_⟩
  · intro h; exact absurd h (by simp)
  · rw [deriv_sliceMass F hF hp, contDiff_one_iff_deriv]
    exact ⟨hd2, by rw [deriv_massDeriv F hF hp]; exact hcont⟩

lemma contDiff_marg (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hW : ∀ y, 0 < sliceMass F y) : ContDiff ℝ 2 (marg F) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  have h1 : ContDiffAt ℝ 2 (sliceMass F) y := (contDiff_sliceMass F hF hp).contDiffAt
  have h2 : ContDiffAt ℝ 2 (fun t : ℝ => -Real.log t) (sliceMass F y) :=
    ((Real.contDiffAt_log).mpr (ne_of_gt (hW y))).neg
  exact h2.comp y h1

lemma deriv_deriv_marg (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hW : ∀ y, 0 < sliceMass F y) (y : ℝ) :
    deriv (deriv (marg F)) y = margD2 F y := by
  have h1 : deriv (marg F) = fun z => -(massDeriv F z) / sliceMass F z := by
    funext z
    have hz := (hasDerivAt_marg F hF hp z (ne_of_gt (hW z))).deriv
    rw [hz, neg_div]
  rw [h1]
  exact (hasDerivAt_margDeriv F hF hp y (ne_of_gt (hW y))).deriv

/-! #### Integrability and the identity `U'' = ⟨∂²F⟩ - Var(∂F)` -/

/-- Integrability of `B (1 + ‖z‖ + |a|)^M exp (-(π/2)‖z‖²)`. -/
lemma integrable_gauss_poly_y (a : ℝ) (B : ℝ) (M : ℕ) :
    Integrable (fun z : G => B * (1 + ‖z‖ + |a|) ^ M * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)) := by
  set f : G → ℝ := fun z => |B| * (1 + |a| + 1) ^ M * (1 + ‖z‖) ^ M
    * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) with hfdef
  have hf : Integrable f := integrable_gauss_poly (|B| * (1 + |a| + 1) ^ M) M
  have hf0 : ∀ z, 0 ≤ f z := fun z => by rw [hfdef]; positivity
  refine hf.norm.mono' (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards with z
  rw [Real.norm_of_nonneg (hf0 z)]
  have h1 : (1 + ‖z‖ + |a|) ^ M ≤ (1 + |a| + 1) ^ M * (1 + ‖z‖) ^ M :=
    pow_one_add_norm_add_abs_le (G := G) z a M
  have h2 : |B| * (1 + ‖z‖ + |a|) ^ M ≤ |B| * (1 + |a| + 1) ^ M * (1 + ‖z‖) ^ M := by
    calc |B| * (1 + ‖z‖ + |a|) ^ M ≤ |B| * ((1 + |a| + 1) ^ M * (1 + ‖z‖) ^ M) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg B)
      _ = |B| * (1 + |a| + 1) ^ M * (1 + ‖z‖) ^ M := by ring
  calc ‖B * (1 + ‖z‖ + |a|) ^ M * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)‖
      = |B| * (1 + ‖z‖ + |a|) ^ M * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_nonneg (show (0 : ℝ) ≤ (1 + ‖z‖ + |a|) ^ M by positivity),
          abs_of_nonneg (Real.exp_pos _).le]
    _ ≤ |B| * (1 + |a| + 1) ^ M * (1 + ‖z‖) ^ M * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = f z := by rw [hfdef]

/-- Integrability of `Φ · exp (-(F (·, y)))` when `Φ` has polynomial growth. -/
lemma integrable_of_le_gauss (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F) (y : ℝ)
    (Φ : G → ℝ) (hΦc : Continuous Φ) (B : ℝ) (hB0 : 0 ≤ B) (M : ℕ)
    (hΦ : ∀ z : G, |Φ z| ≤ B * (1 + ‖z‖ + |y|) ^ M) :
    Integrable (fun z : G => Φ z * Real.exp (-(F (z, y)))) := by
  obtain ⟨-, D, hD⟩ := hp
  have hK0 : (0 : ℝ) < Real.exp D := Real.exp_pos D
  have he : ∀ z : G, Real.exp (-(F (z, y))) ≤ Real.exp D * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := by
    intro z
    calc Real.exp (-(F (z, y))) ≤ Real.exp (D - (Real.pi / 2) * ‖(z, y)‖ ^ 2) := by
          apply Real.exp_le_exp.mpr
          have h := hD (z, y); linarith
      _ = Real.exp D * Real.exp (-(Real.pi / 2) * ‖(z, y)‖ ^ 2) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp D * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (exp_neg_half_pi_norm_sq_le_fst z y) hK0.le
  refine (integrable_gauss_poly_y (G := G) y (B * Real.exp D) M).norm.mono'
    (hΦc.mul (Real.continuous_exp.comp
      (hF.continuous.comp (continuous_id.prodMk continuous_const)).neg)).aestronglyMeasurable ?_
  filter_upwards with z
  rw [Real.norm_of_nonneg (show (0 : ℝ) ≤ B * Real.exp D * (1 + ‖z‖ + |y|) ^ M
    * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) by positivity)]
  have hmul : |Φ z| * Real.exp (-(F (z, y)))
      ≤ B * (1 + ‖z‖ + |y|) ^ M * (Real.exp D * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)) :=
    mul_le_mul (hΦ z) (he z) (Real.exp_pos _).le (by positivity)
  calc ‖Φ z * Real.exp (-(F (z, y)))‖
      = |Φ z| * Real.exp (-(F (z, y))) := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    _ ≤ B * (1 + ‖z‖ + |y|) ^ M * (Real.exp D * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)) := hmul
    _ = B * Real.exp D * (1 + ‖z‖ + |y|) ^ M * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) := by ring

lemma integrable_dY_exp_neg (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F) (y : ℝ) :
    Integrable (fun z : G => dY F (z, y) * Real.exp (-(F (z, y)))) := by
  obtain ⟨C, hC0, N, hC⟩ := hp.1
  refine integrable_of_le_gauss F hF hp y (fun z => dY F (z, y))
    ((contDiff_dY F hF).continuous.comp (continuous_id.prodMk continuous_const)) C hC0 N ?_
  intro z
  exact le_trans (hC (z, y)).1
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith [norm_pair_le z y]) N) hC0)

lemma integrable_dY2_exp_neg (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F) (y : ℝ) :
    Integrable (fun z : G => (dY F (z, y)) ^ 2 * Real.exp (-(F (z, y)))) := by
  obtain ⟨C, hC0, N, hC⟩ := hp.1
  refine integrable_of_le_gauss F hF hp y (fun z => (dY F (z, y)) ^ 2)
    (((contDiff_dY F hF).continuous.comp (continuous_id.prodMk continuous_const)).pow 2)
    (C ^ 2) (by positivity) (2 * N) ?_
  intro z
  have h1 : |dY F (z, y)| ≤ C * (1 + ‖z‖ + |y|) ^ N :=
    le_trans (hC (z, y)).1
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (by linarith [norm_pair_le z y]) N) hC0)
  have h2 : (dY F (z, y)) ^ 2 ≤ (C * (1 + ‖z‖ + |y|) ^ N) ^ 2 := by
    rw [show (dY F (z, y)) ^ 2 = |dY F (z, y)| ^ 2 from by rw [sq_abs]]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  rw [show |(dY F (z, y)) ^ 2| = (dY F (z, y)) ^ 2 from abs_of_nonneg (sq_nonneg _)]
  calc (dY F (z, y)) ^ 2 ≤ (C * (1 + ‖z‖ + |y|) ^ N) ^ 2 := h2
    _ = C ^ 2 * (1 + ‖z‖ + |y|) ^ (2 * N) := by rw [mul_pow, ← pow_mul, Nat.mul_comm]

lemma integrable_d2Y_exp_neg (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F) (y : ℝ) :
    Integrable (fun z : G => d2Y F (z, y) * Real.exp (-(F (z, y)))) := by
  obtain ⟨C, hC0, N, hC⟩ := hp.1
  have hdY1 : ContDiff ℝ 1 (dY F) := contDiff_dY F hF
  have hcont2 : Continuous (fun p : G × ℝ => d2Y F p) :=
    (hdY1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  refine integrable_of_le_gauss F hF hp y (fun z => d2Y F (z, y))
    (hcont2.comp (continuous_id.prodMk continuous_const)) C hC0 N ?_
  intro z
  exact le_trans (hC (z, y)).2
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith [norm_pair_le z y]) N) hC0)

lemma massDeriv_eq (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F) (y : ℝ) :
    massDeriv F y = -∫ z, dY F (z, y) * Real.exp (-(F (z, y))) := by
  show (∫ z, -(dY F (z, y)) * Real.exp (-(F (z, y)))) = _
  rw [show (fun z : G => -(dY F (z, y)) * Real.exp (-(F (z, y))))
      = fun z : G => -(dY F (z, y) * Real.exp (-(F (z, y)))) from funext (fun z => by ring)]
  rw [integral_neg]

lemma massDeriv2_eq (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F) (y : ℝ) :
    massDeriv2 F y = (∫ z, (dY F (z, y)) ^ 2 * Real.exp (-(F (z, y))))
      - ∫ z, d2Y F (z, y) * Real.exp (-(F (z, y))) := by
  show (∫ z, ((dY F (z, y)) ^ 2 - d2Y F (z, y)) * Real.exp (-(F (z, y)))) = _
  rw [show (fun z : G => ((dY F (z, y)) ^ 2 - d2Y F (z, y)) * Real.exp (-(F (z, y))))
      = fun z : G => (dY F (z, y)) ^ 2 * Real.exp (-(F (z, y)))
          - d2Y F (z, y) * Real.exp (-(F (z, y))) from funext (fun z => by ring)]
  rw [integral_sub (integrable_dY2_exp_neg F hF hp y) (integrable_d2Y_exp_neg F hF hp y)]

lemma margD2_eq (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (y : ℝ) (hW : sliceMass F y ≠ 0) :
    margD2 F y = condMean F (d2Y F) y - condVar F (dY F) y := by
  have h1 := massDeriv2_eq F hF hp y
  have h2 := massDeriv_eq F hF hp y
  show (-(massDeriv2 F y) * sliceMass F y + (massDeriv F y) ^ 2) / (sliceMass F y) ^ 2
      = (∫ z, d2Y F (z, y) * Real.exp (-(F (z, y)))) / sliceMass F y
        - ((∫ z, (dY F (z, y)) ^ 2 * Real.exp (-(F (z, y)))) / sliceMass F y
            - ((∫ z, dY F (z, y) * Real.exp (-(F (z, y)))) / sliceMass F y) ^ 2)
  rw [h1, h2]
  field_simp
  ring

/-! #### Coercivity of the marginal potential -/

/-- `y ↦ exp (-c y²)` tends to `0` at `+∞`, for `c > 0`. -/
lemma tendsto_exp_neg_sq_atTop (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun y : ℝ => Real.exp (-c * y ^ 2)) Filter.atTop (𝓝 0) := by
  have hsq_top : Filter.Tendsto (fun z : ℝ => z ^ 2) Filter.atTop Filter.atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop (max b 0), eventually_ge_atTop (1 : ℝ)] with z h1 h2
    by_cases hb : b ≤ 0
    · nlinarith [sq_nonneg z, hb]
    · rw [not_le] at hb
      have h3 : b ≤ z := le_trans (le_max_left b 0) h1
      have h4 := mul_le_mul h3 h2 (by norm_num : (0 : ℝ) ≤ 1) (le_trans hb.le h3)
      nlinarith [h4]
  have h2 : Filter.Tendsto (fun y : ℝ => c * y ^ 2) Filter.atTop Filter.atTop := by
    have h := Tendsto.atTop_mul_const hc hsq_top
    have h3 : (fun z : ℝ => z ^ 2 * c) = fun z : ℝ => c * z ^ 2 := by funext z; ring
    rwa [h3] at h
  have h1 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h2
  simpa only [Function.comp_def, neg_mul] using h1

/-- `y ↦ exp (-c y²)` tends to `0` at `-∞`, for `c > 0`. -/
lemma tendsto_exp_neg_sq_atBot (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun y : ℝ => Real.exp (-c * y ^ 2)) Filter.atBot (𝓝 0) := by
  have hsq_top : Filter.Tendsto (fun z : ℝ => z ^ 2) Filter.atTop Filter.atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop (max b 0), eventually_ge_atTop (1 : ℝ)] with z h1 h2
    by_cases hb : b ≤ 0
    · nlinarith [sq_nonneg z, hb]
    · rw [not_le] at hb
      have h3 : b ≤ z := le_trans (le_max_left b 0) h1
      have h4 := mul_le_mul h3 h2 (by norm_num : (0 : ℝ) ≤ 1) (le_trans hb.le h3)
      nlinarith [h4]
  have hneg : Filter.Tendsto (fun y : ℝ => -y) Filter.atBot Filter.atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_le_atBot (-b)] with y h1
    linarith
  have hsq_bot : Filter.Tendsto (fun y : ℝ => y ^ 2) Filter.atBot Filter.atTop := by
    have h := hsq_top.comp hneg
    simpa [Function.comp_def, neg_sq] using h
  have h2 : Filter.Tendsto (fun y : ℝ => c * y ^ 2) Filter.atBot Filter.atTop := by
    have h := Tendsto.atTop_mul_const hc hsq_bot
    have h3 : (fun z : ℝ => z ^ 2 * c) = fun z : ℝ => c * z ^ 2 := by funext z; ring
    rwa [h3] at h
  have h1 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h2
  simpa only [Function.comp_def, neg_mul] using h1

lemma tendsto_sliceMass_atTop_zero (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F) :
    Filter.Tendsto (sliceMass F) Filter.atTop (𝓝 0) := by
  obtain ⟨-, D, hD⟩ := hp
  have hK0 : (0 : ℝ) < Real.exp D := Real.exp_pos D
  have hInt : Integrable (fun z : G => Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2)) :=
    Commons.Measure.Integral.integrable_rexp_neg_mul_sq_norm (Real.pi / 4) (by positivity)
  set K : ℝ := Real.exp D * ∫ z : G, Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2) with hKdef
  have hupper : ∀ y : ℝ, sliceMass F y ≤ K * Real.exp (-(Real.pi / 4) * y ^ 2) := by
    intro y
    have hpt : ∀ z : G, Real.exp (-(F (z, y)))
        ≤ Real.exp D * Real.exp (-(Real.pi / 4) * y ^ 2) * Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2) := by
      intro z
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h := hD (z, y)
      have hmax : (Real.pi / 4) * (‖z‖ ^ 2 + y ^ 2) ≤ (Real.pi / 2) * ‖(z, y)‖ ^ 2 := by
        have h1 : ‖z‖ ≤ ‖(z, y)‖ := by rw [Prod.norm_def]; exact le_max_left _ _
        have h2 : |y| ≤ ‖(z, y)‖ := by rw [Prod.norm_def]; exact le_max_right _ _
        have h3 : y ^ 2 ≤ ‖(z, y)‖ ^ 2 := by
          rw [show y ^ 2 = |y| ^ 2 from (sq_abs y).symm]
          exact pow_le_pow_left₀ (abs_nonneg y) h2 2
        have h4 : ‖z‖ ^ 2 ≤ ‖(z, y)‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg z) h1 2
        nlinarith [h3, h4, Real.pi_pos]
      nlinarith [hmax, h]
    calc sliceMass F y = ∫ z, Real.exp (-(F (z, y))) := rfl
      _ ≤ ∫ z, Real.exp D * Real.exp (-(Real.pi / 4) * y ^ 2)
            * Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2) := by
          refine integral_mono ?_ ?_ (fun z => hpt z)
          · refine Integrable.mono'
              (hInt.const_mul (Real.exp D * Real.exp (-(Real.pi / 4) * y ^ 2))) ?_ ?_
            · exact Continuous.aestronglyMeasurable
                (Real.continuous_exp.comp
                  (hF.continuous.comp (continuous_id.prodMk continuous_const)).neg)
            · filter_upwards with z
              rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
              exact hpt z
          · exact hInt.const_mul _
      _ = Real.exp D * Real.exp (-(Real.pi / 4) * y ^ 2)
            * ∫ z : G, Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2) := by
          rw [MeasureTheory.integral_const_mul]
      _ = K * Real.exp (-(Real.pi / 4) * y ^ 2) := by rw [hKdef]; ring
  have h0 : ∀ y : ℝ, 0 ≤ sliceMass F y := fun y => integral_nonneg (fun z => (Real.exp_pos _).le)
  have hlim : Filter.Tendsto (fun y : ℝ => K * Real.exp (-(Real.pi / 4) * y ^ 2))
      Filter.atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := K) (f := Filter.atTop)).mul
      (tendsto_exp_neg_sq_atTop (Real.pi / 4) (by positivity))
    simpa using h
  exact squeeze_zero (fun y => h0 y) (fun y => hupper y) hlim

lemma tendsto_sliceMass_atBot_zero (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F) :
    Filter.Tendsto (sliceMass F) Filter.atBot (𝓝 0) := by
  obtain ⟨-, D, hD⟩ := hp
  have hK0 : (0 : ℝ) < Real.exp D := Real.exp_pos D
  have hInt : Integrable (fun z : G => Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2)) :=
    Commons.Measure.Integral.integrable_rexp_neg_mul_sq_norm (Real.pi / 4) (by positivity)
  set K : ℝ := Real.exp D * ∫ z : G, Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2) with hKdef
  have hupper : ∀ y : ℝ, sliceMass F y ≤ K * Real.exp (-(Real.pi / 4) * y ^ 2) := by
    intro y
    have hpt : ∀ z : G, Real.exp (-(F (z, y)))
        ≤ Real.exp D * Real.exp (-(Real.pi / 4) * y ^ 2) * Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2) := by
      intro z
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h := hD (z, y)
      have hmax : (Real.pi / 4) * (‖z‖ ^ 2 + y ^ 2) ≤ (Real.pi / 2) * ‖(z, y)‖ ^ 2 := by
        have h1 : ‖z‖ ≤ ‖(z, y)‖ := by rw [Prod.norm_def]; exact le_max_left _ _
        have h2 : |y| ≤ ‖(z, y)‖ := by rw [Prod.norm_def]; exact le_max_right _ _
        have h3 : y ^ 2 ≤ ‖(z, y)‖ ^ 2 := by
          rw [show y ^ 2 = |y| ^ 2 from (sq_abs y).symm]
          exact pow_le_pow_left₀ (abs_nonneg y) h2 2
        have h4 : ‖z‖ ^ 2 ≤ ‖(z, y)‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg z) h1 2
        nlinarith [h3, h4, Real.pi_pos]
      nlinarith [hmax, h]
    calc sliceMass F y = ∫ z, Real.exp (-(F (z, y))) := rfl
      _ ≤ ∫ z, Real.exp D * Real.exp (-(Real.pi / 4) * y ^ 2)
            * Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2) := by
          refine integral_mono ?_ ?_ (fun z => hpt z)
          · refine Integrable.mono'
              (hInt.const_mul (Real.exp D * Real.exp (-(Real.pi / 4) * y ^ 2))) ?_ ?_
            · exact Continuous.aestronglyMeasurable
                (Real.continuous_exp.comp
                  (hF.continuous.comp (continuous_id.prodMk continuous_const)).neg)
            · filter_upwards with z
              rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
              exact hpt z
          · exact hInt.const_mul _
      _ = Real.exp D * Real.exp (-(Real.pi / 4) * y ^ 2)
            * ∫ z : G, Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2) := by
          rw [MeasureTheory.integral_const_mul]
      _ = K * Real.exp (-(Real.pi / 4) * y ^ 2) := by rw [hKdef]; ring
  have h0 : ∀ y : ℝ, 0 ≤ sliceMass F y := fun y => integral_nonneg (fun z => (Real.exp_pos _).le)
  have hlim : Filter.Tendsto (fun y : ℝ => K * Real.exp (-(Real.pi / 4) * y ^ 2))
      Filter.atBot (𝓝 0) := by
    have h := (tendsto_const_nhds (x := K) (f := Filter.atBot)).mul
      (tendsto_exp_neg_sq_atBot (Real.pi / 4) (by positivity))
    simpa using h
  exact squeeze_zero (fun y => h0 y) (fun y => hupper y) hlim
lemma tendsto_marg_atTop (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hW : ∀ y, 0 < sliceMass F y) :
    Filter.Tendsto (marg F) Filter.atTop Filter.atTop := by
  have h0 := tendsto_sliceMass_atTop_zero F hF hp
  have hW' : Filter.Tendsto (sliceMass F) Filter.atTop (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨h0, Eventually.of_forall (fun y => hW y)⟩
  have hlog := Real.tendsto_log_nhdsGT_zero.comp hW'
  rw [tendsto_atTop]
  intro b
  rw [tendsto_atBot] at hlog
  filter_upwards [hlog (-b)] with y hy
  simp only [Function.comp_apply] at hy
  change b ≤ -Real.log (sliceMass F y)
  linarith

lemma tendsto_marg_atBot (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hW : ∀ y, 0 < sliceMass F y) :
    Filter.Tendsto (marg F) Filter.atBot Filter.atTop := by
  have h0 := tendsto_sliceMass_atBot_zero F hF hp
  have hW' : Filter.Tendsto (sliceMass F) Filter.atBot (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨h0, Eventually.of_forall (fun y => hW y)⟩
  have hlog := Real.tendsto_log_nhdsGT_zero.comp hW'
  rw [tendsto_atTop]
  intro b
  rw [tendsto_atBot] at hlog
  filter_upwards [hlog (-b)] with y hy
  simp only [Function.comp_apply] at hy
  change b ≤ -Real.log (sliceMass F y)
  linarith

/-! #### The product (induction) step -/

/-- Integrals over `WithLp 2 (G × ℝ)` written as integrals over `G × ℝ`. -/
lemma integral_comp_toLp (Φ : WithLp 2 (G × ℝ) → ℝ) :
    (∫ x : WithLp 2 (G × ℝ), Φ x) = ∫ p : G × ℝ, Φ (WithLp.toLp 2 p) := by
  have hmp : MeasurePreserving (WithLp.toLp 2 : G × ℝ → WithLp 2 (G × ℝ)) volume volume :=
    WithLp.volume_preserving_toLp G ℝ
  have hme : MeasurableEmbedding (WithLp.toLp 2 : G × ℝ → WithLp 2 (G × ℝ)) := by
    have h1 : (WithLp.toLp 2 : G × ℝ → WithLp 2 (G × ℝ))
        = ⇑((WithLp.prodContinuousLinearEquiv 2 ℝ G ℝ).symm :
            (G × ℝ) ≃L[ℝ] WithLp 2 (G × ℝ)) := rfl
    rw [h1]
    exact (WithLp.prodContinuousLinearEquiv 2 ℝ G ℝ).symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  exact (hmp.integral_comp hme Φ).symm

/-- The `L²`-norm of `toLp 2 (z,y)`. -/
lemma toLp_norm_sq (p : G × ℝ) :
    ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖ ^ 2 = ‖p.fst‖ ^ 2 + p.snd ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp

/-- `toLp` preserves the norm up to the factor `2` (the product norm is the max-norm). -/
lemma norm_le_toLp_norm (p : G × ℝ) :
    ‖p‖ ≤ ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖ := by
  have h := toLp_norm_sq p
  rw [Prod.norm_def, Real.norm_eq_abs]
  refine max_le ?_ ?_
  · have h2 : ‖p.fst‖ ^ 2 ≤ ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖ ^ 2 := by
      rw [h]; nlinarith [sq_nonneg p.snd]
    calc ‖p.fst‖ = Real.sqrt (‖p.fst‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖ ^ 2) := Real.sqrt_le_sqrt h2
      _ = ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖ := Real.sqrt_sq (norm_nonneg _)
  · have h2 : p.snd ^ 2 ≤ ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖ ^ 2 := by
      rw [h]; nlinarith [sq_nonneg ‖p.fst‖]
    calc |p.snd| = Real.sqrt (p.snd ^ 2) := (Real.sqrt_sq_eq_abs p.snd).symm
      _ ≤ Real.sqrt (‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖ ^ 2) := Real.sqrt_le_sqrt h2
      _ = ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖ := Real.sqrt_sq (norm_nonneg _)

lemma toLp_norm_le (p : G × ℝ) :
    ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖ ≤ 2 * ‖p‖ := by
  have h1 : ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖ ^ 2 = ‖p.fst‖ ^ 2 + p.snd ^ 2 := toLp_norm_sq p
  have hmax1 : ‖p.fst‖ ≤ ‖p‖ := by rw [Prod.norm_def, Real.norm_eq_abs]; exact le_max_left _ _
  have hmax2 : |p.snd| ≤ ‖p‖ := by rw [Prod.norm_def, Real.norm_eq_abs]; exact le_max_right _ _
  have h2 : ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖ ^ 2 ≤ (2 * ‖p‖) ^ 2 := by
    have hA : p.snd ^ 2 ≤ ‖p‖ ^ 2 := by
      rw [← sq_abs p.snd]; exact pow_le_pow_left₀ (abs_nonneg _) hmax2 2
    have hB : ‖p.fst‖ ^ 2 ≤ ‖p‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hmax1 2
    rw [h1]; nlinarith
  calc ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖
      = Real.sqrt (‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((2 * ‖p‖) ^ 2) := Real.sqrt_le_sqrt h2
    _ = 2 * ‖p‖ := Real.sqrt_sq (by positivity)

/-- The chain rule for the composition with `toLp`, first order. -/
lemma fderiv_comp_toLp (g : WithLp 2 (G × ℝ) → ℝ) (p v : G × ℝ)
    (hg : DifferentiableAt ℝ g (WithLp.toLp 2 p)) :
    fderiv ℝ (fun p' : G × ℝ => g (WithLp.toLp 2 p')) p v
      = fderiv ℝ g (WithLp.toLp 2 p) (WithLp.toLp 2 v) := by
  have hL : HasFDerivAt (WithLp.toLp 2 : G × ℝ → WithLp 2 (G × ℝ))
      ((WithLp.prodContinuousLinearEquiv 2 ℝ G ℝ).symm.toContinuousLinearMap) p :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ G ℝ).symm.hasFDerivAt
  have hcomp : HasFDerivAt (fun p' : G × ℝ => g (WithLp.toLp 2 p'))
      ((fderiv ℝ g (WithLp.toLp 2 p)).comp
        ((WithLp.prodContinuousLinearEquiv 2 ℝ G ℝ).symm.toContinuousLinearMap)) p :=
    hg.hasFDerivAt.comp p hL
  have hmain : fderiv ℝ (fun p' : G × ℝ => g (WithLp.toLp 2 p')) p
      = (fderiv ℝ g (WithLp.toLp 2 p)).comp
        ((WithLp.prodContinuousLinearEquiv 2 ℝ G ℝ).symm.toContinuousLinearMap) := by
    simpa [Function.comp_def] using hcomp.fderiv
  rw [hmain]
  simp only [ContinuousLinearMap.comp_apply]
  rfl

/-- The chain rule for the composition with `toLp`, second order. -/
lemma fderiv_fderiv_comp_toLp (g : WithLp 2 (G × ℝ) → ℝ) (hg : ContDiff ℝ 2 g)
    (p v w : G × ℝ) :
    fderiv ℝ (fderiv ℝ (fun p' : G × ℝ => g (WithLp.toLp 2 p'))) p v w
      = fderiv ℝ (fderiv ℝ g) (WithLp.toLp 2 p) (WithLp.toLp 2 v) (WithLp.toLp 2 w) := by
  have h1 := Commons.Analysis.Calculus.fderiv_fderiv_comp_continuousLinearMap
    ((WithLp.prodContinuousLinearEquiv 2 ℝ G ℝ).symm.toContinuousLinearMap) g hg p v w
  simpa [Function.comp_def] using h1

/-- The derivative of the evaluated first derivative: `fderiv (fun q => fderiv F q w) p u
= (fderiv (fderiv F) p u) w`. -/
lemma fderiv_fderiv_eval (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (w u p : G × ℝ) :
    fderiv ℝ (fun q : G × ℝ => fderiv ℝ F q w) p u
      = (fderiv ℝ (fderiv ℝ F) p u) w := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p := by
    have h : ContDiffAt ℝ 1 (fderiv ℝ F) p := hF.contDiffAt.fderiv_right (by norm_num)
    exact h.differentiableAt (by norm_num)
  have hconst : DifferentiableAt ℝ (fun _ : G × ℝ => w) p := differentiableAt_const w
  rw [fderiv_clm_apply (c := (fderiv ℝ F : G × ℝ → (G × ℝ) →L[ℝ] ℝ))
    (u := fun _ : G × ℝ => w) hd hconst]
  simp

/-- The slice `z ↦ F (z,y)` of `F`. -/
noncomputable def slicePot (F : G × ℝ → ℝ) (y : ℝ) : G → ℝ := fun z => F (z, y)

/-- The partial `y`-derivative of `F` at fixed `y`, as a function of `z`. -/
noncomputable def mixPot (F : G × ℝ → ℝ) (y : ℝ) : G → ℝ := fun z => dY F (z, y)

lemma contDiff_slicePot (F : G × ℝ → ℝ) (y : ℝ) (n : ℕ) (hF : ContDiff ℝ n F) :
    ContDiff ℝ n (slicePot F y) :=
  hF.comp (by fun_prop)

lemma fderiv_slicePot (F : G × ℝ → ℝ) (y : ℝ) (z v : G)
    (hF : DifferentiableAt ℝ F (z, y)) :
    fderiv ℝ (slicePot F y) z v = fderiv ℝ F (z, y) (v, 0) := by
  have h1 : HasFDerivAt (fun z' : G => (z', y)) (ContinuousLinearMap.inl ℝ G ℝ) z := by
    have h := (ContinuousLinearMap.inl ℝ G ℝ).hasFDerivAt (x := z)
    have h2 := h.add_const ((0 : G), y)
    have h3 : (fun z' : G => (z', y))
        = (fun z' : G => ContinuousLinearMap.inl ℝ G ℝ z' + ((0:G), y)) := by
      funext z'; simp
    rw [h3]
    exact h2
  have h2 : HasFDerivAt (slicePot F y)
      ((fderiv ℝ F (z, y)).comp (ContinuousLinearMap.inl ℝ G ℝ)) z :=
    hF.hasFDerivAt.comp z h1
  have hmain : fderiv ℝ (slicePot F y) z
      = (fderiv ℝ F (z, y)).comp (ContinuousLinearMap.inl ℝ G ℝ) := h2.fderiv
  rw [hmain]
  rfl

lemma fderiv_fderiv_slicePot (F : G × ℝ → ℝ) (y : ℝ) (hF : ContDiff ℝ 2 F) (z v w : G) :
    fderiv ℝ (fderiv ℝ (slicePot F y)) z v w = fderiv ℝ (fderiv ℝ F) (z, y) (v, 0) (w, 0) := by
  have hshift : ContDiff ℝ 2 (fun q : G × ℝ => F (q + ((0:G), y))) := hF.comp (by fun_prop)
  have hfun : slicePot F y = fun z' : G =>
      (fun q : G × ℝ => F (q + ((0:G), y))) (ContinuousLinearMap.inl ℝ G ℝ z') := by
    funext z'; simp [slicePot]
  have h1 := Commons.Analysis.Calculus.fderiv_fderiv_comp_continuousLinearMap
    (ContinuousLinearMap.inl ℝ G ℝ) (fun q : G × ℝ => F (q + ((0:G), y))) hshift z v w
  have h2 := Commons.Analysis.Calculus.fderiv_fderiv_comp_add F hF ((0:G), y) (z, 0) (v, 0) (w, 0)
  rw [hfun, h1]
  rw [show (ContinuousLinearMap.inl ℝ G ℝ) z = (z, 0) from rfl,
    show (ContinuousLinearMap.inl ℝ G ℝ) v = (v, 0) from rfl,
    show (ContinuousLinearMap.inl ℝ G ℝ) w = (w, 0) from rfl, h2]
  simp

lemma fderiv_mixPot (F : G × ℝ → ℝ) (y : ℝ) (hF : ContDiff ℝ 2 F) (z v : G) :
    fderiv ℝ (mixPot F y) z v = fderiv ℝ (fderiv ℝ F) (z, y) (v, 0) (0, 1) := by
  have h1 : HasFDerivAt (fun z' : G => (z', y)) (ContinuousLinearMap.inl ℝ G ℝ) z := by
    have h := (ContinuousLinearMap.inl ℝ G ℝ).hasFDerivAt (x := z)
    have h2 := h.add_const ((0 : G), y)
    have h3 : (fun z' : G => (z', y))
        = (fun z' : G => ContinuousLinearMap.inl ℝ G ℝ z' + ((0:G), y)) := by
      funext z'; simp
    rw [h3]
    exact h2
  have hdL : DifferentiableAt ℝ (fun q : G × ℝ => fderiv ℝ F q (0,1)) (z, y) :=
    ((contDiff_dY F hF).contDiffAt).differentiableAt (by norm_num)
  have hfun : mixPot F y = (fun q : G × ℝ => fderiv ℝ F q (0,1)) ∘ (fun z' : G => (z', y)) := rfl
  have hcomp : fderiv ℝ (mixPot F y) z
      = (fderiv ℝ (fun q : G × ℝ => fderiv ℝ F q (0,1)) (z,y)).comp
        (ContinuousLinearMap.inl ℝ G ℝ) := by
    rw [hfun, fderiv_comp z hdL h1.differentiableAt, h1.fderiv]
  rw [hcomp]
  simp only [ContinuousLinearMap.comp_apply]
  exact fderiv_fderiv_eval F hF (0, 1) (v, 0) (z, y)

/-- The `toLp`-transfer of convexity of `f - π‖·‖²`. -/
lemma convexOn_comp_toLp (f : WithLp 2 (G × ℝ) → ℝ)
    (h : ConvexOn ℝ Set.univ (fun x => f x - Real.pi * ‖x‖ ^ 2)) :
    ConvexOn ℝ Set.univ
      (fun p : G × ℝ => f (WithLp.toLp 2 p) - Real.pi * (‖p.fst‖ ^ 2 + p.snd ^ 2)) := by
  have h1 : ConvexOn ℝ Set.univ
      ((fun x : WithLp 2 (G × ℝ) => f x - Real.pi * ‖x‖ ^ 2) ∘ (WithLp.toLp 2)) :=
    h.comp_linearMap ((WithLp.prodContinuousLinearEquiv 2 ℝ G ℝ).symm.toLinearEquiv.toLinearMap)
  refine h1.congr ?_
  intro p _
  simp only [Function.comp_apply, toLp_norm_sq]

/-- The `toLp`-transfer of the growth hypotheses on the potential. -/
lemma growth_comp_toLp (f : WithLp 2 (G × ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : WithLp 2 (G × ℝ),
      |fderiv ℝ f x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ f) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ (fun p' : G × ℝ => f (WithLp.toLp 2 p')) p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ (fun p' : G × ℝ => f (WithLp.toLp 2 p'))) p v v|
        ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2 := by
  obtain ⟨C, hC0, N, hCN⟩ := hgf
  refine ⟨C * 2 ^ N * 4, by positivity, N, fun p v => ⟨?_, ?_⟩⟩
  · rw [fderiv_comp_toLp f p v (hf.contDiffAt.differentiableAt (by norm_num))]
    have h1 := (hCN (WithLp.toLp 2 p) (WithLp.toLp 2 v)).1
    have h2 : (1 + ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖) ^ N ≤ 2 ^ N * (1 + ‖p‖) ^ N := by
      have h3 : ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖ ≤ 2 * ‖p‖ := toLp_norm_le p
      have h5 : 1 + ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖ ≤ 2 * (1 + ‖p‖) := by linarith
      calc (1 + ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖) ^ N ≤ (2 * (1 + ‖p‖)) ^ N :=
            pow_le_pow_left₀ (by positivity) h5 N
        _ = 2 ^ N * (1 + ‖p‖) ^ N := by rw [mul_pow]
    have h6 : ‖(WithLp.toLp 2 v : WithLp 2 (G × ℝ))‖ ≤ 2 * ‖v‖ := toLp_norm_le v
    calc |fderiv ℝ f (WithLp.toLp 2 p) (WithLp.toLp 2 v)|
        ≤ C * (1 + ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖) ^ N
            * ‖(WithLp.toLp 2 v : WithLp 2 (G × ℝ))‖ := h1
      _ ≤ C * (2 ^ N * (1 + ‖p‖) ^ N) * (2 * ‖v‖) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left h2 hC0) h6 (norm_nonneg _) ?_
            positivity
      _ = C * 2 ^ N * (1 + ‖p‖) ^ N * ‖v‖ * 2 := by ring
      _ ≤ C * 2 ^ N * 4 * (1 + ‖p‖) ^ N * ‖v‖ := by
            have hX : (0:ℝ) ≤ C * 2 ^ N * (1 + ‖p‖) ^ N * ‖v‖ := by positivity
            linarith
  · rw [fderiv_fderiv_comp_toLp f hf p v v]
    have h1 := (hCN (WithLp.toLp 2 p) (WithLp.toLp 2 v)).2
    have h2 : (1 + ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖) ^ N ≤ 2 ^ N * (1 + ‖p‖) ^ N := by
      have h3 : ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖ ≤ 2 * ‖p‖ := toLp_norm_le p
      have h5 : 1 + ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖ ≤ 2 * (1 + ‖p‖) := by linarith
      calc (1 + ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖) ^ N ≤ (2 * (1 + ‖p‖)) ^ N :=
            pow_le_pow_left₀ (by positivity) h5 N
        _ = 2 ^ N * (1 + ‖p‖) ^ N := by rw [mul_pow]
    have h6 : ‖(WithLp.toLp 2 v : WithLp 2 (G × ℝ))‖ ^ 2 ≤ (2 * ‖v‖) ^ 2 := by
      have := toLp_norm_le v
      nlinarith [norm_nonneg (WithLp.toLp 2 v : WithLp 2 (G × ℝ)), norm_nonneg v]
    calc |fderiv ℝ (fderiv ℝ f) (WithLp.toLp 2 p) (WithLp.toLp 2 v) (WithLp.toLp 2 v)|
        ≤ C * (1 + ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖) ^ N
            * ‖(WithLp.toLp 2 v : WithLp 2 (G × ℝ))‖ ^ 2 := h1
      _ ≤ C * (2 ^ N * (1 + ‖p‖) ^ N) * (2 * ‖v‖) ^ 2 := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left h2 hC0) h6 (by positivity) ?_
            positivity
      _ = C * 2 ^ N * (1 + ‖p‖) ^ N * ‖v‖ ^ 2 * 4 := by ring
      _ = C * 2 ^ N * 4 * (1 + ‖p‖) ^ N * ‖v‖ ^ 2 := by ring

/-- The `toLp`-transfer of the growth hypotheses on the test function. -/
lemma growth_comp_toLp_h (h : WithLp 2 (G × ℝ) → ℝ) (hh : ContDiff ℝ 1 h)
    (hgh : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : WithLp 2 (G × ℝ),
      |h x| ≤ C * (1 + ‖x‖) ^ N ∧ |fderiv ℝ h x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |h (WithLp.toLp 2 p)| ≤ C * (1 + ‖p‖) ^ N ∧
      |fderiv ℝ (fun p' : G × ℝ => h (WithLp.toLp 2 p')) p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ := by
  obtain ⟨C, hC0, N, hCN⟩ := hgh
  refine ⟨C * 2 ^ N * 2, by positivity, N, fun p v => ⟨?_, ?_⟩⟩
  · have h1 := (hCN (WithLp.toLp 2 p) (0 : WithLp 2 (G × ℝ))).1
    have h2 : (1 + ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖) ^ N ≤ 2 ^ N * (1 + ‖p‖) ^ N := by
      have h3 : ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖ ≤ 2 * ‖p‖ := toLp_norm_le p
      have h5 : 1 + ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖ ≤ 2 * (1 + ‖p‖) := by linarith
      calc (1 + ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖) ^ N ≤ (2 * (1 + ‖p‖)) ^ N :=
            pow_le_pow_left₀ (by positivity) h5 N
        _ = 2 ^ N * (1 + ‖p‖) ^ N := by rw [mul_pow]
    calc |h (WithLp.toLp 2 p)| ≤ C * (1 + ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖) ^ N := h1
      _ ≤ C * (2 ^ N * (1 + ‖p‖) ^ N) := mul_le_mul_of_nonneg_left h2 hC0
      _ = C * 2 ^ N * (1 + ‖p‖) ^ N := by ring
      _ ≤ C * 2 ^ N * 2 * (1 + ‖p‖) ^ N := by
            have hX : (0:ℝ) ≤ C * 2 ^ N * (1 + ‖p‖) ^ N := by positivity
            linarith
  · rw [fderiv_comp_toLp h p v (hh.contDiffAt.differentiableAt (by norm_num))]
    have h1 := (hCN (WithLp.toLp 2 p) (WithLp.toLp 2 v)).2
    have h2 : (1 + ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖) ^ N ≤ 2 ^ N * (1 + ‖p‖) ^ N := by
      have h3 : ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖ ≤ 2 * ‖p‖ := toLp_norm_le p
      have h5 : 1 + ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖ ≤ 2 * (1 + ‖p‖) := by linarith
      calc (1 + ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖) ^ N ≤ (2 * (1 + ‖p‖)) ^ N :=
            pow_le_pow_left₀ (by positivity) h5 N
        _ = 2 ^ N * (1 + ‖p‖) ^ N := by rw [mul_pow]
    have h6 : ‖(WithLp.toLp 2 v : WithLp 2 (G × ℝ))‖ ≤ 2 * ‖v‖ := toLp_norm_le v
    calc |fderiv ℝ h (WithLp.toLp 2 p) (WithLp.toLp 2 v)|
        ≤ C * (1 + ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖) ^ N
            * ‖(WithLp.toLp 2 v : WithLp 2 (G × ℝ))‖ := h1
      _ ≤ C * (2 ^ N * (1 + ‖p‖) ^ N) * (2 * ‖v‖) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left h2 hC0) h6 (norm_nonneg _) ?_
            positivity
      _ = C * 2 ^ N * 2 * (1 + ‖p‖) ^ N * ‖v‖ := by ring

/-- The `toLp`-transfer of the Hessian bound `D²f ⪰ 2π·Id`. -/
lemma hessian_comp_toLp (f : WithLp 2 (G × ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (hH : ∀ x v : WithLp 2 (G × ℝ), 2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v) :
    ∀ p v : G × ℝ, 2 * Real.pi * ‖v‖ ^ 2
      ≤ fderiv ℝ (fderiv ℝ (fun p' : G × ℝ => f (WithLp.toLp 2 p'))) p v v := by
  intro p v
  rw [fderiv_fderiv_comp_toLp f hf p v v]
  have h1 : ‖v‖ ≤ ‖(WithLp.toLp 2 v : WithLp 2 (G × ℝ))‖ := norm_le_toLp_norm v
  have h2 : ‖v‖ ^ 2 ≤ ‖(WithLp.toLp 2 v : WithLp 2 (G × ℝ))‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg v) h1 2
  have h3 := hH (WithLp.toLp 2 p) (WithLp.toLp 2 v)
  nlinarith [Real.pi_pos]

/-- The `toLp`-transfer of the regularity of the potential. -/
lemma contDiff_comp_toLp (f : WithLp 2 (G × ℝ) → ℝ) (n : ℕ) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun p' : G × ℝ => f (WithLp.toLp 2 p')) :=
  hf.comp (((WithLp.prodContinuousLinearEquiv 2 ℝ G ℝ).symm.toContinuousLinearMap).contDiff)

/-- The coordinates of the gradient of a function on `WithLp 2 (G × ℝ)` are the slice gradient
and the partial `y`-derivative. -/
lemma grad_comp_toLp_coord (h : WithLp 2 (G × ℝ) → ℝ) (hh : ContDiff ℝ 1 h) (z : G) (y : ℝ) :
    (WithLp.ofLp (grad h (WithLp.toLp 2 (z,y)))).1
        = grad (slicePot (fun p : G × ℝ => h (WithLp.toLp 2 p)) y) z ∧
    (WithLp.ofLp (grad h (WithLp.toLp 2 (z,y)))).2
        = dY (fun p : G × ℝ => h (WithLp.toLp 2 p)) (z,y) := by
  set H : G × ℝ → ℝ := fun p => h (WithLp.toLp 2 p) with hHdef
  have hHcd : ContDiff ℝ 1 H := contDiff_comp_toLp h 1 hh
  have hchain : ∀ v : G × ℝ,
      fderiv ℝ h (WithLp.toLp 2 (z,y)) (WithLp.toLp 2 v) = fderiv ℝ H (z,y) v :=
    fun v => (fderiv_comp_toLp h (z,y) v (hh.contDiffAt.differentiableAt (by norm_num))).symm
  have hdH : DifferentiableAt ℝ H (z,y) := hHcd.contDiffAt.differentiableAt (by norm_num)
  constructor
  · refine ext_inner_right ℝ (fun v => ?_)
    have hstep : ⟪(WithLp.ofLp (grad h (WithLp.toLp 2 (z,y)))).1, v⟫_ℝ
        = ⟪grad h (WithLp.toLp 2 (z,y)), WithLp.toLp 2 (v, 0)⟫_ℝ := by
      rw [WithLp.prod_inner_apply]; simp
    rw [hstep, grad_spec, hchain (v, 0), ← fderiv_slicePot H y z v hdH, grad_spec]
  · have hstep : (WithLp.ofLp (grad h (WithLp.toLp 2 (z,y)))).2
        = ⟪grad h (WithLp.toLp 2 (z,y)), WithLp.toLp 2 ((0:G), 1)⟫_ℝ := by
      rw [WithLp.prod_inner_apply]; simp
    rw [hstep, grad_spec, hchain (0,1)]
    rfl

/-- The block form of the Hessian operator of a function on `WithLp 2 (G × ℝ)`. -/
lemma hessOp_block (f : WithLp 2 (G × ℝ) → ℝ) (hf : ContDiff ℝ 2 f) (z : G) (y : ℝ)
    (u : G) (t : ℝ) :
    hessOp f (WithLp.toLp 2 (z,y)) (WithLp.toLp 2 (u,t))
      = WithLp.toLp 2 (hessOp (slicePot (fun p : G × ℝ => f (WithLp.toLp 2 p)) y) z u
            + t • grad (mixPot (fun p : G × ℝ => f (WithLp.toLp 2 p)) y) z,
          ⟪u, grad (mixPot (fun p : G × ℝ => f (WithLp.toLp 2 p)) y) z⟫_ℝ
            + (fderiv ℝ (fderiv ℝ (fun p : G × ℝ => f (WithLp.toLp 2 p))) (z,y) (0,1) (0,1)) * t) := by
  set F : G × ℝ → ℝ := fun p => f (WithLp.toLp 2 p) with hFdef
  have hFcd : ContDiff ℝ 2 F := contDiff_comp_toLp f 2 hf
  have hsec : ∀ x w : G × ℝ, fderiv ℝ (fderiv ℝ f) (WithLp.toLp 2 (z,y)) (WithLp.toLp 2 x)
        (WithLp.toLp 2 w) = fderiv ℝ (fderiv ℝ F) (z,y) x w := by
    intro x w
    have h := fderiv_fderiv_comp_toLp f hf (z,y) x w
    rw [← h]
  have hsymm : ∀ a b : G × ℝ, fderiv ℝ (fderiv ℝ F) (z,y) a b = fderiv ℝ (fderiv ℝ F) (z,y) b a :=
    fun a b => hFcd.contDiffAt.isSymmSndFDerivAt (by simp) a b
  have hsplit : (u, t) = (u, 0) + t • ((0:G), (1:ℝ)) := by ext <;> simp
  have hcoord1 : (WithLp.ofLp (hessOp f (WithLp.toLp 2 (z,y)) (WithLp.toLp 2 (u,t)))).1
      = hessOp (slicePot F y) z u + t • grad (mixPot F y) z := by
    refine ext_inner_right ℝ (fun w => ?_)
    have hstep : ⟪(WithLp.ofLp (hessOp f (WithLp.toLp 2 (z,y)) (WithLp.toLp 2 (u,t)))).1, w⟫_ℝ
        = ⟪hessOp f (WithLp.toLp 2 (z,y)) (WithLp.toLp 2 (u,t)), WithLp.toLp 2 (w, 0)⟫_ℝ := by
      rw [WithLp.prod_inner_apply]; simp
    rw [hstep, hessOp_spec, hsec (u, t) (w, 0), hsplit, map_add, map_smul,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    rw [← fderiv_fderiv_slicePot F y hFcd z u w, hsymm (0,1) (w,0), ← fderiv_mixPot F y hFcd z w]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, inner_add_left, inner_smul_left,
      starRingEnd_apply, star_trivial, hessOp_spec, grad_spec]
  have hcoord2 : (WithLp.ofLp (hessOp f (WithLp.toLp 2 (z,y)) (WithLp.toLp 2 (u,t)))).2
      = ⟪u, grad (mixPot F y) z⟫_ℝ
        + (fderiv ℝ (fderiv ℝ F) (z,y) (0,1) (0,1)) * t := by
    have hstep : (WithLp.ofLp (hessOp f (WithLp.toLp 2 (z,y)) (WithLp.toLp 2 (u,t)))).2
        = ⟪hessOp f (WithLp.toLp 2 (z,y)) (WithLp.toLp 2 (u,t)), WithLp.toLp 2 ((0:G), 1)⟫_ℝ := by
      rw [WithLp.prod_inner_apply]; simp
    rw [hstep, hessOp_spec, hsec (u, t) (0, 1), hsplit, map_add, map_smul,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    rw [← fderiv_mixPot F y hFcd z u,
      show (fderiv ℝ (mixPot F y) z) u = ⟪u, grad (mixPot F y) z⟫_ℝ from by
        rw [real_inner_comm, grad_spec],
      smul_eq_mul]
    ring
  have hofLp : WithLp.ofLp (hessOp f (WithLp.toLp 2 (z,y)) (WithLp.toLp 2 (u,t)))
      = (hessOp (slicePot F y) z u + t • grad (mixPot F y) z,
         ⟪u, grad (mixPot F y) z⟫_ℝ
           + (fderiv ℝ (fderiv ℝ F) (z,y) (0,1) (0,1)) * t) :=
    Prod.ext_iff.mpr ⟨hcoord1, hcoord2⟩
  rw [← WithLp.toLp_ofLp 2 (hessOp f (WithLp.toLp 2 (z,y)) (WithLp.toLp 2 (u,t))), hofLp]

/-- Symmetry of the inverse of a symmetric `2π`-dominated operator (in the form needed for the
Schur complement). -/
lemma hessInv_symm_aux {E₂ : Type*} [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
    (A Ainv : E₂ →ₗ[ℝ] E₂) (hAL : ∀ u, Ainv (A u) = u) (hAR : ∀ u, A (Ainv u) = u)
    (hAsym : ∀ u v, ⟪A u, v⟫_ℝ = ⟪u, A v⟫_ℝ) (u v : E₂) :
    ⟪Ainv u, v⟫_ℝ = ⟪u, Ainv v⟫_ℝ := by
  have h1 : ⟪Ainv u, v⟫_ℝ = ⟪Ainv u, A (Ainv v)⟫_ℝ := by rw [hAR v]
  have h2 : ⟪Ainv u, A (Ainv v)⟫_ℝ = ⟪A (Ainv u), Ainv v⟫_ℝ := (hAsym (Ainv u) (Ainv v)).symm
  have h3 : ⟪A (Ainv u), Ainv v⟫_ℝ = ⟪u, Ainv v⟫_ℝ := by rw [hAR u]
  rw [h1, h2, h3]

/-- **The energy of the inverse Hessian in Schur-complement form.**
For a function `f` on `WithLp 2 (G × ℝ)` with `D²f ⪰ 2π·Id` and a `C¹` function `h`, the energy
`⟪(D²f)⁻¹ ∇h, ∇h⟫` at `(z,y)` equals the energy of the slice Hessian plus the square of the
"Schur correction", divided by the Schur complement.

The functions `F`, `H` are the pullbacks of `f`, `h` along `WithLp.toLp 2`; they are passed as
parameters (with proofs that they are the pullbacks) to keep the statement readable. -/
lemma hessInv_energy_eq (f : WithLp 2 (G × ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (F : G × ℝ → ℝ) (hF : F = fun p : G × ℝ => f (WithLp.toLp 2 p))
    (hH : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (h : WithLp 2 (G × ℝ) → ℝ) (hh : ContDiff ℝ 1 h)
    (H : G × ℝ → ℝ) (hHh : H = fun p : G × ℝ => h (WithLp.toLp 2 p)) (z : G) (y : ℝ) :
    ⟪hessInv f (WithLp.toLp 2 (z,y)) (grad h (WithLp.toLp 2 (z,y))),
        grad h (WithLp.toLp 2 (z,y))⟫_ℝ
      = ⟪hessInv (slicePot F y) z (grad (slicePot H y) z), grad (slicePot H y) z⟫_ℝ
        + (dY H (z,y)
            - ⟪hessInv (slicePot F y) z (grad (mixPot F y) z), grad (slicePot H y) z⟫_ℝ) ^ 2
          / (fderiv ℝ (fderiv ℝ F) (z,y) (0,1) (0,1)
             - ⟪hessInv (slicePot F y) z (grad (mixPot F y) z),
                 grad (mixPot F y) z⟫_ℝ) := by
  have hFcd : ContDiff ℝ 2 F := by rw [hF]; exact contDiff_comp_toLp f 2 hf
  have hHcd : ContDiff ℝ 1 H := by rw [hHh]; exact contDiff_comp_toLp h 1 hh
  have hsl_cd : ContDiff ℝ 2 (slicePot F y) := contDiff_slicePot F y 2 hFcd
  -- the slice Hessian is injective
  have hFy_inj : Function.Injective (hessOp (slicePot F y) z) := by
    refine hessOp_injective _ z (fun v => ?_)
    have h1 := hH (z, y) (v, 0)
    rw [← fderiv_fderiv_slicePot F y hFcd z v v] at h1
    simpa using h1
  have hAL : ∀ u : G, hessInv (slicePot F y) z (hessOp (slicePot F y) z u) = u :=
    fun u => hessInv_left _ _ hFy_inj u
  have hAR : ∀ u : G, hessOp (slicePot F y) z (hessInv (slicePot F y) z u) = u :=
    fun u => hessInv_right _ _ hFy_inj u
  have hAsym : ∀ u v : G, ⟪hessOp (slicePot F y) z u, v⟫_ℝ
      = ⟪u, hessOp (slicePot F y) z v⟫_ℝ := fun u v => hessOp_symm _ hsl_cd z u v
  -- the quadratic form of the ambient Hessian
  have hquad : ∀ (v : G) (t : ℝ), 2 * Real.pi * (‖v‖ ^ 2 + t ^ 2)
      ≤ ⟪hessOp (slicePot F y) z v, v⟫_ℝ + 2 * t * ⟪grad (mixPot F y) z, v⟫_ℝ
        + (fderiv ℝ (fderiv ℝ F) (z,y) (0,1) (0,1)) * t ^ 2 := by
    intro v t
    have h1 := hH (z, y) (v, t)
    rw [hF] at h1
    have h3 : fderiv ℝ (fderiv ℝ (fun p : G × ℝ => f (WithLp.toLp 2 p))) (z,y) (v,t) (v,t)
        = ⟪hessOp (slicePot F y) z v, v⟫_ℝ + t * ⟪grad (mixPot F y) z, v⟫_ℝ
          + (⟪v, grad (mixPot F y) z⟫_ℝ
              + (fderiv ℝ (fderiv ℝ F) (z,y) (0,1) (0,1)) * t) * t := by
      rw [fderiv_fderiv_comp_toLp f hf (z,y) (v,t) (v,t)]
      have hspec : fderiv ℝ (fderiv ℝ f) (WithLp.toLp 2 (z,y)) (WithLp.toLp 2 (v,t))
            (WithLp.toLp 2 (v,t))
          = ⟪hessOp f (WithLp.toLp 2 (z,y)) (WithLp.toLp 2 (v,t)), WithLp.toLp 2 (v,t)⟫_ℝ :=
        (hessOp_spec (E := WithLp 2 (G × ℝ)) f _ _ _).symm
      rw [hspec, hessOp_block f hf z y v t, WithLp.prod_inner_apply]
      simp only [WithLp.ofLp_toLp, WithLp.toLp_fst, WithLp.toLp_snd, WithLp.ofLp_fst,
        WithLp.ofLp_snd, inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial,
        RCLike.inner_apply, hF]
      ring
    rw [h3] at h1
    have h4 : ⟪v, grad (mixPot F y) z⟫_ℝ = ⟪grad (mixPot F y) z, v⟫_ℝ :=
      (real_inner_comm v _).symm
    rw [h4] at h1
    linarith [h1]

  -- positivity of the Schur complement
  have hβ : 2 * Real.pi ≤ (fderiv ℝ (fderiv ℝ F) (z,y) (0,1) (0,1))
      - ⟪hessInv (slicePot F y) z (grad (mixPot F y) z), grad (mixPot F y) z⟫_ℝ := by
    have h1 := hquad (-(hessInv (slicePot F y) z (grad (mixPot F y) z))) 1
    have h2 : (hessOp (slicePot F y) z) (-(hessInv (slicePot F y) z (grad (mixPot F y) z)))
        = -(grad (mixPot F y) z) := by
      rw [map_neg, hAR (grad (mixPot F y) z)]
    rw [h2] at h1
    simp only [inner_neg_left, inner_neg_right, neg_neg, mul_one, one_pow] at h1
    have hsym := hessInv_symm_aux _ _ hAL hAR hAsym (grad (mixPot F y) z) (grad (mixPot F y) z)
    have hpi : (0:ℝ) < 2 * Real.pi := by positivity
    nlinarith [h1, sq_nonneg ‖(hessInv (slicePot F y) z (grad (mixPot F y) z))‖, hsym]
  have hs : (fderiv ℝ (fderiv ℝ F) (z,y) (0,1) (0,1))
      - ⟪hessInv (slicePot F y) z (grad (mixPot F y) z), grad (mixPot F y) z⟫_ℝ ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by positivity : (0:ℝ) < 2 * Real.pi) hβ)
  -- the ambient Hessian is injective
  have hfinj : Function.Injective (hessOp f (WithLp.toLp 2 (z,y))) := by
    refine hessOp_injective _ _ (fun w => ?_)
    obtain ⟨v, rfl⟩ : ∃ v : G × ℝ, WithLp.toLp 2 v = w := ⟨WithLp.ofLp w, WithLp.toLp_ofLp 2 w⟩
    have h1 := hH (z, y) v
    rw [hF] at h1
    rw [fderiv_fderiv_comp_toLp f hf (z,y) v v] at h1
    have h3 : ‖(WithLp.toLp 2 v : WithLp 2 (G × ℝ))‖ ^ 2 = ‖v.1‖ ^ 2 + v.2 ^ 2 := toLp_norm_sq v
    rwa [h3]
  -- coordinates of the gradient
  have hcoordg := grad_comp_toLp_coord h hh z y
  have hw : WithLp.toLp 2 (grad (slicePot H y) z, dY H (z,y)) = grad h (WithLp.toLp 2 (z,y)) := by
    have h1 : WithLp.ofLp (grad h (WithLp.toLp 2 (z,y))) = (grad (slicePot H y) z, dY H (z,y)) := by
      rw [hHh]
      exact Prod.ext_iff.mpr ⟨hcoordg.1, hcoordg.2⟩
    rw [← WithLp.toLp_ofLp 2 (grad h (WithLp.toLp 2 (z,y))), h1]
  set X := hessInv f (WithLp.toLp 2 (z,y)) (grad h (WithLp.toLp 2 (z,y))) with hXdef
  -- the Schur identity
  have hblock : ∀ (u : G) (t : ℝ),
      (hessOp f (WithLp.toLp 2 (z,y))).toLinearMap (WithLp.toLp 2 (u, t))
        = WithLp.toLp 2 ((hessOp (slicePot F y) z).toLinearMap u + t • grad (mixPot F y) z,
            ⟪u, grad (mixPot F y) z⟫_ℝ
              + (fderiv ℝ (fderiv ℝ F) (z,y) (0,1) (0,1)) * t) := by
    intro u t
    simpa [hF] using hessOp_block f hf z y u t
  have hv : (hessOp f (WithLp.toLp 2 (z,y))).toLinearMap
        (WithLp.toLp 2 ((WithLp.ofLp X).1, (WithLp.ofLp X).2))
      = WithLp.toLp 2 (grad (slicePot H y) z, dY H (z,y)) := by
    have h1 : (hessOp f (WithLp.toLp 2 (z,y)))
          (hessInv f (WithLp.toLp 2 (z,y)) (grad h (WithLp.toLp 2 (z,y))))
        = grad h (WithLp.toLp 2 (z,y)) :=
      hessInv_right f _ hfinj (grad h (WithLp.toLp 2 (z,y)))
    rw [← hXdef] at h1
    rw [WithLp.toLp_ofLp]
    exact h1.trans hw.symm
  have hschur := Commons.Analysis.InnerProductSpace.schur_block_energy
    (T := (hessOp f (WithLp.toLp 2 (z,y))).toLinearMap)
    (A := (hessOp (slicePot F y) z).toLinearMap) (Ainv := hessInv (slicePot F y) z)
    (b := grad (mixPot F y) z) (c := fderiv ℝ (fderiv ℝ F) (z,y) (0,1) (0,1))
    (v₁ := (WithLp.ofLp X).1) (w₁ := grad (slicePot H y) z)
    (v₂ := (WithLp.ofLp X).2) (w₂ := dY H (z,y))
    (fun u => hAL u) (fun u => hAR u) (fun u v => hAsym u v)
    (fun u v => hessInv_symm_aux _ _ hAL hAR hAsym u v)
    hblock hs hv
  rw [← hschur, ← hw]
  rw [WithLp.prod_inner_apply]
  simp only [WithLp.ofLp_toLp, WithLp.toLp_fst, WithLp.toLp_snd, WithLp.ofLp_fst,
    WithLp.ofLp_snd, RCLike.inner_apply, starRingEnd_apply, star_trivial]
  ring

/-- The Brascamp–Lieb inequality on the slice at height `y` of a potential `F` satisfying the
"coordinate" hypotheses of the product step. -/
lemma slice_BL (IH : BLon G) (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hH : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (hconv : ConvexOn ℝ Set.univ (fun p : G × ℝ => F p - Real.pi * (‖p.1‖ ^ 2 + p.2 ^ 2)))
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ F p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ F) p v v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2)
    (y : ℝ) (Gf : G → ℝ) (hGf : ContDiff ℝ 1 Gf)
    (hGgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ z v : G,
      |Gf z| ≤ C * (1 + ‖z‖) ^ N ∧ |fderiv ℝ Gf z v| ≤ C * (1 + ‖z‖) ^ N * ‖v‖) :
    (∫ z, Gf z ^ 2 * Real.exp (-(slicePot F y z)))
        - (∫ z, Gf z * Real.exp (-(slicePot F y z))) ^ 2 / (∫ z, Real.exp (-(slicePot F y z)))
      ≤ ∫ z, ⟪hessInv (slicePot F y) z (grad Gf z), grad Gf z⟫_ℝ
          * Real.exp (-(slicePot F y z)) := by
  refine IH (slicePot F y) Gf (contDiff_slicePot F y 2 hF) (fun z v => ?_) ?_ ?_ hGf hGgf
  · rw [fderiv_fderiv_slicePot F y hF z v v]
    have h1 := hH (z, y) (v, 0)
    simpa using h1
  · -- convexity of the slice potential
    have hsl : ConvexOn ℝ Set.univ (fun z : G => F (z, y) - Real.pi * (‖z‖ ^ 2 + y ^ 2)) := by
      refine ⟨convex_univ, ?_⟩
      intro z₁ _ z₂ _ a b ha hb hab
      have h1 := hconv.2 (show (z₁, y) ∈ Set.univ from Set.mem_univ _)
        (show (z₂, y) ∈ Set.univ from Set.mem_univ _) ha hb hab
      have h2 : (a • (z₁, y) + b • (z₂, y) : G × ℝ) = (a • z₁ + b • z₂, y) := by
        ext
        · simp
        · show a * y + b * y = y
          rw [← add_mul, hab, one_mul]
      rw [h2] at h1
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd] at h1
      nlinarith [h1, hab]
    have h3 := hsl.add_const (Real.pi * y ^ 2)
    refine h3.congr ?_
    intro z _
    simp only [Pi.add_apply, slicePot]
    ring
  · -- growth of the slice potential
    obtain ⟨C, hC0, N, hCN⟩ := hgf
    refine ⟨C * (2 + |y|) ^ N, by positivity, N, fun z v => ⟨?_, ?_⟩⟩
    · have h1 := (hCN (z, y) (v, 0)).1
      rw [fderiv_slicePot F y z v (hF.contDiffAt.differentiableAt (by norm_num))]
      have h2 : ‖(v, (0:ℝ))‖ = ‖v‖ := by simp
      have h5 : ‖(z, y)‖ ≤ ‖z‖ + |y| := norm_pair_le z y
      have h6 : (0:ℝ) ≤ 1 + ‖z‖ + |y| := by positivity
      have h4 : (1 + ‖z‖ + |y|) ^ N ≤ (2 + |y|) ^ N * (1 + ‖z‖) ^ N := by
        calc (1 + ‖z‖ + |y|) ^ N ≤ (1 + |y| + 1) ^ N * (1 + ‖z‖) ^ N :=
              pow_one_add_norm_add_abs_le z y N
          _ = (2 + |y|) ^ N * (1 + ‖z‖) ^ N := by ring
      calc |fderiv ℝ F (z, y) (v, 0)|
          ≤ C * (1 + ‖(z, y)‖) ^ N * ‖(v, (0:ℝ))‖ := h1
        _ ≤ C * (1 + ‖z‖ + |y|) ^ N * ‖v‖ := by
            rw [h2]
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg v)
            refine mul_le_mul_of_nonneg_left ?_ hC0
            have h5' : (1:ℝ) + ‖(z, y)‖ ≤ 1 + ‖z‖ + |y| := by linarith [h5]
            exact pow_le_pow_left₀ (by positivity) h5' N
        _ ≤ C * (2 + |y|) ^ N * (1 + ‖z‖) ^ N * ‖v‖ := by
            calc C * (1 + ‖z‖ + |y|) ^ N * ‖v‖
                ≤ C * ((2 + |y|) ^ N * (1 + ‖z‖) ^ N) * ‖v‖ := by
                  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg v)
                  exact mul_le_mul_of_nonneg_left h4 hC0
              _ = C * (2 + |y|) ^ N * (1 + ‖z‖) ^ N * ‖v‖ := by ring
    · have h1 := (hCN (z, y) (v, 0)).2
      rw [fderiv_fderiv_slicePot F y hF z v v]
      have h2 : ‖(v, (0:ℝ))‖ = ‖v‖ := by simp
      have h5 : ‖(z, y)‖ ≤ ‖z‖ + |y| := norm_pair_le z y
      have h4 : (1 + ‖z‖ + |y|) ^ N ≤ (2 + |y|) ^ N * (1 + ‖z‖) ^ N := by
        calc (1 + ‖z‖ + |y|) ^ N ≤ (1 + |y| + 1) ^ N * (1 + ‖z‖) ^ N :=
              pow_one_add_norm_add_abs_le z y N
          _ = (2 + |y|) ^ N * (1 + ‖z‖) ^ N := by ring
      calc |fderiv ℝ (fderiv ℝ F) (z, y) (v, 0) (v, 0)|
          ≤ C * (1 + ‖(z, y)‖) ^ N * ‖(v, (0:ℝ))‖ ^ 2 := h1
        _ ≤ C * (1 + ‖z‖ + |y|) ^ N * ‖v‖ ^ 2 := by
            rw [h2]
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            refine mul_le_mul_of_nonneg_left ?_ hC0
            have h5' : (1:ℝ) + ‖(z, y)‖ ≤ 1 + ‖z‖ + |y| := by linarith [h5]
            exact pow_le_pow_left₀ (by positivity) h5' N
        _ ≤ C * (2 + |y|) ^ N * (1 + ‖z‖) ^ N * ‖v‖ ^ 2 := by
            calc C * (1 + ‖z‖ + |y|) ^ N * ‖v‖ ^ 2
                ≤ C * ((2 + |y|) ^ N * (1 + ‖z‖) ^ N) * ‖v‖ ^ 2 := by
                  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                  exact mul_le_mul_of_nonneg_left h4 hC0
              _ = C * (2 + |y|) ^ N * (1 + ‖z‖) ^ N * ‖v‖ ^ 2 := by ring

/-- The slice Hessian energy of a test function `A` at height `y`. -/
noncomputable def sliceEnergy (F : G × ℝ → ℝ) (y : ℝ) (A : G → ℝ) : ℝ :=
  ∫ z, ⟪hessInv (slicePot F y) z (grad A z), grad A z⟫_ℝ * Real.exp (-(slicePot F y z))

/-- The slice Hessian cross-energy of `A` and `B` at height `y`. -/
noncomputable def sliceCrossEnergy (F : G × ℝ → ℝ) (y : ℝ) (A B : G → ℝ) : ℝ :=
  ∫ z, ⟪hessInv (slicePot F y) z (grad A z), grad B z⟫_ℝ * Real.exp (-(slicePot F y z))

/-! ### Generic integral lemmas -/

/-- Linearity of the integral for a quadratic combination. -/
theorem integral_quad {α : Type*} [MeasurableSpace α] {μ : Measure α} (F G H : α → ℝ) (t : ℝ)
    (hF : Integrable F μ) (hG : Integrable G μ) (hH : Integrable H μ) :
    (∫ x, F x + 2 * t * (G x) + t ^ 2 * (H x) ∂μ)
      = (∫ x, F x ∂μ) + 2 * t * (∫ x, G x ∂μ) + t ^ 2 * (∫ x, H x ∂μ) := by
  have hI2 : Integrable ((2 * t) • G) μ := hG.const_mul (2 * t)
  have hI3 : Integrable ((t ^ 2) • H) μ := hH.const_mul (t ^ 2)
  have h1 := integral_add (hF.add hI2) hI3
  have h2 := integral_add hF hI2
  have h3 := integral_const_mul (μ := μ) (2 * t) G
  have h4 := integral_const_mul (μ := μ) (t ^ 2) H
  have key : (fun x : α => F x + 2 * t * (G x) + t ^ 2 * (H x))
      = fun x : α => (F + (2 * t) • G) x + ((t ^ 2) • H) x := by
    funext x; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [key, h1]
  rw [show (fun x : α => (F + (2 * t) • G) x) = fun x : α => F x + ((2 * t) • G) x from by
    funext x; simp only [Pi.add_apply]]
  rw [h2]
  rw [show (fun x : α => ((2 * t) • G) x) = fun x : α => 2 * t * G x from by
    funext x; simp only [Pi.smul_apply, smul_eq_mul]]
  rw [h3]
  rw [show (fun x : α => ((t ^ 2) • H) x) = fun x : α => t ^ 2 * H x from by
    funext x; simp only [Pi.smul_apply, smul_eq_mul]]
  rw [h4]

/-- Linearity of the integral for a linear combination. -/
theorem integral_lin {α : Type*} [MeasurableSpace α] {μ : Measure α} (F G w : α → ℝ) (t : ℝ)
    (h1 : Integrable (fun x => F x * w x) μ) (h2 : Integrable (fun x => G x * w x) μ) :
    (∫ x, (F x + t * G x) * w x ∂μ)
      = (∫ x, F x * w x ∂μ) + t * (∫ x, G x * w x ∂μ) := by
  have hI : Integrable (t • fun x => G x * w x) μ := h2.const_mul t
  have h := integral_add h1 hI
  have hkey : (fun x : α => (F x + t * G x) * w x)
      = fun x : α => F x * w x + (t • fun x => G x * w x) x := by
    funext x; simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [hkey, h]
  rw [show (fun a : α => (t • fun x : α => G x * w x) a) = fun a : α => t * (G a * w a) from by
    funext a; simp only [Pi.smul_apply, smul_eq_mul]]
  rw [integral_const_mul (μ := μ) t (fun a => G a * w a)]

/-- The quadratic expansion of the weighted variance. -/
theorem wVar_quad {α : Type*} [MeasureSpace α] (w A B : α → ℝ) (t : ℝ)
    (h1 : Integrable (fun x => A x ^ 2 * w x)) (h2 : Integrable (fun x => A x * B x * w x))
    (h3 : Integrable (fun x => B x ^ 2 * w x)) (h4 : Integrable (fun x => A x * w x))
    (h5 : Integrable (fun x => B x * w x)) :
    wVar w (fun x => A x + t * B x)
      = wVar w A + 2 * t * ((∫ x, A x * B x * w x)
          - (∫ x, A x * w x) * (∫ x, B x * w x) / (∫ x, w x))
        + t ^ 2 * wVar w B := by
  rw [wVar, wVar, wVar]
  rw [show (fun x => (A x + t * B x) ^ 2 * w x)
      = fun x => A x ^ 2 * w x + 2 * t * (A x * B x * w x) + t ^ 2 * (B x ^ 2 * w x) from by
    funext x; ring]
  rw [integral_quad (fun x => A x ^ 2 * w x) (fun x => A x * B x * w x)
    (fun x => B x ^ 2 * w x) t h1 h2 h3]
  rw [integral_lin (fun x => A x) (fun x => B x) w t h4 h5]
  by_cases hw : (∫ x, w x) = 0
  · simp only [hw, div_zero, sub_zero]
  · field_simp
    ring

/-! ### Slice linear algebra -/

lemma grad_add' (A B : G → ℝ) (z : G) (hA : DifferentiableAt ℝ A z)
    (hB : DifferentiableAt ℝ B z) : grad (A + B) z = grad A z + grad B z :=
  grad_add A B z hA hB

lemma grad_smul' (t : ℝ) (A : G → ℝ) (z : G) (hA : DifferentiableAt ℝ A z) :
    grad (t • A) z = t • grad A z := by
  have h1 : (t • A) = fun w : G => t * A w := rfl
  rw [h1, grad_const_mul t A z hA]

lemma grad_add_smul (A B : G → ℝ) (z : G) (t : ℝ) (hA : DifferentiableAt ℝ A z)
    (hB : DifferentiableAt ℝ B z) :
    grad (A + t • B) z = grad A z + t • grad B z := by
  rw [grad_add' A (t • B) z hA (hB.const_smul t), grad_smul' t B z hB]

lemma hessInv_lin (F : G × ℝ → ℝ) (y : ℝ) (z : G) (t : ℝ) (u v : G) :
    hessInv (slicePot F y) z (u + t • v)
      = hessInv (slicePot F y) z u + t • hessInv (slicePot F y) z v := by
  rw [map_add, map_smul]

lemma hessInv_slice_symm (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (y : ℝ) (z u v : G) :
    ⟪hessInv (slicePot F y) z u, v⟫_ℝ = ⟪u, hessInv (slicePot F y) z v⟫_ℝ := by
  refine hessInv_symm (slicePot F y) (contDiff_slicePot F y 2 hF) (fun z' w => ?_) z u v
  rw [fderiv_fderiv_slicePot F y hF z' w w]
  have h := hH2 (z', y) (w, 0)
  simpa using h

lemma sliceEnergy_add_smul (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (y : ℝ) (A B : G → ℝ) (t : ℝ)
    (hA : Differentiable ℝ A) (hB : Differentiable ℝ B)
    (hIntA : Integrable (fun z => ⟪hessInv (slicePot F y) z (grad A z), grad A z⟫_ℝ
      * Real.exp (-(slicePot F y z))))
    (hIntAB : Integrable (fun z => ⟪hessInv (slicePot F y) z (grad A z), grad B z⟫_ℝ
      * Real.exp (-(slicePot F y z))))
    (hIntB : Integrable (fun z => ⟪hessInv (slicePot F y) z (grad B z), grad B z⟫_ℝ
      * Real.exp (-(slicePot F y z)))) :
    sliceEnergy F y (A + t • B)
      = sliceEnergy F y A + 2 * t * sliceCrossEnergy F y A B + t ^ 2 * sliceEnergy F y B := by
  have hpt : ∀ z : G,
      ⟪hessInv (slicePot F y) z (grad (A + t • B) z), grad (A + t • B) z⟫_ℝ
        * Real.exp (-(slicePot F y z))
      = ⟪hessInv (slicePot F y) z (grad A z), grad A z⟫_ℝ * Real.exp (-(slicePot F y z))
        + 2 * t * (⟪hessInv (slicePot F y) z (grad A z), grad B z⟫_ℝ
            * Real.exp (-(slicePot F y z)))
        + t ^ 2 * (⟪hessInv (slicePot F y) z (grad B z), grad B z⟫_ℝ
            * Real.exp (-(slicePot F y z))) := by
    intro z
    rw [grad_add_smul A B z t (hA z) (hB z), hessInv_lin]
    have hsym : ⟪hessInv (slicePot F y) z (grad B z), grad A z⟫_ℝ
        = ⟪hessInv (slicePot F y) z (grad A z), grad B z⟫_ℝ := by
      rw [real_inner_comm (grad A z) (hessInv (slicePot F y) z (grad B z)),
        hessInv_slice_symm F hF hH2 y z (grad A z) (grad B z)]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      starRingEnd_apply, star_trivial]
    rw [hsym]
    ring
  rw [show sliceEnergy F y (A + t • B) =
      ∫ z, (fun z : G => ⟪hessInv (slicePot F y) z (grad A z), grad A z⟫_ℝ
              * Real.exp (-(slicePot F y z))) z
        + 2 * t * ((fun z : G => ⟪hessInv (slicePot F y) z (grad A z), grad B z⟫_ℝ
              * Real.exp (-(slicePot F y z))) z)
        + t ^ 2 * ((fun z : G => ⟪hessInv (slicePot F y) z (grad B z), grad B z⟫_ℝ
              * Real.exp (-(slicePot F y z))) z) from
    integral_congr_ae (Eventually.of_forall hpt)]
  rw [integral_quad (fun z : G => ⟪hessInv (slicePot F y) z (grad A z), grad A z⟫_ℝ
        * Real.exp (-(slicePot F y z)))
      (fun z : G => ⟪hessInv (slicePot F y) z (grad A z), grad B z⟫_ℝ
        * Real.exp (-(slicePot F y z)))
      (fun z : G => ⟪hessInv (slicePot F y) z (grad B z), grad B z⟫_ℝ
        * Real.exp (-(slicePot F y z))) t hIntA hIntAB hIntB]
  simp only [sliceEnergy, sliceCrossEnergy]


/-! ### The block structure of the second derivative -/

lemma fderiv_fderiv_block (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (z : G) (y : ℝ) (v : G) (t : ℝ) :
    fderiv ℝ (fderiv ℝ F) (z, y) (v, t) (v, t)
      = ⟪hessOp (slicePot F y) z v, v⟫_ℝ + 2 * t * ⟪grad (mixPot F y) z, v⟫_ℝ
        + (fderiv ℝ (fderiv ℝ F) (z, y) (0, 1) (0, 1)) * t ^ 2 := by
  set f' : WithLp 2 (G × ℝ) → ℝ := fun x => F (WithLp.ofLp x) with hf'def
  have hF' : ContDiff ℝ 2 f' := by
    rw [hf'def]
    exact hF.comp ((WithLp.prodContinuousLinearEquiv 2 ℝ G ℝ).toContinuousLinearMap.contDiff)
  have hFeq : F = fun p : G × ℝ => f' (WithLp.toLp 2 p) := by
    funext p
    rw [hf'def]
  have h1 : fderiv ℝ (fderiv ℝ F) (z, y) (v, t) (v, t)
      = fderiv ℝ (fderiv ℝ f') (WithLp.toLp 2 (z,y)) (WithLp.toLp 2 (v,t))
          (WithLp.toLp 2 (v,t)) := by
    rw [hFeq]
    exact fderiv_fderiv_comp_toLp f' hF' (z,y) (v,t) (v,t)
  rw [h1, ← hessOp_spec (E := WithLp 2 (G × ℝ)) f' (WithLp.toLp 2 (z,y))
    (WithLp.toLp 2 (v,t)) (WithLp.toLp 2 (v,t))]
  rw [hessOp_block f' hF' z y v t, WithLp.prod_inner_apply]
  rw [show (fun p : G × ℝ => f' (WithLp.toLp 2 p)) = F from hFeq.symm]
  simp only [WithLp.ofLp_toLp, WithLp.toLp_fst, WithLp.toLp_snd, WithLp.ofLp_fst,
    WithLp.ofLp_snd, inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial,
    RCLike.inner_apply]
  rw [real_inner_comm v (grad (mixPot F y) z)]
  ring


lemma schur_ge_two_pi (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (y : ℝ) (z : G) :
    2 * Real.pi ≤ fderiv ℝ (fderiv ℝ F) (z, y) (0, 1) (0, 1)
      - ⟪hessInv (slicePot F y) z (grad (mixPot F y) z), grad (mixPot F y) z⟫_ℝ := by
  have hFy_inj : Function.Injective (hessOp (slicePot F y) z) := by
    refine hessOp_injective _ z (fun v => ?_)
    have h1 := hH2 (z, y) (v, 0)
    rw [← fderiv_fderiv_slicePot F y hF z v v] at h1
    simpa using h1
  have hAR : ∀ u : G, hessOp (slicePot F y) z (hessInv (slicePot F y) z u) = u :=
    fun u => hessInv_right _ _ hFy_inj u
  have hquad : ∀ (v : G) (t : ℝ), 2 * Real.pi * (‖v‖ ^ 2 + t ^ 2)
      ≤ ⟪hessOp (slicePot F y) z v, v⟫_ℝ + 2 * t * ⟪grad (mixPot F y) z, v⟫_ℝ
        + (fderiv ℝ (fderiv ℝ F) (z, y) (0, 1) (0, 1)) * t ^ 2 := by
    intro v t
    have h1 := hH2 (z, y) (v, t)
    rwa [fderiv_fderiv_block F hF z y v t] at h1
  have h1 := hquad (-(hessInv (slicePot F y) z (grad (mixPot F y) z))) 1
  have h2 : hessOp (slicePot F y) z (-(hessInv (slicePot F y) z (grad (mixPot F y) z)))
      = -(grad (mixPot F y) z) := by
    rw [map_neg, hAR (grad (mixPot F y) z)]
  rw [h2] at h1
  simp only [inner_neg_left, inner_neg_right, neg_neg, mul_one, one_pow, norm_neg] at h1
  have hsym : ⟪hessInv (slicePot F y) z (grad (mixPot F y) z), grad (mixPot F y) z⟫_ℝ
      = ⟪grad (mixPot F y) z, hessInv (slicePot F y) z (grad (mixPot F y) z)⟫_ℝ :=
    hessInv_slice_symm F hF hH2 y z (grad (mixPot F y) z) (grad (mixPot F y) z)
  nlinarith [h1, sq_nonneg ‖hessInv (slicePot F y) z (grad (mixPot F y) z)‖, hsym, Real.pi_pos]



/-! ### STATUS / PLAN for the product step (updated)

**PROVED in this file** (all in the `Product` section unless stated):

* `bl_real : BLon ℝ` (the 1-dimensional base case, from the sharp 1D Brascamp–Lieb).
* Generic lemmas (before `BLon`): `grad_add`, `grad_const_mul`, `hessInv_symm`,
  `hessInv_norm_le` (`‖(D²f)⁻¹u‖ ≤ ‖u‖/(2π)`), `convexOn_tangent_le`.
* The `ℝ`-lemmas used by `bl_real`: `fderiv_fderiv_real`, `grad_real`, `hessOp_real`,
  `hessInv_real`, `convexOn_pi_norm_sq_real`, `tangent_le_of_convexOn`,
  `tendsto_pi_sq_add_linear`, `tendsto_pi_sq_add_linear_bot`,
  `integrable_poly_mul_exp_neg_of_coercive`.
* Ambient integrability on `G × ℝ`: `integrable_pow_mul_exp_neg_sq_prod`,
  `integrable_mul_exp_neg_potGrowth`, `volume_univ_pos`, `sliceMass_pos`
  (`0 < sliceMass F y` for any `PotGrowth F`).
* Slice energies: `sliceEnergy`, `sliceCrossEnergy`, `sliceEnergy_add_smul`
  (quadratic expansion in `t`), plus the generic `integral_quad`, `integral_lin`,
  `wVar_quad` (`wVar w (A + t•B) = wVar A + 2t·(cov-term) + t²·wVar B`).
* `fderiv_fderiv_block`: `D²F(z,y) (v,t) (v,t) = ⟪hessOp (slicePot F y) z v, v⟫
  + 2t⟪grad (mixPot F y) z, v⟫ + (D²F(z,y)(0,1)(0,1))·t²`.
* `schur_ge_two_pi`: `2π ≤ D²F(z,y)(0,1)(0,1) - ⟪hessInv (slicePot F y) z (grad (mixPot F y) z),
  grad (mixPot F y) z⟫` for all `z`.
* `condMean_const`, `condMean_sub`, `condMean_add`, `condMean_slice`.
* `grad_norm_eq` (`‖grad f x‖ = ‖fderiv ℝ f x‖`), `hess_polar_le` (the *polarized* Hessian bound
  from the diagonal bound — see the warning below), `grad_slicePot_growth`, `grad_mixPot_growth`.
* `continuous_ratio_slice` (the quotient `(∫ z, Φ (z,y) e^{-F(z,y)})/sliceMass F y` is continuous
  whenever `Φ` is continuous with polynomial growth — built on
  `continuousAt_sliceIntegral_of_valGrowth` + `ValGrowth_mul_exp_neg`), `continuous_condMean_of`,
  `continuous_condCov`, and **`contDiff_condMean`: `ContDiff ℝ 1 (condMean F H)`** — via
  `contDiff_one_iff_deriv`, with `hasDerivAt_condMean` supplying differentiability and
  `continuous_condCov`/`continuous_condMean_of` supplying the continuity of
  `deriv Ξ = condMean F (dY H) - condCov F H (dY F)`.
* `integrable_dYH`, `integrable_H_mul_dYF` (slice integrability of `dY H · e^{-F}` and
  `H · dY F · e^{-F}`), and — the analytic heart of the marginal step —
  `condMeanDeriv_mul_sliceMass`:
  `(condMean F (dY H) y - condCov F H (dY F) y) · W y
     = ∫ z, (dY H (z,y) - (H (z,y) - condMean F H y) · dY F (z,y)) e^{-F(z,y)}`,
  i.e. `Ξ' · W = ∫ φ e^{-F}` with `φ = dY H - (H - Ξ)·dY F` (the `Ξ'` here is the value supplied by
  `hasDerivAt_condMean`; the proof splits the right-hand side with `integral_add` +
  `integral_const_mul` and the first integral with `integral_sub`, then `field_simp`/`ring`).
* `condMeanDeriv_sq_mul_sliceMass_le`: `(Ξ')² · W ≤ ∫ z, φ² e^{-F(z,y)}` — Cauchy–Schwarz
  (`sq_integral_mul_le_integral_sq_mul_meas` with `b ≡ 1`) applied to the previous identity.
  Together with `margD2 F y ≥ 2π` this gives the `hud` integrability condition of the sharp
  1-dimensional inequality.
* `integrable_condMean_mul_sliceMass` (`Ξ · W` is integrable) and
  `integrable_condMean_sq_mul_sliceMass` (`Ξ² · W` is integrable) — the first half of the marginal
  integrability, done via `condMean_mul` / Cauchy–Schwarz plus `Integrable.integral_prod_right`
  on the ambient integrability of `H · e^{-F}` and `H² · e^{-F}`
  (`integrable_mul_exp_neg_potGrowth`).  They must be stated for the *ambient* measure on
  `G × ℝ` and then `rw [Measure.volume_eq_prod G ℝ]`-ed before `integral_prod_right`
  (and likewise before `aestronglyMeasurable_integral_prod_left'` for the a.e.-measurability).
* `integrable_slice_mul` (`Φ (·,y) · e^{-F (·,y)}` is integrable on the slice whenever `Φ` has
  polynomial growth) and `hasDerivAt_condMean`
  (`deriv (condMean F H) y = condMean F (dY H) y - condCov F H (dY F) y`) — the two workhorses of
  the marginal step.
* Slice decay: `hpt_bound`, `slice_integral_bound` (`|∫ z, Φ (z,y) e^{-F(z,y)}| ≤ C(1+|y|)^N e^{-πy²/4}`
  for polynomially bounded continuous `Φ`), and `integrable_slice_integral` (the same slice integral
  is integrable as a function of `y`) — these are the tools for the integrability conditions of the
  sharp 1D inequality.

**REMAINING** (the proof of `bl_product_step`).  Notation for a fixed height `y` (with
`W := sliceMass F y`, `Ξ := condMean F H`, `Φ(z) := d2Y F (z,y) - ⟪hessInv (slicePot F y) z
(grad (mixPot F y) z), grad (mixPot F y) z⟫`):
`A11 := sliceEnergy F y (fun z => H (z,y)) / W`, `A12 := sliceCrossEnergy F y (fun z => H (z,y))
(fun z => dY F (z,y)) / W`, `A22 := sliceEnergy F y (fun z => dY F (z,y)) / W`,
`B11 := condVar F H y`, `B12 := condCov F H (fun p => dY F p) y`, `B22 := condVar F (fun p => dY F p) y`.
Since `slicePot H y z = H (z,y)`, `mixPot F y z = dY F (z,y)` and `Var(e^{-slice})(Φ) = W·condVar ...`
(`condVar_mul`, `condCov_mul`), the quantities above are the normalised versions.

1. **`margD2` identity.**  `margD2 F y - (A22 - B22) = condMean F Φ y` (from `margD2_eq` =
   `condMean F (d2Y F) y - condVar F (dY F) y` and `condMean_sub`), and `Φ (z,y) ≥ 2π`
   (`schur_ge_two_pi`).  Hence, with `β := A22 - B22 ≥ 0` (`slice_BL` on `mixPot F y` alone),
   `2π ≤ margD2 F y`.  Consequence: `marg F = -log ∘ sliceMass` is convex with
   `0 < deriv (deriv (marg F)) y` (`deriv_deriv_marg`).
2. **Marginal (sharp 1D BL).**  Apply `brascamp_lieb_one_dim_sharp` to `V := marg F`,
   `u := Ξ := condMean F H`.  Needed: `ContDiff ℝ 2 (marg F)` (`contDiff_marg`), convexity,
   `0 < deriv (deriv (marg F))`, coercivity both ends (`tendsto_marg_atTop/atBot`, needs
   `hW : ∀ y, 0 < sliceMass F y`), `ContDiff ℝ 1 Ξ`, and the four integrability conditions
   `Ξ e^{-V}, Ξ² e^{-V}, Ξ²/V'' e^{-V}, (Ξ')²/V'' e^{-V}`.
   * `Ξ = B/W` with `B y = ∫ z, H (z,y) e^{-F(z,y)}`; `ContDiff ℝ 1 Ξ` from
     `contDiff_sliceMass` + `contDiff` of `B` (use `hasDerivAt_mixDeriv` +
     `continuousAt_sliceIntegral_of_valGrowth` on `mixDeriv F H`, and
     `contDiff_one_iff_deriv`).
   * `Ξ' = condMean F (fun p => dY H p) y - condCov F H (fun p => dY F p) y`
     (`quotient rule` + `hasDerivAt_mixDeriv` + `hasDerivAt_sliceMass`, `massDeriv_eq`).
   * `Integrable (fun y => Ξ y * W y)`: `Ξ y * W y = ∫ z, H (z,y) e^{-F(z,y)}` (`condMean_mul`)
     and `Integrable.integral_prod_right` applied to the ambient integrability of
     `H · e^{-F}` (`integrable_mul_exp_neg_potGrowth`).
   * `Integrable (fun y => Ξ y² * W y)`: bound `Ξ²W = B²/W ≤ A := ∫ z, H(z,y)²e^{-F(z,y)}`
     (Cauchy–Schwarz on the slice) and `Integrable A` by `integral_prod_right` +
     `integrable_mul_exp_neg_potGrowth`.
   * `Integrable (fun y => (Ξ')²/margD2 F y * W y)` (use `margD2 ≥ 2π`):
     `(Ξ')²W = (Ξ'W)²/W` and `Ξ'W = ∫ z, (dY H - (H - Ξ)·dY F) e^{-F}` (Cauchy–Schwarz with
     the centred `H - Ξ`), so `(Ξ')²W ≤ ∫ z, (dY H - (H-Ξ)dY F)² e^{-F}`, whose `y`-integral is
     finite because the slice integrals of polynomially bounded functions decay like
     `C(1+|y|)^N e^{-(π/4)y²}` (see the general domination lemma to be written, modelled on
     `integrable_of_le_gauss`/`tendsto_sliceMass_atTop_zero`).
2b. **Ambient integrability / Fubini for the marginal.**  `Ξ y * W y = ∫ z, H (z,y) e^{-F(z,y)}`
   (`condMean_mul`) and `Ξ y² * W y = B y²/W y ≤ ∫ z, H(z,y)² e^{-F(z,y)}` (Cauchy–Schwarz), so both
   `Integrable (fun y => Ξ y * W y)` and `Integrable (fun y => Ξ y² * W y)` follow from
   `Integrable.integral_prod_right` applied to the ambient integrability of `H · e^{-F}` and
   `H² · e^{-F}` (`integrable_mul_exp_neg_potGrowth`).  For `(Ξ')²` use the identity
   `Ξ' · W = ∫ z, (dY H - (H - Ξ) dY F) e^{-F}` and Cauchy–Schwarz, which gives
   `(Ξ')² W ≤ ∫ z, (dY H - (H-Ξ) dY F)² e^{-F}`.  [Both of these are now PROVED:
   `condMeanDeriv_mul_sliceMass` and `condMeanDeriv_sq_mul_sliceMass_le`.]  What is still missing
   for `hud` is the `y`-integrability of the right-hand side `∫ z, φ² e^{-F(z,y)}`: since
   `margD2 F y ≥ 2π`, `(Ξ')²/margD2 · W ≤ (Ξ')²W/(2π) ≤ (∫ z, φ² e^{-F})/(2π)`, and the
   `y`-integral of the right-hand side is finite by Tonelli (`φ² e^{-F} ≤ 2(dYH)²e^{-F}
   + 2(H-Ξ)²(dYF)²e^{-F}`; the first term is ambient-integrable, the second needs the polynomial
   growth of `Ξ` in `y` plus the `e^{-πy²/4}` slice decay of `∫ z, (dYF)²e^{-F}` —
   cf. `slice_integral_bound`/`integrable_slice_integral`).

   **How to get the polynomial growth of `Ξ` in `y`** (this is the one new ingredient; everything
   else in the `hud` chain is already in the file):
   * *Numerator*: `|∫ z, H (z,y) e^{-F(z,y)}| ≤ C (1+|y|)^{N_H} e^{-πy²/4}` — this is exactly
     `slice_integral_bound F hF hp (fun p => H p) hH.continuous C hC0 N (fun p => (hCH p).1) y`
     with `C, N` from `HGrowth H`.
   * *Denominator*: `sliceMass F y ≥ vol (ball 0 1) · exp (-(F 0 + C (2+|y|)^{N+1}))`, i.e.
     `log (sliceMass F y) ≥ -poly y`.  This needs an *upper* bound on `F`, which `PotGrowth F` does
     not supply but which is available in `bl_product_step` from `growth_comp_toLp`
     (`|fderiv ℝ F p v| ≤ C (1+‖p‖)^N ‖v‖`): for `‖z‖ ≤ 1`,
     `F (z,y) - F 0 = ∫_0^1 fderiv ℝ F (t • (z,y)) (z,y) dt ≤ C (1+‖(z,y)‖)^N ‖(z,y)‖ ≤
      C (2+|y|)^{N+1}`, then restrict the defining integral of `sliceMass` to the unit ball.
     (To be proved as `sliceMass_ge_exp`; the FTC along the ray
     `F p - F 0 = ∫_0^1 fderiv ℝ F (t • p) p dt` is the only real step, via the 1-D FTC
     `intervalIntegral.integral_deriv_eq_sub` applied to `t ↦ F (t • p)`.)
     **`sliceMass_ge_exp` IS NOW PROVED** (ported below, in the `Product` section): with
     `hF : ContDiff ℝ 2 F`, `hp : PotGrowth F`, and the gradient bound
     `hderiv : ∀ p v, |fderiv ℝ F p v| ≤ C (1+‖p‖)^N ‖v‖`, it gives
     `exp (-(F 0 + C (2+|y|)^{N+1})) * vol (ball 0 1) ≤ sliceMass F y`.  The proof is the FTC-free
     route: `Convex.norm_image_sub_le_of_norm_deriv_le` on `Set.Icc 0 1` applied to
     `t ↦ F (t • p)` (chain rule + `‖t • p‖ ≤ ‖p‖` for `t ≤ 1`) bounds `|F p - F 0|`, and the
     integral bound is then `MeasureTheory.integral_mono_of_nonneg` against the indicator of the
     unit ball (only `Integrable (e^{-F(·,y)})` from `integrable_of_le_gauss` is needed — this is
     why `PotGrowth F` is required after all, for that integrability, even though the analytic
     content does not use it).
     *(Historical note: an earlier partial proof of this lemma is in the workspace scratch
     `s16.lean`; the following description of its state is superseded.)*  The
     mean-value core `hup : ∀ z, ‖z‖ < 1 → F (z,y) ≤ F 0 + C (2+|y|)^{N+1}` is fully written
     (chain rule `HasDerivAt (t ↦ F (t • p)) (fderiv ℝ F (t • p) p) t` + the rescaled bound
     `‖t • p‖ ≤ ‖p‖` + `Convex.norm_image_sub_le_of_norm_deriv_le` on `Set.Icc 0 1` + the
     arithmetic `C (1+‖p‖)^N ‖p‖ ≤ C (2+|y|)^{N+1}`), and only the final integral assembly
     (`∫ z in ball, e^{-(F 0 + …)} ≤ ∫ z, e^{-F(z,y)}` via `setIntegral_mono_on` and
     `setIntegral_le_integral`) plus three small annotation fixes are outstanding — see the
     compiler errors in that file.  Note `sliceMass_ge_exp` does *not* need `PotGrowth F`.
   * *Conclusion*: since `e^{-πy²/4 + C(2+|y|)^{N+1}}` is bounded,
     `|Ξ y| ≤ C' (1+|y|)^{N_H}` is polynomial.  Then `∫ z, (H-Ξ)²(dYF)²e^{-F}` is a slice integral
     of a polynomially bounded function and its `y`-integral is finite by
     `integrable_slice_integral` (the `Ξ y` factor is a *constant* in `z`, so it is absorbed into
     the polynomial bound with a constant that grows polynomially in `y`).

   **!!! CORRECTION (important).**  The route sketched immediately below is WRONG and has been
   abandoned.  The step `C (2+t)^{N+1} ≤ (π/8) t² + K` is false for `N + 1 ≥ 3`, and so is the
   companion `exp (-(a t²) + b (2+t)^n) ≤ K` for `n ≥ 3`: a polynomial of degree `≥ 3` is not
   dominated by a quadratic.  Both delegated lemmas were correctly declared FALSE by the provers
   with counterexamples.  Consequently **`Ξ` need not be polynomially bounded in `y`** — the
   denominator lower bound `1/W y ≤ e^{F 0 + C (2+|y|)^{N+1}}` can outrun the numerator decay
   `e^{-πy²/4}` — and `condMean_growth` is NOT provable in general.

   **WHERE THIS LEAVES `hud` (open).**  A second attempt at avoiding `Ξ`'s growth also fails, and
   it is worth recording *why* so it is not retried: one would like to separate
   `(H-Ξ)² (dY F)² ≤ λ² (H-Ξ)² + (dY F)⁴/λ²` and then bound each piece by
   `integrable_slice_integral`.  That inequality is **FALSE** for every constant `λ > 0`
   (take `a := |H-Ξ|` large, `b := |dY F| ≥ 1` fixed: `a²b²` grows quadratically in `a` while
   `λ²a² + b⁴/λ²` is affine in `a²` — the same polynomial-degree obstruction that refuted the two
   Commons lemmas).  More generally `a²b²` is *not* bounded by `C(a² + b⁴)` for any constant `C`
   (take `b = 2`, `a → ∞`).
   So the honest state is: `(Ξ')²W ≤ ∫ z, φ² e^{-F}` is proved
   (`condMeanDeriv_sq_mul_sliceMass_le`), and what is missing is a genuine argument that
   `y ↦ ∫ z, φ² e^{-F(z,y)}` is integrable.  Naively this needs `Ξ` to grow slowly in `y`, and the
   crude lower bound `sliceMass F y ≥ vol (ball 0 1) · exp (-(F 0 + C (2+|y|)^{N+1}))` does *not*
   certify even polynomial growth when `N + 1 ≥ 3`.  Two things are therefore open:
   (a) whether `Ξ` really is polynomially bounded in `y` under `PotGrowth F` + the ℓ²-gradient
       bound (the crude bound cannot decide it; a concentration argument for the slice measures
       would), and
   (b) failing that, whether the integrability of `∫ z, φ² e^{-F}` can be obtained by a route that
       never separates `(H-Ξ)` from `dY F` (e.g. Tonelli in `y` first, or a Cauchy-Schwarz in `y`
       rather than in `z`).
   Do NOT reintroduce the `condMean_growth`/`poly_le_sq_add_const` step: it is unprovable as
   stated.

   **DIRECTION (b) — attempted, not yet closed.**  Attempts that never separate `(H-Ξ)` from
   `dY F`, and where each stops:
   * *Tonelli in `y` first* (`∫ y ∫ z φ²e^{-F} = ∫ z ∫ y φ²e^{-F}` by Tonelli, the integrand being
     nonnegative so no finiteness is needed to interchange): the inner integral is
     `∫ y (dY H (z,y) - (H (z,y) - Ξ(y)) dY F (z,y))² e^{-F(z,y)} dy`, and the `Ξ(y)` factor now
     forces `Ξ` to be square-integrable against the `y`-measure — a *different* unproved growth
     statement, not an escape.
   * *Centring `dY F` as well*: writing `Ξ' = ⟨dY H⟩ - ⟨(H-Ξ)(dY F - Ξ_G)⟩` with
     `Ξ_G := ⟨dY F⟩` and applying Cauchy-Schwarz **on the slice** gives
     `(Ξ')² ≤ 2⟨dY H⟩² + 2 V_z(H) V_z(dY F) ≤ 2⟨dY H⟩² + 2 A Ã₂ / W²`, hence
     `(Ξ')² W ≤ 2W⟨dY H⟩² + 2 A Ã₂/W` with `A := ∫ z H² e^{-F}`, `Ã₂ := ∫ z (dY F)² e^{-F}`.
     The first term is fine (`W⟨dY H⟩² ≤ ∫ z (dY H)²e^{-F}`, integrable in `y` by
     `integrable_slice_integral`); the second still carries `1/W`.
     **The quantity actually needed is therefore `Ã₂/W = ⟨(dY F)²⟩`, the conditional mean of
     `(dY F)²`** — and the useful reformulation of the open problem is: *is `⟨(dY F)²⟩` (and more
     generally `⟨(1+‖z‖)^{2N}⟩`) polynomially bounded in `y`?*  Note it is *not* the same as Ξ's
     growth but it is the same *kind* of question (a conditional mean against a possibly tiny `W`),
     and it is what a concentration argument would have to deliver.  Model check: for
     `F (z,y) = πz² + y⁴`, `H (z,y) = z²` (so `N ≈ 3`, the regime where the old route died),
     `Ã₂/W = 16y⁶` is polynomial and `A Ã₂/W` is integrable — so the statement is *not* obviously
     false, it is simply unproved.

   **STRATEGIC SUGGESTION for the next session.**  The statement of the auxiliary lemma
   `bl_prod_aux` (the `G × ℝ` form of the BL inequality that `bl_product_step` reduces to) is
   *ours to choose*.  Rather than blocking the whole development on this integrability question,
   state `bl_prod_aux` with the sharp-1D-inequality hypotheses (`Integrable (Ξ·W)`,
   `Integrable (Ξ²·W)`, `Integrable ((Ξ')²/margD2 · W)`, plus the slice growth conditions) as
   explicit *hypotheses*, and prove the body — the law of total variance, the slice Loewner
   inequality with `bl_combine`, the `a-b = ⟨φ⟩` / `α-β = ⟨s⟩` identifications, `condMean_sq_div_le`
   and the Fubini assembly all go through *unchanged* — since every one of them only ever uses those
   quantities through the hypotheses.  Then `bl_product_step` supplies them from the ambient
   hypotheses of `BLon`, and the integrability question above becomes a single isolated lemma with
   a precise statement, instead of a blocker for four other pieces of work.

   **THE SUPERSEDED ROUTE, kept only as a record of what not to do:**   **THE SUPERSEDED ROUTE, kept only as a record of what not to do:**
   **THE REMAINING ASSEMBLY (exact recipe; two lemmas).**

   (i) `condMean_growth`: `∃ C M, ∀ y, |condMean F H y| ≤ C * (1 + |y|)^M`.
       * Numerator: `|∫ z, H (z,y) e^{-F(z,y)}| ≤ C₁ (1+|y|)^{N₁} e^{-πy²/4}` — the direct
         instantiation of `slice_integral_bound` with `Φ := H`, `C₁, N₁` from `HGrowth H`.
       * Denominator: `sliceMass F y ≥ exp (-(F 0 + C (2+|y|)^{N+1})) * vol (ball 0 1)` —
         `sliceMass_ge_exp` (needs `ContDiff ℝ 2 F`, `PotGrowth F`, and the gradient bound of `F`).
       * Combine: `|Ξ y| ≤ (C₁ / vol (ball 0 1)) (1+|y|)^{N₁} exp (F 0 + C (2+|y|)^{N+1} - πy²/4)`,
         and the exponential factor is *bounded*: from `C (2+t)^{N+1} ≤ (π/8) t² + K` (an elementary
         polynomial-domination bound) the exponent is `≤ -(π/8) t² + K`, hence
         `≤ exp (F 0 + K)`.  So `|Ξ y| ≤ C (1+|y|)^{N₁}`.
   (ii) `integrable_slice_phi_sq`: `Integrable (fun y => ∫ z, φ² e^{-F(z,y)})` with
       `φ = dY H - (H - Ξ)·dY F` (where `Ξ = condMean F H y`).  By `integrable_slice_integral`
       it suffices that `z ↦ φ (z,y)²` has a bound `B (1+‖z‖+|y‖)^{M}` with `B` polynomial in `|y|`:
       `|φ| ≤ |dY H| + (|H| + |Ξ y|)|dY F|`, and `|Ξ y| ≤ C (1+|y|)^{N₁}` from (i).
   Then `hud` follows: `margD2 F y ≥ 2π` gives `(Ξ')²/margD2 · W ≤ (Ξ')²W/(2π) ≤
   (∫ z, φ²e^{-F})/(2π)` by `condMeanDeriv_sq_mul_sliceMass_le`, and (ii) makes that integrable.
   **The only ingredient in (i)/(ii) that is not yet in the file is the polynomial-domination
   estimate `C (2+t)^{N+1} ≤ (π/8) t² + K`.**  This (and its exponential corollary) has been
   delegated to the fleet as two generic Mathlib-level lemmas:
   * `Commons.Algebra.Order.poly_le_sq_add_const` (file
     `Submission/Commons/Algebra/Order/poly_le_sq_add_const.lean`) —
     `C ≥ 0 → ε > 0 → ∃ K, ∀ t ≥ 0, C * (2 + t) ^ (N + 1) ≤ ε * t ^ 2 + K`;
   * `Commons.Real.exp_neg_sq_add_pow_bounded` (file
     `Submission/Commons/Real/exp_neg_sq_add_pow_bounded.lean`) —
     `a > 0 → b ≥ 0 → ∃ K, ∀ t ≥ 0, Real.exp (-(a * t ^ 2) + b * (2 + t) ^ n) ≤ K`.
   Import them when they land and both (i) and (ii) are short assemblies of already-proved
   lemmas.  `ContDiff ℝ 1 Ξ` follows from
   `contDiff_one_iff_deriv`, `hasDerivAt_condMean` and the continuity of `condMean F (dY H)` and
   `condCov F H (dY F)` (slice-integral continuity, cf. `continuousAt_sliceIntegral_of_valGrowth`).

3. **Slice step (Loewner).**  *(Pieces already in place: `sliceEnergy_add_smul` and `wVar_quad`
   give the two quadratic expansions in `t`; `condVar_mul_sliceMass_eq`, `condCov_mul_sliceMass_eq`
   and `condVar_mixPot_mul_sliceMass_eq` move between the `wVar`-of-the-slice and
   `condVar`/`condCov` normalisations; `grad_slicePot_growth`/`grad_mixPot_growth` supply the
   growth hypotheses that `slice_BL` needs for the test function
   `fun z => slicePot H y z + t * mixPot F y z`; `integrable_slice_mul` gives the slice
   integrability hypotheses of `wVar_quad`.  What remains here is the bookkeeping that applies
   `slice_BL` to that test function for each `t`, rewrites both sides with the two expansions,
   divides by `sliceMass F y > 0`, and reads off `hquad : ∀ t, 0 ≤ α₁ + 2 b t + β t²`.)**  Apply `slice_BL` at the test function
   `Gf_t := slicePot H y + t • mixPot F y` for arbitrary `t`; expand both sides with
   `wVar_quad` and `sliceEnergy_add_smul`; divide by `W > 0` to obtain
   `hquad : ∀ t, 0 ≤ α₁ + 2 b t + β t²` with `α₁ := A11 - B11`, `b := A12 - B12`,
   `β := A22 - B22`.  Then `bl_combine` (or `bl_combine_zero` in the degenerate case `β = 0`)
   gives `a²/α - (a-b)²/(α-β) ≤ α₁` where `a := deriv Ξ y`, `α := margD2 F y`.
4. **Identification.**  `a - b = condMean F φ y` where
   `φ(z) := dY H (z,y) - ⟪hessInv (slicePot F y) z (grad (mixPot F y) z), grad (slicePot H y) z⟫`
   (uses `A12 = condMean F (fun p => ⟪...⟫) y` and `B12 = condCov F H (dY F) y` and the formula
   for `Ξ'`), and `α - β = condMean F Φ y`.  Conditional Cauchy–Schwarz
   (`condMean_sq_div_le`) gives `(a-b)²/(α-β) ≤ (∫ z, φ²/Φ · e^{-F(z,y)})/W`.
5. **Assembly.**  From steps 2–4 and the law of total variance `wVar_prod_eq`,
   `wVar (e^{-F}) H ≤ ∫ y, sliceEnergy F y (slicePot H y) + ∫ y, ∫ z, φ²/Φ · e^{-F(z,y)}`.
   Fubini transforms this into `∫ p, ⟪hessInv f (toLp p) (grad h (toLp p)), grad h (toLp p)⟫
   e^{-F p}` using `hessInv_energy_eq` pointwise (which states exactly that the ambient energy
   is the sum of the slice energy and the Schur correction term `φ²/Φ`).
   * `∫ y, sliceEnergy F y (slicePot H y) = ∫ p, ⟪hessInv (slicePot F y) p.1 (grad (slicePot H y) p.1),
     grad (slicePot H y) p.1⟫ e^{-F p}` by unfolding and `integral_prod_symm`.
**USEFUL REMARKS**

* `PotGrowth F` only bounds `dY F` and `d2Y F` (the `(0,1)` direction of `D²F`), *not* the full
  operator bound `‖D²F p‖`.  When the full bound is needed (growth of `grad (mixPot F y)`, i.e. of
  the Riesz vector of `fderiv (dY F)`, and the growth hypotheses of `slice_BL` for the test function
  `mixPot F y`), derive it from the *diagonal* bound by the parallelogram identity:
  `2·D²F(v,w) = D²F(v+w,v+w) - D²F(v,v) - D²F(w,w)` (symmetric bilinear form), which turns
  `|D²F p v v| ≤ C(1+‖p‖)^N ‖v‖²` into `‖D²F p‖ ≤ C'(1+‖p‖)^N`.  (Same for the ambient `f`.)
* `‖grad f x‖ = ‖fderiv ℝ f x‖` (the Riesz map is an isometry).
* **Do not write `‖fderiv ℝ (fderiv ℝ F) p‖` for `F : G × ℝ → ℝ`**: type-class synthesis for
  `Norm ((G × ℝ) →L ((G × ℝ) →L ℝ))` fails (the `InnerProductSpace ℝ G` instance diamond).
  Instead state the *polarized* (homogeneous bilinear) bound
  `∃ C' ≥ 0, ∀ p u w, |fderiv ℝ (fderiv ℝ F) p u w| ≤ C' * (1 + ‖p‖)^N * ‖u‖ * ‖w‖`,
  which is what the growth estimates actually need.  It is obtained from the diagonal bound by
  `2·B u w = B (u+w) (u+w) - B u u - B w w` (symmetry of the second derivative) together with the
  rescaling `(u,w) ↦ (t•u, t⁻¹•w)`, `t = √(‖w‖/‖u‖)` (both sides are homogeneous of degree 2).
  A draft of this lemma (`hess_polar_le`) is in the scratch file `s9.lean` in the workspace root
  (not yet debugging-free): the two remaining issues there are the `hpar` bookkeeping
  (`(B (u+w)) (u+w) = (B u) u + (B u) w + ((B w) u + (B w) w)` by `map_add`/`add_apply`, then
  `hsym w u`) and the final constant comparison `C ≤ 3C`, both mechanical.
* Integrability of the slice quantities is obtained from `integrable_of_le_gauss` (polynomial
  growth) and, for the `y`-direction, from `integrable_slice_integral` (decay like `e^{-πy²/4}`).

6. **`bl_product_step`.**  **THE INTERFACE LAYER IS COMPLETE** (the transfers below are all proved
   and in the file): `contDiff_comp_toLp`, `convexOn_comp_toLp`, `growth_comp_toLp_h` (from an
   earlier session), and now `hessian_comp_toLp_l2` (the ℓ² form `2π(‖v.1‖²+v.2²) ≤ D²F p v v`;
   NB the file's `hessian_comp_toLp` gives only the *strictly weaker* max-norm version),
   `growth_dY_comp_toLp`, `coercive_comp_toLp` (via `convexOn_tangent_le` at `0` on the excess
   `f - π‖·‖²`), `hgrowth_comp_toLp` (`HGrowth` of the pullback), and finally
   `potGrowth_comp_toLp` (`PotGrowth` of the pullback, as the one-line pairing of
   `growth_dY_comp_toLp` and `coercive_comp_toLp`).
   Transport the hypotheses of `BLon (WithLp 2 (G × ℝ))` to
   `F := fun p => f (toLp p)`, `H := fun p => h (toLp p)` (`contDiff_comp_toLp`,
   `hessian_comp_toLp` — replace `‖v‖²` by `‖v.1‖² + v.2²` via `toLp_norm_sq`,
   `convexOn_comp_toLp`, `growth_comp_toLp`), build `PotGrowth F` and `HGrowth H` (using
   `convexOn_tangent_le` for the coercivity `F p ≥ (π/2)‖p‖² - D`), apply the auxiliary lemma,
   and transfer the integrals back with `integral_comp_toLp`.
-/

/-! ### Decay of slice integrals in the slice height -/

/-- Pointwise bound for the slice integrand. -/
lemma hpt_bound (F : G × ℝ → ℝ) {D : ℝ} (hD : ∀ p : G × ℝ, (Real.pi / 2) * ‖p‖ ^ 2 - D ≤ F p)
    (Φ : G × ℝ → ℝ) (B : ℝ) (hB0 : 0 ≤ B) (N : ℕ)
    (hΦ : ∀ z y, |Φ (z, y)| ≤ B * (1 + ‖z‖ + |y|) ^ N) (z : G) (y : ℝ) :
    |Φ (z, y)| * Real.exp (-(F (z, y)))
      ≤ B * Real.exp D * (1 + |y|) ^ N * (1 + ‖z‖) ^ N
        * Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2) * Real.exp (-(Real.pi / 4) * y ^ 2) := by
  have hb : (1 + ‖z‖ + |y|) ^ N ≤ (1 + |y|) ^ N * (1 + ‖z‖) ^ N := by
    have h : 1 + ‖z‖ + |y| ≤ (1 + |y|) * (1 + ‖z‖) := by
      nlinarith [abs_nonneg y, norm_nonneg z]
    calc (1 + ‖z‖ + |y|) ^ N ≤ ((1 + |y|) * (1 + ‖z‖)) ^ N := pow_le_pow_left₀ (by positivity) h N
      _ = (1 + |y|) ^ N * (1 + ‖z‖) ^ N := by rw [mul_pow]
  have hexp : Real.exp (-(F (z, y))) ≤ Real.exp D
      * Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2) * Real.exp (-(Real.pi / 4) * y ^ 2) := by
    have h0 : Real.exp (-(F (z, y))) ≤ Real.exp D * Real.exp (-(Real.pi / 2) * ‖(z, y)‖ ^ 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h := hD (z, y); linarith
    have h1 : Real.exp (-(Real.pi / 2) * ‖(z, y)‖ ^ 2)
        ≤ Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2) * Real.exp (-(Real.pi / 4) * y ^ 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hz : ‖z‖ ≤ ‖(z, y)‖ := by rw [Prod.norm_def]; exact le_max_left _ _
      have hy : |y| ≤ ‖(z, y)‖ := by
        rw [Prod.norm_def, Real.norm_eq_abs]; exact le_max_right _ _
      have h1' : ‖z‖ ^ 2 ≤ ‖(z, y)‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
      have h2' : y ^ 2 ≤ ‖(z, y)‖ ^ 2 := by
        rw [← sq_abs y]; exact pow_le_pow_left₀ (abs_nonneg y) hy 2
      nlinarith [h1', h2', Real.pi_pos]
    calc Real.exp (-(F (z, y))) ≤ Real.exp D * Real.exp (-(Real.pi / 2) * ‖(z, y)‖ ^ 2) := h0
      _ ≤ Real.exp D * (Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2)
            * Real.exp (-(Real.pi / 4) * y ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos D).le
      _ = Real.exp D * Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2)
            * Real.exp (-(Real.pi / 4) * y ^ 2) := by ring
  calc |Φ (z, y)| * Real.exp (-(F (z, y)))
      ≤ B * (1 + ‖z‖ + |y|) ^ N * (Real.exp D * Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2)
          * Real.exp (-(Real.pi / 4) * y ^ 2)) :=
        mul_le_mul (hΦ z y) hexp (Real.exp_pos _).le (by positivity)
    _ ≤ B * ((1 + |y|) ^ N * (1 + ‖z‖) ^ N) * (Real.exp D * Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2)
          * Real.exp (-(Real.pi / 4) * y ^ 2)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hb hB0
    _ = B * Real.exp D * (1 + |y|) ^ N * (1 + ‖z‖) ^ N
          * Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2) * Real.exp (-(Real.pi / 4) * y ^ 2) := by ring

/-- A slice integral of a polynomially bounded continuous function decays like `exp (-π y²/4)`. -/
lemma slice_integral_bound (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (Φ : G × ℝ → ℝ) (hΦc : Continuous Φ) (B : ℝ) (hB0 : 0 ≤ B) (N : ℕ)
    (hΦ : ∀ z y, |Φ (z, y)| ≤ B * (1 + ‖z‖ + |y|) ^ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ,
      |∫ z, Φ (z, y) * Real.exp (-(F (z, y)))| ≤ C * (1 + |y|) ^ N
        * Real.exp (-(Real.pi / 4) * y ^ 2) := by
  obtain ⟨-, D, hD⟩ := hp
  have hK0 : 0 ≤ ∫ z : G, (1 + ‖z‖) ^ N * Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2) :=
    integral_nonneg (fun z => by positivity)
  refine ⟨B * Real.exp D * (∫ z : G, (1 + ‖z‖) ^ N * Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2)),
    by positivity, fun y => ?_⟩
  have hEcont : Continuous (fun z : G => Real.exp (-(F (z, y)))) :=
    Real.continuous_exp.comp (hF.continuous.comp (continuous_id.prodMk continuous_const)).neg
  have hInt : Integrable (fun z : G => B * Real.exp D * (1 + |y|) ^ N * (1 + ‖z‖) ^ N
      * Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2) * Real.exp (-(Real.pi / 4) * y ^ 2)) := by
    have h1 : Integrable (fun z : G => (B * Real.exp D * (1 + |y|) ^ N
        * Real.exp (-(Real.pi / 4) * y ^ 2)) * ((1 + ‖z‖) ^ N
          * Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2))) :=
      Integrable.const_mul (Commons.Analysis.Asymptotics.integrable_pow_mul_exp_neg_sq
        (V := G) (Real.pi / 4) (by positivity) N) _
    refine h1.congr (Eventually.of_forall (fun z => ?_))
    ring
  have hfInt : Integrable (fun z : G => Φ (z, y) * Real.exp (-(F (z, y)))) := by
    refine Integrable.mono' hInt (hΦc.comp (continuous_id.prodMk continuous_const) |>.mul
      hEcont).aestronglyMeasurable ?_
    filter_upwards with z
    have h1 : ‖Φ (z, y) * Real.exp (-(F (z, y)))‖
        = |Φ (z, y)| * Real.exp (-(F (z, y))) := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    rw [h1]
    exact hpt_bound F hD Φ B hB0 N hΦ z y
  have hbound : ∀ z : G, ‖Φ (z, y) * Real.exp (-(F (z, y)))‖
      ≤ B * Real.exp D * (1 + |y|) ^ N * (1 + ‖z‖) ^ N
        * Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2) * Real.exp (-(Real.pi / 4) * y ^ 2) := by
    intro z
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    exact hpt_bound F hD Φ B hB0 N hΦ z y
  have hfac : (∫ z : G, B * Real.exp D * (1 + |y|) ^ N * (1 + ‖z‖) ^ N
        * Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2) * Real.exp (-(Real.pi / 4) * y ^ 2))
      = B * Real.exp D * (1 + |y|) ^ N * Real.exp (-(Real.pi / 4) * y ^ 2)
        * ∫ z : G, (1 + ‖z‖) ^ N * Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2) := by
    rw [← MeasureTheory.integral_const_mul (μ := (volume : Measure G))
      (B * Real.exp D * (1 + |y|) ^ N * Real.exp (-(Real.pi / 4) * y ^ 2))
      (fun z : G => (1 + ‖z‖) ^ N * Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2))]
    congr 1
    funext z; ring
  calc |∫ z, Φ (z, y) * Real.exp (-(F (z, y)))|
      ≤ ∫ z, ‖Φ (z, y) * Real.exp (-(F (z, y)))‖ := by
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (fun z : G => (Φ (z, y) * Real.exp (-(F (z, y))) : ℝ)))
    _ ≤ ∫ z, B * Real.exp D * (1 + |y|) ^ N * (1 + ‖z‖) ^ N
          * Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2) * Real.exp (-(Real.pi / 4) * y ^ 2) :=
        integral_mono_ae hfInt.norm hInt (Eventually.of_forall hbound)
    _ = B * Real.exp D * (1 + |y|) ^ N * Real.exp (-(Real.pi / 4) * y ^ 2)
          * ∫ z : G, (1 + ‖z‖) ^ N * Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2) := hfac
    _ = B * Real.exp D * (∫ z : G, (1 + ‖z‖) ^ N * Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2))
          * (1 + |y|) ^ N * Real.exp (-(Real.pi / 4) * y ^ 2) := by ring

/-- Integrability in the slice height of a slice integral of a polynomially bounded function. -/
lemma integrable_slice_integral (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (Φ : G × ℝ → ℝ) (hΦc : Continuous Φ) (B : ℝ) (hB0 : 0 ≤ B) (N : ℕ)
    (hΦ : ∀ z y, |Φ (z, y)| ≤ B * (1 + ‖z‖ + |y|) ^ N) :
    Integrable (fun y : ℝ => ∫ z, Φ (z, y) * Real.exp (-(F (z, y)))) := by
  obtain ⟨C, hC0, hC⟩ := slice_integral_bound F hF hp Φ hΦc B hB0 N hΦ
  have hmeas : AEMeasurable (fun y : ℝ => ∫ z, Φ (z, y) * Real.exp (-(F (z, y)))) volume :=
    aestronglyMeasurable_integral_prod_left' (μ := (volume : Measure G))
      ((hΦc.mul (Real.continuous_exp.comp hF.continuous.neg)).aestronglyMeasurable)
  have hbd : Integrable (fun y : ℝ => C * (1 + |y|) ^ N * Real.exp (-(Real.pi / 4) * y ^ 2)) := by
    have h := Commons.Analysis.Asymptotics.integrable_pow_mul_exp_neg_sq (V := ℝ)
      (Real.pi / 4) (by positivity) N
    refine (h.const_mul C).congr (Eventually.of_forall (fun y => ?_))
    simp only [Real.norm_eq_abs, sq_abs]
    ring
  refine Integrable.mono' hbd hmeas.aestronglyMeasurable ?_
  filter_upwards with y
  rw [Real.norm_eq_abs]
  exact hC y

/-! ### Algebra of the conditional mean -/

lemma condMean_const (F : G × ℝ → ℝ) (c : ℝ) (y : ℝ) (hW : sliceMass F y ≠ 0) :
    condMean F (fun _ : G × ℝ => c) y = c := by
  have h1 : (fun z : G => (fun _ : G × ℝ => c) (z, y) * Real.exp (-(F (z, y))))
      = fun z : G => c * Real.exp (-(F (z, y))) := rfl
  rw [condMean, h1, MeasureTheory.integral_const_mul]
  rw [show (∫ z, Real.exp (-(F (z, y)))) = sliceMass F y from rfl]
  field_simp

lemma condMean_sub (F f g : G × ℝ → ℝ) (y : ℝ) (hW : sliceMass F y ≠ 0)
    (hf : Integrable (fun z => f (z, y) * Real.exp (-(F (z, y)))))
    (hg : Integrable (fun z => g (z, y) * Real.exp (-(F (z, y))))) :
    condMean F (f - g) y = condMean F f y - condMean F g y := by
  have h1 : (fun z : G => (f - g) (z, y) * Real.exp (-(F (z, y))))
      = fun z : G => f (z, y) * Real.exp (-(F (z, y))) - g (z, y) * Real.exp (-(F (z, y))) := by
    funext z; simp only [Pi.sub_apply]; ring
  rw [condMean, condMean, condMean, h1, integral_sub hf hg]
  ring

lemma condMean_add (F f g : G × ℝ → ℝ) (y : ℝ) (hW : sliceMass F y ≠ 0)
    (hf : Integrable (fun z => f (z, y) * Real.exp (-(F (z, y)))))
    (hg : Integrable (fun z => g (z, y) * Real.exp (-(F (z, y))))) :
    condMean F (f + g) y = condMean F f y + condMean F g y := by
  have h1 : (fun z : G => (f + g) (z, y) * Real.exp (-(F (z, y))))
      = fun z : G => f (z, y) * Real.exp (-(F (z, y))) + g (z, y) * Real.exp (-(F (z, y))) := by
    funext z; simp only [Pi.add_apply]; ring
  rw [condMean, condMean, condMean, h1, integral_add hf hg]
  ring


/-- The polarized form of the Hessian is controlled by its diagonal. -/
lemma hess_polar_le (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (C : ℝ) (hC : 0 ≤ C) (N : ℕ)
    (h : ∀ p v : G × ℝ, |fderiv ℝ (fderiv ℝ F) p v v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ p u w : G × ℝ,
      |fderiv ℝ (fderiv ℝ F) p u w| ≤ C' * (1 + ‖p‖) ^ N * ‖u‖ * ‖w‖ := by
  refine ⟨3 * C, by positivity, fun p u w => ?_⟩
  have hsym : ∀ u w : G × ℝ, fderiv ℝ (fderiv ℝ F) p u w = fderiv ℝ (fderiv ℝ F) p w u :=
    fun u w => ContDiffAt.isSymmSndFDerivAt hF.contDiffAt (by simp) u w
  have hpar : ∀ u w : G × ℝ, fderiv ℝ (fderiv ℝ F) p (u + w) (u + w)
      = fderiv ℝ (fderiv ℝ F) p u u + 2 * fderiv ℝ (fderiv ℝ F) p u w
        + fderiv ℝ (fderiv ℝ F) p w w := by
    intro u w
    have h1 : fderiv ℝ (fderiv ℝ F) p (u + w)
        = fderiv ℝ (fderiv ℝ F) p u + fderiv ℝ (fderiv ℝ F) p w := map_add _ _ _
    calc fderiv ℝ (fderiv ℝ F) p (u + w) (u + w)
        = (fderiv ℝ (fderiv ℝ F) p u + fderiv ℝ (fderiv ℝ F) p w) (u + w) := by rw [h1]
      _ = fderiv ℝ (fderiv ℝ F) p u (u + w) + fderiv ℝ (fderiv ℝ F) p w (u + w) := by
            rw [ContinuousLinearMap.add_apply]
      _ = (fderiv ℝ (fderiv ℝ F) p u u + fderiv ℝ (fderiv ℝ F) p u w)
            + (fderiv ℝ (fderiv ℝ F) p w u + fderiv ℝ (fderiv ℝ F) p w w) := by
            rw [map_add, map_add]
      _ = fderiv ℝ (fderiv ℝ F) p u u + 2 * fderiv ℝ (fderiv ℝ F) p u w
            + fderiv ℝ (fderiv ℝ F) p w w := by
            rw [hsym w u]; ring
  have hstep : ∀ u w : G × ℝ, 2 * |fderiv ℝ (fderiv ℝ F) p u w|
      ≤ 3 * C * (1 + ‖p‖) ^ N * (‖u‖ ^ 2 + ‖w‖ ^ 2) := by
    intro u w
    have hb1 := h p (u + w)
    have hb2 := h p u
    have hb3 := h p w
    have h6 : 2 * fderiv ℝ (fderiv ℝ F) p u w
        = fderiv ℝ (fderiv ℝ F) p (u + w) (u + w)
          - fderiv ℝ (fderiv ℝ F) p u u - fderiv ℝ (fderiv ℝ F) p w w := by
      have := hpar u w; linarith
    have h6' : fderiv ℝ (fderiv ℝ F) p u w
        = (fderiv ℝ (fderiv ℝ F) p (u + w) (u + w) - fderiv ℝ (fderiv ℝ F) p u u
            - fderiv ℝ (fderiv ℝ F) p w w) / 2 := by linarith [h6]
    rw [h6']
    have h9 : |(fderiv ℝ (fderiv ℝ F) p (u + w) (u + w) - fderiv ℝ (fderiv ℝ F) p u u
        - fderiv ℝ (fderiv ℝ F) p w w) / 2|
        = |fderiv ℝ (fderiv ℝ F) p (u + w) (u + w) - fderiv ℝ (fderiv ℝ F) p u u
        - fderiv ℝ (fderiv ℝ F) p w w| / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    rw [h9]
    have h7 : |fderiv ℝ (fderiv ℝ F) p (u + w) (u + w) - fderiv ℝ (fderiv ℝ F) p u u
        - fderiv ℝ (fderiv ℝ F) p w w|
        ≤ |fderiv ℝ (fderiv ℝ F) p (u + w) (u + w)| + |fderiv ℝ (fderiv ℝ F) p u u|
          + |fderiv ℝ (fderiv ℝ F) p w w| := by
      have ha : |fderiv ℝ (fderiv ℝ F) p (u + w) (u + w) - fderiv ℝ (fderiv ℝ F) p u u
          - fderiv ℝ (fderiv ℝ F) p w w|
          ≤ |fderiv ℝ (fderiv ℝ F) p (u + w) (u + w) - fderiv ℝ (fderiv ℝ F) p u u|
            + |fderiv ℝ (fderiv ℝ F) p w w| := abs_sub _ _
      have hb : |fderiv ℝ (fderiv ℝ F) p (u + w) (u + w) - fderiv ℝ (fderiv ℝ F) p u u|
          ≤ |fderiv ℝ (fderiv ℝ F) p (u + w) (u + w)| + |fderiv ℝ (fderiv ℝ F) p u u| :=
        abs_sub _ _
      linarith
    have h5 : ‖u + w‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
      have h6 := norm_add_le u w
      have h7 : (0:ℝ) ≤ ‖u‖ + ‖w‖ := add_nonneg (norm_nonneg u) (norm_nonneg w)
      nlinarith [h6, h7, norm_nonneg (u + w), sq_nonneg (‖u‖ - ‖w‖)]
    have hC0 : (0:ℝ) ≤ C * (1 + ‖p‖) ^ N := by positivity
    nlinarith [h7, hb1, hb2, hb3, h5, hC0, norm_nonneg u, norm_nonneg w]
  have hhom : ∀ u w : G × ℝ,
      |fderiv ℝ (fderiv ℝ F) p u w| ≤ 3 * C * (1 + ‖p‖) ^ N * ‖u‖ * ‖w‖ := by
    intro u w
    rcases eq_or_ne u 0 with huz | hu
    · subst huz; simp
    rcases eq_or_ne w 0 with hwz | hw
    · subst hwz; simp
    have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr hw
    set t : ℝ := Real.sqrt (‖w‖ / ‖u‖) with ht
    have ht0 : 0 < t := Real.sqrt_pos.mpr (div_pos hw0 hu0)
    have ht2 : t ^ 2 = ‖w‖ / ‖u‖ := Real.sq_sqrt (div_pos hw0 hu0).le
    have hsl : fderiv ℝ (fderiv ℝ F) p (t • u) (t⁻¹ • w)
        = t * (t⁻¹ * fderiv ℝ (fderiv ℝ F) p u w) := by
      have h1 : fderiv ℝ (fderiv ℝ F) p (t • u) = t • fderiv ℝ (fderiv ℝ F) p u :=
        map_smul _ _ _
      rw [h1]
      simp only [ContinuousLinearMap.smul_apply, map_smul, smul_eq_mul]
      ring
    have habs : 2 * |fderiv ℝ (fderiv ℝ F) p (t • u) (t⁻¹ • w)|
        = 2 * |fderiv ℝ (fderiv ℝ F) p u w| := by
      rw [hsl, abs_mul, abs_mul, abs_of_pos ht0, abs_of_pos (inv_pos.mpr ht0)]
      congr 1
      field_simp
    have h1 := hstep (t • u) (t⁻¹ • w)
    rw [habs] at h1
    have hnu : ‖t • u‖ ^ 2 = t ^ 2 * ‖u‖ ^ 2 := by
      rw [norm_smul, Real.norm_of_nonneg ht0.le, mul_pow]
    have hnw : ‖t⁻¹ • w‖ ^ 2 = (t ^ 2)⁻¹ * ‖w‖ ^ 2 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr ht0).le, mul_pow, inv_pow]
    rw [hnu, hnw, ht2] at h1
    have e1 : (‖w‖ / ‖u‖) * ‖u‖ ^ 2 = ‖w‖ * ‖u‖ := by field_simp
    have e2 : (‖w‖ / ‖u‖)⁻¹ * ‖w‖ ^ 2 = ‖u‖ * ‖w‖ := by rw [inv_div]; field_simp
    rw [e1, e2] at h1
    have hnd : 3 * C * (1 + ‖p‖) ^ N * (‖w‖ * ‖u‖ + ‖u‖ * ‖w‖)
        = 2 * (3 * C * (1 + ‖p‖) ^ N * ‖u‖ * ‖w‖) := by ring
    rw [hnd] at h1
    linarith [h1]
  exact hhom u w


/-- Growth of the gradient of a slice potential. -/
lemma grad_slicePot_growth (H : G × ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C) (N : ℕ)
    (hH : ∀ p v : G × ℝ, |fderiv ℝ H p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖)
    (hHcd : ContDiff ℝ 1 H) (y : ℝ) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∃ M : ℕ, ∀ z : G, ‖grad (slicePot H y) z‖ ≤ C' * (1 + ‖z‖ + |y|) ^ M := by
  refine ⟨C, hC, N, fun z => ?_⟩
  rw [grad_norm_eq]
  have hdif : DifferentiableAt ℝ H (z, y) := hHcd.contDiffAt.differentiableAt (by norm_num)
  have h1 : ‖fderiv ℝ (slicePot H y) z‖ ≤ ‖fderiv ℝ H (z, y)‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (fderiv ℝ H (z, y))) (fun v => ?_)
    rw [fderiv_slicePot H y z v hdif, Real.norm_eq_abs]
    calc |fderiv ℝ H (z, y) (v, 0)| = ‖fderiv ℝ H (z, y) (v, 0)‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖fderiv ℝ H (z, y)‖ * ‖((v, 0) : G × ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ H (z, y)‖ * ‖v‖ := by rw [show ‖((v, 0) : G × ℝ)‖ = ‖v‖ from by simp]
  have h2 : ‖fderiv ℝ H (z, y)‖ ≤ C * (1 + ‖(z, y)‖) ^ N := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
    rw [Real.norm_eq_abs]
    exact hH (z, y) v
  calc ‖fderiv ℝ (slicePot H y) z‖ ≤ ‖fderiv ℝ H (z, y)‖ := h1
    _ ≤ C * (1 + ‖(z, y)‖) ^ N := h2
    _ ≤ C * (1 + ‖z‖ + |y|) ^ N := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        exact pow_le_pow_left₀ (by positivity) (by linarith [norm_pair_le z y]) N

/-- Growth of the gradient of `mixPot F y` (the `y`-derivative of the potential). -/
lemma grad_mixPot_growth (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (C : ℝ) (hC : 0 ≤ C) (N : ℕ)
    (hdiag : ∀ p v : G × ℝ, |fderiv ℝ (fderiv ℝ F) p v v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2)
    (y : ℝ) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∃ M : ℕ, ∀ z : G, ‖grad (mixPot F y) z‖ ≤ C' * (1 + ‖z‖ + |y|) ^ M := by
  obtain ⟨C', hC'0, hpol⟩ := hess_polar_le F hF C hC N hdiag
  refine ⟨C', hC'0, N, fun z => ?_⟩
  rw [grad_norm_eq]
  have h1 : ‖fderiv ℝ (mixPot F y) z‖ ≤ C' * (1 + ‖(z, y)‖) ^ N := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
    rw [fderiv_mixPot F y hF z v, Real.norm_eq_abs]
    have h2 := hpol (z, y) (v, 0) (0, 1)
    rw [show ‖((v, 0) : G × ℝ)‖ = ‖v‖ from by simp,
      show ‖((0, 1) : G × ℝ)‖ = 1 from by simp, mul_one] at h2
    exact h2
  calc ‖fderiv ℝ (mixPot F y) z‖ ≤ C' * (1 + ‖(z, y)‖) ^ N := h1
    _ ≤ C' * (1 + ‖z‖ + |y|) ^ N := by
        refine mul_le_mul_of_nonneg_left ?_ hC'0
        exact pow_le_pow_left₀ (by positivity) (by linarith [norm_pair_le z y]) N


/-- Slice integrability of `Φ · e^{-F}` from polynomial growth of `Φ`. -/
lemma integrable_slice_mul (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F) (y : ℝ)
    (Φ : G × ℝ → ℝ) (hΦc : Continuous Φ) (C : ℝ) (hC0 : 0 ≤ C) (N : ℕ)
    (hΦ : ∀ p : G × ℝ, |Φ p| ≤ C * (1 + ‖p‖) ^ N) :
    Integrable (fun z : G => Φ (z, y) * Real.exp (-(F (z, y)))) := by
  refine integrable_of_le_gauss F hF hp y (fun z => Φ (z, y))
    (hΦc.comp (continuous_id.prodMk continuous_const)) C hC0 N (fun z => ?_)
  exact le_trans (hΦ (z, y)) (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (by linarith [norm_pair_le z y]) N) hC0)


/-- The derivative of the conditional mean. -/
lemma hasDerivAt_condMean (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hH : ContDiff ℝ 1 H) (hg : HGrowth H) (y : ℝ) (hW : sliceMass F y ≠ 0) :
    HasDerivAt (condMean F H)
      (condMean F (fun p => dY H p) y - condCov F H (fun p => dY F p) y) y := by
  obtain ⟨⟨CF, hCF0, NF, hCF⟩, DF, hDF⟩ := hp
  obtain ⟨CH, hCH0, NH, hCH⟩ := hg
  have hp' : PotGrowth F := ⟨⟨CF, hCF0, NF, hCF⟩, DF, hDF⟩
  have hg' : HGrowth H := ⟨CH, hCH0, NH, hCH⟩
  have hIntDYH : Integrable (fun z : G => dY H (z, y) * Real.exp (-(F (z, y)))) :=
    integrable_slice_mul F hF hp' y (fun p => dY H p)
      ((hH.continuous_fderiv (by norm_num)).clm_apply continuous_const) CH hCH0 NH
      (fun p => (hCH p).2)
  have hIntHdYF : Integrable (fun z : G => H (z, y) * dY F (z, y) * Real.exp (-(F (z, y)))) := by
    refine integrable_slice_mul F hF hp' y (fun p => H p * dY F p)
      (((hH.continuous).mul (contDiff_dY F hF).continuous)) (CH * CF) (by positivity) (NH + NF) ?_
    intro p
    rw [abs_mul]
    calc |H p| * |dY F p| ≤ (CH * (1 + ‖p‖) ^ NH) * (CF * (1 + ‖p‖) ^ NF) :=
          mul_le_mul (hCH p).1 (hCF p).1 (abs_nonneg _) (by positivity)
      _ = CH * CF * (1 + ‖p‖) ^ (NH + NF) := by rw [pow_add]; ring
  have hmix : mixDeriv F H y = (∫ z, dY H (z, y) * Real.exp (-(F (z, y))))
      - ∫ z, H (z, y) * dY F (z, y) * Real.exp (-(F (z, y))) := by
    rw [show mixDeriv F H y = ∫ z, (dY H (z, y) - H (z, y) * dY F (z, y))
        * Real.exp (-(F (z, y))) from rfl]
    rw [show (fun z : G => (dY H (z, y) - H (z, y) * dY F (z, y)) * Real.exp (-(F (z, y))))
        = fun z : G => dY H (z, y) * Real.exp (-(F (z, y)))
          - H (z, y) * dY F (z, y) * Real.exp (-(F (z, y))) from by funext z; ring]
    rw [integral_sub hIntDYH hIntHdYF]
  have hB : HasDerivAt (fun y => ∫ z, H (z, y) * Real.exp (-(F (z, y)))) (mixDeriv F H y) y :=
    hasDerivAt_mixDeriv F H hF hp' hH hg' y
  have hW' : HasDerivAt (sliceMass F) (massDeriv F y) y := hasDerivAt_sliceMass F hF hp' y
  have hdiv := hB.div hW' hW
  have hfun : condMean F H
      = fun y => (∫ z, H (z, y) * Real.exp (-(F (z, y)))) / sliceMass F y := by
    funext t; rfl
  rw [hfun]
  refine hdiv.congr_deriv ?_
  rw [hmix, massDeriv_eq F hF hp' y]
  simp only [condMean, condCov]
  field_simp
  ring


/-- The Gaussian weight `(1 + ‖p‖)^N exp (-(π/2)‖p‖²)` is integrable on `G × ℝ`
(with the max norm). -/
lemma integrable_pow_mul_exp_neg_sq_prod (N : ℕ) :
    Integrable (fun p : G × ℝ => (1 + ‖p‖) ^ N * Real.exp (-(Real.pi / 2) * ‖p‖ ^ 2)) := by
  set g : G → ℝ := fun z => (1 + ‖z‖) ^ N * Real.exp (-(Real.pi / 4) * ‖z‖ ^ 2) with hg
  set k : ℝ → ℝ := fun y => (1 + |y|) ^ N * Real.exp (-(Real.pi / 4) * y ^ 2) with hk
  have hgi : Integrable g := by
    rw [hg]
    simpa [Real.norm_eq_abs] using
      Commons.Analysis.Asymptotics.integrable_pow_mul_exp_neg_sq (V := G)
        (Real.pi / 4) (by positivity) N
  have hki : Integrable k := by
    rw [hk]
    simpa [Real.norm_eq_abs] using
      Commons.Analysis.Asymptotics.integrable_pow_mul_exp_neg_sq (V := ℝ)
        (Real.pi / 4) (by positivity) N
  have hprod : Integrable (fun p : G × ℝ => g p.1 * k p.2) volume := by
    rw [Measure.volume_eq_prod G ℝ]
    exact hgi.mul_prod hki
  refine hprod.mono' ?_ ?_
  · exact (by fun_prop : Continuous
      (fun p : G × ℝ => (1 + ‖p‖) ^ N * Real.exp (-(Real.pi / 2) * ‖p‖ ^ 2))).aestronglyMeasurable
  · filter_upwards with p
    rw [Real.norm_of_nonneg (by positivity)]
    have hm : ‖p‖ = max ‖(p.1 : G)‖ |(p.2 : ℝ)| := by
      rw [Prod.norm_def, Real.norm_eq_abs]
    have h1 : (1 + ‖p‖) ^ N ≤ (1 + ‖p.1‖) ^ N * (1 + |p.2|) ^ N := by
      rw [hm]
      have h2 : 1 + max ‖p.1‖ |p.2| ≤ (1 + ‖p.1‖) * (1 + |p.2|) := by
        have h4 : max ‖p.1‖ |p.2| ≤ ‖p.1‖ + |p.2| :=
          max_le (by linarith [abs_nonneg p.2]) (by linarith [norm_nonneg p.1])
        nlinarith [h4, abs_nonneg p.2, norm_nonneg p.1]
      calc (1 + max ‖p.1‖ |p.2|) ^ N ≤ ((1 + ‖p.1‖) * (1 + |p.2|)) ^ N :=
            pow_le_pow_left₀ (by positivity) h2 N
        _ = (1 + ‖p.1‖) ^ N * (1 + |p.2|) ^ N := by rw [mul_pow]
    have h3 : Real.exp (-(Real.pi / 2) * ‖p‖ ^ 2)
        ≤ Real.exp (-(Real.pi / 4) * ‖p.1‖ ^ 2) * Real.exp (-(Real.pi / 4) * p.2 ^ 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hm2 : ‖p‖ ^ 2 = (max ‖(p.1 : G)‖ |(p.2 : ℝ)|) ^ 2 := by rw [hm]
      have ha : ‖(p.1 : G)‖ ^ 2 ≤ ‖p‖ ^ 2 := by
        rw [hm2]
        exact pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) 2
      have hb : p.2 ^ 2 ≤ ‖p‖ ^ 2 := by
        rw [hm2, ← sq_abs (p.2)]
        exact pow_le_pow_left₀ (abs_nonneg _) (le_max_right _ _) 2
      nlinarith [ha, hb, Real.pi_pos]
    calc (1 + ‖p‖) ^ N * Real.exp (-(Real.pi / 2) * ‖p‖ ^ 2)
        ≤ ((1 + ‖p.1‖) ^ N * (1 + |p.2|) ^ N)
            * (Real.exp (-(Real.pi / 4) * ‖p.1‖ ^ 2) * Real.exp (-(Real.pi / 4) * p.2 ^ 2)) :=
          mul_le_mul h1 h3 (Real.exp_pos _).le (by positivity)
      _ = g p.1 * k p.2 := by simp only [hg, hk]; ring

/-- Integrability of `Φ · exp (-F)` on `G × ℝ` when `Φ` has polynomial growth and `F` satisfies
`PotGrowth`. -/
lemma integrable_mul_exp_neg_potGrowth (F Φ : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hp : PotGrowth F) (hΦc : Continuous Φ) (C : ℝ) (hC : 0 ≤ C) (N : ℕ)
    (hΦ : ∀ p : G × ℝ, |Φ p| ≤ C * (1 + ‖p‖) ^ N) :
    Integrable (fun p : G × ℝ => Φ p * Real.exp (-(F p))) := by
  obtain ⟨-, D, hD⟩ := hp
  have he : ∀ p : G × ℝ, Real.exp (-(F p)) ≤ Real.exp D * Real.exp (-(Real.pi / 2) * ‖p‖ ^ 2) := by
    intro p
    calc Real.exp (-(F p)) ≤ Real.exp (D - (Real.pi / 2) * ‖p‖ ^ 2) := by
          apply Real.exp_le_exp.mpr
          have h := hD p; linarith
      _ = Real.exp D * Real.exp (-(Real.pi / 2) * ‖p‖ ^ 2) := by
          rw [← Real.exp_add]; ring_nf
  refine ((integrable_pow_mul_exp_neg_sq_prod (G := G) N).const_mul
    (Real.exp D * C)).mono' ?_ ?_
  · exact (hΦc.mul (Real.continuous_exp.comp hF.continuous.neg)).aestronglyMeasurable
  · filter_upwards with p
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    calc |Φ p| * Real.exp (-(F p))
        ≤ C * (1 + ‖p‖) ^ N * (Real.exp D * Real.exp (-(Real.pi / 2) * ‖p‖ ^ 2)) :=
          mul_le_mul (hΦ p) (he p) (Real.exp_pos _).le (by positivity)
      _ = Real.exp D * C * ((1 + ‖p‖) ^ N * Real.exp (-(Real.pi / 2) * ‖p‖ ^ 2)) := by ring

/-- The volume of `Set.univ` on a finite-dimensional real inner product space is positive. -/
lemma volume_univ_pos (G : Type*) [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] :
    (0 : ENNReal) < volume (Set.univ : Set G) := by
  haveI : MeasureTheory.Measure.IsAddHaarMeasure (volume : Measure G) := inferInstance
  exact pos_iff_ne_zero.mpr (MeasureTheory.Measure.IsOpenPosMeasure.open_pos
    (Set.univ : Set G) isOpen_univ Set.univ_nonempty)

/-- Positivity of the slice mass. -/
lemma sliceMass_pos (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F) (y : ℝ) :
    0 < sliceMass F y := by
  have hint : Integrable (fun z : G => Real.exp (-(F (z, y)))) := by
    simpa using integrable_of_le_gauss F hF hp y (fun _ : G => (1:ℝ)) continuous_const 1
      (by norm_num) 0 (fun z => by simp)
  rw [show sliceMass F y = ∫ z, Real.exp (-(F (z, y))) from rfl]
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall fun z => (Real.exp_pos _).le) hint]
  have : Function.support (fun z : G => Real.exp (-(F (z, y)))) = Set.univ := by
    ext z; simp [Function.mem_support]
  rw [this]
  exact volume_univ_pos G

/-- `Ξ · W` is integrable, where `Ξ = condMean F H` and `W = sliceMass F`. -/
lemma integrable_condMean_mul_sliceMass (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hp : PotGrowth F) (hH : ContDiff ℝ 1 H) (hg : HGrowth H) :
    Integrable (fun y : ℝ => condMean F H y * sliceMass F y) := by
  obtain ⟨CH, hCH0, NH, hCH⟩ := hg
  have hg' : HGrowth H := ⟨CH, hCH0, NH, hCH⟩
  have hamb : Integrable (fun p : G × ℝ => H p * Real.exp (-(F p))) :=
    integrable_mul_exp_neg_potGrowth F H hF hp hH.continuous CH hCH0 NH (fun p => (hCH p).1)
  have h1 : Integrable (fun y : ℝ => ∫ z : G, H (z, y) * Real.exp (-(F (z, y)))) := by
    rw [Measure.volume_eq_prod G ℝ] at hamb
    exact hamb.integral_prod_right
  refine h1.congr (Eventually.of_forall (fun y => ?_))
  exact (condMean_mul F H (ne_of_gt (sliceMass_pos F hF hp y))).symm

/-- `Ξ² · W` is integrable, where `Ξ = condMean F H` and `W = sliceMass F`. -/
lemma integrable_condMean_sq_mul_sliceMass (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hp : PotGrowth F) (hH : ContDiff ℝ 1 H) (hg : HGrowth H) :
    Integrable (fun y : ℝ => condMean F H y ^ 2 * sliceMass F y) := by
  obtain ⟨CH, hCH0, NH, hCH⟩ := hg
  have hg' : HGrowth H := ⟨CH, hCH0, NH, hCH⟩
  -- ambient integrability of `H² e^{-F}`
  have hamb : Integrable (fun p : G × ℝ => H p ^ 2 * Real.exp (-(F p))) := by
    refine integrable_mul_exp_neg_potGrowth F (fun p => H p ^ 2) hF hp
      (hH.continuous.pow 2) (CH ^ 2) (by positivity) (2 * NH) (fun p => ?_)
    rw [abs_of_nonneg (sq_nonneg _)]
    calc H p ^ 2 ≤ (CH * (1 + ‖p‖) ^ NH) ^ 2 := by
          rw [← sq_abs (H p)]; exact pow_le_pow_left₀ (abs_nonneg _) (hCH p).1 2
      _ = CH ^ 2 * (1 + ‖p‖) ^ (2 * NH) := by rw [mul_pow, ← pow_mul, Nat.mul_comm]
  have hA : Integrable (fun y : ℝ => ∫ z : G, H (z, y) ^ 2 * Real.exp (-(F (z, y)))) := by
    rw [Measure.volume_eq_prod G ℝ] at hamb
    exact hamb.integral_prod_right
  -- measurability
  have hmeasB : AEMeasurable (fun y : ℝ => ∫ z : G, H (z, y) * Real.exp (-(F (z, y)))) := by
    have h1 : AEStronglyMeasurable (fun p : G × ℝ => H p * Real.exp (-(F p))) volume :=
      (hH.continuous.mul (Real.continuous_exp.comp hF.continuous.neg)).aestronglyMeasurable
    rw [Measure.volume_eq_prod G ℝ] at h1
    exact aestronglyMeasurable_integral_prod_left' h1
  have hmeasW : AEMeasurable (sliceMass F) := by
    have h1 : AEStronglyMeasurable (fun p : G × ℝ => Real.exp (-(F p))) volume :=
      (Real.continuous_exp.comp hF.continuous.neg).aestronglyMeasurable
    rw [Measure.volume_eq_prod G ℝ] at h1
    exact aestronglyMeasurable_integral_prod_left' h1
  have hmeas : AEMeasurable (fun y : ℝ => condMean F H y ^ 2 * sliceMass F y) := by
    have hΞ : AEMeasurable (condMean F H) := by
      have : condMean F H
          = fun y => (∫ z : G, H (z, y) * Real.exp (-(F (z, y)))) / sliceMass F y := by
        funext t; rfl
      rw [this]
      exact hmeasB.div hmeasW
    have hΞ2 : AEMeasurable ((condMean F H) * (condMean F H) * sliceMass F) := (hΞ.mul hΞ).mul hmeasW
    refine hΞ2.congr (Eventually.of_forall (fun y => ?_))
    simp only [Pi.mul_apply, pow_two]
  refine Integrable.mono' hA hmeas.aestronglyMeasurable ?_
  filter_upwards with y
  have hWy := sliceMass_pos F hF hp y
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hWy.le)]
  have hIntH : Integrable (fun z : G => H (z, y) ^ 2 * Real.exp (-(F (z, y)))) :=
    integrable_slice_mul F hF hp y (fun p => H p ^ 2) (hH.continuous.pow 2) (CH ^ 2)
      (by positivity) (2 * NH) (fun p => by
        rw [abs_of_nonneg (sq_nonneg _)]
        calc H p ^ 2 ≤ (CH * (1 + ‖p‖) ^ NH) ^ 2 := by
              rw [← sq_abs (H p)]; exact pow_le_pow_left₀ (abs_nonneg _) (hCH p).1 2
          _ = CH ^ 2 * (1 + ‖p‖) ^ (2 * NH) := by rw [mul_pow, ← pow_mul, Nat.mul_comm])
  have hInt1 : Integrable (fun z : G => (1 : ℝ) ^ 2 * Real.exp (-(F (z, y)))) := by
    simpa using integrable_slice_mul F hF hp y (fun _ : G × ℝ => (1:ℝ)) continuous_const 1
      (by norm_num) 0 (fun p => by simp)
  have hcs := sq_integral_mul_le_integral_sq_mul_meas (fun z : G => H (z, y)) (fun _ => (1:ℝ))
    (fun z => Real.exp (-(F (z, y)))) (fun z => (Real.exp_pos _).le) hIntH hInt1
  have hcs' : (∫ z : G, H (z, y) * Real.exp (-(F (z, y)))) ^ 2
      ≤ (∫ z : G, H (z, y) ^ 2 * Real.exp (-(F (z, y)))) * sliceMass F y := by
    simpa [sliceMass, mul_one, one_pow] using hcs
  rw [condMean_sq_mul F H (ne_of_gt hWy)]
  rw [div_le_iff₀ hWy]
  linarith [hcs']


/-- Integrability of `(H · dY F) · e^{-F}` on a slice. -/
lemma integrable_H_mul_dYF (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hH : ContDiff ℝ 1 H)
    (hp : PotGrowth F) (hg : HGrowth H) (y : ℝ) :
    Integrable (fun z : G => H (z, y) * dY F (z, y) * Real.exp (-(F (z, y)))) := by
  obtain ⟨⟨CF, hCF0, NF, hCF⟩, DF, hDF⟩ := hp
  obtain ⟨CH, hCH0, NH, hCH⟩ := hg
  have hp' : PotGrowth F := ⟨⟨CF, hCF0, NF, hCF⟩, DF, hDF⟩
  refine integrable_slice_mul F hF hp' y (fun p => H p * dY F p)
    ((hH.continuous.mul (contDiff_dY F hF).continuous)) (CH * CF) (by positivity) (NH + NF) ?_
  intro p
  rw [abs_mul]
  calc |H p| * |dY F p| ≤ (CH * (1 + ‖p‖) ^ NH) * (CF * (1 + ‖p‖) ^ NF) :=
        mul_le_mul (hCH p).1 (hCF p).1 (abs_nonneg _) (by positivity)
    _ = CH * CF * (1 + ‖p‖) ^ (NH + NF) := by rw [pow_add]; ring

/-- Integrability of `dY H · e^{-F}` on a slice. -/
lemma integrable_dYH (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hH : ContDiff ℝ 1 H)
    (hp : PotGrowth F) (hg : HGrowth H) (y : ℝ) :
    Integrable (fun z : G => dY H (z, y) * Real.exp (-(F (z, y)))) := by
  obtain ⟨CH, hCH0, NH, hCH⟩ := hg
  exact integrable_slice_mul F hF hp y (fun p => dY H p)
    ((hH.continuous_fderiv (by norm_num)).clm_apply continuous_const) CH hCH0 NH
    (fun p => (hCH p).2)

/-- The derivative of the conditional mean, against the slice mass. -/
lemma condMeanDeriv_mul_sliceMass (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hH : ContDiff ℝ 1 H) (hg : HGrowth H) (y : ℝ) :
    (condMean F (fun p => dY H p) y - condCov F H (fun p => dY F p) y) * sliceMass F y
      = ∫ z, (dY H (z, y) - (H (z, y) - condMean F H y) * dY F (z, y))
          * Real.exp (-(F (z, y))) := by
  have hW := sliceMass_pos F hF hp y
  have hWne : sliceMass F y ≠ 0 := ne_of_gt hW
  have hI1 : Integrable (fun z : G => dY H (z, y) * Real.exp (-(F (z, y)))) :=
    integrable_dYH F H hF hH hp hg y
  have hI2 : Integrable (fun z : G => H (z, y) * dY F (z, y) * Real.exp (-(F (z, y)))) :=
    integrable_H_mul_dYF F H hF hH hp hg y
  have hI3 : Integrable (fun z : G => dY F (z, y) * Real.exp (-(F (z, y)))) :=
    integrable_dY_exp_neg F hF hp y
  have hA : Integrable (fun z : G => (dY H (z, y) - H (z, y) * dY F (z, y))
      * Real.exp (-(F (z, y)))) := by
    rw [show (fun z : G => (dY H (z, y) - H (z, y) * dY F (z, y)) * Real.exp (-(F (z, y))))
        = fun z : G => dY H (z, y) * Real.exp (-(F (z, y)))
          - H (z, y) * dY F (z, y) * Real.exp (-(F (z, y))) from by funext z; ring]
    exact hI1.sub hI2
  have hB : Integrable (fun z : G => condMean F H y * (dY F (z, y) * Real.exp (-(F (z, y))))) :=
    hI3.const_mul _
  have hsplit : (∫ z, (dY H (z, y) - (H (z, y) - condMean F H y) * dY F (z, y))
        * Real.exp (-(F (z, y))))
      = (∫ z, (dY H (z, y) - H (z, y) * dY F (z, y)) * Real.exp (-(F (z, y))))
        + condMean F H y * (∫ z, dY F (z, y) * Real.exp (-(F (z, y)))) := by
    have h1 : (fun z : G => (dY H (z, y) - (H (z, y) - condMean F H y) * dY F (z, y))
          * Real.exp (-(F (z, y))))
        = ((fun z : G => (dY H (z, y) - H (z, y) * dY F (z, y)) * Real.exp (-(F (z, y))))
            + fun z : G => condMean F H y * (dY F (z, y) * Real.exp (-(F (z, y))))) := by
      funext z; simp only [Pi.add_apply]; ring
    have h2 : ((fun z : G => (dY H (z, y) - H (z, y) * dY F (z, y)) * Real.exp (-(F (z, y))))
            + fun z : G => condMean F H y * (dY F (z, y) * Real.exp (-(F (z, y)))))
        = (fun z : G => (dY H (z, y) - H (z, y) * dY F (z, y)) * Real.exp (-(F (z, y)))
            + condMean F H y * (dY F (z, y) * Real.exp (-(F (z, y))))) := by
      funext z; simp only [Pi.add_apply]
    rw [h1, h2, integral_add hA hB, MeasureTheory.integral_const_mul]
  have hsub : (∫ z, (dY H (z, y) - H (z, y) * dY F (z, y)) * Real.exp (-(F (z, y))))
      = (∫ z, dY H (z, y) * Real.exp (-(F (z, y))))
        - ∫ z, H (z, y) * dY F (z, y) * Real.exp (-(F (z, y))) := by
    rw [show (fun z : G => (dY H (z, y) - H (z, y) * dY F (z, y)) * Real.exp (-(F (z, y))))
        = fun z : G => dY H (z, y) * Real.exp (-(F (z, y)))
          - H (z, y) * dY F (z, y) * Real.exp (-(F (z, y))) from by funext z; ring]
    rw [integral_sub hI1 hI2]
  rw [hsplit, hsub]
  simp only [condMean, condCov]
  field_simp
  ring


/-- Cauchy–Schwarz bound for the derivative of the conditional mean. -/
lemma condMeanDeriv_sq_mul_sliceMass_le (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hp : PotGrowth F) (hH : ContDiff ℝ 1 H) (hg : HGrowth H) (y : ℝ) :
    (condMean F (fun p => dY H p) y - condCov F H (fun p => dY F p) y) ^ 2 * sliceMass F y
      ≤ ∫ z, (dY H (z, y) - (H (z, y) - condMean F H y) * dY F (z, y)) ^ 2
          * Real.exp (-(F (z, y))) := by
  obtain ⟨⟨CF, hCF0, NF, hCF⟩, DF, hDF⟩ := hp
  obtain ⟨CH, hCH0, NH, hCH⟩ := hg
  have hp' : PotGrowth F := ⟨⟨CF, hCF0, NF, hCF⟩, DF, hDF⟩
  have hg' : HGrowth H := ⟨CH, hCH0, NH, hCH⟩
  have hW := sliceMass_pos F hF hp' y
  have hdYHcont : Continuous (fun p : G × ℝ => dY H p) :=
    (hH.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdYFcont : Continuous (fun p : G × ℝ => dY F p) := (contDiff_dY F hF).continuous
  -- integrability of `φ² e^{-F}` where `φ z = dYH (z,y) - (H (z,y) - Ξ) dYF (z,y)`
  have hIφ : Integrable (fun z : G => (dY H (z, y) - (H (z, y) - condMean F H y) * dY F (z, y)) ^ 2
      * Real.exp (-(F (z, y)))) := by
    refine integrable_slice_mul F hF hp' y
      (fun p : G × ℝ => (dY H p - (H p - condMean F H y) * dY F p) ^ 2)
      (((hdYHcont.sub (((hH.continuous.sub continuous_const)).mul hdYFcont))).pow 2)
      ((CH + (CH + |condMean F H y|) * CF) ^ 2) (by positivity) (2 * (NH + NF)) ?_
    intro p
    have h1 : |dY H p| ≤ CH * (1 + ‖p‖) ^ NH := (hCH p).2
    have h2 : |H p| ≤ CH * (1 + ‖p‖) ^ NH := (hCH p).1
    have h3 : |dY F p| ≤ CF * (1 + ‖p‖) ^ NF := (hCF p).1
    have h4 : (1:ℝ) ≤ (1 + ‖p‖) ^ NH := one_le_pow₀ (by linarith [norm_nonneg p])
    have h5 : (1:ℝ) ≤ (1 + ‖p‖) ^ NF := one_le_pow₀ (by linarith [norm_nonneg p])
    have hb : |dY H p - (H p - condMean F H y) * dY F p|
        ≤ (CH + (CH + |condMean F H y|) * CF) * (1 + ‖p‖) ^ (NH + NF) := by
      have h6 : |H p - condMean F H y| ≤ |H p| + |condMean F H y| := abs_sub _ _
      have h7 : |H p - condMean F H y| ≤ (CH + |condMean F H y|) * (1 + ‖p‖) ^ NH := by
        have h8 : |condMean F H y| ≤ |condMean F H y| * (1 + ‖p‖) ^ NH := by
          nlinarith [abs_nonneg (condMean F H y), h4]
        nlinarith [h2, h6, h8, hCH0, abs_nonneg (condMean F H y)]
      have h9 : |(H p - condMean F H y) * dY F p| ≤ (CH + |condMean F H y|) * CF
          * (1 + ‖p‖) ^ (NH + NF) := by
        rw [abs_mul]
        calc |H p - condMean F H y| * |dY F p| ≤ ((CH + |condMean F H y|) * (1 + ‖p‖) ^ NH)
              * (CF * (1 + ‖p‖) ^ NF) :=
              mul_le_mul h7 h3 (abs_nonneg _) (by positivity)
          _ = (CH + |condMean F H y|) * CF * (1 + ‖p‖) ^ (NH + NF) := by rw [pow_add]; ring
      have h10 : CH * (1 + ‖p‖) ^ NH ≤ CH * (1 + ‖p‖) ^ (NH + NF) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (by linarith [norm_nonneg p]) (Nat.le_add_right NH NF)) hCH0
      have h11 : |dY H p - (H p - condMean F H y) * dY F p|
          ≤ |dY H p| + |(H p - condMean F H y) * dY F p| := abs_sub _ _
      nlinarith [h11, h1, h9, h10, hCH0, hCF0, abs_nonneg (condMean F H y)]
    have hb2 : ((dY H p - (H p - condMean F H y) * dY F p) ^ 2)
        ≤ ((CH + (CH + |condMean F H y|) * CF) * (1 + ‖p‖) ^ (NH + NF)) ^ 2 := by
      rw [show (dY H p - (H p - condMean F H y) * dY F p) ^ 2
          = |dY H p - (H p - condMean F H y) * dY F p| ^ 2 from by rw [sq_abs]]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    rw [abs_of_nonneg (sq_nonneg _)]
    calc (dY H p - (H p - condMean F H y) * dY F p) ^ 2
        ≤ ((CH + (CH + |condMean F H y|) * CF) * (1 + ‖p‖) ^ (NH + NF)) ^ 2 := hb2
      _ = (CH + (CH + |condMean F H y|) * CF) ^ 2 * (1 + ‖p‖) ^ (2 * (NH + NF)) := by
          rw [mul_pow, ← pow_mul, Nat.mul_comm]
  have hI1 : Integrable (fun z : G => (1:ℝ) ^ 2 * Real.exp (-(F (z, y)))) := by
    simpa using integrable_slice_mul F hF hp' y (fun _ : G × ℝ => (1:ℝ)) continuous_const 1
      (by norm_num) 0 (fun p => by simp)
  have hcs := sq_integral_mul_le_integral_sq_mul_meas
    (fun z : G => dY H (z, y) - (H (z, y) - condMean F H y) * dY F (z, y)) (fun _ => (1:ℝ))
    (fun z => Real.exp (-(F (z, y)))) (fun z => (Real.exp_pos _).le) hIφ hI1
  have hcs' : (∫ z : G, (dY H (z, y) - (H (z, y) - condMean F H y) * dY F (z, y))
        * Real.exp (-(F (z, y)))) ^ 2
      ≤ (∫ z : G, (dY H (z, y) - (H (z, y) - condMean F H y) * dY F (z, y)) ^ 2
          * Real.exp (-(F (z, y)))) * sliceMass F y := by
    simpa [sliceMass, mul_one, one_pow] using hcs
  have hid := condMeanDeriv_mul_sliceMass F H hF hp' hH hg' y
  have hsq : (condMean F (fun p => dY H p) y - condCov F H (fun p => dY F p) y) ^ 2
        * sliceMass F y * sliceMass F y
      = (∫ z : G, (dY H (z, y) - (H (z, y) - condMean F H y) * dY F (z, y))
          * Real.exp (-(F (z, y)))) ^ 2 := by
    rw [show (condMean F (fun p => dY H p) y - condCov F H (fun p => dY F p) y) ^ 2
          * sliceMass F y * sliceMass F y
        = ((condMean F (fun p => dY H p) y - condCov F H (fun p => dY F p) y) * sliceMass F y) ^ 2
        from by ring, hid]
  refine le_of_mul_le_mul_right ?_ hW
  rw [hsq]
  exact hcs'


/-- Continuity of `y ↦ (∫ z, Φ (z,y) e^{-F(z,y)}) / sliceMass F y`. -/
lemma continuous_ratio_slice (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (Φ : G × ℝ → ℝ) (hΦc : Continuous Φ) (hΦg : HGrowth0 Φ) :
    Continuous (fun y : ℝ => (∫ z : G, Φ (z, y) * Real.exp (-(F (z, y)))) / sliceMass F y) := by
  refine Continuous.div ?_ (contDiff_sliceMass F hF hp).continuous
    (fun y => ne_of_gt (sliceMass_pos F hF hp y))
  exact continuous_iff_continuousAt.mpr (fun y => continuousAt_sliceIntegral_of_valGrowth
    (fun p : G × ℝ => Φ p * Real.exp (-(F p)))
    (hΦc.mul (Real.continuous_exp.comp hF.continuous.neg))
    (ValGrowth_mul_exp_neg F Φ hp hΦg) y)

/-- Continuity of the conditional mean. -/
lemma continuous_condMean_of (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hHc : Continuous H) (hHg : HGrowth0 H) : Continuous (condMean F H) := by
  rw [show condMean F H = fun y : ℝ => (∫ z : G, H (z, y) * Real.exp (-(F (z, y))))
      / sliceMass F y from by funext t; rfl]
  exact continuous_ratio_slice F hF hp H hHc hHg

/-- Continuity of the conditional covariance with `dY F`. -/
lemma continuous_condCov (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hH : ContDiff ℝ 1 H) (hg : HGrowth H) :
    Continuous (condCov F H (fun p => dY F p)) := by
  obtain ⟨⟨CF, hCF0, NF, hCF⟩, DF, hDF⟩ := hp
  obtain ⟨CH, hCH0, NH, hCH⟩ := hg
  have hp' : PotGrowth F := ⟨⟨CF, hCF0, NF, hCF⟩, DF, hDF⟩
  have hdYFcont : Continuous (fun p : G × ℝ => dY F p) := (contDiff_dY F hF).continuous
  have hHg0 : HGrowth0 (fun p : G × ℝ => dY F p) := ⟨CF, hCF0, NF, fun p => (hCF p).1⟩
  have hProdg : HGrowth0 (fun p : G × ℝ => H p * dY F p) :=
    ⟨CH * CF, by positivity, NH + NF, fun p => by
      rw [abs_mul]
      calc |H p| * |dY F p| ≤ (CH * (1 + ‖p‖) ^ NH) * (CF * (1 + ‖p‖) ^ NF) :=
            mul_le_mul (hCH p).1 (hCF p).1 (abs_nonneg _) (by positivity)
        _ = CH * CF * (1 + ‖p‖) ^ (NH + NF) := by rw [pow_add]; ring⟩
  have hcontHN : Continuous (fun y : ℝ => (∫ z : G, H (z, y) * dY F (z, y)
      * Real.exp (-(F (z, y)))) / sliceMass F y) :=
    continuous_ratio_slice F hF hp' (fun p => H p * dY F p)
      (hH.continuous.mul hdYFcont) hProdg
  rw [show condCov F H (fun p => dY F p)
      = fun y : ℝ => (∫ z : G, H (z, y) * dY F (z, y) * Real.exp (-(F (z, y))))
          / sliceMass F y - condMean F H y * condMean F (fun p => dY F p) y from by
    funext y
    simp only [condCov, condMean]]
  refine hcontHN.sub ((continuous_condMean_of F H hF hp' hH.continuous
    ⟨CH, hCH0, NH, fun p => (hCH p).1⟩).mul
    (continuous_condMean_of F (fun p => dY F p) hF hp' hdYFcont hHg0))

/-- The conditional mean is `C¹`. -/
theorem contDiff_condMean (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hH : ContDiff ℝ 1 H) (hg : HGrowth H) : ContDiff ℝ 1 (condMean F H) := by
  obtain ⟨CH, hCH0, NH, hCH⟩ := hg
  have hg' : HGrowth H := ⟨CH, hCH0, NH, hCH⟩
  rw [contDiff_one_iff_deriv]
  constructor
  · intro y
    exact (hasDerivAt_condMean F H hF hp hH hg' y
      (ne_of_gt (sliceMass_pos F hF hp y))).differentiableAt
  · have hderiv : deriv (condMean F H)
        = fun y => condMean F (fun p => dY H p) y - condCov F H (fun p => dY F p) y :=
      funext (fun y => (hasDerivAt_condMean F H hF hp hH hg' y
        (ne_of_gt (sliceMass_pos F hF hp y))).deriv)
    rw [hderiv]
    refine Continuous.sub ?_ (continuous_condCov F H hF hp hH hg')
    exact continuous_condMean_of F (fun p => dY H p) hF hp
      ((hH.continuous_fderiv (by norm_num)).clm_apply continuous_const)
      ⟨CH, hCH0, NH, fun p => (hCH p).2⟩


lemma sliceMass_ge_exp (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F) (C : ℝ)
    (hC0 : 0 ≤ C) (N : ℕ)
    (hderiv : ∀ p v : G × ℝ, |fderiv ℝ F p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖) (y : ℝ) :
    Real.exp (-(F 0 + C * (2 + |y|) ^ (N + 1))) * (volume (Metric.ball (0 : G) 1)).toReal
      ≤ sliceMass F y := by
  have hFdiff : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hup : ∀ z : G, ‖z‖ < 1 → F (z, y) ≤ F 0 + C * (2 + |y|) ^ (N + 1) := by
    intro z hz
    set p : G × ℝ := (z, y) with hpdef
    have hφdiff : ∀ t ∈ Set.Icc (0:ℝ) 1, DifferentiableAt ℝ (fun t : ℝ => F (t • p)) t := by
      intro t _
      exact hFdiff.differentiableAt.comp t (((hasDerivAt_id t).smul_const p).differentiableAt)
    have hbound : ∀ t ∈ Set.Icc (0:ℝ) 1,
        ‖deriv (fun t : ℝ => F (t • p)) t‖ ≤ C * (1 + ‖p‖) ^ N * ‖p‖ := by
      intro t ht
      have h1 : HasDerivAt (fun t : ℝ => t • p) p t := by
        simpa using (hasDerivAt_id t).smul_const p
      have h2 : HasDerivAt (fun t : ℝ => F (t • p)) (fderiv ℝ F (t • p) p) t :=
        hFdiff.differentiableAt.hasFDerivAt.comp_hasDerivAt t h1
      rw [h2.deriv, Real.norm_eq_abs]
      have h3 : ‖t • p‖ ≤ ‖p‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        calc t * ‖p‖ ≤ 1 * ‖p‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg p)
          _ = ‖p‖ := one_mul _
      calc |fderiv ℝ F (t • p) p| ≤ C * (1 + ‖t • p‖) ^ N * ‖p‖ := hderiv (t • p) p
        _ ≤ C * (1 + ‖p‖) ^ N * ‖p‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg p)
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by positivity) (by linarith [h3, norm_nonneg p]) N) hC0
    have hlip : |F p - F 0| ≤ C * (1 + ‖p‖) ^ N * ‖p‖ := by
      have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
        (f := fun t : ℝ => F (t • p)) (s := Set.Icc (0:ℝ) 1) (x := (0:ℝ)) (y := (1:ℝ))
        (C := C * (1 + ‖p‖) ^ N * ‖p‖) hφdiff hbound (convex_Icc (0:ℝ) 1)
        (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
      simpa [Real.norm_eq_abs, one_smul, zero_smul, sub_zero, abs_one, mul_one] using h
    have hp_norm : ‖p‖ ≤ 1 + |y| := by
      rw [hpdef, Prod.norm_def, Real.norm_eq_abs]
      exact max_le (by linarith [le_of_lt hz, abs_nonneg y]) (by linarith [abs_nonneg y])
    have hK : C * (1 + ‖p‖) ^ N * ‖p‖ ≤ C * (2 + |y|) ^ (N + 1) := by
      have h1' : (1:ℝ) + ‖p‖ ≤ 2 + |y| := by linarith
      calc C * (1 + ‖p‖) ^ N * ‖p‖ ≤ C * (2 + |y|) ^ N * (2 + |y|) :=
            mul_le_mul (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by positivity) h1' N) hC0)
            (by linarith [hp_norm] : ‖p‖ ≤ 2 + |y|) (norm_nonneg p) (by positivity)
        _ = C * (2 + |y|) ^ (N + 1) := by rw [pow_succ]; ring
    have h4 : F p - F 0 ≤ C * (2 + |y|) ^ (N + 1) := by
      linarith [le_abs_self (F p - F 0), hlip, hK]
    rw [hpdef] at h4
    linarith [h4]
  have hInt : Integrable (fun z : G => Real.exp (-(F (z, y)))) := by
    simpa using integrable_of_le_gauss F hF hp y (fun _ : G => (1:ℝ)) continuous_const 1
      (by norm_num) 0 (fun z => by simp)
  have hpt : ∀ z ∈ Metric.ball (0 : G) 1,
      Real.exp (-(F 0 + C * (2 + |y|) ^ (N + 1))) ≤ Real.exp (-(F (z, y))) :=
    fun z hz => Real.exp_le_exp.mpr (by
      have := Metric.mem_ball.mp hz
      rw [dist_eq_norm, sub_zero] at this
      linarith [hup z this])
  have hpt2 : ∀ z : G, Set.indicator (Metric.ball (0 : G) 1)
        (fun _ : G => Real.exp (-(F 0 + C * (2 + |y|) ^ (N + 1)))) z ≤ Real.exp (-(F (z, y))) := by
    intro z
    by_cases hz : z ∈ Metric.ball (0 : G) 1
    · rw [Set.indicator_of_mem hz]; exact hpt z hz
    · rw [Set.indicator_of_notMem hz]; exact (Real.exp_pos _).le
  rw [show sliceMass F y = ∫ z, Real.exp (-(F (z, y))) from rfl]
  calc Real.exp (-(F 0 + C * (2 + |y|) ^ (N + 1))) * (volume (Metric.ball (0 : G) 1)).toReal
      = ∫ z, Set.indicator (Metric.ball (0 : G) 1)
          (fun _ : G => Real.exp (-(F 0 + C * (2 + |y|) ^ (N + 1)))) z := by
        rw [MeasureTheory.integral_indicator measurableSet_ball, MeasureTheory.setIntegral_const,
          smul_eq_mul, measureReal_def]
        ring
    _ ≤ ∫ z, Real.exp (-(F (z, y))) :=
        MeasureTheory.integral_mono_of_nonneg
          (Eventually.of_forall (fun z => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) z))
          hInt (Eventually.of_forall hpt2)


/-- The `toLp`-transfer of the Hessian bound `D²f ⪰ 2π·Id`, in the ℓ² (product) form. -/
lemma hessian_comp_toLp_l2 (f : WithLp 2 (G × ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (hH : ∀ x v : WithLp 2 (G × ℝ), 2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v) :
    ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ (fun p' : G × ℝ => f (WithLp.toLp 2 p'))) p v v := by
  intro p v
  rw [fderiv_fderiv_comp_toLp f hf p v v]
  have h1 := hH (WithLp.toLp 2 p) (WithLp.toLp 2 v)
  rwa [toLp_norm_sq v] at h1


/-- Growth of `dY F` and `d2Y F` for the `toLp`-pullback `F` of a potential `f`. -/
lemma growth_dY_comp_toLp (f : WithLp 2 (G × ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : WithLp 2 (G × ℝ),
      |fderiv ℝ f x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ f) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p : G × ℝ,
      |dY (fun p' : G × ℝ => f (WithLp.toLp 2 p')) p| ≤ C * (1 + ‖p‖) ^ N ∧
      |d2Y (fun p' : G × ℝ => f (WithLp.toLp 2 p')) p| ≤ C * (1 + ‖p‖) ^ N := by
  obtain ⟨C, hC0, N, hCN⟩ := growth_comp_toLp f hf hgf
  have hFcd : ContDiff ℝ 2 (fun p' : G × ℝ => f (WithLp.toLp 2 p')) := contDiff_comp_toLp f 2 hf
  refine ⟨C, hC0, N, fun p => ⟨?_, ?_⟩⟩
  · have h1 := (hCN p (0, 1)).1
    rw [show ‖((0, 1) : G × ℝ)‖ = 1 from by simp, mul_one] at h1
    simpa [dY] using h1
  · have h1 := (hCN p (0, 1)).2
    rw [show ‖((0, 1) : G × ℝ)‖ = 1 from by simp, one_pow, mul_one] at h1
    have h2 : d2Y (fun p' : G × ℝ => f (WithLp.toLp 2 p')) p
        = fderiv ℝ (fderiv ℝ (fun p' : G × ℝ => f (WithLp.toLp 2 p'))) p (0, 1) (0, 1) := by
      show fderiv ℝ (dY (fun p' : G × ℝ => f (WithLp.toLp 2 p'))) p (0, 1) = _
      exact fderiv_fderiv_eval _ hFcd (0, 1) (0, 1) p
    rw [h2]; exact h1


/-- Coercivity of the `toLp`-pullback of a potential whose excess over `π‖·‖²` is convex. -/
lemma coercive_comp_toLp (f : WithLp 2 (G × ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (hconv : ConvexOn ℝ Set.univ (fun x => f x - Real.pi * ‖x‖ ^ 2)) :
    ∃ D : ℝ, ∀ p : G × ℝ, (Real.pi / 2) * ‖p‖ ^ 2 - D ≤ f (WithLp.toLp 2 p) := by
  set g : WithLp 2 (G × ℝ) → ℝ := fun x => f x - Real.pi * ‖x‖ ^ 2 with hg
  have hgconv : ConvexOn ℝ Set.univ g := hconv
  have hd0 : DifferentiableAt ℝ g 0 := by
    rw [hg]
    refine (hf.differentiable (n := 2) (by norm_num) |>.differentiableAt).sub ?_
    have h2 : ContDiff ℝ 1 (fun x : WithLp 2 (G × ℝ) => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
    exact ((h2.const_smul (Real.pi : ℝ)).differentiable (by norm_num)).differentiableAt
  have htan : ∀ x : WithLp 2 (G × ℝ), g 0 + fderiv ℝ g 0 x ≤ g x :=
    fun x => convexOn_tangent_le g hgconv hd0 x
  refine ⟨‖fderiv ℝ g 0‖ ^ 2 - f 0, fun p => ?_⟩
  have h2 := htan (WithLp.toLp 2 p)
  have hg0 : g 0 = f 0 := by simp [hg]
  rw [hg0] at h2
  have hb : -(‖fderiv ℝ g 0‖ * ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖) ≤ fderiv ℝ g 0 (WithLp.toLp 2 p) := by
    have h4 := ContinuousLinearMap.le_opNorm (fderiv ℝ g 0) (WithLp.toLp 2 p)
    rw [Real.norm_eq_abs] at h4
    linarith [neg_abs_le (fderiv ℝ g 0 (WithLp.toLp 2 p))]
  have h5 : (Real.pi / 2) * ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖ ^ 2 - ‖fderiv ℝ g 0‖ ^ 2
      ≤ Real.pi * ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖ ^ 2
        + fderiv ℝ g 0 (WithLp.toLp 2 p) := by
    have hb' : -(‖fderiv ℝ g 0‖ * ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖)
        ≤ fderiv ℝ g 0 (WithLp.toLp 2 p) := hb
    nlinarith [hb', sq_nonneg (Real.pi * ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖ - ‖fderiv ℝ g 0‖),
      sq_nonneg (‖fderiv ℝ g 0‖), Real.pi_gt_three, norm_nonneg (fderiv ℝ g 0)]
  have h6 : Real.pi * ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖ ^ 2 + f 0
      + fderiv ℝ g 0 (WithLp.toLp 2 p) ≤ f (WithLp.toLp 2 p) := by
    have h := h2
    rw [hg] at h
    simp only at h
    linarith [h]
  have h7 : (Real.pi / 2) * ‖(WithLp.toLp 2 p : WithLp 2 (G × ℝ))‖ ^ 2
      - (‖fderiv ℝ g 0‖ ^ 2 - f 0) ≤ f (WithLp.toLp 2 p) := by
    linarith [h5, h6]
  refine le_trans ?_ h7
  rw [toLp_norm_sq p]
  have hmax : ‖p‖ ^ 2 ≤ ‖p.1‖ ^ 2 + p.2 ^ 2 := by
    rw [Prod.norm_def, Real.norm_eq_abs]
    rcases max_cases ‖p.1‖ |p.2| with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; nlinarith [sq_nonneg p.2]
    · rw [h, sq_abs]; nlinarith [sq_nonneg ‖p.1‖]
  nlinarith [hmax, Real.pi_pos]


/-- `toLp`-transfer of the growth hypotheses on the test function, in `HGrowth` form. -/
lemma hgrowth_comp_toLp (h : WithLp 2 (G × ℝ) → ℝ) (hh : ContDiff ℝ 1 h)
    (hgh : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : WithLp 2 (G × ℝ),
      |h x| ≤ C * (1 + ‖x‖) ^ N ∧ |fderiv ℝ h x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖) :
    HGrowth (fun p : G × ℝ => h (WithLp.toLp 2 p)) := by
  obtain ⟨C, hC0, N, hCN⟩ := growth_comp_toLp_h h hh hgh
  refine ⟨C, hC0, N, fun p => ⟨(hCN p 0).1, ?_⟩⟩
  have h1 := (hCN p (0, 1)).2
  rw [show ‖((0, 1) : G × ℝ)‖ = 1 from by simp, mul_one] at h1
  simpa [dY] using h1


/-- `PotGrowth` for the `toLp`-pullback of a potential `f`. -/
lemma potGrowth_comp_toLp (f : WithLp 2 (G × ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (hconv : ConvexOn ℝ Set.univ (fun x => f x - Real.pi * ‖x‖ ^ 2))
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : WithLp 2 (G × ℝ),
      |fderiv ℝ f x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ f) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2) :
    PotGrowth (fun p : G × ℝ => f (WithLp.toLp 2 p)) :=
  ⟨growth_dY_comp_toLp f hf hgf, coercive_comp_toLp f hf hconv⟩


/-- The conditional variance times the slice mass is the weighted variance of the slice. -/
lemma condVar_mul_sliceMass_eq (F H : G × ℝ → ℝ) (y : ℝ) (hW : sliceMass F y ≠ 0) :
    condVar F H y * sliceMass F y
      = wVar (fun z : G => Real.exp (-(slicePot F y z))) (slicePot H y) := by
  rw [wVar, condVar_mul F H hW]
  simp only [slicePot, sliceMass]

/-- The conditional covariance times the slice mass is the weighted cross-term of the slices. -/
lemma condCov_mul_sliceMass_eq (F H : G × ℝ → ℝ) (y : ℝ) (hW : sliceMass F y ≠ 0) :
    condCov F H (fun p => dY F p) y * sliceMass F y
      = (∫ z, slicePot H y z * mixPot F y z * Real.exp (-(slicePot F y z)))
        - (∫ z, slicePot H y z * Real.exp (-(slicePot F y z)))
          * (∫ z, mixPot F y z * Real.exp (-(slicePot F y z))) / sliceMass F y := by
  rw [condCov_mul F H (fun p => dY F p) hW]
  simp only [slicePot, mixPot, sliceMass]

/-- The conditional variance of `dY F` times the slice mass is the weighted variance of `mixPot`. -/
lemma condVar_mixPot_mul_sliceMass_eq (F : G × ℝ → ℝ) (y : ℝ) (hW : sliceMass F y ≠ 0) :
    condVar F (fun p => dY F p) y * sliceMass F y
      = wVar (fun z : G => Real.exp (-(slicePot F y z))) (mixPot F y) := by
  rw [wVar, condVar_mul F (fun p => dY F p) hW]
  simp only [slicePot, mixPot, sliceMass]


/-- Value growth of the test function `slicePot H y + t * mixPot F y`. -/
lemma slice_value_growth_test (F H : G × ℝ → ℝ) (hgH : HGrowth H) (hp : PotGrowth F)
    (y t : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ z : G,
      |slicePot H y z + t * mixPot F y z| ≤ C * (1 + ‖z‖) ^ N := by
  obtain ⟨CH, hCH0, NH, hCH⟩ := hgH
  obtain ⟨CF, hCF0, NF, hCF⟩ := hp.1
  refine ⟨CH * (2 + |y|) ^ NH + |t| * (CF * (2 + |y|) ^ NF), by positivity, max NH NF, fun z => ?_⟩
  have h1 : |slicePot H y z| ≤ CH * (2 + |y|) ^ NH * (1 + ‖z‖) ^ NH := by
    show |H (z, y)| ≤ _
    have h3 : (1 + ‖z‖ + |y|) ^ NH ≤ (2 + |y|) ^ NH * (1 + ‖z‖) ^ NH := by
      calc (1 + ‖z‖ + |y|) ^ NH ≤ (1 + |y| + 1) ^ NH * (1 + ‖z‖) ^ NH :=
            pow_one_add_norm_add_abs_le z y NH
        _ = (2 + |y|) ^ NH * (1 + ‖z‖) ^ NH := by ring
    calc |H (z, y)| ≤ CH * (1 + ‖(z, y)‖) ^ NH := (hCH (z, y)).1
      _ ≤ CH * (1 + ‖z‖ + |y|) ^ NH := by
          refine mul_le_mul_of_nonneg_left ?_ hCH0
          exact pow_le_pow_left₀ (by positivity) (by linarith [norm_pair_le z y]) NH
      _ ≤ CH * ((2 + |y|) ^ NH * (1 + ‖z‖) ^ NH) := mul_le_mul_of_nonneg_left h3 hCH0
      _ = CH * (2 + |y|) ^ NH * (1 + ‖z‖) ^ NH := by ring
  have h2 : |mixPot F y z| ≤ CF * (2 + |y|) ^ NF * (1 + ‖z‖) ^ NF := by
    show |dY F (z, y)| ≤ _
    have h3 : (1 + ‖z‖ + |y|) ^ NF ≤ (2 + |y|) ^ NF * (1 + ‖z‖) ^ NF := by
      calc (1 + ‖z‖ + |y|) ^ NF ≤ (1 + |y| + 1) ^ NF * (1 + ‖z‖) ^ NF :=
            pow_one_add_norm_add_abs_le z y NF
        _ = (2 + |y|) ^ NF * (1 + ‖z‖) ^ NF := by ring
    calc |dY F (z, y)| ≤ CF * (1 + ‖(z, y)‖) ^ NF := (hCF (z, y)).1
      _ ≤ CF * (1 + ‖z‖ + |y|) ^ NF := by
          refine mul_le_mul_of_nonneg_left ?_ hCF0
          exact pow_le_pow_left₀ (by positivity) (by linarith [norm_pair_le z y]) NF
      _ ≤ CF * ((2 + |y|) ^ NF * (1 + ‖z‖) ^ NF) := mul_le_mul_of_nonneg_left h3 hCF0
      _ = CF * (2 + |y|) ^ NF * (1 + ‖z‖) ^ NF := by ring
  have hz1 : (1:ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
  have e1 : (1 + ‖z‖) ^ NH ≤ (1 + ‖z‖) ^ (max NH NF) :=
    pow_le_pow_right₀ hz1 (le_max_left _ _)
  have e2 : (1 + ‖z‖) ^ NF ≤ (1 + ‖z‖) ^ (max NH NF) :=
    pow_le_pow_right₀ hz1 (le_max_right _ _)
  calc |slicePot H y z + t * mixPot F y z|
      ≤ |slicePot H y z| + |t * mixPot F y z| := abs_add_le _ _
    _ = |slicePot H y z| + |t| * |mixPot F y z| := by rw [abs_mul]
    _ ≤ CH * (2 + |y|) ^ NH * (1 + ‖z‖) ^ NH
          + |t| * (CF * (2 + |y|) ^ NF * (1 + ‖z‖) ^ NF) :=
        add_le_add h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg t))
    _ ≤ (CH * (2 + |y|) ^ NH + |t| * (CF * (2 + |y|) ^ NF)) * (1 + ‖z‖) ^ (max NH NF) := by
        have hp1 : (0:ℝ) ≤ CH * (2 + |y|) ^ NH := by positivity
        have hp2 : (0:ℝ) ≤ |t| * (CF * (2 + |y|) ^ NF) := by positivity
        nlinarith [h1, h2, e1, e2, hp1, hp2,
          mul_le_mul_of_nonneg_left e1 hp1, mul_le_mul_of_nonneg_left e2 hp2]


lemma continuous_slice_hessInv_apply (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (y : ℝ) (A B : G → ℝ) (hAc : Continuous (fun z : G => grad A z))
    (hBc : Continuous (fun z : G => grad B z)) :
    Continuous (fun z : G => ⟪hessInv (slicePot F y) z (grad A z), grad B z⟫_ℝ) := by
  have hslice : ∀ z v : G, 2 * Real.pi * ‖v‖ ^ 2
      ≤ fderiv ℝ (fderiv ℝ (slicePot F y)) z v v := by
    intro z v
    rw [fderiv_fderiv_slicePot F y hF z v v]
    have h := hH2 (z, y) (v, 0)
    simpa using h
  have hcont := continuous_hessInv_pair (slicePot F y) (contDiff_slicePot F y 2 hF) hslice
  have h1 : Continuous (fun z : G => hessInv (slicePot F y) z (grad A z)) :=
    hcont.comp (continuous_id.prodMk hAc)
  exact continuous_inner.comp (h1.prodMk hBc)

lemma integrable_slice_hessInv_pair (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (y : ℝ) (A B : G → ℝ) (hAc : Continuous (fun z : G => grad A z))
    (hBc : Continuous (fun z : G => grad B z))
    {C1 C2 : ℝ} (hC10 : 0 ≤ C1) (hC20 : 0 ≤ C2) {N1 N2 : ℕ}
    (hA : ∀ z : G, ‖grad A z‖ ≤ C1 * (1 + ‖z‖ + |y|) ^ N1)
    (hB : ∀ z : G, ‖grad B z‖ ≤ C2 * (1 + ‖z‖ + |y|) ^ N2) :
    Integrable (fun z : G => ⟪hessInv (slicePot F y) z (grad A z), grad B z⟫_ℝ
      * Real.exp (-(F (z, y)))) := by
  have hslice : ∀ z v : G, 2 * Real.pi * ‖v‖ ^ 2
      ≤ fderiv ℝ (fderiv ℝ (slicePot F y)) z v v := by
    intro z v
    rw [fderiv_fderiv_slicePot F y hF z v v]
    have h := hH2 (z, y) (v, 0)
    simpa using h
  have hinj : ∀ z : G, Function.Injective (hessOp (slicePot F y) z) :=
    fun z => hessOp_injective _ z (hslice z)
  have hK0 : (0 : ℝ) ≤ C1 * C2 := by positivity
  have hdom : Integrable (fun z : G =>
      (C1 * C2 * (1 + |y| + 1) ^ (N1 + N2) * (1 + ‖z‖) ^ (N1 + N2))
        * Real.exp (-(F (z, y)))) := by
    refine integrable_slice_mul F hF hp y
      (fun p : G × ℝ => C1 * C2 * (1 + |y| + 1) ^ (N1 + N2) * (1 + ‖p.1‖) ^ (N1 + N2))
      ?_ (C1 * C2 * (1 + |y| + 1) ^ (N1 + N2)) (by positivity) (N1 + N2) ?_
    · fun_prop
    · intro p
      have h1 : ‖p.1‖ ≤ ‖p‖ := by rw [Prod.norm_def]; exact le_max_left _ _
      have h2 : (1 + ‖p.1‖) ^ (N1 + N2) ≤ (1 + ‖p‖) ^ (N1 + N2) :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ C1 * C2),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (1+|y|+1)^(N1+N2)),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (1+‖p.1‖)^(N1+N2))]
      have e : C1 * C2 * (1 + |y| + 1) ^ (N1 + N2) * (1 + ‖p.1‖) ^ (N1 + N2)
          = (C1 * C2 * (1 + |y| + 1) ^ (N1 + N2)) * (1 + ‖p.1‖) ^ (N1 + N2) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hmeas : AEStronglyMeasurable
      (fun z : G => ⟪hessInv (slicePot F y) z (grad A z), grad B z⟫_ℝ
        * Real.exp (-(F (z, y)))) :=
    ((continuous_slice_hessInv_apply F hF hH2 y A B hAc hBc).mul
      (Real.continuous_exp.comp ((hF.continuous.comp (by fun_prop)).neg))).aestronglyMeasurable
  refine Integrable.mono' hdom hmeas ?_
  filter_upwards with z
  have hbnd : |⟪hessInv (slicePot F y) z (grad A z), grad B z⟫_ℝ|
      ≤ ‖grad A z‖ * ‖grad B z‖ / (2 * Real.pi) := by
    have hn := hessInv_norm_le (slicePot F y) z (hinj z) (hslice z) (grad A z)
    calc |⟪hessInv (slicePot F y) z (grad A z), grad B z⟫_ℝ|
        ≤ ‖hessInv (slicePot F y) z (grad A z)‖ * ‖grad B z‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖grad A z‖ / (2 * Real.pi)) * ‖grad B z‖ :=
          mul_le_mul_of_nonneg_right hn (norm_nonneg _)
      _ = ‖grad A z‖ * ‖grad B z‖ / (2 * Real.pi) := by ring
  have hkey : |⟪hessInv (slicePot F y) z (grad A z), grad B z⟫_ℝ|
      ≤ C1 * C2 * (1 + |y| + 1) ^ (N1 + N2) * (1 + ‖z‖) ^ (N1 + N2) := by
    have hX : 0 ≤ ‖grad A z‖ * ‖grad B z‖ := by positivity
    have h1 : ‖grad A z‖ * ‖grad B z‖ / (2 * Real.pi) ≤ ‖grad A z‖ * ‖grad B z‖ := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)]
      nlinarith [hX, Real.pi_gt_three]
    have h2 : ‖grad A z‖ * ‖grad B z‖ ≤ C1 * C2 * (1 + ‖z‖ + |y|) ^ (N1 + N2) := by
      have h := mul_le_mul (hA z) (hB z) (norm_nonneg (grad B z))
        (by positivity : (0:ℝ) ≤ C1 * (1 + ‖z‖ + |y|) ^ N1)
      calc ‖grad A z‖ * ‖grad B z‖
          ≤ (C1 * (1 + ‖z‖ + |y|) ^ N1) * (C2 * (1 + ‖z‖ + |y|) ^ N2) := h
        _ = C1 * C2 * (1 + ‖z‖ + |y|) ^ (N1 + N2) := by rw [pow_add]; ring
    have h3 : (1 + ‖z‖ + |y|) ^ (N1 + N2)
        ≤ (1 + |y| + 1) ^ (N1 + N2) * (1 + ‖z‖) ^ (N1 + N2) :=
      pow_one_add_norm_add_abs_le z y (N1 + N2)
    have h4 : C1 * C2 * (1 + ‖z‖ + |y|) ^ (N1 + N2)
        ≤ C1 * C2 * ((1 + |y| + 1) ^ (N1 + N2) * (1 + ‖z‖) ^ (N1 + N2)) :=
      mul_le_mul_of_nonneg_left h3 hK0
    have h5 : C1 * C2 * ((1 + |y| + 1) ^ (N1 + N2) * (1 + ‖z‖) ^ (N1 + N2))
        = C1 * C2 * (1 + |y| + 1) ^ (N1 + N2) * (1 + ‖z‖) ^ (N1 + N2) := by ring
    linarith [hbnd, h1, h2, h4, le_of_eq h5]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
  exact mul_le_mul_of_nonneg_right hkey (Real.exp_pos _).le

lemma norm_hessOp_slice_sub_le (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (z z' : G) (y y' : ℝ) :
    ‖hessOp (slicePot F y) z - hessOp (slicePot F y') z'‖
      ≤ ‖fderiv ℝ (fderiv ℝ F) (z, y) - fderiv ℝ (fderiv ℝ F) (z', y')‖ := by
  set D := fderiv ℝ (fderiv ℝ F) (z, y) - fderiv ℝ (fderiv ℝ F) (z', y') with hDdef
  have hD0 : 0 ≤ ‖D‖ := norm_nonneg _
  refine ContinuousLinearMap.opNorm_le_bound _ hD0 (fun v => ?_)
  by_cases hv : (hessOp (slicePot F y) z - hessOp (slicePot F y') z') v = 0
  · rw [hv, norm_zero]; positivity
  · set w : G := (hessOp (slicePot F y) z - hessOp (slicePot F y') z') v with hwdef
    have hwne : w ≠ 0 := by rw [hwdef]; exact hv
    have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr hwne
    have hself : ⟪w, w⟫_ℝ = ‖w‖ ^ 2 := real_inner_self_eq_norm_sq w
    have hkey : ⟪(hessOp (slicePot F y) z - hessOp (slicePot F y') z') v, w⟫_ℝ
        = D (ContinuousLinearMap.inl ℝ G ℝ v) (ContinuousLinearMap.inl ℝ G ℝ w) := by
      rw [sub_apply, inner_sub_left, hessOp_spec, hessOp_spec,
        fderiv_fderiv_slicePot F y hF z v w, fderiv_fderiv_slicePot F y' hF z' v w, hDdef]
      simp only [sub_apply, ContinuousLinearMap.inl_apply]
    have hle : D (ContinuousLinearMap.inl ℝ G ℝ v) (ContinuousLinearMap.inl ℝ G ℝ w)
        ≤ ‖D‖ * ‖v‖ * ‖w‖ := by
      calc D (ContinuousLinearMap.inl ℝ G ℝ v) (ContinuousLinearMap.inl ℝ G ℝ w)
          ≤ |D (ContinuousLinearMap.inl ℝ G ℝ v) (ContinuousLinearMap.inl ℝ G ℝ w)| :=
            le_abs_self _
        _ ≤ ‖D‖ * ‖ContinuousLinearMap.inl ℝ G ℝ v‖
              * ‖ContinuousLinearMap.inl ℝ G ℝ w‖ := by
            rw [← Real.norm_eq_abs]
            exact ContinuousLinearMap.le_opNorm₂ D _ _
        _ = ‖D‖ * ‖v‖ * ‖w‖ := by
            rw [show ‖ContinuousLinearMap.inl ℝ G ℝ v‖ = ‖v‖ from by
                  rw [ContinuousLinearMap.inl_apply]; simp,
                show ‖ContinuousLinearMap.inl ℝ G ℝ w‖ = ‖w‖ from by
                  rw [ContinuousLinearMap.inl_apply]; simp]
    have h1 : ‖w‖ ^ 2 ≤ ‖D‖ * ‖v‖ * ‖w‖ := by
      rw [← hself]
      calc ⟪w, w⟫_ℝ
          = ⟪(hessOp (slicePot F y) z - hessOp (slicePot F y') z') v, w⟫_ℝ := by
            conv_lhs => rw [hwdef]
        _ = D (ContinuousLinearMap.inl ℝ G ℝ v) (ContinuousLinearMap.inl ℝ G ℝ w) := hkey
        _ ≤ ‖D‖ * ‖v‖ * ‖w‖ := hle
    have h2 : ‖w‖ * ‖w‖ ≤ (‖D‖ * ‖v‖) * ‖w‖ := by
      rw [← sq]; linarith [h1]
    have h3 : ‖w‖ ≤ ‖D‖ * ‖v‖ := le_of_mul_le_mul_right h2 hw0
    rw [hwdef] at h3
    exact h3

lemma continuous_hessOp_slice (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) :
    Continuous (fun p : G × ℝ => hessOp (slicePot F p.2) p.1) := by
  have hD : Continuous (fun p : G × ℝ => fderiv ℝ (fderiv ℝ F) p) := by
    have h2 : ContDiff ℝ 1 (fderiv ℝ F) :=
      ((contDiff_succ_iff_fderiv (𝕜 := ℝ) (n := 1) (f := F)).mp hF).2.2
    exact h2.continuous_fderiv (by norm_num)
  rw [Metric.continuous_iff]
  rintro p₀ ε hε
  obtain ⟨δ, hδ0, hδ⟩ := (Metric.continuous_iff.mp hD) p₀ ε hε
  refine ⟨δ, hδ0, fun p hp => ?_⟩
  have h2' := hδ p hp
  rw [dist_eq_norm] at h2' ⊢
  exact lt_of_le_of_lt (norm_hessOp_slice_sub_le F hF p.1 p₀.1 p.2 p₀.2) h2'

lemma continuous_hessInv_pair_y (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v) :
    Continuous (fun q : (G × ℝ) × G => hessInv (slicePot F q.1.2) q.1.1 q.2) := by
  have hslice : ∀ (p : G × ℝ) (v : G),
      2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (slicePot F p.2)) p.1 v v := by
    intro p v
    rw [fderiv_fderiv_slicePot F p.2 hF p.1 v v]
    have h := hH2 p (v, 0)
    simpa using h
  have hinj : ∀ p : G × ℝ, Function.Injective (hessOp (slicePot F p.2) p.1) :=
    fun p => hessOp_injective _ _ (hslice p)
  have := continuous_inverse_family (E := G)
    (fun p : G × ℝ => hessOp (slicePot F p.2) p.1)
    (fun p u => hessInv (slicePot F p.2) p.1 u)
    (continuous_hessOp_slice F hF)
    (fun p v => by rw [hessOp_spec]; exact hslice p v)
    (fun p u => hessInv_left _ _ (hinj p) u)
    (fun p u => hessInv_right _ _ (hinj p) u)
    (fun p u => hessInv_norm_le _ _ (hinj p) (hslice p) u)
  exact this

/-- The gradient of the slice of `A` at height `p.2`, evaluated at `p.1`. -/
noncomputable def gradSlice (A : G × ℝ → ℝ) (p : G × ℝ) : G := grad (slicePot A p.2) p.1

lemma continuous_gradSlice (H : G × ℝ → ℝ) (hH : ContDiff ℝ 1 H) :
    Continuous (fun p : G × ℝ => gradSlice H p) := by
  have h1 : (fun p : G × ℝ => gradSlice H p)
      = fun p => grad (slicePot H p.2) p.1 := rfl
  rw [h1]
  have h1' : (fun p : G × ℝ => grad (slicePot H p.2) p.1)
      = fun p => (InnerProductSpace.toDual ℝ G).symm
          ((fderiv ℝ H p).comp (ContinuousLinearMap.inl ℝ G ℝ)) := by
    funext p
    rw [grad]
    congr 1
    ext v
    rw [fderiv_slicePot H p.2 p.1 v (hH.contDiffAt.differentiableAt (by norm_num))]
    rfl
  rw [h1']
  exact ((InnerProductSpace.toDual ℝ G).symm.continuous).comp
    ((hH.continuous_fderiv (by norm_num)).clm_comp_const (ContinuousLinearMap.inl ℝ G ℝ))

lemma continuous_slice_hessInv_bilin (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (ψ χ : G × ℝ → G) (hψ : Continuous ψ) (hχ : Continuous χ) :
    Continuous (fun p : G × ℝ => ⟪hessInv (slicePot F p.2) p.1 (ψ p), χ p⟫_ℝ) :=
  continuous_inner.comp
    (((continuous_hessInv_pair_y F hF hH2).comp (continuous_id.prodMk hψ)).prodMk hχ)

lemma integrable_gradSlice_bilin (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (A B : G × ℝ → ℝ) (hAc : Continuous (fun p : G × ℝ => gradSlice A p))
    (hBc : Continuous (fun p : G × ℝ => gradSlice B p))
    {C1 C2 : ℝ} (hC10 : 0 ≤ C1) (hC20 : 0 ≤ C2) {N1 N2 : ℕ}
    (hA : ∀ p : G × ℝ, ‖gradSlice A p‖ ≤ C1 * (1 + ‖p‖) ^ N1)
    (hB : ∀ p : G × ℝ, ‖gradSlice B p‖ ≤ C2 * (1 + ‖p‖) ^ N2) :
    Integrable (fun p : G × ℝ =>
      ⟪hessInv (slicePot F p.2) p.1 (gradSlice A p), gradSlice B p⟫_ℝ * Real.exp (-(F p))) := by
  have hslice : ∀ (p : G × ℝ) (v : G),
      2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (slicePot F p.2)) p.1 v v := by
    intro p v
    rw [fderiv_fderiv_slicePot F p.2 hF p.1 v v]
    have h := hH2 p (v, 0)
    simpa using h
  have hinj : ∀ p : G × ℝ, Function.Injective (hessOp (slicePot F p.2) p.1) :=
    fun p => hessOp_injective _ _ (hslice p)
  have hdom : Integrable (fun p : G × ℝ =>
      (C1 * C2 * (1 + ‖p‖) ^ (N1 + N2)) * Real.exp (-(F p))) := by
    refine integrable_mul_exp_neg_potGrowth F (fun p : G × ℝ => C1 * C2 * (1 + ‖p‖) ^ (N1 + N2))
      hF hp ?_ (C1 * C2) (by positivity) (N1 + N2) ?_
    · fun_prop
    · intro p
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ C1 * C2 * (1 + ‖p‖) ^ (N1 + N2))]
  have hmeas : AEStronglyMeasurable (fun p : G × ℝ =>
      ⟪hessInv (slicePot F p.2) p.1 (gradSlice A p), gradSlice B p⟫_ℝ * Real.exp (-(F p))) :=
    ((continuous_slice_hessInv_bilin F hF hH2 _ _ hAc hBc).mul
      (Real.continuous_exp.comp (hF.continuous.neg))).aestronglyMeasurable
  refine Integrable.mono' hdom hmeas ?_
  filter_upwards with p
  have hbnd : |⟪hessInv (slicePot F p.2) p.1 (gradSlice A p), gradSlice B p⟫_ℝ|
      ≤ ‖gradSlice A p‖ * ‖gradSlice B p‖ / (2 * Real.pi) := by
    have hn := hessInv_norm_le (slicePot F p.2) p.1 (hinj p) (hslice p) (gradSlice A p)
    calc |⟪hessInv (slicePot F p.2) p.1 (gradSlice A p), gradSlice B p⟫_ℝ|
        ≤ ‖hessInv (slicePot F p.2) p.1 (gradSlice A p)‖ * ‖gradSlice B p‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ (‖gradSlice A p‖ / (2 * Real.pi)) * ‖gradSlice B p‖ :=
          mul_le_mul_of_nonneg_right hn (norm_nonneg _)
      _ = ‖gradSlice A p‖ * ‖gradSlice B p‖ / (2 * Real.pi) := by ring
  have hX : 0 ≤ ‖gradSlice A p‖ * ‖gradSlice B p‖ := by positivity
  have h1 : ‖gradSlice A p‖ * ‖gradSlice B p‖ / (2 * Real.pi)
      ≤ ‖gradSlice A p‖ * ‖gradSlice B p‖ := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)]
    nlinarith [hX, Real.pi_gt_three]
  have h2 : ‖gradSlice A p‖ * ‖gradSlice B p‖ ≤ C1 * C2 * (1 + ‖p‖) ^ (N1 + N2) := by
    have h := mul_le_mul (hA p) (hB p) (norm_nonneg _)
      (by positivity : (0:ℝ) ≤ C1 * (1 + ‖p‖) ^ N1)
    calc ‖gradSlice A p‖ * ‖gradSlice B p‖
        ≤ (C1 * (1 + ‖p‖) ^ N1) * (C2 * (1 + ‖p‖) ^ N2) := h
      _ = C1 * C2 * (1 + ‖p‖) ^ (N1 + N2) := by rw [pow_add]; ring
  have hkey : |⟪hessInv (slicePot F p.2) p.1 (gradSlice A p), gradSlice B p⟫_ℝ|
      ≤ C1 * C2 * (1 + ‖p‖) ^ (N1 + N2) := le_trans hbnd (le_trans h1 h2)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
  exact mul_le_mul_of_nonneg_right hkey (Real.exp_pos _).le

lemma integrable_gradSlice_bilin_y (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (A B : G × ℝ → ℝ) (hAc : Continuous (fun p : G × ℝ => gradSlice A p))
    (hBc : Continuous (fun p : G × ℝ => gradSlice B p))
    {C1 C2 : ℝ} (hC10 : 0 ≤ C1) (hC20 : 0 ≤ C2) {N1 N2 : ℕ}
    (hA : ∀ p : G × ℝ, ‖gradSlice A p‖ ≤ C1 * (1 + ‖p‖) ^ N1)
    (hB : ∀ p : G × ℝ, ‖gradSlice B p‖ ≤ C2 * (1 + ‖p‖) ^ N2) :
    Integrable (fun y : ℝ => ∫ z : G,
      ⟪hessInv (slicePot F y) z (grad (slicePot A y) z), grad (slicePot B y) z⟫_ℝ
        * Real.exp (-(F (z, y)))) := by
  have h := integrable_gradSlice_bilin F hF hp hH2 A B hAc hBc hC10 hC20 hA hB
  rw [Measure.volume_eq_prod G ℝ] at h
  exact h.integral_prod_right

lemma grad_slice_add_smul (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hH : ContDiff ℝ 1 H)
    (y t : ℝ) (z : G) :
    grad (fun z => slicePot H y z + t * mixPot F y z) z
      = grad (slicePot H y) z + t • grad (mixPot F y) z := by
  have hslice : DifferentiableAt ℝ (slicePot H y) z :=
    ((contDiff_slicePot H y 1 hH).contDiffAt).differentiableAt (by norm_num)
  have hmix : DifferentiableAt ℝ (mixPot F y) z := by
    show DifferentiableAt ℝ (fun z' : G => dY F (z', y)) z
    exact (((contDiff_dY F hF).contDiffAt).differentiableAt (by norm_num)).comp z (by fun_prop)
  have hfun : (fun z : G => slicePot H y z + t * mixPot F y z)
      = slicePot H y + t • mixPot F y := by
    funext z'; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun, grad_add _ _ z hslice (hmix.const_smul t)]
  congr 1
  exact grad_const_mul t (mixPot F y) z hmix

lemma slice_deriv_growth_test (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hH : ContDiff ℝ 1 H)
    (hderivH : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ H p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖)
    (hdiag : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ (fderiv ℝ F) p v v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2)
    (y t : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ z v : G,
      |fderiv ℝ (fun z => slicePot H y z + t * mixPot F y z) z v| ≤ C * (1 + ‖z‖) ^ N * ‖v‖ := by
  obtain ⟨CH, hCH0, NH, hCH⟩ := hderivH
  obtain ⟨CF, hCF0, NF, hCF⟩ := hdiag
  obtain ⟨C1, hC10, M1, hC1⟩ := grad_slicePot_growth H CH hCH0 NH hCH hH y
  obtain ⟨C2, hC20, M2, hC2⟩ := grad_mixPot_growth F hF CF hCF0 NF hCF y
  refine ⟨C1 * (2 + |y|) ^ M1 + |t| * (C2 * (2 + |y|) ^ M2), by positivity, max M1 M2,
    fun z v => ?_⟩
  rw [← grad_spec, grad_slice_add_smul F H hF hH y t z]
  have hb1 : ‖grad (slicePot H y) z‖ ≤ C1 * (2 + |y|) ^ M1 * (1 + ‖z‖) ^ M1 := by
    have h3 : (1 + ‖z‖ + |y|) ^ M1 ≤ (2 + |y|) ^ M1 * (1 + ‖z‖) ^ M1 := by
      have hb : (1 : ℝ) + |y| + 1 = 2 + |y| := by ring
      calc (1 + ‖z‖ + |y|) ^ M1 ≤ (1 + |y| + 1) ^ M1 * (1 + ‖z‖) ^ M1 :=
            pow_one_add_norm_add_abs_le z y M1
        _ = (2 + |y|) ^ M1 * (1 + ‖z‖) ^ M1 := by rw [hb]
    calc ‖grad (slicePot H y) z‖ ≤ C1 * (1 + ‖z‖ + |y|) ^ M1 := hC1 z
      _ ≤ C1 * ((2 + |y|) ^ M1 * (1 + ‖z‖) ^ M1) := mul_le_mul_of_nonneg_left h3 hC10
      _ = C1 * (2 + |y|) ^ M1 * (1 + ‖z‖) ^ M1 := by ring
  have hb2 : ‖grad (mixPot F y) z‖ ≤ C2 * (2 + |y|) ^ M2 * (1 + ‖z‖) ^ M2 := by
    have h3 : (1 + ‖z‖ + |y|) ^ M2 ≤ (2 + |y|) ^ M2 * (1 + ‖z‖) ^ M2 := by
      have hb : (1 : ℝ) + |y| + 1 = 2 + |y| := by ring
      calc (1 + ‖z‖ + |y|) ^ M2 ≤ (1 + |y| + 1) ^ M2 * (1 + ‖z‖) ^ M2 :=
            pow_one_add_norm_add_abs_le z y M2
        _ = (2 + |y|) ^ M2 * (1 + ‖z‖) ^ M2 := by rw [hb]
    calc ‖grad (mixPot F y) z‖ ≤ C2 * (1 + ‖z‖ + |y|) ^ M2 := hC2 z
      _ ≤ C2 * ((2 + |y|) ^ M2 * (1 + ‖z‖) ^ M2) := mul_le_mul_of_nonneg_left h3 hC20
      _ = C2 * (2 + |y|) ^ M2 * (1 + ‖z‖) ^ M2 := by ring
  have hsum : ‖grad (slicePot H y) z + t • grad (mixPot F y) z‖
      ≤ ‖grad (slicePot H y) z‖ + |t| * ‖grad (mixPot F y) z‖ := by
    calc ‖grad (slicePot H y) z + t • grad (mixPot F y) z‖
        ≤ ‖grad (slicePot H y) z‖ + ‖t • grad (mixPot F y) z‖ := norm_add_le _ _
      _ = ‖grad (slicePot H y) z‖ + |t| * ‖grad (mixPot F y) z‖ := by
          rw [norm_smul, Real.norm_eq_abs]
  have hz1 : (1:ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
  have e1 : (1 + ‖z‖) ^ M1 ≤ (1 + ‖z‖) ^ (max M1 M2) :=
    pow_le_pow_right₀ hz1 (le_max_left _ _)
  have e2 : (1 + ‖z‖) ^ M2 ≤ (1 + ‖z‖) ^ (max M1 M2) :=
    pow_le_pow_right₀ hz1 (le_max_right _ _)
  have hp1 : (0:ℝ) ≤ C1 * (2 + |y|) ^ M1 := by positivity
  have hp2 : (0:ℝ) ≤ |t| * (C2 * (2 + |y|) ^ M2) := by positivity
  calc |⟪grad (slicePot H y) z + t • grad (mixPot F y) z, v⟫_ℝ|
      ≤ ‖grad (slicePot H y) z + t • grad (mixPot F y) z‖ * ‖v‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ (‖grad (slicePot H y) z‖ + |t| * ‖grad (mixPot F y) z‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right hsum (norm_nonneg v)
    _ ≤ (C1 * (2 + |y|) ^ M1 * (1 + ‖z‖) ^ M1
          + |t| * (C2 * (2 + |y|) ^ M2 * (1 + ‖z‖) ^ M2)) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (add_le_add hb1 (mul_le_mul_of_nonneg_left hb2 (abs_nonneg t)))
          (norm_nonneg v)
    _ ≤ (C1 * (2 + |y|) ^ M1 + |t| * (C2 * (2 + |y|) ^ M2))
          * (1 + ‖z‖) ^ (max M1 M2) * ‖v‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg v)
        nlinarith [e1, e2, hp1, hp2, mul_le_mul_of_nonneg_left e1 hp1,
          mul_le_mul_of_nonneg_left e2 hp2]

lemma sliceGrowth_test (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hgH : HGrowth H) (hH : ContDiff ℝ 1 H)
    (hderivH : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ H p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖)
    (hdiag : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ (fderiv ℝ F) p v v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2)
    (y t : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ z v : G,
      |slicePot H y z + t * mixPot F y z| ≤ C * (1 + ‖z‖) ^ N ∧
      |fderiv ℝ (fun z => slicePot H y z + t * mixPot F y z) z v|
        ≤ C * (1 + ‖z‖) ^ N * ‖v‖ := by
  obtain ⟨Cv, hCv0, Nv, hCv⟩ := slice_value_growth_test F H hgH hp y t
  obtain ⟨Cd, hCd0, Nd, hCd⟩ := slice_deriv_growth_test F H hF hH hderivH hdiag y t
  refine ⟨Cv + Cd, by positivity, max Nv Nd, fun z v => ⟨?_, ?_⟩⟩
  · have hz1 : (1:ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
    have e : (1 + ‖z‖) ^ Nv ≤ (1 + ‖z‖) ^ (max Nv Nd) := pow_le_pow_right₀ hz1 (le_max_left _ _)
    calc |slicePot H y z + t * mixPot F y z| ≤ Cv * (1 + ‖z‖) ^ Nv := hCv z
      _ ≤ Cv * (1 + ‖z‖) ^ (max Nv Nd) := mul_le_mul_of_nonneg_left e hCv0
      _ ≤ (Cv + Cd) * (1 + ‖z‖) ^ (max Nv Nd) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · have hz1 : (1:ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
    have e : (1 + ‖z‖) ^ Nd ≤ (1 + ‖z‖) ^ (max Nv Nd) := pow_le_pow_right₀ hz1 (le_max_right _ _)
    calc |fderiv ℝ (fun z => slicePot H y z + t * mixPot F y z) z v| ≤ Cd * (1 + ‖z‖) ^ Nd * ‖v‖ :=
          hCd z v
      _ ≤ Cd * (1 + ‖z‖) ^ (max Nv Nd) * ‖v‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg v)
          exact mul_le_mul_of_nonneg_left e hCd0
      _ ≤ (Cv + Cd) * (1 + ‖z‖) ^ (max Nv Nd) * ‖v‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg v)
          exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

lemma continuous_gradSlice_fixed (H : G × ℝ → ℝ) (hH : ContDiff ℝ 1 H) (y : ℝ) :
    Continuous (fun z : G => grad (slicePot H y) z) :=
  (continuous_gradSlice H hH).comp (continuous_id.prodMk continuous_const)

lemma bl_slice_quad (IH : BLon G) (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hH : ContDiff ℝ 1 H)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (hconv : ConvexOn ℝ Set.univ (fun p : G × ℝ => F p - Real.pi * (‖p.1‖ ^ 2 + p.2 ^ 2)))
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ F p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ F) p v v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2)
    (hp : PotGrowth F) (hgH : HGrowth H)
    (hderivH : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ H p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖)
    (y : ℝ) :
    ∀ t : ℝ, 0 ≤ (sliceEnergy F y (slicePot H y) / sliceMass F y - condVar F H y)
      + 2 * t * (sliceCrossEnergy F y (slicePot H y) (mixPot F y) / sliceMass F y
          - condCov F H (fun p => dY F p) y)
      + t ^ 2 * (sliceEnergy F y (mixPot F y) / sliceMass F y
          - condVar F (fun p => dY F p) y) := by
  intro t
  have hW : 0 < sliceMass F y := sliceMass_pos F hF hp y
  have hWne : sliceMass F y ≠ 0 := ne_of_gt hW
  have hgf' := hgf
  have hgH' := hgH
  obtain ⟨CF, hCF0, NF, hCF⟩ := hgf'
  obtain ⟨CH, hCH0, NH, hCH⟩ := hgH'
  have hdYcd : ContDiff ℝ 1 (dY F) := contDiff_dY F hF
  have hderivH' := hderivH
  obtain ⟨Ch, hCh0, Nh, hCh⟩ := hderivH'
  have hdiag : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ (fderiv ℝ F) p v v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2 :=
    ⟨CF, hCF0, NF, fun p v => (hCF p v).2⟩
  have hgradD : ∀ p : G × ℝ, |dY F p| ≤ CF * (1 + ‖p‖) ^ NF := by
    intro p
    have h := (hCF p (0, 1)).1
    rw [show ‖((0,1) : G × ℝ)‖ = 1 from by simp, mul_one] at h
    simpa [dY] using h
  -- the test function
  have hGfcd : ContDiff ℝ 1 (fun z : G => slicePot H y z + t * mixPot F y z) := by
    refine (contDiff_slicePot H y 1 hH).add ?_
    have h1 : ContDiff ℝ 1 (fun z : G => dY F (z, y)) :=
      (contDiff_dY F hF).comp (by fun_prop : ContDiff ℝ 1 (fun z : G => (z, y)))
    exact ContDiff.const_smul t h1
  obtain ⟨Cv, hCv0, Nv, hCv⟩ := sliceGrowth_test F H hF hp hgH hH hderivH hdiag y t
  have hGgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ z v : G,
      |(fun z : G => slicePot H y z + t * mixPot F y z) z| ≤ C * (1 + ‖z‖) ^ N ∧
      |fderiv ℝ (fun z : G => slicePot H y z + t * mixPot F y z) z v|
        ≤ C * (1 + ‖z‖) ^ N * ‖v‖ := ⟨Cv, hCv0, Nv, hCv⟩
  have hBL := slice_BL IH F hF hH2 hconv hgf y _ hGfcd hGgf
  -- wVar integrability hypotheses
  have hpH : Integrable (fun z : G => slicePot H y z * Real.exp (-(slicePot F y z))) := by
    simpa only [slicePot] using integrable_slice_mul F hF hp y H hH.continuous CH hCH0 NH
      (fun p => (hCH p).1)
  have hqH : Integrable (fun z : G => slicePot H y z ^ 2 * Real.exp (-(slicePot F y z))) := by
    refine (integrable_slice_mul F hF hp y (fun p => H p ^ 2) (hH.continuous.pow 2)
      (CH ^ 2) (by positivity) (NH * 2) ?_).congr ?_
    · intro p
      rw [abs_of_nonneg (sq_nonneg (H p))]
      calc H p ^ 2 ≤ (CH * (1 + ‖p‖) ^ NH) ^ 2 :=
            sq_le_sq' (abs_le.mp (hCH p).1).1 (abs_le.mp (hCH p).1).2
        _ = CH ^ 2 * (1 + ‖p‖) ^ (NH * 2) := by rw [mul_pow, pow_mul]
    · filter_upwards with z
      simp only [slicePot]
  have hpD : Integrable (fun z : G => mixPot F y z * Real.exp (-(slicePot F y z))) := by
    simpa only [slicePot, mixPot] using integrable_slice_mul F hF hp y (fun p => dY F p)
      hdYcd.continuous CF hCF0 NF hgradD
  have hqD : Integrable (fun z : G => mixPot F y z ^ 2 * Real.exp (-(slicePot F y z))) := by
    refine (integrable_slice_mul F hF hp y (fun p => dY F p ^ 2) (hdYcd.continuous.pow 2)
      (CF ^ 2) (by positivity) (NF * 2) ?_).congr ?_
    · intro p
      rw [abs_of_nonneg (sq_nonneg (dY F p))]
      calc dY F p ^ 2 ≤ (CF * (1 + ‖p‖) ^ NF) ^ 2 :=
            sq_le_sq' (abs_le.mp (hgradD p)).1 (abs_le.mp (hgradD p)).2
        _ = CF ^ 2 * (1 + ‖p‖) ^ (NF * 2) := by rw [mul_pow, pow_mul]
    · filter_upwards with z
      simp only [slicePot, mixPot]
  have hpHD : Integrable (fun z : G => slicePot H y z * mixPot F y z * Real.exp (-(slicePot F y z))) := by
    refine (integrable_slice_mul F hF hp y (fun p => H p * dY F p)
      (hH.continuous.mul hdYcd.continuous) (CH * CF) (by positivity) (NH + NF) ?_).congr ?_
    · intro p
      have h1 : |H p| ≤ CH * (1 + ‖p‖) ^ NH := (hCH p).1
      have h2 : |dY F p| ≤ CF * (1 + ‖p‖) ^ NF := hgradD p
      rw [abs_mul]
      calc |H p| * |dY F p| ≤ (CH * (1 + ‖p‖) ^ NH) * (CF * (1 + ‖p‖) ^ NF) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = CH * CF * (1 + ‖p‖) ^ (NH + NF) := by rw [pow_add]; ring
    · filter_upwards with z
      simp only [slicePot, mixPot]
  -- the BL inequality
  have hWQ := wVar_quad (fun z : G => Real.exp (-(slicePot F y z))) (slicePot H y) (mixPot F y) t
    hqH hpHD hqD hpH hpD
  -- the slice energy expansion
  obtain ⟨C1, hC10, M1, hC1⟩ := grad_slicePot_growth H Ch hCh0 Nh hCh hH y
  obtain ⟨C2, hC20, M2, hC2⟩ := grad_mixPot_growth F hF CF hCF0 NF (fun p v => (hCF p v).2) y
  have hIntA : Integrable (fun z : G => ⟪hessInv (slicePot F y) z (grad (slicePot H y) z),
      grad (slicePot H y) z⟫_ℝ * Real.exp (-(slicePot F y z))) :=
    integrable_slice_hessInv_pair F hF hp hH2 y (slicePot H y) (slicePot H y)
      (continuous_gradSlice_fixed H hH y) (continuous_gradSlice_fixed H hH y)
      hC10 hC10 hC1 hC1
  have hIntB : Integrable (fun z : G => ⟪hessInv (slicePot F y) z (grad (mixPot F y) z),
      grad (mixPot F y) z⟫_ℝ * Real.exp (-(slicePot F y z))) :=
    integrable_slice_hessInv_pair F hF hp hH2 y (mixPot F y) (mixPot F y)
      (continuous_gradSlice_fixed (dY F) hdYcd y)
      (continuous_gradSlice_fixed (dY F) hdYcd y)
      hC20 hC20 hC2 hC2
  have hIntAB : Integrable (fun z : G => ⟪hessInv (slicePot F y) z (grad (slicePot H y) z),
      grad (mixPot F y) z⟫_ℝ * Real.exp (-(slicePot F y z))) :=
    integrable_slice_hessInv_pair F hF hp hH2 y (slicePot H y) (mixPot F y)
      (continuous_gradSlice_fixed H hH y)
      (continuous_gradSlice_fixed (dY F) hdYcd y)
      hC10 hC20 hC1 hC2
  have hdAH : Differentiable ℝ (slicePot H y) := by
    rw [show slicePot H y = fun z : G => H (z, y) from rfl]
    exact fun z => (hH.contDiffAt.differentiableAt (by norm_num)).comp z (by fun_prop)
  have hdBM : Differentiable ℝ (mixPot F y) := by
    show Differentiable ℝ (fun z : G => dY F (z, y))
    exact fun z => (hdYcd.contDiffAt.differentiableAt (by norm_num)).comp z (by fun_prop)
  have hSE := sliceEnergy_add_smul F hF hH2 y (slicePot H y) (mixPot F y) t hdAH hdBM
    hIntA hIntAB hIntB
  have hSE' : sliceEnergy F y (fun z : G => slicePot H y z + t * mixPot F y z)
      = sliceEnergy F y (slicePot H y)
        + 2 * t * sliceCrossEnergy F y (slicePot H y) (mixPot F y)
        + t ^ 2 * sliceEnergy F y (mixPot F y) := hSE
  -- combine
  have hBL' : wVar (fun x : G => Real.exp (-(slicePot F y x))) (fun z : G => slicePot H y z + t * mixPot F y z)
      ≤ sliceEnergy F y (fun z : G => slicePot H y z + t * mixPot F y z) := hBL
  rw [hSE'] at hBL'
  rw [hWQ] at hBL'
  rw [show wVar (fun x : G => Real.exp (-(slicePot F y x))) (slicePot H y)
        = condVar F H y * sliceMass F y from (condVar_mul_sliceMass_eq F H y hWne).symm] at hBL'
  rw [show wVar (fun x : G => Real.exp (-(slicePot F y x))) (mixPot F y)
        = condVar F (fun p => dY F p) y * sliceMass F y
      from (condVar_mixPot_mul_sliceMass_eq F y hWne).symm] at hBL'
  rw [show (∫ x, slicePot H y x * mixPot F y x * Real.exp (-(slicePot F y x)))
        - (∫ x, slicePot H y x * Real.exp (-(slicePot F y x)))
          * (∫ x, mixPot F y x * Real.exp (-(slicePot F y x))) / (∫ x, Real.exp (-(slicePot F y x)))
        = condCov F H (fun p => dY F p) y * sliceMass F y
      from (condCov_mul_sliceMass_eq F H y hWne).symm] at hBL'
  have h1 : (condVar F H y * sliceMass F y
        + 2 * t * (condCov F H (fun p => dY F p) y * sliceMass F y)
        + t ^ 2 * (condVar F (fun p => dY F p) y * sliceMass F y)) / sliceMass F y
      = condVar F H y + 2 * t * condCov F H (fun p => dY F p) y
        + t ^ 2 * condVar F (fun p => dY F p) y := by
    field_simp
    try ring
  have h2 : (sliceEnergy F y (slicePot H y) + 2 * t * sliceCrossEnergy F y (slicePot H y) (mixPot F y)
        + t ^ 2 * sliceEnergy F y (mixPot F y)) / sliceMass F y
      = sliceEnergy F y (slicePot H y) / sliceMass F y
        + 2 * t * (sliceCrossEnergy F y (slicePot H y) (mixPot F y) / sliceMass F y)
        + t ^ 2 * (sliceEnergy F y (mixPot F y) / sliceMass F y) := by
    field_simp
    try ring
  have hdiv : condVar F H y + 2 * t * condCov F H (fun p => dY F p) y
        + t ^ 2 * condVar F (fun p => dY F p) y
      ≤ sliceEnergy F y (slicePot H y) / sliceMass F y
        + 2 * t * (sliceCrossEnergy F y (slicePot H y) (mixPot F y) / sliceMass F y)
        + t ^ 2 * (sliceEnergy F y (mixPot F y) / sliceMass F y) := by
    rw [← h1, ← h2, div_le_div_iff_of_pos_right hW]
    exact hBL'
  linarith [hdiv]

noncomputable def sliceEnergyFn (F : G × ℝ → ℝ) (p : G × ℝ) : ℝ :=
  ⟪hessInv (slicePot F p.2) p.1 (gradSlice (dY F) p), gradSlice (dY F) p⟫_ℝ

/-- The Schur complement of the slice Hessian in the ambient Hessian, as a function of the point:
`schurPot F (z,y) = D²F(z,y)(0,1)(0,1) - ⟨(Hess_z F)⁻¹ ∇_z ∂_yF, ∇_z ∂_yF⟩`. -/
noncomputable def schurPot (F : G × ℝ → ℝ) (p : G × ℝ) : ℝ := d2Y F p - sliceEnergyFn F p

lemma d2Y_eq_hess (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (p : G × ℝ) :
    d2Y F p = fderiv ℝ (fderiv ℝ F) p (0, 1) (0, 1) := by
  show fderiv ℝ (fun q : G × ℝ => fderiv ℝ F q (0, 1)) p (0, 1) = _
  rw [fderiv_fderiv_eval F hF (0, 1) (0, 1) p]

lemma schurPot_ge_two_pi (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v) (p : G × ℝ) :
    2 * Real.pi ≤ schurPot F p := by
  have h := schur_ge_two_pi F hF hH2 p.2 p.1
  rw [show schurPot F p = fderiv ℝ (fderiv ℝ F) p (0,1) (0,1)
      - ⟪hessInv (slicePot F p.2) p.1 (grad (mixPot F p.2) p.1), grad (mixPot F p.2) p.1⟫_ℝ
    from by rw [schurPot, sliceEnergyFn, d2Y_eq_hess F hF p]; rfl]
  exact h

lemma condMean_sliceEnergyFn (F : G × ℝ → ℝ) (y : ℝ) :
    condMean F (sliceEnergyFn F) y = sliceEnergy F y (mixPot F y) / sliceMass F y := rfl

lemma margD2_eq_schur (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ F p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ F) p v v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2)
    (y : ℝ) (hW : sliceMass F y ≠ 0) :
    margD2 F y = condMean F (schurPot F) y
      + (sliceEnergy F y (mixPot F y) / sliceMass F y - condVar F (fun p => dY F p) y) := by
  obtain ⟨CF, hCF0, NF, hCF⟩ := hgf
  have hdYcd : ContDiff ℝ 1 (dY F) := contDiff_dY F hF
  obtain ⟨C2, hC20, M2, hC2⟩ :=
    grad_mixPot_growth F hF CF hCF0 NF (fun p v => (hCF p v).2) y
  have hIntE : Integrable (fun z : G => sliceEnergyFn F (z, y) * Real.exp (-(F (z, y)))) :=
    integrable_slice_hessInv_pair F hF hp hH2 y (mixPot F y) (mixPot F y)
      (continuous_gradSlice_fixed (dY F) hdYcd y) (continuous_gradSlice_fixed (dY F) hdYcd y)
      hC20 hC20 hC2 hC2
  rw [margD2_eq F hF hp y hW]
  rw [show condMean F (schurPot F) y
      = condMean F (d2Y F) y - condMean F (sliceEnergyFn F) y from
    condMean_sub F (d2Y F) (sliceEnergyFn F) y hW
      (integrable_d2Y_exp_neg F hF hp y) hIntE]
  rw [condMean_sliceEnergyFn F y]
  ring

lemma mixPot_growth (F : G × ℝ → ℝ) (hp : PotGrowth F) (y : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ z : G, |mixPot F y z| ≤ C * (1 + ‖z‖) ^ N := by
  obtain ⟨C, hC0, N, hC⟩ := hp.1
  refine ⟨C * (2 + |y|) ^ N, by positivity, N, fun z => ?_⟩
  show |dY F (z, y)| ≤ _
  have h3 : (1 + ‖z‖ + |y|) ^ N ≤ (2 + |y|) ^ N * (1 + ‖z‖) ^ N := by
    have hb : (1 : ℝ) + |y| + 1 = 2 + |y| := by ring
    rw [← hb]; exact pow_one_add_norm_add_abs_le z y N
  calc |dY F (z, y)| ≤ C * (1 + ‖(z, y)‖) ^ N := (hC (z, y)).1
    _ ≤ C * (1 + ‖z‖ + |y|) ^ N := by
        refine mul_le_mul_of_nonneg_left ?_ hC0
        exact pow_le_pow_left₀ (by positivity) (by linarith [norm_pair_le z y]) N
    _ ≤ C * ((2 + |y|) ^ N * (1 + ‖z‖) ^ N) := mul_le_mul_of_nonneg_left h3 hC0
    _ = C * (2 + |y|) ^ N * (1 + ‖z‖) ^ N := by ring

lemma sliceEnergy_mix_sub_condVar_nonneg (IH : BLon G) (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (hconv : ConvexOn ℝ Set.univ (fun p : G × ℝ => F p - Real.pi * (‖p.1‖ ^ 2 + p.2 ^ 2)))
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ F p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ F) p v v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2)
    (hp : PotGrowth F) (y : ℝ) (hW : 0 < sliceMass F y) :
    0 ≤ sliceEnergy F y (mixPot F y) / sliceMass F y - condVar F (fun p => dY F p) y := by
  have hgf' := hgf
  obtain ⟨CF, hCF0, NF, hCF⟩ := hgf'
  have hdYcd : ContDiff ℝ 1 (dY F) := contDiff_dY F hF
  have hGfcd : ContDiff ℝ 1 (mixPot F y) := by
    show ContDiff ℝ 1 (fun z : G => dY F (z, y))
    exact hdYcd.comp (by fun_prop : ContDiff ℝ 1 (fun z : G => (z, y)))
  obtain ⟨C2, hC20, M2, hC2⟩ :=
    grad_mixPot_growth F hF CF hCF0 NF (fun p v => (hCF p v).2) y
  obtain ⟨Cv, hCv0, Nv, hCv⟩ := mixPot_growth F hp y
  set K : ℝ := Cv + C2 * (2 + |y|) ^ M2 with hKdef
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  have hGgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ z v : G,
      |(mixPot F y) z| ≤ C * (1 + ‖z‖) ^ N ∧
      |fderiv ℝ (mixPot F y) z v| ≤ C * (1 + ‖z‖) ^ N * ‖v‖ := by
    refine ⟨K, hK0, max Nv M2, fun z v => ⟨?_, ?_⟩⟩
    · have hz1 : (1:ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
      have e : (1 + ‖z‖) ^ Nv ≤ (1 + ‖z‖) ^ (max Nv M2) :=
        pow_le_pow_right₀ hz1 (le_max_left _ _)
      calc |(mixPot F y) z| ≤ Cv * (1 + ‖z‖) ^ Nv := hCv z
        _ ≤ Cv * (1 + ‖z‖) ^ (max Nv M2) := mul_le_mul_of_nonneg_left e hCv0
        _ ≤ K * (1 + ‖z‖) ^ (max Nv M2) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            rw [hKdef]; nlinarith [hC20, pow_nonneg (by positivity : (0:ℝ) ≤ 2 + |y|) M2]
    · have hz1 : (1:ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
      have e : (1 + ‖z‖) ^ M2 ≤ (1 + ‖z‖) ^ (max Nv M2) :=
        pow_le_pow_right₀ hz1 (le_max_right _ _)
      have h2 : ‖grad (mixPot F y) z‖ ≤ C2 * (2 + |y|) ^ M2 * (1 + ‖z‖) ^ M2 := by
        have h3 : (1 + ‖z‖ + |y|) ^ M2 ≤ (2 + |y|) ^ M2 * (1 + ‖z‖) ^ M2 := by
          have hb : (1 : ℝ) + |y| + 1 = 2 + |y| := by ring
          calc (1 + ‖z‖ + |y|) ^ M2 ≤ (1 + |y| + 1) ^ M2 * (1 + ‖z‖) ^ M2 :=
                pow_one_add_norm_add_abs_le z y M2
            _ = (2 + |y|) ^ M2 * (1 + ‖z‖) ^ M2 := by rw [hb]
        calc ‖grad (mixPot F y) z‖ ≤ C2 * (1 + ‖z‖ + |y|) ^ M2 := hC2 z
          _ ≤ C2 * ((2 + |y|) ^ M2 * (1 + ‖z‖) ^ M2) := mul_le_mul_of_nonneg_left h3 hC20
          _ = C2 * (2 + |y|) ^ M2 * (1 + ‖z‖) ^ M2 := by ring
      calc |fderiv ℝ (mixPot F y) z v| = |⟪grad (mixPot F y) z, v⟫_ℝ| := by rw [grad_spec]
        _ ≤ ‖grad (mixPot F y) z‖ * ‖v‖ := abs_real_inner_le_norm _ _
        _ ≤ C2 * (2 + |y|) ^ M2 * (1 + ‖z‖) ^ M2 * ‖v‖ :=
            mul_le_mul_of_nonneg_right h2 (norm_nonneg v)
        _ ≤ K * (1 + ‖z‖) ^ (max Nv M2) * ‖v‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg v)
            calc C2 * (2 + |y|) ^ M2 * (1 + ‖z‖) ^ M2
                ≤ C2 * (2 + |y|) ^ M2 * (1 + ‖z‖) ^ (max Nv M2) :=
                  mul_le_mul_of_nonneg_left e (by positivity)
              _ ≤ K * (1 + ‖z‖) ^ (max Nv M2) := by
                  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                  rw [hKdef]; nlinarith [abs_nonneg y, hCv0]
  have hBL := slice_BL IH F hF hH2 hconv hgf y (mixPot F y) hGfcd hGgf
  have hBL' : wVar (fun z : G => Real.exp (-(slicePot F y z))) (mixPot F y)
      ≤ sliceEnergy F y (mixPot F y) := hBL
  rw [show wVar (fun z : G => Real.exp (-(slicePot F y z))) (mixPot F y)
      = condVar F (fun p => dY F p) y * sliceMass F y
    from (condVar_mixPot_mul_sliceMass_eq F y (ne_of_gt hW)).symm] at hBL'
  have h1 : condVar F (fun p => dY F p) y ≤ sliceEnergy F y (mixPot F y) / sliceMass F y := by
    rw [le_div_iff₀ hW]
    linarith [hBL']
  linarith

lemma two_pi_le_condMean_schurPot (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ F p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ F) p v v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2)
    (y : ℝ) :
    2 * Real.pi ≤ condMean F (schurPot F) y := by
  obtain ⟨CF, hCF0, NF, hCF⟩ := hgf
  have hdYcd : ContDiff ℝ 1 (dY F) := contDiff_dY F hF
  obtain ⟨C2, hC20, M2, hC2⟩ :=
    grad_mixPot_growth F hF CF hCF0 NF (fun p v => (hCF p v).2) y
  have hIntE : Integrable (fun z : G => sliceEnergyFn F (z, y) * Real.exp (-(F (z, y)))) :=
    integrable_slice_hessInv_pair F hF hp hH2 y (mixPot F y) (mixPot F y)
      (continuous_gradSlice_fixed (dY F) hdYcd y) (continuous_gradSlice_fixed (dY F) hdYcd y)
      hC20 hC20 hC2 hC2
  have hIntSchur : Integrable (fun z : G => schurPot F (z, y) * Real.exp (-(F (z, y)))) := by
    rw [show (fun z : G => schurPot F (z, y) * Real.exp (-(F (z, y))))
        = fun z : G => d2Y F (z, y) * Real.exp (-(F (z, y)))
            - sliceEnergyFn F (z, y) * Real.exp (-(F (z, y))) from by
      funext z; rw [schurPot]; ring]
    exact (integrable_d2Y_exp_neg F hF hp y).sub hIntE
  have hInt2pi : Integrable (fun z : G => (2 * Real.pi) * Real.exp (-(F (z, y)))) :=
    integrable_of_le_gauss F hF hp y (fun _ : G => 2 * Real.pi) continuous_const
      (2 * Real.pi) (by positivity) 0
      (fun z => by rw [pow_zero, mul_one, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi)])
  have hmono : (∫ z, (2 * Real.pi) * Real.exp (-(F (z, y))))
      ≤ ∫ z, schurPot F (z, y) * Real.exp (-(F (z, y))) :=
    integral_mono hInt2pi hIntSchur
      (fun z => mul_le_mul_of_nonneg_right (schurPot_ge_two_pi F hF hH2 (z, y)) (Real.exp_pos _).le)
  rw [show (∫ z, (2 * Real.pi) * Real.exp (-(F (z, y)))) = (2 * Real.pi) * sliceMass F y from by
    rw [integral_const_mul]; rfl] at hmono
  rw [show condMean F (schurPot F) y
      = (∫ z, schurPot F (z, y) * Real.exp (-(F (z, y)))) / sliceMass F y from rfl]
  rw [le_div_iff₀ (sliceMass_pos F hF hp y)]
  exact hmono

lemma two_pi_le_margD2 (IH : BLon G) (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (hconv : ConvexOn ℝ Set.univ (fun p : G × ℝ => F p - Real.pi * (‖p.1‖ ^ 2 + p.2 ^ 2)))
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ F p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ F) p v v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2)
    (hp : PotGrowth F) (y : ℝ) :
    2 * Real.pi ≤ margD2 F y := by
  have hW : 0 < sliceMass F y := sliceMass_pos F hF hp y
  have h1 := margD2_eq_schur F hF hp hH2 hgf y (ne_of_gt hW)
  have h2 := two_pi_le_condMean_schurPot F hF hp hH2 hgf y
  have h3 := sliceEnergy_mix_sub_condVar_nonneg IH F hF hH2 hconv hgf hp y hW
  linarith [h1]

lemma exp_neg_marg_apply (F : G × ℝ → ℝ) (hW : ∀ y, 0 < sliceMass F y) (y : ℝ) :
    Real.exp (-(marg F y)) = sliceMass F y := by
  show Real.exp (-(-Real.log (sliceMass F y))) = sliceMass F y
  rw [neg_neg, Real.exp_log (hW y)]

lemma continuous_margD2 (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hW : ∀ y, 0 < sliceMass F y) : Continuous (margD2 F) := by
  have h1 : margD2 F = fun y => deriv (deriv (marg F)) y := by
    funext y; exact (deriv_deriv_marg F hF hp hW y).symm
  rw [h1]
  have hc1 : ContDiff ℝ 1 (deriv (marg F)) :=
    ((contDiff_succ_iff_deriv (𝕜 := ℝ) (n := 1) (f := marg F)).mp
      (contDiff_marg F hF hp hW)).2.2
  exact ContDiff.continuous_deriv hc1 (by norm_num)

lemma convexOn_marg (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hW : ∀ y, 0 < sliceMass F y) (hV2 : ∀ y, 0 < deriv (deriv (marg F)) y) :
    ConvexOn ℝ Set.univ (marg F) := by
  have hdiff : Differentiable ℝ (marg F) :=
    (contDiff_marg F hF hp hW).differentiable (by norm_num)
  exact (strictMono_of_deriv_pos hV2).monotone.convexOn_univ_of_deriv hdiff

lemma integrable_condMean_mul_exp_neg_marg (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hp : PotGrowth F) (hH : ContDiff ℝ 1 H) (hg : HGrowth H)
    (hW : ∀ y, 0 < sliceMass F y) :
    Integrable (fun y : ℝ => condMean F H y * Real.exp (-(marg F y))) := by
  refine (integrable_condMean_mul_sliceMass F H hF hp hH hg).congr ?_
  filter_upwards with y
  rw [exp_neg_marg_apply F hW y]

lemma integrable_condMean_sq_mul_exp_neg_marg (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hp : PotGrowth F) (hH : ContDiff ℝ 1 H) (hg : HGrowth H)
    (hW : ∀ y, 0 < sliceMass F y) :
    Integrable (fun y : ℝ => condMean F H y ^ 2 * Real.exp (-(marg F y))) := by
  refine (integrable_condMean_sq_mul_sliceMass F H hF hp hH hg).congr ?_
  filter_upwards with y
  rw [exp_neg_marg_apply F hW y]

lemma integrable_condMean_sq_div_margD2 (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hp : PotGrowth F) (hH : ContDiff ℝ 1 H) (hg : HGrowth H)
    (hW : ∀ y, 0 < sliceMass F y) (hmarg2 : ∀ y, 2 * Real.pi ≤ margD2 F y) :
    Integrable (fun y : ℝ =>
      condMean F H y ^ 2 / deriv (deriv (marg F)) y * Real.exp (-(marg F y))) := by
  have hcongr : (fun y : ℝ => condMean F H y ^ 2 / deriv (deriv (marg F)) y
      * Real.exp (-(marg F y)))
      = fun y : ℝ => condMean F H y ^ 2 / deriv (deriv (marg F)) y * sliceMass F y := by
    funext y; rw [exp_neg_marg_apply F hW y]
  rw [hcongr]
  have hcden : Continuous (fun y : ℝ => deriv (deriv (marg F)) y) := by
    have h1 : (fun y : ℝ => deriv (deriv (marg F)) y) = margD2 F := by
      funext y; exact deriv_deriv_marg F hF hp hW y
    rw [h1]; exact continuous_margD2 F hF hp hW
  have hcont' : Continuous (fun y : ℝ => condMean F H y ^ 2 / deriv (deriv (marg F)) y
      * sliceMass F y) := by
    refine Continuous.mul ?_ (contDiff_sliceMass F hF hp).continuous
    refine Continuous.div ?_ hcden ?_
    · exact (contDiff_condMean F H hF hp hH hg).continuous.pow 2
    · intro y
      have h2 : deriv (deriv (marg F)) y = margD2 F y := deriv_deriv_marg F hF hp hW y
      rw [h2]
      have h3 := hmarg2 y
      linarith [Real.pi_pos]
  refine Integrable.mono'
    ((integrable_condMean_sq_mul_sliceMass F H hF hp hH hg).const_mul (1 / (2 * Real.pi)))
    hcont'.aestronglyMeasurable ?_
  filter_upwards with y
  have hden : (0:ℝ) < deriv (deriv (marg F)) y := by
    have h2 : deriv (deriv (marg F)) y = margD2 F y := deriv_deriv_marg F hF hp hW y
    rw [h2]
    have h3 := hmarg2 y
    linarith [Real.pi_pos]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (div_nonneg (sq_nonneg _) hden.le)
    (sliceMass_pos F hF hp y).le)]
  have hkey : condMean F H y ^ 2 / deriv (deriv (marg F)) y * sliceMass F y
      ≤ (1 / (2 * Real.pi)) * (condMean F H y ^ 2 * sliceMass F y) := by
    have hden2 : 2 * Real.pi ≤ deriv (deriv (marg F)) y := by
      rw [deriv_deriv_marg F hF hp hW y]; exact hmarg2 y
    have hpi : (0:ℝ) < 2 * Real.pi := by positivity
    have h1 : (1:ℝ) ≤ (1 / (2 * Real.pi)) * deriv (deriv (marg F)) y := by
      calc (1:ℝ) = (1 / (2 * Real.pi)) * (2 * Real.pi) := by field_simp
        _ ≤ (1 / (2 * Real.pi)) * deriv (deriv (marg F)) y :=
            mul_le_mul_of_nonneg_left hden2 (by positivity)
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    have h2 : (0:ℝ) ≤ condMean F H y ^ 2 * sliceMass F y :=
      mul_nonneg (sq_nonneg _) (sliceMass_pos F hF hp y).le
    calc condMean F H y ^ 2 * sliceMass F y
        = (condMean F H y ^ 2 * sliceMass F y) * 1 := by ring
      _ ≤ (condMean F H y ^ 2 * sliceMass F y)
            * ((1 / (2 * Real.pi)) * deriv (deriv (marg F)) y) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = (1 / (2 * Real.pi)) * (condMean F H y ^ 2 * sliceMass F y)
            * deriv (deriv (marg F)) y := by ring
  exact hkey

/-- **Sharp one-dimensional Brascamp–Lieb for the marginal at height `y`.** -/
lemma marg_variance_le (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hH : ContDiff ℝ 1 H) (hg : HGrowth H) (hW : ∀ y, 0 < sliceMass F y)
    (hV2 : ∀ y : ℝ, 0 < deriv (deriv (marg F)) y)
    (huw : Integrable (fun y : ℝ => condMean F H y ^ 2
      / deriv (deriv (marg F)) y * Real.exp (-(marg F y))))
    (hud : Integrable (fun y : ℝ => (deriv (condMean F H) y) ^ 2
      / deriv (deriv (marg F)) y * Real.exp (-(marg F y)))) :
    (∫ y, condMean F H y ^ 2 * Real.exp (-(marg F y)))
        - (∫ y, condMean F H y * Real.exp (-(marg F y))) ^ 2
          / (∫ y, Real.exp (-(marg F y)))
      ≤ ∫ y, (deriv (condMean F H) y) ^ 2 / deriv (deriv (marg F)) y
          * Real.exp (-(marg F y)) :=
  Commons.Analysis.Convex.brascamp_lieb_one_dim_sharp (marg F) (condMean F H)
    (contDiff_marg F hF hp hW) (convexOn_marg F hF hp hW hV2) hV2
    (tendsto_marg_atTop F hF hp hW) (tendsto_marg_atBot F hF hp hW)
    (contDiff_condMean F H hF hp hH hg)
    (integrable_condMean_mul_exp_neg_marg F H hF hp hH hg hW)
    (integrable_condMean_sq_mul_exp_neg_marg F H hF hp hH hg hW)
    huw hud

/-- The same inequality, with `e^{-marg F}` rewritten as the slice mass. -/
lemma marg_variance_le_sliceMass (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hH : ContDiff ℝ 1 H) (hg : HGrowth H) (hW : ∀ y, 0 < sliceMass F y)
    (hV2 : ∀ y : ℝ, 0 < deriv (deriv (marg F)) y)
    (huw : Integrable (fun y : ℝ => condMean F H y ^ 2
      / deriv (deriv (marg F)) y * Real.exp (-(marg F y))))
    (hud : Integrable (fun y : ℝ => (deriv (condMean F H) y) ^ 2
      / deriv (deriv (marg F)) y * Real.exp (-(marg F y)))) :
    (∫ y, condMean F H y ^ 2 * sliceMass F y)
        - (∫ y, condMean F H y * sliceMass F y) ^ 2 / (∫ y, sliceMass F y)
      ≤ ∫ y, (deriv (condMean F H) y) ^ 2 / deriv (deriv (marg F)) y * sliceMass F y := by
  have h := marg_variance_le F H hF hp hH hg hW hV2 huw hud
  simp_rw [exp_neg_marg_apply F hW] at h
  exact h

/-- The `hessInv`-correction pairing `⟨(Hess_z F)⁻¹ ∇_z H, ∇_z∂_yF⟩` as a function of the point.
(The order of the two arguments is that of `sliceCrossEnergy`; by self-adjointness of the inverse
Hessian it equals the Schur-form pairing -- see `crossFn_eq_swapped`.) -/
noncomputable def crossFn (F H : G × ℝ → ℝ) (p : G × ℝ) : ℝ :=
  ⟪hessInv (slicePot F p.2) p.1 (gradSlice H p), gradSlice (dY F) p⟫_ℝ

/-- The correction term of the Schur identity: `dY H - ⟨(Hess_z F)⁻¹ ∇_z∂_yF, ∇_z H⟩`. -/
noncomputable def schurPhi (F H : G × ℝ → ℝ) (p : G × ℝ) : ℝ := dY H p - crossFn F H p

lemma condMean_crossFn (F H : G × ℝ → ℝ) (y : ℝ) :
    condMean F (crossFn F H) y
      = sliceCrossEnergy F y (slicePot H y) (mixPot F y) / sliceMass F y := by
  simp only [condMean, sliceCrossEnergy, sliceMass, crossFn, gradSlice, slicePot]
  congr 3 with z

/-- `crossFn` equals the Schur-form pairing (self-adjointness of the inverse slice Hessian). -/
lemma crossFn_eq_swapped (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v) (p : G × ℝ) :
    crossFn F H p
      = ⟪hessInv (slicePot F p.2) p.1 (gradSlice (dY F) p), gradSlice H p⟫_ℝ := by
  rw [crossFn, hessInv_slice_symm F hF hH2 p.2 p.1 (gradSlice H p) (gradSlice (dY F) p),
    real_inner_comm]

lemma continuous_crossFn (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hH : ContDiff ℝ 1 H)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v) :
    Continuous (crossFn F H) :=
  continuous_slice_hessInv_bilin F hF hH2 (fun p => gradSlice H p) (fun p => gradSlice (dY F) p)
    (continuous_gradSlice H hH) (continuous_gradSlice (dY F) (contDiff_dY F hF))

lemma condMeanDeriv_sub_eq (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hH : ContDiff ℝ 1 H) (hg : HGrowth H)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ F p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ F) p v v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2)
    (hderivH : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ H p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖)
    (y : ℝ) (hW : sliceMass F y ≠ 0) :
    deriv (condMean F H) y
      - (sliceCrossEnergy F y (slicePot H y) (mixPot F y) / sliceMass F y
          - condCov F H (fun p => dY F p) y)
      = condMean F (schurPhi F H) y := by
  obtain ⟨CF, hCF0, NF, hCF⟩ := hgf
  obtain ⟨CH, hCH0, NH, hCH⟩ := hderivH
  have hdYcd : ContDiff ℝ 1 (dY F) := contDiff_dY F hF
  obtain ⟨C1, hC10, M1, hC1⟩ := grad_slicePot_growth H CH hCH0 NH hCH hH y
  obtain ⟨C2, hC20, M2, hC2⟩ :=
    grad_mixPot_growth F hF CF hCF0 NF (fun p v => (hCF p v).2) y
  have hintX : Integrable (fun z : G => crossFn F H (z, y) * Real.exp (-(F (z, y)))) :=
    integrable_slice_hessInv_pair F hF hp hH2 y (slicePot H y) (mixPot F y)
      (continuous_gradSlice_fixed H hH y) (continuous_gradSlice_fixed (dY F) hdYcd y)
      hC10 hC20 hC1 hC2
  rw [(hasDerivAt_condMean F H hF hp hH hg y hW).deriv]
  rw [show schurPhi F H = dY H - crossFn F H from rfl]
  rw [condMean_sub F (dY H) (crossFn F H) y hW (integrable_dYH F H hF hH hp hg y) hintX]
  rw [condMean_crossFn F H y]
  ring

/-- `α - β = ⟨schurPot⟩` for the marginal `α = margD2 F y` and `β = A22 - B22`. -/
lemma margD2_sub_beta (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ F p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ F) p v v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2)
    (y : ℝ) (hW : sliceMass F y ≠ 0) :
    margD2 F y - (sliceEnergy F y (mixPot F y) / sliceMass F y
        - condVar F (fun p => dY F p) y) = condMean F (schurPot F) y := by
  have h := margD2_eq_schur F hF hp hH2 hgf y hW
  linarith

/-- The pointwise combination `a²/α ≤ α₁ + (a-b)²/(α-β)` (from `bl_slice_quad` and
`bl_combine`), multiplied by the slice mass. -/
lemma a_sq_div_le_combined (IH : BLon G) (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hH : ContDiff ℝ 1 H)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (hconv : ConvexOn ℝ Set.univ (fun p : G × ℝ => F p - Real.pi * (‖p.1‖ ^ 2 + p.2 ^ 2)))
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ F p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ F) p v v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2)
    (hp : PotGrowth F) (hgH : HGrowth H)
    (hderivH : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ H p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖)
    (y : ℝ) :
    (deriv (condMean F H) y) ^ 2 / margD2 F y * sliceMass F y
      ≤ (sliceEnergy F y (slicePot H y) / sliceMass F y - condVar F H y
          + (deriv (condMean F H) y
              - (sliceCrossEnergy F y (slicePot H y) (mixPot F y) / sliceMass F y
                - condCov F H (fun p => dY F p) y)) ^ 2
            / condMean F (schurPot F) y) * sliceMass F y := by
  have hW : 0 < sliceMass F y := sliceMass_pos F hF hp y
  have hWne : sliceMass F y ≠ 0 := ne_of_gt hW
  have hquad := bl_slice_quad IH F H hF hH hH2 hconv hgf hp hgH hderivH y
  have halpha : condMean F (schurPot F) y
      = margD2 F y - (sliceEnergy F y (mixPot F y) / sliceMass F y
          - condVar F (fun p => dY F p) y) :=
    (margD2_sub_beta F hF hp hH2 hgf y hWne).symm
  have hαpos : 0 < margD2 F y := by
    have h := two_pi_le_margD2 IH F hF hH2 hconv hgf hp y
    linarith [Real.pi_pos]
  set α₁ : ℝ := sliceEnergy F y (slicePot H y) / sliceMass F y - condVar F H y
  set b : ℝ := sliceCrossEnergy F y (slicePot H y) (mixPot F y) / sliceMass F y
    - condCov F H (fun p => dY F p) y
  set β : ℝ := sliceEnergy F y (mixPot F y) / sliceMass F y - condVar F (fun p => dY F p) y
  set a : ℝ := deriv (condMean F H) y
  have hquad' : ∀ t : ℝ, 0 ≤ α₁ + 2 * b * t + β * t ^ 2 := by
    intro t
    have h := hquad t
    rw [show (α₁ + 2 * b * t + β * t ^ 2)
        = (sliceEnergy F y (slicePot H y) / sliceMass F y - condVar F H y)
          + 2 * t * (sliceCrossEnergy F y (slicePot H y) (mixPot F y) / sliceMass F y
            - condCov F H (fun p => dY F p) y)
          + t ^ 2 * (sliceEnergy F y (mixPot F y) / sliceMass F y
            - condVar F (fun p => dY F p) y) from by
      simp only [α₁, b, β]; ring]
    exact h
  have hmain : a ^ 2 / margD2 F y - (a - b) ^ 2 / condMean F (schurPot F) y ≤ α₁ := by
    have hβnn : 0 ≤ β := sliceEnergy_mix_sub_condVar_nonneg IH F hF hH2 hconv hgf hp y hW
    by_cases hβ0 : β = 0
    · have hcc : condMean F (schurPot F) y = margD2 F y := by rw [halpha, hβ0]; ring
      have hquad0 : ∀ t : ℝ, 0 ≤ α₁ + 2 * b * t := by
        intro t
        have h := hquad' t
        rw [show β * t ^ 2 = 0 from by rw [hβ0]; ring, add_zero] at h
        exact h
      rw [hcc]
      simpa using bl_combine_zero (a := a) hαpos hquad0
    · have hβpos : 0 < β := lt_of_le_of_ne hβnn (Ne.symm hβ0)
      have hcc : condMean F (schurPot F) y = margD2 F y - β := halpha
      have hβα : β < margD2 F y := by
        have h2 := two_pi_le_condMean_schurPot F hF hp hH2 hgf y
        rw [hcc] at h2
        linarith [Real.pi_pos]
      rw [hcc]
      exact bl_combine (a := a) hβpos hβα hquad'
  have hmul : a ^ 2 / margD2 F y * sliceMass F y
      ≤ (α₁ + (a - b) ^ 2 / condMean F (schurPot F) y) * sliceMass F y := by
    have h := hmain
    nlinarith [hW]
  have hexp : (α₁ + (a - b) ^ 2 / condMean F (schurPot F) y) * sliceMass F y
      = (sliceEnergy F y (slicePot H y) / sliceMass F y - condVar F H y
          + (deriv (condMean F H) y - (sliceCrossEnergy F y (slicePot H y) (mixPot F y) / sliceMass F y
              - condCov F H (fun p => dY F p) y)) ^ 2 / condMean F (schurPot F) y) * sliceMass F y := by
    simp only [α₁, b, a]
  rw [← hexp]
  exact hmul

lemma gradSlice_le_poly (H : G × ℝ → ℝ) (hH : ContDiff ℝ 1 H) (C : ℝ) (hC : 0 ≤ C) (N : ℕ)
    (hgH : ∀ p v : G × ℝ, |fderiv ℝ H p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∃ M : ℕ, ∀ p : G × ℝ, ‖gradSlice H p‖ ≤ C' * (1 + ‖p‖) ^ M := by
  refine ⟨C, hC, N, fun p => ?_⟩
  show ‖grad (slicePot H p.2) p.1‖ ≤ C * (1 + ‖p‖) ^ N
  rw [grad_norm_eq]
  have hdif : DifferentiableAt ℝ H (p.1, p.2) := hH.contDiffAt.differentiableAt (by norm_num)
  have h1 : ‖fderiv ℝ (slicePot H p.2) p.1‖ ≤ ‖fderiv ℝ H (p.1, p.2)‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun v => ?_)
    rw [fderiv_slicePot H p.2 p.1 v hdif, Real.norm_eq_abs]
    calc |fderiv ℝ H (p.1, p.2) (v, 0)| = ‖fderiv ℝ H (p.1, p.2) (v, 0)‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖fderiv ℝ H (p.1, p.2)‖ * ‖((v, 0) : G × ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ H (p.1, p.2)‖ * ‖v‖ := by
          rw [show ‖((v, 0) : G × ℝ)‖ = ‖v‖ from by simp]
  have h2 : ‖fderiv ℝ H (p.1, p.2)‖ ≤ C * (1 + ‖(p.1, p.2)‖) ^ N := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
    rw [Real.norm_eq_abs]; exact hgH (p.1, p.2) v
  simpa using le_trans h1 h2

lemma gradSlice_dY_le_poly (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (C : ℝ) (hC : 0 ≤ C) (N : ℕ)
    (hdiag : ∀ p v : G × ℝ, |fderiv ℝ (fderiv ℝ F) p v v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∃ M : ℕ, ∀ p : G × ℝ, ‖gradSlice (dY F) p‖ ≤ C' * (1 + ‖p‖) ^ M := by
  obtain ⟨C', hC'0, hpol⟩ := hess_polar_le F hF C hC N hdiag
  refine ⟨C', hC'0, N, fun p => ?_⟩
  show ‖grad (mixPot F p.2) p.1‖ ≤ C' * (1 + ‖p‖) ^ N
  rw [grad_norm_eq]
  have h1 : ‖fderiv ℝ (mixPot F p.2) p.1‖ ≤ C' * (1 + ‖(p.1, p.2)‖) ^ N := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
    rw [fderiv_mixPot F p.2 hF p.1 v, Real.norm_eq_abs]
    have h2 := hpol (p.1, p.2) (v, 0) (0, 1)
    rw [show ‖((v, 0) : G × ℝ)‖ = ‖v‖ from by simp,
      show ‖((0, 1) : G × ℝ)‖ = 1 from by simp, mul_one] at h2
    exact h2
  simpa using h1

lemma schurPot_pos (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v) (z : G) (y : ℝ) :
    0 < schurPot F (z, y) := by
  have h := schurPot_ge_two_pi F hF hH2 (z, y)
  linarith [Real.pi_pos]

lemma continuous_schurPot (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v) :
    Continuous (schurPot F) := by
  have h1 : schurPot F = fun p => d2Y F p - sliceEnergyFn F p := rfl
  rw [h1]
  refine Continuous.sub ?_ ?_
  · show Continuous (fun p : G × ℝ => fderiv ℝ (fun q : G × ℝ => fderiv ℝ F q (0, 1)) p (0, 1))
    exact ((contDiff_dY F hF).continuous_fderiv (by norm_num)).clm_apply continuous_const
  · exact continuous_slice_hessInv_bilin F hF hH2 (fun p => gradSlice (dY F) p)
      (fun p => gradSlice (dY F) p) (continuous_gradSlice (dY F) (contDiff_dY F hF))
      (continuous_gradSlice (dY F) (contDiff_dY F hF))

lemma continuous_schurPhi (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hH : ContDiff ℝ 1 H)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v) :
    Continuous (schurPhi F H) := by
  have h1 : schurPhi F H = fun p => dY H p - crossFn F H p := rfl
  rw [h1]
  exact ((hH.continuous_fderiv (by norm_num)).clm_apply continuous_const).sub
    (continuous_crossFn F H hF hH hH2)

lemma wVar_nonneg {α : Type*} [MeasureSpace α] (w A : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (h1 : Integrable (fun x => A x ^ 2 * w x)) (h2 : Integrable (fun x => A x * w x))
    (h3 : Integrable w) (hW : 0 < ∫ x, w x) : 0 ≤ wVar w A := by
  have hcs := sq_integral_mul_le_integral_sq_mul_meas A (fun _ => (1 : ℝ)) w hw h1
    (by simpa using h3)
  have hcs' : (∫ x, A x * w x) ^ 2 ≤ (∫ x, A x ^ 2 * w x) * (∫ x, w x) := by
    simpa only [mul_one, one_mul, one_pow, Pi.one_apply] using hcs
  rw [wVar, sub_nonneg, div_le_iff₀ hW]
  linarith [hcs']

lemma integrable_slice_exp_neg (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (y : ℝ) : Integrable (fun z : G => Real.exp (-(slicePot F y z))) := by
  simpa only [slicePot, one_mul] using integrable_of_le_gauss F hF hp y (fun _ : G => (1 : ℝ))
    continuous_const 1 (by norm_num) 0 (fun z => by simp)

lemma condVar_mul_sliceMass_nonneg (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hH : ContDiff ℝ 1 H) (hg : HGrowth H) (y : ℝ) :
    0 ≤ condVar F H y * sliceMass F y := by
  have hW : 0 < sliceMass F y := sliceMass_pos F hF hp y
  obtain ⟨CH, hCH0, NH, hCH⟩ := hg
  have hI2 : Integrable (fun z : G => slicePot H y z ^ 2 * Real.exp (-(slicePot F y z))) := by
    refine (integrable_slice_mul F hF hp y (fun p => H p ^ 2) (hH.continuous.pow 2)
      (CH ^ 2) (by positivity) (NH * 2) ?_).congr ?_
    · intro p
      rw [abs_of_nonneg (sq_nonneg (H p))]
      calc H p ^ 2 ≤ (CH * (1 + ‖p‖) ^ NH) ^ 2 :=
            sq_le_sq' (abs_le.mp (hCH p).1).1 (abs_le.mp (hCH p).1).2
        _ = CH ^ 2 * (1 + ‖p‖) ^ (NH * 2) := by rw [mul_pow, pow_mul]
    · filter_upwards with z
      simp only [slicePot]
  have hI1 : Integrable (fun z : G => slicePot H y z * Real.exp (-(slicePot F y z))) := by
    simpa only [slicePot] using integrable_slice_mul F hF hp y H hH.continuous CH hCH0 NH
      (fun p => (hCH p).1)
  rw [condVar_mul_sliceMass_eq F H y (ne_of_gt hW)]
  exact wVar_nonneg (fun z : G => Real.exp (-(slicePot F y z))) (slicePot H y)
    (fun z => (Real.exp_pos _).le) hI2 hI1 (integrable_slice_exp_neg F hF hp y) hW

lemma integrable_schurPot_slice (F : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ F p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ F) p v v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2)
    (y : ℝ) :
    Integrable (fun z : G => schurPot F (z, y) * Real.exp (-(F (z, y)))) := by
  obtain ⟨CF, hCF0, NF, hCF⟩ := hgf
  have hdYcd : ContDiff ℝ 1 (dY F) := contDiff_dY F hF
  obtain ⟨C2, hC20, M2, hC2⟩ :=
    grad_mixPot_growth F hF CF hCF0 NF (fun p v => (hCF p v).2) y
  have hIntE : Integrable (fun z : G => sliceEnergyFn F (z, y) * Real.exp (-(F (z, y)))) :=
    integrable_slice_hessInv_pair F hF hp hH2 y (mixPot F y) (mixPot F y)
      (continuous_gradSlice_fixed (dY F) hdYcd y) (continuous_gradSlice_fixed (dY F) hdYcd y)
      hC20 hC20 hC2 hC2
  rw [show (fun z : G => schurPot F (z, y) * Real.exp (-(F (z, y))))
      = fun z : G => d2Y F (z, y) * Real.exp (-(F (z, y)))
          - sliceEnergyFn F (z, y) * Real.exp (-(F (z, y))) from by
    funext z; rw [schurPot]; ring]
  exact (integrable_d2Y_exp_neg F hF hp y).sub hIntE

/-- Continuity of the correction ratio `schurPhi²/schurPot` in the slice variable. -/
lemma continuous_schurPhi_sq_div_slice (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hH : ContDiff ℝ 1 H)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v) (y : ℝ) :
    Continuous (fun z : G => schurPhi F H (z, y) ^ 2 / schurPot F (z, y)) := by
  have h1 : Continuous (fun z : G => schurPhi F H (z, y)) :=
    (continuous_schurPhi F H hF hH hH2).comp (continuous_id.prodMk continuous_const)
  have h2 : Continuous (fun z : G => schurPot F (z, y)) :=
    (continuous_schurPot F hF hH2).comp (continuous_id.prodMk continuous_const)
  refine Continuous.div (h1.pow 2) h2 (fun z => ne_of_gt (schurPot_pos F hF hH2 z y))

lemma integrable_schurPhi_sq_div_slice (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hH : ContDiff ℝ 1 H) (hgH : HGrowth H)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ F p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ F) p v v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2)
    (hderivH : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ H p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖)
    (y : ℝ) :
    Integrable (fun z : G =>
      schurPhi F H (z, y) ^ 2 / schurPot F (z, y) * Real.exp (-(F (z, y)))) := by
  obtain ⟨CF, hCF0, NF, hCF⟩ := hgf
  obtain ⟨CH, hCH0, NH, hCH⟩ := hderivH
  obtain ⟨CV, hCV0, NV, hCV⟩ := hgH
  obtain ⟨C1, hC10, M1, hC1⟩ := grad_slicePot_growth H CH hCH0 NH hCH hH y
  obtain ⟨C2, hC20, M2, hC2⟩ :=
    grad_mixPot_growth F hF CF hCF0 NF (fun p v => (hCF p v).2) y
  have hslice : ∀ z v : G, 2 * Real.pi * ‖v‖ ^ 2
      ≤ fderiv ℝ (fderiv ℝ (slicePot F y)) z v v := by
    intro z v
    rw [fderiv_fderiv_slicePot F y hF z v v]
    have h := hH2 (z, y) (v, 0)
    simpa using h
  have hinj : ∀ z : G, Function.Injective (hessOp (slicePot F y) z) :=
    fun z => hessOp_injective _ _ (hslice z)
  refine integrable_of_le_gauss F hF hp y
    (fun z : G => schurPhi F H (z, y) ^ 2 / schurPot F (z, y))
    (continuous_schurPhi_sq_div_slice F H hF hH hH2 y)
    (2 * CV ^ 2 + 2 * (C1 / (2 * Real.pi)) ^ 2 * C2 ^ 2) (by positivity)
    (2 * NV + 2 * M1 + 2 * M2) (fun z => ?_)
  set X : ℝ := (1 + ‖z‖ + |y|) ^ (2 * NV + 2 * M1 + 2 * M2) with hXdef
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  have hbV : |dY H (z, y)| ≤ CV * (1 + ‖z‖ + |y|) ^ NV := by
    have h := (hCV (z, y)).2
    refine le_trans h (mul_le_mul_of_nonneg_left ?_ hCV0)
    exact pow_le_pow_left₀ (by positivity) (by linarith [norm_pair_le z y]) NV
  have hV2 : (dY H (z, y)) ^ 2 ≤ CV ^ 2 * X := by
    have h1 : (dY H (z, y)) ^ 2 ≤ (CV * (1 + ‖z‖ + |y|) ^ NV) ^ 2 :=
      sq_le_sq' (abs_le.mp hbV).1 (abs_le.mp hbV).2
    have h2 : (CV * (1 + ‖z‖ + |y|) ^ NV) ^ 2
        = CV ^ 2 * (1 + ‖z‖ + |y|) ^ (NV * 2) := by rw [mul_pow, pow_mul]
    have h3 : (1 + ‖z‖ + |y|) ^ (NV * 2) ≤ X := by
      rw [hXdef]
      exact pow_le_pow_right₀ (by linarith [norm_nonneg z, abs_nonneg y]) (by omega)
    rw [h2] at h1
    calc (dY H (z, y)) ^ 2 ≤ CV ^ 2 * (1 + ‖z‖ + |y|) ^ (NV * 2) := h1
      _ ≤ CV ^ 2 * X := mul_le_mul_of_nonneg_left h3 (sq_nonneg CV)
  have hX2 : crossFn F H (z, y) ^ 2 ≤ (C1 / (2 * Real.pi)) ^ 2 * C2 ^ 2 * X := by
    have hn := hessInv_norm_le (slicePot F y) z (hinj z) (hslice z) (gradSlice H (z, y))
    have hb : |crossFn F H (z, y)|
        ≤ (C1 / (2 * Real.pi) * (1 + ‖z‖ + |y|) ^ M1) * (C2 * (1 + ‖z‖ + |y|) ^ M2) := by
      rw [crossFn]
      calc |⟪hessInv (slicePot F y) z (gradSlice H (z, y)), gradSlice (dY F) (z, y)⟫_ℝ|
          ≤ ‖hessInv (slicePot F y) z (gradSlice H (z, y))‖ * ‖gradSlice (dY F) (z, y)‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ (‖gradSlice H (z, y)‖ / (2 * Real.pi)) * ‖gradSlice (dY F) (z, y)‖ :=
            mul_le_mul_of_nonneg_right hn (norm_nonneg _)
        _ ≤ (C1 * (1 + ‖z‖ + |y|) ^ M1 / (2 * Real.pi)) * (C2 * (1 + ‖z‖ + |y|) ^ M2) := by
            refine mul_le_mul ?_ (hC2 z) (norm_nonneg _) (by positivity)
            exact div_le_div_of_nonneg_right (hC1 z) (by positivity)
        _ = (C1 / (2 * Real.pi) * (1 + ‖z‖ + |y|) ^ M1) * (C2 * (1 + ‖z‖ + |y|) ^ M2) := by
            ring
    have h1 : crossFn F H (z, y) ^ 2
        ≤ ((C1 / (2 * Real.pi) * (1 + ‖z‖ + |y|) ^ M1) * (C2 * (1 + ‖z‖ + |y|) ^ M2)) ^ 2 :=
      sq_le_sq' (abs_le.mp hb).1 (abs_le.mp hb).2
    have h2 : ((C1 / (2 * Real.pi) * (1 + ‖z‖ + |y|) ^ M1) * (C2 * (1 + ‖z‖ + |y|) ^ M2)) ^ 2
        = (C1 / (2 * Real.pi)) ^ 2 * C2 ^ 2 * (1 + ‖z‖ + |y|) ^ (M1 * 2 + M2 * 2) := by
      have hpow : ((1 + ‖z‖ + |y|) ^ M1) ^ 2 = (1 + ‖z‖ + |y|) ^ (M1 * 2) := by rw [← pow_mul]
      have hpow2 : ((1 + ‖z‖ + |y|) ^ M2) ^ 2 = (1 + ‖z‖ + |y|) ^ (M2 * 2) := by rw [← pow_mul]
      have hpow3 : (1 + ‖z‖ + |y|) ^ (M1 * 2) * (1 + ‖z‖ + |y|) ^ (M2 * 2)
          = (1 + ‖z‖ + |y|) ^ (M1 * 2 + M2 * 2) := by rw [← pow_add]
      rw [mul_pow, mul_pow, mul_pow, hpow, hpow2,
        show (C1 / (2 * Real.pi)) ^ 2 * (1 + ‖z‖ + |y|) ^ (M1 * 2)
              * (C2 ^ 2 * (1 + ‖z‖ + |y|) ^ (M2 * 2))
            = (C1 / (2 * Real.pi)) ^ 2 * C2 ^ 2
              * ((1 + ‖z‖ + |y|) ^ (M1 * 2) * (1 + ‖z‖ + |y|) ^ (M2 * 2)) from by ring,
        hpow3]
    have h3 : (1 + ‖z‖ + |y|) ^ (M1 * 2 + M2 * 2) ≤ X := by
      rw [hXdef]
      refine pow_le_pow_right₀ (by linarith [norm_nonneg z, abs_nonneg y]) ?_
      omega
    rw [h2] at h1
    calc crossFn F H (z, y) ^ 2
        ≤ (C1 / (2 * Real.pi)) ^ 2 * C2 ^ 2 * (1 + ‖z‖ + |y|) ^ (M1 * 2 + M2 * 2) := h1
      _ ≤ (C1 / (2 * Real.pi)) ^ 2 * C2 ^ 2 * X :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
  have hnum : schurPhi F H (z, y) ^ 2 ≤ (2 * CV ^ 2 + 2 * (C1 / (2 * Real.pi)) ^ 2 * C2 ^ 2) * X := by
    have h1 : schurPhi F H (z, y) ^ 2 ≤ 2 * (dY H (z, y)) ^ 2 + 2 * crossFn F H (z, y) ^ 2 := by
      rw [schurPhi]
      nlinarith [sq_nonneg (dY H (z, y) - crossFn F H (z, y)),
        sq_nonneg (dY H (z, y) + crossFn F H (z, y))]
    calc schurPhi F H (z, y) ^ 2 ≤ 2 * (dY H (z, y)) ^ 2 + 2 * crossFn F H (z, y) ^ 2 := h1
      _ ≤ 2 * (CV ^ 2 * X) + 2 * ((C1 / (2 * Real.pi)) ^ 2 * C2 ^ 2 * X) := by
          gcongr
      _ = (2 * CV ^ 2 + 2 * (C1 / (2 * Real.pi)) ^ 2 * C2 ^ 2) * X := by ring
  have hden := schurPot_ge_two_pi F hF hH2 (z, y)
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (schurPot_pos F hF hH2 z y).le)]
  calc schurPhi F H (z, y) ^ 2 / schurPot F (z, y)
      ≤ schurPhi F H (z, y) ^ 2 / (2 * Real.pi) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden
    _ ≤ ((2 * CV ^ 2 + 2 * (C1 / (2 * Real.pi)) ^ 2 * C2 ^ 2) * X) / (2 * Real.pi) :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (2 * CV ^ 2 + 2 * (C1 / (2 * Real.pi)) ^ 2 * C2 ^ 2) * X := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)]
        nlinarith [hX0, Real.pi_gt_three]

/-- Pointwise domination of the correction ratio `schurPhi²/schurPot` in the `p`-form. -/
lemma schurPhi_sq_div_le (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    {C1 C2 CV : ℝ} {M1 M2 NV M : ℕ} (hC10 : 0 ≤ C1) (hC20 : 0 ≤ C2) (hCV0 : 0 ≤ CV)
    (hN : 2 * NV + 2 * M1 + 2 * M2 ≤ M)
    (hV : ∀ p : G × ℝ, |dY H p| ≤ CV * (1 + ‖p‖) ^ NV)
    (hg1 : ∀ p : G × ℝ, ‖gradSlice H p‖ ≤ C1 * (1 + ‖p‖) ^ M1)
    (hg2 : ∀ p : G × ℝ, ‖gradSlice (dY F) p‖ ≤ C2 * (1 + ‖p‖) ^ M2)
    (p : G × ℝ) :
    |schurPhi F H p ^ 2 / schurPot F p|
      ≤ (2 * CV ^ 2 + 2 * (C1 / (2 * Real.pi)) ^ 2 * C2 ^ 2) * (1 + ‖p‖) ^ M := by
  have hslice : ∀ v : G, 2 * Real.pi * ‖v‖ ^ 2
      ≤ fderiv ℝ (fderiv ℝ (slicePot F p.2)) p.1 v v := by
    intro v
    rw [fderiv_fderiv_slicePot F p.2 hF p.1 v v]
    have h := hH2 p (v, 0)
    simpa using h
  have hinj : Function.Injective (hessOp (slicePot F p.2) p.1) :=
    hessOp_injective _ _ hslice
  have hX0 : 0 ≤ (1 + ‖p‖) ^ M := by positivity
  have hpowV : (1 + ‖p‖) ^ (NV * 2) ≤ (1 + ‖p‖) ^ M :=
    pow_le_pow_right₀ (by linarith [norm_nonneg p]) (by omega)
  have hpowX : (1 + ‖p‖) ^ (M1 * 2 + M2 * 2) ≤ (1 + ‖p‖) ^ M :=
    pow_le_pow_right₀ (by linarith [norm_nonneg p]) (by omega)
  have hV2 : (dY H p) ^ 2 ≤ CV ^ 2 * (1 + ‖p‖) ^ M := by
    have h1 : (dY H p) ^ 2 ≤ (CV * (1 + ‖p‖) ^ NV) ^ 2 :=
      sq_le_sq' (abs_le.mp (hV p)).1 (abs_le.mp (hV p)).2
    have h2 : (CV * (1 + ‖p‖) ^ NV) ^ 2 = CV ^ 2 * (1 + ‖p‖) ^ (NV * 2) := by
      rw [mul_pow, ← pow_mul]
    rw [h2] at h1
    calc (dY H p) ^ 2 ≤ CV ^ 2 * (1 + ‖p‖) ^ (NV * 2) := h1
      _ ≤ CV ^ 2 * (1 + ‖p‖) ^ M := mul_le_mul_of_nonneg_left hpowV (sq_nonneg CV)
  have hX2 : crossFn F H p ^ 2 ≤ (C1 / (2 * Real.pi)) ^ 2 * C2 ^ 2 * (1 + ‖p‖) ^ M := by
    have hn := hessInv_norm_le (slicePot F p.2) p.1 hinj hslice (gradSlice H p)
    have hb : |crossFn F H p|
        ≤ (C1 / (2 * Real.pi) * (1 + ‖p‖) ^ M1) * (C2 * (1 + ‖p‖) ^ M2) := by
      rw [crossFn]
      calc |⟪hessInv (slicePot F p.2) p.1 (gradSlice H p), gradSlice (dY F) p⟫_ℝ|
          ≤ ‖hessInv (slicePot F p.2) p.1 (gradSlice H p)‖ * ‖gradSlice (dY F) p‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ (‖gradSlice H p‖ / (2 * Real.pi)) * ‖gradSlice (dY F) p‖ :=
            mul_le_mul_of_nonneg_right hn (norm_nonneg _)
        _ ≤ (C1 * (1 + ‖p‖) ^ M1 / (2 * Real.pi)) * (C2 * (1 + ‖p‖) ^ M2) := by
            refine mul_le_mul ?_ (hg2 p) (norm_nonneg _) (by positivity)
            exact div_le_div_of_nonneg_right (hg1 p) (by positivity)
        _ = (C1 / (2 * Real.pi) * (1 + ‖p‖) ^ M1) * (C2 * (1 + ‖p‖) ^ M2) := by ring
    have h1 : crossFn F H p ^ 2
        ≤ ((C1 / (2 * Real.pi) * (1 + ‖p‖) ^ M1) * (C2 * (1 + ‖p‖) ^ M2)) ^ 2 :=
      sq_le_sq' (abs_le.mp hb).1 (abs_le.mp hb).2
    have hpow : ((1 + ‖p‖) ^ M1) ^ 2 = (1 + ‖p‖) ^ (M1 * 2) := by rw [← pow_mul]
    have hpow2 : ((1 + ‖p‖) ^ M2) ^ 2 = (1 + ‖p‖) ^ (M2 * 2) := by rw [← pow_mul]
    have hpow3 : (1 + ‖p‖) ^ (M1 * 2) * (1 + ‖p‖) ^ (M2 * 2)
        = (1 + ‖p‖) ^ (M1 * 2 + M2 * 2) := by rw [← pow_add]
    have h2 : ((C1 / (2 * Real.pi) * (1 + ‖p‖) ^ M1) * (C2 * (1 + ‖p‖) ^ M2)) ^ 2
        = (C1 / (2 * Real.pi)) ^ 2 * C2 ^ 2 * (1 + ‖p‖) ^ (M1 * 2 + M2 * 2) := by
      rw [mul_pow, mul_pow, mul_pow, hpow, hpow2,
        show (C1 / (2 * Real.pi)) ^ 2 * (1 + ‖p‖) ^ (M1 * 2)
              * (C2 ^ 2 * (1 + ‖p‖) ^ (M2 * 2))
            = (C1 / (2 * Real.pi)) ^ 2 * C2 ^ 2
              * ((1 + ‖p‖) ^ (M1 * 2) * (1 + ‖p‖) ^ (M2 * 2)) from by ring,
        hpow3]
    rw [h2] at h1
    calc crossFn F H p ^ 2
        ≤ (C1 / (2 * Real.pi)) ^ 2 * C2 ^ 2 * (1 + ‖p‖) ^ (M1 * 2 + M2 * 2) := h1
      _ ≤ (C1 / (2 * Real.pi)) ^ 2 * C2 ^ 2 * (1 + ‖p‖) ^ M :=
          mul_le_mul_of_nonneg_left hpowX (by positivity)
  have hnum : schurPhi F H p ^ 2
      ≤ (2 * CV ^ 2 + 2 * (C1 / (2 * Real.pi)) ^ 2 * C2 ^ 2) * (1 + ‖p‖) ^ M := by
    have h1 : schurPhi F H p ^ 2 ≤ 2 * (dY H p) ^ 2 + 2 * crossFn F H p ^ 2 := by
      rw [schurPhi]
      nlinarith [sq_nonneg (dY H p - crossFn F H p), sq_nonneg (dY H p + crossFn F H p)]
    calc schurPhi F H p ^ 2 ≤ 2 * (dY H p) ^ 2 + 2 * crossFn F H p ^ 2 := h1
      _ ≤ 2 * (CV ^ 2 * (1 + ‖p‖) ^ M)
            + 2 * ((C1 / (2 * Real.pi)) ^ 2 * C2 ^ 2 * (1 + ‖p‖) ^ M) := by gcongr
      _ = (2 * CV ^ 2 + 2 * (C1 / (2 * Real.pi)) ^ 2 * C2 ^ 2) * (1 + ‖p‖) ^ M := by ring
  have hden := schurPot_ge_two_pi F hF hH2 p
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (schurPot_pos F hF hH2 p.1 p.2).le)]
  calc schurPhi F H p ^ 2 / schurPot F p
      ≤ schurPhi F H p ^ 2 / (2 * Real.pi) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden
    _ ≤ ((2 * CV ^ 2 + 2 * (C1 / (2 * Real.pi)) ^ 2 * C2 ^ 2) * (1 + ‖p‖) ^ M) / (2 * Real.pi) :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (2 * CV ^ 2 + 2 * (C1 / (2 * Real.pi)) ^ 2 * C2 ^ 2) * (1 + ‖p‖) ^ M := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)]
        nlinarith [hX0, Real.pi_gt_three]

lemma integrable_schurPhi_sq_div_joint (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hH : ContDiff ℝ 1 H) (hgH : HGrowth H)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ F p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ F) p v v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2)
    (hderivH : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ H p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖) :
    Integrable (fun p : G × ℝ => schurPhi F H p ^ 2 / schurPot F p * Real.exp (-(F p))) := by
  obtain ⟨CF, hCF0, NF, hCF⟩ := hgf
  obtain ⟨CH, hCH0, NH, hCH⟩ := hderivH
  obtain ⟨CV, hCV0, NV, hCV⟩ := hgH
  obtain ⟨C1, hC10, M1, hC1⟩ := gradSlice_le_poly H hH CH hCH0 NH hCH
  obtain ⟨C2, hC20, M2, hC2⟩ := gradSlice_dY_le_poly F hF CF hCF0 NF (fun p v => (hCF p v).2)
  have hcont : Continuous (fun p : G × ℝ => schurPhi F H p ^ 2 / schurPot F p) :=
    Continuous.div ((continuous_schurPhi F H hF hH hH2).pow 2) (continuous_schurPot F hF hH2)
      (fun p => ne_of_gt (schurPot_pos F hF hH2 p.1 p.2))
  refine integrable_mul_exp_neg_potGrowth F (fun p : G × ℝ => schurPhi F H p ^ 2 / schurPot F p)
    hF hp hcont (2 * CV ^ 2 + 2 * (C1 / (2 * Real.pi)) ^ 2 * C2 ^ 2) (by positivity)
    (2 * NV + 2 * M1 + 2 * M2) (fun p => ?_)
  exact schurPhi_sq_div_le F H hF hH2 hC10 hC20 hCV0 le_rfl (fun p => (hCV p).2) hC1 hC2 p

lemma integrable_schurPhi_sq_div_y (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hH : ContDiff ℝ 1 H) (hgH : HGrowth H)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ F p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ F) p v v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2)
    (hderivH : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ H p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖) :
    Integrable (fun y : ℝ => ∫ z : G,
      schurPhi F H (z, y) ^ 2 / schurPot F (z, y) * Real.exp (-(F (z, y)))) := by
  have h := integrable_schurPhi_sq_div_joint F H hF hp hH hgH hH2 hgf hderivH
  rw [Measure.volume_eq_prod G ℝ] at h
  exact h.integral_prod_right

lemma HGrowth0_of_HGrowth {H : G × ℝ → ℝ} (hg : HGrowth H) : HGrowth0 H := by
  obtain ⟨C, hC0, N, hC⟩ := hg
  exact ⟨C, hC0, N, fun p => (hC p).1⟩

lemma HGrowth0_sq {H : G × ℝ → ℝ} (hg : HGrowth H) : HGrowth0 (fun p => H p ^ 2) := by
  obtain ⟨C, hC0, N, hC⟩ := hg
  refine ⟨C ^ 2, by positivity, N * 2, fun p => ?_⟩
  rw [abs_of_nonneg (sq_nonneg (H p))]
  calc H p ^ 2 ≤ (C * (1 + ‖p‖) ^ N) ^ 2 :=
        sq_le_sq' (abs_le.mp (hC p).1).1 (abs_le.mp (hC p).1).2
    _ = C ^ 2 * (1 + ‖p‖) ^ (N * 2) := by rw [mul_pow, ← pow_mul]

lemma continuous_condVar (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hH : ContDiff ℝ 1 H) (hgH : HGrowth H) : Continuous (condVar F H) := by
  have h1 : condVar F H = fun y : ℝ =>
      (∫ z, H (z, y) ^ 2 * Real.exp (-(F (z, y)))) / sliceMass F y
        - ((∫ z, H (z, y) * Real.exp (-(F (z, y)))) / sliceMass F y) ^ 2 := by
    funext y
    rw [condVar, condMean]
  rw [h1]
  exact Continuous.sub
    (continuous_ratio_slice F hF hp (fun p => H p ^ 2) (hH.continuous.pow 2)
      (HGrowth0_sq hgH))
    ((continuous_ratio_slice F hF hp H hH.continuous (HGrowth0_of_HGrowth hgH)).pow 2)

/-- The conditional Cauchy–Schwarz bound `(a-b)²/⟨schurPot⟩ * W ≤ ∫ z schurPhi²/schurPot e^{-F}`. -/
lemma condMeanDeriv_sq_div_mul_sliceMass_le (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hp : PotGrowth F) (hH : ContDiff ℝ 1 H) (hgH : HGrowth H)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ F p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ F) p v v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2)
    (hderivH : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ H p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖)
    (y : ℝ) :
    (deriv (condMean F H) y
        - (sliceCrossEnergy F y (slicePot H y) (mixPot F y) / sliceMass F y
          - condCov F H (fun p => dY F p) y)) ^ 2 / condMean F (schurPot F) y
      * sliceMass F y
      ≤ ∫ z : G, schurPhi F H (z, y) ^ 2 / schurPot F (z, y) * Real.exp (-(F (z, y))) := by
  have hW : 0 < sliceMass F y := sliceMass_pos F hF hp y
  have hcs := condMean_sq_div_le F (schurPhi F H) (schurPot F) y hW
    (fun z => schurPot_pos F hF hH2 z y)
    (integrable_schurPot_slice F hF hp hH2 hgf y)
    (integrable_schurPhi_sq_div_slice F H hF hp hH hgH hH2 hgf hderivH y)
  rw [← condMeanDeriv_sub_eq F H hF hp hH hgH hH2 hgf hderivH y (ne_of_gt hW)] at hcs
  rw [le_div_iff₀ hW] at hcs
  exact hcs

/-- Integrability of `α₁ · W`, where `α₁ = A11 - B11`. -/
lemma integrable_alpha1_mul_sliceMass (IH : BLon G) (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hp : PotGrowth F) (hH : ContDiff ℝ 1 H) (hgH : HGrowth H)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (hderivH : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ H p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖)
    (hconv : ConvexOn ℝ Set.univ (fun p : G × ℝ => F p - Real.pi * (‖p.1‖ ^ 2 + p.2 ^ 2)))
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ F p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ F) p v v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2) :
    Integrable (fun y : ℝ =>
      (sliceEnergy F y (slicePot H y) / sliceMass F y - condVar F H y) * sliceMass F y) := by
  have hderivH' := hderivH
  obtain ⟨CH, hCH0, NH, hCH⟩ := hderivH'
  obtain ⟨C1, hC10, M1, hC1⟩ := gradSlice_le_poly H hH CH hCH0 NH hCH
  have hSE : Integrable (fun y : ℝ => sliceEnergy F y (slicePot H y)) :=
    integrable_gradSlice_bilin_y F hF hp hH2 H H (continuous_gradSlice H hH)
      (continuous_gradSlice H hH) hC10 hC10 hC1 hC1
  have hCV : Integrable (fun y : ℝ => condVar F H y * sliceMass F y) := by
    have hcont : Continuous (fun y : ℝ => condVar F H y * sliceMass F y) :=
      (continuous_condVar F H hF hp hH hgH).mul (contDiff_sliceMass F hF hp).continuous
    refine Integrable.mono' hSE hcont.aestronglyMeasurable ?_
    filter_upwards with y
    have hW : 0 < sliceMass F y := sliceMass_pos F hF hp y
    have h0 := condVar_mul_sliceMass_nonneg F H hF hp hH hgH y
    have hq := bl_slice_quad IH F H hF hH hH2 hconv hgf hp hgH hderivH y 0
    have hq2 : condVar F H y ≤ sliceEnergy F y (slicePot H y) / sliceMass F y := by
      rw [show (sliceEnergy F y (slicePot H y) / sliceMass F y - condVar F H y
          + 2 * (0:ℝ) * (sliceCrossEnergy F y (slicePot H y) (mixPot F y) / sliceMass F y
            - condCov F H (fun p => dY F p) y)
          + (0:ℝ) ^ 2 * (sliceEnergy F y (mixPot F y) / sliceMass F y
            - condVar F (fun p => dY F p) y))
          = sliceEnergy F y (slicePot H y) / sliceMass F y - condVar F H y from by ring] at hq
      linarith [hq]
    have h1 : condVar F H y * sliceMass F y ≤ sliceEnergy F y (slicePot H y) :=
      (le_div_iff₀ hW).mp hq2
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1
  have heq : (fun y : ℝ => (sliceEnergy F y (slicePot H y) / sliceMass F y - condVar F H y)
        * sliceMass F y)
      = fun y : ℝ => sliceEnergy F y (slicePot H y) - condVar F H y * sliceMass F y := by
    funext y
    rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt (sliceMass_pos F hF hp y))]
  rw [heq]
  exact hSE.sub hCV

/-- `α₁ · W ≤ sliceEnergy F y (slicePot H y)`. -/
lemma alpha1_mul_sliceMass_le (IH : BLon G) (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hp : PotGrowth F) (hH : ContDiff ℝ 1 H) (hgH : HGrowth H)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (hderivH : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ H p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖)
    (hconv : ConvexOn ℝ Set.univ (fun p : G × ℝ => F p - Real.pi * (‖p.1‖ ^ 2 + p.2 ^ 2)))
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ F p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ F) p v v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2)
    (y : ℝ) :
    (sliceEnergy F y (slicePot H y) / sliceMass F y - condVar F H y) * sliceMass F y
      ≤ sliceEnergy F y (slicePot H y) := by
  have hW : 0 < sliceMass F y := sliceMass_pos F hF hp y
  have h0 := condVar_mul_sliceMass_nonneg F H hF hp hH hgH y
  have hq := bl_slice_quad IH F H hF hH hH2 hconv hgf hp hgH hderivH y 0
  have hq2 : condVar F H y ≤ sliceEnergy F y (slicePot H y) / sliceMass F y := by
    rw [show (sliceEnergy F y (slicePot H y) / sliceMass F y - condVar F H y
        + 2 * (0:ℝ) * (sliceCrossEnergy F y (slicePot H y) (mixPot F y) / sliceMass F y
          - condCov F H (fun p => dY F p) y)
        + (0:ℝ) ^ 2 * (sliceEnergy F y (mixPot F y) / sliceMass F y
          - condVar F (fun p => dY F p) y))
        = sliceEnergy F y (slicePot H y) / sliceMass F y - condVar F H y from by ring] at hq
    linarith [hq]
  have h1 : condVar F H y * sliceMass F y ≤ sliceEnergy F y (slicePot H y) :=
    (le_div_iff₀ hW).mp hq2
  rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hW)]
  linarith

/-- **Integrability of `(Ξ')²/margD2 · W`** — the `hud` condition of the sharp 1D inequality. -/
lemma integrable_condMeanDeriv_sq_div_margD2 (IH : BLon G) (F H : G × ℝ → ℝ)
    (hF : ContDiff ℝ 2 F) (hp : PotGrowth F) (hH : ContDiff ℝ 1 H) (hgH : HGrowth H)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (hderivH : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ H p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖)
    (hconv : ConvexOn ℝ Set.univ (fun p : G × ℝ => F p - Real.pi * (‖p.1‖ ^ 2 + p.2 ^ 2)))
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ F p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ F) p v v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2) :
    Integrable (fun y : ℝ => (deriv (condMean F H) y) ^ 2 / margD2 F y * sliceMass F y) := by
  have hderivH' := hderivH
  obtain ⟨CH, hCH0, NH, hCH⟩ := hderivH'
  obtain ⟨C1, hC10, M1, hC1⟩ := gradSlice_le_poly H hH CH hCH0 NH hCH
  have hSE : Integrable (fun y : ℝ => sliceEnergy F y (slicePot H y)) :=
    integrable_gradSlice_bilin_y F hF hp hH2 H H (continuous_gradSlice H hH)
      (continuous_gradSlice H hH) hC10 hC10 hC1 hC1
  have hPhi := integrable_schurPhi_sq_div_y F H hF hp hH hgH hH2 hgf hderivH
  have hcont : Continuous (fun y : ℝ => (deriv (condMean F H) y) ^ 2 / margD2 F y
      * sliceMass F y) := by
    refine Continuous.mul ?_ (contDiff_sliceMass F hF hp).continuous
    refine Continuous.div
      ((ContDiff.continuous_deriv (contDiff_condMean F H hF hp hH hgH) (by norm_num)).pow 2)
      (continuous_margD2 F hF hp (fun y => sliceMass_pos F hF hp y)) ?_
    intro y
    have h := two_pi_le_margD2 IH F hF hH2 hconv hgf hp y
    linarith [Real.pi_pos]
  refine Integrable.mono' (hSE.add hPhi) hcont.aestronglyMeasurable ?_
  filter_upwards with y
  have hW : 0 < sliceMass F y := sliceMass_pos F hF hp y
  have hα : 0 < margD2 F y := by
    have h := two_pi_le_margD2 IH F hF hH2 hconv hgf hp y
    linarith [Real.pi_pos]
  have hnn : 0 ≤ (deriv (condMean F H) y) ^ 2 / margD2 F y * sliceMass F y :=
    mul_nonneg (div_nonneg (sq_nonneg _) hα.le) hW.le
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  have hkey := a_sq_div_le_combined IH F H hF hH hH2 hconv hgf hp hgH hderivH y
  have hsplit : (sliceEnergy F y (slicePot H y) / sliceMass F y - condVar F H y
      + (deriv (condMean F H) y - (sliceCrossEnergy F y (slicePot H y) (mixPot F y) / sliceMass F y
          - condCov F H (fun p => dY F p) y)) ^ 2 / condMean F (schurPot F) y) * sliceMass F y
      = (sliceEnergy F y (slicePot H y) / sliceMass F y - condVar F H y) * sliceMass F y
        + (deriv (condMean F H) y - (sliceCrossEnergy F y (slicePot H y) (mixPot F y) / sliceMass F y
            - condCov F H (fun p => dY F p) y)) ^ 2 / condMean F (schurPot F) y * sliceMass F y := by
    ring
  rw [hsplit] at hkey
  have h2 := condMeanDeriv_sq_div_mul_sliceMass_le F H hF hp hH hgH hH2 hgf hderivH y
  have h1 := alpha1_mul_sliceMass_le IH F H hF hp hH hgH hH2 hderivH hconv hgf y
  show deriv (condMean F H) y ^ 2 / margD2 F y * sliceMass F y
      ≤ sliceEnergy F y (slicePot H y)
        + ∫ z : G, schurPhi F H (z, y) ^ 2 / schurPot F (z, y) * Real.exp (-(F (z, y)))
  linarith [hkey, h1, h2]

/-- **The marginal conclusion.** The variance of `Ξ = condMean F H` with respect to the marginal
`sliceMass F y dy` is bounded by `∫ (Ξ')²/margD2 · W` — the sharp 1D Brascamp–Lieb inequality with
every hypothesis discharged. -/
lemma marg_variance_le_margD2 (IH : BLon G) (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hp : PotGrowth F) (hH : ContDiff ℝ 1 H) (hgH : HGrowth H)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (hderivH : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ H p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖)
    (hconv : ConvexOn ℝ Set.univ (fun p : G × ℝ => F p - Real.pi * (‖p.1‖ ^ 2 + p.2 ^ 2)))
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ F p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ F) p v v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2) :
    (∫ y, condMean F H y ^ 2 * sliceMass F y)
        - (∫ y, condMean F H y * sliceMass F y) ^ 2 / (∫ y, sliceMass F y)
      ≤ ∫ y, (deriv (condMean F H) y) ^ 2 / margD2 F y * sliceMass F y := by
  have hW : ∀ y : ℝ, 0 < sliceMass F y := fun y => sliceMass_pos F hF hp y
  have hmarg2 : ∀ y : ℝ, 2 * Real.pi ≤ margD2 F y :=
    fun y => two_pi_le_margD2 IH F hF hH2 hconv hgf hp y
  have hV2 : ∀ y : ℝ, 0 < deriv (deriv (marg F)) y := by
    intro y
    rw [deriv_deriv_marg F hF hp hW y]
    linarith [hmarg2 y, Real.pi_pos]
  have hud : Integrable (fun y : ℝ => (deriv (condMean F H) y) ^ 2
      / deriv (deriv (marg F)) y * Real.exp (-(marg F y))) := by
    have h0 := integrable_condMeanDeriv_sq_div_margD2 IH F H hF hp hH hgH hH2 hderivH hconv hgf
    refine h0.congr ?_
    filter_upwards with y
    rw [← exp_neg_marg_apply F hW y, ← deriv_deriv_marg F hF hp hW y]
  have h := marg_variance_le_sliceMass F H hF hp hH hgH hW hV2
    (integrable_condMean_sq_div_margD2 F H hF hp hH hgH hW hmarg2) hud
  simp_rw [deriv_deriv_marg F hF hp hW] at h
  exact h

lemma condVar_mul_sliceMass_le_sliceEnergy (IH : BLon G) (F H : G × ℝ → ℝ)
    (hF : ContDiff ℝ 2 F) (hp : PotGrowth F) (hH : ContDiff ℝ 1 H) (hgH : HGrowth H)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (hderivH : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ H p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖)
    (hconv : ConvexOn ℝ Set.univ (fun p : G × ℝ => F p - Real.pi * (‖p.1‖ ^ 2 + p.2 ^ 2)))
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ F p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ F) p v v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2)
    (y : ℝ) :
    condVar F H y * sliceMass F y ≤ sliceEnergy F y (slicePot H y) := by
  have hW : 0 < sliceMass F y := sliceMass_pos F hF hp y
  have hq := bl_slice_quad IH F H hF hH hH2 hconv hgf hp hgH hderivH y 0
  have hq2 : condVar F H y ≤ sliceEnergy F y (slicePot H y) / sliceMass F y := by
    rw [show (sliceEnergy F y (slicePot H y) / sliceMass F y - condVar F H y
        + 2 * (0:ℝ) * (sliceCrossEnergy F y (slicePot H y) (mixPot F y) / sliceMass F y
          - condCov F H (fun p => dY F p) y)
        + (0:ℝ) ^ 2 * (sliceEnergy F y (mixPot F y) / sliceMass F y
          - condVar F (fun p => dY F p) y))
        = sliceEnergy F y (slicePot H y) / sliceMass F y - condVar F H y from by ring] at hq
    linarith [hq]
  exact (le_div_iff₀ hW).mp hq2

lemma deriv_condMean_sq_div_le (IH : BLon G) (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hH : ContDiff ℝ 1 H) (hgH : HGrowth H)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (hconv : ConvexOn ℝ Set.univ (fun p : G × ℝ => F p - Real.pi * (‖p.1‖ ^ 2 + p.2 ^ 2)))
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ F p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ F) p v v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2)
    (hp : PotGrowth F)
    (hderivH : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ H p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖)
    (y : ℝ) :
    (deriv (condMean F H) y) ^ 2 / margD2 F y
      ≤ (sliceEnergy F y (slicePot H y) / sliceMass F y - condVar F H y)
        + (deriv (condMean F H) y
            - (sliceCrossEnergy F y (slicePot H y) (mixPot F y) / sliceMass F y
              - condCov F H (fun p => dY F p) y)) ^ 2 / condMean F (schurPot F) y := by
  have hW : 0 < sliceMass F y := sliceMass_pos F hF hp y
  have hkey := a_sq_div_le_combined IH F H hF hH hH2 hconv hgf hp hgH hderivH y
  rw [mul_le_mul_iff_of_pos_right hW] at hkey
  convert hkey using 2 <;> ring

lemma integrable_condVar_mul_sliceMass (IH : BLon G) (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hp : PotGrowth F) (hH : ContDiff ℝ 1 H) (hgH : HGrowth H)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (hderivH : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ H p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖)
    (hconv : ConvexOn ℝ Set.univ (fun p : G × ℝ => F p - Real.pi * (‖p.1‖ ^ 2 + p.2 ^ 2)))
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ F p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ F) p v v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2) :
    Integrable (fun y : ℝ => condVar F H y * sliceMass F y) := by
  have hderivH' := hderivH
  obtain ⟨CH, hCH0, NH, hCH⟩ := hderivH'
  obtain ⟨C1, hC10, M1, hC1⟩ := gradSlice_le_poly H hH CH hCH0 NH hCH
  have hSE : Integrable (fun y : ℝ => sliceEnergy F y (slicePot H y)) :=
    integrable_gradSlice_bilin_y F hF hp hH2 H H (continuous_gradSlice H hH)
      (continuous_gradSlice H hH) hC10 hC10 hC1 hC1
  have hcont : Continuous (fun y : ℝ => condVar F H y * sliceMass F y) :=
    (continuous_condVar F H hF hp hH hgH).mul (contDiff_sliceMass F hF hp).continuous
  refine Integrable.mono' hSE hcont.aestronglyMeasurable ?_
  filter_upwards with y
  have h0 := condVar_mul_sliceMass_nonneg F H hF hp hH hgH y
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact condVar_mul_sliceMass_le_sliceEnergy IH F H hF hp hH hgH hH2 hderivH hconv hgf y

theorem bl_slice_level (IH : BLon G) (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hH : ContDiff ℝ 1 H) (hgH : HGrowth H)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (hderivH : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ H p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖)
    (hconv : ConvexOn ℝ Set.univ (fun p : G × ℝ => F p - Real.pi * (‖p.1‖ ^ 2 + p.2 ^ 2)))
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ F p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ F) p v v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2) :
    wVar (fun p : G × ℝ => Real.exp (-(F p))) H
      ≤ (∫ y, sliceEnergy F y (slicePot H y))
        + ∫ y, ∫ z : G,
            schurPhi F H (z, y) ^ 2 / schurPot F (z, y) * Real.exp (-(F (z, y))) := by
  have hW : ∀ y : ℝ, 0 < sliceMass F y := fun y => sliceMass_pos F hF hp y
  have hderivH0 := hderivH
  have hgH0 := hgH
  obtain ⟨CH, hCH0, NH, hCH⟩ := hderivH0
  obtain ⟨CV, hCV0, NV, hCV⟩ := hgH0
  obtain ⟨C1, hC10, M1, hC1⟩ := gradSlice_le_poly H hH CH hCH0 NH hCH
  have hintE : Integrable (fun p : G × ℝ => Real.exp (-(F p))) := by
    simpa only [one_mul] using integrable_mul_exp_neg_potGrowth F (fun _ : G × ℝ => (1 : ℝ))
      hF hp continuous_const 1 (by norm_num) 0 (fun p => by simp)
  have hsq : ∀ p : G × ℝ, |H p ^ 2| ≤ CV ^ 2 * (1 + ‖p‖) ^ (NV * 2) := by
    intro p
    rw [abs_of_nonneg (sq_nonneg (H p))]
    calc H p ^ 2 ≤ (CV * (1 + ‖p‖) ^ NV) ^ 2 :=
          sq_le_sq' (abs_le.mp (hCV p).1).1 (abs_le.mp (hCV p).1).2
      _ = CV ^ 2 * (1 + ‖p‖) ^ (NV * 2) := by rw [mul_pow, ← pow_mul]
  have hint2 : Integrable (fun p : G × ℝ => H p ^ 2 * Real.exp (-(F p))) :=
    integrable_mul_exp_neg_potGrowth F (fun p : G × ℝ => H p ^ 2) hF hp
      (hH.continuous.pow 2) (CV ^ 2) (by positivity) (NV * 2) hsq
  have hint1 : Integrable (fun p : G × ℝ => H p * Real.exp (-(F p))) :=
    integrable_mul_exp_neg_potGrowth F H hF hp hH.continuous CV hCV0 NV (fun p => (hCV p).1)
  have hsl2 : ∀ y : ℝ, Integrable (fun z : G => H (z, y) ^ 2 * Real.exp (-(F (z, y)))) := by
    intro y
    refine (integrable_slice_mul F hF hp y (fun p => H p ^ 2) (hH.continuous.pow 2)
      (CV ^ 2) (by positivity) (NV * 2) hsq).congr ?_
    filter_upwards with z
    simp only [slicePot]
  have hslE : ∀ y : ℝ, Integrable (fun z : G => Real.exp (-(F (z, y)))) :=
    fun y => integrable_slice_exp_neg F hF hp y
  have hWTV := wVar_prod_eq F H hW hintE hint2 hint1 hsl2 hslE
  have hTV := marg_variance_le_margD2 IH F H hF hp hH hgH hH2 hderivH hconv hgf
  have hintB : Integrable (fun y : ℝ => condVar F H y * sliceMass F y) :=
    integrable_condVar_mul_sliceMass IH F H hF hp hH hgH hH2 hderivH hconv hgf
  have hSE : Integrable (fun y : ℝ => sliceEnergy F y (slicePot H y)) :=
    integrable_gradSlice_bilin_y F hF hp hH2 H H (continuous_gradSlice H hH)
      (continuous_gradSlice H hH) hC10 hC10 hC1 hC1
  have hint_a : Integrable (fun y : ℝ => (deriv (condMean F H) y) ^ 2 / margD2 F y
      * sliceMass F y) :=
    integrable_condMeanDeriv_sq_div_margD2 IH F H hF hp hH hgH hH2 hderivH hconv hgf
  have hGam : Integrable (fun y : ℝ => ∫ z : G,
      schurPhi F H (z, y) ^ 2 / schurPot F (z, y) * Real.exp (-(F (z, y)))) :=
    integrable_schurPhi_sq_div_y F H hF hp hH hgH hH2 hgf hderivH
  have hmain : ∀ y : ℝ, condVar F H y * sliceMass F y
        + (deriv (condMean F H) y) ^ 2 / margD2 F y * sliceMass F y
      ≤ sliceEnergy F y (slicePot H y)
        + ∫ z : G, schurPhi F H (z, y) ^ 2 / schurPot F (z, y) * Real.exp (-(F (z, y))) := by
    intro y
    have hWy : 0 < sliceMass F y := hW y
    have h1 := deriv_condMean_sq_div_le IH F H hF hH hgH hH2 hconv hgf hp hderivH y
    have h2 := condMeanDeriv_sq_div_mul_sliceMass_le F H hF hp hH hgH hH2 hgf hderivH y
    have h3 : (deriv (condMean F H) y) ^ 2 / margD2 F y * sliceMass F y
        ≤ sliceEnergy F y (slicePot H y) - condVar F H y * sliceMass F y
          + (deriv (condMean F H) y
              - (sliceCrossEnergy F y (slicePot H y) (mixPot F y) / sliceMass F y
                - condCov F H (fun p => dY F p) y)) ^ 2 / condMean F (schurPot F) y
            * sliceMass F y := by
      have h := mul_le_mul_of_nonneg_right h1 hWy.le
      rw [show (sliceEnergy F y (slicePot H y) / sliceMass F y - condVar F H y
            + (deriv (condMean F H) y
                - (sliceCrossEnergy F y (slicePot H y) (mixPot F y) / sliceMass F y
                  - condCov F H (fun p => dY F p) y)) ^ 2 / condMean F (schurPot F) y)
            * sliceMass F y
          = sliceEnergy F y (slicePot H y) - condVar F H y * sliceMass F y
            + (deriv (condMean F H) y
                - (sliceCrossEnergy F y (slicePot H y) (mixPot F y) / sliceMass F y
                  - condCov F H (fun p => dY F p) y)) ^ 2 / condMean F (schurPot F) y
              * sliceMass F y from by
        rw [add_mul, sub_mul, div_mul_cancel₀ _ (ne_of_gt hWy)]
        try ring] at h
      exact h
    linarith [h2, h3]
  have hmono : (∫ y, (condVar F H y * sliceMass F y
        + (deriv (condMean F H) y) ^ 2 / margD2 F y * sliceMass F y))
      ≤ ∫ y, (sliceEnergy F y (slicePot H y)
        + ∫ z : G, schurPhi F H (z, y) ^ 2 / schurPot F (z, y) * Real.exp (-(F (z, y)))) :=
    integral_mono (hintB.add hint_a) (hSE.add hGam) hmain
  rw [hWTV]
  calc (∫ y, condVar F H y * sliceMass F y)
        + ((∫ y, condMean F H y ^ 2 * sliceMass F y)
          - (∫ y, condMean F H y * sliceMass F y) ^ 2 / (∫ y, sliceMass F y))
      ≤ (∫ y, condVar F H y * sliceMass F y)
        + ∫ y, (deriv (condMean F H) y) ^ 2 / margD2 F y * sliceMass F y := by
        linarith [hTV]
    _ = ∫ y, (condVar F H y * sliceMass F y
          + (deriv (condMean F H) y) ^ 2 / margD2 F y * sliceMass F y) :=
        (integral_add hintB hint_a).symm
    _ ≤ ∫ y, (sliceEnergy F y (slicePot H y)
          + ∫ z : G, schurPhi F H (z, y) ^ 2 / schurPot F (z, y) * Real.exp (-(F (z, y)))) := hmono
    _ = (∫ y, sliceEnergy F y (slicePot H y))
          + ∫ y, ∫ z : G, schurPhi F H (z, y) ^ 2 / schurPot F (z, y) * Real.exp (-(F (z, y))) :=
        integral_add hSE hGam

lemma EN_eq_slice (f : WithLp 2 (G × ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (F : G × ℝ → ℝ) (hF : F = fun p : G × ℝ => f (WithLp.toLp 2 p))
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (h : WithLp 2 (G × ℝ) → ℝ) (hh : ContDiff ℝ 1 h)
    (H : G × ℝ → ℝ) (hHh : H = fun p : G × ℝ => h (WithLp.toLp 2 p)) (z : G) (y : ℝ) :
    ⟪hessInv f (WithLp.toLp 2 (z, y)) (grad h (WithLp.toLp 2 (z, y))),
        grad h (WithLp.toLp 2 (z, y))⟫_ℝ
      = ⟪hessInv (slicePot F y) z (grad (slicePot H y) z), grad (slicePot H y) z⟫_ℝ
        + schurPhi F H (z, y) ^ 2 / schurPot F (z, y) := by
  have hFcd : ContDiff ℝ 2 F := by rw [hF]; exact contDiff_comp_toLp f 2 hf
  have h1 := hessInv_energy_eq f hf F hF hH2 h hh H hHh z y
  rw [h1]
  have hnum : dY H (z, y)
      - ⟪hessInv (slicePot F y) z (grad (mixPot F y) z), grad (slicePot H y) z⟫_ℝ
      = schurPhi F H (z, y) := by
    rw [schurPhi]
    congr 1
    exact (crossFn_eq_swapped F H hFcd hH2 (z, y)).symm
  have hden : fderiv ℝ (fderiv ℝ F) (z, y) (0, 1) (0, 1)
      - ⟪hessInv (slicePot F y) z (grad (mixPot F y) z), grad (mixPot F y) z⟫_ℝ
      = schurPot F (z, y) := by
    rw [schurPot, sliceEnergyFn, ← d2Y_eq_hess F hFcd (z, y)]
    try rfl
  rw [hnum, hden]

lemma fubini_sliceEnergy (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hH : ContDiff ℝ 1 H)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (hderivH : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ H p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖) :
    (∫ p : G × ℝ,
        ⟪hessInv (slicePot F p.2) p.1 (gradSlice H p), gradSlice H p⟫_ℝ * Real.exp (-(F p)))
      = ∫ y, sliceEnergy F y (slicePot H y) := by
  obtain ⟨CH, hCH0, NH, hCH⟩ := hderivH
  obtain ⟨C1, hC10, M1, hC1⟩ := gradSlice_le_poly H hH CH hCH0 NH hCH
  have hint := integrable_gradSlice_bilin F hF hp hH2 H H (continuous_gradSlice H hH)
    (continuous_gradSlice H hH) hC10 hC10 hC1 hC1
  rw [Measure.volume_eq_prod G ℝ] at hint ⊢
  rw [integral_prod_symm _ hint]
  rfl

lemma fubini_schurPhi (F H : G × ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hp : PotGrowth F)
    (hH : ContDiff ℝ 1 H) (hgH : HGrowth H)
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ F p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ F) p v v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2)
    (hderivH : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ H p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖) :
    (∫ p : G × ℝ, schurPhi F H p ^ 2 / schurPot F p * Real.exp (-(F p)))
      = ∫ y, ∫ z : G,
          schurPhi F H (z, y) ^ 2 / schurPot F (z, y) * Real.exp (-(F (z, y))) := by
  have hint := integrable_schurPhi_sq_div_joint F H hF hp hH hgH hH2 hgf hderivH
  rw [Measure.volume_eq_prod G ℝ] at hint ⊢
  rw [integral_prod_symm _ hint]

lemma EN_eq_slice' (f : WithLp 2 (G × ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (F : G × ℝ → ℝ) (hF : F = fun p : G × ℝ => f (WithLp.toLp 2 p))
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (h : WithLp 2 (G × ℝ) → ℝ) (hh : ContDiff ℝ 1 h)
    (H : G × ℝ → ℝ) (hHh : H = fun p : G × ℝ => h (WithLp.toLp 2 p)) (p : G × ℝ) :
    ⟪hessInv f (WithLp.toLp 2 p) (grad h (WithLp.toLp 2 p)), grad h (WithLp.toLp 2 p)⟫_ℝ
      = ⟪hessInv (slicePot F p.2) p.1 (gradSlice H p), gradSlice H p⟫_ℝ
        + schurPhi F H p ^ 2 / schurPot F p :=
  EN_eq_slice f hf F hF hH2 h hh H hHh p.1 p.2

theorem bl_ambient (IH : BLon G) (f : WithLp 2 (G × ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (F : G × ℝ → ℝ) (hF : F = fun p : G × ℝ => f (WithLp.toLp 2 p))
    (h : WithLp 2 (G × ℝ) → ℝ) (hh : ContDiff ℝ 1 h)
    (H : G × ℝ → ℝ) (hHh : H = fun p : G × ℝ => h (WithLp.toLp 2 p))
    (hH2 : ∀ p v : G × ℝ, 2 * Real.pi * (‖v.1‖ ^ 2 + v.2 ^ 2)
      ≤ fderiv ℝ (fderiv ℝ F) p v v)
    (hconv : ConvexOn ℝ Set.univ (fun p : G × ℝ => F p - Real.pi * (‖p.1‖ ^ 2 + p.2 ^ 2)))
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ F p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ F) p v v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ ^ 2)
    (hp : PotGrowth F) (hH : ContDiff ℝ 1 H) (hgH : HGrowth H)
    (hderivH : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ H p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖) :
    wVar (fun p : G × ℝ => Real.exp (-(F p))) H
      ≤ ∫ p : G × ℝ, ⟪hessInv f (WithLp.toLp 2 p) (grad h (WithLp.toLp 2 p)),
          grad h (WithLp.toLp 2 p)⟫_ℝ * Real.exp (-(F p)) := by
  have hFcd : ContDiff ℝ 2 F := by rw [hF]; exact contDiff_comp_toLp f 2 hf
  have hderivH' := hderivH
  obtain ⟨CH, hCH0, NH, hCH⟩ := hderivH'
  obtain ⟨C1, hC10, M1, hC1⟩ := gradSlice_le_poly H hH CH hCH0 NH hCH
  have hint1 := integrable_gradSlice_bilin F hFcd hp hH2 H H (continuous_gradSlice H hH)
    (continuous_gradSlice H hH) hC10 hC10 hC1 hC1
  have hint2 := integrable_schurPhi_sq_div_joint F H hFcd hp hH hgH hH2 hgf hderivH
  have h1 := bl_slice_level IH F H hFcd hp hH hgH hH2 hderivH hconv hgf
  rw [← fubini_sliceEnergy F H hFcd hp hH hH2 hderivH,
    ← fubini_schurPhi F H hFcd hp hH hgH hH2 hgf hderivH] at h1
  refine le_trans h1 ?_
  rw [← integral_add hint1 hint2]
  refine le_of_eq (integral_congr_ae ?_)
  filter_upwards with p
  rw [EN_eq_slice' f hf F hF hH2 h hh H hHh p]
  ring

theorem bl_product_step (IH : BLon G) : BLon (WithLp 2 (G × ℝ)) := by
  intro f h hf hHess hconv hgf hh hgh
  have hFcd : ContDiff ℝ 2 (fun p : G × ℝ => f (WithLp.toLp 2 p)) := contDiff_comp_toLp f 2 hf
  have hHcd : ContDiff ℝ 1 (fun p : G × ℝ => h (WithLp.toLp 2 p)) := contDiff_comp_toLp h 1 hh
  have hGH : HGrowth (fun p : G × ℝ => h (WithLp.toLp 2 p)) := hgrowth_comp_toLp h hh hgh
  have hderivH : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p v : G × ℝ,
      |fderiv ℝ (fun p : G × ℝ => h (WithLp.toLp 2 p)) p v| ≤ C * (1 + ‖p‖) ^ N * ‖v‖ := by
    obtain ⟨C, hC0, N, hCN⟩ := growth_comp_toLp_h h hh hgh
    exact ⟨C, hC0, N, fun p v => (hCN p v).2⟩
  have hmain := bl_ambient IH f hf (fun p : G × ℝ => f (WithLp.toLp 2 p)) rfl h hh
    (fun p : G × ℝ => h (WithLp.toLp 2 p)) rfl
    (hessian_comp_toLp_l2 f hf hHess) (convexOn_comp_toLp f hconv)
    (growth_comp_toLp f hf hgf) (potGrowth_comp_toLp f hf hconv hgf) hHcd hGH hderivH
  have hwv : wVar (fun x : WithLp 2 (G × ℝ) => Real.exp (-(f x))) h
      = wVar (fun p : G × ℝ => Real.exp (-(f (WithLp.toLp 2 p))))
          (fun p : G × ℝ => h (WithLp.toLp 2 p)) := by
    rw [wVar, wVar,
      ← integral_comp_toLp (fun x : WithLp 2 (G × ℝ) => h x ^ 2 * Real.exp (-(f x))),
      ← integral_comp_toLp (fun x : WithLp 2 (G × ℝ) => h x * Real.exp (-(f x))),
      ← integral_comp_toLp (fun x : WithLp 2 (G × ℝ) => Real.exp (-(f x)))]
  show wVar (fun x : WithLp 2 (G × ℝ) => Real.exp (-(f x))) h
      ≤ ∫ x : WithLp 2 (G × ℝ), ⟪hessInv f x (grad h x), grad h x⟫_ℝ * Real.exp (-(f x))
  rw [hwv,
    integral_comp_toLp (fun x : WithLp 2 (G × ℝ) =>
      ⟪hessInv f x (grad h x), grad h x⟫_ℝ * Real.exp (-(f x)))]
  exact hmain


end Product





/-! ### Brascamp–Lieb for a smooth strongly convex potential

This is the induction target of Stage 1 described at the top of the file.  The proof is by strong
induction on `Module.finrank ℝ E`.  For `0 < finrank ℝ E` choose a nonzero vector `u`, let
`K := ℝ ∙ u` (a one-dimensional subspace) and use the orthogonal decomposition
`E ≃ₗᵢ[ℝ] WithLp 2 (K × Kᗮ)` (`Submodule.orthogonalDecomposition`) together with `K ≃ₗᵢ[ℝ] ℝ`
(`MeasureTheory.volume_eq_of_finrank_eq_one` and the one-dimensional isometry lemma).  This reduces
the statement to the *product step*: Brascamp–Lieb for `WithLp 2 (G × ℝ)` assuming Brascamp–Lieb
for `G` — which is proved by slicing and using the sharp one-dimensional inequality for the
marginal. -/
theorem bl_zero : BLon (EuclideanSpace ℝ (Fin 0)) := by
  intro f h hf hH hconv hgf hh hgh
  have hconst : ∀ x y : EuclideanSpace ℝ (Fin 0), h x = h y := fun x y => by
    rw [Subsingleton.elim x y]
  have hconstfun : h = fun _ : EuclideanSpace ℝ (Fin 0) => h 0 := funext (fun y => hconst y 0)
  have hgrad : ∀ x : EuclideanSpace ℝ (Fin 0), grad h x = 0 := by
    intro x
    refine ext_inner_right ℝ (fun v => ?_)
    rw [grad_spec]
    have hv : v = 0 := Subsingleton.elim v 0
    rw [hv, hconstfun]
    simp
  have hhi : ∀ x : EuclideanSpace ℝ (Fin 0), h x = h 0 := fun x => hconst x 0
  have e1 : (∫ x : EuclideanSpace ℝ (Fin 0), h x ^ 2 * Real.exp (-(f x)))
      = h 0 ^ 2 * ∫ x : EuclideanSpace ℝ (Fin 0), Real.exp (-(f x)) := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext x
    rw [hhi x]
  have e2 : (∫ x : EuclideanSpace ℝ (Fin 0), h x * Real.exp (-(f x)))
      = h 0 * ∫ x : EuclideanSpace ℝ (Fin 0), Real.exp (-(f x)) := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext x
    rw [hhi x]
  have e3 : (∫ x : EuclideanSpace ℝ (Fin 0),
        ⟪hessInv f x (grad h x), grad h x⟫_ℝ * Real.exp (-(f x))) = 0 := by
    refine MeasureTheory.integral_eq_zero_of_ae ?_
    filter_upwards with x
    rw [hgrad x]
    simp
  rw [e1, e2, e3]
  set M : ℝ := ∫ x : EuclideanSpace ℝ (Fin 0), Real.exp (-(f x)) with hMdef
  have hzero : h 0 ^ 2 * M - (h 0 * M) ^ 2 / M = 0 := by
    rcases eq_or_ne M 0 with hM0 | hM0
    · rw [hM0, mul_zero, mul_zero, div_zero, sub_zero]
    · field_simp
      ring
  rw [hzero]

/-! ### Calculus identities on `ℝ` -/

lemma fderiv_fderiv_real (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (x v w : ℝ) :
    fderiv ℝ (fderiv ℝ f) x v w = deriv (deriv f) x * v * w := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x := by
    have h : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.contDiffAt.fderiv_right (by norm_num)
    exact h.differentiableAt (by norm_num)
  have h1 : fderiv ℝ (fun q : ℝ => fderiv ℝ f q w) x v = fderiv ℝ (fderiv ℝ f) x v w := by
    have h := fderiv_clm_apply (𝕜 := ℝ) (c := (fderiv ℝ f : ℝ → (ℝ →L[ℝ] ℝ)))
      (u := fun _ : ℝ => w) (x := x) hd (differentiableAt_const w)
    rw [h]
    simp
  rw [← h1]
  have h2 : (fun q : ℝ => fderiv ℝ f q w) = fun q => w * deriv f q := by
    funext q
    rw [fderiv_eq_smul_deriv]
    simp
  rw [h2, show (fun q : ℝ => w * deriv f q) = fun q => w • deriv f q from rfl]
  rw [fderiv_fun_const_smul (f := deriv f) ?_ w]
  · rw [smul_apply, fderiv_eq_smul_deriv]
    ring
  · exact ((hf.deriv' (n := 1)).contDiffAt).differentiableAt (by norm_num)

lemma grad_real (h : ℝ → ℝ) (x : ℝ) : grad h x = deriv h x := by
  have h1 := grad_spec h x 1
  rw [fderiv_apply_one_eq_deriv] at h1
  simpa using h1

lemma hessOp_real (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (x v : ℝ) :
    hessOp f x v = deriv (deriv f) x * v := by
  refine ext_inner_right ℝ (fun w => ?_)
  rw [hessOp_spec, fderiv_fderiv_real f hf x v w]
  simp [mul_comm]

lemma hessInv_real (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hH : ∀ x v : ℝ, 2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v)
    (x v : ℝ) (hpos : 0 < deriv (deriv f) x) :
    hessInv f x v = v / deriv (deriv f) x := by
  have hinj : Function.Injective (hessOp f x) := hessOp_injective f x (hH x)
  have hkey : hessOp f x (v / deriv (deriv f) x) = v := by
    rw [hessOp_real f hf x, mul_div_cancel₀ v (ne_of_gt hpos)]
  calc hessInv f x v = hessInv f x (hessOp f x (v / deriv (deriv f) x)) := by rw [hkey]
    _ = v / deriv (deriv f) x := hessInv_left f x hinj _

/-! ### Convexity, coercivity, integrability on `ℝ` -/

lemma convexOn_pi_norm_sq_real : ConvexOn ℝ Set.univ (fun x : ℝ => Real.pi * ‖x‖ ^ 2) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hnorm : ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ := by
    calc ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
  have hsq : ‖a • x + b • y‖ ^ 2 ≤ (a * ‖x‖ + b * ‖y‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hkey : (a * ‖x‖ + b * ‖y‖) ^ 2 ≤ a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x‖ - ‖y‖), mul_nonneg ha hb, sq_nonneg ‖x‖, sq_nonneg ‖y‖, hab]
  calc Real.pi * ‖a • x + b • y‖ ^ 2
      ≤ Real.pi * (a * ‖x‖ + b * ‖y‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq Real.pi_pos.le
    _ ≤ Real.pi * (a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hkey Real.pi_pos.le
    _ = a * (Real.pi * ‖x‖ ^ 2) + b * (Real.pi * ‖y‖ ^ 2) := by ring

lemma tangent_le_of_convexOn (g : ℝ → ℝ) (hconv : ConvexOn ℝ Set.univ g)
    (hd : DifferentiableAt ℝ g 0) (x : ℝ) :
    g 0 + deriv g 0 * x ≤ g x := by
  rcases lt_trichotomy (0:ℝ) x with h | h | h
  · have h1 := hconv.deriv_le_slope (Set.mem_univ 0) (Set.mem_univ x) h hd
    rw [slope_def_field] at h1
    have hpos : 0 < x - 0 := by linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hpos.le
    rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at h2
    linarith
  · subst h; simp
  · have h1 := hconv.slope_le_deriv (Set.mem_univ x) (Set.mem_univ 0) h hd
    rw [slope_def_field] at h1
    have hpos : 0 < 0 - x := by linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hpos.le
    rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at h2
    linarith

lemma tendsto_pi_sq_add_linear (g0 d0 : ℝ) :
    Tendsto (fun x : ℝ => Real.pi * x ^ 2 + g0 + d0 * x) atTop atTop := by
  have hbase : Tendsto (fun x : ℝ => Real.pi / 2 * x ^ 2 + g0) atTop atTop := by
    have hsq : Tendsto (fun x : ℝ => x ^ 2) atTop atTop := by
      rw [tendsto_atTop]
      intro b
      filter_upwards [eventually_ge_atTop (max 1 (Real.sqrt (max 0 b)))] with x hx
      have hb : b ≤ (Real.sqrt (max 0 b)) ^ 2 := by
        rw [Real.sq_sqrt (le_max_left 0 b)]
        exact le_max_right 0 b
      have hx' : Real.sqrt (max 0 b) ≤ x := le_trans (le_max_right _ _) hx
      calc b ≤ (Real.sqrt (max 0 b)) ^ 2 := hb
        _ ≤ x ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hx' 2
    exact tendsto_atTop_add_const_right _ g0 (Tendsto.const_mul_atTop (by positivity) hsq)
  refine tendsto_atTop_mono' atTop ?_ hbase
  filter_upwards [eventually_ge_atTop (max 1 (2 * |d0| / Real.pi))] with x hx
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : 2 * |d0| / Real.pi ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : 0 < x := lt_of_lt_of_le one_pos hx1
  have h4 : |d0| ≤ Real.pi / 2 * x := by
    have h5 : 2 * |d0| ≤ Real.pi * x := by
      have h6 := mul_le_mul_of_nonneg_right hx2 Real.pi_pos.le
      rw [div_mul_cancel₀ _ (ne_of_gt Real.pi_pos)] at h6
      linarith
    linarith
  have h3 : |d0| * x ≤ Real.pi / 2 * x ^ 2 := by nlinarith [h4, hxpos]
  have h6 : -( |d0| * x) ≤ d0 * x := by
    have h7 : -|d0| ≤ d0 := neg_abs_le d0
    have h8 := mul_le_mul_of_nonneg_right h7 hxpos.le
    linarith
  linarith

lemma tendsto_pi_sq_add_linear_bot (g0 d0 : ℝ) :
    Tendsto (fun x : ℝ => Real.pi * x ^ 2 + g0 + d0 * x) atBot atTop := by
  have h := (tendsto_pi_sq_add_linear g0 (-d0)).comp tendsto_neg_atBot_atTop
  have h' : (fun x : ℝ => Real.pi * x ^ 2 + g0 + d0 * x)
      = ((fun x : ℝ => Real.pi * x ^ 2 + g0 + (-d0) * x) ∘ fun x : ℝ => -x) := by
    funext x
    simp only [Function.comp_apply]
    ring
  rwa [h']

lemma integrable_poly_mul_exp_neg_of_coercive (f : ℝ → ℝ) (l m : ℝ) (hfc : Continuous f)
    (h : ∀ x, Real.pi * x ^ 2 + l * x + m ≤ f x) (N : ℕ) :
    Integrable (fun x : ℝ => (1 + ‖x‖) ^ N * Real.exp (-(f x))) := by
  have hbase : Integrable (fun x : ℝ => (1 + ‖x‖) ^ N * Real.exp (-(Real.pi / 2) * x ^ 2)) := by
    have hb := Commons.Analysis.Asymptotics.integrable_pow_mul_exp_neg_sq (V := ℝ)
      (Real.pi / 2) (by positivity) N
    simpa [Real.norm_eq_abs, sq_abs] using hb
  refine (hbase.const_mul (Real.exp (l ^ 2 / (2 * Real.pi) - m))).mono' ?_ ?_
  · exact (((continuous_const.add continuous_norm).pow N).mul
      (Real.continuous_exp.comp hfc.neg)).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_of_nonneg (by positivity)]
    have hle : Real.exp (-(f x)) ≤ Real.exp (l ^ 2 / (2 * Real.pi) - m)
        * Real.exp (-(Real.pi / 2) * x ^ 2) := by
      have h1 : Real.exp (-(f x)) ≤ Real.exp (-(Real.pi * x ^ 2 + l * x + m)) :=
        Real.exp_le_exp.mpr (by linarith [h x])
      have h2 : Real.exp (-(Real.pi * x ^ 2 + l * x + m))
          = Real.exp (-(Real.pi / 2) * x ^ 2) * Real.exp (-((Real.pi / 2) * x ^ 2 + l * x + m)) := by
        rw [← Real.exp_add]; congr 1; ring
      have h3 : -((Real.pi / 2) * x ^ 2 + l * x + m) ≤ l ^ 2 / (2 * Real.pi) - m := by
        have h4 : 0 ≤ (Real.pi / 2) * (x + l / Real.pi) ^ 2 := by positivity
        have h5 : (Real.pi / 2) * (x + l / Real.pi) ^ 2
            = (Real.pi / 2) * x ^ 2 + l * x + l ^ 2 / (2 * Real.pi) := by
          field_simp
          ring
        linarith [h4, h5]
      calc Real.exp (-(f x)) ≤ Real.exp (-(Real.pi * x ^ 2 + l * x + m)) := h1
        _ = Real.exp (-(Real.pi / 2) * x ^ 2) * Real.exp (-((Real.pi / 2) * x ^ 2 + l * x + m)) := h2
        _ ≤ Real.exp (-(Real.pi / 2) * x ^ 2) * Real.exp (l ^ 2 / (2 * Real.pi) - m) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h3) (Real.exp_pos _).le
        _ = Real.exp (l ^ 2 / (2 * Real.pi) - m) * Real.exp (-(Real.pi / 2) * x ^ 2) := by ring
    calc (1 + ‖x‖) ^ N * Real.exp (-(f x))
        ≤ (1 + ‖x‖) ^ N * (Real.exp (l ^ 2 / (2 * Real.pi) - m)
            * Real.exp (-(Real.pi / 2) * x ^ 2)) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = Real.exp (l ^ 2 / (2 * Real.pi) - m)
            * ((1 + ‖x‖) ^ N * Real.exp (-(Real.pi / 2) * x ^ 2)) := by ring

/-- Brascamp–Lieb on `ℝ`, from the sharp one-dimensional inequality. -/
theorem bl_real : BLon ℝ := by
  intro f h hf hH hconv hgf hh hgh
  have hd0 : DifferentiableAt ℝ f 0 := hf.contDiffAt.differentiableAt (by norm_num)
  have hd0' : DifferentiableAt ℝ (fun x : ℝ => Real.pi * ‖x‖ ^ 2) 0 := by
    have he : (fun x : ℝ => Real.pi * ‖x‖ ^ 2) = fun x : ℝ => Real.pi * x ^ 2 := by
      funext x; rw [Real.norm_eq_abs, sq_abs]
    rw [he]; fun_prop
  have hgd : DifferentiableAt ℝ (fun y : ℝ => f y - Real.pi * ‖y‖ ^ 2) 0 := hd0.sub hd0'
  have hgtan : ∀ x : ℝ, (fun y : ℝ => f y - Real.pi * ‖y‖ ^ 2) 0
      + deriv (fun y : ℝ => f y - Real.pi * ‖y‖ ^ 2) 0 * x
      ≤ (fun y : ℝ => f y - Real.pi * ‖y‖ ^ 2) x :=
    fun x => tangent_le_of_convexOn _ hconv hgd x
  have hflb : ∀ x : ℝ, Real.pi * x ^ 2
      + (fun y : ℝ => f y - Real.pi * ‖y‖ ^ 2) 0
      + deriv (fun y : ℝ => f y - Real.pi * ‖y‖ ^ 2) 0 * x ≤ f x := by
    intro x
    have h1 := hgtan x
    simp only [Real.norm_eq_abs, sq_abs] at h1 ⊢
    linarith
  have hfcont : Continuous f := hf.continuous
  have hftop : Tendsto f atTop atTop :=
    tendsto_atTop_mono' atTop (Eventually.of_forall hflb)
      (tendsto_pi_sq_add_linear ((fun y : ℝ => f y - Real.pi * ‖y‖ ^ 2) 0)
        (deriv (fun y : ℝ => f y - Real.pi * ‖y‖ ^ 2) 0))
  have hfbot : Tendsto f atBot atTop :=
    tendsto_atTop_mono' atBot (Eventually.of_forall hflb)
      (tendsto_pi_sq_add_linear_bot ((fun y : ℝ => f y - Real.pi * ‖y‖ ^ 2) 0)
        (deriv (fun y : ℝ => f y - Real.pi * ‖y‖ ^ 2) 0))
  have hfconv : ConvexOn ℝ Set.univ f := by
    have h1 := hconv.add convexOn_pi_norm_sq_real
    have h2 : ((fun x : ℝ => f x - Real.pi * ‖x‖ ^ 2) + fun x : ℝ => Real.pi * ‖x‖ ^ 2) = f := by
      funext x; simp
    rwa [h2] at h1
  have hV2b : ∀ x : ℝ, 2 * Real.pi ≤ deriv (deriv f) x := by
    intro x
    have h2 := hH x 1
    rw [Real.norm_eq_abs, abs_one, one_pow, mul_one] at h2
    rwa [show fderiv ℝ (fderiv ℝ f) x 1 1 = deriv (deriv f) x from by
      rw [fderiv_fderiv_real f hf x 1 1]; ring] at h2
  have hV2 : ∀ x : ℝ, 0 < deriv (deriv f) x :=
    fun x => lt_of_lt_of_le (by positivity) (hV2b x)
  have hflb' : ∀ x : ℝ, Real.pi * x ^ 2
      + deriv (fun y : ℝ => f y - Real.pi * ‖y‖ ^ 2) 0 * x
      + (fun y : ℝ => f y - Real.pi * ‖y‖ ^ 2) 0 ≤ f x :=
    fun x => by linarith [hflb x]
  obtain ⟨Ch, hCh0, Nh, hCh⟩ := hgh
  have hcoer := integrable_poly_mul_exp_neg_of_coercive f
    (deriv (fun y : ℝ => f y - Real.pi * ‖y‖ ^ 2) 0)
    ((fun y : ℝ => f y - Real.pi * ‖y‖ ^ 2) 0) hfcont hflb'
  have hderiv_cont : Continuous (deriv (deriv f)) := (hf.deriv' (n := 1)).continuous_deriv_one
  -- integrability of the four functions appearing in the sharp one-dimensional inequality
  have hint1 : Integrable (fun x : ℝ => h x * Real.exp (-(f x))) := by
    refine Integrable.mono' ((hcoer Nh).const_mul Ch) ?_ ?_
    · exact (hh.continuous.mul (Real.continuous_exp.comp hfcont.neg)).aestronglyMeasurable
    · filter_upwards with x
      have h1 : |h x| ≤ Ch * (1 + ‖x‖) ^ Nh := (hCh x 1).1
      calc ‖h x * Real.exp (-(f x))‖
          = |h x| * Real.exp (-(f x)) := by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
        _ ≤ (Ch * (1 + ‖x‖) ^ Nh) * Real.exp (-(f x)) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = Ch * ((1 + ‖x‖) ^ Nh * Real.exp (-(f x))) := by ring
  have hint2 : Integrable (fun x : ℝ => h x ^ 2 * Real.exp (-(f x))) := by
    refine Integrable.mono' ((hcoer (2 * Nh)).const_mul (Ch ^ 2)) ?_ ?_
    · exact ((hh.continuous.pow 2).mul (Real.continuous_exp.comp hfcont.neg)).aestronglyMeasurable
    · filter_upwards with x
      have h1 : |h x| ≤ Ch * (1 + ‖x‖) ^ Nh := (hCh x 1).1
      have h1' : h x ^ 2 ≤ (Ch * (1 + ‖x‖) ^ Nh) ^ 2 := by
        rw [← sq_abs (h x)]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      calc ‖h x ^ 2 * Real.exp (-(f x))‖
          = h x ^ 2 * Real.exp (-(f x)) := by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _),
              abs_of_nonneg (Real.exp_pos _).le]
        _ ≤ (Ch * (1 + ‖x‖) ^ Nh) ^ 2 * Real.exp (-(f x)) :=
            mul_le_mul_of_nonneg_right h1' (Real.exp_pos _).le
        _ = Ch ^ 2 * ((1 + ‖x‖) ^ (2 * Nh) * Real.exp (-(f x))) := by
            rw [mul_pow]
            have h3 : ((1 + ‖x‖) ^ Nh) ^ 2 = (1 + ‖x‖) ^ (2 * Nh) := by
              rw [← pow_mul (1 + ‖x‖) Nh 2, Nat.mul_comm Nh 2]
            rw [h3]; ring
  have hintU : Integrable (fun x : ℝ => h x ^ 2 / deriv (deriv f) x * Real.exp (-(f x))) := by
    refine Integrable.mono'
      ((hcoer (2 * Nh)).const_mul (Ch ^ 2 / (2 * Real.pi))) ?_ ?_
    · exact (((hh.continuous.pow 2).div hderiv_cont (fun x => ne_of_gt (hV2 x))).mul
        (Real.continuous_exp.comp hfcont.neg)).aestronglyMeasurable
    · filter_upwards with x
      have h1 : |h x| ≤ Ch * (1 + ‖x‖) ^ Nh := (hCh x 1).1
      have h1' : h x ^ 2 ≤ (Ch * (1 + ‖x‖) ^ Nh) ^ 2 := by
        rw [← sq_abs (h x)]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      have hle : h x ^ 2 / deriv (deriv f) x ≤ (Ch * (1 + ‖x‖) ^ Nh) ^ 2 / (2 * Real.pi) := by
        rw [div_le_div_iff₀ (hV2 x) (by positivity)]
        have hxm : (0:ℝ) ≤ (Ch * (1 + ‖x‖) ^ Nh) ^ 2 := sq_nonneg _
        have hs1 : h x ^ 2 * (2 * Real.pi)
            ≤ (Ch * (1 + ‖x‖) ^ Nh) ^ 2 * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_right h1' (by positivity)
        have hs2 : (Ch * (1 + ‖x‖) ^ Nh) ^ 2 * (2 * Real.pi)
            ≤ (Ch * (1 + ‖x‖) ^ Nh) ^ 2 * deriv (deriv f) x :=
          mul_le_mul_of_nonneg_left (hV2b x) hxm
        linarith [hs1, hs2]
      calc ‖h x ^ 2 / deriv (deriv f) x * Real.exp (-(f x))‖
          = h x ^ 2 / deriv (deriv f) x * Real.exp (-(f x)) := by
            rw [Real.norm_eq_abs, abs_mul,
              abs_of_nonneg (div_nonneg (sq_nonneg _) (hV2 x).le),
              abs_of_nonneg (Real.exp_pos _).le]
        _ ≤ ((Ch * (1 + ‖x‖) ^ Nh) ^ 2 / (2 * Real.pi)) * Real.exp (-(f x)) :=
            mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
        _ = (Ch ^ 2 / (2 * Real.pi)) * ((1 + ‖x‖) ^ (2 * Nh) * Real.exp (-(f x))) := by
            rw [mul_pow]
            have h3 : ((1 + ‖x‖) ^ Nh) ^ 2 = (1 + ‖x‖) ^ (2 * Nh) := by
              rw [← pow_mul (1 + ‖x‖) Nh 2, Nat.mul_comm Nh 2]
            rw [h3]; ring
  have hintd : Integrable (fun x : ℝ => (deriv h x) ^ 2 * Real.exp (-(f x))) := by
    refine Integrable.mono' ((hcoer (2 * Nh)).const_mul (Ch ^ 2)) ?_ ?_
    · exact ((hh.continuous_deriv_one.pow 2).mul
        (Real.continuous_exp.comp hfcont.neg)).aestronglyMeasurable
    · filter_upwards with x
      have h1 : |deriv h x| ≤ Ch * (1 + ‖x‖) ^ Nh := by
        have h2 := (hCh x 1).2
        simpa using h2
      have h1' : (deriv h x) ^ 2 ≤ (Ch * (1 + ‖x‖) ^ Nh) ^ 2 := by
        rw [← sq_abs (deriv h x)]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      calc ‖(deriv h x) ^ 2 * Real.exp (-(f x))‖
          = (deriv h x) ^ 2 * Real.exp (-(f x)) := by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _),
              abs_of_nonneg (Real.exp_pos _).le]
        _ ≤ (Ch * (1 + ‖x‖) ^ Nh) ^ 2 * Real.exp (-(f x)) :=
            mul_le_mul_of_nonneg_right h1' (Real.exp_pos _).le
        _ = Ch ^ 2 * ((1 + ‖x‖) ^ (2 * Nh) * Real.exp (-(f x))) := by
            rw [mul_pow]
            have h3 : ((1 + ‖x‖) ^ Nh) ^ 2 = (1 + ‖x‖) ^ (2 * Nh) := by
              rw [← pow_mul (1 + ‖x‖) Nh 2, Nat.mul_comm Nh 2]
            rw [h3]; ring
  have hintD : Integrable (fun x : ℝ => (deriv h x) ^ 2 / deriv (deriv f) x * Real.exp (-(f x))) := by
    refine Integrable.mono' ((hcoer (2 * Nh)).const_mul (Ch ^ 2 / (2 * Real.pi))) ?_ ?_
    · exact (((hh.continuous_deriv_one.pow 2).div hderiv_cont
        (fun x => ne_of_gt (hV2 x))).mul (Real.continuous_exp.comp hfcont.neg)).aestronglyMeasurable
    · filter_upwards with x
      have h1 : |deriv h x| ≤ Ch * (1 + ‖x‖) ^ Nh := by
        have h2 := (hCh x 1).2
        simpa using h2
      have h1' : (deriv h x) ^ 2 ≤ (Ch * (1 + ‖x‖) ^ Nh) ^ 2 := by
        rw [← sq_abs (deriv h x)]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      have hle : (deriv h x) ^ 2 / deriv (deriv f) x
          ≤ (Ch * (1 + ‖x‖) ^ Nh) ^ 2 / (2 * Real.pi) := by
        rw [div_le_div_iff₀ (hV2 x) (by positivity)]
        have hxm : (0:ℝ) ≤ (Ch * (1 + ‖x‖) ^ Nh) ^ 2 := sq_nonneg _
        have hs1 : (deriv h x) ^ 2 * (2 * Real.pi)
            ≤ (Ch * (1 + ‖x‖) ^ Nh) ^ 2 * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_right h1' (by positivity)
        have hs2 : (Ch * (1 + ‖x‖) ^ Nh) ^ 2 * (2 * Real.pi)
            ≤ (Ch * (1 + ‖x‖) ^ Nh) ^ 2 * deriv (deriv f) x :=
          mul_le_mul_of_nonneg_left (hV2b x) hxm
        linarith [hs1, hs2]
      calc ‖(deriv h x) ^ 2 / deriv (deriv f) x * Real.exp (-(f x))‖
          = (deriv h x) ^ 2 / deriv (deriv f) x * Real.exp (-(f x)) := by
            rw [Real.norm_eq_abs, abs_mul,
              abs_of_nonneg (div_nonneg (sq_nonneg _) (hV2 x).le),
              abs_of_nonneg (Real.exp_pos _).le]
        _ ≤ ((Ch * (1 + ‖x‖) ^ Nh) ^ 2 / (2 * Real.pi)) * Real.exp (-(f x)) :=
            mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
        _ = (Ch ^ 2 / (2 * Real.pi)) * ((1 + ‖x‖) ^ (2 * Nh) * Real.exp (-(f x))) := by
            rw [mul_pow]
            have h3 : ((1 + ‖x‖) ^ Nh) ^ 2 = (1 + ‖x‖) ^ (2 * Nh) := by
              rw [← pow_mul (1 + ‖x‖) Nh 2, Nat.mul_comm Nh 2]
            rw [h3]; ring
  have hsharp := Commons.Analysis.Convex.brascamp_lieb_one_dim_sharp f h hf hfconv hV2 hftop hfbot
    hh hint1 hint2 hintU hintD
  have henergy : ∀ x : ℝ, ⟪hessInv f x (grad h x), grad h x⟫_ℝ
      = (deriv h x) ^ 2 / deriv (deriv f) x := by
    intro x
    rw [hessInv_real f hf hH x (grad h x) (hV2 x), grad_real h x]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, div_eq_mul_inv]
    ring
  have hcongr : (∫ x, ⟪hessInv f x (grad h x), grad h x⟫_ℝ * Real.exp (-(f x)))
      = ∫ x, (deriv h x) ^ 2 / deriv (deriv f) x * Real.exp (-(f x)) := by
    refine integral_congr_ae (Eventually.of_forall (fun x => ?_))
    simp only [henergy x]
  rw [hcongr]
  exact hsharp

/-- Brascamp–Lieb on `EuclideanSpace ℝ (Fin 1)`, read off from `bl_real`. -/
theorem bl_one_dim : BLon (EuclideanSpace ℝ (Fin 1)) := by
  obtain ⟨e⟩ := Commons.Analysis.InnerProductSpace.isometry_equiv_real_of_finrank_one
    (E := EuclideanSpace ℝ (Fin 1)) (by simp)
  exact bl_transport e bl_real

/-- **Brascamp–Lieb by induction on the dimension.** -/
theorem blon_euclid : ∀ n : ℕ, BLon (EuclideanSpace ℝ (Fin n))
  | 0 => bl_zero
  | 1 => bl_one_dim
  | n + 2 => by
      obtain ⟨e⟩ := Commons.Analysis.InnerProductSpace.euclidean_split_isometry (n + 1)
      exact bl_transport e (bl_product_step (IH := blon_euclid (n + 1)))

/-- **Brascamp–Lieb on any finite-dimensional real inner product space.**  Obtained from
`blon_euclid` by transporting along an orthonormal-basis representation. -/
theorem blon_holds (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] : BLon E :=
  bl_transport (stdOrthonormalBasis ℝ E).repr (blon_euclid (Module.finrank ℝ E))

/-! ### Brascamp–Lieb for a smooth strongly convex potential

This is the induction target of Stage 1 described at the top of the file. -/
theorem brascamp_lieb_smooth (f h : E → ℝ)
    (hf : ContDiff ℝ 2 f)
    (hH : ∀ x v : E, 2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v)
    (hconv : ConvexOn ℝ Set.univ (fun x => f x - Real.pi * ‖x‖ ^ 2))
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E,
      |fderiv ℝ f x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ f) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2)
    (hh : ContDiff ℝ 1 h)
    (hgh : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E,
      |h x| ≤ C * (1 + ‖x‖) ^ N ∧
      |fderiv ℝ h x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖) :
    (∫ x, h x ^ 2 * Real.exp (-(f x)))
        - (∫ x, h x * Real.exp (-(f x))) ^ 2 / (∫ x, Real.exp (-(f x)))
      ≤ ∫ x, ⟪hessInv f x (grad h x), grad h x⟫_ℝ * Real.exp (-(f x)) :=
  blon_holds E f h hf hH hconv hgf hh hgh


/-- **Brascamp–Lieb (full Poincaré) inequality for the Gaussian truncated to a convex set.**
For `A` convex and any mean-zero `C¹` function `w`, the variance with respect to the (unnormalized)
measure `1_A(x)·exp(-π‖x‖²)dx` is bounded by `1/(2π)` times the Dirichlet energy.
This is the `n`-dimensional Brascamp–Lieb inequality for the log-concave measure `1_A exp(-π‖x‖²)dx`,
whose potential `π‖x‖²` has Hessian `2π·I`. -/
theorem growth_fderiv_penalized (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (A : Set (EuclideanSpace ℝ (Fin n))) (hAm : MeasurableSet A) (hA : Convex ℝ A)
    (hApos : 0 < volume A)
    (hpos : ∀ x : EuclideanSpace ℝ (Fin n), 0 < ∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : EuclideanSpace ℝ (Fin n),
      |fderiv ℝ (fun x => Real.pi * ‖x‖ ^ 2
          + -Real.log (∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2))) x v|
        ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ (fun x => Real.pi * ‖x‖ ^ 2
          + -Real.log (∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2)))) x v v|
        ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2 := by
  obtain ⟨C1, hC10, N1, hC1⟩ := Commons.Analysis.Asymptotics.growth_fderiv_logLaplace n hε A hAm hA hApos hpos
  obtain ⟨C2, hC20, N2, hC2⟩ := Commons.Analysis.Asymptotics.growth_fderiv2_logLaplace n hε A hAm hA hApos hpos
  set φ : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => -Real.log (∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2)) with hφdef
  set q : EuclideanSpace ℝ (Fin n) → ℝ := fun x => Real.pi * ‖x‖ ^ 2 with hqdef
  have hφcd : ContDiff ℝ 2 φ := by
    rw [hφdef]
    exact (Commons.Analysis.Convex.contDiff_logLaplace_penalty n hε A hAm hpos).of_le (by norm_num)
  have hqcd : ContDiff ℝ 2 q := by
    rw [hqdef]
    exact contDiff_const.mul (contDiff_norm_sq ℝ (E := EuclideanSpace ℝ (Fin n)))
  have hfeq : (fun x : EuclideanSpace ℝ (Fin n) => Real.pi * ‖x‖ ^ 2
        + -Real.log (∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2))) = fun x => q x + φ x := by
    funext x; rw [hqdef, hφdef]
  have hq1 : ∀ x v, fderiv ℝ q x v = 2 * Real.pi * inner ℝ x v := by
    intro x v
    have h := Commons.Analysis.Calculus.FDeriv.fderiv_mul_norm_sq_sub
      (E := EuclideanSpace ℝ (Fin n)) Real.pi (0 : EuclideanSpace ℝ (Fin n)) x
    have h' : fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) => Real.pi * ‖z‖ ^ 2) x
        = (2 * Real.pi) • innerSL ℝ x := by simpa using h
    rw [hqdef, h']
    simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
    try ring
  have hq2 : ∀ x v w, fderiv ℝ (fderiv ℝ q) x v w = 2 * Real.pi * inner ℝ v w := by
    intro x v w
    have h := Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_mul_norm_sq_sub
      (E := EuclideanSpace ℝ (Fin n)) Real.pi (0 : EuclideanSpace ℝ (Fin n)) x
    have h' : fderiv ℝ (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) => Real.pi * ‖z‖ ^ 2)) x
        = (2 * Real.pi) • innerSL ℝ := by simpa using h
    rw [hqdef, h']
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [innerSL_apply_apply]
    try ring
  refine ⟨2 * Real.pi + C1 + C2, by positivity, max 1 (max N1 N2), fun x v => ?_⟩
  rw [hfeq]
  have hbase : (1:ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have e1 : (1 + ‖x‖) ^ 1 ≤ (1 + ‖x‖) ^ max 1 (max N1 N2) :=
    pow_le_pow_right₀ hbase (le_max_left _ _)
  have eN1 : (1 + ‖x‖) ^ N1 ≤ (1 + ‖x‖) ^ max 1 (max N1 N2) :=
    pow_le_pow_right₀ hbase (le_trans (le_max_left _ _) (le_max_right _ _))
  have eN2 : (1 + ‖x‖) ^ N2 ≤ (1 + ‖x‖) ^ max 1 (max N1 N2) :=
    pow_le_pow_right₀ hbase (le_trans (le_max_right _ _) (le_max_right _ _))
  have hb1 : |fderiv ℝ (fun x => q x + φ x) x v|
      ≤ (2 * Real.pi + C1 + C2) * (1 + ‖x‖) ^ max 1 (max N1 N2) * ‖v‖ := by
    rw [fderiv_fun_add (hqcd.differentiable (by norm_num) x)
      (hφcd.differentiable (by norm_num) x), ContinuousLinearMap.add_apply]
    calc |fderiv ℝ q x v + fderiv ℝ φ x v| ≤ |fderiv ℝ q x v| + |fderiv ℝ φ x v| := abs_add_le _ _
      _ ≤ 2 * Real.pi * (1 + ‖x‖) ^ max 1 (max N1 N2) * ‖v‖
            + C1 * (1 + ‖x‖) ^ max 1 (max N1 N2) * ‖v‖ := by
          refine add_le_add ?_ ?_
          · rw [hq1]
            have hab : |inner ℝ x v| ≤ ‖x‖ * ‖v‖ := abs_real_inner_le_norm x v
            rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
            calc 2 * Real.pi * |inner ℝ x v| ≤ 2 * Real.pi * (‖x‖ * ‖v‖) :=
                  mul_le_mul_of_nonneg_left hab (by positivity)
              _ ≤ 2 * Real.pi * ((1 + ‖x‖) ^ max 1 (max N1 N2) * ‖v‖) := by
                  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg v)
                  calc ‖x‖ ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
                    _ = (1 + ‖x‖) ^ 1 := (pow_one _).symm
                    _ ≤ _ := e1
              _ = 2 * Real.pi * (1 + ‖x‖) ^ max 1 (max N1 N2) * ‖v‖ := by ring
          · calc |fderiv ℝ φ x v| ≤ C1 * (1 + ‖x‖) ^ N1 * ‖v‖ := hC1 x v
              _ ≤ C1 * (1 + ‖x‖) ^ max 1 (max N1 N2) * ‖v‖ := by
                  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg v)
                  exact mul_le_mul_of_nonneg_left eN1 hC10
      _ = (2 * Real.pi + C1) * (1 + ‖x‖) ^ max 1 (max N1 N2) * ‖v‖ := by ring
      _ ≤ (2 * Real.pi + C1 + C2) * (1 + ‖x‖) ^ max 1 (max N1 N2) * ‖v‖ := by
          have hnn : (0:ℝ) ≤ (1 + ‖x‖) ^ max 1 (max N1 N2) * ‖v‖ := by positivity
          nlinarith [hnn, hC20]
  have hb2 : |fderiv ℝ (fderiv ℝ (fun x => q x + φ x)) x v v|
      ≤ (2 * Real.pi + C1 + C2) * (1 + ‖x‖) ^ max 1 (max N1 N2) * ‖v‖ ^ 2 := by
    rw [Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_add_of_contDiffAt
      (φ := q) (q := φ) hqcd.contDiffAt hφcd.contDiffAt, ContinuousLinearMap.add_apply]
    calc |fderiv ℝ (fderiv ℝ q) x v v + fderiv ℝ (fderiv ℝ φ) x v v|
        ≤ |fderiv ℝ (fderiv ℝ q) x v v| + |fderiv ℝ (fderiv ℝ φ) x v v| := abs_add_le _ _
      _ ≤ 2 * Real.pi * (1 + ‖x‖) ^ max 1 (max N1 N2) * ‖v‖ ^ 2
            + C2 * (1 + ‖x‖) ^ max 1 (max N1 N2) * ‖v‖ ^ 2 := by
          refine add_le_add ?_ ?_
          · rw [hq2]
            have hab : |inner ℝ v v| ≤ ‖v‖ * ‖v‖ := abs_real_inner_le_norm v v
            rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
            have hvv : |inner ℝ v v| ≤ ‖v‖ ^ 2 := by
              simpa [sq] using hab
            calc 2 * Real.pi * |inner ℝ v v| ≤ 2 * Real.pi * ‖v‖ ^ 2 :=
                  mul_le_mul_of_nonneg_left hvv (by positivity)
              _ ≤ 2 * Real.pi * ((1 + ‖x‖) ^ max 1 (max N1 N2) * ‖v‖ ^ 2) := by
                  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                  exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ hbase)
              _ = 2 * Real.pi * (1 + ‖x‖) ^ max 1 (max N1 N2) * ‖v‖ ^ 2 := by ring
          · calc |fderiv ℝ (fderiv ℝ φ) x v v| ≤ C2 * (1 + ‖x‖) ^ N2 * ‖v‖ ^ 2 := hC2 x v
              _ ≤ C2 * (1 + ‖x‖) ^ max 1 (max N1 N2) * ‖v‖ ^ 2 := by
                  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                  exact mul_le_mul_of_nonneg_left eN2 hC20
      _ = (2 * Real.pi + C2) * (1 + ‖x‖) ^ max 1 (max N1 N2) * ‖v‖ ^ 2 := by ring
      _ ≤ (2 * Real.pi + C1 + C2) * (1 + ‖x‖) ^ max 1 (max N1 N2) * ‖v‖ ^ 2 := by
          have hnn : (0:ℝ) ≤ (1 + ‖x‖) ^ max 1 (max N1 N2) * ‖v‖ ^ 2 := by positivity
          nlinarith [hnn, hC10]
  exact ⟨hb1, hb2⟩


/-- Translation invariance of the (unnormalised) Gaussian kernel. -/
lemma integral_gaussian_translate_eq (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (x : EuclideanSpace ℝ (Fin n)) :
    (∫ y : EuclideanSpace ℝ (Fin n), Real.exp (-‖x - y‖ ^ 2 / ε ^ 2))
      = ∫ y : EuclideanSpace ℝ (Fin n), Real.exp (-‖y‖ ^ 2 / ε ^ 2) := by
  rw [show (fun y : EuclideanSpace ℝ (Fin n) => Real.exp (-‖x - y‖ ^ 2 / ε ^ 2))
      = (fun y => Real.exp (-‖y - x‖ ^ 2 / ε ^ 2)) from by
    funext y; rw [norm_sub_rev x y]]
  exact integral_add_right_eq_self
    (fun u : EuclideanSpace ℝ (Fin n) => Real.exp (-‖u‖ ^ 2 / ε ^ 2)) (-x)

/-- Positivity of the Gaussian normalisation `∫ y, exp (-‖y‖²/ε²)`. -/
lemma integral_gaussian_pos (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    0 < ∫ y : EuclideanSpace ℝ (Fin n), Real.exp (-‖y‖ ^ 2 / ε ^ 2) := by
  have hint0 : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-‖y‖ ^ 2 / ε ^ 2)) := by
    simpa using Commons.Analysis.Convex.integrable_gaussian_translate hε
      (0 : EuclideanSpace ℝ (Fin n))
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun y => (Real.exp_pos _).le) hint0]
  have hsupp : Function.support (fun y : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-‖y‖ ^ 2 / ε ^ 2)) = Set.univ := by
    ext y; simp [Function.mem_support, Real.exp_ne_zero]
  rw [hsupp]
  exact volume_univ_pos (EuclideanSpace ℝ (Fin n))

/-- **Nonnegativity of the (normalised) log-Laplace penalty.**

For every `x`, `φ_ε x = -Real.log ((∫ y in A, exp (-‖x-y‖²/ε²)) / (∫ y, exp (-‖y‖²/ε²))) ≥ 0`:
the numerator is the integral of a nonnegative function over a subset, and the denominator is the
same integral over all of `ℝ^n` (translation invariance of Lebesgue measure). -/
theorem logLaplace_penalty_nonneg (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (A : Set (EuclideanSpace ℝ (Fin n))) (hAm : MeasurableSet A)
    (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ -Real.log ((∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2))
      / (∫ y : EuclideanSpace ℝ (Fin n), Real.exp (-‖y‖ ^ 2 / ε ^ 2))) := by
  have hint : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-‖x - y‖ ^ 2 / ε ^ 2)) :=
    Commons.Analysis.Convex.integrable_gaussian_translate hε x
  have hCpos := integral_gaussian_pos n hε
  have hle : (∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2))
      ≤ ∫ y : EuclideanSpace ℝ (Fin n), Real.exp (-‖y‖ ^ 2 / ε ^ 2) := by
    rw [← integral_gaussian_translate_eq n hε x]
    exact setIntegral_le_integral hint (Filter.Eventually.of_forall fun y => Real.exp_nonneg _)
  have hnonneg : (0:ℝ) ≤ ∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2) :=
    integral_nonneg fun y => Real.exp_nonneg _
  have hratio : (∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2))
      / (∫ y : EuclideanSpace ℝ (Fin n), Real.exp (-‖y‖ ^ 2 / ε ^ 2)) ≤ 1 := (div_le_one hCpos).mpr hle
  have := Real.log_nonpos (by positivity) hratio
  linarith


/-- **First half of the interior limit.** For `x` in the interior of `A`, the indicator
`z ↦ 1_A (x + ε z)` tends to `1` as `ε → 0⁺`. -/
lemma indicator_tendsto_of_mem_interior {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin n))}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ interior A)
    (z : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun ε : ℝ => A.indicator (fun _ => (1:ℝ)) (x + ε • z)) (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have hcont : Tendsto (fun ε : ℝ => x + ε • z) (𝓝 (0:ℝ)) (𝓝 x) := by
    have h1 : Tendsto (fun ε : ℝ => ε • z) (𝓝 (0:ℝ)) (𝓝 ((0:ℝ) • z)) :=
      tendsto_id.smul tendsto_const_nhds
    simpa using tendsto_const_nhds.add h1
  have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ), x + ε • z ∈ A :=
    ((hcont.eventually (IsOpen.mem_nhds isOpen_interior hx)).filter_mono nhdsWithin_le_nhds).mono
      fun ε hε => interior_subset hε
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [hev] with ε hε
  rw [Set.indicator_of_mem hε]

/-- **First half of the interior limit, integrated.** For `x` in the interior of a measurable `A`,
`∫ z, 1_A (x + ε z) * exp (-‖z‖²) → ∫ z, exp (-‖z‖²)` as `ε → 0⁺` (dominated convergence with
dominating function `exp (-‖z‖²)`). -/
lemma tendsto_integral_indicator_gaussian {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin n))}
    (hAm : MeasurableSet A) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ interior A) :
    Tendsto (fun ε : ℝ => ∫ z : EuclideanSpace ℝ (Fin n),
        A.indicator (fun _ => (1:ℝ)) (x + ε • z) * Real.exp (-‖z‖ ^ 2))
      (𝓝[>] (0:ℝ)) (𝓝 (∫ z : EuclideanSpace ℝ (Fin n), Real.exp (-‖z‖ ^ 2))) := by
  have hbound : Integrable (fun z : EuclideanSpace ℝ (Fin n) => Real.exp (-‖z‖ ^ 2)) := by
    simpa using Commons.Measure.Integral.integrable_rexp_neg_mul_sq_norm
      (V := EuclideanSpace ℝ (Fin n)) 1 (by norm_num)
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun z : EuclideanSpace ℝ (Fin n) => Real.exp (-‖z‖ ^ 2)) ?_ ?_ hbound ?_
  · filter_upwards with ε
    exact (((measurable_const.indicator hAm).comp
      (by fun_prop : Measurable (fun z : EuclideanSpace ℝ (Fin n) => x + ε • z))).mul
        (by fun_prop : Measurable (fun z : EuclideanSpace ℝ (Fin n) => Real.exp (-‖z‖ ^ 2)))
      ).aestronglyMeasurable
  · filter_upwards with ε
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    have h1 : |A.indicator (fun _ => (1:ℝ)) (x + ε • z)| ≤ 1 := by
      by_cases h : x + ε • z ∈ A
      · rw [Set.indicator_of_mem h]; norm_num
      · rw [Set.indicator_of_notMem h]; norm_num
    calc |A.indicator (fun _ => (1:ℝ)) (x + ε • z)| * Real.exp (-‖z‖ ^ 2)
        ≤ 1 * Real.exp (-‖z‖ ^ 2) := mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
      _ = Real.exp (-‖z‖ ^ 2) := one_mul _
  · filter_upwards with z
    simpa using (indicator_tendsto_of_mem_interior hx z).mul_const (Real.exp (-‖z‖ ^ 2))


/-- The Laplace transform of the indicator of `A` against the Gaussian kernel of width `ε`. -/
noncomputable def penLaplace (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2)

/-- The normalising constant `∫ y, exp (-‖y‖²/ε²)`. -/
noncomputable def gaussNorm (n : ℕ) (ε : ℝ) : ℝ :=
  ∫ y : EuclideanSpace ℝ (Fin n), Real.exp (-‖y‖ ^ 2 / ε ^ 2)

/-- The normalised Laplace ratio. -/
noncomputable def penRatio (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ := penLaplace n A ε x / gaussNorm n ε

/-- The un-normalised log-Laplace penalty. -/
noncomputable def penG (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ := -Real.log (penLaplace n A ε x)

/-- The (normalised) log-Laplace penalty. -/
noncomputable def penPot (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ := -Real.log (penRatio n A ε x)

/-- The penalised potential `π‖x‖² + φ_ε x`. -/
noncomputable def penF (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ := Real.pi * ‖x‖ ^ 2 + penPot n A ε x

/-- The un-normalised penalised potential `π‖x‖² - log (∫_{y∈A} exp (-‖x-y‖²/ε²))`. -/
noncomputable def penH (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ := Real.pi * ‖x‖ ^ 2 - Real.log (penLaplace n A ε x)

/-- The Gaussian quadratic form `π‖x‖²`. -/
noncomputable def quad (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ := Real.pi * ‖x‖ ^ 2

/-- The `π`-Gaussian density `exp (-π‖x‖²)`. -/
noncomputable def gDens (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (-(Real.pi * ‖x‖ ^ 2))

lemma gDens_nonneg (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ gDens n x := by
  rw [gDens]; positivity

lemma gDens_eq (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    gDens n x = Real.exp (-Real.pi * ‖x‖ ^ 2) := by
  rw [gDens]
  congr 1
  ring

lemma penRatio_apply (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    penRatio n A ε x = (∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2))
      / (∫ y : EuclideanSpace ℝ (Fin n), Real.exp (-‖y‖ ^ 2 / ε ^ 2)) := rfl

lemma gaussNorm_pos (n : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < gaussNorm n ε := by
  rw [gaussNorm]; exact integral_gaussian_pos n hε

/-- `∫_{y∈A} exp (-‖x-y‖²/ε²) > 0` when `A` has positive measure. -/
lemma penLaplace_pos (n : ℕ) {ε : ℝ} (hε : 0 < ε) (A : Set (EuclideanSpace ℝ (Fin n)))
    (hAm : MeasurableSet A) (hvol : 0 < volume A) (x : EuclideanSpace ℝ (Fin n)) :
    0 < penLaplace n A ε x := by
  rw [penLaplace, ← MeasureTheory.integral_indicator hAm]
  have hint : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      A.indicator (fun y => Real.exp (-‖x - y‖ ^ 2 / ε ^ 2)) y) :=
    (Commons.Analysis.Convex.integrable_gaussian_translate hε x).indicator hAm
  have hsupp : Function.support (fun y : EuclideanSpace ℝ (Fin n) =>
      A.indicator (fun y => Real.exp (-‖x - y‖ ^ 2 / ε ^ 2)) y) = A := by
    ext y
    rw [Function.mem_support]
    by_cases h : y ∈ A
    · rw [Set.indicator_of_mem h]
      exact ⟨fun _ => h, fun _ => Real.exp_ne_zero _⟩
    · rw [Set.indicator_of_notMem h]
      exact ⟨fun h0 => absurd rfl h0, fun h0 => absurd h0 h⟩
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun y =>
      Set.indicator_nonneg (fun a _ => (Real.exp_pos _).le) y) hint, hsupp]
  exact hvol

lemma penPot_nonneg (n : ℕ) {ε : ℝ} (hε : 0 < ε) (A : Set (EuclideanSpace ℝ (Fin n)))
    (hAm : MeasurableSet A) (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ penPot n A ε x := by
  rw [penPot, penRatio_apply]
  exact logLaplace_penalty_nonneg n hε A hAm x

/-- The normalised penalty differs from the un-normalised one by the constant
`log (∫ y, exp (-‖y‖²/ε²))`. -/
lemma penPot_eq (n : ℕ) {ε : ℝ} (hε : 0 < ε) (A : Set (EuclideanSpace ℝ (Fin n)))
    (hAm : MeasurableSet A) (hvol : 0 < volume A) (x : EuclideanSpace ℝ (Fin n)) :
    penPot n A ε x = penG n A ε x + Real.log (gaussNorm n ε) := by
  have h1 : penLaplace n A ε x ≠ 0 := ne_of_gt (penLaplace_pos n hε A hAm hvol x)
  have h2 : gaussNorm n ε ≠ 0 := ne_of_gt (gaussNorm_pos n hε)
  show -Real.log (penLaplace n A ε x / gaussNorm n ε)
      = -Real.log (penLaplace n A ε x) + Real.log (gaussNorm n ε)
  rw [Real.log_div h1 h2]
  ring

lemma contDiff_penG (n : ℕ) {ε : ℝ} (hε : 0 < ε) (A : Set (EuclideanSpace ℝ (Fin n)))
    (hAm : MeasurableSet A) (hvol : 0 < volume A) : ContDiff ℝ ⊤ (penG n A ε) := by
  have hpos : ∀ x : EuclideanSpace ℝ (Fin n), 0 < ∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2) :=
    fun x => penLaplace_pos n hε A hAm hvol x
  change ContDiff ℝ ⊤ (fun x : EuclideanSpace ℝ (Fin n) =>
    -Real.log (penLaplace n A ε x))
  simpa only [penLaplace] using
    Commons.Analysis.Convex.contDiff_logLaplace_penalty n hε A hAm hpos

lemma convexOn_penG (n : ℕ) {ε : ℝ} (hε : 0 < ε) (A : Set (EuclideanSpace ℝ (Fin n)))
    (hAm : MeasurableSet A) (hA : Convex ℝ A) :
    ConvexOn ℝ Set.univ (penG n A ε) := by
  change ConvexOn ℝ Set.univ (fun x : EuclideanSpace ℝ (Fin n) =>
    -Real.log (penLaplace n A ε x))
  simpa only [penLaplace] using
    Commons.Analysis.Convex.convexOn_logLaplace n hε A hAm hA

lemma contDiff_penPot (n : ℕ) {ε : ℝ} (hε : 0 < ε) (A : Set (EuclideanSpace ℝ (Fin n)))
    (hAm : MeasurableSet A) (hvol : 0 < volume A) : ContDiff ℝ ⊤ (penPot n A ε) := by
  have heq : penPot n A ε = penG n A ε + fun _ : EuclideanSpace ℝ (Fin n) =>
      Real.log (gaussNorm n ε) := by
    funext x; rw [penPot_eq n hε A hAm hvol x, Pi.add_apply]
  rw [heq]
  exact (contDiff_penG n hε A hAm hvol).add contDiff_const

lemma convexOn_penPot (n : ℕ) {ε : ℝ} (hε : 0 < ε) (A : Set (EuclideanSpace ℝ (Fin n)))
    (hAm : MeasurableSet A) (hA : Convex ℝ A) (hvol : 0 < volume A) :
    ConvexOn ℝ Set.univ (penPot n A ε) := by
  have heq : penPot n A ε = penG n A ε + fun _ : EuclideanSpace ℝ (Fin n) =>
      Real.log (gaussNorm n ε) := by
    funext x; rw [penPot_eq n hε A hAm hvol x, Pi.add_apply]
  rw [heq]
  exact (convexOn_penG n hε A hAm hA).add_const _


lemma penRatio_pos (n : ℕ) {ε : ℝ} (hε : 0 < ε) (A : Set (EuclideanSpace ℝ (Fin n)))
    (hAm : MeasurableSet A) (hvol : 0 < volume A) (x : EuclideanSpace ℝ (Fin n)) :
    0 < penRatio n A ε x :=
  div_pos (penLaplace_pos n hε A hAm hvol x) (gaussNorm_pos n hε)

lemma penRatio_le_one (n : ℕ) {ε : ℝ} (hε : 0 < ε) (A : Set (EuclideanSpace ℝ (Fin n)))
    (hAm : MeasurableSet A) (hvol : 0 < volume A) (x : EuclideanSpace ℝ (Fin n)) :
    penRatio n A ε x ≤ 1 := by
  have hr : 0 < penRatio n A ε x := penRatio_pos n hε A hAm hvol x
  have h := logLaplace_penalty_nonneg n hε A hAm x
  rw [show -Real.log ((∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2))
      / (∫ y : EuclideanSpace ℝ (Fin n), Real.exp (-‖y‖ ^ 2 / ε ^ 2))) = -Real.log (penRatio n A ε x)
      from by rw [penRatio_apply]] at h
  rw [← Real.exp_zero, ← Real.log_le_iff_le_exp hr]
  linarith

/-- `exp (-(penF ε x)) = exp (-π‖x‖²) · penRatio ε x`. -/
lemma exp_neg_penF (n : ℕ) {ε : ℝ} (hε : 0 < ε) (A : Set (EuclideanSpace ℝ (Fin n)))
    (hAm : MeasurableSet A) (hvol : 0 < volume A) (x : EuclideanSpace ℝ (Fin n)) :
    Real.exp (-(penF n A ε x)) = gDens n x * penRatio n A ε x := by
  have hr : 0 < penRatio n A ε x := penRatio_pos n hε A hAm hvol x
  have harg : -(penF n A ε x)
      = -(Real.pi * ‖x‖ ^ 2) + Real.log (penRatio n A ε x) := by
    rw [penF, penPot]
    ring
  rw [harg, Real.exp_add, Real.exp_log hr]
  rfl

/-- `0 < volume A` follows from `0 < ∫ x in A, exp (-π‖x‖²)`. -/
lemma volume_pos_of_integral_pos (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n)))
    (hAm : MeasurableSet A)
    (hpos : 0 < ∫ x in A, Real.exp (-Real.pi * ‖x‖ ^ 2)) : 0 < volume A := by
  rw [← MeasureTheory.integral_indicator hAm] at hpos
  have hint : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      A.indicator (fun x => Real.exp (-Real.pi * ‖x‖ ^ 2)) x) :=
    (Commons.Measure.Integral.integrable_rexp_neg_mul_sq_norm Real.pi Real.pi_pos).indicator hAm
  have hsupp : Function.support (fun x : EuclideanSpace ℝ (Fin n) =>
      A.indicator (fun x => Real.exp (-Real.pi * ‖x‖ ^ 2)) x) = A := by
    ext y
    rw [Function.mem_support]
    by_cases h : y ∈ A
    · rw [Set.indicator_of_mem h]
      exact ⟨fun _ => h, fun _ => Real.exp_ne_zero _⟩
    · rw [Set.indicator_of_notMem h]
      exact ⟨fun h0 => absurd rfl h0, fun h0 => absurd h0 h⟩
  rwa [MeasureTheory.integral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun y =>
      Set.indicator_nonneg (fun a _ => (Real.exp_pos _).le) y) hint, hsupp] at hpos

lemma contDiff_quad (n : ℕ) : ContDiff ℝ ⊤ (quad n) := by
  change ContDiff ℝ ⊤ (fun x : EuclideanSpace ℝ (Fin n) => Real.pi * ‖x‖ ^ 2)
  exact contDiff_const.mul (contDiff_norm_sq ℝ)

lemma quad_fderiv (n : ℕ) (x v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (quad n) x v = 2 * Real.pi * inner ℝ x v := by
  change fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) => Real.pi * ‖z‖ ^ 2) x v
    = 2 * Real.pi * inner ℝ x v
  have h := Commons.Analysis.Calculus.FDeriv.fderiv_mul_norm_sq_sub
    (E := EuclideanSpace ℝ (Fin n)) Real.pi (0 : EuclideanSpace ℝ (Fin n)) x
  have h' : fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) => Real.pi * ‖z‖ ^ 2) x
      = (2 * Real.pi) • innerSL ℝ x := by simpa using h
  rw [h']
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
  try ring

lemma quad_fderiv2 (n : ℕ) (x v w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fderiv ℝ (quad n)) x v w = 2 * Real.pi * inner ℝ v w := by
  change fderiv ℝ (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) => Real.pi * ‖z‖ ^ 2)) x v w
    = 2 * Real.pi * inner ℝ v w
  have h := Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_mul_norm_sq_sub
    (E := EuclideanSpace ℝ (Fin n)) Real.pi (0 : EuclideanSpace ℝ (Fin n)) x
  have h' : fderiv ℝ (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) => Real.pi * ‖z‖ ^ 2)) x
      = (2 * Real.pi) • innerSL ℝ := by simpa using h
  rw [h']
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [innerSL_apply_apply]
  try ring

/-- `penH = quad + penG`. -/
lemma penH_eq (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ) :
    penH n A ε = quad n + penG n A ε := by
  funext x
  rw [penH, Pi.add_apply, quad, penG]
  ring

/-- `penF = penH + log (gaussNorm)`. -/
lemma penF_eq (n : ℕ) {ε : ℝ} (hε : 0 < ε) (A : Set (EuclideanSpace ℝ (Fin n)))
    (hAm : MeasurableSet A) (hvol : 0 < volume A) :
    penF n A ε = penH n A ε + fun _ : EuclideanSpace ℝ (Fin n) => Real.log (gaussNorm n ε) := by
  funext x
  rw [penF, Pi.add_apply, penH, penPot_eq n hε A hAm hvol x, penG]
  ring

lemma fderiv_penF_eq (n : ℕ) {ε : ℝ} (hε : 0 < ε) (A : Set (EuclideanSpace ℝ (Fin n)))
    (hAm : MeasurableSet A) (hvol : 0 < volume A) :
    fderiv ℝ (penF n A ε) = fderiv ℝ (penH n A ε) := by
  rw [penF_eq n hε A hAm hvol]
  funext x
  rw [show penH n A ε + (fun _ : EuclideanSpace ℝ (Fin n) => Real.log (gaussNorm n ε))
      = fun y => penH n A ε y + Real.log (gaussNorm n ε) from rfl, fderiv_add_const]

lemma contDiff_penH (n : ℕ) {ε : ℝ} (hε : 0 < ε) (A : Set (EuclideanSpace ℝ (Fin n)))
    (hAm : MeasurableSet A) (hvol : 0 < volume A) : ContDiff ℝ ⊤ (penH n A ε) := by
  rw [penH_eq]
  exact (contDiff_quad n).add (contDiff_penG n hε A hAm hvol)

lemma contDiff_penF (n : ℕ) {ε : ℝ} (hε : 0 < ε) (A : Set (EuclideanSpace ℝ (Fin n)))
    (hAm : MeasurableSet A) (hvol : 0 < volume A) : ContDiff ℝ 2 (penF n A ε) := by
  rw [penF_eq n hε A hAm hvol]
  exact ((contDiff_penH n hε A hAm hvol).add contDiff_const).of_le (by norm_num)

/-- The penalised potential is `2π`-strongly convex. -/
lemma hessian_penF (n : ℕ) {ε : ℝ} (hε : 0 < ε) (A : Set (EuclideanSpace ℝ (Fin n)))
    (hAm : MeasurableSet A) (hA : Convex ℝ A) (hvol : 0 < volume A)
    (x v : EuclideanSpace ℝ (Fin n)) :
    2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (penF n A ε)) x v v := by
  have hcdG : ContDiff ℝ 2 (penG n A ε) :=
    (contDiff_penG n hε A hAm hvol).of_le (by norm_num)
  have hcvG : ConvexOn ℝ Set.univ (penG n A ε) := convexOn_penG n hε A hAm hA
  have hnn : 0 ≤ fderiv ℝ (fderiv ℝ (penG n A ε)) x v v :=
    Commons.Analysis.Convex.fderiv2_nonneg_of_convexOn (penG n A ε) hcdG hcvG x v
  rw [fderiv_penF_eq n hε A hAm hvol, penH_eq,
    show quad n + penG n A ε
      = fun y : EuclideanSpace ℝ (Fin n) => quad n y + penG n A ε y from rfl,
    Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_add_of_contDiffAt
      (φ := quad n) (q := penG n A ε) ((contDiff_quad n).of_le (by norm_num)).contDiffAt
      hcdG.contDiffAt]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
  rw [quad_fderiv2, real_inner_self_eq_norm_sq]
  linarith

/-- The penalised potential has at most polynomial growth (of its gradient and Hessian). -/
lemma growth_penF (n : ℕ) {ε : ℝ} (hε : 0 < ε) (A : Set (EuclideanSpace ℝ (Fin n)))
    (hAm : MeasurableSet A) (hA : Convex ℝ A) (hvol : 0 < volume A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : EuclideanSpace ℝ (Fin n),
      |fderiv ℝ (penF n A ε) x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ (penF n A ε)) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2 := by
  obtain ⟨C, hC0, N, hC⟩ := growth_fderiv_penalized n hε A hAm hA hvol
    (fun x => penLaplace_pos n hε A hAm hvol x)
  refine ⟨C, hC0, N, fun x v => ?_⟩
  have hpenH : (fun x : EuclideanSpace ℝ (Fin n) =>
      Real.pi * ‖x‖ ^ 2 + -Real.log (∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2)))
      = penH n A ε := by
    funext x
    rw [penH, penLaplace]
    ring
  obtain ⟨hb1, hb2⟩ := hC x v
  rw [hpenH] at hb1 hb2
  rw [fderiv_penF_eq n hε A hAm hvol]
  exact ⟨hb1, hb2⟩


lemma norm_smul_sq_div {n : ℕ} {ε : ℝ} (hε : ε ≠ 0) (z : EuclideanSpace ℝ (Fin n)) :
    ‖ε • z‖ ^ 2 / ε ^ 2 = ‖z‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp

/-- The Gaussian kernel is unchanged by the scaling `z ↦ ε z` after dividing by `ε²`. -/
lemma exp_neg_norm_smul {n : ℕ} {ε : ℝ} (hε : ε ≠ 0) (z : EuclideanSpace ℝ (Fin n)) :
    Real.exp (-‖ε • z‖ ^ 2 / ε ^ 2) = Real.exp (-‖z‖ ^ 2) := by
  rw [show -‖ε • z‖ ^ 2 / ε ^ 2 = -‖z‖ ^ 2 from by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp]

lemma penLaplace_smul (n : ℕ) {ε : ℝ} (hε : 0 < ε) (A : Set (EuclideanSpace ℝ (Fin n)))
    (hAm : MeasurableSet A) (x : EuclideanSpace ℝ (Fin n)) :
    penLaplace n A ε x = ε ^ n * ∫ z : EuclideanSpace ℝ (Fin n),
      A.indicator (fun _ => (1:ℝ)) (x + ε • z) * Real.exp (-‖z‖ ^ 2) := by
  set g : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun y => A.indicator (fun _ => (1:ℝ)) y * Real.exp (-‖x - y‖ ^ 2 / ε ^ 2) with hg
  have hgint : Integrable g := by
    refine (Commons.Analysis.Convex.integrable_gaussian_translate hε x).mono' ?_ ?_
    · exact (((measurable_const.indicator hAm).mul
        (by fun_prop : Measurable (fun y : EuclideanSpace ℝ (Fin n) =>
          Real.exp (-‖x - y‖ ^ 2 / ε ^ 2)))).aestronglyMeasurable)
    · filter_upwards with y
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      have h1 : |A.indicator (fun _ => (1:ℝ)) y| ≤ 1 := by
        by_cases h : y ∈ A
        · rw [Set.indicator_of_mem h]; norm_num
        · rw [Set.indicator_of_notMem h]; norm_num
      calc |A.indicator (fun _ => (1:ℝ)) y| * Real.exp (-‖x - y‖ ^ 2 / ε ^ 2)
          ≤ 1 * Real.exp (-‖x - y‖ ^ 2 / ε ^ 2) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
        _ = Real.exp (-‖x - y‖ ^ 2 / ε ^ 2) := one_mul _
  have hset : penLaplace n A ε x = ∫ y, g y := by
    rw [penLaplace, ← MeasureTheory.integral_indicator hAm]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with y
    rw [hg]
    by_cases h : y ∈ A
    · simp only [Set.indicator_of_mem h, Pi.mul_apply, one_mul]
    · simp only [Set.indicator_of_notMem h, Pi.mul_apply, zero_mul]
  rw [hset, Commons.Analysis.Measure.integral_smul_add_eq n hε x g hgint, hg]
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with z
  have hsub : x - (x + ε • z) = -(ε • z) := by abel
  rw [hsub, norm_neg, exp_neg_norm_smul (ne_of_gt hε)]

lemma gaussNorm_smul (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    gaussNorm n ε = ε ^ n * gaussNorm n 1 := by
  have hint : Integrable (fun y : EuclideanSpace ℝ (Fin n) => Real.exp (-‖y‖ ^ 2 / ε ^ 2)) := by
    simpa only [zero_sub, norm_neg] using
      Commons.Analysis.Convex.integrable_gaussian_translate hε (0 : EuclideanSpace ℝ (Fin n))
  simp only [gaussNorm]
  rw [Commons.Analysis.Measure.integral_smul_add_eq n hε (0 : EuclideanSpace ℝ (Fin n))
    (fun y : EuclideanSpace ℝ (Fin n) => Real.exp (-‖y‖ ^ 2 / ε ^ 2)) hint]
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with z
  rw [zero_add, exp_neg_norm_smul (ne_of_gt hε)]
  congr 1
  rw [one_pow, div_one]


lemma indicator_tendsto_of_not_mem_closure {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin n))}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∉ closure A) (z : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun ε : ℝ => A.indicator (fun _ => (1:ℝ)) (x + ε • z)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isClosed_closure.isOpen_compl x hx
  have hcont : Tendsto (fun ε : ℝ => x + ε • z) (𝓝 (0:ℝ)) (𝓝 x) := by
    have h1 : Tendsto (fun ε : ℝ => ε • z) (𝓝 (0:ℝ)) (𝓝 ((0:ℝ) • z)) :=
      tendsto_id.smul tendsto_const_nhds
    simpa using tendsto_const_nhds.add h1
  have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ), x + ε • z ∈ Metric.ball x r :=
    (hcont.eventually (Metric.ball_mem_nhds x hr)).filter_mono nhdsWithin_le_nhds
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [hev] with ε hε
  have hnot : x + ε • z ∉ A := fun hmem => hball hε (subset_closure hmem)
  rw [Set.indicator_of_notMem hnot]

/-- Dominated convergence for the scaled indicator: exterior case. -/
lemma tendsto_integral_indicator_gaussian_exterior (n : ℕ)
    (A : Set (EuclideanSpace ℝ (Fin n))) (hAm : MeasurableSet A)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∉ closure A) :
    Tendsto (fun ε : ℝ => ∫ z : EuclideanSpace ℝ (Fin n),
        A.indicator (fun _ => (1:ℝ)) (x + ε • z) * Real.exp (-‖z‖ ^ 2))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hbound : Integrable (fun z : EuclideanSpace ℝ (Fin n) => Real.exp (-‖z‖ ^ 2)) := by
    simpa only [neg_one_mul] using
      Commons.Measure.Integral.integrable_rexp_neg_mul_sq_norm
        (V := EuclideanSpace ℝ (Fin n)) 1 (by norm_num)
  have h := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[>] (0:ℝ))
    (F := fun ε : ℝ => fun z : EuclideanSpace ℝ (Fin n) =>
      A.indicator (fun _ => (1:ℝ)) (x + ε • z) * Real.exp (-‖z‖ ^ 2))
    (f := fun _ : EuclideanSpace ℝ (Fin n) => (0:ℝ))
    (bound := fun z : EuclideanSpace ℝ (Fin n) => Real.exp (-‖z‖ ^ 2))
    ?_ ?_ hbound ?_
  · simpa only [Pi.zero_apply, MeasureTheory.integral_zero] using h
  · filter_upwards with ε
    exact (((measurable_const.indicator hAm).comp
      (by fun_prop : Measurable (fun z : EuclideanSpace ℝ (Fin n) => x + ε • z))).mul
        (by fun_prop : Measurable (fun z : EuclideanSpace ℝ (Fin n) => Real.exp (-‖z‖ ^ 2)))
      ).aestronglyMeasurable
  · filter_upwards with ε
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    have h1 : |A.indicator (fun _ => (1:ℝ)) (x + ε • z)| ≤ 1 := by
      by_cases h : x + ε • z ∈ A
      · rw [Set.indicator_of_mem h]; norm_num
      · rw [Set.indicator_of_notMem h]; norm_num
    calc |A.indicator (fun _ => (1:ℝ)) (x + ε • z)| * Real.exp (-‖z‖ ^ 2)
        ≤ 1 * Real.exp (-‖z‖ ^ 2) := mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
      _ = Real.exp (-‖z‖ ^ 2) := one_mul _
  · filter_upwards with z
    simpa only [Pi.zero_apply, zero_mul] using
      (indicator_tendsto_of_not_mem_closure hx z).mul_const (Real.exp (-‖z‖ ^ 2))


lemma integral_gauss_eq_gaussNorm (n : ℕ) :
    (∫ z : EuclideanSpace ℝ (Fin n), Real.exp (-‖z‖ ^ 2)) = gaussNorm n 1 := by
  rw [gaussNorm]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with z
  congr 1
  rw [one_pow, div_one]

lemma penRatio_tendsto_interior (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n)))
    (hAm : MeasurableSet A) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ interior A) :
    Tendsto (fun ε : ℝ => penRatio n A ε x) (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have hCpos : 0 < gaussNorm n 1 := gaussNorm_pos n one_pos
  have hlim : Tendsto (fun ε : ℝ => ∫ z : EuclideanSpace ℝ (Fin n),
      A.indicator (fun _ => (1:ℝ)) (x + ε • z) * Real.exp (-‖z‖ ^ 2))
      (𝓝[>] (0:ℝ)) (𝓝 (gaussNorm n 1)) := by
    have h := tendsto_integral_indicator_gaussian (n := n) (A := A) hAm hx
    rwa [integral_gauss_eq_gaussNorm n] at h
  have hdiv : Tendsto (fun ε : ℝ => (∫ z : EuclideanSpace ℝ (Fin n),
      A.indicator (fun _ => (1:ℝ)) (x + ε • z) * Real.exp (-‖z‖ ^ 2)) / gaussNorm n 1)
      (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have h := hlim.div_const (gaussNorm n 1)
    rwa [div_self (ne_of_gt hCpos)] at h
  refine Tendsto.congr' ?_ hdiv
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [penRatio, penLaplace_smul n hε A hAm x, gaussNorm_smul n hε]
  rw [mul_div_mul_left _ _ (pow_ne_zero n (ne_of_gt hε))]

lemma penRatio_tendsto_exterior (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n)))
    (hAm : MeasurableSet A) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∉ closure A) :
    Tendsto (fun ε : ℝ => penRatio n A ε x) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hlim : Tendsto (fun ε : ℝ => ∫ z : EuclideanSpace ℝ (Fin n),
      A.indicator (fun _ => (1:ℝ)) (x + ε • z) * Real.exp (-‖z‖ ^ 2))
      (𝓝[>] (0:ℝ)) (𝓝 0) :=
    tendsto_integral_indicator_gaussian_exterior n A hAm hx
  have hdiv : Tendsto (fun ε : ℝ => (∫ z : EuclideanSpace ℝ (Fin n),
      A.indicator (fun _ => (1:ℝ)) (x + ε • z) * Real.exp (-‖z‖ ^ 2)) / gaussNorm n 1)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h := hlim.div_const (gaussNorm n 1)
    simpa only [zero_div] using h
  refine Tendsto.congr' ?_ hdiv
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [penRatio, penLaplace_smul n hε A hAm x, gaussNorm_smul n hε]
  rw [mul_div_mul_left _ _ (pow_ne_zero n (ne_of_gt hε))]


lemma ae_tendsto_exp_penF (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) (hA : Convex ℝ A)
    (hAm : MeasurableSet A) (hvol : 0 < volume A) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      Tendsto (fun ε : ℝ => Real.exp (-(penF n A ε x))) (𝓝[>] (0:ℝ))
        (𝓝 (A.indicator (fun _ => (1:ℝ)) x * gDens n x)) := by
  have hfr : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), x ∉ frontier A := by
    rw [MeasureTheory.ae_iff]
    simpa using Convex.addHaar_frontier (volume : Measure (EuclideanSpace ℝ (Fin n))) hA
  filter_upwards [hfr] with x hx
  have hx' : x ∈ interior A ∨ x ∉ closure A := by
    by_contra h
    push_neg at h
    exact hx ⟨h.2, h.1⟩
  rcases hx' with hin | hout
  · have h1 : A.indicator (fun _ => (1:ℝ)) x = 1 :=
      Set.indicator_of_mem (interior_subset hin) (fun _ => (1:ℝ))
    rw [h1, one_mul]
    have h2 : Tendsto (fun ε : ℝ => gDens n x * penRatio n A ε x)
        (𝓝[>] (0:ℝ)) (𝓝 (gDens n x)) := by
      simpa using (penRatio_tendsto_interior n A hAm hin).const_mul (gDens n x)
    refine Tendsto.congr' ?_ h2
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (exp_neg_penF n hε A hAm hvol x).symm
  · have h1 : A.indicator (fun _ => (1:ℝ)) x = 0 :=
      Set.indicator_of_notMem (fun hmem => hout (subset_closure hmem)) (fun _ => (1:ℝ))
    rw [h1, zero_mul]
    have h2 : Tendsto (fun ε : ℝ => gDens n x * penRatio n A ε x)
        (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa using (penRatio_tendsto_exterior n A hAm hout).const_mul (gDens n x)
    refine Tendsto.congr' ?_ h2
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (exp_neg_penF n hε A hAm hvol x).symm

lemma tendsto_integral_penF_mul (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) (hA : Convex ℝ A)
    (hAm : MeasurableSet A) (hvol : 0 < volume A)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφm : AEStronglyMeasurable φ volume)
    (hφint : Integrable (fun x => ‖φ x‖ * gDens n x)) :
    Tendsto (fun ε : ℝ => ∫ x, φ x * Real.exp (-(penF n A ε x)))
      (𝓝[>] (0:ℝ)) (𝓝 (∫ x in A, φ x * gDens n x)) := by
  have hlim : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      Tendsto (fun ε : ℝ => φ x * Real.exp (-(penF n A ε x))) (𝓝[>] (0:ℝ))
        (𝓝 (φ x * (A.indicator (fun _ => (1:ℝ)) x * gDens n x))) :=
    (ae_tendsto_exp_penF n A hA hAm hvol).mono fun x hx => hx.const_mul (φ x)
  have hmain : Tendsto (fun ε : ℝ => ∫ x, φ x * Real.exp (-(penF n A ε x))) (𝓝[>] (0:ℝ))
      (𝓝 (∫ x, φ x * (A.indicator (fun _ => (1:ℝ)) x * gDens n x))) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (bound := fun x : EuclideanSpace ℝ (Fin n) => ‖φ x‖ * gDens n x) ?_ ?_ hφint ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
          Real.exp (-(penF n A ε x))) :=
        Real.continuous_exp.comp (contDiff_penF n hε A hAm hvol).continuous.neg
      exact (hφm.mul hcont.measurable.aestronglyMeasurable)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards with x
      rw [gDens, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
      have h2 := penPot_nonneg n hε A hAm x
      rw [penF]
      nlinarith [h2, Real.pi_pos, sq_nonneg ‖x‖]
    · exact hlim
  have hident : (∫ x, φ x * (A.indicator (fun _ => (1:ℝ)) x * gDens n x))
      = ∫ x in A, φ x * gDens n x := by
    rw [← MeasureTheory.integral_indicator hAm]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    by_cases h : x ∈ A
    · simp only [Set.indicator_of_mem h, Pi.mul_apply]
      ring
    · simp only [Set.indicator_of_notMem h, Pi.mul_apply, mul_zero, zero_mul]
  rwa [hident] at hmain


/-! ### The smooth cutoff -/

noncomputable def gbump (n : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
  ⟨1, 2, one_pos, one_lt_two⟩

noncomputable def cut (n : ℕ) (R : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (gbump n) (R⁻¹ • x)

noncomputable def uPark (n : ℕ) (w : EuclideanSpace ℝ (Fin n) → ℝ) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ := cut n R x * w x

lemma contDiff_cut (n : ℕ) (R : ℝ) : ContDiff ℝ 1 (cut n R) :=
  (ContDiffBump.contDiff (gbump n) (n := 1)).comp (contDiff_const_smul (R⁻¹ : ℝ))

lemma cut_nonneg (n : ℕ) (R : ℝ) (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ cut n R x :=
  ContDiffBump.nonneg (gbump n)

lemma cut_le_one (n : ℕ) (R : ℝ) (x : EuclideanSpace ℝ (Fin n)) : cut n R x ≤ 1 :=
  ContDiffBump.le_one (gbump n)

lemma cut_eq_one (n : ℕ) {R : ℝ} (hR : 0 < R) {x : EuclideanSpace ℝ (Fin n)}
    (hx : ‖x‖ ≤ R) : cut n R x = 1 := by
  refine ContDiffBump.one_of_mem_closedBall (f := gbump n) ?_
  simp only [Metric.mem_closedBall, dist_zero_right]
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
  show R⁻¹ * ‖x‖ ≤ 1
  calc R⁻¹ * ‖x‖ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hR.le)
    _ = 1 := by rw [inv_mul_cancel₀ (ne_of_gt hR)]

lemma cut_eq_zero (n : ℕ) {R : ℝ} (hR : 0 < R) {x : EuclideanSpace ℝ (Fin n)}
    (hx : 2 * R ≤ ‖x‖) : cut n R x = 0 := by
  by_contra hne
  have hmem : R⁻¹ • x ∈ Function.support (gbump n : EuclideanSpace ℝ (Fin n) → ℝ) := hne
  rw [ContDiffBump.support_eq (gbump n), Metric.mem_ball, dist_zero_right, norm_smul,
    Real.norm_eq_abs, abs_inv, abs_of_pos hR] at hmem
  have hmem' : R⁻¹ * ‖x‖ < 2 := hmem
  have hge : 2 ≤ R⁻¹ * ‖x‖ := by
    calc (2:ℝ) = R⁻¹ * (2 * R) := by
          rw [mul_comm 2 R, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hR), one_mul]
      _ ≤ R⁻¹ * ‖x‖ := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hR.le)
  linarith

lemma hasCompactSupport_cut (n : ℕ) {R : ℝ} (hR : 0 < R) : HasCompactSupport (cut n R) := by
  have hsupp : Function.support (cut n R)
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (2 * R) := fun x hx => by
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hlt
    push_neg at hlt
    exact hx (cut_eq_zero n hR hlt.le)
  exact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (2 * R)).of_isClosed_subset
    (isClosed_tsupport (cut n R)) (closure_minimal hsupp Metric.isClosed_closedBall)

lemma cut_tendsto (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun R : ℝ => cut n R x) atTop (𝓝 1) := by
  have h0 : (gbump n : EuclideanSpace ℝ (Fin n) → ℝ) 0 = 1 := by
    refine ContDiffBump.one_of_mem_closedBall (f := gbump n) ?_
    simp only [Metric.mem_closedBall, dist_self]
    exact (gbump n).rIn_pos.le
  have hcd : ContDiff ℝ 1 (gbump n : EuclideanSpace ℝ (Fin n) → ℝ) :=
    ContDiffBump.contDiff (gbump n) (n := 1)
  have hcont : ContinuousAt (gbump n : EuclideanSpace ℝ (Fin n) → ℝ) 0 :=
    hcd.continuous.continuousAt
  have harg : Tendsto (fun R : ℝ => R⁻¹ • x) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 (0:ℝ)) := tendsto_inv_atTop_zero
    simpa using h1.smul (tendsto_const_nhds : Tendsto (fun _ : ℝ => x) atTop (𝓝 x))
  have hcomp : Tendsto (fun R : ℝ => (gbump n) (R⁻¹ • x)) atTop (𝓝 ((gbump n) 0)) :=
    hcont.tendsto.comp harg
  rw [h0] at hcomp
  simpa only [cut] using hcomp

lemma fderiv_cut (n : ℕ) (R : ℝ) :
    fderiv ℝ (cut n R)
      = fun x : EuclideanSpace ℝ (Fin n) =>
          (fderiv ℝ (gbump n : EuclideanSpace ℝ (Fin n) → ℝ) (R⁻¹ • x)).comp
            (R⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) := by
  have hd : ∀ x : EuclideanSpace ℝ (Fin n),
      DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin n) => R⁻¹ • y) x := by
    intro x
    have heq : (fun y : EuclideanSpace ℝ (Fin n) => R⁻¹ • y)
        = R⁻¹ • (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) := rfl
    rw [heq]
    exact differentiableAt_id.const_smul (R⁻¹)
  have hsmul : ∀ x : EuclideanSpace ℝ (Fin n),
      fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => R⁻¹ • y) x
        = R⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    intro x
    have heq : (fun y : EuclideanSpace ℝ (Fin n) => R⁻¹ • y)
        = R⁻¹ • (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) := rfl
    rw [heq, fderiv_const_smul differentiableAt_id (R⁻¹), fderiv_id]
  have hg : ∀ x : EuclideanSpace ℝ (Fin n),
      DifferentiableAt ℝ (gbump n : EuclideanSpace ℝ (Fin n) → ℝ) (R⁻¹ • x) := fun x =>
    ((ContDiffBump.contDiff (gbump n) (n := 1)).differentiable (by norm_num)).differentiableAt
  change fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => (gbump n) (R⁻¹ • y))
      = fun x : EuclideanSpace ℝ (Fin n) =>
          (fderiv ℝ (gbump n : EuclideanSpace ℝ (Fin n) → ℝ) (R⁻¹ • x)).comp
            (R⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
  funext x
  show fderiv ℝ ((gbump n : EuclideanSpace ℝ (Fin n) → ℝ)
        ∘ fun y : EuclideanSpace ℝ (Fin n) => R⁻¹ • y) x
      = (fderiv ℝ (gbump n : EuclideanSpace ℝ (Fin n) → ℝ) (R⁻¹ • x)).comp
          (R⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
  rw [fderiv_comp x (hg x) (hd x), hsmul x]

lemma exists_bound_fderiv_compactSupport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {χ : E → ℝ} (hχ : ContDiff ℝ 1 χ) (hcs : HasCompactSupport χ) :
    ∃ C : ℝ, ∀ x : E, ‖fderiv ℝ χ x‖ ≤ C :=
  (hcs.fderiv (𝕜 := ℝ)).exists_bound_of_continuous (hχ.continuous_fderiv (by norm_num))

lemma exists_bound_gbump_fderiv (n : ℕ) :
    ∃ C : ℝ, ∀ y : EuclideanSpace ℝ (Fin n),
      ‖fderiv ℝ (gbump n : EuclideanSpace ℝ (Fin n) → ℝ) y‖ ≤ C :=
  exists_bound_fderiv_compactSupport (ContDiffBump.contDiff (gbump n) (n := 1))
    (ContDiffBump.hasCompactSupport (gbump n))

lemma norm_inv_smul_id_le (n : ℕ) (R : ℝ) :
    ‖R⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ |R⁻¹| := by
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) ContinuousLinearMap.norm_id_le

lemma exists_bound_fderiv_cut (n : ℕ) :
    ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ x : EuclideanSpace ℝ (Fin n),
      ‖fderiv ℝ (cut n R) x‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ := exists_bound_gbump_fderiv n
  have hC₀nn : 0 ≤ C₀ := le_trans (norm_nonneg _) (hC₀ 0)
  refine ⟨C₀, fun R hR x => ?_⟩
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
  have hle1 : |R⁻¹| ≤ 1 := by
    rw [abs_of_pos (inv_pos.mpr hRpos)]
    exact inv_le_one_of_one_le₀ hR
  have hfd := congrFun (fderiv_cut n R) x
  rw [hfd]
  calc ‖(fderiv ℝ (gbump n : EuclideanSpace ℝ (Fin n) → ℝ) (R⁻¹ • x)).comp
        (R⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))‖
      ≤ ‖fderiv ℝ (gbump n : EuclideanSpace ℝ (Fin n) → ℝ) (R⁻¹ • x)‖ *
          ‖R⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ C₀ * |R⁻¹| := mul_le_mul (hC₀ _) (norm_inv_smul_id_le n R) (norm_nonneg _) hC₀nn
    _ ≤ C₀ * 1 := mul_le_mul_of_nonneg_left hle1 hC₀nn
    _ = C₀ := mul_one C₀

lemma fderiv_cut_tendsto_zero (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun R : ℝ => fderiv ℝ (cut n R) x) atTop (𝓝 0) := by
  obtain ⟨C₀, hC₀⟩ := exists_bound_gbump_fderiv n
  have hC₀nn : 0 ≤ C₀ := le_trans (norm_nonneg _) (hC₀ 0)
  have hbound : ∀ R : ℝ, ‖fderiv ℝ (cut n R) x‖ ≤ C₀ * |R⁻¹| := by
    intro R
    rw [congrFun (fderiv_cut n R) x]
    calc ‖(fderiv ℝ (gbump n : EuclideanSpace ℝ (Fin n) → ℝ) (R⁻¹ • x)).comp
          (R⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))‖
        ≤ ‖fderiv ℝ (gbump n : EuclideanSpace ℝ (Fin n) → ℝ) (R⁻¹ • x)‖ *
            ‖R⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C₀ * |R⁻¹| := mul_le_mul (hC₀ _) (norm_inv_smul_id_le n R) (norm_nonneg _) hC₀nn
  refine squeeze_zero_norm (a := fun R : ℝ => C₀ * |R⁻¹|) hbound ?_
  have h1 : Tendsto (fun R : ℝ => |R⁻¹|) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).abs
  simpa using h1.const_mul C₀


/-! ### The penalised potential as a `BLon` potential -/

lemma convexOn_penF (n : ℕ) {ε : ℝ} (hε : 0 < ε) (A : Set (EuclideanSpace ℝ (Fin n)))
    (hAm : MeasurableSet A) (hA : Convex ℝ A) (hvol : 0 < volume A) :
    ConvexOn ℝ Set.univ
      (fun x : EuclideanSpace ℝ (Fin n) => penF n A ε x - Real.pi * ‖x‖ ^ 2) := by
  have heq : (fun x : EuclideanSpace ℝ (Fin n) => penF n A ε x - Real.pi * ‖x‖ ^ 2)
      = penPot n A ε := by
    funext x; rw [penF]; ring
  rw [heq]
  exact convexOn_penPot n hε A hAm hA hvol

lemma integrable_gDens (n : ℕ) : Integrable (gDens n) volume := by
  have h := Commons.Measure.Integral.integrable_rexp_neg_mul_sq_norm
    (V := EuclideanSpace ℝ (Fin n)) Real.pi Real.pi_pos
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  rw [gDens]
  congr 1
  ring

section HessInvNonneg
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

lemma hessInv_nonneg (f : E → ℝ) (x : E) (hinj : Function.Injective (hessOp f x))
    (hH : ∀ v : E, 2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v) (u : E) :
    0 ≤ ⟪hessInv f x u, u⟫_ℝ := by
  set w : E := hessInv f x u with hwdef
  have hw' : hessOp f x w = u := hessInv_right f x hinj u
  have h1 : ⟪hessInv f x u, u⟫_ℝ = fderiv ℝ (fderiv ℝ f) x w w := by
    calc ⟪hessInv f x u, u⟫_ℝ = ⟪hessInv f x u, hessOp f x w⟫_ℝ := by rw [hw']
      _ = ⟪w, hessOp f x w⟫_ℝ := by rw [← hw', hessInv_left f x hinj w]
      _ = ⟪hessOp f x w, w⟫_ℝ := real_inner_comm _ _
      _ = fderiv ℝ (fderiv ℝ f) x w w := hessOp_spec f x w w
  rw [h1]
  exact le_trans (by positivity : (0:ℝ) ≤ 2 * Real.pi * ‖w‖ ^ 2) (hH w)

end HessInvNonneg

lemma contDiff_uPark (n : ℕ) (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 1 w)
    (R : ℝ) : ContDiff ℝ 1 (uPark n w R) :=
  (contDiff_cut n R).mul hw

lemma hasCompactSupport_uPark (n : ℕ) (w : EuclideanSpace ℝ (Fin n) → ℝ) {R : ℝ}
    (hR : 0 < R) : HasCompactSupport (uPark n w R) :=
  (hasCompactSupport_cut n hR).mul_right

lemma bound_uPark (n : ℕ) (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 1 w)
    {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : EuclideanSpace ℝ (Fin n),
      |uPark n w R x| ≤ C ∧ ‖fderiv ℝ (uPark n w R) x‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ := (hasCompactSupport_uPark n w hR).exists_bound_of_continuous
    (contDiff_uPark n w hw R).continuous
  obtain ⟨C₁, hC₁⟩ := exists_bound_fderiv_compactSupport (contDiff_uPark n w hw R)
    (hasCompactSupport_uPark n w hR)
  have hC₀nn : 0 ≤ C₀ := le_trans (norm_nonneg _) (hC₀ 0)
  refine ⟨max C₀ C₁, le_max_of_le_left hC₀nn, fun x => ⟨?_, ?_⟩⟩
  · have h := hC₀ x
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  · exact le_trans (hC₁ x) (le_max_right _ _)

lemma growth_uPark (n : ℕ) (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 1 w)
    {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : EuclideanSpace ℝ (Fin n),
      |uPark n w R x| ≤ C * (1 + ‖x‖) ^ N ∧
      |fderiv ℝ (uPark n w R) x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ := by
  obtain ⟨C, hC0, hC⟩ := bound_uPark n w hw hR
  refine ⟨C, hC0, 0, fun x v => ⟨?_, ?_⟩⟩
  · rw [pow_zero, mul_one]; exact (hC x).1
  · have h := ContinuousLinearMap.le_opNorm (fderiv ℝ (uPark n w R) x) v
    rw [pow_zero, mul_one]
    calc |fderiv ℝ (uPark n w R) x v| = ‖fderiv ℝ (uPark n w R) x v‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖fderiv ℝ (uPark n w R) x‖ * ‖v‖ := h
      _ ≤ C * ‖v‖ := mul_le_mul_of_nonneg_right (hC x).2 (norm_nonneg v)

lemma fderiv_uPark (n : ℕ) (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 1 w)
    (R : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (uPark n w R) x
      = cut n R x • fderiv ℝ w x + w x • fderiv ℝ (cut n R) x := by
  have h1 : DifferentiableAt ℝ (cut n R) x :=
    ((contDiff_cut n R).differentiable (by norm_num)).differentiableAt
  have h2 : DifferentiableAt ℝ w x := (hw.differentiable (by norm_num)).differentiableAt
  exact fderiv_fun_mul h1 h2

lemma tendsto_fderiv_uPark (n : ℕ) (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 1 w)
    (x : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun R : ℝ => fderiv ℝ (uPark n w R) x) atTop (𝓝 (fderiv ℝ w x)) := by
  have h1 : Tendsto (fun R : ℝ => cut n R x • fderiv ℝ w x) atTop (𝓝 (fderiv ℝ w x)) := by
    have := (cut_tendsto n x).smul_const (fderiv ℝ w x)
    simpa using this
  have h2 : Tendsto (fun R : ℝ => w x • fderiv ℝ (cut n R) x) atTop (𝓝 0) := by
    have := (fderiv_cut_tendsto_zero n x).const_smul (w x)
    simpa using this
  have hsum := h1.add h2
  rw [add_zero] at hsum
  refine Tendsto.congr (fun R => ?_) hsum
  exact (fderiv_uPark n w hw R x).symm

lemma tendsto_fderiv_uPark_norm_sq (n : ℕ) (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (hw : ContDiff ℝ 1 w) (x : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun R : ℝ => ‖fderiv ℝ (uPark n w R) x‖ ^ 2) atTop
      (𝓝 (‖fderiv ℝ w x‖ ^ 2)) :=
  ((continuous_norm.pow 2).tendsto (fderiv ℝ w x)).comp (tendsto_fderiv_uPark n w hw x)

lemma tendsto_uPark_sq (n : ℕ) (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun R : ℝ => uPark n w R x ^ 2) atTop (𝓝 (w x ^ 2)) := by
  have h := (cut_tendsto n x).pow 2
  have := h.mul_const (w x ^ 2)
  simpa [uPark, mul_pow] using this

lemma tendsto_uPark (n : ℕ) (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun R : ℝ => uPark n w R x) atTop (𝓝 (w x)) := by
  have h := (cut_tendsto n x).mul_const (w x)
  simpa [uPark] using h

/-! ### The dominated convergence lemma for the cutoff -/

lemma tendsto_integral_cut_mul (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n)))
    (ψ : ℝ → EuclideanSpace ℝ (Fin n) → ℝ) (Ψ B : EuclideanSpace ℝ (Fin n) → ℝ)
    (hB : Integrable (fun x => B x * gDens n x) (volume.restrict A))
    (hbd : ∀ᶠ R in atTop, ∀ᵐ x ∂(volume.restrict A), ‖ψ R x‖ ≤ B x)
    (hlim : ∀ᵐ x ∂(volume.restrict A), Tendsto (fun R => ψ R x) atTop (𝓝 (Ψ x)))
    (hmeas : ∀ᶠ R in atTop,
      AEStronglyMeasurable (fun x => ψ R x * gDens n x) (volume.restrict A)) :
    Tendsto (fun R => ∫ x in A, ψ R x * gDens n x) atTop
      (𝓝 (∫ x in A, Ψ x * gDens n x)) := by
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (F := fun R x => ψ R x * gDens n x) (f := fun x => Ψ x * gDens n x)
    (bound := fun x : EuclideanSpace ℝ (Fin n) => B x * gDens n x) hmeas ?_ hB ?_
  · filter_upwards [hbd] with R hR
    filter_upwards [hR] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gDens_nonneg n x)]
    exact mul_le_mul_of_nonneg_right hx (gDens_nonneg n x)
  · exact hlim.mono fun x hx => hx.mul_const (gDens n x)


/-! ### The `ε → 0` stage at fixed cutoff -/

section EnergyCont
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

lemma continuous_hessInv_energy (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (hH : ∀ x v : E, 2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v)
    (g : E → E) (hg : Continuous g) :
    Continuous (fun x : E => ⟪hessInv f x (g x), g x⟫_ℝ) :=
  ((continuous_hessInv_pair f hf hH).comp (continuous_id.prodMk hg)).inner hg

end EnergyCont

/-- A measurable function with a bounded norm is integrable against `gDens`. -/
lemma integrable_norm_mul_gDens (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : AEStronglyMeasurable φ volume) {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C) :
    Integrable (fun x => ‖φ x‖ * gDens n x) volume := by
  have hm_g : AEStronglyMeasurable (gDens n) volume := (integrable_gDens n).aestronglyMeasurable
  refine ((integrable_gDens n).const_mul C).mono' (hφ.norm.mul hm_g) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (gDens_nonneg n x))]
  exact mul_le_mul_of_nonneg_right (hC x) (gDens_nonneg n x)

lemma bl_cut_stage (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) (hA : Convex ℝ A)
    (hAm : MeasurableSet A) (hvol : 0 < volume A) (hZ : 0 < ∫ x in A, gDens n x)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 1 w) {R : ℝ} (hR : 1 ≤ R) :
    (∫ x in A, uPark n w R x ^ 2 * gDens n x)
      - (∫ x in A, uPark n w R x * gDens n x) ^ 2 / (∫ x in A, gDens n x)
    ≤ (1 / (2 * Real.pi)) * ∫ x in A, ‖fderiv ℝ (uPark n w R) x‖ ^ 2 * gDens n x := by
  obtain ⟨Cu, hCu0, hCu⟩ := bound_uPark n w hw (lt_of_lt_of_le one_pos hR)
  set u : EuclideanSpace ℝ (Fin n) → ℝ := uPark n w R with hu
  set Z : ℝ := ∫ x in A, gDens n x with hZdef
  have hZpos : 0 < Z := hZ
  have hZne : Z ≠ 0 := ne_of_gt hZpos
  have hgint : Integrable (gDens n) volume := integrable_gDens n
  have hD2 : Integrable (fun x : EuclideanSpace ℝ (Fin n) => Cu ^ 2 * gDens n x) volume :=
    hgint.const_mul _
  have hmeas_u : AEStronglyMeasurable u volume :=
    (contDiff_uPark n w hw R).continuous.measurable.aestronglyMeasurable
  have hCd : ContDiff ℝ 1 u := contDiff_uPark n w hw R
  have hgradc : Continuous (fun x : EuclideanSpace ℝ (Fin n) => grad u x) :=
    continuous_grad_of_contDiff u hCd
  -- integrability of the four test functions against `gDens`
  have hphi2 : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖u x ^ 2‖ * gDens n x) volume :=
    integrable_norm_mul_gDens n (hmeas_u.pow 2) (C := Cu ^ 2) (fun x => by
      have h := (hCu x).1
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (u x))]
      nlinarith [h, hCu0, abs_nonneg (u x), sq_abs (u x)])
  have hphi1 : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖u x‖ * gDens n x) volume :=
    integrable_norm_mul_gDens n hmeas_u (C := Cu) (fun x => by
      rw [Real.norm_eq_abs]; exact (hCu x).1)
  have hphi0 : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖(1:ℝ)‖ * gDens n x) volume := by
    simpa using hgint
  have hphiD : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      ‖‖fderiv ℝ u x‖ ^ 2‖ * gDens n x) volume :=
    integrable_norm_mul_gDens n (((hCd.continuous_fderiv (by norm_num)).norm.pow 2).aestronglyMeasurable)
      (C := Cu ^ 2) (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have h := (hCu x).2
        nlinarith [h, hCu0, norm_nonneg (fderiv ℝ u x)])
  -- the four epsilon-limits
  have hA2 := tendsto_integral_penF_mul n A hA hAm hvol (fun x => u x ^ 2) (hmeas_u.pow 2) hphi2
  have hA1 := tendsto_integral_penF_mul n A hA hAm hvol (fun x => u x) hmeas_u hphi1
  have hA0 : Tendsto (fun ε : ℝ => ∫ x, Real.exp (-(penF n A ε x))) (𝓝[>] (0:ℝ)) (𝓝 Z) := by
    have h := tendsto_integral_penF_mul n A hA hAm hvol (fun _ => (1:ℝ))
      aestronglyMeasurable_const hphi0
    simpa only [one_mul, ← hZdef] using h
  have hAe := tendsto_integral_penF_mul n A hA hAm hvol (fun x => ‖fderiv ℝ u x‖ ^ 2)
    (((hCd.continuous_fderiv (by norm_num)).norm.pow 2).aestronglyMeasurable) hphiD
  have hvar : Tendsto (fun ε : ℝ => wVar (fun x => Real.exp (-(penF n A ε x))) u)
      (𝓝[>] (0:ℝ))
      (𝓝 ((∫ x in A, u x ^ 2 * gDens n x) - (∫ x in A, u x * gDens n x) ^ 2 / Z)) := by
    have h := hA2.sub ((hA1.pow 2).div hA0 hZne)
    simpa only [wVar, one_mul, ← hZdef, div_apply, Pi.div_apply] using h
  have henergy : Tendsto (fun ε : ℝ => (1 / (2 * Real.pi)) *
      ∫ x, ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(penF n A ε x))) (𝓝[>] (0:ℝ))
      (𝓝 ((1 / (2 * Real.pi)) * ∫ x in A, ‖fderiv ℝ u x‖ ^ 2 * gDens n x)) :=
    hAe.const_mul (1 / (2 * Real.pi))
  refine le_of_tendsto_of_tendsto hvar henergy ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hCd2 : ContDiff ℝ 2 (penF n A ε) := contDiff_penF n hε A hAm hvol
  have hH : ∀ x v : EuclideanSpace ℝ (Fin n),
      2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (penF n A ε)) x v v :=
    hessian_penF n hε A hAm hA hvol
  have hbl : wVar (fun x => Real.exp (-(penF n A ε x))) u
      ≤ ∫ x, ⟪hessInv (penF n A ε) x (grad u x), grad u x⟫_ℝ *
          Real.exp (-(penF n A ε x)) :=
    brascamp_lieb_smooth (penF n A ε) u hCd2 hH
      (convexOn_penF n hε A hAm hA hvol) (growth_penF n hε A hAm hA hvol)
      hCd (growth_uPark n w hw (lt_of_lt_of_le one_pos hR))
  refine le_trans hbl ?_
  -- pointwise facts
  have hexp_le : ∀ x : EuclideanSpace ℝ (Fin n), Real.exp (-(penF n A ε x)) ≤ gDens n x := by
    intro x
    rw [gDens, Real.exp_le_exp]
    have h := penPot_nonneg n hε A hAm x
    rw [penF]; linarith
  have hgrad_le : ∀ x : EuclideanSpace ℝ (Fin n), ‖grad u x‖ ^ 2 / (2 * Real.pi) ≤ Cu ^ 2 := by
    intro x
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)]
    have h := (hCu x).2
    rw [grad_norm_eq]
    have hπ : (1:ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    nlinarith [h, hCu0, norm_nonneg (fderiv ℝ u x), hπ]
  have hboundfun : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      (‖grad u x‖ ^ 2 / (2 * Real.pi)) * Real.exp (-(penF n A ε x))) volume := by
    have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
        (‖grad u x‖ ^ 2 / (2 * Real.pi)) * Real.exp (-(penF n A ε x))) :=
      ((hgradc.norm.pow 2).div_const _).mul (Real.continuous_exp.comp hCd2.continuous.neg)
    refine hD2.mono' hcont.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (div_nonneg (sq_nonneg _) (by positivity))
      (Real.exp_nonneg _))]
    exact mul_le_mul (hgrad_le x) (hexp_le x) (Real.exp_nonneg _) (by positivity)
  have hboundint : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      ⟪hessInv (penF n A ε) x (grad u x), grad u x⟫_ℝ * Real.exp (-(penF n A ε x))) volume := by
    have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
        ⟪hessInv (penF n A ε) x (grad u x), grad u x⟫_ℝ * Real.exp (-(penF n A ε x))) :=
      (continuous_hessInv_energy (penF n A ε) hCd2 hH (fun x => grad u x) hgradc).mul
        (Real.continuous_exp.comp hCd2.continuous.neg)
    refine hD2.mono' hcont.aestronglyMeasurable ?_
    filter_upwards with x
    have hnonneg := hessInv_nonneg (penF n A ε) x
      (hessOp_injective (penF n A ε) x (hH x)) (hH x) (grad u x)
    have hen := hessInv_energy (penF n A ε) x
      (hessOp_injective (penF n A ε) x (hH x)) (hH x) (grad u x)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _),
      abs_of_nonneg hnonneg]
    exact mul_le_mul (le_trans hen (hgrad_le x)) (hexp_le x) (Real.exp_nonneg _) (by positivity)
  calc ∫ x, ⟪hessInv (penF n A ε) x (grad u x), grad u x⟫_ℝ * Real.exp (-(penF n A ε x))
      ≤ ∫ x, (‖grad u x‖ ^ 2 / (2 * Real.pi)) * Real.exp (-(penF n A ε x)) := by
        refine MeasureTheory.integral_mono_ae hboundint hboundfun ?_
        filter_upwards with x
        exact mul_le_mul_of_nonneg_right
          (hessInv_energy (penF n A ε) x
            (hessOp_injective (penF n A ε) x (hH x)) (hH x) (grad u x))
          (Real.exp_nonneg _)
    _ = (1 / (2 * Real.pi)) * ∫ x, ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(penF n A ε x)) := by
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with x
        rw [grad_norm_eq]
        ring


lemma continuous_gDens (n : ℕ) : Continuous (gDens n) := by
  change Continuous (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-(Real.pi * ‖x‖ ^ 2)))
  exact Real.continuous_exp.comp ((continuous_const.mul (continuous_norm.pow 2)).neg)

lemma bl_final (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) (hA : Convex ℝ A)
    (hAm : MeasurableSet A) (hvol : 0 < volume A) (hZ : 0 < ∫ x in A, gDens n x)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 1 w)
    (hw2 : Integrable (fun x => w x ^ 2 * gDens n x) (volume.restrict A))
    (hg : Integrable (fun x => ‖fderiv ℝ w x‖ ^ 2 * gDens n x) (volume.restrict A))
    (hmean : (∫ x in A, w x * gDens n x) = 0) :
    (∫ x in A, w x ^ 2 * gDens n x)
      ≤ (1 / (2 * Real.pi)) * ∫ x in A, ‖fderiv ℝ w x‖ ^ 2 * gDens n x := by
  obtain ⟨Cc, hCc⟩ := exists_bound_fderiv_cut n
  set Z : ℝ := ∫ x in A, gDens n x with hZdef
  have hZne : Z ≠ 0 := ne_of_gt hZ
  have hgA : Integrable (gDens n) (volume.restrict A) := (integrable_gDens n).integrableOn
  -- integrability of `|w| * gDens` on `A`
  have hwg : Integrable (fun x => |w x| * gDens n x) (volume.restrict A) := by
    have hG : Integrable (fun x => (w x ^ 2 * gDens n x + gDens n x) / 2)
        (volume.restrict A) := (hw2.add hgA).div_const 2
    refine hG.mono' ?_ ?_
    · exact ((hw.continuous.abs.mul (continuous_gDens n)).measurable).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (gDens_nonneg n x))]
      have hg0 := gDens_nonneg n x
      nlinarith [sq_nonneg (|w x| - 1), sq_abs (w x), hg0]
  -- the integrable domination for the energy term
  have hB : Integrable (fun x => (2 * ‖fderiv ℝ w x‖ ^ 2 + 2 * Cc ^ 2 * w x ^ 2) * gDens n x)
      (volume.restrict A) := by
    have h1 : Integrable (fun x => 2 * (‖fderiv ℝ w x‖ ^ 2 * gDens n x)) (volume.restrict A) :=
      hg.const_mul 2
    have h2 : Integrable (fun x => 2 * Cc ^ 2 * (w x ^ 2 * gDens n x)) (volume.restrict A) :=
      hw2.const_mul (2 * Cc ^ 2)
    refine (h1.add h2).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  -- the three limits
  have hcut_sq : ∀ R x, ‖uPark n w R x ^ 2‖ ≤ w x ^ 2 := by
    intro R x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), uPark, mul_pow]
    have h3 : |cut n R x| ≤ 1 := by
      rw [abs_of_nonneg (cut_nonneg n R x)]; exact cut_le_one n R x
    have h3' : cut n R x ^ 2 ≤ 1 := by
      nlinarith [h3, abs_nonneg (cut n R x), sq_abs (cut n R x)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right h3' (sq_nonneg (w x))
  have hI2 : Tendsto (fun R : ℝ => ∫ x in A, uPark n w R x ^ 2 * gDens n x) atTop
      (𝓝 (∫ x in A, w x ^ 2 * gDens n x)) :=
    tendsto_integral_cut_mul n A (fun R x => uPark n w R x ^ 2) (fun x => w x ^ 2)
      (fun x => w x ^ 2) hw2
      (Filter.Eventually.of_forall fun R => Filter.Eventually.of_forall fun x => hcut_sq R x)
      (Filter.Eventually.of_forall fun x => tendsto_uPark_sq n w x)
      (Filter.Eventually.of_forall fun R =>
        ((((contDiff_uPark n w hw R).continuous.pow 2).mul (continuous_gDens n)).measurable).aestronglyMeasurable)
  have hcut_le : ∀ R x, ‖uPark n w R x‖ ≤ |w x| := by
    intro R x
    rw [Real.norm_eq_abs, uPark, abs_mul]
    have h3 : |cut n R x| ≤ 1 := by
      rw [abs_of_nonneg (cut_nonneg n R x)]; exact cut_le_one n R x
    simpa only [one_mul] using mul_le_mul_of_nonneg_right h3 (abs_nonneg (w x))
  have hI1 : Tendsto (fun R : ℝ => ∫ x in A, uPark n w R x * gDens n x) atTop (𝓝 0) := by
    have h := tendsto_integral_cut_mul n A (fun R x => uPark n w R x) w (fun x => |w x|) hwg
      (Filter.Eventually.of_forall fun R => Filter.Eventually.of_forall fun x => hcut_le R x)
      (Filter.Eventually.of_forall fun x => tendsto_uPark n w x)
      (Filter.Eventually.of_forall fun R =>
        (((contDiff_uPark n w hw R).continuous.mul (continuous_gDens n)).measurable).aestronglyMeasurable)
    rw [hmean] at h
    exact h
  have hcut_fderiv : ∀ R ≥ (1:ℝ), ∀ x, ‖fderiv ℝ (uPark n w R) x‖
      ≤ ‖fderiv ℝ w x‖ + Cc * |w x| := by
    intro R hR x
    rw [fderiv_uPark n w hw R x]
    have h3 : |cut n R x| ≤ 1 := by
      rw [abs_of_nonneg (cut_nonneg n R x)]; exact cut_le_one n R x
    calc ‖cut n R x • fderiv ℝ w x + w x • fderiv ℝ (cut n R) x‖
        ≤ ‖cut n R x • fderiv ℝ w x‖ + ‖w x • fderiv ℝ (cut n R) x‖ := norm_add_le _ _
      _ = |cut n R x| * ‖fderiv ℝ w x‖ + |w x| * ‖fderiv ℝ (cut n R) x‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 1 * ‖fderiv ℝ w x‖ + |w x| * Cc := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
          · exact mul_le_mul_of_nonneg_left (hCc R hR x) (abs_nonneg _)
      _ = ‖fderiv ℝ w x‖ + Cc * |w x| := by ring
  have hIe : Tendsto (fun R : ℝ => ∫ x in A, ‖fderiv ℝ (uPark n w R) x‖ ^ 2 * gDens n x) atTop
      (𝓝 (∫ x in A, ‖fderiv ℝ w x‖ ^ 2 * gDens n x)) :=
    tendsto_integral_cut_mul n A (fun R x => ‖fderiv ℝ (uPark n w R) x‖ ^ 2)
      (fun x => ‖fderiv ℝ w x‖ ^ 2)
      (fun x => 2 * ‖fderiv ℝ w x‖ ^ 2 + 2 * Cc ^ 2 * w x ^ 2) hB
      ((eventually_ge_atTop (1:ℝ)).mono fun R hR => Filter.Eventually.of_forall fun x => by
        have hnorm := hcut_fderiv R hR x
        have hCcnn : 0 ≤ Cc := le_trans (norm_nonneg _) (hCc 1 le_rfl x)
        have h1 : ‖fderiv ℝ (uPark n w R) x‖ ^ 2 ≤ (‖fderiv ℝ w x‖ + Cc * |w x|) ^ 2 := by
          have h0 : 0 ≤ ‖fderiv ℝ (uPark n w R) x‖ := norm_nonneg _
          have h1 : 0 ≤ ‖fderiv ℝ w x‖ + Cc * |w x| := by positivity
          nlinarith [hnorm, h0, h1]
        have h2 : (‖fderiv ℝ w x‖ + Cc * |w x|) ^ 2
            ≤ 2 * ‖fderiv ℝ w x‖ ^ 2 + 2 * Cc ^ 2 * w x ^ 2 := by
          nlinarith [sq_abs (w x), sq_nonneg (‖fderiv ℝ w x‖ - Cc * |w x|)]
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        linarith)
      (Filter.Eventually.of_forall fun x => tendsto_fderiv_uPark_norm_sq n w hw x)
      (Filter.Eventually.of_forall fun R =>
        ((((contDiff_uPark n w hw R).continuous_fderiv (by norm_num)).norm.pow 2).mul
          (continuous_gDens n)).measurable.aestronglyMeasurable)
  -- the cutoff-stage inequality holds eventually
  have hev : ∀ᶠ R in atTop, (∫ x in A, uPark n w R x ^ 2 * gDens n x)
      - (∫ x in A, uPark n w R x * gDens n x) ^ 2 / Z
      ≤ (1 / (2 * Real.pi)) * ∫ x in A, ‖fderiv ℝ (uPark n w R) x‖ ^ 2 * gDens n x := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
    exact bl_cut_stage n A hA hAm hvol hZ w hw hR
  have hL : Tendsto (fun R : ℝ => (∫ x in A, uPark n w R x ^ 2 * gDens n x)
      - (∫ x in A, uPark n w R x * gDens n x) ^ 2 / Z) atTop
      (𝓝 (∫ x in A, w x ^ 2 * gDens n x)) := by
    have h := hI2.sub ((hI1.pow 2).div_const Z)
    simpa only [zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_div, sub_zero] using h
  have hR : Tendsto (fun R : ℝ => (1 / (2 * Real.pi)) *
      ∫ x in A, ‖fderiv ℝ (uPark n w R) x‖ ^ 2 * gDens n x) atTop
      (𝓝 ((1 / (2 * Real.pi)) * ∫ x in A, ‖fderiv ℝ w x‖ ^ 2 * gDens n x)) :=
    hIe.const_mul _
  exact le_of_tendsto_of_tendsto hL hR hev



theorem brascamp_lieb_truncated {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hA : Convex ℝ A) (hAm : MeasurableSet A)
    (hApos : 0 < ∫ x : EuclideanSpace ℝ (Fin n) in A, Real.exp (-Real.pi * ‖x‖ ^ 2))
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 1 w)
    (hw2 : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) =>
        w x ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) A)
    (hg : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) =>
        ‖fderiv ℝ w x‖ ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) A)
    (hmean : (∫ x : EuclideanSpace ℝ (Fin n) in A, w x * Real.exp (-Real.pi * ‖x‖ ^ 2)) = 0) :
    (∫ x : EuclideanSpace ℝ (Fin n) in A, w x ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
      ≤ (1 / (2 * Real.pi)) *
        (∫ x : EuclideanSpace ℝ (Fin n) in A,
          ‖fderiv ℝ w x‖ ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by

  have heq2 : (fun x : EuclideanSpace ℝ (Fin n) => w x ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
      = fun x => w x ^ 2 * gDens n x := by
    funext x; rw [gDens_eq]
  have heqD : (fun x : EuclideanSpace ℝ (Fin n) =>
        ‖fderiv ℝ w x‖ ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
      = fun x => ‖fderiv ℝ w x‖ ^ 2 * gDens n x := by
    funext x; rw [gDens_eq]
  have heqm : (fun x : EuclideanSpace ℝ (Fin n) => w x * Real.exp (-Real.pi * ‖x‖ ^ 2))
      = fun x => w x * gDens n x := by
    funext x; rw [gDens_eq]
  have heqZ : (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-Real.pi * ‖x‖ ^ 2))
      = fun x => gDens n x := by
    funext x; rw [gDens_eq]
  have hvol : 0 < volume A := volume_pos_of_integral_pos n A hAm hApos
  have hZeq : (∫ x in A, gDens n x)
      = ∫ x in A, Real.exp (-Real.pi * ‖x‖ ^ 2) :=
    setIntegral_congr_fun hAm (fun x _ => (congrFun heqZ x).symm)
  have hZ : 0 < ∫ x in A, gDens n x := by
    rw [hZeq]; exact hApos
  have hw2' : Integrable (fun x : EuclideanSpace ℝ (Fin n) => w x ^ 2 * gDens n x)
      (volume.restrict A) :=
    hw2.congr (Filter.Eventually.of_forall fun x => congrFun heq2 x)
  have hg' : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖fderiv ℝ w x‖ ^ 2 * gDens n x)
      (volume.restrict A) :=
    hg.congr (Filter.Eventually.of_forall fun x => congrFun heqD x)
  have hmeq : (∫ x in A, w x * gDens n x) = ∫ x in A, w x * Real.exp (-Real.pi * ‖x‖ ^ 2) :=
    setIntegral_congr_fun hAm (fun x _ => (congrFun heqm x).symm)
  have hmean' : (∫ x in A, w x * gDens n x) = 0 := by
    rw [hmeq]; exact hmean
  have hmain := bl_final n A hA hAm hvol hZ w hw hw2' hg' hmean'
  have hconv2 : (∫ x in A, w x ^ 2 * gDens n x)
      = ∫ x in A, w x ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2) :=
    setIntegral_congr_fun hAm (fun x _ => (congrFun heq2 x).symm)
  have hconvD : (∫ x in A, ‖fderiv ℝ w x‖ ^ 2 * gDens n x)
      = ∫ x in A, ‖fderiv ℝ w x‖ ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2) :=
    setIntegral_congr_fun hAm (fun x _ => (congrFun heqD x).symm)
  rw [hconv2, hconvD] at hmain
  exact hmain




end

end Commons.Analysis.GaussianMeasure

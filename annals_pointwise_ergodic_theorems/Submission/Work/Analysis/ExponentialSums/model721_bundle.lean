import Mathlib
import Submission.Commons.Analysis.CalderonZygmund.cz_shift
import Submission.Commons.Analysis.ExponentialSums.card_small_intDist_residues
import Submission.Commons.Analysis.ExponentialSums.intDist_abs_sub_le
import Submission.Commons.Analysis.ExponentialSums.iterated_differencing_step
import Submission.Commons.Analysis.ExponentialSums.norm_sum_sq_le_shift_conj
import Submission.Commons.Analysis.ExponentialSums.poly_phase_residue_split
import Submission.Commons.Analysis.Fourier.band_limited_reproducing_kernel
import Submission.Commons.Analysis.Fourier.block_maximal_of_separated
import Submission.Commons.Analysis.Fourier.bourgain_entropy_integral_l2_fixed
import Submission.Commons.Analysis.Fourier.finset_bracket_lattice_le
import Submission.Commons.Analysis.Fourier.lintegral_translate_sub_sq_le_of_fourier_support
import Submission.Commons.Analysis.Real.tsum_int_inv_one_add_sq_sub_le
import Submission.Commons.Analysis.Series.harmonic_sum_le_rpow

/-! # BUNDLE: Bourgain §7.2 (Lemma 7.20 / (7.21)) for the squares, in one file.

Concatenation of `model721.lean`, `probeP8.lean`, `model721_slice.lean`, `window_bridge.lean`,
`window_maximal.lean`.  The headline theorem is `window_maximal_lp` at the bottom. -/


/-! ===== concatenated from model721.lean ===== -/

/-
# Bourgain §7.2, Lemma 7.20 (the smooth fixed-window model): the `ℓ^p` maximal bound

This file builds, in a self-contained way (Mathlib + the published commons), the **`1 < p < ∞`
model maximal inequality** of Bourgain's §7.2 — the estimate that the corpus calls hypothesis (A).
It is Lemma 7.20 of

> J. Bourgain, *Pointwise ergodic theorems for arithmetic sets*, Publ. Math. IHÉS **69** (1989), §7,

in the "smooth fixed-window" form in which Bourgain actually states it, and with the
**normalisation that makes the constant uniform in the denominator bound `q`** — the point that the
corpus's earlier `Σ_z c_{z−m}`-route (built on the *Gauss-weighted* residue decomposition) could not
reach.

## The theorem being assembled

For `p > 1`, `q ≥ 1`, `D ≥ q`, a bounded measurable `φ` supported in `[-1/2,1/2]`, a finitely
supported `g : ℤ → ℂ` with periodic transform `G(α) = Σ_j g_j e(2πi j α)` and `Ψ = fresnelProfile`:

`T_N g(m) = Σ_{a<q} ∫_ℝ Ψ(N²β) G(a/q + β) φ(Dβ) e(2πi m (β + a/q)) dβ`

satisfies `∫⁻_m (⨆_N ‖T_N g(m)‖ₑ)^p ∂count ≤ C^p ∫⁻_m ‖g m‖ₑ^p ∂count`, with `C` **independent of
`q` and `D`**.

## The proof route, and the constant bookkeeping (this is the key point)

Write `m = y q + z`, `0 ≤ z < q`.  Then

* (residue identity, §6 below — *no Gauss weights*)
  `Σ_{a<q} e(2πi z a/q) G(a/q + β) = q · F_z(β)`, `F_z(β) = Σ_{j ≡ −z (q)} g_j e(2πi j β)`;
* hence, after eliminating the phase `e(2πi(yq+z)β)` and substituting `γ = q β`,
  `T_N g(yq + z) = ∫_ℝ Ψ((N²/q) γ) · \tilde F_z(γ) · e(2πi y γ) dγ`,
  with `\tilde F_z(γ) = F_z(γ/q) e(2πi z γ/q) φ(Dγ/q)`, supported in `|γ| ≤ q/(2D) ≤ 1/8`;
* **crucially**, `𝓕⁻¹[\tilde F_z](x) = Σ_{j ≡ −z (q)} g_j κ̃(x + (j+z)/q)` where
  `κ̃ = 𝓕⁻¹[φ(D·/q)]` has width `q/D ≤ 1/4`, i.e. **strictly less than the lattice spacing `1`** of
  the points `(j+z)/q ∈ ℤ`.  So the bumps do **not** overlap and
  `∫_ℝ |𝓕⁻¹[\tilde F_z]|^p = (q/D)^{p−1} ‖φ̌‖_p^p · Σ_{j ≡ −z (q)} |g_j|^p`;
  summed over the `q` residue classes (a bijection `{0,…,q−1} × ℤ → ℤ`) this is
  `≤ ‖φ̌‖_p^p · ‖g‖_{ℓ^p}^p`.  **This is where the `q`-uniformity comes from** — a *width* gain
  `(q/D)^{p−1}`, not a Riesz–Thorin or a-priori-bootstrap gain.

Then the three analytic steps, all of which are in this file or in the published commons:

1. the published lattice comparison `lattice_sup_le_integral_sup_band_limited_rpow` applied to the
   (band-limited to `1/8`) family `k ↦ 𝓕⁻¹[\tilde F_z · Ψ((2^k)²/q ·)]`:
   `Σ_y (⨆_k ‖·(y)‖ₑ)^p ≤ C ∫_x (⨆_k ‖·(x)‖ₑ)^p`  — **no `q`-loss**, because the sampling is at the
   *original* (spacing-1) lattice after the substitution `γ = qβ`;
2. §7.1 for a general family of dilation parameters (`fresnel_sup_le_hlMax_param` below, from the
   published `quadratic_kernel_real_maximal_le_hlMax` + the parabolic change of variables
   `lintegral_Ioc_sq_dilation_inv`): `⨆_k ‖·(x)‖ₑ ≤ C · hlMax (‖𝓕⁻¹[\tilde F_z]‖ₑ) x`;
3. the published `L^p` bound for `hlMax` (`lintegral_rpow_hlMax_le`).

## What is proved in this file (no `sorry`)

| lemma | content |
|---|---|
| `lintegral_Ioc_sq_dilation`, `..._inv` | the parabolic change of variables `u = t s²` |
| `quadratic_kernel_real_maximal_minus_s_le_hlMax` | Bourgain (7.16) in the `s`-form (dyadic dilations) |
| `quadratic_kernel_real_maximal_param_le_hlMax` | Bourgain (7.16) for an **arbitrary** family of dilations |
| `fresnel_dilation_pointwise`, `fresnel_dilation_average_neg` | `𝓕⁻¹[W · Ψ(−a·)](x) = ∫₀¹ 𝓕⁻¹[W](x − a s²) ds` |
| `continuous_invTransform` | continuity of the inverse transform of an integrable amplitude |
| `fresnel_sup_le_hlMax_uniform`, `fresnel_sup_le_hlMax_param` | (7.26): the Fresnel-dilation maximal function is `≤ C · hlMax` of the inverse transform, uniformly in the amplitude and in the dilation family |
| `sum_range_exp_two_pi_I_div_eq_ite`, `residue_sum_identity` | the residue identity (7.23), **without Gauss weights** |
| `fourier_comp_mul_left` | the missing Mathlib fact `𝓕(f(c·))(ξ) = c⁻¹𝓕f(ξ/c)` |
| `lintegral_comp_mul_left'` | the `∫⁻` change of variables `x ↦ q x` |
| `sublattice_sup_le_integral_sup_rpow` | the sharp sub-lattice sampling bound, with the density gain `q⁻¹` |

## The width gain, in the form used

The remaining ingredients are now also in place.  With `a = q/D ≤ 1` and `κ̃ = a·φ̌(a·)` (the inverse
transform of `φ(D·/q)`), the key facts are

* (`lattice_kernel_sum_le`) `Σ_{j ∈ s} ‖κ̃ (x − j)‖ₑ ≤ 2C(1 + π/2)`, uniform in `x` and in `s`,
  where `C` is the Schwartz decay constant of `φ̌` — this is the *width gain*: the lattice sum of the
  dilated bump is bounded uniformly, because `κ̃` is a bump of width `D/q ≥ 1`;
* (`lintegral_conv_finset_rpow_le`) the Hölder/Tonelli bound
  `∫⁻_x (‖Σ_j g_j κ (x − j)‖ₑ)^p ≤ A^{p-1} (∫⁻ ‖κ‖) (Σ_j ‖g_j‖ₑ^p)`
  whenever `Σ_{j∈s}‖κ(x−j)‖ₑ ≤ A` uniformly in `x`;
* (`schwartz_decay`) the Schwartz decay `‖Φ u‖ ≤ C(1 + u²)⁻¹`;
* (`finset_sum_inv_one_add_sq_step_le` and its companions) the elementary Cauchy-kernel lattice sums.

## State of the assembly (all of the following are proved, no `sorry`)

| block | lemmas |
|---|---|
| §7.1 with general dilations | `quadratic_kernel_real_maximal_minus_s_le_hlMax`, `quadratic_kernel_real_maximal_param_le_hlMax` |
| Fresnel dilation average | `fresnel_dilation_pointwise`, `fresnel_dilation_average_neg`, `continuous_invTransform` |
| (7.26): Fresnel sup ≤ `hlMax` | `fresnel_sup_le_hlMax_uniform`, `fresnel_sup_le_hlMax_param` |
| residue identity (7.23) | `sum_range_exp_two_pi_I_div_eq_ite`, `residue_sum_identity` |
| Fourier scaling & the sharp sub-lattice sampling | `fourier_comp_mul_left`, `lintegral_comp_mul_left'`, `sublattice_sup_le_integral_sup_rpow` |
| the width-gain mechanism | `lintegral_conv_finset_rpow_le`, `lattice_kernel_sum_le` |
| Cauchy-kernel lattice sums | `sum_range_inv_one_add_sq_mul_le`, `tsum_nat_inv_one_add_sq_mul_le`, `summable_nat_inv_one_add_sq_mul`, `finset_sum_inv_one_add_sq_step_le` |
| Schwartz decay | `schwartz_decay`, `fourierInv_decay`, `lintegral_norm_dilate_eq` |
| the per-residue-class bound (steps 1–2) | `residue_slice_bound` |
| the residue-class summation (step 4) | `filter_residue_singleton`, `sum_filter_residue_le` |

**Remaining (the final section's target).**  With `a = q/D`, `Φ = 𝓕⁻¹φ` (so `κ̃ = a·Φ(a·)`), `G_z`
the sliced amplitude and `J_z = 𝓕⁻¹[G_z] = Σ_{j ≡ −z (q)} g_j κ̃(· + (j+z)/q)`, the composition

```
Σ_z ∫⁻_y (⨆_k ‖h_z k (y)‖ₑ)^p                                     [h_z k = the Fresnel-dilation family]
  ≤ Σ_z C ∫⁻_x (⨆_k ‖h_z k (x)‖ₑ)^p        (published lattice comparison; needs `Integrable`,
                                             `Continuous` and band-limitedness of `h_z k`, the last
                                             from `Integrable.fourier_fourierInv_eq` for the smooth
                                             compactly-supported `G_z`)
  ≤ Σ_z C'' ∫⁻_x (‖J_z x‖ₑ)^p               (`fresnel_sup_le_hlMax_param` + `lintegral_rpow_hlMax_le`)
  ≤ Σ_z C'' A^{p−1} ‖Φ‖₁ Σ_{j ∈ filter z} ‖g_j‖ₑ^p     (`residue_slice_bound`)
  ≤ C'' A^{p-1} ‖Φ‖₁ Σ_j ‖g_j‖ₑ^p            (`sum_filter_residue_le`),
```
which is the `ℓ^p` maximal bound for the smooth fixed-window model — Bourgain's Lemma 7.20.

The remaining steps 1–3 of the route above are the subject of the final section: the residue
identification (step 1), the application of `lintegral_conv_finset_rpow_le` to the sliced amplitudes
(step 2), the maximal bound through `fresnel_sup_le_hlMax_param` + `lintegral_rpow_hlMax_le`
(step 3), and the summation over the `q` residue classes (step 4).
-/


open MeasureTheory Finset
open scoped BigOperators ENNReal FourierTransform

namespace Commons.Analysis.ExponentialSums

noncomputable section


/-! ## §1. The parabolic change of variables `u = t s²` in `∫⁻` -/

/-- `s ↦ t * s ^ 2` on `(0,1]` has image `(0,t]` for `t > 0`. -/
private lemma image_sq_Ioc (t : ℝ) (ht : 0 < t) :
    (fun s : ℝ => t * s ^ 2) '' Set.Ioc (0:ℝ) 1 = Set.Ioc (0:ℝ) t := by
  ext u
  constructor
  · rintro ⟨s, ⟨hs0, hs1⟩, rfl⟩
    refine ⟨mul_pos ht (pow_pos hs0 2), ?_⟩
    have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs0.le, hs1]
    calc t * s ^ 2 ≤ t * 1 := mul_le_mul_of_nonneg_left hs2 ht.le
      _ = t := mul_one t
  · intro hu
    refine ⟨Real.sqrt (u / t), ⟨?_, ?_⟩, ?_⟩
    · exact Real.sqrt_pos.mpr (div_pos hu.1 ht)
    · rw [Real.sqrt_le_one, div_le_one ht]; exact hu.2
    · show t * (Real.sqrt (u / t)) ^ 2 = u
      rw [Real.sq_sqrt (div_nonneg hu.1.le ht.le)]
      field_simp

/-- **The parabolic change of variables.**  For `t > 0` and any `g : ℝ → ℝ≥0∞`,
`∫_{(0,t]} g u (√u)⁻¹ du = 2√t · ∫_{(0,1]} g (t s²) ds`. -/
theorem lintegral_Ioc_sq_dilation {t : ℝ} (ht : 0 < t) (g : ℝ → ℝ≥0∞) :
    ∫⁻ u in Set.Ioc (0:ℝ) t, g u * ENNReal.ofReal ((Real.sqrt u)⁻¹)
      = ENNReal.ofReal (2 * Real.sqrt t) * ∫⁻ s in Set.Ioc (0:ℝ) 1, g (t * s ^ 2) := by
  have hs : MeasurableSet (Set.Ioc (0:ℝ) 1) := measurableSet_Ioc
  have hderiv : ∀ x ∈ Set.Ioc (0:ℝ) 1,
      HasDerivWithinAt (fun s : ℝ => t * s ^ 2) (2 * t * x) (Set.Ioc (0:ℝ) 1) x := by
    intro x _
    have h : HasDerivAt (fun s : ℝ => t * s ^ 2) (t * (2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_mul t
    have h2 : t * (2 * x) = 2 * t * x := by ring
    rw [h2] at h
    exact h.hasDerivWithinAt
  have hinj : Set.InjOn (fun s : ℝ => t * s ^ 2) (Set.Ioc (0:ℝ) 1) := by
    intro a ha b hb hab
    have h1 : a ^ 2 = b ^ 2 := by
      have h2 := mul_left_cancel₀ (ne_of_gt ht) hab
      simpa using h2
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
    · exact h
    · exfalso
      have ha0 : (0:ℝ) < a := ha.1
      have hb0 : (0:ℝ) < b := hb.1
      linarith
  have hchange := lintegral_image_eq_lintegral_abs_deriv_mul hs hderiv hinj
    (fun u : ℝ => g u * ENNReal.ofReal ((Real.sqrt u)⁻¹))
  rw [image_sq_Ioc t ht] at hchange
  rw [hchange]
  have key : ∀ x ∈ Set.Ioc (0:ℝ) 1,
      ENNReal.ofReal (|2 * t * x|) * ENNReal.ofReal ((Real.sqrt (t * x ^ 2))⁻¹)
        = ENNReal.ofReal (2 * Real.sqrt t) := by
    intro x hx
    have hx0 : 0 < x := hx.1
    rw [← ENNReal.ofReal_mul (abs_nonneg (2 * t * x))]
    congr 1
    rw [abs_of_pos (by positivity : (0:ℝ) < 2 * t * x), Real.sqrt_mul ht.le, Real.sqrt_sq hx0.le]
    have htne : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ht)
    field_simp
    rw [Real.sq_sqrt ht.le]
  have hpt : ∀ x ∈ Set.Ioc (0:ℝ) 1,
      ENNReal.ofReal (|2 * t * x|) * (g (t * x ^ 2) * ENNReal.ofReal ((Real.sqrt (t * x ^ 2))⁻¹))
        = ENNReal.ofReal (2 * Real.sqrt t) * g (t * x ^ 2) := by
    intro x hx
    rw [mul_comm (g (t * x ^ 2)) (ENNReal.ofReal ((Real.sqrt (t * x ^ 2))⁻¹)), ← mul_assoc,
      key x hx]
  calc ∫⁻ x in Set.Ioc (0:ℝ) 1,
        ENNReal.ofReal (|2 * t * x|) * (g (t * x ^ 2) * ENNReal.ofReal ((Real.sqrt (t * x ^ 2))⁻¹))
      = ∫⁻ x in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (2 * Real.sqrt t) * g (t * x ^ 2) :=
        setLIntegral_congr_fun measurableSet_Ioc hpt
    _ = ENNReal.ofReal (2 * Real.sqrt t) * ∫⁻ x in Set.Ioc (0:ℝ) 1, g (t * x ^ 2) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The normalized form of `lintegral_Ioc_sq_dilation`. -/
theorem lintegral_Ioc_sq_dilation_inv {t : ℝ} (ht : 0 < t) (g : ℝ → ℝ≥0∞) :
    ∫⁻ s in Set.Ioc (0:ℝ) 1, g (t * s ^ 2)
      = (ENNReal.ofReal (2 * Real.sqrt t))⁻¹ *
        ∫⁻ u in Set.Ioc (0:ℝ) t, g u * ENNReal.ofReal ((Real.sqrt u)⁻¹) := by
  have hc0 : ENNReal.ofReal (2 * Real.sqrt t) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]; positivity
  have hct : ENNReal.ofReal (2 * Real.sqrt t) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [lintegral_Ioc_sq_dilation ht g, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

/-- `4^k = (2^k)²`. -/
private lemma four_pow_eq_sq (k : ℕ) : (4:ℝ)^k = ((2:ℝ)^k)^2 := by
  rw [show (4:ℝ) = 2^2 by norm_num, ← pow_mul, ← pow_mul]
  ring_nf

/-! ## §2. The `s`-form of the real-variable maximal inequality (§7.1, `−` sign) -/

/-! ## §3. The Fresnel dilation average -/

/-- The inverse transform of a (complex) amplitude is continuous when the amplitude is integrable. -/
theorem continuous_invTransform (W : ℝ → ℂ) (hW : Integrable W) :
    Continuous (fun y : ℝ => ∫ β : ℝ, W β * Complex.exp (2 * Real.pi * Complex.I * y * β)) := by
  refine continuous_of_dominated
    (F := fun y : ℝ => fun β : ℝ => W β * Complex.exp (2 * Real.pi * Complex.I * y * β))
    (bound := fun β : ℝ => ‖W β‖) ?_ ?_ hW.norm ?_
  · intro y
    exact hW.aestronglyMeasurable.mul
      (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  · intro y
    filter_upwards with β
    rw [norm_mul,
      show 2 * Real.pi * Complex.I * y * β = ((2 * Real.pi * y * β : ℝ) : ℂ) * Complex.I by
        push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  · filter_upwards with β
    fun_prop

/-! ## §6. The residue (Poisson) identity of §7.2

`Σ_{0≤a<q} e(2πi z a/q) G(a/q + β) = q · Σ_{j ≡ −z (mod q)} g_j e(2πi j β)`,
which is the mechanism turning the `a`-sum of (7.21) into the residue slices `x = yq + z` of
(7.22).  Unlike the corpus's `blockAmplitude_eq_residue_sum` this identity carries **no Gauss
weights**, which is the normalisation that makes the bound uniform in `q`.
-/

/-- Character orthogonality on `ℤ/q`. -/
theorem sum_range_exp_two_pi_I_div_eq_ite (q : ℕ) (z : ℤ) :
    (∑ a ∈ Finset.range q, Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (z : ℂ) / (q : ℂ))))
      = if (q : ℤ) ∣ z then (q : ℂ) else 0 := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq; simp
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  set w : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((z : ℂ) / (q : ℂ))) with hwdef
  have hab : ∀ a : ℕ,
      Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (z : ℂ) / (q : ℂ))) = w ^ a := by
    intro a
    rw [show 2 * Real.pi * Complex.I * ((a : ℂ) * (z : ℂ) / (q : ℂ))
        = 2 * Real.pi * Complex.I * (a : ℂ) * ((z : ℂ) / (q : ℂ)) by ring,
      hwdef, ← Complex.exp_nat_mul]
    congr 1
    ring
  have hwq : w ^ q = 1 := by
    rw [hwdef, ← Complex.exp_nat_mul]
    have hzc : (q : ℂ) * (2 * Real.pi * Complex.I * ((z : ℂ) / (q : ℂ)))
        = (z : ℂ) * (2 * Real.pi * Complex.I) := by
      field_simp
    rw [hzc, Complex.exp_int_mul_two_pi_mul_I]
  simp only [hab]
  by_cases hd : (q : ℤ) ∣ z
  · rw [if_pos hd]
    have hw1 : w = 1 := by
      obtain ⟨n, hn⟩ := hd
      rw [hwdef, hn]
      push_cast
      rw [show 2 * Real.pi * Complex.I * ((q : ℂ) * (n : ℂ) / (q : ℂ))
          = (n : ℂ) * (2 * Real.pi * Complex.I) by
        field_simp,
        Complex.exp_int_mul_two_pi_mul_I]
    rw [hw1]
    simp
  · rw [if_neg hd]
    have hw1 : w ≠ 1 := by
      intro h
      apply hd
      rw [hwdef] at h
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
      have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
      have h2 : (z : ℂ) / (q : ℂ) = (n : ℂ) := by
        rw [mul_comm ((2:ℂ) * ↑Real.pi * Complex.I) ((z:ℂ)/(q:ℂ))] at hn
        exact mul_right_cancel₀ hne hn
      have h3 : (z : ℂ) = (n : ℂ) * (q : ℂ) := (div_eq_iff hqC).mp h2
      have h4 : (z : ℂ) = (((q : ℤ) * n : ℤ) : ℂ) := by rw [h3]; push_cast; ring
      exact ⟨n, by exact_mod_cast h4⟩
    rw [geom_sum_eq hw1 q, hwq]
    simp

/-- **The residue identity (Bourgain (7.23)).**  For `q ≥ 1`, a finite index set `s ⊆ ℤ`, a
coefficient sequence `g` and `z : ℤ`,

`Σ_{0≤a<q} e(2πi z a/q) · Σ_{j∈s} g_j e(2πi j (a/q + β)) = q · Σ_{j∈s, q ∣ z+j} g_j e(2πi j β)`. -/
theorem residue_sum_identity (q : ℕ) (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) (β : ℝ) :
    (∑ a ∈ Finset.range q,
        Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (z : ℂ) / (q : ℂ))) *
        (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I *
          ((j : ℂ) * ((((a : ℝ) / (q : ℝ) + β : ℝ)) : ℂ)))))
      = (q : ℂ) * ∑ j ∈ s.filter (fun j => (q : ℤ) ∣ (z + j)),
          g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (β : ℂ))) := by
  have hterm : ∀ a : ℕ,
      Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (z : ℂ) / (q : ℂ))) *
        (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I *
          ((j : ℂ) * ((((a : ℝ) / (q : ℝ) + β : ℝ)) : ℂ))))
      = ∑ j ∈ s, Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * ((z + j : ℤ) : ℂ) / (q : ℂ))) *
          (g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (β : ℂ)))) := by
    intro a
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have key : Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (z : ℂ) / (q : ℂ))) *
          Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * ((((a : ℝ) / (q : ℝ) + β : ℝ)) : ℂ)))
        = Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * ((z + j : ℤ) : ℂ) / (q : ℂ))) *
          Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (β : ℂ))) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (z : ℂ) / (q : ℂ))) *
          (g j * Complex.exp (2 * Real.pi * Complex.I *
            ((j : ℂ) * ((((a : ℝ) / (q : ℝ) + β : ℝ)) : ℂ))))
        = g j * (Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (z : ℂ) / (q : ℂ))) *
            Complex.exp (2 * Real.pi * Complex.I *
              ((j : ℂ) * ((((a : ℝ) / (q : ℝ) + β : ℝ)) : ℂ)))) := by ring
      _ = g j * (Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * ((z + j : ℤ) : ℂ) / (q : ℂ))) *
            Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (β : ℂ)))) := by rw [key]
      _ = Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * ((z + j : ℤ) : ℂ) / (q : ℂ))) *
          (g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (β : ℂ)))) := by ring
  rw [Finset.sum_congr rfl (fun a _ => hterm a), Finset.sum_comm, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_mul, sum_range_exp_two_pi_I_div_eq_ite q (z + j)]
  by_cases h : (q : ℤ) ∣ (z + j)
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, zero_mul]


/-! ## §5. Dilation of the Fourier transform and the sharp sub-lattice sampling bound -/

/-- **Dilation of the Fourier transform**: `𝓕(f(c·))(ξ) = c⁻¹·𝓕f(ξ/c)` for `c > 0`. -/
theorem fourier_comp_mul_left (f : ℝ → ℂ) {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    FourierTransform.fourier (fun x : ℝ => f (c * x)) ξ
      = ((c : ℂ))⁻¹ * FourierTransform.fourier f (ξ / c) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  set g : ℝ → ℂ := fun y => Real.fourierChar (-((y/c) * ξ)) • f y with hg
  have h1 : (∫ v : ℝ, Real.fourierChar (-(v * ξ)) • f (c * v)) = ∫ v : ℝ, g (c * v) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [hg]
    congr 2
    field_simp
  rw [h1]
  have h2 := Measure.integral_comp_mul_left g c
  rw [h2, abs_of_pos (inv_pos.mpr hc)]
  simp only [hg]
  rw [show (fun y : ℝ => Real.fourierChar (-(y / c * ξ)) • f y)
      = fun y : ℝ => Real.fourierChar (-(y * (ξ / c))) • f y from by
    funext y; congr 2; ring]
  rw [Complex.real_smul, Complex.ofReal_inv]

/-- **Change of variables `x ↦ q x` for `∫⁻` on `ℝ`.** -/
theorem lintegral_comp_mul_left' {q : ℕ} (hq : 0 < q) {F : ℝ → ENNReal} (hF : Measurable F) :
    ∫⁻ x : ℝ, F ((q:ℝ) * x) = ENNReal.ofReal ((q:ℝ))⁻¹ * ∫⁻ y : ℝ, F y := by
  rw [← lintegral_map (f := F) hF (by fun_prop : Measurable fun x : ℝ => (q:ℝ) * x)]
  rw [Real.map_volume_mul_left (by exact_mod_cast hq.ne' : (q:ℝ) ≠ 0)]
  rw [lintegral_smul_measure, abs_of_pos (by positivity : (0:ℝ) < ((q:ℝ))⁻¹), smul_eq_mul]

/-! ## §7. The lattice convolution bound (the width gain of §7.2) -/

theorem lintegral_conv_finset_rpow_le {p : ℝ} (hp : 1 < p) {κ : ℝ → ℂ} (hκ : Measurable κ)
    {g : ℤ → ℂ} (s : Finset ℤ) (A : ℝ≥0∞)
    (hA : ∀ x : ℝ, ∑ j ∈ s, ‖κ (x - (j:ℝ))‖ₑ ≤ A) :
    ∫⁻ x : ℝ, (‖∑ j ∈ s, g j * κ (x - (j:ℝ))‖ₑ) ^ p
      ≤ A ^ (p - 1) * (∫⁻ y : ℝ, ‖κ y‖ₑ) * (∑ j ∈ s, ‖g j‖ₑ ^ p) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hp1 : 0 ≤ p - 1 := by linarith
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hp1ne : p - 1 ≠ 0 := by linarith
  have hconj : p.HolderConjugate (p / (p - 1)) := by
    rw [Real.holderConjugate_iff]
    refine ⟨hp, ?_⟩
    field_simp
    ring
  have hpo : (1:ℝ)/p * p = 1 := by rw [one_div, inv_mul_cancel₀ hpne]
  have hpo2 : (p - 1)/p * p = p - 1 := by field_simp
  have hpo3 : (1:ℝ)/(p/(p-1)) = (p-1)/p := one_div_div p (p-1)
  have hmul : ∀ (c z : ℝ≥0∞), (c * z ^ (1/p)) ^ p = c ^ p * z := by
    intro c z
    by_cases hz : z = 0
    · rw [hz, ENNReal.zero_rpow_of_pos (by positivity : (0:ℝ) < 1/p), mul_zero,
        ENNReal.zero_rpow_of_pos hp0, mul_zero]
    · rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0:ℝ) ≤ p), ← ENNReal.rpow_mul, hpo,
        ENNReal.rpow_one]
  have hpow : ∀ (z : ℝ≥0∞), (z ^ ((p-1)/p)) ^ (p/(p-1)) = z := by
    intro z
    rw [← ENNReal.rpow_mul, show (p-1)/p * (p/(p-1)) = 1 by
      rw [div_mul_div_comm, mul_comm (p-1) p, div_self (mul_ne_zero hpne hp1ne)],
      ENNReal.rpow_one]
  have hpt : ∀ x : ℝ, (‖∑ j ∈ s, g j * κ (x - (j:ℝ))‖ₑ) ^ p
      ≤ A ^ (p - 1) * (∑ j ∈ s, ‖g j‖ₑ ^ p * ‖κ (x - (j:ℝ))‖ₑ) := by
    intro x
    have hsum_le : ‖∑ j ∈ s, g j * κ (x - (j:ℝ))‖ₑ
        ≤ ∑ j ∈ s, ‖g j‖ₑ * ‖κ (x - (j:ℝ))‖ₑ := by
      refine le_trans (enorm_sum_le _ _) (le_of_eq ?_)
      exact Finset.sum_congr rfl (fun j _ => by rw [enorm_mul])
    have hholder := ENNReal.inner_le_Lp_mul_Lq s
      (fun j => ‖g j‖ₑ * ‖κ (x - (j:ℝ))‖ₑ ^ (1/p))
      (fun j => ‖κ (x - (j:ℝ))‖ₑ ^ ((p-1)/p)) hconj
    have hleft : ∑ j ∈ s, (‖g j‖ₑ * ‖κ (x - (j:ℝ))‖ₑ ^ (1/p))
          * (‖κ (x - (j:ℝ))‖ₑ ^ ((p-1)/p))
        = ∑ j ∈ s, ‖g j‖ₑ * ‖κ (x - (j:ℝ))‖ₑ := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases hz : ‖κ (x - (j:ℝ))‖ₑ = 0
      · rw [hz, ENNReal.zero_rpow_of_pos (by positivity : (0:ℝ) < 1/p),
          ENNReal.zero_rpow_of_pos (by positivity : (0:ℝ) < (p-1)/p)]
        simp
      · rw [mul_assoc, ← ENNReal.rpow_add (1/p) ((p-1)/p) hz (by finiteness),
          show 1/p + (p-1)/p = 1 by
            rw [← add_div, show 1 + (p-1) = p by ring, div_self hpne], ENNReal.rpow_one]
    have hA1 : (∑ j ∈ s, (‖g j‖ₑ * ‖κ (x - (j:ℝ))‖ₑ ^ (1/p)) ^ p)
        = ∑ j ∈ s, ‖g j‖ₑ ^ p * ‖κ (x - (j:ℝ))‖ₑ :=
      Finset.sum_congr rfl (fun j _ => hmul _ _)
    have hA2 : (∑ j ∈ s, (‖κ (x - (j:ℝ))‖ₑ ^ ((p-1)/p)) ^ (p/(p-1)))
        = ∑ j ∈ s, ‖κ (x - (j:ℝ))‖ₑ :=
      Finset.sum_congr rfl (fun j _ => hpow _)
    have h1 : (∑ j ∈ s, ‖g j‖ₑ * ‖κ (x - (j:ℝ))‖ₑ)
        ≤ (∑ j ∈ s, ‖g j‖ₑ ^ p * ‖κ (x - (j:ℝ))‖ₑ) ^ (1/p)
          * (∑ j ∈ s, ‖κ (x - (j:ℝ))‖ₑ) ^ ((p-1)/p) := by
      calc (∑ j ∈ s, ‖g j‖ₑ * ‖κ (x - (j:ℝ))‖ₑ)
          = ∑ j ∈ s, (‖g j‖ₑ * ‖κ (x - (j:ℝ))‖ₑ ^ (1/p))
              * (‖κ (x - (j:ℝ))‖ₑ ^ ((p-1)/p)) := hleft.symm
        _ ≤ (∑ j ∈ s, (‖g j‖ₑ * ‖κ (x - (j:ℝ))‖ₑ ^ (1/p)) ^ p) ^ (1/p)
              * (∑ j ∈ s, (‖κ (x - (j:ℝ))‖ₑ ^ ((p-1)/p)) ^ (p/(p-1))) ^ (1/(p/(p-1))) := hholder
        _ = (∑ j ∈ s, ‖g j‖ₑ ^ p * ‖κ (x - (j:ℝ))‖ₑ) ^ (1/p)
              * (∑ j ∈ s, ‖κ (x - (j:ℝ))‖ₑ) ^ ((p-1)/p) := by rw [hA1, hA2, hpo3]
    have h2 : ((∑ j ∈ s, ‖g j‖ₑ ^ p * ‖κ (x - (j:ℝ))‖ₑ) ^ (1/p)
          * (∑ j ∈ s, ‖κ (x - (j:ℝ))‖ₑ) ^ ((p-1)/p)) ^ p
        = (∑ j ∈ s, ‖g j‖ₑ ^ p * ‖κ (x - (j:ℝ))‖ₑ)
          * (∑ j ∈ s, ‖κ (x - (j:ℝ))‖ₑ) ^ (p - 1) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
      rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      rw [hpo, hpo2, ENNReal.rpow_one]
    calc (‖∑ j ∈ s, g j * κ (x - (j:ℝ))‖ₑ) ^ p
        ≤ (∑ j ∈ s, ‖g j‖ₑ * ‖κ (x - (j:ℝ))‖ₑ) ^ p := ENNReal.rpow_le_rpow hsum_le hp0.le
      _ ≤ ((∑ j ∈ s, ‖g j‖ₑ ^ p * ‖κ (x - (j:ℝ))‖ₑ) ^ (1/p)
            * (∑ j ∈ s, ‖κ (x - (j:ℝ))‖ₑ) ^ ((p-1)/p)) ^ p :=
            ENNReal.rpow_le_rpow h1 hp0.le
      _ = (∑ j ∈ s, ‖g j‖ₑ ^ p * ‖κ (x - (j:ℝ))‖ₑ)
            * (∑ j ∈ s, ‖κ (x - (j:ℝ))‖ₑ) ^ (p - 1) := h2
      _ ≤ (∑ j ∈ s, ‖g j‖ₑ ^ p * ‖κ (x - (j:ℝ))‖ₑ) * A ^ (p - 1) :=
            mul_le_mul_right (ENNReal.rpow_le_rpow (hA x) hp1) _
      _ = A ^ (p - 1) * (∑ j ∈ s, ‖g j‖ₑ ^ p * ‖κ (x - (j:ℝ))‖ₑ) := by ring
  have hmeas : Measurable (fun x : ℝ => ∑ j ∈ s, ‖g j‖ₑ ^ p * ‖κ (x - (j:ℝ))‖ₑ) :=
    Finset.measurable_sum s (fun j _ => Measurable.const_mul
      (hκ.comp (measurable_id.sub measurable_const)).enorm _)
  calc ∫⁻ x : ℝ, (‖∑ j ∈ s, g j * κ (x - (j:ℝ))‖ₑ) ^ p
      ≤ ∫⁻ x : ℝ, A ^ (p - 1) * (∑ j ∈ s, ‖g j‖ₑ ^ p * ‖κ (x - (j:ℝ))‖ₑ) :=
        lintegral_mono hpt
    _ = A ^ (p - 1) * ∫⁻ x : ℝ, (∑ j ∈ s, ‖g j‖ₑ ^ p * ‖κ (x - (j:ℝ))‖ₑ) :=
        lintegral_const_mul _ hmeas
    _ = A ^ (p - 1) * ∑ j ∈ s, ‖g j‖ₑ ^ p * ∫⁻ x : ℝ, ‖κ (x - (j:ℝ))‖ₑ := by
        have hms : ∀ j ∈ s, Measurable (fun x : ℝ => ‖g j‖ₑ ^ p * ‖κ (x - (j:ℝ))‖ₑ) :=
          fun j _ => Measurable.const_mul
            (hκ.comp (measurable_id.sub measurable_const)).enorm _
        congr 1
        rw [lintegral_finsetSum s hms]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [lintegral_const_mul' (‖g j‖ₑ ^ p) (fun x : ℝ => ‖κ (x - (j:ℝ))‖ₑ) (by finiteness)]
    _ = A ^ (p - 1) * ∑ j ∈ s, ‖g j‖ₑ ^ p * ∫⁻ y : ℝ, ‖κ y‖ₑ := by
        congr 1
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [lintegral_sub_right_eq_self (fun y : ℝ => ‖κ y‖ₑ) (j:ℝ)]
    _ = A ^ (p - 1) * (∫⁻ y : ℝ, ‖κ y‖ₑ) * (∑ j ∈ s, ‖g j‖ₑ ^ p) := by
        rw [← Finset.sum_mul, mul_comm (∑ i ∈ s, ‖g i‖ₑ ^ p) (∫⁻ y : ℝ, ‖κ y‖ₑ), mul_assoc]

/-! ## §8. The elementary lattice-sum bounds for the width gain, and the model target -/

theorem sum_range_inv_one_add_sq_mul_le {a : ℝ} (ha : 0 < a) (N : ℕ) :
    ∑ m ∈ Finset.range (N+1), (1 + (a * (m:ℝ))^2)⁻¹ ≤ 1 + Real.pi / (2 * a) := by
  have hcont : Continuous (fun u : ℝ => (1 + u^2)⁻¹) :=
    Continuous.inv₀ (by fun_prop) (fun u => by positivity)
  have hint : ∀ m : ℕ, 1 ≤ m → (1 + (a * (m:ℝ))^2)⁻¹
      ≤ a⁻¹ * ∫ u in (a * ((m:ℝ) - 1))..(a * (m:ℝ)), (1 + u^2)⁻¹ := by
    intro m hm
    have hmR : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    have hmono : ∀ u ∈ Set.Icc (a * ((m:ℝ)-1)) (a * (m:ℝ)), (1 + (a*(m:ℝ))^2)⁻¹ ≤ (1+u^2)⁻¹ := by
      intro u hu
      simp only [Set.mem_Icc] at hu
      have h1 : (0:ℝ) ≤ a * ((m:ℝ) - 1) := by nlinarith [ha, hmR]
      have h2 : u^2 ≤ (a*(m:ℝ))^2 := by nlinarith [hu.1, hu.2, h1, abs_nonneg u]
      have h3 : (0:ℝ) < 1 + (a*(m:ℝ))^2 := by positivity
      have h4 : (0:ℝ) < 1 + u^2 := by positivity
      rw [inv_le_inv₀ h3 h4]; linarith
    have hlen : a * (m:ℝ) - a * ((m:ℝ) - 1) = a := by ring
    have hconst : ∫ u in (a * ((m:ℝ) - 1))..(a * (m:ℝ)), (1 + (a*(m:ℝ))^2)⁻¹
        = a * (1 + (a*(m:ℝ))^2)⁻¹ := by
      rw [intervalIntegral.integral_const, hlen, smul_eq_mul]
    calc (1 + (a * (m:ℝ))^2)⁻¹
        = a⁻¹ * (a * (1 + (a*(m:ℝ))^2)⁻¹) := by field_simp
      _ ≤ a⁻¹ * ∫ u in (a * ((m:ℝ)-1))..(a*(m:ℝ)), (1 + u^2)⁻¹ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← hconst]
          exact intervalIntegral.integral_mono_on (by nlinarith [ha, hmR])
            intervalIntegrable_const (hcont.intervalIntegrable (a * ((m:ℝ) - 1)) (a * (m:ℝ))) hmono
  have htel : ∑ m ∈ Finset.range N,
      ∫ u in (a * (m:ℝ))..(a * ((m:ℝ)+1)), (1 + u^2)⁻¹ = ∫ u in (0:ℝ)..(a * (N:ℝ)), (1 + u^2)⁻¹ := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (f := fun u : ℝ => (1 + u^2)⁻¹) (a := fun k : ℕ => a * (k:ℝ)) (n := N)
      (fun k _ => hcont.intervalIntegrable (μ := volume) _ _)
    simpa using h
  rw [Finset.sum_range_succ']
  have h0 : (1 + (a * (((0:ℕ)):ℝ))^2)⁻¹ = 1 := by norm_num
  rw [h0]
  have hstep : (∑ m ∈ Finset.range N, (1 + (a * (((m+1:ℕ)):ℝ))^2)⁻¹)
      ≤ a⁻¹ * ∑ m ∈ Finset.range N, ∫ u in (a*(m:ℝ))..(a*((m:ℝ)+1)), (1 + u^2)⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun m _ => ?_)
    have h := hint (m+1) (by omega : 1 ≤ m+1)
    have hc : (((m+1:ℕ)):ℝ) = (m:ℝ) + 1 := by push_cast; ring
    rw [hc] at h ⊢
    simpa only [add_sub_cancel_right] using h
  rw [htel, integral_inv_one_add_sq, Real.arctan_zero, sub_zero] at hstep
  have hle : Real.arctan (a * (N:ℝ)) ≤ Real.pi / 2 := le_of_lt (Real.arctan_lt_pi_div_two _)
  have h2 : a⁻¹ * Real.arctan (a*(N:ℝ)) ≤ a⁻¹ * (Real.pi/2) :=
    mul_le_mul_of_nonneg_left hle (by positivity)
  have h3 : 1 + a⁻¹ * (Real.pi/2) = 1 + Real.pi/(2*a) := by field_simp
  linarith

theorem tsum_nat_inv_one_add_sq_mul_le {a : ℝ} (ha : 0 < a) :
    ∑' m : ℕ, (1 + (a * (m:ℝ))^2)⁻¹ ≤ 1 + Real.pi / (2 * a) := by
  refine Real.tsum_le_of_sum_le (fun m => by positivity) (fun u => ?_)
  obtain ⟨N, hN⟩ : ∃ N, ∀ m ∈ u, m ≤ N := ⟨u.sup id, fun m hm => Finset.le_sup (f := id) hm⟩
  exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg
    (fun m hm => Finset.mem_range.mpr (Nat.lt_succ_of_le (hN m hm)))
    (fun m _ _ => by positivity)) (sum_range_inv_one_add_sq_mul_le ha N)

theorem summable_nat_inv_one_add_sq_mul {a : ℝ} (ha : 0 < a) :
    Summable (fun m : ℕ => (1 + (a * (m:ℝ))^2)⁻¹) := by
  refine summable_of_sum_le (c := 1 + Real.pi / (2 * a)) (fun m => by positivity) (fun u => ?_)
  obtain ⟨N, hN⟩ : ∃ N, ∀ m ∈ u, m ≤ N := ⟨u.sup id, fun m hm => Finset.le_sup (f := id) hm⟩
  exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg
    (fun m hm => Finset.mem_range.mpr (Nat.lt_succ_of_le (hN m hm)))
    (fun m _ _ => by positivity)) (sum_range_inv_one_add_sq_mul_le ha N)

theorem finset_sum_inv_one_add_sq_step_le {a : ℝ} (ha : 0 < a) (x : ℝ) (s : Finset ℤ) :
    ∑ j ∈ s, (1 + (a * (x - (j:ℝ)))^2)⁻¹ ≤ 2 * (1 + Real.pi / (2 * a)) := by
  set n₀ : ℤ := ⌊x⌋ with hn₀
  have hxn₀ : (n₀:ℝ) ≤ x := by rw [hn₀]; exact Int.floor_le x
  have hxn₀' : x < (n₀:ℝ) + 1 := by rw [hn₀]; exact Int.lt_floor_add_one x
  have hsumm := summable_nat_inv_one_add_sq_mul ha
  have key : ∀ (j : ℤ) (h3 : (0:ℤ) ≤ j),
      (((j.toNat : ℕ) : ℝ)) = (j:ℝ) := by
    intro j h3
    have h4 : (j.toNat : ℤ) = j := Int.toNat_of_nonneg h3
    have h5 : (((j.toNat : ℕ)) : ℝ) = (((j.toNat : ℤ)) : ℝ) := by push_cast; ring
    rw [h5, h4]
  have hlow : ∑ j ∈ s.filter (fun j => j ≤ n₀), (1 + (a * (x - (j:ℝ)))^2)⁻¹
      ≤ ∑' m : ℕ, (1 + (a * (m:ℝ))^2)⁻¹ := by
    set φ : ℤ → ℕ := fun j => (n₀ - j).toNat with hφ
    have hinj : Set.InjOn φ (↑(s.filter (fun j => j ≤ n₀)) : Set ℤ) := by
      intro j hj k hk hjk
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hj hk
      have hj' : j ≤ n₀ := hj.2
      have hk' : k ≤ n₀ := hk.2
      simp only [hφ] at hjk
      have h3 : (0:ℤ) ≤ n₀ - j := by omega
      have h4 : (0:ℤ) ≤ n₀ - k := by omega
      have h5 : ((n₀-j).toNat : ℤ) = ((n₀-k).toNat : ℤ) := by rw [hjk]
      rw [Int.toNat_of_nonneg h3, Int.toNat_of_nonneg h4] at h5
      omega
    have hstep1 : ∑ j ∈ s.filter (fun j => j ≤ n₀), (1 + (a * (x - (j:ℝ)))^2)⁻¹
        ≤ ∑ j ∈ s.filter (fun j => j ≤ n₀), (1 + (a * ((φ j : ℕ):ℝ))^2)⁻¹ := by
      refine Finset.sum_le_sum (fun j hj => ?_)
      have hj' : j ≤ n₀ := (Finset.mem_filter.mp hj).2
      have hcast : (j:ℝ) ≤ (n₀:ℝ) := by exact_mod_cast hj'
      have h1 : (0:ℝ) ≤ (n₀:ℝ) - (j:ℝ) := by linarith
      have h2 : ((φ j : ℕ):ℝ) = (n₀:ℝ) - (j:ℝ) := by
        simp only [hφ]
        have h3 : (0:ℤ) ≤ n₀ - j := by omega
        have h4 : ((n₀ - j).toNat : ℤ) = n₀ - j := Int.toNat_of_nonneg h3
        have h5 : (((n₀ - j).toNat : ℕ) : ℝ) = (((n₀ - j).toNat : ℤ) : ℝ) := by push_cast; ring
        rw [h5, h4]
        push_cast
        ring
      have h5 : ((n₀:ℝ) - (j:ℝ))^2 ≤ (x - (j:ℝ))^2 := by nlinarith [hxn₀, h1]
      have h6 : (0:ℝ) < 1 + (a*((n₀:ℝ)-(j:ℝ)))^2 := by positivity
      have h7 : (0:ℝ) < 1 + (a*(x-(j:ℝ)))^2 := by positivity
      have h8 : (a*(↑n₀ - ↑j))^2 ≤ (a*(x - ↑j))^2 := by nlinarith [h5, sq_nonneg a]
      rw [h2, inv_le_inv₀ h7 h6]
      linarith
    refine le_trans hstep1 ?_
    rw [← Finset.sum_image (f := fun m : ℕ => (1 + (a * (m:ℝ))^2)⁻¹) hinj]
    exact hsumm.sum_le_tsum _ (fun m _ => by positivity)
  have hhigh : ∑ j ∈ s.filter (fun j => ¬ (j ≤ n₀)), (1 + (a * (x - (j:ℝ)))^2)⁻¹
      ≤ ∑' m : ℕ, (1 + (a * (m:ℝ))^2)⁻¹ := by
    set ψ : ℤ → ℕ := fun j => (j - n₀ - 1).toNat with hψ
    have hinj : Set.InjOn ψ (↑(s.filter (fun j => ¬ (j ≤ n₀))) : Set ℤ) := by
      intro j hj k hk hjk
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hj hk
      have hj' : n₀ < j := lt_of_not_ge hj.2
      have hk' : n₀ < k := lt_of_not_ge hk.2
      simp only [hψ] at hjk
      have h3 : (0:ℤ) ≤ j - n₀ - 1 := by omega
      have h4 : (0:ℤ) ≤ k - n₀ - 1 := by omega
      have h5 : ((j-n₀-1).toNat : ℤ) = ((k-n₀-1).toNat : ℤ) := by rw [hjk]
      rw [Int.toNat_of_nonneg h3, Int.toNat_of_nonneg h4] at h5
      omega
    have hstep1 : ∑ j ∈ s.filter (fun j => ¬ (j ≤ n₀)), (1 + (a * (x - (j:ℝ)))^2)⁻¹
        ≤ ∑ j ∈ s.filter (fun j => ¬ (j ≤ n₀)), (1 + (a * ((ψ j : ℕ):ℝ))^2)⁻¹ := by
      refine Finset.sum_le_sum (fun j hj => ?_)
      have hj' : n₀ < j := lt_of_not_ge (Finset.mem_filter.mp hj).2
      have h1 : (0:ℝ) ≤ (j:ℝ) - (n₀:ℝ) - 1 := by
        have : (n₀:ℝ) + 1 ≤ (j:ℝ) := by exact_mod_cast (by omega : n₀ + 1 ≤ j)
        linarith
      have h2 : ((ψ j : ℕ):ℝ) = (j:ℝ) - (n₀:ℝ) - 1 := by
        simp only [hψ]
        have h3 : (0:ℤ) ≤ j - n₀ - 1 := by omega
        have h4 : ((j - n₀ - 1).toNat : ℤ) = j - n₀ - 1 := Int.toNat_of_nonneg h3
        have h5 : (((j - n₀ - 1).toNat : ℕ) : ℝ) = (((j - n₀ - 1).toNat : ℤ) : ℝ) := by
          push_cast; ring
        rw [h5, h4]
        push_cast
        ring
      have h5 : ((j:ℝ) - (n₀:ℝ) - 1)^2 ≤ (x - (j:ℝ))^2 := by
        have h6 : x - (j:ℝ) < 0 := by linarith [hxn₀']
        nlinarith [h1, h6]
      have h6 : (0:ℝ) < 1 + (a*((j:ℝ)-(n₀:ℝ)-1))^2 := by positivity
      have h7 : (0:ℝ) < 1 + (a*(x-(j:ℝ)))^2 := by positivity
      have h8 : (a*((j:ℝ) - ↑n₀ - 1))^2 ≤ (a*(x - ↑j))^2 := by nlinarith [h5, sq_nonneg a]
      rw [h2, inv_le_inv₀ h7 h6]
      linarith
    refine le_trans hstep1 ?_
    rw [← Finset.sum_image (f := fun m : ℕ => (1 + (a * (m:ℝ))^2)⁻¹) hinj]
    exact hsumm.sum_le_tsum _ (fun m _ => by positivity)
  rw [← Finset.sum_filter_add_sum_filter_not s (fun j => j ≤ n₀)]
  have hb := tsum_nat_inv_one_add_sq_mul_le ha
  linarith

theorem schwartz_decay (f : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖f x‖ ≤ C * (1 + x^2)⁻¹ := by
  refine ⟨2 * max (SchwartzMap.seminorm ℂ 2 0 f) (SchwartzMap.seminorm ℂ 0 0 f) + 1, by positivity, fun x => ?_⟩
  have hA : ‖x‖^2 * ‖f x‖ ≤ SchwartzMap.seminorm ℂ 2 0 f := SchwartzMap.norm_pow_mul_le_seminorm ℂ f 2 x
  have hB : ‖f x‖ ≤ SchwartzMap.seminorm ℂ 0 0 f := SchwartzMap.norm_le_seminorm ℂ f x
  have hnn : (0:ℝ) ≤ SchwartzMap.seminorm ℂ 2 0 f := by positivity
  have hnn' : (0:ℝ) ≤ SchwartzMap.seminorm ℂ 0 0 f := by positivity
  have habs : ‖x‖ = |x| := Real.norm_eq_abs x
  have hpos : (0:ℝ) < 1 + x^2 := by positivity
  have hmain : ‖f x‖ * (1 + x^2) ≤ 2 * max (SchwartzMap.seminorm ℂ 2 0 f) (SchwartzMap.seminorm ℂ 0 0 f) := by
    by_cases h : (1:ℝ) ≤ |x|
    · have h2 : (1 + x^2) ≤ 2 * x^2 := by nlinarith [h, sq_abs x]
      have h3 : ‖f x‖ * (1 + x^2) ≤ 2 * SchwartzMap.seminorm ℂ 2 0 f := by
        have h4 : ‖f x‖ * (1 + x^2) ≤ ‖f x‖ * (2 * x^2) :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        have h5 : ‖f x‖ * (2 * x^2) = 2 * (‖x‖^2 * ‖f x‖) := by rw [habs, sq_abs]; ring
        rw [h5] at h4
        linarith [hA]
      linarith [h3, le_max_left (SchwartzMap.seminorm ℂ 2 0 f) (SchwartzMap.seminorm ℂ 0 0 f)]
    · have h1 : |x| < 1 := lt_of_not_ge h
      have h2 : (1 + x^2) ≤ 2 := by
        have h1' : |x|^2 < 1 := by nlinarith [h1, abs_nonneg x]
        rw [sq_abs] at h1'
        linarith
      have h3 : ‖f x‖ * (1 + x^2) ≤ 2 * SchwartzMap.seminorm ℂ 0 0 f := by
        have h4 : ‖f x‖ * (1 + x^2) ≤ ‖f x‖ * 2 :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        linarith [hB]
      linarith [h3, le_max_right (SchwartzMap.seminorm ℂ 2 0 f) (SchwartzMap.seminorm ℂ 0 0 f)]
  have hfin : ‖f x‖ ≤ (2 * max (SchwartzMap.seminorm ℂ 2 0 f) (SchwartzMap.seminorm ℂ 0 0 f)) * (1 + x^2)⁻¹ := by
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ hpos).mpr hmain
  calc ‖f x‖ ≤ (2 * max (SchwartzMap.seminorm ℂ 2 0 f) (SchwartzMap.seminorm ℂ 0 0 f)) * (1 + x^2)⁻¹ := hfin
    _ ≤ (2 * max (SchwartzMap.seminorm ℂ 2 0 f) (SchwartzMap.seminorm ℂ 0 0 f) + 1) * (1 + x^2)⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)

theorem lattice_kernel_sum_le {a C : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hC : 0 < C)
    {Φ : ℝ → ℂ} (hΦ : ∀ u, ‖Φ u‖ ≤ C * (1 + u^2)⁻¹) (x : ℝ) (s : Finset ℤ) :
    ∑ j ∈ s, ‖a * Φ (a * (x - (j:ℝ)))‖ₑ ≤ ENNReal.ofReal (2 * C * (1 + Real.pi / 2)) := by
  have h1 : ∀ j : ℤ, ‖a * Φ (a * (x - (j:ℝ)))‖ ≤ a * C * (1 + (a*(x - (j:ℝ)))^2)⁻¹ := by
    intro j
    rw [norm_mul, show ‖((a:ℝ):ℂ)‖ = a by simp [abs_of_pos ha]]
    calc a * ‖Φ (a * (x - (j:ℝ)))‖ ≤ a * (C * (1+(a*(x-(j:ℝ)))^2)⁻¹) :=
          mul_le_mul_of_nonneg_left (hΦ _) ha.le
      _ = a * C * (1 + (a*(x-(j:ℝ)))^2)⁻¹ := by ring
  have h2 : ∀ j ∈ s, (0:ℝ) ≤ a * C * (1 + (a*(x - (j:ℝ)))^2)⁻¹ := fun j _ => by positivity
  calc ∑ j ∈ s, ‖a * Φ (a * (x - (j:ℝ)))‖ₑ
      ≤ ∑ j ∈ s, ENNReal.ofReal (a * C * (1 + (a*(x - (j:ℝ)))^2)⁻¹) :=
        Finset.sum_le_sum (fun j _ => by
          rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (h1 j))
    _ = ENNReal.ofReal (∑ j ∈ s, a * C * (1 + (a*(x - (j:ℝ)))^2)⁻¹) :=
        (ENNReal.ofReal_sum_of_nonneg h2).symm
    _ ≤ ENNReal.ofReal (2 * C * (1 + Real.pi / 2)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h3 : ∑ j ∈ s, a * C * (1 + (a*(x - (j:ℝ)))^2)⁻¹
            = a * C * ∑ j ∈ s, (1 + (a*(x - (j:ℝ)))^2)⁻¹ := by rw [Finset.mul_sum]
        rw [h3]
        have h4 := finset_sum_inv_one_add_sq_step_le ha x s
        have h5 : a * C * ∑ j ∈ s, (1 + (a*(x - (j:ℝ)))^2)⁻¹ ≤ a * C * (2 * (1 + Real.pi/(2*a))) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
        have h6 : a * C * (2 * (1 + Real.pi/(2*a))) = 2 * C * (a + Real.pi/2) := by
          field_simp
        rw [h6] at h5
        refine le_trans h5 ?_
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-! ## §9. The residue-slice bound (steps 1–2 of the §7.2 route) -/

/-- Change of variables `x ↦ a x` (`a > 0`) for `∫⁻` on `ℝ`. -/
theorem lintegral_comp_mul_left_real {a : ℝ} (ha : 0 < a) {F : ℝ → ENNReal} (hF : Measurable F) :
    ∫⁻ x : ℝ, F (a * x) = ENNReal.ofReal (a⁻¹) * ∫⁻ y : ℝ, F y := by
  rw [← lintegral_map (f := F) hF (by fun_prop : Measurable fun x : ℝ => a * x)]
  rw [Real.map_volume_mul_left (ne_of_gt ha)]
  rw [lintegral_smul_measure, abs_of_pos (by positivity : (0:ℝ) < a⁻¹), smul_eq_mul]

/-- The `L^1`-scaling of the dilated kernel. -/
theorem lintegral_norm_dilate_eq {a : ℝ} (ha : 0 < a) {Φ : ℝ → ℂ} (hΦ : Measurable Φ) :
    ∫⁻ y : ℝ, ‖a * Φ (a * y)‖ₑ = ∫⁻ z : ℝ, ‖Φ z‖ₑ := by
  have h1 : ∀ y : ℝ, ‖a * Φ (a*y)‖ₑ = ENNReal.ofReal a * ‖Φ (a*y)‖ₑ := by
    intro y
    rw [enorm_mul, show ‖((a:ℝ):ℂ)‖ₑ = ENNReal.ofReal a by
      rw [← ofReal_norm]
      congr 1
      simp [abs_of_pos ha]]
  rw [lintegral_congr h1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [lintegral_comp_mul_left_real ha hΦ.enorm]
  rw [← mul_assoc, ← ENNReal.ofReal_mul ha.le, mul_inv_cancel₀ (ne_of_gt ha), ENNReal.ofReal_one, one_mul]


/-- The per-residue-class bound of §7.2, with the width gain already in place. -/
theorem residue_slice_bound {p : ℝ} (hp : 1 < p) {q : ℕ} (hq : 0 < q)
    {a C : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hC : 0 < C) {Φ : ℝ → ℂ} (hΦm : Measurable Φ)
    (hΦ : ∀ u : ℝ, ‖Φ u‖ ≤ C * (1 + u^2)⁻¹)
    (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) :
    ∫⁻ x : ℝ, (‖∑ j ∈ s.filter (fun j => (q:ℤ) ∣ (z+j)),
        g j * (a * Φ (a * (x + (((j+z:ℤ):ℝ)/(q:ℝ)))))‖ₑ)^p ∂volume
      ≤ ENNReal.ofReal ((2*C*(1+Real.pi/2))^(p-1)) * (∫⁻ y : ℝ, ‖Φ y‖ₑ) *
          (∑ j ∈ s.filter (fun j => (q:ℤ) ∣ (z+j)), ‖g j‖ₑ ^ p) := by
  set kern : ℝ → ℂ := fun y => a * Φ (a * y) with hkern
  have hkernm : Measurable kern := by
    rw [hkern]; exact (hΦm.comp (by fun_prop : Measurable fun y : ℝ => a*y)).const_mul _
  set A : ℝ≥0∞ := ENNReal.ofReal (2 * C * (1 + Real.pi / 2)) with hAdef
  have hA : ∀ x : ℝ, ∑ m ∈ (s.filter (fun j => (q:ℤ) ∣ (z+j))).image (fun j => -((z+j)/(q:ℤ))),
      ‖kern (x - (m:ℝ))‖ₑ ≤ A := by
    intro x
    rw [hkern, hAdef]
    exact lattice_kernel_sum_le ha ha1 hC hΦ x _
  have hinj : Set.InjOn (fun j : ℤ => -((z+j)/(q:ℤ)))
      ↑(s.filter (fun j => (q:ℤ) ∣ (z+j))) := by
    intro j hj k hk hjk
    have hjP : (q:ℤ) ∣ (z+j) := (Finset.mem_filter.mp hj).2
    have hkP : (q:ℤ) ∣ (z+k) := (Finset.mem_filter.mp hk).2
    have h1 : ((z+j)/(q:ℤ)) = ((z+k)/(q:ℤ)) := neg_inj.mp hjk
    have h2 := Int.mul_ediv_cancel' hjP
    have h3 := Int.mul_ediv_cancel' hkP
    have h4 : z + j = z + k := by rw [← h2, h1, h3]
    omega
  have hcast : ∀ (j : ℤ), (q:ℤ) ∣ (z+j) →
      (((z+j)/(q:ℤ) : ℤ) : ℝ) = ((z+j : ℤ) : ℝ)/(q:ℝ) := by
    intro j hjP
    have h2 := Int.mul_ediv_cancel' hjP
    have h3 : ((q:ℤ):ℝ) * (((z+j)/(q:ℤ) : ℤ):ℝ) = ((z+j:ℤ):ℝ) := by
      rw [← Int.cast_mul, h2]
    rw [eq_div_iff (by positivity : (q:ℝ) ≠ 0), mul_comm]
    exact h3
  have hcancel : ∀ (j : ℤ), (q:ℤ) ∣ (z+j) → -((q:ℤ) * (-((z+j)/(q:ℤ)))) - z = j := by
    intro j hjP
    rw [mul_neg, neg_neg, Int.mul_ediv_cancel' hjP]; omega
  have hsum_eq : ∀ x : ℝ,
      (∑ j ∈ s.filter (fun j => (q:ℤ) ∣ (z+j)),
          g j * kern (x + (((j+z:ℤ):ℝ)/(q:ℝ))))
        = ∑ m ∈ (s.filter (fun j => (q:ℤ) ∣ (z+j))).image (fun j => -((z+j)/(q:ℤ))),
            g (-((q:ℤ) * m) - z) * kern (x - (m:ℝ)) := by
    intro x
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hjP : (q:ℤ) ∣ (z+j) := (Finset.mem_filter.mp hj).2
    rw [hcancel j hjP]
    congr 1
    push_cast
    rw [hcast j hjP]
    push_cast
    ring
  have hsub : (∑ m ∈ (s.filter (fun j => (q:ℤ) ∣ (z+j))).image (fun j => -((z+j)/(q:ℤ))),
        ‖g (-((q:ℤ) * m) - z)‖ₑ ^ p)
      = ∑ j ∈ s.filter (fun j => (q:ℤ) ∣ (z+j)), ‖g j‖ₑ ^ p := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have hxP : (q:ℤ) ∣ (z+x) := (Finset.mem_filter.mp hx).2
    rw [hcancel x hxP]
  have hL := lintegral_conv_finset_rpow_le hp hkernm
    ((s.filter (fun j => (q:ℤ) ∣ (z+j))).image (fun j => -((z+j)/(q:ℤ)))) A hA
    (g := fun m : ℤ => g (-((q:ℤ) * m) - z))
  refine le_trans (le_of_eq ?_) (le_trans hL ?_)
  · refine lintegral_congr (fun x => ?_)
    rw [hsum_eq x]
  · rw [lintegral_norm_dilate_eq ha hΦm, hAdef]
    have hAr : (ENNReal.ofReal (2 * C * (1 + Real.pi / 2))) ^ (p-1)
        = ENNReal.ofReal ((2 * C * (1 + Real.pi / 2)) ^ (p-1)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith)]
    rw [hAr]
    exact mul_le_mul le_rfl (le_of_eq hsub) (by positivity) (by positivity)

/-! ## §10. The summation over the residue classes -/

theorem filter_residue_singleton {q : ℕ} (hq : 0 < q) (j : ℤ) :
    (Finset.Icc (0:ℤ) ((q:ℤ)-1)).filter (fun z => (q:ℤ) ∣ (z+j)) = {(-(j)) % (q:ℤ)} := by
  have hqZ : (0:ℤ) < (q:ℤ) := by exact_mod_cast hq
  have hqne : (q:ℤ) ≠ 0 := ne_of_gt hqZ
  set z₀ : ℤ := (-(j)) % (q:ℤ) with hz₀
  have hz₀0 : 0 ≤ z₀ := Int.emod_nonneg _ hqne
  have hz₀1 : z₀ ≤ (q:ℤ) - 1 := by have := Int.emod_lt_of_pos (-(j)) hqZ; omega
  have hdiv : (q:ℤ) ∣ ((-(j)) - z₀) := by
    refine ⟨(-(j))/(q:ℤ), ?_⟩
    rw [hz₀]
    have := Int.emod_add_mul_ediv (-(j)) (q:ℤ)
    linarith
  have hdiv2 : (q:ℤ) ∣ (z₀ + j) := by
    have h : z₀ + j = -((-(j)) - z₀) := by ring
    rw [h]
    exact dvd_neg.mpr hdiv
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    exact ⟨⟨hz₀0, hz₀1⟩, hdiv2⟩
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_Icc] at hz
    obtain ⟨⟨hz0, hz1⟩, hzdvd⟩ := hz
    have hsub : (q:ℤ) ∣ z - z₀ := by
      have := dvd_sub hzdvd hdiv2
      have h : (z+j) - (z₀+j) = z - z₀ := by ring
      rwa [h] at this
    rcases hsub with ⟨c, hc⟩
    have hlt : |z - z₀| < (q:ℤ) := by
      rw [abs_lt]; constructor <;> omega
    have hc0 : c = 0 := by
      by_contra hcne
      have : (q:ℤ) ≤ |z - z₀| := by
        rw [hc, abs_mul, abs_of_pos hqZ]
        have h1 : (1:ℤ) ≤ |c| := by have := abs_pos.mpr hcne; omega
        nlinarith
      omega
    rw [hc0, mul_zero] at hc
    omega

theorem sum_filter_residue_le {q : ℕ} (hq : 0 < q) {p : ℝ} (g : ℤ → ℂ) (s : Finset ℤ) :
    ∑ z ∈ Finset.Icc (0:ℤ) ((q:ℤ)-1), ∑ j ∈ s.filter (fun j => (q:ℤ) ∣ (z+j)), ‖g j‖ₑ ^ p
      = ∑ j ∈ s, ‖g j‖ₑ ^ p := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hsing := filter_residue_singleton hq j
  rw [← Finset.sum_filter, hsing, Finset.sum_singleton]

/-- The inverse Fourier transform of a Schwartz function decays like `(1+x²)⁻¹`. -/
theorem fourierInv_decay (φ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ,
      ‖FourierTransformInv.fourierInv (φ : ℝ → ℂ) u‖ ≤ C * (1 + u^2)⁻¹ := by
  obtain ⟨C, hC, hCd⟩ := schwartz_decay ((SchwartzMap.fourierTransformCLM ℝ) φ)
  refine ⟨C, hC, fun u => ?_⟩
  have h : FourierTransformInv.fourierInv (φ : ℝ → ℂ) u = 𝓕 (φ : ℝ → ℂ) (-u) := by
    rw [Real.fourierInv_eq, Real.fourier_eq]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
    simp [inner_neg_right]
  rw [h]
  simpa only [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe, neg_sq] using hCd (-u)

/-! ## §11. The `ℓ^p(ℤ)` slice bound -/

/-! ## §12. The dilation identity for the sliced amplitudes -/

/-- The change of variables `γ = (q/D)·β` in the dilated amplitude integral. -/
theorem integral_dilated_fourierInv {q D c : ℝ} (hq : 0 < q) (hD : 0 < D) (φ : ℝ → ℂ) :
    (∫ γ : ℝ, Complex.exp (2 * Real.pi * Complex.I * (c:ℂ) * (γ:ℂ)) * φ (D * γ / q))
      = (q / D) * FourierTransformInv.fourierInv φ ((q / D) * c) := by
  have ha : (0:ℝ) < D/q := div_pos hD hq
  have hqC : ((q:ℝ):ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  have hDC : ((D:ℝ):ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hD)
  have haC : (((D/q:ℝ)):ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ha)
  set F : ℝ → ℂ := fun β => Complex.exp (2 * Real.pi * Complex.I * (((q/D)*c : ℝ):ℂ) * (β:ℂ)) * φ β
    with hF
  have hsub : (∫ γ : ℝ, Complex.exp (2 * Real.pi * Complex.I * (c:ℂ) * (γ:ℂ)) * φ (D * γ / q))
      = ∫ γ : ℝ, F ((D/q) * γ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun γ => ?_)
    simp only [hF]
    congr 2
    · push_cast
      field_simp
    · rw [show (D/q) * γ = D * γ / q by ring]
  rw [hsub, MeasureTheory.Measure.integral_comp_mul_left]
  rw [show |((D/q:ℝ))⁻¹| = q/D by
    rw [abs_of_pos (inv_pos.mpr ha), show ((D/q:ℝ))⁻¹ = q/D by field_simp]]
  rw [Complex.real_smul]
  push_cast
  congr 1
  rw [Real.fourierInv_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun β => ?_)
  simp only [hF, Circle.smul_def]
  rw [Real.fourierChar_apply]
  congr 1
  have hinner : inner ℝ β (q / D * c) = (q / D * c) * β := by simp [mul_comm]
  rw [hinner]
  push_cast
  ring

end

end Commons.Analysis.ExponentialSums


/-! ===== concatenated from probeP8.lean ===== -/

open MeasureTheory Finset
open scoped ENNReal BigOperators FourierTransform
namespace Commons.Analysis.ExponentialSums
noncomputable section

private theorem support_exp_mul_phi_subset {q D : ℝ} (hq : 0 < q) (hD : 0 < D) {φ : ℝ → ℂ}
    (hφsupp : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0) (c : ℝ) :
    Function.support (fun γ : ℝ => Complex.exp (2 * Real.pi * Complex.I * (c:ℂ) * (γ:ℂ))
        * φ (D * γ / q)) ⊆ Set.Icc (-(q/(2*D))) (q/(2*D)) := by
  have hDq : (0:ℝ) < D/q := div_pos hD hq
  intro γ hγ
  rw [Function.mem_support] at hγ
  rw [Set.mem_Icc]
  by_contra hcon
  have hcon' : γ < -(q/(2*D)) ∨ q/(2*D) < γ := by
    by_contra h
    push_neg at h
    exact hcon ⟨h.1, h.2⟩
  have hout : D * γ / q < -(1/2) ∨ (1/2) < D * γ / q := by
    have h2 : (0:ℝ) < 2*D := by positivity
    rcases hcon' with h | h
    · left
      have hh : γ * (2*D) < -q := by
        have hm := mul_lt_mul_of_pos_right h h2
        rwa [neg_mul, div_mul_cancel₀ q (ne_of_gt h2)] at hm
      rw [div_lt_iff₀ hq]
      nlinarith [hh]
    · right
      have hh : q < γ * (2*D) := by
        have hm := mul_lt_mul_of_pos_right h h2
        rwa [div_mul_cancel₀ q (ne_of_gt h2)] at hm
      rw [lt_div_iff₀ hq]
      nlinarith [hh]
  have hphi : φ (D * γ / q) = 0 := by
    apply hφsupp
    intro hmem
    rw [Set.mem_Icc] at hmem
    rcases hout with h | h
    · linarith [hmem.1]
    · linarith [hmem.2]
  exact hγ (by rw [hphi, mul_zero])

private theorem integrable_exp_mul_phi {q D c : ℝ} (hq : 0 < q) (hD : 0 < D) {φ : ℝ → ℂ}
    (hφcont : Continuous φ) (hφsupp : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0) :
    Integrable (fun γ : ℝ => Complex.exp (2 * Real.pi * Complex.I * (c:ℂ) * (γ:ℂ))
        * φ (D * γ / q)) volume := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · fun_prop
  · exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (support_exp_mul_phi_subset hq hD hφsupp c)

/-- **The inverse transform of a sliced amplitude** — Bourgain's substitution `γ = qβ` applied
term by term, i.e. the identification
`𝓕⁻¹[Σ_j g_j e(2πi(j+z)·/q) φ(D·/q)](x) = Σ_j g_j (q/D) φ̌((q/D)(x+(j+z)/q))`. -/
theorem sliced_inverse_transform {q : ℕ} (hq : 0 < q) {D : ℝ} (hD : 0 < D) {φ : ℝ → ℂ}
    (hφcont : Continuous φ) (hφsupp : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0)
    (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) (x : ℝ) :
    (∫ γ : ℝ, (∑ j ∈ s.filter (fun j => (q:ℤ) ∣ (z+j)),
        g j * Complex.exp (2 * Real.pi * Complex.I * (((j:ℂ) + (z:ℂ)) * (γ:ℂ) / ((q:ℝ):ℂ))))
        * φ (D * γ / (q:ℝ)) * Complex.exp (2 * Real.pi * Complex.I * (x:ℂ) * (γ:ℂ)))
      = ∑ j ∈ s.filter (fun j => (q:ℤ) ∣ (z+j)), g j * (((q:ℝ)/D) *
          FourierTransformInv.fourierInv φ (((q:ℝ)/D) * (x + ((j+z:ℤ):ℝ)/(q:ℝ)))) := by
  set J : Finset ℤ := s.filter (fun j => (q:ℤ) ∣ (z+j)) with hJ
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hfun : (fun γ : ℝ => (∑ j ∈ J, g j *
        Complex.exp (2 * Real.pi * Complex.I * (((j:ℂ) + (z:ℂ)) * (γ:ℂ) / ((q:ℝ):ℂ))))
        * φ (D * γ / (q:ℝ)) * Complex.exp (2 * Real.pi * Complex.I * (x:ℂ) * (γ:ℂ)))
      = fun γ : ℝ => ∑ j ∈ J, (g j *
        Complex.exp (2 * Real.pi * Complex.I * (((j:ℂ) + (z:ℂ)) * (γ:ℂ) / ((q:ℝ):ℂ)))
        * φ (D * γ / (q:ℝ)) * Complex.exp (2 * Real.pi * Complex.I * (x:ℂ) * (γ:ℂ))) := by
    funext γ
    rw [Finset.sum_mul, Finset.sum_mul]
  rw [hfun, integral_finset_sum]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    have key : ∀ γ : ℝ,
        Complex.exp (2 * Real.pi * Complex.I * (((j:ℂ) + (z:ℂ)) * (γ:ℂ) / ((q:ℝ):ℂ)))
          * Complex.exp (2 * Real.pi * Complex.I * (x:ℂ) * (γ:ℂ))
        = Complex.exp (2 * Real.pi * Complex.I *
            (((x + ((j+z:ℤ):ℝ)/(q:ℝ)):ℝ):ℂ) * (γ:ℂ)) := by
      intro γ
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hsummand : (∫ γ : ℝ, g j *
        Complex.exp (2 * Real.pi * Complex.I * (((j:ℂ) + (z:ℂ)) * (γ:ℂ) / ((q:ℝ):ℂ)))
        * φ (D * γ / (q:ℝ)) * Complex.exp (2 * Real.pi * Complex.I * (x:ℂ) * (γ:ℂ)))
        = g j * ∫ γ : ℝ, Complex.exp (2 * Real.pi * Complex.I *
            (((x + ((j+z:ℤ):ℝ)/(q:ℝ)):ℝ):ℂ) * (γ:ℂ)) * φ (D * γ / (q:ℝ)) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun γ => ?_))
      simp only []
      rw [show g j * Complex.exp (2 * Real.pi * Complex.I * (((j:ℂ) + (z:ℂ)) * (γ:ℂ) / ((q:ℝ):ℂ)))
            * φ (D * γ / (q:ℝ)) * Complex.exp (2 * Real.pi * Complex.I * (x:ℂ) * (γ:ℂ))
          = g j * (Complex.exp (2 * Real.pi * Complex.I * (((j:ℂ) + (z:ℂ)) * (γ:ℂ) / ((q:ℝ):ℂ)))
            * Complex.exp (2 * Real.pi * Complex.I * (x:ℂ) * (γ:ℂ))) * φ (D * γ / (q:ℝ)) by ring,
          key γ]
      ring
    rw [hsummand, integral_dilated_fourierInv hqR hD φ]
  · intro j _
    have key : ∀ γ : ℝ,
        Complex.exp (2 * Real.pi * Complex.I * (((j:ℂ) + (z:ℂ)) * (γ:ℂ) / ((q:ℝ):ℂ)))
          * Complex.exp (2 * Real.pi * Complex.I * (x:ℂ) * (γ:ℂ))
        = Complex.exp (2 * Real.pi * Complex.I *
            (((x + ((j+z:ℤ):ℝ)/(q:ℝ)):ℝ):ℂ) * (γ:ℂ)) := by
      intro γ
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hint := (integrable_exp_mul_phi (q := (q:ℝ)) (D := D)
      (c := x + ((j+z:ℤ):ℝ)/(q:ℝ)) hqR hD hφcont hφsupp).const_mul (g j)
    refine hint.congr (Filter.Eventually.of_forall (fun γ => ?_))
    simp only []
    rw [show g j * (Complex.exp (2 * Real.pi * Complex.I *
            (((x + ((j+z:ℤ):ℝ)/(q:ℝ)):ℝ):ℂ) * (γ:ℂ)) * φ (D * γ / (q:ℝ)))
          = g j * (Complex.exp (2 * Real.pi * Complex.I * (((j:ℂ) + (z:ℂ)) * (γ:ℂ) / ((q:ℝ):ℂ)))
            * Complex.exp (2 * Real.pi * Complex.I * (x:ℂ) * (γ:ℂ))) * φ (D * γ / (q:ℝ)) by
        rw [key γ]; ring]
    ring

end
end Commons.Analysis.ExponentialSums


/-! ===== concatenated from model721_slice.lean ===== -/

/-
# Bourgain §7.2, Lemma 7.20 — the sliced (residue-class) form, and the assembly

`Work/Analysis/ExponentialSums/model721.lean` contains the whole analytic content of Bourgain's
Lemma 7.20 (the width gain).  This file supplies the remaining **identification** and the
**assembly**, i.e. the actual inequality of Lemma 7.20 in its sliced form.

Everything is stated in the `γ`-variable (i.e. *after* Bourgain's substitution `γ = qβ`), where the
residue identity reads

`T_N g (yq+z) = ∫_γ Φ(-(N²/q)γ) · \tilde F_z(γ) · e(2πiyγ) dγ`,   `\tilde F_z(γ) = F_z(γ/q) e(2πizγ/q) φ(Dγ/q)`

with **no** factor of `q` (the `q` of the residue identity is cancelled by the substitution
`β = γ/q`).  Here `Φ = fresnelProfile`.

## The result of this file (SESSION 43): Bourgain's Lemma 7.20, PROVED

`theorem sliced_maximal_lp` (at the bottom) is the `1 < p < ∞` model maximal inequality of §7.2
with a constant **uniform in `q` and `D`**:

`∑_{z<q} ∫⁻_y (⨆_k ‖slicedBlock k q D φ g s z y‖ₑ)^p ≤ C · ∫⁻_m ‖g m‖ₑ^p`.

The three ingredients it needed beyond `model721.lean`:

* `sliced_inverse_transform` (`Work/Analysis/ExponentialSums/probeP8.lean`) — the identification
  `𝓕⁻¹[\tilde F_z](x) = ∑_{j ≡ −z} g_j (q/D) φ̌((q/D)(x+(j+z)/q))`;
* `contDiff_fresnelProfile` (`Work/Analysis/Fresnel/fresnel_smooth.lean`) — `Φ` is `C^∞`, which is
  what makes the smooth window `φ(Dβ)·Φ(-N²β)` Schwartz so that the Fourier-inversion
  band-limitedness criterion applies (**this is why §7.2 needs a *smooth* arc truncation**);
* the assembly lemmas below (`slicedAmp`/`slicedSymbol`/`slicedBlock`/`slicedResidue`,
  `fourier_slicedBlock`, `fourier_slicedBlock_eq_zero`, `lintegral_invTransform_rpow_lt_top`,
  `exists_decay_fourierInv`, `fourierInv_slicedAmp`, ...).

**Nothing is missing from §7.2.**  What remains for the target is (i) the identity between the
`∑_{a<q}`-form of (7.21) and this sliced form (residue identity + `β = γ/q`), and (ii) the
sharp-to-smooth replacement of §7.4 (the corpus's `majorArcBlock` uses a sharp arc indicator, for
which `𝓕(sharp · Φ)` is not `L¹`, so it is *not* covered by this smooth-window theorem).

See `SEVEN_PLAN.md`, SESSION 43.
-/

open MeasureTheory Finset
open scoped ENNReal BigOperators FourierTransform Topology
namespace Commons.Analysis.ExponentialSums
noncomputable section

/-- `fun_prop` does not know that `ℝ → ℂ` is `C^∞`. -/
theorem contDiff_ofRealCLM : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (x : ℂ)) :=
  Complex.ofRealCLM.contDiff
attribute [fun_prop] contDiff_ofRealCLM

/-- `\tilde F_z(γ) = F_z(γ/q) · e^{2πizγ/q} · φ(Dγ/q)` — the `z`-sliced amplitude in the
`γ`-variable. -/
def slicedAmp (q : ℕ) (D : ℝ) (φ : ℝ → ℂ) (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) (γ : ℝ) : ℂ :=
  (∑ j ∈ s.filter (fun j => (q:ℤ) ∣ (z+j)),
      g j * Complex.exp (2 * Real.pi * Complex.I *
        (((j:ℂ) + (z:ℂ)) * (γ:ℂ) / ((q:ℝ):ℂ))))
    * φ (D * γ / (q:ℝ))

/-! ## Smoothness, compact support and integrability of the sliced amplitude -/

theorem contDiff_slicedAmp {q : ℕ} {D : ℝ} {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (slicedAmp q D φ g s z) := by
  unfold slicedAmp
  fun_prop

theorem support_slicedAmp_subset {q : ℕ} (hq : 0 < q) {D : ℝ} (hD : 0 < D) {φ : ℝ → ℂ}
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0) (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) :
    Function.support (slicedAmp q D φ g s z) ⊆ Set.Icc (-(q/(2*D))) (q/(2*D)) := by
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  intro γ hγ
  rw [Function.mem_support] at hγ
  rw [Set.mem_Icc]
  by_contra hcon
  have hcon' : γ < -(q/(2*D)) ∨ q/(2*D) < γ := by
    by_contra h
    push_neg at h
    exact hcon ⟨h.1, h.2⟩
  have hout : D * γ / (q:ℝ) < -(1/2) ∨ (1/2) < D * γ / (q:ℝ) := by
    have h2 : (0:ℝ) < 2*D := by positivity
    rcases hcon' with h | h
    · left
      have hh : γ * (2*D) < -q := by
        have hm := mul_lt_mul_of_pos_right h h2
        rwa [neg_mul, div_mul_cancel₀ (q:ℝ) (ne_of_gt h2)] at hm
      rw [div_lt_iff₀ hqR]
      nlinarith [hh]
    · right
      have hh : q < γ * (2*D) := by
        have hm := mul_lt_mul_of_pos_right h h2
        rwa [div_mul_cancel₀ (q:ℝ) (ne_of_gt h2)] at hm
      rw [lt_div_iff₀ hqR]
      nlinarith [hh]
  have hphi : φ (D * γ / (q:ℝ)) = 0 := by
    apply hφs
    intro hmem
    rw [Set.mem_Icc] at hmem
    rcases hout with h | h
    · linarith [hmem.1]
    · linarith [hmem.2]
  exact hγ (by simp only [slicedAmp]; rw [hphi, mul_zero])

theorem hasCompactSupport_slicedAmp {q : ℕ} (hq : 0 < q) {D : ℝ} (hD : 0 < D) {φ : ℝ → ℂ}
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0) (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) :
    HasCompactSupport (slicedAmp q D φ g s z) :=
  HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-(q/(2*D))) (q/(2*D)))
    isCompact_Icc (support_slicedAmp_subset hq hD hφs g s z)

/-! ## The band-limitedness and integrability of the sliced blocks -/

private theorem fourierChar_smul_eq (x γ : ℝ) (z : ℂ) :
    Complex.exp ((((2 * Real.pi * inner ℝ γ x : ℝ)) : ℂ) * Complex.I) • z
      = z * Complex.exp (2 * Real.pi * Complex.I * x * γ) := by
  rw [smul_eq_mul, mul_comm (Complex.exp _) z]
  congr 1
  congr 1
  rw [show (inner ℝ γ x : ℝ) = γ * x by simp [mul_comm]]
  push_cast
  ring_nf

private theorem fourierChar_smul_eq' (x γ : ℝ) (z : ℂ) :
    z * Complex.exp (2 * Real.pi * Complex.I * x * γ)
      = Complex.exp ((((2 * Real.pi * inner ℝ γ x : ℝ)) : ℂ) * Complex.I) • z :=
  (fourierChar_smul_eq x γ z).symm

private theorem fourierChar_smul_eq_eq (x γ : ℝ) (z : ℂ) :
    Real.fourierChar (inner ℝ γ x) • z = z * Complex.exp (2 * Real.pi * Complex.I * x * γ) := by
  rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  rw [show (inner ℝ γ x : ℝ) = γ * x by simp [mul_comm], mul_comm (Complex.exp _) z]
  congr 1
  push_cast
  ring_nf

/-! ## The residual estimates and the assembly -/

/-- `𝓕⁻ W x = ∫ β, W β e^{2πixβ}` in the shape used by the model. -/
theorem fourierInv_eq_integral (W : ℝ → ℂ) (x : ℝ) :
    FourierTransformInv.fourierInv W x
      = ∫ β : ℝ, W β * Complex.exp (2 * Real.pi * Complex.I * x * β) := by
  rw [Real.fourierInv_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun β => ?_))
  simp only []
  rw [fourierChar_smul_eq_eq x β (W β)]

theorem lintegral_enorm_rpow_lt_top_of_integrable_bounded {f : ℝ → ℂ} (hf : Integrable f)
    {C p : ℝ} (hC : ∀ x : ℝ, ‖f x‖ ≤ C) (hp : 1 ≤ p) :
    ∫⁻ x : ℝ, ‖f x‖ₑ ^ p < ⊤ := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  have hp1 : (0:ℝ) ≤ p - 1 := by linarith
  have hbound : ∀ x : ℝ, ‖f x‖ₑ ^ p ≤ ENNReal.ofReal (C ^ (p-1) * ‖f x‖) := by
    intro x
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (le_trans zero_le_one hp)]
    refine ENNReal.ofReal_le_ofReal ?_
    rcases eq_or_lt_of_le (norm_nonneg (f x)) with h0 | h0
    · rw [← h0]; simp [Real.zero_rpow (by linarith : p ≠ 0)]
    · have h1 : ‖f x‖ ^ p = ‖f x‖ ^ (p-1) * ‖f x‖ := by
        have h2 : ‖f x‖ ^ ((p-1)+1) = ‖f x‖ ^ (p-1) * ‖f x‖ := by
          rw [Real.rpow_add h0, Real.rpow_one]
        rw [show (p-1)+1 = p by ring] at h2
        exact h2
      rw [h1]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (norm_nonneg _) (hC x) hp1) (norm_nonneg _)
  calc ∫⁻ x : ℝ, ‖f x‖ₑ ^ p
      ≤ ∫⁻ x : ℝ, ENNReal.ofReal (C ^ (p-1) * ‖f x‖) := lintegral_mono hbound
    _ = ENNReal.ofReal (∫ x : ℝ, C ^ (p-1) * ‖f x‖) :=
        (ofReal_integral_eq_lintegral_ofReal (hf.norm.const_mul _)
          (Filter.Eventually.of_forall (fun x => by positivity))).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

theorem norm_exp_two_pi_I_mul' (x β : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * x * β)‖ = 1 := by
  rw [show 2 * Real.pi * Complex.I * x * β = (((2 * Real.pi * x * β : ℝ)) : ℂ) * Complex.I by
        push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-! ## The identification of the sliced amplitude's inverse transform and the assembly -/

/-- The residue sum `∑_{j ≡ -z (q)} g_j · (q/D) · φ̌((q/D)(x+(j+z)/q))` — the inverse transform of
the sliced amplitude. -/
noncomputable def slicedResidue (a : ℝ) (φ : ℝ → ℂ) (g : ℤ → ℂ) (s : Finset ℤ) (q : ℕ) (z : ℤ)
    (x : ℝ) : ℂ :=
  ∑ j ∈ s.filter (fun j => (q:ℤ) ∣ (z+j)), g j * (a *
    FourierTransformInv.fourierInv φ (a * (x + ((j+z:ℤ):ℝ)/(q:ℝ))))

theorem hasCompactSupport_of_Icc {φ : ℝ → ℂ}
    (h : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0) : HasCompactSupport φ :=
  HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-(1/2)) (1/2)) isCompact_Icc
    (fun β hβ => by
      rw [Function.mem_support] at hβ
      by_contra hc
      exact hβ (h β hc))

theorem exists_decay_fourierInv {φ : ℝ → ℂ} (hφcs : HasCompactSupport φ)
    (hφcd : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ,
      ‖FourierTransformInv.fourierInv φ u‖ ≤ C * (1 + u^2)⁻¹ := by
  obtain ⟨C, hC, hCd⟩ :=
    schwartz_decay (FourierTransformInv.fourierInv (hφcs.toSchwartzMap hφcd))
  refine ⟨C, hC, fun u => ?_⟩
  have hcoe : (FourierTransformInv.fourierInv (hφcs.toSchwartzMap hφcd) : ℝ → ℂ)
      = FourierTransformInv.fourierInv φ := by
    rw [SchwartzMap.fourierInv_coe]
    congr 1
  rw [← hcoe]
  exact hCd u

theorem continuous_fourierInv {φ : ℝ → ℂ} (hφint : Integrable φ) :
    Continuous (FourierTransformInv.fourierInv φ) :=
  (continuous_invTransform φ hφint).congr (fun x => (fourierInv_eq_integral φ x).symm)

theorem fourierInv_slicedAmp {q : ℕ} (hq : 0 < q) {D : ℝ} (hD : 0 < D) {φ : ℝ → ℂ}
    (hφc : Continuous φ) (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0)
    (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) (x : ℝ) :
    FourierTransformInv.fourierInv (slicedAmp q D φ g s z) x
      = slicedResidue ((q:ℝ)/D) φ g s q z x := by
  rw [fourierInv_eq_integral]
  unfold slicedAmp
  rw [sliced_inverse_transform hq hD hφc hφs g s z x]
  unfold slicedResidue
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hc : (((q:ℝ)/D : ℝ) : ℂ) = ((q:ℂ)/D) := by rw [Complex.ofReal_div]; push_cast; ring
  rw [hc]; push_cast; ring

end
end Commons.Analysis.ExponentialSums


/-! ===== concatenated from window_bridge.lean ===== -/

/-
# The `∑_{a<q}` form of Bourgain's (7.21)

`Work/Analysis/ExponentialSums/model721_slice.lean` proves Bourgain's Lemma 7.20 in the *sliced*
(`γ`-variable, residue-class) form `sliced_maximal_lp`.  This file supplies the identification of
that sliced form with the original `∑_{0≤a<q}`-form of (7.21), i.e. the change of variables
`x = yq + z` together with the residue identity (7.23).
-/

set_option maxHeartbeats 1000000

open MeasureTheory Finset
open scoped ENNReal BigOperators Topology
namespace Commons.Analysis.ExponentialSums
noncomputable section


/-- The exponentials of the two phases agree: for `m = y q + z`,
`e(2πi m (a/q + β)) = e(2πi z a/q) · e(2πi m β)`. -/
theorem exp_phase_split {q : ℕ} (hq : 0 < q) (y z m : ℤ) (hm : m = y * (q:ℤ) + z)
    (a : ℕ) (β : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * ((((a : ℝ) / (q : ℝ) + β : ℝ)) : ℂ))
      = Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (z : ℂ) / (q : ℂ)))
        * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (β : ℂ)) := by
  have hqC : ((q : ℂ)) ≠ 0 := by exact_mod_cast hq.ne'
  have hin : ((((a : ℝ) / (q : ℝ) + β : ℝ)) : ℂ) = ((a : ℂ) / (q : ℂ) + (β : ℂ)) := by
    push_cast; ring
  have hmC : (m : ℂ) = (y : ℂ) * (q : ℂ) + (z : ℂ) := by
    rw [hm]; push_cast; ring
  have hmain : (m : ℂ) * ((a : ℂ) / (q : ℂ)) = ((y * a : ℤ) : ℂ) + (z : ℂ) * ((a : ℂ) / (q : ℂ)) := by
    have hh : (y:ℂ) * (q:ℂ) * (a:ℂ) / (q:ℂ) = ((y*a:ℤ):ℂ) := by
      rw [div_eq_iff hqC]; push_cast; ring
    rw [← mul_div_assoc (m:ℂ) (a:ℂ) (q:ℂ), ← mul_div_assoc (z:ℂ) (a:ℂ) (q:ℂ),
      hmC, add_mul, add_div, hh]
  have hX : 2 * Real.pi * Complex.I * (m : ℂ) * ((((a : ℝ) / (q : ℝ) + β : ℝ)) : ℂ)
      = ((y * a : ℤ) : ℂ) * (2 * Real.pi * Complex.I)
        + (2 * Real.pi * Complex.I * ((a : ℂ) * (z : ℂ) / (q : ℂ))
            + 2 * Real.pi * Complex.I * (m : ℂ) * (β : ℂ)) := by
    rw [hin]
    have h1 : (m : ℂ) * ((a : ℂ) / (q : ℂ) + (β : ℂ))
        = ((y * a : ℤ) : ℂ) + ((a : ℂ) * (z : ℂ) / (q : ℂ) + (m : ℂ) * (β : ℂ)) := by
      rw [mul_add, hmain]
      have h2 : ((y * a : ℤ) : ℂ) + (z : ℂ) * ((a : ℂ) / (q : ℂ)) + (m : ℂ) * (β : ℂ)
          = ((y * a : ℤ) : ℂ) + ((a : ℂ) * (z : ℂ) / (q : ℂ) + (m : ℂ) * (β : ℂ)) := by ring
      rw [h2]
    rw [show 2 * Real.pi * Complex.I * (m : ℂ) * ((a : ℂ) / (q : ℂ) + (β : ℂ))
        = 2 * Real.pi * Complex.I * ((m : ℂ) * ((a : ℂ) / (q : ℂ) + (β : ℂ))) by ring, h1]
    ring
  rw [hX, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul, Complex.exp_add]

section Bridge

variable {q : ℕ} {D : ℝ} {φ : ℝ → ℂ} {g : ℤ → ℂ} {s : Finset ℤ}

end Bridge

section Main

/-- The `a`-th summand of the `∑_{a<q}`-form of (7.21), after the phase `e(2πi z a/q)` has been
pulled out (so that the residue identity (7.23) applies to the `a`-sum). -/
def windowFac (q : ℕ) (z : ℤ) (a : ℕ) (g : ℤ → ℂ) (s : Finset ℤ) (β : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (z : ℂ) / (q : ℂ)))
  * (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I *
      ((j : ℂ) * ((((a : ℝ) / (q : ℝ) + β : ℝ)) : ℂ))))

/-- The residue identity (7.23) in the shape of `windowFac`. -/
theorem windowFac_sum (q : ℕ) (z : ℤ) (g : ℤ → ℂ) (s : Finset ℤ) (β : ℝ) :
    (∑ a ∈ Finset.range q, windowFac q z a g s β)
      = (q : ℂ) * ∑ j ∈ s.filter (fun j => (q:ℤ) ∣ (z+j)),
          g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (β : ℂ))) := by
  simp only [windowFac]
  rw [residue_sum_identity q g s z β]

open scoped ComplexOrder in
/-- `ring`-only rearrangement used inside `windowBlock_eq_sum_windowSummand` (kept separate so
that `ring` never has to look at the definitions of `Complex.exp` or `fresnelProfile`). -/
theorem mul_rearr (S F ph Ea Em : ℂ) :
    S * F * ph * (Ea * Em) = Ea * S * (F * ph) * Em := by ring

/-- Abstract substitution `β = γ/q` (change of variables on `ℝ`). -/
theorem mul_integral_comp_div (q : ℕ) (hq : 0 < q) (H : ℝ → ℂ) :
    (q : ℂ) * (∫ β : ℝ, H β) = ∫ γ : ℝ, H (γ/(q:ℝ)) := by
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have h2 := Measure.integral_comp_mul_left H ((q:ℝ)⁻¹)
  rw [inv_inv, abs_of_pos hqR] at h2
  have hcast : (q : ℂ) * (∫ β : ℝ, H β) = (q:ℝ) • ∫ β : ℝ, H β := by
    rw [Complex.real_smul, Complex.ofReal_natCast]
  rw [hcast, ← h2]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun γ => ?_))
  congr 1
  ring

/-- `windowFac` is continuous. -/
theorem continuous_windowFac (q : ℕ) (z : ℤ) (a : ℕ) (g : ℤ → ℂ) (s : Finset ℤ) :
    Continuous (windowFac q z a g s) := by
  rw [show windowFac q z a g s = fun β : ℝ =>
      Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (z : ℂ) / (q : ℂ)))
      * (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I *
          ((j : ℂ) * ((((a : ℝ) / (q : ℝ) + β : ℝ)) : ℂ)))) from funext (fun β => by rw [windowFac])]
  fun_prop

end Main

end


/-! ===== concatenated from window_maximal.lean ===== -/

/-
# Bourgain's (7.21) in the `∑_{a<q}`-form: the ℓ^p maximal bound

`window_bridge.lean` identifies the `∑_{0≤a<q}`-form of (7.21) with the sliced form of
`model721_slice.lean`.  This file reindexes `ℤ = ⊔_{z<q} (qℤ+z)` to deduce the ℓ^p maximal bound
for the `∑_{a<q}`-form (Bourgain's (7.21) verbatim) from `sliced_maximal_lp`.
-/

open MeasureTheory Finset
open scoped ENNReal BigOperators Topology
namespace Commons.Analysis.ExponentialSums
noncomputable section

/-- `(c % q).toNat < q`. -/
theorem emod_toNat_lt (q : ℕ) [NeZero q] (c : ℤ) : (c % (q:ℤ)).toNat < q := by
  have hq : (0:ℤ) < (q:ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have h1 : 0 ≤ c % (q:ℤ) := Int.emod_nonneg c (ne_of_gt hq)
  rw [Int.toNat_lt h1]
  exact Int.emod_lt_of_pos c hq

/-- `(y q + z) % q = z` for `0 ≤ z < q`. -/
theorem add_mul_emod_eq (q : ℕ) [NeZero q] (y : ℤ) (z : Fin q) :
    (y * (q:ℤ) + (z:ℤ)) % (q:ℤ) = (z:ℤ) := by
  have hq : (0:ℤ) < (q:ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hz0 : 0 ≤ (z:ℤ) := Int.natCast_nonneg z.1
  have hzq : (z:ℤ) < (q:ℤ) := by exact_mod_cast z.2
  rw [show y * (q:ℤ) + (z:ℤ) = (z:ℤ) + y * (q:ℤ) by ring,
    Int.add_mul_emod_self_right (z:ℤ) y (q:ℤ), Int.emod_eq_of_lt hz0 hzq]

/-- `(y q + z) / q = y` for `0 ≤ z < q`. -/
theorem add_mul_ediv_eq (q : ℕ) [NeZero q] (y : ℤ) (z : Fin q) :
    (y * (q:ℤ) + (z:ℤ)) / (q:ℤ) = y := by
  have hq : (0:ℤ) < (q:ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hz0 : 0 ≤ (z:ℤ) := Int.natCast_nonneg z.1
  have hzq : (z:ℤ) < (q:ℤ) := by exact_mod_cast z.2
  rw [show y * (q:ℤ) + (z:ℤ) = (z:ℤ) + y * (q:ℤ) by ring,
    Int.add_mul_ediv_right (z:ℤ) y (ne_of_gt hq), Int.ediv_eq_zero_of_lt hz0 hzq, zero_add]

/-- The bijection `ℤ ≃ ℤ × Fin q`, `c ↦ (c / q, c % q)`. -/
def zmodEquiv (q : ℕ) [NeZero q] : ℤ ≃ ℤ × Fin q where
  toFun c := (c / (q:ℤ), ⟨(c % (q:ℤ)).toNat, emod_toNat_lt q c⟩)
  invFun p := p.1 * (q:ℤ) + (p.2 : ℤ)
  left_inv c := by
    have hq : (0:ℤ) < (q:ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    have h1 : 0 ≤ c % (q:ℤ) := Int.emod_nonneg c (ne_of_gt hq)
    show c / (q:ℤ) * (q:ℤ) + (((c % (q:ℤ)).toNat : ℕ) : ℤ) = c
    rw [Int.toNat_of_nonneg h1]
    exact Int.ediv_mul_add_emod c (q:ℤ)
  right_inv p := by
    obtain ⟨y, z⟩ := p
    show ((y * (q:ℤ) + (z:ℤ)) / (q:ℤ),
      (⟨((y * (q:ℤ) + (z:ℤ)) % (q:ℤ)).toNat, emod_toNat_lt q (y * (q:ℤ) + (z:ℤ))⟩ : Fin q)) = (y, z)
    have hfin : (⟨((y * (q:ℤ) + (z:ℤ)) % (q:ℤ)).toNat,
        emod_toNat_lt q (y * (q:ℤ) + (z:ℤ))⟩ : Fin q) = z := by
      have hval : ((y * (q:ℤ) + (z:ℤ)) % (q:ℤ)).toNat = z.1 := by
        rw [add_mul_emod_eq q y z]
        exact Int.toNat_natCast z.1
      exact Fin.ext hval
    exact Prod.ext (add_mul_ediv_eq q y z) hfin

/-- The inverse law, in the shape needed below. -/
theorem zmodEquiv_inv (q : ℕ) [NeZero q] (c : ℤ) :
    (zmodEquiv q c).1 * (q:ℤ) + ((zmodEquiv q c).2 : ℤ) = c :=
  (zmodEquiv q).left_inv c

/-- `{0,…,q-1} ⊆ ℤ` is the image of `range q`. -/
theorem Icc_cast_range (q : ℕ) :
    Finset.Icc (0:ℤ) ((q:ℤ)-1)
      = (Finset.range q).map ⟨(fun n : ℕ => (n:ℤ)), Nat.cast_injective⟩ := by
  ext z
  simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨z.toNat, ?_, ?_⟩
    · have hz : z < (q:ℤ) := by omega
      omega
    · exact Int.toNat_of_nonneg h0
  · rintro ⟨n, hn, rfl⟩
    refine ⟨by positivity, ?_⟩
    omega

/-- The sum over the residue classes, reorganised as a sum over `Fin q`. -/
theorem sum_Icc_eq_sum_fin (q : ℕ) (H : ℤ → ENNReal) :
    (∑ z ∈ Finset.Icc (0:ℤ) ((q:ℤ)-1), H z) = ∑ z : Fin q, H (z:ℤ) := by
  rw [Icc_cast_range, Finset.sum_map]
  exact (Fin.sum_univ_eq_sum_range (fun n : ℕ => H (n:ℤ)) q).symm

/-- **Reindexing `ℤ` by residue classes**: `∑'_ℤ F = ∑_{z<q} ∑'_{y} F(yq+z)`. -/
theorem tsum_int_eq_sum_fin (q : ℕ) [NeZero q] (F : ℤ → ENNReal) :
    ∑' m : ℤ, F m = ∑ z : Fin q, ∑' y : ℤ, F (y * (q:ℤ) + (z : ℤ)) := by
  have h1 : ∑' m : ℤ, F m = ∑' p : ℤ × Fin q, F (p.1 * (q:ℤ) + ((p.2 : ℤ))) := by
    rw [← Equiv.tsum_eq (zmodEquiv q) (fun p : ℤ × Fin q => F (p.1 * (q:ℤ) + ((p.2 : ℤ))))]
    refine tsum_congr (fun c => ?_)
    congr 1
    exact (zmodEquiv_inv q c).symm
  rw [h1, ENNReal.tsum_prod (f := fun (a : ℤ) (b : Fin q) => F (a * (q:ℤ) + (b:ℤ))),
    ENNReal.tsum_comm, tsum_fintype]

end
end Commons.Analysis.ExponentialSums

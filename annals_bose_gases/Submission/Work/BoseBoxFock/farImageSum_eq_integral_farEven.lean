import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.farAnisoDefs
import Submission.Work.BoseBoxFock.farK0_summable_lattice_inv_fourth
import Submission.Work.BoseBoxFock.tsum_lintegral_aliasKernel_imageW_lens_closed
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.farImageSum_eq_integral_farEven`

The far-image lattice series of the aliasing deficit, in the two spellings used in the workspace,
are the same object:

    ∑_{‖latVec m‖ ≥ √2} ∫_u 𝒢(u) ‖u − ℓ•latVec m‖⁻⁴ du
      = ∫_u 𝒢(u) · farEven ℓ u ,

where `𝒢 = aliasKernel g` and

    `farEven ℓ u = ∑_{‖latVec m‖ ≥ √2} ½ (‖u − ℓ•latVec m‖⁻⁴ + ‖u + ℓ•latVec m‖⁻⁴)`

is the reflection-symmetrised far kernel of `farAnisoDefs`.  The identity is what lets the
anisotropy budget `∫𝒢(farEven − farAvg)` of the `farAnisoDefs` chapter feed back into the
(first-moment) aliasing deficit, which is stated with the *one-sided* images `imgW ℓ m u`.

**Mathematical content.**  The index set `{m | √2 ≤ ‖latVec m‖}` is stable under `m ↦ −m`
(`latVec_neg`), and the summand of `farEven` is exactly the symmetrisation
`½(a_m + a_{−m})` of the one-sided far image `a_m(u) = (‖u − ℓ•latVec m‖⁴)⁻¹`.  Since
`∑_m ½(a_m + a_{−m}) = ∑_m a_m` (the two halves are equal by the reindexing `Equiv.neg`), the
pointwise series of `farEven` is the guarded one-sided series `∑_m farTerm ℓ m u`
(`farEven_eq_tsum_farTerm`).  The exchange of `∑_m` with `∫_u` is then
`MeasureTheory.integral_tsum`, whose two hypotheses are (i) the a.e. strong measurability of each
summand, and (ii) the `ℝ≥0∞`-finiteness `∑'_m ∫⁻_u ‖𝒢(u)‖·imgW ℓ m u ≠ ⊤` of the *guarded*
series.  The latter is the corpus's `tsum_lintegral_aliasKernel_imageW_lens_closed`: the guarded
series is dominated termwise by the unguarded one (`farTerm ≤ imgW`).

Note that **no summability of the pointwise series is needed for the exchange**: the `ℝ≥0∞`
criterion of `integral_tsum` is strictly weaker than per-summand integrability.  The pointwise
summability `∑_m (‖u − ℓm‖⁴)⁻¹ < ∞` (`summable_inv_norm_sub_latVec`, an eventual comparison with
the summable lattice kernel `(‖latVec m‖⁴)⁻¹`, `farK0_summable_lattice_inv_fourth`) is needed only
for the *pointwise* series identity `farEven ℓ u = ∑_m farTerm ℓ m u`, through the additivity
`Summable.tsum_add` of two summable series.

## The auxiliary pieces

* `farTerm ℓ m u` — the guarded one-sided image `1_{√2 ≤ ‖latVec m‖}(‖u − ℓ•latVec m‖⁴)⁻¹`;
* `latVec_neg`, `norm_latVec_neg`, `latVec_eq_zero`, `latVec_ne_zero` — the lattice/sign
  bookkeeping;
* `finite_latVec_norm_lt` — the lattice points in a ball are finite (containment in `box N`);
* `summable_inv_norm_sub_latVec` — pointwise summability of the one-sided images;
* `farEven_eq_tsum_farTerm` — the pointwise series identity;
* `imgW_eq_of_guard` — on the far guard, `imgW ℓ m u` *is* the one-sided image (the `m = 0` guard
  of `imgW` is inactive because `√2 ≤ ‖latVec 0‖ = 0` is false).
-/

noncomputable section

open MeasureTheory Filter
open scoped Real BigOperators ENNReal

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The guarded one-sided image term -/

/-- The **guarded one-sided far image** `1_{√2 ≤ ‖latVec m‖}·(‖u − ℓ•latVec m‖⁴)⁻¹`.  For far
indices (`‖latVec m‖ ≥ √2`, in particular `m ≠ 0`) this is exactly `imgW ℓ m u`
(`imgW_eq_of_guard`); on the touching/zero indices it is `0`. -/
noncomputable def farTerm (ℓ : ℝ) (m : Fin 3 → ℤ) (u : E3) : ℝ :=
  if Real.sqrt 2 ≤ ‖latVec m‖ then (‖u - ℓ • latVec m‖ ^ 4)⁻¹ else 0

lemma farTerm_nonneg (ℓ : ℝ) (m : Fin 3 → ℤ) (u : E3) : 0 ≤ farTerm ℓ m u := by
  rw [farTerm]
  split_ifs with h
  · exact inv_nonneg.mpr (pow_nonneg (norm_nonneg _) 4)
  · exact le_refl 0

lemma farTerm_le_inv (ℓ : ℝ) (m : Fin 3 → ℤ) (u : E3) :
    farTerm ℓ m u ≤ (‖u - ℓ • latVec m‖ ^ 4)⁻¹ := by
  rw [farTerm]
  split_ifs with h
  · exact le_refl _
  · exact inv_nonneg.mpr (pow_nonneg (norm_nonneg _) 4)

/-! ## 2. Lattice bookkeeping -/

lemma latVec_neg (m : Fin 3 → ℤ) : latVec (-m) = -latVec m := by
  ext i
  simp [latVec_apply]

lemma norm_latVec_neg (m : Fin 3 → ℤ) : ‖latVec (-m)‖ = ‖latVec m‖ := by
  rw [latVec_neg, norm_neg]

/-- `latVec` is injective: the lattice vector determines the multi-index. -/
lemma latVec_eq_zero {m : Fin 3 → ℤ} (h : latVec m = 0) : m = 0 := by
  funext i
  have h2 : ((m i : ℤ) : ℝ) = ((0 : ℤ) : ℝ) := by
    have h3 := congrFun (congrArg WithLp.ofLp h) i
    simpa [latVec_apply] using h3
  exact Int.cast_injective h2

lemma latVec_ne_zero {m : Fin 3 → ℤ} (hm : m ≠ 0) : latVec m ≠ 0 := fun h =>
  hm (latVec_eq_zero h)

/-! ## 3. Finiteness of the lattice points in a ball -/

/-- There are only finitely many lattice vectors in a ball.  Each coordinate of `m` is bounded by
the sup-norm `K m`, which is at most the Euclidean norm `‖latVec m‖`, so the set is contained in
the integer box `box N` for any `N ≥ c`. -/
lemma finite_latVec_norm_lt (c : ℝ) : {m : Fin 3 → ℤ | ‖latVec m‖ < c}.Finite := by
  refine (box ⌈max c 0⌉₊).finite_toSet.subset ?_
  intro m hm
  rw [Finset.mem_coe, mem_box_iff]
  intro i
  have h1 : (m i).natAbs ≤ K m := K_spec m i
  have h2 : (K m : ℝ) ≤ ‖latVec m‖ := K_le_norm_latVec m
  have h3 : (K m : ℝ) < (⌈max c 0⌉₊ : ℝ) :=
    lt_of_le_of_lt h2 (lt_of_lt_of_le hm (le_trans (le_max_left c 0) (Nat.le_ceil _)))
  have h4 : K m < ⌈max c 0⌉₊ := by exact_mod_cast h3
  exact le_of_lt (lt_of_le_of_lt h1 h4)

/-! ## 4. Pointwise summability of the one-sided far images -/

/-- The one-sided far images are pointwise summable: for `‖latVec m‖ ≥ 2‖u‖/ℓ` (all but
finitely many `m`, `finite_latVec_norm_lt` with the `m = 0` term removed separately) one has
`‖u − ℓ•latVec m‖ ≥ (ℓ/2)·‖latVec m‖`, hence
`(‖u − ℓ•latVec m‖⁴)⁻¹ ≤ (ℓ/2)⁻⁴·(‖latVec m‖⁴)⁻¹`, and the lattice kernel `(‖latVec m‖⁴)⁻¹` is
summable (`farK0_summable_lattice_inv_fourth`). -/
lemma summable_inv_norm_sub_latVec {ℓ : ℝ} (hℓ : 0 < ℓ) (u : E3) :
    Summable (fun m : Fin 3 → ℤ => (‖u - ℓ • latVec m‖ ^ 4)⁻¹) := by
  refine Summable.of_norm_bounded_eventually (g := fun m : Fin 3 → ℤ =>
      ((ℓ / 2) ^ 4)⁻¹ * ((‖latVec m‖ ^ 4)⁻¹))
    ((farK0_summable_lattice_inv_fourth).mul_left _) ?_
  have hev : ∀ᶠ m : Fin 3 → ℤ in Filter.cofinite,
      (2 * ‖u‖ / ℓ ≤ ‖latVec m‖) ∧ m ≠ 0 := by
    rw [Filter.eventually_cofinite]
    refine ((finite_latVec_norm_lt (2 * ‖u‖ / ℓ)).union
      (Set.finite_singleton (0 : Fin 3 → ℤ))).subset ?_
    intro m hm
    rcases not_and_or.mp hm with h | h
    · exact Or.inl (lt_of_not_ge h)
    · exact Or.inr (by simpa using not_not.mp h)
  filter_upwards [hev] with m hm
  obtain ⟨hc, hne⟩ := hm
  have hDpos : 0 < ‖latVec m‖ := by
    rw [norm_pos_iff]
    exact latVec_ne_zero hne
  have hkey : (ℓ / 2) * ‖latVec m‖ ≤ ‖u - ℓ • latVec m‖ := by
    have h1 : ‖ℓ • latVec m‖ - ‖u‖ ≤ ‖ℓ • latVec m - u‖ := norm_sub_norm_le _ _
    rw [norm_sub_rev] at h1
    rw [norm_smul, Real.norm_of_nonneg hℓ.le] at h1
    have h2 : ‖u‖ ≤ ℓ * ‖latVec m‖ / 2 := by
      rw [div_le_iff₀ hℓ] at hc
      linarith
    linarith
  have hpos : 0 < (ℓ / 2) * ‖latVec m‖ := by positivity
  have hppos : 0 < ‖u - ℓ • latVec m‖ := lt_of_lt_of_le hpos hkey
  have hmain : (‖u - ℓ • latVec m‖ ^ 4)⁻¹ ≤ (((ℓ / 2) * ‖latVec m‖) ^ 4)⁻¹ :=
    (inv_le_inv₀ (pow_pos hppos 4) (pow_pos hpos 4)).mpr (pow_le_pow_left₀ hpos.le hkey 4)
  have h6 : (((ℓ / 2) * ‖latVec m‖) ^ 4)⁻¹ = ((ℓ / 2) ^ 4)⁻¹ * ((‖latVec m‖ ^ 4)⁻¹) := by
    rw [mul_pow, mul_inv, mul_comm]
  rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (‖u - ℓ • latVec m‖ ^ 4)⁻¹)]
  exact hmain.trans h6.le

/-! ## 5. The pointwise series identity -/

/-- **The pointwise series identity.**  The symmetrised far kernel `farEven ℓ u` is the guarded
one-sided far-image series `∑_m 1_{√2 ≤ ‖latVec m‖}(‖u − ℓ•latVec m‖⁴)⁻¹`.

Indeed the summand of `farEven` is `½(a_m + a_{−m})`, and `∑_m ½(a_m + a_{−m}) = ∑_m a_m`
because `∑_m a_{−m} = ∑_m a_m` (`Equiv.neg`) and `∑_m a_m` is summable. -/
theorem farEven_eq_tsum_farTerm {ℓ : ℝ} (hℓ : 0 < ℓ) (u : E3) :
    farEven ℓ u = ∑' m : Fin 3 → ℤ, farTerm ℓ m u := by
  have hF : Summable (fun m : Fin 3 → ℤ => farTerm ℓ m u) :=
    Summable.of_nonneg_of_le (f := fun m : Fin 3 → ℤ => (‖u - ℓ • latVec m‖ ^ 4)⁻¹)
      (fun m => farTerm_nonneg ℓ m u) (fun m => farTerm_le_inv ℓ m u)
      (summable_inv_norm_sub_latVec hℓ u)
  have hFneg : Summable (fun m : Fin 3 → ℤ => farTerm ℓ (-m) u) :=
    hF.comp_injective fun a b h => by simpa using neg_inj.mp h
  have hstep : ∀ m : Fin 3 → ℤ,
      (if Real.sqrt 2 ≤ ‖latVec m‖ then
        (2 : ℝ)⁻¹ * ((‖u - ℓ • latVec m‖ ^ 4)⁻¹ + (‖u + ℓ • latVec m‖ ^ 4)⁻¹) else 0)
        = (2 : ℝ)⁻¹ * (farTerm ℓ m u + farTerm ℓ (-m) u) := by
    intro m
    by_cases hc : Real.sqrt 2 ≤ ‖latVec m‖
    · have hc' : Real.sqrt 2 ≤ ‖latVec (-m)‖ := by
        rw [norm_latVec_neg]; exact hc
      rw [if_pos hc, farTerm, if_pos hc, farTerm, if_pos hc']
      have h4 : ℓ • latVec (-m) = -(ℓ • latVec m) := by rw [latVec_neg, smul_neg]
      rw [h4, sub_neg_eq_add]
    · have hc' : ¬ (Real.sqrt 2 ≤ ‖latVec (-m)‖) := by
        rw [norm_latVec_neg]; exact hc
      rw [if_neg hc, farTerm, if_neg hc, farTerm, if_neg hc']
      ring
  rw [farEven]
  rw [tsum_congr hstep, tsum_mul_left, Summable.tsum_add hF hFneg]
  rw [show (∑' m : Fin 3 → ℤ, farTerm ℓ (-m) u) = ∑' m : Fin 3 → ℤ, farTerm ℓ m u from
    by simpa using Equiv.tsum_eq (Equiv.neg (Fin 3 → ℤ)) (fun m => farTerm ℓ m u)]
  ring

/-! ## 6. `imgW` on the far guard -/

/-- On the far indices the `m = 0` guard of `imgW` is inactive, so `imgW ℓ m u` is the one-sided
image `(‖u − ℓ•latVec m‖⁴)⁻¹`. -/
lemma imgW_eq_of_guard {ℓ : ℝ} {m : Fin 3 → ℤ} (hm : Real.sqrt 2 ≤ ‖latVec m‖) (u : E3) :
    imgW ℓ m u = (‖u - ℓ • latVec m‖ ^ 4)⁻¹ := by
  have hm0 : m ≠ 0 := by
    intro h
    subst h
    have h0 : ‖latVec (0 : Fin 3 → ℤ)‖ = 0 := by
      rw [show latVec (0 : Fin 3 → ℤ) = 0 from by ext i; simp [latVec_apply]]
      exact norm_zero
    rw [h0] at hm
    have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
    linarith
  rw [imgW_ne_zero hm0]

/-! ## 7. The target -/

theorem farImageSum_eq_integral_farEven {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2)) :
    (∑' m : Fin 3 → ℤ, (if Real.sqrt 2 ≤ ‖Work.BoseBoxFock.latVec m‖
        then ∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseBoxFock.aliasKernel g u *
          Work.BoseBoxFock.imgW ℓ m u else 0))
      = ∫ u : EuclideanSpace ℝ (Fin 3),
          Work.BoseBoxFock.aliasKernel g u * Work.BoseBoxFock.farEven ℓ u := by
  have hgc : HasCompactSupport g := hasCompactSupport_of_closedBall hgsupp
  have hGcont : Continuous (fun u : E3 => aliasKernel g u) :=
    Complex.continuous_re.comp (autocorr_continuous hg hgc)
  -- (i) a.e. strong measurability of the summands
  have hmeas : ∀ m : Fin 3 → ℤ,
      AEStronglyMeasurable (fun u : E3 => aliasKernel g u * farTerm ℓ m u) volume := by
    intro m
    have hFm : Measurable (fun u : E3 => farTerm ℓ m u) := by
      by_cases hc : Real.sqrt 2 ≤ ‖latVec m‖
      · have hfun : (fun u : E3 => farTerm ℓ m u) = fun u : E3 => (‖u - ℓ • latVec m‖ ^ 4)⁻¹ := by
          funext u; rw [farTerm, if_pos hc]
        rw [hfun]
        exact (((continuous_norm.comp (continuous_id.sub continuous_const)).pow 4).measurable).inv
      · have hfun : (fun u : E3 => farTerm ℓ m u) = fun _ : E3 => (0 : ℝ) := by
          funext u; rw [farTerm, if_neg hc]
        rw [hfun]
        exact measurable_const
    exact (hGcont.measurable.mul hFm).aestronglyMeasurable
  -- (ii) the `ℝ≥0∞`-finiteness of the guarded series, by comparison with `imgW`
  have hcond : (∑' m : Fin 3 → ℤ, ∫⁻ u : E3, ‖aliasKernel g u * farTerm ℓ m u‖ₑ) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (tsum_lintegral_aliasKernel_imageW_lens_closed hℓ hg hgsupp)
      (ENNReal.tsum_le_tsum fun m => ?_)
    refine lintegral_mono fun u => ?_
    have hle : farTerm ℓ m u ≤ imgW ℓ m u := by
      rw [farTerm]
      split_ifs with h
      · rw [imgW_eq_of_guard h u]
      · exact imgW_nonneg ℓ m u
    rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (farTerm_nonneg ℓ m u), Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hle (abs_nonneg _))
  -- the per-`m` identification of the guarded integral with the `imgW` integral
  have hterm : ∀ m : Fin 3 → ℤ,
      (if Real.sqrt 2 ≤ ‖latVec m‖ then ∫ u : E3, aliasKernel g u * imgW ℓ m u else 0)
        = ∫ u : E3, aliasKernel g u * farTerm ℓ m u := by
    intro m
    by_cases hc : Real.sqrt 2 ≤ ‖latVec m‖
    · rw [if_pos hc]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      show aliasKernel g u * imgW ℓ m u = aliasKernel g u * farTerm ℓ m u
      rw [farTerm, if_pos hc, imgW_eq_of_guard hc u]
    · rw [if_neg hc]
      have hfun : (fun u : E3 => aliasKernel g u * farTerm ℓ m u) = fun _ : E3 => (0 : ℝ) := by
        funext u
        show aliasKernel g u * farTerm ℓ m u = (0 : ℝ)
        rw [farTerm, if_neg hc, mul_zero]
      rw [hfun, integral_zero]
  rw [show (∑' m : Fin 3 → ℤ, (if Real.sqrt 2 ≤ ‖latVec m‖ then
        ∫ u : E3, aliasKernel g u * imgW ℓ m u else 0))
      = ∑' m : Fin 3 → ℤ, ∫ u : E3, aliasKernel g u * farTerm ℓ m u from tsum_congr hterm]
  rw [← MeasureTheory.integral_tsum hmeas hcond]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  show (∑' m : Fin 3 → ℤ, aliasKernel g u * farTerm ℓ m u) = aliasKernel g u * farEven ℓ u
  rw [tsum_mul_left, farEven_eq_tsum_farTerm hℓ u]

end Work.BoseBoxFock

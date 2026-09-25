import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc

namespace Work.CR.Flat.Cauchy

noncomputable section

open scoped NNReal ENNReal
open Set

/-- If `g` vanishes on the closed complement of the open polydisc `P(r)`, then all of its
(ambient) iterated derivatives vanish at every point where some coordinate is *strictly*
outside `P(r)`. -/
lemma iteratedFDeriv_eq_zero_of_vanishing_off_polydisc {n : ℕ} {c : Fin n → ℂ}
    {r : Fin n → ℝ} {g : (Fin n → ℂ) → ℂ}
    (hsupp : ∀ z, (∃ i, r i ≤ ‖z i - c i‖) → g z = 0)
    (m : ℕ) {z : Fin n → ℂ} (hz : ∃ i, r i < ‖z i - c i‖) :
    iteratedFDeriv ℝ m g z = 0 := by
  obtain ⟨i, hi⟩ := hz
  have hopen : IsOpen {w : Fin n → ℂ | r i < ‖w i - c i‖} :=
    isOpen_lt continuous_const ((continuous_apply i).sub continuous_const).norm
  have h0 : g =ᶠ[nhds z] (fun _ => (0 : ℂ)) := by
    filter_upwards [hopen.mem_nhds hi] with w hw
    exact hsupp w ⟨i, le_of_lt hw⟩
  have h1 : iteratedFDeriv ℝ m g =ᶠ[nhds z] iteratedFDeriv ℝ m (fun _ => (0 : ℂ)) :=
    h0.iteratedFDeriv ℝ m
  simpa using h1.eq_of_nhds

/-- If `z ∉ P(r')` then some coordinate of `z` is at least `r' i`, whence also strictly
outside `P(r)`. -/
lemma exists_le_of_notMem_polydisc {n : ℕ} {c : Fin n → ℂ} {r' : Fin n → ℝ}
    {z : Fin n → ℂ} (hz : z ∉ polydisc c r') : ∃ j, r' j ≤ ‖z j - c j‖ := by
  by_contra hc
  exact hz fun j => not_le.mp (not_exists.mp hc j)

/-- The ambient `Set.univ` iterated derivative at a point of `P(r')` agrees with the
iterated derivative within `P(r')`. -/
lemma iteratedFDerivWithin_univ_eq_of_mem_polydisc {n : ℕ} {c : Fin n → ℂ}
    {r' : Fin n → ℝ} {g : (Fin n → ℂ) → ℂ} (m : ℕ) {z : Fin n → ℂ}
    (hz : z ∈ polydisc c r') :
    iteratedFDerivWithin ℝ m g Set.univ z
      = iteratedFDerivWithin ℝ m g (polydisc c r') z := by
  rw [iteratedFDerivWithin_univ]
  exact ((iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) m (isOpen_polydisc c r')) hz).symm

/-- The ambient `Set.univ` iterated derivative vanishes at every point outside `P(r')`. -/
lemma iteratedFDerivWithin_univ_eq_zero_of_notMem_polydisc {n : ℕ} {c : Fin n → ℂ}
    {r r' : Fin n → ℝ} (h : ∀ j, r j < r' j) {g : (Fin n → ℂ) → ℂ}
    (hsupp : ∀ z, (∃ i, r i ≤ ‖z i - c i‖) → g z = 0)
    (m : ℕ) {z : Fin n → ℂ} (hz : z ∉ polydisc c r') :
    iteratedFDerivWithin ℝ m g Set.univ z = 0 := by
  rw [iteratedFDerivWithin_univ]
  obtain ⟨i, hi⟩ := exists_le_of_notMem_polydisc hz
  exact iteratedFDeriv_eq_zero_of_vanishing_off_polydisc hsupp m
    ⟨i, lt_of_lt_of_le (h i) hi⟩

/-- **Geometry in the polydisc.** If `x ∈ P(r')` and the `i`-th coordinate of `y` has
`r' i ≤ ‖y i - c i‖`, then there is a point `z ∈ P(r')` with the `i`-th coordinate of `z`
strictly outside `P(r)` (so `g` vanishes near `z`) and `‖x - z‖ ≤ ‖x - y‖`.  The point `z`
agrees with `x` outside the `i`-th coordinate.

This mirrors the one-variable `Work.CR.Flat.Holder.exists_near_point`. -/
lemma exists_polydisc_vanishing_point {n : ℕ} {c : Fin n → ℂ} {r r' : Fin n → ℝ}
    (h : ∀ j, r j < r' j) {i : Fin n} {x y : Fin n → ℂ}
    (hx : x ∈ polydisc c r') (hy : r' i ≤ ‖y i - c i‖) :
    ∃ z ∈ polydisc c r', r i < ‖z i - c i‖ ∧ ‖x - z‖ ≤ ‖x - y‖ := by
  have hxi : ‖x i - c i‖ < r' i := hx i
  set ρ : ℝ := max ‖x i - c i‖ ((r i + r' i) / 2) with hρdef
  have hρ_r : r i < ρ := by
    rw [hρdef]; linarith [le_max_right (‖x i - c i‖) ((r i + r' i) / 2), h i]
  have hρ_r' : ρ < r' i := by
    rw [hρdef]; exact max_lt hxi (by linarith [h i])
  have hρ_nn : 0 ≤ ρ := by
    rw [hρdef]; exact le_trans (norm_nonneg _) (le_max_left _ _)
  have hd_le_ρ : ‖x i - c i‖ ≤ ρ := by rw [hρdef]; exact le_max_left _ _
  by_cases hd0 : x i - c i = 0
  · have hxci : x i = c i := sub_eq_zero.mp hd0
    refine ⟨Function.update x i (c i + (ρ : ℂ)), ?_, ?_, ?_⟩
    · rw [mem_polydisc]
      intro j
      by_cases hji : j = i
      · rw [hji, Function.update_self]
        have : c i + (ρ : ℂ) - c i = (ρ : ℂ) := by ring
        rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ_nn]
        exact hρ_r'
      · rw [Function.update_of_ne hji]; exact hx j
    · rw [Function.update_self]
      have hz : c i + (ρ : ℂ) - c i = (ρ : ℂ) := by ring
      rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ_nn]
      exact hρ_r
    · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
      intro j
      by_cases hji : j = i
      · rw [hji, Pi.sub_apply, Function.update_self]
        have hval : ‖x i - (c i + (ρ : ℂ))‖ = ρ := by
          rw [hxci]
          have : c i - (c i + (ρ : ℂ)) = -(ρ : ℂ) := by ring
          rw [this, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ_nn]
        rw [hval]
        have hy' : r' i ≤ ‖x i - y i‖ := by rw [hxci, norm_sub_rev]; exact hy
        exact le_trans (le_of_lt hρ_r') (le_trans hy' (norm_le_pi_norm (x - y) i))
      · rw [Pi.sub_apply, Function.update_of_ne hji]; simp
  · set s : ℂ := ((ρ / ‖x i - c i‖ : ℝ) : ℂ) with hsdef
    have hdpos : 0 < ‖x i - c i‖ := norm_pos_iff.mpr hd0
    have hsd : ‖s‖ = ρ / ‖x i - c i‖ := by
      rw [hsdef, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      exact div_nonneg hρ_nn (le_of_lt hdpos)
    have hwd : ‖s * (x i - c i)‖ = ρ := by
      rw [norm_mul, hsd]
      exact div_mul_cancel₀ ρ (ne_of_gt hdpos)
    refine ⟨Function.update x i (c i + s * (x i - c i)), ?_, ?_, ?_⟩
    · rw [mem_polydisc]
      intro j
      by_cases hji : j = i
      · rw [hji, Function.update_self]
        have : c i + s * (x i - c i) - c i = s * (x i - c i) := by ring
        rw [this, hwd]; exact hρ_r'
      · rw [Function.update_of_ne hji]; exact hx j
    · rw [Function.update_self]
      have hz : c i + s * (x i - c i) - c i = s * (x i - c i) := by ring
      rw [hz, hwd]; exact hρ_r
    · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
      intro j
      by_cases hji : j = i
      · rw [hji, Pi.sub_apply, Function.update_self]
        have hne : ‖x i - c i‖ ≠ 0 := ne_of_gt hdpos
        have hval : ‖x i - (c i + s * (x i - c i))‖ = ρ - ‖x i - c i‖ := by
          have he : x i - (c i + s * (x i - c i)) = (1 - s) * (x i - c i) := by ring
          rw [he, norm_mul]
          have h1s : ‖(1 : ℂ) - s‖ = ρ / ‖x i - c i‖ - 1 := by
            rw [hsdef, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
              Real.norm_eq_abs]
            have hle : (1 : ℝ) - ρ / ‖x i - c i‖ ≤ 0 := by
              have h1 : 1 ≤ ρ / ‖x i - c i‖ :=
                (le_div_iff₀ hdpos).mpr (by linarith [hd_le_ρ])
              linarith
            rw [abs_of_nonpos hle]; ring
          rw [h1s]
          rw [show ρ / ‖x i - c i‖ - 1 = (ρ - ‖x i - c i‖) / ‖x i - c i‖ by field_simp]
          rw [div_mul_cancel₀ _ hne]
        rw [hval]
        have hyi : ρ - ‖x i - c i‖ ≤ ‖x i - y i‖ := by
          have h3 : ‖y i - c i‖ - ‖x i - c i‖ ≤ ‖x i - y i‖ := by
            have h2 := norm_sub_norm_le (y i - c i) (x i - c i)
            have he : ‖(y i - c i) - (x i - c i)‖ = ‖x i - y i‖ := by
              have : (y i - c i) - (x i - c i) = -(x i - y i) := by ring
              rw [this, norm_neg]
            rwa [he] at h2
          linarith [hy]
        exact le_trans hyi (norm_le_pi_norm (x - y) i)
      · rw [Pi.sub_apply, Function.update_of_ne hji]; simp

/-- **The pointwise Hölder term.** For `u ∈ P(r')` and `v` with some coordinate at least
`r' j`, the Hölder term of the pair `(u, v)` (computed with *ambient* derivatives) is
bounded by the Hölder seminorm on `P(r')`. -/
lemma holderSeminorm_term_le_polydisc_of_vanishing {n : ℕ} {c : Fin n → ℂ} {r r' : Fin n → ℝ}
    (h : ∀ j, r j < r' j) {g : (Fin n → ℂ) → ℂ}
    (hsupp : ∀ z, (∃ i, r i ≤ ‖z i - c i‖) → g z = 0)
    {m : ℕ} {α : ℝ} (hα : 0 ≤ α) {u v : Fin n → ℂ}
    (hu : u ∈ polydisc c r') (hv : ∃ j, r' j ≤ ‖v j - c j‖) :
    ENNReal.ofReal
        (‖iteratedFDerivWithin ℝ m g Set.univ u - iteratedFDerivWithin ℝ m g Set.univ v‖
          / ‖u - v‖ ^ α)
      ≤ holderSeminorm m α g (polydisc c r') := by
  obtain ⟨j, hvj⟩ := hv
  have hAv : iteratedFDerivWithin ℝ m g Set.univ v = 0 :=
    iteratedFDerivWithin_univ_eq_zero_of_notMem_polydisc h hsupp m
      (fun hc => absurd (hc j) (not_lt.mpr hvj))
  obtain ⟨z, hzP, hzr, hzdist⟩ := exists_polydisc_vanishing_point h hu hvj
  have hAz : iteratedFDerivWithin ℝ m g Set.univ z = 0 := by
    rw [iteratedFDerivWithin_univ]
    exact iteratedFDeriv_eq_zero_of_vanishing_off_polydisc hsupp m ⟨j, hzr⟩
  have hv0 : iteratedFDerivWithin ℝ m g Set.univ u - iteratedFDerivWithin ℝ m g Set.univ v
      = iteratedFDerivWithin ℝ m g Set.univ u - iteratedFDerivWithin ℝ m g Set.univ z := by
    rw [hAv, hAz]
  rw [hv0]
  by_cases huz : u = z
  · rw [huz]; simp
  · have huzpos : 0 < ‖u - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huz)
    have hstep : ENNReal.ofReal
          (‖iteratedFDerivWithin ℝ m g Set.univ u - iteratedFDerivWithin ℝ m g Set.univ z‖
            / ‖u - v‖ ^ α)
        ≤ ENNReal.ofReal
          (‖iteratedFDerivWithin ℝ m g Set.univ u - iteratedFDerivWithin ℝ m g Set.univ z‖
            / ‖u - z‖ ^ α) := by
      apply ENNReal.ofReal_le_ofReal
      refine div_le_div_of_nonneg_left (norm_nonneg _) (Real.rpow_pos_of_pos huzpos α) ?_
      exact Real.rpow_le_rpow (norm_nonneg _) hzdist hα
    refine le_trans hstep ?_
    rw [iteratedFDerivWithin_univ_eq_of_mem_polydisc m hu,
      iteratedFDerivWithin_univ_eq_of_mem_polydisc m hzP]
    exact le_holderSeminorm m α g (polydisc c r') hu hzP huz

/-- **The `C^{k,α}` norm over all of `ℂⁿ` is bounded by the one over a strictly larger polydisc,
for a function vanishing outside a smaller one.**

If `g` vanishes on the closed complement of the open polydisc `P(r)` (i.e. `g z = 0` whenever
`∃ i, r i ≤ ‖z i - c i‖`) and `r j < r' j` for all `j`, then
`‖g‖_{C^{k,α}(univ)} ≤ ‖g‖_{C^{k,α}(P(r'))}`.

The point is that every `z ∉ P(r')` has some `‖z i - c i‖ ≥ r' i > r i`, so `g` vanishes on a
*neighbourhood* of `z` and all its (ambient) iterated derivatives vanish at `z`; for the Hölder
terms with `x ∈ P(r')`, `y ∉ P(r')` one replaces `y` by a point `z ∈ P(r')` with `g = 0` on a
`P(r')`-neighbourhood of `z` (take the `i`-th coordinate of `z` in the annulus
`(r i, r' i)` on the ray from `c i` through `x i`) and `‖x - z‖ ≤ ‖x - y‖`.  This mirrors the
existing one-variable `Work.CR.Flat.Holder.holderNorm_univ_le_holderNorm_ball_of_supportedInBall`
(and its auxiliary `exists_near_point`). -/
theorem holderNorm_univ_le_holderNorm_polydisc_of_vanishing {n : ℕ} {c : Fin n → ℂ}
    {r r' : Fin n → ℝ} (h : ∀ j, r j < r' j) {k : ℕ} {α : ℝ} (hα : 0 ≤ α)
    {g : (Fin n → ℂ) → ℂ}
    (hsupp : ∀ z, (∃ i, r i ≤ ‖z i - c i‖) → g z = 0) :
    Work.CR.Flat.holderNorm k α g Set.univ ≤ Work.CR.Flat.holderNorm k α g (Work.CR.Flat.polydisc c r') := by
  rw [Work.CR.Flat.holderNorm, Work.CR.Flat.holderNorm]
  refine Finset.sum_le_sum fun m _ => ?_
  refine add_le_add ?_ ?_
  · rw [Work.CR.Flat.iterDerivNorm, Work.CR.Flat.iterDerivNorm]
    refine iSup₂_le fun x _ => ?_
    by_cases hxP : x ∈ polydisc c r'
    · rw [iteratedFDerivWithin_univ_eq_of_mem_polydisc m hxP]
      exact le_iSup₂_of_le x hxP le_rfl
    · rw [iteratedFDerivWithin_univ_eq_zero_of_notMem_polydisc h hsupp m hxP]
      simp
  · rw [Work.CR.Flat.holderSeminorm, Work.CR.Flat.holderSeminorm]
    refine iSup₂_le fun x _ => iSup₂_le fun y _ => iSup_le fun hxy => ?_
    by_cases hxP : x ∈ polydisc c r'
    · by_cases hyP : y ∈ polydisc c r'
      · rw [iteratedFDerivWithin_univ_eq_of_mem_polydisc m hxP,
          iteratedFDerivWithin_univ_eq_of_mem_polydisc m hyP]
        exact le_iSup₂_of_le x hxP (le_iSup₂_of_le y hyP (le_iSup_of_le hxy le_rfl))
      · exact holderSeminorm_term_le_polydisc_of_vanishing h hsupp hα hxP
          (exists_le_of_notMem_polydisc hyP)
    · by_cases hyP : y ∈ polydisc c r'
      · have h1 : ‖iteratedFDerivWithin ℝ m g Set.univ x - iteratedFDerivWithin ℝ m g Set.univ y‖
            = ‖iteratedFDerivWithin ℝ m g Set.univ y - iteratedFDerivWithin ℝ m g Set.univ x‖ :=
          norm_sub_rev _ _
        have h2 : ‖x - y‖ = ‖y - x‖ := norm_sub_rev _ _
        rw [h1, h2]
        exact holderSeminorm_term_le_polydisc_of_vanishing h hsupp hα hyP
          (exists_le_of_notMem_polydisc hxP)
      · rw [iteratedFDerivWithin_univ_eq_zero_of_notMem_polydisc h hsupp m hxP,
          iteratedFDerivWithin_univ_eq_zero_of_notMem_polydisc h hsupp m hyP]
        simp

end

end Work.CR.Flat.Cauchy

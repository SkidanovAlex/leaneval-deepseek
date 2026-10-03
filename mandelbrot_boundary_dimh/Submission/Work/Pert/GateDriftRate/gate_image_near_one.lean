import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.scale_lattice
import Submission.Work.Pert.Qm_slice

/-!
# PERT · `Work.Pert.GateDriftRate.gate_image_near_one`

The gate `Qm Ξ α = Qreg (Ξ - 1/α) (-Ξ)` (a complement of two closed 90° cones) has an image
under `w ↦ exp (-(2πi α w))` which covers *everything outside a neighbourhood of `1`*: for every
`E ≠ 0` with `‖1 - E‖ > 2 (exp (2π‖α‖Ξ) - 1)` (and `|Im α| < Re α`, `Ξ > 0`) there is `w ∈ Qm Ξ α`
with `exp (-(2πi α w)) = E`.

## The argument

Fix any `w₀` with `exp (-(2πiαw₀)) = E` (e.g. `w₀ = -log E / (2πiα)`).  The whole coset
`w₀ + ℤ/α` is mapped to `E`, so it suffices to find one lattice point in the gate.  Write
`A = 1/α` (so `α A = 1`) and put, for `s : ℝ`,

* `hf s = Re (w₀ + sA) + A.re + |Im (w₀ + sA) + A.im| - Ξ` — the `b₁`-cone condition
  `Re (z + A) + |Im (z + A)| > Ξ` at `z = w₀ + sA` (this is the *first* conjunction of
  `Qreg`, see `Qm_mem_iff`);
* `gf s = |Im (w₀ + sA)| - Ξ - Re (w₀ + sA)` — the `b₂`-cone condition.

Thus `w₀ + sA ∈ Qm Ξ α ↔ 0 < hf s ∧ 0 < gf s`.

If some lattice point lies in the gate we are done.  Otherwise `hf` is ultimately positive (it is
bounded below by a line of slope `A.re + |A.im| > 0`) and ultimately `≤ 0` (bounded above, for
`s ≤ 0`, by a line of slope `A.re - |A.im| > 0`), so it has a *least* integer `m` with `hf m > 0`
(helper `exists_int_threshold`); then

* `hf m > 0` while `w₀ + mA` is not in the gate, so `gf m ≤ 0`;
* `hf (m-1) ≤ 0` by minimality.

Unwinding the definitions, with `ζ = w₀ + mA` (a lattice point, hence also mapped to `E`),

* `Re ζ + |Im ζ| ≤ Ξ`  (from `hf (m-1) ≤ 0`, i.e. the `b₁`-condition at `w₀ + (m-1)A`),
* `|Im ζ| - Re ζ ≤ Ξ`  (from `gf m ≤ 0`, i.e. the `b₂`-condition at `ζ`),

hence `|Re ζ| + |Im ζ| ≤ Ξ` and `‖ζ‖ ≤ Ξ`.  Therefore
`‖1 - E‖ = ‖1 - exp (-(2πiαζ))‖ ≤ exp (2π‖α‖‖ζ‖) - 1 ≤ exp (2π‖α‖Ξ) - 1`,
contradicting the strict hypothesis.  (The hypothesis `‖α‖Ξ ≤ 1/32` is not needed.)
-/

namespace Work.Pert.GateDriftRate

open Complex

noncomputable section

/-- **Least element of an upper ray of integers (found by a finite search).**

If `B < K`, `h K > 0` and `h k ≤ 0` for all integers `k ≤ B`, then the set of integers `k` with
`0 < h k` has a least element `m` (namely the minimum of `{k ∈ [B,K] : 0 < h k}`). -/
private lemma exists_least_mem {h : ℝ → ℝ} {B K : ℤ} (hBK : B < K) (hK : 0 < h (K : ℝ))
    (hB : ∀ k : ℤ, k ≤ B → h (k : ℝ) ≤ 0) :
    ∃ m : ℤ, 0 < h (m : ℝ) ∧ ∀ k : ℤ, 0 < h (k : ℝ) → m ≤ k := by
  let F : Finset ℤ := (Finset.Icc B K).filter (fun k => 0 < h (k : ℝ))
  have hKmem : K ∈ F := by
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_of_lt hBK, le_rfl⟩, hK⟩
  have hne : F.Nonempty := ⟨K, hKmem⟩
  refine ⟨F.min' hne, ?_, ?_⟩
  · exact (Finset.mem_filter.mp (Finset.min'_mem F hne)).2
  · intro k hk
    by_cases hkK : k ≤ K
    · refine Finset.min'_le F k ?_
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, hkK⟩, hk⟩
      rcases lt_or_ge B k with h | h
      · exact le_of_lt h
      · exact absurd (hB k h) (not_le.mpr hk)
    · push_neg at hkK
      exact le_trans (Finset.min'_le F K hKmem) (le_of_lt hkK)

/-- **Integer threshold of a function that is positive somewhere and eventually non-positive:**
there is an integer `m` with `h (m-1) ≤ 0 < h m`. -/
private lemma exists_int_threshold {h : ℝ → ℝ}
    (hlarge : ∃ K : ℤ, 0 < h (K : ℝ))
    (hsmall : ∃ B : ℤ, ∀ k : ℤ, k ≤ B → h (k : ℝ) ≤ 0) :
    ∃ m : ℤ, h ((m - 1 : ℤ) : ℝ) ≤ 0 ∧ 0 < h (m : ℝ) := by
  obtain ⟨K, hK⟩ := hlarge
  obtain ⟨B, hB⟩ := hsmall
  rcases lt_or_ge B K with h | h
  · obtain ⟨m, hm1, hm2⟩ := exists_least_mem h hK hB
    refine ⟨m, ?_, hm1⟩
    by_contra hcon
    rw [not_le] at hcon
    exact absurd (hm2 (m - 1) hcon) (by omega)
  · exact absurd (hB K h) (not_le.mpr hK)

theorem gate_image_near_one {α : ℂ} {Ξ : ℝ} (hΞ : 0 < Ξ) (hα : MandelDim.InF1 α)
    (hε : ‖α‖ * Ξ ≤ 1 / 32)
    {E : ℂ} (hE : E ≠ 0)
    (hclose : 2 * (Real.exp (2 * Real.pi * ‖α‖ * Ξ) - 1) < ‖1 - E‖) :
    ∃ w ∈ Work.Pert.Qm Ξ α, Complex.exp (-(2 * Real.pi * Complex.I * α * w)) = E := by
  have hαre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hα
  have hαne : α ≠ 0 := by
    intro h
    rw [h] at hαre
    simp at hαre
  -- `A = 1/α` lies in the open right cone: `0 < A.re` and `|A.im| < A.re`
  set A : ℂ := 1 / α with hA
  have hAim : |A.im| < A.re := by
    have hns : 0 < Complex.normSq α := Complex.normSq_pos.mpr hαne
    rw [hA, Complex.div_re, Complex.div_im]
    simp only [Complex.one_re, Complex.one_im, zero_mul, zero_div, one_mul, add_zero, sub_zero,
      zero_sub]
    rw [abs_neg, abs_div, abs_of_pos hns, div_lt_div_iff_of_pos_right hns]
    exact hα
  have hAre : 0 < A.re := lt_of_le_of_lt (abs_nonneg A.im) hAim
  have hαA : α * A = 1 := by
    rw [hA]
    exact mul_one_div_cancel hαne
  -- a reference point of the fibre of `E`
  set w₀ : ℂ := -(Complex.log E) / (2 * Real.pi * Complex.I * α) with hw₀
  have hden : 2 * (Real.pi : ℂ) * Complex.I * α ≠ 0 := by simp [hαne]
  have hw₀val : Complex.exp (-(2 * Real.pi * Complex.I * α * w₀)) = E := by
    have hmul : 2 * Real.pi * Complex.I * α * w₀ = -Complex.log E := by
      rw [hw₀, ← mul_div_assoc, mul_div_cancel_left₀ _ hden]
    have hlog : -(2 * Real.pi * Complex.I * α * w₀) = Complex.log E := by rw [hmul]; ring
    rw [hlog, Complex.exp_log hE]
  -- the whole coset `w₀ + ℤ/α` is mapped to `E`
  have hcoset : ∀ k : ℤ,
      Complex.exp (-(2 * Real.pi * Complex.I * α * (w₀ + (k : ℂ) * A))) = E := by
    intro k
    have hstep : -(2 * Real.pi * Complex.I * α * (w₀ + (k : ℂ) * A))
        = (-(2 * Real.pi * Complex.I * α * w₀)) + ((-(k : ℂ)) * (2 * Real.pi * Complex.I)) := by
      have h1 : 2 * Real.pi * Complex.I * α * (w₀ + (k : ℂ) * A)
          = 2 * Real.pi * Complex.I * α * w₀ + (k : ℂ) * (2 * Real.pi * Complex.I) := by
        rw [mul_add]
        congr 1
        rw [show 2 * Real.pi * Complex.I * α * ((k : ℂ) * A)
            = (k : ℂ) * (2 * Real.pi * Complex.I) * (α * A) by ring, hαA, mul_one]
      rw [h1]
      ring
    have hexpneg : Complex.exp (-(2 * Real.pi * Complex.I)) = 1 := by
      rw [Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
    have hone : Complex.exp ((-(k : ℂ)) * (2 * Real.pi * Complex.I)) = 1 := by
      rw [show (-(k : ℂ)) * (2 * Real.pi * Complex.I)
            = (k : ℂ) * (-(2 * Real.pi * Complex.I)) by ring,
        Complex.exp_int_mul, hexpneg, one_zpow]
    rw [hstep, Complex.exp_add, hw₀val, hone, mul_one]
  by_cases hcase : ∃ k : ℤ, w₀ + (k : ℂ) * A ∈ Work.Pert.Qm Ξ α
  · obtain ⟨k, hk⟩ := hcase
    exact ⟨w₀ + (k : ℂ) * A, hk, hcoset k⟩
  · push_neg at hcase
    -- the two cone conditions along the coset, as functions of the real parameter
    let hf : ℝ → ℝ := fun s => w₀.re + A.re + s * A.re + |w₀.im + A.im + s * A.im| - Ξ
    let gf : ℝ → ℝ := fun s => |w₀.im + s * A.im| - Ξ - w₀.re - s * A.re
    have hf_val : ∀ s : ℝ, hf s = w₀.re + A.re + s * A.re + |w₀.im + A.im + s * A.im| - Ξ :=
      fun s => rfl
    have gf_val : ∀ s : ℝ, gf s = |w₀.im + s * A.im| - Ξ - w₀.re - s * A.re := fun s => rfl
    have hmem : ∀ s : ℝ, w₀ + (s : ℂ) * A ∈ Work.Pert.Qm Ξ α ↔ 0 < hf s ∧ 0 < gf s := by
      intro s
      have hre : (w₀ + (s : ℂ) * A).re = w₀.re + s * A.re := by
        rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
        ring
      have him : (w₀ + (s : ℂ) * A).im = w₀.im + s * A.im := by
        rw [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
        ring
      have harg : |w₀.im + s * A.im + A.im| = |w₀.im + A.im + s * A.im| := by
        congr 1
        ring
      rw [Work.Pert.Qm_mem_iff, hre, him, harg, hf_val s, gf_val s]
      constructor
      · intro h
        exact ⟨by linarith, by linarith⟩
      · intro h
        exact ⟨by linarith, by linarith⟩
    -- `hf` is bounded below by a line of positive slope, so it is positive somewhere …
    have hf_lb : ∀ s : ℝ,
        w₀.re + A.re - |w₀.im + A.im| - Ξ + s * (A.re + |A.im|) ≤ hf s := by
      intro s
      have h1 : |s * A.im| - |w₀.im + A.im| ≤ |w₀.im + A.im + s * A.im| := by
        have h := abs_add_le (w₀.im + A.im + s * A.im) (-(w₀.im + A.im))
        have hx : (w₀.im + A.im + s * A.im) + (-(w₀.im + A.im)) = s * A.im := by ring
        rw [hx, abs_neg] at h
        linarith
      have h2 : s * |A.im| ≤ |s * A.im| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (le_abs_self s) (abs_nonneg A.im)
      rw [hf_val s]
      linarith
    -- … and bounded above by a line of positive slope on the left, so it is `≤ 0` far left.
    have hf_ub : ∀ s : ℝ, s ≤ 0 →
        hf s ≤ w₀.re + A.re + |w₀.im + A.im| - Ξ + s * (A.re - |A.im|) := by
      intro s hs
      have h1 : |w₀.im + A.im + s * A.im| ≤ |w₀.im + A.im| + |s * A.im| := abs_add_le _ _
      have h2 : |s * A.im| = -s * |A.im| := by rw [abs_mul, abs_of_nonpos hs]
      rw [hf_val s]
      linarith
    have hlarge : ∃ K : ℤ, 0 < hf (K : ℝ) := by
      have hcoef : 0 < A.re + |A.im| := by linarith [abs_nonneg A.im, hAre]
      set K : ℤ := ⌊(Ξ + |w₀.im + A.im| - w₀.re - A.re) / (A.re + |A.im|)⌋ + 1 with hKdef
      refine ⟨K, ?_⟩
      have hlt : (Ξ + |w₀.im + A.im| - w₀.re - A.re) / (A.re + |A.im|) < (K : ℝ) := by
        rw [hKdef]
        push_cast
        exact Int.lt_floor_add_one _
      have hkey : Ξ + |w₀.im + A.im| - w₀.re - A.re < (K : ℝ) * (A.re + |A.im|) := by
        rw [div_lt_iff₀ hcoef] at hlt
        linarith
      have hb := hf_lb (K : ℝ)
      linarith
    have hsmall : ∃ B : ℤ, ∀ k : ℤ, k ≤ B → hf (k : ℝ) ≤ 0 := by
      have hcoef : 0 < A.re - |A.im| := by linarith [hAim]
      set B : ℤ := min 0 ⌊-((w₀.re + A.re + |w₀.im + A.im| - Ξ) / (A.re - |A.im|))⌋ with hBdef
      refine ⟨B, ?_⟩
      intro k hk
      have hk0 : k ≤ 0 := le_trans hk (by rw [hBdef]; exact min_le_left _ _)
      have hk1 : k ≤ ⌊-((w₀.re + A.re + |w₀.im + A.im| - Ξ) / (A.re - |A.im|))⌋ :=
        le_trans hk (by rw [hBdef]; exact min_le_right _ _)
      have hkle : (k : ℝ) ≤ -((w₀.re + A.re + |w₀.im + A.im| - Ξ) / (A.re - |A.im|)) :=
        le_trans (by exact_mod_cast hk1) (Int.floor_le _)
      have hkey : (k : ℝ) * (A.re - |A.im|) ≤ -(w₀.re + A.re + |w₀.im + A.im| - Ξ) := by
        have h := mul_le_mul_of_nonneg_right hkle (le_of_lt hcoef)
        have hc : (-((w₀.re + A.re + |w₀.im + A.im| - Ξ) / (A.re - |A.im|)))
            * (A.re - |A.im|) = -(w₀.re + A.re + |w₀.im + A.im| - Ξ) := by
          rw [neg_mul, div_mul_cancel₀ _ (ne_of_gt hcoef)]
        linarith [h, hc]
      have hk0' : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
      have hb := hf_ub (k : ℝ) hk0'
      linarith
    obtain ⟨m, hmneg, hmpos⟩ := exists_int_threshold hlarge hsmall
    -- unwinding the two threshold inequalities at the point `ζ = w₀ + m·A`
    have hml : w₀.re + A.re + ((m - 1 : ℤ) : ℝ) * A.re
        + |w₀.im + A.im + ((m - 1 : ℤ) : ℝ) * A.im| ≤ Ξ := by
      have h := hmneg
      rw [hf_val ((m - 1 : ℤ) : ℝ)] at h
      linarith
    have hshift : w₀.im + A.im + ((m - 1 : ℤ) : ℝ) * A.im = w₀.im + ((m : ℤ) : ℝ) * A.im := by
      push_cast
      ring
    have hshift' : w₀.re + A.re + ((m - 1 : ℤ) : ℝ) * A.re = w₀.re + ((m : ℤ) : ℝ) * A.re := by
      push_cast
      ring
    have hre_m : (w₀ + (m : ℂ) * A).re = w₀.re + (m : ℝ) * A.re := by
      rw [show ((m : ℤ) : ℂ) = ((m : ℝ) : ℂ) from Complex.ofReal_intCast m, Complex.add_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    have him_m : (w₀ + (m : ℂ) * A).im = w₀.im + (m : ℝ) * A.im := by
      rw [show ((m : ℤ) : ℂ) = ((m : ℝ) : ℂ) from Complex.ofReal_intCast m, Complex.add_im,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    -- the two cone conditions at `ζ`
    have hb : (w₀ + (m : ℂ) * A).re + |(w₀ + (m : ℂ) * A).im| ≤ Ξ := by
      rw [hre_m, him_m]
      have h := hml
      rw [hshift', hshift] at h
      linarith
    have hc : |(w₀ + (m : ℂ) * A).im| - (w₀ + (m : ℂ) * A).re ≤ Ξ := by
      have hnot : gf (m : ℝ) ≤ 0 := by
        by_contra hcon
        rw [not_le] at hcon
        exact hcase m ((hmem (m : ℝ)).mpr ⟨hmpos, hcon⟩)
      rw [gf_val (m : ℝ)] at hnot
      rw [hre_m, him_m]
      linarith
    have hnorm : ‖w₀ + (m : ℂ) * A‖ ≤ Ξ := by
      have h1 : |(w₀ + (m : ℂ) * A).im| ≤ Ξ := by linarith
      have h2 : |(w₀ + (m : ℂ) * A).re| ≤ Ξ - |(w₀ + (m : ℂ) * A).im| :=
        abs_le.mpr ⟨by linarith, by linarith⟩
      calc ‖w₀ + (m : ℂ) * A‖ ≤ |(w₀ + (m : ℂ) * A).re| + |(w₀ + (m : ℂ) * A).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ ≤ Ξ := by linarith
    -- … and the value at `ζ` is `E`
    have hbound : ‖1 - E‖ ≤ Real.exp (2 * Real.pi * ‖α‖ * Ξ) - 1 := by
      have h1 : (1 : ℂ) - E
          = -(Complex.exp (-(2 * Real.pi * Complex.I * α * (w₀ + (m : ℂ) * A))) - 1) := by
        rw [hcoset m]
        ring
      rw [h1, norm_neg]
      have h2 := Complex.norm_exp_sub_sum_le_exp_norm_sub_sum
        (-(2 * Real.pi * Complex.I * α * (w₀ + (m : ℂ) * A))) 1
      simp only [Finset.sum_range_one, Nat.factorial_zero, Nat.cast_one, pow_zero, div_one] at h2
      refine le_trans h2 ?_
      have h3 : ‖-(2 * Real.pi * Complex.I * α * (w₀ + (m : ℂ) * A))‖ ≤ 2 * Real.pi * ‖α‖ * Ξ := by
        rw [norm_neg, norm_mul]
        have h4 : ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I * α‖ = 2 * Real.pi * ‖α‖ := by
          simp [Complex.norm_I]
        rw [h4]
        exact mul_le_mul_of_nonneg_left hnorm (by positivity)
      exact sub_le_sub_right (Real.exp_le_exp.mpr h3) 1
    have hexp_gt : 1 < Real.exp (2 * Real.pi * ‖α‖ * Ξ) := by
      rw [Real.one_lt_exp_iff]
      have hnormpos : 0 < ‖α‖ := norm_pos_iff.mpr hαne
      positivity
    exact absurd hbound
      (not_le.mpr (by linarith : Real.exp (2 * Real.pi * ‖α‖ * Ξ) - 1 < ‖1 - E‖))

end

end Work.Pert.GateDriftRate

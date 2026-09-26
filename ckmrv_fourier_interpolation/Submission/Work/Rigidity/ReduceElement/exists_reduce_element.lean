/-
# Reduction of an arbitrary point of `ℍ` into `closure 𝓕`, with polynomial control

For every `τ ∈ ℍ` there is `γ ∈ SL(2,ℤ)` (built from a shortest element of the lattice
`ℤ + ℤτ`) with `γ⁻¹ • τ ∈ closure 𝓕` and both `Frob γ` and `scale (γ⁻¹ • τ)` bounded by a
fixed polynomial in `scale τ = 1 + (im τ)⁻¹ + |τ|`.  This is the elementary input
("choose a fundamental domain representative of `τ`") used by the propagation of the
moderate growth bounds in CKMRV Section 4.

The construction: let `g₀` maximise `im (g • τ)` over `g ∈ SL(2,ℤ)`.  Its bottom row
`(c,d)` is a shortest vector of the lattice `{(c,d) : |cτ + d|}`, so `|c| ≤ 1/im τ` and
`|d| ≤ 1 + |τ|/im τ`; completing `(c,d)` to a unimodular pair `(a,b)` with `|a| ≤ |c| + 1`,
`|b| ≤ |d| + 1` and translating the resulting point by an integer into the strip
`0 ≤ Re ≤ 1` gives a point of `closure 𝓕`.  Every quantity produced is polynomial in
`scale τ` with fixed exponents.

## Contents

* `CoeSlSmulEq`, `im_smul_eq` : the Möbius formula and the imaginary part of `g • z`
  in terms of the entries of `g`.
* `isCoprime_ne_zero` : `a τ + b ≠ 0` for a coprime pair `(a,b)`.
* `minimal_of_maxIm` : the bottom row of an `im`-maximising element is a shortest vector.
* `Frob_inv`, `Frob_mk`, `sqrt_sum_sq_le` : elementary `Frob` computations.
* `closureDomainF_mem_of` : the closed region `{0 ≤ Re ≤ 1, |z| ≥ 1, |z-1| ≥ 1}` lies in
  the closure of CKMRV's fundamental domain `𝓕`.
* `exists_completion_bounded` : a coprime pair is completed to a unimodular one with
  controlled size.
* `exists_reduce_element` : the reduction theorem.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.PropagateBounds.Defs
import Submission.Work.Kernels.Slash

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

set_option maxHeartbeats 2000000

namespace Work.Rigidity.ReduceElement

/-! ## The Möbius action in coordinates -/

/-- The Möbius action of `g ∈ SL(2,ℤ)` written out in the entries of `g`. -/
lemma coe_smul_eq (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane) :
    ((g • z : UpperHalfPlane) : ℂ) =
      (((g 0 0 : ℤ) : ℂ) * (z : ℂ) + ((g 0 1 : ℤ) : ℂ)) /
      (((g 1 0 : ℤ) : ℂ) * (z : ℂ) + ((g 1 1 : ℤ) : ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [algebraMap_int_eq]
  simp

/-- The imaginary part of `g • z`: `im (g • z) = im z / |c z + d|²`, `(c,d)` the bottom row. -/
lemma im_smul_eq (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane) :
    (g • z).im = z.im / ‖((g 1 0 : ℤ) : ℂ) * (z : ℂ) + ((g 1 1 : ℤ) : ℂ)‖ ^ 2 := by
  rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply, Complex.normSq_eq_norm_sq]

/-- For a coprime pair `(a,b)` and `z ∈ ℍ`, the complex number `a z + b` does not vanish. -/
lemma isCoprime_ne_zero (z : UpperHalfPlane) {a b : ℤ} (hab : IsCoprime a b) :
    (a : ℂ) * (z : ℂ) + (b : ℂ) ≠ 0 := by
  rintro h
  have him0 : ((a : ℂ) * (z : ℂ) + (b : ℂ)).im = 0 := by rw [h]; simp
  have ha : (a : ℝ) * z.im = 0 := by
    simpa [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_im,
      UpperHalfPlane.coe_im] using him0
  rcases mul_eq_zero.mp ha with h1 | h1
  · have ha0 : a = 0 := by exact_mod_cast h1
    subst ha0
    simp only [Int.cast_zero, zero_mul, zero_add] at h
    have hb : b = 0 := by exact_mod_cast h
    obtain ⟨x, y, hxy⟩ := hab
    simp [hb] at hxy
  · exact absurd h1 (ne_of_gt z.im_pos)

/-- The bottom row of an element maximising `im (g • τ)` is a shortest vector of the lattice
`ℤ + ℤτ`: for every coprime pair `(a,b)` one has `|cτ + d| ≤ |aτ + b|`. -/
lemma minimal_of_maxIm {τ : UpperHalfPlane} {g₀ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hg₀ : ∀ g' : Matrix.SpecialLinearGroup (Fin 2) ℤ, (g' • τ).im ≤ (g₀ • τ).im)
    {a b : ℤ} (hab : IsCoprime a b) :
    ‖((g₀ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((g₀ 1 1 : ℤ) : ℂ)‖ ≤ ‖(a : ℂ) * (τ : ℂ) + (b : ℂ)‖ := by
  have hcd : IsCoprime ((![a, b] : Fin 2 → ℤ) 0) ((![a, b] : Fin 2 → ℤ) 1) := by
    simpa using hab
  obtain ⟨g, -, hg⟩ := ModularGroup.bottom_row_surj (R := ℤ) hcd
  have hg0 : g 1 0 = a := by
    have := congrFun hg 0
    simpa using this
  have hg1 : g 1 1 = b := by
    have := congrFun hg 1
    simpa using this
  have him := hg₀ g
  rw [im_smul_eq g τ, im_smul_eq g₀ τ, hg0, hg1] at him
  have hpos : 0 < τ.im := τ.im_pos
  have hX : 0 < ‖(a : ℂ) * (τ : ℂ) + (b : ℂ)‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (isCoprime_ne_zero τ hab)) 2
  have hY : 0 < ‖((g₀ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((g₀ 1 1 : ℤ) : ℂ)‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (isCoprime_ne_zero τ (ModularGroup.bottom_row_coprime g₀))) 2
  have h2 : ‖((g₀ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((g₀ 1 1 : ℤ) : ℂ)‖ ^ 2
      ≤ ‖(a : ℂ) * (τ : ℂ) + (b : ℂ)‖ ^ 2 :=
    (div_le_div_iff_of_pos_left hpos hX hY).mp him
  calc ‖((g₀ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((g₀ 1 1 : ℤ) : ℂ)‖
      = Real.sqrt (‖((g₀ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((g₀ 1 1 : ℤ) : ℂ)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖(a : ℂ) * (τ : ℂ) + (b : ℂ)‖ ^ 2) := Real.sqrt_le_sqrt h2
    _ = ‖(a : ℂ) * (τ : ℂ) + (b : ℂ)‖ := Real.sqrt_sq (norm_nonneg _)

/-! ## `Frob` computations -/

/-- `Frob` is invariant under inversion. -/
theorem Frob_inv (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    Work.Asymptotics.Frob γ⁻¹ = Work.Asymptotics.Frob γ := by
  unfold Work.Asymptotics.Frob
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val']
  congr 1
  push_cast
  ring

/-- `Frob` of an explicitly given matrix. -/
lemma Frob_mk (a b c d : ℤ) (h : Matrix.det !![a, b; c, d] = 1) :
    Work.Asymptotics.Frob (⟨!![a, b; c, d], h⟩ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
      = Real.sqrt ((a : ℝ) ^ 2 + (b : ℝ) ^ 2 + (c : ℝ) ^ 2 + (d : ℝ) ^ 2) := by
  unfold Work.Asymptotics.Frob
  simp

/-- The square root of a sum of four squares is at most the sum of the absolute values. -/
lemma sqrt_sum_sq_le (a b c d : ℝ) :
    Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ≤ |a| + |b| + |c| + |d| := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [sq_abs a, sq_abs b, sq_abs c, sq_abs d, abs_nonneg a, abs_nonneg b, abs_nonneg c,
    abs_nonneg d, sq_nonneg (|a| + |b| + |c| + |d|)]

/-! ## The closed region around `𝓕` -/

/-- A point of `ℍ` with `0 ≤ Re z ≤ 1`, `|z| ≥ 1` and `|z - 1| ≥ 1` lies in the closure of
CKMRV's fundamental domain `𝓕 = {0 < Re < 1, |z| > 1, |z - 1| > 1}`. -/
theorem closureDomainF_mem_of {z : UpperHalfPlane} (h0 : 0 ≤ z.re) (h1 : z.re ≤ 1)
    (h2 : 1 ≤ ‖(z : ℂ)‖) (h3 : 1 ≤ ‖(z : ℂ) - 1‖) :
    z ∈ closure Work.Asymptotics.DomainF := by
  have hz2 : 1 ≤ z.re ^ 2 + z.im ^ 2 := by
    have h : Complex.normSq (z : ℂ) = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]; ring
    rw [← h, Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg (z : ℂ)]
  have hz3 : 1 ≤ (z.re - 1) ^ 2 + z.im ^ 2 := by
    have h : Complex.normSq ((z : ℂ) - 1) = (z.re - 1) ^ 2 + z.im ^ 2 := by
      rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
        UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]; ring
    rw [← h, Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg ((z : ℂ) - 1)]
  have him : (1:ℝ)/2 < z.im := by
    have key : (1/2:ℝ)^2 < z.im^2 := by
      rcases le_or_gt z.re (1/2) with hle | hlt
      · have hx2 : z.re^2 ≤ 1/4 := by
          nlinarith [h0, hle, mul_nonneg h0 (show (0:ℝ) ≤ 1/2 - z.re by linarith)]
        nlinarith [hz2, hx2]
      · have hx2 : (z.re - 1)^2 ≤ 1/4 := by
          nlinarith [h1, hlt, mul_nonneg (show (0:ℝ) ≤ 1 - z.re by linarith)
            (show (0:ℝ) ≤ z.re - 1/2 by linarith)]
        nlinarith [hz3, hx2]
    have him0 : 0 < z.im := z.im_pos
    have := sq_lt_sq.mp key
    rw [abs_of_pos him0, abs_of_pos (by norm_num : (0:ℝ) < 1/2)] at this
    linarith
  set α : ℂ := (((1/2 - z.re : ℝ)) : ℂ) + Complex.I with hαdef
  have hstep : ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∃ w : UpperHalfPlane, w ∈ Work.Asymptotics.DomainF ∧
        (w : ℂ) = (z : ℂ) + (t : ℂ) * α := by
    intro t ht ht1
    set u : ℂ := (z : ℂ) + (t : ℂ) * α with hudef
    have hrew : u.re = z.re + t * (1/2 - z.re) := by
      rw [hudef, hαdef]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, UpperHalfPlane.coe_re]
      ring
    have himw' : u.im = z.im + t := by
      rw [hudef, hαdef]
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_im, UpperHalfPlane.coe_im]
      ring
    have hu : 0 < u.im := by rw [himw']; linarith
    refine ⟨⟨u, hu⟩, ?_, ?_⟩
    · rw [Work.Asymptotics.mem_DomainF]
      have hA : -(1/2:ℝ) ≤ z.re * (1/2 - z.re) := by nlinarith [h0, h1]
      have hB : -(1/2:ℝ) ≤ (z.re - 1) * (1/2 - z.re) := by nlinarith [h0, h1]
      refine ⟨?_, ?_, ?_, ?_⟩
      · show 0 < u.re
        rw [hrew]; nlinarith
      · show u.re < 1
        rw [hrew]; nlinarith
      · show 1 < ‖u‖
        rw [← Real.sqrt_sq (norm_nonneg u), Real.lt_sqrt (by norm_num),
          ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hrew, himw']
        nlinarith [hz2, h0, h1, him, ht, ht1, hA, sq_nonneg (1/2 - z.re), sq_nonneg t]
      · show 1 < ‖u - 1‖
        rw [← Real.sqrt_sq (norm_nonneg (u-1)), Real.lt_sqrt (by norm_num)]
        have hs1 : ‖u - 1‖^2 = (u.re - 1)^2 + u.im^2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
            Complex.one_re, Complex.one_im]; ring
        rw [hs1, hrew, himw']
        nlinarith [hz3, h0, h1, him, ht, ht1, hB, sq_nonneg (1/2 - z.re), sq_nonneg t]
    · rfl
  have hone_pos : ∀ n : ℕ, (0:ℝ) < 1/(n+1) := fun n => by positivity
  have hone_le : ∀ n : ℕ, ((1:ℝ)/(n+1)) ≤ 1 := fun n => by
    have hn : (1:ℝ) ≤ ((n:ℝ) + 1) := by
      have : (0:ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.zero_le n
      linarith
    have := one_div_le_one_div_of_le (show (0:ℝ) < 1 by norm_num) hn
    simpa using this
  choose w hwF hwc using fun n : ℕ => hstep (1/(n+1)) (hone_pos n) (hone_le n)
  have hlim : Filter.Tendsto (fun n : ℕ => (w n : ℂ)) Filter.atTop (𝓝 (z : ℂ)) := by
    have hconv : Filter.Tendsto (fun n : ℕ => (((1:ℝ)/(n+1) : ℝ) : ℂ)) Filter.atTop
        (𝓝 (0:ℂ)) := by
      have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp h
      simpa [Function.comp_def, one_div] using h2
    have h3 : Filter.Tendsto (fun n : ℕ => (z:ℂ) + (((1:ℝ)/(n+1) : ℝ) : ℂ) * α)
        Filter.atTop (𝓝 (z:ℂ)) := by
      have h4 := (hconv.mul_const α).const_add ((z:ℂ))
      simpa using h4
    refine h3.congr' ?_
    filter_upwards with n
    rw [hwc n]
  rw [UpperHalfPlane.isEmbedding_coe.closure_eq_preimage_closure_image]
  exact mem_closure_iff_seq_limit.mpr ⟨fun n => (w n : ℂ), fun n => ⟨w n, hwF n, rfl⟩, hlim⟩

/-! ## Bounded completion of a primitive vector -/

/-- A coprime pair `(c,d)` can be completed to a unimodular pair, `a d - b c = 1`, with
`|a| ≤ |c| + 1` and `|b| ≤ |d| + 1`. -/
theorem exists_completion_bounded {c d : ℤ} (h : IsCoprime c d) :
    ∃ a b : ℤ, a * d - b * c = 1 ∧
      |(a : ℝ)| ≤ |(c : ℝ)| + 1 ∧ |(b : ℝ)| ≤ |(d : ℝ)| + 1 := by
  rcases eq_or_ne c 0 with hc | hc
  · subst hc
    obtain ⟨x, y, hy⟩ := h
    simp only [mul_zero, zero_add] at hy
    have hd : d = 1 ∨ d = -1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hy with ⟨-, h⟩ | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
    rcases hd with rfl | rfl
    · exact ⟨1, 0, by norm_num, by simp, by simp⟩
    · exact ⟨-1, 0, by norm_num, by simp, by simp⟩
  · obtain ⟨x, y, hxy⟩ := h
    have hmod : y % c = y - (y / c) * c := by
      have := Int.ediv_mul_add_emod y c
      linarith
    refine ⟨y % c, -x - (y / c) * d, ?_, ?_, ?_⟩
    · rw [hmod]; nlinarith [hxy]
    · have h0 : (0:ℝ) ≤ ((y % c : ℤ) : ℝ) := by
        exact_mod_cast Int.emod_nonneg y hc
      have h1 : ((y % c : ℤ) : ℝ) < |(c : ℝ)| := by
        exact_mod_cast Int.emod_lt_abs y hc
      rw [abs_of_nonneg h0]; linarith
    · have hdet : (y % c) * d - (-x - (y / c) * d) * c = 1 := by
        rw [hmod]; nlinarith [hxy]
      have hbc : (-((x:ℤ):ℝ) - (((y / c : ℤ)) : ℝ) * ((d:ℤ):ℝ)) * ((c:ℤ):ℝ)
          = ((y % c : ℤ) : ℝ) * ((d:ℤ):ℝ) - 1 := by
        have h := congrArg (fun z : ℤ => (z : ℝ)) hdet
        push_cast at h
        linarith
      have habs : |((y % c : ℤ) : ℝ)| ≤ |((c:ℤ):ℝ)| := by
        have h0 : (0:ℝ) ≤ ((y % c : ℤ) : ℝ) := by
          exact_mod_cast Int.emod_nonneg y hc
        have h1 : ((y % c : ℤ) : ℝ) < |((c:ℤ):ℝ)| := by
          exact_mod_cast Int.emod_lt_abs y hc
        rw [abs_of_nonneg h0]; linarith
      have hca : (1:ℝ) ≤ |((c:ℤ):ℝ)| := by
        have h1 : (1:ℤ) ≤ |c| := Int.one_le_abs hc
        exact_mod_cast h1
      have hpos : 0 < |((c:ℤ):ℝ)| := by linarith
      have htri : |((y % c : ℤ) : ℝ) * ((d:ℤ):ℝ) - 1|
          ≤ |((y % c : ℤ) : ℝ) * ((d:ℤ):ℝ)| + 1 := by
        have h := abs_add_le (((y % c : ℤ) : ℝ) * ((d:ℤ):ℝ)) (-1)
        rw [show ((y % c : ℤ) : ℝ) * ((d:ℤ):ℝ) + (-1)
            = ((y % c : ℤ) : ℝ) * ((d:ℤ):ℝ) - 1 by ring] at h
        simpa using h
      have key : |(-((x:ℤ):ℝ) - (((y / c : ℤ)) : ℝ) * ((d:ℤ):ℝ))| * |((c:ℤ):ℝ)|
          ≤ |((c:ℤ):ℝ)| * |((d:ℤ):ℝ)| + 1 := by
        calc |(-((x:ℤ):ℝ) - (((y / c : ℤ)) : ℝ) * ((d:ℤ):ℝ))| * |((c:ℤ):ℝ)|
            = |(-((x:ℤ):ℝ) - (((y / c : ℤ)) : ℝ) * ((d:ℤ):ℝ)) * ((c:ℤ):ℝ)| := by rw [abs_mul]
          _ = |((y % c : ℤ) : ℝ) * ((d:ℤ):ℝ) - 1| := by rw [hbc]
          _ ≤ |((y % c : ℤ) : ℝ) * ((d:ℤ):ℝ)| + 1 := htri
          _ = |((y % c : ℤ) : ℝ)| * |((d:ℤ):ℝ)| + 1 := by rw [abs_mul]
          _ ≤ |((c:ℤ):ℝ)| * |((d:ℤ):ℝ)| + 1 := by
              linarith [mul_le_mul_of_nonneg_right habs (abs_nonneg ((d:ℤ):ℝ))]
      have h2 : |(-((x:ℤ):ℝ) - (((y / c : ℤ)) : ℝ) * ((d:ℤ):ℝ))|
          ≤ (|((c:ℤ):ℝ)| * |((d:ℤ):ℝ)| + 1) / |((c:ℤ):ℝ)| :=
        (le_div_iff₀ hpos).mpr (by linarith)
      have h3 : (|((c:ℤ):ℝ)| * |((d:ℤ):ℝ)| + 1) / |((c:ℤ):ℝ)| ≤ |((d:ℤ):ℝ)| + 1 := by
        rw [div_le_iff₀ hpos]
        linarith [mul_le_mul_of_nonneg_left hca (abs_nonneg ((d:ℤ):ℝ))]
      have hgoal : |(-((x:ℤ):ℝ) - (((y / c : ℤ)) : ℝ) * ((d:ℤ):ℝ))| ≤ |((d:ℤ):ℝ)| + 1 := by
        linarith
      rw [show ((-x - (y / c) * d : ℤ) : ℝ)
          = -((x:ℤ):ℝ) - (((y / c : ℤ)) : ℝ) * ((d:ℤ):ℝ) by push_cast; ring]
      exact hgoal

/-! ## The final polynomial bookkeeping -/

/-- A fixed constant times `S ^ j` (`j ≤ 8`) is at most `1000 * (1 + S) ^ (8 : ℝ)` for `S ≥ 1`. -/
lemma pow_le_target (S : ℝ) (hS : 1 ≤ S) {j : ℕ} (hj : j ≤ 8) {C : ℝ}
    (hC : C ≤ 1000) : C * S ^ j ≤ 1000 * (1 + S) ^ (8 : ℝ) := by
  rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h1 : S ^ j ≤ S ^ 8 := pow_le_pow_right₀ hS hj
  have h2 : S ^ 8 ≤ (1 + S) ^ 8 := pow_le_pow_left₀ (by linarith) (by linarith) 8
  calc C * S ^ j ≤ 1000 * S ^ j := mul_le_mul_of_nonneg_right hC (pow_nonneg (by linarith) j)
    _ ≤ 1000 * S ^ 8 := mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ ≤ 1000 * (1 + S) ^ 8 := mul_le_mul_of_nonneg_left h2 (by norm_num)

/-- The determinant of an explicit `2 × 2` matrix. -/
lemma det_fin_two_eq (a b c d : ℤ) : Matrix.det !![a, b; c, d] = a * d - b * c := by
  rw [Matrix.det_fin_two]; simp

theorem exists_reduce_element :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : UpperHalfPlane,
      ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      γ⁻¹ • τ ∈ closure Work.Asymptotics.DomainF ∧
      Work.Asymptotics.Frob γ ≤ C * (1 + Work.Kernels.scale τ) ^ N ∧
      Work.Kernels.scale (γ⁻¹ • τ) ≤ C * (1 + Work.Kernels.scale τ) ^ N := by
  refine ⟨1000, 8, by norm_num, by norm_num, fun τ => ?_⟩
  obtain ⟨g₀, hg₀⟩ := ModularGroup.exists_max_im τ
  set c : ℤ := g₀ 1 0 with hcdef
  set d : ℤ := g₀ 1 1 with hddef
  set L : ℝ := ‖((c : ℤ) : ℂ) * (τ : ℂ) + ((d : ℤ) : ℂ)‖ with hLdef
  set S : ℝ := Work.Kernels.scale τ with hSdef
  have hS1 : 1 ≤ S := by rw [hSdef]; exact Work.Kernels.one_le_scale τ
  have hinvS : (τ.im)⁻¹ ≤ S := by rw [hSdef]; exact Work.Kernels.inv_im_le_scale τ
  have hnormS : ‖(τ : ℂ)‖ ≤ S := by rw [hSdef]; exact Work.Kernels.coe_norm_le_scale τ
  have htpos : 0 < τ.im := τ.im_pos
  have hcop : IsCoprime c d := by
    have h := ModularGroup.bottom_row_coprime g₀
    simpa [hcdef, hddef] using h
  have hLpos : 0 < L := by
    rw [hLdef]
    exact norm_pos_iff.mpr (isCoprime_ne_zero τ hcop)
  have hLle1 : L ≤ 1 := by
    have h := minimal_of_maxIm hg₀ (show IsCoprime (0 : ℤ) 1 from ⟨0, 1, by norm_num⟩)
    have h1 : ‖((0 : ℤ) : ℂ) * (τ : ℂ) + ((1 : ℤ) : ℂ)‖ = 1 := by norm_num
    rw [h1] at h
    simpa [hLdef, hcdef, hddef] using h
  -- the bottom row of the maximising element is short
  have hct : |(c : ℝ)| * τ.im ≤ L := by
    have h := Complex.abs_im_le_norm (((c : ℤ) : ℂ) * (τ : ℂ) + ((d : ℤ) : ℂ))
    have h2 : (((c : ℤ) : ℂ) * (τ : ℂ) + ((d : ℤ) : ℂ)).im = (c : ℝ) * τ.im := by
      simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
        UpperHalfPlane.coe_im, add_zero]
      ring
    rw [h2, abs_mul, abs_of_pos htpos] at h
    rwa [hLdef]
  have hcS : |(c : ℝ)| ≤ S := by
    have h1 : |(c : ℝ)| * τ.im ≤ 1 := le_trans hct hLle1
    have h2 : |(c : ℝ)| ≤ 1 / τ.im := by rw [le_div_iff₀ htpos]; linarith
    rw [one_div] at h2
    linarith [h2, hinvS]
  have hdS : |(d : ℝ)| ≤ 2 * S ^ 2 := by
    have h1 : |(d : ℝ)| ≤ L + |(c : ℝ)| * ‖(τ : ℂ)‖ := by
      have h3 : ((d : ℤ) : ℂ)
          = (((c : ℤ) : ℂ) * (τ : ℂ) + ((d : ℤ) : ℂ)) - ((c : ℤ) : ℂ) * (τ : ℂ) := by ring
      calc |(d : ℝ)| = ‖((d : ℤ) : ℂ)‖ := by rw [Complex.norm_intCast]
        _ ≤ ‖(((c : ℤ) : ℂ) * (τ : ℂ) + ((d : ℤ) : ℂ))‖ + ‖((c : ℤ) : ℂ) * (τ : ℂ)‖ := by
              conv_lhs => rw [h3]
              exact norm_sub_le _ _
        _ = L + |(c : ℝ)| * ‖(τ : ℂ)‖ := by rw [hLdef, norm_mul, Complex.norm_intCast]
    have h4 : L + |(c : ℝ)| * ‖(τ : ℂ)‖ ≤ 2 * S ^ 2 := by
      have h5 := mul_le_mul hcS hnormS (norm_nonneg _) (by linarith)
      nlinarith [hLle1, h5, hS1]
    linarith
  -- completion to a unimodular pair
  obtain ⟨a, b, habdet, ha, hb⟩ := exists_completion_bounded hcop
  have haS : |(a : ℝ)| ≤ 2 * S := by linarith [ha, hcS, hS1]
  have hbS : |(b : ℝ)| ≤ 3 * S ^ 2 := by
    have h2 : (1:ℝ) ≤ S ^ 2 := one_le_pow₀ hS1
    linarith [hb, hdS, h2]
  -- `1 / L` is bounded polynomially
  have hinvL : 1 / L ≤ S := by
    rcases eq_or_ne c 0 with hc0 | hc0
    · have hd1 : |(d : ℝ)| = 1 := by
        have h : IsCoprime (0 : ℤ) d := by simpa [hc0] using hcop
        obtain ⟨x, y, hxy⟩ := h
        simp only [mul_zero, zero_add] at hxy
        rcases Int.eq_one_or_neg_one_of_mul_eq_one' hxy with ⟨-, hd⟩ | ⟨-, hd⟩ <;> simp [hd]
      have hL1 : L = 1 := by
        rw [hLdef, hc0]
        simp only [Int.cast_zero, zero_mul, zero_add]
        rw [Complex.norm_intCast]
        exact hd1
      rw [hL1]
      simpa using hS1
    · have hc1 : (1 : ℝ) ≤ |(c : ℝ)| := by
        have := Int.one_le_abs hc0
        exact_mod_cast this
      have h1 : τ.im ≤ L := by
        have h2 : τ.im ≤ |(c : ℝ)| * τ.im := by nlinarith [htpos, hc1]
        linarith [hct]
      have h3 : (τ.im)⁻¹ * τ.im ≤ S * L :=
        mul_le_mul hinvS h1 (le_of_lt htpos) (by linarith)
      have h4 : (τ.im)⁻¹ * τ.im = 1 := inv_mul_cancel₀ (ne_of_gt htpos)
      have h5 : (1 : ℝ) ≤ S * L := by linarith
      rw [div_le_iff₀ hLpos]
      linarith
  -- the completed matrix, its translate `σ`, and the two norms at `σ`
  have hdetM : Matrix.det !![a, b; c, d] = 1 := by
    rw [det_fin_two_eq]
    exact habdet
  set M : Matrix.SpecialLinearGroup (Fin 2) ℤ := ⟨!![a, b; c, d], hdetM⟩ with hMdef
  have hM00 : M 0 0 = a := by simp [hMdef]
  have hM01 : M 0 1 = b := by simp [hMdef]
  have hM10 : M 1 0 = c := by simp [hMdef]
  have hM11 : M 1 1 = d := by simp [hMdef]
  have hD : (((c : ℤ) : ℂ) * (τ : ℂ) + ((d : ℤ) : ℂ)) ≠ 0 := isCoprime_ne_zero τ hcop
  set σ : UpperHalfPlane := M • τ with hσdef
  have hσcoe : ((σ : UpperHalfPlane) : ℂ) =
      (((a : ℤ) : ℂ) * (τ : ℂ) + ((b : ℤ) : ℂ)) /
      (((c : ℤ) : ℂ) * (τ : ℂ) + ((d : ℤ) : ℂ)) := by
    rw [hσdef, coe_smul_eq M τ, hM00, hM01, hM10, hM11]
  have hσim : ((σ : UpperHalfPlane) : ℂ).im = τ.im / L ^ 2 := by
    rw [UpperHalfPlane.coe_im, hσdef, im_smul_eq M τ, hM10, hM11, hLdef]
  have hσnorm : ‖((σ : UpperHalfPlane) : ℂ)‖ =
      ‖((a : ℤ) : ℂ) * (τ : ℂ) + ((b : ℤ) : ℂ)‖ / L := by
    rw [hσcoe, norm_div, hLdef]
  have hcop_ab : IsCoprime a b := ⟨d, -c, by nlinarith [habdet]⟩
  have hσ1 : 1 ≤ ‖((σ : UpperHalfPlane) : ℂ)‖ := by
    rw [hσnorm, le_div_iff₀ hLpos]
    have hmin := minimal_of_maxIm hg₀ hcop_ab
    rw [← hcdef, ← hddef, ← hLdef] at hmin
    linarith
  have hσm1 : 1 ≤ ‖((σ : UpperHalfPlane) : ℂ) - 1‖ := by
    have hcoe1 : ((σ : UpperHalfPlane) : ℂ) - 1 =
        ((((a - c : ℤ)) : ℂ) * (τ : ℂ) + (((b - d : ℤ)) : ℂ)) /
        (((c : ℤ) : ℂ) * (τ : ℂ) + ((d : ℤ) : ℂ)) := by
      have h1 : ((σ : UpperHalfPlane) : ℂ) - 1 =
          ((((a : ℤ) : ℂ) * (τ : ℂ) + ((b : ℤ) : ℂ))
            - (((c : ℤ) : ℂ) * (τ : ℂ) + ((d : ℤ) : ℂ))) /
          (((c : ℤ) : ℂ) * (τ : ℂ) + ((d : ℤ) : ℂ)) := by
        rw [hσcoe, ← div_self hD, ← sub_div]
      rw [h1]
      congr 1
      push_cast
      ring
    rw [hcoe1, norm_div, ← hLdef, le_div_iff₀ hLpos]
    have hcop2 : IsCoprime (a - c) (b - d) := ⟨d, -c, by nlinarith [habdet]⟩
    have hmin := minimal_of_maxIm hg₀ hcop2
    rw [← hcdef, ← hddef, ← hLdef] at hmin
    linarith
  -- the integer translate
  set k : ℤ := -⌊((σ : UpperHalfPlane) : ℂ).re⌋ with hkdef
  have hk_le : |(k : ℝ)| ≤ 6 * S ^ 3 := by
    have h1 : |(k : ℝ)| ≤ |((σ : UpperHalfPlane) : ℂ).re| + 1 := by
      rw [hkdef]
      have h2 : |((⌊((σ : UpperHalfPlane) : ℂ).re⌋ : ℤ) : ℝ)|
          ≤ |((σ : UpperHalfPlane) : ℂ).re| + 1 := by
        have h3 : ((⌊((σ : UpperHalfPlane) : ℂ).re⌋ : ℤ) : ℝ)
            ≤ ((σ : UpperHalfPlane) : ℂ).re := Int.floor_le _
        have h4 : ((σ : UpperHalfPlane) : ℂ).re
            < ((⌊((σ : UpperHalfPlane) : ℂ).re⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
        rw [abs_le]
        constructor
        · linarith [neg_abs_le ((σ : UpperHalfPlane) : ℂ).re]
        · linarith [le_abs_self ((σ : UpperHalfPlane) : ℂ).re]
      simpa using h2
    have h5 : |((σ : UpperHalfPlane) : ℂ).re| ≤ 5 * S ^ 3 := by
      have h6 : |((σ : UpperHalfPlane) : ℂ).re| ≤ ‖((σ : UpperHalfPlane) : ℂ)‖ :=
        Complex.abs_re_le_norm _
      rw [hσnorm] at h6
      have h7 : ‖((a : ℤ) : ℂ) * (τ : ℂ) + ((b : ℤ) : ℂ)‖ ≤ 5 * S ^ 2 := by
        have h8 : ‖((a : ℤ) : ℂ) * (τ : ℂ) + ((b : ℤ) : ℂ)‖
            ≤ ‖((a : ℤ) : ℂ) * (τ : ℂ)‖ + ‖((b : ℤ) : ℂ)‖ := norm_add_le _ _
        rw [norm_mul, Complex.norm_intCast, Complex.norm_intCast] at h8
        have h9 : |(a : ℝ)| * ‖(τ : ℂ)‖ ≤ 2 * S * S :=
          mul_le_mul haS hnormS (norm_nonneg _) (by linarith)
        have h10 : 2 * S * S = 2 * S ^ 2 := by ring
        linarith [h8, h9, h10, hbS]
      have h10 : (5 : ℝ) * S ^ 2 / L ≤ 5 * S ^ 3 := by
        rw [div_le_iff₀ hLpos]
        have h11 : (1 : ℝ) ≤ S * L := (div_le_iff₀ hLpos).mp hinvL
        have hpow : S ^ 3 = S ^ 2 * S := by ring
        have h12 : (0 : ℝ) ≤ S ^ 2 * (S * L - 1) :=
          mul_nonneg (sq_nonneg S) (by linarith)
        nlinarith [h12, hpow]
      calc |((σ : UpperHalfPlane) : ℂ).re|
          ≤ ‖((a : ℤ) : ℂ) * (τ : ℂ) + ((b : ℤ) : ℂ)‖ / L := h6
        _ ≤ 5 * S ^ 2 / L := by gcongr
        _ ≤ 5 * S ^ 3 := h10
    have hS3 : (1 : ℝ) ≤ S ^ 3 := one_le_pow₀ hS1
    linarith
  -- the shifted matrix
  set a' : ℤ := a + k * c with hadef
  set b' : ℤ := b + k * d with hbdef
  have ha'S : |(a' : ℝ)| ≤ 8 * S ^ 5 := by
    rw [hadef]
    push_cast
    have h1 : |(a : ℝ) + (k : ℝ) * (c : ℝ)| ≤ |(a : ℝ)| + |(k : ℝ)| * |(c : ℝ)| := by
      rw [← abs_mul]
      exact abs_add_le _ _
    have hkc : |(k : ℝ)| * |(c : ℝ)| ≤ 6 * S ^ 4 := by
      have h2 := mul_le_mul hk_le hcS (abs_nonneg _) (by positivity)
      have h3 : 6 * S ^ 3 * S = 6 * S ^ 4 := by ring
      linarith [h2, h3]
    have h2S : 2 * S ≤ 2 * S ^ 5 := by
      have h4 : S ^ 1 ≤ S ^ 5 := pow_le_pow_right₀ hS1 (by norm_num)
      simp only [pow_one] at h4
      linarith
    have h6S : 6 * S ^ 4 ≤ 6 * S ^ 5 := by
      have h4 : S ^ 4 ≤ S ^ 5 := pow_le_pow_right₀ hS1 (by norm_num)
      linarith
    linarith
  have hb'S : |(b' : ℝ)| ≤ 15 * S ^ 5 := by
    rw [hbdef]
    push_cast
    have h1 : |(b : ℝ) + (k : ℝ) * (d : ℝ)| ≤ |(b : ℝ)| + |(k : ℝ)| * |(d : ℝ)| := by
      rw [← abs_mul]
      exact abs_add_le _ _
    have hkd : |(k : ℝ)| * |(d : ℝ)| ≤ 12 * S ^ 5 := by
      have h2 := mul_le_mul hk_le hdS (abs_nonneg _) (by positivity)
      have h3 : 6 * S ^ 3 * (2 * S ^ 2) = 12 * S ^ 5 := by ring
      linarith [h2, h3]
    have h3S : 3 * S ^ 2 ≤ 3 * S ^ 5 := by
      have h4 : S ^ 2 ≤ S ^ 5 := pow_le_pow_right₀ hS1 (by norm_num)
      linarith
    linarith
  have hdetM' : Matrix.det !![a', b'; c, d] = 1 := by
    rw [det_fin_two_eq, hadef, hbdef]
    nlinarith [habdet]
  set M' : Matrix.SpecialLinearGroup (Fin 2) ℤ := ⟨!![a', b'; c, d], hdetM'⟩ with hM'def
  have hM'00 : M' 0 0 = a' := by simp [hM'def]
  have hM'01 : M' 0 1 = b' := by simp [hM'def]
  have hM'10 : M' 1 0 = c := by simp [hM'def]
  have hM'11 : M' 1 1 = d := by simp [hM'def]
  set σ' : UpperHalfPlane := M' • τ with hσ'def
  have hσ'coe : ((σ' : UpperHalfPlane) : ℂ) =
      (((a' : ℤ) : ℂ) * (τ : ℂ) + ((b' : ℤ) : ℂ)) /
      (((c : ℤ) : ℂ) * (τ : ℂ) + ((d : ℤ) : ℂ)) := by
    rw [hσ'def, coe_smul_eq M' τ, hM'00, hM'01, hM'10, hM'11]
  have hσ'val : ((σ' : UpperHalfPlane) : ℂ) = ((σ : UpperHalfPlane) : ℂ) + (k : ℂ) := by
    rw [hσ'coe, hσcoe, hadef, hbdef]
    push_cast
    field_simp
    ring
  have hσ're : ((σ' : UpperHalfPlane) : ℂ).re =
      Int.fract (((σ : UpperHalfPlane) : ℂ).re) := by
    have h := congrArg Complex.re hσ'val
    simp only [Complex.add_re, Complex.intCast_re] at h
    rw [h, hkdef]
    have hcast : (((-⌊((σ : UpperHalfPlane) : ℂ).re⌋ : ℤ)) : ℝ)
        = -(⌊((σ : UpperHalfPlane) : ℂ).re⌋ : ℝ) := by push_cast; ring
    rw [hcast, ← Int.self_sub_floor]
    ring
  have hσ'im : ((σ' : UpperHalfPlane) : ℂ).im = τ.im / L ^ 2 := by
    have h := congrArg Complex.im hσ'val
    simp only [Complex.add_im, Complex.intCast_im, add_zero] at h
    rw [h, hσim]
  have hσ'1 : 1 ≤ ‖((σ' : UpperHalfPlane) : ℂ)‖ := by
    have hcoenorm : ‖((σ' : UpperHalfPlane) : ℂ)‖ =
        ‖((a' : ℤ) : ℂ) * (τ : ℂ) + ((b' : ℤ) : ℂ)‖ / L := by
      rw [hσ'coe, norm_div, hLdef]
    rw [hcoenorm, le_div_iff₀ hLpos]
    have hcop' : IsCoprime a' b' := by
      refine ⟨d, -c, ?_⟩
      rw [hadef, hbdef]
      nlinarith [habdet]
    have hmin := minimal_of_maxIm hg₀ hcop'
    rw [← hcdef, ← hddef, ← hLdef] at hmin
    linarith
  have hσ'm1 : 1 ≤ ‖((σ' : UpperHalfPlane) : ℂ) - 1‖ := by
    have hcoe1 : ((σ' : UpperHalfPlane) : ℂ) - 1 =
        ((((a' - c : ℤ)) : ℂ) * (τ : ℂ) + (((b' - d : ℤ)) : ℂ)) /
        (((c : ℤ) : ℂ) * (τ : ℂ) + ((d : ℤ) : ℂ)) := by
      have h1 : ((σ' : UpperHalfPlane) : ℂ) - 1 =
          ((((a' : ℤ) : ℂ) * (τ : ℂ) + ((b' : ℤ) : ℂ))
            - (((c : ℤ) : ℂ) * (τ : ℂ) + ((d : ℤ) : ℂ))) /
          (((c : ℤ) : ℂ) * (τ : ℂ) + ((d : ℤ) : ℂ)) := by
        rw [hσ'coe, ← div_self hD, ← sub_div]
      rw [h1]
      congr 1
      push_cast
      ring
    rw [hcoe1, norm_div, ← hLdef, le_div_iff₀ hLpos]
    have hcop2 : IsCoprime (a' - c) (b' - d) := by
      refine ⟨d, -c, ?_⟩
      rw [hadef, hbdef]
      nlinarith [habdet]
    have hmin := minimal_of_maxIm hg₀ hcop2
    rw [← hcdef, ← hddef, ← hLdef] at hmin
    linarith
  have hmem : σ' ∈ closure Work.Asymptotics.DomainF := by
    refine closureDomainF_mem_of ?_ ?_ ?_ ?_
    · rw [← UpperHalfPlane.coe_re, hσ're]
      exact Int.fract_nonneg _
    · rw [← UpperHalfPlane.coe_re, hσ're]
      exact le_of_lt (Int.fract_lt_one _)
    · exact hσ'1
    · exact hσ'm1
  have hFrob_le : Work.Asymptotics.Frob M' ≤ 26 * S ^ 5 := by
    rw [hM'def, Frob_mk]
    calc Real.sqrt ((a' : ℝ) ^ 2 + (b' : ℝ) ^ 2 + (c : ℝ) ^ 2 + (d : ℝ) ^ 2)
        ≤ |(a' : ℝ)| + |(b' : ℝ)| + |(c : ℝ)| + |(d : ℝ)| := sqrt_sum_sq_le _ _ _ _
      _ ≤ 8 * S ^ 5 + 15 * S ^ 5 + S + 2 * S ^ 2 := by linarith [ha'S, hb'S, hcS, hdS]
      _ ≤ 26 * S ^ 5 := by
          have h1 : S ^ 1 ≤ S ^ 5 := pow_le_pow_right₀ hS1 (by norm_num)
          have h2 : S ^ 2 ≤ S ^ 5 := pow_le_pow_right₀ hS1 (by norm_num)
          simp only [pow_one] at h1
          linarith [h1, h2]
  have hscale_le : Work.Kernels.scale σ' ≤ 25 * S ^ 7 := by
    rw [Work.Kernels.scale]
    have him_inv : (σ'.im)⁻¹ ≤ S := by
      rw [← UpperHalfPlane.coe_im (σ' : UpperHalfPlane), hσ'im]
      have hL2 : L ^ 2 ≤ 1 := by nlinarith [hLle1, hLpos]
      have h1 : L ^ 2 / τ.im ≤ 1 / τ.im := div_le_div_of_nonneg_right hL2 (le_of_lt htpos)
      have h2 : (1 : ℝ) / τ.im ≤ S := by rw [one_div]; exact hinvS
      have h3 : (τ.im / L ^ 2)⁻¹ = L ^ 2 / τ.im := inv_div _ _
      rw [h3]
      linarith
    have hnormσ' : ‖((σ' : UpperHalfPlane) : ℂ)‖ ≤ 23 * S ^ 7 := by
      have hcoenorm : ‖((σ' : UpperHalfPlane) : ℂ)‖ =
          ‖((a' : ℤ) : ℂ) * (τ : ℂ) + ((b' : ℤ) : ℂ)‖ / L := by
        rw [hσ'coe, norm_div, hLdef]
      rw [hcoenorm, div_eq_mul_inv]
      have hinvL' : L⁻¹ ≤ S := by rw [inv_eq_one_div]; exact hinvL
      have hnum : ‖((a' : ℤ) : ℂ) * (τ : ℂ) + ((b' : ℤ) : ℂ)‖ ≤ 23 * S ^ 6 := by
        have h8 : ‖((a' : ℤ) : ℂ) * (τ : ℂ) + ((b' : ℤ) : ℂ)‖
            ≤ ‖((a' : ℤ) : ℂ) * (τ : ℂ)‖ + ‖((b' : ℤ) : ℂ)‖ := norm_add_le _ _
        rw [norm_mul, Complex.norm_intCast, Complex.norm_intCast] at h8
        have h9 : |(a' : ℝ)| * ‖(τ : ℂ)‖ ≤ 8 * S ^ 6 := by
          have h2 := mul_le_mul ha'S hnormS (norm_nonneg _) (by positivity)
          have h3 : 8 * S ^ 5 * S = 8 * S ^ 6 := by ring
          linarith [h2, h3]
        have h4 : 15 * S ^ 5 ≤ 15 * S ^ 6 := by
          have h5 : S ^ 5 ≤ S ^ 6 := pow_le_pow_right₀ hS1 (by norm_num)
          linarith
        linarith [h8, h9, h4, hb'S]
      calc ‖((a' : ℤ) : ℂ) * (τ : ℂ) + ((b' : ℤ) : ℂ)‖ * L⁻¹
          ≤ (23 * S ^ 6) * S := mul_le_mul hnum hinvL' (by positivity) (by positivity)
        _ ≤ 23 * S ^ 7 := by
            have h3 : (23 * S ^ 6) * S = 23 * S ^ 7 := by ring
            linarith
    have h1 : (1 : ℝ) ≤ S ^ 7 := one_le_pow₀ hS1
    have h2 : S ≤ S ^ 7 := by
      have := pow_le_pow_right₀ hS1 (show (1:ℕ) ≤ 7 by norm_num)
      simpa using this
    linarith
  refine ⟨M'⁻¹, ?_, ?_, ?_⟩
  · rw [inv_inv]
    simpa [hσ'def] using hmem
  · rw [Frob_inv]
    exact le_trans hFrob_le (pow_le_target S hS1 (by norm_num) (by norm_num))
  · rw [inv_inv, ← hσ'def]
    exact le_trans hscale_le (pow_le_target S hS1 (by norm_num) (by norm_num))

end Work.Rigidity.ReduceElement

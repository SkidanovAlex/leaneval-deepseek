import Mathlib
import Submission.Work.FIArea4.S15stratumDefs
import Submission.Work.FIArea4.S15EvarGDefs
import Submission.Work.FIArea4.S15prim_defs
import Submission.Work.FIArea4.S15EvgAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# `Work.FIArea4.S15EG` — the support box of the §15 stratum arrays

The stratum array `S15strU β u t ℓ e` is supported on the points `z` whose image
`w = ⟨e·Re z, Im z⟩` lies in the polar box (5.14) of `β`, hence has norm `< (1+θ)N ≤ 2N`; in
particular `e·|Re z| ≤ √(2N)` and `|Im z| ≤ √(2N)`.  This module fixes the resulting *support
box* `(S15EG_Re Pa e, S15EG_Se Pa)` of the variance chain (`2·S15EG_Re Pa e ≥ K/e`,
`2·S15EG_Se Pa ≥ K` with `K = (radN Pa).natAbs`), together with the elementary bounds on `K`.
-/

/-- `K = ⌈√(4N)⌉`, i.e. `radN Pa` read as a natural number. -/
def S15EG_K (Pa : Work.FITop.Params) : ℕ := (Work.FITop.radN Pa).natAbs

/-- The `Re`-support bound of the stratum `e`: chosen so that `2 * S15EG_Re Pa e ≥ K / e`. -/
def S15EG_Re (Pa : Work.FITop.Params) (e : ℕ) : ℕ := S15EG_K Pa / (2 * e) + 1

/-- The `Im`-support bound of every stratum: chosen so that `2 * S15EG_Se Pa ≥ K`. -/
def S15EG_Se (Pa : Work.FITop.Params) : ℕ := S15EG_K Pa / 2 + 1

/-- `radN Pa = K` as an integer. -/
lemma S15EG_radN_eq (Pa : Work.FITop.Params) : Work.FITop.radN Pa = (S15EG_K Pa : ℤ) := rfl

lemma S15EG_Re_pos (Pa : Work.FITop.Params) (e : ℕ) : 1 ≤ S15EG_Re Pa e := by
  rw [S15EG_Re]; exact Nat.le_add_left 1 _

lemma S15EG_Se_pos (Pa : Work.FITop.Params) : 1 ≤ S15EG_Se Pa := by
  rw [S15EG_Se]; exact Nat.le_add_left 1 _

lemma S15EG_sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `K ≥ 2√N`. -/
lemma S15EG_K_ge_two_sqrt (Pa : Work.FITop.Params) :
    2 * Real.sqrt Pa.N ≤ (S15EG_K Pa : ℝ) := by
  have hK : ((S15EG_K Pa : ℕ) : ℝ) = (⌈Real.sqrt (4*Pa.N)⌉₊ : ℝ) := by
    rw [S15EG_K, Work.FITop.radN]; simp
  rw [hK]
  have h4 : Real.sqrt (4 * Pa.N) = 2 * Real.sqrt Pa.N := by
    rw [show (4:ℝ)*Pa.N = 4 * Pa.N by ring, Real.sqrt_mul (by norm_num), S15EG_sqrt_four]
  rw [← h4]
  exact Nat.le_ceil _

/-- `K ≤ 2√N + 1`. -/
lemma S15EG_K_le_two_sqrt_add (Pa : Work.FITop.Params) :
    (S15EG_K Pa : ℝ) ≤ 2 * Real.sqrt Pa.N + 1 := by
  have hK : ((S15EG_K Pa : ℕ) : ℝ) = (⌈Real.sqrt (4*Pa.N)⌉₊ : ℝ) := by
    rw [S15EG_K, Work.FITop.radN]; simp
  rw [hK]
  have h4 : Real.sqrt (4 * Pa.N) = 2 * Real.sqrt Pa.N := by
    rw [show (4:ℝ)*Pa.N = 4 * Pa.N by ring, Real.sqrt_mul (by norm_num), S15EG_sqrt_four]
  rw [← h4]
  have h0 : (0:ℝ) ≤ Real.sqrt (4 * Pa.N) := Real.sqrt_nonneg _
  have hlt := Nat.ceil_lt_add_one h0
  linarith [hlt.le]

/-- `K ≤ 3√N`. -/
lemma S15EG_K_le (Pa : Work.FITop.Params) : (S15EG_K Pa : ℝ) ≤ 3 * Real.sqrt Pa.N := by
  have h1 := S15EG_K_le_two_sqrt_add Pa
  have hN1 : (1:ℝ) ≤ Pa.N := Pa.hN1
  have hsqrt : (1:ℝ) ≤ Real.sqrt Pa.N := Real.one_le_sqrt.mpr hN1
  linarith

/-- `K² ≤ 9N`. -/
lemma S15EG_K_sq_le (Pa : Work.FITop.Params) : ((S15EG_K Pa : ℕ) : ℝ)^2 ≤ 9 * Pa.N := by
  have h1 := S15EG_K_le Pa
  have hN1 : (1:ℝ) ≤ Pa.N := Pa.hN1
  have h2 : (0:ℝ) ≤ ((S15EG_K Pa : ℕ) : ℝ) := Nat.cast_nonneg _
  have h3 := pow_le_pow_left₀ h2 h1 2
  have hs : Real.sqrt Pa.N ^ 2 = Pa.N := Real.sq_sqrt (le_trans zero_le_one hN1)
  nlinarith [h3, hs]

/-- `1 ≤ K`. -/
lemma S15EG_K_pos (Pa : Work.FITop.Params) : 1 ≤ S15EG_K Pa := by
  rw [S15EG_K, Work.FITop.radN]
  simp only [Int.natAbs_natCast]
  refine Nat.one_le_ceil_iff.mpr ?_
  have hN1 : (1:ℝ) ≤ Pa.N := Pa.hN1
  have h2 : (1:ℝ) ≤ Real.sqrt (4 * Pa.N) := by
    rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith)
  linarith

/-- `√(2N) ≤ K`. -/
lemma S15EG_sqrt_two_le_K (Pa : Work.FITop.Params) :
    Real.sqrt (2 * Pa.N) ≤ (S15EG_K Pa : ℝ) := by
  have h := S15EG_K_ge_two_sqrt Pa
  have hN1 : (1:ℝ) ≤ Pa.N := Pa.hN1
  have hs : Real.sqrt (2 * Pa.N) ≤ 2 * Real.sqrt Pa.N := by
    have h2 : (0:ℝ) ≤ 2 * Pa.N := by linarith
    have h3 : (0:ℝ) ≤ 2 * Real.sqrt Pa.N := by positivity
    rw [← Real.sqrt_sq h3]
    apply Real.sqrt_le_sqrt
    nlinarith [Real.sq_sqrt (le_trans zero_le_one hN1), Real.sqrt_nonneg Pa.N]
  linarith

/-! ## The `z`-factor `S15zf` is unimodular-bounded -/

/-- `‖S15zf u t ℓ z‖ ≤ 1`. -/
lemma S15EG_norm_S15zf_le_one (u t : ℝ) (ℓ : ℤ) (z : GaussianInt) :
    ‖S15zf u t ℓ z‖ ≤ 1 := by
  have h1 : ‖Complex.exp (2 * Real.pi * Complex.I *
      ((u : ℂ) * (((z.im : ℝ) / (z.re : ℝ) : ℝ) : ℂ)))‖ = 1 := by
    rw [show 2 * ↑Real.pi * Complex.I * ((u : ℂ) * (((z.im : ℝ) / (z.re : ℝ) : ℝ) : ℂ))
        = (((2 * Real.pi * (u * ((z.im : ℝ) / (z.re : ℝ))) : ℝ)) : ℂ) * Complex.I by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have h2 : ‖(((z.re.natAbs : ℝ)) : ℂ) ^ (Complex.I * (t : ℂ))‖ ≤ 1 := by
    rcases Nat.eq_zero_or_pos z.re.natAbs with h | h
    · rw [h]; simp only [Nat.cast_zero, Complex.ofReal_zero]
      by_cases hh : Complex.I * (t : ℂ) = 0
      · rw [hh, Complex.cpow_zero]; norm_num
      · rw [Complex.zero_cpow hh]; norm_num
    · have hpos : (0 : ℝ) < (z.re.natAbs : ℝ) := by exact_mod_cast h
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by simpa using hpos)]
      simp
  have h3 : ‖(Complex.exp (Complex.I * (ℓ : ℂ) * ((Complex.arg z.toComplex : ℝ) : ℂ)))⁻¹‖ = 1 := by
    rw [norm_inv]
    rw [show Complex.I * (ℓ : ℂ) * ((Complex.arg z.toComplex : ℝ) : ℂ)
        = ((((ℓ : ℝ) * Complex.arg z.toComplex) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.norm_exp_ofReal_mul_I, inv_one]
  calc ‖S15zf u t ℓ z‖
      = ‖Complex.exp (2 * Real.pi * Complex.I *
            ((u : ℂ) * (((z.im : ℝ) / (z.re : ℝ) : ℝ) : ℂ)))‖
          * ‖(((z.re.natAbs : ℝ)) : ℂ) ^ (Complex.I * (t : ℂ))‖
          * ‖(Complex.exp (Complex.I * (ℓ : ℂ) * ((Complex.arg z.toComplex : ℝ) : ℂ)))⁻¹‖ := by
        rw [S15zf, norm_mul, norm_mul]
    _ = ‖(((z.re.natAbs : ℝ)) : ℂ) ^ (Complex.I * (t : ℂ))‖ := by rw [h1, h3]; ring
    _ ≤ 1 := h2

lemma S15EG_support_re (Pa : Work.FITop.Params) {e r : ℕ} (he : 1 ≤ e)
    (h : (r:ℝ) * e ≤ (S15EG_K Pa : ℝ)) : r ≤ 2 * S15EG_Re Pa e := by
  have he0 : 0 < e := by omega
  have h1 : r * e ≤ S15EG_K Pa := by exact_mod_cast h
  have h2 : S15EG_K Pa ≤ (2 * S15EG_Re Pa e) * e := by
    have h3 : S15EG_K Pa = 2*e*(S15EG_K Pa/(2*e)) + S15EG_K Pa % (2*e) :=
      (Nat.div_add_mod _ _).symm
    have h4 : S15EG_K Pa % (2*e) < 2*e := Nat.mod_lt _ (by omega)
    have h5 : 2 * S15EG_Re Pa e = 2 * (S15EG_K Pa / (2*e)) + 2 := by
      rw [S15EG_Re]; ring
    rw [h3, h5]
    nlinarith [h4]
  have h6 : r * e ≤ (2 * S15EG_Re Pa e) * e := le_trans h1 h2
  exact Nat.le_of_mul_le_mul_right h6 he0

lemma S15EG_support_im (Pa : Work.FITop.Params) {s : ℕ}
    (h : (s:ℝ) ≤ (S15EG_K Pa : ℝ)) : s ≤ 2 * S15EG_Se Pa := by
  have h1 : s ≤ S15EG_K Pa := by exact_mod_cast h
  have h2 : S15EG_K Pa ≤ 2 * S15EG_Se Pa := by
    have h3 : S15EG_K Pa = 2*(S15EG_K Pa/2) + S15EG_K Pa % 2 := (Nat.div_add_mod _ _).symm
    have h4 : S15EG_K Pa % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have h5 : 2 * S15EG_Se Pa = 2 * (S15EG_K Pa / 2) + 2 := by
      rw [S15EG_Se]; ring
    rw [h3, h5]
    omega
  exact le_trans h1 h2

/-! ## The stratum array `S15strU` and its support -/

/-- The definitional unfolding of `S15strU`. -/
lemma S15EG_strU_eq (β : GaussianInt → ℂ) (u t : ℝ) (ℓ : ℤ) (e : ℕ) (z : GaussianInt) :
    S15strU β u t ℓ e z
      = β ⟨(e : ℤ) * z.re, z.im⟩ * ((jacobiSym z.im e : ℤ) : ℂ)
        * S15zf u t ℓ ⟨(e : ℤ) * z.re, z.im⟩ := rfl

/-- **Support of the stratum array.**  If `S15strU β u t ℓ e w ≠ 0`, then the point
`⟨e·Re w, Im w⟩` lies in the polar box (5.14) of `β`, hence has norm `≤ (1+θ)N ≤ 2N`; in
particular `e·|Re w| ≤ K` and `|Im w| ≤ K`. -/
lemma S15EG_strU_support (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ)
    (hβ : IsPrimBoxCoeff Pa φ β) (u t : ℝ) (ℓ : ℤ) (e : ℕ) {w : GaussianInt}
    (hw : S15strU β u t ℓ e w ≠ 0) :
    (w.re.natAbs : ℝ) * e ≤ (S15EG_K Pa : ℝ) ∧ (w.im.natAbs : ℝ) ≤ (S15EG_K Pa : ℝ) := by
  rw [S15EG_strU_eq] at hw
  have hb : β ⟨(e:ℤ)*w.re, w.im⟩ ≠ 0 := by
    intro h0; exact hw (by rw [h0, zero_mul, zero_mul])
  have hpol := hβ.inPolarBox hb
  have hθ : Pa.θ ≤ 1 := S15theta_le_one Pa
  have hN0 : (0:ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have hgn : (Work.FIPlan.gnorm ⟨(e:ℤ)*w.re, w.im⟩ : ℝ) ≤ 2 * Pa.N := by
    have h1 := hpol.2.2.1
    nlinarith
  rw [gnorm_eq_re_sq_add_im_sq] at hgn
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at hgn
  have hgn' : (((e * w.re.natAbs : ℕ) : ℝ))^2 + ((w.im.natAbs : ℕ) : ℝ)^2 ≤ 2 * Pa.N := by
    simpa [Nat.cast_add, Nat.cast_pow] using hgn
  have hcast : (((e * w.re.natAbs : ℕ) : ℝ)) = (w.re.natAbs : ℝ) * e := by push_cast; ring
  rw [hcast] at hgn'
  have hre : (((w.re.natAbs : ℝ) * e)) ^ 2 ≤ 2 * Pa.N := by
    nlinarith [sq_nonneg (w.im.natAbs : ℝ)]
  have him : ((w.im.natAbs : ℝ)) ^ 2 ≤ 2 * Pa.N := by
    nlinarith [sq_nonneg (((w.re.natAbs : ℝ) * e))]
  have hsN := S15EG_sqrt_two_le_K Pa
  constructor
  · have h2 := Real.sqrt_le_sqrt hre
    rw [Real.sqrt_sq (by positivity)] at h2
    linarith
  · have h2 := Real.sqrt_le_sqrt him
    rw [Real.sqrt_sq (by positivity)] at h2
    linarith

/-- The `Re`-support of the stratum array lies in `[1, 2·S15EG_Re]`. -/
lemma S15EG_strU_support_re (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ)
    (hβ : IsPrimBoxCoeff Pa φ β) (u t : ℝ) (ℓ : ℤ) {e : ℕ} (he : 1 ≤ e) {w : GaussianInt}
    (hw : S15strU β u t ℓ e w ≠ 0) : w.re.natAbs ≤ 2 * S15EG_Re Pa e :=
  S15EG_support_re Pa he (S15EG_strU_support Pa φ β hβ u t ℓ e hw).1

/-- The `Im`-support of the stratum array lies in `[1, 2·S15EG_Se]`. -/
lemma S15EG_strU_support_im (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ)
    (hβ : IsPrimBoxCoeff Pa φ β) (u t : ℝ) (ℓ : ℤ) (e : ℕ) {w : GaussianInt}
    (hw : S15strU β u t ℓ e w ≠ 0) : w.im.natAbs ≤ 2 * S15EG_Se Pa :=
  S15EG_support_im Pa (S15EG_strU_support Pa φ β hβ u t ℓ e hw).2


/-! ## Elementary properties of the Jacobi-twisted variance `Evar` -/

/-- `Evar` is nonnegative. -/
lemma S15EG_Evar_nonneg (R S d : ℕ) (α : ℕ → ℕ → ℂ) : 0 ≤ Work.FIPlan.Evar R S d α := by
  unfold Work.FIPlan.Evar
  exact Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _)

/-- **Box shrinking.**  If `α` vanishes off the box `r ≤ 2R'`, `s ≤ 2S'` and `R' ≤ R`, `S' ≤ S`,
then `Evar R S d α = Evar R' S' d α`. -/
lemma S15EG_Evar_eq_of_le {R R' S S' d : ℕ} (hR : R' ≤ R) (hS : S' ≤ S) (α : ℕ → ℕ → ℂ)
    (h1 : ∀ r s, 2 * R' < r → α r s = 0) (h2 : ∀ r s, 2 * S' < s → α r s = 0) :
    Work.FIPlan.Evar R S d α = Work.FIPlan.Evar R' S' d α := by
  unfold Work.FIPlan.Evar
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  have hsub : (Finset.Icc 1 (2 * R')).filter (fun r => Nat.Coprime r d)
      ⊆ (Finset.Icc 1 (2 * R)).filter (fun r => Nat.Coprime r d) := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr1).1,
      le_trans (Finset.mem_Icc.mp hr1).2 (Nat.mul_le_mul_left 2 hR)⟩, hr2⟩
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl (fun r _ => ?_)
    have hsub2 : (Finset.Icc 1 (2 * S')).filter
          (fun s' => ((s' : ℕ) : ZMod d) = ((r : ℕ) : ZMod d) * ((a : ℕ) : ZMod d))
        ⊆ (Finset.Icc 1 (2 * S)).filter
          (fun s' => ((s' : ℕ) : ZMod d) = ((r : ℕ) : ZMod d) * ((a : ℕ) : ZMod d)) := by
      intro s hs
      obtain ⟨hs1, hs2⟩ := Finset.mem_filter.mp hs
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hs1).1,
        le_trans (Finset.mem_Icc.mp hs1).2 (Nat.mul_le_mul_left 2 hS)⟩, hs2⟩
    exact (Finset.sum_subset hsub2 (fun s hs hnot => by
      obtain ⟨hs1, hs2⟩ := Finset.mem_filter.mp hs
      have hgt : 2 * S' < s := by
        by_contra hle
        exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
          ⟨(Finset.mem_Icc.mp hs1).1, Nat.le_of_not_lt hle⟩, hs2⟩)
      rw [h2 r s hgt, zero_mul])).symm
  · intro r hr hnot
    obtain ⟨hr1, hr2⟩ := Finset.mem_filter.mp hr
    have hgt : 2 * R' < r := by
      by_contra hle
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hr1).1, Nat.le_of_not_lt hle⟩, hr2⟩)
    exact Finset.sum_eq_zero (fun s _ => by rw [h1 r s hgt, zero_mul])

/-- **`Evar` is dominated by `Vvar`** for any `D` with `D < m ≤ 2D`. -/
lemma S15EG_Evar_le_Vvar {R S D m : ℕ} (hmD : D < m) (hm2D : m ≤ 2 * D) (α : ℕ → ℕ → ℂ) :
    Work.FIPlan.Evar R S m α ≤ Work.FIPlan.Vvar R S D α := by
  unfold Work.FIPlan.Vvar
  exact Finset.single_le_sum (fun d _ => S15EG_Evar_nonneg R S d α)
    (Finset.mem_Ioc.mpr ⟨hmD, hm2D⟩)

/-! ## `quadArrE`, unfolded -/

lemma S15EG_quadArrE_eq (R : ℕ) (u : GaussianInt → ℂ) (σ₁ σ₂ : ℤ) (r s : ℕ)
    (hr : r ≤ R) (hs : s ≤ R) :
    quadArrE R u σ₁ σ₂ r s = u ⟨σ₁ * (r : ℤ), σ₂ * (s : ℤ)⟩ := by
  unfold quadArrE
  rw [if_pos]
  refine ⟨Finset.mem_Icc.mpr ⟨?_, by exact_mod_cast hr⟩,
          Finset.mem_Icc.mpr ⟨?_, by exact_mod_cast hs⟩⟩
  · show (-(R : ℤ)) ≤ ((r : ℕ) : ℤ)
    have h1 := Int.natCast_nonneg r
    have h2 : (0 : ℤ) ≤ (R : ℤ) := Int.natCast_nonneg R
    linarith
  · show (-(R : ℤ)) ≤ ((s : ℕ) : ℤ)
    have h1 := Int.natCast_nonneg s
    have h2 : (0 : ℤ) ≤ (R : ℤ) := Int.natCast_nonneg R
    linarith

lemma S15EG_quadArrE_eq_zero (R : ℕ) (u : GaussianInt → ℂ) (σ₁ σ₂ : ℤ) (r s : ℕ)
    (h : R < r ∨ R < s) : quadArrE R u σ₁ σ₂ r s = 0 := by
  unfold quadArrE
  rw [if_neg]
  rintro ⟨h1, h2⟩
  rw [Finset.mem_Icc] at h1 h2
  rcases h with h | h
  · exact absurd (by exact_mod_cast h1.2 : r ≤ R) (by omega)
  · exact absurd (by exact_mod_cast h2.2 : s ≤ R) (by omega)

/-! ## `S15strU` vanishes on the real axis, and the quadrant support -/

/-- **`S15strU` vanishes on the real axis.**  For `z.im = 0` the point `⟨e·Re z, 0⟩` can lie in
the support of a primitive box coefficient only if `|e·Re z| = 1`, which the polar box
(`gnorm > N ≥ 1`) excludes. -/
lemma S15EG_strU_eq_zero_of_im_eq_zero (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ)
    (hβ : IsPrimBoxCoeff Pa φ β) (u t : ℝ) (ℓ : ℤ) (e : ℕ) {z : GaussianInt}
    (hz : z.im = 0) : S15strU β u t ℓ e z = 0 := by
  rw [S15EG_strU_eq]
  have hb0 : β ⟨(e : ℤ) * z.re, z.im⟩ = 0 := by
    by_contra hb
    have hprim := hβ.coprime hb
    have him : (⟨(e : ℤ) * z.re, z.im⟩ : GaussianInt).im.natAbs = 0 := by
      show z.im.natAbs = 0
      rw [hz]; rfl
    rw [him, mul_zero] at hprim
    have hone : (⟨(e : ℤ) * z.re, z.im⟩ : GaussianInt).re.natAbs = 1 :=
      (Nat.coprime_zero_right _).mp hprim
    have hpol := hβ.inPolarBox hb
    have hgn : (1 : ℝ) < (Work.FIPlan.gnorm ⟨(e : ℤ) * z.re, z.im⟩ : ℝ) := by
      have := hpol.2.1; linarith [Pa.hN1]
    have h1 : (Work.FIPlan.gnorm ⟨(e : ℤ) * z.re, z.im⟩ : ℝ) = 1 := by
      rw [gnorm_eq_re_sq_add_im_sq]
      simp only [Int.natAbs_natCast]
      rw [hone, him]; norm_num
    linarith
  rw [hb0]; simp

/-- **Support of the quadrant array** `quadArrE K (S15strU β u t ℓ e) σ`. -/
lemma S15EG_quadArrE_strU_support (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ)
    (hβ : IsPrimBoxCoeff Pa φ β) (u t : ℝ) (ℓ : ℤ) (e : ℕ) (he : 1 ≤ e)
    {σ₁ σ₂ : ℤ} (hσ₁ : σ₁ = 1 ∨ σ₁ = -1) (hσ₂ : σ₂ = 1 ∨ σ₂ = -1) :
    ∀ r s, quadArrE (S15EG_K Pa) (S15strU β u t ℓ e) σ₁ σ₂ r s ≠ 0 →
      r ≤ 2 * S15EG_Re Pa e ∧ s ≤ 2 * S15EG_Se Pa := by
  intro r s hrs
  have hne : S15strU β u t ℓ e ⟨σ₁ * (r : ℤ), σ₂ * (s : ℤ)⟩ ≠ 0 := by
    intro h0
    exact hrs (by rw [quadArrE]; split_ifs <;> simp [h0])
  have hsup := S15EG_strU_support Pa φ β hβ u t ℓ e hne
  have hre_nat : (⟨σ₁ * (r : ℤ), σ₂ * (s : ℤ)⟩ : GaussianInt).re.natAbs = r := by
    show (σ₁ * (r : ℤ)).natAbs = r
    rcases hσ₁ with h | h <;> rw [h] <;> simp
  have him_nat : (⟨σ₁ * (r : ℤ), σ₂ * (s : ℤ)⟩ : GaussianInt).im.natAbs = s := by
    show (σ₂ * (s : ℤ)).natAbs = s
    rcases hσ₂ with h | h <;> rw [h] <;> simp
  rw [hre_nat, him_nat] at hsup
  exact ⟨S15EG_support_re Pa he hsup.1, S15EG_support_im Pa hsup.2⟩

/-! ## The quadrant arrays of the stratum -/

/-- Pointwise bound of a quadrant array by the coefficient `β`. -/
lemma S15EG_norm_quadArrE_le (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) (u t : ℝ) (ℓ : ℤ)
    (e : ℕ) (σ₁ σ₂ : ℤ) (r s : ℕ) :
    ‖quadArrE (S15EG_K Pa) (S15strU β u t ℓ e) σ₁ σ₂ r s‖
      ≤ ‖β ⟨(e : ℤ) * (σ₁ * (r : ℤ)), σ₂ * (s : ℤ)⟩‖ := by
  classical
  rw [quadArrE]
  split_ifs with h
  · rw [S15EG_strU_eq, norm_mul, norm_mul]
    calc ‖β ⟨↑e * (σ₁ * ↑r), σ₂ * ↑s⟩‖
          * ‖((jacobiSym (σ₂ * ↑s) e : ℤ) : ℂ)‖
          * ‖S15zf u t ℓ ⟨↑e * (σ₁ * ↑r), σ₂ * ↑s⟩‖
        ≤ ‖β ⟨↑e * (σ₁ * ↑r), σ₂ * ↑s⟩‖ * 1 * 1 := by
          gcongr
          · exact norm_jacobiSym_cast_le_one _ _
          · exact S15EG_norm_S15zf_le_one _ _ _ _
      _ = ‖β ⟨↑e * (σ₁ * ↑r), σ₂ * ↑s⟩‖ := by ring
  · simp

/-- `S15EG_Re` is monotone in `e`. -/
lemma S15EG_Re_anti (Pa : Work.FITop.Params) {e e' : ℕ} (he : 1 ≤ e) (hee : e ≤ e') :
    S15EG_Re Pa e' ≤ S15EG_Re Pa e := by
  rw [S15EG_Re, S15EG_Re]
  have h2 : 2 * e ≤ 2 * e' := by omega
  have := Nat.div_le_div_left (a := S15EG_K Pa) h2 (by omega : 0 < 2 * e)
  omega

end

end Work.FIArea4

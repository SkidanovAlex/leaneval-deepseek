/-
# `S15red.EvarG_filtered_strU_defs`

Vocabulary and elementary lemmas for the *filtered* stratum-`U` variance sum of FI §15,

`Σ_{e ≤ Y} Σ_{d' : X < e d' ≤ Y} EvarG (radN Pa) (4 d') (S15strU β u t ℓ e)`,

bounded in the τ²-energy form by `C (log N + 1)^24 · S15Br Pa X · Σ_z τ(|Re z|)²‖β z‖²`.

The main objects are the support box `(ReK Pa e, SeK Pa)` of the stratum `e` (the array
`S15strU β u t ℓ e` is supported on `|Re w| · e ≤ KK Pa`, `|Im w| ≤ KK Pa`), the quadratic
sum over the four sign quadrants, and the τ²-energy `E2`.
-/
import Mathlib
import Submission.Work.FIArea4.S15cutDefs
import Submission.Work.FIArea4.S15expSumDefs
import Submission.Work.FIArea4.S15stratumDefs
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIArea4.S15EvarGDefs
import Submission.Work.FIArea4.S15EvgAux
import Submission.Work.FIArea4.S15prim_defs
import Submission.Work.FIArea4.S15pDngAux
import Submission.Work.FIArea4.PairSumCommon
import Submission.Work.FIArea4.pair_sum_le_Evar
import Submission.Work.FIArea4.Assembly
import Submission.Work.FIArea4.Wdyad_le_majorant

namespace Work.FIArea4.S15red

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `K = ⌈√(4N)⌉`, i.e. `radN Pa` read as a natural number. -/
def KK (Pa : Work.FITop.Params) : ℕ := (Work.FITop.radN Pa).natAbs

/-- The `Re`-support bound `K/(2e) + 1` of the stratum `e` (the array `S15strU β u t ℓ e`
satisfies `|Re w| · e ≤ K`); chosen so that `2 * ReK Pa e ≥ K / e + 2`. -/
def ReK (Pa : Work.FITop.Params) (e : ℕ) : ℕ := KK Pa / (2 * e) + 1

/-- The `Im`-support bound `K/2 + 1` of every stratum. -/
def SeK (Pa : Work.FITop.Params) : ℕ := KK Pa / 2 + 1

/-- The four sign quadrants. -/
def Q2 : Finset ℤ := ({1, -1} : Finset ℤ)

/-- The τ²-energy `Σ_{z ∈ boxN} τ(|Re z|)² ‖β z‖²` of FI §15. -/
def E2 (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) : ℝ :=
  ∑ z ∈ Work.FITop.boxN Pa, (((z.re.natAbs.divisors.card : ℕ) : ℝ) ^ 2) * Complex.normSq (β z)

/-- The quadrant-reduced, `e`-stratified variance energy
`Σ_e Σ_{σ ∈ {±1}²} p14Ener (ReK Pa e) (SeK Pa) (quadArrE (S15strU β u t ℓ e))`. -/
def QStrEner (Pa : Work.FITop.Params) (X j : ℕ) (β : GaussianInt → ℂ) (u t : ℝ) (ℓ : ℤ) : ℝ :=
  ∑ e ∈ Finset.Icc 1 (Work.FIArea4.S15Y Pa X j),
    ∑ σ ∈ Q2.product Q2,
      Work.FIArea4.p14Ener (ReK Pa e) (SeK Pa)
        (Work.FIArea4.quadArrE (KK Pa) (Work.FIArea4.S15strU β u t ℓ e) σ.1 σ.2)

/-! ## Elementary arithmetic of `KK`, `ReK`, `SeK` -/

/-- For `0 < c`, `n/c - 1 < ⌊n/c⌋` (the "floor is within one" bound, on the lower side). -/
lemma div_sub_one_lt_cast_div (n c : ℕ) (hc : 0 < c) :
    (n : ℝ) / c - 1 < ((n / c : ℕ) : ℝ) := by
  have hnat := (Nat.div_lt_iff_lt_mul (x := n) (y := n / c + 1) (k := c) hc).mp
    (Nat.lt_succ_self (n / c))
  have hmul : (n:ℝ) < (((n / c : ℕ) : ℝ) + 1) * (c:ℝ) := by exact_mod_cast hnat
  have hcR : (0:ℝ) < (c:ℝ) := by exact_mod_cast hc
  have h2 : (n:ℝ)/(c:ℝ) < ((n/c:ℕ):ℝ) + 1 := (div_lt_iff₀ hcR).mpr (by linarith [hmul])
  linarith

lemma sqrt_two_mul_le_KK (Pa : Work.FITop.Params) :
    Real.sqrt (2 * Pa.N) ≤ ((KK Pa : ℕ) : ℝ) := by
  have h2N : 2 * Pa.N ≤ 4 * Pa.N := by linarith [Pa.hN1]
  have h1 : Real.sqrt (2 * Pa.N) ≤ Real.sqrt (4 * Pa.N) := Real.sqrt_le_sqrt h2N
  have h2 : Real.sqrt (4 * Pa.N) ≤ ((KK Pa : ℕ) : ℝ) := by
    rw [KK, Work.FITop.radN]
    simp only [Int.natAbs_natCast]
    exact Nat.le_ceil _
  linarith

lemma KK_pos (Pa : Work.FITop.Params) : 1 ≤ KK Pa := by
  have h : (1 : ℝ) ≤ ((KK Pa : ℕ) : ℝ) := by
    have h1 : (1 : ℝ) ≤ Real.sqrt (2 * Pa.N) := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by linarith [Pa.hN1])
    linarith [sqrt_two_mul_le_KK Pa, h1]
  exact_mod_cast h

lemma one_le_ReK (Pa : Work.FITop.Params) (e : ℕ) : 1 ≤ ReK Pa e := by
  rw [ReK]; exact Nat.le_add_left 1 _

lemma one_le_SeK (Pa : Work.FITop.Params) : 1 ≤ SeK Pa := by
  rw [SeK]; exact Nat.le_add_left 1 _

lemma ReK_le_SeK (Pa : Work.FITop.Params) {e : ℕ} (he : 1 ≤ e) : ReK Pa e ≤ SeK Pa := by
  rw [ReK, SeK]
  have h : KK Pa / (2 * e) ≤ KK Pa / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    calc KK Pa / (2 * e) * 2 ≤ KK Pa / (2 * e) * (2 * e) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ KK Pa := Nat.div_mul_le_self _ _
  omega

/-! ## The stratum array `S15strU`, unfolded, and the norm bound for `S15zf` -/

/-- The definitional unfolding of `S15strU` used throughout. -/
lemma S15strU_eq (β : GaussianInt → ℂ) (u t : ℝ) (ℓ : ℤ) (e : ℕ) (z : GaussianInt) :
    Work.FIArea4.S15strU β u t ℓ e z
      = β (Work.FIArea4.scalePt e z) * ((jacobiSym z.im e : ℤ) : ℂ)
        * Work.FIArea4.S15zf u t ℓ (Work.FIArea4.scalePt e z) := rfl

/-- `‖S15zf u t ℓ z‖ ≤ 1`. -/
lemma norm_S15zf_le_one (u t : ℝ) (ℓ : ℤ) (z : GaussianInt) :
    ‖Work.FIArea4.S15zf u t ℓ z‖ ≤ 1 := by
  rw [Work.FIArea4.S15zf]
  rw [norm_mul, norm_mul]
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
  rw [h1, h3, one_mul, mul_one]
  exact h2

/-! ## Support of the stratum array `S15strU` -/

/-- **Support of the stratum array.**  If `S15strU β u t ℓ e w ≠ 0`, then the point
`⟨e·Re w, Im w⟩` lies in the polar box (5.14) of `β`, hence has norm `< (1+θ)N ≤ 2N`; in
particular `e·|Re w| ≤ √(2N) ≤ K` and `|Im w| ≤ √(2N) ≤ K`, with `K = ⌈√(4N)⌉ = KK Pa`. -/
lemma S15strU_support (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ)
    (hβ : Work.FIArea4.IsPrimBoxCoeff Pa φ β) (u t : ℝ) (ℓ : ℤ) (e : ℕ) {w : GaussianInt}
    (hw : Work.FIArea4.S15strU β u t ℓ e w ≠ 0) :
    (w.re.natAbs : ℝ) * e ≤ KK Pa ∧ (w.im.natAbs : ℝ) ≤ KK Pa := by
  classical
  rw [S15strU_eq] at hw
  have hb : β (Work.FIArea4.scalePt e w) ≠ 0 := by
    intro h0; exact hw (by rw [h0, zero_mul, zero_mul])
  have hpol := hβ.inPolarBox hb
  have hθ : Pa.θ ≤ 1 := Work.FIArea4.S15theta_le_one Pa
  have hN0 : (0 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have hgn : (Work.FIPlan.gnorm (Work.FIArea4.scalePt e w) : ℝ) ≤ 2 * Pa.N := by
    have h1 := hpol.2.2.1; nlinarith [h1, hθ, hN0]
  rw [Work.FIArea4.gnorm_eq_re_sq_add_im_sq] at hgn
  simp only [Work.FIArea4.scalePt_re, Work.FIArea4.scalePt_im, Int.natAbs_mul,
    Int.natAbs_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at hgn
  have hre : (((w.re.natAbs : ℝ) * e)) ^ 2 ≤ 2 * Pa.N := by
    nlinarith [sq_nonneg (w.im.natAbs : ℝ)]
  have him : ((w.im.natAbs : ℝ)) ^ 2 ≤ 2 * Pa.N := by
    nlinarith [sq_nonneg (((w.re.natAbs : ℝ) * e))]
  have hsN := sqrt_two_mul_le_KK Pa
  constructor
  · have h2 := Real.sqrt_le_sqrt hre
    rw [Real.sqrt_sq (by positivity)] at h2
    exact le_trans h2 hsN
  · have h2 := Real.sqrt_le_sqrt him
    rw [Real.sqrt_sq (by positivity)] at h2
    exact le_trans h2 hsN

/-- **Support of the quadrant array** `quadArrE (KK Pa) (S15strU β u t ℓ e) σ`, for signs
`σ₁, σ₂ = ±1`: it is supported in `r ≤ 2 * ReK Pa e`, `s ≤ 2 * SeK Pa`. -/
lemma quadArrE_strU_support (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ)
    (hβ : Work.FIArea4.IsPrimBoxCoeff Pa φ β) (u t : ℝ) (ℓ : ℤ) (e : ℕ) (he : 1 ≤ e)
    {σ₁ σ₂ : ℤ} (hσ₁ : σ₁ = 1 ∨ σ₁ = -1) (hσ₂ : σ₂ = 1 ∨ σ₂ = -1) :
    ∀ r s, Work.FIArea4.quadArrE (KK Pa) (Work.FIArea4.S15strU β u t ℓ e) σ₁ σ₂ r s ≠ 0 →
      r ≤ 2 * ReK Pa e ∧ s ≤ 2 * SeK Pa := by
  intro r s hrs
  have hne : Work.FIArea4.S15strU β u t ℓ e ⟨σ₁ * (r : ℤ), σ₂ * (s : ℤ)⟩ ≠ 0 := by
    intro h0
    exact hrs (by rw [Work.FIArea4.quadArrE]; split_ifs <;> simp [h0])
  have hsup := S15strU_support Pa φ β hβ u t ℓ e hne
  have hre_nat : (⟨σ₁ * (r : ℤ), σ₂ * (s : ℤ)⟩ : GaussianInt).re.natAbs = r := by
    show (σ₁ * (r : ℤ)).natAbs = r
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    rcases hσ₁ with h | h <;> rw [h] <;> simp
  have him_nat : (⟨σ₁ * (r : ℤ), σ₂ * (s : ℤ)⟩ : GaussianInt).im.natAbs = s := by
    show (σ₂ * (s : ℤ)).natAbs = s
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    rcases hσ₂ with h | h <;> rw [h] <;> simp
  rw [hre_nat, him_nat] at hsup
  obtain ⟨h1, h2⟩ := hsup
  have hepos : (0:ℝ) < (e:ℝ) := by positivity
  have hdiv : (KK Pa:ℝ)/(2*(e:ℝ)) - 1 < ((KK Pa/(2*e):ℕ):ℝ) := by
    have := div_sub_one_lt_cast_div (KK Pa) (2*e) (by omega)
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using this
  have hdiv2 : (KK Pa:ℝ)/(2:ℝ) - 1 < ((KK Pa/2:ℕ):ℝ) := by
    have := div_sub_one_lt_cast_div (KK Pa) 2 (by norm_num)
    simpa only [Nat.cast_ofNat] using this
  constructor
  · have hid : (KK Pa : ℝ) / (e:ℝ) = 2 * ((KK Pa : ℝ) / (2*(e:ℝ))) := by field_simp
    have hKey : 2*(ReK Pa e : ℝ) = 2*(((KK Pa/(2*e):ℕ):ℝ)) + 2 := by rw [ReK]; push_cast; ring
    have hReK2 : ((KK Pa : ℕ) : ℝ) / (e:ℝ) ≤ 2 * (ReK Pa e : ℝ) := by
      rw [hKey, hid]; linarith
    have hrr : (r : ℝ) ≤ ((KK Pa : ℕ) : ℝ) / (e:ℝ) := by
      rw [le_div_iff₀ hepos]; linarith [h1]
    exact_mod_cast le_trans hrr hReK2
  · have hKey : 2*(SeK Pa : ℝ) = 2*(((KK Pa/2:ℕ):ℝ)) + 2 := by rw [SeK]; push_cast; ring
    have hSeK2 : ((KK Pa : ℕ) : ℝ) ≤ 2 * (SeK Pa : ℝ) := by
      rw [hKey]; linarith
    exact_mod_cast le_trans h2 hSeK2

/-- **Pointwise bound of the quadrant array by the coefficient `β`.** -/
lemma norm_quadArrE_le (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) (u t : ℝ) (ℓ : ℤ)
    (e : ℕ) (σ₁ σ₂ : ℤ) (r s : ℕ) :
    ‖Work.FIArea4.quadArrE (KK Pa) (Work.FIArea4.S15strU β u t ℓ e) σ₁ σ₂ r s‖
      ≤ ‖β (Work.FIArea4.scalePt e ⟨σ₁ * (r : ℤ), σ₂ * (s : ℤ)⟩)‖ := by
  classical
  rw [Work.FIArea4.quadArrE]
  split_ifs with h
  · rw [S15strU_eq, norm_mul, norm_mul]
    calc ‖β (Work.FIArea4.scalePt e ⟨σ₁ * (r : ℤ), σ₂ * (s : ℤ)⟩)‖
          * ‖((jacobiSym (σ₂ * (s : ℤ)) e : ℤ) : ℂ)‖
          * ‖Work.FIArea4.S15zf u t ℓ (Work.FIArea4.scalePt e ⟨σ₁ * (r : ℤ), σ₂ * (s : ℤ)⟩)‖
        ≤ ‖β (Work.FIArea4.scalePt e ⟨σ₁ * (r : ℤ), σ₂ * (s : ℤ)⟩)‖ * 1 * 1 := by
          gcongr
          · exact Work.FIArea4.norm_jacobiSym_cast_le_one _ _
          · exact norm_S15zf_le_one _ _ _ _
      _ = ‖β (Work.FIArea4.scalePt e ⟨σ₁ * (r : ℤ), σ₂ * (s : ℤ)⟩)‖ := by ring
  · simp

/-- **`S15strU` vanishes on the real axis.**  For `z.im = 0` the point `⟨e·Re z, 0⟩` can lie in the
support of a primitive box coefficient only if `|e·Re z| = 1`, which the polar box
(`gnorm > N ≥ 1`) excludes; hence `S15strU β u t ℓ e z = 0`. -/
lemma S15strU_eq_zero_of_im_eq_zero (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ)
    (hβ : Work.FIArea4.IsPrimBoxCoeff Pa φ β) (u t : ℝ) (ℓ : ℤ) (e : ℕ) {z : GaussianInt}
    (hz : z.im = 0) : Work.FIArea4.S15strU β u t ℓ e z = 0 := by
  rw [S15strU_eq]
  have hb0 : β (Work.FIArea4.scalePt e z) = 0 := by
    by_contra hb
    have hprim := hβ.coprime hb
    have him : (Work.FIArea4.scalePt e z).im.natAbs = 0 := by
      rw [Work.FIArea4.scalePt_im, hz]; rfl
    rw [him, mul_zero] at hprim
    have hone : (Work.FIArea4.scalePt e z).re.natAbs = 1 := (Nat.coprime_zero_right _).mp hprim
    have hpol := hβ.inPolarBox hb
    have hgn : (1 : ℝ) < (Work.FIPlan.gnorm (Work.FIArea4.scalePt e z) : ℝ) := by
      have := hpol.2.1; linarith [Pa.hN1]
    have h1 : (Work.FIPlan.gnorm (Work.FIArea4.scalePt e z) : ℝ) = 1 := by
      rw [Work.FIArea4.gnorm_eq_re_sq_add_im_sq, hone, him]; norm_num
    linarith
  rw [hb0]; ring

/-- **`S15strU` vanishes for `e > KK Pa`.** -/
lemma S15strU_eq_zero_of_gt (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ)
    (hβ : Work.FIArea4.IsPrimBoxCoeff Pa φ β) (u t : ℝ) (ℓ : ℤ) {e : ℕ} (he : KK Pa < e)
    (z : GaussianInt) : Work.FIArea4.S15strU β u t ℓ e z = 0 := by
  rw [S15strU_eq]
  have hb0 : β (Work.FIArea4.scalePt e z) = 0 := by
    by_contra hb
    have hprim := hβ.coprime hb
    have hre : (Work.FIArea4.scalePt e z).re.natAbs = e * z.re.natAbs := by
      rw [Work.FIArea4.scalePt_re, Int.natAbs_mul, Int.natAbs_natCast]
    have him : (Work.FIArea4.scalePt e z).im.natAbs = z.im.natAbs := by
      rw [Work.FIArea4.scalePt_im]
    rw [hre, him] at hprim
    have hzr : 1 ≤ z.re.natAbs := by
      by_contra h
      have h0 : z.re.natAbs = 0 := by omega
      rw [h0, Nat.mul_zero] at hprim
      have h1 : 2 * z.im.natAbs = 1 := (Nat.coprime_zero_left _).mp hprim
      omega
    have hpol := hβ.inPolarBox hb
    have hθ : Pa.θ ≤ 1 := Work.FIArea4.S15theta_le_one Pa
    have hN0 : (0 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
    have hgn : (Work.FIPlan.gnorm (Work.FIArea4.scalePt e z) : ℝ) ≤ 2 * Pa.N := by
      have h1 := hpol.2.2.1; nlinarith [h1, hθ, hN0]
    rw [Work.FIArea4.gnorm_eq_re_sq_add_im_sq] at hgn
    simp only [Work.FIArea4.scalePt_re, Work.FIArea4.scalePt_im, Int.natAbs_mul,
      Int.natAbs_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at hgn
    have hK2 : 4 * Pa.N ≤ ((KK Pa : ℕ) : ℝ) ^ 2 := by
      rw [KK, Work.FITop.radN]
      simp only [Int.natAbs_natCast]
      have h := Nat.le_ceil (Real.sqrt (4 * Pa.N))
      have h0 : (0 : ℝ) ≤ Real.sqrt (4 * Pa.N) := Real.sqrt_nonneg _
      have h2 := pow_le_pow_left₀ h0 h 2
      rwa [Real.sq_sqrt (by linarith [Pa.hN1] : (0:ℝ) ≤ 4 * Pa.N)] at h2
    have hzrR : (1 : ℝ) ≤ (z.re.natAbs : ℝ) := by exact_mod_cast hzr
    have heK : ((KK Pa : ℕ) : ℝ) < e := by exact_mod_cast he
    have hbig : ((KK Pa : ℕ) : ℝ) ^ 2 < (((z.re.natAbs : ℝ) * e)) ^ 2 := by
      have hKKnn : (0:ℝ) ≤ ((KK Pa:ℕ):ℝ) := Nat.cast_nonneg _
      have hprod : ((KK Pa : ℕ) : ℝ) < (z.re.natAbs : ℝ) * e := by
        have hepos : (0:ℝ) < (e:ℝ) := by linarith [heK, hKKnn]
        have h1 : (1:ℝ) * e ≤ (z.re.natAbs : ℝ) * e :=
          mul_le_mul_of_nonneg_right hzrR (le_of_lt hepos)
        linarith [h1, heK]
      exact pow_lt_pow_left₀ hprod hKKnn (by norm_num)
    have hsingle : (((z.re.natAbs : ℝ) * e)) ^ 2 ≤ 2 * Pa.N := by
      nlinarith [sq_nonneg (z.im.natAbs : ℝ)]
    linarith [hK2, hbig, hsingle]
  rw [hb0]; ring

end

end Work.FIArea4.S15red

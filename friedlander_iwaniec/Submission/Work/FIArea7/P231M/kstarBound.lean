/-
# `Work.FIArea7.P231.kstar_from_prop214` — *FI* Prop. 21.4 ⟹ the restricted bound `K*`

*FI* Prop. 21.4 states the bilinear estimate (21.13) for the Jacobi–Kubota bilinear form
`K(M,N) = ∑_w ∑_z α_w β_z [wz]`, and then derives, **inside the same proposition**, the same
estimate for the coprimality-restricted form

  `K*(M,N) = ∑_{(w,z)=1} α_w β_z [wz]`     (21.12)

by Möbius inversion.  This file performs that derivation from the proposition
`Work.FIArea7.Prop214` alone.

The derivation is the paper's:

* write `1[(w,z)=1] = ∑_{e primary, e | w, e | z} μ(e)` (the Gaussian Möbius indicator of
  `Work.FIArea4.gaussMoebius_coprime_indicator`) and exchange sums: `K* = ∑_e μ(e) T_e`;
* for each `e`, substitute `w = e w₁`, `z = e z₁`, so `T_e` is a sum of `α_{ew₁} β_{ez₁} [e²w₁z₁]`;
* the multiplier rule (`Work.FIArea7.jksym_mul_rule_primary`) gives

    `[e² w₁ z₁] = ε(e²,w₁z₁)·[e²]·[w₁z₁]·ξ_{e²}(w₁z₁)`

  and `ξ_{e²}(w₁z₁) = ξ_{e²}(w₁)ξ_{e²}(z₁)` (`Work.FIArea7.dirichletSym_mul`), the Dirichlet
  symbols being absorbed into the coefficients;
* the multiplier sign `ε(e²,w₁z₁)` — which depends on the *product* `w₁z₁` only — is expanded as a
  separated Fourier series in `w₁` and `z₁` (`Work.FIArea7.P231.multEps_expansion`, *FI* (20.15)
  + (20.19)); the `ℓ¹`-norm of the coefficients is `≪ log⁴(2R)`.

Hence `T_e` is bounded by `≪ log⁴(2R) ·‖K(M/|e|², N/|e|²)‖`, i.e. by `≪ |e|^{-23/6}·log⁴(2R)`
times the bound of `K(M,N)`; summing over the divisors `e` (the series `∑_e |e|^{-23/6}` converges,
`23/6 > 2`) gives the claim.

The two "room" conditions of the Fourier separation hold *automatically* here, with
`R = ⌈√(MN)⌉ + 2`: because `w₁, z₁, e²` are primary, the real parts `Re(w₁z₁)`, `Re(e²w₁z₁)` are odd
and hence `≥ 1` in absolute value, while `|w₁z₁| ≤ √(MN)/|e|² ≤ √(MN)` and
`|e²w₁z₁| ≤ √(MN)`.
-/
import Mathlib
import Submission.Work.FIArea7.P231Defs
import Submission.Work.FIArea7.jksym_mul_rule_primary
import Submission.Work.FIArea7.multEps_sqWave_separation
import Submission.Work.FIArea4.GaussMoebiusCore
import Submission.Work.FIArea4.gaussMoebius_coprime_indicator
import Submission.Work.FIArea7.dirichletSym_mul
import Submission.Work.FIArea7.cardFilterGnormLe
import Submission.Work.FIArea7.P231M.multEpsExpansion
import Submission.Work.FIArea7.P231.isPrimary_of_mul
import Submission.Work.FIArea7.P231.isCoprime_sq
import Submission.Work.FIArea7.P231.isCoprime_mul_factors
import Submission.Work.FIArea7.P231M.Aux2
import Submission.Work.FIArea7.P231.Bfun_scaling
import Submission.Work.FIArea7.P231M.Aux3

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea7.P231

/-! Copy of `kstar_from_prop214` with the three `sorry`-backed inputs replaced by proved versions
(`Work.FIArea7.P231.multEpsExpansion`, `Work.FIArea7.P231M.sumGnormPowLe`,
`Work.FIArea7.P231M.finalArith`). -/

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Elementary facts -/

/-- `|Re z| ≤ |z|²`. -/
lemma natAbs_re_le_gnorm (z : GaussianInt) : z.re.natAbs ≤ Work.FIPlan.gnorm z := by
  rcases Nat.eq_zero_or_pos z.re.natAbs with h | h
  · omega
  · have h2 : z.re.natAbs ^ 2 ≤ Work.FIPlan.gnorm z := by
      rw [Work.FIPlan.gnorm, GaussianInt.natAbs_norm_eq, pow_two]
      exact Nat.le_add_right _ _
    calc z.re.natAbs = z.re.natAbs * 1 := (Nat.mul_one _).symm
      _ ≤ z.re.natAbs * z.re.natAbs := Nat.mul_le_mul_left _ h
      _ = z.re.natAbs ^ 2 := (pow_two _).symm
      _ ≤ Work.FIPlan.gnorm z := h2

/-- `|Im z| ≤ |z|²`. -/
lemma natAbs_im_le_gnorm (z : GaussianInt) : z.im.natAbs ≤ Work.FIPlan.gnorm z := by
  rcases Nat.eq_zero_or_pos z.im.natAbs with h | h
  · omega
  · have h2 : z.im.natAbs ^ 2 ≤ Work.FIPlan.gnorm z := by
      rw [Work.FIPlan.gnorm, GaussianInt.natAbs_norm_eq, pow_two]
      exact Nat.le_add_left _ _
    calc z.im.natAbs = z.im.natAbs * 1 := (Nat.mul_one _).symm
      _ ≤ z.im.natAbs * z.im.natAbs := Nat.mul_le_mul_left _ h
      _ = z.im.natAbs ^ 2 := (pow_two _).symm
      _ ≤ Work.FIPlan.gnorm z := h2

/-- A primary `e ≠ 1` has non-zero imaginary part (a primary integer with `Im = 0` is `1`, since
`Im ≡ Re - 1 (mod 4)` with `Re` odd forces `Re ≡ 1 (mod 4)`, and primitivity is not needed if
`Im = 0` is combined with... — here we use the coprimality, which is the only case needed). -/
lemma im_ne_zero_of_isPrimary_ne_one {e : GaussianInt} (hP : Work.FIPlan.IsPrimary e)
    (hc : IsCoprime e.re e.im) (h1 : e ≠ 1) : e.im ≠ 0 := by
  intro him
  obtain ⟨ho, hev, h4⟩ := hP
  -- `e.im = 0`, so coprimality forces `e.re = ±1`
  rw [him] at hc
  have hg : e.re.natAbs = 1 := by
    have h := Int.isCoprime_iff_gcd_eq_one.mp hc
    rw [Int.gcd_eq_natAbs] at h
    simpa using h
  have hre : e.re = 1 ∨ e.re = -1 := by omega
  rcases hre with hre | hre
  · exact h1 (Zsqrtd.ext hre (by rw [him]; rfl))
  · exfalso
    rw [hre, him] at h4
    have hd : (4 : ℤ) ∣ (-1 - 1) - 0 := Int.modEq_iff_dvd.mp h4
    omega

/-- `(e * e).im = 2 * e.re * e.im`. -/
lemma mul_self_im (e : GaussianInt) : (e * e).im = 2 * e.re * e.im := by
  rw [im_mul]; ring

/-- `‖μ z‖ ≤ 1` for the Möbius function of `ℤ[i]`. -/
lemma norm_moebius_le_one (z : GaussianInt) :
    ‖((UniqueFactorizationMonoid.moebius z : ℤ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast, ← Int.cast_abs]
  have h : UniqueFactorizationMonoid.moebius z = 0 ∨
      UniqueFactorizationMonoid.moebius z = 1 ∨ UniqueFactorizationMonoid.moebius z = -1 := by
    by_cases hs : Squarefree z
    · rw [Squarefree.moebius_eq hs]
      rcases Nat.even_or_odd (UniqueFactorizationMonoid.factors z).card with he | ho
      · exact Or.inr (Or.inl (Even.neg_one_pow he))
      · exact Or.inr (Or.inr (Odd.neg_one_pow ho))
    · exact Or.inl (UniqueFactorizationMonoid.moebius_of_not_squarefree hs)
  rcases h with h | h | h <;> rw [h] <;> norm_num

/-- The `ℂ`-valued Möbius indicator of coprimality over a finite set `E` of primary Gaussian
integers containing all primary common divisors: for `z₁, z₂` of odd norm,

  `∑_{e ∈ E} μ(e)·1[e | z₁]·1[e | z₂] = 1[(z₁,z₂) = 1]`. -/
lemma moebius_indicator {E : Finset GaussianInt} {z1 z2 : GaussianInt}
    (hodd1 : Odd (Work.FIPlan.gnorm z1)) (hodd2 : Odd (Work.FIPlan.gnorm z2))
    (hE : ∀ e : GaussianInt, e ∣ z1 → e ∣ z2 → Work.FIPlan.IsPrimary e → e ∈ E)
    (hEprim : ∀ e ∈ E, Work.FIPlan.IsPrimary e) :
    (∑ e ∈ E, ((UniqueFactorizationMonoid.moebius e : ℤ) : ℂ)
        * (if e ∣ z1 ∧ e ∣ z2 then (1 : ℂ) else 0))
      = if Work.FIPlan.GaussCoprime z1 z2 then 1 else 0 := by
  classical
  have hz1 : z1 ≠ 0 := Work.FIArea4.odd_gnorm_ne_zero hodd1
  set g : GaussianInt := EuclideanDomain.gcd z1 z2 with hg
  have hgnz : g ≠ 0 := by
    intro h
    have hd := EuclideanDomain.gcd_dvd_left z1 z2
    rw [← hg, h] at hd
    exact hz1 (zero_dvd_iff.mp hd)
  have hgodd : Odd (Work.FIPlan.gnorm g) := by
    rw [hg]
    exact Work.FIArea4.odd_gnorm_of_dvd_odd (EuclideanDomain.gcd_dvd_left z1 z2) hodd1
  have hB : (Work.FIPlan.gnorm g : ℤ) ≤ ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) := by
    have hdvd : Work.FIPlan.gnorm g ∣ Work.FIPlan.gnorm z1 := by
      apply Work.FIArea4.gnorm_dvd
      rw [hg]; exact EuclideanDomain.gcd_dvd_left z1 z2
    exact_mod_cast Nat.le_of_dvd (Work.FIArea4.gnorm_pos hz1) hdvd
  have hseq : E.filter (fun e => e ∣ z1 ∧ e ∣ z2)
      = (Work.FIPlan.gBox ((Work.FIPlan.gnorm z1 : ℕ) : ℤ)).filter
          (fun e => e ∣ g ∧ Work.FIPlan.IsPrimary e) := by
    apply Finset.ext
    intro e
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨heE, h1, h2⟩
      have hp := hEprim e heE
      exact ⟨Work.FIArea4.primaryDivisor_mem_gBox hz1 h1 hp, by rw [hg]; exact EuclideanDomain.dvd_gcd h1 h2, hp⟩
    · rintro ⟨heB, hgd, hp⟩
      exact ⟨hE e (hgd.trans (EuclideanDomain.gcd_dvd_left z1 z2))
        (hgd.trans (EuclideanDomain.gcd_dvd_right z1 z2)) hp,
        hgd.trans (EuclideanDomain.gcd_dvd_left z1 z2),
        hgd.trans (EuclideanDomain.gcd_dvd_right z1 z2)⟩
  have hsum : (∑ e ∈ E, ((UniqueFactorizationMonoid.moebius e : ℤ) : ℂ)
        * (if e ∣ z1 ∧ e ∣ z2 then (1 : ℂ) else 0))
      = ∑ e ∈ (Work.FIPlan.gBox ((Work.FIPlan.gnorm z1 : ℕ) : ℤ)).filter
          (fun e => e ∣ g ∧ Work.FIPlan.IsPrimary e),
          ((UniqueFactorizationMonoid.moebius e : ℤ) : ℂ) := by
    rw [← hseq, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e he
    by_cases h : e ∣ z1 ∧ e ∣ z2 <;> simp [h]
  rw [hsum, Work.FIArea4.sum_primaryDivs_eq_of_le g hgnz hgodd hB]
  have hiff : IsUnit g ↔ Work.FIPlan.GaussCoprime z1 z2 := by
    rw [Work.FIPlan.GaussCoprime, hg]
    exact EuclideanDomain.gcd_isUnit_iff (x := z1) (y := z2)
  by_cases hc : IsUnit g
  · rw [if_pos hc, if_pos (hiff.mp hc)]
  · rw [if_neg hc, if_neg (fun h => hc (hiff.mpr h))]

/-- The room parameter: `⌈√(MN)⌉ + 2`. -/
def RR (M N : ℝ) : ℕ := Nat.ceil (Real.sqrt (M * N)) + 2

/-- The shape of the bound of *FI* (21.13). -/
def Bfun (C A M N : ℝ) : ℝ :=
  C * (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12) * (Real.log (M * N + 2)) ^ A

/-- Membership in `gBox R` from `natAbs` bounds and `R ≥ 0`. -/
lemma mem_gBox_of_natAbs_le {R : ℤ} (hR : 0 ≤ R) {z : GaussianInt}
    (h1 : z.re.natAbs ≤ R.natAbs) (h2 : z.im.natAbs ≤ R.natAbs) :
    z ∈ Work.FIPlan.gBox R := by
  have h1' : |z.re| ≤ R := by
    rw [Int.abs_eq_natAbs]
    have : (z.re.natAbs : ℤ) ≤ (R.natAbs : ℤ) := by exact_mod_cast h1
    rwa [Int.natAbs_of_nonneg hR] at this
  have h2' : |z.im| ≤ R := by
    rw [Int.abs_eq_natAbs]
    have : (z.im.natAbs : ℤ) ≤ (R.natAbs : ℤ) := by exact_mod_cast h2
    rwa [Int.natAbs_of_nonneg hR] at this
  rw [Work.FIArea4.mem_gBox]
  exact ⟨(abs_le.mp h1').1, (abs_le.mp h1').2, (abs_le.mp h2').1, (abs_le.mp h2').2⟩

/-- `gnorm z = (Re z)² + (Im z)²`. -/
lemma gnorm_sq (z : GaussianInt) :
    Work.FIPlan.gnorm z = z.re.natAbs ^ 2 + z.im.natAbs ^ 2 := by
  rw [Work.FIPlan.gnorm, GaussianInt.natAbs_norm_eq]; ring

/-- A `gBox Rw` member of the form `e * w₁` bounds `gnorm w₁ ≤ 2 Rw²`. -/
lemma gnorm_le_of_mul_mem_gBox {e w₁ : GaussianInt} {Rw : ℤ}
    (he : e ≠ 0) (h : e * w₁ ∈ Work.FIPlan.gBox Rw) :
    Work.FIPlan.gnorm w₁ ≤ 2 * Rw.natAbs ^ 2 := by
  rw [Work.FIArea4.mem_gBox] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hre : (e * w₁).re.natAbs ≤ Rw.natAbs := by
    have h5 : |(e * w₁).re| ≤ Rw := abs_le.mpr ⟨by omega, by omega⟩
    have h6 : (((e * w₁).re.natAbs : ℤ)) ≤ Rw := by rwa [Int.abs_eq_natAbs] at h5
    have h7 : (((e * w₁).re.natAbs : ℤ)) ≤ ((Rw.natAbs : ℤ)) := by
      calc (((e * w₁).re.natAbs : ℤ)) ≤ Rw := h6
        _ ≤ ((Rw.natAbs : ℤ)) := by omega
    exact_mod_cast h7
  have him : (e * w₁).im.natAbs ≤ Rw.natAbs := by
    have h5 : |(e * w₁).im| ≤ Rw := abs_le.mpr ⟨by omega, by omega⟩
    have h6 : (((e * w₁).im.natAbs : ℤ)) ≤ Rw := by rwa [Int.abs_eq_natAbs] at h5
    have h7 : (((e * w₁).im.natAbs : ℤ)) ≤ ((Rw.natAbs : ℤ)) := by
      calc (((e * w₁).im.natAbs : ℤ)) ≤ Rw := h6
        _ ≤ ((Rw.natAbs : ℤ)) := by omega
    exact_mod_cast h7
  have h2' : Work.FIPlan.gnorm (e * w₁) ≤ 2 * Rw.natAbs ^ 2 := by
    rw [gnorm_sq]
    have ha := Nat.pow_le_pow_left hre 2
    have hb := Nat.pow_le_pow_left him 2
    linarith
  rw [Work.FIArea4.gnorm_mul] at h2'
  have hpos : 1 ≤ Work.FIPlan.gnorm e := Nat.one_le_iff_ne_zero.mpr (Work.FIArea4.gnorm_ne_zero he)
  calc Work.FIPlan.gnorm w₁ = 1 * Work.FIPlan.gnorm w₁ := (one_mul _).symm
    _ ≤ Work.FIPlan.gnorm e * Work.FIPlan.gnorm w₁ := Nat.mul_le_mul_right _ hpos
    _ ≤ 2 * Rw.natAbs ^ 2 := h2'

/-- Reindexing a doubly filtered box-sum along `w ↦ e * w`. -/
lemma sum_filter_dvd_eq {e : GaussianInt} (he : e ≠ 0) (F : GaussianInt → GaussianInt → ℂ)
    {Rw Rz MC NC : ℤ}
    (hMC : ∀ w₁, e * w₁ ∈ Work.FIPlan.gBox Rw → w₁ ∈ Work.FIPlan.gBox MC)
    (hNC : ∀ z₁, e * z₁ ∈ Work.FIPlan.gBox Rz → z₁ ∈ Work.FIPlan.gBox NC) :
    (∑ w ∈ (Work.FIPlan.gBox Rw).filter (fun w => e ∣ w),
       ∑ z ∈ (Work.FIPlan.gBox Rz).filter (fun z => e ∣ z), F w z)
      = ∑ w₁ ∈ Work.FIPlan.gBox MC, ∑ z₁ ∈ Work.FIPlan.gBox NC,
          (if e * w₁ ∈ Work.FIPlan.gBox Rw then (1 : ℂ) else 0)
            * (if e * z₁ ∈ Work.FIPlan.gBox Rz then (1 : ℂ) else 0) * F (e * w₁) (e * z₁) := by
  have hinj : Function.Injective (fun w₁ : GaussianInt => e * w₁) :=
    fun x y hxy => mul_left_cancel₀ he hxy
  have himgw : ((Work.FIPlan.gBox MC).filter (fun w₁ => e * w₁ ∈ Work.FIPlan.gBox Rw)).image
        (fun w₁ => e * w₁)
      = (Work.FIPlan.gBox Rw).filter (fun w => e ∣ w) := by
    apply Finset.ext
    intro w
    rw [Finset.mem_image]
    constructor
    · rintro ⟨w₁, hw₁, rfl⟩
      rw [Finset.mem_filter] at hw₁ ⊢
      exact ⟨hw₁.2, dvd_mul_right e w₁⟩
    · rintro hw
      rw [Finset.mem_filter] at hw
      obtain ⟨hw1, w₁, rfl⟩ := hw
      exact ⟨w₁, by rw [Finset.mem_filter]; exact ⟨hMC w₁ hw1, hw1⟩, rfl⟩
  have himgz : ((Work.FIPlan.gBox NC).filter (fun z₁ => e * z₁ ∈ Work.FIPlan.gBox Rz)).image
        (fun z₁ => e * z₁)
      = (Work.FIPlan.gBox Rz).filter (fun z => e ∣ z) := by
    apply Finset.ext
    intro z
    rw [Finset.mem_image]
    constructor
    · rintro ⟨z₁, hz₁, rfl⟩
      rw [Finset.mem_filter] at hz₁ ⊢
      exact ⟨hz₁.2, dvd_mul_right e z₁⟩
    · rintro hz
      rw [Finset.mem_filter] at hz
      obtain ⟨hz1, z₁, rfl⟩ := hz
      exact ⟨z₁, by rw [Finset.mem_filter]; exact ⟨hNC z₁ hz1, hz1⟩, rfl⟩
  rw [← himgw]
  rw [Finset.sum_image (f := fun w => ∑ z ∈ (Work.FIPlan.gBox Rz).filter (fun z => e ∣ z), F w z)
        (g := fun w₁ => e * w₁) hinj.injOn]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w₁ _
  by_cases h1 : e * w₁ ∈ Work.FIPlan.gBox Rw
  · simp only [h1, if_true]
    rw [← himgz]
    rw [Finset.sum_image (f := fun z => F (e * w₁) z) (g := fun z₁ => e * z₁) hinj.injOn]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z₁ _
    by_cases h2 : e * z₁ ∈ Work.FIPlan.gBox Rz <;> simp [h2]
  · simp only [h1, if_false]
    simp [h1]

/-! ## 2. Elementary bounds -/

/-- `‖(z/‖z‖)^k‖ ≤ 1`. -/
lemma norm_div_norm_zpow_le (z : GaussianInt) (k : ℤ) :
    ‖(z.toComplex / (((‖z.toComplex‖ : ℝ)) : ℂ)) ^ k‖ ≤ 1 := by
  rcases eq_or_ne z.toComplex 0 with h | h
  · rw [h, norm_zero, zero_div]
    rcases eq_or_ne k 0 with hk | hk
    · rw [hk]; simp
    · rw [zero_zpow _ hk]; simp
  · have hpos : 0 < ‖z.toComplex‖ := norm_pos_iff.mpr h
    have hnorm : ‖(((‖z.toComplex‖ : ℝ)) : ℂ)‖ = ‖z.toComplex‖ := by
      rw [show ‖(((‖z.toComplex‖ : ℝ)) : ℂ)‖ = |‖z.toComplex‖| by simp,
        abs_of_nonneg hpos.le]
    rw [norm_zpow, norm_div, hnorm, div_self (ne_of_gt hpos), one_zpow]

/-- `‖(1/2 : ℂ)‖ = 1/2`. -/
lemma norm_two_inv : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
  rw [show (1 / 2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) by norm_num, Complex.norm_real,
    Real.norm_eq_abs]
  norm_num

/-- `‖z.toComplex‖ = √|z|²`. -/
lemma norm_toComplex_sqrt (z : GaussianInt) :
    ‖z.toComplex‖ = Real.sqrt (((Work.FIPlan.gnorm z : ℕ)) : ℝ) := by
  have h2 : (((Work.FIPlan.gnorm z : ℕ)) : ℝ) = (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 := by
    have h3 : (Work.FIPlan.gnorm z : ℤ) = z.re ^ 2 + z.im ^ 2 := Work.FIArea7.norm_eq z
    exact_mod_cast h3
  have h : ‖z.toComplex‖ ^ 2 = (((Work.FIPlan.gnorm z : ℕ)) : ℝ) := by
    rw [Complex.sq_norm, Complex.normSq_apply, h2,
      GaussianInt.intCast_re, GaussianInt.intCast_im]
    ring
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

/-- `(u,v)_∞² = 1`. -/
lemma hilb_sq (u v : ℤ) : (HilbertInf u v : ℂ) * (HilbertInf u v : ℂ) = 1 := by
  have h : (HilbertInf u v : ℂ) = -1 ∨ (HilbertInf u v : ℂ) = 1 := by
    rw [HilbertInf]; split_ifs <;> simp
  rcases h with h | h <;> rw [h] <;> norm_num

/-- The real part of a product of primary Gaussian integers is odd. -/
lemma odd_re_mul_of_isPrimary {w z : GaussianInt} (hw : Work.FIPlan.IsPrimary w)
    (hz : Work.FIPlan.IsPrimary z) : Odd (w * z).re := by
  obtain ⟨hu, hv, _⟩ := hw
  obtain ⟨hr, hs, _⟩ := hz
  rw [re_mul]
  exact (hu.mul hr).sub_even (hv.mul_right z.im)

/-- For primary `w, z` the real part of `wz` is a non-zero odd integer. -/
lemma abs_re_mul_ge_one {w z : GaussianInt} (hw : Work.FIPlan.IsPrimary w)
    (hz : Work.FIPlan.IsPrimary z) :
    (1 : ℝ) ≤ |((((w * z).re : ℤ)) : ℝ)| := by
  have hodd := odd_re_mul_of_isPrimary hw hz
  have hne : (w * z).re ≠ 0 := by
    intro h; rw [h] at hodd; exact (Int.not_even_iff_odd.mpr hodd) ⟨0, by norm_num⟩
  have h1 : (1 : ℤ) ≤ |(w * z).re| := by
    have := abs_pos.mpr hne; omega
  rw [← Int.cast_abs]
  exact_mod_cast h1

/-- The "room" condition of the Fourier separation, in the form used below. -/
lemma room_cond_le {M N : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) {w z : GaussianInt}
    (hw : Work.FIPlan.IsPrimary w) (hz : Work.FIPlan.IsPrimary z)
    (hgw : (Work.FIPlan.gnorm w : ℝ) ≤ M) (hgz : (Work.FIPlan.gnorm z : ℝ) ≤ N) :
    ‖w.toComplex‖ * ‖z.toComplex‖ ≤ ((RR M N : ℕ) : ℝ) * |((((w * z).re : ℤ)) : ℝ)| := by
  have hMN : (0 : ℝ) ≤ M * N := by nlinarith
  have h1 : ‖w.toComplex‖ * ‖z.toComplex‖ ≤ Real.sqrt (M * N) := by
    have hsq : ‖w.toComplex‖ * ‖z.toComplex‖
        = Real.sqrt (((Work.FIPlan.gnorm (w * z) : ℕ)) : ℝ) := by
      rw [norm_toComplex_sqrt, norm_toComplex_sqrt, ← Real.sqrt_mul (by positivity),
        ← Nat.cast_mul, ← Work.FIArea4.gnorm_mul]
    rw [hsq, Real.sqrt_le_sqrt_iff (by positivity), Work.FIArea4.gnorm_mul]
    push_cast
    exact mul_le_mul hgw hgz (by positivity) (by linarith)
  have h2 : Real.sqrt (M * N) ≤ ((RR M N : ℕ) : ℝ) := by
    have h3 : Real.sqrt (M * N) ≤ (Nat.ceil (Real.sqrt (M * N)) : ℝ) := Nat.le_ceil _
    simp only [RR]; push_cast; linarith
  have h3 : (1 : ℝ) ≤ |((((w * z).re : ℤ)) : ℝ)| := abs_re_mul_ge_one hw hz
  have h4 : (0 : ℝ) ≤ ((RR M N : ℕ) : ℝ) := by positivity
  calc ‖w.toComplex‖ * ‖z.toComplex‖ ≤ Real.sqrt (M * N) := h1
    _ ≤ ((RR M N : ℕ) : ℝ) := h2
    _ ≤ ((RR M N : ℕ) : ℝ) * |((((w * z).re : ℤ)) : ℝ)| := by nlinarith


/-- `‖(u,v)_∞‖ = 1` in `ℂ`. -/
lemma norm_hilb (u v : ℤ) : ‖(HilbertInf u v : ℂ)‖ = 1 := by
  have h : (HilbertInf u v : ℂ) = -1 ∨ (HilbertInf u v : ℂ) = 1 := by
    rw [HilbertInf]; split_ifs <;> simp
  rcases h with h | h <;> rw [h] <;> norm_num

/-! ## 3. The coefficient families of the reduction -/

/-- The `w`-side coefficient after absorbing `ξ_{e²}`: `α(e w₁)ξ_{e²}(w₁)`, zero off the box. -/
def kA (Rw : ℤ) (e σ : GaussianInt) (α : GaussianInt → ℂ) (w₁ : GaussianInt) : ℂ :=
  if e * w₁ ∈ Work.FIPlan.gBox Rw then α (e * w₁) * (((DirichletSym σ w₁ : ℤ)) : ℂ) else 0

/-- The `z`-side coefficient after absorbing `ξ_{e²}`. -/
def kB (Rz : ℤ) (e σ : GaussianInt) (β : GaussianInt → ℂ) (z₁ : GaussianInt) : ℂ :=
  if e * z₁ ∈ Work.FIPlan.gBox Rz then β (e * z₁) * (((DirichletSym σ z₁ : ℤ)) : ℂ) else 0

/-- The `k`-th `w`-side coefficient of the Fourier separation. -/
def kGam (Rw : ℤ) (e σ : GaussianInt) (α : GaussianInt → ℂ) (k : ℤ) (w₁ : GaussianInt) : ℂ :=
  kA Rw e σ α w₁ * ((w₁.toComplex / (((‖w₁.toComplex‖ : ℝ)) : ℂ)) ^ k)

/-- The `k`-th `z`-side coefficient of the Fourier separation. -/
def kDel (Rz : ℤ) (e σ : GaussianInt) (β : GaussianInt → ℂ) (k : ℤ) (z₁ : GaussianInt) : ℂ :=
  kB Rz e σ β z₁ * ((z₁.toComplex / (((‖z₁.toComplex‖ : ℝ)) : ℂ)) ^ k)

lemma norm_kA_le {Rw : ℤ} {e σ : GaussianInt} {α : GaussianInt → ℂ}
    (hα : ∀ w, ‖α w‖ ≤ 1) (w₁ : GaussianInt) : ‖kA Rw e σ α w₁‖ ≤ 1 := by
  rw [kA]; split_ifs with h
  · rw [norm_mul]
    exact mul_le_one₀ (hα _) (norm_nonneg _)
      (by rw [Complex.norm_intCast, ← Int.cast_abs]
          exact_mod_cast abs_dirichletSym_le_one σ w₁)
  · simp

lemma norm_kB_le {Rz : ℤ} {e σ : GaussianInt} {β : GaussianInt → ℂ}
    (hβ : ∀ z, ‖β z‖ ≤ 1) (z₁ : GaussianInt) : ‖kB Rz e σ β z₁‖ ≤ 1 := by
  rw [kB]; split_ifs with h
  · rw [norm_mul]
    exact mul_le_one₀ (hβ _) (norm_nonneg _)
      (by rw [Complex.norm_intCast, ← Int.cast_abs]
          exact_mod_cast abs_dirichletSym_le_one σ z₁)
  · simp

lemma norm_kGam_le {Rw : ℤ} {e σ : GaussianInt} {α : GaussianInt → ℂ}
    (hα : ∀ w, ‖α w‖ ≤ 1) (k : ℤ) (w₁ : GaussianInt) : ‖kGam Rw e σ α k w₁‖ ≤ 1 := by
  rw [kGam, norm_mul]
  exact mul_le_one₀ (norm_kA_le hα w₁) (norm_nonneg _) (norm_div_norm_zpow_le w₁ k)

lemma norm_kDel_le {Rz : ℤ} {e σ : GaussianInt} {β : GaussianInt → ℂ}
    (hβ : ∀ z, ‖β z‖ ≤ 1) (k : ℤ) (z₁ : GaussianInt) : ‖kDel Rz e σ β k z₁‖ ≤ 1 := by
  rw [kDel, norm_mul]
  exact mul_le_one₀ (norm_kB_le hβ z₁) (norm_nonneg _) (norm_div_norm_zpow_le z₁ k)

lemma norm_triple_le {Rw Rz : ℤ} {e σ : GaussianInt} {α β : GaussianInt → ℂ}
    (hα : ∀ w, ‖α w‖ ≤ 1) (hβ : ∀ z, ‖β z‖ ≤ 1) (k : ℤ) (w₁ z₁ : GaussianInt) :
    ‖kGam Rw e σ α k w₁ * kDel Rz e σ β k z₁ * JKSym (w₁ * z₁)‖ ≤ 1 := by
  rw [norm_mul, norm_mul]
  exact mul_le_one₀ (mul_le_one₀ (norm_kGam_le hα k w₁) (norm_nonneg _)
    (norm_kDel_le hβ k z₁)) (by positivity) (norm_JKSym_le_one _)

lemma supp_kGam {Rw : ℤ} {e σ : GaussianInt} {α : GaussianInt → ℂ} {M : ℝ}
    (he : Work.FIPlan.IsPrimary e) (hgann : 0 < (Work.FIPlan.gnorm e : ℝ))
    (hsα : ∀ w, α w ≠ 0 → Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧
      (Work.FIPlan.gnorm w : ℝ) ≤ M)
    {k : ℤ} {w₁ : GaussianInt} (hw : kGam Rw e σ α k w₁ ≠ 0) :
    Work.FIPlan.IsPrimary w₁ ∧ IsCoprime w₁.re w₁.im ∧
      (Work.FIPlan.gnorm w₁ : ℝ) ≤ M / (Work.FIPlan.gnorm e : ℝ) := by
  rw [kGam, mul_ne_zero_iff, kA] at hw
  by_cases hmem : e * w₁ ∈ Work.FIPlan.gBox Rw
  · rw [if_pos hmem] at hw
    have hαw : α (e * w₁) ≠ 0 := fun h0 => hw.1 (by rw [h0, zero_mul])
    refine ⟨isPrimary_of_mul he (hsα (e * w₁) hαw).1,
      isCoprime_mul_factors (hsα (e * w₁) hαw).2.1, ?_⟩
    have hle := (hsα (e * w₁) hαw).2.2
    rw [Work.FIArea4.gnorm_mul] at hle
    push_cast at hle
    rw [le_div_iff₀ hgann]; linarith
  · rw [if_neg hmem] at hw
    exact absurd rfl hw.1

lemma supp_kDel {Rz : ℤ} {e σ : GaussianInt} {β : GaussianInt → ℂ} {N : ℝ}
    (he : Work.FIPlan.IsPrimary e) (hgann : 0 < (Work.FIPlan.gnorm e : ℝ))
    (hsβ : ∀ z, β z ≠ 0 → Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ N)
    {k : ℤ} {z₁ : GaussianInt} (hz : kDel Rz e σ β k z₁ ≠ 0) :
    Work.FIPlan.IsPrimary z₁ ∧ (Work.FIPlan.gnorm z₁ : ℝ) ≤ N / (Work.FIPlan.gnorm e : ℝ) := by
  rw [kDel, mul_ne_zero_iff, kB] at hz
  by_cases hmem : e * z₁ ∈ Work.FIPlan.gBox Rz
  · rw [if_pos hmem] at hz
    have hβz : β (e * z₁) ≠ 0 := fun h0 => hz.1 (by rw [h0, zero_mul])
    refine ⟨isPrimary_of_mul he (hsβ (e * z₁) hβz).1, ?_⟩
    have hle := (hsβ (e * z₁) hβz).2
    rw [Work.FIArea4.gnorm_mul] at hle
    push_cast at hle
    rw [le_div_iff₀ hgann]; linarith
  · rw [if_neg hmem] at hz
    exact absurd rfl hz.1

/-! ## 4. The per-divisor reduction -/

/-- **The per-divisor reduction.** -/
lemma per_e_bound {C A C1 : ℝ} (hC : 0 < C) (hC1 : 0 < C1)
    (hK : ∀ (M N : ℝ) (Rw Rz : ℤ) (α β : GaussianInt → ℂ),
      1 ≤ M → 1 ≤ N →
      (∀ w, ‖α w‖ ≤ 1) → (∀ z, ‖β z‖ ≤ 1) →
      (∀ w, α w ≠ 0 → Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧
        (Work.FIPlan.gnorm w : ℝ) ≤ M) →
      (∀ z, β z ≠ 0 → Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ N) →
      ‖KBilin Rw Rz α β‖ ≤ Bfun C A M N)
    (hmult : ∀ (σ : GaussianInt) (R : ℕ), 2 ≤ R → Work.FIPlan.IsPrimary σ →
      IsCoprime σ.re σ.im → σ.im ≠ 0 → ∃ ĉ : ℤ → ℂ,
        (∀ s : Finset ℤ, ∑ k ∈ s, ‖ĉ k‖ ≤ C1 * (Real.log (2 * (R : ℝ))) ^ 4) ∧
        ∀ (w z : GaussianInt), Work.FIPlan.IsPrimary w → Work.FIPlan.IsPrimary z →
          w ≠ 0 → z ≠ 0 →
          ‖σ.toComplex‖ * ‖(w * z).toComplex‖
              ≤ (R : ℝ) * |((((σ * (w * z)).re : ℤ)) : ℝ)| →
          ‖w.toComplex‖ * ‖z.toComplex‖ ≤ (R : ℝ) * |((((w * z).re : ℤ)) : ℝ)| →
          HasSum (fun k : ℤ => ĉ k * ((w.toComplex / (‖w.toComplex‖ : ℂ)) ^ k
            * (z.toComplex / (‖z.toComplex‖ : ℂ)) ^ k))
            (2 * (MultEps σ (w * z) : ℂ) * (HilbertInf σ.re σ.im : ℂ)))
    (hBfun : ∀ (e : GaussianInt), Work.FIPlan.IsPrimary e → ∀ (M N : ℝ), 1 ≤ M → 1 ≤ N →
      Bfun C A (M / (Work.FIPlan.gnorm e : ℝ)) (N / (Work.FIPlan.gnorm e : ℝ))
        ≤ ((Work.FIPlan.gnorm e : ℝ)) ^ (-(23 / 12 : ℝ)) * Bfun C A M N)
    {M N : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) {Rw Rz : ℤ} {α β : GaussianInt → ℂ}
    (hα : ∀ w, ‖α w‖ ≤ 1) (hβ : ∀ z, ‖β z‖ ≤ 1)
    (hsα : ∀ w, α w ≠ 0 → Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧
        (Work.FIPlan.gnorm w : ℝ) ≤ M)
    (hsβ : ∀ z, β z ≠ 0 → Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ N)
    (e : GaussianInt) (heP : Work.FIPlan.IsPrimary e) (hec : IsCoprime e.re e.im)
    (he1 : e ≠ 1) :
    ‖∑ w ∈ (Work.FIPlan.gBox Rw).filter (fun w => e ∣ w),
       ∑ z ∈ (Work.FIPlan.gBox Rz).filter (fun z => e ∣ z),
         α w * β z * JKSym (w * z)‖
      ≤ (C1 / 2) * (Real.log (2 * ((RR M N : ℕ) : ℝ))) ^ 4
          * ((Work.FIPlan.gnorm e : ℝ)) ^ (-(23 / 12 : ℝ)) * Bfun C A M N := by
  classical
  have he0 : e ≠ 0 := Work.FIArea4.isPrimary_ne_zero heP
  by_cases hsz : (Work.FIPlan.gnorm e : ℝ) ≤ M ∧ (Work.FIPlan.gnorm e : ℝ) ≤ N
  · obtain ⟨heM, heN⟩ := hsz
    have hgann : (0 : ℝ) < (Work.FIPlan.gnorm e : ℝ) := by
      exact_mod_cast Work.FIArea4.gnorm_pos he0
    have hg1 : (1 : ℝ) ≤ (Work.FIPlan.gnorm e : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Work.FIArea4.gnorm_ne_zero he0)
    have hMnn : (0 : ℝ) ≤ M := le_trans zero_le_one hM
    have hNnn : (0 : ℝ) ≤ N := le_trans zero_le_one hN
    have hMg : 1 ≤ M / (Work.FIPlan.gnorm e : ℝ) := by
      rw [le_div_iff₀ hgann]; linarith
    have hNg : 1 ≤ N / (Work.FIPlan.gnorm e : ℝ) := by
      rw [le_div_iff₀ hgann]; linarith
    have heim : e.im ≠ 0 := im_ne_zero_of_isPrimary_ne_one heP hec he1
    set σ : GaussianInt := e * e with hσdef
    have hσP : Work.FIPlan.IsPrimary σ := by
      rw [hσdef]; exact Work.FIArea4.isPrimary_mul heP heP
    have hσc : IsCoprime σ.re σ.im := by rw [hσdef]; exact isCoprime_sq heP hec
    have hσim : σ.im ≠ 0 := by
      rw [hσdef, mul_self_im]
      exact mul_ne_zero (mul_ne_zero (by norm_num) (Work.FIArea7.primary_re_ne_zero heP)) heim
    have hR2 : 2 ≤ RR M N := by simp only [RR]; omega
    have hRRnn : (0 : ℝ) ≤ ((RR M N : ℕ) : ℝ) := by positivity
    obtain ⟨ĉ, hc_bound, hc_has⟩ := hmult σ (RR M N) hR2 hσP hσc hσim
    have hc_summ : Summable fun k : ℤ => ‖ĉ k‖ :=
      summable_of_sum_le (fun k => norm_nonneg _) hc_bound
    have hc_tsum : ∑' k : ℤ, ‖ĉ k‖ ≤ C1 * (Real.log (2 * ((RR M N : ℕ) : ℝ))) ^ 4 :=
      Summable.tsum_le_of_sum_le hc_summ hc_bound
    set MC : ℤ := (((2 * Rw.natAbs ^ 2 + 2 : ℕ) : ℤ)) with hMCdef
    set NC : ℤ := (((2 * Rz.natAbs ^ 2 + 2 : ℕ) : ℤ)) with hNCdef
    have hMCmem : ∀ w₁ : GaussianInt, e * w₁ ∈ Work.FIPlan.gBox Rw →
        w₁ ∈ Work.FIPlan.gBox MC := by
      intro w₁ hw₁
      have hmem := gnorm_le_of_mul_mem_gBox he0 hw₁
      refine mem_gBox_of_natAbs_le (by rw [hMCdef]; positivity) ?_ ?_
      · calc w₁.re.natAbs ≤ Work.FIPlan.gnorm w₁ := natAbs_re_le_gnorm w₁
          _ ≤ 2 * Rw.natAbs ^ 2 := hmem
          _ ≤ MC.natAbs := by simp only [hMCdef, Int.natAbs_natCast]; omega
      · calc w₁.im.natAbs ≤ Work.FIPlan.gnorm w₁ := natAbs_im_le_gnorm w₁
          _ ≤ 2 * Rw.natAbs ^ 2 := hmem
          _ ≤ MC.natAbs := by simp only [hMCdef, Int.natAbs_natCast]; omega
    have hNCmem : ∀ z₁ : GaussianInt, e * z₁ ∈ Work.FIPlan.gBox Rz →
        z₁ ∈ Work.FIPlan.gBox NC := by
      intro z₁ hz₁
      have hmem := gnorm_le_of_mul_mem_gBox he0 hz₁
      refine mem_gBox_of_natAbs_le (by rw [hNCdef]; positivity) ?_ ?_
      · calc z₁.re.natAbs ≤ Work.FIPlan.gnorm z₁ := natAbs_re_le_gnorm z₁
          _ ≤ 2 * Rz.natAbs ^ 2 := hmem
          _ ≤ NC.natAbs := by simp only [hNCdef, Int.natAbs_natCast]; omega
      · calc z₁.im.natAbs ≤ Work.FIPlan.gnorm z₁ := natAbs_im_le_gnorm z₁
          _ ≤ 2 * Rz.natAbs ^ 2 := hmem
          _ ≤ NC.natAbs := by simp only [hNCdef, Int.natAbs_natCast]; omega
    have hre : (∑ w ∈ (Work.FIPlan.gBox Rw).filter (fun w => e ∣ w),
          ∑ z ∈ (Work.FIPlan.gBox Rz).filter (fun z => e ∣ z),
            α w * β z * JKSym (w * z))
        = ∑ w₁ ∈ Work.FIPlan.gBox MC, ∑ z₁ ∈ Work.FIPlan.gBox NC,
            (if e * w₁ ∈ Work.FIPlan.gBox Rw then α (e * w₁) else 0)
              * (if e * z₁ ∈ Work.FIPlan.gBox Rz then β (e * z₁) else 0)
              * JKSym ((e * w₁) * (e * z₁)) := by
      rw [sum_filter_dvd_eq he0 (fun w z => α w * β z * JKSym (w * z)) hMCmem hNCmem]
      apply Finset.sum_congr rfl; intro w₁ _
      apply Finset.sum_congr rfl; intro z₁ _
      by_cases h1 : e * w₁ ∈ Work.FIPlan.gBox Rw
      · by_cases h2 : e * z₁ ∈ Work.FIPlan.gBox Rz
        · simp only [if_pos h1, if_pos h2]; ring_nf
        · simp only [if_pos h1, if_neg h2]; ring_nf
      · simp only [if_neg h1]; ring_nf
    have hpt : ∀ w₁ z₁ : GaussianInt,
        (if e * w₁ ∈ Work.FIPlan.gBox Rw then α (e * w₁) else 0)
          * (if e * z₁ ∈ Work.FIPlan.gBox Rz then β (e * z₁) else 0)
          * JKSym ((e * w₁) * (e * z₁))
        = (1 / 2 : ℂ) * JKSym σ * (HilbertInf σ.re σ.im : ℂ)
            * (∑' k : ℤ, ĉ k * (kGam Rw e σ α k w₁ * kDel Rz e σ β k z₁ * JKSym (w₁ * z₁))) := by
      intro w₁ z₁
      by_cases h1 : e * w₁ ∈ Work.FIPlan.gBox Rw
      · by_cases h2 : e * z₁ ∈ Work.FIPlan.gBox Rz
        · rw [if_pos h1, if_pos h2]
          by_cases h3 : α (e * w₁) = 0
          · have hzero : (∑' k : ℤ, ĉ k * (kGam Rw e σ α k w₁ * kDel Rz e σ β k z₁
                * JKSym (w₁ * z₁))) = 0 := by
              rw [show (∑' k : ℤ, ĉ k * (kGam Rw e σ α k w₁ * kDel Rz e σ β k z₁
                    * JKSym (w₁ * z₁))) = ∑' _ : ℤ, (0 : ℂ) from
                tsum_congr (fun k => by
                  simp only [kGam, kA, kDel, kB, if_pos h1, if_pos h2, h3, mul_zero, zero_mul])]
              exact tsum_zero
            rw [h3, hzero]; ring
          · by_cases h4 : β (e * z₁) = 0
            · have hzero : (∑' k : ℤ, ĉ k * (kGam Rw e σ α k w₁ * kDel Rz e σ β k z₁
                  * JKSym (w₁ * z₁))) = 0 := by
                rw [show (∑' k : ℤ, ĉ k * (kGam Rw e σ α k w₁ * kDel Rz e σ β k z₁
                      * JKSym (w₁ * z₁))) = ∑' _ : ℤ, (0 : ℂ) from
                  tsum_congr (fun k => by
                    simp only [kGam, kA, kDel, kB, if_pos h1, if_pos h2, h4, mul_zero, zero_mul])]
                exact tsum_zero
              rw [h4, mul_zero, hzero]; ring
            · have hwP : Work.FIPlan.IsPrimary w₁ :=
                isPrimary_of_mul heP (hsα (e * w₁) h3).1
              have hzP : Work.FIPlan.IsPrimary z₁ :=
                isPrimary_of_mul heP (hsβ (e * z₁) h4).1
              have hα0 : α 0 = 0 := by
                by_contra hh
                have h1' := (hsα 0 hh).1.1
                rw [show (0 : GaussianInt).re = 0 from rfl] at h1'
                obtain ⟨k, hk⟩ := h1'; omega
              have hβ0 : β 0 = 0 := by
                by_contra hh
                have h1' := (hsβ 0 hh).1.1
                rw [show (0 : GaussianInt).re = 0 from rfl] at h1'
                obtain ⟨k, hk⟩ := h1'; omega
              have hwN : w₁ ≠ 0 := fun h => h3 (by rw [h, mul_zero]; exact hα0)
              have hzN : z₁ ≠ 0 := fun h => h4 (by rw [h, mul_zero]; exact hβ0)
              have hwMg : (Work.FIPlan.gnorm w₁ : ℝ) ≤ M / (Work.FIPlan.gnorm e : ℝ) := by
                have hle := (hsα (e * w₁) h3).2.2
                rw [Work.FIArea4.gnorm_mul] at hle
                push_cast at hle
                rw [le_div_iff₀ hgann]; linarith
              have hzNg : (Work.FIPlan.gnorm z₁ : ℝ) ≤ N / (Work.FIPlan.gnorm e : ℝ) := by
                have hle := (hsβ (e * z₁) h4).2
                rw [Work.FIArea4.gnorm_mul] at hle
                push_cast at hle
                rw [le_div_iff₀ hgann]; linarith
              have hgwM : (Work.FIPlan.gnorm w₁ : ℝ) ≤ M :=
                le_trans hwMg (div_le_self hMnn hg1)
              have hgzM : (Work.FIPlan.gnorm z₁ : ℝ) ≤ N :=
                le_trans hzNg (div_le_self hNnn hg1)
              have hroom2 := room_cond_le hM hN hwP hzP hgwM hgzM
              have hroom1 : ‖σ.toComplex‖ * ‖(w₁ * z₁).toComplex‖
                  ≤ ((RR M N : ℕ) : ℝ) * |((((σ * (w₁ * z₁)).re : ℤ)) : ℝ)| := by
                have hgnσ : Work.FIPlan.gnorm σ = (Work.FIPlan.gnorm e) ^ 2 := by
                  rw [hσdef, Work.FIArea4.gnorm_mul]; ring
                have hsq : ‖σ.toComplex‖ * ‖(w₁ * z₁).toComplex‖
                    = Real.sqrt ((((Work.FIPlan.gnorm σ * Work.FIPlan.gnorm (w₁ * z₁) : ℕ)) : ℝ)) := by
                  rw [norm_toComplex_sqrt, norm_toComplex_sqrt, ← Real.sqrt_mul (by positivity),
                    ← Nat.cast_mul, ← Work.FIArea4.gnorm_mul]
                rw [hsq]
                have hle : ((Work.FIPlan.gnorm σ * Work.FIPlan.gnorm (w₁ * z₁) : ℕ) : ℝ) ≤ M * N := by
                  rw [hgnσ, Work.FIArea4.gnorm_mul]; push_cast
                  calc (Work.FIPlan.gnorm e : ℝ) ^ 2
                        * ((Work.FIPlan.gnorm w₁ : ℝ) * (Work.FIPlan.gnorm z₁ : ℝ))
                      ≤ (Work.FIPlan.gnorm e : ℝ) ^ 2 * ((M / (Work.FIPlan.gnorm e : ℝ))
                          * (N / (Work.FIPlan.gnorm e : ℝ))) := by
                        exact mul_le_mul_of_nonneg_left
                          (mul_le_mul hwMg hzNg (by positivity) (by positivity)) (by positivity)
                    _ = M * N := by field_simp
                have hre1 : (1 : ℝ) ≤ |((((σ * (w₁ * z₁)).re : ℤ)) : ℝ)| :=
                  abs_re_mul_ge_one hσP (Work.FIArea4.isPrimary_mul hwP hzP)
                calc Real.sqrt _ ≤ Real.sqrt (M * N) := Real.sqrt_le_sqrt hle
                  _ ≤ ((RR M N : ℕ) : ℝ) := by
                      have h5 : Real.sqrt (M * N) ≤ (Nat.ceil (Real.sqrt (M * N)) : ℝ) :=
                        Nat.le_ceil _
                      simp only [RR]; push_cast; linarith
                  _ ≤ ((RR M N : ℕ) : ℝ) * |((((σ * (w₁ * z₁)).re : ℤ)) : ℝ)| := by
                      nlinarith [hre1, hRRnn]
              have hHS := hc_has w₁ z₁ hwP hzP hwN hzN hroom1 hroom2
              have hsum_eq : (∑' k : ℤ, ĉ k * ((w₁.toComplex / (((‖w₁.toComplex‖ : ℝ)) : ℂ)) ^ k
                    * (z₁.toComplex / (((‖z₁.toComplex‖ : ℝ)) : ℂ)) ^ k))
                  = 2 * (MultEps σ (w₁ * z₁) : ℂ) * (HilbertInf σ.re σ.im : ℂ) := hHS.tsum_eq
              have hH2 : (HilbertInf σ.re σ.im : ℂ) * (HilbertInf σ.re σ.im : ℂ) = 1 :=
                hilb_sq σ.re σ.im
              have heps : (MultEps σ (w₁ * z₁) : ℂ)
                  = (1 / 2 : ℂ) * (HilbertInf σ.re σ.im : ℂ)
                    * (∑' k : ℤ, ĉ k * ((w₁.toComplex / (((‖w₁.toComplex‖ : ℝ)) : ℂ)) ^ k
                        * (z₁.toComplex / (((‖z₁.toComplex‖ : ℝ)) : ℂ)) ^ k)) := by
                rw [hsum_eq]
                rw [show (1 / 2 : ℂ) * (HilbertInf σ.re σ.im : ℂ)
                      * (2 * (MultEps σ (w₁ * z₁) : ℂ) * (HilbertInf σ.re σ.im : ℂ))
                    = (MultEps σ (w₁ * z₁) : ℂ)
                      * ((HilbertInf σ.re σ.im : ℂ) * (HilbertInf σ.re σ.im : ℂ)) by ring,
                  hH2, mul_one]
              have hprod : (e * w₁) * (e * z₁) = σ * (w₁ * z₁) := by rw [hσdef]; ring
              have hjk := jksym_mul_rule_primary hσP hσc (Work.FIArea4.isPrimary_mul hwP hzP)
              have hds := dirichletSym_mul hσP hσc w₁ z₁
              have hL : α (e * w₁) * β (e * z₁) * JKSym (σ * (w₁ * z₁))
                  = (1 / 2 : ℂ) * JKSym σ * (HilbertInf σ.re σ.im : ℂ)
                    * (∑' k : ℤ, ĉ k * ((w₁.toComplex / (((‖w₁.toComplex‖ : ℝ)) : ℂ)) ^ k
                        * (z₁.toComplex / (((‖z₁.toComplex‖ : ℝ)) : ℂ)) ^ k))
                    * (α (e * w₁) * (((DirichletSym σ w₁ : ℤ)) : ℂ)
                        * (β (e * z₁) * (((DirichletSym σ z₁ : ℤ)) : ℂ)) * JKSym (w₁ * z₁)) := by
                rw [hjk, hds, heps]
                push_cast
                ring_nf
              rw [show (e * w₁) * (e * z₁) = σ * (w₁ * z₁) from hprod, hL]
              rw [show (∑' k : ℤ, ĉ k * (kGam Rw e σ α k w₁ * kDel Rz e σ β k z₁
                    * JKSym (w₁ * z₁)))
                  = (∑' k : ℤ, ĉ k * ((w₁.toComplex / (((‖w₁.toComplex‖ : ℝ)) : ℂ)) ^ k
                      * (z₁.toComplex / (((‖z₁.toComplex‖ : ℝ)) : ℂ)) ^ k))
                    * (α (e * w₁) * (((DirichletSym σ w₁ : ℤ)) : ℂ)
                        * (β (e * z₁) * (((DirichletSym σ z₁ : ℤ)) : ℂ)) * JKSym (w₁ * z₁)) from by
                rw [← tsum_mul_right]
                apply tsum_congr; intro k
                simp only [kGam, kDel, kA, kB, h1, h2, if_true]
                ring]
              ring_nf
        · have hzero : (∑' k : ℤ, ĉ k * (kGam Rw e σ α k w₁ * kDel Rz e σ β k z₁
              * JKSym (w₁ * z₁))) = 0 := by
            rw [show (∑' k : ℤ, ĉ k * (kGam Rw e σ α k w₁ * kDel Rz e σ β k z₁
                  * JKSym (w₁ * z₁))) = ∑' _ : ℤ, (0 : ℂ) from
              tsum_congr (fun k => by
                simp only [kGam, kA, kDel, kB, h2, if_false, mul_zero, zero_mul])]
            exact tsum_zero
          rw [hzero]; rw [if_neg h2]; ring
      · have hzero : (∑' k : ℤ, ĉ k * (kGam Rw e σ α k w₁ * kDel Rz e σ β k z₁
            * JKSym (w₁ * z₁))) = 0 := by
          rw [show (∑' k : ℤ, ĉ k * (kGam Rw e σ α k w₁ * kDel Rz e σ β k z₁
                * JKSym (w₁ * z₁))) = ∑' _ : ℤ, (0 : ℂ) from
            tsum_congr (fun k => by
              simp only [kGam, kA, kDel, kB, h1, if_false, mul_zero, zero_mul])]
          exact tsum_zero
        rw [hzero]; rw [if_neg h1]; ring
    have hsumm1 : ∀ (w₁ : GaussianInt) (z₁ : GaussianInt),
        Summable (fun k : ℤ => ĉ k * (kGam Rw e σ α k w₁ * kDel Rz e σ β k z₁
            * JKSym (w₁ * z₁))) := by
      intro w₁ z₁
      refine Summable.of_norm_bounded hc_summ (fun k => ?_)
      rw [norm_mul]
      calc ‖ĉ k‖ * ‖kGam Rw e σ α k w₁ * kDel Rz e σ β k z₁ * JKSym (w₁ * z₁)‖
          ≤ ‖ĉ k‖ * 1 := mul_le_mul_of_nonneg_left (norm_triple_le hα hβ k w₁ z₁) (norm_nonneg _)
        _ = ‖ĉ k‖ := mul_one _
    have hsumm2 : ∀ w₁ : GaussianInt, Summable (fun k : ℤ =>
        ∑ z₁ ∈ Work.FIPlan.gBox NC, ĉ k * (kGam Rw e σ α k w₁ * kDel Rz e σ β k z₁
          * JKSym (w₁ * z₁))) := by
      intro w₁
      have hbd : ∀ k : ℤ,
          ‖∑ z₁ ∈ Work.FIPlan.gBox NC, ĉ k * (kGam Rw e σ α k w₁ * kDel Rz e σ β k z₁
              * JKSym (w₁ * z₁))‖ ≤ ((Work.FIPlan.gBox NC).card : ℝ) * ‖ĉ k‖ := by
        intro k
        calc ‖∑ z₁ ∈ Work.FIPlan.gBox NC, ĉ k * (kGam Rw e σ α k w₁ * kDel Rz e σ β k z₁
                * JKSym (w₁ * z₁))‖
            ≤ ∑ z₁ ∈ Work.FIPlan.gBox NC,
                ‖ĉ k * (kGam Rw e σ α k w₁ * kDel Rz e σ β k z₁ * JKSym (w₁ * z₁))‖ :=
              norm_sum_le _ _
          _ ≤ ∑ z₁ ∈ Work.FIPlan.gBox NC, ‖ĉ k‖ := by
              apply Finset.sum_le_sum; intro z₁ _
              rw [norm_mul]
              calc ‖ĉ k‖ * ‖kGam Rw e σ α k w₁ * kDel Rz e σ β k z₁ * JKSym (w₁ * z₁)‖
                  ≤ ‖ĉ k‖ * 1 :=
                    mul_le_mul_of_nonneg_left (norm_triple_le hα hβ k w₁ z₁) (norm_nonneg _)
                _ = ‖ĉ k‖ := mul_one _
          _ = ((Work.FIPlan.gBox NC).card : ℝ) * ‖ĉ k‖ := by
              rw [Finset.sum_const, nsmul_eq_mul]
      refine Summable.of_norm_bounded (g := fun k : ℤ => ((Work.FIPlan.gBox NC).card : ℝ) * ‖ĉ k‖)
        (hc_summ.mul_left _) (fun k => ?_)
      exact hbd k
    set K : ℤ → ℂ := fun k => KBilin MC NC (kGam Rw e σ α k) (kDel Rz e σ β k) with hKdef
    have hstep : (∑ w ∈ (Work.FIPlan.gBox Rw).filter (fun w => e ∣ w),
          ∑ z ∈ (Work.FIPlan.gBox Rz).filter (fun z => e ∣ z),
            α w * β z * JKSym (w * z))
        = (1 / 2 : ℂ) * JKSym σ * (HilbertInf σ.re σ.im : ℂ) * (∑' k : ℤ, ĉ k * K k) := by
      rw [hre]
      rw [Finset.sum_congr rfl (fun w₁ _ => Finset.sum_congr rfl (fun z₁ _ => hpt w₁ z₁))]
      rw [show (∑ w₁ ∈ Work.FIPlan.gBox MC, ∑ z₁ ∈ Work.FIPlan.gBox NC,
            (1 / 2 : ℂ) * JKSym σ * (HilbertInf σ.re σ.im : ℂ)
              * (∑' k : ℤ, ĉ k * (kGam Rw e σ α k w₁ * kDel Rz e σ β k z₁ * JKSym (w₁ * z₁))))
          = (1 / 2 : ℂ) * JKSym σ * (HilbertInf σ.re σ.im : ℂ)
            * (∑ w₁ ∈ Work.FIPlan.gBox MC, ∑ z₁ ∈ Work.FIPlan.gBox NC,
                (∑' k : ℤ, ĉ k * (kGam Rw e σ α k w₁ * kDel Rz e σ β k z₁ * JKSym (w₁ * z₁))))
          from by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro w₁ _
        rw [Finset.mul_sum]]
      congr 1
      rw [show (∑ w₁ ∈ Work.FIPlan.gBox MC, ∑ z₁ ∈ Work.FIPlan.gBox NC,
              (∑' k : ℤ, ĉ k * (kGam Rw e σ α k w₁ * kDel Rz e σ β k z₁ * JKSym (w₁ * z₁))))
            = ∑ w₁ ∈ Work.FIPlan.gBox MC, ∑' k : ℤ, ∑ z₁ ∈ Work.FIPlan.gBox NC,
                ĉ k * (kGam Rw e σ α k w₁ * kDel Rz e σ β k z₁ * JKSym (w₁ * z₁)) from by
        apply Finset.sum_congr rfl; intro w₁ _
        exact (Summable.tsum_finsetSum (s := Work.FIPlan.gBox NC)
          (f := fun z₁ k => ĉ k * (kGam Rw e σ α k w₁ * kDel Rz e σ β k z₁ * JKSym (w₁ * z₁)))
          (fun z₁ _ => hsumm1 w₁ z₁)).symm]
      rw [show (∑ w₁ ∈ Work.FIPlan.gBox MC, ∑' k : ℤ, ∑ z₁ ∈ Work.FIPlan.gBox NC,
                ĉ k * (kGam Rw e σ α k w₁ * kDel Rz e σ β k z₁ * JKSym (w₁ * z₁)))
            = ∑' k : ℤ, ∑ w₁ ∈ Work.FIPlan.gBox MC, ∑ z₁ ∈ Work.FIPlan.gBox NC,
                ĉ k * (kGam Rw e σ α k w₁ * kDel Rz e σ β k z₁ * JKSym (w₁ * z₁)) from
          (Summable.tsum_finsetSum (s := Work.FIPlan.gBox MC)
            (f := fun w₁ k => ∑ z₁ ∈ Work.FIPlan.gBox NC,
              ĉ k * (kGam Rw e σ α k w₁ * kDel Rz e σ β k z₁ * JKSym (w₁ * z₁)))
            (fun w₁ _ => hsumm2 w₁)).symm]
      apply tsum_congr; intro k
      rw [show (∑ w₁ ∈ Work.FIPlan.gBox MC, ∑ z₁ ∈ Work.FIPlan.gBox NC,
            ĉ k * (kGam Rw e σ α k w₁ * kDel Rz e σ β k z₁ * JKSym (w₁ * z₁)))
          = ĉ k * (∑ w₁ ∈ Work.FIPlan.gBox MC, ∑ z₁ ∈ Work.FIPlan.gBox NC,
            kGam Rw e σ α k w₁ * kDel Rz e σ β k z₁ * JKSym (w₁ * z₁)) from by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro w₁ _
        rw [Finset.mul_sum]]
      rw [hKdef]; rfl
    have hKb : ∀ k : ℤ, ‖K k‖ ≤ Bfun C A (M / (Work.FIPlan.gnorm e : ℝ))
        (N / (Work.FIPlan.gnorm e : ℝ)) := by
      intro k
      have hbound : ‖KBilin MC NC (kGam Rw e σ α k) (kDel Rz e σ β k)‖
          ≤ Bfun C A (M / (Work.FIPlan.gnorm e : ℝ)) (N / (Work.FIPlan.gnorm e : ℝ)) :=
        hK _ _ MC NC _ _ hMg hNg (norm_kGam_le hα k) (norm_kDel_le hβ k)
          (fun w₁ hw => supp_kGam heP hgann hsα hw)
          (fun z₁ hz => supp_kDel heP hgann hsβ hz)
      rw [hKdef]; exact hbound
    have htdsum : ‖∑' k : ℤ, ĉ k * K k‖
        ≤ (∑' k : ℤ, ‖ĉ k‖) * Bfun C A (M / (Work.FIPlan.gnorm e : ℝ))
            (N / (Work.FIPlan.gnorm e : ℝ)) := by
      have hf_summ : Summable fun k : ℤ => ‖ĉ k‖ * ‖K k‖ :=
        Summable.of_nonneg_of_le (fun k => by positivity)
          (fun k => mul_le_mul_of_nonneg_left (hKb k) (norm_nonneg _)) (hc_summ.mul_right _)
      calc ‖∑' k : ℤ, ĉ k * K k‖ ≤ ∑' k : ℤ, ‖ĉ k * K k‖ :=
            norm_tsum_le_tsum_norm (by simpa only [norm_mul] using hf_summ)
        _ = ∑' k : ℤ, ‖ĉ k‖ * ‖K k‖ := by
            apply tsum_congr; intro k; rw [norm_mul]
        _ ≤ ∑' k : ℤ, ‖ĉ k‖ * Bfun C A (M / (Work.FIPlan.gnorm e : ℝ))
              (N / (Work.FIPlan.gnorm e : ℝ)) :=
            Summable.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left (hKb k) (norm_nonneg _))
              hf_summ (hc_summ.mul_right _)
        _ = (∑' k : ℤ, ‖ĉ k‖) * Bfun C A (M / (Work.FIPlan.gnorm e : ℝ))
              (N / (Work.FIPlan.gnorm e : ℝ)) := tsum_mul_right
    have hBscale := hBfun e heP M N hM hN
    have hpow_nn : (0:ℝ) ≤ ((Work.FIPlan.gnorm e : ℝ)) ^ (-(23 / 12 : ℝ)) := by positivity
    have hBnn : (0:ℝ) ≤ Bfun C A M N := by
      rw [Bfun]
      have h4' : (0:ℝ) < M + N := by linarith
      have h5' : (0:ℝ) < M * N := by nlinarith
      have h6' : (0:ℝ) < Real.log (M * N + 2) := Real.log_pos (by nlinarith)
      exact le_of_lt (mul_pos (mul_pos (mul_pos hC (Real.rpow_pos_of_pos h4' _))
        (Real.rpow_pos_of_pos h5' _)) (Real.rpow_pos_of_pos h6' A))
    have h4 : (0:ℝ) ≤ ((Work.FIPlan.gnorm e : ℝ)) ^ (-(23 / 12 : ℝ)) * Bfun C A M N :=
      mul_nonneg hpow_nn hBnn
    calc ‖∑ w ∈ (Work.FIPlan.gBox Rw).filter (fun w => e ∣ w),
            ∑ z ∈ (Work.FIPlan.gBox Rz).filter (fun z => e ∣ z), α w * β z * JKSym (w * z)‖
        = ‖(1 / 2 : ℂ) * JKSym σ * (HilbertInf σ.re σ.im : ℂ) * (∑' k : ℤ, ĉ k * K k)‖ := by
          rw [hstep]
      _ ≤ (1 / 2) * ‖∑' k : ℤ, ĉ k * K k‖ := by
          rw [norm_mul, norm_mul, norm_mul, norm_two_inv, norm_hilb, mul_one]
          have h0 : (0:ℝ) ≤ ‖∑' k : ℤ, ĉ k * K k‖ := norm_nonneg _
          nlinarith [norm_JKSym_le_one σ, h0]
      _ ≤ (1 / 2) * ((∑' k : ℤ, ‖ĉ k‖) * Bfun C A (M / (Work.FIPlan.gnorm e : ℝ))
            (N / (Work.FIPlan.gnorm e : ℝ))) := by linarith [htdsum]
      _ ≤ (1 / 2) * ((C1 * (Real.log (2 * ((RR M N : ℕ) : ℝ))) ^ 4)
            * (((Work.FIPlan.gnorm e : ℝ)) ^ (-(23 / 12 : ℝ)) * Bfun C A M N)) := by
          have h1 : (0:ℝ) ≤ ∑' k : ℤ, ‖ĉ k‖ := tsum_nonneg (fun k => norm_nonneg _)
          have h6 : (0:ℝ) ≤ Bfun C A (M / (Work.FIPlan.gnorm e : ℝ))
              (N / (Work.FIPlan.gnorm e : ℝ)) := by
            rw [Bfun]
            have hMg' : (0:ℝ) < M / (Work.FIPlan.gnorm e : ℝ) := by linarith
            have hNg' : (0:ℝ) < N / (Work.FIPlan.gnorm e : ℝ) := by linarith
            have h1' : (0:ℝ) < M / (Work.FIPlan.gnorm e : ℝ) + N / (Work.FIPlan.gnorm e : ℝ) := by linarith
            have h2' : (0:ℝ) < (M / (Work.FIPlan.gnorm e : ℝ)) * (N / (Work.FIPlan.gnorm e : ℝ)) :=
              mul_pos hMg' hNg'
            have h3' : (0:ℝ) < Real.log ((M / (Work.FIPlan.gnorm e : ℝ))
                * (N / (Work.FIPlan.gnorm e : ℝ)) + 2) := Real.log_pos (by linarith)
            exact le_of_lt (mul_pos (mul_pos (mul_pos hC (Real.rpow_pos_of_pos h1' _))
              (Real.rpow_pos_of_pos h2' _)) (Real.rpow_pos_of_pos h3' A))
          have h7 : (0:ℝ) ≤ C1 * (Real.log (2 * ((RR M N : ℕ) : ℝ))) ^ 4 := by positivity
          nlinarith [hc_tsum, h1, hBscale, h4, h6, h7]
      _ = (C1 / 2) * (Real.log (2 * ((RR M N : ℕ) : ℝ))) ^ 4
            * ((Work.FIPlan.gnorm e : ℝ)) ^ (-(23 / 12 : ℝ)) * Bfun C A M N := by ring
  · have hzero : (∑ w ∈ (Work.FIPlan.gBox Rw).filter (fun w => e ∣ w),
        ∑ z ∈ (Work.FIPlan.gBox Rz).filter (fun z => e ∣ z), α w * β z * JKSym (w * z)) = 0 := by
      refine Finset.sum_eq_zero (fun w hw => ?_)
      rw [Finset.mem_filter] at hw
      refine Finset.sum_eq_zero (fun z hz => ?_)
      rw [Finset.mem_filter] at hz
      by_cases hαw : α w = 0
      · rw [hαw]; ring
      · by_cases hβz : β z = 0
        · rw [hβz]; ring
        · exfalso
          have hα0 : α 0 = 0 := by
            by_contra hh
            have h1' := (hsα 0 hh).1.1
            rw [show (0 : GaussianInt).re = 0 from rfl] at h1'
            obtain ⟨k, hk⟩ := h1'; omega
          have hβ0 : β 0 = 0 := by
            by_contra hh
            have h1' := (hsβ 0 hh).1.1
            rw [show (0 : GaussianInt).re = 0 from rfl] at h1'
            obtain ⟨k, hk⟩ := h1'; omega
          have hwne : w ≠ 0 := fun h => hαw (by rw [h]; exact hα0)
          have hzne : z ≠ 0 := fun h => hβz (by rw [h]; exact hβ0)
          have hwdvd : Work.FIPlan.gnorm e ∣ Work.FIPlan.gnorm w :=
            Work.FIArea4.gnorm_dvd hw.2
          have hzdvd : Work.FIPlan.gnorm e ∣ Work.FIPlan.gnorm z :=
            Work.FIArea4.gnorm_dvd hz.2
          have hwge : (Work.FIPlan.gnorm e : ℝ) ≤ (Work.FIPlan.gnorm w : ℝ) := by
            exact_mod_cast Nat.le_of_dvd (Work.FIArea4.gnorm_pos hwne) hwdvd
          have hzge : (Work.FIPlan.gnorm e : ℝ) ≤ (Work.FIPlan.gnorm z : ℝ) := by
            exact_mod_cast Nat.le_of_dvd (Work.FIArea4.gnorm_pos hzne) hzdvd
          have hwle := (hsα w hαw).2.2
          have hzle := (hsβ z hβz).2
          rcases (not_and_or.mp hsz) with h | h
          · linarith
          · linarith
    rw [hzero, norm_zero]
    have h1 : (0:ℝ) ≤ (Real.log (2 * ((RR M N : ℕ) : ℝ))) ^ 4 := by positivity
    have h2 : (0:ℝ) ≤ ((Work.FIPlan.gnorm e : ℝ)) ^ (-(23 / 12 : ℝ)) := by positivity
    have h3 : (0:ℝ) ≤ Bfun C A M N := by
      rw [Bfun]
      have h4 : (0:ℝ) < M + N := by linarith
      have h5 : (0:ℝ) < M * N := by nlinarith
      have h6 : (0:ℝ) < Real.log (M * N + 2) := Real.log_pos (by nlinarith)
      positivity
    have h7 : (0:ℝ) < C1 / 2 := by linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg h7.le h1) h2) h3

theorem kstarBound_of_prop214 (h : Prop214) : KStarBound := by
  obtain ⟨C, A, hC, hA, hK⟩ := h
  obtain ⟨C1, hC1, hmult⟩ := Work.FIArea7.P231.multEpsExpansion
  obtain ⟨S1, hS1nn, hS1⟩ := Work.FIArea7.P231M.sumGnormPowLe (23 / 12) (by norm_num)
  have hBf : ∀ (e : GaussianInt), Work.FIPlan.IsPrimary e → ∀ (M N : ℝ), 1 ≤ M → 1 ≤ N →
      Bfun C A (M / (Work.FIPlan.gnorm e : ℝ)) (N / (Work.FIPlan.gnorm e : ℝ))
        ≤ ((Work.FIPlan.gnorm e : ℝ)) ^ (-(23 / 12 : ℝ)) * Bfun C A M N := by
    intro e heP M N hM hN
    exact Bfun_scaling hC hA hM hN (by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Work.FIArea4.gnorm_ne_zero (Work.FIArea4.isPrimary_ne_zero heP)))
  have hlog4 : (0 : ℝ) < 1 + Real.log 4 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 4); linarith
  refine ⟨C + (C1 / 2) * (1 + Real.log 4) ^ 4 * S1 * C, A + 4, ?_, ?_, ?_⟩
  · have h2 : (0 : ℝ) < C1 / 2 := by linarith
    have h3 : (0 : ℝ) < 1 + Real.log 4 := hlog4
    positivity
  · linarith
  · intro M N Rw Rz α β hM hN hα hβ hsα hsβ
    classical
    set E : Finset GaussianInt :=
      (Work.FIPlan.gBox (((Nat.ceil M : ℕ) : ℤ))).filter (Work.FIPlan.IsPrimary) with hEdef
    have hEprim : ∀ e ∈ E, Work.FIPlan.IsPrimary e := fun e he => (Finset.mem_filter.mp he).2
    have hpoint : ∀ w z : GaussianInt,
        (if Work.FIPlan.GaussCoprime w z then α w * β z * JKSym (w * z) else 0)
          = (∑ e ∈ E, ((UniqueFactorizationMonoid.moebius e : ℤ) : ℂ)
              * (if e ∣ w ∧ e ∣ z then (1 : ℂ) else 0)) * (α w * β z * JKSym (w * z)) := by
      intro w z
      by_cases h0 : α w * β z = 0
      · simp [h0]
      · have hαw : α w ≠ 0 := fun hh => h0 (by rw [hh, zero_mul])
        have hβz : β z ≠ 0 := fun hh => h0 (by rw [hh, mul_zero])
        have hwP := (hsα w hαw).1
        have hzP := (hsβ z hβz).1
        have hEM : ∀ e : GaussianInt, e ∣ w → e ∣ z → Work.FIPlan.IsPrimary e → e ∈ E := by
          intro e he1 he2 hep
          rw [hEdef, Finset.mem_filter]
          refine ⟨?_, hep⟩
          have hle : Work.FIPlan.gnorm e ≤ Nat.ceil M := by
            have h1 : Work.FIPlan.gnorm e ≤ Work.FIPlan.gnorm w :=
              Nat.le_of_dvd (Work.FIArea4.gnorm_pos (Work.FIArea4.isPrimary_ne_zero hwP))
                (Work.FIArea4.gnorm_dvd he1)
            have h2 : Work.FIPlan.gnorm w ≤ Nat.ceil M := by
              have h3 : (Work.FIPlan.gnorm w : ℝ) ≤ M := (hsα w hαw).2.2
              have h4 : (M : ℝ) ≤ (Nat.ceil M : ℕ) := Nat.le_ceil M
              exact_mod_cast le_trans h3 h4
            exact le_trans h1 h2
          exact mem_gBox_of_natAbs_le (by positivity) (le_trans (natAbs_re_le_gnorm e) hle)
            (le_trans (natAbs_im_le_gnorm e) hle)
        rw [show (if Work.FIPlan.GaussCoprime w z then α w * β z * JKSym (w * z) else 0)
              = (if Work.FIPlan.GaussCoprime w z then (1 : ℂ) else 0)
                * (α w * β z * JKSym (w * z)) from by
            by_cases hc : Work.FIPlan.GaussCoprime w z <;> simp [hc],
          moebius_indicator (Work.FIArea4.isPrimary_odd_gnorm hwP)
            (Work.FIArea4.isPrimary_odd_gnorm hzP) hEM hEprim]
    let U : GaussianInt → ℂ := fun e =>
      ∑ w ∈ (Work.FIPlan.gBox Rw).filter (fun w => e ∣ w),
        ∑ z ∈ (Work.FIPlan.gBox Rz).filter (fun z => e ∣ z), α w * β z * JKSym (w * z)
    have hBfnn : (0 : ℝ) ≤ Bfun C A M N := by
      rw [Bfun]
      have h1 : (0 : ℝ) < M + N := by linarith
      have h2 : (0 : ℝ) < M * N := by nlinarith
      have h3 : (0 : ℝ) < Real.log (M * N + 2) := Real.log_pos (by nlinarith)
      exact le_of_lt (mul_pos (mul_pos (mul_pos hC (Real.rpow_pos_of_pos h1 _))
        (Real.rpow_pos_of_pos h2 _)) (Real.rpow_pos_of_pos h3 A))
    have hred : KBilinStar Rw Rz α β
        = ∑ e ∈ E, ((UniqueFactorizationMonoid.moebius e : ℤ) : ℂ) * U e := by
      rw [KBilinStar]
      rw [show (∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz,
              (if Work.FIPlan.GaussCoprime w z then α w * β z * JKSym (w * z) else 0))
          = ∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz, ∑ e ∈ E,
              ((UniqueFactorizationMonoid.moebius e : ℤ) : ℂ)
                * ((if e ∣ w ∧ e ∣ z then (1 : ℂ) else 0) * (α w * β z * JKSym (w * z))) from by
        apply Finset.sum_congr rfl; intro w _
        apply Finset.sum_congr rfl; intro z _
        rw [hpoint w z, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro e _
        ring]
      rw [show (∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz, ∑ e ∈ E,
              ((UniqueFactorizationMonoid.moebius e : ℤ) : ℂ)
                * ((if e ∣ w ∧ e ∣ z then (1 : ℂ) else 0) * (α w * β z * JKSym (w * z))))
          = ∑ w ∈ Work.FIPlan.gBox Rw, ∑ e ∈ E, ∑ z ∈ Work.FIPlan.gBox Rz,
              ((UniqueFactorizationMonoid.moebius e : ℤ) : ℂ)
                * ((if e ∣ w ∧ e ∣ z then (1 : ℂ) else 0) * (α w * β z * JKSym (w * z))) from by
        apply Finset.sum_congr rfl; intro w _
        exact Finset.sum_comm]
      rw [show (∑ w ∈ Work.FIPlan.gBox Rw, ∑ e ∈ E, ∑ z ∈ Work.FIPlan.gBox Rz,
              ((UniqueFactorizationMonoid.moebius e : ℤ) : ℂ)
                * ((if e ∣ w ∧ e ∣ z then (1 : ℂ) else 0) * (α w * β z * JKSym (w * z))))
          = ∑ e ∈ E, ∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz,
              ((UniqueFactorizationMonoid.moebius e : ℤ) : ℂ)
                * ((if e ∣ w ∧ e ∣ z then (1 : ℂ) else 0) * (α w * β z * JKSym (w * z))) from
        Finset.sum_comm]
      apply Finset.sum_congr rfl; intro e _
      dsimp only [U]
      have key : (∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz,
              ((UniqueFactorizationMonoid.moebius e : ℤ) : ℂ)
                * ((if e ∣ w ∧ e ∣ z then (1 : ℂ) else 0) * (α w * β z * JKSym (w * z))))
          = ((UniqueFactorizationMonoid.moebius e : ℤ) : ℂ)
            * (∑ w ∈ (Work.FIPlan.gBox Rw).filter (fun w => e ∣ w),
               ∑ z ∈ (Work.FIPlan.gBox Rz).filter (fun z => e ∣ z),
                 α w * β z * JKSym (w * z)) := by
        conv_rhs => rw [Finset.mul_sum]
        conv_rhs => rw [Finset.sum_filter]
        apply Finset.sum_congr rfl; intro w _
        by_cases hw : e ∣ w
        · rw [if_pos hw]
          conv_rhs => rw [Finset.mul_sum]
          conv_rhs => rw [Finset.sum_filter]
          apply Finset.sum_congr rfl; intro z _
          by_cases hz : e ∣ z <;> simp [hw, hz]
        · rw [if_neg hw]
          apply Finset.sum_eq_zero
          intro z _
          by_cases hz : e ∣ z <;> simp [hw, hz]
      rw [key]
    -- bounds for the individual terms
    have hU1 : ‖U 1‖ ≤ Bfun C A M N := by
      have h1 : U 1 = KBilin Rw Rz α β := by
        dsimp only [U]
        rw [Finset.filter_true_of_mem (fun x _ => one_dvd x),
          Finset.filter_true_of_mem (fun x _ => one_dvd x)]
        rfl
      rw [h1]
      exact hK M N Rw Rz α β hM hN hα hβ hsα hsβ
    have hUp : ∀ e ∈ E, IsCoprime e.re e.im → e ≠ 1 → ‖U e‖
        ≤ (C1 / 2) * (Real.log (2 * ((RR M N : ℕ) : ℝ))) ^ 4
            * ((Work.FIPlan.gnorm e : ℝ)) ^ (-(23 / 12 : ℝ)) * Bfun C A M N := by
      intro e heE hec he1
      dsimp only [U]
      exact per_e_bound hC hC1 hK hmult hBf hM hN hα hβ hsα hsβ e (hEprim e heE) hec he1
    have hZero : ∀ e ∈ E, ¬ IsCoprime e.re e.im → U e = 0 := by
      intro e heE hnp
      have heP : Work.FIPlan.IsPrimary e := hEprim e heE
      dsimp only [U]
      refine Finset.sum_eq_zero (fun w hw => ?_)
      rw [Finset.mem_filter] at hw
      obtain ⟨w₁, rfl⟩ := hw.2
      refine Finset.sum_eq_zero (fun z hz => ?_)
      by_cases h0 : α (e * w₁) * β z = 0
      · rw [h0, zero_mul]
      · have hαw : α (e * w₁) ≠ 0 := fun hh => h0 (by rw [hh, zero_mul])
        have hβz : β z ≠ 0 := fun hh => h0 (by rw [hh, mul_zero])
        have hwP₁ : Work.FIPlan.IsPrimary w₁ :=
          isPrimary_of_mul heP (hsα (e * w₁) hαw).1
        have hzP : Work.FIPlan.IsPrimary z := (hsβ z hβz).1
        have hjk0 : JKSym ((e * w₁) * z) = 0 := by
          rw [show (e * w₁) * z = (w₁ * z) * e by ring]
          exact JKSym_mul_eq_zero_of_not_isCoprime_primary
            (Work.FIArea4.isPrimary_mul hwP₁ hzP) heP hnp
        rw [hjk0, mul_zero]
    have h1E : (1 : GaussianInt) ∈ E := by
      rw [hEdef, Finset.mem_filter]
      refine ⟨?_, Work.FIArea4.isPrimary_one⟩
      have hM1 : (1 : ℤ) ≤ ((Nat.ceil M : ℕ) : ℤ) := by
        have h1 : (1 : ℝ) ≤ M := hM
        have h2 : (M : ℝ) ≤ (Nat.ceil M : ℕ) := Nat.le_ceil M
        have h3 : (1 : ℝ) ≤ (Nat.ceil M : ℕ) := le_trans h1 h2
        exact_mod_cast h3
      rw [Work.FIArea4.mem_gBox]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [show (1 : GaussianInt).re = (1 : ℤ) from rfl]; linarith
      · rw [show (1 : GaussianInt).re = (1 : ℤ) from rfl]; linarith
      · rw [show (1 : GaussianInt).im = (0 : ℤ) from rfl]; linarith
      · rw [show (1 : GaussianInt).im = (0 : ℤ) from rfl]; linarith
    have hp1 : IsCoprime (1 : GaussianInt).re (1 : GaussianInt).im := by
      rw [show (1 : GaussianInt).re = (1 : ℤ) from rfl, show (1 : GaussianInt).im = (0 : ℤ) from rfl]
      exact isCoprime_one_left
    -- the sum bound
    have hsplit : E.filter (fun e => IsCoprime e.re e.im)
        = insert (1 : GaussianInt) (E.filter (fun e => IsCoprime e.re e.im ∧ e ≠ 1)) := by
      apply Finset.ext
      intro e
      simp only [Finset.mem_insert, Finset.mem_filter]
      constructor
      · rintro ⟨heE, hec⟩
        by_cases h1 : e = 1
        · exact Or.inl h1
        · exact Or.inr ⟨heE, hec, h1⟩
      · rintro (rfl | ⟨heE, hec, -⟩)
        · exact ⟨h1E, hp1⟩
        · exact ⟨heE, hec⟩
    have hnotin : (1 : GaussianInt) ∉ E.filter (fun e => IsCoprime e.re e.im ∧ e ≠ 1) := by
      intro h1
      exact (Finset.mem_filter.mp h1).2.2 rfl
    have hsumEp : (∑ e ∈ E.filter (fun e => IsCoprime e.re e.im ∧ e ≠ 1), ‖U e‖)
        ≤ (C1 / 2) * (Real.log (2 * ((RR M N : ℕ) : ℝ))) ^ 4 * S1 * Bfun C A M N := by
      have hpt : ∀ e ∈ E.filter (fun e => IsCoprime e.re e.im ∧ e ≠ 1), ‖U e‖
          ≤ (C1 / 2) * (Real.log (2 * ((RR M N : ℕ) : ℝ))) ^ 4
              * ((Work.FIPlan.gnorm e : ℝ)) ^ (-(23 / 12 : ℝ)) * Bfun C A M N := by
        intro e he
        rw [Finset.mem_filter] at he
        exact hUp e he.1 he.2.1 he.2.2
      calc (∑ e ∈ E.filter (fun e => IsCoprime e.re e.im ∧ e ≠ 1), ‖U e‖)
          ≤ ∑ e ∈ E.filter (fun e => IsCoprime e.re e.im ∧ e ≠ 1),
              (C1 / 2) * (Real.log (2 * ((RR M N : ℕ) : ℝ))) ^ 4
                * ((Work.FIPlan.gnorm e : ℝ)) ^ (-(23 / 12 : ℝ)) * Bfun C A M N :=
            Finset.sum_le_sum hpt
        _ = ((C1 / 2) * (Real.log (2 * ((RR M N : ℕ) : ℝ))) ^ 4 * Bfun C A M N)
              * (∑ e ∈ E.filter (fun e => IsCoprime e.re e.im ∧ e ≠ 1),
                  ((Work.FIPlan.gnorm e : ℝ)) ^ (-(23 / 12 : ℝ))) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro e _; ring
        _ ≤ ((C1 / 2) * (Real.log (2 * ((RR M N : ℕ) : ℝ))) ^ 4 * Bfun C A M N) * S1 :=
            mul_le_mul_of_nonneg_left (hS1 _)
              (mul_nonneg (mul_nonneg (by linarith) (by positivity)) hBfnn)
        _ = (C1 / 2) * (Real.log (2 * ((RR M N : ℕ) : ℝ))) ^ 4 * S1 * Bfun C A M N := by ring
    have hsumEnp : (∑ e ∈ E.filter (fun e => ¬ IsCoprime e.re e.im), ‖U e‖) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      rw [Finset.mem_filter] at he
      rw [hZero e he.1 he.2, norm_zero]
    rw [hred]
    calc ‖∑ e ∈ E, ((UniqueFactorizationMonoid.moebius e : ℤ) : ℂ) * U e‖
        ≤ ∑ e ∈ E, ‖((UniqueFactorizationMonoid.moebius e : ℤ) : ℂ) * U e‖ :=
          norm_sum_le _ _
      _ ≤ ∑ e ∈ E, ‖U e‖ := by
          apply Finset.sum_le_sum; intro e _
          rw [norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) (norm_moebius_le_one e)
      _ = (∑ e ∈ E.filter (fun e => IsCoprime e.re e.im), ‖U e‖)
            + (∑ e ∈ E.filter (fun e => ¬ IsCoprime e.re e.im), ‖U e‖) :=
          (Finset.sum_filter_add_sum_filter_not E (fun e => IsCoprime e.re e.im)
            (fun e => ‖U e‖)).symm
      _ = (‖U 1‖ + ∑ e ∈ E.filter (fun e => IsCoprime e.re e.im ∧ e ≠ 1), ‖U e‖) + 0 := by
          rw [hsplit, Finset.sum_insert hnotin, hsumEnp]
      _ ≤ (Bfun C A M N + (C1 / 2) * (Real.log (2 * ((RR M N : ℕ) : ℝ))) ^ 4 * S1
              * Bfun C A M N) + 0 := by
          have := hU1; have := hsumEp; linarith
      _ ≤ (C + (C1 / 2) * (1 + Real.log 4) ^ 4 * S1 * C)
            * (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12)
            * (Real.log (M * N + 2)) ^ (A + 4) := by
          have hfa := Work.FIArea7.P231M.finalArith hC hA hC1 hS1nn hM hN
          simp only [Bfun, RR]
          linarith [hfa]


end

end Work.FIArea7.P231

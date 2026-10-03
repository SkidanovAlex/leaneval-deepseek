/-
# FI §15: the joint polar-box lattice count (the closing estimate of Proposition 15.1)

The statement `S15_polar_joint_count` bounds the number of Gaussian integers in the polar box
(5.14) that are divisible by `L` in their real part and by `d` in norm:

  `#{z ∈ polarBox : L ∣ Re z, d ∣ |z|²} ≤ C·(A/d + 1)·(A/L + 1)·2^{ω(d)}·d₂(d)`,
  `A = 10θ√N` (twice the radius `5θ√N` of the disc containing the polar box).

The proof fibres the box over `Re z`:

* the polar box lies in the disc of radius `ρ = 5θ√N` centred at the mid-angle point `c` of the
  sector (5.14), so the real parts `x` lie in an interval of length `A = 2ρ` and, thanks to
  `L ∣ Re z`, there are at most `A/L + 1` of them (`card_le_of_dvd_mem_interval`);

* for a fixed `x = Re z` the imaginary parts `y` lie in an interval of length `2ρ = A`, and the
  norm condition reads `x² + y² ≡ 0 (mod d)`.  The residues `α = y mod d` all lie in the set
  `{α : ZMod d | α² + x² = 0}`, which has at most `2^{ω(d)}·gcd(x, d₂(d)) ≤ 2^{ω(d)}·d₂(d)`
  elements (Commons `sq_sum_sq_root_count_le_two_pow_omega`); each residue class contributes at
  most `2(ρ+1)/d + 1` points (`card_le_of_pairwise_dvd_interval`).
-/
import Mathlib
import Submission.Work.FIArea4.S15_energy_defs
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_sum_sq_root_count_le_two_pow_omega
import Submission.Commons.NumberTheory.Divisors.sum_tau_pow_div_le
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound_ge_three
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
import Submission.Commons.NumberTheory.Divisors.small_divisor_tau_le
import Submission.Commons.NumberTheory.DivisorSum.tau_pow_eight_le_sum_dvd_cube
import Submission.Work.FIArea4.polarBox_card_le
import Submission.Work.FIArea4.S15box
import Submission.Work.FIArea4.S15_hard_defs
import Submission.Work.FIArea4.S15_ap_polar_count

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Elementary `ZMod` and norm facts -/

/-- `(n.natAbs)² = n²` in `ZMod d`: the two differ only by the sign of `n`. -/
lemma zmod_sq_natAbs (d : ℕ) (n : ℤ) :
    ((n.natAbs : ZMod d)) ^ 2 = ((n : ZMod d)) ^ 2 := by
  rw [Nat.cast_natAbs]
  rcases le_or_gt 0 n with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h]
    push_cast
    ring

/-- `|z|²` of a Gaussian integer, in `ℤ`. -/
lemma gnorm_cast_eq (z : GaussianInt) :
    ((Work.FIPlan.gnorm z : ℕ) : ℤ) = z.re * z.re + z.im * z.im := by
  have hnorm : Zsqrtd.norm z = z.re * z.re + z.im * z.im := by simp [Zsqrtd.norm]
  have hge : (0 : ℤ) ≤ z.norm := by
    rw [hnorm]
    nlinarith [mul_self_nonneg z.re, mul_self_nonneg z.im]
  rw [Work.FIPlan.gnorm, Int.natAbs_of_nonneg hge, hnorm]

/-- `d ∣ |z|²` implies `Im(z)² + (Re z)² = 0` in `ZMod d`. -/
lemma dvd_gnorm_zmod {d : ℕ} {z : GaussianInt} (h : d ∣ Work.FIPlan.gnorm z) :
    ((z.im : ZMod d)) ^ 2 + ((z.re.natAbs : ZMod d)) ^ 2 = 0 := by
  have hcast := gnorm_cast_eq z
  have hdvd : (d : ℤ) ∣ z.re * z.re + z.im * z.im := by
    rw [← hcast]
    exact_mod_cast h
  have hzero : ((z.re * z.re + z.im * z.im : ℤ) : ZMod d) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ d).mpr hdvd
  push_cast at hzero
  have hzero2 : (z.re : ZMod d) ^ 2 + (z.im : ZMod d) ^ 2 = 0 := by
    simpa [pow_two] using hzero
  rw [zmod_sq_natAbs d z.re, add_comm]
  exact hzero2

/-! ## 2. The two counting inputs -/

/-- The number of residues `α mod d` with `α² + b² ≡ 0` is at most `2^{ω(d)}·d₂(d)`. -/
lemma card_sqRoots_le (d b : ℕ) [NeZero d] (hd : 1 ≤ d) :
    ((Finset.univ : Finset (ZMod d)).filter (fun α => α ^ 2 + ((b : ZMod d)) ^ 2 = 0)).card
      ≤ 2 ^ (Nat.primeFactors d).card * S15d2 d := by
  have hd0 : 0 < d := by omega
  have hpos : 0 < S15d2 d := by
    rw [S15d2]
    refine Finset.prod_pos (fun p hp => ?_)
    exact pow_pos (Nat.pos_of_mem_primeFactors hp) _
  have h := Commons.NumberTheory.FriedlanderIwaniec.sq_sum_sq_root_count_le_two_pow_omega
    (d := d) (b := b) hd0
  have hbridge : ({α : ZMod d | α ^ 2 + ((b : ZMod d)) ^ 2 = 0} : Set (ZMod d)).ncard
      = ((Finset.univ : Finset (ZMod d)).filter
          (fun α => α ^ 2 + ((b : ZMod d)) ^ 2 = 0)).card := by
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext α
    simp
  rw [hbridge] at h
  exact le_trans h (Nat.mul_le_mul_left _ (Nat.gcd_le_right b hpos))

/-- **The imaginary-part fibre count.**  `T` is a set of imaginary parts lying in an interval of
length `2A` about `t`, all of whose elements `y` satisfy `y² + x² ≡ 0 (mod d)`.  Then
`#T ≤ 2^{ω(d)}·d₂(d)·(2(A+1)/d + 1)`. -/
lemma card_im_fiber_le (d : ℕ) [NeZero d] (hd : 1 ≤ d) (x : ℤ) (t A : ℝ) (hA : 0 ≤ A)
    (T : Finset ℤ)
    (hint : ∀ y ∈ T, |(y : ℝ) - t| ≤ A)
    (hcong : ∀ y ∈ T, ((y : ZMod d)) ^ 2 + ((x.natAbs : ZMod d)) ^ 2 = 0) :
    (T.card : ℝ)
      ≤ (2 ^ (Nat.primeFactors d).card * (S15d2 d : ℝ)) * (2 * (A + 1) / (d : ℝ) + 1) := by
  classical
  set V : Finset (ZMod d) :=
    Finset.univ.filter (fun α => α ^ 2 + ((x.natAbs : ZMod d)) ^ 2 = 0) with hV
  have hB0 : (0 : ℝ) ≤ 2 * (A + 1) / (d : ℝ) + 1 := by
    have h1 : (0 : ℝ) ≤ 2 * (A + 1) := by linarith
    have h2 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have h3 := div_nonneg h1 h2
    linarith
  have hVle : (V.card : ℝ) ≤ 2 ^ (Nat.primeFactors d).card * (S15d2 d : ℝ) := by
    rw [hV]
    exact_mod_cast card_sqRoots_le d x.natAbs hd
  have hsub : T.image (fun y : ℤ => (y : ZMod d)) ⊆ V := by
    intro α hα
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hα
    rw [hV, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hcong y hy⟩
  have hfib : ∀ α ∈ T.image (fun y : ℤ => (y : ZMod d)),
      (((T.filter (fun y : ℤ => (y : ZMod d) = α)).card : ℕ) : ℝ)
        ≤ 2 * (A + 1) / (d : ℝ) + 1 := by
    intro α _
    apply card_le_of_pairwise_dvd_interval (m := d) hd (t := t) (A := A) hA
    · intro y hy
      exact hint y (Finset.mem_of_mem_filter y hy)
    · intro y hy y' hy'
      have h1 : (y : ZMod d) = α := (Finset.mem_filter.mp hy).2
      have h2 : (y' : ZMod d) = α := (Finset.mem_filter.mp hy').2
      have h3 : ((y - y' : ℤ) : ZMod d) = 0 := by
        rw [Int.cast_sub, h1, h2, sub_self]
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h3
  calc (T.card : ℝ)
      = ∑ α ∈ T.image (fun y : ℤ => (y : ZMod d)),
          (((T.filter (fun y : ℤ => (y : ZMod d) = α)).card : ℕ) : ℝ) := by
        rw [Finset.card_eq_sum_card_image (fun y : ℤ => (y : ZMod d)) T, Nat.cast_sum]
    _ ≤ ∑ _α ∈ T.image (fun y : ℤ => (y : ZMod d)), (2 * (A + 1) / (d : ℝ) + 1) :=
        Finset.sum_le_sum hfib
    _ = ((T.image (fun y : ℤ => (y : ZMod d))).card : ℝ) * (2 * (A + 1) / (d : ℝ) + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (V.card : ℝ) * (2 * (A + 1) / (d : ℝ) + 1) := by
        apply mul_le_mul_of_nonneg_right _ hB0
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (2 ^ (Nat.primeFactors d).card * (S15d2 d : ℝ)) * (2 * (A + 1) / (d : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hVle hB0

/-! ## 3. The theorem -/

theorem S15_polar_joint_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (Pa : Work.FITop.Params) (φ : ℝ) (L d : ℕ), 1 ≤ L → 1 ≤ d →
      (((Work.FIArea4.S15polarBox Pa φ).filter
        (fun z => L ∣ z.re.natAbs ∧ d ∣ Work.FIPlan.gnorm z)).card : ℝ)
        ≤ C * ((10 * Pa.θ * Real.sqrt Pa.N) / (d : ℝ) + 1)
            * ((10 * Pa.θ * Real.sqrt Pa.N) / (L : ℝ) + 1)
            * (2 : ℝ) ^ (Nat.primeFactors d).card * ((Work.FIArea4.S15d2 d : ℕ) : ℝ) := by
  refine ⟨4, by norm_num, ?_⟩
  intro Pa φ L d hL hd
  classical
  haveI : NeZero d := ⟨by omega⟩
  have hθ0 : 0 < Pa.θ := Pa.hθ0
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  set ρ : ℝ := 5 * Pa.θ * Real.sqrt Pa.N with hρdef
  set c : ℂ := (Real.sqrt Pa.N : ℂ)
    * Complex.exp (((φ + Real.pi * Pa.θ : ℝ) : ℂ) * Complex.I) with hcdef
  set S : Finset GaussianInt :=
    (S15polarBox Pa φ).filter (fun z => L ∣ z.re.natAbs ∧ d ∣ Work.FIPlan.gnorm z) with hSdef
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; positivity
  have hmem : ∀ z ∈ S, Work.FITop3.InPolarBox Pa φ z ∧ L ∣ z.re.natAbs
      ∧ d ∣ Work.FIPlan.gnorm z := by
    intro z hz
    rw [hSdef, Finset.mem_filter] at hz
    exact ⟨(mem_S15polarBox.mp hz.1).2, hz.2.1, hz.2.2⟩
  have hdisc : ∀ z ∈ S, ‖z.toComplex - c‖ ≤ ρ := by
    intro z hz
    rw [hcdef, hρdef]
    exact dist_polarBox_le Pa φ z (hmem z hz).1
  have hre : ∀ z ∈ S, |((z.re : ℤ) : ℝ) - c.re| ≤ ρ := by
    intro z hz
    calc |((z.re : ℤ) : ℝ) - c.re| = |(z.toComplex - c).re| := by
          rw [ofReal_re_eq_re z, Complex.sub_re]
      _ ≤ ‖z.toComplex - c‖ := Complex.abs_re_le_norm _
      _ ≤ ρ := hdisc z hz
  have him : ∀ z ∈ S, |((z.im : ℤ) : ℝ) - c.im| ≤ ρ := by
    intro z hz
    calc |((z.im : ℤ) : ℝ) - c.im| = |(z.toComplex - c).im| := by
          rw [ofReal_im_eq_im z, Complex.sub_im]
      _ ≤ ‖z.toComplex - c‖ := Complex.abs_im_le_norm _
      _ ≤ ρ := hdisc z hz
  set X : Finset ℤ := S.image (fun z => z.re) with hXdef
  have hXcard : (X.card : ℝ) ≤ 2 * (ρ / (L : ℝ)) + 1 := by
    rw [hXdef]
    apply card_le_of_dvd_mem_interval (e := L) hL (t := c.re - ρ) hρ0
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have h1 : (L : ℤ) ∣ ((z.re.natAbs : ℕ) : ℤ) :=
        Int.natCast_dvd_natCast.mpr (hmem z hz).2.1
      exact (Int.dvd_natAbs (a := (L : ℤ)) (b := z.re)).mp h1
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have h1 := hre z hz
      rw [abs_le] at h1
      exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  have hfiber : ∀ x ∈ X, ((S.filter (fun z => z.re = x)).card : ℝ)
      ≤ (2 ^ (Nat.primeFactors d).card * (S15d2 d : ℝ)) * (2 * (ρ + 1) / (d : ℝ) + 1) := by
    intro x _
    set F : Finset GaussianInt := S.filter (fun z => z.re = x) with hF
    set T : Finset ℤ := F.image (fun z => z.im) with hT
    have hTF : (T.card : ℕ) = F.card := by
      rw [hT]
      apply Finset.card_image_of_injOn
      intro z hz w hw hzw
      have hz' : z.re = x := (Finset.mem_filter.mp hz).2
      have hw' : w.re = x := (Finset.mem_filter.mp hw).2
      exact Zsqrtd.ext (by rw [hz', hw']) hzw
    have hTcard : (F.card : ℝ) = (T.card : ℝ) := by rw [hTF]
    have hint : ∀ y ∈ T, |(y : ℝ) - c.im| ≤ ρ := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      exact him z (Finset.mem_of_mem_filter z hz)
    have hcong : ∀ y ∈ T, ((y : ZMod d)) ^ 2 + ((x.natAbs : ZMod d)) ^ 2 = 0 := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      have hzS : z ∈ S := Finset.mem_of_mem_filter z hz
      have hzre : z.re = x := (Finset.mem_filter.mp hz).2
      have hdvd : d ∣ Work.FIPlan.gnorm z := (hmem z hzS).2.2
      have h1 := dvd_gnorm_zmod hdvd
      rwa [hzre] at h1
    rw [hTcard]
    exact card_im_fiber_le d hd x c.im ρ hρ0 T hint hcong
  have hSsum : S.card = ∑ x ∈ X, (S.filter (fun z => z.re = x)).card := by
    rw [hXdef]
    exact Finset.card_eq_sum_card_image (fun z : GaussianInt => z.re) S
  have hN0 : (0 : ℝ) ≤ 2 ^ (Nat.primeFactors d).card * (S15d2 d : ℝ) := by positivity
  have hmain : (S.card : ℝ) ≤ (2 * (ρ / (L : ℝ)) + 1)
      * ((2 ^ (Nat.primeFactors d).card * (S15d2 d : ℝ)) * (2 * (ρ + 1) / (d : ℝ) + 1)) := by
    have hB0' : (0 : ℝ) ≤ 2 * (ρ + 1) / (d : ℝ) + 1 := by
      have h1 : (0 : ℝ) ≤ 2 * (ρ + 1) := by linarith
      have h3 := div_nonneg h1 hdR.le
      linarith
    have hfb : (0 : ℝ) ≤ 2 ^ (Nat.primeFactors d).card * (S15d2 d : ℝ) := hN0
    calc (S.card : ℝ)
        = ∑ x ∈ X, ((S.filter (fun z => z.re = x)).card : ℝ) := by
          rw [hSsum, Nat.cast_sum]
      _ ≤ ∑ _x ∈ X, (2 ^ (Nat.primeFactors d).card * (S15d2 d : ℝ))
            * (2 * (ρ + 1) / (d : ℝ) + 1) := Finset.sum_le_sum hfiber
      _ = (X.card : ℝ) * ((2 ^ (Nat.primeFactors d).card * (S15d2 d : ℝ))
            * (2 * (ρ + 1) / (d : ℝ) + 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * (ρ / (L : ℝ)) + 1) * ((2 ^ (Nat.primeFactors d).card * (S15d2 d : ℝ))
            * (2 * (ρ + 1) / (d : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hXcard (mul_nonneg hfb hB0')
  -- final arithmetic: `2ρ = 10θ√N`
  have hAeq : 10 * Pa.θ * Real.sqrt Pa.N = 2 * ρ := by rw [hρdef]; ring
  have hA0 : 0 ≤ 10 * Pa.θ * Real.sqrt Pa.N := by rw [hAeq]; linarith
  have hLdiv0 : 0 ≤ (10 * Pa.θ * Real.sqrt Pa.N) / (L : ℝ) + 1 := by
    have h1 : (0 : ℝ) ≤ 10 * Pa.θ * Real.sqrt Pa.N := hA0
    have h2 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    have h3 := div_nonneg h1 h2
    linarith
  have h1 : 2 * (ρ / (L : ℝ)) + 1 = (10 * Pa.θ * Real.sqrt Pa.N) / (L : ℝ) + 1 := by
    rw [hAeq]; ring
  have h2 : 2 * (ρ + 1) / (d : ℝ) + 1 ≤ (10 * Pa.θ * Real.sqrt Pa.N) / (d : ℝ) + 3 := by
    rw [hAeq]
    have hsplit : 2 * (ρ + 1) / (d : ℝ) = 2 * ρ / (d : ℝ) + 2 / (d : ℝ) := by
      rw [show 2 * (ρ + 1) = 2 * ρ + 2 from by ring, add_div]
    rw [hsplit]
    have h2d : 2 / (d : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hdR]
      linarith [show (1 : ℝ) ≤ (d : ℝ) from by exact_mod_cast hd]
    linarith
  have h3 : (10 * Pa.θ * Real.sqrt Pa.N) / (d : ℝ) + 3
      ≤ 4 * ((10 * Pa.θ * Real.sqrt Pa.N) / (d : ℝ) + 1) := by
    have hdiv0 : 0 ≤ (10 * Pa.θ * Real.sqrt Pa.N) / (d : ℝ) := div_nonneg hA0 hdR.le
    linarith
  have hkey : (2 * (ρ / (L : ℝ)) + 1)
      * ((2 ^ (Nat.primeFactors d).card * (S15d2 d : ℝ)) * (2 * (ρ + 1) / (d : ℝ) + 1))
      ≤ 4 * ((10 * Pa.θ * Real.sqrt Pa.N) / (d : ℝ) + 1)
          * ((10 * Pa.θ * Real.sqrt Pa.N) / (L : ℝ) + 1)
          * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ) := by
    have hstep : (2 ^ (Nat.primeFactors d).card * (S15d2 d : ℝ))
        * (2 * (ρ + 1) / (d : ℝ) + 1)
        ≤ (2 ^ (Nat.primeFactors d).card * (S15d2 d : ℝ))
          * (4 * ((10 * Pa.θ * Real.sqrt Pa.N) / (d : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (le_trans h2 h3) hN0
    calc (2 * (ρ / (L : ℝ)) + 1)
          * ((2 ^ (Nat.primeFactors d).card * (S15d2 d : ℝ)) * (2 * (ρ + 1) / (d : ℝ) + 1))
        = ((10 * Pa.θ * Real.sqrt Pa.N) / (L : ℝ) + 1)
          * ((2 ^ (Nat.primeFactors d).card * (S15d2 d : ℝ)) * (2 * (ρ + 1) / (d : ℝ) + 1)) := by
          rw [h1]
      _ ≤ ((10 * Pa.θ * Real.sqrt Pa.N) / (L : ℝ) + 1)
          * ((2 ^ (Nat.primeFactors d).card * (S15d2 d : ℝ))
            * (4 * ((10 * Pa.θ * Real.sqrt Pa.N) / (d : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hstep hLdiv0
      _ = 4 * ((10 * Pa.θ * Real.sqrt Pa.N) / (d : ℝ) + 1)
          * ((10 * Pa.θ * Real.sqrt Pa.N) / (L : ℝ) + 1)
          * (2 : ℝ) ^ (Nat.primeFactors d).card * ((S15d2 d : ℕ) : ℝ) := by ring
  linarith [hmain, hkey]

end

end Work.FIArea4

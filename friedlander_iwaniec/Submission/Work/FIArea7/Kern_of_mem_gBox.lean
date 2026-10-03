import Mathlib
import Submission.Work.FIArea7.oddPartKernelDefs
import Submission.Work.FIArea7.sqfreeKernel_dvd_iff_odd

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary facts about the box `gBox` and the norm `gnorm`

The box `gBox R = {a + bi : |a|, |b| ≤ R}` is empty for `R < 0`, and for `R ≥ 0` every one of its
elements has `|z|² = a² + b² ≤ R² + R² ≤ (2R+1)²`.  We record the coordinate bounds, the formula
`|z|² = |a|² + |b|²` in `ℕ`, the inequality `|z|² ≤ (2R+1)²`, and the fact that `|z|²` is a sum of
two squares. -/

/-- The coordinates of a member of the box are bounded by `R`. -/
lemma mem_gBox_coords' {R : ℤ} {w : GaussianInt} (hw : w ∈ Work.FIPlan.gBox R) :
    |w.re| ≤ R ∧ |w.im| ≤ R := by
  rw [Work.FIPlan.gBox] at hw
  obtain ⟨p, hp, hpw⟩ := Finset.mem_image.mp hw
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  rw [Finset.mem_Icc] at hp1 hp2
  rw [← hpw]
  constructor
  · have h : (⟨p.1, p.2⟩ : GaussianInt).re = p.1 := rfl
    rw [h, abs_le]; exact ⟨hp1.1, hp1.2⟩
  · have h : (⟨p.1, p.2⟩ : GaussianInt).im = p.2 := rfl
    rw [h, abs_le]; exact ⟨hp2.1, hp2.2⟩

/-- `|z|² = |Re z|² + |Im z|²` as natural numbers. -/
lemma gnorm_eq_natAbs_sq_add (z : GaussianInt) :
    Work.FIPlan.gnorm z = z.re.natAbs ^ 2 + z.im.natAbs ^ 2 := by
  have h : (Work.FIPlan.gnorm z : ℤ) = ((z.re.natAbs ^ 2 + z.im.natAbs ^ 2 : ℕ) : ℤ) := by
    rw [Work.FIArea7.norm_eq]
    push_cast
    rw [sq_abs, sq_abs]
  exact_mod_cast h

/-- The norm of a member of the box is at most `(2R+1)²`. -/
lemma gnorm_le_of_mem_gBox {R : ℤ} {w : GaussianInt} (hw : w ∈ Work.FIPlan.gBox R) :
    Work.FIPlan.gnorm w ≤ (2 * R + 1).toNat ^ 2 := by
  obtain ⟨hre, him⟩ := mem_gBox_coords' hw
  have hR : 0 ≤ R := le_trans (abs_nonneg _) hre
  have hRc : ((R.toNat : ℕ) : ℤ) = R := Int.toNat_of_nonneg hR
  have h1 : w.re.natAbs ≤ R.toNat := by
    have h : ((w.re.natAbs : ℕ) : ℤ) ≤ ((R.toNat : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs, hRc]; exact hre
    exact_mod_cast h
  have h2 : w.im.natAbs ≤ R.toNat := by
    have h : ((w.im.natAbs : ℕ) : ℤ) ≤ ((R.toNat : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs, hRc]; exact him
    exact_mod_cast h
  have hR1 : (2 * R + 1).toNat = 2 * R.toNat + 1 := by
    apply Nat.cast_injective (R := ℤ)
    rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ 2 * R + 1 by linarith)]
    push_cast
    rw [hRc]
  calc Work.FIPlan.gnorm w = w.re.natAbs ^ 2 + w.im.natAbs ^ 2 := gnorm_eq_natAbs_sq_add w
    _ ≤ R.toNat ^ 2 + R.toNat ^ 2 :=
        Nat.add_le_add (Nat.pow_le_pow_left h1 2) (Nat.pow_le_pow_left h2 2)
    _ ≤ (2 * R.toNat + 1) ^ 2 := by nlinarith
    _ = (2 * R + 1).toNat ^ 2 := by rw [hR1]

/-- `|z|²` is a sum of two squares. -/
lemma gnorm_sq_add_sq (z : GaussianInt) : ∃ a b : ℕ, Work.FIPlan.gnorm z = a ^ 2 + b ^ 2 :=
  ⟨z.re.natAbs, z.im.natAbs, gnorm_eq_natAbs_sq_add z⟩

/-! ## Elementary facts about the kernel `Kern n = sqfreeKernel (oddPart n)` -/

/-- The odd part of a nonzero number is nonzero. -/
lemma oddPart_ne_zero {n : ℕ} (hn : n ≠ 0) : Work.FIPlan.oddPart n ≠ 0 := by
  intro h
  have h' : n / 2 ^ n.factorization 2 * 2 ^ n.factorization 2 = n :=
    Nat.div_mul_cancel (Nat.ordProj_dvd n 2)
  rw [Work.FIPlan.oddPart] at h
  rw [h, zero_mul] at h'
  exact hn h'.symm

/-- The odd part of a nonzero number is odd. -/
lemma oddPart_odd {n : ℕ} (hn : n ≠ 0) : Odd (Work.FIPlan.oddPart n) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm0 : Work.FIPlan.oddPart n ≠ 0 := oddPart_ne_zero hn
  rw [← Nat.not_even_iff_odd]
  intro hE
  have hdvd : 2 ∣ Work.FIPlan.oddPart n := even_iff_two_dvd.mp hE
  have h1 : 1 ≤ padicValNat 2 (Work.FIPlan.oddPart n) := one_le_padicValNat_of_dvd hm0 hdvd
  have h2 : padicValNat 2 (Work.FIPlan.oddPart n) = 0 := by
    have h := padicValNat.div_pow (p := 2) (a := n.factorization 2) (b := n) (Nat.ordProj_dvd n 2)
    have hf : padicValNat 2 n = n.factorization 2 := (Nat.factorization_def n Nat.prime_two).symm
    rw [hf, Nat.sub_self] at h
    exact h
  omega

/-- `Kern 0 = 0`. -/
lemma Kern_zero : Kern 0 = 0 := by
  have h1 : Work.FIPlan.oddPart 0 = 0 := by
    rw [Work.FIPlan.oddPart]
    simp
  rw [Kern, h1]
  have h2 : Work.FIArea4.sqPart 0 = 0 := by
    rw [Work.FIArea4.sqPart]
    simp
  unfold Work.FIArea4.sqfreeKernel
  rw [h2]
  simp

/-- `Kern n ≠ 0` for `n ≠ 0`. -/
lemma Kern_ne_zero {n : ℕ} (hn : n ≠ 0) : Kern n ≠ 0 := by
  have hm : Work.FIPlan.oddPart n ≠ 0 := oddPart_ne_zero hn
  have hsq := (Work.FIArea4.sqfree_kernel (Work.FIPlan.oddPart n) hm).2.2.1
  intro h0
  rw [Kern] at h0
  rw [h0, zero_mul] at hsq
  exact hm hsq.symm

/-- `Kern n` is squarefree for `n ≠ 0`. -/
lemma squarefree_Kern {n : ℕ} (hn : n ≠ 0) : Squarefree (Kern n) :=
  (Work.FIArea4.sqfree_kernel (Work.FIPlan.oddPart n) (oddPart_ne_zero hn)).2.2.2.2

/-- `oddPart d` divides `d`. -/
lemma oddPart_dvd' (d : ℕ) : Work.FIPlan.oddPart d ∣ d := by
  rw [Work.FIPlan.oddPart]
  exact Nat.div_dvd_of_dvd (Nat.ordProj_dvd d 2)

/-- `Kern n` divides the odd part of `n`, hence `n` itself. -/
lemma Kern_dvd_oddPart (n : ℕ) : Kern n ∣ Work.FIPlan.oddPart n := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Kern_zero, show Work.FIPlan.oddPart 0 = 0 by simp [Work.FIPlan.oddPart] ]; try exact dvd_zero _
  · exact (Work.FIArea4.sqfree_kernel (Work.FIPlan.oddPart n) (oddPart_ne_zero hn)).2.2.2.1

/-- `Kern n ≤ n` for `n ≠ 0`. -/
lemma Kern_le_self {n : ℕ} (hn : n ≠ 0) : Kern n ≤ n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (dvd_trans (Kern_dvd_oddPart n) (oddPart_dvd' n))

/-- `Kern n` is odd for `n ≠ 0`. -/
lemma Kern_odd {n : ℕ} (hn : n ≠ 0) : Odd (Kern n) := by
  rw [← Nat.not_even_iff_odd]
  intro hE
  have hdvd : 2 ∣ Kern n := even_iff_two_dvd.mp hE
  have hdvd' : 2 ∣ Work.FIPlan.oddPart n := dvd_trans hdvd (Kern_dvd_oddPart n)
  exact (Odd.not_two_dvd_nat (oddPart_odd hn)) hdvd'

/-- For an odd prime `p`, the `p`-adic valuation of `oddPart n` equals that of `n`. -/
lemma padicValNat_oddPart {n p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    padicValNat p (Work.FIPlan.oddPart n) = padicValNat p n := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hcop2 : p.Coprime 2 :=
    hp.coprime_iff_not_dvd.mpr fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have hcp : p.Coprime (2 ^ n.factorization 2) := hcop2.pow_right _
  exact padicValNat.div' (p := p) (m := 2 ^ n.factorization 2) hcp (Nat.ordProj_dvd n 2)

/-- For `n ≠ 0` and an odd prime `p`: `p` divides `Kern n` exactly when `p` occurs in `n` to an
odd power. -/
lemma Kern_dvd_iff_odd_padicValNat {n p : ℕ} (hn : n ≠ 0) (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    p ∣ Kern n ↔ Odd (padicValNat p n) := by
  have hm : Work.FIPlan.oddPart n ≠ 0 := oddPart_ne_zero hn
  rw [show Kern n = Work.FIArea4.sqfreeKernel (Work.FIPlan.oddPart n) from rfl]
  rw [Work.FIArea7.sqfreeKernel_dvd_iff_odd (Work.FIPlan.oddPart n) p hm hp]
  rw [Nat.factorization_def (Work.FIPlan.oddPart n) hp]
  rw [padicValNat_oddPart hp hp2]

/-- **The kernel of a sum of two squares.**  If `n = x² + y² ≠ 0`, then `Kern n` is squarefree,
has no prime factor `≡ 3 (mod 4)`, and is at most `n`. -/
theorem Kern_of_sq_add_sq {n : ℕ} (hn : n ≠ 0) (h : ∃ x y : ℕ, n = x ^ 2 + y ^ 2) :
    Squarefree (Kern n) ∧ (∀ p ∈ (Kern n).primeFactors, p % 4 = 1) ∧ Kern n ≤ n := by
  refine ⟨squarefree_Kern hn, ?_, Kern_le_self hn⟩
  intro p hp_mem
  rw [Nat.mem_primeFactors] at hp_mem
  obtain ⟨hp, hpdvd, _⟩ := hp_mem
  have hp2 : p ≠ 2 := by
    intro h2
    rw [h2] at hpdvd
    exact (Odd.not_two_dvd_nat (Kern_odd hn)) hpdvd
  have hpodd : Odd (padicValNat p n) := (Kern_dvd_iff_odd_padicValNat hn hp hp2).mp hpdvd
  have hne3 : p % 4 ≠ 3 := by
    intro h3
    have hpdvdn : p ∣ n := dvd_trans hpdvd (dvd_trans (Kern_dvd_oddPart n) (oddPart_dvd' n))
    have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdn, hn⟩
    have heven : Even (padicValNat p n) := Nat.eq_sq_add_sq_iff.mp h p hmem h3
    obtain ⟨a, ha⟩ := heven
    obtain ⟨b, hb⟩ := hpodd
    omega
  have hmod2 : p % 2 = 1 := (Nat.Prime.eq_two_or_odd hp).resolve_left hp2
  have hlt : p % 4 < 4 := Nat.mod_lt p (by norm_num)
  have hmod4 : (p % 4) % 2 = p % 2 := Nat.mod_mod_of_dvd p (by norm_num : 2 ∣ 4)
  omega

/-- Every `w` in the box `gBox R` has `Kern |w|² = 0`, or else this kernel is squarefree, has all
prime factors `≡ 1 (mod 4)`, and is at most `(2R+1)²`. -/
theorem Kern_of_mem_gBox (R : ℤ) (w : GaussianInt) (hw : w ∈ Work.FIPlan.gBox R) :
    Kern (Work.FIPlan.gnorm w) = 0 ∨
      (Squarefree (Kern (Work.FIPlan.gnorm w)) ∧
       (∀ p ∈ (Kern (Work.FIPlan.gnorm w)).primeFactors, p % 4 = 1) ∧
       Kern (Work.FIPlan.gnorm w) ≤ (((2 * R + 1).toNat) ^ 2)) := by
  by_cases hn : Work.FIPlan.gnorm w = 0
  · exact Or.inl (by rw [hn, Kern_zero])
  · obtain ⟨hsf, hprimes, hle⟩ := Kern_of_sq_add_sq hn (gnorm_sq_add_sq w)
    exact Or.inr ⟨hsf, hprimes, le_trans hle (gnorm_le_of_mem_gBox hw)⟩

end

end Work.FIArea7

/-
# `Work.FIArea3.JointCount.twoPin` — the "pin" at the ramified prime `2`

`IsSPt d w` means `w ∣ d` and `d ∣ |w|²` in `ℤ[i]`; `w` is a *maximal piece* of
`{z | d ∣ |z|²}` when in addition it is minimal in `S = {w | IsSPt d w}` for divisibility.
`twoPin` says that for such a `w` the exponent of the **ramified** rational prime `2` in the
norm `|w|²` is exactly its exponent in `d`:

    `(|w|²).factorization 2 = d.factorization 2`.

The two inequalities are of very different nature.

* `≤` is the *descent* (`SStructure.descent`) applied to the Gaussian prime `1 + i` above `2`,
  which has norm `2`.  Its hypotheses are met as soon as `1 + i ∣ w`, and this holds exactly
  when `2 ∣ |w|²`: writing `w = a + bi` we have `|w|² = a² + b² = (a + b)² - 2ab`, so
  `2 ∣ a² + b²` forces `a + b` even, and then `w = (1+i)·⟨(a+b)/2, (b-a)/2⟩`
  (`one_add_I_dvd_of_two_dvd_gnorm`).  Since `|w/(1+i)|² = |w|²/2`, the descent forbids
  `d ∣ |w|²/2`, which by `factorization_le_of_not_dvd_div` is precisely
  `(|w|²).factorization 2 ≤ d.factorization 2`.  When `2 ∤ |w|²` the exponent is `0` outright.

* `≥` is immediate from `d ∣ |w|²` (`Nat.factorization_le_iff_dvd`), since `d ≥ 1` and `w ≠ 0`.

The auxiliary facts about `1 + i` are proved from scratch: `gnorm (1+i) = 2`,
`Prime (1+i)` (via its irreducible norm `2`), and the divisibility criterion above.
-/
import Mathlib
import Submission.Work.FIArea3.JointCount.SStructure

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea3.JointCount

open Work.FIPlan

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The Gaussian norm of the ramified prime `1 + i` is `2`. -/
lemma gnorm_one_add_I : gnorm (⟨1, 1⟩ : GaussianInt) = 2 := by
  simp [gnorm, Zsqrtd.norm_def]

/-- If `2 ∣ |w|²` then `2 ∣ w.re + w.im`: this is the statement that `w` lies in the ideal
`(1 + i)`, which is the unique prime ideal above `2`. -/
lemma two_dvd_re_add_im_of_two_dvd_gnorm {w : GaussianInt} (h : 2 ∣ gnorm w) :
    (2 : ℤ) ∣ w.re + w.im := by
  have hnorm : ((gnorm w : ℕ) : ℤ) = w.re ^ 2 + w.im ^ 2 := by
    rw [gnorm, GaussianInt.abs_natCast_norm, Zsqrtd.norm_def]
    ring
  have h2 : (2 : ℤ) ∣ w.re ^ 2 + w.im ^ 2 := by
    rw [← hnorm]
    exact_mod_cast h
  -- reduce `a ^ 2 + b ^ 2 ≡ 0` to `a + b ≡ 0` modulo `2`, where `x ^ 2 = x`
  have hz : (w.re : ZMod 2) ^ 2 + (w.im : ZMod 2) ^ 2 = 0 := by
    have h0 : ((w.re ^ 2 + w.im ^ 2 : ℤ) : ZMod 2) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr h2
    push_cast at h0
    exact h0
  have hsq : ∀ x : ZMod 2, x ^ 2 = x := by decide
  rw [hsq w.re, hsq w.im] at hz
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (w.re + w.im) 2).mp (by push_cast; exact hz)

/-- `1 + i` divides every `w` with `2 ∣ |w|²`, with the explicit quotient
`⟨(a+b)/2, (b-a)/2⟩` for `w = a + bi`. -/
lemma one_add_I_dvd_of_two_dvd_gnorm {w : GaussianInt} (h : 2 ∣ gnorm w) :
    (⟨1, 1⟩ : GaussianInt) ∣ w := by
  obtain ⟨k, hk⟩ := two_dvd_re_add_im_of_two_dvd_gnorm h
  refine ⟨⟨k, w.im - k⟩, ?_⟩
  ext
  · simp only [Zsqrtd.re_mul]
    linarith
  · simp only [Zsqrtd.im_mul]
    ring

/-- `1 + i` is prime in `ℤ[i]`: it is irreducible because its norm is the rational prime `2`. -/
lemma prime_one_add_I : Prime (⟨1, 1⟩ : GaussianInt) := by
  rw [← UniqueFactorizationMonoid.irreducible_iff_prime]
  refine ⟨?_, ?_⟩
  · intro hu
    have h1 : gnorm (⟨1, 1⟩ : GaussianInt) = 1 := Zsqrtd.norm_eq_one_iff.mpr hu
    rw [gnorm_one_add_I] at h1
    norm_num at h1
  · intro a b hab
    have hg : gnorm a * gnorm b = 2 := by rw [← gnorm_mul, ← hab, gnorm_one_add_I]
    have hdiv : gnorm a ∣ 2 := ⟨gnorm b, hg.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h1 | h2
    · exact Or.inl (Zsqrtd.norm_eq_one_iff.mp h1)
    · refine Or.inr (Zsqrtd.norm_eq_one_iff.mp ?_)
      have hb : gnorm b = 1 := by
        rw [h2] at hg
        omega
      exact hb

theorem twoPin {d : ℕ} (hd : 1 ≤ d) {w : GaussianInt}
    (hS : Work.FIArea3.JointCount.IsSPt d w)
    (hmin : ∀ v : GaussianInt, Work.FIArea3.JointCount.IsSPt d v → v ∣ w → w ∣ v) :
    (Work.FIPlan.gnorm w).factorization 2 = d.factorization 2 := by
  have hd0 : d ≠ 0 := by omega
  have hdc : (d : GaussianInt) ≠ 0 := by exact_mod_cast hd0
  have hw0 : w ≠ 0 := ne_zero_of_dvd_ne_zero hdc hS.1
  have hgw0 : gnorm w ≠ 0 := fun h => hw0 ((gnorm_eq_zero_iff w).mp h)
  -- `≥`: `d` divides `|w|²`, hence its `2`-adic exponent is at most that of `|w|²`
  have hle : d.factorization 2 ≤ (gnorm w).factorization 2 :=
    (Nat.factorization_le_iff_dvd hd0 hgw0).mpr hS.2 2
  refine le_antisymm ?_ hle
  by_cases h2 : 2 ∣ gnorm w
  · -- `≤`: the descent at `1 + i`, where `|w/(1+i)|² = |w|²/2`
    have hρw : (⟨1, 1⟩ : GaussianInt) ∣ w := one_add_I_dvd_of_two_dvd_gnorm h2
    have hndvd : ¬ d ∣ gnorm (w / (⟨1, 1⟩ : GaussianInt)) :=
      descent hd hS hmin (⟨1, 1⟩ : GaussianInt) prime_one_add_I hρw
    have hρ0 : (⟨1, 1⟩ : GaussianInt) ≠ 0 := prime_one_add_I.ne_zero
    have hmul : gnorm (w / (⟨1, 1⟩ : GaussianInt)) * 2 = gnorm w := by
      have h := gnorm_div_mul hρ0 hρw
      rwa [gnorm_one_add_I] at h
    have hdiv : gnorm w / 2 = gnorm (w / (⟨1, 1⟩ : GaussianInt)) := by
      rw [← hmul, mul_comm]
      exact Nat.mul_div_right _ (by norm_num)
    have hq0 : gnorm (w / (⟨1, 1⟩ : GaussianInt)) ≠ 0 := by
      intro h
      have hq : w / (⟨1, 1⟩ : GaussianInt) = 0 := (gnorm_eq_zero_iff _).mp h
      have hm : (⟨1, 1⟩ : GaussianInt) * (w / (⟨1, 1⟩ : GaussianInt)) = w :=
        EuclideanDomain.mul_div_cancel' hρ0 hρw
      rw [hq, mul_zero] at hm
      exact hw0 hm.symm
    exact factorization_le_of_not_dvd_div (p := 2) (d := d) (M := gnorm w) Nat.prime_two
      (by rw [hdiv]; exact hq0) hd0 (Nat.mul_div_cancel' h2) hS.2 (by rw [hdiv]; exact hndvd)
  · -- `2 ∤ |w|²`: the exponent vanishes
    rw [Nat.factorization_eq_zero_of_not_dvd h2]
    exact Nat.zero_le _

end

end Work.FIArea3.JointCount

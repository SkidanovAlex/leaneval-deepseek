/-
# `Submission.Work.FIArea3.JointCount.splitPin` — the split-prime pinning on the minimal set `S`

For `d ≥ 1` let `S = IsSPt d` be the interpolating set `{w : ℤ[i] | w ∣ d, d ∣ |w|²}` and let
`w ∈ S` be minimal in `S` for divisibility (`hmin`).  The present file pins down the exponent of a
**split** prime `p ≡ 1 (mod 4)`, `p ∣ d`, in the norm of `w`:

  `(gnorm w).factorization p = d.factorization p`.

## Mathematics

`d ∣ gnorm w` immediately gives `≤`.  For the reverse inequality, note that `p ≡ 1 (mod 4)` is
not prime in `ℤ[i]`: by Fermat's two-squares theorem `p = a² + b²`, so `π = a + bi` has
`gnorm π = p` and is a Gaussian prime.  Since `p ∣ d ∣ gnorm w = w · star w`, the prime `π`
divides `w · star w`, hence `π ∣ w` or `π ∣ star w`; either way there is a Gaussian prime `ρ` with
`gnorm ρ = p` dividing `w`.

The **descent** (`SStructure.descent`) applied to `ρ` gives `d ∤ gnorm (w/ρ)`, i.e. `d` does not
divide `M/p` where `M = gnorm w`.  Since `d ∣ M`, that failure can only be at the prime `p`
itself (for every other prime `r` the exponent of `r` in `M/p` equals its exponent in `M`, which
is at least its exponent in `d`).  Hence `M.factorization p - 1 < d.factorization p`, so
`M.factorization p ≤ d.factorization p`, and the two inequalities agree.
-/
import Mathlib
import Submission.Work.FIArea3.JointCount.SStructure

set_option linter.style.haveILetI false

namespace Work.FIArea3.JointCount

open Work.FIPlan

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Elementary Gaussian arithmetic -/

/-- The Gaussian norm of `a + bi` (with integer coordinates). -/
lemma splitPin_gnorm_mk (a b : ℤ) :
    gnorm (⟨a, b⟩ : GaussianInt) = (a ^ 2 + b ^ 2).natAbs := by
  have h : (⟨a, b⟩ : GaussianInt).norm = a ^ 2 + b ^ 2 := by
    rw [Zsqrtd.norm_def]; ring
  rw [gnorm, h]

/-- `q ∣ n` for natural numbers lifts to `(q : ℤ[i]) ∣ (n : ℤ[i])`. -/
lemma splitPin_natCast_dvd_natCast {q n : ℕ} (h : q ∣ n) :
    (q : GaussianInt) ∣ (n : GaussianInt) := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨(c : GaussianInt), by push_cast; ring⟩

/-- **Any Gaussian integer of prime norm is a Gaussian prime.**  (`ℤ[i]` is a UFD, so
irreducible elements are prime.) -/
lemma splitPin_prime_of_gnorm_eq_prime {ρ : GaussianInt} {p : ℕ} (hp : p.Prime)
    (hρ : gnorm ρ = p) : Prime ρ := by
  rw [← irreducible_iff_prime]
  refine ⟨?_, ?_⟩
  · intro hu
    have h1 : gnorm ρ = 1 := Zsqrtd.norm_eq_one_iff.mpr hu
    exact hp.ne_one (hρ ▸ h1)
  · intro x y hxy
    have h1 : gnorm x * gnorm y = p := by rw [← gnorm_mul, ← hxy, hρ]
    have hx : gnorm x ∣ p := h1 ▸ dvd_mul_right _ _
    rcases hp.eq_one_or_self_of_dvd (gnorm x) hx with hx1 | hxp
    · exact Or.inl (Zsqrtd.norm_eq_one_iff.mp hx1)
    · refine Or.inr (Zsqrtd.norm_eq_one_iff.mp ?_)
      have h2 : p * gnorm y = p * 1 := by
        calc p * gnorm y = gnorm x * gnorm y := by rw [hxp]
          _ = p := h1
          _ = p * 1 := (mul_one p).symm
      exact Nat.mul_left_cancel hp.pos h2

/-! ## A Gaussian prime above a split prime `p`

Fermat's two-squares theorem: a prime `p ≡ 1 (mod 4)` is a sum of two squares, so it is the norm of
a Gaussian prime.  If such a prime divides `gnorm z = z · star z`, one of `π`, `star π` divides `z`.
-/

/-- Fermat's two-squares input: for a prime `p ≡ 1 (mod 4)` there is a Gaussian prime `π` with
`gnorm π = p`. -/
lemma splitPin_exists_prime_gnorm_eq {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    ∃ π : GaussianInt, Prime π ∧ gnorm π = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpne : p % 4 ≠ 3 := by rw [hp4]; norm_num
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) hpne
  refine ⟨⟨(a : ℤ), (b : ℤ)⟩, ?_, ?_⟩
  · refine splitPin_prime_of_gnorm_eq_prime hp ?_
    rw [splitPin_gnorm_mk]
    have h2 : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = (p : ℤ) := by exact_mod_cast hab
    rw [h2, Int.natAbs_natCast]
  · rw [splitPin_gnorm_mk]
    have h2 : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = (p : ℤ) := by exact_mod_cast hab
    rw [h2, Int.natAbs_natCast]

/-- **A Gaussian prime of norm `p` dividing `z`.**  For `p ≡ 1 (mod 4)` prime with
`p ∣ gnorm z`, some Gaussian prime of norm exactly `p` divides `z`. -/
lemma splitPin_exists_prime_dvd_gnorm {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1)
    {z : GaussianInt} (h : p ∣ gnorm z) :
    ∃ ρ : GaussianInt, Prime ρ ∧ ρ ∣ z ∧ gnorm ρ = p := by
  obtain ⟨π, hπprime, hπgn⟩ := splitPin_exists_prime_gnorm_eq hp hp4
  have hdvd : (p : GaussianInt) ∣ z * star z := by
    rw [mul_star_eq_gnorm]
    exact splitPin_natCast_dvd_natCast h
  have hpval : (p : GaussianInt) = π * star π := by
    rw [← hπgn]
    exact (Work.FIArea3.JointCount.mul_star_eq_gnorm π).symm
  rw [hpval] at hdvd
  have hdvd' : π ∣ z * star z := dvd_trans (dvd_mul_right π (star π)) hdvd
  rcases hπprime.dvd_mul.mp hdvd' with hc | hc
  · exact ⟨π, hπprime, hc, hπgn⟩
  · refine ⟨star π, ?_, ?_, ?_⟩
    · refine splitPin_prime_of_gnorm_eq_prime hp ?_
      rw [GaussPieceMax_arith_gnorm_star]; exact hπgn
    · rwa [star_dvd_iff_dvd_star]
    · rwa [GaussPieceMax_arith_gnorm_star]

/-! ## The pinning -/

theorem splitPin {d : ℕ} (hd : 1 ≤ d) {w : GaussianInt}
    (hS : Work.FIArea3.JointCount.IsSPt d w)
    (hmin : ∀ v : GaussianInt, Work.FIArea3.JointCount.IsSPt d v → v ∣ w → w ∣ v)
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) (hpd : p ∣ d) :
    (Work.FIPlan.gnorm w).factorization p = d.factorization p := by
  have hd0 : d ≠ 0 := by omega
  have hdc : (d : GaussianInt) ≠ 0 := Nat.cast_ne_zero.mpr hd0
  have hw0 : w ≠ 0 := ne_zero_of_dvd_ne_zero hdc hS.1
  have hM0 : gnorm w ≠ 0 := fun h => hw0 ((gnorm_eq_zero_iff w).mp h)
  -- `d ∣ gnorm w` gives the inequality `≤` in the exponents.
  have hleM : d.factorization ≤ (gnorm w).factorization :=
    (Nat.factorization_le_iff_dvd hd0 hM0).mpr hS.2
  -- A Gaussian prime `ρ` of norm `p` divides `w`.
  obtain ⟨ρ, hρprime, hρw, hρgn⟩ :=
    splitPin_exists_prime_dvd_gnorm hp hp4 (hpd.trans hS.2)
  have hρ0 : ρ ≠ 0 := hρprime.ne_zero
  have hq0 : w / ρ ≠ 0 := by
    intro h0
    have hmul := EuclideanDomain.mul_div_cancel' hρ0 hρw
    rw [h0, mul_zero] at hmul
    exact hw0 hmul.symm
  have hK0 : gnorm (w / ρ) ≠ 0 := fun h => hq0 ((gnorm_eq_zero_iff (w / ρ)).mp h)
  have hmulgn : gnorm (w / ρ) * gnorm ρ = gnorm w := gnorm_div_mul hρ0 hρw
  -- Factorization bookkeeping along `gnorm w = gnorm (w/ρ) · p`.
  have hfac : (gnorm w).factorization = (gnorm (w / ρ)).factorization + p.factorization := by
    rw [← hmulgn, hρgn, Nat.factorization_mul hK0 hp.ne_zero]
  have hKp : (gnorm (w / ρ)).factorization p = (gnorm w).factorization p - 1 := by
    have h := congrArg (fun f : ℕ →₀ ℕ => f p) hfac
    simp only [Finsupp.add_apply, Nat.Prime.factorization hp, Finsupp.single_eq_same] at h
    omega
  have hKr : ∀ r : ℕ, r ≠ p →
      (gnorm (w / ρ)).factorization r = (gnorm w).factorization r := by
    intro r hr
    have h := congrArg (fun f : ℕ →₀ ℕ => f r) hfac
    simp only [Finsupp.add_apply, Nat.Prime.factorization hp, Finsupp.single_eq_of_ne hr,
      add_zero] at h
    exact h.symm
  -- The descent: `d ∤ gnorm (w/ρ)`.
  have hnd : ¬ d ∣ gnorm (w / ρ) := descent (d := d) hd hS hmin ρ hρprime hρw
  refine le_antisymm ?_ (hleM p)
  by_contra hcon
  push Not at hcon
  have hnotle : ¬ (d.factorization ≤ (gnorm (w / ρ)).factorization) := by
    intro h
    exact hnd ((Nat.factorization_le_iff_dvd hd0 hK0).mp h)
  obtain ⟨r, hr⟩ : ∃ r, (gnorm (w / ρ)).factorization r < d.factorization r := by
    by_contra hc
    push Not at hc
    exact hnotle (Finsupp.le_def.mpr hc)
  rcases eq_or_ne r p with hrp | hrp
  · subst hrp
    rw [hKp] at hr
    omega
  · rw [hKr r hrp] at hr
    exact absurd hr (not_lt.mpr (hleM r))

end

end Work.FIArea3.JointCount

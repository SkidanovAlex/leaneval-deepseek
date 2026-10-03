/-
# `Submission.Work.FIArea5.S16Hecke.splitPrimaryClass`

The primary Gaussian integers of norm `p ^ ν`, for `p ≡ 1 (mod 4)` a rational prime, are exactly
the `ν + 1` elements `π ^ a · π' ^ (ν - a)`, `0 ≤ a ≤ ν`, where `π`, `π'` are the two primary
primes of norm `p` (conjugate to each other).

This is the local (at the split prime `p`) input to the local recursion of the Hecke eigenvalues
`λ(p ^ ν)` of `ℚ(i)`: over the primary coset `1 + 2(1+i)ℤ[i]` every ideal of norm `p ^ ν` has a
single primary generator, so the ideals `(π) ^ a (π') ^ (ν - a)` correspond bijectively to those
`ν + 1` primary elements.

The file reduces the theorem to three statements proved elsewhere in the workspace:

* `existsPrimarySplit` — a primary Gaussian prime `π` of norm `p` whose conjugate is not an
  associate (Fermat's two-squares theorem plus the primary normalisation);
* `primaryPowClassify` — every primary `z` of norm `p ^ ν` equals `π ^ a · (star π) ^ (ν - a)`;
* `powClassUnique` — the exponent `a` in that representation is unique.

The remaining ingredients (conjugation preserves primacy, `gnorm` of a conjugate, conjugation
preserves irreducibility) are proved inline below.
-/
import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea5.S16Hecke.existsPrimarySplit
import Submission.Work.FIArea5.S16Hecke.primaryPowClassify
import Submission.Work.FIArea5.S16Hecke.powClassUnique

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke

open Work.FIPlan

/-- **The primary condition survives conjugation.**  If `z.re` is odd and `z.im` is even with
`z.im ≡ z.re - 1 (mod 4)`, then for `star z` (same real part, imaginary part `-z.im`) one has
`-z.im ≡ z.re - 1 (mod 4)` because `z.re - 1` is even, so `-(z.re - 1) ≡ z.re - 1 (mod 4)`. -/
private theorem isPrimary_star_aux {z : GaussianInt} (hz : IsPrimary z) : IsPrimary (star z) := by
  obtain ⟨hodd, heven, hmod⟩ := hz
  refine ⟨by simpa [Zsqrtd.re_star] using hodd, ?_, ?_⟩
  · simpa [Zsqrtd.im_star] using heven.neg
  · rw [Zsqrtd.im_star, Zsqrtd.re_star]
    have hsym : -(z.re - 1) ≡ z.re - 1 [ZMOD 4] := by
      rw [Int.modEq_iff_dvd]
      obtain ⟨k, hk⟩ := hodd
      exact ⟨k, by rw [hk]; ring⟩
    exact hmod.neg.trans hsym

/-- Conjugation preserves `gnorm = |z|²`. -/
private theorem gnorm_star_aux (z : GaussianInt) : gnorm (star z) = gnorm z := by
  simp only [gnorm, Zsqrtd.norm_conj]

/-- Conjugation preserves irreducibility (`star` is an isomorphism of `ℤ[i]`). -/
private theorem irreducible_star_aux {z : GaussianInt} (hz : Irreducible z) :
    Irreducible (star z) := by
  refine ⟨fun hu => hz.1 (isUnit_star.mp hu), fun a b hab => ?_⟩
  have h : z = star a * star b := by
    have h1 := congrArg star hab
    rw [star_mul, star_star] at h1
    rw [h1, mul_comm]
  rcases hz.2 h with h | h
  · exact Or.inl (isUnit_star.mp h)
  · exact Or.inr (isUnit_star.mp h)

theorem splitPrimaryClass (p : ℕ) (hp : p.Prime) (h1 : p % 4 = 1) :
    ∃ π π' : GaussianInt,
      Work.FIPlan.IsPrimary π ∧ Work.FIPlan.IsPrimary π' ∧
      Work.FIPlan.gnorm π = p ∧ Work.FIPlan.gnorm π' = p ∧
      Irreducible π ∧ Irreducible π' ∧ ¬ Associated π π' ∧
      (∀ ν : ℕ, ∀ z : GaussianInt, Work.FIPlan.IsPrimary z → Work.FIPlan.gnorm z = p ^ ν →
        ∃! a : ℕ, a ≤ ν ∧ z = π ^ a * π' ^ (ν - a)) := by
  obtain ⟨π, hπprim, hπgn, hπirr, hnassoc⟩ := existsPrimarySplit p hp h1
  refine ⟨π, star π, hπprim, isPrimary_star_aux hπprim, hπgn, ?_, hπirr,
    irreducible_star_aux hπirr, hnassoc, ?_⟩
  · rw [gnorm_star_aux]; exact hπgn
  · intro ν z hzp hzgn
    obtain ⟨a, ha, haeq⟩ := primaryPowClassify p π hp.pos hπprim hπgn hπirr ν z hzp hzgn
    exact ⟨a, ⟨ha, haeq⟩, fun b hb =>
      (powClassUnique π ν a b hπirr hnassoc ha hb.1 (haeq.symm.trans hb.2)).symm⟩

end Work.FIArea5.S16Hecke

import Mathlib
import Submission.Work.FIArea7.ReSymbolTwist
import Submission.Work.FIArea7.WBOmega
import Submission.Work.FIArea7.reflection_pair_betaPrime_general

namespace Work.FIArea7

/-- ***FI* Lemma 17.1 (17.5) at the round-6 ratio symbol, general sign.**

The round-3 form `Work.FIArea7.ratioSym_absDelta_eq` (and its frozen-symbol ancestor
`Work.FIArea7.jacobiSym_reflection`) assumes the paper's (17.4) `0 < r₁r₂`, i.e. that the polar
box does not straddle the imaginary axis.  The round-6 polar box (5.14) has an *arbitrary* `φ`
and may contain points with `Re = 0`, so the general-sign form is needed: for primary, coprime
`z₁, z₂` with squarefree norms, `(|z₁|²,|Δ|) = 1`, `z₁ ≡ z₂ (mod 8)`, `r_i ≠ 0` and `Δ ≠ 0`,

  `(z₂/z₁||Δ|) = reflSign z₁ z₂ · (s₁/|r₁|)·(s₂/|r₂|)`,

where `Work.FIArea7.reflSign` is the mixed-sign correction of the reciprocity bookkeeping (the
§11ter formula of `FIArea7/NOTES.md`: `1` iff `0 < r₁r₂` or `sign r₁ = sign Δ`).

The proof route is short, given what is already proved:
* `Work.FIArea7.reflection_pair_betaPrime_general` (the *mod 4*, general-sign, frozen-symbol
  identity) at `β = 1` gives
  `J(Re(z̄₁z₂)||Δ|) = twCorr·reflSign·i^{(r₂-1)/2-(r₁-1)/2}·J(|z₁|²||Δ|)·([z₁]·conj([z₂]))`;
* `Work.FIArea7.jksym_mul_star` evaluates `[z₁]·conj([z₂])`, and the two powers of `i` cancel;
* `Work.FIArea7.jacobiSym_re_eq_ratioSym_mul` plus `jacobiSym.sq_one` give
  `ratioSym z₁ z₂ |Δ| = J(Re(z̄₁z₂)||Δ|)·J(|z₁|²||Δ|)`;
* `htw` removes the 2-adic factor — for `z₁ ≡ z₂ (mod 8)` it is `1` by
  `Work.FIArea7.twCorr_eq_one_of_sameClass8` (so `twCorr` may in fact be replaced by `1`, but the
  explicit hypothesis keeps this statement independent of that one).

`reflSign z₁ z₂ = 1` whenever `0 < r₁r₂`, so this generalises
`Work.FIArea7.ratioSym_absDelta_eq`. -/
theorem ratioSym_absDelta_eq_general (z1 z2 : GaussianInt)
    (hP1 : Work.FIPlan.IsPrimary z1) (hP2 : Work.FIPlan.IsPrimary z2)
    (hs1 : Squarefree (Work.FIPlan.gnorm z1)) (hs2 : Squarefree (Work.FIPlan.gnorm z2))
    (hc : IsCoprime z1 z2)
    (hcc : IsCoprime ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℤ))
    (h8r : z1.re ≡ z2.re [ZMOD 8]) (h8i : z1.im ≡ z2.im [ZMOD 8])
    (htw : Work.FIArea7.twCorr z1 z2 = 1)
    (hr1 : z1.re ≠ 0) (hr2 : z2.re ≠ 0) (hD : 0 < Work.FIPlan.absDelta z1 z2) :
    Work.FIArea7.ratioSym z1 z2 (Work.FIPlan.absDelta z1 z2)
      = Work.FIArea7.reflSign z1 z2
        * (jacobiSym z1.im z1.re.natAbs * jacobiSym z2.im z2.re.natAbs) := by
  have hd : Work.FIPlan.absDelta z1 z2 ≠ 0 := Nat.pos_iff_ne_zero.mp hD
  have NeZero_absDelta : NeZero (Work.FIPlan.absDelta z1 z2) := ⟨hd⟩
  haveI := NeZero_absDelta
  -- `z₁ ≡ z₂ (mod 8)` is in particular a congruence mod 4
  have h4r : z1.re ≡ z2.re [ZMOD 4] := Int.ModEq.of_dvd (by norm_num) h8r
  have h4i : z1.im ≡ z2.im [ZMOD 4] := Int.ModEq.of_dvd (by norm_num) h8i
  have hcop : Nat.Coprime (Work.FIPlan.gnorm z1) (Work.FIPlan.absDelta z1 z2) := by
    have h1 : Int.gcd (((Work.FIPlan.gnorm z1 : ℕ)) : ℤ)
        (((Work.FIPlan.absDelta z1 z2 : ℕ)) : ℤ) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcc
    rw [Int.gcd_natCast_natCast] at h1
    exact h1
  -- **(1)** the arithmetic core of Lemma 17.1 at the frozen symbol `J(Re(z̄₁z₂))`
  have hcore :=
    jacobiSym_reflection_mod4_general hP1 hP2 hs1 hs2 hc hcc h4r h4i hr1 hr2 hD
  rw [← Work.FIArea7.re_star_mul_coords] at hcore
  -- **(2)** on the diagonal classes mod 8 the `2`-adic correction is trivial
  have htw' : (Work.FIArea7.kronTwo ((star z1 * z2).re)
        * Work.FIArea7.kronTwo ((Work.FIPlan.gnorm z1 : ℕ) : ℤ))
        ^ ((Work.FIPlan.absDelta z1 z2).factorization 2) = 1 := by
    simpa only [Work.FIArea7.twCorr] using htw
  rw [htw', one_mul] at hcore
  -- **(3)** the passage from the frozen to the ratio symbol
  have hA := jacobiSym_re_eq_ratioSym_mul z1 z2 hcop
  -- **(4)** `J(|z₁|²)² = 1`
  have hB2 : jacobiSym (((Work.FIPlan.gnorm z1 : ℕ) : ℤ)) (Work.FIPlan.absDelta z1 z2) ^ 2
      = 1 := by
    apply jacobiSym.sq_one
    rw [Int.gcd_natCast_natCast]
    exact hcop
  have hBB : jacobiSym (((Work.FIPlan.gnorm z1 : ℕ) : ℤ)) (Work.FIPlan.absDelta z1 z2)
      * jacobiSym (((Work.FIPlan.gnorm z1 : ℕ) : ℤ)) (Work.FIPlan.absDelta z1 z2) = 1 := by
    rw [← pow_two]
    exact hB2
  have key : Work.FIArea7.ratioSym z1 z2 (Work.FIPlan.absDelta z1 z2)
      * jacobiSym (((Work.FIPlan.gnorm z1 : ℕ) : ℤ)) (Work.FIPlan.absDelta z1 z2)
      * jacobiSym (((Work.FIPlan.gnorm z1 : ℕ) : ℤ)) (Work.FIPlan.absDelta z1 z2)
      = Work.FIArea7.reflSign z1 z2
        * (jacobiSym z1.im z1.re.natAbs * jacobiSym z2.im z2.re.natAbs) := by
    rw [← hA]
    exact hcore
  rw [mul_assoc, hBB, mul_one] at key
  exact key

end Work.FIArea7

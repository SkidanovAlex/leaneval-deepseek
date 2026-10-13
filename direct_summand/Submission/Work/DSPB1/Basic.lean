import Submission.Work.DSMap.Mix

/-!
# DSPB1 — perfectoid basics: the pseudo-uniformizer `ϖ` and its tilt

This is the base layer of the subproject `DSPB1` of the direct-summand development
(the `PB`-nodes of `sources/dsmap/direct_summand_mix_design.md`).  The frozen vocabulary
(`DSMap.PerfectoidData`, `DSMap.Mix.*`, `PreTilt`) lives in the read-only files
`Submission/Work/DSMap/Map.lean` and `Submission/Work/DSMap/Mix.lean` and is imported,
never redefined.

A `DSMap.PerfectoidData p C` is a `p`-torsion-free `p`-adically complete ring `C` with a
compatible system of `p`-power roots `P.ϖ : ℕ → C` of a pseudo-uniformizer, i.e.
`P.ϖ (k+1) ^ p = P.ϖ k` (`P.root`) and `P.ϖ 0 ^ p = p * v` for a unit `v` (`P.unit`),
together with Frobenius-surjectivity and Frobenius-injectivity mod `p` (`P.frobSurj`,
`P.frobInj`).

## Contents of this file

* `Work.DSPB1.varpi_pow_iterate` — `ϖ_{k+n}^{p^n} = ϖ_k`;
* `Work.DSPB1.varpiTilt` — **the tilt of `ϖ`**: the compatible system `n ↦ ϖ_n mod p`,
  an element of `PreTilt C p = Perfection (C ⧸ (p)) p`, with coefficient API
  `Work.DSPB1.coeff_varpiTilt`;
* `Work.DSPB1.varpiTilt_untilt` — **the ϖ-flatness statement (PB1)**: the Teichmüller
  untilt map `PreTilt.untilt` sends `varpiTilt P` back to `ϖ_0` *exactly* (not only mod `p`);
* `Work.DSPB1.varpiTiltShift`, its coefficients, and `Work.DSPB1.varpiTiltShift_untilt`:
  the same statement with `ϖ_0` replaced by `ϖ_k` for any `k`.

The main deliverable of the area, `DSMap.Mix.perfectoid_varpiFlat_proved`, is assembled
from these in `Submission/Work/DSPB1/Main.lean`.
-/

set_option linter.style.haveILetI false

namespace Work.DSPB1

universe a

/-! ## The powers of `ϖ` -/

section Varpi

variable {p : ℕ} {C : Type a} [CommRing C]

/-- The defining property of the pseudo-uniformizer: `ϖ_{k+1}` is a `p`-th root of `ϖ_k`. -/
@[simp] theorem varpi_pow_p (P : DSMap.PerfectoidData p C) (k : ℕ) :
    P.ϖ (k + 1) ^ p = P.ϖ k :=
  P.root k

/-- `ϖ_{k+n}` is a `p^n`-th root of `ϖ_k`: the tower property of the pseudo-uniformizer. -/
theorem varpi_pow_iterate (P : DSMap.PerfectoidData p C) (k n : ℕ) :
    P.ϖ (k + n) ^ p ^ n = P.ϖ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc P.ϖ (k + (n + 1)) ^ p ^ (n + 1)
        = (P.ϖ (k + n + 1) ^ p) ^ p ^ n := by rw [Nat.add_succ, pow_succ', pow_mul]
      _ = P.ϖ (k + n) ^ p ^ n := by
            rw [show P.ϖ (k + n + 1) ^ p = P.ϖ (k + n) from P.root (k + n)]
      _ = P.ϖ k := ih

/-- The `n`-th root of the pseudo-uniformizer is a `p^n`-th root of `ϖ_0`. -/
theorem varpi_pow_iterate_zero (P : DSMap.PerfectoidData p C) (n : ℕ) :
    P.ϖ n ^ p ^ n = P.ϖ 0 := by
  simpa using varpi_pow_iterate P 0 n

end Varpi

/-! ## The tilt `ϖ♭` -/

section Tilt

variable {p : ℕ} [Fact p.Prime] {C : Type a} [CommRing C] [Fact ¬IsUnit (p : C)]

/-- **The tilt of the pseudo-uniformizer**: the compatible system `n ↦ ϖ_n mod p`, viewed as
an element of `PreTilt C p = Perfection (C ⧸ (p)) p`.  The compatibility
`(ϖ_{k+1} mod p)^p = ϖ_k mod p` is exactly `P.root`. -/
def varpiTilt (P : DSMap.PerfectoidData p C) : PreTilt C p :=
  ⟨fun n => Ideal.Quotient.mk (Ideal.span {(p : C)}) (P.ϖ n), fun n => by
    rw [← map_pow, P.root n]⟩

/-- The `n`-th coefficient of `varpiTilt P` is `ϖ_n` mod `p`. -/
@[simp] theorem coeff_varpiTilt (P : DSMap.PerfectoidData p C) (n : ℕ) :
    PreTilt.coeff n (varpiTilt P) =
      Ideal.Quotient.mk (Ideal.span {(p : C)}) (P.ϖ n) := rfl

/-- **PB1, ϖ-flatness**: the Teichmüller untilt of `varpiTilt P` is *exactly* `ϖ_0`.

The element `untilt x = teichmuller x` is characterised (`Perfection.teichmuller_spec`) as the
`p`-adic limit of the `p^n`-th powers of lifts of the coefficients `coeff n x`: if
`z ≡ coeff n x mod p` then `z ^ p ^ n ≡ untilt x mod p ^ (n+1)`.  For `x = varpiTilt P` the
lift `P.ϖ n` of `coeff n (varpiTilt P)` has `p^n`-th power exactly `P.ϖ 0` for every `n`
(`varpi_pow_iterate_zero`), so the limit is `P.ϖ 0`. -/
theorem varpiTilt_untilt (P : DSMap.PerfectoidData p C) :
    letI := P.complete
    PreTilt.untilt (varpiTilt P) = P.ϖ 0 := by
  letI := P.complete
  show Perfection.teichmuller p (Ideal.span {(p : C)}) (varpiTilt P) = P.ϖ 0
  refine Perfection.teichmuller_spec fun n => ⟨P.ϖ n, rfl, ?_⟩
  rw [varpi_pow_iterate_zero P n]

/-- The shifted tilt `n ↦ ϖ_{k+n} mod p ∈ PreTilt C p`: it flattens the `k`-th root `ϖ_k`.
For `k = 0` this is `varpiTilt`. -/
def varpiTiltShift (P : DSMap.PerfectoidData p C) (k : ℕ) : PreTilt C p :=
  ⟨fun n => Ideal.Quotient.mk (Ideal.span {(p : C)}) (P.ϖ (k + n)), fun n => by
    rw [← map_pow, show k + (n + 1) = (k + n) + 1 from by omega, P.root (k + n)]⟩

/-- The `n`-th coefficient of the shifted tilt is `ϖ_{k+n}` mod `p`. -/
@[simp] theorem coeff_varpiTiltShift (P : DSMap.PerfectoidData p C) (k n : ℕ) :
    PreTilt.coeff n (varpiTiltShift P k) =
      Ideal.Quotient.mk (Ideal.span {(p : C)}) (P.ϖ (k + n)) := rfl

/-- The shifted tilt for `k = 0` is the tilt of `ϖ`. -/
theorem varpiTiltShift_zero (P : DSMap.PerfectoidData p C) :
    varpiTiltShift P 0 = varpiTilt P := by
  have h : ∀ n, PreTilt.coeff n (varpiTiltShift P 0) = PreTilt.coeff n (varpiTilt P) :=
    fun n => by rw [coeff_varpiTiltShift, coeff_varpiTilt, Nat.zero_add]
  exact Perfection.ext h

/-- The shifted tilt is the `k`-th Frobenius root of the tilt of `ϖ`. -/
theorem varpiTiltShift_eq_symm (P : DSMap.PerfectoidData p C) (k : ℕ) :
    varpiTiltShift P k = (frobeniusEquiv (PreTilt C p) p).symm^[k] (varpiTilt P) := by
  have h : ∀ n, PreTilt.coeff n (varpiTiltShift P k) =
      PreTilt.coeff n ((frobeniusEquiv (PreTilt C p) p).symm^[k] (varpiTilt P)) := fun n => by
    rw [coeff_varpiTiltShift, PreTilt.coeff_iterate_frobeniusEquiv_symm, coeff_varpiTilt,
      Nat.add_comm]
  exact Perfection.ext h

/-- **PB1 for every level**: the `k`-th root `ϖ_k` is also the exact Teichmüller untilt of an
element of the tilt, namely the shifted tilt `varpiTiltShift P k`. -/
theorem varpiTiltShift_untilt (P : DSMap.PerfectoidData p C) (k : ℕ) :
    letI := P.complete
    PreTilt.untilt (varpiTiltShift P k) = P.ϖ k := by
  letI := P.complete
  show Perfection.teichmuller p (Ideal.span {(p : C)}) (varpiTiltShift P k) = P.ϖ k
  refine Perfection.teichmuller_spec fun n => ⟨P.ϖ (k + n), rfl, ?_⟩
  rw [varpi_pow_iterate P k n]

/-- Characterisation of the tilt of `ϖ` by its coefficients: the elimination principle by which
consumers compare `varpiTilt P` with other elements of `C♭`. -/
theorem varpiTilt_eq_iff (P : DSMap.PerfectoidData p C) (x : PreTilt C p) :
    x = varpiTilt P ↔ ∀ n, PreTilt.coeff n x =
      Ideal.Quotient.mk (Ideal.span {(p : C)}) (P.ϖ n) := by
  constructor
  · intro h n; rw [h, coeff_varpiTilt]
  · intro h; exact Perfection.ext h

/-- Reduction of `♯(ϖ♭)` mod `p`: it is the class of `ϖ_0` (a weaker form of
`varpiTilt_untilt`, which is the equality in `C`). -/
theorem mk_untilt_varpiTilt (P : DSMap.PerfectoidData p C) :
    letI := P.complete
    Ideal.Quotient.mk (Ideal.span {(p : C)}) (PreTilt.untilt (varpiTilt P)) =
      Ideal.Quotient.mk (Ideal.span {(p : C)}) (P.ϖ 0) := by
  letI := P.complete
  rw [varpiTilt_untilt P]

end Tilt

end Work.DSPB1

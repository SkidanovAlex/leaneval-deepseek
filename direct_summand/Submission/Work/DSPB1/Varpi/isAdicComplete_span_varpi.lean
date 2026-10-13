import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSPB1.Basic

/-!
# `C` is `ϖ_k`-adically complete

For a `p`-torsion-free, `p`-adically complete ring `C` with pseudo-uniformizer data
`P : DSMap.PerfectoidData p C` (`P.ϖ 0 ^ p = p * unit`, `P.ϖ (k+1) ^ p = P.ϖ k`) the
powers of `ϖ k` are *cofinal* with the powers of `p`: more precisely

  `(span {ϖ k}) ^ (p ^ (k+1)) = span {p}`

because `(ϖ k) ^ (p ^ k) = ϖ 0` (`Work.DSPB1.varpi_pow_iterate_zero`) and
`(ϖ 0) ^ p = p * v` with `v` a unit.  Consequently the `span {ϖ k}`-adic topology and the
`p`-adic topology agree, and `C` is complete for the former since it is complete for the
latter.

The cofinality statement for an arbitrary ideal (if `I = J ^ N`, `N > 0`, then
`I`-adic completeness implies `J`-adic completeness) is `isAdicComplete_of_pow_eq`.
-/

namespace Work.DSPB1.Varpi

variable {R : Type*} [CommRing R]

/-- If `R` is complete for the `J ^ N`-adic topology with `N > 0`, it is complete for the
`J`-adic topology: the two filtrations `(J ^ N)^n = J ^ (N * n)` and `J ^ n` are cofinal.

Hausdorff: `⋂ n, J ^ n ⊆ ⋂ n, J ^ (N * n) = ⋂ n, (J ^ N) ^ n = 0`.
Precomplete: given a `J`-Cauchy sequence `f`, the subsequence `n ↦ f (N * n)` is
`J ^ N`-Cauchy, so it has a limit `L`; interpolating, `f n ≡ f (N * n) ≡ L` modulo `J ^ n`
because `J ^ (N * n) ≤ J ^ n`. -/
theorem isAdicComplete_of_pow_eq (J : Ideal R) (N : ℕ) (hN : 0 < N)
    (h : IsAdicComplete (J ^ N) R) : IsAdicComplete J R := by
  rw [isAdicComplete_iff] at h ⊢
  refine ⟨?_, ?_⟩
  · rw [isHausdorff_iff] at h ⊢
    intro x hx
    exact h.1 x fun n => by simpa [pow_mul] using hx (N * n)
  · rw [isPrecomplete_iff] at h ⊢
    intro f hf
    obtain ⟨L, hL⟩ := h.2 (fun n => f (N * n)) fun {m n} hmn => by
      simpa [pow_mul] using hf (Nat.mul_le_mul_left N hmn)
    refine ⟨L, fun n => ?_⟩
    have h1 : f n ≡ f (N * n) [SMOD (J ^ n • ⊤ : Submodule R R)] :=
      hf (Nat.le_mul_of_pos_left n hN)
    have h2 : f (N * n) ≡ L [SMOD (J ^ (N * n) • ⊤ : Submodule R R)] := by
      simpa [pow_mul] using hL n
    exact h1.trans (SModEq.mono (Submodule.smul_mono_left
      (Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left n hN))) h2)

/-- For a perfectoid ring `C`, the `ϖ_k`-adic topology is the `p`-adic topology:
`(span {ϖ_k}) ^ (p ^ (k+1)) = span {p}`. -/
theorem span_varpi_pow_eq_span_p {p : ℕ} [Fact p.Prime] {C : Type*} [CommRing C]
    (P : DSMap.PerfectoidData p C) (k : ℕ) :
    (Ideal.span {P.ϖ k}) ^ p ^ (k + 1) = Ideal.span {(p : C)} := by
  obtain ⟨v, hv⟩ := P.unit
  have hpow : P.ϖ k ^ p ^ (k + 1) = (p : C) * (v : C) := by
    rw [pow_succ, pow_mul, varpi_pow_iterate_zero P k, hv]
  rw [Ideal.span_singleton_pow, hpow,
    Ideal.span_singleton_mul_right_unit (Units.isUnit v)]

/-- **A perfectoid ring is `ϖ_k`-adically complete for every `k`.** -/
theorem isAdicComplete_span_varpi {p : ℕ} [Fact p.Prime] {C : Type*} [CommRing C]
    (P : DSMap.PerfectoidData p C) (k : ℕ) : IsAdicComplete (Ideal.span {P.ϖ k}) C := by
  refine isAdicComplete_of_pow_eq (Ideal.span {P.ϖ k}) (p ^ (k + 1))
    (pow_pos (Fact.out : p.Prime).pos (k + 1)) ?_
  rw [span_varpi_pow_eq_span_p P k]
  exact P.complete

end Work.DSPB1.Varpi

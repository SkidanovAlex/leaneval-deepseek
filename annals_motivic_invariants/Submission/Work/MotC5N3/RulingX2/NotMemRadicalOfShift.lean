import Mathlib
import Submission.Work.MotAS.ASResidual

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.RulingX2.NotMemRadicalOfShift`

Two general commutative-algebra steps, forked into this directory from
`Submission/Work/MotAS/ASRulV2/X2_notMem_radical.lean` (where they are proved) so that the
`X₂ = 1` chart route to `X 2 ∉ √(ZIAS a b g)` does **not** have to import that module — its
transitive imports (`ASRulV2/zias_ne_top_AS`, `MotAS/ZiasNeTop`, the `MotAS/ZiasNe*` family) are a
work in progress and one of them does not compile; nothing of that route is used here.  The two
statements and their proofs are verbatim (the only change is the namespace).

* `notMem_radical_of_mem_minimalPrimes` — `x ∉ √Z` from `x` avoiding every minimal prime of a
  proper `Z`;
* `notMem_radical_of_shift_ne_top` — the *chart* step: if `Z ⊔ (X 2 - C c)` is proper with
  `c ≠ 0`, then `X 2 ∉ √Z` (a maximal ideal above `Z ⊔ (X 2 - C c)` contains `Z` and misses `X 2`).
-/

set_option autoImplicit false

namespace Work.MotC5N3.RulingX2

/-- **The radical is the intersection of the minimal primes.**  If `x` lies in no minimal prime of
a proper ideal `Z`, then `x ∉ √Z`. -/
theorem notMem_radical_of_mem_minimalPrimes {K : Type*} [Field K]
    (Z : Ideal (MvPolynomial (Fin 3) K)) (x : MvPolynomial (Fin 3) K) (hZ : Z ≠ ⊤)
    (h : ∀ 𝔭 ∈ Z.minimalPrimes, x ∉ 𝔭) :
    x ∉ Ideal.radical Z := by
  intro hx
  rw [← Ideal.sInf_minimalPrimes] at hx
  obtain ⟨𝔭, h𝔭⟩ := Ideal.nonempty_minimalPrimes hZ
  exact h 𝔭 h𝔭 (Ideal.mem_sInf.mp hx h𝔭)

/-- **The chart step.**  If `Z ⊔ (X 2 - C c)` is a proper ideal and `c ≠ 0`, then `X 2` is not in
the radical of `Z`: a maximal ideal above `Z ⊔ (X 2 - C c)` is a prime containing `Z` and missing
`X 2` (as `C c` would otherwise be a unit of it). -/
theorem notMem_radical_of_shift_ne_top {K : Type*} [Field K]
    (Z : Ideal (MvPolynomial (Fin 3) K)) (c : K) (hc : c ≠ 0)
    (h : Z ⊔ Ideal.span {(MvPolynomial.X 2 - MvPolynomial.C c)} ≠ ⊤) :
    (MvPolynomial.X 2 : MvPolynomial (Fin 3) K) ∉ Ideal.radical Z := by
  obtain ⟨M, hMmax, hMle⟩ := Ideal.exists_le_maximal _ h
  haveI := hMmax.isPrime
  have hZ : Z ≤ M := le_trans le_sup_left hMle
  have hrad : Ideal.radical Z ≤ M := hMmax.isPrime.radical_le_iff.mpr hZ
  intro hX2rad
  have hX2M : MvPolynomial.X 2 ∈ M := hrad hX2rad
  have hsub : (MvPolynomial.X 2 - MvPolynomial.C c) ∈ M :=
    le_trans le_sup_right hMle (Ideal.subset_span (Set.mem_singleton _))
  have hCc : (MvPolynomial.C c : MvPolynomial (Fin 3) K) ∈ M := by
    have h := sub_mem hX2M hsub
    simpa using h
  have hunit : IsUnit (MvPolynomial.C c : MvPolynomial (Fin 3) K) := by
    rw [isUnit_iff_exists_inv]
    exact ⟨MvPolynomial.C c⁻¹, by rw [← map_mul, mul_inv_cancel₀ hc, map_one]⟩
  exact hMmax.ne_top (Ideal.eq_top_of_isUnit_mem M hCc hunit)

end Work.MotC5N3.RulingX2

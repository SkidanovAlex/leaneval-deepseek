import Mathlib.Algebra.Lie.Sl2
import Mathlib.RingTheory.SimpleRing.Principal

set_option linter.unusedVariables false

namespace Commons.Algebra.Lie.Sl2

open LieModule

/-- **The string through a primitive vector of a locally nilpotent `𝔰𝔩₂`-module is finite of length
`μ + 1`.**

Let `(h, e, f)` be an `sl₂`-triple acting on a module `M` over a field `R` of characteristic zero,
and suppose that `e` and `f` act *locally nilpotently* on `M`.  If `0 ≠ m ∈ M` is primitive of
weight `μ` (that is `⁅e, m⁆ = 0` and `⁅h, m⁆ = μ • m`), then the `f`-string through `m` has length
`μ + 1`: with `N` the smallest integer with `f^N m = 0` one has `N > 0`, `(N : R) = μ + 1`, and
`f^k m ≠ 0` for every `k < N`.

The point is that in a module where both `e` and `f` are locally nilpotent the weight multiplicities
along each `h`-string are finite, which is the finiteness statement needed to run string/Weyl-group
arguments on the adjoint representation of a Serre-constructed Lie algebra (the Serre relations make
`ad eᵢ` and `ad fᵢ` locally nilpotent). -/
theorem string_of_locallyNilpotent {R L M : Type*} [Field R] [CharZero R] [LieRing L]
    [LieAlgebra R L] [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
    {h e f : L} (t : IsSl2Triple h e f)
    (he : ∀ m : M, ∃ n : ℕ, ((LieModule.toEnd R L M e)^n) m = 0)
    (hf : ∀ m : M, ∃ n : ℕ, ((LieModule.toEnd R L M f)^n) m = 0)
    (m : M) (hm : m ≠ 0) (hem : ⁅e, m⁆ = 0) (μ : R) (hμm : ⁅h, m⁆ = μ • m) :
    ∃ N : ℕ, 0 < N ∧ (N : R) = μ + 1 ∧ ((LieModule.toEnd R L M f)^N) m = 0 ∧
      ∀ k : ℕ, k < N → ((LieModule.toEnd R L M f)^k) m ≠ 0 := by
  classical
  let P : IsSl2Triple.HasPrimitiveVectorWith t m μ := ⟨hm, hμm, hem⟩
  have hN0 : ((LieModule.toEnd R L M f)^(Nat.find (hf m))) m = 0 := Nat.find_spec (hf m)
  have hNmin : ∀ k < Nat.find (hf m), ((LieModule.toEnd R L M f)^k) m ≠ 0 :=
    fun k hk => Nat.find_min (hf m) hk
  have hNpos : 0 < Nat.find (hf m) := by
    rcases Nat.eq_zero_or_pos (Nat.find (hf m)) with h | h
    · exfalso
      have h' : m = 0 := by simpa [h] using hN0
      exact hm h'
    · exact h
  refine ⟨Nat.find (hf m), hNpos, ?_, hN0, hNmin⟩
  obtain ⟨n, hn⟩ : ∃ n, Nat.find (hf m) = n + 1 := ⟨Nat.find (hf m) - 1, by omega⟩
  have hvne : ((LieModule.toEnd R L M f)^n) m ≠ 0 := by
    apply hNmin n
    omega
  have hN0' : ((LieModule.toEnd R L M f)^(n + 1)) m = 0 := by rw [← hn]; exact hN0
  have hle := P.lie_e_pow_succ_toEnd_f n
  rw [hN0', lie_zero] at hle
  have hc0 : ((n : R) + 1) * (μ - (n : R)) = 0 :=
    (eq_zero_or_eq_zero_of_smul_eq_zero hle.symm).resolve_right hvne
  have hne0 : ((n : R) + 1) ≠ 0 := by
    rw [← Nat.cast_one, ← Nat.cast_add]
    exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hμ : μ = (n : R) := sub_eq_zero.mp ((mul_eq_zero.mp hc0).resolve_left hne0)
  rw [hn, hμ]
  push_cast
  ring

end Commons.Algebra.Lie.Sl2
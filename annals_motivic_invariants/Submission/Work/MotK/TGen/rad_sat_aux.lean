/-
# `rad_sat_aux`: `zA` is a non-zero-divisor modulo the radical of `ZI`

Target: `∀ f, (∃ n, zA^n * f ∈ √(ZI)) → f ∈ √(ZI)`.

The proof is the assembly of two inputs:

* `ZI ≤ ker zPsi` (`ZI_le_ker_zPsi`, `ZPlaneModel.lean`) together with primality of the kernel
  gives `√(ZI) ≤ ker zPsi`;
* the geometric input `ker zPsi ≤ √(ZI)` — no irreducible component of the curve `V(ZI)` lies in
  the divisor `{zA = 0}` — which is `kernel_le_radical` from `kernel_le_radical.lean`
  (there proved via `ker zPsi = (zB,zg) : zA^∞`, `zA_saturation_iff`,
  `zJ_zA_cancel`, `zJ ≤ ZI`).

So `√(ZI) = ker zPsi`.  Finally `ker zPsi` is prime and `zA ∉ ker zPsi`
(`zPsi zA = za1 ≠ 0`), so an induction on `n` gives the claim.
-/
import Mathlib
import Submission.Work.MotK.TGen.ZPlaneDefs
import Submission.Work.MotK.TGen.ker_zPsi_eq_saturation
import Submission.Work.MotK.TGen.kernel_le_radical

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type} [Field K]

/-- `zA ∉ ker zPsi`, because `zPsi zA = za1 ≠ 0` (the class of `zpA` in `ZD` is a non-zero-divisor,
being the class of an irreducible plane polynomial). -/
theorem zA_notMem_ker_zPsi (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0)
    [IsDomain (Work.MotK.TGen.ZD K a b h)] :
    zA K a b h ∉ RingHom.ker (zPsi K a b h) := by
  intro hmem
  exact za1_ne_zero (K := K) a b h ha hb hh (by rw [← zPsi_zA K a b h]; exact hmem)

theorem rad_sat_aux (K : Type) [Field K] (a b h : K) [IsDomain (Work.MotK.TGen.ZD K a b h)] (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) : ∀ f : MvPolynomial (Fin 3) K, (∃ n : ℕ, (Work.MotK.TGen.zA K a b h)^n * f ∈ Ideal.radical (Work.MotK.TwCensus.ZI a b h)) → f ∈ Ideal.radical (Work.MotK.TwCensus.ZI a b h) := by
  intro f hf
  -- `√(ZI) ≤ ker zPsi`: `ZI ≤ ker zPsi` and `ker zPsi` is prime.
  have hker_le : Ideal.radical (Work.MotK.TwCensus.ZI a b h) ≤ RingHom.ker (zPsi K a b h) := by
    intro x hx
    obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.mp hx
    exact (RingHom.ker_isPrime (zPsi K a b h)).mem_of_pow_mem m
      (ZI_le_ker_zPsi K a b h ha hb hh hm)
  -- `ker zPsi ≤ √(ZI)`: the geometric input.
  have hker_ge : RingHom.ker (zPsi K a b h) ≤ Ideal.radical (Work.MotK.TwCensus.ZI a b h) :=
    kernel_le_radical K a b h ha hb hh
  have hrad : Ideal.radical (Work.MotK.TwCensus.ZI a b h) = RingHom.ker (zPsi K a b h) :=
    le_antisymm hker_le hker_ge
  have hzA : zA K a b h ∉ RingHom.ker (zPsi K a b h) := zA_notMem_ker_zPsi a b h ha hb hh
  -- `ker zPsi` is prime and `zA ∉ ker zPsi`; induction on `n`.
  obtain ⟨n, hn⟩ := hf
  rw [hrad] at hn ⊢
  induction n with
  | zero => simpa using hn
  | succ n ih =>
    rw [pow_succ', mul_assoc] at hn
    rcases ((RingHom.ker_isPrime (zPsi K a b h)).mem_or_mem hn) with h1 | h1
    · exact absurd h1 hzA
    · exact ih h1

end Work.MotK.TGen

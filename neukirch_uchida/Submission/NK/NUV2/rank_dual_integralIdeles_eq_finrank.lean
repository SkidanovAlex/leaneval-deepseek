import Mathlib
import Submission.NK.RankTheoryDeep.All
import Submission.NK.NUV2.localUnits_two
import Submission.NK.NUV2.ideleDefs
import Submission.NK.NUV2.rank_pi_ge_sum

/-!
# `rank_{ℤ₂} Hom_cts(∏_v 𝒪_vˣ, ℤ₂) = [K : ℚ]`

The `ℤ_2`-rank of the continuous character module of the integral idèles
`𝕀_int = ∏_v 𝒪_vˣ` is the degree `[K : ℚ]` of the number field.

Both inequalities are proved here:

* `≤` : `NK.RankTheoryDeep.rank_dual_integralIdeles_le` (CoNF (10.3.20)), using the local unit
  structure at `2` (`NK.NUV2.localUnits_two`);
* `≥` : the characters of the local units at the places `q | 2` push forward to characters of
  `𝕀_int` (`NK.NUV2.pushForward`, `NK.NUV2.Phi_injective`), and their ranks add up over the
  finitely many places above `2` (`NK.NUV2.sum_rank_le_rank_pi`); the hypothesis `h` bounds each
  local rank below by the local degree `e_q f_q`, and `∑_{q | 2} e_q f_q = [K : ℚ]`
  (`NK.RankTheoryDeep.sum_localDeg_eq_finrank`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField

namespace NK.NUV2

open NK.GlobalCFT

theorem rank_dual_integralIdeles_eq_finrank (K : Type) [Field K] [NumberField K]
    (h : ∀ (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      q.asIdeal.LiesOver (Ideal.span {(2 : ℤ)}) →
      ((q.asIdeal.ramificationIdx ℤ * q.asIdeal.inertiaDeg ℤ : ℕ) : Cardinal) ≤
        Module.rank (PadicInt 2)
          (NK.Reconstruct.Dual
            (↥(NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite q))) 2)) :
    Module.rank (PadicInt 2)
        (NK.Reconstruct.Dual (↥(NK.GlobalCFT.Idele.integralIdeles K)) 2)
      = (Module.finrank ℚ K : Cardinal) := by
  classical
  -- `(2)` is a maximal ideal of `ℤ`; this instance is what makes the finiteness of the set of
  -- primes of `𝓞 K` above `2` available (the general instance is stated for `Ideal.span {ℓ}`
  -- with `ℓ` a variable prime, and its unification with the numeral `2` needs the hint).
  haveI hmax : (Ideal.span {(2 : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 2
  -- **Upper bound**: `IdeleAssembly`.
  have hupper : Module.rank (PadicInt 2)
      (NK.Reconstruct.Dual (↥(NK.GlobalCFT.Idele.integralIdeles K)) 2)
      ≤ (Module.finrank ℚ K : Cardinal) :=
    NK.RankTheoryDeep.rank_dual_integralIdeles_le K NK.NUV2.localUnits_two
  -- the finset of finite places of `K` above `2`
  let S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
    (Finset.univ : Finset ↥((Ideal.span {(2 : ℤ)}).primesOver (𝓞 K))).image
      (NK.RankTheoryDeep.primeOfOver K)
  have hmem : ∀ q ∈ S, q.asIdeal.LiesOver (Ideal.span {(2 : ℤ)}) := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨a, -, rfl⟩ := hq
    exact a.2.2
  have hinj : ∀ x ∈ (Finset.univ : Finset ↥((Ideal.span {(2 : ℤ)}).primesOver (𝓞 K))),
      ∀ y ∈ (Finset.univ : Finset ↥((Ideal.span {(2 : ℤ)}).primesOver (𝓞 K))),
        NK.RankTheoryDeep.primeOfOver K x = NK.RankTheoryDeep.primeOfOver K y → x = y := by
    intro x _ y _ hxy
    exact Subtype.ext (congrArg (fun q => q.asIdeal) hxy)
  -- `∑_{q | 2} e_q f_q = [K : ℚ]`
  have hsum_nat : ∑ q ∈ S, (q.asIdeal.ramificationIdx ℤ * q.asIdeal.inertiaDeg ℤ)
      = Module.finrank ℚ K := by
    rw [Finset.sum_image hinj]
    exact NK.RankTheoryDeep.sum_localDeg_eq_finrank K
  have hsum : (∑ q ∈ S,
        (((q.asIdeal.ramificationIdx ℤ * q.asIdeal.inertiaDeg ℤ : ℕ)) : Cardinal))
      = (Module.finrank ℚ K : Cardinal) := by
    rw [← Nat.cast_sum, hsum_nat]
  -- **Lower bound**.
  have hprod : (∑ q ∈ S, Module.rank (PadicInt 2)
        (NK.Reconstruct.Dual
          (↥(NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite q))) 2))
      ≤ Module.rank (PadicInt 2)
        (NK.Reconstruct.Dual (↥(NK.GlobalCFT.Idele.integralIdeles K)) 2) := by
    calc (∑ q ∈ S, Module.rank (PadicInt 2)
          (NK.Reconstruct.Dual
            (↥(NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite q))) 2))
        ≤ Module.rank (PadicInt 2)
            ((q : {q : IsDedekindDomain.HeightOneSpectrum (𝓞 K) // q ∈ S}) →
              NK.Reconstruct.Dual
                (↥(NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite q))) 2) :=
          sum_rank_le_rank_pi S (fun q => NK.Reconstruct.Dual
            (↥(NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite q))) 2)
      _ ≤ Module.rank (PadicInt 2)
            (NK.Reconstruct.Dual (↥(NK.GlobalCFT.Idele.integralIdeles K)) 2) :=
          LinearMap.rank_le_of_injective (Phi (K := K) S) (Phi_injective S)
  refine le_antisymm hupper ?_
  calc (Module.finrank ℚ K : Cardinal)
      = (∑ q ∈ S,
          (((q.asIdeal.ramificationIdx ℤ * q.asIdeal.inertiaDeg ℤ : ℕ)) : Cardinal)) := hsum.symm
    _ ≤ (∑ q ∈ S, Module.rank (PadicInt 2)
          (NK.Reconstruct.Dual
            (↥(NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite q))) 2)) :=
        Finset.sum_le_sum (fun q hq => h q (hmem q hq))
    _ ≤ Module.rank (PadicInt 2)
          (NK.Reconstruct.Dual (↥(NK.GlobalCFT.Idele.integralIdeles K)) 2) := hprod

end NK.NUV2

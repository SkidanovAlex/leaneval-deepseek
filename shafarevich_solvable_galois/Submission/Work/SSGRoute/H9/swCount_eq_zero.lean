import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.EscapeCoreLib.correctionFromPrime
import Submission.Work.SSGRoute.H9.swPairingValueFrob
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Unramified Kummer level forces `p ∣ v(b)`

The classical fact used in §5/§6 of `H9/NOTE_chain_paper_verbatim.md` to kill the `S`-terms of the
two-place reciprocity: if the Kummer extension `K(b^{1/p})` is *unramified* at a height-one prime
`𝔮` of `K`, then `p` divides the `𝔮`-adic valuation of `b`, i.e. `count_𝔮(b) ≡ 0 (mod p)`.

The proof is the contrapositive of `dvd_ramificationIdx_of_val_log_notMem_pow` (proved in
`Work.SSGRoute.ZDataMup.LocalUnramified`): if `p ∤ v_𝔮(b)` then every prime `P` above `𝔮` in the
Kummer level has `p ∣ e(P|𝔮)`, so `e ≠ 1` and the extension is ramified at `P`.
-/

open scoped Pointwise

namespace Work.SSGRoute.H9

open _root_.SSGRoute
open Work.SSGRoute.ZDataMup.LTRecFamHonest
open Work.SSGRoute.ZDataMup

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- **An unramified Kummer level forces `p ∣ v_𝔮(b)`.**  Let `K` be a number field, `b ∈ Kˣ`, `p` a
prime, and `𝔮` a height-one prime of `𝓞 K` at which the Kummer extension `K(b^{1/p})` is unramified.
Then the `𝔮`-adic valuation of `b` is divisible by `p`, i.e. the `𝔮`-count of `b` vanishes in
`ZMod p`. -/
theorem swCount_eq_zero_of_isUnramifiedIn_hLevel {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (b : (↥K)ˣ)
    [FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) b)]
    [IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) b)]
    [NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) b)]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (hunr : NK.HeckeL.IsUnramifiedIn (K := ↥K)
      (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) b)) 𝔮) :
    ((FractionalIdeal.count ↥K 𝔮 (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (b : ↥K)) : ℤ) : ZMod p) = 0 := by
  classical
  by_contra hcon
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hcon
  have hdvd : ¬ (p : ℤ) ∣
      (IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔮 (b : ↥K)).log := by
    rw [Work.SSGRoute.EscapeCoreLib.count_spanSingleton_eq_neg_log (K := ↥K) 𝔮 (Units.ne_zero b)]
      at hcon
    exact fun h => hcon (by simpa using dvd_neg.mpr h)
  obtain ⟨P, hP⟩ := Work.SSGRoute.ZDataMup.exists_heightOneSpectrum_liesOver
    (K := ↥K) (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) b)) 𝔮
  haveI : P.asIdeal.LiesOver 𝔮.asIdeal := hP
  have hmem : Work.SSGRoute.kummerSqrtZMod (K := ↥K) (Ω := Ω) p b ∈
      hLevel (Ω := Ω) (K := K) (p := p) b :=
    NK.LocalAnabelian.mem_kummerField_of_pow_eq (K' := Ω)
      (Work.SSGRoute.kummerSqrtZMod_pow (K := ↥K) (Ω := Ω) p b)
  have hβ : ((⟨Work.SSGRoute.kummerSqrtZMod (K := ↥K) (Ω := Ω) p b, hmem⟩ :
      ↥(hLevel (Ω := Ω) (K := K) (p := p) b)) ^ p)
      = algebraMap ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) b) (b : ↥K) := by
    refine Subtype.ext ?_
    rw [IntermediateField.coe_pow, IntermediateField.coe_algebraMap_apply]
    exact Work.SSGRoute.kummerSqrtZMod_pow (K := ↥K) (Ω := Ω) p b
  have hdiv := Work.SSGRoute.ZDataMup.LocalUnramified.dvd_ramificationIdx_of_val_log_notMem_pow
    (↥K) (↥(hLevel (Ω := Ω) (K := K) (p := p) b))
    p (Fact.out) b (⟨Work.SSGRoute.kummerSqrtZMod (K := ↥K) (Ω := Ω) p b, hmem⟩) hβ 𝔮 P
    hdvd
  rw [hunr P hP] at hdiv
  exact (Fact.out : p.Prime).not_dvd_one hdiv

end Work.SSGRoute.H9

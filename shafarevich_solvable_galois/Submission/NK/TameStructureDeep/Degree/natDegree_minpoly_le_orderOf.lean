import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.LocalStructure.Main
import Submission.NK.Mine.ResidueCharAutomatic
import Submission.NK.TameStructureDeep.Degree.dvd_pow_orderOf_sub_one
import Submission.NK.TameStructureDeep.Degree.exists_isPrimitiveRoot_adicCompletion_of_dvd
import Submission.NK.TameStructureDeep.Degree.primitiveRoot_natDegree_le_finrank
import Submission.NK.TameStructureDeep.Degree.unramifiedExtensionGeneral

open scoped Classical IntermediateField
open Polynomial
open IsDedekindDomain.HeightOneSpectrum

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace NK.TameStructureDeep.Degree

theorem natDegree_minpoly_le_orderOf {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {n : ℕ} (hn0 : n ≠ 0)
    (hn : ¬ ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) ∣ n)
    {ζ : K'} (hζ : IsPrimitiveRoot ζ n) :
    (minpoly (𝔭.adicCompletion K) ζ).natDegree ≤
      orderOf ((NK.LocalStructure.residueCard K 𝔭 : ZMod n)) := by
  classical
  -- ## the residue cardinality is prime to `n`
  have hcop : Nat.Coprime (NK.LocalStructure.residueCard K 𝔭) n := by
    have hpprime := NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
    have hcharP := NK.Mine.charP_ringChar_residueField_adicCompletion 𝔭
    obtain ⟨f, _hfpos, hqf⟩ :=
      NK.LocalStructure.Tame.residueCard_eq_pow_of_charP 𝔭 hpprime hcharP
    rw [hqf]
    exact Nat.Coprime.pow_left f ((Nat.Prime.coprime_iff_not_dvd hpprime).mpr hn)
  -- ## `d = ord_n(q)` is positive and `n ∣ q ^ d - 1`
  obtain ⟨hdvd, hdpos⟩ :=
    dvd_pow_orderOf_sub_one (q := NK.LocalStructure.residueCard K 𝔭) hn0 hcop
  -- ## the unramified extension of degree `d` at `𝔭`
  obtain ⟨K₂, hK₂F, hK₂NF, hK₂A, 𝔮, hLies, he, hf, hfr⟩ :=
    exists_unramified_extension_of_inertiaDeg' (L := K) 𝔭
      (orderOf (NK.LocalStructure.residueCard K 𝔭 : ZMod n)) hdpos
  letI : Algebra K K₂ := hK₂A
  haveI hFDK : FiniteDimensional K K₂ :=
    FiniteDimensional.of_finrank_pos (by rw [hfr]; exact hdpos)
  -- ## the local field `κ₂ = (K₂)_𝔮` as a `κ`-algebra of degree `d`
  letI : Algebra (𝔭.adicCompletion K) (𝔮.adicCompletion K₂) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap 𝔭 𝔮 hLies)
  have hfin : Module.finrank (𝔭.adicCompletion K) (𝔮.adicCompletion K₂) =
      orderOf (NK.LocalStructure.residueCard K 𝔭 : ZMod n) := by
    rw [← Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      (K := K) (L := K₂) 𝔭 𝔮 hLies, he, hf, one_mul]
  haveI hFDL : FiniteDimensional (𝔭.adicCompletion K) (𝔮.adicCompletion K₂) :=
    FiniteDimensional.of_finrank_pos (by rw [hfin]; exact hdpos)
  -- ## separability (characteristic zero)
  haveI hcharZero : CharZero (𝔭.adicCompletion K) :=
    Commons.NumberTheory.NumberField.charZero_adicCompletion 𝔭
  haveI hInt : Algebra.IsIntegral (𝔭.adicCompletion K) (𝔮.adicCompletion K₂) :=
    ⟨fun x => IsIntegral.of_finite (𝔭.adicCompletion K) x⟩
  haveI hSep : Algebra.IsSeparable (𝔭.adicCompletion K) (𝔮.adicCompletion K₂) :=
    Algebra.IsSeparable.of_integral (𝔭.adicCompletion K) (𝔮.adicCompletion K₂)
  -- ## the residue field of `κ₂` has `q ^ d` elements
  have hN : Nat.card (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K₂)) =
      (NK.LocalStructure.residueCard K 𝔭) ^
        orderOf (NK.LocalStructure.residueCard K 𝔭 : ZMod n) := by
    rw [Commons.NumberTheory.NumberField.Completion.natCard_residueField_adicCompletion_eq_pow_inertiaDeg
      K K₂ 𝔭 𝔮 hLies, hf]
    rfl
  -- ## hence `κ₂` contains a primitive `n`-th root of unity (Hensel/Teichmüller)
  have hdvdN : n ∣ Nat.card (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K₂)) - 1 := by
    rw [hN]; exact hdvd
  obtain ⟨ψ, hψ⟩ := exists_isPrimitiveRoot_adicCompletion_of_dvd 𝔭 𝔮 hLies hn0 hdvdN
  -- ## the degree bound
  have hmain := primitiveRoot_natDegree_le_finrank
    (F := 𝔭.adicCompletion K) (F' := 𝔮.adicCompletion K₂) (E := K') hn0 hζ hψ
  rwa [hfin] at hmain

end NK.TameStructureDeep.Degree

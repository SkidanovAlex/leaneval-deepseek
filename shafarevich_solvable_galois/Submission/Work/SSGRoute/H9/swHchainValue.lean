import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.H9.swDictionaryKills
import Submission.Work.SSGRoute.H9.swKummerCochar_kills_levelKernel
import Submission.Work.SSGRoute.H9.swTwoPlacePairing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# From the §4(b) chain value identity to the local-group vanishing

`Work.SSGRoute.H9.swChainValueH9` proves the *value* `χ_{b_i}(ψ) + χ_{b_N}(ψ) = 0` at a pinned
Frobenius `ψ` of the local group at a sibling of the last escape prime.  The `hchain` input of
`Work.SSGRoute.H9.ZSix_of_histK` is the vanishing on the *whole* local group, so one applies
Schmidt--Wingberg's final step ("`z_i` and `z_N` are unramified at `σP_N`, so it suffices to check
the Frobenius", `ZSplit.localValue_eq_zero_of_isFrobAtPrime`) with the level
`L ⊇ K((b_i b_N)^{1/p})` — the two classes sum to `χ_{b_i b_N}`, whose Kummer level is unramified at
the sibling (each class is unramified there), so the level kernel is killed by
`H9.swKummerCochar_kills_levelKernel`.
-/

namespace Work.SSGRoute.H9

open _root_.SSGRoute
open Work.SSGRoute.ZDataMup.LTRecFamHonest
open Work.SSGRoute.ZDataMup

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]

/-- **The level kernel of `L ⊇ K((b_i b_N)^{1/p})` is killed by `χ_{b_i} + χ_{b_N}`.**  The sum is
the Kummer cochain of the product, and the restriction of a root of the product to `L` kills it
(`H9.swKummerCochar_kills_levelKernel`). -/
theorem swSum_kills_levelKernel {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (bi bN : (↥K)ˣ)
    (L : IntermediateField k Ω) [Normal k L]
    (hroot : (Work.SSGRoute.kummerSqrtZMod (K := ↥K) (Ω := Ω) p (bi * bN) : Ω) ∈ L)
    (u : Ω ≃ₐ[k] Ω) (huK : u ∈ K.fixingSubgroup) (huL : SSGRoute.res k L u = 1) :
    Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi u
      + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN u = 0 := by
  have h := swKummerCochar_kills_levelKernel (K := K) (p := p) ζ hζ hζK (bi * bN) L hroot u huK huL
  rwa [Work.SSGRoute.nodeKummerCocharZMod_mul K ζ hζ hζK bi bN] at h

/-- **From the value at a pinned Frobenius to the whole local group.**  If the sum of the two Kummer
cochains vanishes at a Frobenius `ψ` of the local group at `A` which is pinned in the auxiliary
level `L ⊇ K((b_i b_N)^{1/p})`, and `L|k` is unramified at `A`, then the sum vanishes on the whole
local group `decomp k A ⊓ G_K`. -/
theorem swLocalValue_sum_eq_zero_of_isFrobAtPrime {K : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K] [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (bi bN : (↥K)ˣ)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (ψ : Ω ≃ₐ[k] Ω) (hψ : ψ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup)
    (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    (hroot : (Work.SSGRoute.kummerSqrtZMod (K := ↥K) (Ω := Ω) p (bi * bN) : Ω) ∈ L)
    (hunrL : ¬ SSGRoute.IsRamifiedIn k L A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (h𝔭 : A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭)
    (hfrob : NK.Chebotarev.IsFrobAtPrime (K := k) (L := L) 𝔭 (SSGRoute.res k L ψ))
    (hval : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi ψ
      + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN ψ = 0) :
    ∀ y ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi y
        + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN y = 0 := by
  refine Work.SSGRoute.ZSplit.localValue_eq_zero_of_isFrobAtPrime (K := K) (L := L) A hA 𝔭 h𝔭
    hunrL (fun u => Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi u
      + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN u) ?_ ψ hψ hfrob ?_ hval
  · intro g hg h hh
    rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ bi g hg h hh,
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ bN g hg h hh]
    abel
  · intro u hu huL
    exact swSum_kills_levelKernel (K := K) (p := p) ζ hζ hζK bi bN L (by
      exact_mod_cast hroot) u (Subgroup.mem_inf.mp hu).2 huL

/-- **Extension from the `galLift`-siblings to all siblings.**  If the sum `χ_{b_i} + χ_{b_N}` vanishes
on the local group of `galLift K σ • Q_N` for every `σ ≠ 1`, then it vanishes on the local group of
*every* place which is `k`-conjugate to `Q_N` but not `K`-conjugate to it — which is the `hchain`
input of `H9.ZSix_of_histK`.

Indeed every such place is `K`-conjugate to one of the `galLift`-siblings (two `k`-lifts of the same
element of `Gal(K|k)` differ by an element of `G_K`), and both `χ_{b_i}` and `χ_{b_N}` are invariant
under conjugation by `G_K` (`ZDataMup.nodeKummerCocharZMod_conj`). -/
theorem swSiblingVanishing_all {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (bi bN : (↥K)ˣ) (QN : ValuationSubring Ω)
    (hone : ∀ (σ : K ≃ₐ[k] K), σ ≠ 1 →
      ∀ y ∈ SSGRoute.decomp k (galLift K σ • QN) ⊓ K.fixingSubgroup,
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi y
          + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN y = 0) :
    ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k QN Q →
      (¬ ∃ τ ∈ K.fixingSubgroup, τ • QN = Q) →
      ∀ y ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup,
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi y
          + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN y = 0 := by
  classical
  intro Q hQ hnotK y hy
  obtain ⟨ρ, hρ⟩ := hQ
  have hσne : SSGRoute.res k K ρ ≠ 1 := by
    intro h
    refine hnotK ⟨ρ, ?_, hρ⟩
    rw [← IntermediateField.restrictNormalHom_ker K]
    exact h
  set u : Ω ≃ₐ[k] Ω := ρ * (galLift K (SSGRoute.res k K ρ))⁻¹ with hudef
  have huK : u ∈ K.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker K]
    show SSGRoute.res k K u = 1
    rw [hudef, map_mul, map_inv, galLift_spec, mul_inv_cancel]
  have hQeq : Q = u • (galLift K (SSGRoute.res k K ρ) • QN) := by
    rw [← hρ, hudef, mul_smul, inv_smul_smul]
  have hyK : y ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hy).2
  have huK' : u⁻¹ ∈ K.fixingSubgroup := K.fixingSubgroup.inv_mem huK
  have hconj : u⁻¹ * y * u ∈
      SSGRoute.decomp k (galLift K (SSGRoute.res k K ρ) • QN) ⊓ K.fixingSubgroup := by
    refine Subgroup.mem_inf.mpr ⟨?_, K.fixingSubgroup.mul_mem
      (K.fixingSubgroup.mul_mem huK' hyK) huK⟩
    have hdec : SSGRoute.decomp k Q = (SSGRoute.decomp k
        (galLift K (SSGRoute.res k K ρ) • QN)).map (MulAut.conj u).toMonoidHom := by
      rw [hQeq, SSGRoute.decomp_conj]
    have hmem : y ∈ (SSGRoute.decomp k
        (galLift K (SSGRoute.res k K ρ) • QN)).map (MulAut.conj u).toMonoidHom := by
      rw [← hdec]
      exact (Subgroup.mem_inf.mp hy).1
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hmem
    have hzeq : u⁻¹ * y * u = z := by
      rw [← hzy]
      simp [mul_assoc]
    rwa [← hzeq] at hz
  have hval := hone (SSGRoute.res k K ρ) hσne (u⁻¹ * y * u) hconj
  have e1 : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi (u⁻¹ * y * u)
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi y := by
    simpa only [inv_inv] using
      Work.SSGRoute.ZDataMup.nodeKummerCocharZMod_conj K ζ hζ hζK bi huK' y
  have e2 : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN (u⁻¹ * y * u)
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN y := by
    simpa only [inv_inv] using
      Work.SSGRoute.ZDataMup.nodeKummerCocharZMod_conj K ζ hζ hζK bN huK' y
  rw [e1, e2] at hval
  exact hval

end Work.SSGRoute.H9

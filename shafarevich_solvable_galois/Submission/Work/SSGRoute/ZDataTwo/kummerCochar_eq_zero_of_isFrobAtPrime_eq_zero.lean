import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZDataTwo.KummerCocharBase
import Submission.Work.SSGRoute.ZDataTwo.chebotarev_frobenius_split
import Submission.Work.SSGRoute.decomp_mod_inertia_cyclic
import Submission.Work.SSGRoute.ZDataTwo.ramificationIdx_levelPrime_eq_one_of_not_isRamifiedIn
import Submission.Work.SSGRoute.ZDataTwo.map_decomp_res_eq_zpowers_of_isFrobAtPrime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataTwo

open scoped NumberField

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **The Frobenius form of clause (b): the value at a Frobenius detects the unramified class.**
Let `b ∈ (↥K)ˣ` be unramified at a finite place `A` with `A ∤ 2`, and let `σ` lie in the local group
`decomp k A ⊓ K.fixingSubgroup`.  If `σ` restricts to a Frobenius at the level `L`
(`NK.Chebotarev.IsFrobAtPrime`, the finite-level spelling used by the banked Chebotarev step
`ZDataTwo/chebotarev_frobenius_split`; that step also *produces* the unramifiedness hypothesis
`¬ SSGRoute.IsRamifiedIn k L A`, so it is free in the application), the Kummer cochain of `b` is
constant on the cosets of the kernel of `res k L` inside the local group, and the value at `σ`
vanishes, then the cochain vanishes on the *whole* local group.

Equivalently (by `ZDataTwo/KummerCocharBase.kummerCochar_eq_zero_iff_localPowClass`) the class of `b`
at the prime of `K` below `A` is a local square.  This is the statement Schmidt–Wingberg's chain in
§4 uses when it converts "the Frobenius value of `z_s` at `σP_t` is `1`" into "the local class
`(z_s)_{σP_t}` vanishes".  The proof: `hur` makes the cochain of `b` kill the inertia of `A`
(`kummerCochar_eq_zero_of_isInertia_of_even_valuation`), so it descends to `D/I`; `hfac` makes it
factor through `res k L`; `hfrob` says `res k L σ` acts on the residue field at `P` as the Frobenius,
hence generates the decomposition subgroup modulo inertia at the level `L` — so every `τ` in the local
group is `σ^n` times an inertia element modulo `ker (res k L)`, and the cochain vanishes on both
factors.  Without `hfrob` the statement is **false** (the unramified character of `D/I ≅ Ẑ` vanishes
on the even part of `Ẑ`, so a general `σ ∈ D ∖ I` can satisfy `χ_b(σ) = 0` with `χ_b ≠ 0`). -/
theorem kummerCochar_eq_zero_of_isFrobAtPrime_eq_zero
    {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (hp : A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k p)
    (h2 : ¬ A.valuation (2 : Ω) < 1)
    (hunrL : ¬ SSGRoute.IsRamifiedIn k L A)
    (b : (↥K)ˣ) (d : (↥K)ˣ)
    (hur : A.valuation (algebraMap ↥K Ω (b : ↥K)) =
      A.valuation (algebraMap ↥K Ω (d : ↥K)) ^ 2)
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup)
    (hfac : ∀ τ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ τ' ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      SSGRoute.res k L τ = SSGRoute.res k L τ' →
      Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b τ =
        Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b τ')
    (hfrob : NK.Chebotarev.IsFrobAtPrime (K := k) (L := L) p (SSGRoute.res k L σ))
    (hval : Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b σ = 0) :
    ∀ τ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b τ = 0 := by
  have hpram : (Work.SSGRoute.levelPrime k Ω A hA L).asIdeal.ramificationIdx
      (NumberField.RingOfIntegers k) = 1 :=
    ramificationIdx_levelPrime_eq_one_of_not_isRamifiedIn k Ω L A hA hunrL
  have hσD : σ ∈ SSGRoute.decomp k A := (Subgroup.mem_inf.mp hσ).1
  have hσK : σ ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hσ).2
  have hmap : (SSGRoute.decomp k A).map (SSGRoute.res k L) =
      Subgroup.zpowers (SSGRoute.res k L σ) :=
    map_decomp_res_eq_zpowers_of_isFrobAtPrime k Ω L A hA p hp hpram σ hσD hfrob
  have hchi_one : Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b 1 = 0 := by
    have h := Work.SSGRoute.nodeKummerCochar_add K ζ hζK hζ b 1
      (K.fixingSubgroup.one_mem) 1 (K.fixingSubgroup.one_mem)
    rw [one_mul] at h
    rw [Work.SSGRoute.zmodTwo_add_self] at h
    exact h
  let S : Subgroup (Ω ≃ₐ[k] Ω) :=
    { carrier := {g | g ∈ K.fixingSubgroup ∧
        Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b g = 0}
      mul_mem' := by
        intro g h hg hh
        obtain ⟨hgK, hg0⟩ := hg
        obtain ⟨hhK, hh0⟩ := hh
        refine ⟨K.fixingSubgroup.mul_mem hgK hhK, ?_⟩
        rw [Work.SSGRoute.nodeKummerCochar_add K ζ hζK hζ b g hgK h hhK, hg0, hh0, zero_add]
      one_mem' := ⟨K.fixingSubgroup.one_mem, hchi_one⟩
      inv_mem' := by
        intro g hg
        obtain ⟨hgK, hg0⟩ := hg
        refine ⟨K.fixingSubgroup.inv_mem hgK, ?_⟩
        have h1 := Work.SSGRoute.nodeKummerCochar_add K ζ hζK hζ b g hgK g⁻¹
          (K.fixingSubgroup.inv_mem hgK)
        rw [mul_inv_cancel] at h1
        rw [hchi_one, hg0, zero_add] at h1
        exact h1.symm }
  intro τ hτ
  obtain ⟨hτD, hτK⟩ := Subgroup.mem_inf.mp hτ
  have hmem : SSGRoute.res k L τ ∈ (SSGRoute.decomp k A).map (SSGRoute.res k L) :=
    Subgroup.mem_map.mpr ⟨τ, hτD, rfl⟩
  rw [hmap] at hmem
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hres : SSGRoute.res k L (σ ^ m) = SSGRoute.res k L τ :=
    (map_zpow (SSGRoute.res k L) σ m).trans hm
  have hσm : σ ^ m ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup :=
    Subgroup.mem_inf.mpr ⟨Subgroup.zpow_mem (SSGRoute.decomp k A) hσD m,
      Subgroup.zpow_mem K.fixingSubgroup hσK m⟩
  have hfac' := hfac τ hτ (σ ^ m) hσm hres.symm
  rw [hfac']
  exact (Subgroup.zpow_mem S (show σ ∈ S from ⟨hσK, hval⟩) m).2

end Work.SSGRoute.ZDataTwo

import Mathlib
import Submission.Work.SSGRoute.E1aClean.completion_quotient_uniqueDivisible
import Submission.Work.SSGRoute.ExtChain.ext_push_engine
import Submission.Work.SSGRoute.E1aClean.decompField_embeds_completion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.SSGRoute.E1aClean

open AddSubgroup

/-- **Abstract unique `n`-divisibility of a quotient.**  A subgroup `H ≤ M` of an abelian group
such that every `z : M` is `z = u * w ^ n` with `u ∈ H` and such that `z ^ n ∈ H → z ∈ H` has
`n`-multiplication a bijection on `M / H`. -/
lemma nsmul_bijective_quotient {M : Type} [CommGroup M] (H : Subgroup M) (n : ℕ)
    (hdiv : ∀ z : M, ∃ w : M, ∃ u : H, z = (u : M) * w ^ n)
    (hpur : ∀ z : M, ∀ u : H, z ^ n = (u : M) → ∃ u' : H, z = (u' : M)) :
    Function.Bijective (fun q : Additive M ⧸ H.toAddSubgroup => n • q) := by
  haveI : (H.toAddSubgroup).Normal := inferInstance
  refine ⟨fun a b hab => ?_, fun q => ?_⟩
  · have hab' : n • a = n • b := hab
    suffices hm : ∀ x : Additive M ⧸ H.toAddSubgroup, n • x = 0 → x = 0 by
      have h' : n • (a - b) = 0 := by rw [nsmul_sub, hab', sub_self]
      exact sub_eq_zero.mp (hm (a - b) h')
    intro x hx
    induction x using QuotientAddGroup.induction_on with
    | _ z =>
      rw [(QuotientAddGroup.mk_nsmul H.toAddSubgroup z n).symm] at hx
      rw [QuotientAddGroup.eq_zero_iff] at hx
      rw [QuotientAddGroup.eq_zero_iff]
      set m : M := Additive.toMul z with hm
      have hz : (Additive.ofMul m : Additive M) = z := rfl
      rw [← hz] at hx ⊢
      have hmem : m ^ n ∈ H := by
        have h2 : (n • (Additive.ofMul m : Additive M)) ∈ H.toAddSubgroup := hx
        have h3 : (n • (Additive.ofMul m : Additive M)) = (Additive.ofMul (m ^ n) : Additive M) :=
          by simp
        rw [h3] at h2
        exact h2
      obtain ⟨u', hu'⟩ := hpur m ⟨m ^ n, hmem⟩ rfl
      have : (Additive.toMul (Additive.ofMul m) : M) ∈ H := by
        rw [show Additive.toMul (Additive.ofMul m) = m from rfl]; exact hu' ▸ u'.2
      exact this
  · induction q using QuotientAddGroup.induction_on with
    | _ z =>
      set m : M := Additive.toMul z with hm
      have hz : (Additive.ofMul m : Additive M) = z := rfl
      rw [← hz]
      obtain ⟨w, u, hu⟩ := hdiv m
      refine ⟨((Additive.ofMul w : Additive M) : Additive M ⧸ H.toAddSubgroup), ?_⟩
      change n • (((Additive.ofMul w : Additive M)) : Additive M ⧸ H.toAddSubgroup) = _
      rw [(QuotientAddGroup.mk_nsmul H.toAddSubgroup (Additive.ofMul w) n).symm]
      rw [show n • (Additive.ofMul w : Additive M) = (Additive.ofMul (w ^ n) : Additive M) from
        by simp]
      rw [QuotientAddGroup.eq_iff_sub_mem]
      have hsub : (Additive.ofMul (w ^ n) : Additive M) - Additive.ofMul m
          = (Additive.ofMul (w ^ n * m⁻¹) : Additive M) := by
        rw [sub_eq_add_neg]; simp
      rw [hsub]
      show (Additive.toMul (Additive.ofMul (w ^ n * m⁻¹)) : M) ∈ H
      rw [show Additive.toMul (Additive.ofMul (w ^ n * m⁻¹)) = w ^ n * m⁻¹ from rfl]
      have : w ^ n * m⁻¹ = (u : M)⁻¹ := by rw [hu]; group
      rw [this]
      exact H.inv_mem u.2

/-- **The arithmetic half of `(PUSH)`**: for the henselisation `K^h = Ω^{D_A ⊓ Gal(Ω/K)}` of `K`
at a finite place `A` of `Ω` and any injective field map `φ : K^h →+* K_q` whose image is
relatively algebraically closed in the completion `K_q = localField K (ofFinite q)` (both supplied
by `E1aClean.decompField_embeds_completion`), multiplication by `p` is a bijection on the quotient
of the additive group `K_qˣ` by the image of `(K^h)ˣ`.

This is exactly the hypothesis `hQ` of the `(PUSH)` engine
`Work.SSGRoute.ExtChain.postcomp_mk₀_bijective_of_ptorsion_uniqueDivisible`
(`ExtChain/ext_push_engine.lean`) — i.e. unique `p`-divisibility of the cokernel
`K_qˣ/(K^h)ˣ`: surjectivity is the divisibility clause and injectivity the purity clause of
`E1aClean.completion_quotient_uniqueDivisible`. -/
theorem unitsQuotient_pow_bijective (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (φ : ↥(IntermediateField.fixedField (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)) →+*
      (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q)))
    (hφ : Function.Injective φ)
    (halg : ∀ z : NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q),
      (∃ r : Polynomial ↥(IntermediateField.fixedField
            (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)),
          r ≠ 0 ∧ Polynomial.eval₂ φ z r = 0) →
        ∃ x : ↥(IntermediateField.fixedField (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)),
          φ x = z)
    (p : ℕ) [Fact p.Prime] :
    Function.Bijective (fun z : Additive (NK.GlobalCFT.Place.localField K
        (NK.GlobalCFT.Place.ofFinite q))ˣ ⧸
        (MonoidHom.range (Units.map φ.toMonoidHom)).toAddSubgroup => p • z) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hcomp := completion_quotient_uniqueDivisible k Ω K A hA q φ hφ halg
  refine nsmul_bijective_quotient (MonoidHom.range (Units.map φ.toMonoidHom)) p ?_ ?_
  · intro z
    obtain ⟨w, u, hw⟩ := hcomp.1 p hp z
    exact ⟨w, ⟨Units.map φ.toMonoidHom u, MonoidHom.mem_range.mpr ⟨u, rfl⟩⟩, hw⟩
  · intro z u hzu
    obtain ⟨u0, hu0⟩ := MonoidHom.mem_range.mp u.2
    obtain ⟨u', hu'⟩ := hcomp.2 p hp z u0 (hzu.trans hu0.symm)
    exact ⟨⟨Units.map φ.toMonoidHom u', MonoidHom.mem_range.mpr ⟨u', rfl⟩⟩, hu'⟩

end Work.SSGRoute.E1aClean

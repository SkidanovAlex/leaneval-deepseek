import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.isLocalNorm_mul_of_localPowClass_eq_one
import Submission.Work.SSGRoute.ZDataTwo.exists_level_normGroup_eq_of_quadratic
import Submission.Work.HilbertSymbolGeneral.hilbertSymbol_comm
import Submission.NeukirchUchida.Local.LocalGalois
import Submission.NK.CFTLib.IdeleHasse.range_localNormFinite_eq_of_liesOver
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_le_finrank
import Submission.NK.Chebotarev.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataTwo

open scoped NumberField

/-- **A degree-one extension has norm group everything.**

If `Module.finrank F E = 1` then `E` is `F`-isomorphic to `F`, and the norm of the degree one
extension is the identity; equivalently every element of `Fˣ` is the norm of `algebraMap F E x`,
whose norm is `x ^ 1 = x`.  This is the "split place" case of
`exists_level_localNormSubgroup_eq`. -/
theorem normGroup_eq_top_of_finrank_eq_one {F E : Type*} [Field F] [Field E] [Algebra F E]
    (h : Module.finrank F E = 1) :
    NK.LocalReciprocity.normGroup F E = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro x
  rw [NK.LocalReciprocity.mem_normGroup_iff]
  refine ⟨Units.mk0 (algebraMap F E (x : F)) ?_, ?_⟩
  · intro hx
    exact Units.ne_zero x ((algebraMap F E).injective (by simpa using hx))
  · rw [Units.val_mk0, Algebra.norm_algebraMap, h, pow_one]

theorem exists_level_localNormSubgroup_eq {k : Type} [Field k] [NumberField k]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    {L : Type} [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (h2 : Nat.card (L ≃ₐ[k] L) = 2) :
    ∃ (Λ : IntermediateField (Q.adicCompletion k)
        (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion k)
          (SeparableClosure (Q.adicCompletion k))))
      (_ : FiniteDimensional (Q.adicCompletion k) Λ) (_ : Normal (Q.adicCompletion k) Λ),
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := k) (L := L)
          (NK.GlobalCFT.Place.ofFinite Q)
        = NK.LocalReciprocity.normGroup (Q.adicCompletion k) ↥Λ := by
  classical
  -- a prime of `L` above `Q`
  obtain ⟨q₀, hq₀⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := k) (L := L) Q
  -- the local algebra structure and finiteness
  letI algQ : Algebra (Q.adicCompletion k) (q₀.adicCompletion L) :=
    (Commons.RingTheory.Henselian.adicCompletionMap Q q₀ hq₀).toAlgebra
  haveI hfin : Module.Finite (Q.adicCompletion k) (q₀.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q₀ hq₀
  -- the local norm subgroup is the (single) norm group of any prime above `Q`
  have hlocal : NK.CFTLib.IdeleHasse.localNormSubgroup (K := k) (L := L)
        (NK.GlobalCFT.Place.ofFinite Q)
      = NK.LocalReciprocity.normGroup (Q.adicCompletion k) (q₀.adicCompletion L) := by
    apply le_antisymm
    · rw [NK.CFTLib.IdeleHasse.localNormSubgroup_ofFinite]
      refine iSup_le (fun q => ?_)
      rw [NK.CFTLib.IdeleHasse.range_localNormFinite_eq_of_liesOver (K := k) (L := L) Q
        q.1 q₀ q.2 hq₀]
      exact le_of_eq rfl
    · rw [NK.CFTLib.IdeleHasse.localNormSubgroup_ofFinite]
      exact le_iSup (fun q : {q : IsDedekindDomain.HeightOneSpectrum (𝓞 L) //
          q.asIdeal.LiesOver Q.asIdeal} =>
          MonoidHom.range (NK.GlobalCFT.Place.localNormFinite q.1 Q q.2)) ⟨q₀, hq₀⟩
  -- the local degree is `1` or `2`
  have hfKL : Module.finrank k L = 2 := (IsGalois.card_aut_eq_finrank k L).symm.trans h2
  have hd : Module.finrank (Q.adicCompletion k) (q₀.adicCompletion L) ≤ 2 := by
    have h := Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_le_finrank
      (K := k) (L := L) Q q₀ hq₀
    rw [hfKL] at h
    exact h
  have hd1 : 1 ≤ Module.finrank (Q.adicCompletion k) (q₀.adicCompletion L) :=
    Module.finrank_pos
  rcases (by omega : Module.finrank (Q.adicCompletion k) (q₀.adicCompletion L) = 1 ∨
      Module.finrank (Q.adicCompletion k) (q₀.adicCompletion L) = 2) with h1 | h2'
  · -- split place: the local norm subgroup is everything, and so is the norm group of `⊥`
    refine ⟨⊥, inferInstance, inferInstance, ?_⟩
    rw [hlocal, normGroup_eq_top_of_finrank_eq_one h1]
    exact (Work.HilbertSymbolGeneral.normGroup_bot_eq_top
      (F := Q.adicCompletion k)
      (E := NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion k)
        (SeparableClosure (Q.adicCompletion k)))).symm
  · -- nonsplit place: the local extension is quadratic, so it is a level of `F^{ab}`
    haveI hgal : IsGalois (Q.adicCompletion k) (q₀.adicCompletion L) :=
      Submission.NeukirchUchida.Local.isGalois_adicCompletion Q q₀ hq₀
    have hcard : Nat.card (q₀.adicCompletion L ≃ₐ[Q.adicCompletion k]
        q₀.adicCompletion L) = 2 := by
      rw [IsGalois.card_aut_eq_finrank, h2']
    obtain ⟨Λ, hfd, hn, -, hnorm⟩ :=
      exists_level_normGroup_eq_of_quadratic (F := Q.adicCompletion k)
        (F' := SeparableClosure (Q.adicCompletion k)) (q₀.adicCompletion L) hcard
    exact ⟨Λ, hfd, hn, by rw [hlocal]; exact hnorm.symm⟩

end Work.SSGRoute.ZDataTwo

import Mathlib
import Submission.Work.HilbertSymbolGeneral.hilbertReciprocityTwo
import Submission.Work.SSGRoute.ZConstruction.localKummerDictionary
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Multiplying a local norm by an element whose local `2`-power class is trivial

Let `L / K` be a quadratic Galois extension of number fields (`Nat.card (L ≃ₐ[K] L) = 2`), `Q` a
finite place of `K` and `γ ∈ Kˣ` an element which is a local *square* at `Q` — the meaning of
`NK.UchidaKummer.localPowClass K 2 Q γ = 1`.  Then at `Q` the local-norm condition is unchanged by
multiplying with `γ`:

  `IsLocalNorm K L (γ * β) Q ↔ IsLocalNorm K L β Q`.

The arithmetic content is that **the local norm group of a quadratic local extension contains the
squares**: for `q | Q` the local degree `[L_q : K_Q] = e·f` is `1` or `2`, so every `z ∈ K_Qˣ`
satisfies `z^[L_q:K_Q] ∈ N_{L_q/K_Q}(L_qˣ)` (`NK.GlobalCFTdeep.pow_finrank_mem_localNormFinite`),
which is `z` itself when `[L_q : K_Q] = 1` and `z²` when `[L_q : K_Q] = 2`; in either case `z²` is
a local norm.  Since `IsLocalNorm K L · Q` is membership in the subgroup
`NK.CFTLib.IdeleHasse.localNormSubgroup K L Q` (`Work.HilbertSymbolGeneral`), the claim follows
from the subgroup axioms.
-/

set_option linter.style.haveILetI false

namespace Work.SSGRoute.ZDataTwo

open scoped NumberField

/-- **Squares are local norms at a finite place of a quadratic extension.**  For `L / K` quadratic
Galois and a finite prime `Q` of `K`, the subgroup of `2`-nd powers of `K_Qˣ` is contained in the
local norm subgroup `N_{L/K} K_Qˣ ≤ K_Qˣ`. -/
theorem ellPowSubgroup_two_le_localNormSubgroup_of_card_eq_two
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (h2 : Nat.card (L ≃ₐ[K] L) = 2)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    NK.UchidaKummer.ellPowSubgroup (Q.adicCompletion K) 2 ≤
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite Q) := by
  intro x hx
  rw [NK.UchidaKummer.ellPowSubgroup, MonoidHom.mem_range] at hx
  obtain ⟨z, hz⟩ := hx
  obtain ⟨q, hq⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := L) Q
  rw [NK.CFTLib.IdeleHasse.localNormSubgroup_ofFinite]
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    (Commons.RingTheory.Henselian.adicCompletionMap Q q hq).toAlgebra
  haveI hfin : Module.Finite (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  -- the local degree `[L_q : K_Q] = e·f` is at most the global degree `[L : K] = 2`
  have hd : Module.finrank (Q.adicCompletion K) (q.adicCompletion L) ≤ 2 := by
    have h := Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_le_finrank Q q hq
    have hf : Module.finrank K L = 2 := (IsGalois.card_aut_eq_finrank K L).symm.trans h2
    omega
  have hd1 : 1 ≤ Module.finrank (Q.adicCompletion K) (q.adicCompletion L) :=
    Module.finrank_pos
  rcases (by omega : Module.finrank (Q.adicCompletion K) (q.adicCompletion L) = 1 ∨
      Module.finrank (Q.adicCompletion K) (q.adicCompletion L) = 2) with h | h
  · -- split place: `L_q = K_Q`, so the norm group is everything
    refine Subgroup.mem_iSup_of_mem ⟨q, hq⟩ ?_
    have hz1 : z ∈ (NK.GlobalCFT.Place.localNormFinite q Q hq).range := by
      have := NK.GlobalCFTdeep.pow_finrank_mem_localNormFinite Q q hq z
      rwa [h, pow_one] at this
    rw [← hz]
    exact pow_mem hz1 2
  · -- nonsplit place: the norm of `z ∈ K_Qˣ ⊂ L_qˣ` is `z²`
    refine Subgroup.mem_iSup_of_mem ⟨q, hq⟩ ?_
    have hz2 : z ^ 2 ∈ (NK.GlobalCFT.Place.localNormFinite q Q hq).range := by
      have := NK.GlobalCFTdeep.pow_finrank_mem_localNormFinite Q q hq z
      rwa [h] at this
    rw [← hz]
    exact hz2

/-- **A unit whose local `2`-power class at `Q` is trivial is a local norm at `Q`.** -/
theorem isLocalNorm_of_localPowClass_eq_one {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (h2 : Nat.card (L ≃ₐ[K] L) = 2) (γ : Kˣ)
    (hγ : NK.UchidaKummer.localPowClass K 2 Q γ = 1) :
    NK.NUV2.LC.IsLocalNorm K L γ (NK.GlobalCFT.Place.ofFinite Q) := by
  rw [Work.HilbertSymbolGeneral.isLocalNorm_iff_localNormSubgroup (K := K) (L := L) γ
    (NK.GlobalCFT.Place.ofFinite Q)]
  rw [NK.UchidaKummer.localPowClass, MonoidHom.comp_apply, QuotientGroup.mk'_apply] at hγ
  exact ellPowSubgroup_two_le_localNormSubgroup_of_card_eq_two h2 Q
    ((QuotientGroup.eq_one_iff _).mp hγ)

theorem isLocalNorm_mul_of_localPowClass_eq_one {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (h2 : Nat.card (L ≃ₐ[K] L) = 2) (γ : Kˣ)
    (hγ : NK.UchidaKummer.localPowClass K 2 Q γ = 1) (β : Kˣ) :
    NK.NUV2.LC.IsLocalNorm K L (γ * β) (NK.GlobalCFT.Place.ofFinite Q) ↔
      NK.NUV2.LC.IsLocalNorm K L β (NK.GlobalCFT.Place.ofFinite Q) := by
  have hγmem : NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) γ ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite Q) := by
    rw [← Work.HilbertSymbolGeneral.isLocalNorm_iff_localNormSubgroup (K := K) (L := L) γ
      (NK.GlobalCFT.Place.ofFinite Q)]
    exact isLocalNorm_of_localPowClass_eq_one Q h2 γ hγ
  rw [Work.HilbertSymbolGeneral.isLocalNorm_iff_localNormSubgroup (K := K) (L := L) (γ * β)
        (NK.GlobalCFT.Place.ofFinite Q),
      Work.HilbertSymbolGeneral.isLocalNorm_iff_localNormSubgroup (K := K) (L := L) β
        (NK.GlobalCFT.Place.ofFinite Q)]
  have hmul : NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) (γ * β) =
      NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) γ *
        NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) β := by
    simp [NK.CFTLib.IdeleHasse.localImageAt, map_mul]
  rw [hmul]
  exact Subgroup.mul_mem_cancel_left _ hγmem

end Work.SSGRoute.ZDataTwo

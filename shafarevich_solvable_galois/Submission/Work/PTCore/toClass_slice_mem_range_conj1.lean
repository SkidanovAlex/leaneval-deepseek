import Mathlib
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.HSConj
import Submission.Work.PTCore.slice_mem_lcCocycles
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.PTCore

open Classical

/-- `toClass` of a difference of locally constant `1`-cocycles. -/
private lemma toClass_sub_slice
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) {f g : (Ω ≃ₐ[k] Ω) → M}
    (hf : f ∈ Work.SSGRoute.lcCocycles p k Ω K M I)
    (hg : g ∈ Work.SSGRoute.lcCocycles p k Ω K M I) :
    Work.SSGRoute.toClass p k Ω K M I (f - g)
      = Work.SSGRoute.toClass p k Ω K M I f - Work.SSGRoute.toClass p k Ω K M I g := by
  have hfg : f - g ∈ Work.SSGRoute.lcCocycles p k Ω K M I := Submodule.sub_mem _ hf hg
  have h1 : Work.SSGRoute.toClass p k Ω K M I (f - g)
        + Work.SSGRoute.toClass p k Ω K M I g
      = Work.SSGRoute.toClass p k Ω K M I f := by
    rw [← Work.SSGRoute.toClass_add p k Ω K M I hfg hg]
    congr 1
    ext n
    simp only [Pi.add_apply, Pi.sub_apply]
    abel
  exact eq_sub_of_add_eq h1

theorem toClass_slice_mem_range_conj1
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hI : I ≤ SSGRoute.decomp k A)
    (hσ : σ ∈ SSGRoute.decomp k A)
    (hnorm1 : ∀ n ∈ I, σ * n * σ⁻¹ ∈ I) (hnorm2 : ∀ n ∈ I, σ⁻¹ * n * σ ∈ I)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (F : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M)
    (hF : F ∈ Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A))
    (hFn : ∀ g ∈ SSGRoute.decomp k A, ∀ n ∈ I, F g n = 0)
    (hslice : (fun n => F n σ) ∈ Work.SSGRoute.lcCocycles p k Ω K M I)
    (hFcob : F ∈ Work.SSGRoute.coboundaries2 p k Ω K M (SSGRoute.decomp k A)) :
    Work.SSGRoute.toClass p k Ω K M I (fun n => F n σ) ∈
      LinearMap.range (Work.SSGRoute.conj1 p k Ω K M I σ hnorm1 hnorm2 - LinearMap.id) := by
  classical
  -- Unpack the hypothesis that `F` is a coboundary: `F = δβ` for a locally constant `β`.
  obtain ⟨β, hβloc, hβeq⟩ := hFcob
  obtain ⟨U, hUo, hU⟩ := hβloc
  -- The crossed-homomorphism identity for `β` on `D × I`, obtained from `F = δβ` and `F|D×I = 0`.
  have key : ∀ g ∈ SSGRoute.decomp k A, ∀ n ∈ I,
      β (g * n) = β g + SSGRoute.res k K g • β n := by
    intro g hg n hn
    have h1 := hβeq g hg n (hI hn)
    have h2 := hFn g hg n hn
    rw [h2] at h1
    have hh : (β g + SSGRoute.res k K g • β n) - β (g * n) = 0 := by
      rw [h1]; abel
    exact (sub_eq_zero.mp hh).symm
  -- `β` restricted to `I` is a locally constant `1`-cocycle.
  have hf_mem : β ∈ Work.SSGRoute.lcCocycles p k Ω K M I := by
    refine ⟨?_, ?_⟩
    · intro g hg h hh
      exact key g (hI hg) h hh
    · exact ⟨U, hUo, fun g hg u hu huI => hU g (hI hg) u hu (hI huI)⟩
  -- The slice, and the conjugation shift of `β`.
  set G : (Ω ≃ₐ[k] Ω) → M := fun n => F n σ with hGdef
  set Hf : (Ω ≃ₐ[k] Ω) → M := Work.SSGRoute.h1locConjShift p k Ω K M σ β with hHfdef
  have hG_apply : ∀ n, G n = F n σ := fun n => rfl
  have hHf_apply : ∀ n, Hf n = SSGRoute.res k K σ • β (σ⁻¹ * n * σ) := fun n => rfl
  have hG_mem : G ∈ Work.SSGRoute.lcCocycles p k Ω K M I := hslice
  have hHf_mem : Hf ∈ Work.SSGRoute.lcCocycles p k Ω K M I :=
    Work.SSGRoute.h1locConjShift_mem_lcCocycles p k Ω K M I σ hnorm2 hf_mem
  -- The pointwise identity expressing the slice through `β`.
  have hpoint : ∀ n ∈ I, F n σ + (SSGRoute.res k K σ • β (σ⁻¹ * n * σ) - β n)
      = SSGRoute.res k K n • β σ - β σ := by
    intro n hn
    have hGn := hβeq n (hI hn) σ hσ
    have hbn : β (n * σ) = β σ + SSGRoute.res k K σ • β (σ⁻¹ * n * σ) := by
      have hh := key σ hσ (σ⁻¹ * n * σ) (hnorm2 n hn)
      have harg : σ * (σ⁻¹ * n * σ) = n * σ := by group
      rwa [harg] at hh
    rw [hGn, hbn]; abel
  -- `G + Hf - β` is the coboundary of `β σ` on `I`.
  have hAcob : (G + Hf - β) ∈ Work.SSGRoute.coboundaries p k Ω K M I := by
    refine ⟨β σ, ?_⟩
    intro n hn
    have hp := hpoint n hn
    show G n + Hf n - β n = SSGRoute.res k K n • β σ - β σ
    rw [hG_apply n, hHf_apply n]
    have hkey : F n σ + SSGRoute.res k K σ • β (σ⁻¹ * n * σ) - β n
        = F n σ + (SSGRoute.res k K σ • β (σ⁻¹ * n * σ) - β n) := by abel
    rw [hkey, hp]
  have hAlc : (G + Hf - β) ∈ Work.SSGRoute.lcCocycles p k Ω K M I :=
    Work.SSGRoute.coboundaries_le_lcCocycles p k Ω K M I hAcob
  have hA0 : Work.SSGRoute.toClass p k Ω K M I (G + Hf - β) = 0 :=
    (Work.SSGRoute.toClass_eq_zero_iff p k Ω K M I hAlc).mpr hAcob
  have hGHf : G + Hf ∈ Work.SSGRoute.lcCocycles p k Ω K M I :=
    Submodule.add_mem _ hG_mem hHf_mem
  have hExp : Work.SSGRoute.toClass p k Ω K M I (G + Hf - β)
      = (Work.SSGRoute.toClass p k Ω K M I G + Work.SSGRoute.toClass p k Ω K M I Hf)
        - Work.SSGRoute.toClass p k Ω K M I β := by
    rw [toClass_sub_slice p k Ω K M I (f := G + Hf) (g := β) hGHf hf_mem,
      Work.SSGRoute.toClass_add p k Ω K M I hG_mem hHf_mem]
  have hmain : Work.SSGRoute.toClass p k Ω K M I G
      = Work.SSGRoute.toClass p k Ω K M I β - Work.SSGRoute.toClass p k Ω K M I Hf := by
    have hzero : (Work.SSGRoute.toClass p k Ω K M I G + Work.SSGRoute.toClass p k Ω K M I Hf)
        - Work.SSGRoute.toClass p k Ω K M I β = 0 := by
      rw [← hExp]; exact hA0
    exact eq_sub_iff_add_eq.mpr (sub_eq_zero.mp hzero)
  have hconj : (Work.SSGRoute.conj1 p k Ω K M I σ hnorm1 hnorm2)
        (Work.SSGRoute.toClass p k Ω K M I β)
      = Work.SSGRoute.toClass p k Ω K M I Hf := by
    rw [Work.SSGRoute.conj1_spec p k Ω K M I σ hnorm1 hnorm2 β hf_mem]
    rfl
  refine LinearMap.mem_range.mpr ⟨-(Work.SSGRoute.toClass p k Ω K M I β), ?_⟩
  simp only [LinearMap.sub_apply, LinearMap.id_apply, map_neg, hconj]
  rw [hmain]
  abel

end Work.PTCore

import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.HSConj
import Submission.Work.SSGRoute.HSRow.TransgressionDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.HSRow

open Classical

set_option linter.unusedSectionVars false

noncomputable section

/-- The pointwise difference of two functions locally constant on a subgroup is again locally
constant on that subgroup. -/
lemma isLocConstOn_sub_lc {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [AddCommGroup M]
    {I : Subgroup Γ} {f g : Γ → M} (hf : SSGRoute.IsLocConstOn I f)
    (hg : SSGRoute.IsLocConstOn I g) : SSGRoute.IsLocConstOn I (f - g) := by
  obtain ⟨U, hU, hfU⟩ := hf
  obtain ⟨V, hV, hgV⟩ := hg
  refine ⟨U ⊓ V, hU.inter hV, ?_⟩
  intro x hx u hu huH
  rw [Pi.sub_apply, Pi.sub_apply, hfU x hx u hu.1 huH, hgV x hx u hu.2 huH]

section Helpers

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]

/-- `toClass` of a difference of locally constant `1`-cocycles: the class map is additive on
locally constant `1`-cocycles. -/
lemma toClass_sub_lc (I : Subgroup (Ω ≃ₐ[k] Ω)) {f g : (Ω ≃ₐ[k] Ω) → M}
    (hf : f ∈ Work.SSGRoute.lcCocycles p k Ω K M I)
    (hg : g ∈ Work.SSGRoute.lcCocycles p k Ω K M I) :
    Work.SSGRoute.toClass p k Ω K M I (f - g) =
      Work.SSGRoute.toClass p k Ω K M I f - Work.SSGRoute.toClass p k Ω K M I g := by
  have hfg : f - g ∈ Work.SSGRoute.lcCocycles p k Ω K M I := Submodule.sub_mem _ hf hg
  have h1 : (⟨f - g, hfg⟩ : ↥(Work.SSGRoute.lcCocycles p k Ω K M I)) =
      ⟨f, hf⟩ - ⟨g, hg⟩ := Subtype.ext rfl
  rw [Work.SSGRoute.toClass, dif_pos hfg, Work.SSGRoute.toClass, dif_pos hf,
    Work.SSGRoute.toClass, dif_pos hg, h1, map_sub]

/-- Two locally constant `1`-cocycles with the same class differ by a coboundary. -/
lemma sub_mem_coboundaries_of_toClass_eq_lc (I : Subgroup (Ω ≃ₐ[k] Ω))
    {f g : (Ω ≃ₐ[k] Ω) → M}
    (hf : f ∈ Work.SSGRoute.lcCocycles p k Ω K M I)
    (hg : g ∈ Work.SSGRoute.lcCocycles p k Ω K M I)
    (heq : Work.SSGRoute.toClass p k Ω K M I f = Work.SSGRoute.toClass p k Ω K M I g) :
    f - g ∈ Work.SSGRoute.coboundaries p k Ω K M I := by
  have hfg : f - g ∈ Work.SSGRoute.lcCocycles p k Ω K M I := Submodule.sub_mem _ hf hg
  rw [← Work.SSGRoute.toClass_eq_zero_iff p k Ω K M I hfg,
    toClass_sub_lc p k Ω K M I hf hg, heq, sub_self]

end Helpers

/-- **Gauging the transgression to a coboundary.**  If the class of the transgression cochain
`tcoch I σ c β` lies in `range (conj₁ - 1)`, then the primitive `β` can be shifted by a locally
constant `1`-cocycle `ε` on `I` so that the shifted primitive `β' := β - ε` is still a primitive of
`c|_{I × I}` and the transgression cochain `tcoch I σ c β'` is the coboundary of a single element
`m ∈ M`.  (Unwrap `range (conj₁ - 1)` with `conj1_spec` and `toClass_surjective`: the class of
`tcoch I σ c β` is `conj₁ [ε] - [ε] + d⁰ m`; `conj1_spec` identifies `conj₁ [ε]` with the class of
`n ↦ ρ(σ) • ε (σ⁻¹nσ)`, and `tcoch` is affine-linear in the primitive with linear part
`β ↦ ρ(σ) • β (σ⁻¹ • σ)`.) -/
theorem tcoch_gauge_shift
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hnorm1 : ∀ n ∈ I, σ * n * σ⁻¹ ∈ I) (hnorm2 : ∀ n ∈ I, σ⁻¹ * n * σ ∈ I)
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M)
    (β : (Ω ≃ₐ[k] Ω) → M) (hβlc : SSGRoute.IsLocConstOn I β)
    (hβ : ∀ n ∈ I, ∀ m ∈ I, SSGRoute.res k K n • β m - β (n * m) + β n = c n m)
    (htcoch : tcoch p k Ω K M I σ c β ∈ Work.SSGRoute.lcCocycles p k Ω K M I)
    (hτ : Work.SSGRoute.toClass p k Ω K M I (tcoch p k Ω K M I σ c β) ∈
      LinearMap.range (Work.SSGRoute.conj1 p k Ω K M I σ hnorm1 hnorm2 - LinearMap.id)) :
    ∃ (β' : (Ω ≃ₐ[k] Ω) → M) (m : M),
      SSGRoute.IsLocConstOn I β' ∧
      (∀ n ∈ I, ∀ m' ∈ I, SSGRoute.res k K n • β' m' - β' (n * m') + β' n = c n m') ∧
      (∀ n ∈ I, tprim p k Ω K M σ c β' n - β' n = SSGRoute.res k K n • m - m) := by
  -- The class of `tcoch` is `conj₁ y - y` for some `y ∈ H¹loc(I,M)`, and `y = [ε]`.
  obtain ⟨y, hy⟩ := hτ
  have hy' : Work.SSGRoute.conj1 p k Ω K M I σ hnorm1 hnorm2 y - y =
      Work.SSGRoute.toClass p k Ω K M I (tcoch p k Ω K M I σ c β) := by
    rw [LinearMap.sub_apply, LinearMap.id_apply] at hy
    exact hy
  obtain ⟨ε, hεmem, hεclass⟩ := Work.SSGRoute.toClass_surjective p k Ω K M I y
  -- The conjugation shift `A n = ρ(σ) • ε (σ⁻¹ n σ)` of `ε`.
  let A : (Ω ≃ₐ[k] Ω) → M := fun n => SSGRoute.res k K σ • ε (σ⁻¹ * n * σ)
  have hAmem : A ∈ Work.SSGRoute.lcCocycles p k Ω K M I :=
    h1locConjShift_mem_lcCocycles p k Ω K M I σ hnorm2 hεmem
  have hconj1 : Work.SSGRoute.conj1 p k Ω K M I σ hnorm1 hnorm2
        (Work.SSGRoute.toClass p k Ω K M I ε) = Work.SSGRoute.toClass p k Ω K M I A :=
    Work.SSGRoute.conj1_spec p k Ω K M I σ hnorm1 hnorm2 ε hεmem
  -- The shift `ψ = A - ε` of the primitive, whose class is `conj₁ [ε] - [ε]`.
  let ψ : (Ω ≃ₐ[k] Ω) → M := A - ε
  have hψmem : ψ ∈ Work.SSGRoute.lcCocycles p k Ω K M I :=
    Submodule.sub_mem _ hAmem hεmem
  have hψclass : Work.SSGRoute.toClass p k Ω K M I ψ =
      Work.SSGRoute.toClass p k Ω K M I A - Work.SSGRoute.toClass p k Ω K M I ε :=
    toClass_sub_lc p k Ω K M I hAmem hεmem
  -- Hence `[tcoch] = [ψ]`, so `tcoch - ψ` is a coboundary.
  have hclass : Work.SSGRoute.toClass p k Ω K M I (tcoch p k Ω K M I σ c β) =
      Work.SSGRoute.toClass p k Ω K M I ψ := by
    rw [← hy', ← hεclass, hconj1, ← hψclass]
  have hcob : tcoch p k Ω K M I σ c β - ψ ∈ Work.SSGRoute.coboundaries p k Ω K M I :=
    sub_mem_coboundaries_of_toClass_eq_lc p k Ω K M I htcoch hψmem hclass
  obtain ⟨m, hm⟩ := hcob
  -- The shifted primitive `β' := β - ε` and the single element `m` do the job.
  refine ⟨β - ε, m, ?_, ?_, ?_⟩
  · exact isLocConstOn_sub_lc hβlc hεmem.2
  · -- `β - ε` is still a primitive of `c|_{I × I}` (`ε` is a `1`-cocycle on `I`).
    intro n hn m' hm'
    have hcoc := hεmem.1 n hn m' hm'
    have h0 : SSGRoute.res k K n • ε m' - ε (n * m') + ε n = 0 := by
      rw [hcoc]; abel
    have hsplit : SSGRoute.res k K n • (β m' - ε m') - (β (n * m') - ε (n * m'))
          + (β n - ε n)
        = (SSGRoute.res k K n • β m' - β (n * m') + β n)
          - (SSGRoute.res k K n • ε m' - ε (n * m') + ε n) := by
      rw [smul_sub]; abel
    simp only [Pi.sub_apply]
    rw [hsplit, hβ n hn m' hm', h0, sub_zero]
  · -- The transgression cochain of the shifted primitive is the same coboundary.
    intro n hn
    have htr : tprim p k Ω K M σ c (β - ε) n
        = tprim p k Ω K M σ c β n - SSGRoute.res k K σ • ε (σ⁻¹ * n * σ) := by
      rw [tprim_apply p k Ω K M σ c (β - ε) n, tprim_apply p k Ω K M σ c β n]
      simp only [Pi.sub_apply, smul_sub]
      abel
    have hm' := hm n hn
    rw [Pi.sub_apply] at hm'
    have htc : tcoch p k Ω K M I σ c β n = tprim p k Ω K M σ c β n - β n :=
      tcoch_apply_of_mem p k Ω K M I σ c β hn
    have hψn : ψ n = SSGRoute.res k K σ • ε (σ⁻¹ * n * σ) - ε n := rfl
    rw [htr]
    show tprim p k Ω K M σ c β n - SSGRoute.res k K σ • ε (σ⁻¹ * n * σ)
      - (β n - ε n) = SSGRoute.res k K n • m - m
    rw [← hm', htc, hψn]
    abel

end

end Work.SSGRoute.HSRow

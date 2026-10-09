import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.glue_fin_decomp_ex
import Submission.Work.SSGRoute.glue_infinite_place
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open SSGRoute.PTExt

namespace Work.SSGRoute

/-- **Monotonicity of `IsCoboundaryOn` in the subgroup.**  A `1`-cochain that is a coboundary on
`H₂` is a coboundary on every subgroup `H₁ ≤ H₂`: the same witnessing element `m` works.  (The
public form of this lives in `Work.SSGRoute.place_basics`; recorded here so that this file depends
only on the two glue lemmas it uses.) -/
private theorem isCoboundaryOn_mono_glue {Γ G M : Type} [Group Γ] [Group G] [AddCommGroup M]
    [DistribMulAction G M] {act : Γ →* G} {H₁ H₂ : Subgroup Γ} (hle : H₁ ≤ H₂) {f : Γ → M}
    (h : SSGRoute.IsCoboundaryOn act H₂ f) : SSGRoute.IsCoboundaryOn act H₁ f := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, fun g hg => hm g (hle hg)⟩

/-- A `1`-cochain vanishing at `1` is a coboundary on the trivial subgroup: take `m = 0`. -/
private theorem isCoboundaryOn_bot {Γ G M : Type} [Group Γ] [Group G] [AddCommGroup M]
    [DistribMulAction G M] {act : Γ →* G} {f : Γ → M} (h1 : f 1 = 0) :
    SSGRoute.IsCoboundaryOn act (⊥ : Subgroup Γ) f := by
  refine ⟨0, ?_⟩
  intro g hg
  rw [Subgroup.mem_bot] at hg
  subst hg
  simp [h1]

/-- **Place glue, converse direction.**  A cochain `ψ : Gal(K/k) → M` which is a coboundary on the
image of the decomposition group of every finite place `A` of `Ω` and on the image of every
involution of `G_k` is a coboundary on the decomposition group `D_w` of *every* place `w` of `K`.

Intended route: case on the place `w : NK.GlobalCFT.Place ↥K` (it is `Place.ofFinite q` or
`Place.ofInfinite v`).  For a finite place `q` of `K` use
`Work.SSGRoute.glue_fin_decomp_ex`, which produces a finite place `A` of `Ω` with
`decompK (ofFinite q) ≤ (decomp k A).map (res k K)`; for an infinite place `v` use
`Work.SSGRoute.glue_infinite_place`, which says the stabiliser is either `⊥` (and then
`IsCoboundaryOn _ ⊥ ψ` holds by taking `m = 0`, using the hypothesis `ψ 1 = 0`) or is contained in
`(zpowers σ).map (res k K)` for an involution `σ` of `G_k`.  `IsCoboundaryOn` is monotone in the
subgroup. -/
theorem glue_local_of_sha1_conditions (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (M : Type) [AddCommGroup M]
    [DistribMulAction (K ≃ₐ[k] K) M]
    (ψ : (K ≃ₐ[k] K) → M) (h1 : ψ 1 = 0)
    (hfin : ∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
      SSGRoute.IsCoboundaryOn (MonoidHom.id (K ≃ₐ[k] K))
        ((SSGRoute.decomp k A).map (SSGRoute.res k K)) ψ)
    (hinf : ∀ σ : Ω ≃ₐ[k] Ω, σ ^ 2 = 1 →
      SSGRoute.IsCoboundaryOn (MonoidHom.id (K ≃ₐ[k] K))
        ((Subgroup.zpowers σ).map (SSGRoute.res k K)) ψ) :
    ∀ w : NK.GlobalCFT.Place ↥K,
      SSGRoute.IsCoboundaryOn (MonoidHom.id (K ≃ₐ[k] K))
        (SSGRoute.PTExt.decompK (k := k) w) ψ := by
  intro w
  -- `NK.GlobalCFT.Place K = InfinitePlace K ⊕ HeightOneSpectrum (𝓞 K)`, so `w` is either
  -- archimedean or nonarchimedean, and we handle the two cases with the two place glue lemmas.
  cases w with
  | inl v =>
    -- `w = Place.ofInfinite v` is an archimedean place of `K`.
    rcases glue_infinite_place k Ω K v with hbot | ⟨σ, hσ2, hle⟩
    · -- The decomposition group is trivial: take the witnessing element `m = 0`.
      have hd : SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite v) = ⊥ := hbot
      rw [hd]
      exact isCoboundaryOn_bot h1
    · -- The decomposition group sits inside the image of the involutions `⟨σ⟩`.
      exact isCoboundaryOn_mono_glue hle (hinf σ hσ2)
  | inr q =>
    -- `w = Place.ofFinite q` is a nonarchimedean place of `K`.
    obtain ⟨A, hAfin, hAle⟩ := glue_fin_decomp_ex k Ω K q
    exact isCoboundaryOn_mono_glue hAle (hfin A hAfin)

end Work.SSGRoute

import Mathlib

/-!
# Currying of locally constant functions on a light profinite set

For a compact space `S`, a topological space `T` and a type `M`, a locally constant function
`φ : S × T → M` is the same thing as a locally constant function `T → LocallyConstant S M`,
sending `φ` to `t ↦ (s ↦ φ (s, t))`.

The only non-trivial point is that `t ↦ (s ↦ φ (s, t))` is *locally constant*: for `t'` near `t`
the whole function `s ↦ φ (s, t')` must agree with `s ↦ φ (s, t)`, uniformly in `s`.  Compactness
of `S` supplies this: `φ` is constant on a neighbourhood of each `(s, t)`, and a finite subcover
of `S` cuts down a neighbourhood of `t` on which the `s`-dependence no longer varies.

The main result `exists_lcCurry` states that this currying is a `ℤ`-linear equivalence
`LocallyConstant (S × T) M ≃ₗ[ℤ] LocallyConstant T (LocallyConstant S M)` when `M` is a
`ℤ`-module.
-/

open scoped Topology

namespace Work.ANALYTIC.CechPt

/-- The *unbundled* currying of `φ : LocallyConstant (S × T) M`: the function
`t ↦ (s ↦ φ (s, t))`, with the inner local constancy supplied by continuity of `s ↦ (s, t)`. -/
noncomputable def lcCurryFun {S T M : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (φ : LocallyConstant (S × T) M) : T → LocallyConstant S M :=
  fun t => ⟨fun s => φ (s, t),
    φ.isLocallyConstant.comp_continuous (continuous_id.prodMk continuous_const)⟩

/-- **Compactness step.** For a compact space `S` and any topological space `T`, the function
`t ↦ (s ↦ φ (s, t))` is locally constant as soon as `φ` is locally constant on `S × T`: near any
`t` the whole family `s ↦ φ (s, t')` is literally equal to `s ↦ φ (s, t)`. -/
lemma exists_nhds_lcCurryFun {S T M : Type*} [TopologicalSpace S] [TopologicalSpace T]
    [CompactSpace S] (φ : LocallyConstant (S × T) M) (t : T) :
    ∃ U ∈ 𝓝 t, ∀ t' ∈ U, ∀ s, φ (s, t') = φ (s, t) := by
  -- Each `s` has a product neighbourhood `V s ×ˢ W s` of `(s, t)` on which `φ` is constant,
  -- with value `φ (s, t)`.
  have key : ∀ s : S, ∃ V : Set S, ∃ W : Set T, IsOpen V ∧ s ∈ V ∧ IsOpen W ∧ t ∈ W ∧
      ∀ a ∈ V, ∀ b ∈ W, φ (a, b) = φ (s, t) := by
    intro s
    have h : ∀ᶠ p in 𝓝 (s, t), φ p = φ (s, t) :=
      (IsLocallyConstant.iff_eventually_eq _).mp φ.isLocallyConstant (s, t)
    rw [nhds_prod_eq] at h
    obtain ⟨V₀, hV₀, W₀, hW₀, hVW⟩ := Filter.mem_prod_iff.mp h
    obtain ⟨V, hVs, hVopen, hsV⟩ := mem_nhds_iff.mp hV₀
    obtain ⟨W, hWs, hWopen, htW⟩ := mem_nhds_iff.mp hW₀
    exact ⟨V, W, hVopen, hsV, hWopen, htW,
      fun a ha b hb => hVW (Set.mk_mem_prod (hVs ha) (hWs hb))⟩
  choose V W hVopen hsV hWopen htW hVW using key
  -- Compactness of `S` cuts the `s`-direction down to finitely many `V s`.
  obtain ⟨t₀, hcov⟩ := isCompact_univ.elim_finite_subcover V (fun s => hVopen s)
      (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hsV x⟩)
  refine ⟨⋂ i ∈ (↑t₀ : Set S), W i, ?_, ?_⟩
  · rw [Filter.biInter_mem (Finset.finite_toSet t₀)]
    exact fun i _ => mem_nhds_iff.mpr ⟨W i, subset_rfl, hWopen i, htW i⟩
  · intro t' ht' s
    have h1 : s ∈ ⋃ i ∈ (↑t₀ : Set S), V i := hcov (Set.mem_univ s)
    obtain ⟨i, hi, hsi⟩ := by simpa only [Set.mem_iUnion] using h1
    have h2 : ∀ j, j ∈ (↑t₀ : Set S) → t' ∈ W j := by
      simpa only [Set.mem_iInter] using ht'
    rw [hVW i s hsi t' (h2 i hi), hVW i s hsi t (htW i)]

/-- The curried function, bundled as a locally constant function. -/
noncomputable def lcCurry {S T M : Type*} [TopologicalSpace S] [TopologicalSpace T]
    [CompactSpace S] (φ : LocallyConstant (S × T) M) :
    LocallyConstant T (LocallyConstant S M) :=
  ⟨lcCurryFun φ, by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t
    obtain ⟨U, hU, hUt⟩ := exists_nhds_lcCurryFun φ t
    exact Filter.mem_of_superset hU fun t' ht' => LocallyConstant.ext fun s => hUt t' ht' s⟩

/-- The uncurried function `(s, t) ↦ ψ t s` is locally constant (no compactness needed). -/
lemma isLocallyConstant_uncurryFun {S T M : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (ψ : LocallyConstant T (LocallyConstant S M)) :
    IsLocallyConstant fun p : S × T => ψ p.2 p.1 := by
  rw [IsLocallyConstant.iff_eventually_eq]
  rintro ⟨s, t⟩
  have hA : {t' : T | ψ t' = ψ t} ∈ 𝓝 t :=
    (IsLocallyConstant.iff_eventually_eq _).mp ψ.isLocallyConstant t
  have hB : {s' : S | ψ t s' = ψ t s} ∈ 𝓝 s :=
    (IsLocallyConstant.iff_eventually_eq _).mp (ψ t).isLocallyConstant s
  rw [nhds_prod_eq]
  exact Filter.mem_of_superset (Filter.prod_mem_prod hB hA)
    (by
      rintro ⟨s', t'⟩ ⟨hs', ht'⟩
      simp only [Set.mem_ofPred_eq] at hs' ht' ⊢
      exact (congrArg (fun f : LocallyConstant S M => f s') ht').trans hs')

/-- The uncurried function, bundled as a locally constant function. -/
noncomputable def lcUncurry {S T M : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (ψ : LocallyConstant T (LocallyConstant S M)) : LocallyConstant (S × T) M :=
  ⟨fun p => ψ p.2 p.1, isLocallyConstant_uncurryFun ψ⟩

/-- The currying linear equivalence `LocallyConstant (S × T) M ≃ₗ[ℤ] LocallyConstant T
(LocallyConstant S M)` for light profinite `S` (compact!) and `T` and a `ℤ`-module `M`. -/
noncomputable def lcCurryEquiv (S T : LightProfinite.{0}) (M : ModuleCat.{0} ℤ) :
    LocallyConstant (↥S.toTop × ↥T.toTop) ↥M ≃ₗ[ℤ]
      LocallyConstant ↥T.toTop (LocallyConstant ↥S.toTop ↥M) where
  toFun := lcCurry
  invFun := lcUncurry
  left_inv := by
    intro φ
    apply LocallyConstant.ext
    intro p
    rfl
  right_inv := by
    intro ψ
    apply LocallyConstant.ext
    intro t
    apply LocallyConstant.ext
    intro s
    rfl
  map_add' := by
    intro φ₁ φ₂
    ext t s
    simp [lcCurry, lcCurryFun, LocallyConstant.add_apply]
  map_smul' := by
    intro c φ
    ext t s
    simp [lcCurry, lcCurryFun, LocallyConstant.smul_apply]

theorem exists_lcCurry (S T : LightProfinite.{0}) (M : ModuleCat.{0} ℤ) :
    ∃ e : LocallyConstant (↥S.toTop × ↥T.toTop) ↥M ≃ₗ[ℤ]
        LocallyConstant ↥T.toTop (LocallyConstant ↥S.toTop ↥M),
      ∀ (φ : LocallyConstant (↥S.toTop × ↥T.toTop) ↥M) (t : ↥T.toTop) (s : ↥S.toTop),
        e φ t s = φ (s, t) :=
  ⟨lcCurryEquiv S T M, fun _ _ _ => rfl⟩

end Work.ANALYTIC.CechPt

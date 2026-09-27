import Mathlib
import Submission.Work.Projection.mfderiv_chartAt_decomp

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


open scoped Manifold ContDiff
open Topology Set Function

namespace Work.Isotopy

/-- On `ℝ × F` the product model and the self model induce the same smoothness (they are equal,
but not definitionally so). -/
private theorem contMDiffOn_prod_iff_contDiffOn {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : ℝ × F → G} {s : Set (ℝ × F)} :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, F))) (𝓘(ℝ, G)) ((↑(⊤ : ℕ∞) : WithTop ℕ∞)) f s ↔
      ContDiffOn ℝ ((↑(⊤ : ℕ∞) : WithTop ℕ∞)) f s := by
  have h1 : (𝓘(ℝ, ℝ)).prod (𝓘(ℝ, F)) = 𝓘(ℝ, ℝ × F) := by
    rw [modelWithCornersSelf_prod]
  rw [h1]
  rw [show prodChartedSpace ℝ ℝ F F = chartedSpaceSelf (ℝ × F) from chartedSpaceSelf_prod]
  exact contMDiffOn_iff_contDiffOn

private theorem local_leftInverse_aux {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {G : ℝ × E → F} {U : Set (ℝ × E)} (hU : IsOpen U) {s₀ : ℝ} {p : E} (hUp : (s₀, p) ∈ U)
    (hG : ContDiffOn ℝ ((↑(⊤ : ℕ∞) : WithTop ℕ∞)) G U)
    (hinj : Function.Injective (fun v : E => fderiv ℝ G (s₀, p) (0, v))) :
    ∃ (O : Set ℝ) (V : Set E) (W : Set F) (h : ℝ → F → E),
      IsOpen O ∧ s₀ ∈ O ∧ IsOpen V ∧ p ∈ V ∧ IsOpen W ∧ G (s₀, p) ∈ W ∧
      ContDiffOn ℝ ((↑(⊤ : ℕ∞) : WithTop ℕ∞)) (Function.uncurry h) (O ×ˢ W) ∧
      (∀ s ∈ O, ∀ y ∈ V, h s (G (s, y)) = y) := by
  classical
  let L : (ℝ × E) →L[ℝ] F := fderiv ℝ G (s₀, p)
  let A : F := L (1, 0)
  let D : E →L[ℝ] F := L ∘L ContinuousLinearMap.inr ℝ ℝ E
  have hDinj : Function.Injective (D : E → F) := hinj
  have hLA : ∀ q : ℝ × E, L q - q.1 • A = D q.2 := by
    intro q
    have hq : q = (q.1, 0) + (0, q.2) := by ext <;> simp
    have hq2 : (q.1, (0 : E)) = q.1 • ((1 : ℝ), (0 : E)) := by simp
    have e1 : L q = L (q.1, 0) + L (0, q.2) := by
      conv_lhs => rw [hq]
      rw [map_add]
    have e2 : L (q.1, 0) = q.1 • A := by rw [hq2, map_smul]
    have e3 : L (0, q.2) = D q.2 := rfl
    rw [e1, e2, e3]
    abel
  let S : Submodule ℝ F := LinearMap.range (D : E →ₗ[ℝ] F)
  obtain ⟨K, hK⟩ := Submodule.exists_isCompl S
  have hSfd : FiniteDimensional ℝ ↥S := FiniteDimensional.finiteDimensional_submodule S
  have hKfd : FiniteDimensional ℝ ↥K := FiniteDimensional.finiteDimensional_submodule K
  have hKbot : S ⊓ K = ⊥ := hK.inf_eq_bot
  have hKtop : S ⊔ K = ⊤ := hK.sup_eq_top
  let Φ : (ℝ × E) × ↥K →ₗ[ℝ] ℝ × F :=
    LinearMap.prod
      ((LinearMap.fst ℝ ℝ E).comp (LinearMap.fst ℝ (ℝ × E) ↥K))
      ((D : E →ₗ[ℝ] F).comp ((LinearMap.snd ℝ ℝ E).comp (LinearMap.fst ℝ (ℝ × E) ↥K)) +
        (Submodule.subtype K).comp (LinearMap.snd ℝ (ℝ × E) ↥K))
  have hΦ_apply : ∀ x : (ℝ × E) × ↥K, Φ x = (x.1.1, D x.1.2 + (x.2 : F)) := fun x => rfl
  have hinjΦ : Function.Injective Φ := by
    intro x y hxy
    have h1 : x.1.1 = y.1.1 := by
      have := congrArg Prod.fst hxy
      simpa only [hΦ_apply] using this
    have h2 : D x.1.2 + (x.2 : F) = D y.1.2 + (y.2 : F) := by
      have := congrArg Prod.snd hxy
      simpa only [hΦ_apply] using this
    have h3 : (x.2 : F) - (y.2 : F) = D (y.1.2 - x.1.2) := by
      rw [map_sub]
      rw [sub_eq_sub_iff_add_eq_add]
      rw [add_comm (x.2 : F)]
      exact h2
    have h3mem : (x.2 : F) - (y.2 : F) ∈ S ⊓ K := by
      constructor
      · rw [h3]
        exact ⟨y.1.2 - x.1.2, rfl⟩
      · exact K.sub_mem x.2.2 y.2.2
    have h3zero : (x.2 : F) - (y.2 : F) = 0 := by
      have := hKbot ▸ h3mem
      simpa using this
    have hk : x.2 = y.2 := Subtype.ext (sub_eq_zero.mp h3zero)
    have h12 : x.1.2 = y.1.2 := by
      apply hDinj
      have h2' := h2
      rw [hk] at h2'
      exact add_right_cancel h2'
    have h11 : x.1 = y.1 := Prod.ext h1 h12
    exact Prod.ext h11 hk
  have hsurjΦ : Function.Surjective Φ := by
    intro y
    obtain ⟨s, hs, k, hk, hsk⟩ := Submodule.mem_sup.mp (show (y.2 : F) ∈ S ⊔ K by rw [hKtop]; trivial)
    obtain ⟨b, hb⟩ := LinearMap.mem_range.mp (show s ∈ LinearMap.range (D : E →ₗ[ℝ] F) from hs)
    refine ⟨((y.1, b), ⟨k, hk⟩), ?_⟩
    rw [hΦ_apply]
    refine Prod.ext rfl ?_
    show D b + k = y.2
    rw [← hb] at hsk
    exact hsk
  let eAllₗ := LinearEquiv.ofBijective Φ ⟨hinjΦ, hsurjΦ⟩
  let eAll := eAllₗ.toContinuousLinearEquiv
  let eAllCL : (ℝ × E) × ↥K →L[ℝ] ℝ × F := eAllₗ.toContinuousLinearEquiv
  have heAll_apply : ∀ x : (ℝ × E) × ↥K, eAllCL x = (x.1.1, D x.1.2 + (x.2 : F)) := by
    intro x
    have h1 : eAllCL x = eAllₗ x := rfl
    have h2 : eAllₗ x = Φ x := rfl
    rw [h1, h2, hΦ_apply]
  have hfinrk : Module.finrank ℝ ((ℝ × E) × ↥K) = Module.finrank ℝ (ℝ × F) :=
    LinearEquiv.finrank_eq eAllₗ
  let a₀ : (ℝ × E) × ↥K := ((s₀, p), 0)
  let Ξ : (ℝ × E) × ↥K → ℝ × F := fun x => (x.1.1, G x.1 - (x.1.1 - s₀) • A + (x.2 : F))
  have hWU : IsOpen {x : (ℝ × E) × ↥K | x.1 ∈ U} := hU.preimage continuous_fst
  have hΞ_cont : ContDiffOn ℝ ((↑(⊤ : ℕ∞) : WithTop ℕ∞)) Ξ {x : (ℝ × E) × ↥K | x.1 ∈ U} := by
    have h1 : ContDiffOn ℝ ((↑(⊤ : ℕ∞) : WithTop ℕ∞))
        (fun x : (ℝ × E) × ↥K => x.1.1) {x | x.1 ∈ U} := contDiffOn_fst.fst
    have h2 : ContDiffOn ℝ ((↑(⊤ : ℕ∞) : WithTop ℕ∞))
        (fun x : (ℝ × E) × ↥K => G x.1) {x | x.1 ∈ U} :=
      hG.comp contDiffOn_fst (fun x hx => hx)
    have h3 : ContDiffOn ℝ ((↑(⊤ : ℕ∞) : WithTop ℕ∞))
        (fun x : (ℝ × E) × ↥K => (x.1.1 - s₀) • A) {x | x.1 ∈ U} :=
      (h1.sub contDiffOn_const).smul_const A
    have h4 : ContDiffOn ℝ ((↑(⊤ : ℕ∞) : WithTop ℕ∞))
        (fun x : (ℝ × E) × ↥K => (x.2 : F)) {x | x.1 ∈ U} :=
      ((Submodule.subtypeL K).contDiff.contDiffOn).comp contDiffOn_id.snd
        (fun x _ => Set.mem_univ _)
    exact ContDiffOn.prodMk h1 ((h2.sub h3).add h4)
  have ha₀U : a₀ ∈ {x : (ℝ × E) × ↥K | x.1 ∈ U} := hUp
  have hΞ_at : ContDiffAt ℝ ((↑(⊤ : ℕ∞) : WithTop ℕ∞)) Ξ a₀ :=
    hΞ_cont.contDiffAt (hWU.mem_nhds ha₀U)
  have hG_at : HasFDerivAt G L (s₀, p) := by
    have h := (hG.contDiffAt (hU.mem_nhds hUp)).differentiableAt (by simp)
    simpa only [L] using h.hasFDerivAt
  have hΞ_deriv : HasFDerivAt Ξ eAllCL a₀ := by
    have hfst : HasFDerivAt (fun x : (ℝ × E) × ↥K => x.1.1)
        ((ContinuousLinearMap.fst ℝ ℝ E).comp (ContinuousLinearMap.fst ℝ (ℝ × E) ↥K)) a₀ :=
      (hasFDerivAt_fst (p := a₀.1)).comp a₀ (hasFDerivAt_fst (p := a₀))
    have hGd : HasFDerivAt (fun x : (ℝ × E) × ↥K => G x.1)
        (L ∘L (ContinuousLinearMap.fst ℝ (ℝ × E) ↥K)) a₀ :=
      hG_at.comp a₀ (hasFDerivAt_fst (p := a₀))
    have hsm : HasFDerivAt (fun x : (ℝ × E) × ↥K => (x.1.1 - s₀) • A)
        (((ContinuousLinearMap.fst ℝ ℝ E).comp (ContinuousLinearMap.fst ℝ (ℝ × E) ↥K)).smulRight A) a₀ :=
      (hfst.sub_const s₀).smul_const A
    have hk : HasFDerivAt (fun x : (ℝ × E) × ↥K => (x.2 : F))
        ((Submodule.subtypeL K).comp (ContinuousLinearMap.snd ℝ (ℝ × E) ↥K)) a₀ :=
      (Submodule.subtypeL K).hasFDerivAt.comp a₀ (hasFDerivAt_snd (p := a₀))
    have hbody := (hGd.sub hsm).add hk
    have hclm : ((ContinuousLinearMap.fst ℝ ℝ E).comp (ContinuousLinearMap.fst ℝ (ℝ × E) ↥K)).prod
        ((L ∘L (ContinuousLinearMap.fst ℝ (ℝ × E) ↥K)) -
          (((ContinuousLinearMap.fst ℝ ℝ E).comp (ContinuousLinearMap.fst ℝ (ℝ × E) ↥K)).smulRight A) +
          ((Submodule.subtypeL K).comp (ContinuousLinearMap.snd ℝ (ℝ × E) ↥K)))
        = eAllCL := by
      apply ContinuousLinearMap.ext
      intro x
      rw [ContinuousLinearMap.prod_apply, heAll_apply]
      refine Prod.ext rfl ?_
      show L x.1 - x.1.1 • A + (x.2 : F) = D x.1.2 + (x.2 : F)
      rw [hLA x.1]
    have hprod := hfst.prodMk hbody
    rw [hclm] at hprod
    exact hprod
  -- ## the inverse function theorem
  let e : OpenPartialHomeomorph ((ℝ × E) × ↥K) (ℝ × F) :=
    hΞ_at.toOpenPartialHomeomorph Ξ hΞ_deriv (by simp)
  have hsa : a₀ ∈ e.source :=
    ContDiffAt.mem_toOpenPartialHomeomorph_source hΞ_at hΞ_deriv (by simp)
  have hJ : Function.Injective (fderiv ℝ Ξ a₀) := by
    rw [hΞ_deriv.fderiv]
    exact fun x y hxy => eAll.injective hxy
  let W' : Set ((ℝ × E) × ↥K) := {x | x.1 ∈ U ∧ Function.Injective (fderiv ℝ Ξ x)}
  have hW'_mem : W' ∈ 𝓝 a₀ := by
    refine Filter.inter_mem ?_ ?_
    · exact hWU.mem_nhds hUp
    · exact (hΞ_at.continuousAt_fderiv (by simp)).preimage_mem_nhds
        (ContinuousLinearMap.isOpen_injective.mem_nhds hJ)
  obtain ⟨W'', hW''sub, hW''open, ha₀W''⟩ := mem_nhds_iff.mp hW'_mem
  have hsymm_smooth : ∀ y ∈ e.target, e.symm y ∈ W'' →
      ContDiffAt ℝ ((↑(⊤ : ℕ∞) : WithTop ℕ∞)) e.symm y := by
    intro y hy hyW'
    have hyW'2 := hW''sub hyW'
    have hxAt : ContDiffAt ℝ ((↑(⊤ : ℕ∞) : WithTop ℕ∞)) Ξ (e.symm y) :=
      hΞ_cont.contDiffAt (hWU.mem_nhds hyW'2.1)
    have hxd : HasFDerivAt Ξ (fderiv ℝ Ξ (e.symm y)) (e.symm y) :=
      (hxAt.differentiableAt (by simp)).hasFDerivAt
    have hker : (fderiv ℝ Ξ (e.symm y)).ker = ⊥ := LinearMap.ker_eq_bot.mpr hyW'2.2
    have hrange : (fderiv ℝ Ξ (e.symm y)).range = ⊤ := by
      rw [LinearMap.range_eq_top]
      exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfinrk).mp hyW'2.2
    have he' : HasFDerivAt Ξ (ContinuousLinearEquiv.ofBijective (fderiv ℝ Ξ (e.symm y)) hker hrange
        : (ℝ × E) × ↥K →L[ℝ] ℝ × F) (e.symm y) := by
      rw [ContinuousLinearEquiv.coe_ofBijective (fderiv ℝ Ξ (e.symm y)) hker hrange]
      exact hxd
    exact e.contDiffAt_symm
      (f₀' := ContinuousLinearEquiv.ofBijective (fderiv ℝ Ξ (e.symm y)) hker hrange) hy he' hxAt
  let Ue : Set (ℝ × F) := e.target ∩ e.symm ⁻¹' W''
  have hUe_open : IsOpen Ue := e.isOpen_inter_preimage_symm hW''open
  have hΞa₀_mem : Ξ a₀ ∈ Ue := by
    refine ⟨e.map_source hsa, ?_⟩
    rw [Set.mem_preimage]
    have h2 : e.symm (Ξ a₀) = a₀ := e.left_inv hsa
    rw [h2]
    exact ha₀W''
  have hsmooth_e : ContDiffOn ℝ ((↑(⊤ : ℕ∞) : WithTop ℕ∞)) e.symm Ue :=
    fun y hy => (hsymm_smooth y hy.1 hy.2).contDiffWithinAt
  -- ## the final neighbourhoods
  let T : ℝ × F → ℝ × F := fun q => (q.1, q.2 - (q.1 - s₀) • A)
  have hT_cont : Continuous T := by fun_prop
  have hΞa₀ : T (s₀, G (s₀, p)) = Ξ a₀ := by
    show (s₀, G (s₀, p) - (s₀ - s₀) • A) = (s₀, G (s₀, p) - (s₀ - s₀) • A + (0 : F))
    rw [add_zero]
  have hT_mem : T ⁻¹' Ue ∈ 𝓝 (s₀, G (s₀, p)) := by
    have h1 : Ue ∈ 𝓝 (T (s₀, G (s₀, p))) := by
      rw [hΞa₀]
      exact hUe_open.mem_nhds hΞa₀_mem
    exact hT_cont.continuousAt.preimage_mem_nhds h1
  rw [nhds_prod_eq] at hT_mem
  obtain ⟨a₁, ha₁, b₁, hb₁, hsub₁⟩ := Filter.mem_prod_iff.mp hT_mem
  obtain ⟨O₁, hO₁sub, hO₁, hs₀O₁⟩ := mem_nhds_iff.mp ha₁
  obtain ⟨W₁, hW₁sub, hW₁, hgpW₁⟩ := mem_nhds_iff.mp hb₁
  have hsrc_mem : (fun q : ℝ × E => (q, (0 : ↥K))) ⁻¹' e.source ∈ 𝓝 (s₀, p) :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds hsa)
  rw [nhds_prod_eq] at hsrc_mem
  obtain ⟨a₂, ha₂, b₂, hb₂, hsub₂⟩ := Filter.mem_prod_iff.mp hsrc_mem
  obtain ⟨O₂, hO₂sub, hO₂, hs₀O₂⟩ := mem_nhds_iff.mp ha₂
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp hb₂
  refine ⟨O₁ ∩ O₂, V, W₁, fun s w => (e.symm (T (s, w))).1.2,
    hO₁.inter hO₂, ⟨hs₀O₁, hs₀O₂⟩, hV, hpV, hW₁, hgpW₁, ?_, ?_⟩
  · have hmaps : Set.MapsTo T ((O₁ ∩ O₂) ×ˢ W₁) Ue :=
      fun q hq => hsub₁ ⟨hO₁sub hq.1.1, hW₁sub hq.2⟩
    have hcomp : ContDiffOn ℝ ((↑(⊤ : ℕ∞) : WithTop ℕ∞))
        (fun q : ℝ × F => e.symm (T q)) ((O₁ ∩ O₂) ×ˢ W₁) :=
      hsmooth_e.comp (by fun_prop) hmaps
    have hproj : ContDiffOn ℝ ((↑(⊤ : ℕ∞) : WithTop ℕ∞))
        (fun z : (ℝ × E) × ↥K => z.1.2) Set.univ := by fun_prop
    exact hproj.comp hcomp (fun q _ => Set.mem_univ _)
  · intro s hs y hy
    have hsrc : ((s, y), (0 : ↥K)) ∈ e.source := hsub₂ ⟨hO₂sub hs.2, hVsub hy⟩
    have h1 : T (s, G (s, y)) = Ξ ((s, y), 0) := by
      show (s, G (s, y) - (s - s₀) • A) = (s, G (s, y) - (s - s₀) • A + (0 : F))
      rw [add_zero]
    have h3 : e.symm (Ξ ((s, y), (0 : ↥K))) = ((s, y), (0 : ↥K)) := e.left_inv hsrc
    show (e.symm (T (s, G (s, y)))).1.2 = y
    rw [h1, h3]

set_option backward.isDefEq.respectTransparency false in
theorem exists_local_retraction {n N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (↑(⊤ : ℕ∞) : WithTop ℕ∞) M]
    (Φ : ℝ → M → EuclideanSpace ℝ (Fin N))
    (hΦ : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry Φ))
    (himm : ∀ s x, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))) (Φ s) x))
    (s₀ : ℝ) (x₀ : M) :
    ∃ (O : Set ℝ) (V : Set M) (W : Set (EuclideanSpace ℝ (Fin N)))
      (ρ : ℝ → EuclideanSpace ℝ (Fin N) → M),
      IsOpen O ∧ s₀ ∈ O ∧ IsOpen V ∧ x₀ ∈ V ∧ IsOpen W ∧ Φ s₀ x₀ ∈ W ∧
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (Function.uncurry ρ) (O ×ˢ W) ∧
      (∀ s ∈ O, ∀ x ∈ V, ρ s (Φ s x) = x) := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let F := EuclideanSpace ℝ (Fin N)
  let c : OpenPartialHomeomorph M E := chartAt E x₀
  let p : E := c x₀
  let G : ℝ × E → F := fun q => Φ q.1 (c.symm q.2)
  have hΦs : ∀ s : ℝ, ContMDiff (𝓡 n) (𝓡 N) ∞ (Φ s) := fun s =>
    hΦ.comp (ContMDiff.prodMk contMDiff_const contMDiff_id)
  have hsymm : ContMDiffOn (𝓡 n) (𝓡 n) ∞ c.symm c.target :=
    contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := 𝓡 n) (n := ((↑(⊤ : ℕ∞) : WithTop ℕ∞))) x₀)
  have hpair : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ∞
      (fun q : ℝ × E => (q.1, c.symm q.2)) (Set.univ ×ˢ c.target) :=
    ContMDiffOn.prodMk contMDiffOn_fst
      (hsymm.comp (contMDiffOn_snd (s := Set.univ ×ˢ c.target)) (fun q hq => hq.2))
  have hcomp : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓡 N) ∞
      (fun q : ℝ × E => Φ q.1 (c.symm q.2)) (Set.univ ×ˢ c.target) :=
    ContMDiffOn.comp (t := Set.univ) (hΦ.contMDiffOn (s := Set.univ)) hpair
      (fun q _ => Set.mem_univ _)
  have hcomp2 : ContDiffOn ℝ ∞ (fun q : ℝ × E => Φ q.1 (c.symm q.2)) (Set.univ ×ˢ c.target) :=
    contMDiffOn_prod_iff_contDiffOn.mp hcomp
  have hG : ContDiffAt ℝ ∞ G (s₀, p) := by
    refine hcomp2.contDiffAt ?_
    exact (isOpen_univ.prod c.open_target).mem_nhds ⟨trivial, mem_chart_target E x₀⟩
  have hB : fderiv ℝ (fun y : E => Φ s₀ (c.symm y)) p =
      (fderiv ℝ G (s₀, p)) ∘L ContinuousLinearMap.inr ℝ ℝ E := by
    have hinner : HasFDerivAt (fun y : E => (s₀, y)) (ContinuousLinearMap.inr ℝ ℝ E) p :=
      hasFDerivAt_prodMk_right s₀ p
    have hGd : HasFDerivAt G (fderiv ℝ G (s₀, p)) (s₀, p) :=
      (hG.differentiableAt (by simp)).hasFDerivAt
    have hcomp' : HasFDerivAt (fun y : E => Φ s₀ (c.symm y))
        ((fderiv ℝ G (s₀, p)) ∘L ContinuousLinearMap.inr ℝ ℝ E) p := hGd.comp p hinner
    exact hcomp'.fderiv
  have hA : mfderiv (𝓡 n) (𝓡 n) c x₀ =
      ContinuousLinearMap.id ℝ (TangentSpace (𝓡 n) x₀) := by
    rw [mfderiv_chartAt_eq_tangentCoordChange (I := 𝓡 n) (H := E) (M := M)
      (x := x₀) (y := x₀) (mem_chart_source _ x₀)]
    apply ContinuousLinearMap.ext
    intro v
    exact tangentCoordChange_self (I := 𝓡 n) (x := x₀) (z := x₀) (mem_extChartAt_source x₀)
  have hdecomp : mfderiv (𝓡 n) (𝓡 N) (Φ s₀) x₀ =
      (fderiv ℝ (fun y : E => Φ s₀ (c.symm y)) p) ∘L mfderiv (𝓡 n) (𝓡 n) c x₀ :=
    Work.Projection.mfderiv_chartAt_decomp (n := n) (N := N) (f := Φ s₀) (hf := hΦs s₀)
      (p := x₀) (x := x₀) (hx := mem_chart_source _ x₀)
  have hinj : Function.Injective (fun v : E => fderiv ℝ G (s₀, p) (0, v)) := by
    have hBinj : Function.Injective (fderiv ℝ (fun y : E => Φ s₀ (c.symm y)) p) := by
      have hEq : fderiv ℝ (fun y : E => Φ s₀ (c.symm y)) p =
          mfderiv (𝓡 n) (𝓡 N) (Φ s₀) x₀ := by
        rw [hdecomp, hA, ContinuousLinearMap.comp_id]
      rw [hEq]
      exact himm s₀ x₀
    change Function.Injective ((fderiv ℝ G (s₀, p)) ∘L ContinuousLinearMap.inr ℝ ℝ E)
    rw [← hB]
    exact hBinj
  obtain ⟨O₀, U₀, W₀, h, hO₀, hs₀O₀, hU₀, hpU₀, hW₀, hgpW₀, hh, hid⟩ :=
    local_leftInverse_aux (G := G) (U := Set.univ ×ˢ c.target) (s₀ := s₀) (p := p)
      (isOpen_univ.prod c.open_target) ⟨trivial, mem_chart_target E x₀⟩ hcomp2 hinj
  have hbase : h s₀ (G (s₀, p)) = p := hid s₀ hs₀O₀ p hpU₀
  have hgpeq : G (s₀, p) = Φ s₀ x₀ := by
    change Φ s₀ (c.symm (c x₀)) = Φ s₀ x₀
    rw [c.left_inv (mem_chart_source _ x₀)]
  have hcont : ContinuousAt (Function.uncurry h) (s₀, G (s₀, p)) :=
    hh.continuousOn.continuousAt ((hO₀.prod hW₀).mem_nhds ⟨hs₀O₀, hgpW₀⟩)
  have hnhds1 : (Function.uncurry h) ⁻¹' c.target ∈ 𝓝 (s₀, G (s₀, p)) :=
    hcont.preimage_mem_nhds
      (c.open_target.mem_nhds (by rw [Function.uncurry_apply_pair, hbase]; exact mem_chart_target E x₀))
  have hnhds : ((Function.uncurry h) ⁻¹' c.target) ∩ (O₀ ×ˢ W₀) ∈ 𝓝 (s₀, G (s₀, p)) :=
    Filter.inter_mem hnhds1 ((hO₀.prod hW₀).mem_nhds ⟨hs₀O₀, hgpW₀⟩)
  rw [nhds_prod_eq] at hnhds
  obtain ⟨O₁, hO₁, W₁, hW₁, hsub⟩ := Filter.mem_prod_iff.mp hnhds
  obtain ⟨O₂, hO₂sub, hO₂, hs₀O₂⟩ := mem_nhds_iff.mp hO₁
  obtain ⟨W₂, hW₂sub, hW₂, hgpW₂⟩ := mem_nhds_iff.mp hW₁
  have hOWsub : (O₂ ∩ O₀) ×ˢ (W₂ ∩ W₀) ⊆ O₁ ×ˢ W₁ :=
    fun q hq => ⟨hO₂sub hq.1.1, hW₂sub hq.2.1⟩
  refine ⟨O₂ ∩ O₀, c.symm '' (U₀ ∩ c.target), W₂ ∩ W₀, fun s w => c.symm (h s w),
    hO₂.inter hO₀, ⟨hs₀O₂, hs₀O₀⟩,
    c.isOpen_image_symm_of_subset_target (hU₀.inter c.open_target) inter_subset_right,
    ⟨p, ⟨hpU₀, mem_chart_target E x₀⟩, c.left_inv (mem_chart_source _ x₀)⟩,
    hW₂.inter hW₀, ?_, ?_, ?_⟩
  · rw [← hgpeq]; exact ⟨hgpW₂, hgpW₀⟩
  · have hmapsTo : ∀ q ∈ (O₂ ∩ O₀) ×ˢ (W₂ ∩ W₀), Function.uncurry h q ∈ c.target :=
      fun q hq => (hsub (hOWsub hq)).1
    have hh' : ContDiffOn ℝ ∞ (Function.uncurry h) ((O₂ ∩ O₀) ×ˢ (W₂ ∩ W₀)) :=
      hh.mono (fun q hq => (hsub (hOWsub hq)).2)
    have hh'' : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 N)) (𝓘(ℝ, E)) ∞ (Function.uncurry h)
        ((O₂ ∩ O₀) ×ˢ (W₂ ∩ W₀)) :=
      (contMDiffOn_prod_iff_contDiffOn (F := EuclideanSpace ℝ (Fin N))).mpr hh'
    exact hsymm.comp hh'' (fun q hq => hmapsTo q hq)
  · intro s hs x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h2 : h s (Φ s (c.symm y)) = y := hid s hs.2 y hy.1
    show c.symm (h s (Φ s (c.symm y))) = c.symm y
    rw [h2]

end Work.Isotopy

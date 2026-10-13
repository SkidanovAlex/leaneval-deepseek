import Mathlib
import Submission.Work.WilE2.RegVals.isClosed_setOf_not_surjective
import Submission.Work.WilE9G.Sard.levelSetChartAnalytic
import Submission.Work.WilE9G.Sard.levelSetChartTransport

/-!
# `levelSetChartParam`: a chart for the level set of a submersion

Given `h : ℝ^Q → ℝ^j` which is analytic everywhere and whose differential at `z₀` is surjective,
the level set `{h = h z₀}` is, near `z₀`, the image of an analytic chart `γ` of a neighbourhood
`V` of `0` in the kernel `K = ker (fderiv ℝ h z₀)`, and the tangent space of the level set at
`γ t` is `ker (fderiv ℝ h (γ t))`.  Moreover the linear projection `C` onto the kernel used to
build the chart is a left inverse of `γ` on the level points.

The proof is assembled from three ingredients:

* `fderiv_surj_on_nhds` — surjectivity of the differential persists on a neighbourhood of `z₀`
  (openness of surjectivity of finite-dimensional continuous linear maps);
* `levelSetChartKer` — the chart in the kernel model, together with the tangent space identity;
* `levelSetChartTransport` — reindexing the chart along a linear equivalence
  `(Fin r → ℝ) ≃L[ℝ] ker (fderiv ℝ h z₀)`.
-/

namespace Work.WilE9G.Sard

open Set Filter
open scoped Topology

/-! ## Step 1: the derivative of an everywhere-analytic map is continuous -/

lemma continuous_fderiv_of_analyticAt {Q j : ℕ} {h : (Fin Q → ℝ) → (Fin j → ℝ)}
    (hh : ∀ x, AnalyticAt ℝ h x) : Continuous (fderiv ℝ h) :=
  (AnalyticOn.contDiff (𝕜 := ℝ) (n := 1) (fun x _ => (hh x).analyticWithinAt)).continuous_fderiv
    (by norm_num)

/-! ## Step 2: surjectivity of the derivative persists on a neighbourhood -/

theorem fderiv_surj_on_nhds {Q j : ℕ} (h : (Fin Q → ℝ) → (Fin j → ℝ)) (z₀ : Fin Q → ℝ)
    (hh : ∀ x, AnalyticAt ℝ h x) (hsurj : Function.Surjective (fderiv ℝ h z₀)) :
    ∃ U : Set (Fin Q → ℝ), IsOpen U ∧ z₀ ∈ U ∧ ∀ x ∈ U, (fderiv ℝ h x).range = ⊤ := by
  refine ⟨(fderiv ℝ h) ⁻¹'
      {T : (Fin Q → ℝ) →L[ℝ] (Fin j → ℝ) | Function.Surjective T},
    WilE2.RegVals.isOpen_setOf_surjective.preimage (continuous_fderiv_of_analyticAt hh),
    hsurj, ?_⟩
  exact fun x hx => LinearMap.range_eq_top.mpr hx

/-! ## Step 3: rank–nullity for a surjective map `ℝ^Q → ℝ^j` -/

lemma finrank_ker_of_surjective (Q j : ℕ) (A : (Fin Q → ℝ) →L[ℝ] (Fin j → ℝ))
    (hA : A.range = ⊤) : Module.finrank ℝ A.ker = Q - j := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (A : (Fin Q → ℝ) →ₗ[ℝ] (Fin j → ℝ))
  rw [hA] at h1
  rw [finrank_top] at h1
  simp only [Module.finrank_fin_fun] at h1
  omega

/-! ## Step 4: the level-set chart in the kernel model, with the tangent-space identity -/

theorem levelSetChartKer {Q j : ℕ} (h : (Fin Q → ℝ) → (Fin j → ℝ)) (z₀ : Fin Q → ℝ)
    (hh : ∀ x, AnalyticAt ℝ h x) (hsurj : Function.Surjective (fderiv ℝ h z₀)) :
    ∃ (γ : (fderiv ℝ h z₀).ker → (Fin Q → ℝ))
      (C : (Fin Q → ℝ) →L[ℝ] (fderiv ℝ h z₀).ker)
      (V : Set (fderiv ℝ h z₀).ker) (U : Set (Fin Q → ℝ)),
      IsOpen V ∧ IsOpen U ∧ (0 : (fderiv ℝ h z₀).ker) ∈ V ∧ z₀ ∈ U ∧ γ 0 = z₀ ∧
      (∀ t ∈ V, AnalyticAt ℝ γ t) ∧ (∀ t ∈ V, γ t ∈ U) ∧ (∀ t ∈ V, h (γ t) = h z₀) ∧
      (∀ y ∈ U, h y = h z₀ → C (y - z₀) ∈ V ∧ γ (C (y - z₀)) = y) ∧
      (∀ t ∈ V, (fderiv ℝ γ t).range = (fderiv ℝ h (γ t)).ker) := by
  obtain ⟨C, γ, V₀, U₀, hV₀o, hU₀o, h0V₀, hz₀U₀, hγ0, hγan, hγU₀, hhγ, hCγ, hχ₀⟩ :=
    levelSetChartAnalytic h z₀ hh hsurj
  obtain ⟨W, hWo, hz₀W, hsurjW⟩ := fderiv_surj_on_nhds h z₀ hh hsurj
  -- shrink the neighbourhoods so that every level point in `U` sits over `V`
  set U : Set (Fin Q → ℝ) := U₀ ∩ W ∩ {y | C (y - z₀) ∈ V₀} with hUdef
  set V : Set (fderiv ℝ h z₀).ker := V₀ ∩ γ ⁻¹' U with hVdef
  have hCcont : Continuous fun y : Fin Q → ℝ => C (y - z₀) :=
    C.continuous.comp (continuous_id.sub continuous_const)
  have hUo : IsOpen U := by
    rw [hUdef]
    exact (hU₀o.inter hWo).inter (hV₀o.preimage hCcont)
  have hz₀U : z₀ ∈ U := by
    rw [hUdef]
    refine ⟨⟨hz₀U₀, hz₀W⟩, ?_⟩
    simpa using h0V₀
  have h0V : (0 : (fderiv ℝ h z₀).ker) ∈ V := by
    rw [hVdef]
    exact ⟨h0V₀, by rw [Set.mem_preimage, hγ0]; exact hz₀U⟩
  have hVo : IsOpen V := by
    rw [hVdef, isOpen_iff_mem_nhds]
    rintro t ht
    exact Filter.inter_mem (hV₀o.mem_nhds ht.1)
      ((hγan t ht.1).continuousAt.preimage_mem_nhds (hUo.mem_nhds ht.2))
  have hχ : ∀ y ∈ U, h y = h z₀ → C (y - z₀) ∈ V ∧ γ (C (y - z₀)) = y := by
    intro y hy hyh
    have hyU : y ∈ U := hy
    rw [hUdef] at hy
    obtain ⟨⟨hyU₀, -⟩, -⟩ := hy
    obtain ⟨hy1, hy2⟩ := hχ₀ y hyU₀ hyh
    refine ⟨⟨hy1, ?_⟩, hy2⟩
    rw [Set.mem_preimage, hy2]
    exact hyU
  refine ⟨γ, C, V, U, hVo, hUo, h0V, hz₀U, hγ0, ?_, ?_, ?_, hχ, ?_⟩
  · intro t ht; exact hγan t ht.1
  · intro t ht; exact ht.2
  · intro t ht; exact hhγ t ht.1
  · -- the tangent space of the level set is the kernel of the derivative
    intro t ht
    rw [hVdef] at ht
    obtain ⟨htV₀, htU⟩ := ht
    rw [hUdef] at htU
    obtain ⟨⟨-, htW⟩, -⟩ := htU
    have hsurjt : (fderiv ℝ h (γ t)).range = ⊤ := hsurjW (γ t) htW
    have hdt : DifferentiableAt ℝ γ t := (hγan t htV₀).differentiableAt
    have hdh : DifferentiableAt ℝ h (γ t) := (hh (γ t)).differentiableAt
    -- `h ∘ γ` and `C (γ · - z₀)` are constant, resp. the identity, near `t`
    have hG : (h ∘ γ) =ᶠ[𝓝 t] Function.const _ (h z₀) := by
      filter_upwards [hV₀o.mem_nhds htV₀] with s hs using hhγ s hs
    have hF : ((fun y : Fin Q → ℝ => C (y - z₀)) ∘ γ) =ᶠ[𝓝 t] id := by
      filter_upwards [hV₀o.mem_nhds htV₀] with s hs using hCγ s hs
    have hcomp_h : (fderiv ℝ h (γ t)).comp (fderiv ℝ γ t) = 0 := by
      have h1 : fderiv ℝ (h ∘ γ) t = (fderiv ℝ h (γ t)).comp (fderiv ℝ γ t) :=
        fderiv_comp t hdh hdt
      have h2 : fderiv ℝ (h ∘ γ) t = 0 := by
        rw [hG.fderiv_eq]
        exact (hasFDerivAt_const (c := h z₀) (x := t)).fderiv
      rw [← h1, h2]
    have hcomp_C : C.comp (fderiv ℝ γ t) = ContinuousLinearMap.id ℝ _ := by
      have hder : fderiv ℝ ((fun y : Fin Q → ℝ => C (y - z₀)) ∘ γ) t
          = C.comp (fderiv ℝ γ t) :=
        (C.hasFDerivAt.comp t (hdt.hasFDerivAt.sub_const z₀)).fderiv
      rw [← hder, hF.fderiv_eq, fderiv_id]
    -- the second identity says `C` is a left inverse of `Dγ_t`
    have hinj : Function.Injective (fderiv ℝ γ t) := by
      intro u v huv
      have h2 : (C.comp (fderiv ℝ γ t)) u = (C.comp (fderiv ℝ γ t)) v := by
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, huv]
      rw [hcomp_C] at h2
      simpa using h2
    -- and the first that the range is contained in the kernel of `Dh`
    have hle : (fderiv ℝ γ t).range ≤ (fderiv ℝ h (γ t)).ker := by
      rintro u ⟨w, rfl⟩
      change (fderiv ℝ h (γ t)) ((fderiv ℝ γ t) w) = 0
      rw [← ContinuousLinearMap.comp_apply, hcomp_h, zero_apply]
    -- both subspaces have the same dimension `Q - j`, so they are equal
    have hfr1 : Module.finrank ℝ ((fderiv ℝ γ t).range)
        = Module.finrank ℝ (fderiv ℝ h z₀).ker := by
      let A : (fderiv ℝ h z₀).ker →ₗ[ℝ] (Fin Q → ℝ) := fderiv ℝ γ t
      have hkerA : A.ker = ⊥ := LinearMap.ker_eq_bot.mpr (by simpa [A] using hinj)
      have hsum := LinearMap.finrank_range_add_finrank_ker A
      rw [hkerA] at hsum
      have hb : Module.finrank ℝ (⊥ : Submodule ℝ (fderiv ℝ h z₀).ker) = 0 :=
        finrank_bot ℝ _
      rw [hb, add_zero] at hsum
      simpa [A] using hsum
    have hfr2 : Module.finrank ℝ ((fderiv ℝ h (γ t)).ker)
        = Module.finrank ℝ (fderiv ℝ h z₀).ker := by
      rw [finrank_ker_of_surjective Q j (fderiv ℝ h (γ t)) hsurjt,
        finrank_ker_of_surjective Q j (fderiv ℝ h z₀) (LinearMap.range_eq_top.mpr hsurj)]
    exact Submodule.eq_of_le_of_finrank_eq hle (hfr1.trans hfr2.symm)

theorem levelSetChartParam {Q j : ℕ} (h : (Fin Q → ℝ) → (Fin j → ℝ)) (z₀ : Fin Q → ℝ) (hh : ∀ x, AnalyticAt ℝ h x) (hsurj : Function.Surjective (fderiv ℝ h z₀)) : ∃ (r : ℕ) (γ : (Fin r → ℝ) → (Fin Q → ℝ)) (C : (Fin Q → ℝ) →L[ℝ] (Fin r → ℝ)) (V : Set (Fin r → ℝ)) (U : Set (Fin Q → ℝ)), IsOpen V ∧ IsOpen U ∧ (0 : Fin r → ℝ) ∈ V ∧ z₀ ∈ U ∧ γ 0 = z₀ ∧ AnalyticAt ℝ γ 0 ∧ (∀ t ∈ V, γ t ∈ U) ∧ (∀ t ∈ V, h (γ t) = h z₀) ∧ (∀ y ∈ U, h y = h z₀ → C (y - z₀) ∈ V ∧ γ (C (y - z₀)) = y) ∧ (∀ t ∈ V, (fderiv ℝ γ t).range = (fderiv ℝ h (γ t)).ker) := by
  obtain ⟨γ, C, V, U, hVo, hUo, h0V, hz₀U, hγ0, hγan, hγU, hhγ, hχ, hrange⟩ :=
    levelSetChartKer h z₀ hh hsurj
  -- reindex the kernel by `Fin r → ℝ` using a basis of the kernel
  let e : (Fin (Module.finrank ℝ (fderiv ℝ h z₀).ker) → ℝ) ≃L[ℝ] (fderiv ℝ h z₀).ker :=
    ((Module.finBasis ℝ (fderiv ℝ h z₀).ker).equivFun.symm).toContinuousLinearEquiv
  obtain ⟨γ', C', V', U', hV'o, hU'o, h0V', hz₀U', hγ'0, hγ'an, hγ'U, hhγ', hχ', hrange'⟩ :=
    levelSetChartTransport h z₀ e C γ V U hVo hUo h0V hz₀U hγ0 hγan hγU hhγ hχ hrange
  exact ⟨Module.finrank ℝ (fderiv ℝ h z₀).ker, γ', C', V', U', hV'o, hU'o, h0V', hz₀U',
    hγ'0, hγ'an, hγ'U, hhγ', hχ', hrange'⟩

end Work.WilE9G.Sard

import Mathlib

/-!
# A parametrised local left inverse

Let `G : ℝ × E → F` be smooth on an open set `U₀ ∋ (s₀, p)` (with `E`, `F` finite dimensional
real normed spaces) and suppose that the partial derivative of `G` in the second variable at
`(s₀, p)` is injective.  Then, locally around `s₀` and around `p`, `y ↦ G (s, y)` admits a left
inverse which depends smoothly on `s`.

The proof is the standard inverse function theorem argument, carried out in a
*parameter-augmented* space: choose a linear complement `K` of the range of the partial
derivative `D = ∂₂G (s₀,p)` in `F` and consider

`Ξ : ℝ × (E × K) → ℝ × F,  Ξ (s, v, k) = (s, G (s, v) + k)`.

Its derivative at `x₀ = (s₀, p, 0)` is the continuous linear equivalence
`(a, w) ↦ (a, ∂₁G·a + D v + k)`, so `Ξ` is a local diffeomorphism at `x₀`; the desired map `h`
is the `E`-component of the inverse, and the fact that it is a *left* inverse of `y ↦ G (s, y)`
on the image comes from the fact that the `K`-coordinate is the constant `0`.
-/

open scoped ContDiff
open Topology Set Function

set_option linter.style.haveILetI false

namespace Work.Isotopy

/-- If a continuous linear map `A` is close enough to an invertible one `T`, it is injective:
if `A u = 0`, then `T u = (T - A) u`, so `‖u‖ ≤ ‖T⁻¹‖ ‖T - A‖ ‖u‖`, and the factor is `< 1`. -/
private lemma ker_eq_bot_of_norm_sub_mul_lt_one {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : X ≃L[ℝ] Y) {A : X →L[ℝ] Y}
    (h : ‖A - T‖ * ‖(T.symm : Y →L[ℝ] X)‖ < 1) : (A : X →ₗ[ℝ] Y).ker = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro u hu
  rw [LinearMap.mem_ker] at hu
  have hTu : T u = (T - A) u := by
    rw [sub_apply, show A u = 0 from hu, sub_zero]
    rfl
  have hu' : u = T.symm ((T - A) u) := by
    rw [← hTu, ContinuousLinearEquiv.symm_apply_apply]
  have hX : ‖u‖ = ‖(T.symm : Y →L[ℝ] X) ((T - A) u)‖ := congrArg Norm.norm hu'
  have hle : ‖u‖ ≤ ‖(T.symm : Y →L[ℝ] X)‖ * ‖T - A‖ * ‖u‖ := by
    conv_lhs => rw [hX]
    calc ‖(T.symm : Y →L[ℝ] X) ((T - A) u)‖
        ≤ ‖(T.symm : Y →L[ℝ] X)‖ * ‖(T - A) u‖ := (T.symm : Y →L[ℝ] X).le_opNorm _
      _ ≤ ‖(T.symm : Y →L[ℝ] X)‖ * (‖T - A‖ * ‖u‖) := by
            gcongr
            exact (T - A).le_opNorm _
      _ = ‖(T.symm : Y →L[ℝ] X)‖ * ‖T - A‖ * ‖u‖ := by ring
  have hlt : ‖(T.symm : Y →L[ℝ] X)‖ * ‖T - A‖ < 1 := by
    rw [norm_sub_rev] at h
    rw [mul_comm]
    exact h
  by_contra hne
  have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hne
  have h2 := mul_lt_mul_of_pos_right hlt hpos
  have h3 : ‖u‖ < ‖u‖ := by simpa using lt_of_le_of_lt hle h2
  exact absurd h3 (lt_irrefl _)

/-- The `dist`-form of the previous criterion. -/
private lemma ker_eq_bot_of_dist_mul_lt_one {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : X ≃L[ℝ] Y) {A : X →L[ℝ] Y}
    (h : dist A T * ‖(T.symm : Y →L[ℝ] X)‖ < 1) : (A : X →ₗ[ℝ] Y).ker = ⊥ := by
  rw [dist_eq_norm] at h
  exact ker_eq_bot_of_norm_sub_mul_lt_one T h

theorem exists_localInverse_param {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (G : ℝ × E → F) (U₀ : Set (ℝ × E)) (hU₀ : IsOpen U₀) (s₀ : ℝ) (p : E)
    (hmem : (s₀, p) ∈ U₀) (hG : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) G U₀)
    (V : Set E) (hV : IsOpen V) (hpV : p ∈ V)
    (hinj : Function.Injective (fun v : E => fderiv ℝ G (s₀, p) (0, v))) :
    ∃ (O : Set ℝ) (U : Set E) (W : Set F) (h : ℝ → F → E),
      IsOpen O ∧ s₀ ∈ O ∧ IsOpen U ∧ p ∈ U ∧ IsOpen W ∧ G (s₀, p) ∈ W ∧
      (∀ s ∈ O, ∀ w ∈ W, h s w ∈ V) ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry h) (O ×ˢ W) ∧
      (∀ s ∈ O, ∀ y ∈ U, G (s, y) ∈ W) ∧
      (∀ s ∈ O, ∀ y ∈ U, h s (G (s, y)) = y) := by
  classical
  -- ## Step 1: the partial derivative in the second variable
  let L : (ℝ × E) →L[ℝ] F := fderiv ℝ G (s₀, p)
  let D : E →L[ℝ] F := L.comp (ContinuousLinearMap.inr ℝ ℝ E)
  have hD : Function.Injective D := by
    intro u v huv
    apply hinj
    simpa [D, L, ContinuousLinearMap.inr_apply] using huv
  have hD_eq : ∀ v : E, L (0, v) = D v := by
    intro v
    rfl
  -- a linear complement of the range of `D`
  obtain ⟨K, hK⟩ := Submodule.exists_isCompl (LinearMap.range (D : E →ₗ[ℝ] F))
  haveI : FiniteDimensional ℝ K := inferInstance
  -- ## Step 2: the parameter-augmented space and the derivative of `Ξ`
  let p₁ : ℝ × (E × K) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (E × K)
  let pE : ℝ × (E × K) →L[ℝ] E :=
    (ContinuousLinearMap.fst ℝ E K).comp (ContinuousLinearMap.snd ℝ ℝ (E × K))
  let pK : ℝ × (E × K) →L[ℝ] K :=
    (ContinuousLinearMap.snd ℝ E K).comp (ContinuousLinearMap.snd ℝ ℝ (E × K))
  let q : ℝ × (E × K) →L[ℝ] (ℝ × E) := p₁.prod pE
  let A : ℝ × (E × K) →L[ℝ] F := L.comp q + K.subtypeL.comp pK
  let T₁ : ℝ × (E × K) →L[ℝ] (ℝ × F) := p₁.prod A
  have hT₁ : ∀ z : ℝ × (E × K), T₁ z = (z.1, L (z.1, z.2.1) + (z.2.2 : F)) := by
    intro z
    simp [T₁, A, q, p₁, pE, pK, ContinuousLinearMap.prod_apply]
  -- ## Step 3: `T₁` is bijective
  have hbij : Function.Bijective T₁ := by
    constructor
    · have hker : ∀ z : ℝ × (E × K), T₁ z = 0 → z = 0 := by
        intro z hz
        have hz1 : z.1 = 0 := by
          have h1 : (T₁ z).1 = (0 : ℝ) := congrArg Prod.fst hz
          rwa [hT₁ z] at h1
        have hz2 : L (z.1, z.2.1) + (z.2.2 : F) = 0 := by
          have h2 : (T₁ z).2 = (0 : F) := congrArg Prod.snd hz
          rwa [hT₁ z] at h2
        have hz1' : (z.1, z.2.1) = (0, z.2.1) := by rw [hz1]
        have hDz : D z.2.1 = -(z.2.2 : F) := by
          have h3 := hz2
          rw [hz1', hD_eq] at h3
          exact eq_neg_of_add_eq_zero_left h3
        have hmemK : D z.2.1 ∈ K := by
          rw [hDz]
          exact K.neg_mem (z.2.2 : K).2
        have hmemR : D z.2.1 ∈ LinearMap.range (D : E →ₗ[ℝ] F) :=
          LinearMap.mem_range.mpr ⟨z.2.1, rfl⟩
        have hbot : D z.2.1 ∈ (⊥ : Submodule ℝ F) := by
          rw [← hK.inf_eq_bot]
          exact Submodule.mem_inf.mpr ⟨hmemR, hmemK⟩
        have hzero : D z.2.1 = 0 := (Submodule.mem_bot ℝ).mp hbot
        have hz21 : z.2.1 = 0 := hD (by simpa using hzero)
        have hz22 : (z.2.2 : F) = 0 := by
          have : -(z.2.2 : F) = 0 := by rw [← hDz, hzero]
          exact neg_eq_zero.mp this
        exact Prod.ext hz1 (Prod.ext hz21 (Subtype.ext hz22))
      intro a b hab
      have hab' : T₁ (a - b) = 0 := by rw [map_sub, hab, sub_self]
      exact sub_eq_zero.mp (hker (a - b) hab')
    · intro y
      obtain ⟨b, w⟩ := y
      have hy : w - L (b, 0) ∈ (LinearMap.range (D : E →ₗ[ℝ] F)) ⊔ K := by
        rw [hK.sup_eq_top]; trivial
      obtain ⟨a, ha, k, hk, hak⟩ := Submodule.mem_sup.mp hy
      obtain ⟨v, hv⟩ := LinearMap.mem_range.mp ha
      refine ⟨(b, (v, ⟨k, hk⟩)), ?_⟩
      rw [hT₁]
      simp only [Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      have hL1 : L (b, v) = L (b, 0) + D v := by
        have hbv : (b, v) = (b, 0) + (0, v) := by simp
        rw [hbv, map_add, hD_eq]
      have hv' : D v = a := hv
      rw [hL1, hv']
      have hsum : L (b, 0) + (a + k) = w := by rw [hak]; abel
      simpa [add_assoc] using hsum
  -- the corresponding continuous linear equivalence
  let e : (ℝ × (E × K)) ≃ₗ[ℝ] (ℝ × F) :=
    LinearEquiv.ofBijective (T₁ : ℝ × (E × K) →ₗ[ℝ] (ℝ × F)) hbij
  let T : (ℝ × (E × K)) ≃L[ℝ] (ℝ × F) := e.toContinuousLinearEquiv
  have hTcoe : T₁ = (T : ℝ × (E × K) →L[ℝ] (ℝ × F)) := by
    have hfun : ((T : ℝ × (E × K) →L[ℝ] (ℝ × F)) : ℝ × (E × K) → (ℝ × F)) = T₁ := by
      ext z : 1
      simp [T, e, LinearEquiv.ofBijective_apply, ContinuousLinearMap.coe_coe]
    exact ContinuousLinearMap.ext fun z => congrFun hfun z 
  have hfin : Module.finrank ℝ (ℝ × (E × K)) = Module.finrank ℝ (ℝ × F) :=
    (T : (ℝ × (E × K)) ≃ₗ[ℝ] (ℝ × F)).finrank_eq
  -- ## Step 4: the map `Ξ` and its derivative at `x₀`
  let x₀ : ℝ × (E × K) := (s₀, (p, 0))
  let Ξ : ℝ × (E × K) → (ℝ × F) := fun z => (z.1, G (z.1, z.2.1) + (z.2.2 : F))
  let S : Set (ℝ × (E × K)) := q ⁻¹' U₀
  have hne0 : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hGat : ContDiffAt ℝ ∞ G (s₀, p) := hG.contDiffAt (hU₀.mem_nhds hmem)
  have hGd : HasFDerivAt G L (s₀, p) := by
    have := (hGat.differentiableAt hne0).hasFDerivAt
    simpa [L] using this
  have hp₁ : HasFDerivAt (fun z : ℝ × (E × K) => z.1) p₁ x₀ := by
    simpa [p₁] using
      (hasFDerivAt_fst : HasFDerivAt (fun z : ℝ × (E × K) => z.1)
        (ContinuousLinearMap.fst ℝ ℝ (E × K)) x₀)
  have hpE : HasFDerivAt (fun z : ℝ × (E × K) => z.2.1) pE x₀ := by
    simpa [pE] using (hasFDerivAt_snd.fst :
      HasFDerivAt (fun z : ℝ × (E × K) => z.2.1)
        ((ContinuousLinearMap.fst ℝ E K).comp (ContinuousLinearMap.snd ℝ ℝ (E × K))) x₀)
  have hpK : HasFDerivAt (fun z : ℝ × (E × K) => z.2.2) pK x₀ := by
    have h := (hasFDerivAt_snd.snd :
      HasFDerivAt (fun z : ℝ × (E × K) => z.2.2)
        ((ContinuousLinearMap.snd ℝ E K).comp (ContinuousLinearMap.snd ℝ ℝ (E × K))) x₀)
    simpa [pK] using h
  have hq : HasFDerivAt (fun z : ℝ × (E × K) => (z.1, z.2.1)) q x₀ := by
    have h := hp₁.prodMk hpE
    simpa [q, Function.comp_def] using h
  have hcomp : HasFDerivAt (fun z : ℝ × (E × K) => G (z.1, z.2.1)) (L.comp q) x₀ := by
    have h := hGd.comp x₀ hq
    simpa [Function.comp_def] using h
  have hKpart : HasFDerivAt (fun z : ℝ × (E × K) => ((z.2.2 : K) : F))
      (K.subtypeL.comp pK) x₀ := by
    have h := (K.subtypeL.hasFDerivAt).comp x₀ hpK
    simpa [Function.comp_def] using h
  have hA : HasFDerivAt ((fun z : ℝ × (E × K) => G (z.1, z.2.1)) +
      (fun z : ℝ × (E × K) => ((z.2.2 : K) : F))) A x₀ := by
    have h := hcomp.add hKpart
    simpa [A] using h
  have hΞd : HasFDerivAt Ξ T₁ x₀ := by
    have h := hp₁.prodMk hA
    simpa [Ξ, T₁, Pi.add_apply] using h
  have hd : HasFDerivAt Ξ (T : ℝ × (E × K) →L[ℝ] (ℝ × F)) x₀ := hΞd.congr_fderiv hTcoe
  have hΞx₀ : fderiv ℝ Ξ x₀ = (T : ℝ × (E × K) →L[ℝ] (ℝ × F)) := hd.fderiv
  -- smoothness of `Ξ` near `x₀`
  have hSopen : IsOpen S := hU₀.preimage q.continuous
  have hx₀S : x₀ ∈ S := by
    show q x₀ ∈ U₀
    simpa [q, p₁, pE, x₀] using hmem
  have hΞS : ContDiffOn ℝ ∞ Ξ S := by
    have h1 : ContDiffOn ℝ ∞ (fun z : ℝ × (E × K) => G (z.1, z.2.1)) S := by
      have hpair : ContDiffOn ℝ ∞ (fun z : ℝ × (E × K) => (z.1, z.2.1)) S :=
        contDiffOn_fst.prodMk contDiffOn_snd.fst
      exact hG.comp hpair (fun z hz => hz)
    have h2 : ContDiffOn ℝ ∞ (fun z : ℝ × (E × K) => ((z.2.2 : K) : F)) S :=
      ((K.subtypeL.comp pK).contDiff).contDiffOn
    have h3 : ContDiffOn ℝ ∞ (fun z : ℝ × (E × K) => z.1) S := p₁.contDiff.contDiffOn
    have h := h3.prodMk (h1.add h2)
    simpa [Ξ] using h
  have hΞat : ContDiffAt ℝ ∞ Ξ x₀ := hΞS.contDiffAt (hSopen.mem_nhds hx₀S)
  -- ## Step 5: the local inverse
  let φ : OpenPartialHomeomorph (ℝ × (E × K)) (ℝ × F) :=
    hΞat.toOpenPartialHomeomorph Ξ hd hne0
  have hφcoe : (φ : ℝ × (E × K) → (ℝ × F)) = Ξ := rfl
  have hx₀src : x₀ ∈ φ.source := by
    show x₀ ∈ (hΞat.toOpenPartialHomeomorph Ξ hd hne0).source
    exact hΞat.mem_toOpenPartialHomeomorph_source hd hne0
  let x₁ : ℝ × F := (s₀, G (s₀, p))
  have hΞx₀' : Ξ x₀ = x₁ := by simp [Ξ, x₀, x₁]
  have hφx₀ : (φ : ℝ × (E × K) → (ℝ × F)) x₀ = x₁ := by rw [hφcoe, hΞx₀']
  have hx₁tgt : x₁ ∈ φ.target := by
    have h := hΞat.image_mem_toOpenPartialHomeomorph_target hd hne0
    rwa [hΞx₀'] at h
  have hsymmx₁ : φ.symm x₁ = x₀ := by
    rw [← hφx₀]
    exact φ.left_inv hx₀src
  -- ## Step 6: an open neighbourhood of `x₀` on which the derivative of `Ξ` is invertible
  let c : ℝ := ‖(T.symm : (ℝ × F) →L[ℝ] (ℝ × (E × K)))‖
  have hc0 : 0 ≤ c := norm_nonneg (T.symm : (ℝ × F) →L[ℝ] (ℝ × (E × K)))
  let ε : ℝ := 1 / (2 * (c + 1))
  have hεpos : 0 < ε := by positivity
  have hεc : ε * c ≤ 1 / 2 := by
    have h2 : (0 : ℝ) < 2 * (c + 1) := by linarith
    have heq : ε * c = c / (2 * (c + 1)) := by
      change (1 / (2 * (c + 1))) * c = c / (2 * (c + 1))
      field_simp
    rw [heq, div_le_iff₀ h2]
    linarith
  have hfderivcont : ContinuousAt (fderiv ℝ Ξ) x₀ :=
    (hΞS.continuousOn_fderiv_of_isOpen hSopen (by simp)).continuousAt (hSopen.mem_nhds hx₀S)
  have hV₂ : S ∩ (fderiv ℝ Ξ ⁻¹' Metric.ball (fderiv ℝ Ξ x₀) ε) ∈ 𝓝 x₀ :=
    Filter.inter_mem (hSopen.mem_nhds hx₀S)
      (hfderivcont.preimage_mem_nhds (Metric.ball_mem_nhds (fderiv ℝ Ξ x₀) hεpos))
  -- at every point of this neighbourhood the derivative of `Ξ` is an isomorphism
  have hex : ∀ y ∈ S, fderiv ℝ Ξ y ∈ Metric.ball (fderiv ℝ Ξ x₀) ε →
      ∃ T' : (ℝ × (E × K)) ≃L[ℝ] (ℝ × F), HasFDerivAt Ξ (T' : ℝ × (E × K) →L[ℝ] (ℝ × F)) y := by
    intro y hyS hyb
    have hySmooth : ContDiffAt ℝ ∞ Ξ y := hΞS.contDiffAt (hSopen.mem_nhds hyS)
    have hyd : HasFDerivAt Ξ (fderiv ℝ Ξ y) y := (hySmooth.differentiableAt hne0).hasFDerivAt
    have hinjker : (fderiv ℝ Ξ y : ℝ × (E × K) →ₗ[ℝ] (ℝ × F)).ker = ⊥ := by
      refine ker_eq_bot_of_dist_mul_lt_one T ?_
      have hdist : dist (fderiv ℝ Ξ y) (T : ℝ × (E × K) →L[ℝ] (ℝ × F)) < ε := by
        have h := Metric.mem_ball.mp hyb
        rwa [hΞx₀] at h
      have hb' : dist (fderiv ℝ Ξ y) (T : ℝ × (E × K) →L[ℝ] (ℝ × F)) * c < 1 := by
        have h1 : dist (fderiv ℝ Ξ y) (T : ℝ × (E × K) →L[ℝ] (ℝ × F)) * c ≤ ε * c :=
          mul_le_mul_of_nonneg_right (le_of_lt hdist) hc0
        linarith [hεc]
      exact hb'
    have hinjfun : Function.Injective
        ((fderiv ℝ Ξ y : ℝ × (E × K) →ₗ[ℝ] (ℝ × F))) := LinearMap.ker_eq_bot.mp hinjker
    have hsurj : Function.Surjective
        ((fderiv ℝ Ξ y : ℝ × (E × K) →ₗ[ℝ] (ℝ × F))) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinjfun
    let e' : (ℝ × (E × K)) ≃ₗ[ℝ] (ℝ × F) :=
      LinearEquiv.ofBijective (fderiv ℝ Ξ y : ℝ × (E × K) →ₗ[ℝ] (ℝ × F)) ⟨hinjfun, hsurj⟩
    refine ⟨e'.toContinuousLinearEquiv, ?_⟩
    have hcoe : (e'.toContinuousLinearEquiv : ℝ × (E × K) →L[ℝ] (ℝ × F)) = fderiv ℝ Ξ y := by
      have hfun : ((e'.toContinuousLinearEquiv : ℝ × (E × K) →L[ℝ] (ℝ × F)) :
          ℝ × (E × K) → (ℝ × F)) = fderiv ℝ Ξ y := by
        ext z : 1
        show (LinearEquiv.ofBijective (fderiv ℝ Ξ y : ℝ × (E × K) →ₗ[ℝ] (ℝ × F))
          ⟨hinjfun, hsurj⟩) z = (fderiv ℝ Ξ y) z
        exact LinearEquiv.ofBijective_apply _ z
      exact ContinuousLinearMap.ext fun z => congrFun hfun z
    rw [hcoe]
    exact hyd
  -- ## Step 7: shrink to a product box and finish
  have hpre : φ.symm ⁻¹' (S ∩ (fderiv ℝ Ξ ⁻¹' Metric.ball (fderiv ℝ Ξ x₀) ε)) ∈ 𝓝 x₁ := by
    have hcont : ContinuousAt (φ.symm : (ℝ × F) → (ℝ × (E × K))) x₁ := φ.continuousAt_symm hx₁tgt
    refine hcont.preimage_mem_nhds ?_
    rw [hsymmx₁]
    exact hV₂
  have hN : φ.target ∩ (φ.symm ⁻¹' (S ∩ (fderiv ℝ Ξ ⁻¹' Metric.ball (fderiv ℝ Ξ x₀) ε)))
      ∈ 𝓝 x₁ :=
    Filter.inter_mem (φ.open_target.mem_nhds hx₁tgt) hpre
  rw [nhds_prod_eq] at hN
  obtain ⟨Oa, hOa, Wa, hWa, hOW⟩ := Filter.mem_prod_iff.mp hN
  obtain ⟨O₁, hO₁sub, hO₁open, hs₀O₁⟩ := mem_nhds_iff.mp hOa
  obtain ⟨W₁, hW₁sub, hW₁open, hgpW₁⟩ := mem_nhds_iff.mp hWa
  have hBsub : O₁ ×ˢ W₁ ⊆
      φ.target ∩ (φ.symm ⁻¹' (S ∩ (fderiv ℝ Ξ ⁻¹' Metric.ball (fderiv ℝ Ξ x₀) ε))) :=
    fun z hz => hOW ⟨hO₁sub hz.1, hW₁sub hz.2⟩
  -- smoothness of the inverse on this box
  have hBsm : ∀ z ∈ O₁ ×ˢ W₁, ContDiffAt ℝ ∞ (φ.symm : (ℝ × F) → (ℝ × (E × K))) z := by
    intro z hz
    have hztgt : z ∈ φ.target := (hBsub hz).1
    have hzV₂ : φ.symm z ∈ S ∩ (fderiv ℝ Ξ ⁻¹' Metric.ball (fderiv ℝ Ξ x₀) ε) := (hBsub hz).2
    obtain ⟨T', hT'⟩ := hex (φ.symm z) hzV₂.1 hzV₂.2
    have hsm : ContDiffAt ℝ ∞ Ξ (φ.symm z) := hΞS.contDiffAt (hSopen.mem_nhds hzV₂.1)
    have hder : HasFDerivAt (φ : ℝ × (E × K) → (ℝ × F)) (T' : ℝ × (E × K) →L[ℝ] (ℝ × F))
        (φ.symm z) := by
      rw [hφcoe]
      exact hT'
    exact φ.contDiffAt_symm hztgt hder hsm
  -- the `V`-condition
  have hcontV : ContinuousAt (fun z : ℝ × F => (φ.symm z).2.1) x₁ := by
    have h1 : ContinuousAt (fun z : ℝ × F => pE (φ.symm z)) x₁ :=
      (pE.continuous.continuousAt).comp (φ.continuousAt_symm hx₁tgt)
    simpa [Function.comp_def, pE] using h1
  have hpreV : (fun z : ℝ × F => (φ.symm z).2.1) ⁻¹' V ∈ 𝓝 x₁ := by
    refine hcontV.preimage_mem_nhds ?_
    show V ∈ 𝓝 ((φ.symm x₁).2.1)
    rw [hsymmx₁]
    exact hV.mem_nhds (by simpa [x₀] using hpV)
  rw [nhds_prod_eq] at hpreV
  obtain ⟨OV, hOV, WV, hWV, hOVWV⟩ := Filter.mem_prod_iff.mp hpreV
  obtain ⟨OV', hOV'sub, hOV'open, hs₀OV'⟩ := mem_nhds_iff.mp hOV
  obtain ⟨WV', hWV'sub, hWV'open, hgpWV'⟩ := mem_nhds_iff.mp hWV
  -- the source condition: `(s, y, 0) ∈ φ.source` for `s`, `y` in a product box
  have hsrcnhds : φ.source ∈ 𝓝 x₀ := φ.open_source.mem_nhds hx₀src
  rw [nhds_prod_eq] at hsrcnhds
  obtain ⟨As, hAs, Bs, hBs, hAsBs⟩ := Filter.mem_prod_iff.mp hsrcnhds
  rw [nhds_prod_eq] at hBs
  obtain ⟨Us, hUs, Bk, hBk, hUsBk⟩ := Filter.mem_prod_iff.mp hBs
  obtain ⟨Os, hOssub, hOsopen, hs₀Os⟩ := mem_nhds_iff.mp hAs
  obtain ⟨Us', hUs'sub, hUs'open, hpUs'⟩ := mem_nhds_iff.mp hUs
  have h0Bk : (0 : K) ∈ Bk := mem_of_mem_nhds hBk
  have hsrc_box : ∀ s ∈ Os, ∀ y ∈ Us', (s, (y, (0 : K))) ∈ φ.source := by
    intro s hs y hy
    apply hAsBs
    refine ⟨hOssub hs, ?_⟩
    apply hUsBk
    exact ⟨hUs'sub hy, h0Bk⟩
  -- the box on which `G` lands in `W₁ ∩ WV'`
  have hGcont : ContinuousAt G (s₀, p) := hGat.continuousAt
  have hWopen : IsOpen (W₁ ∩ WV') := hW₁open.inter hWV'open
  have hgpW : G (s₀, p) ∈ W₁ ∩ WV' := ⟨hgpW₁, hgpWV'⟩
  have hpreG : G ⁻¹' (W₁ ∩ WV') ∈ 𝓝 (s₀, p) :=
    hGcont.preimage_mem_nhds (hWopen.mem_nhds hgpW)
  rw [nhds_prod_eq] at hpreG
  obtain ⟨OG, hOG, UG, hUG, hOGUG⟩ := Filter.mem_prod_iff.mp hpreG
  obtain ⟨OG', hOG'sub, hOG'open, hs₀OG'⟩ := mem_nhds_iff.mp hOG
  obtain ⟨UG', hUG'sub, hUG'open, hpUG'⟩ := mem_nhds_iff.mp hUG
  -- assemble
  refine ⟨Os ∩ OV' ∩ O₁ ∩ OG', Us' ∩ UG', W₁ ∩ WV', fun s w => (φ.symm (s, w)).2.1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((hOsopen.inter hOV'open).inter hO₁open).inter hOG'open
  · exact ⟨⟨⟨hs₀Os, hs₀OV'⟩, hs₀O₁⟩, hs₀OG'⟩
  · exact hUs'open.inter hUG'open
  · exact ⟨hpUs', hpUG'⟩
  · exact hW₁open.inter hWV'open
  · exact ⟨hgpW₁, hgpWV'⟩
  · -- the values of `h` lie in `V`
    intro s hs w hw
    exact hOVWV ⟨hOV'sub hs.1.1.2, hWV'sub hw.2⟩
  · -- smoothness of `h`
    have hbox : Os ∩ OV' ∩ O₁ ∩ OG' ⊆ O₁ := fun s hs => hs.1.2
    have hWbox : W₁ ∩ WV' ⊆ W₁ := fun w hw => hw.1
    have hOWopen : IsOpen ((Os ∩ OV' ∩ O₁ ∩ OG') ×ˢ (W₁ ∩ WV')) :=
      (((hOsopen.inter hOV'open).inter hO₁open).inter hOG'open).prod
        (hW₁open.inter hWV'open)
    rw [IsOpen.contDiffOn_iff hOWopen]
    intro z hz
    have hz' : z ∈ O₁ ×ˢ W₁ := ⟨hbox hz.1, hWbox hz.2⟩
    have h1 : ContDiffAt ℝ ∞ (fun z : ℝ × F => pE ((φ.symm : (ℝ × F) → (ℝ × (E × K))) z)) z :=
      (pE.contDiff.contDiffAt).comp z (hBsm z hz')
    have h2 : ContDiffAt ℝ ∞ (fun z : ℝ × F => (φ.symm z).2.1) z := by
      simpa [pE] using h1
    have h3 : Function.uncurry (fun s w => (φ.symm (s, w)).2.1) =
        (fun z : ℝ × F => (φ.symm z).2.1) := rfl
    rw [h3]
    exact h2
  · -- `G` lands in `W`
    intro s hs y hy
    have hOG'sub' : Os ∩ OV' ∩ O₁ ∩ OG' ⊆ OG' := fun s hs => hs.2
    exact hOGUG ⟨hOG'sub (hOG'sub' hs), hUG'sub hy.2⟩
  · -- `h` is a left inverse
    intro s hs y hy
    have hsrc : (s, (y, (0 : K))) ∈ φ.source := hsrc_box s hs.1.1.1 y hy.1
    have h1 : φ.symm (s, G (s, y)) = (s, (y, (0 : K))) := by
      calc φ.symm (s, G (s, y)) = φ.symm ((φ : ℝ × (E × K) → (ℝ × F)) (s, (y, (0 : K)))) := by
            congr 1
            show (s, G (s, y)) = (φ : ℝ × (E × K) → (ℝ × F)) (s, (y, (0 : K)))
            rw [hφcoe]
            simp [Ξ]
        _ = (s, (y, (0 : K))) := φ.left_inv hsrc
    show (φ.symm (s, G (s, y))).2.1 = y
    rw [h1]

end Work.Isotopy

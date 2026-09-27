import Mathlib
import Submission.Work.Mostow.cuspDefs
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.horSpec
import Submission.Work.Mostow.cuspZ2Defs
import Submission.Work.Mostow.flatActProper
import Submission.Work.Mostow.flatActCocompact
import Submission.Work.Mostow.flatActBasic
import Submission.Work.Mostow.horoActTrivId

/-!
# `cuspZ2` : a rank-two free abelian subgroup in the centraliser

This file proves `Work.Mostow.cuspZ2`.  The setting is that of a horospherical subgroup
`G ≤ PO n 1` of a rank-one hyperbolic space, i.e. a subgroup all of whose elements fix a
boundary point `ξ` (`hfix`) and preserve the horosphere levels `lev ξ ·` (`hlev`), whose action
on the level-`D` horosphere is proper (`hprop`) and cocompact (`hcoc`).

The horosphere of `ξ` is flat: in the flat coordinate `yc ξ ·` it is the Euclidean space
`ξ^⊥ = xiPerp ξ`, and the horospherical action of `G` becomes an action by Euclidean isometries
(`cuspFlatHom`, from `cuspZ2Defs`).  Bieberbach's first theorem applied to that Euclidean action
produces a finite index subgroup acting by translations spanning `ξ^⊥`; as `dim ξ^⊥ = n - 1 ≥ 2`
two of those translations are linearly independent, and (the flat action being faithful,
`horoActTrivId`) the corresponding elements of `G` commute with, and together with, a power of
any prescribed element `γ₀`.

## Plan

* `bieberbachInnerProduct` : Bieberbach's theorem for an arbitrary finite-dimensional real
  inner product space (transport of `BieberbachProp` along an orthonormal basis);
* `xiPerpFinrank`, `spanTopIndependent` : the linear algebra of the conclusion;
* `cuspFlatProper`, `cuspFlatCocompact` : properness and cocompactness of the flat action,
  transported from `hprop` and `hcoc` (via `flatActProper`, `flatActCocompact`);
* `cuspFlatInjective` : the flat action is faithful (via `horoActTrivId`);
* `cuspZ2` : the assembly.
-/

namespace Work.Mostow

open LeanEval.Geometry.MostowRigidity Submission.Mostow MeasureTheory

noncomputable section

variable {n : ℕ}

/-! ## Bieberbach's theorem for an inner product space -/

/-- **Bieberbach's first theorem** for a finite-dimensional real inner product space: a group
acting properly discontinuously and cocompactly by Euclidean isometries of `V` contains a finite
index subgroup acting by translations whose translation vectors span.  `BieberbachProp` is the
statement for `V = E m = EuclideanSpace ℝ (Fin m)`; the two are identified by an orthonormal
basis of `V`. -/
theorem bieberbachInnerProduct {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {G : Type} [Group G]
    (hBb : BieberbachProp (Module.finrank ℝ V)) (ρ : G →* (V ≃ᵢ V))
    (hpd : ∀ K : Set V, IsCompact K → {g : G | ((ρ g) '' K ∩ K).Nonempty}.Finite)
    (hcoc : ∃ K : Set V, IsCompact K ∧ ∀ x : V, ∃ g : G, ρ g x ∈ K) :
    ∃ (T : Subgroup G) (v : G → V), T.FiniteIndex ∧
      (∀ t ∈ T, ∀ x : V, ρ t x = x + v t) ∧
      Submodule.span ℝ (v '' (T : Set G)) = ⊤ := by
  let eL : V ≃ₗᵢ[ℝ] E (Module.finrank ℝ V) := (stdOrthonormalBasis ℝ V).repr
  let e : V ≃ᵢ E (Module.finrank ℝ V) := eL.toIsometryEquiv
  -- the conjugate action `ρ' g = e ∘ ρ g ∘ e⁻¹` on `E (finrank ℝ V)`
  let ρ' : G →* (E (Module.finrank ℝ V) ≃ᵢ E (Module.finrank ℝ V)) :=
    { toFun := fun g => (e.symm).trans ((ρ g).trans e)
      map_one' := by
        apply IsometryEquiv.ext
        intro x
        show e ((ρ 1) (e.symm x)) = x
        rw [map_one]
        show e (e.symm x) = x
        rw [IsometryEquiv.apply_symm_apply]
      map_mul' := by
        intro g₁ g₂
        apply IsometryEquiv.ext
        intro x
        show e ((ρ (g₁ * g₂)) (e.symm x)) = e ((ρ g₁) (e.symm (e ((ρ g₂) (e.symm x)))))
        rw [map_mul, IsometryEquiv.mul_apply, IsometryEquiv.symm_apply_apply] }
  have hpd' : ∀ K : Set (E (Module.finrank ℝ V)), IsCompact K →
      {g : G | ((ρ' g) '' K ∩ K).Nonempty}.Finite := by
    intro K hK
    have hK' : IsCompact ((e.symm) '' K) := hK.image e.symm.continuous
    refine (hpd ((e.symm) '' K) hK').subset ?_
    rintro g ⟨z, ⟨y, hyK, hzy⟩, hzK⟩
    have hzy' : ρ g (e.symm y) = e.symm z := by
      have h : e ((ρ g) (e.symm y)) = z := hzy
      have h' := congrArg (fun w => e.symm w) h
      simpa using h'
    exact ⟨e.symm z, ⟨e.symm y, ⟨y, hyK, rfl⟩, hzy'⟩, ⟨z, hzK, rfl⟩⟩
  have hcoc' : ∃ K : Set (E (Module.finrank ℝ V)), IsCompact K ∧
      ∀ x : E (Module.finrank ℝ V), ∃ g : G, ρ' g x ∈ K := by
    obtain ⟨K, hKc, hK⟩ := hcoc
    refine ⟨e '' K, hKc.image e.continuous, fun x => ?_⟩
    obtain ⟨g, hg⟩ := hK (e.symm x)
    exact ⟨g, ⟨ρ g (e.symm x), hg, rfl⟩⟩
  obtain ⟨T, w, hTfin, htrans, hspan⟩ := hBb G ρ' hpd' hcoc'
  refine ⟨T, fun t => eL.symm (w t), hTfin, ?_, ?_⟩
  · intro t ht x
    have h1 : e (ρ t x) = e x + w t := by
      have h2 := htrans t ht (e x)
      have h3 : (ρ' t) (e x) = e ((ρ t) x) := by
        show e ((ρ t) (e.symm (e x))) = e ((ρ t) x)
        rw [IsometryEquiv.symm_apply_apply]
      rwa [h3] at h2
    apply e.injective
    have h4 : e (x + eL.symm (w t)) = e x + w t := by
      show eL (x + eL.symm (w t)) = eL x + w t
      rw [LinearIsometryEquiv.map_add, LinearIsometryEquiv.apply_symm_apply]
    rw [h1, h4]
  · have himg : (eL : V →ₗ[ℝ] E (Module.finrank ℝ V)) ''
        ((fun t => eL.symm (w t)) '' (T : Set G)) = w '' (T : Set G) := by
      ext y
      rw [Set.mem_image]
      constructor
      · rintro ⟨z, ⟨t, ht, htz⟩, hzy⟩
        refine ⟨t, ht, ?_⟩
        rw [← hzy, ← htz]
        exact (LinearIsometryEquiv.apply_symm_apply eL (w t)).symm
      · rintro ⟨t, ht, hwt⟩
        exact ⟨eL.symm (w t), ⟨t, ht, rfl⟩,
          (LinearIsometryEquiv.apply_symm_apply eL (w t)).trans hwt⟩
    have h1 : Submodule.map (eL : V →ₗ[ℝ] E (Module.finrank ℝ V))
        (Submodule.span ℝ ((fun t => eL.symm (w t)) '' (T : Set G))) = ⊤ := by
      rw [Submodule.map_span, himg, hspan]
    have h2 : Submodule.map (eL : V →ₗ[ℝ] E (Module.finrank ℝ V))
        (⊤ : Submodule ℝ V) = ⊤ := by
      rw [Submodule.map_top]
      exact LinearMap.range_eq_top.mpr eL.surjective
    exact Submodule.map_injective_of_injective eL.injective (h1.trans h2.symm)

/-! ## The dimension of the flat space -/

theorem xiPerpFinrank (n : ℕ) (hn : 3 ≤ n) (ξ : E n) (hξ : ξ ∈ Sph n) :
    Module.finrank ℝ (xiPerp ξ) = n - 1 := by
  have hξ0 : ξ ≠ 0 := by
    intro h
    have h1 : ‖ξ‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
    rw [h, norm_zero] at h1
    exact one_ne_zero h1.symm
  have h1 : Module.finrank ℝ ↥(ℝ ∙ ξ) = 1 := finrank_span_singleton hξ0
  have h2 := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ ξ)
  have h3 : Module.finrank ℝ (E n) = n := by
    rw [finrank_euclideanSpace]; simp
  have h4 : Module.finrank ℝ ↥((ℝ ∙ ξ)ᗮ) = n - 1 := by omega
  rw [xiPerp]
  exact h4

/-! ## Two independent translation vectors -/

lemma mem_span_singleton_of_not_linearIndependent {V : Type*} [AddCommGroup V] [Module ℝ V]
    {x y : V} (hx : x ≠ 0) (h : ¬ LinearIndependent ℝ ![x, y]) :
    y ∈ Submodule.span ℝ ({x} : Set V) := by
  rw [LinearIndependent.pair_iff] at h
  by_contra hy
  apply h
  intro s t hst
  have ht : t = 0 := by
    by_contra ht
    refine hy ?_
    have h1 : t • y = (-s) • x := by
      rw [neg_smul]
      calc t • y = (s • x + t • y) - s • x := by abel
        _ = 0 - s • x := by rw [hst]
        _ = -(s • x) := zero_sub _
    have h2 : y = (t⁻¹ * (-s)) • x := by
      calc y = t⁻¹ • (t • y) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = t⁻¹ • ((-s) • x) := by rw [h1]
        _ = (t⁻¹ * (-s)) • x := by rw [smul_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
  constructor
  · rw [ht, zero_smul, add_zero] at hst
    exact (smul_eq_zero.mp hst).resolve_right hx
  · exact ht

/-- If the image of `T` under `v` spans a space of dimension at least two, two of its values are
linearly independent. -/
theorem spanTopIndependent {V : Type*} [AddCommGroup V] [Module ℝ V]
    {G : Type*} [Group G] {T : Subgroup G} {v : G → V}
    (hspan : Submodule.span ℝ (v '' (T : Set G)) = ⊤) (hfin : 2 ≤ Module.finrank ℝ V) :
    ∃ a b : G, a ∈ T ∧ b ∈ T ∧ LinearIndependent ℝ ![v a, v b] := by
  have hex : ∃ a ∈ T, v a ≠ 0 := by
    by_contra h0
    push_neg at h0
    have h1 : Submodule.span ℝ (v '' (T : Set G)) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro y ⟨a, ha, rfl⟩
      exact h0 a ha
    have : Module.finrank ℝ V = 0 := by
      have h2 : Module.finrank ℝ (⊤ : Submodule ℝ V) = 0 := by
        rw [← hspan, h1]
        exact finrank_bot ℝ V
      rwa [finrank_top] at h2
    omega
  obtain ⟨a₀, ha₀, hva₀⟩ := hex
  by_contra hcon
  have hpair : ∀ b ∈ T, ¬ LinearIndependent ℝ ![v a₀, v b] := by
    intro b hb hli
    exact hcon ⟨a₀, b, ha₀, hb, hli⟩
  have hsub : (v '' (T : Set G)) ⊆ Submodule.span ℝ ({v a₀} : Set V) := by
    rintro y ⟨b, hb, rfl⟩
    exact mem_span_singleton_of_not_linearIndependent hva₀ (hpair b hb)
  have hle : Module.finrank ℝ V ≤ 1 := by
    have h1 : Module.finrank ℝ V ≤
        Module.finrank ℝ ↥(Submodule.span ℝ ({v a₀} : Set V)) := by
      have h2 := Submodule.finrank_mono (Submodule.span_le.mpr hsub)
      rwa [hspan, finrank_top] at h2
    rwa [finrank_span_singleton hva₀] at h1
  omega

/-! ## The flat action of `G` : properness, cocompactness, faithfulness -/

/-- Properness of the flat action of `G` on `ξ^⊥`, transported from `hprop`. -/
lemma cuspFlatProper (n : ℕ) (hI : HypIsometryProp n) (ξ : E n) (hξ : ξ ∈ Sph n)
    (D : ℝ) (hD : 0 < D) (G : Subgroup (PO n 1))
    (hlev : ∀ g ∈ G, ∀ u : E n, lev ξ (g • u) = lev ξ u)
    (hprop : ∀ u₀ : E n, lev ξ u₀ = D → ∀ K : Set (E n), IsCompact K →
        {g : G | (g : PO n 1) • u₀ ∈ K}.Finite)
    (K : Set (xiPerp ξ)) (hK : IsCompact K) :
    {g : G | ((fun y : xiPerp ξ => flatFun hξ D (g : PO n 1) y) '' K ∩ K).Nonempty}.Finite := by
  have hKc : IsCompact ((fun y : xiPerp ξ => (y : E n)) '' K) :=
    hK.image continuous_subtype_val
  have hKW : ∀ y ∈ (fun y : xiPerp ξ => (y : E n)) '' K, inner ℝ y ξ = 0 := by
    rintro y ⟨z, hz, rfl⟩
    exact xiPerp_inner' z
  refine (flatActProper (n := n) (hI := hI) (ξ := ξ) (hξ := hξ) (D := D) (hD := hD)
    (G := G) (hlev := hlev) (hprop := hprop) _ hKc hKW).subset ?_
  rintro g ⟨z, ⟨y, hyK, hzy⟩, hzK⟩
  exact ⟨(y : E n), ⟨y, hyK, rfl⟩, (z : E n), ⟨z, hzK, rfl⟩, by rw [← hzy, flatFun_coe]⟩

/-- Cocompactness of the flat action of `G` on `ξ^⊥`, transported from `hcoc`. -/
lemma cuspFlatCocompact (n : ℕ) (hI : HypIsometryProp n) (ξ : E n) (hξ : ξ ∈ Sph n)
    (D : ℝ) (hD : 0 < D) (G : Subgroup (PO n 1))
    (hlev : ∀ g ∈ G, ∀ u : E n, lev ξ (g • u) = lev ξ u)
    (hcoc : ∃ K : Set (E n), IsCompact K ∧ ∀ u : E n, lev ξ u = D →
        ∃ g : G, (g : PO n 1) • u ∈ K) :
    ∃ K : Set (xiPerp ξ), IsCompact K ∧ ∀ y : xiPerp ξ,
      ∃ g : G, flatFun hξ D (g : PO n 1) y ∈ K := by
  obtain ⟨R, hR⟩ := flatActCocompact (n := n) (hI := hI) (ξ := ξ) (hξ := hξ) (D := D)
    (hD := hD) (G := G) (hlev := hlev) (hcoc := hcoc)
  refine ⟨Metric.closedBall (0 : xiPerp ξ) R, isCompact_closedBall _ _, fun y => ?_⟩
  obtain ⟨g, hg⟩ := hR (y : E n) (xiPerp_inner' y)
  exact ⟨g, by rw [Metric.mem_closedBall, dist_zero_right, ← Submodule.norm_coe
    (flatFun hξ D (g : PO n 1) y), flatFun_coe]; exact hg⟩

/-- The flat action of `G` on `ξ^⊥` is faithful: an element acting trivially on the level-`D`
horosphere is the identity. -/
lemma cuspFlatInjective (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n) (ξ : E n)
    (hξ : ξ ∈ Sph n) (D : ℝ) (hD : 0 < D) (G : Subgroup (PO n 1))
    (hfix : ∀ g ∈ G, bd g ξ = ξ)
    (hlev : ∀ g ∈ G, ∀ u : E n, lev ξ (g • u) = lev ξ u)
    (g : G) (hg : ∀ y : xiPerp ξ, flatFun hξ D (g : PO n 1) y = y) : g = 1 := by
  have hkey : ∀ Y : xiPerp ξ,
      (g : PO n 1) • hptOf ξ (Y : E n) D = hptOf ξ (Y : E n) D := by
    intro Y
    have hlevY : lev ξ ((g : PO n 1) • hptOf ξ (Y : E n) D) = D := by
      rw [hlev g g.2, (hptOfLevelYc ξ hξ (xiPerp_inner' Y) hD).1]
    have hyc : yc ξ ((g : PO n 1) • hptOf ξ (Y : E n) D) = yc ξ (hptOf ξ (Y : E n) D) := by
      have h := congrArg (fun z : xiPerp ξ => (z : E n)) (hg Y)
      simp only [flatFun_coe] at h
      rw [h, (hptOfLevelYc ξ hξ (xiPerp_inner' Y) hD).2.1]
    calc (g : PO n 1) • hptOf ξ (Y : E n) D
        = hptOf ξ (yc ξ ((g : PO n 1) • hptOf ξ (Y : E n) D)) D :=
          (hptOf_yc_eq_of_lev hξ hlevY).symm
      _ = hptOf ξ (yc ξ (hptOf ξ (Y : E n) D)) D := by rw [hyc]
      _ = hptOf ξ (Y : E n) D := by rw [(hptOfLevelYc ξ hξ (xiPerp_inner' Y) hD).2.1]
  have htriv : ∀ u : E n, lev ξ u = D → (g : PO n 1) • u = u := by
    intro u hu
    have hyu : inner ℝ (yc ξ u) ξ = 0 := inner_yc hξ u
    have hu' : u = hptOf ξ (yc ξ u) D := by
      calc u = hptOf ξ (yc ξ u) (lev ξ u) := (hptOf_yc_lev hξ u).symm
        _ = hptOf ξ (yc ξ u) D := by rw [hu]
    calc (g : PO n 1) • u = (g : PO n 1) • hptOf ξ (yc ξ u) D :=
          congrArg (fun z => (g : PO n 1) • z) hu'
      _ = hptOf ξ (yc ξ u) D := hkey ⟨yc ξ u, mem_xiPerp_iff.mpr (by
          rw [real_inner_comm]; exact hyu)⟩
      _ = u := hu'.symm
  apply Subtype.ext
  simpa using horoActTrivId (hA := hA) (g := (g : PO n 1)) (ξ := ξ) (hξ := hξ) (D := D)
    (hD := hD) (hfix g g.2) (hlev g g.2) htriv

/-! ## The main theorem -/

theorem cuspZ2 (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (hBb : ∀ m, BieberbachProp m) (ξ : E n) (hξ : ξ ∈ Sph n) (D : ℝ) (hD : 0 < D)
    (G : Subgroup (PO n 1)) (hfix : ∀ g ∈ G, bd g ξ = ξ)
    (hlev : ∀ g ∈ G, ∀ u : E n, lev ξ (g • u) = lev ξ u)
    (hprop : ∀ u₀ : E n, lev ξ u₀ = D → ∀ K : Set (E n), IsCompact K →
        {g : G | (g : PO n 1) • u₀ ∈ K}.Finite)
    (hcoc : ∃ K : Set (E n), IsCompact K ∧ ∀ u : E n, lev ξ u = D →
        ∃ g : G, (g : PO n 1) • u ∈ K)
    (γ₀ : G) :
    ∃ k : ℕ, 0 < k ∧ ∃ a b : G,
      a * γ₀ ^ k = γ₀ ^ k * a ∧ b * γ₀ ^ k = γ₀ ^ k * b ∧ a * b = b * a ∧
      (∀ i j : ℤ, a ^ i * b ^ j = 1 → i = 0 ∧ j = 0) := by
  have hAb : POBasic n := POBasic.ofProp hA
  have hId : HypIsoData n := HypIsoData.ofProp hI
  -- the flat action of `G` on `ξ^⊥`
  let ρ : G →* (xiPerp ξ ≃ᵢ xiPerp ξ) := cuspFlatHom hAb hId hξ D hD G hlev
  have hρapp : ∀ (g : G) (y : xiPerp ξ), ρ g y = flatFun hξ D (g : PO n 1) y := fun g y => rfl
  have hfin2 : 2 ≤ Module.finrank ℝ (xiPerp ξ) := by
    have := xiPerpFinrank n hn ξ hξ
    omega
  -- properness and cocompactness
  have hpd : ∀ K : Set (xiPerp ξ), IsCompact K →
      {g : G | ((ρ g) '' K ∩ K).Nonempty}.Finite := by
    intro K hK
    refine (cuspFlatProper n hI ξ hξ D hD G hlev hprop K hK).subset ?_
    rintro g ⟨z, ⟨y, hyK, hzy⟩, hzK⟩
    rw [hρapp g y] at hzy
    exact ⟨z, ⟨y, hyK, hzy⟩, hzK⟩
  have hcoc' : ∃ K : Set (xiPerp ξ), IsCompact K ∧ ∀ x : xiPerp ξ, ∃ g : G, ρ g x ∈ K := by
    obtain ⟨K, hKc, hK⟩ := cuspFlatCocompact n hI ξ hξ D hD G hlev hcoc
    exact ⟨K, hKc, fun x => by obtain ⟨g, hg⟩ := hK x; exact ⟨g, by rwa [hρapp g x]⟩⟩
  -- Bieberbach
  obtain ⟨T, v, hTfin, htrans, hspan⟩ :=
    bieberbachInnerProduct (hBb (Module.finrank ℝ (xiPerp ξ))) ρ hpd hcoc'
  haveI : T.FiniteIndex := hTfin
  -- the flat action is faithful, so `T` is abelian
  have hinj : Function.Injective ρ := by
    intro a b hab
    have h1 : ρ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ∀ y : xiPerp ξ, flatFun hξ D ((a * b⁻¹ : G) : PO n 1) y = y := by
      intro y
      have h := congrArg (fun (e : xiPerp ξ ≃ᵢ xiPerp ξ) => e y) h1
      have h' : (1 : xiPerp ξ ≃ᵢ xiPerp ξ) y = y := rfl
      rw [hρapp (a * b⁻¹) y, h'] at h
      exact h
    have h3 : a * b⁻¹ = 1 :=
      cuspFlatInjective n hA hI ξ hξ D hD G hfix hlev (a * b⁻¹) h2
    calc a = a * b⁻¹ * b := by group
      _ = 1 * b := by rw [h3]
      _ = b := one_mul b
  have hker : ∀ t ∈ T, ∀ s ∈ T, t * s = s * t := by
    intro t ht s hs
    apply hinj
    rw [map_mul, map_mul]
    apply IsometryEquiv.ext
    intro x
    have h1 : (ρ t * ρ s) x = x + (v s + v t) := by
      rw [IsometryEquiv.mul_apply, htrans s hs x, htrans t ht (x + v s)]
      abel
    have h2 : (ρ s * ρ t) x = x + (v t + v s) := by
      rw [IsometryEquiv.mul_apply, htrans t ht x, htrans s hs (x + v t)]
      abel
    rw [h1, h2]
    abel
  -- two independent translations
  obtain ⟨a, b, haT, hbT, hlin⟩ := spanTopIndependent (T := T) (v := v) hspan hfin2
  -- a power of `γ₀` lies in `T`
  obtain ⟨k, hkpos, -, hkT⟩ :=
    Subgroup.exists_pow_mem_of_index_ne_zero (H := T)
      (Subgroup.FiniteIndex.index_ne_zero (H := T)) γ₀
  refine ⟨k, hkpos, a, b, hker a haT (γ₀ ^ k) hkT, hker b hbT (γ₀ ^ k) hkT,
    hker a haT b hbT, ?_⟩
  -- `v` is a homomorphism on `T`, so integer relations between `a` and `b` give relations
  -- between `v a` and `v b`
  let ψ : T →* Multiplicative (xiPerp ξ) :=
    { toFun := fun t => Multiplicative.ofAdd (v t)
      map_one' := by
        rw [Multiplicative.ext_iff, toAdd_ofAdd, toAdd_one]
        have h := htrans (1 : G) (T.one_mem) (0 : xiPerp ξ)
        have h' : (0 : xiPerp ξ) + v 1 = 0 := by
          rw [← h, map_one]
          rfl
        simpa using h'
      map_mul' := fun s t => by
        rw [Multiplicative.ext_iff, toAdd_ofAdd, toAdd_mul, toAdd_ofAdd, toAdd_ofAdd]
        have h := htrans (s * t) (T.mul_mem s.2 t.2) (0 : xiPerp ξ)
        have h1 : (0 : xiPerp ξ) + v (s * t) = (0 : xiPerp ξ) + (v s + v t) := by
          rw [← h, map_mul, IsometryEquiv.mul_apply, htrans t t.2 (0 : xiPerp ξ),
            htrans s s.2 (0 + v t)]
          abel
        exact add_left_cancel h1 }
  intro i j hij
  have hmem : (⟨a, haT⟩ : T) ^ i * (⟨b, hbT⟩ : T) ^ j = 1 := by
    apply Subgroup.subtype_injective T
    rw [map_mul, map_zpow, map_zpow, map_one]
    simpa using hij
  have hzero : i • v a + j • v b = 0 := by
    have h1 : ψ ((⟨a, haT⟩ : T) ^ i * (⟨b, hbT⟩ : T) ^ j) = 1 := by rw [hmem, map_one]
    have h2 := congrArg Multiplicative.toAdd h1
    simp only [map_mul, map_zpow, toAdd_mul, toAdd_zpow, toAdd_one] at h2
    have ha : Multiplicative.toAdd (ψ ⟨a, haT⟩) = v a := rfl
    have hb : Multiplicative.toAdd (ψ ⟨b, hbT⟩) = v b := rfl
    rw [ha, hb] at h2
    exact h2
  have hcast : (i : ℝ) • v a + (j : ℝ) • v b = 0 := by
    simpa only [Int.cast_smul_eq_zsmul ℝ] using hzero
  obtain ⟨hi, hj⟩ := (LinearIndependent.pair_iff.mp hlin) (i : ℝ) (j : ℝ) hcast
  exact ⟨Int.cast_eq_zero.mp hi, Int.cast_eq_zero.mp hj⟩

end

end Work.Mostow

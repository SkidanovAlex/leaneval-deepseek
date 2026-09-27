import Mathlib
import Submission.Work.ManifoldParity.exists_tangentField_of_closed_curves
import Submission.Work.ManifoldParity.GraphManifold
import Submission.Work.ManifoldParity.CircleParam
import Submission.Work.ManifoldParity.fderiv_eq_of_eq_of_periodic
import Submission.Work.ManifoldParity.component_tangent_field
import Submission.Work.OneDim.classify_connected_one_manifold

/-!
# A continuous tangent field from local graph data

The target of this file: given a compact set `K` and a closed set `Z ⊇ K` such that at every point of
`K` the set `Z` is *locally the graph of a smooth curve over some coordinate axis* (`IsGraphData`),
there is a continuous non-vanishing field `U` on `K` which is parallel to the tangent of every such
local graph curve at every point of `K`.

The proof reduces to the per-component statement `Work.ManifoldParity.component_tangent_field`: the
union `W` of the local graph patches is a set that is locally a graph over a coordinate axis
(`HasLocalGraphCharts W`), hence `↥W` is a smooth `1`-manifold; its components carry tangent fields,
and `K` meets finitely many of them, so the fields glue over the components.
-/

open scoped Topology ContDiff
open Set Function Filter

namespace Work.ManifoldParity

noncomputable section

/-- The ambient Euclidean space `ℝ^{m+1}`. -/
abbrev Env (m : ℕ) := EuclideanSpace ℝ (Fin (m+1))

/-- **Local graph data for a set `S` at a point `x`** (the hypothesis clause of the target): a
coordinate `i` and a smooth curve `γ` with `(γ t) i = t`, whose graph over the coordinate `i`
agrees with `S` on the open set `R`. -/
def IsGraphData {m : ℕ} (S : Set (Env m)) (x : Env m) (i : Fin (m+1)) (γ : ℝ → Env m)
    (R : Set (Env m)) : Prop :=
  IsOpen R ∧ x ∈ R ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ ∧ (∀ t, (γ t) i = t) ∧
    γ (x i) = x ∧ (∀ y ∈ R, y ∈ S ↔ y = γ (y i))

namespace IsGraphData

variable {m : ℕ} {S : Set (Env m)} {x : Env m} {i : Fin (m+1)} {γ : ℝ → Env m} {R : Set (Env m)}

theorem isOpen (h : IsGraphData S x i γ R) : IsOpen R := h.1

theorem mem (h : IsGraphData S x i γ R) : x ∈ R := h.2.1

theorem contDiff (h : IsGraphData S x i γ R) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ := h.2.2.1

theorem coord (h : IsGraphData S x i γ R) (t : ℝ) : (γ t) i = t := h.2.2.2.1 t

theorem self (h : IsGraphData S x i γ R) : γ (x i) = x := h.2.2.2.2.1

theorem mem_iff (h : IsGraphData S x i γ R) {y : Env m} (hy : y ∈ R) :
    y ∈ S ↔ y = γ (y i) := h.2.2.2.2.2 y hy

/-- The `i`-th coordinate of the tangent vector `fderiv γ t 1` is `1`. -/
theorem fderiv_coord (h : IsGraphData S x i γ R) (t : ℝ) :
    ((fderiv ℝ γ t) (1 : ℝ)) i = 1 := by
  have hcoord : (fun s : ℝ => (γ s) i) = fun s : ℝ => s := funext h.coord
  have hd : DifferentiableAt ℝ γ t := (h.contDiff.differentiable (by simp)) t
  have h1 : HasDerivAt (fun s : ℝ => (γ s) i)
      (0 + ((PiLp.proj 2 (fun _ : Fin (m+1) => ℝ) i) (deriv γ t))) t :=
    (hasDerivAt_const (x := t) (c := PiLp.proj 2 (fun _ : Fin (m+1) => ℝ) i)).clm_apply
      hd.hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ => (γ s) i) 1 t := by rw [hcoord]; exact hasDerivAt_id t
  have huniq := h1.unique h2
  have hderiv : (deriv γ t) i = 1 := by
    simpa using huniq
  rw [fderiv_apply_one_eq_deriv]
  exact hderiv

/-- The tangent vector of a local graph chart never vanishes. -/
theorem fderiv_ne_zero (h : IsGraphData S x i γ R) (t : ℝ) :
    (fderiv ℝ γ t) (1 : ℝ) ≠ 0 := by
  intro h0
  have h1 := h.fderiv_coord t
  rw [h0] at h1
  simp at h1

end IsGraphData

/-- **Comparison of two local graph data.**  Suppose `(i₁, γ₁, R₁)` is local graph data for the set
`S` at `y`, `(i₂, γ₂, R₂)` is local graph data for the set `S'` at `y`, and the two sets agree on a
neighbourhood of `y`.  Then the tangent vectors are parallel. -/
theorem parallel_of_isGraphData {m : ℕ} {S S' : Set (Env m)} {y : Env m}
    {i₁ : Fin (m+1)} {γ₁ : ℝ → Env m} {R₁ : Set (Env m)}
    {i₂ : Fin (m+1)} {γ₂ : ℝ → Env m} {R₂ : Set (Env m)}
    (h₁ : IsGraphData S y i₁ γ₁ R₁) (h₂ : IsGraphData S' y i₂ γ₂ R₂)
    (hU : ∃ U ∈ 𝓝 y, ∀ z ∈ U, (z ∈ S ↔ z ∈ S')) :
    ∃ c : ℝ, c ≠ 0 ∧ fderiv ℝ γ₁ (y i₁) (1 : ℝ) = c • (fderiv ℝ γ₂ (y i₂) (1 : ℝ)) := by
  obtain ⟨U, hUne, hUiff⟩ := hU
  set ψ : ℝ → ℝ := fun t => (γ₁ t) i₂ with hψ
  have hmem₁ : R₁ ∈ 𝓝 y := h₁.isOpen.mem_nhds h₁.mem
  have hmem₂ : R₂ ∈ 𝓝 y := h₂.isOpen.mem_nhds h₂.mem
  have hmem₁' : R₁ ∈ 𝓝 (γ₁ (y i₁)) := by rw [h₁.self]; exact hmem₁
  have hmem₂' : R₂ ∈ 𝓝 (γ₁ (y i₁)) := by rw [h₁.self]; exact hmem₂
  have hmemU' : U ∈ 𝓝 (γ₁ (y i₁)) := by rw [h₁.self]; exact hUne
  have hcont₁ : ContinuousAt γ₁ (y i₁) := h₁.contDiff.continuous.continuousAt
  have hev : γ₁ =ᶠ[𝓝 (y i₁)] (γ₂ ∘ ψ) := by
    have h1 : ∀ᶠ t in 𝓝 (y i₁), γ₁ t ∈ R₁ := hcont₁.eventually hmem₁'
    have h2 : ∀ᶠ t in 𝓝 (y i₁), γ₁ t ∈ R₂ := hcont₁.eventually hmem₂'
    have h3 : ∀ᶠ t in 𝓝 (y i₁), γ₁ t ∈ U := hcont₁.eventually hmemU'
    filter_upwards [h1, h2, h3] with t ht1 ht2 ht3
    have hS : γ₁ t ∈ S := (h₁.mem_iff ht1).mpr (by rw [h₁.coord])
    have hS' : γ₁ t ∈ S' := (hUiff _ ht3).mp hS
    exact (h₂.mem_iff ht2).mp hS'
  have hd1 : DifferentiableAt ℝ γ₁ (y i₁) := (h₁.contDiff.differentiable (by simp)) _
  have hψeq : ψ = (fun v : Env m => v i₂) ∘ γ₁ := rfl
  have hdψ : DifferentiableAt ℝ ψ (y i₁) := by
    rw [hψeq]
    exact (ContinuousLinearMap.differentiableAt
      (PiLp.proj 2 (fun _ : Fin (m+1) => ℝ) i₂)).comp (y i₁) hd1
  have hψval : ψ (y i₁) = y i₂ := by
    rw [hψ]; exact congrArg (fun v : Env m => v i₂) h₁.self
  have hd2' : DifferentiableAt ℝ γ₂ (ψ (y i₁)) := by
    rw [hψval]; exact (h₂.contDiff.differentiable (by simp)) _
  have hcomp : fderiv ℝ (γ₂ ∘ ψ) (y i₁)
      = (fderiv ℝ γ₂ (y i₂)).comp (fderiv ℝ ψ (y i₁)) := by
    rw [fderiv_comp (y i₁) hd2' hdψ, hψval]
  have hfd : fderiv ℝ γ₁ (y i₁) = (fderiv ℝ γ₂ (y i₂)).comp (fderiv ℝ ψ (y i₁)) := by
    rw [Filter.EventuallyEq.fderiv_eq hev, hcomp]
  refine ⟨(fderiv ℝ ψ (y i₁)) (1 : ℝ), ?_, ?_⟩
  · intro hc
    apply h₁.fderiv_ne_zero (y i₁)
    rw [hfd, ContinuousLinearMap.comp_apply, hc, map_zero]
  · rw [hfd, ContinuousLinearMap.comp_apply]
    rw [show (fderiv ℝ ψ (y i₁)) (1 : ℝ) = ((fderiv ℝ ψ (y i₁)) (1 : ℝ)) • (1 : ℝ) from
      (mul_one _).symm, ContinuousLinearMap.map_smul]
    simp

/-- Two local graph data for the *same* set at the same point have parallel tangents. -/
theorem parallel_of_two_isGraphData {m : ℕ} {S : Set (Env m)} {y : Env m}
    {i₁ : Fin (m+1)} {γ₁ : ℝ → Env m} {R₁ : Set (Env m)}
    {i₂ : Fin (m+1)} {γ₂ : ℝ → Env m} {R₂ : Set (Env m)}
    (h₁ : IsGraphData S y i₁ γ₁ R₁) (h₂ : IsGraphData S y i₂ γ₂ R₂) :
    ∃ c : ℝ, c ≠ 0 ∧ fderiv ℝ γ₁ (y i₁) (1 : ℝ) = c • (fderiv ℝ γ₂ (y i₂) (1 : ℝ)) :=
  parallel_of_isGraphData h₁ h₂ ⟨univ, univ_mem, fun _ _ => Iff.rfl⟩


/-- The chosen local graph datum at a point of `K`. -/
structure LocalDatum {m : ℕ} (S : Set (Env m)) (x : Env m) where
  idx : Fin (m+1)
  g : ℝ → Env m
  R : Set (Env m)
  isData : IsGraphData S x idx g R

/-- **Main theorem.**  A compact set `K` contained in a closed set `Z` which is locally a graph of a
smooth curve over a coordinate axis at every point of `K` admits a continuous non-vanishing field
parallel to the tangent of every such local graph curve. -/
theorem exists_continuous_tangent_field_of_local_data_aux {m : ℕ}
    (K Z : Set (Env m)) (hK : IsCompact K) (hZ : IsClosed Z) (hKZ : K ⊆ Z)
    (hdata : ∀ x ∈ K, ∃ (i : Fin (m+1)) (γ : ℝ → Env m) (R : Set (Env m)),
        IsGraphData Z x i γ R) :
    ∃ U : Env m → Env m, ContinuousOn U K ∧ (∀ x ∈ K, U x ≠ 0) ∧
      (∀ x ∈ K, ∀ (i : Fin (m+1)) (γ : ℝ → Env m) (R : Set (Env m)),
        IsGraphData Z x i γ R → ∃ c : ℝ, c ≠ 0 ∧ U x = c • (fderiv ℝ γ (x i) (1 : ℝ))) := by
  classical
  -- ## The chosen local graph datum at each point of `K`
  let D : (p : ↥K) → LocalDatum Z p.1 := fun p =>
    let h1 := hdata p.1 p.2
    let h2 := Classical.choose_spec h1
    let h3 := Classical.choose_spec h2
    ⟨Classical.choose h1, Classical.choose h2, Classical.choose h3, Classical.choose_spec h3⟩
  have hD : ∀ p : ↥K, IsGraphData Z p.1 (D p).idx (D p).g (D p).R := fun p => (D p).isData
  -- ## The union of the patches
  let W : Set (Env m) := ⋃ p : ↥K, Z ∩ (D p).R
  have hWZ : W ⊆ Z := by
    intro z hz
    obtain ⟨p, hp⟩ := mem_iUnion.mp hz
    exact hp.1
  have hKW : K ⊆ W := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hKZ hx, (hD ⟨x, hx⟩).mem⟩
  have hpatch : ∀ x (hx : x ∈ K), Z ∩ (D ⟨x, hx⟩).R ⊆ W := by
    intro x hx z hz
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hz⟩
  -- ## `W` is locally a graph over a coordinate axis
  have hWgraph : HasLocalGraphCharts W := by
    intro z hz
    obtain ⟨p, hp⟩ := mem_iUnion.mp hz
    have hd := hD p
    refine ⟨(D p).idx, (D p).R,
      fun t => (D p).g t - t • EuclideanSpace.single (D p).idx (1 : ℝ), ?_, hp.2⟩
    refine ⟨hd.isOpen, ?_, ?_, ?_⟩
    · exact hd.contDiff.sub (contDiff_id.smul contDiff_const)
    · intro t
      simp [hd.coord t]
    · intro z' hz'
      have hgmap : gmap (D p).idx
          (fun t => (D p).g t - t • EuclideanSpace.single (D p).idx (1 : ℝ))
          (z' (D p).idx) = (D p).g (z' (D p).idx) := by
        rw [gmap_apply]
        abel
      rw [hgmap]
      constructor
      · intro hz'W
        exact (hd.mem_iff hz').mp (hWZ hz'W)
      · intro h
        exact mem_iUnion.mpr ⟨p, (hd.mem_iff hz').mpr h, hz'⟩
  -- ## The tangent field on one component (the geometric core, proved in a companion file)
  have hcrux : ∀ q : ↥W, ∃ U : Env m → Env m,
      ContinuousOn U ((Subtype.val : ↥W → Env m) '' (connectedComponent q)) ∧
      (∀ y ∈ (Subtype.val : ↥W → Env m) '' (connectedComponent q), U y ≠ 0) ∧
      (∀ y ∈ (Subtype.val : ↥W → Env m) '' (connectedComponent q),
        ∀ (i : Fin (m+1)) (V : Set (Env m)) (η : ℝ → Env m),
          IsGraphChart W i V η → y ∈ V → ∃ c : ℝ, c ≠ 0 ∧
            U y = c • (EuclideanSpace.single i (1 : ℝ) + (fderiv ℝ η (y i)) (1 : ℝ))) :=
    fun q => component_tangent_field W hWgraph q
  -- ## The same, stated for a component given as a *set*
  let cruxC : ∀ (C : Set ↥W), (∃ q : ↥W, C = connectedComponent q) → ∃ U : Env m → Env m,
      ContinuousOn U ((Subtype.val : ↥W → Env m) '' C) ∧
      (∀ y ∈ (Subtype.val : ↥W → Env m) '' C, U y ≠ 0) ∧
      (∀ y ∈ (Subtype.val : ↥W → Env m) '' C,
        ∀ (i : Fin (m+1)) (V : Set (Env m)) (η : ℝ → Env m),
          IsGraphChart W i V η → y ∈ V → ∃ c : ℝ, c ≠ 0 ∧
            U y = c • (EuclideanSpace.single i (1 : ℝ) + (fderiv ℝ η (y i)) (1 : ℝ))) :=
    fun C hC => by
      obtain ⟨q, hq⟩ := hC
      rw [hq]
      exact hcrux q
  -- ## A field attached to each component *set* (hence coherent)
  let fam : Set ↥W → Env m → Env m := fun C =>
    if h : ∃ q : ↥W, C = connectedComponent q then Classical.choose (cruxC C h) else 0
  have hfam : ∀ (C : Set ↥W) (hC : ∃ q : ↥W, C = connectedComponent q),
      ContinuousOn (fam C) ((Subtype.val : ↥W → Env m) '' C) ∧
      (∀ y ∈ (Subtype.val : ↥W → Env m) '' C, fam C y ≠ 0) ∧
      (∀ y ∈ (Subtype.val : ↥W → Env m) '' C,
        ∀ (i : Fin (m+1)) (V : Set (Env m)) (η : ℝ → Env m),
          IsGraphChart W i V η → y ∈ V → ∃ c : ℝ, c ≠ 0 ∧
            fam C y = c • (EuclideanSpace.single i (1 : ℝ) + (fderiv ℝ η (y i)) (1 : ℝ))) := by
    intro C hC
    rw [show fam C = Classical.choose (cruxC C hC) from dif_pos hC]
    exact Classical.choose_spec (cruxC C hC)
  -- ## The component of a point
  let Cof : Env m → Set ↥W := fun y =>
    if hy : y ∈ W then connectedComponent (⟨y, hy⟩ : ↥W) else ∅
  have hCof_mem : ∀ y (hy : y ∈ W), Cof y = connectedComponent (⟨y, hy⟩ : ↥W) := by
    intro y hy
    exact dif_pos hy
  have hCof_self : ∀ y (hy : y ∈ W), (⟨y, hy⟩ : ↥W) ∈ Cof y := by
    intro y hy
    rw [hCof_mem y hy]
    exact mem_connectedComponent
  -- ## Every point of `K` has a neighbourhood in `K` lying in a single component of `↥W`
  have hlocal : ∀ x ∈ K, ∃ O ∈ 𝓝 x, ∀ y ∈ K ∩ O, Cof y = Cof x := by
    intro x hx
    let p : ↥K := ⟨x, hx⟩
    let i : Fin (m+1) := (D p).idx
    let g : ℝ → Env m := (D p).g
    let t₀ : ℝ := x i
    have hd : IsGraphData Z x i g (D p).R := hD p
    have hgt₀ : g t₀ = x := hd.self
    have hSopen : IsOpen {t : ℝ | g t ∈ (D p).R} := hd.isOpen.preimage hd.contDiff.continuous
    have ht₀S : t₀ ∈ {t : ℝ | g t ∈ (D p).R} := by
      show g t₀ ∈ (D p).R
      rw [hgt₀]
      exact hd.mem
    obtain ⟨ε, hε, hεS⟩ := Metric.mem_nhds_iff.mp (hSopen.mem_nhds ht₀S)
    refine ⟨(D p).R ∩ {y : Env m | dist (y i) t₀ < ε}, ?_, ?_⟩
    · refine Filter.inter_mem (hd.isOpen.mem_nhds hd.mem) ?_
      refine (isOpen_lt ((coordProj i).continuous.dist continuous_const)
        continuous_const).mem_nhds ?_
      show dist (x i) t₀ < ε
      rw [show x i = t₀ from rfl, dist_self]
      exact hε
    · intro y hy
      obtain ⟨hyK, hyR, hyI⟩ := hy
      have hyW : y ∈ W := hKW hyK
      have hxW : x ∈ W := hKW hx
      have hyg : g (y i) = y := ((hd.mem_iff hyR).mp (hKZ hyK)).symm
      have hgy : ∀ t ∈ Metric.ball t₀ ε, g t ∈ W := by
        intro t ht
        have htS : g t ∈ (D p).R := hεS ht
        have htZ : g t ∈ Z := by
          refine (hd.mem_iff htS).mpr ?_
          rw [hd.coord]
        exact hpatch x hx ⟨htZ, htS⟩
      haveI : PreconnectedSpace ↥(Metric.ball t₀ ε) :=
        isPreconnected_iff_preconnectedSpace.mp (convex_ball t₀ ε).isPreconnected
      let Φ : ↥(Metric.ball t₀ ε) → ↥W := fun t => ⟨g t.1, hgy t.1 t.2⟩
      have hAcont : Continuous Φ := (hd.contDiff.continuous.comp continuous_subtype_val).subtype_mk _
      have hApc : IsPreconnected (Φ '' Set.univ) :=
        isPreconnected_univ.image Φ hAcont.continuousOn
      have hxA : (⟨x, hxW⟩ : ↥W) ∈ Φ '' Set.univ := by
        refine ⟨⟨t₀, Metric.mem_ball_self (by simpa using hε)⟩, Set.mem_univ _, ?_⟩
        exact Subtype.ext hgt₀
      have hyA : (⟨y, hyW⟩ : ↥W) ∈ Φ '' Set.univ := by
        refine ⟨⟨y i, Metric.mem_ball.mpr hyI⟩, Set.mem_univ _, ?_⟩
        exact Subtype.ext hyg
      have hsame : (⟨y, hyW⟩ : ↥W) ∈ connectedComponent (⟨x, hxW⟩ : ↥W) :=
        hApc.subset_connectedComponent hxA hyA
      rw [hCof_mem y hyW, hCof_mem x hxW]
      exact (connectedComponent_eq hsame).symm
  let U : Env m → Env m := fun y => fam (Cof y) y
  refine ⟨U, ?_, ?_, ?_⟩
  · -- continuity
    intro x hx
    have hCx : ∃ q : ↥W, Cof x = connectedComponent q :=
      ⟨⟨x, hKW hx⟩, hCof_mem x (hKW hx)⟩
    have hFx := hfam (Cof x) hCx
    have hxmem : x ∈ (Subtype.val : ↥W → Env m) '' Cof x :=
      ⟨⟨x, hKW hx⟩, hCof_self x (hKW hx), rfl⟩
    obtain ⟨O, hO, hsame⟩ := hlocal x hx
    have hsub : K ∩ O ⊆ (Subtype.val : ↥W → Env m) '' Cof x := by
      intro y hy
      obtain ⟨hyK, hyO⟩ := hy
      have h1 : Cof y = Cof x := hsame y ⟨hyK, hyO⟩
      have h2 : (⟨y, hKW hyK⟩ : ↥W) ∈ Cof x := by
        rw [← h1]
        exact hCof_self y (hKW hyK)
      exact ⟨⟨y, hKW hyK⟩, h2, rfl⟩
    have heq : U =ᶠ[𝓝[K] x] fam (Cof x) := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨K ∩ O, Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hO), ?_⟩
      rintro y ⟨hyK, hyO⟩
      have h1 : Cof y = Cof x := hsame y ⟨hyK, hyO⟩
      show fam (Cof y) y = fam (Cof x) y
      rw [h1]
    have hcont : ContinuousWithinAt (fam (Cof x)) K x :=
      (hFx.1 x hxmem).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset
          (Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hO)) hsub)
    exact hcont.congr_of_eventuallyEq_of_mem heq hx
  · -- non-vanishing
    intro x hx
    have hCx : ∃ q : ↥W, Cof x = connectedComponent q :=
      ⟨⟨x, hKW hx⟩, hCof_mem x (hKW hx)⟩
    have hxmem : x ∈ (Subtype.val : ↥W → Env m) '' Cof x :=
      ⟨⟨x, hKW hx⟩, hCof_self x (hKW hx), rfl⟩
    exact (hfam (Cof x) hCx).2.1 x hxmem
  · -- parallelism with every local graph datum
    intro x hx i γ R hR
    obtain ⟨i', V, η, hchart, hxV⟩ := hWgraph x (hKW hx)
    have hCx : ∃ q : ↥W, Cof x = connectedComponent q :=
      ⟨⟨x, hKW hx⟩, hCof_mem x (hKW hx)⟩
    have hxmem : x ∈ (Subtype.val : ↥W → Env m) '' Cof x :=
      ⟨⟨x, hKW hx⟩, hCof_self x (hKW hx), rfl⟩
    obtain ⟨c₁, hc₁, hFpar⟩ := (hfam (Cof x) hCx).2.2 x hxmem i' V η hchart hxV
    -- the graph chart read as local graph data for `W`
    set δ : ℝ → Env m := fun t => gmap i' η t with hδ
    have hδdata : IsGraphData W x i' δ V := by
      refine ⟨hchart.1, hxV, ?_, ?_, ?_, ?_⟩
      · exact contDiff_gmap hchart.2.1
      · intro t
        exact gmap_coord hchart.2.2.1 t
      · exact ((hchart.2.2.2 x hxV).mp (hKW hx)).symm
      · intro z hz
        exact hchart.2.2.2 z hz
    -- `Z` and `W` agree near `x`
    have hagree : ∃ U ∈ 𝓝 x, ∀ z ∈ U, (z ∈ Z ↔ z ∈ W) := by
      refine ⟨R ∩ (D ⟨x, hx⟩).R,
        Filter.inter_mem (hR.isOpen.mem_nhds hR.mem)
          ((hD ⟨x, hx⟩).isOpen.mem_nhds (hD ⟨x, hx⟩).mem), ?_⟩
      intro z hz
      exact ⟨fun hzZ => hpatch x hx ⟨hzZ, hz.2⟩, fun hzW => hWZ hzW⟩
    obtain ⟨c₂, hc₂, hpar⟩ := parallel_of_isGraphData hR hδdata hagree
    have hδderiv : fderiv ℝ δ (x i') (1 : ℝ)
        = EuclideanSpace.single i' (1 : ℝ) + (fderiv ℝ η (x i')) (1 : ℝ) := by
      have hdη : DifferentiableAt ℝ η (x i') := (hchart.2.1.differentiable (by simp)) _
      have hsum : HasFDerivAt (fun t : ℝ => t • EuclideanSpace.single i' (1 : ℝ) + η t)
          ((ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i' (1 : ℝ)))
            + fderiv ℝ η (x i')) (x i') :=
        (ContinuousLinearMap.hasFDerivAt
          (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i' (1 : ℝ)))).add
          hdη.hasFDerivAt
      have hfun : δ = fun t : ℝ => t • EuclideanSpace.single i' (1 : ℝ) + η t := by
        funext t
        rw [hδ]
        rfl
      rw [hfun, hsum.fderiv, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.toSpanSingleton_apply]
      simp
    refine ⟨c₁ * c₂⁻¹, mul_ne_zero hc₁ (inv_ne_zero hc₂), ?_⟩
    rw [show U x = fam (Cof x) x from rfl, hFpar, hpar, hδderiv]
    rw [smul_smul, mul_assoc, inv_mul_cancel₀ hc₂, mul_one]


/-- **Main theorem** (the statement as requested).  A compact set `K` contained in a closed set `Z`
which is locally a graph of a smooth curve over a coordinate axis at every point of `K` admits a
continuous non-vanishing field parallel to the tangent of every such local graph curve. -/
theorem exists_continuous_tangent_field_of_local_data {m : ℕ}
    (K Z : Set (EuclideanSpace ℝ (Fin (m+1)))) (hK : IsCompact K) (hZ : IsClosed Z)
    (hKZ : K ⊆ Z)
    (hdata : ∀ x ∈ K, ∃ (i : Fin (m+1)) (γ : ℝ → EuclideanSpace ℝ (Fin (m+1)))
        (R : Set (EuclideanSpace ℝ (Fin (m+1)))),
        IsOpen R ∧ x ∈ R ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ ∧ (∀ t, (γ t) i = t) ∧
        γ (x i) = x ∧ (∀ y ∈ R, y ∈ Z ↔ y = γ (y i))) :
    ∃ U : EuclideanSpace ℝ (Fin (m+1)) → EuclideanSpace ℝ (Fin (m+1)),
      ContinuousOn U K ∧ (∀ x ∈ K, U x ≠ 0) ∧
      (∀ x ∈ K, ∀ (i : Fin (m+1)) (γ : ℝ → EuclideanSpace ℝ (Fin (m+1)))
          (R : Set (EuclideanSpace ℝ (Fin (m+1)))),
        IsOpen R → x ∈ R → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ → (∀ t, (γ t) i = t) →
        γ (x i) = x → (∀ y ∈ R, y ∈ Z ↔ y = γ (y i)) →
        ∃ c : ℝ, c ≠ 0 ∧ U x = c • (fderiv ℝ γ (x i) 1)) := by
  obtain ⟨U, hcont, hne, hpar⟩ :=
    exists_continuous_tangent_field_of_local_data_aux K Z hK hZ hKZ hdata
  exact ⟨U, hcont, hne, fun x hx i γ R hR hxR hsm hci heq hgr =>
    hpar x hx i γ R ⟨hR, hxR, hsm, hci, heq, hgr⟩⟩

end

end Work.ManifoldParity

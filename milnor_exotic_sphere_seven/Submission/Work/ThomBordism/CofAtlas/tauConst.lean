import Mathlib
import Submission.Work.ThomBordism.CofAtlas.Signs
import Submission.Work.ThomBordism.CofAtlas.Delta_comp_DeltaInv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The sign `tau` of a chart change is constant and nonzero on the chart source

`Work.ThomBordism.CofAtlas.tauConst`: for the coframed level-set data `D : Cof k n M`, a point
`x` of the level set lying over an *interior* point of the ambient manifold, and any `p` in the
connected source `D.src x` of the chart at `x`,

* `D.tau x p = D.tau x x` (the sign of the chart change is constant on the source), and
* `D.tau x p ≠ 0` (the chart change is invertible there).

Both statements are consequences of the invertibility `Delta x q ∘ DeltaInv x q = 1`
(`Delta_comp_DeltaInv`) together with the *continuity* of `q ↦ Delta x q` on the preconnected
source `D.src x`:

* nonvanishing: `det (Delta x q) * det (DeltaInv x q) = det 1 = 1`, so `det (Delta x q) ≠ 0`;
* constancy: `q ↦ det (Delta x q)` is continuous and nonzero on the preconnected `D.src x`, hence
  its sign is constant (intermediate value theorem: a change of sign would force a zero).

The continuity of `q ↦ Delta x q = fderiv ℝ (ambDomChange x) (ambExt x q)` is the composition of

* `q ↦ ambExt x q = (ambChart x).extend I q`, continuous at `q` because `q` lies in the source of
  the chart at `x` (`OpenPartialHomeomorph.continuousAt_extend`),
* `fderiv ℝ (ambDomChange x)`, continuous at `ambExt x q` because the transition
  `I.extendCoordChange (ambChart x) (domChart x)` is `C^∞` (within `range I`) at that point
  (`ModelWithCorners.contDiffWithinAt_extendCoordChange'`) and `ambExt x q` lies in the *interior*
  of `range I` — which is where the hypothesis `x ∉ ∂M` is used: it forces every point of the
  chart source to be an interior point of `M`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter ModelWithCorners
open Work.PTGeometric

namespace Work.ThomBordism.CofAtlas

noncomputable section

/-! ## A continuous nonvanishing function on a preconnected set has constant sign -/

/-- **A continuous nonvanishing real function on a preconnected set has constant sign.** -/
theorem sign_eq_of_isPreconnected {α : Type*} [TopologicalSpace α] {s : Set α}
    (hs : IsPreconnected s) {g : α → ℝ} (hg : ContinuousOn g s)
    (hg0 : ∀ x ∈ s, g x ≠ 0) {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
    SignType.sign (g x) = SignType.sign (g y) := by
  by_contra hne
  have hx0 : g x ≠ 0 := hg0 x hx
  have hy0 : g y ≠ 0 := hg0 y hy
  have hxcase : SignType.sign (g x) = 1 ∨ SignType.sign (g x) = -1 := by
    rcases lt_trichotomy (g x) 0 with h | h | h
    · exact Or.inr (sign_neg h)
    · exact absurd h hx0
    · exact Or.inl (sign_pos h)
  have hycase : SignType.sign (g y) = 1 ∨ SignType.sign (g y) = -1 := by
    rcases lt_trichotomy (g y) 0 with h | h | h
    · exact Or.inr (sign_neg h)
    · exact absurd h hy0
    · exact Or.inl (sign_pos h)
  have hbetween : (0 : ℝ) ∈ Set.Icc (g x) (g y) ∨ (0 : ℝ) ∈ Set.Icc (g y) (g x) := by
    rcases hxcase with h1 | h1 <;> rcases hycase with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · exact Or.inr ⟨le_of_lt (sign_eq_neg_one_iff.mp h2), le_of_lt (sign_eq_one_iff.mp h1)⟩
    · exact Or.inl ⟨le_of_lt (sign_eq_neg_one_iff.mp h1), le_of_lt (sign_eq_one_iff.mp h2)⟩
    · exact absurd (h1.trans h2.symm) hne
  have himg : (g '' s).OrdConnected := (hs.image g hg).ordConnected
  rcases hbetween with hb | hb
  · obtain ⟨r, hr, hr0⟩ := himg.out ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ hb
    exact hg0 r hr hr0
  · obtain ⟨r, hr, hr0⟩ := himg.out ⟨y, hy, rfl⟩ ⟨x, hx, rfl⟩ hb
    exact hg0 r hr hr0

/-! ## Continuity of the chart change `Delta` -/

variable {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (NN k)) M]
  [IsManifold (𝓡∂ (NN k)) ((⊤ : ENat) : WithTop ENat) M]

/-- **The chart change `Delta x ·` is continuous at every point of the source `src x`.** -/
theorem Cof.continuousAt_delta (D : Cof k n M) (x : D.S.Pre) {p : D.S.Pre}
    (hp : p ∈ D.src x) (hx : (x : M) ∉ (𝓡∂ (NN k)).boundary M) :
    ContinuousAt (fun p : D.S.Pre => D.Delta x (p : M)) p := by
  have hn : (((⊤ : ENat) : WithTop ENat) : ℕ∞ω) ≠ 0 := by simp
  have hambx : D.ambChart x ∈ IsManifold.maximalAtlas (𝓡∂ (NN k))
      ((⊤ : ENat) : WithTop ENat) M :=
    IsManifold.chart_mem_maximalAtlas (x : M)
  have hdomx : D.domChart x ∈ IsManifold.maximalAtlas (𝓡∂ (NN k))
      ((⊤ : ENat) : WithTop ENat) M :=
    Lvl.Setup.domChartAt_mem_maximalAtlas D.S x
  have hsrc : (p : M) ∈ (D.ambChart x).source := D.src_subset_ambSrc x hp
  have hdomsrc : (p : M) ∈ (D.domChart x).source := (D.src_subset_chartSource x hp).1
  have hint : (p : M) ∈ (𝓡∂ (NN k)).interior M :=
    D.interior_of_mem_intSrc x hx (D.src_subset_intSrc x hp)
  have hy : (D.ambExt x (p : M)) ∈ interior (range (𝓡∂ (NN k))) :=
    tcD_mem_interior_range (𝓡∂ (NN k)) hn hambx hsrc hint
  have hcd : ContDiffAt ℝ (((⊤ : ENat) : WithTop ENat) : ℕ∞ω) (D.ambDomChange x)
      (D.ambExt x (p : M)) :=
    (ModelWithCorners.contDiffWithinAt_extendCoordChange' (I := 𝓡∂ (NN k))
      (n := ((⊤ : ENat) : WithTop ENat)) hambx hdomx hsrc hdomsrc).contDiffAt
      (mem_of_superset (isOpen_interior.mem_nhds hy) interior_subset)
  have hcontF : ContinuousAt (fderiv ℝ (D.ambDomChange x)) (D.ambExt x (p : M)) :=
    hcd.continuousAt_fderiv hn
  have hcontAmb : ContinuousAt (fun p : D.S.Pre => D.ambExt x (p : M)) p :=
    (OpenPartialHomeomorph.continuousAt_extend (D.ambChart x) hsrc).comp
      continuous_subtype_val.continuousAt
  exact hcontF.comp (f := fun p : D.S.Pre => D.ambExt x (p : M)) hcontAmb

/-- **`p ↦ det (Delta x p)` is continuous on the source `src x`** (for an interior centre `x`). -/
theorem Cof.continuousOn_det_delta (D : Cof k n M) (x : D.S.Pre)
    (hx : (x : M) ∉ (𝓡∂ (NN k)).boundary M) :
    ContinuousOn (fun p : D.S.Pre => LinearMap.det (D.Delta x (p : M)).toLinearMap)
      (D.src x) := by
  intro p hp
  have h1 : ContinuousAt (fun p : D.S.Pre => (D.Delta x (p : M)).det) p :=
    ContinuousLinearMap.continuous_det.continuousAt.comp (D.continuousAt_delta x hp hx)
  exact h1.continuousWithinAt

/-- **The chart change `Delta x p` is invertible at every point of the source** (interior centre):
its determinant is nonzero. -/
theorem Cof.det_delta_ne_zero (D : Cof k n M) (x : D.S.Pre) {p : D.S.Pre}
    (hp : p ∈ D.src x) (hx : (x : M) ∉ (𝓡∂ (NN k)).boundary M) :
    LinearMap.det (D.Delta x (p : M)).toLinearMap ≠ 0 := by
  have hcomp := Delta_comp_DeltaInv D x (D.src_subset_chartSource x hp)
    (D.src_subset_ambSrc x hp) (D.interior_of_mem_intSrc x hx (D.src_subset_intSrc x hp))
  have key : LinearMap.det (D.Delta x (p : M)).toLinearMap
      * LinearMap.det (D.DeltaInv x (p : M)).toLinearMap = 1 := by
    have h2 := congrArg
      (fun (L : ModN k →L[ℝ] ModN k) => LinearMap.det L.toLinearMap) hcomp
    rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
      ContinuousLinearMap.toLinearMap_one] at h2
    simpa using h2
  intro h
  rw [h, zero_mul] at key
  exact zero_ne_one key

/-! ## The target -/

theorem tauConst
    {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) ((⊤ : ENat) : WithTop ENat) M]
    (D : Work.ThomBordism.CofAtlas.Cof k n M) (x : D.S.Pre)
    (hx : (x : M) ∉ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M) :
    (∀ p : D.S.Pre, p ∈ D.src x → D.tau x (p : M) = D.tau x (x : M)) ∧
    (∀ p : D.S.Pre, p ∈ D.src x → D.tau x (p : M) ≠ 0) := by
  constructor
  · intro p hp
    exact sign_eq_of_isPreconnected (D.isPreconnected_src x)
      (D.continuousOn_det_delta x hx)
      (fun q hq => D.det_delta_ne_zero x hq hx) hp (D.mem_src_self x)
  · intro p hp
    exact sign_ne_zero.mpr (D.det_delta_ne_zero x hp hx)

end

end Work.ThomBordism.CofAtlas

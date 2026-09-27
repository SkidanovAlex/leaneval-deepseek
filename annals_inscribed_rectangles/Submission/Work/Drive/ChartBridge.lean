import Mathlib
import Submission.Work.Drive.regular_of_transverse
import Submission.Work.Drive.exists_local_normalForm
import Submission.Work.Drive.boxParity

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# The chart bridge: derivative of the charted difference map

For a smooth `4`-manifold `M` (charted on `ℝ⁴`) and smooth maps `D : ℝ² → M`, `N : ℝ³ → M`, the
local model of the intersection problem is the *charted difference map*

`chartDiff p D N : ℝ⁵ → ℝ⁴,  x ↦ φ (D (sqPart x)) − φ (N (cbPart x))`

where `φ = chartAt ℝ⁴ p` is a chart of `M` and `sqPart`, `cbPart` are the two block projections of
`ℝ⁵ = ℝ² × ℝ³`.  On the *chart region* `chartRegion p D N` (where both images lie in the source of
`φ`) this map is smooth and its zero set is exactly the set of pairs with `D (sqPart x) = N (cbPart x)`.

This file computes its Fréchet derivative in terms of the manifold derivatives `mfderiv D`,
`mfderiv N` (via the change-of-coordinates maps `tangentCoordChange`), which is what allows the
transversality hypothesis (`htrans`) and the face hypothesis (`hface`) of
`Work.Drive.transverse_inter_boundary_parity` to be turned into the hypotheses of the vector-space
theorem `Submission.Drive.ParityProp` (proved as `Work.Drive.boxParity`).
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-- The chart at `p`. -/
def chr (p : M) : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 4)) :=
  chartAt (EuclideanSpace ℝ (Fin 4)) p

/-- **The chart region**: the points of `ℝ⁵` where both `D` and `N` take their values in the source
of the chart at `p`. -/
def chartRegion (p : M) (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M) :
    Set (Amb 4) :=
  {x | D (sqPart x) ∈ (chr p).source ∧ N (cbPart x) ∈ (chr p).source}

/-- **The charted difference map** of the two chains in the chart at `p`. -/
def chartDiff (p : M) (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M) :
    Amb 4 → Tgt 4 :=
  fun x => chr p (D (sqPart x)) - chr p (N (cbPart x))

theorem mem_chartRegion {p : M} {D : EuclideanSpace ℝ (Fin 2) → M}
    {N : EuclideanSpace ℝ (Fin 3) → M} {x : Amb 4} :
    x ∈ chartRegion p D N ↔
      D (sqPart x) ∈ (chr p).source ∧ N (cbPart x) ∈ (chr p).source := Iff.rfl

/-- The chart region is open. -/
theorem isOpen_chartRegion (p : M) (D : EuclideanSpace ℝ (Fin 2) → M)
    (N : EuclideanSpace ℝ (Fin 3) → M)
    (hD : Continuous D) (hN : Continuous N) : IsOpen (chartRegion p D N) := by
  have h1 : Continuous fun x : Amb 4 => D (sqPart x) := hD.comp (by unfold sqPart; fun_prop)
  have h2 : Continuous fun x : Amb 4 => N (cbPart x) := hN.comp (by unfold cbPart; fun_prop)
  exact (h1.isOpen_preimage _ (chr p).open_source).inter
    (h2.isOpen_preimage _ (chr p).open_source)

/-- The charted difference map vanishes exactly where the two chains meet (inside the chart
region). -/
theorem chartDiff_eq_zero_iff {p : M} {D : EuclideanSpace ℝ (Fin 2) → M}
    {N : EuclideanSpace ℝ (Fin 3) → M} {x : Amb 4} (hx : x ∈ chartRegion p D N) :
    chartDiff p D N x = 0 ↔ D (sqPart x) = N (cbPart x) := by
  rw [chartDiff, sub_eq_zero, mem_chartRegion] at *
  constructor
  · intro h
    exact (chr p).injOn hx.1 hx.2 h
  · intro h
    rw [h]

/-- **The derivative of the chart-composition `φ ∘ D`**, in terms of `mfderiv D` and the
change-of-coordinates map `tangentCoordChange`. -/
theorem mfderiv_chart_comp {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → M)
    (hf : ContMDiff (𝓡 n) (𝓡 4) Ctop f) (p : M) {s : EuclideanSpace ℝ (Fin n)}
    (hs : f s ∈ (chr p).source) :
    mfderiv (𝓡 n) (𝓡 4) (fun u => chr p (f u)) s =
      (tangentCoordChange (𝓡 4) (f s) p (f s)).comp (mfderiv (𝓡 n) (𝓡 4) f s) := by
  have hφ : MDifferentiableAt (𝓡 4) (𝓡 4) (chartAt (EuclideanSpace ℝ (Fin 4)) p) (f s) :=
    mdifferentiableAt_atlas (chart_mem_atlas _ _) hs
  have hfs : MDifferentiableAt (𝓡 n) (𝓡 4) f s := (hf s).mdifferentiableAt (by simp)
  have hmain := mfderiv_comp s hφ hfs
  rw [mfderiv_chartAt_eq_tangentCoordChange hs] at hmain
  exact hmain

/-- The same, for the Fréchet derivative (the source is a vector space). -/
theorem fderiv_chart_comp {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → M)
    (hf : ContMDiff (𝓡 n) (𝓡 4) Ctop f) (p : M) {s : EuclideanSpace ℝ (Fin n)}
    (hs : f s ∈ (chr p).source) :
    fderiv ℝ (fun u => chr p (f u)) s =
      (tangentCoordChange (𝓡 4) (f s) p (f s)).comp (mfderiv (𝓡 n) (𝓡 4) f s) := by
  rw [← mfderiv_eq_fderiv]
  exact mfderiv_chart_comp f hf p hs

/-- The two-sided inverse of `tangentCoordChange`. -/
theorem tangentCoordChange_comp_inv {x y z : M}
    (h : z ∈ (extChartAt (𝓡 4) x).source ∩ (extChartAt (𝓡 4) y).source) (v : EuclideanSpace ℝ (Fin 4)) :
    tangentCoordChange (𝓡 4) y x z (tangentCoordChange (𝓡 4) x y z v) = v := by
  have h1 : z ∈ (extChartAt (𝓡 4) x).source ∩ (extChartAt (𝓡 4) y).source ∩
      (extChartAt (𝓡 4) x).source := ⟨⟨h.1, h.2⟩, h.1⟩
  have h2 := tangentCoordChange_comp (I := 𝓡 4) (w := x) (x := y) (y := x) (z := z) (v := v) h1
  rw [tangentCoordChange_self (I := 𝓡 4) h.1] at h2
  exact h2

theorem chartDiff_eq (p : M) (D : EuclideanSpace ℝ (Fin 2) → M)
    (N : EuclideanSpace ℝ (Fin 3) → M) :
    chartDiff p D N =
      fun x => chr p (D (sqPartCLM x)) - chr p (N (cbPartCLM x)) := by
  funext x
  simp only [chartDiff, sqPartCLM_eq_sqPart, cbPartCLM_eq_cbPart]

theorem fderiv_chart_comp_hasFDerivAt {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → M)
    (hf : ContMDiff (𝓡 n) (𝓡 4) Ctop f) (p : M) {s : EuclideanSpace ℝ (Fin n)}
    (hs : f s ∈ (chr p).source) :
    HasFDerivAt (fun u => chr p (f u))
      ((tangentCoordChange (𝓡 4) (f s) p (f s)).comp (mfderiv (𝓡 n) (𝓡 4) f s)) s := by
  have h1 : MDifferentiableAt (𝓡 4) (𝓡 4) (chr p : M → EuclideanSpace ℝ (Fin 4)) (f s) :=
    mdifferentiableAt_atlas (chart_mem_atlas _ _) hs
  have h2 : MDifferentiableAt (𝓡 n) (𝓡 4) f s := (hf s).mdifferentiableAt (by simp)
  have hmd : MDifferentiableAt (𝓡 n) (𝓡 4) (fun u => chr p (f u)) s := h1.comp s h2
  rw [← fderiv_chart_comp f hf p hs]
  exact hmd.differentiableAt.hasFDerivAt

-- The main derivative formula for the charted difference map (pointwise form).
theorem fderiv_chartDiff_apply (p : M) (D : EuclideanSpace ℝ (Fin 2) → M)
    (N : EuclideanSpace ℝ (Fin 3) → M)
    (hD : ContMDiff (𝓡 2) (𝓡 4) Ctop D) (hN : ContMDiff (𝓡 3) (𝓡 4) Ctop N)
    {x : Amb 4} (hx : x ∈ chartRegion p D N) (v : Amb 4) :
    fderiv ℝ (chartDiff p D N) x v =
      tangentCoordChange (𝓡 4) (D (sqPart x)) p (D (sqPart x))
          (mfderiv (𝓡 2) (𝓡 4) D (sqPart x) (sqPartCLM v))
        - tangentCoordChange (𝓡 4) (N (cbPart x)) p (N (cbPart x))
          (mfderiv (𝓡 3) (𝓡 4) N (cbPart x) (cbPartCLM v)) := by
  obtain ⟨hx1, hx2⟩ := hx
  have h1 := fderiv_chart_comp_hasFDerivAt D hD p hx1
  have h2 := fderiv_chart_comp_hasFDerivAt N hN p hx2
  have h1' : HasFDerivAt (fun y : Amb 4 => chr p (D (sqPartCLM y)))
      (((tangentCoordChange (𝓡 4) (D (sqPart x)) p (D (sqPart x))).comp
        (mfderiv (𝓡 2) (𝓡 4) D (sqPart x))).comp (sqPartCLM)) x := by
    have hc := h1.comp x (sqPartCLM.hasFDerivAt (x := x))
    simpa [Function.comp_def, sqPartCLM_eq_sqPart] using hc
  have h2' : HasFDerivAt (fun y : Amb 4 => chr p (N (cbPartCLM y)))
      (((tangentCoordChange (𝓡 4) (N (cbPart x)) p (N (cbPart x))).comp
        (mfderiv (𝓡 3) (𝓡 4) N (cbPart x))).comp (cbPartCLM)) x := by
    have hc := h2.comp x (cbPartCLM.hasFDerivAt (x := x))
    simpa [Function.comp_def, cbPartCLM_eq_cbPart] using hc
  have h3 : HasFDerivAt (chartDiff p D N)
      ((((tangentCoordChange (𝓡 4) (D (sqPart x)) p (D (sqPart x))).comp
          (mfderiv (𝓡 2) (𝓡 4) D (sqPart x))).comp (sqPartCLM))
        - (((tangentCoordChange (𝓡 4) (N (cbPart x)) p (N (cbPart x))).comp
          (mfderiv (𝓡 3) (𝓡 4) N (cbPart x))).comp (cbPartCLM))) x := by
    rw [chartDiff_eq]
    exact h1'.sub h2'
  rw [h3.fderiv]
  rw [sub_apply]
  rfl

/-! ## Corollaries: transversality, the face criterion, and smoothness -/



open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

theorem tangentCoordChange_left_inv {x y z : M}
    (h : z ∈ (extChartAt (𝓡 4) x).source ∩ (extChartAt (𝓡 4) y).source) :
    Function.LeftInverse (tangentCoordChange (𝓡 4) y x z) (tangentCoordChange (𝓡 4) x y z) :=
  fun v => tangentCoordChange_comp_inv h v

theorem tangentCoordChange_injective {x y z : M}
    (h : z ∈ (extChartAt (𝓡 4) x).source ∩ (extChartAt (𝓡 4) y).source) :
    Function.Injective (tangentCoordChange (𝓡 4) x y z) :=
  (tangentCoordChange_left_inv h).injective

/-- The two change-of-coordinates maps agree when the base points agree. -/
theorem tangentCoordChange_congr {y y' p : M} (h : y = y') :
    tangentCoordChange (𝓡 4) y p y = tangentCoordChange (𝓡 4) y' p y' := by
  rw [h]

variable (p : M) (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M)

/-- The derivative of the charted difference map in the direction `mkPart σ τ`. -/
theorem chartDiff_fderiv_mkPart (hD : ContMDiff (𝓡 2) (𝓡 4) Ctop D)
    (hN : ContMDiff (𝓡 3) (𝓡 4) Ctop N)
    {x : Amb 4} (hx : x ∈ chartRegion p D N)
    (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (chartDiff p D N) x (mkPart σ τ) =
      tangentCoordChange (𝓡 4) (D (sqPart x)) p (D (sqPart x))
          (mfderiv (𝓡 2) (𝓡 4) D (sqPart x) σ)
        - tangentCoordChange (𝓡 4) (N (cbPart x)) p (N (cbPart x))
          (mfderiv (𝓡 3) (𝓡 4) N (cbPart x) τ) := by
  rw [fderiv_chartDiff_apply p D N hD hN hx]
  rw [sqPartCLM_mkPart, cbPartCLM_mkPart]

/-- **A common direction of the two derivatives is a kernel direction of the charted difference
map.** -/
theorem chartDiff_fderiv_mkPart_eq_zero (hD : ContMDiff (𝓡 2) (𝓡 4) Ctop D)
    (hN : ContMDiff (𝓡 3) (𝓡 4) Ctop N)
    {x : Amb 4} (hx : x ∈ chartRegion p D N) (heq : D (sqPart x) = N (cbPart x))
    {σ : EuclideanSpace ℝ (Fin 2)} {τ : EuclideanSpace ℝ (Fin 3)}
    (hστ : mfderiv (𝓡 2) (𝓡 4) D (sqPart x) σ
      = mfderiv (𝓡 3) (𝓡 4) N (cbPart x) τ) :
    fderiv ℝ (chartDiff p D N) x (mkPart σ τ) = 0 := by
  rw [chartDiff_fderiv_mkPart p D N hD hN hx σ τ]
  -- the two change-of-coordinates maps agree; it remains to use `hστ`
  have htceq : tangentCoordChange (𝓡 4) (D (sqPart x)) p (D (sqPart x))
      = tangentCoordChange (𝓡 4) (N (cbPart x)) p (N (cbPart x)) := by
    rw [← heq]
  rw [← htceq]
  rw [← hστ, sub_self]

end



open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-- The `i`-th coordinate of `mkPart σ τ`, for an `s`-block index. -/
theorem mkPart_sqIdx (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)) (i : Fin 2) :
    mkPart σ τ (sqIdx i) = σ i := by
  simp [mkPart, sqIdx, Fin.addCases_left]

/-- The `j`-th coordinate of `mkPart σ τ`, for a `t`-block index. -/
theorem mkPart_cbIdx (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)) (j : Fin 3) :
    mkPart σ τ (cbIdx j) = τ j := by
  simp [mkPart, cbIdx, Fin.addCases_right]

/-- **The face criterion for the charted difference map.**  If the charted difference map is a
submersion at a point of the chart region at which the two chains meet, and a common direction of the
two derivatives has non-zero `i`-th coordinate, then the restriction of the derivative to the
coordinate hyperplane `{v | v i = 0}` is surjective. -/
theorem chartDiff_face_of_kernel (p : M) (D : EuclideanSpace ℝ (Fin 2) → M)
    (N : EuclideanSpace ℝ (Fin 3) → M)
    (hD : ContMDiff (𝓡 2) (𝓡 4) Ctop D) (hN : ContMDiff (𝓡 3) (𝓡 4) Ctop N)
    {x : Amb 4} (hx : x ∈ chartRegion p D N) (heq : D (sqPart x) = N (cbPart x))
    (hsurj : Function.Surjective (fderiv ℝ (chartDiff p D N) x))
    {i : Fin 5} {σ : EuclideanSpace ℝ (Fin 2)} {τ : EuclideanSpace ℝ (Fin 3)}
    (hστ : mfderiv (𝓡 2) (𝓡 4) D (sqPart x) σ
      = mfderiv (𝓡 3) (𝓡 4) N (cbPart x) τ) (hi : mkPart σ τ i ≠ 0) :
    Function.Surjective (fun v : {v : Amb 4 // v i = 0} =>
      fderiv ℝ (chartDiff p D N) x v.1) := by
  rw [surjective_domRestrict_iff_cofactorVec_ne_zero _ hsurj i]
  have hk : fderiv ℝ (chartDiff p D N) x (mkPart σ τ) = 0 :=
    chartDiff_fderiv_mkPart_eq_zero p D N hD hN hx heq hστ
  have hne : mkPart σ τ ≠ 0 := by
    intro h
    exact hi (by rw [h]; rfl)
  exact (cofactorVec_apply_ne_zero_iff _ hsurj hk hne i).mpr hi

theorem chartDiff_surjective_of_transverse (p : M) (D : EuclideanSpace ℝ (Fin 2) → M)
    (N : EuclideanSpace ℝ (Fin 3) → M)
    (hD : ContMDiff (𝓡 2) (𝓡 4) Ctop D) (hN : ContMDiff (𝓡 3) (𝓡 4) Ctop N)
    {x : Amb 4} (hx : x ∈ chartRegion p D N) (heq : D (sqPart x) = N (cbPart x))
    (htrans : LinearMap.range (mfderiv (𝓡 2) (𝓡 4) D (sqPart x)).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) N (cbPart x)).toLinearMap = ⊤) :
    Function.Surjective (fderiv ℝ (chartDiff p D N) x) := by
  have hx1 : D (sqPart x) ∈ (chr p).source := hx.1
  have hx2 : N (cbPart x) ∈ (chr p).source := hx.2
  set T : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    tangentCoordChange (𝓡 4) (D (sqPart x)) p (D (sqPart x)) with hT
  have hsrc1 : D (sqPart x) ∈ (extChartAt (𝓡 4) (D (sqPart x))).source :=
    mem_extChartAt_source (I := 𝓡 4) (D (sqPart x))
  have hsrc2 : D (sqPart x) ∈ (extChartAt (𝓡 4) p).source := by
    rw [extChartAt_source]; exact hx1
  have hleft2 : Function.LeftInverse T (tangentCoordChange (𝓡 4) p (D (sqPart x)) (D (sqPart x))) :=
    fun v => tangentCoordChange_comp_inv ⟨hsrc2, hsrc1⟩ v
  have hsurjT : Function.Surjective T := hleft2.surjective
  have htceq' : ∀ v : EuclideanSpace ℝ (Fin 4),
      tangentCoordChange (𝓡 4) (N (cbPart x)) p (N (cbPart x)) v =
        tangentCoordChange (𝓡 4) (D (sqPart x)) p (D (sqPart x)) v := by
    intro v; rw [← heq]
  intro w
  obtain ⟨w', hw'⟩ := hsurjT w
  have hw'mem : w' ∈ (mfderiv (𝓡 2) (𝓡 4) D (sqPart x)).range ⊔
      (mfderiv (𝓡 3) (𝓡 4) N (cbPart x)).range := by
    rw [htrans]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hw'mem
  obtain ⟨σ, hσ₀⟩ := LinearMap.mem_range.mp ha
  obtain ⟨τ, hτ₀⟩ := LinearMap.mem_range.mp (Submodule.neg_mem _ hb)
  have hσ : mfderiv (𝓡 2) (𝓡 4) D (sqPart x) σ = a := hσ₀
  have hτ : mfderiv (𝓡 3) (𝓡 4) N (cbPart x) τ = -b := hτ₀
  refine ⟨mkPart σ τ, ?_⟩
  rw [chartDiff_fderiv_mkPart p D N hD hN hx σ τ, htceq']
  rw [hσ, hτ, map_neg, sub_neg_eq_add, ← map_add, hab, hw']

end



open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

example (p : M) : ContMDiffOn (𝓡 4) (𝓡 4) Ctop (chr p) (chr p).source := by
  have h := contMDiffOn_extChartAt (I := 𝓡 4) (x := p) (n := Ctop)
  simpa [chr] using h

example (p : M) (D : EuclideanSpace ℝ (Fin 2) → M)
    (hD : ContMDiff (𝓡 2) (𝓡 4) Ctop D) :
    ContMDiff (𝓡 5) (𝓡 4) Ctop (fun x : Amb 4 => D (sqPart x)) := by
  have h1 : ContMDiff (𝓡 5) (𝓡 2) Ctop (sqPart : Amb 4 → EuclideanSpace ℝ (Fin 2)) := by
    have : (sqPart : Amb 4 → EuclideanSpace ℝ (Fin 2)) = ⇑sqPartCLM := by
      funext x; exact sqPartCLM_eq_sqPart x
    rw [this]
    exact sqPartCLM.contMDiff
  exact hD.comp h1

end



open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

theorem contMDiffOn_chart_comp (f : Amb 4 → M) (hf : ContMDiff (𝓡 5) (𝓡 4) Ctop f) (p : M) :
    ContMDiffOn (𝓡 5) (𝓡 4) Ctop (fun x => chr p (f x)) (f ⁻¹' (chr p).source) := by
  have hchart : ContMDiffOn (𝓡 4) (𝓡 4) Ctop (chr p) (chr p).source := by
    have h := contMDiffOn_extChartAt (I := 𝓡 4) (x := p) (n := Ctop)
    simpa [chr] using h
  have hcomp := hchart.comp (hf.contMDiffOn (s := f ⁻¹' (chr p).source)) (fun x hx => hx)
  simpa [Function.comp_def] using hcomp

theorem contDiffOn_chartDiff (p : M) (D : EuclideanSpace ℝ (Fin 2) → M)
    (N : EuclideanSpace ℝ (Fin 3) → M)
    (hD : ContMDiff (𝓡 2) (𝓡 4) Ctop D) (hN : ContMDiff (𝓡 3) (𝓡 4) Ctop N) :
    ContDiffOn ℝ Ctop (chartDiff p D N) (chartRegion p D N) := by
  have hD2 : ContMDiff (𝓡 5) (𝓡 4) Ctop (fun x : Amb 4 => D (sqPart x)) := by
    have h1 : ContMDiff (𝓡 5) (𝓡 2) Ctop (sqPart : Amb 4 → EuclideanSpace ℝ (Fin 2)) := by
      have : (sqPart : Amb 4 → EuclideanSpace ℝ (Fin 2)) = ⇑sqPartCLM := by
        funext x; exact sqPartCLM_eq_sqPart x
      rw [this]
      exact sqPartCLM.contMDiff
    exact hD.comp h1
  have hN2 : ContMDiff (𝓡 5) (𝓡 4) Ctop (fun x : Amb 4 => N (cbPart x)) := by
    have h1 : ContMDiff (𝓡 5) (𝓡 3) Ctop (cbPart : Amb 4 → EuclideanSpace ℝ (Fin 3)) := by
      have : (cbPart : Amb 4 → EuclideanSpace ℝ (Fin 3)) = ⇑cbPartCLM := by
        funext x; exact cbPartCLM_eq_cbPart x
      rw [this]
      exact cbPartCLM.contMDiff
    exact hN.comp h1
  have h1 := contMDiffOn_chart_comp (fun x : Amb 4 => D (sqPart x)) hD2 p
  have h2 := contMDiffOn_chart_comp (fun x : Amb 4 => N (cbPart x)) hN2 p
  have hD3 : ContDiffOn ℝ Ctop (fun x : Amb 4 => chr p (D (sqPart x)))
      (chartRegion p D N) := by
    have := h1.mono (fun x (hx : x ∈ chartRegion p D N) => hx.1)
    intro x hx
    have h1x : ContMDiffWithinAt (𝓡 5) (𝓡 4) Ctop
        (fun x : Amb 4 => chr p (D (sqPart x))) (chartRegion p D N) x := this x hx
    simpa [writtenInExtChartAt] using (contMDiffWithinAt_iff.mp h1x).2
  have hN3 : ContDiffOn ℝ Ctop (fun x : Amb 4 => chr p (N (cbPart x)))
      (chartRegion p D N) := by
    have := h2.mono (fun x (hx : x ∈ chartRegion p D N) => hx.2)
    intro x hx
    have h1x : ContMDiffWithinAt (𝓡 5) (𝓡 4) Ctop
        (fun x : Amb 4 => chr p (N (cbPart x))) (chartRegion p D N) x := this x hx
    simpa [writtenInExtChartAt] using (contMDiffWithinAt_iff.mp h1x).2
  have hsub := hD3.sub hN3
  rw [show chartDiff p D N = fun x : Amb 4 => chr p (D (sqPart x)) - chr p (N (cbPart x)) from rfl]
  exact hsub

end



open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

example : writtenInExtChartAt (𝓡 5) (𝓡 5) (0 : EuclideanSpace ℝ (Fin 5)) (fun x : EuclideanSpace ℝ (Fin 5) => x) = id := by
  funext x
  simp [writtenInExtChartAt]

theorem contMDiffOn_to_contDiffOn (F : EuclideanSpace ℝ (Fin 5) → EuclideanSpace ℝ (Fin 4))
    (s : Set (EuclideanSpace ℝ (Fin 5)))
    (h : ContMDiffOn (𝓡 5) (𝓡 4) (n := Ctop) F s) : ContDiffOn ℝ Ctop F s := by
  intro x hx
  have h1 := (contMDiffWithinAt_iff.mp (h x hx)).2
  simpa [writtenInExtChartAt] using h1

end


end


end Work.Drive

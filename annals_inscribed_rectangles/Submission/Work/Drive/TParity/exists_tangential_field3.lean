import Mathlib
import Submission.Work.Drive.TParity.Basic
import Submission.Work.Drive.TParity.LocalGraph
import Submission.Work.Drive.TParity.ChartDeriv
import Submission.Work.Drive.TParity.graph_tangent_field
import Submission.Work.Drive.TParity.exists_flowCover3
import Submission.Work.Euclidean.TangentField.exists_smooth_tangent_field

/-!
# A smooth compactly supported field tangent to the triple intersection set

`Work.Drive.TParity.exists_tangential_field3`: in the nine-box picture of the triple intersection
set `K3 D` of three smooth chains, if `K3 D` is locally a graph of a smooth function over a
coordinate axis, then there is a smooth compactly supported field `V` on the nine-box which is
non-zero on `K3 D` and which lies in the kernel of the derivative of every charted difference map
at every point of `K3 D`.

The existence of a smooth compactly supported field which is non-zero and parallel to the graph
tangent at every point of a compact locally-graph set is the Euclidean statement
`Work.Euclidean.TangentField.exists_smooth_tangent_field` (proved by reducing to the proved
ManifoldParity chapter).  The only work of this file is the translation:

* `K3 D` is compact (it is a closed subset of the compact nine-box);
* the local graph hypothesis of the present statement is exactly the `P`-form hypothesis of the
  Euclidean lemma with `P = meet3 D` and `K = K3 D`;
* the parallelism with the graph tangent is converted into the kernel condition
  `Vtan D V` by `graph_tangent_mem_ker`, which differentiates the charted difference map along the
  graph curve `t ↦ t • eᵢ + η t` of a local graph chart.

Note (a trap, not used below): the hypothesis `hgra` alone does **not** make the charted difference
map `chartDiff3 p D` a submersion at the points of `K3 D`; its rank can drop below `8`.  For example
with `M = ℝ⁴`, `D 0 u = (u₀, u₁, u₂, u₀² + u₁²)` and `D 1 = D 2 = e`, `e u = (u₀, u₁, u₂, 0)`, the
triple intersection set is the line `{t • (e₂ + e₅ + e₈)}` (so `hgra` holds with `η t = t • (e₅ + e₈)`,
`i = 2`), while at `0 ∈ K3` the derivative of the charted difference map has rank `6`.  Accordingly
the argument here never invokes transversality: the tangential field is produced from the graph
structure alone (`Work.Euclidean.TangentField.exists_smooth_tangent_field`), which is exactly the
hypothesis `hgra` supplies.
-/

namespace Work.Drive.TParity

open scoped Manifold ContDiff Topology
open Manifold Set

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-- **The graph tangent of a local graph chart kills the charted difference map.**

If `(i, U, η)` is a local graph representation of the triple intersection set at the point
`x ∈ region3 p D` at which the three chains meet, then the derivative of the charted difference map
`chartDiff3 p D` at `x` annihilates the graph tangent vector `tanVec i η x = eᵢ + η'(xᵢ)(1)`.

Indeed, the graph curve `t ↦ gcurve i η t = t • eᵢ + η t` is exactly the triple intersection set
near `x`, hence the charted difference map vanishes along it, and the chain rule gives the claim. -/
theorem graph_tangent_mem_ker (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, ContMDiff (𝓡 3) (𝓡 4) Ctop (D k))
    {p : M} {x : Amb 8} (hx : x ∈ region3 p D) (hm : meet3 D x)
    {i : Fin 9} {U : Set (Amb 8)} {η : ℝ → Amb 8}
    (hU : IsOpen U) (hxU : x ∈ U) (hη : ContDiff ℝ Ctop η) (hηi : ∀ t, η t i = 0)
    (hgr : ∀ y ∈ U, (meet3 D y ↔ y = (y i) • EuclideanSpace.single i (1:ℝ) + η (y i))) :
    fderiv ℝ (chartDiff3 p D) x (tanVec i η x) = 0 := by
  have hγcd : ContDiff ℝ Ctop (gcurve i η) := contDiff_gcurve hη
  have hγc : Continuous (gcurve i η) := hγcd.continuous
  -- `x` is the graph point at parameter `x i`
  have hxγ : x = gcurve i η (x i) := by
    have h1 := (hgr x hxU).mp hm
    rw [gcurve_def]
    exact h1
  have hxγ' : gcurve i η (x i) = x := hxγ.symm
  -- the graph curve stays in the chart region and in the graph chart near `x i`
  have hregion_open : IsOpen (region3 p D) := isOpen_region3 p D (fun k => (hD k).continuous)
  have hx' : gcurve i η (x i) ∈ region3 p D := by rw [hxγ']; exact hx
  have hxU' : gcurve i η (x i) ∈ U := by rw [hxγ']; exact hxU
  have hγmem : ∀ᶠ t in 𝓝 (x i), gcurve i η t ∈ region3 p D :=
    hγc.continuousAt (hregion_open.mem_nhds hx')
  have hγU : ∀ᶠ t in 𝓝 (x i), gcurve i η t ∈ U :=
    hγc.continuousAt (hU.mem_nhds hxU')
  -- along the graph curve the charted difference map vanishes
  have hzero : (fun t => chartDiff3 p D (gcurve i η t)) =ᶠ[𝓝 (x i)] (fun _ => 0) := by
    filter_upwards [hγmem, hγU] with t hreg hUt
    rw [chartDiff3_eq_zero_iff hreg]
    refine (hgr (gcurve i η t) hUt).mpr ?_
    have h2 : (gcurve i η t) i = t := gcurve_apply_i hηi t
    rw [h2]
    rfl
  have hderiv0 : fderiv ℝ (fun t => chartDiff3 p D (gcurve i η t)) (x i) = 0 := by
    rw [Filter.EventuallyEq.fderiv_eq hzero]
    simp
  -- the chain rule
  have hdiffψ : DifferentiableAt ℝ (chartDiff3 p D) (gcurve i η (x i)) := by
    have h := (contDiffOn_chartDiff3 p D hD).contDiffAt (hregion_open.mem_nhds hx')
    exact h.differentiableAt (by simp)
  have hdiffγ : DifferentiableAt ℝ (gcurve i η) (x i) := hγcd.differentiable (by simp) _
  have hcomp : fderiv ℝ (fun t => chartDiff3 p D (gcurve i η t)) (x i)
      = (fderiv ℝ (chartDiff3 p D) (gcurve i η (x i))).comp
        (fderiv ℝ (gcurve i η) (x i)) :=
    fderiv_comp (x := x i) hdiffψ hdiffγ
  have hkey : fderiv ℝ (chartDiff3 p D) x ((fderiv ℝ (gcurve i η) (x i)) 1) = 0 := by
    have h1 := congrArg (fun (L : ℝ →L[ℝ] Tgt 8) => L 1) hcomp
    simp only [ContinuousLinearMap.comp_apply] at h1
    rw [hderiv0, zero_apply] at h1
    rw [← hxγ] at h1
    exact h1.symm
  -- the derivative of the graph curve is the graph tangent
  have hγderiv : (fderiv ℝ (gcurve i η) (x i)) 1 = tanVec i η x := by
    rw [tanVec_eq_deriv hη x, fderiv_apply_one_eq_deriv]
  rw [hγderiv] at hkey
  exact hkey

theorem exists_tangential_field3 {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (D k))
    (hgra : ∀ x ∈ Work.Drive.TParity.K3 D,
      ∃ (i : Fin 9) (U : Set (Work.Drive.Amb 8)) (η : ℝ → Work.Drive.Amb 8),
        IsOpen U ∧ x ∈ U ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧ (∀ t, η t i = 0) ∧
        (∀ y ∈ U, (Work.Drive.TParity.meet3 D y ↔
          y = (y i) • EuclideanSpace.single i (1:ℝ) + η (y i)))) :
    ∃ V : Work.Drive.Amb 8 → Work.Drive.Amb 8,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V ∧ HasCompactSupport V ∧
      Work.Drive.TParity.Vne D V ∧ Work.Drive.TParity.Vtan D V := by
  -- `K3 D` is compact
  have hK : IsCompact (K3 D) := isCompact_K3 D (fun k => (hD k).continuous)
  -- the Euclidean tangent-field lemma, applied with `P = meet3 D`
  obtain ⟨V, hVcd, hVcs, hVne, hVpar⟩ :=
    Work.Euclidean.TangentField.exists_smooth_tangent_field (n := 9)
      (P := fun y : Amb 8 => meet3 D y) (K := K3 D) hK (fun x hx => hx.2) (fun x hx => hgra x hx)
  refine ⟨V, hVcd, hVcs, hVne, ?_⟩
  -- convert the parallelism with the graph tangent into the kernel condition
  intro x hx p hxreg
  obtain ⟨i, U, η, hUo, hxU, hη, hηi, hgr⟩ := hgra x hx
  obtain ⟨c, hc, hcV⟩ := hVpar x hx i U η hUo hxU hη hηi hgr
  have hG : fderiv ℝ (chartDiff3 p D) x (tanVec i η x) = 0 :=
    graph_tangent_mem_ker D hD hxreg hx.2 hUo hxU hη hηi hgr
  rw [hcV, map_smul]
  show c • (fderiv ℝ (chartDiff3 p D) x (tanVec i η x)) = 0
  rw [hG, smul_zero]

end

end Work.Drive.TParity

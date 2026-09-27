import Mathlib
import Submission.Work.Drive.TParity.Basic
import Submission.Work.Drive.TParity.LocalGraph
import Submission.Work.Drive.TParity.ChartDeriv
import Submission.Work.Drive.ManifoldParity.FlowSetupDefs

/-!
# The local flow chart of the triple intersection set

The nine-box analogue of `Work.Drive.exists_flowChart_at` (`ManifoldParity/InterSetFlowDefs.lean`):
at a point of the triple intersection set `K3 D`, the charted difference map is surjective and also
surjective on the coordinate hyperplane `{v | v i = 0}`, the tangential field `V` is non-zero there;
then `K3 D` is, near that point, the graph of a continuous `η` over the `i`-th coordinate
(`Work.Drive.TParity.exists_local_graph3`), shrunk so that the `i`-th component of `V` is bounded away
from zero on the chart region: a `Work.Drive.FlowChart`.
-/

namespace Work.Drive.TParity

open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- **The coordinate of a non-zero tangent vector** (nine-box form of
`Work.Drive.kernel_coord_ne_zero`).  If `T : ℝ⁹ → ℝ⁸` is surjective and also surjective on the
coordinate hyperplane `{v | v i = 0}`, then every non-zero kernel vector has non-zero `i`-th
coordinate. -/
theorem kernel_coord_ne_zero8 {T : Amb 8 →L[ℝ] Tgt 8} (hT : Function.Surjective T)
    {k : Amb 8} (hk : T k = 0) (hne : k ≠ 0) {i : Fin 9}
    (hsurj : Function.Surjective (fun v : {v : Amb 8 // v i = 0} => T v.1)) : k i ≠ 0 :=
  (Work.Drive.cofactorVec_apply_ne_zero_iff T hT hk hne i).mp
    (Work.Drive.cofactorVec_apply_ne_zero T i hsurj)

/-- **The local flow chart of the triple intersection set.**  If the derivative of the charted
difference map at `x ∈ K3 D` is surjective and also surjective on the coordinate hyperplane
`{v | v i = 0}`, then there is a `FlowChart` for `K3 D` at `x` with coordinate `i`. -/
theorem exists_flowChart_at3 {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (D k))
    {V : Work.Drive.Amb 8 → Work.Drive.Amb 8} (hVcont : Continuous V)
    {x : Work.Drive.Amb 8} (hx : x ∈ Work.Drive.TParity.K3 D)
    (hsurj : Function.Surjective
      (fderiv ℝ (Work.Drive.TParity.chartDiff3 (D 0 (Work.Drive.TParity.bPartC 0 x)) D) x))
    (htan : fderiv ℝ (Work.Drive.TParity.chartDiff3 (D 0 (Work.Drive.TParity.bPartC 0 x)) D) x (V x) = 0)
    (hne : V x ≠ 0) (i : Fin 9)
    (hsurj_i : Function.Surjective (fun v : {v : Work.Drive.Amb 8 // v i = 0} =>
      fderiv ℝ (Work.Drive.TParity.chartDiff3 (D 0 (Work.Drive.TParity.bPartC 0 x)) D) x v.1)) :
    ∃ C : Work.Drive.FlowChart V (Work.Drive.TParity.K3 D) x, C.i = i ∧ x ∈ C.region := by
  obtain ⟨_, hmeet⟩ := hx
  have hxreg : x ∈ region3 (D 0 (bPartC 0 x)) D := mem_region3_self D hmeet
  obtain ⟨δ, ρ, η, hδ, hρ, hηcd, hηi, hηx, hchar⟩ :=
    exists_local_graph3 (D 0 (bPartC 0 x)) D hD hxreg hmeet i hsurj_i
  have hηc : Continuous η := hηcd.continuous
  have hVi : V x i ≠ 0 := kernel_coord_ne_zero8 hsurj htan hne hsurj_i
  have hVipos : 0 < |V x i| := abs_pos.mpr hVi
  -- a small ball on which the `i`-th component of `V` stays away from zero
  have hcont_i : Continuous fun y : Amb 8 => V y i :=
    (PiLp.continuous_apply 2 (fun _ : Fin 9 => ℝ) i).comp hVcont
  obtain ⟨εV, hεV, hεV'⟩ : ∃ εV > 0, ∀ y, ‖y - x‖ < εV → |V y i - V x i| < |V x i| / 2 := by
    have hhalf : 0 < |V x i| / 2 := by linarith
    obtain ⟨εV, hεV, h⟩ := Metric.continuousAt_iff.mp hcont_i.continuousAt (|V x i| / 2) hhalf
    exact ⟨εV, hεV, fun y hy => by
      have h' := h (by rwa [dist_eq_norm])
      rwa [Real.dist_eq] at h'⟩
  have hε0 : (0 : ℝ) < min εV 1 := lt_min hεV one_pos
  obtain ⟨εη, hεη, hεη'⟩ : ∃ εη > 0, ∀ u, |u - x i| < εη → ‖η u - η (x i)‖ < min εV 1 / 3 := by
    have h3 : 0 < min εV 1 / 3 := by linarith
    obtain ⟨εη, hεη, h⟩ := Metric.continuousAt_iff.mp hηc.continuousAt (min εV 1 / 3) h3
    exact ⟨εη, hεη, fun u hu => by
      have h' := h (by rwa [Real.dist_eq])
      rwa [dist_eq_norm] at h'⟩
  set δs : ℝ := min δ (min εη (min εV 1 / 3)) with hδsdef
  set ρs : ℝ := min ρ (min εV 1 / 3) with hρsdef
  set cval : ℝ := |V x i| / 2 with hcvaldef
  have hδs : 0 < δs := by
    rw [hδsdef]; exact lt_min hδ (lt_min hεη (by linarith))
  have hρs : 0 < ρs := by
    rw [hρsdef]; exact lt_min hρ (by linarith)
  have hcval : 0 < cval := by rw [hcvaldef]; linarith
  have hδsle : δs ≤ δ := by rw [hδsdef]; exact min_le_left _ _
  have hρsle : ρs ≤ ρ := by rw [hρsdef]; exact min_le_left _ _
  have hδsε : δs ≤ min εV 1 / 3 := by
    rw [hδsdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hδsη : δs ≤ εη := by
    rw [hδsdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρsε : ρs ≤ min εV 1 / 3 := by rw [hρsdef]; exact min_le_right _ _
  -- the region of the shrunk chart lies in the ball of radius `min εV 1` around `x`
  have hball : ∀ y : Amb 8, |y i - x i| < δs →
      ‖y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i)‖ < ρs →
      ‖y - x‖ < min εV 1 := by
    intro y h1 h2
    have h1' : |y i - x i| < min εV 1 / 3 := lt_of_lt_of_le h1 hδsε
    have h1'' : |y i - x i| < εη := lt_of_lt_of_le h1 hδsη
    have h2' : ‖y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i)‖ < min εV 1 / 3 :=
      lt_of_lt_of_le h2 hρsε
    have h3 : ‖η (y i) - η (x i)‖ < min εV 1 / 3 := hεη' (y i) h1''
    have hdecomp : y - x = (y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i)) +
        (η (y i) - η (x i)) + ((y i - x i) • EuclideanSpace.single i (1 : ℝ)) := by
      rw [hηx]; module
    have hsingle : ‖(y i - x i) • EuclideanSpace.single (i : Fin 9) (1 : ℝ)‖ = |y i - x i| := by
      rw [norm_smul, Real.norm_eq_abs, PiLp.norm_single]
      simp
    rw [hdecomp]
    calc ‖(y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i)) + (η (y i) - η (x i)) +
          ((y i - x i) • EuclideanSpace.single i (1 : ℝ))‖
        ≤ ‖y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i)‖ + ‖η (y i) - η (x i)‖ +
          ‖(y i - x i) • EuclideanSpace.single i (1 : ℝ)‖ := by
          have h1 := norm_add_le (y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i))
            (η (y i) - η (x i))
          have h2 := norm_add_le
            ((y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i)) + (η (y i) - η (x i)))
            ((y i - x i) • EuclideanSpace.single i (1 : ℝ))
          linarith
      _ = ‖y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i)‖ + ‖η (y i) - η (x i)‖ +
          |y i - x i| := by rw [hsingle]
      _ < min εV 1 := by linarith
  have hgraphs : ∀ y : Amb 8, |y i - x i| < δs →
      ‖y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i)‖ < ρs → y ∈ K3 D →
      y = (y i) • EuclideanSpace.single i (1 : ℝ) + η (y i) := by
    intro y h1 h2 hy
    obtain ⟨-, hiff⟩ := hchar y (lt_of_lt_of_le h1 hδsle) (lt_of_lt_of_le h2 hρsle)
    exact hiff.mp hy.2
  have hvels : ∀ y : Amb 8, |y i - x i| < δs →
      ‖y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i)‖ < ρs → cval ≤ |V y i| := by
    intro y h1 h2
    have hb := hball y h1 h2
    have hεV'' : ‖y - x‖ < εV := lt_of_lt_of_le hb (min_le_left _ _)
    have hlt : |V y i - V x i| < |V x i| / 2 := hεV' y hεV''
    have htri : |V x i| - |V y i| ≤ |V x i - V y i| := by
      have h := abs_add_le (V x i - V y i) (V y i)
      rw [sub_add_cancel] at h
      linarith
    have hlt' : |V x i - V y i| < |V x i| / 2 := by rwa [abs_sub_comm] at hlt
    have : |V x i| - |V y i| < |V x i| / 2 := lt_of_le_of_lt htri hlt'
    rw [hcvaldef]
    linarith
  let C : FlowChart V (K3 D) x :=
    { i := i, δ := δs, ρ := ρs, c := cval, η := η, hδ := hδs, hρ := hρs,
      hc := hcval, hηc := hηc, hηi := hηi, hgraph := hgraphs, hvel := hvels }
  refine ⟨C, rfl, ?_⟩
  rw [FlowChart.mem_region]
  refine ⟨by simp only [sub_self, abs_zero]; exact hδs, ?_⟩
  have h0 : x - (x i) • EuclideanSpace.single i (1 : ℝ) - η (x i) = 0 := by
    rw [hηx]; abel
  rw [h0, norm_zero]
  exact hρs

end

end Work.Drive.TParity

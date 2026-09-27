import Mathlib
import Submission.Work.Drive.ManifoldParity.InterSetDefs
import Submission.Work.Drive.ManifoldParity.FlowSetupDefs
import Submission.Work.Drive.ManifoldParity.exists_local_graph
import Submission.Work.Drive.ChartBridge
import Submission.Work.Drive.cofactor_restrict_surjective
import Submission.Work.Drive.flowField_basic
import Submission.Work.Drive.integralCurve_unique

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# The flow of a tangential field on the intersection set of two chains

This file sets up the instantiation of the abstract flow theory (`FlowSetup`, `FlowChart`, …) for the
intersection set `K = interSet D N` of two smooth chains `D : ℝ² → M`, `N : ℝ³ → M` in a smooth
4-manifold, and a global tangential field `V`:

* `exists_domRestrict_surjective` — a surjective `ℝ⁵ → ℝ⁴` has a coordinate hyperplane on which it is
  surjective;
* `kernel_coord_ne_zero` — a non-zero kernel vector of such a map is non-zero in that coordinate;
* `flowV`, `flowV_zero`, `flowV_deriv`, `flowV_add` — the (global) flow of `V`;
* `exists_flowChart_at` — the local graph structure of `K` (`FlowChart`) at a point of `K`, with a
  prescribed coordinate `i`, on which the `i`-th component of `V` does not vanish.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Set Manifold

set_option backward.isDefEq.respectTransparency false

noncomputable section

/-! ## Linear algebra: the coordinate hyperplane -/

/-- **A surjective linear map `ℝ^{m+1} → ℝ^m` is surjective on some coordinate hyperplane.**  Its
kernel is non-trivial (dimension reasons: otherwise it would be injective), and for any non-zero
kernel vector `k` the restriction to `{v | v i = 0}` has trivial kernel when `k i ≠ 0`, hence is
surjective for dimension reasons; in terms of the cofactor vector, this is
`cofactorVec_apply_ne_zero`. -/
theorem exists_domRestrict_surjective {m : ℕ} {T : Amb m →L[ℝ] Tgt m}
    (hT : Function.Surjective T) :
    ∃ i : Fin (m + 1), Function.Surjective (fun v : {v : Amb m // v i = 0} => T v.1) := by
  have hker : LinearMap.ker (T : Amb m →ₗ[ℝ] Tgt m) ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective (T : Amb m →ₗ[ℝ] Tgt m) := LinearMap.ker_eq_bot.mp hbot
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    have h1 : Module.finrank ℝ (Amb m) = m + 1 := by simp [Amb]
    have h2 : Module.finrank ℝ (Tgt m) = m := by simp [Tgt]
    omega
  obtain ⟨k, hkmem, hkne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hk : T k = 0 := hkmem
  have hcoord : ∃ i : Fin (m + 1), k i ≠ 0 := by
    by_contra h
    push Not at h
    exact hkne (by rw [← WithLp.ofLp_eq_zero, funext_iff]; exact h)
  obtain ⟨i, hi⟩ := hcoord
  refine ⟨i, ?_⟩
  rw [surjective_domRestrict_iff_cofactorVec_ne_zero T hT i]
  exact (cofactorVec_apply_ne_zero_iff T hT hk hkne i).mpr hi

/-- **The coordinate of a non-zero tangent vector.**  If `T : ℝ^{m+1} → ℝ^m` is surjective and also
surjective on the coordinate hyperplane `{v | v i = 0}`, then every non-zero kernel vector has
non-zero `i`-th coordinate. -/
theorem kernel_coord_ne_zero {m : ℕ} {T : Amb m →L[ℝ] Tgt m} (hT : Function.Surjective T)
    {k : Amb m} (hk : T k = 0) (hne : k ≠ 0) {i : Fin (m + 1)}
    (hsurj : Function.Surjective (fun v : {v : Amb m // v i = 0} => T v.1)) : k i ≠ 0 :=
  (cofactorVec_apply_ne_zero_iff T hT hk hne i).mp (cofactorVec_apply_ne_zero T i hsurj)

/-! ## The flow of the field -/

/-- The global flow of a compactly supported smooth field `V : ℝ⁵ → ℝ⁵`, as a function of the time
and the initial point. -/
noncomputable def flowV (V : Amb 4 → Amb 4) (hV : ContDiff ℝ Ctop V)
    (hVs : HasCompactSupport V) : ℝ → Amb 4 → Amb 4 :=
  fun t x => (Classical.choose (exists_global_integralCurve hV hVs x)) t

theorem flowV_zero (V : Amb 4 → Amb 4) (hV : ContDiff ℝ Ctop V) (hVs : HasCompactSupport V)
    (x : Amb 4) : flowV V hV hVs 0 x = x :=
  (Classical.choose_spec (exists_global_integralCurve hV hVs x)).1

theorem flowV_deriv (V : Amb 4 → Amb 4) (hV : ContDiff ℝ Ctop V) (hVs : HasCompactSupport V)
    (x : Amb 4) : ∀ t, HasDerivAt (fun s => flowV V hV hVs s x) (V (flowV V hV hVs t x)) t :=
  (Classical.choose_spec (exists_global_integralCurve hV hVs x)).2

/-- **The flow property.**  The integral curves of `V` through the same point agree, so the global
flow is a group action of `ℝ`. -/
theorem flowV_add (V : Amb 4 → Amb 4) (hV : ContDiff ℝ Ctop V) (hVs : HasCompactSupport V)
    (s t : ℝ) (x : Amb 4) :
    flowV V hV hVs (s + t) x = flowV V hV hVs s (flowV V hV hVs t x) := by
  obtain ⟨L, hL⟩ := exists_lipschitzWith_of_contDiff_hasCompactSupport hV hVs
  have h1 : ∀ u : ℝ, HasDerivAt (fun v : ℝ => flowV V hV hVs (v + t) x)
      (V ((fun v : ℝ => flowV V hV hVs (v + t) x) u)) u := by
    intro u
    have h := (flowV_deriv V hV hVs x (u + t)).comp_add_const u
    simpa using h
  have h2 : ∀ u : ℝ, HasDerivAt (fun v : ℝ => flowV V hV hVs v (flowV V hV hVs t x))
      (V ((fun v : ℝ => flowV V hV hVs v (flowV V hV hVs t x)) u)) u := fun u =>
    flowV_deriv V hV hVs (flowV V hV hVs t x) u
  have heq : (fun u : ℝ => flowV V hV hVs (u + t) x) =
      (fun u : ℝ => flowV V hV hVs u (flowV V hV hVs t x)) :=
    integralCurve_unique hL h1 h2 (by rw [zero_add, flowV_zero])
  have := congrFun heq s
  simpa [zero_add] using this

/-! ## The local chart at a point of the intersection set -/

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-- **The tangential field does not vanish in the chart coordinate.**  At a point `x` of the
intersection set, `V x` is a non-zero kernel vector of the derivative of the charted difference map,
and if that derivative is surjective on the coordinate hyperplane `{v | v i = 0}`, then the `i`-th
component of `V x` is non-zero. -/
theorem vcoord_ne_zero_of_tangent {D : EuclideanSpace ℝ (Fin 2) → M}
    {N : EuclideanSpace ℝ (Fin 3) → M} {V : Amb 4 → Amb 4}
    {x : Amb 4} (hx : x ∈ chartRegion (D (sqPart x)) D N) (heq : D (sqPart x) = N (cbPart x))
    (hsurj : Function.Surjective (fderiv ℝ (chartDiff (D (sqPart x)) D N) x))
    (htan : fderiv ℝ (chartDiff (D (sqPart x)) D N) x (V x) = 0)
    (hne : V x ≠ 0) {i : Fin 5}
    (hsurj_i : Function.Surjective (fun v : {v : Amb 4 // v i = 0} =>
      fderiv ℝ (chartDiff (D (sqPart x)) D N) x v.1)) : V x i ≠ 0 :=
  kernel_coord_ne_zero hsurj htan hne hsurj_i

/-- **The local graph structure of the intersection set at a point of `K`.**  If the derivative of
the charted difference map at `x ∈ K` is surjective and also surjective on the coordinate hyperplane
`{v | v i = 0}`, then there is a `FlowChart` for `K = interSet D N` at `x` with coordinate `i` — the
graph of `Work.Drive.exists_local_graph`, shrunk so that the `i`-th component of `V` is bounded away
from zero on the chart region. -/
theorem exists_flowChart_at {D : EuclideanSpace ℝ (Fin 2) → M}
    {N : EuclideanSpace ℝ (Fin 3) → M} (hD : ContMDiff (𝓡 2) (𝓡 4) Ctop D)
    (hN : ContMDiff (𝓡 3) (𝓡 4) Ctop N) {V : Amb 4 → Amb 4} (hVcont : Continuous V)
    {x : Amb 4} (hx : x ∈ interSet D N)
    (hsurj : Function.Surjective (fderiv ℝ (chartDiff (D (sqPart x)) D N) x))
    (htan : fderiv ℝ (chartDiff (D (sqPart x)) D N) x (V x) = 0) (hne : V x ≠ 0)
    (i : Fin 5)
    (hsurj_i : Function.Surjective (fun v : {v : Amb 4 // v i = 0} =>
      fderiv ℝ (chartDiff (D (sqPart x)) D N) x v.1)) :
    ∃ C : FlowChart V (interSet D N) x, C.i = i ∧ x ∈ C.region := by
  obtain ⟨hbox, heq⟩ := hx
  have hxreg : x ∈ chartRegion (D (sqPart x)) D N := by
    rw [mem_chartRegion]
    exact ⟨mem_chart_source _ (D (sqPart x)), by rw [← heq]; exact mem_chart_source _ (D (sqPart x))⟩
  obtain ⟨δ, ρ, η, hδ, hρ, hηcd, hηi, hηx, hchar⟩ :=
    exists_local_graph (D (sqPart x)) D N hD hN hxreg heq i hsurj_i
  have hηc : Continuous η := hηcd.continuous
  have hVi : V x i ≠ 0 := kernel_coord_ne_zero hsurj htan hne hsurj_i
  have hVipos : 0 < |V x i| := abs_pos.mpr hVi
  -- a small ball on which the `i`-th component of `V` stays away from zero
  have hcont_i : Continuous fun y : Amb 4 => V y i :=
    (PiLp.continuous_apply 2 (fun _ : Fin 5 => ℝ) i).comp hVcont
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
  have hδsε : δs ≤ min εV 1 / 3 := by rw [hδsdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hδsη : δs ≤ εη := by rw [hδsdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρsε : ρs ≤ min εV 1 / 3 := by rw [hρsdef]; exact min_le_right _ _
  -- the region of the shrunk chart lies in the ball of radius `min εV 1` around `x`
  have hball : ∀ y : Amb 4, |y i - x i| < δs →
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
    have hsingle : ‖(y i - x i) • EuclideanSpace.single (i : Fin 5) (1 : ℝ)‖ = |y i - x i| := by
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
  have hgraphs : ∀ y : Amb 4, |y i - x i| < δs →
      ‖y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i)‖ < ρs → y ∈ interSet D N →
      y = (y i) • EuclideanSpace.single i (1 : ℝ) + η (y i) := by
    intro y h1 h2 hy
    obtain ⟨-, hiff⟩ := hchar y (lt_of_lt_of_le h1 hδsle) (lt_of_lt_of_le h2 hρsle)
    exact hiff.mp hy.2
  have hvels : ∀ y : Amb 4, |y i - x i| < δs →
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
  let C : FlowChart V (interSet D N) x :=
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

end Work.Drive

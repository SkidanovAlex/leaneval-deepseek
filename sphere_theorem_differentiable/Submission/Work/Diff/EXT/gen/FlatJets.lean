import Mathlib
import Submission.Work.Diff.EXT.gen_defs
import Submission.Work.Diff.EXT.jets_eq_of_t_derivs_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vanishing time Taylor coefficients imply vanishing jets (generic, local form)

`Work.Diff.EXT.jets_eq_flat_imp_jets_zero` (in
`Submission/Work/Diff/EXT/jets_eq_of_t_derivs_eq.lean`) shows that a *globally* smooth function
whose time Taylor coefficients vanish along the hyperplane over an open set has vanishing jets
there.  Here we localise it: it is enough that the function be smooth on an open neighbourhood of
the base point, and the flatness be assumed on an open set.  The reduction uses a bump function
(`ContDiffBump`) to globalise, which is why `FiniteDimensional ℝ E` is needed.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
open scoped ContDiff Topology
open Filter

namespace Work.Diff.EXT.gen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Locality of the iterated Fréchet derivative. -/
theorem iteratedFDeriv_congr_of_eventuallyEq {f g : ℝ × E → F} {p : ℝ × E}
    (h : f =ᶠ[nhds p] g) (k : ℕ) : iteratedFDeriv ℝ k f p = iteratedFDeriv ℝ k g p := by
  obtain ⟨W, hWsub, hWopen, hpW⟩ := mem_nhds_iff.mp h
  rw [← (iteratedFDerivWithin_of_isOpen k hWopen) hpW]
  rw [iteratedFDerivWithin_congr (s := W) (f₁ := f) (f := g) (fun y hy => hWsub hy) hpW k]
  exact (iteratedFDerivWithin_of_isOpen k hWopen) hpW

/-- **Vanishing time Taylor coefficients give vanishing jets** (local form). -/
theorem exists_forall_iteratedFDeriv_eq_zero_of_timeTaylor
    [FiniteDimensional ℝ E] [CompleteSpace F]
    {T : ℝ} {y₀ : E} {δ : ℝ × E → F} {V : Set (ℝ × E)} {U : Set E}
    (hV : IsOpen V) (hV₀ : (T, y₀) ∈ V) (hδ : ContDiffOn ℝ (⊤ : ℕ∞) δ V)
    (hU : IsOpen U) (hy₀ : y₀ ∈ U)
    (hflat : ∀ x ∈ U, ∀ i : ℕ, iteratedDeriv i (fun s : ℝ => δ (s, x)) T = 0) :
    ∀ᶠ x in nhds y₀, ∀ k : ℕ, iteratedFDeriv ℝ k δ (T, x) = 0 := by
  classical
  obtain ⟨ρ, hρ, hρV⟩ := Metric.isOpen_iff.mp hV (T, y₀) hV₀
  -- the bump function
  let χ : ContDiffBump (T, y₀) :=
    ContDiffBump.mk (c := (T, y₀)) (ρ / 4) (ρ / 2) (by linarith) (by linarith)
  have hrIn : χ.rIn = ρ / 4 := rfl
  have hrOut : χ.rOut = ρ / 2 := rfl
  have hχsmooth : ContDiff ℝ (⊤ : ℕ∞) (χ : ℝ × E → ℝ) := ContDiffBump.contDiff χ
  have hclV : Metric.closedBall (T, y₀) χ.rIn ⊆ V := by
    rw [hrIn]
    exact (Metric.closedBall_subset_ball (by linarith : ρ / 4 < ρ)).trans hρV
  have htsupp : tsupport (χ : ℝ × E → ℝ) ⊆ V := by
    have hsub : tsupport (χ : ℝ × E → ℝ) ⊆ Metric.closedBall (T, y₀) χ.rOut :=
      closure_minimal (fun q hq => by
        rw [Function.mem_support] at hq
        by_contra hc
        rw [Metric.mem_closedBall, not_le] at hc
        exact hq (ContDiffBump.zero_of_le_dist χ (x := q) (le_of_lt hc)))
        Metric.isClosed_closedBall
    have hball : Metric.closedBall (T, y₀) χ.rOut ⊆ V := by
      rw [hrOut]
      exact (Metric.closedBall_subset_ball (by linarith : ρ / 2 < ρ)).trans hρV
    exact hsub.trans hball
  -- the globalised function
  set δ' : ℝ × E → F := fun q => χ q • (if q ∈ V then δ q else 0) with hδ'def
  have hδ'val : ∀ q : ℝ × E, δ' q = χ q • (if q ∈ V then δ q else 0) := by
    intro q; rw [hδ'def]
  have hδ'smooth : ContDiff ℝ (⊤ : ℕ∞) δ' := by
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p ∈ V
    · have hev : δ' =ᶠ[nhds p] (fun q => χ q • δ q) := by
        filter_upwards [hV.mem_nhds hp] with q hq
        rw [hδ'val q, ite_eq_left hq]
      exact ((hχsmooth.contDiffAt).smul (hδ.contDiffAt (hV.mem_nhds hp))).congr_of_eventuallyEq
        hev
    · have hnot : p ∉ closure (Function.support (χ : ℝ × E → ℝ)) := fun hc => hp (htsupp hc)
      have hzero : ∀ᶠ q in nhds p, χ q = 0 := by
        filter_upwards [(isClosed_closure).isOpen_compl.mem_nhds hnot] with q hq
        by_contra h
        exact hq (subset_closure h)
      refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_
      filter_upwards [hzero] with q hq
      rw [hδ'val q, hq, zero_smul]
  -- the flatness of the globalised function, on a smaller open set
  let U' : Set E := U ∩ Metric.ball y₀ χ.rIn
  have hU'o : IsOpen U' := hU.inter Metric.isOpen_ball
  have hy₀U' : y₀ ∈ U' := by
    refine ⟨hy₀, ?_⟩
    rw [Metric.mem_ball]
    simpa using χ.rIn_pos
  have hclx : ∀ x ∈ U', ∀ᶠ s in nhds T, (s, x) ∈ Metric.closedBall (T, y₀) χ.rIn := by
    intro x hx
    have hxr : dist x y₀ < χ.rIn := by
      have := hx.2; rwa [Metric.mem_ball] at this
    filter_upwards [Metric.closedBall_mem_nhds T (by linarith : (0:ℝ) < χ.rIn - dist x y₀)]
      with s hs
    have h1 : dist (s, x) (T, x) ≤ χ.rIn - dist x y₀ := by
      rw [Prod.dist_eq]
      refine max_le ?_ ?_
      · rwa [Metric.mem_closedBall] at hs
      · rw [dist_self]
        linarith
    have h2 : dist (T, x) (T, y₀) = dist x y₀ := by
      rw [Prod.dist_eq, Real.dist_eq]
      simp
    calc dist (s, x) (T, y₀) ≤ dist (s, x) (T, x) + dist (T, x) (T, y₀) :=
          dist_triangle _ _ _
      _ ≤ (χ.rIn - dist x y₀) + dist x y₀ := by rw [h2]; exact add_le_add h1 le_rfl
      _ = χ.rIn := by ring
  have hδ'eq_of_ball : ∀ q ∈ Metric.ball (T, y₀) χ.rIn, δ' q = δ q := by
    intro q hq
    have hqcl : q ∈ Metric.closedBall (T, y₀) χ.rIn := Metric.ball_subset_closedBall hq
    rw [hδ'val q, ite_eq_left (hclV hqcl), ContDiffBump.one_of_mem_closedBall χ hqcl, one_smul]
  have hflat' : ∀ x ∈ U', ∀ i : ℕ, iteratedDeriv i (fun s : ℝ => δ' (s, x)) T = 0 := by
    intro x hx i
    have hev : (fun s : ℝ => δ' (s, x)) =ᶠ[nhds T] (fun s : ℝ => δ (s, x)) := by
      filter_upwards [hclx x hx] with s hs
      rw [hδ'val (s, x), ite_eq_left (hclV hs), ContDiffBump.one_of_mem_closedBall χ hs,
        one_smul]
    rw [hev.iteratedDeriv_eq, hflat x hx.1 i]
  have hjets' : ∀ x ∈ U', ∀ k : ℕ, iteratedFDeriv ℝ k δ' (T, x) = 0 :=
    Work.Diff.EXT.jets_eq_flat_imp_jets_zero hU'o δ' hδ'smooth hflat'
  -- transfer back to `δ`
  filter_upwards [hU'o.mem_nhds hy₀U'] with x hx
  intro k
  have hev : δ =ᶠ[nhds (T, x)] δ' := by
    have hxr : dist x y₀ < χ.rIn := by
      have := hx.2; rwa [Metric.mem_ball] at this
    have hmem : (T, x) ∈ Metric.ball (T, y₀) χ.rIn := by
      rw [Metric.mem_ball, Prod.dist_eq]
      refine max_lt ?_ hxr
      rw [Real.dist_eq]
      simpa using χ.rIn_pos
    filter_upwards [Metric.isOpen_ball.mem_nhds hmem] with q hq
    exact (hδ'eq_of_ball q hq).symm
  rw [iteratedFDeriv_congr_of_eventuallyEq hev k, hjets' x hx k]

end Work.Diff.EXT.gen

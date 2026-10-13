import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.CoreStep.GermDefs
import Submission.Work.WilE7.CoreStep.fiber_empty_of_good_of_vertical
import Submission.Work.WilE7.DimAPI.coordProj_fderiv_ker_eventually

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology

namespace Work.WilE7.Endgame

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreStep

/-! ## G2: the linear maps used in the endgame assembly

These are the map `Ae = (e-coordinate projection) ∘ π_n` (the coordinate projection that is
injective on the tangent base image) and the joint map `Av = (verT, Ae) : ℝ^{0+N} → ℝ^{K+1}` used
for the ball covering of the vertical stratum `T`. -/

/-- The vertical coordinate `verT` as a linear map. -/
def verTLin (n m : ℕ) : (Fin (0 + (n + (m + 1))) → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.proj (R := ℝ) (Fin.natAdd 0 (Fin.natAdd n (Fin.last m)))

theorem verTLin_apply {n m : ℕ} (v : Fin (0 + (n + (m + 1))) → ℝ) :
    verTLin n m v = verT v := rfl

/-- The `e`-coordinate projection `v ↦ (i ↦ v (e i))`, as a **linear** map (the underlying linear
map of `DimAPI.coordProjCLM`).  This is the form in which `exists_coordProj_surj_submodule`
produces its surjectivity statement. -/
def πLin {D K : ℕ} (e : Fin K ↪ Fin D) : (Fin D → ℝ) →ₗ[ℝ] (Fin K → ℝ) :=
  LinearMap.pi (fun i => (LinearMap.proj (e i)))

theorem πLin_eq_coordProjCLM {D K : ℕ} (e : Fin K ↪ Fin D) :
    πLin e = (Work.WilE7.DimAPI.coordProjCLM e).toLinearMap := rfl

theorem πLin_apply {D K : ℕ} (e : Fin K ↪ Fin D) (v : Fin D → ℝ) :
    πLin e v = fun i => v (e i) := by
  show (Work.WilE7.DimAPI.coordProjCLM e) v = fun i => v (e i)
  rw [Work.WilE7.DimAPI.coordProjCLM_apply]

/-- The `e`-coordinate projection composed with the base projection `π_n`. -/
def AeLin {n m K : ℕ} (e : Fin K ↪ Fin n) :
    (Fin (0 + (n + (m + 1))) → ℝ) →ₗ[ℝ] (Fin K → ℝ) :=
  (πLin e).comp (basePrLin n (m + 1))

theorem AeLin_eq_coordProjCLM {n m K : ℕ} (e : Fin K ↪ Fin n) :
    AeLin (n := n) (m := m) e =
      (Work.WilE7.DimAPI.coordProjCLM e).toLinearMap.comp (basePrLin n (m + 1)) := by
  rw [AeLin, πLin_eq_coordProjCLM]

theorem AeLin_apply {n m K : ℕ} (e : Fin K ↪ Fin n)
    (v : Fin (0 + (n + (m + 1))) → ℝ) :
    AeLin e v = fun i => basePrLin n (m + 1) v (e i) := by
  rw [AeLin, LinearMap.comp_apply, πLin_apply]

/-- The joint map `(verT, Ae) : ℝ^{0+N} → ℝ^{K+1}`, with the vertical coordinate in position `0`. -/
def AvLin {n m K : ℕ} (e : Fin K ↪ Fin n) :
    (Fin (0 + (n + (m + 1))) → ℝ) →ₗ[ℝ] (Fin (K + 1) → ℝ) :=
  LinearMap.pi (fun i : Fin (K + 1) =>
    Fin.cases (verTLin n m)
      (fun j : Fin K => (LinearMap.proj (e j)).comp (basePrLin n (m + 1))) i)

theorem AvLin_apply {n m K : ℕ} (e : Fin K ↪ Fin n)
    (v : Fin (0 + (n + (m + 1))) → ℝ) :
    AvLin e v = Fin.cons (verT v) (fun i => basePrLin n (m + 1) v (e i)) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rw [AvLin, LinearMap.pi_apply, Fin.cases_zero, Fin.cons_zero]
    exact verTLin_apply v
  · intro j
    rw [AvLin, LinearMap.pi_apply, Fin.cases_succ, Fin.cons_succ]
    rfl

/-! ## Elementary metric estimates used in the final assembly -/

/-- `projTop` of an absolute stratum point, in terms of the base projection and `verT`. -/
theorem projTop_absPt_snoc {n m : ℕ} (t : Fin (0 + (n + (m + 1))) → ℝ) :
    Work.WilE7.CoreStep.projTop n m (Work.WilE7.MainDesign.absPt t)
      = Fin.snoc (Work.WilE7.MainDesign.basePrLin n (m + 1) t) (Work.WilE7.CoreStep.verT t) := by
  have hL : Work.WilE7.CoreStep.projTop n m (Work.WilE7.MainDesign.absPt t)
      = Work.WilE7.CoreStep.projTopLin n m
        (Work.WilE7.CoreStep.absPtLin (n + (m + 1)) t) := by
    rw [Work.WilE7.CoreStep.projTopLin_apply, Work.WilE7.CoreStep.absPtLin_apply]
  rw [hL]
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [Fin.snoc_last]
    exact Work.WilE7.CoreStep.projTopLin_absPtLin_last t
  · intro j
    rw [Fin.snoc_castSucc]
    exact congrFun (Work.WilE7.CoreStep.projTopLin_absPtLin_init (n := n) (m := m) t) j

/-- Reassemble a function from its `Fin.init` and its last coordinate. -/
theorem snoc_init_self {n : ℕ} (f : Fin (n + 1) → ℝ) :
    Fin.snoc (Fin.init f) (f (Fin.last n)) = f := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [Fin.snoc_last]
  · intro j
    rw [Fin.snoc_castSucc]
    rfl

/-- The `e`-coordinate projection is `1`-Lipschitz on the sup norm. -/
theorem dist_coordProj_le {D K : ℕ} (e : Fin K ↪ Fin D) (x y : Fin D → ℝ) :
    dist (fun i : Fin K => x (e i)) (fun i : Fin K => y (e i)) ≤ dist x y := by
  refine (dist_pi_le_iff dist_nonneg).mpr fun i => ?_
  exact le_trans (dist_le_pi_dist x y (e i)) le_rfl

/-- `Fin.cons` is `1`-Lipschitz for the sup norm. -/
theorem dist_cons_le_max {K : ℕ} (a b : ℝ) (f g : Fin K → ℝ) :
    dist (@Fin.cons K (fun _ => ℝ) a f) (@Fin.cons K (fun _ => ℝ) b g)
      ≤ max (dist a b) (dist f g) := by
  have h : 0 ≤ max (dist a b) (dist f g) := le_trans dist_nonneg (le_max_left _ _)
  refine (dist_pi_le_iff h).mpr fun i => ?_
  refine Fin.cases ?_ ?_ i
  · rw [Fin.cons_zero, Fin.cons_zero]
    exact le_max_left _ _
  · intro j
    rw [Fin.cons_succ, Fin.cons_succ]
    exact le_trans (dist_le_pi_dist f g j) (le_max_right _ _)

/-- `Fin.init` is `1`-Lipschitz for the sup norm. -/
theorem dist_init_le {n : ℕ} (z z' : Fin (n + 1) → ℝ) :
    dist (Fin.init z) (Fin.init z') ≤ dist z z' := by
  refine (dist_pi_le_iff dist_nonneg).mpr fun i => ?_
  exact le_trans (dist_le_pi_dist z z' i.castSucc) le_rfl

/-- The last coordinate is `1`-Lipschitz for the sup norm. -/
theorem dist_last_le {n : ℕ} (z z' : Fin (n + 1) → ℝ) :
    dist (z (Fin.last n)) (z' (Fin.last n)) ≤ dist z z' :=
  dist_le_pi_dist z z' (Fin.last n)

end Work.WilE7.Endgame

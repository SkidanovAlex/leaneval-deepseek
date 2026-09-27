import Mathlib
import Submission.Work.OneDim.Defs
import Submission.Work.OneDim.real_interval_parametrization
import Submission.Work.OneDim.exists_maximal_arc_param

/-!
# Open arcs in a one-dimensional manifold

Self-contained notion of *open arc* in a smooth `1`-manifold: an open subset which is the image of an
injective local diffeomorphism `ℝ → C`.  Also: chart balls are open arcs.
-/

open scoped Manifold ContDiff Topology
open Set Function Filter

noncomputable section

namespace Work.OneDim

variable {C : Type*} [TopologicalSpace C] [ChartedSpace E1 C] [IsManifold I1 sm C]

/-- An **open arc** in `C`: the image of an injective global local diffeomorphism `ℝ → C`. -/
def IsArcSet (A : Set C) : Prop :=
  ∃ γ : ℝ → C, Function.Injective γ ∧
    IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) I1 sm γ ∧ A = Set.range γ

theorem IsArcSet.isOpen {A : Set C} (h : IsArcSet A) : IsOpen A := by
  obtain ⟨γ, -, hld, rfl⟩ := h
  exact hld.isOpen_range

theorem IsArcSet.nonempty {A : Set C} (h : IsArcSet A) : A.Nonempty := by
  obtain ⟨γ, -, -, rfl⟩ := h
  exact ⟨γ 0, Set.mem_range_self 0⟩

theorem IsArcSet.isPreconnected {A : Set C} (h : IsArcSet A) : IsPreconnected A := by
  obtain ⟨γ, -, hld, rfl⟩ := h
  rw [← Set.image_univ]
  exact isPreconnected_univ.image γ hld.contMDiff.continuous.continuousOn

/-- The unit vector `e₁ = (1,0,…,0)` of `E1`. -/
def e₁ : E1 := EuclideanSpace.single (𝕜 := ℝ) (0 : Fin 1) 1

lemma norm_e₁ : ‖e₁‖ = 1 := by
  rw [e₁, PiLp.norm_single]
  simp

lemma eq_smul_e₁ (x : E1) : x = (x 0) • e₁ := by
  ext i
  fin_cases i
  simp [e₁]

lemma norm_sub_eq_abs_coord (a b : E1) : ‖a - b‖ = |(a - b) 0| := by
  conv_lhs => rw [eq_smul_e₁ (a - b)]
  rw [norm_smul, norm_e₁, mul_one, Real.norm_eq_abs]

lemma sub_coord_smul_e₁ (c y : E1) : (y - c) 0 • e₁ = y - c := by
  rw [← eq_smul_e₁ (y - c)]

lemma norm_add_smul_e₁_sub (c : E1) (t : ℝ) : ‖c + t • e₁ - c‖ = |t| := by
  rw [add_sub_cancel_left, norm_smul, norm_e₁, mul_one, Real.norm_eq_abs]

lemma mem_ball_coord (c : E1) {r : ℝ} {y : E1} (hy : y ∈ Metric.ball c r) :
    (y - c) 0 ∈ Metric.ball (0:ℝ) r := by
  rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, sub_zero]
  have h := Metric.mem_ball.mp hy
  rw [dist_eq_norm, norm_sub_eq_abs_coord] at h
  exact h

/-- The affine line parametrisation `t ↦ c + t • e₁` in `E1`, as a partial diffeomorphism. -/
def pdiffLine (c : E1) :
    PartialDiffeomorph (modelWithCornersSelf ℝ ℝ) I1 ℝ E1 sm where
  toPartialEquiv :=
    { toFun := fun t : ℝ => c + t • e₁
      invFun := fun y : E1 => (y - c) 0
      source := univ
      target := univ
      map_source' := fun t _ => mem_univ _
      map_target' := fun y _ => mem_univ _
      left_inv' := fun t _ => by
        show ((c + t • e₁) - c) 0 = t
        rw [add_sub_cancel_left]
        simp [e₁]
      right_inv' := fun y _ => by
        show c + ((y - c) 0) • e₁ = y
        rw [sub_coord_smul_e₁, add_sub_cancel] }
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := by
    rw [contMDiffOn_univ, contMDiff_iff_contDiff]
    fun_prop
  contMDiffOn_invFun := by
    rw [contMDiffOn_univ, contMDiff_iff_contDiff]
    fun_prop

lemma isLocalDiffeomorphAt_line (c : E1) (t : ℝ) :
    IsLocalDiffeomorphAt (modelWithCornersSelf ℝ ℝ) I1 sm (fun s : ℝ => c + s • e₁) t :=
  PartialDiffeomorph.isLocalDiffeomorphAt _ _ _ (pdiffLine c) (mem_univ t)

set_option maxHeartbeats 1000000 in
/-- **A chart ball in a one-manifold is an open arc.** -/
theorem isArcSet_ball (p : C) (r : ℝ) (hr : 0 < r)
    (hsub : Metric.closedBall ((chartAt E1 p) p) r ⊆ (chartAt E1 p).target) :
    IsArcSet ((chartAt E1 p).symm '' Metric.ball ((chartAt E1 p) p) r) := by
  classical
  set φ := chartAt E1 p with hφ
  obtain ⟨ρ, hρinj, hρrange, hρld⟩ :=
    real_interval_parametrization (s := Metric.ball (0:ℝ) r) Metric.isOpen_ball
      (convex_ball 0 r).isPreconnected ⟨0, Metric.mem_ball_self hr⟩
  have hρmem : ∀ t : ℝ, ρ t ∈ Metric.ball (0:ℝ) r := by
    intro t; rw [← hρrange]; exact ⟨t, rfl⟩
  have hρabs : ∀ t : ℝ, |ρ t| < r := by
    intro t
    have h := Metric.mem_ball.mp (hρmem t)
    rwa [dist_eq_norm, Real.norm_eq_abs, sub_zero] at h
  have hmem_target : ∀ t : ℝ, φ p + ρ t • e₁ ∈ φ.target := by
    intro t
    refine hsub (Metric.ball_subset_closedBall ?_)
    rw [Metric.mem_ball, dist_eq_norm, norm_add_smul_e₁_sub]
    exact hρabs t
  have hval : ∀ t : ℝ, φ (φ.symm (φ p + ρ t • e₁)) = φ p + ρ t • e₁ := by
    intro t; exact φ.right_inv (hmem_target t)
  refine ⟨fun t : ℝ => φ.symm (φ p + ρ t • e₁), ?_, ?_, ?_⟩
  · intro a b hab
    have h1 : φ p + ρ a • e₁ = φ p + ρ b • e₁ := by
      have := congrArg φ hab
      simpa [hval a, hval b] using this
    have h2 : ρ a = ρ b := by
      have := congrArg (fun y : E1 => (y - φ p) 0) h1
      simpa [add_sub_cancel_left, e₁] using this
    exact hρinj h2
  · intro t
    have hinner : IsLocalDiffeomorphAt (modelWithCornersSelf ℝ ℝ) I1 sm
        (fun t : ℝ => φ p + ρ t • e₁) t :=
      IsLocalDiffeomorphAt.comp (K := I1) (P := E1) (hρld t)
        (isLocalDiffeomorphAt_line (φ p) (ρ t))
    have hsymm : IsLocalDiffeomorphAt I1 I1 sm φ.symm (φ p + ρ t • e₁) := by
      have htgt : φ p + ρ t • e₁ ∈ (pdiffChart p).target := by
        show φ p + ρ t • e₁ ∈ (chartAt E1 p).target
        exact hmem_target t
      show IsLocalDiffeomorphAt I1 I1 sm (chartAt E1 p).symm _
      exact PartialDiffeomorph.isLocalDiffeomorphAt _ _ _ (pdiffChart p).symm
        (x := φ p + ρ t • e₁) htgt
    show IsLocalDiffeomorphAt (modelWithCornersSelf ℝ ℝ) I1 sm
      (fun t : ℝ => φ.symm (φ p + ρ t • e₁)) t
    exact IsLocalDiffeomorphAt.comp (K := I1) (P := C) hinner hsymm
  · ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hc : (w - φ p) 0 ∈ Set.range ρ := by
        rw [hρrange]; exact mem_ball_coord (φ p) hw
      obtain ⟨t, ht⟩ := hc
      refine ⟨t, ?_⟩
      show φ.symm (φ p + ρ t • e₁) = φ.symm w
      rw [ht, sub_coord_smul_e₁, add_sub_cancel]
    · rintro ⟨t, rfl⟩
      refine ⟨φ p + ρ t • e₁, ?_, rfl⟩
      rw [Metric.mem_ball, dist_eq_norm, norm_add_smul_e₁_sub]
      exact hρabs t

/-! ## Chart balls -/

/-- The chart ball of radius `r` around `p`. -/
def chartBall (p : C) (r : ℝ) : Set C :=
  (chartAt E1 p).symm '' Metric.ball ((chartAt E1 p) p) r

lemma isArcSet_chartBall (p : C) (r : ℝ) (hr : 0 < r)
    (hsub : Metric.closedBall ((chartAt E1 p) p) r ⊆ (chartAt E1 p).target) :
    IsArcSet (chartBall p r) :=
  isArcSet_ball p r hr hsub

lemma mem_chartBall {p : C} {r : ℝ}
    (hsub : Metric.ball ((chartAt E1 p) p) r ⊆ (chartAt E1 p).target) {x : C} :
    x ∈ chartBall p r ↔ x ∈ (chartAt E1 p).source ∧
      (chartAt E1 p) x ∈ Metric.ball ((chartAt E1 p) p) r := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(chartAt E1 p).map_target (hsub hy),
      by rw [(chartAt E1 p).right_inv (hsub hy)]; exact hy⟩
  · rintro ⟨hx, hxball⟩
    exact ⟨(chartAt E1 p) x, hxball, (chartAt E1 p).left_inv hx⟩

lemma chartBall_subset_chartBall {p : C} {r r' : ℝ} (h : r ≤ r') :
    chartBall p r ⊆ chartBall p r' :=
  image_mono (Metric.ball_subset_ball h)

lemma mem_chartBall_self (p : C) {r : ℝ} (hr : 0 < r) : p ∈ chartBall p r :=
  ⟨(chartAt E1 p) p, Metric.mem_ball_self hr, (chartAt E1 p).left_inv (mem_chart_source E1 p)⟩

/-- If a point lies in every sufficiently small chart ball around `p`, then it is `p`. -/
lemma eq_of_forall_mem_chartBall {p : C} {x : C} {R : ℝ} (hR : 0 < R)
    (hsub : Metric.closedBall ((chartAt E1 p) p) R ⊆ (chartAt E1 p).target)
    (h : ∀ r, 0 < r → r ≤ R → x ∈ chartBall p r) : x = p := by
  have hballr : ∀ r : ℝ, 0 < r → r ≤ R →
      Metric.ball ((chartAt E1 p) p) r ⊆ (chartAt E1 p).target :=
    fun r _ hrR => (Metric.ball_subset_ball hrR).trans
      (Metric.ball_subset_closedBall.trans hsub)
  have hxsrc : x ∈ (chartAt E1 p).source :=
    ((mem_chartBall (hballr R hR le_rfl)).mp (h R hR le_rfl)).1
  have hdist : dist ((chartAt E1 p) x) ((chartAt E1 p) p) = 0 := by
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) dist_nonneg
    have hε2 : 0 < min (ε/2) (R/2) := lt_min (by linarith) (by linarith)
    have hle : min (ε/2) (R/2) ≤ R := by
      linarith [min_le_right (ε/2) (R/2), hR]
    have hmem := h (min (ε/2) (R/2)) hε2 hle
    have hlt := ((mem_chartBall (hballr _ hε2 hle)).mp hmem).2
    rw [Metric.mem_ball] at hlt
    linarith [min_le_left (ε/2) (R/2)]
  have hφ : (chartAt E1 p) x = (chartAt E1 p) p := dist_eq_zero.mp hdist
  rw [← (chartAt E1 p).left_inv hxsrc, hφ, (chartAt E1 p).left_inv (mem_chart_source E1 p)]

end Work.OneDim

end

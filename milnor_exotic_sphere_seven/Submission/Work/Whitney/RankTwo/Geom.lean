import Mathlib
import Submission.Work.Whitney.TCMProdDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-!
# The explicit cycle for `Work.Whitney.tcmProd_rankOne_one`

This module builds the explicit geometric data used to evaluate both sides of the `(1,1)` case of
the model product formula on one cycle: the unit vector `u2 θ` of `ℝ²`, the six arcs of the
inscribed hexagon on the unit circle (angles `k·π/3`, `k = 0..6`), the cone sectors over them (with
apex the origin) and the radial segments, all inside the coordinate space
`X = tcmX Y 1 1 = Y × (ℝ¹ × ℝ¹)`.

The faces of the sector `S_k` are
* `δ 0 S_k = arc k` (the arc of the unit circle),
* `δ 1 S_k = rad (k+1)` (the radial segment to the `(k+1)`-st vertex),
* `δ 2 S_k = rad k` (the radial segment to the `k`-th vertex),
so the radial terms telescope and the boundary of `Z = Σ_k S_k` is the cycle `c = Σ_k arc k`.
-/

namespace Work.Whitney.RankTwo

open Work.Thom
open CategoryTheory AlgebraicTopology
open scoped Simplicial

noncomputable section

/-! ## The unit circle in `ℝ²` -/

/-- The unit vector of `ℝ²` at angle `θ`. -/
def u2 (θ : ℝ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![Real.cos θ, Real.sin θ]

@[simp] theorem u2_ofLp (θ : ℝ) : (u2 θ).ofLp = ![Real.cos θ, Real.sin θ] := rfl
@[simp] theorem u2_apply_zero (θ : ℝ) : (u2 θ).ofLp 0 = Real.cos θ := rfl
@[simp] theorem u2_apply_one (θ : ℝ) : (u2 θ).ofLp 1 = Real.sin θ := rfl

theorem norm_u2 (θ : ℝ) : ‖u2 θ‖ = 1 := by
  have h : ‖u2 θ‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
    simp only [Fin.sum_univ_two, u2, WithLp.ofLp_toLp, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, Real.cos_sq_add_sin_sq]
  nlinarith [norm_nonneg (u2 θ)]

theorem continuous_u2 : Continuous u2 := by unfold u2; fun_prop

/-- **The polar scaling map is continuous**: `(φ, r) ↦ r • u2 (φ / r)` extends continuously to
`r = 0` by `0` (Lean's convention `φ / 0 = 0` gives exactly that value). -/
theorem continuous_scale_u2 : Continuous fun p : ℝ × ℝ => p.2 • u2 (p.1 / p.2) := by
  have hcont : Continuous fun q : ℝ × ℝ => q.2 • u2 q.1 :=
    continuous_snd.smul (continuous_u2.comp continuous_fst)
  rw [continuous_iff_continuousAt]
  rintro ⟨a, b⟩
  by_cases hb : b = 0
  · subst hb
    rw [ContinuousAt, Metric.tendsto_nhds]
    simp only [zero_smul]
    intro ε hε
    filter_upwards [Metric.ball_mem_nhds (a, 0) hε] with p hp
    rw [dist_zero_right, norm_smul, norm_u2, mul_one, Real.norm_eq_abs]
    have h2 : |p.2| ≤ ‖p - (a, 0)‖ := by
      have h := norm_snd_le (p - (a, 0))
      rw [Real.norm_eq_abs] at h
      simpa using h
    calc |p.2| ≤ ‖p - (a, 0)‖ := h2
      _ = dist p (a, 0) := (dist_eq_norm _ _).symm
      _ < ε := hp
  · have hc : ContinuousAt (fun p : ℝ × ℝ => (p.1 / p.2, p.2)) (a, b) :=
      (continuousAt_fst.div continuousAt_snd (by simpa using hb)).prodMk continuousAt_snd
    exact hcont.continuousAt.comp hc

/-! ## The six angles -/

/-- The angles of the inscribed hexagon: `ang k = k·π/3`. -/
def ang (k : ℕ) : ℝ := k * Real.pi / 3

theorem ang_zero : ang 0 = 0 := by simp [ang]
theorem ang_one : ang 1 = Real.pi / 3 := by simp [ang]
theorem ang_two : ang 2 = 2 * Real.pi / 3 := by simp [ang]
theorem ang_three : ang 3 = Real.pi := by simp [ang]
theorem ang_four : ang 4 = 4 * Real.pi / 3 := by simp [ang]
theorem ang_five : ang 5 = 5 * Real.pi / 3 := by simp [ang]
theorem ang_six : ang 6 = 2 * Real.pi := by simp [ang]; ring

/-! ## The coordinate space and its singular simplicial set -/

variable (Y : Type) [TopologicalSpace Y]

/-- The coordinate space of the `(1,1)` model product formula. -/
abbrev X : Type := tcmX Y 1 1

/-- The singular simplicial set of `X`. -/
abbrev ssX : SSet := TopCat.toSSet.obj (TopCat.of (X Y))

/-- The singular-simplex equivalence, spelled once. -/
abbrev sEquiv (n : ℕ) :
    (ssX Y) _⦋n⦌ ≃ C(stdSimplex ℝ (Fin (n + 1)), TopCat.of (X Y)) :=
  TopCat.toSSetObjEquivOld (TopCat.of (X Y)) (Opposite.op (SimplexCategory.mk n))

theorem sEquiv_apply (n : ℕ) (a : (ssX Y) _⦋n⦌) :
    (sEquiv Y n) a = (TopCat.toSSetObjEquivOld (TopCat.of (X Y))
      (Opposite.op (SimplexCategory.mk n))) a := rfl

/-- **Extensionality for simplices** of the singular simplicial set of `X`. -/
theorem ssX_ext {n : ℕ} {a b : (ssX Y) _⦋n⦌}
    (h : ∀ z : stdSimplex ℝ (Fin (n + 1)), (sEquiv Y n) a z = (sEquiv Y n) b z) : a = b :=
  (sEquiv Y n).injective (ContinuousMap.ext h)

/-- The face computation for simplices of `X`. -/
theorem ssX_δ_apply {n : ℕ} (x : (ssX Y) _⦋n + 1⦌) (i : Fin (n + 2))
    (z : stdSimplex ℝ (Fin (n + 1))) :
    (sEquiv Y n) ((ssX Y).δ i x) z = (sEquiv Y (n + 1)) x (stdSimplex.map i.succAbove z) :=
  TopCat.toSSetObjEquivOld_δ_apply x i z

/-! ## The vertices, arcs, radial segments and sectors -/

/-- The point of the fibre of `X` at "angle numerator `φ` and radius `r`":
`(tcmSumLin)⁻¹ (r • u2 (φ/r))`.  The angle is the normalized combination of the two endpoint
angles; the continuity at `r = 0` is `Work.Whitney.RankTwo.continuous_scale_u2`. -/
def fibCone (φ r : ℝ) : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) :=
  (tcmSumLin 1 1).symm (r • u2 (φ / r))

/-- The cone map as a function of a pair (the lambda-free form is the one on which
`Continuous.comp` elaborates without unfolding `fibCone`). -/
def fibConeP (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) :=
  fibCone p.1 p.2

theorem continuous_fibConeP : Continuous fibConeP :=
  (tcmSumLin 1 1).symm.continuous.comp continuous_scale_u2

/-- The `k`-th vertex of the hexagon. -/
def vtx (y : Y) (k : ℕ) : X Y := (y, fibCone (ang k) 1)

/-- The coordinate function `q ↦ q i` on the standard simplex. -/
def coord (n : ℕ) (i : Fin n) : C(stdSimplex ℝ (Fin n), ℝ) :=
  ⟨fun q => q i, (continuous_apply i).comp continuous_subtype_val⟩

@[simp] theorem coord_apply (n : ℕ) (i : Fin n) (q : stdSimplex ℝ (Fin n)) :
    coord n i q = q i := rfl

/-- The cone map as a bundled continuous map. -/
def fibConeCM : C(ℝ × ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) :=
  ⟨fibConeP, continuous_fibConeP⟩

@[simp] theorem fibConeCM_apply (p : ℝ × ℝ) : fibConeCM p = fibConeP p := rfl

/-- The `k`-th arc of the hexagon, as a continuous map out of `Δ¹`. -/
def arcC (y : Y) (k : ℕ) : C(stdSimplex ℝ (Fin 2), TopCat.of (X Y)) :=
  (ContinuousMap.const _ y).prodMk (fibConeCM.comp
    (((ContinuousMap.const _ (ang k)) * (coord 2 0)
      + (ContinuousMap.const _ (ang (k + 1))) * (coord 2 1)).prodMk
        (ContinuousMap.const _ 1)))

/-- The `k`-th radial segment, as a continuous map out of `Δ¹`. -/
def radC (y : Y) (k : ℕ) : C(stdSimplex ℝ (Fin 2), TopCat.of (X Y)) :=
  (ContinuousMap.const _ y).prodMk (fibConeCM.comp
    (((coord 2 1) * (ContinuousMap.const _ (ang k))).prodMk (coord 2 1)))

/-- The `k`-th sector: the cone over the `k`-th arc with apex the origin. -/
def secC (y : Y) (k : ℕ) : C(stdSimplex ℝ (Fin 3), TopCat.of (X Y)) :=
  (ContinuousMap.const _ y).prodMk (fibConeCM.comp
    (((ContinuousMap.const _ (ang k)) * (coord 3 1)
      + (ContinuousMap.const _ (ang (k + 1))) * (coord 3 2)).prodMk
        ((coord 3 1) + (coord 3 2))))

/-- The simplices of the arc. -/
def arcSimp (y : Y) (k : ℕ) : (ssX Y) _⦋1⦌ := (sEquiv Y 1).symm (arcC Y y k)

/-- The simplices of the radial segment. -/
def radSimp (y : Y) (k : ℕ) : (ssX Y) _⦋1⦌ := (sEquiv Y 1).symm (radC Y y k)

/-- The simplices of the sector. -/
def secSimp (y : Y) (k : ℕ) : (ssX Y) _⦋2⦌ := (sEquiv Y 2).symm (secC Y y k)

@[simp] theorem sEquiv_arcSimp (y : Y) (k : ℕ) : sEquiv Y 1 (arcSimp Y y k) = arcC Y y k :=
  (sEquiv Y 1).apply_symm_apply _

@[simp] theorem sEquiv_radSimp (y : Y) (k : ℕ) : sEquiv Y 1 (radSimp Y y k) = radC Y y k :=
  (sEquiv Y 1).apply_symm_apply _

@[simp] theorem sEquiv_secSimp (y : Y) (k : ℕ) : sEquiv Y 2 (secSimp Y y k) = secC Y y k :=
  (sEquiv Y 2).apply_symm_apply _

end

end Work.Whitney.RankTwo

namespace Work.Whitney.RankTwo

open Work.Thom
open CategoryTheory AlgebraicTopology
open scoped Simplicial

noncomputable section

/-! ## Coordinates of the splitting `tcmSumLin 1 1` -/

/-- The vector `1` of `ℝ¹`, written once. -/
abbrev one1 : EuclideanSpace ℝ (Fin 1) := (Work.Cohomology.s0N : EuclideanSpace ℝ (Fin 1))

theorem one1_ofLp_zero : one1.ofLp 0 = 1 := rfl

/-- **Coordinate formula for the splitting**: the first block of `tcmSumLin 1 1`. -/
theorem tcmSumLin_apply_ofLp_zero (x : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) :
    (tcmSumLin 1 1 x).ofLp 0 = (x.1).ofLp 0 := by
  have h := Work.Thom.finAddEquivProd_symm_apply_inl (𝕜 := ℝ) (n := 1) (m := 1) x.1 x.2
    (0 : Fin 1)
  rw [finSumFinEquiv_apply_left] at h
  exact h

/-- **Coordinate formula for the splitting**: the second block of `tcmSumLin 1 1`. -/
theorem tcmSumLin_apply_ofLp_one (x : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) :
    (tcmSumLin 1 1 x).ofLp 1 = (x.2).ofLp 0 := by
  have h := Work.Thom.finAddEquivProd_symm_apply_inr (𝕜 := ℝ) (n := 1) (m := 1) x.1 x.2
    (0 : Fin 1)
  rw [finSumFinEquiv_apply_right] at h
  exact h

/-- The first block of the inverse splitting is `u.ofLp 0 • 1`. -/
theorem tcmSumLin_symm_fst (u : EuclideanSpace ℝ (Fin 2)) :
    ((tcmSumLin 1 1).symm u).1 = u.ofLp 0 • one1 := by
  have h : ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1) u).1).ofLp 0
      = u.ofLp 0 := by
    have h0 := Work.Thom.finAddEquivProd_fst (𝕜 := ℝ) (n := 1) (m := 1) u (0 : Fin 1)
    rw [finSumFinEquiv_apply_left] at h0
    exact h0
  apply WithLp.ofLp_injective 2
  funext j
  fin_cases j
  show ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1) u).1).ofLp 0
    = (u.ofLp 0 • one1).ofLp 0
  rw [WithLp.ofLp_smul, one1, Work.Cohomology.s0N, WithLp.ofLp_toLp, Pi.smul_apply,
    smul_eq_mul, mul_one]
  exact h

/-- The second block of the inverse splitting is `u.ofLp 1 • 1`. -/
theorem tcmSumLin_symm_snd (u : EuclideanSpace ℝ (Fin 2)) :
    ((tcmSumLin 1 1).symm u).2 = u.ofLp 1 • one1 := by
  have h : ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1) u).2).ofLp 0
      = u.ofLp 1 := by
    have h0 := Work.Thom.finAddEquivProd_snd (𝕜 := ℝ) (n := 1) (m := 1) u (0 : Fin 1)
    rw [finSumFinEquiv_apply_right] at h0
    exact h0
  apply WithLp.ofLp_injective 2
  funext j
  fin_cases j
  show ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1) u).2).ofLp 0
    = (u.ofLp 1 • one1).ofLp 0
  rw [WithLp.ofLp_smul, one1, Work.Cohomology.s0N, WithLp.ofLp_toLp, Pi.smul_apply,
    smul_eq_mul, mul_one]
  exact h

end

end Work.Whitney.RankTwo

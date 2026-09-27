import Mathlib
import Submission.Work.Mostow.BdExt.Basic
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.poBdAlg
import Submission.Work.Mostow.BusemannRay
import Submission.Work.Mostow.BdExt.lawCosines

/-!
# `isomRayCompare`: an isometry moves a ray to within bounded distance of the ray

For a boundary point `ξ ∈ Sph n` the geodesic ray issued from the base point `0` towards `ξ` is
`ray ξ t = sinh t • ξ` (`BdExt.Basic`), parametrised by hyperbolic arclength.  Under an isometry
`g : PO n 1` it is carried to the ray issued from `g • 0` towards `bd g ξ`.  The classical fact
that two geodesic rays with the same endpoint in the visual boundary stay at bounded distance is
what `BoundaryExt` (the Morse lemma, area C4) needs; here it is proved by explicit computation in
the hyperboloid chart.

The computation is two-fold.

* *The rays are explicit.*  With `A := rep g`, `z := mat A *ᵥ hlift 0`, `θ ξ = (ξ,1)`, the lift of
  the hyperboloid point over `actO A (ray ξ t)` is
  `sinh t • (tsign A • (mat A *ᵥ θ ξ)) + exp (-t) • (tsign A • z)`; since
  `tsign A • (mat A *ᵥ θ ξ) = c • θ (bdO A ξ)` with `c := tsign A * ((mat A *ᵥ θ ξ) (inr 0))`
  (`smul_theta_of_time_ne_zero`) and `tsign A • z = hlift (actO A 0)` (`hlift_actO`), this gives
  `actO A (ray ξ t) = (c * sinh t) • bdO A ξ + exp (-t) • (actO A 0)` in the chart.

* *The bound.*  Writing `cz := tpart (actO A 0)`, `a := ⟪actO A 0, bdO A ξ⟫`, the identity
  `tpart² = 1 + ‖·‖²` at `t = 1` gives the relation `c * (cz - a) = 1`, and then
  `cosh (hdist (actO A (ray ξ t)) (ray (bdO A ξ) t)) = exp (-t) * (cz * cosh t + sinh t * (c - a))
  ≤ cz = cosh (hdist 0 (actO A 0))`, so the distance never exceeds `hdist 0 (g • 0)`.
-/

namespace Work.Mostow.BdExt

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

/-- The scalar `c` attached to a pair `(A, ξ)`: the (positive) factor by which `A` scales the null
vector `θ ξ = (ξ,1)` in the direction of the boundary point `bdO A ξ`. -/
def cpar (A : O1 n) (ξ : E n) : ℝ :=
  tsign A * ((mat A) *ᵥ Work.Mostow.theta ξ) (Sum.inr 0)

/-- The chart identity `‖a • x + b • y‖² = a²‖x‖² + 2ab⟪x,y⟫ + b²‖y‖²`. -/
lemma norm_smul_add_sq (a b : ℝ) (x y : E n) :
    ‖a • x + b • y‖ ^ 2 = a ^ 2 * ‖x‖ ^ 2 + 2 * a * b * inner ℝ x y + b ^ 2 * ‖y‖ ^ 2 := by
  rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
    Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
  ring

/-! ## Lifting rays to the hyperboloid -/

/-- The lift of a point of the ray from the origin towards `ξ`. -/
lemma hlift_ray (ξ : E n) (t : ℝ) (hξ : ξ ∈ Sph n) :
    hlift (ray ξ t) = Real.sinh t • Work.Mostow.theta ξ + Real.exp (-t) • hlift (0 : E n) := by
  have hξn : ‖ξ‖ = 1 := (Work.Mostow.mem_Sph_iff ξ).mp hξ
  have htime : tpart (Real.sinh t • ξ) = Real.cosh t :=
    Work.Mostow.tpart_sinh_smul ξ t hξn
  funext j
  rcases j with i | ⟨k⟩
  · simp [Submission.Mostow.hlift, Work.Mostow.theta, Work.Mostow.BdExt.ray]
  · simp only [Submission.Mostow.hlift, Work.Mostow.theta, Work.Mostow.BdExt.ray,
      Sum.elim_inr, Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_one]
    rw [htime, tpart, norm_zero, sq, mul_zero, add_zero, Real.sqrt_one, mul_one,
      Real.cosh_eq, Real.sinh_eq]
    ring

/-- The null vector `mat A *ᵥ θ ξ` is a multiple of `θ (bdO A ξ)`; `tsign A` corrects the sign. -/
lemma tsign_theta_eq (A : O1 n) (ξ : E n) (hξ : ξ ∈ Sph n) :
    tsign A • ((mat A) *ᵥ Work.Mostow.theta ξ) = cpar A ξ • Work.Mostow.theta (bdO A ξ) := by
  have hne : ((mat A) *ᵥ Work.Mostow.theta ξ) (Sum.inr 0) ≠ 0 :=
    Work.Mostow.mat_mulVec_theta_ne_zero A hξ
  have hW : (mat A) *ᵥ Work.Mostow.theta ξ =
      ((mat A) *ᵥ Work.Mostow.theta ξ) (Sum.inr 0) • Work.Mostow.theta (bdO A ξ) :=
    Work.Mostow.smul_theta_of_time_ne_zero ((mat A) *ᵥ Work.Mostow.theta ξ) hne
  rw [hW, smul_smul]
  rfl

/-- The lift of the isometric image of a ray: the two terms of `hlift_ray` are moved by `A`. -/
lemma hlift_actO_ray (A : O1 n) (ξ : E n) (t : ℝ) (hξ : ξ ∈ Sph n) :
    hlift (actO A (ray ξ t)) =
      Real.sinh t • (cpar A ξ • Work.Mostow.theta (bdO A ξ)) +
        Real.exp (-t) • hlift (actO A 0) := by
  have hA1 : tsign A • (Real.sinh t • ((mat A) *ᵥ Work.Mostow.theta ξ)) =
      Real.sinh t • (cpar A ξ • Work.Mostow.theta (bdO A ξ)) := by
    rw [smul_smul, mul_comm (tsign A) (Real.sinh t), ← smul_smul, tsign_theta_eq A ξ hξ]
  have hA2 : tsign A • (Real.exp (-t) • ((mat A) *ᵥ hlift (0 : E n))) =
      Real.exp (-t) • hlift (actO A 0) := by
    rw [smul_smul, mul_comm (tsign A) (Real.exp (-t)), ← smul_smul,
      ← Submission.Mostow.Hyper.hlift_actO A (0 : E n)]
  rw [Submission.Mostow.Hyper.hlift_actO A (ray ξ t), hlift_ray ξ t hξ, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_smul, smul_add, hA1, hA2]

/-- The isometric image of the ray, as a point of the chart: a ray issued from `actO A 0`. -/
lemma actO_ray_chart (A : O1 n) (ξ : E n) (t : ℝ) (hξ : ξ ∈ Sph n) :
    actO A (ray ξ t) = (cpar A ξ * Real.sinh t) • bdO A ξ + Real.exp (-t) • actO A 0 := by
  have h := congrArg Submission.Mostow.Hyper.spat (hlift_actO_ray A ξ t hξ)
  rw [Submission.Mostow.Hyper.spat_hlift] at h
  rw [h]
  apply PiLp.ext
  intro i
  simp only [Submission.Mostow.Hyper.spat, PiLp.toLp_apply, PiLp.add_apply, PiLp.smul_apply,
    Pi.add_apply, Pi.smul_apply, Sum.elim_inl, Work.Mostow.theta, Submission.Mostow.hlift,
    smul_eq_mul]
  ring

/-- The time coordinate (hyperbolic level data) of the isometric image of the ray. -/
lemma tpart_actO_ray (A : O1 n) (ξ : E n) (t : ℝ) (hξ : ξ ∈ Sph n) :
    tpart (actO A (ray ξ t)) =
      cpar A ξ * Real.sinh t + Real.exp (-t) * tpart (actO A 0) := by
  have h := congrArg (fun y : Fin n ⊕ Fin 1 → ℝ => y (Sum.inr 0)) (hlift_actO_ray A ξ t hξ)
  simp only [Submission.Mostow.hlift, Sum.elim_inr, Pi.add_apply, Pi.smul_apply,
    Work.Mostow.theta, smul_eq_mul, mul_one] at h
  rw [h]
  ring

/-! ## The relation `c * (cz - a) = 1` -/

/-- The key relation between the scaling factor `cpar A ξ`, the level `tpart (actO A 0)` and the
inner product `⟪actO A 0, bdO A ξ⟫`: it expresses that the ray `s ↦ actO A (ray ξ s)` starts at
`actO A 0` with unit speed, and follows from `tpart² = 1 + ‖·‖²` at `t = 1`. -/
lemma cpar_rel (A : O1 n) (ξ : E n) (hξ : ξ ∈ Sph n) :
    cpar A ξ * (tpart (actO A 0) - inner ℝ (actO A 0) (bdO A ξ)) = 1 := by
  have hξ'n : ‖bdO A ξ‖ = 1 :=
    (Work.Mostow.mem_Sph_iff _).mp ((Work.Mostow.poBdAlg n).1 A ξ hξ)
  have hnorm : ‖actO A (ray ξ 1)‖ ^ 2 =
      (cpar A ξ * Real.sinh 1) ^ 2 +
        2 * (cpar A ξ * Real.sinh 1) * Real.exp (-1) * inner ℝ (actO A 0) (bdO A ξ) +
        Real.exp (-1) ^ 2 * ‖actO A 0‖ ^ 2 := by
    rw [actO_ray_chart A ξ 1 hξ, norm_smul_add_sq (cpar A ξ * Real.sinh 1) (Real.exp (-1))
      (bdO A ξ) (actO A 0), hξ'n, one_pow, mul_one, real_inner_comm (bdO A ξ) (actO A 0)]
  have hrel : 2 * (cpar A ξ * Real.sinh 1) * Real.exp (-1) *
      (tpart (actO A 0) - inner ℝ (actO A 0) (bdO A ξ)) = 1 - Real.exp (-1) ^ 2 := by
    have h1 : tpart (actO A (ray ξ 1)) ^ 2 = 1 + ‖actO A (ray ξ 1)‖ ^ 2 :=
      Submission.Mostow.Hyper.sq_tpart _
    have h2 : tpart (actO A 0) ^ 2 = 1 + ‖actO A 0‖ ^ 2 :=
      Submission.Mostow.Hyper.sq_tpart _
    rw [hnorm, tpart_actO_ray A ξ 1 hξ] at h1
    nlinarith [h1, h2]
  have hE2 : 1 - Real.exp (-1) ^ 2 = 2 * Real.sinh 1 * Real.exp (-1) := by
    have hb := Work.Mostow.exp_neg_mul_sinh (1 : ℝ)
    have h2 : Real.exp (-(2 * (1 : ℝ))) = Real.exp (-1) ^ 2 := by
      rw [sq, ← Real.exp_add]
      norm_num
    rw [h2] at hb
    nlinarith [hb]
  have hfin : 2 * Real.sinh 1 * Real.exp (-1) *
      (cpar A ξ * (tpart (actO A 0) - inner ℝ (actO A 0) (bdO A ξ))) =
      2 * Real.sinh 1 * Real.exp (-1) * 1 := by
    nlinarith [hrel, hE2]
  refine mul_left_cancel₀ ?_ hfin
  have h1 : Real.sinh 1 ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr (by norm_num))
  have h2 : Real.exp (-1) ≠ 0 := Real.exp_ne_zero (-1)
  exact mul_ne_zero (mul_ne_zero (by norm_num) h1) h2

/-! ## The final real inequality -/

/-- If `E * C + E * S = 1` with `E > 0`, `S ≥ 0`, and `c * (cz - a) = 1` with `a² + 1 ≤ cz²` and
`1 ≤ cz`, then `E * (cz * C + S * (c - a)) ≤ cz`. -/
lemma ray_final_bound (c cz a E C S : ℝ) (hE : 0 < E) (hS : 0 ≤ S) (hone : E * C + E * S = 1)
    (hcz : 1 ≤ cz) (hrel : c * (cz - a) = 1) (ha : a ^ 2 + 1 ≤ cz ^ 2) :
    E * (cz * C + S * (c - a)) ≤ cz := by
  have hczpos : 0 < cz := lt_of_lt_of_le one_pos hcz
  have h2 : (1 : ℝ) ≤ cz ^ 2 - a ^ 2 := by linarith
  have hlt : |a| < cz := by
    have h1 : a ^ 2 < cz ^ 2 := by linarith
    nlinarith [h1, abs_nonneg a, sq_abs a]
  have hdpos : 0 < cz - a := by
    have := le_abs_self a
    linarith
  have hcs : c ≤ cz + a := by
    have h1 : c * (cz - a) ≤ (cz + a) * (cz - a) := by
      nlinarith [hrel, h2]
    exact le_of_mul_le_mul_right h1 hdpos
  have hkey : c - a - cz ≤ 0 := by linarith
  have hsplit : E * (cz * C + S * (c - a)) - cz = E * S * (c - a - cz) := by
    nlinarith [hone]
  have hES : 0 ≤ E * S := mul_nonneg (le_of_lt hE) hS
  nlinarith [hsplit, hES, hkey]

/-! ## Bounding the distance -/

/-- **The comparison of rays.**  For any `A : O(n,1)` and `ξ ∈ Sph n`, the isometric image of the
ray from `0` to `ξ` is at distance at most `hdist 0 (A • 0)` from the ray from `0` to `bdO A ξ`. -/
lemma rayCompare_O1 (A : O1 n) (ξ : E n) (hξ : ξ ∈ Sph n) (hξ' : bdO A ξ ∈ Sph n)
    (t : ℝ) (ht : 0 ≤ t) :
    hdist (actO A (ray ξ t)) (ray (bdO A ξ) t) ≤ hdist 0 (actO A 0) := by
  have hξ'n : ‖bdO A ξ‖ = 1 := (Work.Mostow.mem_Sph_iff _).mp hξ'
  have hrel := cpar_rel A ξ hξ
  -- Cauchy–Schwarz for the parameter `a`
  have ha : inner ℝ (actO A 0) (bdO A ξ) ^ 2 + 1 ≤ tpart (actO A 0) ^ 2 := by
    have hcs : |inner ℝ (actO A 0) (bdO A ξ)| ≤ ‖actO A 0‖ := by
      have h := abs_real_inner_le_norm (actO A 0) (bdO A ξ)
      rwa [hξ'n, mul_one] at h
    have h1 : |inner ℝ (actO A 0) (bdO A ξ)| ^ 2 ≤ ‖actO A 0‖ ^ 2 := by
      nlinarith [hcs, abs_nonneg (inner ℝ (actO A 0) (bdO A ξ))]
    rw [sq_abs] at h1
    have h0 : tpart (actO A 0) ^ 2 = 1 + ‖actO A 0‖ ^ 2 := Submission.Mostow.Hyper.sq_tpart _
    linarith
  -- the two rays in the chart
  have hqt : tpart (ray (bdO A ξ) t) = Real.cosh t := by
    rw [ray]
    exact Work.Mostow.tpart_sinh_smul (bdO A ξ) t hξ'n
  have hinner : inner ℝ (actO A (ray ξ t)) (ray (bdO A ξ) t) =
      (cpar A ξ * Real.sinh t) * Real.sinh t +
        Real.exp (-t) * Real.sinh t * inner ℝ (actO A 0) (bdO A ξ) := by
    rw [actO_ray_chart A ξ t hξ, ray]
    simp only [inner_add_left, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hξ'n]
    ring
  have hcc : Submission.Mostow.Hyper.cc (actO A (ray ξ t)) (ray (bdO A ξ) t) =
      Real.exp (-t) * (tpart (actO A 0) * Real.cosh t +
        Real.sinh t * (cpar A ξ - inner ℝ (actO A 0) (bdO A ξ))) := by
    show tpart (actO A (ray ξ t)) * tpart (ray (bdO A ξ) t) -
        inner ℝ (actO A (ray ξ t)) (ray (bdO A ξ) t) = _
    have hC : Real.cosh t = Real.sinh t + Real.exp (-t) := by
      linarith [Real.cosh_sub_sinh t]
    rw [tpart_actO_ray A ξ t hξ, hqt, hinner, hC]
    ring
  have hD : hdist 0 (actO A 0) = Real.arcosh (tpart (actO A 0)) := by
    rw [Submission.Mostow.Hyper.hdist_eq_cc, Submission.Mostow.Hyper.cc_comm,
      Submission.Mostow.Hyper.cc_zero]
  have h1 : 0 < Submission.Mostow.Hyper.cc (actO A (ray ξ t)) (ray (bdO A ξ) t) := by
    show 0 < tpart (actO A (ray ξ t)) * tpart (ray (bdO A ξ) t) -
      inner ℝ (actO A (ray ξ t)) (ray (bdO A ξ) t)
    have hone := one_le_tpart_mul_sub_inner (actO A (ray ξ t)) (ray (bdO A ξ) t)
    linarith
  have h2 : 0 < tpart (actO A 0) := Submission.Mostow.Hyper.tpart_pos _
  rw [hD, Submission.Mostow.Hyper.hdist_eq_cc]
  rw [Real.arcosh_le_arcosh h1 h2]
  rw [hcc]
  have hone : Real.exp (-t) * Real.cosh t + Real.exp (-t) * Real.sinh t = 1 := by
    rw [← mul_add, Real.cosh_add_sinh, ← Real.exp_add]
    norm_num
  exact ray_final_bound _ _ _ _ _ _ (Real.exp_pos _) (Real.sinh_nonneg_iff.mpr ht) hone
    (Submission.Mostow.Hyper.one_le_tpart _) hrel ha

/-- **`isomRayCompare`.**  The isometric image of the geodesic ray from the base point to `ξ` stays
at bounded distance (namely `hdist 0 (g • 0)`) from the geodesic ray from the base point to
`bd g ξ`. -/
theorem isomRayCompare (n : ℕ) (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n)
    (g : LeanEval.Geometry.MostowRigidity.PO n 1) (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, 0 ≤ t →
      Submission.Mostow.hdist (g • Work.Mostow.BdExt.ray ξ t) (Work.Mostow.BdExt.ray (Submission.Mostow.bd g ξ) t) ≤ D := by
  obtain ⟨-, -, -, -, -, -, -, hbdSph, -, -, -, -⟩ := hA
  refine ⟨Submission.Mostow.hdist 0 (g • (0 : Submission.Mostow.E n)), hI.1 _ _, ?_⟩
  intro t ht
  exact rayCompare_O1 (Submission.Mostow.rep g) ξ hξ (hbdSph g ξ hξ) t ht

end

end Work.Mostow.BdExt

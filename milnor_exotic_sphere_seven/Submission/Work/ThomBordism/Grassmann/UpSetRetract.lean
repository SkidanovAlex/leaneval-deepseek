import Mathlib
import Submission.Work.ThomBordism.Grassmann.Retraction
import Submission.Work.ThomBordism.Grassmann.OpenQuotient

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# The upper half of the incidence space retracts onto the fibre over `baseVec`

`upSet k m` is the part of the incidence space `E = zeroComplement (tautologicalBundle k m)` whose
(vector-)direction lies in the upper hemisphere; `fibreVec k m` is the fibre over `baseVec`.  The
rotation `rotLI (dirVec x) baseVec` carries a point of `upSet` into `fibreVec`, and the straight-line
path `t ↦ ‖(1-t) dirVec x + t baseVec‖⁻¹ • ((1-t) dirVec x + t baseVec)` in the sphere provides a
homotopy from the identity of `upSet` to the retraction, so that

`Work.ThomBordism.Grassmann.nonempty_homotopyEquiv_upSet_fibre` — `upSet k m` and `fibreVec k m` are
homotopy equivalent.

This is the "first half" of the local triviality of the incidence fibration: it identifies the
cohomology of the upper half with that of the fibre.
-/

open scoped Topology
open unitInterval CategoryTheory

namespace Work.ThomBordism.Grassmann

noncomputable section

variable {k m : ℕ}

/-! ## Elementary rotation identities -/

theorem rotMap_self_apply {n : ℕ} {u x : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ = 1) :
    rotMap u u x = x := by
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have h2 : (inner ℝ x u - inner ℝ x u * inner ℝ u u) / (1 + inner ℝ u u) = 0 := by
    rw [huu]; ring
  rw [rotMap, sub_self, smul_zero, add_zero, h2, zero_smul, sub_zero]

theorem rotLI_self {k m : ℕ} {u : Amb (k+m)} (hu : ‖u‖ = 1) (h : 1 + inner ℝ u u ≠ 0) :
    rotLI u u hu hu h = 1 := by
  refine LinearIsometry.ext fun x => ?_
  rw [rotLI_apply, rotMap_self_apply hu]
  rfl

theorem planeAct_one {k m : ℕ} (P : OG k m) :
    planeAct (1 : Amb (k+m) →ₗᵢ[ℝ] Amb (k+m)) P = P := by
  obtain ⟨f, rfl⟩ := Quotient.exists_rep P
  rw [planeAct_mk]
  exact congrArg (fun g : Stiefel k m => (Quotient.mk'' g : OG k m)) (Subtype.ext rfl)

/-- `mkTotal` only depends on the plane and the coordinate. -/
theorem mkTotal_ext {k m : ℕ} {P P' : OG k m} {c c' : Amb k} (hP : P = P') (hc : c = c') :
    mkTotal P c = mkTotal P' c' := by
  subst hP; subst hc; rfl

/-- **A point of the incidence space is determined by its plane and its vector.** -/
theorem toE_self {k m : ℕ} (p : ↥(incZero k m)) :
    toE p.1.1 (evalVec p.1) (evalVec_ne_zero_of_mem_zeroComplement p.1 p.2)
      (evalVec_memPlane p.1) = p := by
  have hS : p.1.1 ∈ (tautologicalBundle k m).baseSet ((tautologicalBundle k m).indexAt p.1.1) :=
    (tautologicalBundle k m).mem_baseSet_at p.1.1
  have hev : evalVec p.1 = evalChartO ((tautologicalBundle k m).indexAt p.1.1)
      ⟨p.1.1, hS⟩ (show Amb k from ((tautologicalBundle k m).localTriv
        ((tautologicalBundle k m).indexAt p.1.1) p.1).2) :=
    evalVec_apply_chart p.1 _ hS
  have hcoord : (show Amb k from ((tautologicalBundle k m).localTriv
      ((tautologicalBundle k m).indexAt p.1.1) p.1).2) = p.1.2 := by
    rw [VectorBundleCore.localTriv_apply]
    exact VectorBundleCore.coordChange_self (tautologicalBundle k m) _ p.1.1 hS p.1.2
  have hkey : toECoordAt ((tautologicalBundle k m).indexAt p.1.1) p.1.1 (evalVec p.1) = p.1.2 := by
    apply peEvalChartO_injective ((tautologicalBundle k m).indexAt p.1.1) ⟨p.1.1, hS⟩
    rw [evalChartO_toECoordAt _ _ hS _ (evalVec_memPlane p.1), hev, hcoord]
  refine Subtype.ext ?_
  show mkTotal p.1.1 (toECoordAt ((tautologicalBundle k m).indexAt p.1.1) p.1.1 (evalVec p.1)) = p.1
  rw [hkey]
  rfl

/-- **`toE` only depends on the plane and the vector.** -/
theorem toE_congr {k m : ℕ} {P P' : OG k m} {w w' : Amb (k+m)} (hP : P = P') (hwe : w = w')
    (hw0 : w ≠ 0) (hm : memPlane P w) (hw0' : w' ≠ 0) (hm' : memPlane P' w') :
    toE P w hw0 hm = toE P' w' hw0' hm' := by
  subst hP; subst hwe
  exact Subtype.ext rfl

theorem rotE_one {k m : ℕ} (x : ↥(incZero k m)) :
    rotE (1 : Amb (k+m) →ₗᵢ[ℝ] Amb (k+m)) x = x :=
  (toE_congr (planeAct_one x.1.1) rfl _ _
    (evalVec_ne_zero_of_mem_zeroComplement x.1 x.2) (evalVec_memPlane x.1)).trans (toE_self x)

/-! ## Continuity of `dirVec` and of the retraction -/

theorem continuous_dirVec {k m : ℕ} : Continuous fun x : ↥(incZero k m) => dirVec x := by
  have h1 : Continuous fun x : ↥(incZero k m) => evalVec x.1 :=
    continuous_evalVec.comp continuous_subtype_val
  have h2 : Continuous fun x : ↥(incZero k m) => (‖evalVec x.1‖)⁻¹ :=
    h1.norm.inv₀ fun x => norm_evalVec_ne_zero x
  exact h2.smul h1

/-- **The retraction of `upSet` is continuous.** -/
theorem continuous_sPlus {k m : ℕ} (hk : 1 ≤ k) :
    Continuous (sPlus (k := k) (m := m) hk) := by
  have hb : ‖baseVec k m‖ = 1 := norm_baseVec (by omega)
  have hR : Continuous fun q : ↥(upSet k m) × Amb (k+m) =>
      rotLI (dirVec (q.1 : ↥(incZero k m))) (baseVec k m) (norm_dirVec _) hb (upSet_angle q.1) q.2 := by
    have hdir : Continuous fun q : ↥(upSet k m) × Amb (k+m) =>
        dirVec (q.1 : ↥(incZero k m)) :=
      continuous_dirVec.comp (continuous_subtype_val.comp continuous_fst)
    have hmap : Continuous fun q : ↥(upSet k m) × Amb (k+m) =>
        (dirVec (q.1 : ↥(incZero k m)), q.2) := hdir.prodMk continuous_snd
    have h := (continuous_rotMap (n := k+m) (e := baseVec k m)).comp_continuous hmap
      (fun q => upSet_angle q.1)
    simpa only [rotLI_apply, Function.comp_def] using h
  have hx : Continuous fun x : ↥(upSet k m) => (x : ↥(incZero k m)) := continuous_subtype_val
  have h := continuous_rotE_comp' (k := k) (m := m) (ι := ↥(upSet k m))
    (R := fun x => rotLI (dirVec (x : ↥(incZero k m))) (baseVec k m) (norm_dirVec _) hb
      (upSet_angle x))
    (x := fun x : ↥(upSet k m) => (x : ↥(incZero k m))) hR hx
  exact h

/-! ## Positivity of the angle on the upper half -/

/-- `star` is the identity on `ℝ`. -/
theorem starRingEnd_real (a : ℝ) : (starRingEnd ℝ) a = a := rfl

/-- The inner product of two interpolated vectors: `⟪u v + t e, v + e⟫ = (u+t)(1+⟪v,e⟫)`. -/
theorem inner_interp_add {N : ℕ} {v e : EuclideanSpace ℝ (Fin N)} (u t : ℝ) (hv : ‖v‖ = 1)
    (he : ‖e‖ = 1) :
    inner ℝ (u • v + t • e) (v + e) = (u + t) * (1 + inner ℝ v e) := by
  have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hst : ∀ a : ℝ, (starRingEnd ℝ) a = a := fun a => rfl
  simp only [inner_add_left, inner_add_right, inner_smul_left, hvv, hee,
    real_inner_comm e v, hst]
  ring

/-- **The angle at a point of the upper half**: `⟪dirVec x, baseVec⟫ > -1/2`. -/
theorem upSet_angle_gt {k m : ℕ} (x : ↥(upSet k m)) :
    -(1/2 : ℝ) < inner ℝ (dirVec (x : ↥(incZero k m))) (baseVec k m) := by
  have hn : 0 < ‖evalVec (x : ↥(incZero k m)).1‖ :=
    norm_pos_iff.mpr (evalVec_ne_zero_of_mem_zeroComplement _ (x : ↥(incZero k m)).2)
  have hup : 0 < 2 * inner ℝ (evalVec (x : ↥(incZero k m)).1) (baseVec k m)
      + ‖evalVec (x : ↥(incZero k m)).1‖ := by
    have h := x.2
    simpa only [upSet, heightVec, Set.mem_ofPred_eq] using h
  have hy : evalVec (x : ↥(incZero k m)).1
      = ‖evalVec (x : ↥(incZero k m)).1‖ • dirVec (x : ↥(incZero k m)) :=
    (dirVec_smul (x : ↥(incZero k m))).symm
  have hsplit : 2 * inner ℝ (evalVec (x : ↥(incZero k m)).1) (baseVec k m)
      + ‖evalVec (x : ↥(incZero k m)).1‖
      = ‖evalVec (x : ↥(incZero k m)).1‖
        * (2 * inner ℝ (dirVec (x : ↥(incZero k m))) (baseVec k m) + 1) := by
    rw [hy, inner_smul_left, starRingEnd_apply, star_trivial, norm_smul, Real.norm_eq_abs,
      abs_of_pos hn, norm_dirVec, mul_one]
    ring
  rw [hsplit] at hup
  have h2 : 0 < 2 * inner ℝ (dirVec (x : ↥(incZero k m))) (baseVec k m) + 1 := by
    by_contra hcon
    push_neg at hcon
    nlinarith [hup, hn]
  linarith

/-- **The angle at a point of the upper half is strictly positive**: `1 + ⟪dirVec x, baseVec⟫ > 0`. -/
theorem upSet_angle_pos {k m : ℕ} (x : ↥(upSet k m)) :
    0 < 1 + inner ℝ (dirVec (x : ↥(incZero k m))) (baseVec k m) := by
  have := upSet_angle_gt x; linarith

/-- `1 + ⟪dirVec x, baseVec⟫ > 1/2` on the upper half. -/
theorem upSet_angle_half {k m : ℕ} (x : ↥(upSet k m)) :
    (1/2 : ℝ) < 1 + inner ℝ (dirVec (x : ↥(incZero k m))) (baseVec k m) := by
  have := upSet_angle_gt x; linarith

/-! ## The fibre over `baseVec` and the straight-line path on the unit sphere -/

/-- The fibre of the incidence fibration over `baseVec`: points whose vector of the plane is a
positive multiple of `baseVec`. -/
def fibreVec (k m : ℕ) : Set ↥(incZero k m) := {x | dirVec x = baseVec k m}

theorem mem_fibreVec_iff {k m : ℕ} {x : ↥(incZero k m)} :
    x ∈ fibreVec k m ↔ dirVec x = baseVec k m := Iff.rfl

/-- The vector of the plane at a point of `fibreVec` is a positive multiple of `baseVec`. -/
theorem evalVec_eq_smul_baseVec {k m : ℕ} {x : ↥(incZero k m)} (hx : x ∈ fibreVec k m) :
    evalVec x.1 = ‖evalVec x.1‖ • baseVec k m := by
  rw [← (mem_fibreVec_iff.mp hx)]
  exact (dirVec_smul x).symm

/-- **Membership in `upSet` from the angle condition on the direction.** -/
theorem mem_upSet_of_dirVec {k m : ℕ} {y : ↥(incZero k m)}
    (h : 0 < 2 * inner ℝ (dirVec y) (baseVec k m) + 1) : y ∈ upSet k m := by
  have hpos : 0 < ‖evalVec y.1‖ :=
    norm_pos_iff.mpr (evalVec_ne_zero_of_mem_zeroComplement _ y.2)
  have hy : evalVec y.1 = ‖evalVec y.1‖ • dirVec y := (dirVec_smul y).symm
  have key : 2 * heightVec k m y.1 + ‖evalVec y.1‖
      = ‖evalVec y.1‖ * (2 * inner ℝ (dirVec y) (baseVec k m) + 1) := by
    rw [heightVec, hy, inner_smul_left, starRingEnd_apply, star_trivial, norm_smul,
      Real.norm_eq_abs, abs_of_pos hpos, norm_dirVec, mul_one]
    ring
  show 0 < 2 * heightVec k m y.1 + ‖evalVec y.1‖
  rw [key]
  exact mul_pos hpos h

/-- Points of the fibre lie in the upper half. -/
theorem mem_upSet_of_mem_fibreVec {k m : ℕ} (hk : 1 ≤ k) {x : ↥(incZero k m)}
    (hx : x ∈ fibreVec k m) : x ∈ upSet k m := by
  refine mem_upSet_of_dirVec ?_
  rw [mem_fibreVec_iff.mp hx]
  have h1 : inner ℝ (baseVec k m) (baseVec k m) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_baseVec (by omega)]; norm_num
  rw [h1]; norm_num

section Path

variable {k m : ℕ}

/-- The (unnormalised) straight-line path on the sphere from the direction of `x` to `baseVec`,
parametrised by `I`. -/
def hPath (q : I × ↥(upSet k m)) : Amb (k+m) :=
  (1 - (q.1 : ℝ)) • dirVec (q.2 : ↥(incZero k m)) + (q.1 : ℝ) • baseVec k m

/-- The normalised straight-line path: a continuous path on the unit sphere from the direction of
`x` to `baseVec`. -/
def wPath (q : I × ↥(upSet k m)) : Amb (k+m) :=
  ‖hPath q‖⁻¹ • hPath q

theorem hPath_inner_add (hk : 1 ≤ k) (q : I × ↥(upSet k m)) :
    inner ℝ (hPath q) (dirVec (q.2 : ↥(incZero k m)) + baseVec k m)
    = 1 + inner ℝ (dirVec (q.2 : ↥(incZero k m))) (baseVec k m) := by
  have h1 : (1 - (q.1 : ℝ)) + (q.1 : ℝ) = 1 := by ring
  have h := inner_interp_add (v := dirVec (q.2 : ↥(incZero k m))) (e := baseVec k m)
    (1 - (q.1 : ℝ)) (q.1 : ℝ) (norm_dirVec _) (norm_baseVec (by omega))
  rw [hPath, h, h1, one_mul]

theorem hPath_ne_zero (hk : 1 ≤ k) (q : I × ↥(upSet k m)) : hPath q ≠ 0 := by
  intro h0
  have hz := hPath_inner_add hk q
  rw [h0, inner_zero_left] at hz
  have hpos := upSet_angle_pos (k := k) (m := m) q.2
  linarith

theorem norm_hPath_pos (hk : 1 ≤ k) (q : I × ↥(upSet k m)) : 0 < ‖hPath q‖ :=
  norm_pos_iff.mpr (hPath_ne_zero hk q)

theorem hPath_eq_smul_wPath (hk : 1 ≤ k) (q : I × ↥(upSet k m)) :
    hPath q = ‖hPath q‖ • wPath q := by
  rw [wPath, smul_smul, mul_inv_cancel₀ (ne_of_gt (norm_hPath_pos hk q)), one_smul]

theorem hPath_inner_self (q : I × ↥(upSet k m)) :
    inner ℝ (hPath q) (dirVec (q.2 : ↥(incZero k m)))
    = (1 - (q.1 : ℝ))
      + (q.1 : ℝ) * inner ℝ (dirVec (q.2 : ↥(incZero k m))) (baseVec k m) := by
  have h1 : inner ℝ (dirVec (q.2 : ↥(incZero k m))) (dirVec (q.2 : ↥(incZero k m))) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_dirVec]; norm_num
  rw [hPath, inner_add_left, inner_smul_left, inner_smul_left, starRingEnd_apply,
    starRingEnd_apply, star_trivial, star_trivial, h1,
    real_inner_comm (baseVec k m) (dirVec (q.2 : ↥(incZero k m)))]
  ring

theorem norm_hPath_le_one (hk : 1 ≤ k) (q : I × ↥(upSet k m)) : ‖hPath q‖ ≤ 1 := by
  have hdir : ‖dirVec (q.2 : ↥(incZero k m))‖ = 1 := norm_dirVec _
  rw [hPath]
  calc ‖(1 - (q.1 : ℝ)) • dirVec (q.2 : ↥(incZero k m)) + (q.1 : ℝ) • baseVec k m‖
      ≤ ‖(1 - (q.1 : ℝ)) • dirVec (q.2 : ↥(incZero k m))‖ + ‖(q.1 : ℝ) • baseVec k m‖ :=
        norm_add_le _ _
    _ = |1 - (q.1 : ℝ)| + |(q.1 : ℝ)| := by
        rw [norm_smul, norm_smul, hdir, norm_baseVec (by omega), mul_one, mul_one,
          Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 1 := by
        have ht0 : 0 ≤ (q.1 : ℝ) := q.1.2.1
        have ht1 : (q.1 : ℝ) ≤ 1 := q.1.2.2
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - (q.1 : ℝ)), abs_of_nonneg ht0]
        linarith

theorem norm_wPath (hk : 1 ≤ k) (q : I × ↥(upSet k m)) : ‖wPath q‖ = 1 := by
  rw [wPath, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ (ne_of_gt (norm_hPath_pos hk q))]

/-- **The normalised interpolated direction is never `-baseVec`**, so the rotation carrying it to
`baseVec` is well defined. -/
theorem wPath_angle (hk : 1 ≤ k) (q : I × ↥(upSet k m)) :
    1 + inner ℝ (wPath q) (baseVec k m) ≠ 0 := by
  have hz := hPath_inner_add hk q
  have hpos := upSet_angle_pos (k := k) (m := m) q.2
  have hze : 0 < inner ℝ (hPath q) (dirVec (q.2 : ↥(incZero k m)) + baseVec k m) := by
    rw [hz]; linarith
  intro hcon
  have hneg : inner ℝ (wPath q) (baseVec k m) = -1 := by linarith
  have hw : wPath q = - baseVec k m := by
    have h1 : ‖wPath q + baseVec k m‖ ^ 2 = 0 := by
      rw [norm_add_sq_real, norm_wPath hk, norm_baseVec (by omega), hneg]
      norm_num
    have h2 : ‖wPath q + baseVec k m‖ = 0 := by
      nlinarith [norm_nonneg (wPath q + baseVec k m)]
    rw [norm_eq_zero] at h2
    rwa [add_eq_zero_iff_eq_neg] at h2
  have hsm : inner ℝ (hPath q) (dirVec (q.2 : ↥(incZero k m)) + baseVec k m)
      = ‖hPath q‖ * (-(inner ℝ (dirVec (q.2 : ↥(incZero k m))) (baseVec k m) + 1)) := by
    conv_lhs => rw [hPath_eq_smul_wPath hk q]
    rw [inner_smul_left, starRingEnd_real, hw, inner_neg_left, inner_add_right,
      real_inner_comm (baseVec k m) (dirVec (q.2 : ↥(incZero k m))),
      real_inner_self_eq_norm_sq, norm_baseVec (by omega)]
    ring
  rw [hsm] at hze
  have hD := norm_hPath_pos hk q
  have hp := upSet_angle_half (k := k) (m := m) q.2
  nlinarith

/-- **The rotated point stays in the upper half**: `2⟪dirVec x, wPath⟫ + 1 > 0`. -/
theorem wPath_cond (hk : 1 ≤ k) (q : I × ↥(upSet k m)) :
    0 < 2 * inner ℝ (dirVec (q.2 : ↥(incZero k m))) (wPath q) + 1 := by
  have hD := norm_hPath_pos hk q
  have hz := hPath_inner_add hk q
  have hpos := upSet_angle_pos (k := k) (m := m) q.2
  have h1 : inner ℝ (dirVec (q.2 : ↥(incZero k m))) (wPath q)
      = (inner ℝ (hPath q) (dirVec (q.2 : ↥(incZero k m)))) / ‖hPath q‖ := by
    rw [wPath, inner_smul_right, real_inner_comm]
    field_simp
  have h2 : inner ℝ (hPath q) (baseVec k m) ≤ ‖hPath q‖ := by
    calc inner ℝ (hPath q) (baseVec k m) ≤ ‖hPath q‖ * ‖baseVec k m‖ := real_inner_le_norm _ _
      _ = ‖hPath q‖ := by rw [norm_baseVec (by omega), mul_one]
  have h3 : inner ℝ (hPath q) (dirVec (q.2 : ↥(incZero k m)))
      = (1 + inner ℝ (dirVec (q.2 : ↥(incZero k m))) (baseVec k m))
        - inner ℝ (hPath q) (baseVec k m) := by
    rw [← hz, inner_add_right]
    ring
  have hDle : ‖hPath q‖ ≤ 1 := norm_hPath_le_one hk q
  have hhalf := upSet_angle_half (k := k) (m := m) q.2
  have key : 0 < 2 * ((1 + inner ℝ (dirVec (q.2 : ↥(incZero k m))) (baseVec k m))
      - inner ℝ (hPath q) (baseVec k m)) + ‖hPath q‖ := by linarith
  rw [h1, h3]
  have hgoal : 2 * (((1 + inner ℝ (dirVec (q.2 : ↥(incZero k m))) (baseVec k m))
        - inner ℝ (hPath q) (baseVec k m)) / ‖hPath q‖) + 1
      = (2 * ((1 + inner ℝ (dirVec (q.2 : ↥(incZero k m))) (baseVec k m))
        - inner ℝ (hPath q) (baseVec k m)) + ‖hPath q‖) / ‖hPath q‖ := by
    field_simp
  rw [hgoal]
  exact div_pos key hD

theorem continuous_hPath : Continuous (hPath (k := k) (m := m)) := by
  have hdir : Continuous fun q : I × ↥(upSet k m) => dirVec (q.2 : ↥(incZero k m)) :=
    continuous_dirVec.comp (continuous_subtype_val.comp continuous_snd)
  refine Continuous.add ?_ ?_
  · exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul hdir
  · exact (continuous_subtype_val.comp continuous_fst).smul continuous_const

theorem continuous_wPath (hk : 1 ≤ k) : Continuous (wPath (k := k) (m := m)) := by
  have h1 : Continuous fun q : I × ↥(upSet k m) => ‖hPath q‖⁻¹ :=
    (continuous_hPath (k := k) (m := m)).norm.inv₀ fun q => ne_of_gt (norm_hPath_pos hk q)
  exact h1.smul (continuous_hPath (k := k) (m := m))


/-! ## The homotopy from the retraction to the identity -/

/-- The direction of the plane is transported by the rotation. -/
theorem dirVec_rotE {k m : ℕ} (R : Amb (k+m) →ₗᵢ[ℝ] Amb (k+m)) (x : ↥(incZero k m)) :
    dirVec (rotE R x) = R (dirVec x) := by
  have hnorm : ‖R (evalVec x.1)‖ = ‖evalVec x.1‖ := LinearIsometry.norm_map R _
  show ‖evalVec (rotE R x).1‖⁻¹ • evalVec (rotE R x).1 = R (dirVec x)
  rw [evalVec_rotE, hnorm, dirVec, map_smul]

/-- `planeAct` only depends on the values of the isometry. -/
theorem planeAct_congr {k m : ℕ} {R R' : Amb (k+m) →ₗᵢ[ℝ] Amb (k+m)} (h : ∀ y, R y = R' y)
    (P : OG k m) : planeAct R P = planeAct R' P := by
  obtain ⟨f, rfl⟩ := Quotient.exists_rep P
  have hf : (⟨fun i => R (f.1 i), ⟨fun i => by
        rw [LinearIsometry.norm_map]; exact f.2.1 i, fun i j hij => by
        show inner ℝ (R (f.1 i)) (R (f.1 j)) = 0
        rw [LinearIsometry.inner_map_map, f.2.2 hij]⟩⟩ : Stiefel k m)
      = ⟨fun i => R' (f.1 i), ⟨fun i => by
        rw [LinearIsometry.norm_map]; exact f.2.1 i, fun i j hij => by
        show inner ℝ (R' (f.1 i)) (R' (f.1 j)) = 0
        rw [LinearIsometry.inner_map_map, f.2.2 hij]⟩⟩ :=
    Subtype.ext (funext fun i => h (f.1 i))
  rw [planeAct_mk, planeAct_mk, hf]

/-- `rotE` only depends on the values of the isometry. -/
theorem rotE_congr {k m : ℕ} {R R' : Amb (k+m) →ₗᵢ[ℝ] Amb (k+m)} (h : ∀ y, R y = R' y)
    (x : ↥(incZero k m)) : rotE R x = rotE R' x := by
  show toE (planeAct R x.1.1) (R (evalVec x.1)) _ _ = toE (planeAct R' x.1.1) (R' (evalVec x.1)) _ _
  exact toE_congr (planeAct_congr h x.1.1) (h (evalVec x.1)) _ _ _ _

/-- `rotLI u e = 1` when `u = e`. -/
theorem rotLI_eq_one_of_eq {k m : ℕ} {u : Amb (k+m)} (he : ‖baseVec k m‖ = 1)
    (hu : ‖u‖ = 1) (h : 1 + inner ℝ u (baseVec k m) ≠ 0) (hue : u = baseVec k m) :
    rotLI u (baseVec k m) hu he h = 1 := by
  subst hue
  exact rotLI_self hu h

/-- The homotopy of `upSet` into itself: rotate the direction along the straight-line path to
`baseVec`. -/
noncomputable def hMap (hk : 1 ≤ k) (q : I × ↥(upSet k m)) : ↥(incZero k m) :=
  rotE (rotLI (wPath q) (baseVec k m) (norm_wPath hk q) (norm_baseVec (by omega))
    (wPath_angle hk q)) (q.2 : ↥(incZero k m))

theorem hMap_dirVec (hk : 1 ≤ k) (q : I × ↥(upSet k m)) :
    dirVec (hMap hk q) = rotMap (wPath q) (baseVec k m) (dirVec (q.2 : ↥(incZero k m))) := by
  rw [hMap, dirVec_rotE, rotLI_apply]

theorem hMap_mem_upSet (hk : 1 ≤ k) (q : I × ↥(upSet k m)) : hMap hk q ∈ upSet k m := by
  refine mem_upSet_of_dirVec ?_
  have hinner : inner ℝ (rotMap (wPath q) (baseVec k m) (dirVec (q.2 : ↥(incZero k m))))
      (baseVec k m) = inner ℝ (dirVec (q.2 : ↥(incZero k m))) (wPath q) := by
    have hin := rotMap_inner (u := wPath q) (e := baseVec k m) (norm_wPath hk q)
      (norm_baseVec (by omega)) (wPath_angle hk q)
      (x := dirVec (q.2 : ↥(incZero k m))) (y := wPath q)
    rw [rotMap_self (norm_wPath hk q) (norm_baseVec (by omega))] at hin
    exact hin
  rw [hMap_dirVec hk q, hinner]
  exact wPath_cond hk q

theorem continuous_hMap (hk : 1 ≤ k) : Continuous (hMap (k := k) (m := m) hk) := by
  have hR : Continuous fun q : (I × ↥(upSet k m)) × Amb (k+m) =>
      rotLI (wPath q.1) (baseVec k m) (norm_wPath hk q.1) (norm_baseVec (by omega))
        (wPath_angle hk q.1) q.2 := by
    have hw : Continuous fun q : (I × ↥(upSet k m)) × Amb (k+m) => wPath q.1 :=
      (continuous_wPath hk).comp continuous_fst
    have hmap : Continuous fun q : (I × ↥(upSet k m)) × Amb (k+m) => (wPath q.1, q.2) :=
      hw.prodMk continuous_snd
    have h := (continuous_rotMap (n := k+m) (e := baseVec k m)).comp_continuous hmap
      (fun q => wPath_angle hk q.1)
    simpa only [rotLI_apply, Function.comp_def] using h
  have hx : Continuous fun q : I × ↥(upSet k m) => (q.2 : ↥(incZero k m)) :=
    continuous_subtype_val.comp continuous_snd
  exact continuous_rotE_comp' (k := k) (m := m) (ι := I × ↥(upSet k m))
    (R := fun q => rotLI (wPath q) (baseVec k m) (norm_wPath hk q) (norm_baseVec (by omega))
      (wPath_angle hk q))
    (x := fun q => (q.2 : ↥(incZero k m))) hR hx

theorem hPath_zero (x : ↥(upSet k m)) :
    hPath ((0 : I), x) = dirVec (x : ↥(incZero k m)) := by
  show (1 - ((0 : I) : ℝ)) • dirVec (x : ↥(incZero k m)) + ((0 : I) : ℝ) • baseVec k m
    = dirVec (x : ↥(incZero k m))
  simp

theorem hPath_one (x : ↥(upSet k m)) : hPath ((1 : I), x) = baseVec k m := by
  show (1 - ((1 : I) : ℝ)) • dirVec (x : ↥(incZero k m)) + ((1 : I) : ℝ) • baseVec k m
    = baseVec k m
  simp

theorem wPath_zero (hk : 1 ≤ k) (x : ↥(upSet k m)) :
    wPath ((0 : I), x) = dirVec (x : ↥(incZero k m)) := by
  rw [wPath, hPath_zero, norm_dirVec, inv_one, one_smul]

theorem wPath_one (hk : 1 ≤ k) (x : ↥(upSet k m)) : wPath ((1 : I), x) = baseVec k m := by
  rw [wPath, hPath_one, norm_baseVec (by omega), inv_one, one_smul]

/-- The homotopy at time `0` is the retraction `sPlus` (which lands in the fibre). -/
theorem hMap_zero (hk : 1 ≤ k) (x : ↥(upSet k m)) :
    hMap hk (0, x) = sPlus hk x := by
  rw [hMap, sPlus]
  refine rotE_congr (fun y => ?_) (x : ↥(incZero k m))
  rw [rotLI_apply, rotLI_apply, wPath_zero hk x]

/-- The homotopy at time `1` is the identity. -/
theorem hMap_one (hk : 1 ≤ k) (x : ↥(upSet k m)) : hMap hk (1, x) = x := by
  rw [hMap]
  refine (rotE_congr (fun y => ?_) (x : ↥(incZero k m))).trans (rotE_one _)
  rw [rotLI_apply]
  show rotMap (wPath ((1 : I), x)) (baseVec k m) y = (1 : Amb (k+m) →ₗᵢ[ℝ] Amb (k+m)) y
  rw [wPath_one hk x, rotMap_self_apply (norm_baseVec (by omega))]
  exact (LinearIsometry.id_apply y).symm

/-- The retraction of `upSet` onto the fibre over `baseVec`, as a map of `upSet` into itself. -/
noncomputable def sPlusMap (hk : 1 ≤ k) : C(↥(upSet k m), ↥(upSet k m)) where
  toFun x := ⟨sPlus hk x, mem_upSet_of_mem_fibreVec hk (dirVec_sPlus hk x)⟩
  continuous_toFun := Continuous.subtype_mk (continuous_sPlus hk) _

/-- The retraction, as a map into the fibre. -/
noncomputable def sPlusFibre (hk : 1 ≤ k) : C(↥(upSet k m), ↥(fibreVec k m)) where
  toFun x := ⟨sPlus hk x, dirVec_sPlus hk x⟩
  continuous_toFun := Continuous.subtype_mk (continuous_sPlus hk) _

/-- The inclusion of the fibre into `upSet`. -/
noncomputable def inclFibre (hk : 1 ≤ k) : C(↥(fibreVec k m), ↥(upSet k m)) where
  toFun x := ⟨x.1, mem_upSet_of_mem_fibreVec hk x.2⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _

/-- **The homotopy from the retraction to the identity of `upSet`.** -/
noncomputable def homotopyUp (hk : 1 ≤ k) :
    ContinuousMap.Homotopy (sPlusMap (k := k) (m := m) hk)
      (ContinuousMap.id ↥(upSet k m)) where
  toFun q := ⟨hMap hk q, hMap_mem_upSet hk q⟩
  continuous_toFun := Continuous.subtype_mk (continuous_hMap hk) _
  map_zero_left x := Subtype.ext (hMap_zero hk x)
  map_one_left x := Subtype.ext (hMap_one hk x)

/-- The retraction is a homotopy inverse of the inclusion of the fibre. -/
theorem sPlusFibre_comp_inclFibre (hk : 1 ≤ k) :
    (sPlusFibre (k := k) (m := m) hk).comp (inclFibre hk) = ContinuousMap.id ↥(fibreVec k m) := by
  refine ContinuousMap.ext fun y => ?_
  refine Subtype.ext ?_
  show sPlus hk (inclFibre hk y) = (y : ↥(incZero k m))
  rw [sPlus]
  refine (rotE_congr (fun z => ?_) (inclFibre hk y : ↥(incZero k m))).trans (rotE_one _)
  show rotMap (dirVec (y : ↥(incZero k m))) (baseVec k m) z
    = (1 : Amb (k+m) →ₗᵢ[ℝ] Amb (k+m)) z
  rw [mem_fibreVec_iff.mp y.2, rotMap_self_apply (norm_baseVec (by omega))]
  exact (LinearIsometry.id_apply z).symm

/-- `sPlusMap` is the composite of the retraction onto the fibre with the inclusion. -/
theorem sPlusMap_eq_comp (hk : 1 ≤ k) :
    sPlusMap (k := k) (m := m) hk = (inclFibre hk).comp (sPlusFibre hk) := by
  refine ContinuousMap.ext fun x => Subtype.ext (Subtype.ext rfl)

/-- **`upSet` and the fibre over `baseVec` are homotopy equivalent.** -/
theorem nonempty_homotopyEquiv_upSet_fibreVec (hk : 1 ≤ k) :
    Nonempty (ContinuousMap.HomotopyEquiv ↥(upSet k m) ↥(fibreVec k m)) :=
  ⟨ContinuousMap.HomotopyEquiv.mk (sPlusFibre hk) (inclFibre hk)
    ⟨((homotopyUp hk).cast (sPlusMap_eq_comp hk) rfl)⟩
    ⟨(ContinuousMap.Homotopy.refl ((sPlusFibre hk).comp (inclFibre hk))).cast rfl
      (sPlusFibre_comp_inclFibre hk)⟩⟩

/-- **A cohomological isomorphism from a homotopy equivalence.** -/
theorem nonempty_singularCohomology_iso_of_homotopyEquiv {X Y : TopCat}
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    Nonempty (Work.Cohomology.singularCohomology ℤ n X ≅ Work.Cohomology.singularCohomology ℤ n Y) := by
  let f : X ⟶ Y := TopCat.ofHom e.toFun
  let g : Y ⟶ X := TopCat.ofHom e.invFun
  have h1 : TopCat.Homotopy (f ≫ g) (𝟙 X) := e.left_inv.some
  have h2 : TopCat.Homotopy (g ≫ f) (𝟙 Y) := e.right_inv.some
  haveI := Work.Cohomology.homotopyEquiv ℤ X Y f g h1 h2 n
  exact ⟨(CategoryTheory.asIso (Work.Cohomology.singularCohomologyMap ℤ X Y f n)).symm⟩

end Path

end

end Work.ThomBordism.Grassmann

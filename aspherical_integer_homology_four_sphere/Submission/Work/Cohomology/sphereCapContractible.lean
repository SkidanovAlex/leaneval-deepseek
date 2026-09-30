import Mathlib
import Submission.Work.Morse.TwoBallsBasic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The "cap" `{x : ‖x‖ = 1 ∧ x_m > -ε}` on the sphere is contractible

For `m : ℕ` and `0 < ε ≤ 1` consider the subset of the unit sphere of `ℝ^{m+1}` cut out by the
half-space `x_m > -ε`.  Since `ε ≤ 1` we have `-ε ≥ -1`, so this region contains the north pole and
is bigger than a closed hemisphere; it is the complement of a (possibly degenerate) small cap
around the south pole.  It is homeomorphic to the open region `{(1-ε)‖y‖² < 1+ε}` of `ℝ^m` via
stereographic projection from the south pole,
```
  x ↦ x_{<m} / (1 + x_m),      y ↦ (2y/(1+‖y‖²), (1-‖y‖²)/(1+‖y‖²)).
```
The latter is convex (it is an open ball for `ε < 1` and all of `ℝ^m` for `ε = 1`), and a nonempty
convex subset of the real topological vector space `ℝ^m` is contractible.  Hence the cap is
contractible too.

## Main result

* `Work.Cohomology.sphereCapContractible`
-/

namespace Work.Cohomology

open Metric
open Work.Morse

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

section Stereo

variable {m : ℕ}

/-- Forward stereographic projection from the south pole `-e_m` of the unit sphere of `ℝ^{m+1}`
onto `ℝ^m`, written in the "unnormalised" form `x_{<m} / (1 + x_m)`.  It is only used as a map
between the appropriate subsets; on the cap `x_m > -ε` the denominator `1 + x_m` is positive. -/
def stereoFwd (x : EuclideanSpace ℝ (Fin (m + 1))) : EuclideanSpace ℝ (Fin m) :=
  (1 / (1 + x.ofLp (Fin.last m))) • strip x

/-- The inverse of `stereoFwd`, namely `y ↦ (2y/(1+‖y‖²), (1-‖y‖²)/(1+‖y‖²))`. -/
def stereoInv (y : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin (m + 1)) :=
  snocLp ((2 / (1 + ‖y‖ ^ 2)) • y) ((1 - ‖y‖ ^ 2) / (1 + ‖y‖ ^ 2))

/-- The cap `{x : ‖x‖ = 1 ∧ x_m > -ε}` of the unit sphere of `ℝ^{m+1}`. -/
def capSet (ε : ℝ) : Set (EuclideanSpace ℝ (Fin (m + 1))) :=
  {x | ‖x‖ = 1 ∧ x.ofLp (Fin.last m) > -ε}

/-- The target region `{(1-ε)‖y‖² < 1+ε}` of `stereoFwd`. -/
def tgtSet (ε : ℝ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {y | (1 - ε) * ‖y‖ ^ 2 < 1 + ε}

lemma continuous_strip : Continuous (@strip m) := by
  unfold strip
  fun_prop

lemma strip_snocLp (y : EuclideanSpace ℝ (Fin m)) (t : ℝ) : strip (snocLp y t) = y := by
  apply PiLp.ext
  intro i
  rw [strip_ofLp, snocLp_ofLp_castSucc]

lemma strip_norm_sq (z : EuclideanSpace ℝ (Fin (m + 1))) :
    ‖strip z‖ ^ 2 = ‖z‖ ^ 2 - (z.ofLp (Fin.last m)) ^ 2 := by
  have h := snocLp_norm_sq (strip z) (z.ofLp (Fin.last m))
  rw [snocLp_strip] at h
  linarith

lemma stereoInv_last (y : EuclideanSpace ℝ (Fin m)) :
    (stereoInv y).ofLp (Fin.last m) = (1 - ‖y‖ ^ 2) / (1 + ‖y‖ ^ 2) := by
  simp only [stereoInv]
  rw [snocLp_ofLp_last]

lemma strip_stereoInv (y : EuclideanSpace ℝ (Fin m)) :
    strip (stereoInv y) = (2 / (1 + ‖y‖ ^ 2)) • y := by
  simp only [stereoInv]
  rw [strip_snocLp]

lemma stereoInv_norm (y : EuclideanSpace ℝ (Fin m)) : ‖stereoInv y‖ = 1 := by
  have h : ‖stereoInv y‖ ^ 2 = 1 := by
    simp only [stereoInv]
    rw [snocLp_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hd : (1 + ‖y‖ ^ 2) ≠ 0 := by positivity
    field_simp; ring
  rw [← Real.sqrt_sq (norm_nonneg (stereoInv y)), h, Real.sqrt_one]

lemma stereoFwd_stereoInv (y : EuclideanSpace ℝ (Fin m)) : stereoFwd (stereoInv y) = y := by
  have hden : 1 + (stereoInv y).ofLp (Fin.last m) = 2 / (1 + ‖y‖ ^ 2) := by
    rw [stereoInv_last]
    field_simp; ring
  unfold stereoFwd
  rw [strip_stereoInv, hden]
  rw [show (1 / (2 / (1 + ‖y‖ ^ 2))) • ((2 / (1 + ‖y‖ ^ 2)) • y) = y by
    rw [smul_smul,
      show 1 / (2 / (1 + ‖y‖ ^ 2)) * (2 / (1 + ‖y‖ ^ 2)) = 1 by field_simp, one_smul]]

lemma stereoInv_stereoFwd (x : EuclideanSpace ℝ (Fin (m + 1))) (hx : ‖x‖ = 1)
    (hu : x.ofLp (Fin.last m) > -1) : stereoInv (stereoFwd x) = x := by
  set u := x.ofLp (Fin.last m) with hu'
  have hu1 : (1 : ℝ) + u ≠ 0 := by linarith
  have hstrip : ‖strip x‖ ^ 2 = 1 - u ^ 2 := by
    have h := snocLp_norm_sq (strip x) (x.ofLp (Fin.last m))
    rw [snocLp_strip, hx] at h
    rw [← hu'] at h
    linarith
  have hnorm : ‖stereoFwd x‖ ^ 2 = (1 - u ^ 2) / (1 + u) ^ 2 := by
    unfold stereoFwd
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hstrip, ← hu']
    field_simp
  have hstep1 : 1 + ‖stereoFwd x‖ ^ 2 = 2 / (1 + u) := by
    rw [hnorm]; field_simp; ring
  have hstep2 : 1 - ‖stereoFwd x‖ ^ 2 = 2 * u / (1 + u) := by
    rw [hnorm]; field_simp; ring
  have hcoef : 2 / (1 + ‖stereoFwd x‖ ^ 2) = 1 + u := by
    rw [hstep1]; field_simp
  have hlast : (1 - ‖stereoFwd x‖ ^ 2) / (1 + ‖stereoFwd x‖ ^ 2) = u := by
    rw [hstep2, hstep1]; field_simp
  have hsm : (1 + u) • stereoFwd x = strip x := by
    unfold stereoFwd
    rw [smul_smul, show (1 + u) * (1 / (1 + u)) = 1 by field_simp, one_smul]
  unfold stereoInv
  rw [hcoef, hlast, hsm, hu', snocLp_strip]

lemma stereoFwd_norm_sq (x : EuclideanSpace ℝ (Fin (m + 1))) (hx : ‖x‖ = 1) :
    ‖stereoFwd x‖ ^ 2 = (1 - x.ofLp (Fin.last m)) / (1 + x.ofLp (Fin.last m)) := by
  set u := x.ofLp (Fin.last m) with hu'
  have hstrip : ‖strip x‖ ^ 2 = 1 - u ^ 2 := by
    have h := snocLp_norm_sq (strip x) (x.ofLp (Fin.last m))
    rw [snocLp_strip, hx] at h
    rw [← hu'] at h
    linarith
  have hc : ‖stereoFwd x‖ ^ 2 = (1 / (1 + u)) ^ 2 * (1 - u ^ 2) := by
    simp only [stereoFwd]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hstrip]
  rw [hc, show (1 - u ^ 2) = (1 - u) * (1 + u) by ring]
  by_cases h : (1 + u) = 0
  · simp [h]
  · field_simp

/-- The continuous (globally defined) inverse map. -/
lemma continuous_stereoInv : Continuous (stereoInv (m := m)) := by
  have hden : Continuous (fun y : EuclideanSpace ℝ (Fin m) => (1 + ‖y‖ ^ 2 : ℝ)) := by fun_prop
  have hnum : Continuous (fun y : EuclideanSpace ℝ (Fin m) => (1 - ‖y‖ ^ 2 : ℝ)) := by fun_prop
  have hne : ∀ y : EuclideanSpace ℝ (Fin m), (1 + ‖y‖ ^ 2 : ℝ) ≠ 0 := fun y => by positivity
  have h : Continuous (fun y : EuclideanSpace ℝ (Fin m) =>
      ((2 / (1 + ‖y‖ ^ 2)) • y, (1 - ‖y‖ ^ 2) / (1 + ‖y‖ ^ 2))) := by
    refine Continuous.prodMk ?_ ?_
    · exact Continuous.smul (Continuous.div continuous_const hden hne) continuous_id
    · exact Continuous.div hnum hden hne
  unfold stereoInv
  exact continuous_snocLp.comp h

/-- `stereoFwd` maps the cap into its target region. -/
lemma stereoFwd_mem {ε : ℝ} (h1 : ε ≤ 1) (x : EuclideanSpace ℝ (Fin (m + 1)))
    (hx : ‖x‖ = 1) (hu : x.ofLp (Fin.last m) > -ε) : stereoFwd x ∈ tgtSet ε := by
  simp only [tgtSet, Set.mem_ofPred_eq]
  have hpos : (0 : ℝ) < 1 + x.ofLp (Fin.last m) := by linarith
  rw [stereoFwd_norm_sq x hx, ← mul_div_assoc, div_lt_iff₀ hpos]
  nlinarith [hu]

/-- `stereoInv` maps the target region into the cap. -/
lemma stereoInv_mem {ε : ℝ} (y : EuclideanSpace ℝ (Fin m)) (hy : y ∈ tgtSet ε) :
    stereoInv y ∈ capSet (m := m) ε := by
  simp only [tgtSet, Set.mem_ofPred_eq] at hy
  simp only [capSet, Set.mem_ofPred_eq]
  refine ⟨stereoInv_norm y, ?_⟩
  rw [stereoInv_last]
  have hpos : (0 : ℝ) < 1 + ‖y‖ ^ 2 := by positivity
  rw [gt_iff_lt, lt_div_iff₀ hpos]
  nlinarith [hy]

/-- `stereoFwd` is continuous on the cap (where its denominator does not vanish). -/
lemma continuousOn_stereoFwd {ε : ℝ} (h1 : ε ≤ 1) :
    ContinuousOn (stereoFwd (m := m)) (capSet ε) := by
  have hden : Continuous (fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
      (1 + x.ofLp (Fin.last m) : ℝ)) := by fun_prop
  have hzero : ∀ x ∈ capSet (m := m) ε, (1 + x.ofLp (Fin.last m) : ℝ) ≠ 0 := by
    intro x hx
    have h := hx.2
    linarith
  have hdiv : ContinuousOn (fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
      1 / (1 + x.ofLp (Fin.last m))) (capSet (m := m) ε) :=
    ContinuousOn.div continuousOn_const hden.continuousOn hzero
  have hstrip : ContinuousOn (fun x : EuclideanSpace ℝ (Fin (m + 1)) => strip x)
      (capSet (m := m) ε) :=
    continuous_strip.continuousOn
  unfold stereoFwd
  exact hdiv.smul hstrip

/-- The target region `{(1-ε)‖y‖² < 1+ε}` is convex when `ε ≤ 1` (it is an open ball for
`ε < 1` and the whole space for `ε = 1`). -/
lemma tgtSet_convex {ε : ℝ} (h1 : ε ≤ 1) : Convex ℝ (tgtSet (m := m) ε) := by
  intro y hy z hz a b ha hb hab
  simp only [tgtSet, Set.mem_ofPred_eq] at hy hz ⊢
  have hle : (0 : ℝ) ≤ 1 - ε := by linarith
  set X := ‖y‖ with hX
  set Z := ‖z‖ with hZ
  set N := ‖a • y + b • z‖ with hN
  have hX0 : 0 ≤ X := by rw [hX]; exact norm_nonneg _
  have hZ0 : 0 ≤ Z := by rw [hZ]; exact norm_nonneg _
  have hN0 : 0 ≤ N := by rw [hN]; exact norm_nonneg _
  have hNle : N ≤ a * X + b * Z := by
    rw [hN, hX, hZ]
    calc ‖a • y + b • z‖ ≤ ‖a • y‖ + ‖b • z‖ := norm_add_le _ _
      _ = a * ‖y‖ + b * ‖z‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
  have hAX0 : 0 ≤ a * X + b * Z := by nlinarith [ha, hb, hX0, hZ0]
  have hsq1 : N ^ 2 ≤ (a * X + b * Z) ^ 2 := by nlinarith [hNle, hN0, hAX0]
  have hid : a * X ^ 2 + b * Z ^ 2 - (a * X + b * Z) ^ 2 = a * b * (X - Z) ^ 2 := by
    rw [show b = 1 - a by linarith]; ring
  have hsq2 : (a * X + b * Z) ^ 2 ≤ a * X ^ 2 + b * Z ^ 2 := by
    have h := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (X - Z))
    rw [← hid] at h
    linarith
  have hmono : (1 - ε) * N ^ 2 ≤ (1 - ε) * (a * X ^ 2 + b * Z ^ 2) :=
    mul_le_mul_of_nonneg_left (le_trans hsq1 hsq2) hle
  have hgoal : (1 - ε) * (a * X ^ 2 + b * Z ^ 2) < 1 + ε := by
    have h1x : (1 - ε) * X ^ 2 < 1 + ε := by rw [hX]; exact hy
    have h1z : (1 - ε) * Z ^ 2 < 1 + ε := by rw [hZ]; exact hz
    have e : (1 - ε) * (a * X ^ 2 + b * Z ^ 2) = a * ((1 - ε) * X ^ 2) + b * ((1 - ε) * Z ^ 2) := by
      ring
    rw [e]
    have hb_le : b * ((1 - ε) * Z ^ 2) ≤ b * (1 + ε) :=
      mul_le_mul_of_nonneg_left (le_of_lt h1z) hb
    have key : a * ((1 - ε) * X ^ 2) + b * ((1 - ε) * Z ^ 2) < a * (1 + ε) + b * (1 + ε) := by
      rcases lt_or_eq_of_le ha with ha0 | ha0
      · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left h1x ha0) hb_le
      · have hb0 : 0 < b := by linarith
        have hthis := mul_lt_mul_of_pos_left h1z hb0
        simpa [← ha0] using hthis
    have key2 : a * (1 + ε) + b * (1 + ε) = 1 + ε := by nlinarith [hab]
    rw [key2] at key
    exact key
  exact lt_of_le_of_lt hmono hgoal

end Stereo

theorem sphereCapContractible (m : ℕ) (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    ContractibleSpace {x : EuclideanSpace ℝ (Fin (m+1)) // ‖x‖ = 1 ∧ x (Fin.last m) > -ε} := by
  -- the target region is nonempty and convex, hence contractible
  have hne : (tgtSet (m := m) ε).Nonempty := by
    refine ⟨0, ?_⟩
    show (1 - ε) * ‖(0 : EuclideanSpace ℝ (Fin m))‖ ^ 2 < 1 + ε
    rw [show ‖(0 : EuclideanSpace ℝ (Fin m))‖ ^ 2 = 0 by simp, mul_zero]
    linarith
  haveI : ContractibleSpace (tgtSet (m := m) ε) :=
    (tgtSet_convex (m := m) h1).contractibleSpace hne
  -- the two stereographic maps are mutually inverse and continuous, giving a homeomorphism
  have hfwd : Continuous (fun x : capSet (m := m) ε =>
      (⟨stereoFwd x.1, stereoFwd_mem h1 x.1 x.2.1 x.2.2⟩ : tgtSet (m := m) ε)) :=
    Continuous.subtype_mk (continuousOn_stereoFwd h1).domRestrict
      (fun x => stereoFwd_mem h1 x.1 x.2.1 x.2.2)
  have hinv : Continuous (fun y : tgtSet (m := m) ε =>
      (⟨stereoInv y.1, stereoInv_mem y.1 y.2⟩ : capSet (m := m) ε)) :=
    Continuous.subtype_mk (continuous_stereoInv.comp continuous_subtype_val)
      (fun y => stereoInv_mem y.1 y.2)
  let e : (capSet (m := m) ε) ≃ (tgtSet (m := m) ε) :=
    { toFun := fun x => ⟨stereoFwd x.1, stereoFwd_mem h1 x.1 x.2.1 x.2.2⟩
      invFun := fun y => ⟨stereoInv y.1, stereoInv_mem y.1 y.2⟩
      left_inv := fun x => Subtype.ext (stereoInv_stereoFwd x.1 x.2.1 (by linarith [x.2.2, h1]))
      right_inv := fun y => Subtype.ext (stereoFwd_stereoInv y.1) }
  have he : (capSet (m := m) ε) ≃ₜ (tgtSet (m := m) ε) := Homeomorph.mk e hfwd hinv
  haveI : ContractibleSpace (capSet (m := m) ε) := he.contractibleSpace
  exact this

end

end Work.Cohomology

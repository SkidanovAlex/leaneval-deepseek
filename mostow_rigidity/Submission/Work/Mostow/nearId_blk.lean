import Mathlib
import Submission.Mostow.GeodDefs
import Submission.Work.Mostow.fermi_inv

/-!
# `nearId_blk`: near-identity two-scale criterion for the block isometry
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-! ### Coordinate splitting for the standard stratum -/

theorem nib_tanC_apply (k m : ℕ) (u : E (k + m)) (i : Fin k) :
    tanC k m u i = u (Fin.castAdd m i) := rfl

theorem nib_nrmC_apply (k m : ℕ) (u : E (k + m)) (i : Fin m) :
    nrmC k m u i = u (Fin.natAdd k i) := rfl

theorem nib_inner_split (k m : ℕ) (u u' : E (k + m)) :
    inner ℝ u u' = inner ℝ (tanC k m u) (tanC k m u') + inner ℝ (nrmC k m u) (nrmC k m u') := by
  rw [PiLp.inner_apply, PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_add]
  simp only [nib_tanC_apply, nib_nrmC_apply]

theorem nib_norm_sq_split (k m : ℕ) (u : E (k + m)) :
    ‖u‖ ^ 2 = ‖tanC k m u‖ ^ 2 + ‖nrmC k m u‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq (tanC k m u),
      EuclideanSpace.real_norm_sq_eq (nrmC k m u), Fin.sum_univ_add]
  simp only [nib_tanC_apply, nib_nrmC_apply]

/-! ### Fermi chart facts -/

theorem nib_tanC_fermi (k m : ℕ) (v : E k) (w : E m) :
    tanC k m (fermi k m v w) = Real.cosh ‖w‖ • v := by
  ext i; simp [tanC, fermi]

theorem nib_nrmC_fermi (k m : ℕ) (v : E k) (w : E m) :
    nrmC k m (fermi k m v w) = sinhc ‖w‖ • w := by
  ext i; simp [nrmC, fermi]

theorem nib_eq_of_tanC_nrmC {k m : ℕ} {u u' : E (k + m)}
    (h1 : tanC k m u = tanC k m u') (h2 : nrmC k m u = nrmC k m u') : u = u' := by
  apply WithLp.ofLp_injective
  funext j
  exact Fin.addCases (motive := fun j => WithLp.ofLp u j = WithLp.ofLp u' j)
    (fun i => by rw [← nib_tanC_apply, ← nib_tanC_apply, h1])
    (fun i => by rw [← nib_nrmC_apply, ← nib_nrmC_apply, h2]) j

theorem nib_tanC_fermiW (m : ℕ) (v : E 1) (W : E m) :
    tanC 1 m (fermiW 1 m v W) = Real.sqrt (1 + ‖W‖ ^ 2) • v := by
  ext i; simp [tanC, fermiW]

theorem nib_nrmC_fermiW (m : ℕ) (v : E 1) (W : E m) :
    nrmC 1 m (fermiW 1 m v W) = W := by
  ext i; simp [nrmC, fermiW]

/-! ### The coordinate rotation map and its isometry property -/

/-- rotate the normal coordinate by `R`, keep the tangential coordinate -/
def nib_rotMap (m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (u : E (1 + m)) : E (1 + m) :=
  WithLp.toLp 2 (Fin.append (fun i : Fin 1 => u (Fin.castAdd m i))
                             (fun j : Fin m => (R (nrmC 1 m u)) j))

theorem nib_tanC_rotMap (m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (u : E (1 + m)) :
    tanC 1 m (nib_rotMap m R u) = tanC 1 m u := by
  ext i; simp [nib_rotMap, tanC]

theorem nib_nrmC_rotMap (m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (u : E (1 + m)) :
    nrmC 1 m (nib_rotMap m R u) = R (nrmC 1 m u) := by
  ext j; simp [nib_rotMap, nrmC]

theorem nib_norm_sq_rotMap (m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (u : E (1 + m)) :
    ‖nib_rotMap m R u‖ ^ 2 = ‖u‖ ^ 2 := by
  rw [nib_norm_sq_split, nib_tanC_rotMap, nib_nrmC_rotMap, LinearIsometryEquiv.norm_map,
      ← nib_norm_sq_split]

theorem nib_norm_rotMap (m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (u : E (1 + m)) :
    ‖nib_rotMap m R u‖ = ‖u‖ := by
  have h := nib_norm_sq_rotMap m R u
  nlinarith [norm_nonneg (nib_rotMap m R u), norm_nonneg u]

theorem nib_tpart_rotMap (m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (u : E (1 + m)) :
    tpart (nib_rotMap m R u) = tpart u := by
  rw [tpart, tpart, nib_norm_rotMap]

theorem nib_inner_rotMap (m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (u u' : E (1 + m)) :
    inner ℝ (nib_rotMap m R u) (nib_rotMap m R u') = inner ℝ u u' := by
  rw [nib_inner_split, nib_inner_split]
  simp only [nib_tanC_rotMap, nib_nrmC_rotMap, LinearIsometryEquiv.inner_map_map]

theorem nib_hdist_rotMap (m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (u u' : E (1 + m)) :
    hdist (nib_rotMap m R u) (nib_rotMap m R u') = hdist u u' := by
  rw [hdist, hdist, nib_tpart_rotMap, nib_tpart_rotMap, nib_inner_rotMap]

theorem nib_exists_g (m : ℕ) (hI : HypIsometryProp (1 + m)) (R : E m ≃ₗᵢ[ℝ] E m) :
    ∃ g : PO (1 + m) 1, ∀ u : E (1 + m), g • u = nib_rotMap m R u := by
  obtain ⟨-, -, -, -, -, -, -, h8, -, -, -, -⟩ := hI
  obtain ⟨g, hg⟩ := h8 (nib_rotMap m R) (fun u v => nib_hdist_rotMap m R u v)
  exact ⟨g, fun u => (hg u).symm⟩

/-! ### The block isometry acts as the coordinate rotation -/

theorem nib_blkMap_eq_rotMap (m : ℕ) (hA1 : POActionProp 1) (R : E m ≃ₗᵢ[ℝ] E m)
    (u : E (1 + m)) : blkMap 1 m 1 R u = nib_rotMap m R u := by
  obtain ⟨-, -, -, hone, -, -, -, -, -, -, -, -⟩ := hA1
  set p : E 1 × E m := fermiInv 1 m u with hp
  have hu : fermi 1 m p.1 p.2 = u := (fermi_inv 1 m).2.1 u
  have h1 : (1 : PO 1 1) • p.1 = p.1 := hone p.1
  show fermi 1 m (1 • p.1) (R p.2) = nib_rotMap m R u
  rw [h1, ← hu]
  refine nib_eq_of_tanC_nrmC ?_ ?_
  · rw [nib_tanC_fermi, nib_tanC_rotMap, nib_tanC_fermi, LinearIsometryEquiv.norm_map]
  · rw [nib_nrmC_fermi, nib_nrmC_rotMap, nib_nrmC_fermi, LinearIsometryEquiv.map_smul,
        LinearIsometryEquiv.norm_map]

theorem nib_blk_smul_fermiW (m : ℕ) (hA1 : POActionProp 1) (hI1 : HypIsometryProp 1)
    (hA : POActionProp (1 + m)) (hI : HypIsometryProp (1 + m))
    (R : E m ≃ₗᵢ[ℝ] E m) (v : E 1) (W : E m) :
    blk 1 m 1 R • fermiW 1 m v W = fermiW 1 m v (R W) := by
  have hex : ∃ g : PO (1 + m) 1, ∀ u : E (1 + m), g • u = blkMap 1 m 1 R u := by
    obtain ⟨g, hg⟩ := nib_exists_g m hI R
    exact ⟨g, fun u => by rw [nib_blkMap_eq_rotMap m hA1 R u, hg u]⟩
  have hb : blk 1 m 1 R = hex.choose := by
    unfold blk
    exact dite_eq_left hex
  rw [hb, hex.choose_spec, nib_blkMap_eq_rotMap m hA1 R (fermiW 1 m v W)]
  refine nib_eq_of_tanC_nrmC ?_ ?_
  · rw [nib_tanC_rotMap, nib_tanC_fermiW, nib_tanC_fermiW, LinearIsometryEquiv.norm_map]
  · rw [nib_nrmC_rotMap, nib_nrmC_fermiW, nib_nrmC_fermiW]


/-! ### Elementary real-analysis bounds -/

theorem nib_cosh_one_le_two : Real.cosh 1 ≤ 2 := by
  rw [Real.cosh_eq]
  have h1 : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
  have h2 : Real.exp (-1) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by norm_num)
  linarith

theorem nib_sinh_one_le_three_halves : Real.sinh 1 ≤ 3 / 2 := by
  rw [Real.sinh_eq]
  have h1 : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
  have h2 : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  linarith

theorem nib_sinh_le_add_sq {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.sinh x ≤ x + x ^ 2 := by
  have hx : |x| ≤ 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have h1 : Real.exp x ≤ 1 + x + x ^ 2 := by
    have := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hx)).2
    linarith
  have h2 : 1 - x - x ^ 2 ≤ Real.exp (-x) := by
    have hx' : |-x| ≤ 1 := by rwa [abs_neg]
    have := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hx')).1
    linarith
  rw [Real.sinh_eq]
  linarith

theorem nib_sinh_half_le {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    Real.sinh (η / 2) ≤ 3 * η / 4 := by
  have h := nib_sinh_le_add_sq (by linarith : (0 : ℝ) ≤ η / 2) (by linarith : η / 2 ≤ 1)
  nlinarith

/-! ### The cosine of the hyperbolic distance -/

theorem nib_one_le_hdist_arg {n : ℕ} (u u' : E n) :
    1 ≤ tpart u * tpart u' - inner ℝ u u' := by
  have h1 : (1 : ℝ) + ‖u‖ * ‖u'‖
      ≤ Real.sqrt (1 + ‖u‖ ^ 2) * Real.sqrt (1 + ‖u'‖ ^ 2) := by
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 1 + ‖u‖ ^ 2)]
    rw [Real.le_sqrt (by positivity) (by positivity)]
    nlinarith [sq_nonneg (‖u‖ - ‖u'‖)]
  have h2 : inner ℝ u u' ≤ ‖u‖ * ‖u'‖ := real_inner_le_norm u u'
  rw [tpart, tpart]
  linarith

theorem nib_hdist_nonneg {n : ℕ} (u u' : E n) : 0 ≤ hdist u u' :=
  Real.arcosh_nonneg (nib_one_le_hdist_arg u u')

theorem nib_cosh_hdist {n : ℕ} (u u' : E n) :
    Real.cosh (hdist u u') = tpart u * tpart u' - inner ℝ u u' := by
  rw [hdist, Real.cosh_arcosh (nib_one_le_hdist_arg u u')]

theorem nib_hdist_self {n : ℕ} (u : E n) : hdist u u = 0 := by
  rw [hdist, tpart, real_inner_self_eq_norm_sq, ← sq, Real.sq_sqrt (by positivity)]
  ring_nf
  rw [Real.arcosh_zero]

theorem nib_hdist_le_one_le {n : ℕ} (u u' : E n) (h : hdist u u' ≤ 1) :
    tpart u * tpart u' - inner ℝ u u' ≤ Real.cosh 1 := by
  rw [← nib_cosh_hdist u u', Real.cosh_le_cosh,
      abs_of_nonneg (nib_hdist_nonneg u u'), abs_one]
  exact h

/-! ### Fermi coordinate formulas for `fermiW` -/

theorem nib_norm_sq_fermiW (m : ℕ) (v : E 1) (W : E m) :
    ‖fermiW 1 m v W‖ ^ 2 = (1 + ‖W‖ ^ 2) * ‖v‖ ^ 2 + ‖W‖ ^ 2 := by
  rw [nib_norm_sq_split 1 m (fermiW 1 m v W), nib_tanC_fermiW, nib_nrmC_fermiW, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (by positivity)]

theorem nib_tpart_fermiW (m : ℕ) (v : E 1) (W : E m) :
    tpart (fermiW 1 m v W) = Real.sqrt (1 + ‖W‖ ^ 2) * tpart v := by
  rw [tpart, tpart, nib_norm_sq_fermiW]
  have h : 1 + ((1 + ‖W‖ ^ 2) * ‖v‖ ^ 2 + ‖W‖ ^ 2)
      = (1 + ‖W‖ ^ 2) * (1 + ‖v‖ ^ 2) := by ring
  rw [h, Real.sqrt_mul (by positivity)]

theorem nib_inner_fermiW (m : ℕ) (v v' : E 1) (W W' : E m) :
    inner ℝ (fermiW 1 m v W) (fermiW 1 m v' W')
      = Real.sqrt (1 + ‖W‖ ^ 2) * Real.sqrt (1 + ‖W'‖ ^ 2) * inner ℝ v v'
        + inner ℝ W W' := by
  rw [nib_inner_split, nib_tanC_fermiW, nib_nrmC_fermiW, nib_tanC_fermiW, nib_nrmC_fermiW,
      real_inner_smul_left, real_inner_smul_right]
  ring

theorem nib_cosh_hdist_fermiW (m : ℕ) (v v' : E 1) (W W' : E m) :
    Real.cosh (hdist (fermiW 1 m v W) (fermiW 1 m v' W'))
      = Real.sqrt (1 + ‖W‖ ^ 2) * Real.sqrt (1 + ‖W'‖ ^ 2) * Real.cosh (hdist v v')
        - inner ℝ W W' := by
  rw [nib_cosh_hdist (fermiW 1 m v W) (fermiW 1 m v' W'), nib_tpart_fermiW, nib_tpart_fermiW,
      nib_inner_fermiW, nib_cosh_hdist v v']
  ring

theorem nib_cosh_hdist_fermiW_le (m : ℕ) (v : E 1) (W W' : E m) :
    Real.cosh (hdist (fermiW 1 m v W) (fermiW 1 m v W')) ≤ 1 + ‖W - W'‖ ^ 2 / 2 := by
  rw [nib_cosh_hdist_fermiW, nib_cosh_hdist v v, tpart, real_inner_self_eq_norm_sq]
  have h1 : Real.sqrt (1 + ‖v‖ ^ 2) * Real.sqrt (1 + ‖v‖ ^ 2) - ‖v‖ ^ 2 = 1 := by
    rw [← sq, Real.sq_sqrt (by positivity)]
    ring
  rw [h1, mul_one]
  have h2 : 2 * (Real.sqrt (1 + ‖W‖ ^ 2) * Real.sqrt (1 + ‖W'‖ ^ 2))
      - ‖W‖ ^ 2 - ‖W'‖ ^ 2 ≤ 2 := by
    have ha : Real.sqrt (1 + ‖W‖ ^ 2) ^ 2 = 1 + ‖W‖ ^ 2 := Real.sq_sqrt (by positivity)
    have hb : Real.sqrt (1 + ‖W'‖ ^ 2) ^ 2 = 1 + ‖W'‖ ^ 2 := Real.sq_sqrt (by positivity)
    nlinarith [sq_nonneg (Real.sqrt (1 + ‖W‖ ^ 2) - Real.sqrt (1 + ‖W'‖ ^ 2))]
  have h3 : ‖W - W'‖ ^ 2 = ‖W‖ ^ 2 - 2 * inner ℝ W W' + ‖W'‖ ^ 2 := norm_sub_sq_real W W'
  linarith

/-- for points at normal distance `≤ 2 sinh(1/2)` from `fermiW v W`, the distance is `≤ 1` -/
theorem nib_hdist_spread (m : ℕ) (v : E 1) (W W' : E m)
    (h : ‖W - W'‖ ≤ 2 * Real.sinh (1 / 2)) :
    hdist (fermiW 1 m v W) (fermiW 1 m v W') ≤ 1 := by
  have hs : 0 ≤ Real.sinh (1 / 2) := Real.sinh_nonneg_iff.mpr (by norm_num)
  have hcosh : Real.cosh (hdist (fermiW 1 m v W) (fermiW 1 m v W')) ≤ Real.cosh 1 := by
    refine le_trans (nib_cosh_hdist_fermiW_le m v W W') ?_
    have hc : Real.cosh 1 = 1 + 2 * Real.sinh (1 / 2) ^ 2 := by
      have h2 := Real.cosh_two_mul (1 / 2)
      rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num] at h2
      rw [h2, Real.cosh_sq]
      ring
    have hsq : ‖W - W'‖ ^ 2 ≤ (2 * Real.sinh (1 / 2)) ^ 2 := by
      simpa [pow_two] using mul_self_le_mul_self (norm_nonneg _) h
    rw [hc]
    nlinarith [hsq]
  rw [Real.cosh_le_cosh, abs_of_nonneg (nib_hdist_nonneg _ _), abs_one] at hcosh
  exact hcosh

/-! ### The displacement of the block isometry -/

theorem nib_cosh_hdist_blk (m : ℕ) (hA1 : POActionProp 1) (hI1 : HypIsometryProp 1)
    (hA : POActionProp (1 + m)) (hI : HypIsometryProp (1 + m))
    (R : E m ≃ₗᵢ[ℝ] E m) (v : E 1) (W : E m) :
    Real.cosh (hdist (fermiW 1 m v W) (blk 1 m 1 R • fermiW 1 m v W))
      = 1 + ‖R W - W‖ ^ 2 / 2 := by
  rw [nib_blk_smul_fermiW m hA1 hI1 hA hI R v W]
  rw [nib_cosh_hdist_fermiW, LinearIsometryEquiv.norm_map, nib_cosh_hdist v v, tpart,
      real_inner_self_eq_norm_sq]
  have h1 : Real.sqrt (1 + ‖v‖ ^ 2) * Real.sqrt (1 + ‖v‖ ^ 2) - ‖v‖ ^ 2 = 1 := by
    rw [← sq, Real.sq_sqrt (by positivity)]
    ring
  have h3 : Real.sqrt (1 + ‖W‖ ^ 2) * Real.sqrt (1 + ‖W‖ ^ 2) = 1 + ‖W‖ ^ 2 := by
    rw [← sq, Real.sq_sqrt (by positivity)]
  have h2 : ‖R W - W‖ ^ 2 = 2 * ‖W‖ ^ 2 - 2 * inner ℝ W (R W) := by
    rw [norm_sub_sq_real, LinearIsometryEquiv.norm_map, real_inner_comm]
    ring
  rw [h1, mul_one, h3, h2]
  ring

theorem nib_hdist_blk_le_disp (m : ℕ) (hA1 : POActionProp 1) (hI1 : HypIsometryProp 1)
    (hA : POActionProp (1 + m)) (hI : HypIsometryProp (1 + m))
    (R : E m ≃ₗᵢ[ℝ] E m) (v : E 1) (W : E m) :
    hdist (fermiW 1 m v W) (blk 1 m 1 R • fermiW 1 m v W) ≤ ‖R W - W‖ := by
  set D := hdist (fermiW 1 m v W) (blk 1 m 1 R • fermiW 1 m v W) with hD
  have hcosh := nib_cosh_hdist_blk m hA1 hI1 hA hI R v W
  have hDnn : 0 ≤ D := by rw [hD]; exact nib_hdist_nonneg _ _
  have hsinh : Real.sinh (D / 2) = ‖R W - W‖ / 2 := by
    have h1 : Real.cosh D = 1 + 2 * Real.sinh (D / 2) ^ 2 := by
      have h := Real.cosh_two_mul (D / 2)
      rw [show (2 : ℝ) * (D / 2) = D by ring] at h
      rw [h, Real.cosh_sq]
      ring
    have h2 : Real.cosh D = 1 + ‖R W - W‖ ^ 2 / 2 := by rw [hD]; exact hcosh
    have h3 : Real.sinh (D / 2) ^ 2 = (‖R W - W‖ / 2) ^ 2 := by nlinarith [h1, h2]
    have h4 : (Real.sinh (D / 2) - ‖R W - W‖ / 2)
        * (Real.sinh (D / 2) + ‖R W - W‖ / 2) = 0 := by nlinarith [h3]
    rcases mul_eq_zero.mp h4 with h5 | h5
    · linarith
    · have hs : 0 ≤ Real.sinh (D / 2) := Real.sinh_nonneg_iff.mpr (by linarith : 0 ≤ D / 2)
      have hx : 0 ≤ ‖R W - W‖ / 2 := by positivity
      linarith
  have h5 : D / 2 ≤ Real.sinh (D / 2) := Real.self_le_sinh_iff.mpr (by linarith)
  rw [hsinh] at h5
  linarith

theorem nib_disp_lt_of_hdist_lt (m : ℕ) (hA1 : POActionProp 1) (hI1 : HypIsometryProp 1)
    (hA : POActionProp (1 + m)) (hI : HypIsometryProp (1 + m))
    (R : E m ≃ₗᵢ[ℝ] E m) (v : E 1) (W : E m) (η : ℝ)
    (hη : hdist (fermiW 1 m v W) (blk 1 m 1 R • fermiW 1 m v W) < η) :
    ‖R W - W‖ < 2 * Real.sinh (η / 2) := by
  have hDnn : 0 ≤ hdist (fermiW 1 m v W) (blk 1 m 1 R • fermiW 1 m v W) :=
    nib_hdist_nonneg _ _
  have hηpos : 0 < η := lt_of_le_of_lt hDnn hη
  have hcosh : Real.cosh (hdist (fermiW 1 m v W) (blk 1 m 1 R • fermiW 1 m v W))
      < Real.cosh η := by
    rw [Real.cosh_lt_cosh]
    rwa [abs_of_nonneg hDnn, abs_of_pos hηpos]
  rw [nib_cosh_hdist_blk m hA1 hI1 hA hI R v W] at hcosh
  have hcosh2 : Real.cosh η = 1 + 2 * Real.sinh (η / 2) ^ 2 := by
    have h2 := Real.cosh_two_mul (η / 2)
    rw [show (2 : ℝ) * (η / 2) = η by ring] at h2
    rw [h2, Real.cosh_sq]
    ring
  rw [hcosh2] at hcosh
  have hx : ‖R W - W‖ ^ 2 < (2 * Real.sinh (η / 2)) ^ 2 := by nlinarith [hcosh]
  have hS : 0 ≤ 2 * Real.sinh (η / 2) := by
    have : 0 ≤ η / 2 := by linarith
    have := Real.sinh_nonneg_iff.mpr this
    linarith
  have h4 := sq_lt_sq.mp hx
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hS] at h4

/-! ### Operator-norm bounds from pointwise ones -/

theorem nib_apply_le_rotN (m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (y : E m) :
    ‖R y - y‖ ≤ rotN R * ‖y‖ := by
  have h := ContinuousLinearMap.le_opNorm
    ((R.toLinearIsometry.toContinuousLinearMap : E m →L[ℝ] E m)
      - ContinuousLinearMap.id ℝ (E m)) y
  simpa [sub_apply, ContinuousLinearMap.id_apply, rotN] using h

theorem nib_rotN_le_of_unit {m : ℕ} {R : E m ≃ₗᵢ[ℝ] E m} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ y : E m, ‖y‖ = 1 → ‖R y - y‖ ≤ K) : rotN R ≤ K := by
  have hmain : ∀ y : E m, ‖((R.toLinearIsometry.toContinuousLinearMap : E m →L[ℝ] E m)
      - ContinuousLinearMap.id ℝ (E m)) y‖ ≤ K * ‖y‖ := by
    intro y
    rw [show ((R.toLinearIsometry.toContinuousLinearMap : E m →L[ℝ] E m)
          - ContinuousLinearMap.id ℝ (E m)) y = R y - y by
      simp [sub_apply, ContinuousLinearMap.id_apply]]
    rcases eq_or_lt_of_le (norm_nonneg y) with hy | hy
    · have hy0 : y = 0 := norm_eq_zero.mp hy.symm
      subst hy0
      simp
    · have hyunit : ‖(‖y‖⁻¹ : ℝ) • y‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hy), inv_mul_cancel₀ hy.ne']
      have h1 := h ((‖y‖⁻¹ : ℝ) • y) hyunit
      have h2 : R ((‖y‖⁻¹ : ℝ) • y) - (‖y‖⁻¹ : ℝ) • y = (‖y‖⁻¹ : ℝ) • (R y - y) := by
        rw [map_smul, smul_sub]
      rw [h2, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hy)] at h1
      calc ‖R y - y‖ = ‖y‖ * (‖y‖⁻¹ * ‖R y - y‖) := by
            rw [← mul_assoc, mul_inv_cancel₀ hy.ne', one_mul]
        _ ≤ ‖y‖ * K := mul_le_mul_of_nonneg_left h1 (norm_nonneg y)
        _ = K * ‖y‖ := by ring
  rw [rotN]
  exact ContinuousLinearMap.opNorm_le_bound _ hK hmain

/-! ### The key numerical estimate -/

theorem nib_key_bound {A p q : ℝ} (hA : 0 ≤ A) (hq : 0 ≤ q)
    (h : (p - Real.cosh 1 * A) ^ 2 + (1 + A ^ 2) * q ^ 2
      ≤ (1 + A ^ 2) * Real.sinh 1 ^ 2) :
    |p| / max A 1 + q ≤ 6 := by
  have hpos : (0 : ℝ) < 1 + A ^ 2 := by positivity
  have hs1 : 0 ≤ Real.sinh 1 := Real.sinh_nonneg_iff.mpr (by norm_num)
  have hq2 : q ^ 2 ≤ (Real.sinh 1) ^ 2 := by
    have h1 : (1 + A ^ 2) * q ^ 2 ≤ (1 + A ^ 2) * (Real.sinh 1) ^ 2 := by
      nlinarith [sq_nonneg (p - Real.cosh 1 * A), h]
    exact le_of_mul_le_mul_left h1 hpos
  have hqs : q ≤ Real.sinh 1 := by nlinarith [hq2, hs1, hq]
  have hp2 : (p - Real.cosh 1 * A) ^ 2 ≤ (1 + A ^ 2) * (Real.sinh 1) ^ 2 := by
    nlinarith [sq_nonneg q, h]
  have hpabs : |p - Real.cosh 1 * A| ≤ Real.sqrt (1 + A ^ 2) * Real.sinh 1 := by
    calc |p - Real.cosh 1 * A| = Real.sqrt ((p - Real.cosh 1 * A) ^ 2) := by
          rw [Real.sqrt_sq_eq_abs]
      _ ≤ Real.sqrt ((1 + A ^ 2) * (Real.sinh 1) ^ 2) := Real.sqrt_le_sqrt hp2
      _ = Real.sqrt (1 + A ^ 2) * Real.sinh 1 := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hs1]
  have hp_le : |p| ≤ Real.cosh 1 * A + Real.sqrt (1 + A ^ 2) * Real.sinh 1 := by
    have h1 : |p| ≤ |p - Real.cosh 1 * A| + |Real.cosh 1 * A| := by
      calc |p| = |(p - Real.cosh 1 * A) + Real.cosh 1 * A| := by congr 1; ring
        _ ≤ |p - Real.cosh 1 * A| + |Real.cosh 1 * A| := abs_add_le _ _
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.cosh 1 * A)] at h1
    linarith
  have hmaxpos : 0 < max A 1 := lt_of_lt_of_le one_pos (le_max_right A 1)
  have hsqrt_le : Real.sqrt (1 + A ^ 2) ≤ Real.sqrt 2 * max A 1 := by
    rcases le_total 1 A with h1 | h1
    · have h2 : 1 + A ^ 2 ≤ 2 * (max A 1) ^ 2 := by
        rw [max_eq_left h1]; nlinarith
      have h3 := Real.sqrt_le_sqrt h2
      rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq (by norm_num)] at h3
    · have h2 : 1 + A ^ 2 ≤ 2 * (max A 1) ^ 2 := by
        rw [max_eq_right h1]; nlinarith [hA]
      have h3 := Real.sqrt_le_sqrt h2
      rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq (by norm_num)] at h3
  have hb1 : |p| / max A 1 ≤ Real.cosh 1 + Real.sqrt 2 * Real.sinh 1 := by
    rw [div_le_iff₀ hmaxpos]
    have h4 : Real.cosh 1 * A ≤ Real.cosh 1 * max A 1 :=
      mul_le_mul_of_nonneg_left (le_max_left A 1) (le_of_lt (Real.cosh_pos 1))
    have h5 : Real.sqrt (1 + A ^ 2) * Real.sinh 1
        ≤ (Real.sqrt 2 * max A 1) * Real.sinh 1 :=
      mul_le_mul_of_nonneg_right hsqrt_le hs1
    calc |p| ≤ Real.cosh 1 * A + Real.sqrt (1 + A ^ 2) * Real.sinh 1 := hp_le
      _ ≤ Real.cosh 1 * max A 1 + (Real.sqrt 2 * max A 1) * Real.sinh 1 := by linarith
      _ = (Real.cosh 1 + Real.sqrt 2 * Real.sinh 1) * max A 1 := by ring
  have hc2 : Real.cosh 1 ≤ 2 := nib_cosh_one_le_two
  have hs2 : Real.sinh 1 ≤ 3 / 2 := nib_sinh_one_le_three_halves
  have hr2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hfinal : Real.cosh 1 + Real.sqrt 2 * Real.sinh 1 + Real.sinh 1 ≤ 6 := by
    nlinarith [hc2, hs2, hr2, hs1, Real.sqrt_nonneg 2]
  linarith

/-! ### Decomposing a point of `E (1+m)` in `fermiW` coordinates -/

theorem nib_fermiW_surj (m : ℕ) (u : E (1 + m)) :
    fermiW 1 m ((Real.sqrt (1 + ‖nrmC 1 m u‖ ^ 2))⁻¹ • tanC 1 m u) (nrmC 1 m u) = u := by
  refine nib_eq_of_tanC_nrmC ?_ ?_
  · rw [nib_tanC_fermiW, smul_smul,
        mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos_of_pos (by positivity))), one_smul]
  · rw [nib_nrmC_fermiW]

/-! ### The displacement bound (part (a) of the target) -/

theorem nib_disp_bound (m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (v v' : E 1) (W W' : E m) (c : ℝ)
    (hc : 0 ≤ c) (hrot : rotN R ≤ c) (hd : ‖R W - W‖ ≤ c)
    (hh : hdist (fermiW 1 m v W) (fermiW 1 m v' W') ≤ 1) :
    ‖R W' - W'‖ ≤ 6 * c := by
  have hXle := nib_hdist_le_one_le (fermiW 1 m v W) (fermiW 1 m v' W') hh
  rw [nib_tpart_fermiW, nib_tpart_fermiW, nib_inner_fermiW] at hXle
  have hrr : (Real.sqrt (1 + ‖W‖ ^ 2) * tpart v) * (Real.sqrt (1 + ‖W'‖ ^ 2) * tpart v')
      - (Real.sqrt (1 + ‖W‖ ^ 2) * Real.sqrt (1 + ‖W'‖ ^ 2) * inner ℝ v v'
        + inner ℝ W W')
      = Real.sqrt (1 + ‖W‖ ^ 2) * Real.sqrt (1 + ‖W'‖ ^ 2)
          * (tpart v * tpart v' - inner ℝ v v') - inner ℝ W W' := by ring
  rw [hrr, ← nib_cosh_hdist v v'] at hXle
  have hAB : Real.sqrt (1 + ‖W‖ ^ 2) * Real.sqrt (1 + ‖W'‖ ^ 2) - inner ℝ W W'
      ≤ Real.cosh 1 := by
    have hcosh1 : (1 : ℝ) ≤ Real.cosh (hdist v v') := Real.one_le_cosh _
    have hnn : 0 ≤ Real.sqrt (1 + ‖W‖ ^ 2) * Real.sqrt (1 + ‖W'‖ ^ 2) := by positivity
    have h3 : Real.sqrt (1 + ‖W‖ ^ 2) * Real.sqrt (1 + ‖W'‖ ^ 2) * 1
        ≤ Real.sqrt (1 + ‖W‖ ^ 2) * Real.sqrt (1 + ‖W'‖ ^ 2) * Real.cosh (hdist v v') :=
      mul_le_mul_of_nonneg_left hcosh1 hnn
    linarith
  rcases eq_or_lt_of_le (norm_nonneg W) with hW0 | hWpos
  · have hW : W = 0 := norm_eq_zero.mp hW0.symm
    subst hW
    have hb : ‖W'‖ ≤ Real.sinh 1 := by
      have h1 : Real.sqrt (1 + ‖W'‖ ^ 2) ≤ Real.cosh 1 := by
        have h := hAB
        rw [norm_zero, inner_zero_left] at h
        simpa using h
      have h2 : 1 + ‖W'‖ ^ 2 ≤ (Real.cosh 1) ^ 2 := (Real.sqrt_le_iff.mp h1).2
      have h3 : (Real.cosh 1) ^ 2 = (Real.sinh 1) ^ 2 + 1 := Real.cosh_sq 1
      nlinarith [h2, h3, Real.sinh_nonneg_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)]
    calc ‖R W' - W'‖ ≤ rotN R * ‖W'‖ := nib_apply_le_rotN m R W'
      _ ≤ c * Real.sinh 1 := mul_le_mul hrot hb (norm_nonneg W') hc
      _ ≤ 6 * c := by
            have hs : Real.sinh 1 ≤ 6 := by linarith [nib_sinh_one_le_three_halves]
            nlinarith [hc, hs]
  · set A : ℝ := ‖W‖ with hA
    have hApos : 0 < A := hWpos
    set Wd : E m := A⁻¹ • W with hWd
    have hWdnorm : ‖Wd‖ = 1 := by
      rw [hWd, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hApos), hA,
          inv_mul_cancel₀ hApos.ne']
    set p : ℝ := inner ℝ Wd W' with hp
    set Z : E m := W' - p • Wd with hZ
    have hqnn : 0 ≤ ‖Z‖ := norm_nonneg _
    have hWdecomp : W = A • Wd := by
      rw [hWd, smul_smul, mul_inv_cancel₀ hApos.ne', one_smul]
    have hinnerWW' : inner ℝ W W' = A * p := by
      rw [hWdecomp, real_inner_smul_left, hp]
    have hZperp : inner ℝ Wd Z = 0 := by
      rw [hZ, inner_sub_right, hp, real_inner_smul_right, real_inner_self_eq_norm_sq, hWdnorm]
      ring
    have hW'nrm : ‖W'‖ ^ 2 = p ^ 2 + ‖Z‖ ^ 2 := by
      have h1 : W' = p • Wd + Z := by rw [hZ]; abel
      have hcross : inner ℝ (p • Wd) Z = 0 := by rw [real_inner_smul_left, hZperp, mul_zero]
      rw [h1, norm_add_sq_real, hcross, norm_smul, Real.norm_eq_abs, hWdnorm, mul_one, sq_abs]
      ring
    have hAB' : Real.sqrt (1 + A ^ 2) * Real.sqrt (1 + ‖W'‖ ^ 2) - A * p ≤ Real.cosh 1 := by
      rw [hA, ← hinnerWW']
      exact hAB
    have hH' : (p - Real.cosh 1 * A) ^ 2 + (1 + A ^ 2) * ‖Z‖ ^ 2
        ≤ (1 + A ^ 2) * Real.sinh 1 ^ 2 := by
      have hle : Real.sqrt (1 + A ^ 2) * Real.sqrt (1 + ‖W'‖ ^ 2) ≤ Real.cosh 1 + A * p := by
        linarith
      have hsq : (Real.sqrt (1 + A ^ 2) * Real.sqrt (1 + ‖W'‖ ^ 2)) ^ 2
          ≤ (Real.cosh 1 + A * p) ^ 2 := by
        have h0 : (0 : ℝ) ≤ Real.sqrt (1 + A ^ 2) * Real.sqrt (1 + ‖W'‖ ^ 2) := by positivity
        simpa [pow_two] using mul_self_le_mul_self h0 hle
      rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), hW'nrm] at hsq
      nlinarith [hsq, Real.cosh_sq 1]
    have hkey := nib_key_bound (le_of_lt hApos) hqnn hH'
    have hdecomp : R W' - W' = p • (R Wd - Wd) + (R Z - Z) := by
      have h1 : W' = p • Wd + Z := by rw [hZ]; abel
      conv_lhs => rw [h1]
      rw [map_add, map_smul]
      module
    have hWd_le : ‖R Wd - Wd‖ ≤ c / max A 1 := by
      rcases le_total 1 A with hA1 | hA1
      · have hmax : max A 1 = A := max_eq_left hA1
        have h1 : R Wd - Wd = A⁻¹ • (R W - W) := by
          rw [hWd, map_smul, ← smul_sub]
        rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hApos), hmax]
        calc A⁻¹ * ‖R W - W‖ ≤ A⁻¹ * c := mul_le_mul_of_nonneg_left hd (by positivity)
          _ = c / A := by rw [div_eq_mul_inv, mul_comm]
      · have hmax : max A 1 = 1 := max_eq_right hA1
        rw [hmax, div_one]
        calc ‖R Wd - Wd‖ ≤ rotN R * ‖Wd‖ := nib_apply_le_rotN m R Wd
          _ = rotN R := by rw [hWdnorm, mul_one]
          _ ≤ c := hrot
    have hZ_le : ‖R Z - Z‖ ≤ c * ‖Z‖ :=
      le_trans (nib_apply_le_rotN m R Z) (mul_le_mul_of_nonneg_right hrot hqnn)
    rw [hdecomp]
    calc ‖p • (R Wd - Wd) + (R Z - Z)‖
        ≤ ‖p • (R Wd - Wd)‖ + ‖R Z - Z‖ := norm_add_le _ _
      _ = |p| * ‖R Wd - Wd‖ + ‖R Z - Z‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |p| * (c / max A 1) + c * ‖Z‖ := by
            have := mul_le_mul_of_nonneg_left hWd_le (abs_nonneg p)
            linarith
      _ = (|p| / max A 1 + ‖Z‖) * c := by ring
      _ ≤ 6 * c := mul_le_mul_of_nonneg_right hkey hc

theorem nib_nearId_blk_aux (m : ℕ) (hA1 : POActionProp 1) (hI1 : HypIsometryProp 1)
    (hA : POActionProp (1 + m)) (hI : HypIsometryProp (1 + m))
    (R : E m ≃ₗᵢ[ℝ] E m) (v v' : E 1) (W W' : E m) (c η : ℝ)
    (hc : 0 ≤ c) (hrot : rotN R ≤ c) (hd : ‖R W - W‖ ≤ c) (h10 : 10 * c < η)
    (hh : hdist (fermiW 1 m v W) (fermiW 1 m v' W') ≤ 1) :
    hdist (fermiW 1 m v' W') (blk 1 m 1 R • fermiW 1 m v' W') < η := by
  have hdisp := nib_disp_bound m R v v' W W' c hc hrot hd hh
  have hle : hdist (fermiW 1 m v' W') (blk 1 m 1 R • fermiW 1 m v' W') ≤ ‖R W' - W'‖ :=
    nib_hdist_blk_le_disp m hA1 hI1 hA hI R v' W'
  have h6 : 6 * c < η := by linarith
  linarith

end

theorem nearId_blk (m : ℕ) (hA1 : POActionProp 1) (hI1 : HypIsometryProp 1)
    (hA : POActionProp (1 + m)) (hI : HypIsometryProp (1 + m))
    (R : E m ≃ₗᵢ[ℝ] E m) (v : E 1) (W : E m) :
    (∀ c η : ℝ, rotN R ≤ c → ‖R W - W‖ ≤ c → 10 * c < η →
      NearIdAt (blk 1 m 1 R) (fermiW 1 m v W) η) ∧
    ∀ η : ℝ, NearIdAt (blk 1 m 1 R) (fermiW 1 m v W) η → η ≤ 1 →
      rotN R ≤ 4 * η ∧ ‖R W - W‖ ≤ 2 * Real.sinh (η / 2) := by
  refine ⟨?_, ?_⟩
  · intro c η hrot hd h10 u' hu'
    have hc : 0 ≤ c := le_trans (norm_nonneg _) hrot
    have hh : hdist (fermiW 1 m v W)
        (fermiW 1 m ((Real.sqrt (1 + ‖nrmC 1 m u'‖ ^ 2))⁻¹ • tanC 1 m u')
          (nrmC 1 m u')) ≤ 1 := by
      rwa [← nib_fermiW_surj m u'] at hu'
    have haux := nib_nearId_blk_aux m hA1 hI1 hA hI R v
      ((Real.sqrt (1 + ‖nrmC 1 m u'‖ ^ 2))⁻¹ • tanC 1 m u') W (nrmC 1 m u') c η
      hc hrot hd h10 hh
    rwa [nib_fermiW_surj m u'] at haux
  · intro η hni hη1
    have hη0 : 0 ≤ η := by
      have hD := hni (fermiW 1 m v W) (by rw [nib_hdist_self]; norm_num)
      have h0 := nib_hdist_nonneg (fermiW 1 m v W) (blk 1 m 1 R • fermiW 1 m v W)
      linarith
    refine ⟨?_, ?_⟩
    · have hbound : ∀ y : E m, ‖y‖ = 1 → ‖R y - y‖ ≤ 4 * η := by
        intro y hy
        have hεpos : (0 : ℝ) < 2 * Real.sinh (1 / 2) := by positivity
        have hsp : hdist (fermiW 1 m v W)
            (fermiW 1 m v (W + (2 * Real.sinh (1 / 2)) • y)) ≤ 1 := by
          refine nib_hdist_spread m v W (W + (2 * Real.sinh (1 / 2)) • y) ?_
          have hsub : W - (W + (2 * Real.sinh (1 / 2)) • y)
              = -((2 * Real.sinh (1 / 2)) • y) := by abel
          rw [hsub, norm_neg, norm_smul, hy, mul_one, Real.norm_eq_abs, abs_of_pos hεpos]
        have haux := hni (fermiW 1 m v (W + (2 * Real.sinh (1 / 2)) • y)) hsp
        have h3 : ‖R (W + (2 * Real.sinh (1 / 2)) • y) - (W + (2 * Real.sinh (1 / 2)) • y)‖
            < 2 * Real.sinh (η / 2) :=
          nib_disp_lt_of_hdist_lt m hA1 hI1 hA hI R v (W + (2 * Real.sinh (1 / 2)) • y) η haux
        have h4 : ‖R W - W‖ < 2 * Real.sinh (η / 2) :=
          nib_disp_lt_of_hdist_lt m hA1 hI1 hA hI R v W η
            (hni _ (by rw [nib_hdist_self]; norm_num))
        have hdecomp : R (W + (2 * Real.sinh (1 / 2)) • y) - (W + (2 * Real.sinh (1 / 2)) • y)
            = (R W - W) + (2 * Real.sinh (1 / 2)) • (R y - y) := by
          rw [map_add, map_smul]
          module
        have h6 : (2 * Real.sinh (1 / 2)) * ‖R y - y‖ < 2 * (2 * Real.sinh (η / 2)) := by
          have h7 : (2 * Real.sinh (1 / 2)) * ‖R y - y‖
              = ‖(2 * Real.sinh (1 / 2)) • (R y - y)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hεpos]
          have h8 : (2 * Real.sinh (1 / 2)) • (R y - y)
              = (R (W + (2 * Real.sinh (1 / 2)) • y) - (W + (2 * Real.sinh (1 / 2)) • y))
                - (R W - W) := by
            rw [hdecomp]
            module
          rw [h7, h8]
          calc ‖(R (W + (2 * Real.sinh (1 / 2)) • y) - (W + (2 * Real.sinh (1 / 2)) • y))
                - (R W - W)‖
              ≤ ‖R (W + (2 * Real.sinh (1 / 2)) • y) - (W + (2 * Real.sinh (1 / 2)) • y)‖
                + ‖R W - W‖ := norm_sub_le _ _
            _ < 2 * Real.sinh (η / 2) + 2 * Real.sinh (η / 2) := by linarith
            _ = 2 * (2 * Real.sinh (η / 2)) := by ring
        have hs1 : (1 / 2 : ℝ) ≤ Real.sinh (1 / 2) :=
          Real.self_le_sinh_iff.mpr (by norm_num)
        have hs1pos : 0 < Real.sinh (1 / 2) := Real.sinh_pos_iff.mpr (by norm_num)
        have hs2 := nib_sinh_half_le hη0 hη1
        have h9 : ‖R y - y‖ ≤ 4 * η := by
          have h9a : (1 / 2) * ‖R y - y‖ ≤ Real.sinh (1 / 2) * ‖R y - y‖ :=
            mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
          have h9b : Real.sinh (1 / 2) * ‖R y - y‖ < 2 * Real.sinh (η / 2) := by
            linarith [h6]
          have h9c : 2 * Real.sinh (η / 2) ≤ 3 * η / 2 := by nlinarith [hs2]
          linarith
        exact h9
      exact nib_rotN_le_of_unit (by positivity) hbound
    · have h4 : ‖R W - W‖ < 2 * Real.sinh (η / 2) :=
        nib_disp_lt_of_hdist_lt m hA1 hI1 hA hI R v W η
          (hni _ (by rw [nib_hdist_self]; norm_num))
      exact le_of_lt h4

end Work.Mostow

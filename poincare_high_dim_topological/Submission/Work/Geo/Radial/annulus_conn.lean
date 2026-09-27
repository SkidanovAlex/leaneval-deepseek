import Mathlib
import Submission.Work.Geo.Radial.Basic
import Submission.Work.Conn.ExtForm
import Submission.Work.Conn.Main
import Submission.Work.Conn.Extend.exists_continuousMap_ball_of_homotopic_const
import Submission.Work.Conn.HomotopyInvariance.nullhomotopic_iff_of_homotopyEquiv

namespace Work.Geo.Radial

open Set Metric
open Work.Geo.Radial

/-!
# The sup-radius and the annulus `openCube 1 \ closedCube β`

This file proves blueprint `G8` (`Work.Geo.Radial.annulus_conn`): the sup-norm cube annulus
`PL.openCube 1 \ PL.closedCube β` (`0 < β < 1`) is `(n-2)`-connected in the extension form
`PL.ExtOverDisc`.

The argument is entirely radial.  We introduce the *sup-radius* `supRad x = max_i |x i|` of a
point of `ℝⁿ` (the radius of the sup-norm cube on which `x` sits), and show that the annulus
deformation retracts onto the sup-norm sphere of radius `ρ` (`β < ρ < 1`) along the straight
line `x ↦ ((1-t) + t ρ/supRad x) • x`.  Normalising by the Euclidean norm turns that
sup-sphere into the unit Euclidean sphere `𝕊ᵐ ⊂ ℝᵐ⁺¹`, so the annulus is homotopy equivalent
to `𝕊ᵐ`; the result then follows from `Work.Conn.extOverDisc_of_homotopyEquiv_sphere`.
-/

/-- The sup-radius of `x : ℝⁿ`: the largest absolute value of a coordinate. -/
noncomputable def supRad {n : ℕ} [NeZero n] (x : PL.E n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i : Fin n => |x i|

theorem le_supRad {n : ℕ} [NeZero n] (x : PL.E n) (i : Fin n) : |x i| ≤ supRad x :=
  Finset.le_sup' (fun i : Fin n => |x i|) (Finset.mem_univ i)

theorem supRad_nonneg {n : ℕ} [NeZero n] (x : PL.E n) : 0 ≤ supRad x := by
  obtain ⟨i⟩ := Finset.univ_nonempty (α := Fin n)
  exact le_trans (abs_nonneg (x i)) (le_supRad x i)

theorem supRad_lt_iff {n : ℕ} [NeZero n] {x : PL.E n} {r : ℝ} :
    supRad x < r ↔ x ∈ PL.openCube r := by
  rw [supRad]; simp [PL.openCube, Finset.sup'_lt_iff]

theorem supRad_le_iff {n : ℕ} [NeZero n] {x : PL.E n} {r : ℝ} :
    supRad x ≤ r ↔ x ∈ PL.closedCube r := by
  rw [supRad]; simp [PL.closedCube, Finset.sup'_le_iff]

theorem not_mem_closedCube_iff {n : ℕ} [NeZero n] {x : PL.E n} {r : ℝ} :
    x ∉ PL.closedCube r ↔ r < supRad x := by
  rw [← supRad_le_iff, not_le]

theorem continuous_supRad {n : ℕ} [NeZero n] : Continuous (supRad : PL.E n → ℝ) := by
  unfold supRad; fun_prop

theorem supRad_smul {n : ℕ} [NeZero n] {x : PL.E n} {c : ℝ} (hc : 0 ≤ c) :
    supRad (c • x) = c * supRad x := by
  have key : (fun i : Fin n => |(c • x) i|) = (fun i => c * |x i|) := by
    funext i; simp [abs_mul, abs_of_nonneg hc]
  unfold supRad
  rw [key, ← Finset.mul₀_sup' hc]

theorem supRad_eq_zero_iff {n : ℕ} [NeZero n] {x : PL.E n} : supRad x = 0 ↔ x = 0 := by
  constructor
  · intro h
    ext i
    have h1 : |x i| ≤ supRad x := le_supRad x i
    rw [h] at h1
    have := abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
    simpa using this
  · rintro rfl
    unfold supRad; simp

theorem supRad_pos_iff {n : ℕ} [NeZero n] {x : PL.E n} : 0 < supRad x ↔ x ≠ 0 := by
  refine ⟨fun h hx => ?_, fun hx => ?_⟩
  · exact absurd (supRad_eq_zero_iff.mpr hx) (ne_of_gt h)
  · by_contra hc
    rw [not_lt] at hc
    exact hx (supRad_eq_zero_iff.mp (le_antisymm hc (supRad_nonneg x)))

/-- Normalising a non-zero vector by its Euclidean norm gives a unit vector. -/
theorem norm_inv_smul_self {n : ℕ} {z : PL.E n} (hz : z ≠ 0) : ‖(‖z‖)⁻¹ • z‖ = 1 := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg z)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]

/-- **The annulus `openCube 1 \ closedCube β` is homotopy equivalent to `𝕊ᵐ`** (`β < ρ < 1`).

The homotopy equivalence is the normalisation `x ↦ ‖x‖⁻¹ • x` in one direction and the radial
retraction `y ↦ (ρ/supRad y) • y` in the other; the homotopy is by radial scaling. -/
theorem nonempty_homotopyEquiv_annulus (m : ℕ) {b r : ℝ} (hb : 0 < b) (hbr : b < r)
    (hr1 : r < 1) :
    Nonempty (ContinuousMap.HomotopyEquiv
      ↥(PL.openCube (n := m + 1) 1 \ PL.closedCube (n := m + 1) b) ↥(Work.Conn.Sph m)) := by
  have hr0 : 0 < r := lt_trans hb hbr
  let M : Type := ↥(PL.openCube (n := m + 1) 1 \ PL.closedCube (n := m + 1) b)
  have hM_open : ∀ x : M, (x : PL.E (m + 1)) ∈ PL.openCube 1 := fun x => x.2.1
  have hM_closed : ∀ x : M, (x : PL.E (m + 1)) ∉ PL.closedCube b := fun x => x.2.2
  have hM_gt : ∀ x : M, b < supRad (x : PL.E (m + 1)) := fun x =>
    not_mem_closedCube_iff.mp (hM_closed x)
  have hM_lt : ∀ x : M, supRad (x : PL.E (m + 1)) < 1 := fun x =>
    supRad_lt_iff.mpr (hM_open x)
  have hM_ne : ∀ x : M, (x : PL.E (m + 1)) ≠ 0 := fun x =>
    supRad_pos_iff.mp (lt_trans hb (hM_gt x))
  have hM_pos : ∀ x : M, 0 < supRad (x : PL.E (m + 1)) := fun x =>
    supRad_pos_iff.mpr (hM_ne x)
  -- the normalisation `M → 𝕊ᵐ`
  let normE : M → PL.E (m + 1) := fun x => (‖(x : PL.E (m + 1))‖)⁻¹ • (x : PL.E (m + 1))
  have hnormE_cont : Continuous normE := by
    show Continuous fun x : M => (‖(x : PL.E (m + 1))‖)⁻¹ • (x : PL.E (m + 1))
    exact ((continuous_norm.comp continuous_subtype_val).inv₀
      (fun x => norm_ne_zero_iff.mpr (hM_ne x))).smul continuous_subtype_val
  have hnormE_mem : ∀ x : M, normE x ∈ Work.Conn.Sph m := fun x => by
    rw [Work.Conn.mem_Sph_iff]
    exact norm_inv_smul_self (hM_ne x)
  let annToSph : C(M, ↥(Work.Conn.Sph m)) :=
    ⟨fun x => ⟨normE x, hnormE_mem x⟩, hnormE_cont.subtype_mk hnormE_mem⟩
  -- the radial retraction `𝕊ᵐ → M`
  let retrE : ↥(Work.Conn.Sph m) → PL.E (m + 1) :=
    fun y => (r / supRad (y : PL.E (m + 1))) • (y : PL.E (m + 1))
  have hSph_norm : ∀ y : ↥(Work.Conn.Sph m), ‖(y : PL.E (m + 1))‖ = 1 := fun y =>
    Work.Conn.mem_Sph_iff.mp y.2
  have hSph_ne : ∀ y : ↥(Work.Conn.Sph m), (y : PL.E (m + 1)) ≠ 0 := fun y hy => by
    have h1 := hSph_norm y
    rw [hy] at h1
    simp at h1
  have hSph_pos : ∀ y : ↥(Work.Conn.Sph m), 0 < supRad (y : PL.E (m + 1)) := fun y =>
    supRad_pos_iff.mpr (hSph_ne y)
  have hretr_sup : ∀ y : ↥(Work.Conn.Sph m), supRad (retrE y) = r := fun y => by
    have h0 : 0 ≤ r / supRad (y : PL.E (m + 1)) := le_of_lt (div_pos hr0 (hSph_pos y))
    show supRad ((r / supRad (y : PL.E (m + 1))) • (y : PL.E (m + 1))) = r
    rw [supRad_smul h0]
    exact div_mul_cancel₀ r (ne_of_gt (hSph_pos y))
  have hretr_cont : Continuous retrE := by
    show Continuous fun y : ↥(Work.Conn.Sph m) =>
      (r / supRad (y : PL.E (m + 1))) • (y : PL.E (m + 1))
    exact (continuous_const.div ((continuous_supRad (n := m + 1)).comp continuous_subtype_val)
      (fun y => ne_of_gt (hSph_pos y))).smul continuous_subtype_val
  have hretr_mem : ∀ y : ↥(Work.Conn.Sph m), retrE y ∈ PL.openCube 1 \ PL.closedCube b := by
    intro y
    refine ⟨?_, ?_⟩
    · rw [← supRad_lt_iff, hretr_sup y]; exact hr1
    · rw [not_mem_closedCube_iff, hretr_sup y]; exact hbr
  let sphToAnn : C(↥(Work.Conn.Sph m), M) :=
    ⟨fun y => ⟨retrE y, hretr_mem y⟩, hretr_cont.subtype_mk hretr_mem⟩
  -- the straight line homotopy from the identity to the radial retraction
  let HE : unitInterval × M → PL.E (m + 1) := fun p =>
    ((1 - (p.1 : ℝ)) + (p.1 : ℝ) * (r / supRad (p.2 : PL.E (m + 1)))) • (p.2 : PL.E (m + 1))
  have ht0 : ∀ p : unitInterval × M, 0 ≤ (p.1 : ℝ) := fun p => p.1.2.1
  have ht1 : ∀ p : unitInterval × M, (p.1 : ℝ) ≤ 1 := fun p => p.1.2.2
  have hcoef : ∀ p : unitInterval × M,
      0 ≤ (1 - (p.1 : ℝ)) + (p.1 : ℝ) * (r / supRad (p.2 : PL.E (m + 1))) := by
    intro p
    have h1 : 0 ≤ r / supRad (p.2 : PL.E (m + 1)) := le_of_lt (div_pos hr0 (hM_pos p.2))
    nlinarith [ht0 p, ht1 p, h1]
  have hHE_sup : ∀ p : unitInterval × M,
      supRad (HE p) = (1 - (p.1 : ℝ)) * supRad (p.2 : PL.E (m + 1)) + (p.1 : ℝ) * r := by
    intro p
    have hM0 : supRad (p.2 : PL.E (m + 1)) ≠ 0 := ne_of_gt (hM_pos p.2)
    show supRad (((1 - (p.1 : ℝ)) + (p.1 : ℝ) * (r / supRad (p.2 : PL.E (m + 1)))) •
      (p.2 : PL.E (m + 1))) = _
    rw [supRad_smul (hcoef p), add_mul, mul_assoc, div_mul_cancel₀ r hM0]
  have hHE_lt : ∀ p : unitInterval × M, supRad (HE p) < 1 := by
    intro p
    rw [hHE_sup p]
    rcases eq_or_lt_of_le (ht0 p) with h0 | h0
    · have h2 : (p.1 : ℝ) * r = 0 := by rw [← h0]; ring
      have h1 : (1 - (p.1 : ℝ)) = 1 := by rw [← h0]; ring
      rw [h1, one_mul, h2, add_zero]
      exact hM_lt p.2
    · have h1 : (1 - (p.1 : ℝ)) * supRad (p.2 : PL.E (m + 1)) ≤ (1 - (p.1 : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left (le_of_lt (hM_lt p.2)) (by linarith [ht1 p])
      have h2 : (p.1 : ℝ) * r < (p.1 : ℝ) * 1 := mul_lt_mul_of_pos_left hr1 h0
      linarith
  have hHE_gt : ∀ p : unitInterval × M, b < supRad (HE p) := by
    intro p
    rw [hHE_sup p]
    rcases eq_or_lt_of_le (ht0 p) with h0 | h0
    · have h2 : (p.1 : ℝ) * r = 0 := by rw [← h0]; ring
      have h1 : (1 - (p.1 : ℝ)) = 1 := by rw [← h0]; ring
      rw [h1, one_mul, h2, add_zero]
      exact hM_gt p.2
    · have h1 : (1 - (p.1 : ℝ)) * b ≤ (1 - (p.1 : ℝ)) * supRad (p.2 : PL.E (m + 1)) :=
        mul_le_mul_of_nonneg_left (le_of_lt (hM_gt p.2)) (by linarith [ht1 p])
      have h2 : (p.1 : ℝ) * b < (p.1 : ℝ) * r := mul_lt_mul_of_pos_left hbr h0
      linarith
  have hHE_mem : ∀ p : unitInterval × M, HE p ∈ PL.openCube 1 \ PL.closedCube b := by
    intro p
    exact ⟨supRad_lt_iff.mp (hHE_lt p), not_mem_closedCube_iff.mpr (hHE_gt p)⟩
  have hHE_cont : Continuous HE := by
    show Continuous fun p : unitInterval × M =>
      ((1 - (p.1 : ℝ)) + (p.1 : ℝ) * (r / supRad (p.2 : PL.E (m + 1)))) •
        (p.2 : PL.E (m + 1))
    have h1 : Continuous fun p : unitInterval × M => (p.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    have h2 : Continuous fun p : unitInterval × M => (p.2 : PL.E (m + 1)) :=
      continuous_subtype_val.comp continuous_snd
    have h3 : Continuous fun p : unitInterval × M => supRad (p.2 : PL.E (m + 1)) :=
      (continuous_supRad (n := m + 1)).comp h2
    have h4 : Continuous fun p : unitInterval × M => r / supRad (p.2 : PL.E (m + 1)) :=
      continuous_const.div h3 (fun p => ne_of_gt (hM_pos p.2))
    exact ((continuous_const.sub h1).add (h1.mul h4)).smul h2
  let Hmap : C(unitInterval × M, M) :=
    ⟨fun p => ⟨HE p, hHE_mem p⟩, hHE_cont.subtype_mk hHE_mem⟩
  -- the two pointwise computations of the homotopy
  have hzero : ∀ x : M, HE (0, x) = (x : PL.E (m + 1)) := fun x => by simp [HE]
  have hone : ∀ x : M, HE (1, x) = retrE (annToSph x) := fun x => by
    have hnorm : (‖(x : PL.E (m + 1))‖) ≠ 0 := norm_ne_zero_iff.mpr (hM_ne x)
    have hM0 : supRad (x : PL.E (m + 1)) ≠ 0 := ne_of_gt (hM_pos x)
    have hL : HE (1, x) = (r / supRad (x : PL.E (m + 1))) • (x : PL.E (m + 1)) := by simp [HE]
    have hsup : supRad ((‖(x : PL.E (m + 1))‖)⁻¹ • (x : PL.E (m + 1)))
        = (‖(x : PL.E (m + 1))‖)⁻¹ * supRad (x : PL.E (m + 1)) :=
      supRad_smul (inv_nonneg.mpr (norm_nonneg _))
    have hR : retrE (annToSph x) = (r / supRad (x : PL.E (m + 1))) • (x : PL.E (m + 1)) := by
      show (r / supRad (normE x)) • normE x = (r / supRad (x : PL.E (m + 1))) • (x : PL.E (m + 1))
      rw [show normE x = (‖(x : PL.E (m + 1))‖)⁻¹ • (x : PL.E (m + 1)) from rfl, hsup]
      rw [div_eq_mul_inv, div_eq_mul_inv, smul_smul]
      congr 1
      field_simp
    rw [hL, hR]
  have hHom : (ContinuousMap.id M).Homotopic (sphToAnn.comp annToSph) :=
    ⟨ContinuousMap.Homotopy.mk Hmap
      (fun x => Subtype.ext (hzero x))
      (fun x => Subtype.ext (hone x))⟩
  -- the other composite is the identity
  have hcomp : annToSph.comp sphToAnn = ContinuousMap.id ↥(Work.Conn.Sph m) := by
    apply ContinuousMap.ext
    intro y
    refine Subtype.ext ?_
    have hc : 0 ≤ r / supRad (y : PL.E (m + 1)) := le_of_lt (div_pos hr0 (hSph_pos y))
    have hcc : (r / supRad (y : PL.E (m + 1))) ≠ 0 := ne_of_gt (div_pos hr0 (hSph_pos y))
    have hnorm : ‖(r / supRad (y : PL.E (m + 1))) • (y : PL.E (m + 1))‖
        = r / supRad (y : PL.E (m + 1)) := by
      rw [norm_smul, Real.norm_of_nonneg hc, hSph_norm y, mul_one]
    show (‖((r / supRad (y : PL.E (m + 1))) • (y : PL.E (m + 1)))‖)⁻¹ •
        ((r / supRad (y : PL.E (m + 1))) • (y : PL.E (m + 1))) = (y : PL.E (m + 1))
    rw [hnorm, inv_smul_smul₀ hcc]
  exact ⟨ContinuousMap.HomotopyEquiv.mk annToSph sphToAnn hHom.symm
    (by simpa only [hcomp] using
      ContinuousMap.Homotopic.refl (ContinuousMap.id ↥(Work.Conn.Sph m)))⟩

/-- Blueprint G8 (`Work.Geo.Radial.annulus_conn`): the cube annulus `openCube 1 \ closedCube β`
(in the sup norm, `0 < β < 1`) is `(n-2)`-connected in the extension-over-the-disc sense.

Proof route: pick `ρ` with `β < ρ < 1`.  The radial map `x ↦ (ρ / ‖x‖_∞) • x` (sup norm!) is a
deformation retraction of the annulus onto the sup-sphere `{y | ‖y‖_∞ = ρ}`, which is
homeomorphic to the Euclidean unit sphere `sphere (0 : ℝⁿ) 1` (scale by `1/ρ`, then divide by the
sup norm).  Conclude with
`Work.Conn.extOverDisc_of_homotopyEquiv_sphere` (`𝕊ⁿ⁻¹` is `(n-2)`-connected in this form) using
`Work.Conn.nullhomotopic_sphere_of_lt`; `Work.Conn.extOverDisc_iff` converts between the
null-homotopy and extension forms.

The intended fully-qualified name is `Work.Geo.Radial.annulus_conn`. -/
theorem annulus_conn {n : ℕ} (hn : 2 ≤ n) (β : ℝ) (h0 : 0 < β) (h1 : β < 1) (j : ℕ)
    (hj : j + 2 ≤ n) :
    PL.ExtOverDisc ↥(PL.openCube (n := n) 1 \ PL.closedCube β) j := by
  rcases n with _ | m
  · exact absurd hn (by omega)
  · obtain ⟨ρ, hβρ, hρ1⟩ : ∃ ρ, β < ρ ∧ ρ < 1 := ⟨(β + 1) / 2, by linarith, by linarith⟩
    obtain ⟨e⟩ := nonempty_homotopyEquiv_annulus m h0 hβρ hρ1
    exact Work.Conn.extOverDisc_of_homotopyEquiv_sphere (n := m) (j := j) (by omega) e

end Work.Geo.Radial

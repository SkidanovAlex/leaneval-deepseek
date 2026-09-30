import Mathlib
import Submission.Work.BW.basisRed_defs
import Submission.Work.BW.basisRed_succMinL_mono
import Submission.Work.BW.Minkowski2.succMinBody_interior

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Elementary properties of a lattice norm `F : (Fin n → ℝ) → ℝ`

A `Work.BW.IsLatticeNorm F` is a norm on `ℝⁿ`; here we record the elementary consequences used in
the proof of Minkowski's second inequality (`Work.BW.KW.minkowski_second_norm`): continuity,
domination of a multiple of the Euclidean norm, and the basic geometric properties of the unit
ball `{x | F x ≤ 1}`.
-/

namespace Work.BW.KWM

open MeasureTheory
open scoped Pointwise

variable {n : ℕ}

/-- The unit ball `{x | F x ≤ 1}` of a lattice norm `F`. -/
def uBall (F : (Fin n → ℝ) → ℝ) : Set (Fin n → ℝ) := {x | F x ≤ 1}

@[simp] theorem mem_uBall {F : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} : x ∈ uBall F ↔ F x ≤ 1 :=
  Iff.rfl

theorem latticeNorm_zero {F : (Fin n → ℝ) → ℝ} (hF : Work.BW.IsLatticeNorm F) : F 0 = 0 :=
  (hF.eq_zero 0).mpr rfl

theorem latticeNorm_neg {F : (Fin n → ℝ) → ℝ} (hF : Work.BW.IsLatticeNorm F)
    (x : Fin n → ℝ) : F (-x) = F x := by
  have h : -x = (-1 : ℝ) • x := by simp
  rw [h, hF.smul]
  norm_num

/-- A lattice norm is Lipschitz, hence continuous. -/
theorem norm_continuous {F : (Fin n → ℝ) → ℝ} (hF : Work.BW.IsLatticeNorm F) : Continuous F := by
  set M : ℝ := ∑ i : Fin n, F (Pi.single i (1 : ℝ) : Fin n → ℝ) with hM
  have hMnn : 0 ≤ M := Finset.sum_nonneg (fun i _ => hF.nonneg _)
  have hsum : ∀ (s : Finset (Fin n)) (x : Fin n → ℝ),
      F (∑ i ∈ s, x i • (Pi.single i (1 : ℝ) : Fin n → ℝ))
        ≤ ∑ i ∈ s, F (x i • (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by
    intro s x
    induction s using Finset.induction with
    | empty => rw [Finset.sum_empty, Finset.sum_empty, latticeNorm_zero hF]
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        exact le_trans (hF.add_le _ _) (add_le_add le_rfl ih)
  have hbound : ∀ x : Fin n → ℝ, F x ≤ M * ‖x‖ := by
    intro x
    have hx : x = ∑ i : Fin n, x i • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    have h2 : F (∑ i : Fin n, x i • (Pi.single i (1 : ℝ) : Fin n → ℝ)) ≤ M * ‖x‖ := by
      refine le_trans (hsum _ _) ?_
      have h1 : ∀ i : Fin n, F (x i • (Pi.single i (1 : ℝ) : Fin n → ℝ))
          ≤ ‖x‖ * F (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
        intro i
        rw [hF.smul]
        have h3 : |x i| ≤ ‖x‖ := by
          have h4 := norm_le_pi_norm x i
          rwa [Real.norm_eq_abs] at h4
        exact mul_le_mul_of_nonneg_right h3 (hF.nonneg _)
      refine le_trans (Finset.sum_le_sum (fun i _ => h1 i)) ?_
      rw [← Finset.mul_sum, ← hM]
      exact le_of_eq (mul_comm _ _)
    rw [← hx] at h2
    exact h2
  have hlip : ∀ x y : Fin n → ℝ, |F x - F y| ≤ M * ‖x - y‖ := by
    intro x y
    have h1 : F x ≤ F y + F (x - y) := by
      have h := hF.add_le y (x - y)
      rwa [add_sub_cancel] at h
    have h2 : F y ≤ F x + F (x - y) := by
      have h := hF.add_le x (y - x)
      have hxy : x + (y - x) = y := by abel
      rw [hxy] at h
      have h3 : F (y - x) = F (x - y) := by
        rw [show y - x = -(x - y) by abel, latticeNorm_neg hF]
      linarith
    have h5 := hbound (x - y)
    rw [abs_sub_le_iff]
    exact ⟨by linarith, by linarith⟩
  rw [Metric.continuous_iff]
  intro x ε hε
  refine ⟨(M + 1)⁻¹ * ε, by positivity, fun y hy => ?_⟩
  have hd : ‖y - x‖ < (M + 1)⁻¹ * ε := by simpa [dist_eq_norm] using hy
  rw [Real.dist_eq]
  have h := hlip x y
  calc |F y - F x| ≤ M * ‖x - y‖ := by rw [abs_sub_comm]; exact h
    _ = M * ‖y - x‖ := by rw [norm_sub_rev]
    _ ≤ (M + 1) * ‖y - x‖ := by nlinarith [norm_nonneg (y - x)]
    _ < (M + 1) * ((M + 1)⁻¹ * ε) := by
        apply mul_lt_mul_of_pos_left hd; linarith [hMnn]
    _ = ε := by
        rw [← mul_assoc, mul_inv_cancel₀ (by linarith [hMnn]), one_mul]

/-- A lattice norm dominates a positive multiple of the norm of `ℝⁿ`. -/
theorem norm_lower_bound {F : (Fin n → ℝ) → ℝ} (hF : Work.BW.IsLatticeNorm F) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin n → ℝ, c * ‖x‖ ≤ F x := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, one_pos, fun x => ?_⟩
    have hx : x = 0 := Subsingleton.elim x 0
    subst hx
    rw [norm_zero, mul_zero]
    exact hF.nonneg 0
  · have hcpt : IsCompact {x : Fin n → ℝ | ‖x‖ = 1} := by
      have h : {x : Fin n → ℝ | ‖x‖ = 1} = Metric.sphere (0 : Fin n → ℝ) 1 := by
        ext x; simp [Metric.mem_sphere, dist_eq_norm]
      rw [h]; exact isCompact_sphere 0 1
    have hne : ({x : Fin n → ℝ | ‖x‖ = 1}).Nonempty :=
      ⟨Pi.single ⟨0, hn⟩ (1 : ℝ), by simp [Pi.norm_single]⟩
    obtain ⟨z, hz, hzmin⟩ := hcpt.exists_isMinOn hne (norm_continuous hF).continuousOn
    have hzpos : 0 < F z := by
      have hz0 : z ≠ 0 := by
        intro h; rw [h] at hz; simp at hz
      exact lt_of_le_of_ne (hF.nonneg z) (Ne.symm fun h => hz0 ((hF.eq_zero z).mp h))
    refine ⟨F z, hzpos, fun x => ?_⟩
    rcases eq_or_ne x 0 with hx | hx
    · subst hx; rw [norm_zero, mul_zero]; exact hF.nonneg 0
    · have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hmem : ‖x‖⁻¹ • x ∈ {x : Fin n → ℝ | ‖x‖ = 1} := by
        simp only [Set.mem_setOf_eq, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hnx), inv_mul_cancel₀ (ne_of_gt hnx)]
      have hle := hzmin hmem
      have hxdecomp : x = ‖x‖ • (‖x‖⁻¹ • x) := by
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hnx), one_smul]
      have hFx : F x = ‖x‖ * F (‖x‖⁻¹ • x) := by
        conv_lhs => rw [hxdecomp]
        rw [hF.smul, abs_of_pos hnx]
      rw [hFx, mul_comm (F z) ‖x‖]
      exact mul_le_mul_of_nonneg_left hle hnx.le

theorem uBall_neg {F : (Fin n → ℝ) → ℝ} (hF : Work.BW.IsLatticeNorm F) :
    ∀ x ∈ uBall F, -x ∈ uBall F := by
  intro x hx
  rw [mem_uBall] at hx ⊢
  rwa [latticeNorm_neg hF]

theorem uBall_convex {F : (Fin n → ℝ) → ℝ} (hF : Work.BW.IsLatticeNorm F) :
    Convex ℝ (uBall F) := by
  intro x hx y hy a b ha hb hab
  rw [mem_uBall] at hx hy ⊢
  calc F (a • x + b • y) ≤ |a| * F x + |b| * F y := by
        rw [← hF.smul a x, ← hF.smul b y]; exact hF.add_le _ _
    _ ≤ |a| * 1 + |b| * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg a))
          (mul_le_mul_of_nonneg_left hy (abs_nonneg b))
    _ = 1 := by rw [mul_one, mul_one, abs_of_nonneg ha, abs_of_nonneg hb, hab]

theorem uBall_closed {F : (Fin n → ℝ) → ℝ} (hF : Work.BW.IsLatticeNorm F) :
    IsClosed (uBall F) :=
  isClosed_le (norm_continuous hF) continuous_const

theorem uBall_measurable {F : (Fin n → ℝ) → ℝ} (hF : Work.BW.IsLatticeNorm F) :
    MeasurableSet (uBall F) :=
  (uBall_closed hF).measurableSet

theorem uBall_bounded {F : (Fin n → ℝ) → ℝ} (hF : Work.BW.IsLatticeNorm F) :
    Bornology.IsBounded (uBall F) := by
  obtain ⟨c, hc, hbound⟩ := norm_lower_bound hF
  refine Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := 0) (r := c⁻¹)) ?_
  intro x hx
  rw [mem_uBall] at hx
  rw [Metric.mem_closedBall, dist_zero_right]
  have h1 : c * ‖x‖ ≤ 1 := le_trans (hbound x) hx
  have h2 : ‖x‖ ≤ 1 / c := (le_div_iff₀ hc).mpr (by linarith)
  simpa [div_eq_inv_mul] using h2

theorem uBall_interior_nonempty {F : (Fin n → ℝ) → ℝ} (hF : Work.BW.IsLatticeNorm F) :
    (interior (uBall F)).Nonempty := by
  refine ⟨0, ?_⟩
  have hopen : IsOpen {x : Fin n → ℝ | F x < 1} :=
    isOpen_lt (norm_continuous hF) continuous_const
  have h0 : (0 : Fin n → ℝ) ∈ {x : Fin n → ℝ | F x < 1} := by
    simp [latticeNorm_zero hF]
  refine mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hopen.mem_nhds h0) ?_)
  intro x hx
  have hx' : F x < 1 := by simpa using hx
  exact le_of_lt hx'

/-- For `t ≥ 0` the dilated unit ball is the sublevel set `{x | F x ≤ t}`. -/
theorem smul_uBall_eq {F : (Fin n → ℝ) → ℝ} (hF : Work.BW.IsLatticeNorm F) {t : ℝ}
    (ht : 0 ≤ t) : t • uBall F = {x : Fin n → ℝ | F x ≤ t} := by
  rcases eq_or_lt_of_le ht with h | h
  · subst h
    ext x
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨y, hy, rfl⟩
      show F (0 • y) ≤ 0
      rw [zero_smul, latticeNorm_zero hF]
    · intro hx
      have hx' : F x ≤ 0 := by simpa using hx
      have hx0 : x = 0 := (hF.eq_zero x).mp (le_antisymm hx' (hF.nonneg x))
      refine ⟨0, ?_, ?_⟩
      · show F (0 : Fin n → ℝ) ≤ 1
        rw [latticeNorm_zero hF]; norm_num
      · rw [hx0, zero_smul]
  · have htpos : 0 < t := h
    ext x
    rw [Set.mem_smul_set, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [mem_uBall] at hy
      rw [hF.smul, abs_of_nonneg ht]
      calc t * F y ≤ t * 1 := mul_le_mul_of_nonneg_left hy ht
        _ = t := mul_one t
    · intro hx
      refine ⟨t⁻¹ • x, ?_, ?_⟩
      · rw [mem_uBall, hF.smul, abs_of_pos (inv_pos.mpr htpos)]
        calc t⁻¹ * F x ≤ t⁻¹ * t :=
              mul_le_mul_of_nonneg_left hx (le_of_lt (inv_pos.mpr htpos))
          _ = 1 := inv_mul_cancel₀ (ne_of_gt htpos)
      · exact smul_inv_smul₀ (ne_of_gt htpos) x

/-- A point of the interior of the dilated unit ball `t • {F ≤ 1}` (`t > 0`) has norm `< t`. -/
theorem F_lt_of_mem_interior_smul {F : (Fin n → ℝ) → ℝ} (hF : Work.BW.IsLatticeNorm F) {t : ℝ}
    (ht : 0 < t) {x : Fin n → ℝ} (hx : x ∈ interior (t • uBall F)) : F x < t := by
  obtain ⟨μ, hμ0, hμt, hxμ⟩ := Work.BW.Minkowski2.exists_smul_lt_of_mem_interior ht hx
  obtain ⟨k, hk, hkx⟩ := Set.mem_smul_set.mp hxμ
  rw [← hkx]
  have h1 : F (μ • k) = μ * F k := by rw [hF.smul, abs_of_pos hμ0]
  rw [h1]
  calc μ * F k ≤ μ * 1 := mul_le_mul_of_nonneg_left hk hμ0.le
    _ = μ := mul_one μ
    _ < t := hμt

/-- The successive minima of a lattice norm are positive. -/
theorem succMinL_pos_of_le {F : (Fin n → ℝ) → ℝ} (hF : Work.BW.IsLatticeNorm F) {j : ℕ}
    (hj1 : 1 ≤ j) (hjn : j ≤ n) : 0 < Work.BW.succMinL F j := by
  obtain ⟨c, hc, hbound⟩ := norm_lower_bound hF
  rw [Work.BW.basisRed_succMinL_eq_sInf]
  refine lt_of_lt_of_le hc (le_csInf (Work.BW.basisRed_succSetL_nonempty hF hjn) ?_)
  intro t ht
  by_contra hcon
  push_neg at hcon
  have hempty : Work.BW.basisRed_succSpanL F t = ⊥ := by
    rw [Work.BW.basisRed_succSpanL, Submodule.span_eq_bot]
    rintro x ⟨⟨v, rfl⟩, hx⟩
    have hv0 : v = 0 := by
      by_contra hv
      obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
        by_contra h
        push_neg at h
        exact hv (funext h)
      have h1 : (1 : ℤ) ≤ |v i| := by
        have := abs_pos.mpr hi; omega
      have h2 : (1 : ℝ) ≤ |((v i : ℤ) : ℝ)| := by exact_mod_cast h1
      have h3 : |((v i : ℤ) : ℝ)| ≤ ‖(fun i : Fin n => ((v i : ℤ) : ℝ))‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm (fun i : Fin n => ((v i : ℤ) : ℝ)) i
      have h4 : (1 : ℝ) ≤ ‖(fun i : Fin n => ((v i : ℤ) : ℝ))‖ := le_trans h2 h3
      have h5 := hbound (fun i : Fin n => ((v i : ℤ) : ℝ))
      have h6 : c ≤ F (fun i : Fin n => ((v i : ℤ) : ℝ)) :=
        calc c = c * 1 := (mul_one c).symm
          _ ≤ c * ‖(fun i : Fin n => ((v i : ℤ) : ℝ))‖ :=
              mul_le_mul_of_nonneg_left h4 hc.le
          _ ≤ F (fun i : Fin n => ((v i : ℤ) : ℝ)) := h5
      linarith
    rw [hv0]
    funext i
    simp
  rw [Work.BW.basisRed_succSetL, Set.mem_setOf_eq] at ht
  rw [hempty, finrank_bot] at ht
  omega

end Work.BW.KWM

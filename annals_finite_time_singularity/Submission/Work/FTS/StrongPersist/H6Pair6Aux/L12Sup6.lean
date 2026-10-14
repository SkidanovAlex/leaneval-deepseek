import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.OpenPkg.ProdOpen.Tools1d
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsSep
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.ExcPairBranches
import Submission.Work.FTS.StrongPersist.N6_L12H
import Submission.Work.FTS.StrongPersist.N6_fkH
import Submission.Work.FTS.StrongPersist.QangSq6Full
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.Spaces.sin_two_rpow
-- ===== merged: Submission.Work.FTS.StrongEps.H5.LevelShift =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5

open Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Locality of `D_z`-iterates on an open set -/

theorem DzIter_congr_isOpen {g g' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j g))
      (Function.uncurry (Work.Spaces.DzIter j g')) V := by
  induction j with
  | zero => exact h
  | succ j ih =>
      intro p hp
      show p.1 * Work.Spaces.pz (Work.Spaces.DzIter j g) p.1 p.2
          = p.1 * Work.Spaces.pz (Work.Spaces.DzIter j g') p.1 p.2
      rw [Work.Spaces.pz_congr_of_isOpen hV ih hp]

/-! ## The slot identities -/

/-- `D_θ^i (D_θ h) = D_θ^{i+1} h` (definitional, via `DthIter_add_right`). -/
theorem DthIter_Dth_eq (h : ℝ → ℝ → ℝ) (i : ℕ) :
    DthIter i (Dth h) = DthIter (i + 1) h := by
  show DthIter i (DthIter 1 h) = DthIter (i + 1) h
  rw [Work.Spaces.DthIter_add_right]

/-- `D_z^i (D_z h) = D_z^{i+1} h` (definitional). -/
theorem DzIter_Dz_eq (h : ℝ → ℝ → ℝ) (i : ℕ) :
    DzIter i (Dz h) = DzIter (i + 1) h := by
  show DzIter i (DzIter 1 h) = DzIter (i + 1) h
  rw [← Work.Spaces.DzIter_add_right]

/-- **The mixed slot of `D_θ h`**: `mixed j i (D_θ h) = mixed j (i+1) h`. -/
theorem mixed_Dth_eq (h : ℝ → ℝ → ℝ) (j i : ℕ) :
    mixed j i (Dth h) = mixed j (i + 1) h := by
  show DzIter j (DthIter i (Dth h)) = DzIter j (DthIter (i + 1) h)
  rw [DthIter_Dth_eq]

/-- **The mixed slot of `D_z h` on the open quadrant**: `mixed j i (D_z h) = mixed (j+1) i h`
at every point of `Q0`, for `h` smooth on the open quadrant. -/
theorem mixed_Dz_eqOn_Q0 {h : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen h)
    (j i : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ' : θ < π / 2) :
    mixed j i (Dz h) z θ = mixed (j + 1) i h z θ := by
  have hcomm : Set.EqOn (Function.uncurry (DthIter i (DzIter 1 h)))
      (Function.uncurry (mixed 1 i h)) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0
      (fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall h).mp hsm n) 1 i
  have hy : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ'⟩
  have h1 : DzIter j (DthIter i (Dz h)) z θ
      = DzIter j (DzIter 1 (DthIter i h)) z θ := by
    refine DzIter_congr_isOpen Work.FTS.EllipticEst.isOpen_Q0 ?_ j hy
    intro p hp
    exact hcomm hp
  have h2 : DzIter j (DzIter 1 (DthIter i h)) z θ = DzIter (j + 1) (DthIter i h) z θ := by
    rw [Work.Spaces.DzIter_add_right]
  show DzIter j (DthIter i (Dz h)) z θ = DzIter (j + 1) (DthIter i h) z θ
  rw [h1, h2]

/-! ## The two parts of the integrand, and the shift -/

/-- The pure `D_z`-part of `HkIntegrand`, as a sum over the index set. -/
def Zak (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (DzIter i f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2

/-- The mixed part of `HkIntegrand`, as a sum over the index set. -/
def Mak (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
    if 1 ≤ i ∧ i + j ≤ k then (mixed j i f z θ * Wt α z θ) ^ 2 else 0

theorem HkIntegrand_eq_Zak_add_Mak (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    HkIntegrand α k f z θ = Zak α k f z θ + Mak α k f z θ := rfl

/-- **The pure `D_z`-slots shift by one level**: `Z_{k+1} f ≤ Z_k f + Z_k (D_z f)`. -/
theorem Zak_succ_le (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Zak α (k + 1) f z θ ≤ Zak α k f z θ + Zak α k (Dz f) z θ := by
  have hsplit : Zak α (k + 1) f z θ
      = Zak α k f z θ + (DzIter (k + 1) f z θ
          * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2 := by
    simp only [Zak, Finset.sum_range_succ]
  have hDz : Zak α k (Dz f) z θ
      = ∑ i ∈ Finset.range (k + 1),
          (DzIter (i + 1) f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2 := by
    simp only [Zak]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [DzIter_Dz_eq]
  rw [hsplit, hDz]
  have hnn : ∀ i ∈ Finset.range (k + 1),
      0 ≤ (DzIter (i + 1) f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2 :=
    fun i _ => sq_nonneg _
  have hle := Finset.single_le_sum hnn (Finset.mem_range.mpr (Nat.lt_succ_self k))
  linarith [hle]

/-- **The mixed slots shift by one level** (for `k ≥ 1`): the new slots at level `k+1` are
priced by the level-`k` integrands of `D_z h` (the slots carrying a `θ`-derivative) and of
`D_θ h` (the `D_z`-free slot `D_θ^{k+1} h`). -/
theorem Mak_succ_le (α : ℝ) {h : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen h)
    {k : ℕ} (hk : 1 ≤ k) {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ' : θ < π / 2) :
    Mak α (k + 1) h z θ ≤ Mak α k h z θ + Mak α k (Dz h) z θ + Mak α k (Dth h) z θ := by
  set T : ℕ → ℕ → ℝ := fun i j => (mixed j i h z θ * Wt α z θ) ^ 2 with hTdef
  have hTnn : ∀ i j : ℕ, 0 ≤ T i j := fun i j => sq_nonneg _
  -- ### the `D_z`-side level-`k` integrand, re-indexed
  have hDz : Mak α k (Dz h) z θ
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then T i (j + 1) else 0) := by
    simp only [Mak]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc, if_pos hc, hTdef]
      rw [mixed_Dz_eqOn_Q0 hsm j i hz hθ hθ']
    · rw [if_neg hc, if_neg hc]
  -- ### the `D_θ`-side level-`k` integrand, re-indexed
  have hDth : Mak α k (Dth h) z θ
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then T (i + 1) j else 0) := by
    simp only [Mak]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc, if_pos hc, hTdef]
      rw [show mixed j i (Dth h) = mixed j (i + 1) h from mixed_Dth_eq h j i]
    · rw [if_neg hc, if_neg hc]
  -- ### the left-hand side, split at `j = 0`
  have hsplit : Mak α (k + 1) h z θ
      = (∑ i ∈ Finset.range (k + 1 + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then T i (j + 1) else 0))
        + (∑ i ∈ Finset.range (k + 1 + 1),
            (if 1 ≤ i ∧ i ≤ k + 1 then T i 0 else 0)) := by
    simp only [Mak]
    have hinner : ∀ i ∈ Finset.range (k + 1 + 1),
        (∑ j ∈ Finset.range (k + 1 + 1),
            (if 1 ≤ i ∧ i + j ≤ k + 1 then T i j else 0))
          = (∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then T i (j + 1) else 0))
            + (if 1 ≤ i ∧ i ≤ k + 1 then T i 0 else 0) := by
      intro i _
      rw [Finset.sum_range_succ']
      congr 1
      · refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hc : 1 ≤ i ∧ i + (j + 1) ≤ k + 1
        · rw [if_pos hc, if_pos (by omega)]
        · rw [if_neg hc, if_neg (by omega)]
    rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib]
  -- ### the outer sum of the first piece: the `i = k+1` term vanishes
  have hA : (∑ i ∈ Finset.range (k + 1 + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then T i (j + 1) else 0))
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then T i (j + 1) else 0) := by
    rw [Finset.sum_range_succ]
    have hz0 : (∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ k + 1 ∧ k + 1 + j ≤ k then T (k + 1) (j + 1) else 0)) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [if_neg (by omega)]
    rw [hz0, add_zero]
  -- ### the outer sum of the second piece: split off the `i = k+1` term
  have hB : (∑ i ∈ Finset.range (k + 1 + 1),
        (if 1 ≤ i ∧ i ≤ k + 1 then T i 0 else 0))
      = (∑ i ∈ Finset.range (k + 1), (if 1 ≤ i ∧ i ≤ k then T i 0 else 0))
        + T (k + 1) 0 := by
    rw [Finset.sum_range_succ]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      by_cases hc : 1 ≤ i
      · rw [if_pos ⟨hc, by omega⟩, if_pos ⟨hc, hi'⟩]
      · rw [if_neg (fun h => hc h.1), if_neg (fun h => hc h.1)]
    · rw [if_pos ⟨by omega, by omega⟩]
  -- ### the second piece is dominated by the `h`- and `D_θ`-integrands
  have hB1 : (∑ i ∈ Finset.range (k + 1), (if 1 ≤ i ∧ i ≤ k then T i 0 else 0))
      ≤ Mak α k h z θ := by
    rw [Mak]
    refine Finset.sum_le_sum fun i _ => ?_
    have hmem : 0 ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.succ_pos k)
    have hnn : ∀ j ∈ Finset.range (k + 1),
        0 ≤ (if 1 ≤ i ∧ i + j ≤ k then T i j else 0) := by
      intro j _
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · rw [if_pos hc]; exact hTnn i j
      · rw [if_neg hc]
    have hle := Finset.single_le_sum hnn hmem
    have hsimp : (if 1 ≤ i ∧ i + 0 ≤ k then T i 0 else 0)
        = (if 1 ≤ i ∧ i ≤ k then T i 0 else 0) := by rw [Nat.add_zero]
    rwa [hsimp] at hle
  have hB2 : T (k + 1) 0 ≤ Mak α k (Dth h) z θ := by
    rw [hDth]
    have hmem : k ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_self k)
    have hmem0 : 0 ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.succ_pos k)
    have hsum : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then T (i + 1) j else 0))
        = ∑ i ∈ Finset.range (k + 1), (∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then T (i + 1) j else 0)) := rfl
    rw [hsum]
    have hnn : ∀ i ∈ Finset.range (k + 1),
        0 ≤ (∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then T (i + 1) j else 0)) := by
      intro i _
      refine Finset.sum_nonneg fun j _ => ?_
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · rw [if_pos hc]; exact hTnn (i + 1) j
      · rw [if_neg hc]
    have h1 : (∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ k ∧ k + j ≤ k then T (k + 1) j else 0)) ≤
        ∑ i ∈ Finset.range (k + 1), (∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then T (i + 1) j else 0)) :=
      Finset.single_le_sum hnn hmem
    have h2 : (if 1 ≤ k ∧ k + 0 ≤ k then T (k + 1) 0 else 0) ≤
        ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ k ∧ k + j ≤ k then T (k + 1) j else 0) := by
      refine Finset.single_le_sum
        (f := fun j => (if 1 ≤ k ∧ k + j ≤ k then T (k + 1) j else 0)) (fun j _ => ?_) hmem0
      by_cases hc : 1 ≤ k ∧ k + j ≤ k
      · rw [if_pos hc]; exact hTnn (k + 1) j
      · rw [if_neg hc]
    have h3 : (if 1 ≤ k ∧ k + 0 ≤ k then T (k + 1) 0 else 0) = T (k + 1) 0 :=
      if_pos ⟨hk, by omega⟩
    linarith [h1, h2, h3.le, h3.ge]
  have hAeq : (∑ i ∈ Finset.range (k + 1 + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then T i (j + 1) else 0)) = Mak α k (Dz h) z θ := by
    rw [hA, hDz]
  have hBle : (∑ i ∈ Finset.range (k + 1 + 1),
        (if 1 ≤ i ∧ i ≤ k + 1 then T i 0 else 0))
      ≤ Mak α k h z θ + Mak α k (Dth h) z θ := by
    rw [hB]
    linarith only [hB1, hB2]
  rw [hsplit, hAeq]
  linarith only [hBle]

/-- **The level shift of the `ℋ^k`-integrand**, on the open quadrant, for `k ≥ 1`. -/
theorem HkIntegrand_succ_le {α : ℝ} {h : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen h) {k : ℕ} (hk : 1 ≤ k)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ' : θ < π / 2) :
    HkIntegrand α (k + 1) h z θ ≤ HkIntegrand α k h z θ + HkIntegrand α k (Dz h) z θ
      + HkIntegrand α k (Dth h) z θ := by
  rw [HkIntegrand_eq_Zak_add_Mak α (k+1) h z θ, HkIntegrand_eq_Zak_add_Mak α k h z θ,
    HkIntegrand_eq_Zak_add_Mak α k (Dz h) z θ, HkIntegrand_eq_Zak_add_Mak α k (Dth h) z θ]
  have h1 := Zak_succ_le α k h z θ
  have h2 := Mak_succ_le α hsm hk hz hθ hθ'
  have h3 : 0 ≤ Zak α k (Dth h) z θ := Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith only [h1, h2, h3]

/-! ## The level shift on the closed quadrant, and its integrated forms -/

/-- **The level shift on the closed quadrant**: both sides are `0` at `z = 0` and at
`sin(2θ) = 0`, so the open-quadrant inequality extends. -/
theorem HkIntegrand_succ_le_IzIθ {α : ℝ} (hα : 0 < α) {h : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen h) {k : ℕ} (hk : 1 ≤ k) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α (k + 1) h z θ
        ≤ Work.Spaces.HkIntegrand α k h z θ + Work.Spaces.HkIntegrand α k (Work.Spaces.Dz h) z θ
          + Work.Spaces.HkIntegrand α k (Work.Spaces.Dth h) z θ := by
  intro z hz θ hθ
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
  · rw [← hz0, Work.FTS.LocData.HkIntegrand_zero_fst]
    exact add_nonneg (add_nonneg (Work.Spaces.HkIntegrand_nonneg α k h 0 θ)
      (Work.Spaces.HkIntegrand_nonneg α k (Work.Spaces.Dz h) 0 θ))
      (Work.Spaces.HkIntegrand_nonneg α k (Work.Spaces.Dth h) 0 θ)
  · by_cases hsin : Real.sin (2 * θ) = 0
    · rw [Work.FTS.StrongPersist.HkIntegrand_eq_zero_of_sin_zero (α := α) hα (k := k + 1) hsin]
      exact add_nonneg (add_nonneg (Work.Spaces.HkIntegrand_nonneg α k h z θ)
        (Work.Spaces.HkIntegrand_nonneg α k (Work.Spaces.Dz h) z θ))
        (Work.Spaces.HkIntegrand_nonneg α k (Work.Spaces.Dth h) z θ)
    · have hsinpos : 0 < Real.sin (2 * θ) :=
        lt_of_le_of_ne (Work.Elliptic.sin_two_nonneg_of_mem hθ) (Ne.symm hsin)
      have hθIoo : θ ∈ Set.Ioo (0 : ℝ) (π / 2) :=
        Work.FTS.CoercivityFix.Coer1.mem_Ioo_of_mem_Iθ_of_sin_pos hθ hsinpos
      exact HkIntegrand_succ_le hsm hk hzpos hθIoo.1 hθIoo.2

/-- **The level shift of `ℋ^k`-membership**: from the level-`k` honesty of `h`, `D_z h` and
`D_θ h`, the level-`(k+1)` honesty of `h`. -/
theorem HkMem_succ_of {α : ℝ} (hα : 0 < α) {h : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen h) {k : ℕ} (hk : 1 ≤ k)
    (h1 : Work.Spaces.HkMem α k h) (h2 : Work.Spaces.HkMem α k (Work.Spaces.Dz h))
    (h3 : Work.Spaces.HkMem α k (Work.Spaces.Dth h)) :
    Work.Spaces.HkMem α (k + 1) h := by
  refine Work.FTS.LocData.HkMem_of_majorant α (k + 1)
    (f := h) (M := fun z θ => Work.Spaces.HkIntegrand α k h z θ
      + Work.Spaces.HkIntegrand α k (Work.Spaces.Dz h) z θ
      + Work.Spaces.HkIntegrand α k (Work.Spaces.Dth h) z θ)
    (hsm.continuousOn_HkIntegrand α (k + 1)) ?_ ?_ ?_
  · intro z hz
    exact ((h1.1 z hz).add (h2.1 z hz)).add (h3.1 z hz)
  · have hI : IntegrableOn (fun z => (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k h z θ) + (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (Work.Spaces.Dz h) z θ) + (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (Work.Spaces.Dth h) z θ)) Work.Spaces.Iz :=
      (h1.2.add h2.2).add h3.2
    refine hI.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    have hsum1 : (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k h z θ + Work.Spaces.HkIntegrand α k (Work.Spaces.Dz h) z θ)
        = (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.Dz h) z θ) :=
      MeasureTheory.integral_add (h1.1 z hz) (h2.1 z hz)
    have hsum2 : (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.HkIntegrand α k h z θ + Work.Spaces.HkIntegrand α k (Work.Spaces.Dz h) z θ)
            + Work.Spaces.HkIntegrand α k (Work.Spaces.Dth h) z θ)
        = (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k h z θ + Work.Spaces.HkIntegrand α k (Work.Spaces.Dz h) z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.Dth h) z θ) :=
      MeasureTheory.integral_add ((h1.1 z hz).add (h2.1 z hz)) (h3.1 z hz)
    rw [hsum2, hsum1]
  · intro z hz θ hθ
    exact HkIntegrand_succ_le_IzIθ hα hsm hk z hz θ hθ

/-- **The level shift of the `ℋ^k`-energy**: the squared norm at level `k+1` is bounded by the
sum of the squared norms of `h`, `D_z h` and `D_θ h` at level `k`. -/
theorem HkSq_succ_le {α : ℝ} (hα : 0 < α) {h : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen h) {k : ℕ} (hk : 1 ≤ k)
    (h1 : Work.Spaces.HkMem α k h) (h2 : Work.Spaces.HkMem α k (Work.Spaces.Dz h))
    (h3 : Work.Spaces.HkMem α k (Work.Spaces.Dth h)) :
    Work.Spaces.HkSq α (k + 1) h ≤ Work.Spaces.HkSq α k h
      + Work.Spaces.HkSq α k (Work.Spaces.Dz h) + Work.Spaces.HkSq α k (Work.Spaces.Dth h) := by
  -- ### the `θ`-integral, at every `z ∈ Iz`
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k + 1) h z θ)
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.Dz h) z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.Dth h) z θ) := by
    intro z hz
    have hA : MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.HkIntegrand α k h z θ
          + Work.Spaces.HkIntegrand α k (Work.Spaces.Dz h) z θ
          + Work.Spaces.HkIntegrand α k (Work.Spaces.Dth h) z θ) Work.Spaces.Iθ :=
      ((h1.1 z hz).add (h2.1 z hz)).add (h3.1 z hz)
    have hstep := MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun θ => Work.Spaces.HkIntegrand α (k + 1) h z θ)
      (g := fun θ => Work.Spaces.HkIntegrand α k h z θ
        + Work.Spaces.HkIntegrand α k (Work.Spaces.Dz h) z θ
        + Work.Spaces.HkIntegrand α k (Work.Spaces.Dth h) z θ)
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α (k + 1) h z θ)
      hA
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        fun θ hθ => HkIntegrand_succ_le_IzIθ hα hsm hk z hz θ hθ)
    have hsum1 : (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k h z θ + Work.Spaces.HkIntegrand α k (Work.Spaces.Dz h) z θ)
        = (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.Dz h) z θ) :=
      MeasureTheory.integral_add (h1.1 z hz) (h2.1 z hz)
    have hsum2 : (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.HkIntegrand α k h z θ + Work.Spaces.HkIntegrand α k (Work.Spaces.Dz h) z θ)
            + Work.Spaces.HkIntegrand α k (Work.Spaces.Dth h) z θ)
        = (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k h z θ + Work.Spaces.HkIntegrand α k (Work.Spaces.Dz h) z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.Dth h) z θ) :=
      MeasureTheory.integral_add ((h1.1 z hz).add (h2.1 z hz)) (h3.1 z hz)
    rw [hsum2, hsum1] at hstep
    exact hstep
  -- ### the `z`-integral
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq]
  have hB : MeasureTheory.IntegrableOn (fun z => (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k h z θ) + (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (Work.Spaces.Dz h) z θ) + (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (Work.Spaces.Dth h) z θ)) Work.Spaces.Iz :=
    (h1.2.add h2.2).add h3.2
  have hstepZ := MeasureTheory.integral_mono_of_nonneg
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (f := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k + 1) h z θ)
    (g := fun z => (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ)
      + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.Dz h) z θ)
      + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.Dth h) z θ))
    (Filter.Eventually.of_forall fun z =>
      integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α (k + 1) h z θ)
    hB
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
      fun z hz => hinner z hz)
  have hz1 : (∫ z in Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.Dz h) z θ))
      = (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ)
        + (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (Work.Spaces.Dz h) z θ) :=
    MeasureTheory.integral_add h1.2 h2.2
  have hz2 : (∫ z in Work.Spaces.Iz,
        ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.Dz h) z θ))
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.Dth h) z θ))
      = (∫ z in Work.Spaces.Iz,
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.Dz h) z θ))
        + (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (Work.Spaces.Dth h) z θ) :=
    MeasureTheory.integral_add (h1.2.add h2.2) h3.2
  rw [hz2, hz1] at hstepZ
  exact hstepZ

end Work.FTS.StrongEps.H5
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# `L12Sup4` — the uniform `z`-jet bound `|D_z^b L₁₂(g)(z)| ≤ C |g|_{ℋ⁴}`, `b ≤ 4`

The sibling `Work.FTS.StrongPersist.L3Rhs.L12fJetUniform` covers `b ≤ 3` in the
open-quadrant class (`SmoothOpen g`, `HkMem α 4 g`, `L12 g 0 = 0`).  The missing case is
`b = 4`, where

  `D_z^4 L₁₂(g)(z) = -Q₃(g)(z)`,  `Q_j(g)(z) = ∫_θ K(θ) D_z^j g(z,θ) dθ`,

and `Q₃` is not directly an `L²`-quantity.  What *is* available in the class (from
`Work.FTS.OpenPkg.QangOpen`) is

* the primitive identity `Q₃(z) - Q₃(z₀) = ∫_{z₀}^{z} Q₄(x)/x dx`,
* the weighted `L²`-bounds `∫_Iz Q_j² w² ≤ (∫_θ K²) |g|²_{ℋ⁴}` for `j ≤ 4`,
* continuity of `Q₃` on `(0,∞)`.

Pick `ξ ∈ [1,2]` minimising `Q₃²` on `[1,2]` (`exists_min_le_mean`): then
`Q₃(ξ)² ≤ ∫_1^2 Q₃² ≤ ∫_Iz Q₃² w²` (as `w ≥ 1` on `[1,2]`), and Cauchy–Schwarz on the
interval between `ξ` and `z` against `1/(x w x) = x/(1+x)²` bounds the primitive.  All the
`L²`/measurability bookkeeping is `Work.FTS.H2.CS1D`.
-/

/-! ## Elementary helpers -/

theorem dzdIter_eq_zop_iter (b : ℕ) (u : ℝ → ℝ) :
    Work.Elliptic.DzdIter b u = Work.Spaces.Zop^[b] u := by
  induction b with
  | zero => rfl
  | succ k ih =>
      rw [Work.Elliptic.DzdIter_succ, Function.iterate_succ_apply', ih]
      rfl

theorem one_div_le_w_div (x : ℝ) (hx : 0 < x) :
    1 / x ≤ Work.Spaces.w x / (1 + x) := by
  rw [Work.Spaces.w]
  have h1x : (0 : ℝ) < 1 + x := by linarith
  have hx2 : (0 : ℝ) < x ^ 2 := by positivity
  rw [le_div_iff₀ h1x, le_div_iff₀ hx2]
  field_simp
  nlinarith [hx]

theorem uIoc_subset_Iz {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Set.uIoc a b ⊆ Work.Spaces.Iz := by
  intro x hx
  rcases le_total a b with hle | hle
  · rw [Set.uIoc_of_le hle] at hx
    exact le_of_lt (lt_trans ha hx.1)
  · rw [Set.uIoc_comm a b, Set.uIoc_of_le hle] at hx
    exact le_of_lt (lt_trans hb hx.1)

theorem uIoc_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ} (hx : x ∈ Set.uIoc a b) :
    0 < x := by
  rcases le_total a b with hle | hle
  · rw [Set.uIoc_of_le hle] at hx
    exact lt_trans ha hx.1
  · rw [Set.uIoc_comm a b, Set.uIoc_of_le hle] at hx
    exact lt_trans hb hx.1

theorem measurableSet_uIoc' (a b : ℝ) : MeasurableSet (Set.uIoc a b) := by
  rw [Set.uIoc]
  exact measurableSet_Ioc

theorem continuousOn_w_sq_Icc : ContinuousOn (fun x : ℝ => (Work.Spaces.w x) ^ 2)
    (Set.Icc (1 : ℝ) 2) := by
  have hfun : (fun x : ℝ => (Work.Spaces.w x) ^ 2)
      = fun x : ℝ => (((1 + x) ^ 2 / x ^ 2) ^ 2) := by
    funext x; rw [Work.Spaces.w]
  rw [hfun]
  apply ContinuousOn.pow
  apply ContinuousOn.div
  · exact (continuousOn_const.add continuousOn_id).pow 2
  · exact continuousOn_id.pow 2
  · intro x hx
    exact pow_ne_zero 2 (ne_of_gt (by linarith [hx.1] : (0 : ℝ) < x))

/-! ## The recurrence `D_z^{k+1} L₁₂(g) = -Q_k(g)` for `k ≤ 3` -/

/-- **The recurrence up to order four.**  For `g` smooth on the open quadrant, `HkMem α 4 g`
and `L₁₂(g)(0) = 0`, the `z ∂_z`-iterates of `L₁₂(g)` are the (negated) angular moments,

  `D_z^{k+1} L₁₂(g)(z) = -Q_k(g)(z)`,  `k ≤ 3`, `z > 0`.

This is the `k ≤ 3` truncation of `Work.FTS.StrongPersist.H6Pair6Aux.L12Rec7`; only the
derivatives `∂_z Q_j = Q_{j+1}/z` for `j ≤ 2` are needed, which is
`Work.FTS.OpenPkg.QangOpen.QangDiff_open`. -/
theorem L12_dzdIter_neg_Qang {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem4 : Work.Spaces.HkMem α 4 g)
    (h0 : Work.Construction.L12 g 0 = 0) :
    ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 g z) z
        = - Work.Elliptic.Qang g k z := by
  have hqder : ∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
      HasDerivAt (fun x => Work.Elliptic.Qang g j x) (Work.Elliptic.Qang g (j + 1) z / z) z :=
    (Work.FTS.OpenPkg.QangOpen.QangDiff_open α g hα hα1 hO hmem4).1
  have hderiv : ∀ z : ℝ, 0 < z →
      HasDerivAt (fun z => Work.Construction.L12 g z) (-(Work.Elliptic.L12dens g z)) z := by
    intro z hz
    have h12 := (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk α 4 g hO hmem4
      (by norm_num : 2 ≤ 4)).2 z hz
    refine h12.congr_deriv ?_
    rw [Work.Elliptic.L12dens_eq_three_Fstar_div]
    ring
  intro k
  induction k with
  | zero =>
      intro _ z hz
      have hd : deriv (fun z => Work.Construction.L12 g z) z = -(Work.Elliptic.L12dens g z) :=
        (hderiv z hz).deriv
      change z * deriv (fun z => Work.Construction.L12 g z) z = - Work.Elliptic.Qang g 0 z
      rw [hd, Work.Elliptic.L12dens_eq_Qang_div, mul_neg, neg_inj,
        mul_div_cancel₀ _ (ne_of_gt hz)]
  | succ n ih =>
      intro hn z hz
      have hev : Work.Elliptic.DzdIter (n + 1) (fun z => Work.Construction.L12 g z)
          =ᶠ[𝓝 z] (fun z' => - Work.Elliptic.Qang g n z') := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih (by omega) z' hz'
      have hdv : deriv (Work.Elliptic.DzdIter (n + 1) (fun z => Work.Construction.L12 g z)) z
          = - deriv (fun z' => Work.Elliptic.Qang g n z') z := by
        rw [hev.deriv_eq]
        exact deriv.neg
      change z * deriv (Work.Elliptic.DzdIter (n + 1) (fun z => Work.Construction.L12 g z)) z
          = - Work.Elliptic.Qang g (n + 1) z
      rw [hdv, mul_neg, neg_inj, (hqder n (by omega) z hz).deriv,
        mul_div_cancel₀ _ (ne_of_gt hz)]

/-! ## Cauchy–Schwarz on the interval between the anchor and `z` -/

/-- **The `L²` bound for the fourth angular moment on an interval.**  For `a, b > 0`,

  `|∫_{uIoc a b} Q₄(g)(x)/x dx| ≤ √2 · (∫_θ K²)^{1/2} · |g|_{ℋ⁴}`.

The point is the decomposition `1/x = w(x) · x/(1+x)²`, Cauchy–Schwarz in the form
`CS1D` with `A = |Q₄|·w` (whose square is the radial `ℋ⁴`-slot of `Q₄`) and
`B = 1/(1+x)` (whose square has integral `≤ 2`, `InvOneAddSq`). -/
theorem Qang_four_ioc_integral_le {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem4 : Work.Spaces.HkMem α 4 g)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |∫ x in Set.uIoc a b, Work.Elliptic.Qang g 4 x / x|
      ≤ Real.sqrt 2 * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Work.Spaces.HkNorm α 4 g) := by
  obtain ⟨hInt4, hBnd4⟩ :=
    Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open (α := α) (g := g) hα hα1 hO hmem4
      (i := 4) (by norm_num)
  have hK2nn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 :=
    integral_nonneg fun θ => sq_nonneg _
  have hsub : Set.uIoc a b ⊆ Work.Spaces.Iz := uIoc_subset_Iz ha hb
  have hsub' : Set.uIoc a b ⊆ Set.Ioi (0 : ℝ) := fun x hx => uIoc_pos ha hb hx
  have hμle : volume.restrict (Set.uIoc a b) ≤ volume.restrict Work.Spaces.Iz :=
    MeasureTheory.Measure.restrict_mono hsub le_rfl
  have hmemu : ∀ᵐ x ∂(volume.restrict (Set.uIoc a b)), x ∈ Set.uIoc a b :=
    MeasureTheory.ae_restrict_mem (measurableSet_uIoc' a b)
  -- measurability of `Q₄`
  have hQmeas : AEStronglyMeasurable (fun x => Work.Elliptic.Qang g 4 x)
      (volume.restrict Work.Spaces.Iz) := by
    have h := (Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * Work.Spaces.DzIter 4 g p.1 p.2)
      (Work.FTS.OpenPkg.QangOpen.continuousOn_Ktheta_DzIter_open hO 4)).integral_prod_right'
    simpa only [Work.Elliptic.Qang] using h
  have hAmeas : AEStronglyMeasurable
      (fun x => |Work.Elliptic.Qang g 4 x| * Work.Spaces.w x)
      (volume.restrict (Set.uIoc a b)) := by
    have hw : AEStronglyMeasurable (fun x : ℝ => Work.Spaces.w x)
        (volume.restrict (Set.uIoc a b)) :=
      (by unfold Work.Spaces.w; fun_prop : Measurable fun x : ℝ => Work.Spaces.w x)
        |>.aestronglyMeasurable
    exact MeasureTheory.AEStronglyMeasurable.mul
      (MeasureTheory.AEStronglyMeasurable.mono_measure hQmeas.norm hμle) hw
  have hAint : Integrable (fun x => (|Work.Elliptic.Qang g 4 x| * Work.Spaces.w x) ^ 2)
      (volume.restrict (Set.uIoc a b)) := by
    refine (hInt4.mono_set hsub).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [mul_pow, sq_abs]
  have hAmem : MemLp (fun x => |Work.Elliptic.Qang g 4 x| * Work.Spaces.w x) 2
      (volume.restrict (Set.uIoc a b)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hAmeas).mpr hAint
  -- measurability and integrability of `B`
  have hBmeas : AEStronglyMeasurable (fun x : ℝ => 1 / (1 + x))
      (volume.restrict (Set.uIoc a b)) :=
    (by fun_prop : Measurable fun x : ℝ => 1 / (1 + x)).aestronglyMeasurable
  have hBint : Integrable (fun x : ℝ => (1 / (1 + x)) ^ 2)
      (volume.restrict (Set.uIoc a b)) :=
    (Work.FTS.H2.InvOneAddSq).1.mono_set hsub'
  have hBmem : MemLp (fun x : ℝ => 1 / (1 + x)) 2 (volume.restrict (Set.uIoc a b)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hBmeas).mpr hBint
  -- the pointwise domination
  have hdom : ∀ᵐ x ∂(volume.restrict (Set.uIoc a b)),
      |Work.Elliptic.Qang g 4 x / x|
        ≤ (|Work.Elliptic.Qang g 4 x| * Work.Spaces.w x) * (1 / (1 + x)) := by
    filter_upwards [hmemu] with x hx
    have hxpos : 0 < x := uIoc_pos ha hb hx
    have h1 : 1 / x ≤ Work.Spaces.w x / (1 + x) := one_div_le_w_div x hxpos
    rw [abs_div, abs_of_pos hxpos]
    calc |Work.Elliptic.Qang g 4 x| / x
        = |Work.Elliptic.Qang g 4 x| * (1 / x) := by ring
      _ ≤ |Work.Elliptic.Qang g 4 x| * (Work.Spaces.w x / (1 + x)) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = (|Work.Elliptic.Qang g 4 x| * Work.Spaces.w x) * (1 / (1 + x)) := by ring
  have hA0 : 0 ≤ᵐ[volume.restrict (Set.uIoc a b)]
      (fun x => |Work.Elliptic.Qang g 4 x| * Work.Spaces.w x) :=
    Filter.Eventually.of_forall fun x =>
      mul_nonneg (abs_nonneg _) (by rw [Work.Spaces.w]; positivity)
  have hB0 : 0 ≤ᵐ[volume.restrict (Set.uIoc a b)] (fun x : ℝ => 1 / (1 + x)) := by
    filter_upwards [hmemu] with x hx
    have hxpos : 0 < x := uIoc_pos ha hb hx
    exact div_nonneg zero_le_one (by linarith)
  -- Cauchy–Schwarz
  have hcs := Work.FTS.H2.CS1D (μ := volume.restrict (Set.uIoc a b))
    (g := fun x => Work.Elliptic.Qang g 4 x / x)
    (A := fun x => |Work.Elliptic.Qang g 4 x| * Work.Spaces.w x)
    (B := fun x => 1 / (1 + x)) hAmem hBmem hA0 hB0 hdom
  -- the two `L²`-integrals
  have hA2 : ∫ x, (|Work.Elliptic.Qang g 4 x| * Work.Spaces.w x) ^ 2
        ∂(volume.restrict (Set.uIoc a b))
      ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α 4 g := by
    have hcongr : (fun x => (|Work.Elliptic.Qang g 4 x| * Work.Spaces.w x) ^ 2)
        = fun x => (Work.Elliptic.Qang g 4 x) ^ 2 * (Work.Spaces.w x) ^ 2 := by
      funext x; rw [mul_pow, sq_abs]
    rw [hcongr]
    exact (MeasureTheory.setIntegral_mono_set hInt4
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
        (fun x _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
      (Filter.Eventually.of_forall (fun x hx => hsub hx))).trans hBnd4
  have hB2 : ∫ x, (1 / (1 + x)) ^ 2 ∂(volume.restrict (Set.uIoc a b)) ≤ 2 :=
    (MeasureTheory.setIntegral_mono_set (Work.FTS.H2.InvOneAddSq).1
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun x _ => sq_nonneg _))
      (Filter.Eventually.of_forall (fun x hx => uIoc_pos ha hb hx))).trans
      (Work.FTS.H2.InvOneAddSq).2
  -- assemble
  calc |∫ x in Set.uIoc a b, Work.Elliptic.Qang g 4 x / x|
      = |∫ x, Work.Elliptic.Qang g 4 x / x ∂(volume.restrict (Set.uIoc a b))| := rfl
    _ ≤ Real.sqrt (∫ x, (|Work.Elliptic.Qang g 4 x| * Work.Spaces.w x) ^ 2
          ∂(volume.restrict (Set.uIoc a b)))
          * Real.sqrt (∫ x, (1 / (1 + x)) ^ 2 ∂(volume.restrict (Set.uIoc a b))) := hcs
    _ ≤ Real.sqrt ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Work.Spaces.HkSq α 4 g) * Real.sqrt 2 :=
        mul_le_mul (Real.sqrt_le_sqrt hA2) (Real.sqrt_le_sqrt hB2)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt 2 * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Work.Spaces.HkNorm α 4 g) := by
        rw [Real.sqrt_mul hK2nn]
        simp only [Work.Spaces.HkNorm]
        ring

/-! ## The pointwise bound on the third angular moment -/

/-- **`Q₃` is bounded by the `ℋ⁴`-norm**, uniformly in `z > 0`. -/
theorem Qang_three_abs_le {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem4 : Work.Spaces.HkMem α 4 g)
    {z : ℝ} (hz : 0 < z) :
    |Work.Elliptic.Qang g 3 z|
      ≤ 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Work.Spaces.HkNorm α 4 g := by
  obtain ⟨hInt3, hBnd3⟩ :=
    Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open (α := α) (g := g) hα hα1 hO hmem4
      (i := 3) (by norm_num)
  have hK2nn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 :=
    integral_nonneg fun θ => sq_nonneg _
  have hXnn : 0 ≤ Work.Spaces.HkNorm α 4 g := Work.Spaces.HkNorm_nonneg α 4 g
  -- continuity of `Q₃`
  have hcont3 : ContinuousOn (fun x => Work.Elliptic.Qang g 3 x) (Set.Ioi 0) :=
    Work.FTS.OpenPkg.QangOpen.continuousOn_Qang_open α g hO hmem4 (j := 3) le_rfl
  have hcont3I : ContinuousOn (fun x => Work.Elliptic.Qang g 3 x) (Set.Icc (1 : ℝ) 2) :=
    hcont3.mono fun x hx => Set.mem_Ioi.mpr (by linarith [hx.1])
  have hcont3U : ContinuousOn (fun x => Work.Elliptic.Qang g 3 x) (Set.uIcc (1 : ℝ) 2) := by
    rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
    exact hcont3I
  -- a minimiser of `Q₃²` on `[1,2]`
  obtain ⟨ξ, hξmem, hξmin⟩ := Work.FTS.OpenPkg.ProdOpen.exists_min_le_mean
    (φ := fun x => (Work.Elliptic.Qang g 3 x) ^ 2) (a := 1) (b := 2) (by norm_num)
    (hcont3I.pow 2)
  have hξpos : 0 < ξ := by linarith [hξmem.1]
  -- the anchor value
  have hanchor : (Work.Elliptic.Qang g 3 ξ) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α 4 g := by
    have hwin : (Work.Elliptic.Qang g 3 ξ) ^ 2
        ≤ ∫ x in (1 : ℝ)..2, (Work.Elliptic.Qang g 3 x) ^ 2 := by
      have h := hξmin
      rw [show (2 - 1 : ℝ)⁻¹ = 1 by norm_num, one_mul] at h
      exact h
    have hmono : ∫ x in (1 : ℝ)..2, (Work.Elliptic.Qang g 3 x) ^ 2
        ≤ ∫ x in Work.Spaces.Iz, (Work.Elliptic.Qang g 3 x) ^ 2 * (Work.Spaces.w x) ^ 2 := by
      refine le_trans (intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ ?_)
        (Work.Spaces.hardyZ_integral_Ioc_le_integral_Iz (a := 1) (b := 2) (by norm_num)
          (by norm_num) hInt3 (fun x _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
      · exact (hcont3U.pow 2).intervalIntegrable
      · refine ContinuousOn.intervalIntegrable ?_
        exact (hcont3U.pow 2).mul (by
          rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
          exact continuousOn_w_sq_Icc)
      · intro x hx
        have hw : (1 : ℝ) ≤ (Work.Spaces.w x) ^ 2 := by
          have h1 := Work.FTS.OpenPkg.ProdOpen.one_le_w_of_pos
            (by linarith [hx.1] : (0 : ℝ) < x)
          nlinarith
        nlinarith [sq_nonneg (Work.Elliptic.Qang g 3 x)]
    exact (hwin.trans hmono).trans hBnd3
  -- the primitive identity
  have hprim := Work.FTS.OpenPkg.QangOpen.Qang_primitive_open α g hO hmem4 (j := 3) le_rfl hz hξpos
  -- Cauchy–Schwarz on the interval between `ξ` and `z`
  have hsplit : |∫ x in ξ..z, Work.Elliptic.Qang g 4 x / x|
      = |∫ x in Set.uIoc ξ z, Work.Elliptic.Qang g 4 x / x| := by
    rcases le_total ξ z with hle | hle
    · rw [intervalIntegral.integral_of_le hle, Set.uIoc_of_le hle]
    · rw [intervalIntegral.integral_of_ge hle, Set.uIoc_comm ξ z, Set.uIoc_of_le hle, abs_neg]
  have hcs := Qang_four_ioc_integral_le hα hα1 hO hmem4 (a := ξ) (b := z) hξpos hz
  have hbound : |Work.Elliptic.Qang g 3 z| ≤ Real.sqrt 2
        * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkNorm α 4 g)
      + Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * Work.Spaces.HkNorm α 4 g := by
    have h1 : Work.Elliptic.Qang g 3 z - Work.Elliptic.Qang g 3 ξ
        = ∫ x in ξ..z, Work.Elliptic.Qang g 4 x / x := hprim
    have h2 : |Work.Elliptic.Qang g 3 z|
        ≤ |Work.Elliptic.Qang g 3 z - Work.Elliptic.Qang g 3 ξ|
          + |Work.Elliptic.Qang g 3 ξ| := by
      have h := abs_add_le (Work.Elliptic.Qang g 3 z - Work.Elliptic.Qang g 3 ξ)
        (Work.Elliptic.Qang g 3 ξ)
      rw [sub_add_cancel] at h
      exact h
    have h3 : |Work.Elliptic.Qang g 3 ξ|
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Work.Spaces.HkNorm α 4 g := by
      have h := Real.sqrt_le_sqrt hanchor
      rw [Real.sqrt_mul hK2nn] at h
      rw [Real.sqrt_sq_eq_abs] at h
      exact h
    have h4 : |Work.Elliptic.Qang g 3 z - Work.Elliptic.Qang g 3 ξ| ≤ Real.sqrt 2
        * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkNorm α 4 g) := by
      rw [h1, hsplit]
      exact hcs
    linarith [h2, h3, h4]
  -- `√2·A + A ≤ 3A`
  have hA0 : 0 ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
      * Work.Spaces.HkNorm α 4 g := mul_nonneg (Real.sqrt_nonneg _) hXnn
  calc |Work.Elliptic.Qang g 3 z|
      ≤ Real.sqrt 2 * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkNorm α 4 g)
        + Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Work.Spaces.HkNorm α 4 g := hbound
    _ ≤ 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Work.Spaces.HkNorm α 4 g := by
        have h2 : Real.sqrt 2 ≤ 2 := by
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
        nlinarith [hA0, h2]

/-! ## The main theorem -/

theorem L12Sup4 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
    Work.Construction.L12 g 0 = 0 →
    ∀ b : ℕ, b ≤ 4 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z|
        ≤ C * Work.Spaces.HkNorm α 4 g := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.StrongPersist.L3Rhs.L12fJetUniform
  refine ⟨max C₁ (3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)) + 1,
    by positivity, ?_⟩
  intro α g hα hα1 hO hmem h0 b hb z hz
  have hmem4 : Work.Spaces.HkMem α 4 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hO 4 (by norm_num) hmem
  have hXnn : 0 ≤ Work.Spaces.HkNorm α 4 g := Work.Spaces.HkNorm_nonneg α 4 g
  rcases lt_or_eq_of_le hb with hb4 | hb4
  · -- the case `b ≤ 3`: the mixed jet bound of `L12fJetUniform`
    have hb3 : b ≤ 3 := by omega
    have hjet := hC₁ α hα hα1 g hO hmem4 h0 b hb3 z hz
    calc |Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z|
        = |Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 g z) z| := by
          rw [dzdIter_eq_zop_iter b (fun z => Work.Construction.L12 g z)]
      _ ≤ C₁ * Work.Spaces.HkNorm α 4 g := hjet
      _ ≤ (max C₁ (3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)) + 1)
            * Work.Spaces.HkNorm α 4 g := by
          refine mul_le_mul_of_nonneg_right ?_ hXnn
          have := le_max_left C₁ (3 * Real.sqrt (∫ θ in Work.Spaces.Iθ,
            Work.Elliptic.Ktheta θ ^ 2))
          linarith
  · -- the case `b = 4`: `D_z^4 L₁₂(g) = -Q₃(g)`
    subst hb4
    have hrec := L12_dzdIter_neg_Qang hα hα1 hO hmem4 h0 3 le_rfl z hz
    have hqq := Qang_three_abs_le hα hα1 hO hmem4 hz
    calc |Work.Elliptic.DzdIter 4 (fun z => Work.Construction.L12 g z) z|
        = |Work.Elliptic.Qang g 3 z| := by
          rw [hrec, abs_neg]
      _ ≤ 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkNorm α 4 g := hqq
      _ ≤ (max C₁ (3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)) + 1)
            * Work.Spaces.HkNorm α 4 g := by
          refine mul_le_mul_of_nonneg_right ?_ hXnn
          have := le_max_right C₁ (3 * Real.sqrt (∫ θ in Work.Spaces.Iθ,
            Work.Elliptic.Ktheta θ ^ 2))
          linarith

end Work.FTS.StrongPersist.H6Pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L12Sup6` — uniform-in-`z` bounds on the `D_z`-jets of `L₁₂(g)`, order `≤ 6`

`L₁₂(g)(z) = ∫_z^∞ ∫_θ K(θ) g(r,θ)/r dθ dr` is a function of `z` alone.  This module proves
the pointwise (in `z > 0`) bound

  `|D_z^b L₁₂(g)(z)| ≤ C · |g|_{ℋ⁶}`   for all `b ≤ 6`,

with a universal constant `C > 0`, for every datum of the open-quadrant class
`SmoothOpen g ∧ HkMem α 6 g ∧ HkMem α 7 g` (`α ∈ (0,1]`) with vanishing zero mode
`L₁₂(g)(0) = 0`.

## Route

`D_z^q L₁₂(g)` is the `q`-th slot of the weighted space `ℋ⁶`; the slot bound
(`Work.FTS.StrongPersist.H6Pair6Aux.L12slotLe7`)

  `∫_z (D_z^q L₁₂(g) · w(z))² dz ≤ C₁ · |g|²_{ℋ⁶}`   (`q ≤ 7`)

is the analytic input.  Given it, the pointwise bound is the one-dimensional Agmon/Sobolev
inequality `Work.FTS.OpenPkg.ProdOpen.sob_z_mean` applied to `h = Zop^b (L₁₂ g)` (where
`Zop u = z ∂_z u = Dzd u`):

  `h(z)² ≤ Cz · (∫_1^2 h² + ∫_z (x h'(x) w(x))²)`,

in which the second integral is `∫ (Zop^{b+1} (L₁₂ g) · w)²` — the slot of order `b + 1 ≤ 7` —
and the first is dominated by the slot of order `b` because `w ≥ 1` on `[1,2]`
(`Work.FTS.StrongPersist.L3Rhs.window_le_slot`).  Taking square roots gives the claim; this is
the level-six analogue of `Work.FTS.StrongPersist.L3Rhs.L12fJetUniform` (which is the same
statement at level four, `b ≤ 3`).
-/

namespace Work.FTS.StrongPersist.H6Pair6Aux

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

/-- `Zop^[b] u = DzdIter b u`: both are the `b`-fold iterate of `u ↦ z ∂_z u`. -/
lemma Zop_iter_eq_DzdIter (b : ℕ) (u : ℝ → ℝ) :
    Work.Spaces.Zop^[b] u = Work.Elliptic.DzdIter b u := by
  induction b with
  | zero => rfl
  | succ n ih =>
      funext z
      rw [Function.iterate_succ_apply', ih]
      rfl

theorem L12Sup6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g → Work.Spaces.HkMem α 7 g →
    Work.Construction.L12 g 0 = 0 →
    ∀ b : ℕ, b ≤ 6 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z|
        ≤ C * Work.Spaces.HkNorm α 6 g := by
  obtain ⟨C₁, hC₁pos, hslotC⟩ := L12slotLe7
  obtain ⟨Cz, hCzpos, hCz⟩ := Work.FTS.OpenPkg.ProdOpen.sob_z_mean
  refine ⟨Real.sqrt (2 * Cz * C₁) + 1, ?_, ?_⟩
  · have h : 0 ≤ 2 * Cz * C₁ := by positivity
    linarith [Real.sqrt_nonneg (2 * Cz * C₁)]
  · intro α g hα hα1 hO hmem6 hmem7 h0 b hb z hz
    set φ : ℝ → ℝ := fun z => Work.Construction.L12 g z with hφ
    -- `L₁₂(g)` is `C⁷` on `(0,∞)`
    have hCd : ContDiffOn ℝ 7 φ (Set.Ioi 0) := by
      have h := Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 7 g hα hα1 hO hmem7
        (by norm_num)
      rw [hφ]
      exact h.congr (fun x _ =>
        (congrFun (Work.FTS.H2.constructionL12_eq_ellipticL12 g) x).symm)
    -- the slot bounds, in the `Zop` spelling
    have hslotZ : ∀ q : ℕ, q ≤ 7 →
        MeasureTheory.IntegrableOn
            (fun x => (Work.Spaces.Zop^[q] φ x * Work.Spaces.w x) ^ 2) Work.Spaces.Iz ∧
          (∫ x in Work.Spaces.Iz, (Work.Spaces.Zop^[q] φ x * Work.Spaces.w x) ^ 2)
            ≤ C₁ * Work.Spaces.HkSq α 6 g := by
      intro q hq
      obtain ⟨hi, hb⟩ := hslotC α g hα hα1 hO hmem6 hmem7 h0 q hq
      have heq : (fun x => (Work.Spaces.Zop^[q] φ x * Work.Spaces.w x) ^ 2)
          = (fun x => (Work.Elliptic.DzdIter q (fun y => Work.Construction.L12 g y) x) ^ 2
              * (Work.Spaces.w x) ^ 2) := by
        funext x
        rw [Zop_iter_eq_DzdIter q φ, hφ]
        ring
      rw [heq]
      exact ⟨hi, hb⟩
    -- smoothness of the iterate and of its derivative
    have hCd1 : ContDiffOn ℝ (b + 1) φ (Set.Ioi 0) :=
      hCd.of_le (by exact_mod_cast (by omega : b + 1 ≤ 7))
    have hCd_b : ContDiffOn ℝ (7 - b) (Work.Spaces.Zop^[b] φ) (Set.Ioi 0) :=
      Work.FTS.CoercivityFix.Transfer.E1Parts.contDiffOn_Zop_iter' b (7 - b)
        (by
          have h : b + (7 - b) = 7 := by omega
          rw [← Nat.cast_add, h]
          exact hCd)
    have hder : ∀ x : ℝ, 0 < x →
        HasDerivAt (Work.Spaces.Zop^[b] φ) (deriv (Work.Spaces.Zop^[b] φ) x) x :=
      fun x hx =>
        (Work.FTS.CoercivityFix.Transfer.E1Parts.differentiableAt_Zop_iter_of_contDiffOn
          (u := φ) (b := b) hCd1 hx).hasDerivAt
    have hcont : ContinuousOn (deriv (Work.Spaces.Zop^[b] φ)) (Set.Ioi 0) := by
      have h1 : ((1 : ℕ) : WithTop ℕ∞) ≤ ((7 - b : ℕ) : WithTop ℕ∞) := by
        exact_mod_cast (by omega : 1 ≤ 7 - b)
      exact hCd_b.continuousOn_deriv_of_isOpen isOpen_Ioi h1
    have heq2 : (fun x => (x * deriv (Work.Spaces.Zop^[b] φ) x * Work.Spaces.w x) ^ 2)
        = (fun x => (Work.Spaces.Zop^[b+1] φ x * Work.Spaces.w x) ^ 2) := by
      funext x
      rw [show x * deriv (Work.Spaces.Zop^[b] φ) x = Work.Spaces.Zop^[b+1] φ x from by
        rw [Function.iterate_succ_apply']; rfl]
    have hint : MeasureTheory.IntegrableOn
        (fun x => (x * deriv (Work.Spaces.Zop^[b] φ) x * Work.Spaces.w x) ^ 2)
        Work.Spaces.Iz := by
      rw [heq2]
      exact (hslotZ (b + 1) (by omega)).1
    -- the one-dimensional Sobolev/Agmon inequality
    have hsob := hCz (Work.Spaces.Zop^[b] φ) (deriv (Work.Spaces.Zop^[b] φ))
      z hz hder hcont hint
    rw [heq2] at hsob
    have hwin : (∫ x in (1 : ℝ)..2, (Work.Spaces.Zop^[b] φ x) ^ 2)
        ≤ C₁ * Work.Spaces.HkSq α 6 g :=
      le_trans (Work.FTS.StrongPersist.L3Rhs.window_le_slot (hslotZ b (by omega)).1)
        (hslotZ b (by omega)).2
    have hsq : (Work.Spaces.Zop^[b] φ z) ^ 2 ≤ 2 * Cz * C₁ * Work.Spaces.HkSq α 6 g := by
      have h2 := (hslotZ (b + 1) (by omega)).2
      have hw' : Cz * (∫ x in (1 : ℝ)..2, (Work.Spaces.Zop^[b] φ x) ^ 2)
          ≤ Cz * (C₁ * Work.Spaces.HkSq α 6 g) :=
        mul_le_mul_of_nonneg_left hwin hCzpos.le
      have hs' : Cz * (∫ x in Work.Spaces.Iz,
            (Work.Spaces.Zop^[b+1] φ x * Work.Spaces.w x) ^ 2)
          ≤ Cz * (C₁ * Work.Spaces.HkSq α 6 g) :=
        mul_le_mul_of_nonneg_left h2 hCzpos.le
      nlinarith [hsob, hw', hs']
    have hsqrt : |Work.Spaces.Zop^[b] φ z|
        ≤ Real.sqrt (2 * Cz * C₁) * Work.Spaces.HkNorm α 6 g := by
      have hCn : 0 ≤ 2 * Cz * C₁ := by positivity
      calc |Work.Spaces.Zop^[b] φ z|
          = Real.sqrt ((Work.Spaces.Zop^[b] φ z) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (2 * Cz * C₁ * Work.Spaces.HkSq α 6 g) := Real.sqrt_le_sqrt hsq
        _ = Real.sqrt (2 * Cz * C₁) * Real.sqrt (Work.Spaces.HkSq α 6 g) :=
            Real.sqrt_mul hCn _
        _ = Real.sqrt (2 * Cz * C₁) * Work.Spaces.HkNorm α 6 g := rfl
    calc |Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z|
        = |Work.Spaces.Zop^[b] φ z| := by
          rw [← hφ, ← Zop_iter_eq_DzdIter b φ]
      _ ≤ Real.sqrt (2 * Cz * C₁) * Work.Spaces.HkNorm α 6 g := hsqrt
      _ ≤ (Real.sqrt (2 * Cz * C₁) + 1) * Work.Spaces.HkNorm α 6 g :=
          mul_le_mul_of_nonneg_right
            (by linarith [Real.sqrt_nonneg (2 * Cz * C₁)])
            (Real.sqrt_nonneg (Work.Spaces.HkSq α 6 g))

end Work.FTS.StrongPersist.H6Pair6Aux
end

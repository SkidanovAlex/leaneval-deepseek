/-
# `H5/LevelShift` — the level-shift of the `ℋ^k`-integrand

The `ℋ⁵`-chapter of the `epsWP` interface is built on a single observation: every slot
occurring in `HkIntegrand α (k+1) f` either already occurs in `HkIntegrand α k f` or is a
slot of `HkIntegrand α k (D_z f)` / `HkIntegrand α k (D_θ f)`.  Concretely, on the open
quadrant (where `D_θ^i` and `D_z^j` commute for a smooth `f`) and for `k ≥ 1`,

`HkIntegrand α (k+1) f ≤ HkIntegrand α k f + HkIntegrand α k (D_z f) + HkIntegrand α k (D_θ f)`

(the `k = 0` case is genuinely false: the level-`1` mixed slot `D_θ f · W` is not a slot of any
of the three level-`0` integrands).  This is the lemma that lets the whole `ℋ⁴`-algebra of
`Submission/Work/FTS/OpenPkg/` price the `ℋ⁵`-slots: the derivative
`D_z (f·g) = D_z f · g + f · D_z g` moves the extra derivative onto one factor, which is then
priced by the *level-four* product rules.

The `η`-slots (`D_z^i f`) are handled by `sum_range_succ` + `single_le_sum`; the mixed slots
need the commutativity `D_θ^i (D_z f) = D_z (D_θ^i f)` for smooth `f` on the open quadrant
(`ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.mixed_comm
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.StrongPersist.IP6_lo_coeffs

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

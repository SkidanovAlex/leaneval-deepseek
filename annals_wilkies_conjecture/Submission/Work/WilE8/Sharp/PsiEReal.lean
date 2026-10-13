/-
  WilE8 — the compactification `psi` and its inverse, extended to `EReal`.

  `psi : ℝ → (-1,1)` is the strictly increasing homeomorphism `x ↦ x/√(1+x²)`.  Its inverse
  `psiR : (-1,1) → ℝ` is `u ↦ u/√(1-u²)`.  For the transport of `IsCell`s along `psiV` we need
  the inverse extended to all of `EReal` by `⊥` at `u ≤ -1` and `⊤` at `u ≥ 1`; this is
  `ePsiInv`.  The two defining properties are the adjunctions

    `ePsiInv u < ↑t  ↔  u < ↑(psi t)`   and   `↑t < ePsiInv u  ↔  ↑(psi t) < u`,

  and `ePsiInv` is continuous.

  Everything is self-contained apart from the frozen vocabulary.
-/
import Mathlib
import Submission.Work.WilE8.Basic
import Submission.Work.WilE10.Psi

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilE8.Sharp

open WilkiesDesign WilkiesDesign.E

/-! ## Strict monotonicity of `psi` -/

theorem psi_sq (x : ℝ) : (psi x) ^ 2 = x ^ 2 / (1 + x ^ 2) := by
  rw [psi, div_pow, Real.sq_sqrt (by positivity)]

theorem psi_odd (x : ℝ) : psi (-x) = - psi x := by
  rw [psi, psi, neg_sq]; ring

theorem psi_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ psi x := by
  rw [psi]; exact div_nonneg hx (Real.sqrt_nonneg _)

theorem psi_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < psi x := by
  rw [psi]; exact div_pos hx (Real.sqrt_pos.mpr (by positivity))

theorem psi_neg_of_neg {x : ℝ} (hx : x < 0) : psi x < 0 := by
  have h := psi_pos_of_pos (neg_pos.mpr hx)
  rwa [psi_odd, neg_pos] at h

theorem psi_strictMonoOn : StrictMonoOn psi (Set.Ici 0) := by
  intro x hx y hy hxy
  rw [Set.mem_Ici] at hx hy
  have hx0 : 0 ≤ psi x := psi_nonneg_of_nonneg hx
  have hy0 : 0 ≤ psi y := psi_nonneg_of_nonneg hy
  have hsq : (psi x) ^ 2 < (psi y) ^ 2 := by
    rw [psi_sq, psi_sq, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h := sq_lt_sq.mp hsq
  rwa [abs_of_nonneg hx0, abs_of_nonneg hy0] at h

theorem psi_strictMono : StrictMono psi := by
  intro x y hxy
  by_cases hx : 0 ≤ x
  · exact psi_strictMonoOn hx (le_trans hx hxy.le) hxy
  · have hx' : x < 0 := not_le.mp hx
    by_cases hy : 0 ≤ y
    · exact lt_of_lt_of_le (psi_neg_of_neg hx') (psi_nonneg_of_nonneg hy)
    · have hy' : y < 0 := not_le.mp hy
      have h1 : psi (-y) < psi (-x) :=
        psi_strictMonoOn (show (0:ℝ) ≤ -y by linarith) (show (0:ℝ) ≤ -x by linarith)
          (show -y < -x by linarith)
      rw [psi_odd, psi_odd, neg_lt_neg_iff] at h1
      exact h1

theorem psi_lt_one (x : ℝ) : psi x < 1 := lt_of_abs_lt (Work.WilE10.psi_abs_lt_one x)

theorem psi_neg_one_lt (x : ℝ) : -1 < psi x := by
  have := Work.WilE10.psi_abs_lt_one x
  rw [abs_lt] at this; exact this.1

theorem continuous_psi : Continuous psi := by
  change Continuous (fun x : ℝ => x / Real.sqrt (1 + x ^ 2))
  exact Continuous.div continuous_id (continuous_const.add (continuous_id.pow 2)).sqrt
    (fun x => ne_of_gt (Real.sqrt_pos.mpr (by positivity)))

/-- `psiV` is continuous (coordinatewise `psi`). -/
theorem continuous_psiV (n : ℕ) : Continuous (psiV : (Fin n → ℝ) → (Fin n → ℝ)) := by
  rw [continuous_pi_iff]
  intro i
  exact continuous_psi.comp (continuous_apply i)

/-! ## The extended inverse `ePsiInv` -/

/-- The inverse of `psi`, extended to `EReal` by `⊥` below `-1` and `⊤` above `1`. -/
def ePsiInv (u : EReal) : EReal :=
  match u with
  | ⊥ => ⊥
  | ((s : ℝ) : EReal) =>
      if s ≤ -1 then ⊥ else if 1 ≤ s then ⊤ else ((s / Real.sqrt (1 - s ^ 2) : ℝ) : EReal)
  | ⊤ => ⊤

@[simp] theorem ePsiInv_bot : ePsiInv ⊥ = ⊥ := rfl
@[simp] theorem ePsiInv_top : ePsiInv ⊤ = ⊤ := rfl

theorem ePsiInv_coe (s : ℝ) : ePsiInv (s : EReal) =
    (if s ≤ -1 then ⊥ else if 1 ≤ s then ⊤ else
      ((s / Real.sqrt (1 - s ^ 2) : ℝ) : EReal)) := rfl

theorem ePsiInv_coe_of_le {s : ℝ} (h : s ≤ -1) : ePsiInv (s : EReal) = ⊥ := by
  rw [ePsiInv_coe, if_pos h]

theorem ePsiInv_coe_of_ge {s : ℝ} (h : 1 ≤ s) : ePsiInv (s : EReal) = ⊤ := by
  rw [ePsiInv_coe, if_neg (by linarith), if_pos h]

theorem ePsiInv_coe_of_mid {s : ℝ} (h1 : ¬ s ≤ -1) (h2 : ¬ (1:ℝ) ≤ s) :
    ePsiInv (s : EReal) = ((s / Real.sqrt (1 - s ^ 2) : ℝ) : EReal) := by
  rw [ePsiInv_coe, if_neg h1, if_neg h2]

theorem psi_psiR' {s : ℝ} (hs : |s| < 1) :
    psi (s / Real.sqrt (1 - s ^ 2)) = s := by
  simpa [Work.WilE10.psiR] using Work.WilE10.psi_psiR hs

/-- The lower adjunction, real upper bound. -/
theorem ePsiInv_lt_coe_iff {u : EReal} {t : ℝ} :
    ePsiInv u < (t : EReal) ↔ u < (psi t : EReal) := by
  induction u using EReal.rec with
  | bot => simp
  | coe s =>
      by_cases h1 : s ≤ -1
      · rw [ePsiInv_coe_of_le h1]
        exact ⟨fun _ => EReal.coe_lt_coe (lt_of_le_of_lt h1 (psi_neg_one_lt t)),
          fun _ => EReal.bot_lt_coe t⟩
      · by_cases h2 : (1:ℝ) ≤ s
        · rw [ePsiInv_coe_of_ge h2]
          exact ⟨fun h => absurd h not_top_lt,
            fun h => absurd (lt_of_lt_of_le (psi_lt_one t) h2)
              (not_lt_of_ge (EReal.coe_lt_coe_iff.mp h).le)⟩
        · rw [ePsiInv_coe_of_mid h1 h2, EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff]
          have hs : |s| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
          have hw : psi (s / Real.sqrt (1 - s ^ 2)) = s := psi_psiR' hs
          conv_rhs => rw [← hw]
          exact ⟨fun h => psi_strictMono h, fun h => by
            by_contra hc
            rw [not_lt] at hc
            exact absurd h (not_lt_of_ge (psi_strictMono.monotone hc))⟩
  | top => simp

/-- The upper adjunction, real lower bound. -/
theorem coe_lt_ePsiInv_iff {u : EReal} {t : ℝ} :
    (t : EReal) < ePsiInv u ↔ (psi t : EReal) < u := by
  induction u using EReal.rec with
  | bot => simp
  | coe s =>
      by_cases h1 : s ≤ -1
      · rw [ePsiInv_coe_of_le h1]
        exact ⟨fun h => absurd h not_lt_bot,
          fun h => absurd (lt_of_le_of_lt h1 (psi_neg_one_lt t))
            (not_lt_of_ge (EReal.coe_lt_coe_iff.mp h).le)⟩
      · by_cases h2 : (1:ℝ) ≤ s
        · rw [ePsiInv_coe_of_ge h2]
          exact ⟨fun _ => EReal.coe_lt_coe (lt_of_lt_of_le (psi_lt_one t) h2),
            fun _ => EReal.coe_lt_top t⟩
        · rw [ePsiInv_coe_of_mid h1 h2, EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff]
          have hs : |s| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
          have hw : psi (s / Real.sqrt (1 - s ^ 2)) = s := psi_psiR' hs
          conv_rhs => rw [← hw]
          exact ⟨fun h => psi_strictMono h, fun h => by
            by_contra hc
            rw [not_lt] at hc
            exact absurd h (not_lt_of_ge (psi_strictMono.monotone hc))⟩
  | top => simp

theorem ePsiInv_eq_bot_iff {u : EReal} : ePsiInv u = ⊥ ↔ u ≤ (-1 : ℝ) := by
  induction u using EReal.rec with
  | bot => exact ⟨fun _ => bot_le, fun _ => ePsiInv_bot⟩
  | coe s =>
      rw [EReal.coe_le_coe_iff]
      constructor
      · intro h
        by_contra hcon
        rw [not_le] at hcon
        have h1 : ¬ s ≤ -1 := by linarith
        by_cases h2 : (1:ℝ) ≤ s
        · rw [ePsiInv_coe_of_ge h2] at h; exact bot_ne_top h.symm
        · rw [ePsiInv_coe_of_mid h1 h2] at h; exact EReal.coe_ne_bot _ h
      · intro h
        exact ePsiInv_coe_of_le h
  | top => exact ⟨fun h => absurd h.symm bot_ne_top, fun h => absurd (EReal.coe_lt_top (-1))
      (not_lt_of_ge h)⟩

theorem ePsiInv_eq_top_iff {u : EReal} : ePsiInv u = ⊤ ↔ (1 : ℝ) ≤ u := by
  induction u using EReal.rec with
  | bot => exact ⟨fun h => absurd h bot_ne_top,
      fun h => absurd (le_antisymm h bot_le) (EReal.coe_ne_bot 1)⟩
  | coe s =>
      rw [EReal.coe_le_coe_iff]
      constructor
      · intro h
        by_contra hcon
        rw [not_le] at hcon
        have h2 : ¬ (1:ℝ) ≤ s := by linarith
        by_cases h1 : s ≤ -1
        · rw [ePsiInv_coe_of_le h1] at h; exact bot_ne_top h
        · rw [ePsiInv_coe_of_mid h1 h2] at h; exact EReal.coe_ne_top _ h
      · intro h
        exact ePsiInv_coe_of_ge h
  | top => exact ⟨fun _ => le_top, fun _ => ePsiInv_top⟩

theorem bot_lt_ePsiInv_iff {u : EReal} : (⊥ : EReal) < ePsiInv u ↔ (-1 : ℝ) < u := by
  rw [lt_iff_not_ge, lt_iff_not_ge]
  exact ⟨fun h hu => h (le_of_eq (ePsiInv_eq_bot_iff.mpr hu)),
    fun h hh => h (ePsiInv_eq_bot_iff.mp (le_antisymm hh bot_le))⟩

theorem ePsiInv_lt_top_iff {u : EReal} : ePsiInv u < (⊤ : EReal) ↔ u < (1 : ℝ) := by
  rw [lt_iff_not_ge, lt_iff_not_ge]
  exact ⟨fun h hu => h (le_of_eq (ePsiInv_eq_top_iff.mpr hu).symm),
    fun h hh => h (ePsiInv_eq_top_iff.mp (le_antisymm le_top hh))⟩

/-! ## Continuity of `ePsiInv` -/

theorem continuous_ePsiInv : Continuous ePsiInv := by
  rw [continuous_iff_continuousAt]
  intro p
  rw [ContinuousAt, tendsto_order]
  refine ⟨?_, ?_⟩
  · intro a' ha'
    induction a' using EReal.rec with
    | bot =>
        have hp : (-1 : ℝ) < p := bot_lt_ePsiInv_iff.mp ha'
        filter_upwards [IsOpen.mem_nhds isOpen_Ioi hp] with u hu
        exact bot_lt_ePsiInv_iff.mpr hu
    | coe t =>
        have hp : (psi t : EReal) < p := coe_lt_ePsiInv_iff.mp ha'
        filter_upwards [IsOpen.mem_nhds isOpen_Ioi hp] with u hu
        exact coe_lt_ePsiInv_iff.mpr hu
    | top => exact absurd ha' not_top_lt
  · intro a' ha'
    induction a' using EReal.rec with
    | bot => exact absurd ha' not_lt_bot
    | coe t =>
        have hp : p < (psi t : EReal) := ePsiInv_lt_coe_iff.mp ha'
        filter_upwards [IsOpen.mem_nhds isOpen_Iio hp] with u hu
        exact ePsiInv_lt_coe_iff.mpr hu
    | top =>
        have hp : p < (1 : ℝ) := ePsiInv_lt_top_iff.mp ha'
        filter_upwards [IsOpen.mem_nhds isOpen_Iio hp] with u hu
        exact ePsiInv_lt_top_iff.mpr hu

end Work.WilE8.Sharp

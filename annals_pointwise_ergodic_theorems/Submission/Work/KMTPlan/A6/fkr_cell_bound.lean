import Mathlib
import Submission.Work.KMTPlan.A6.fkrH_cell
import Submission.Work.KMTPlan.A6.fkrH_beta_node
import Submission.Work.KMTPlan.A6.eLpNorm_smul_slope_le

/-!
# The cell bound for the `fkr` interpolation (area A6)

This is the analytic heart of the `fkr` interchange lemma of Krause--Mirek--Tao (Annals 195 (2022),
Lemma `fkr`): the piecewise-linear interpolation `fkrH K β w x t` of the points `(β k, g k x)`,
whose slopes are the densities `w k x = (g k x - g (k-1) x)/(β k - β (k-1))`, is controlled in
`L^r` by the `V^R`-type hypothesis `hho` on the increments of `g`.

The proof decomposes the window `(t0, t1]` into the complete cells of `β` it contains plus the at
most two incomplete end cells: the complete cells telescope (via the density identity) into one
increment `g (q-1) - g p`, which `hho` bounds by `(bK (t1-t0))^{1/R}`, while each incomplete end
cell is bounded by `eLpNorm_smul_slope_le`, again by `bK^{1/R} (t1-t0)^{1/R}`.  The constant is
therefore `3 bK^{1/R} (t1-t0)^{1/R} ≤ 10 bK^{1/R} (t1-t0)^{1/R}` as required.
-/

set_option autoImplicit false

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal BigOperators

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
/-- `fkrH` vanishes on `[0, β 0]`, i.e. below the first node of the interpolation. -/
lemma fkrH_eq_zero_of_le_beta0 {K : ℕ} {β : ℕ → ℝ} {w : ℕ → X → ℂ} {x : X}
    (hβmono : Monotone β) (hβK : β K = 1)
    {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ β 0) :
    fkrH K β w x s = 0 := by
  have hs1 : s ≤ 1 := le_trans hs (by rw [← hβK]; exact hβmono (Nat.zero_le K))
  rw [fkrH]
  refine Finset.sum_eq_zero fun k hk => ?_
  simp only [Finset.mem_Icc] at hk
  have hk0 : 0 ≤ k := by omega
  have hk1 : 0 ≤ k - 1 := by omega
  rw [fkrPhi_le β k hs0 hs1,
    min_eq_left (le_trans hs (hβmono hk0)),
    min_eq_left (le_trans hs (hβmono hk1)),
    sub_self, Complex.ofReal_zero, mul_zero]

/-- `x ↦ fkrH K β w x t` is a.e. strongly measurable when all the densities are. -/
lemma aestronglyMeasurable_fkrH (μ : Measure X) {K : ℕ} {β : ℕ → ℝ} {w : ℕ → X → ℂ}
    (hw : ∀ k, AEStronglyMeasurable (w k) μ) (t : ℝ) :
    AEStronglyMeasurable (fun x => fkrH K β w x t) μ := by
  have hsum : (fun x => fkrH K β w x t)
      = ∑ k ∈ Finset.Icc 1 K, fun x => w k x * ((fkrPhi β k t : ℝ) : ℂ) := by
    funext x; simp [fkrH]
  rw [hsum]
  exact Finset.aestronglyMeasurable_sum _ fun k hk => (hw k).mul_const _

/-- **The cell bound for `fkrH`**, normalised so that both endpoints lie at or above the first node
`β 0`: `‖fkrH t1 - fkrH t0‖_{L^r} ≤ 3 bK^{1/R} (t1 - t0)^{1/R}` for `β 0 ≤ t0 ≤ t1 ≤ 1`.

The window `(t0, t1]` is cut by the nodes of `β` into a block `(β p, β (q-1)]` of *complete* cells
and at most two incomplete cells at the ends.  The complete cells telescope through the density
identity `w k x * (β k - β (k-1)) = g k x - g (k-1) x` to the single difference `g (q-1) - g p`,
which is controlled by the hypothesis `hho`; the two incomplete cells are controlled by the
per-cell estimate `eLpNorm_smul_slope_le`. -/
lemma fkrH_cell_bound_core (μ : Measure X) {r R : ℝ} (hr : 1 ≤ r) (hR : 1 ≤ R)
    {K : ℕ} (hK : 1 ≤ K) (β : ℕ → ℝ) (bK : ℝ) (hbK : 0 < bK)
    (w g : ℕ → X → ℂ) (hβ0 : 0 ≤ β 0) (hβmono : Monotone β) (hβK : β K = 1)
    (hstrict : ∀ k ∈ Finset.Icc 1 K, β (k - 1) < β k)
    (hdens : ∀ k ∈ Finset.Icc 1 K, ∀ x,
        w k x * ((β k - β (k - 1) : ℝ) : ℂ) = g k x - g (k - 1) x)
    (hho : ∀ p q, p ≤ q → q ≤ K →
        eLpNorm (fun x => g q x - g p x) (ENNReal.ofReal r) μ
          ≤ ENNReal.ofReal ((bK * (β q - β p)) ^ (1 / R)))
    (hw : ∀ k, AEStronglyMeasurable (w k) μ)
    {t0 t1 : ℝ} (hlo : β 0 ≤ t0) (hmid_t : t0 ≤ t1) (hhi : t1 ≤ 1) :
    eLpNorm (fun x => fkrH K β w x t1 - fkrH K β w x t0) (ENNReal.ofReal r) μ
      ≤ ENNReal.ofReal (3 * bK ^ (1 / R) * (t1 - t0) ^ (1 / R)) := by
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := ENNReal.one_le_ofReal.mpr hr
  have hb0t1 : 0 ≤ t1 := le_trans (le_trans hβ0 hlo) hmid_t
  have hB0 : (0 : ℝ) ≤ bK ^ (1 / R) := Real.rpow_nonneg hbK.le _
  rcases eq_or_lt_of_le hmid_t with hEq | hlt
  · have hzero : (fun x => fkrH K β w x t1 - fkrH K β w x t0) = 0 := by
      funext x; simp [← hEq]
    rw [hzero, eLpNorm_zero]
    positivity
  · -- find the cell indices
    have hexp : ∃ j, 1 ≤ j ∧ t0 ≤ β j := ⟨K, hK, by rw [hβK]; exact le_trans hmid_t hhi⟩
    have hexq : ∃ j, 1 ≤ j ∧ t1 ≤ β j := ⟨K, hK, by rw [hβK]; exact hhi⟩
    obtain ⟨p, hp1, hpt0, hpK, hpmin⟩ :
        ∃ p, 1 ≤ p ∧ t0 ≤ β p ∧ p ≤ K ∧ ∀ j, 1 ≤ j → j < p → β j < t0 :=
      ⟨Nat.find hexp, (Nat.find_spec hexp).1, (Nat.find_spec hexp).2,
        Nat.find_min' hexp ⟨hK, by rw [hβK]; exact le_trans hmid_t hhi⟩,
        fun j hj1 hjlt => by
          have h := Nat.find_min hexp hjlt
          exact lt_of_not_ge fun hle => h ⟨hj1, hle⟩⟩
    obtain ⟨q, hq1, hqt1, hqK, hqmin⟩ :
        ∃ q, 1 ≤ q ∧ t1 ≤ β q ∧ q ≤ K ∧ ∀ j, 1 ≤ j → j < q → β j < t1 :=
      ⟨Nat.find hexq, (Nat.find_spec hexq).1, (Nat.find_spec hexq).2,
        Nat.find_min' hexq ⟨hK, by rw [hβK]; exact hhi⟩,
        fun j hj1 hjlt => by
          have h := Nat.find_min hexq hjlt
          exact lt_of_not_ge fun hle => h ⟨hj1, hle⟩⟩
    have hpq : p ≤ q := by
      by_contra hcon
      have hlt' : q < p := Nat.lt_of_not_le hcon
      have h1 := hpmin q hq1 hlt'
      linarith [h1, hqt1, hmid_t]
    have hpcell : β (p - 1) ≤ t0 := by
      rcases eq_or_lt_of_le hp1 with h | h
      · rw [h]; simpa using hlo
      · exact le_of_lt (hpmin (p - 1) (by omega) (by omega))
    have hqcell : β (q - 1) ≤ t1 := by
      rcases eq_or_lt_of_le hq1 with h | h
      · rw [h]; simpa using le_trans hlo (le_of_lt hlt)
      · exact le_of_lt (hqmin (q - 1) (by omega) (by omega))
    have hpI : p ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨hp1, hpK⟩
    have hqI : q ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨hq1, hqK⟩
    have hτ0 : (0 : ℝ) ≤ t1 - t0 := by linarith
    rcases eq_or_lt_of_le hpq with hpq_eq | hpq_lt
    · -- ===== same cell =====
      have hqt1' : t1 ≤ β p := by
        have h := hqt1
        rw [← hpq_eq] at h
        exact h
      have hcell1 : ∀ x, fkrH K β w x t1 - fkrH K β w x (β (p - 1))
          = w p x * ((t1 - β (p - 1) : ℝ) : ℂ) :=
        fun x => fkrH_cell (x := x) (w := w) hβ0 hβmono hβK hp1 hpK hb0t1 (le_trans hpcell hmid_t) hqt1'
      have hcell0 : ∀ x, fkrH K β w x t0 - fkrH K β w x (β (p - 1))
          = w p x * ((t0 - β (p - 1) : ℝ) : ℂ) :=
        fun x => fkrH_cell (x := x) (w := w) hβ0 hβmono hβK hp1 hpK (le_trans hβ0 hlo) hpcell hpt0
      have hfun : (fun x => fkrH K β w x t1 - fkrH K β w x t0)
          = fun x => ((t1 - t0 : ℝ) : ℂ) * w p x := by
        funext x
        have h1 := hcell1 x
        have h2 := hcell0 x
        calc fkrH K β w x t1 - fkrH K β w x t0
            = (fkrH K β w x t1 - fkrH K β w x (β (p - 1)))
                - (fkrH K β w x t0 - fkrH K β w x (β (p - 1))) := by ring
          _ = w p x * ((t1 - β (p - 1) : ℝ) : ℂ) - w p x * ((t0 - β (p - 1) : ℝ) : ℂ) := by
              rw [h1, h2]
          _ = w p x * ((t1 - t0 : ℝ) : ℂ) := by
              rw [← mul_sub, ← Complex.ofReal_sub]
              congr 2
              ring
          _ = ((t1 - t0 : ℝ) : ℂ) * w p x := mul_comm _ _
      rw [hfun]
      refine le_trans (eLpNorm_smul_slope_le μ hR (K := K) (β := β) bK hbK w g hdens hho
        (k := p) hpI (hstrict p hpI) (c := t1 - t0) hτ0 (by linarith)) ?_
      refine ENNReal.ofReal_le_ofReal ?_
      calc bK ^ (1 / R) * (t1 - t0) ^ (1 / R)
          = 1 * (bK ^ (1 / R) * (t1 - t0) ^ (1 / R)) := (one_mul _).symm
        _ ≤ 3 * (bK ^ (1 / R) * (t1 - t0) ^ (1 / R)) :=
            mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg hB0 (Real.rpow_nonneg hτ0 _))
        _ = 3 * bK ^ (1 / R) * (t1 - t0) ^ (1 / R) := by ring
    · -- ===== different cells =====
      have hpq1 : p ≤ q - 1 := by omega
      have hqK1 : q - 1 ≤ K := by omega
      have hβpleβq1 : β p ≤ β (q - 1) := hβmono (by omega)
      have ht0_le_βq1 : t0 ≤ β (q - 1) := le_trans hpt0 hβpleβq1
      have hβple_t1 : β p ≤ t1 := le_trans hβpleβq1 hqcell
      have hcellq : ∀ x, fkrH K β w x t1 - fkrH K β w x (β (q - 1))
          = ((t1 - β (q - 1) : ℝ) : ℂ) * w q x := by
        intro x
        rw [fkrH_cell (x := x) (w := w) hβ0 hβmono hβK hq1 hqK hb0t1 hqcell hqt1]
        ring
      have hcellp : ∀ x, fkrH K β w x (β p) - fkrH K β w x t0
          = ((β p - t0 : ℝ) : ℂ) * w p x := by
        intro x
        have h1 : fkrH K β w x t0 - fkrH K β w x (β (p - 1))
            = w p x * ((t0 - β (p - 1) : ℝ) : ℂ) :=
          fkrH_cell (x := x) (w := w) hβ0 hβmono hβK hp1 hpK (le_trans hβ0 hlo) hpcell hpt0
        have h2 : fkrH K β w x (β p) - fkrH K β w x (β (p - 1))
            = w p x * ((β p - β (p - 1) : ℝ) : ℂ) :=
          fkrH_cell (x := x) (w := w) hβ0 hβmono hβK hp1 hpK
          (le_trans hβ0 (hβmono (Nat.zero_le p))) (le_trans hpcell hpt0) (le_refl _)
        calc fkrH K β w x (β p) - fkrH K β w x t0
            = (fkrH K β w x (β p) - fkrH K β w x (β (p - 1)))
                - (fkrH K β w x t0 - fkrH K β w x (β (p - 1))) := by ring
          _ = w p x * ((β p - β (p - 1) : ℝ) : ℂ) - w p x * ((t0 - β (p - 1) : ℝ) : ℂ) := by
              rw [h1, h2]
          _ = w p x * ((β p - t0 : ℝ) : ℂ) := by
              rw [← mul_sub, ← Complex.ofReal_sub]
              congr 2
              ring
          _ = ((β p - t0 : ℝ) : ℂ) * w p x := mul_comm _ _
      have hmid : ∀ x, fkrH K β w x (β (q - 1)) - fkrH K β w x (β p) = g (q - 1) x - g p x := by
        intro x
        rw [fkrH_beta_node (x := x) hβ0 hβmono hβK (fun k hk => hdens k hk x) hqK1,
            fkrH_beta_node (x := x) hβ0 hβmono hβK (fun k hk => hdens k hk x) hpK]
        ring
      have hT1 : eLpNorm (fun x => fkrH K β w x t1 - fkrH K β w x (β (q - 1)))
            (ENNReal.ofReal r) μ
          ≤ ENNReal.ofReal (bK ^ (1 / R) * (t1 - t0) ^ (1 / R)) := by
        rw [funext hcellq]
        refine le_trans (eLpNorm_smul_slope_le μ hR (K := K) (β := β) bK hbK w g hdens hho
          hqI (hstrict q hqI) (c := t1 - β (q - 1)) (by linarith) (by linarith)) ?_
        refine ENNReal.ofReal_le_ofReal ?_
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)) hB0
      have hT3 : eLpNorm (fun x => fkrH K β w x (β p) - fkrH K β w x t0)
            (ENNReal.ofReal r) μ
          ≤ ENNReal.ofReal (bK ^ (1 / R) * (t1 - t0) ^ (1 / R)) := by
        rw [funext hcellp]
        refine le_trans (eLpNorm_smul_slope_le μ hR (K := K) (β := β) bK hbK w g hdens hho
          hpI (hstrict p hpI) (c := β p - t0) (by linarith) (by linarith)) ?_
        refine ENNReal.ofReal_le_ofReal ?_
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)) hB0
      have hT2 : eLpNorm (fun x => fkrH K β w x (β (q - 1)) - fkrH K β w x (β p))
            (ENNReal.ofReal r) μ
          ≤ ENNReal.ofReal (bK ^ (1 / R) * (t1 - t0) ^ (1 / R)) := by
        rw [funext hmid]
        refine le_trans (hho p (q - 1) hpq1 hqK1) ?_
        rw [Real.mul_rpow hbK.le (by linarith : (0 : ℝ) ≤ β (q - 1) - β p)]
        refine ENNReal.ofReal_le_ofReal ?_
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)) hB0
      have hsplit : (fun x => fkrH K β w x t1 - fkrH K β w x t0)
          = fun x => (fkrH K β w x t1 - fkrH K β w x (β (q - 1)))
              + (fkrH K β w x (β (q - 1)) - fkrH K β w x (β p))
              + (fkrH K β w x (β p) - fkrH K β w x t0) := by
        funext x; ring
      rw [hsplit]
      have hmA : AEStronglyMeasurable
          (fun x => fkrH K β w x t1 - fkrH K β w x (β (q - 1))) μ :=
        (aestronglyMeasurable_fkrH μ hw t1).sub (aestronglyMeasurable_fkrH μ hw (β (q - 1)))
      have hmB : AEStronglyMeasurable
          (fun x => fkrH K β w x (β (q - 1)) - fkrH K β w x (β p)) μ :=
        (aestronglyMeasurable_fkrH μ hw (β (q - 1))).sub (aestronglyMeasurable_fkrH μ hw (β p))
      have hmC : AEStronglyMeasurable
          (fun x => fkrH K β w x (β p) - fkrH K β w x t0) μ :=
        (aestronglyMeasurable_fkrH μ hw (β p)).sub (aestronglyMeasurable_fkrH μ hw t0)
      calc eLpNorm (fun x => (fkrH K β w x t1 - fkrH K β w x (β (q - 1)))
              + (fkrH K β w x (β (q - 1)) - fkrH K β w x (β p))
              + (fkrH K β w x (β p) - fkrH K β w x t0)) (ENNReal.ofReal r) μ
          ≤ eLpNorm (fun x => (fkrH K β w x t1 - fkrH K β w x (β (q - 1)))
                + (fkrH K β w x (β (q - 1)) - fkrH K β w x (β p))) (ENNReal.ofReal r) μ
            + eLpNorm (fun x => fkrH K β w x (β p) - fkrH K β w x t0) (ENNReal.ofReal r) μ :=
            eLpNorm_add_le hone
        _ ≤ (eLpNorm (fun x => fkrH K β w x t1 - fkrH K β w x (β (q - 1)))
                (ENNReal.ofReal r) μ
              + eLpNorm (fun x => fkrH K β w x (β (q - 1)) - fkrH K β w x (β p))
                (ENNReal.ofReal r) μ)
            + eLpNorm (fun x => fkrH K β w x (β p) - fkrH K β w x t0) (ENNReal.ofReal r) μ :=
            add_le_add (eLpNorm_add_le hone) le_rfl
        _ ≤ (ENNReal.ofReal (bK ^ (1 / R) * (t1 - t0) ^ (1 / R))
              + ENNReal.ofReal (bK ^ (1 / R) * (t1 - t0) ^ (1 / R)))
            + ENNReal.ofReal (bK ^ (1 / R) * (t1 - t0) ^ (1 / R)) :=
            add_le_add (add_le_add hT1 hT2) hT3
        _ = ENNReal.ofReal (bK ^ (1 / R) * (t1 - t0) ^ (1 / R)
              + bK ^ (1 / R) * (t1 - t0) ^ (1 / R)
              + (bK ^ (1 / R) * (t1 - t0) ^ (1 / R))) := by
            have hx : (0 : ℝ) ≤ bK ^ (1 / R) * (t1 - t0) ^ (1 / R) :=
              mul_nonneg hB0 (Real.rpow_nonneg hτ0 _)
            rw [← ENNReal.ofReal_add hx hx, ← ENNReal.ofReal_add (add_nonneg hx hx) hx]
        _ ≤ ENNReal.ofReal (3 * bK ^ (1 / R) * (t1 - t0) ^ (1 / R)) :=
            ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

theorem fkr_cell_bound {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X) {r : ℝ}
    (hr : 1 ≤ r) {R : ℝ} (hR : 1 ≤ R) {K : ℕ} (β : ℕ → ℝ) (bK : ℝ) (hbK : 0 < bK)
    (w : ℕ → X → ℂ) (g : ℕ → X → ℂ) (hβ0 : 0 ≤ β 0) (hβmono : Monotone β)
    (hβK : β K = 1) (hstrict : ∀ k ∈ Finset.Icc (1 : ℕ) K, β (k - 1) < β k)
    (hdens : ∀ k ∈ Finset.Icc (1 : ℕ) K, ∀ x,
        w k x * ((β k - β (k - 1) : ℝ) : ℂ) = g k x - g (k - 1) x)
    (hho : ∀ p q, p ≤ q → q ≤ K →
        MeasureTheory.eLpNorm (fun x => g q x - g p x) (ENNReal.ofReal r) μ
          ≤ ENNReal.ofReal ((bK * (β q - β p)) ^ (1 / R)))
    (hw : ∀ k, MeasureTheory.AEStronglyMeasurable (w k) μ)
    (hg : ∀ k, MeasureTheory.AEStronglyMeasurable (g k) μ)
    {t0 t1 : ℝ} (ht0 : 0 ≤ t0) (ht1 : t0 ≤ t1) (ht2 : t1 ≤ 1) :
    MeasureTheory.eLpNorm (fun x => Work.KMTPlan.A6.fkrH K β w x t1
        - Work.KMTPlan.A6.fkrH K β w x t0) (ENNReal.ofReal r) μ
      ≤ ENNReal.ofReal (10 * bK ^ (1 / R) * (t1 - t0) ^ (1 / R)) := by
  have hB0 : (0 : ℝ) ≤ bK ^ (1 / R) := Real.rpow_nonneg hbK.le _
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · -- K = 0 : the interpolant vanishes
    have hdir : ∀ x : X, ∀ t : ℝ, fkrH K β w x t = 0 := by
      intro x t
      have h : Finset.Icc (1 : ℕ) K = ∅ := by rw [hK0]; exact Finset.Icc_eq_empty (by omega)
      rw [fkrH, h, Finset.sum_empty]
    have hzero : (fun x => fkrH K β w x t1 - fkrH K β w x t0) = 0 := by
      funext x; rw [hdir x t1, hdir x t0]; simp
    rw [hzero, eLpNorm_zero]
    positivity
  · by_cases hcase : t1 ≤ β 0
    · -- both endpoints below the first node
      have hzero : (fun x => fkrH K β w x t1 - fkrH K β w x t0) = 0 := by
        funext x
        rw [fkrH_eq_zero_of_le_beta0 (x := x) hβmono hβK (le_trans ht0 ht1) hcase,
          fkrH_eq_zero_of_le_beta0 (x := x) hβmono hβK ht0 (le_trans ht1 hcase)]
        simp
      rw [hzero, eLpNorm_zero]
      positivity
    · have hgt : β 0 < t1 := lt_of_not_ge hcase
      have htmax : max t0 (β 0) ≤ t1 := max_le ht1 (le_of_lt hgt)
      have hcore := fkrH_cell_bound_core μ hr hR hKpos β bK hbK w g hβ0 hβmono hβK hstrict
        hdens hho hw (t0 := max t0 (β 0)) (t1 := t1)
        (hlo := le_max_right t0 (β 0)) (hmid_t := htmax) (hhi := ht2)
      have hFeq : ∀ x, fkrH K β w x (max t0 (β 0)) = fkrH K β w x t0 := by
        intro x
        rcases lt_or_ge t0 (β 0) with h | h
        · rw [max_eq_right (le_of_lt h),
            fkrH_eq_zero_of_le_beta0 (x := x) hβmono hβK ht0 (le_of_lt h)]
          exact fkrH_eq_zero_of_le_beta0 (x := x) hβmono hβK hβ0 le_rfl
        · rw [max_eq_left h]
      have hfun : (fun x => fkrH K β w x t1 - fkrH K β w x t0)
          = fun x => fkrH K β w x t1 - fkrH K β w x (max t0 (β 0)) := by
        funext x; rw [← hFeq x]
      rw [hfun]
      refine le_trans hcore (ENNReal.ofReal_le_ofReal ?_)
      have hu0 : (0 : ℝ) ≤ t1 - max t0 (β 0) := by linarith
      have huv : t1 - max t0 (β 0) ≤ t1 - t0 := by
        have := le_max_left t0 (β 0); linarith
      have hpow : (t1 - max t0 (β 0)) ^ (1 / R) ≤ (t1 - t0) ^ (1 / R) :=
        Real.rpow_le_rpow hu0 huv (by positivity)
      have hτ0 : (0 : ℝ) ≤ t1 - t0 := by linarith
      have hx0 : (0 : ℝ) ≤ bK ^ (1 / R) * (t1 - t0) ^ (1 / R) :=
        mul_nonneg hB0 (Real.rpow_nonneg hτ0 _)
      calc 3 * bK ^ (1 / R) * (t1 - max t0 (β 0)) ^ (1 / R)
          ≤ 3 * bK ^ (1 / R) * (t1 - t0) ^ (1 / R) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = 3 * (bK ^ (1 / R) * (t1 - t0) ^ (1 / R)) := by ring
        _ ≤ 10 * (bK ^ (1 / R) * (t1 - t0) ^ (1 / R)) :=
            mul_le_mul_of_nonneg_right (by norm_num) hx0
        _ = 10 * bK ^ (1 / R) * (t1 - t0) ^ (1 / R) := by ring

end Work.KMTPlan.A6

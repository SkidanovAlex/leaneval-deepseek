import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Continuity of the weighted quadratic form on `L²(Conf N)`

For a weight `W : Conf N → ℝ` which is bounded (`BddBy N W M`) and almost
everywhere measurable (`AEMeas N W`), the quadratic form `φ ↦ ∫ W φ²` is
continuous on `L²(Conf N) = Lp ℝ 2 (volC N)`.  This is the form-level
convergence `tendsto_potSq` needed for the bosonic reduction.

The argument (built from scratch here) is:

* `W` is a bounded a.e. measurable function, hence an element `Wop` of
  `Lp ℝ ∞ (volC N)`; multiplying by it is a bounded operator on `L²` with
  norm at most `M` (`Lp.norm_le_mul_norm_of_ae_le_mul`);
* the identity `∫ W a² = ⟪Wop • a, a⟫` holds (a.e. comparison of the
  representatives, `L2.inner_def`);
* consequently
  `∫ W f² - ∫ W g² = ⟪Wop • (f - g), f + g⟫`, which gives the quantitative
  estimate `|∫ W f² - ∫ W g²| ≤ M ‖f - g‖ (‖f - g‖ + 2 ‖g‖)`.

The limit statement then follows by squeezing with `‖u n - v‖ → 0`.
-/

namespace Work.BoseSym.Form

open MeasureTheory Filter
open scoped Topology ENNReal

set_option autoImplicit false

/-- Quantitative estimate for the difference of the weighted quadratic forms:
for `|W| ≤ M` and `f, g ∈ L²`,
`|∫ W f² - ∫ W g²| ≤ M ‖f - g‖ (‖f - g‖ + 2 ‖g‖)`. -/
private theorem mulSq_sub_le_aux {N : ℕ} {W : Conf N → ℝ} {M : ℝ} (hW : BddBy N W M)
    (hWm : AEMeas N W) (hM : 0 ≤ M) (f g : L2 N) :
    |intC N (fun x => W x * ((f : Conf N → ℝ) x) ^ 2)
      - intC N (fun x => W x * ((g : Conf N → ℝ) x) ^ 2)|
    ≤ M * ‖f - g‖ * (‖f - g‖ + 2 * ‖g‖) := by
  have hWmem : MemLp W (⊤ : ℝ≥0∞) (volC N) :=
    memLp_top_of_bound hWm.aestronglyMeasurable M (Filter.Eventually.of_forall hW)
  let Wop : Lp ℝ (⊤ : ℝ≥0∞) (volC N) := hWmem.toLp W
  have hWop_ae : (Wop : Conf N → ℝ) =ᵐ[volC N] W := MemLp.coeFn_toLp hWmem
  -- the weighted pairing is symmetric
  have hsymm : ∀ a b : L2 N, inner ℝ (Wop • a : L2 N) b = inner ℝ (Wop • b : L2 N) a := by
    intro a b
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    simp only [Real.inner_apply]
    refine integral_congr_ae ?_
    filter_upwards [MeasureTheory.Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) Wop a,
      MeasureTheory.Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) Wop b] with x ha hb
    simp only [ha, hb, Pi.smul_apply', smul_eq_mul]
    ring
  -- the identity `∫ W a² = ⟪Wop • a, a⟫`
  have hIdent : ∀ a : L2 N,
      intC N (fun x => W x * ((a : Conf N → ℝ) x) ^ 2) = inner ℝ (Wop • a : L2 N) a := by
    intro a
    rw [intC, MeasureTheory.L2.inner_def]
    simp only [Real.inner_apply]
    refine integral_congr_ae ?_
    filter_upwards [MeasureTheory.Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) Wop a,
      hWop_ae] with x hx hWx
    simp only [hx, Pi.smul_apply', smul_eq_mul, hWx]
    ring
  -- boundedness of the multiplication operator
  have hnorm : ∀ a : L2 N, ‖(Wop • a : L2 N)‖ ≤ M * ‖a‖ := by
    intro a
    refine MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [MeasureTheory.Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) Wop a,
      hWop_ae] with x hx hWx
    simp only [hx, Pi.smul_apply', smul_eq_mul, hWx, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hW x) (abs_nonneg _)
  -- linearity in the second argument
  have hsub : ∀ a b : L2 N,
      (Wop • (a - b) : L2 N) = (Wop • a : L2 N) - (Wop • b : L2 N) := by
    intro a b
    rw [eq_sub_iff_add_eq, ← MeasureTheory.Lp.add_smul, sub_add_cancel]
  -- the key identity for the difference of the forms
  have hKey : ∀ a b : L2 N,
      intC N (fun x => W x * ((a : Conf N → ℝ) x) ^ 2)
        - intC N (fun x => W x * ((b : Conf N → ℝ) x) ^ 2)
      = inner ℝ (Wop • (a - b) : L2 N) (a + b) := by
    intro a b
    simp only [hIdent a, hIdent b, hsub a b, inner_sub_left, inner_add_right, hsymm b a]
    ring
  calc |intC N (fun x => W x * ((f : Conf N → ℝ) x) ^ 2)
        - intC N (fun x => W x * ((g : Conf N → ℝ) x) ^ 2)|
      = |inner ℝ (Wop • (f - g) : L2 N) (f + g)| := by rw [hKey f g]
    _ ≤ ‖(Wop • (f - g) : L2 N)‖ * ‖f + g‖ := abs_real_inner_le_norm _ _
    _ ≤ M * ‖f - g‖ * ‖f + g‖ := by
        have := hnorm (f - g)
        exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    _ ≤ M * ‖f - g‖ * (‖f - g‖ + 2 * ‖g‖) := by
        have hfvg : ‖f + g‖ ≤ ‖f - g‖ + 2 * ‖g‖ := by
          have hsplit : f + g = (f - g) + (2 : ℝ) • g := by rw [two_smul]; abel
          rw [hsplit]
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, Real.norm_eq_abs]
          norm_num
        exact mul_le_mul_of_nonneg_left hfvg (mul_nonneg hM (norm_nonneg _))

theorem tendsto_potSq {N : ℕ} {W : Conf N → ℝ} {M : ℝ} (hW : BddBy N W M) (hWm : AEMeas N W)
    {u : ℕ → L2 N} {v : L2 N} (h : TendstoL2 N u v) :
    TendstoR (fun n => intC N (fun x => W x * ((u n : Conf N → ℝ) x) ^ 2))
      (intC N (fun x => W x * ((v : Conf N → ℝ) x) ^ 2)) := by
  have hM : 0 ≤ M := by
    have h0 := hW (fun _ => (0 : E3))
    exact le_trans (abs_nonneg _) h0
  have hsub_lim : Tendsto (fun n => u n - v) atTop (nhds 0) := by
    have h' := h.sub (tendsto_const_nhds (x := v))
    simpa using h'
  have hnormlim : Tendsto (fun n => ‖u n - v‖) atTop (nhds 0) := by
    simpa using hsub_lim.norm
  rw [TendstoR]
  refine tendsto_sub_nhds_zero_iff.mp ?_
  have hb : ∀ n, |intC N (fun x => W x * ((u n : Conf N → ℝ) x) ^ 2)
      - intC N (fun x => W x * ((v : Conf N → ℝ) x) ^ 2)|
      ≤ M * ‖u n - v‖ * (‖u n - v‖ + 2 * ‖v‖) :=
    fun n => mulSq_sub_le_aux hW hWm hM (u n) v
  have habs : Tendsto (fun n => |intC N (fun x => W x * ((u n : Conf N → ℝ) x) ^ 2)
      - intC N (fun x => W x * ((v : Conf N → ℝ) x) ^ 2)|) atTop (nhds 0) := by
    refine squeeze_zero
      (f := fun n => |intC N (fun x => W x * ((u n : Conf N → ℝ) x) ^ 2)
        - intC N (fun x => W x * ((v : Conf N → ℝ) x) ^ 2)|)
      (g := fun n => M * ‖u n - v‖ * (‖u n - v‖ + 2 * ‖v‖))
      (fun n => abs_nonneg _) hb ?_
    have h2 : Tendsto (fun n => ‖u n - v‖ + 2 * ‖v‖) atTop (nhds (0 + 2 * ‖v‖)) :=
      hnormlim.add (tendsto_const_nhds (x := 2 * ‖v‖))
    have h3 := (hnormlim.const_mul M).mul h2
    simpa using h3
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [Real.norm_eq_abs] using habs

end Work.BoseSym.Form

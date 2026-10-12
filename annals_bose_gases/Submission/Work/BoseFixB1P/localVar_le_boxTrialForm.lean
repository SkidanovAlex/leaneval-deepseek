import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.arith_final_le
import Submission.Work.BoseFixB1S.integral_sq_sub_mul
import Submission.Work.BoseFixB1S.integral_sq_sub_mul_add_const
import Submission.Work.BoseFixB1S.two_mul_integral_mul_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1P

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Two elementary facts about `Box3` used below -/

/-- **The axis-parallel box `Box3 p q` is compact.**  It is the image of the compact
coordinate box `Set.Icc p q ⊆ (Fin 3 → ℝ)` under the continuous bijection
`WithLp.toLp 2`.  (For `q j < p j` the box is empty, which is compact as well.) -/
private lemma isCompact_Box3 (p q : Fin 3 → ℝ) : IsCompact (Box3 p q) := by
  have h : Box3 p q = WithLp.toLp 2 '' Set.Icc p q := by
    ext x
    constructor
    · intro hx
      refine ⟨x.ofLp, ?_, ?_⟩
      · rw [Set.mem_Icc]; exact ⟨fun j => (hx j).1, fun j => (hx j).2⟩
      · simp
    · rintro ⟨y, hy, rfl⟩ j
      rw [Set.mem_Icc] at hy
      exact ⟨hy.1 j, hy.2 j⟩
  rw [h]
  exact (isCompact_Icc (a := p) (b := q)).image (PiLp.continuous_toLp ..)

/-- The Bochner integral of a constant over a set is the constant times its real volume. -/
private lemma integral_const_box (P : Set ℝ³) (c : ℝ) :
    (∫ x in P, c) = c * volBox P := by
  rw [MeasureTheory.setIntegral_const]
  simp [volBox, MeasureTheory.Measure.real_def, smul_eq_mul, mul_comm]

/-- **The per-box inequality of the gap pairing.**  For an axis-parallel box `P = Box3 p q` with
all sides `<= a` (`0 < a`), `c = a^(-2)`, positive volume, a smooth function `h` and a smooth trial
`g`:

    localVar P h <= (1 + pi^(-2)) * boxTrialForm c P h g ,

where `localVar P h = int_P (h - |P|^(-1) int_P h)^2` is the local mean-free mass and
`boxTrialForm` is the `neuFrac` trial functional.  (`hpoin` is the sharp mean-free Poincare
inequality on the box, which the caller supplies; it holds for such boxes.)

Route, all elementary given `hpoin`:
* expand `boxTrialForm c P h g = int_P (h - c*g)^2 + c * sum_k int_P (partial_k g)^2`;
* write `m := |P|^(-1) int_P h`, `u := h - m` (mean-free) and `g = m/c + v`, so that
  `h - c*g = u - c*v` and `grad v = grad g`; split `v` into its mean `n` and the mean-free part
  `v0 = v - n`; the mean part contributes the perfect square `|P| (m - c*n)^2 >= 0` (only `u` perp 1
  is used), so it suffices to bound `int_P u^2 - 2c int_P u v0 + c sum_k int_P (partial_k v0)^2`
  from below;
* there `hpoin` at `v0` gives `pi^2 c int_P v0^2 <= sum_k int_P (partial_k v0)^2`, and the real
  inequality `2c*t*w <= c*lam*w^2 + c^2*w^2 + t^2/(1+pi^2)` for `pi^2*c <= lam` (completing the
  square: `t^2/(1+pi^2) - 2ctw + (c*lam+c^2)w^2 = (t/sqrt(1+pi^2) - cw sqrt(1+pi^2))^2 + c(lam-pi^2c)w^2
  >= 0`) bounds the cross term with `t = ||u||`, `w = ||v0||`, `lam = pi^2/a^2`; note
  `(1+pi^(-2))^(-1) = 1 - 1/(1+pi^2)`. -/
theorem localVar_le_boxTrialForm {a c : ℝ} (ha : 0 < a) (hc : c = a ^ (-2 : ℤ))
    (p q : Fin 3 → ℝ) (hpq : ∀ j : Fin 3, q j - p j ≤ a)
    (hvol : 0 < Work.BoseFixB1P.volBox (Work.BoseFixB1P.Box3 p q))
    (h g : EuclideanSpace ℝ (Fin 3) → ℝ) (hh : ContDiff ℝ (⊤ : ENat) h)
    (hg : ContDiff ℝ (⊤ : ENat) g)
    (hpoin : ∀ v : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ENat) v →
      (∫ x in Work.BoseFixB1P.Box3 p q, v x) = 0 →
      Real.pi ^ 2 / a ^ 2 * (∫ x in Work.BoseFixB1P.Box3 p q, (v x) ^ 2)
        ≤ ∑ k : Fin 3, ∫ x in Work.BoseFixB1P.Box3 p q,
            (fderiv ℝ v x (Submission.BoseGases.kcStdBasis k)) ^ 2) :
    Work.BoseFixB1P.localVar (Work.BoseFixB1P.Box3 p q) h
      ≤ (1 + (Real.pi ^ 2)⁻¹) * Work.BoseFixB1P.boxTrialForm c (Work.BoseFixB1P.Box3 p q) h g := by
  classical
  -- the box, its compactness, and integrability of continuous functions on it
  set P : Set ℝ³ := Box3 p q with hPdef
  have hPcomp : IsCompact P := by rw [hPdef]; exact isCompact_Box3 p q
  have hVne : volBox P ≠ 0 := by rw [hPdef]; exact ne_of_gt hvol
  have hint : ∀ {f : ℝ³ → ℝ}, Continuous f → IntegrableOn f P volume :=
    fun {f} hf => ContinuousOn.integrableOn_compact hPcomp hf.continuousOn
  -- means, mean-free parts and the mismatch constant
  set M : ℝ := ∫ x in P, h x with hMdef
  set m : ℝ := (1 / volBox P) * M with hmdef
  set N : ℝ := ∫ x in P, g x with hNdef
  set n : ℝ := (1 / volBox P) * N with hndef
  set u : ℝ³ → ℝ := fun x => h x - m with hudef
  set w : ℝ³ → ℝ := fun x => g x - n with hwdef
  set D : ℝ := m - c * n with hDdef
  have hu_cont : Continuous u := by rw [hudef]; exact hh.continuous.sub continuous_const
  have hw_cont : Continuous w := by rw [hwdef]; exact hg.continuous.sub continuous_const
  have hh_int : IntegrableOn h P volume := hint hh.continuous
  have hg_int : IntegrableOn g P volume := hint hg.continuous
  have hu_int : IntegrableOn u P volume := hint hu_cont
  have hw_int : IntegrableOn w P volume := hint hw_cont
  have hm_int : IntegrableOn (fun _ : ℝ³ => m) P volume := hint continuous_const
  have hn_int : IntegrableOn (fun _ : ℝ³ => n) P volume := hint continuous_const
  have hmM : m * volBox P = M := by rw [hmdef]; field_simp
  have hnN : n * volBox P = N := by rw [hndef]; field_simp
  -- the mean-free parts have vanishing integral
  have hu_zero : (∫ x in P, u x) = 0 := by
    rw [hudef, MeasureTheory.integral_sub hh_int hm_int, integral_const_box, hmM, sub_self]
  have hw_zero : (∫ x in P, w x) = 0 := by
    rw [hwdef, MeasureTheory.integral_sub hg_int hn_int, integral_const_box, hnN, sub_self]
  have hw_cd : ContDiff ℝ (⊤ : ENat) w := by rw [hwdef]; exact hg.sub contDiff_const
  -- aggregated quantities
  set A : ℝ := ∫ x in P, (u x) ^ 2 with hAdef
  set B : ℝ := ∫ x in P, u x * w x with hBdef
  set C : ℝ := ∫ x in P, (w x) ^ 2 with hCdef
  set Sw : ℝ := ∑ k : Fin 3, ∫ x in P,
      (fderiv ℝ w x (Submission.BoseGases.kcStdBasis k)) ^ 2 with hSwdef
  set Sg : ℝ := ∑ k : Fin 3, ∫ x in P,
      (fderiv ℝ g x (Submission.BoseGases.kcStdBasis k)) ^ 2 with hSgdef
  set T : ℝ := boxTrialForm c P h g with hTdef
  -- the sharp Poincare inequality at the mean-free part of `g`
  have hpoin_w : Real.pi ^ 2 / a ^ 2 * C ≤ Sw := hpoin w hw_cd hw_zero
  -- (1) the trial form, expanded around `h - c*g`
  have hT1 : T = (∫ x in P, (h x - c * g x) ^ 2) + c * Sg := by
    rw [hTdef, boxTrialForm, hSgdef,
      Work.BoseFixB1S.integral_sq_sub_mul hPcomp hh.continuous hg.continuous c]
    ring
  -- (2) `h - c*g = (u - c*w) + D`
  have hT2 : (∫ x in P, (h x - c * g x) ^ 2) = ∫ x in P, (u x - c * w x + D) ^ 2 := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [hudef, hwdef, hDdef]
    ring
  -- (3) the kinetic sums of `g` and of its mean-free part `w` agree
  have hSv : Sg = Sw := by
    rw [hSgdef, hSwdef]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [hwdef, fderiv_sub_const]
  -- (4) expansion of the shifted square against `A - 2cB + c²C`
  have hT3 : A - 2 * c * B + c ^ 2 * C ≤ ∫ x in P, (u x - c * w x + D) ^ 2 := by
    have hexp := Work.BoseFixB1S.integral_sq_sub_mul_add_const hPcomp hu_cont hw_cont c D
    rw [hexp, hAdef, hBdef, hCdef, hu_zero, hw_zero]
    have hvolnn : 0 ≤ volBox P := volBox_nonneg P
    nlinarith [sq_nonneg D, hvolnn]
  -- (5) the two-variable Young inequality at the sharp parameter `1 + pi^2`
  have hamgm : 2 * c * B ≤ (1 + Real.pi ^ 2)⁻¹ * A + (1 + Real.pi ^ 2) * c ^ 2 * C := by
    have hraw := Work.BoseFixB1S.two_mul_integral_mul_le hPcomp hu_cont hw_cont c
    rw [← hAdef, ← hBdef, ← hCdef] at hraw
    exact hraw
  -- (6) the Poincare term, scaled by `c > 0`
  have hcpos : 0 < c := by rw [hc]; positivity
  have hSc : c * (Real.pi ^ 2 / a ^ 2 * C) ≤ c * Sw :=
    mul_le_mul_of_nonneg_left hpoin_w (le_of_lt hcpos)
  have h4 : c * (Real.pi ^ 2 / a ^ 2 * C) = Real.pi ^ 2 * c ^ 2 * C := by
    have h1 : c = (a ^ 2)⁻¹ := by rw [hc, zpow_neg, zpow_ofNat]
    rw [h1, div_eq_mul_inv]
    ring
  -- (7) the lower bound for the trial form
  have hT_expr : T = (∫ x in P, (u x - c * w x + D) ^ 2) + c * Sw := by rw [hT1, hT2, hSv]
  have hTlb : A - 2 * c * B + (1 + Real.pi ^ 2) * c ^ 2 * C ≤ T := by
    have hgoal : A - 2 * c * B + (1 + Real.pi ^ 2) * c ^ 2 * C
        = (A - 2 * c * B + c ^ 2 * C) + Real.pi ^ 2 * c ^ 2 * C := by ring
    rw [hgoal, hT_expr]
    linarith [hT3, hSc, h4]
  -- (8) the scalar arithmetic, and identification of `localVar P h` with `A`
  have hfinal : A ≤ (1 + (Real.pi ^ 2)⁻¹) * T := Work.BoseFixB1S.arith_final_le hTlb hamgm
  have hloc : localVar (Box3 p q) h = A := by
    rw [localVar, hAdef, hudef, hmdef, hMdef, hPdef]
  rw [hloc]
  exact hfinal

end Work.BoseFixB1P

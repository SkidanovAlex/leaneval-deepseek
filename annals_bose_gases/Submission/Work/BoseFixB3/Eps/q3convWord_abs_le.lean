import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.Eps.highSlot_chiSq_aP_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixB3/Eps/q3convWord_abs_le`

The **`ε₂`-size bound** for the convolution word `q3convWord` of
`Work.BoseFixB3.Defs` (FS `lem:Convolution`'s output word, FS §7,
`Papers/fournais_solovej/final_v2.tex` ll. 1531–1545):

  `|q3convWord fc κ ℓ I Φ| ≤ |I| ℓ⁻³ C (n² ‖Φ‖²)`

whenever `|hRes fc κ ℓ| ≤ C` pointwise, where `hRes = (1−f_L)(χ_Λ²)` is the one-body
residual of `Work.BoseFixB3.Eps.Defs`.

The word is a sum of one-body pairings of `hRes`:

* `highSlot_chiSq_aP_eq` (`Eps/highSlot_chiSq_aP_eq.lean`) collapses the slot-`j`
  fibre: `Q̄_{L,j}(χ_Λ²P_jΦ) x = P_jΦ x · hRes(x j)`, because `P_jΦ` is constant in the
  slot `j` (`Q0Sector.aP_const_in_coord`) and `lowMult` is `ℝ`-homogeneous;
* each resulting box integral is bounded by `C ∫|PᵢΦ PⱼΦ|` (`hH` pointwise, plus
  `norm_integral_le_of_norm_le`);
* the pair sum `∑_{i,j} ∫|PᵢΦ PⱼΦ| ≤ n² ∫Φ²` is `sum_aP_pair_abs_le`.

This is the analytic input of FS's `ε₂`-Cauchy–Schwarz step `B3EpsRoot`
(`Eps/b3EpsRoot_holds.lean`): the constant `C` is FS's bound on `hRes`, which is of
size `(κℓ)^{-s}` for every `s` because the multiplier `1 − f_L` cuts momenta below
`κ` while `χ_Λ²` is an `ℓ`-smooth bump.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixB3.Eps

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix

set_option autoImplicit false

/-! ## The pairwise bound

`sum_aP_pair_abs_le` bounds the *double* sum; the assembly below needs the same bound
pair by pair, and only the latter follows from Cauchy–Schwarz on each pair (summing the
per-pair bound is `sum_aP_pair_abs_le`'s job).  The proof is the AM–GM/contraction route
of `sum_aP_pair_abs_le`, one pair at a time. -/

/-- `∫_{abox} |PᵢΦ · PⱼΦ| ≤ ∫_{abox} Φ²` for every ordered pair `(i,j)`
(Cauchy–Schwarz on the box + the contraction `aP_sq_le`). -/
lemma aP_pair_abs_integral_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) (i j : Fin n) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        |Submission.BoseGases.aP ℓ i Φ x * Submission.BoseGases.aP ℓ j Φ x|)
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by
  have hcs := Submission.BoseGases.cs_box_product hℓ
    (f := fun x => |Submission.BoseGases.aP ℓ i Φ x|)
    (g := fun x => |Submission.BoseGases.aP ℓ j Φ x|)
    ((Submission.BoseGases.aP_continuous hℓ i hΦ).abs)
    ((Submission.BoseGases.aP_continuous hℓ j hΦ).abs)
  have h1 : (∫ x in Submission.BoseGases.abox n ℓ,
          |Submission.BoseGases.aP ℓ i Φ x| * |Submission.BoseGases.aP ℓ j Φ x|) ^ 2
      ≤ (∫ x in Submission.BoseGases.abox n ℓ, (Submission.BoseGases.aP ℓ i Φ x) ^ 2)
        * (∫ x in Submission.BoseGases.abox n ℓ, (Submission.BoseGases.aP ℓ j Φ x) ^ 2) := by
    simpa only [sq_abs] using hcs
  have h2 : (∫ x in Submission.BoseGases.abox n ℓ,
        |Submission.BoseGases.aP ℓ i Φ x * Submission.BoseGases.aP ℓ j Φ x|)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          |Submission.BoseGases.aP ℓ i Φ x| * |Submission.BoseGases.aP ℓ j Φ x| := by
    apply integral_congr_ae
    filter_upwards with x
    rw [abs_mul]
  have h3 : (∫ x in Submission.BoseGases.abox n ℓ, (Submission.BoseGases.aP ℓ i Φ x) ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 :=
    Submission.BoseGases.aP_sq_le hℓ i hΦ
  have h4 : (∫ x in Submission.BoseGases.abox n ℓ, (Submission.BoseGases.aP ℓ j Φ x) ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 :=
    Submission.BoseGases.aP_sq_le hℓ j hΦ
  have h5 : 0 ≤ ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 :=
    integral_nonneg (fun x => sq_nonneg _)
  have h6 : 0 ≤ ∫ x in Submission.BoseGases.abox n ℓ, (Submission.BoseGases.aP ℓ j Φ x) ^ 2 :=
    integral_nonneg (fun x => sq_nonneg _)
  have hsq : (∫ x in Submission.BoseGases.abox n ℓ,
        |Submission.BoseGases.aP ℓ i Φ x| * |Submission.BoseGases.aP ℓ j Φ x|) ^ 2
      ≤ (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) ^ 2 := by
    calc (∫ x in Submission.BoseGases.abox n ℓ,
            |Submission.BoseGases.aP ℓ i Φ x| * |Submission.BoseGases.aP ℓ j Φ x|) ^ 2
        ≤ (∫ x in Submission.BoseGases.abox n ℓ, (Submission.BoseGases.aP ℓ i Φ x) ^ 2)
          * (∫ x in Submission.BoseGases.abox n ℓ, (Submission.BoseGases.aP ℓ j Φ x) ^ 2) := h1
      _ ≤ (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)
          * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) :=
          mul_le_mul h3 h4 h6 h5
      _ = (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) ^ 2 := by ring
  rw [h2]
  exact le_of_sq_le_sq hsq h5

/-! ## The main bound -/

theorem q3convWord_abs_le {fc : Work.BoseBoxFix.LowCut} {κ ℓ I C : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ}
    (hℓ : 0 < ℓ) (hC : 0 ≤ C) (hΦ : Continuous Φ)
    (hH : ∀ z : EuclideanSpace ℝ (Fin 3), |Work.BoseFixB3.Eps.hRes fc κ ℓ z| ≤ C) :
    |Work.BoseFixB3.q3convWord fc κ ℓ I Φ|
      ≤ |I| * ℓ ^ (-(3 : ℤ)) * C *
        ((n : ℝ) ^ 2 * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)) := by
  classical
  have hL : 0 ≤ ℓ ^ (-(3 : ℤ)) := zpow_nonneg hℓ.le _
  -- ## Step 1: the pairwise integral bound, with the fibre collapse applied.
  have hpair : ∀ i j : Fin n,
      |∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ i Φ x
            * (Submission.BoseGases.aP ℓ j Φ x * hRes fc κ ℓ (x j))|
        ≤ C * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
    intro i j
    have hcont : Continuous (fun x : Submission.BoseGases.X n =>
        Submission.BoseGases.aP ℓ i Φ x * Submission.BoseGases.aP ℓ j Φ x) :=
      (Submission.BoseGases.aP_continuous hℓ i hΦ).mul
        (Submission.BoseGases.aP_continuous hℓ j hΦ)
    have hint : Integrable (fun x : Submission.BoseGases.X n =>
        C * |Submission.BoseGases.aP ℓ i Φ x * Submission.BoseGases.aP ℓ j Φ x|)
        ((volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)) :=
      Submission.BoseGases.integrableOn_abox_of_continuous hℓ (hcont.abs.const_mul C)
    have hub : ∀ᵐ x ∂((volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)),
        ‖Submission.BoseGases.aP ℓ i Φ x
            * (Submission.BoseGases.aP ℓ j Φ x * hRes fc κ ℓ (x j))‖
          ≤ C * |Submission.BoseGases.aP ℓ i Φ x * Submission.BoseGases.aP ℓ j Φ x| := by
      filter_upwards with x
      rw [Real.norm_eq_abs]
      have hb := hH (x j)
      calc |Submission.BoseGases.aP ℓ i Φ x
              * (Submission.BoseGases.aP ℓ j Φ x * hRes fc κ ℓ (x j))|
          = |Submission.BoseGases.aP ℓ i Φ x| * |Submission.BoseGases.aP ℓ j Φ x|
              * |hRes fc κ ℓ (x j)| := by rw [abs_mul, abs_mul]; ring
        _ ≤ |Submission.BoseGases.aP ℓ i Φ x| * |Submission.BoseGases.aP ℓ j Φ x| * C :=
            mul_le_mul_of_nonneg_left hb (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = C * |Submission.BoseGases.aP ℓ i Φ x * Submission.BoseGases.aP ℓ j Φ x| := by
            rw [abs_mul]; ring
    have h1 : |∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ i Φ x
            * (Submission.BoseGases.aP ℓ j Φ x * hRes fc κ ℓ (x j))|
        ≤ ∫ x in Submission.BoseGases.abox n ℓ,
            C * |Submission.BoseGases.aP ℓ i Φ x * Submission.BoseGases.aP ℓ j Φ x| := by
      have := norm_integral_le_of_norm_le
        (μ := (volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)) hint hub
      simpa [Real.norm_eq_abs] using this
    rw [show (∫ x in Submission.BoseGases.abox n ℓ,
            C * |Submission.BoseGases.aP ℓ i Φ x * Submission.BoseGases.aP ℓ j Φ x|)
        = C * (∫ x in Submission.BoseGases.abox n ℓ,
            |Submission.BoseGases.aP ℓ i Φ x * Submission.BoseGases.aP ℓ j Φ x|) from
      integral_const_mul C _] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (aP_pair_abs_integral_le hℓ hΦ i j) hC)
  -- ## Step 2: the fibre collapse turns `q3convWord` into the sum of the pairings.
  have hword : Work.BoseFixB3.q3convWord fc κ ℓ I Φ
      = I * ℓ ^ (-(3 : ℤ)) * ∑ i : Fin n, ∑ j : Fin n,
          (∫ x in Submission.BoseGases.abox n ℓ,
            Submission.BoseGases.aP ℓ i Φ x
              * (Submission.BoseGases.aP ℓ j Φ x * hRes fc κ ℓ (x j))) := by
    unfold Work.BoseFixB3.q3convWord
    congr 1
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    apply integral_congr_ae
    filter_upwards with x
    rw [highSlot_chiSq_aP_eq hℓ hΦ x]
  -- ## Step 3: the double sum is bounded by `n² · C ∫Φ²`.
  have hsum : |∑ i : Fin n, ∑ j : Fin n,
        (∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ i Φ x
            * (Submission.BoseGases.aP ℓ j Φ x * hRes fc κ ℓ (x j)))|
      ≤ (n : ℝ) ^ 2 * (C * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)) := by
    have hinner : ∀ i : Fin n, |∑ j : Fin n,
          (∫ x in Submission.BoseGases.abox n ℓ,
            Submission.BoseGases.aP ℓ i Φ x
              * (Submission.BoseGases.aP ℓ j Φ x * hRes fc κ ℓ (x j)))|
        ≤ ∑ j : Fin n, |∫ x in Submission.BoseGases.abox n ℓ,
            Submission.BoseGases.aP ℓ i Φ x
              * (Submission.BoseGases.aP ℓ j Φ x * hRes fc κ ℓ (x j))| :=
      fun i => Finset.abs_sum_le_sum_abs _ _
    calc |∑ i : Fin n, ∑ j : Fin n,
            (∫ x in Submission.BoseGases.abox n ℓ,
              Submission.BoseGases.aP ℓ i Φ x
                * (Submission.BoseGases.aP ℓ j Φ x * hRes fc κ ℓ (x j)))|
        ≤ ∑ i : Fin n, |∑ j : Fin n,
            (∫ x in Submission.BoseGases.abox n ℓ,
              Submission.BoseGases.aP ℓ i Φ x
                * (Submission.BoseGases.aP ℓ j Φ x * hRes fc κ ℓ (x j)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, |∫ x in Submission.BoseGases.abox n ℓ,
            Submission.BoseGases.aP ℓ i Φ x
              * (Submission.BoseGases.aP ℓ j Φ x * hRes fc κ ℓ (x j))| :=
          Finset.sum_le_sum (fun i _ => hinner i)
      _ ≤ ∑ i : Fin n, ∑ j : Fin n,
            C * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpair i j))
      _ = (n : ℝ) ^ 2 * (C * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)) := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          simp only [nsmul_eq_mul]
          ring
  -- ## Step 4: factor out the constants.
  rw [hword]
  calc |I * ℓ ^ (-(3 : ℤ)) * ∑ i : Fin n, ∑ j : Fin n,
          (∫ x in Submission.BoseGases.abox n ℓ,
            Submission.BoseGases.aP ℓ i Φ x
              * (Submission.BoseGases.aP ℓ j Φ x * hRes fc κ ℓ (x j)))|
      = |I| * ℓ ^ (-(3 : ℤ)) * |∑ i : Fin n, ∑ j : Fin n,
          (∫ x in Submission.BoseGases.abox n ℓ,
            Submission.BoseGases.aP ℓ i Φ x
              * (Submission.BoseGases.aP ℓ j Φ x * hRes fc κ ℓ (x j)))| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hL]
    _ ≤ |I| * ℓ ^ (-(3 : ℤ))
          * ((n : ℝ) ^ 2 * (C * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2))) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg (abs_nonneg I) hL)
    _ = |I| * ℓ ^ (-(3 : ℤ)) * C
          * ((n : ℝ) ^ 2 * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)) := by ring

end Work.BoseFixB3.Eps

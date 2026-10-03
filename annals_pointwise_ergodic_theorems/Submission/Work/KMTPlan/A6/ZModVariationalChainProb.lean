/-
# The `ZMod Q` variational chain in the paper's *probability* normalization

`Work.KMTPlan.A6.ZModChainPropP` (`MdlAdelicProb.lean`) is the §8 chain of Krause--Mirek--Tao with
every `L^p(ZMod Q)`-norm taken against the **probability** Haar measure `zmodProb Q = Q⁻¹ •
count` — the normalization in which the paper's linear and bilinear inputs are stated.

The counting-measure version `Work.KMTPlan.A6.ZModChainProp` is *weaker* than this one (the
counting norms dominate the probability ones by `Q^{1/p}`), so this module redoes the §8 chain
directly in the probability normalization rather than deducing it from the counting form.  The
differences with the counting chain are exactly the two points where the measure enters:

* the **supremum part** `sup_n ‖b_n‖ₑ` of the variational norm cannot be bounded by the counting
  `L^r`-seminorm any more (a single point has measure `Q⁻¹`, not `1`); instead one uses the
  elementary pointwise bound `sup_n ‖b_n‖ ≤ ‖b_0‖ + V^r(b)` (the two-point chain realizes every
  single increment) and then Hölder on the probability space, `L¹ ≤ L^r`;
* the **bilinear-`fkr`** estimate is applied to the probability measure, which is possible because
  `Work.KMTPlan.A6.bilinearFkrPacketsGen` is uniform in the measure space.

The remaining ingredients (Cauchy--Schwarz in the real variable, the a.e.-measurability of the
`V^R`-datum) are the same as in the counting proof.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlAdelicProb
import Submission.Work.KMTPlan.A6.ZModVariationalChain
import Submission.Port.Aesm

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

noncomputable section

/-! ## 1. Elementary tools -/

/-- On `ZMod Q` the residues `0, 1, …, Q - 1` list every element of `ZMod Q` exactly once. -/
theorem sum_range_zmod_eq_sum {Q : ℕ} [NeZero Q] {α : Type*} [AddCommMonoid α]
    (G : ZMod Q → α) :
    (∑ ρ ∈ Finset.range Q, G ((ρ : ℤ) : ZMod Q)) = ∑ x : ZMod Q, G x := by
  have hcast : ∀ ρ : ℕ, ((ρ : ℤ) : ZMod Q) = ((ρ : ℕ) : ZMod Q) := fun ρ => Int.cast_natCast ρ
  simp only [hcast]
  refine Finset.sum_bij' (fun ρ (_ : ρ ∈ Finset.range Q) => ((ρ : ℕ) : ZMod Q))
    (fun x (_ : x ∈ Finset.univ) => x.val) (fun ρ _ => Finset.mem_univ _)
    (fun x _ => Finset.mem_range.mpr (ZMod.val_lt x))
    (fun ρ hρ => ZMod.val_cast_of_lt (Finset.mem_range.mp hρ))
    (fun x _ => ZMod.natCast_zmod_val x) (fun ρ _ => rfl)

/-- The `Q⁻¹ ∑_{ρ < Q}` average of a family on `ZMod Q` is its integral against the probability
measure `zmodProb Q`. -/
theorem inv_mul_sum_range_eq_lintegral {Q : ℕ} (hQ : 1 ≤ Q) (F : ZMod Q → ℝ≥0∞) :
    (Q : ENNReal)⁻¹ * ∑ ρ ∈ Finset.range Q, F ((ρ : ℤ) : ZMod Q)
      = ∫⁻ θ : ZMod Q, F θ ∂(zmodProb Q) := by
  haveI : NeZero Q := ⟨by omega⟩
  rw [sum_range_zmod_eq_sum F, lintegral_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [zmodProb, Measure.smul_apply, Measure.count_singleton, smul_eq_mul, mul_one, mul_comm]

/-- The `L²`-seminorm on `ZMod Q` against the probability measure `zmodProb Q`, as a finite sum. -/
theorem eLpNorm_two_zmodProb {Q : ℕ} [NeZero Q] (g : ZMod Q → ℂ) :
    eLpNorm g 2 (zmodProb Q)
      = (Finset.univ.sum fun a : ZMod Q => (Q : ENNReal)⁻¹ * ‖g a‖ₑ ^ (2 : ℝ)) ^
          ((1 : ℝ) / 2) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (by norm_num) (by norm_num), ENNReal.toReal_ofNat]
  refine congrArg (fun t => t ^ ((1 : ℝ) / 2)) ?_
  rw [lintegral_fintype]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [zmodProb, Measure.smul_apply, Measure.count_singleton, smul_eq_mul, mul_one, mul_comm]

/-- A single increment is dominated by the `r`-variation: the chain `m ↦ n` realizes it. -/
theorem enorm_sub_le_varPart {r : NNReal} (hr : 1 ≤ r) (a : ℕ → ℂ) {m n : ℕ} (hmn : m ≤ n) :
    ‖a n - a m‖ₑ ≤ varPart r a := by
  have hrne : (r : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast lt_of_lt_of_le zero_lt_one hr
    exact ne_of_gt hpos
  set N : ℕ → ℕ := fun k => if k = 0 then m else n with hN
  have hN0 : N 0 = m := by simp [hN]
  have hN1 : N 1 = n := by simp [hN]
  have hNmono : Monotone N := by
    intro i j hij
    rcases eq_or_lt_of_le hij with h | h
    · exact le_of_eq (by rw [h])
    · have hj : j ≠ 0 := by omega
      by_cases hi : i = 0
      · simp only [hN]
        rw [if_pos hi, if_neg hj]
        exact hmn
      · simp only [hN]
        rw [if_neg hi, if_neg hj]
  have hsingle : ENNReal.ofReal
      ‖WithLp.toLp r (fun i : Fin 1 => a (N (i + 1)) - a (N i))‖ = ‖a n - a m‖ₑ := by
    rw [Work.KMTAreas.A7.ofReal_norm_toLp_eq_sum r hr]
    have hsum_eq : (∑ i : Fin 1, ‖a (N (i + 1)) - a (N i)‖ₑ ^ (r : ℝ))
        = ∑ i : Fin 1, ‖a n - a m‖ₑ ^ (r : ℝ) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hA : a (N ((i : ℕ) + 1)) - a (N (i : ℕ)) = a n - a m := by
        have hi1 : ((i : ℕ) + 1) = 1 := by have := i.isLt; omega
        have hi0 : ((i : ℕ)) = 0 := by have := i.isLt; omega
        rw [hi1, hi0, hN1, hN0]
      rw [hA]
    rw [hsum_eq, Fin.sum_univ_one]
    rw [← ENNReal.rpow_mul, mul_one_div, div_self hrne, ENNReal.rpow_one]
  calc ‖a n - a m‖ₑ
      = ENNReal.ofReal ‖WithLp.toLp r (fun i : Fin 1 => a (N (i + 1)) - a (N i))‖ :=
        hsingle.symm
    _ ≤ varPart r a := le_iSup_of_le 1 (le_iSup_of_le N (le_iSup_of_le hNmono le_rfl))

/-- The supremum part of the variational norm is dominated by the base term plus the variation
part (for `r ≥ 1`). -/
theorem iSup_enorm_le_enorm_zero_add_varPart {r : NNReal} (hr : 1 ≤ r) (a : ℕ → ℂ) :
    (⨆ n, ‖a n‖ₑ) ≤ ‖a 0‖ₑ + varPart r a := by
  refine iSup_le (fun n => ?_)
  have h1 : ‖a n‖ₑ ≤ ‖a 0‖ₑ + ‖a n - a 0‖ₑ := by
    calc ‖a n‖ₑ = ‖a 0 + (a n - a 0)‖ₑ := by rw [show a 0 + (a n - a 0) = a n by ring]
      _ ≤ ‖a 0‖ₑ + ‖a n - a 0‖ₑ := enorm_add_le _ _
  exact h1.trans (add_le_add le_rfl (enorm_sub_le_varPart hr a (Nat.zero_le n)))

/-! ## 2. Hölder/Jensen on the probability space `ZMod Q -/

/-- On the probability space `ZMod Q`, `L¹ ≤ L^r` for `r ≥ 1`, `ℝ≥0∞`-valued version. -/
theorem lintegral_le_eLpNorm_zmodProb {Q : ℕ} [NeZero Q] (F : ZMod Q → ℝ≥0∞) (r : NNReal)
    (hr : 1 ≤ r) : ∫⁻ θ, F θ ∂(zmodProb Q) ≤ eLpNorm F (r : ENNReal) (zmodProb Q) := by
  haveI : IsProbabilityMeasure (zmodProb Q) := ⟨zmodProb_univ⟩
  have hm : AEStronglyMeasurable F (zmodProb Q) :=
    (by fun_prop : Measurable F).aestronglyMeasurable
  have h := eLpNorm_le_eLpNorm_of_exponent_le (μ := zmodProb Q) (f := F)
    (p := 1) (q := (r : ENNReal)) (by exact_mod_cast hr)
  rwa [eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm),
    lintegral_congr (fun x => enorm_eq_self (F x))] at h

/-- On the probability space `ZMod Q`, `L¹ ≤ L^r` for `r ≥ 1`, `ℂ`-valued version. -/
theorem eLpNorm_one_le_eLpNorm_zmodProb {Q : ℕ} [NeZero Q] (f : ZMod Q → ℂ) (r : NNReal)
    (hr : 1 ≤ r) : eLpNorm f 1 (zmodProb Q) ≤ eLpNorm f (r : ENNReal) (zmodProb Q) := by
  haveI : IsProbabilityMeasure (zmodProb Q) := ⟨zmodProb_univ⟩
  exact eLpNorm_le_eLpNorm_of_exponent_le (μ := zmodProb Q) (f := f) (p := 1)
    (q := (r : ENNReal)) (by exact_mod_cast hr)

/-! ## 3. The `V^R`-datum of a packet family -/

/-- Each packet `L²`-norm is dominated by the `V^R`-datum. -/
theorem eLpNorm_le_VrLiftDataP (R : ℝ) (Q : ℕ) (u : ℕ → ZMod Q → ℂ) (n : ℕ) :
    eLpNorm (u n) 2 (zmodProb Q) ≤ VrLiftDataP R Q u := by
  rw [VrLiftDataP]
  exact le_trans (le_iSup (fun n => eLpNorm (u n) 2 (zmodProb Q)) n) (le_add_right le_rfl)

/-- **Measurability of the `L²`-seminorm against the probability measure.** -/
theorem aemeasurable_eLpNorm_two_zmodProb {Q : ℕ} [NeZero Q] (φ : ℝ → ZMod Q → ℂ)
    (hφ : ∀ a : ZMod Q, AEMeasurable (fun X : ℝ => φ X a)) :
    AEMeasurable (fun X : ℝ => eLpNorm (φ X) 2 (zmodProb Q)) := by
  have hsum : AEMeasurable (fun X : ℝ =>
      Finset.univ.sum fun a : ZMod Q => (Q : ENNReal)⁻¹ * ‖φ X a‖ₑ ^ (2 : ℝ)) := by
    have h := Finset.aemeasurable_sum
      (f := fun a X => (Q : ENNReal)⁻¹ * ‖φ X a‖ₑ ^ (2 : ℝ))
      (Finset.univ : Finset (ZMod Q)) (fun a _ =>
        AEMeasurable.const_mul
          ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable.comp_aemeasurable
            (measurable_enorm.comp_aemeasurable (hφ a))) (Q : ENNReal)⁻¹)
    exact h.congr (Filter.Eventually.of_forall (fun X => by rw [Finset.sum_apply]))
  exact ((ENNReal.continuous_rpow_const (y := ((1 : ℝ) / 2))).measurable.comp_aemeasurable
    hsum).congr (Filter.Eventually.of_forall (fun X => (eLpNorm_two_zmodProb (φ X)).symm))

/-- One summand of the variation part of `VrLiftDataP` is a.e.-measurable. -/
theorem aemeasurable_varTermP {Q : ℕ} [NeZero Q] (R : ℝ) (J : ℕ) (k : Fin (J + 1) → ℕ)
    {w : ℕ → ℝ → ZMod Q → ℂ}
    (hw : ∀ (n : ℕ) (a : ZMod Q), AEMeasurable (fun X : ℝ => w n X a)) :
    AEMeasurable (fun X : ℝ => ENNReal.rpow (Finset.univ.sum fun i : Fin J =>
      ENNReal.rpow (eLpNorm (fun θ : ZMod Q => w (k i.succ) X θ - w (k i.castSucc) X θ) 2
        (zmodProb Q)) R) (1 / R)) := by
  have hsum' := Finset.aemeasurable_sum (f := fun i X => ENNReal.rpow (eLpNorm
      (fun θ : ZMod Q => w (k i.succ) X θ - w (k i.castSucc) X θ) 2
        (zmodProb Q)) R) (Finset.univ : Finset (Fin J))
    (fun i _ => (aemeasurable_eLpNorm_two_zmodProb (φ := fun X : ℝ => fun θ : ZMod Q =>
        w (k i.succ) X θ - w (k i.castSucc) X θ)
      (fun a => (hw (k i.succ) a).sub (hw (k i.castSucc) a))).pow_const R)
  have hsum : AEMeasurable (fun X : ℝ => Finset.univ.sum fun i : Fin J => ENNReal.rpow (eLpNorm
      (fun θ : ZMod Q => w (k i.succ) X θ - w (k i.castSucc) X θ) 2
        (zmodProb Q)) R) :=
    hsum'.congr (Filter.Eventually.of_forall (fun X => by rw [Finset.sum_apply]))
  exact hsum.pow_const ((1 : ℝ) / R)

/-- **The `V^R`-datum of a coordinatewise a.e.-measurable packet family is a.e.-measurable.** -/
theorem aemeasurable_vrLiftDataP {Q : ℕ} [NeZero Q] (R : ℝ) {w : ℕ → ℝ → ZMod Q → ℂ}
    (hw : ∀ (n : ℕ) (a : ZMod Q), AEMeasurable (fun X : ℝ => w n X a)) :
    AEMeasurable (fun X : ℝ => VrLiftDataP R Q (fun n : ℕ => w n X)) := by
  have hfirst : AEMeasurable (fun X : ℝ =>
      ⨆ n : ℕ, eLpNorm (w n X) 2 (zmodProb Q)) :=
    AEMeasurable.iSup (f := fun n X => eLpNorm (w n X) 2 (zmodProb Q))
      (fun n => aemeasurable_eLpNorm_two_zmodProb (φ := fun X : ℝ => w n X)
        (fun a => hw n a))
  have hvar : AEMeasurable (fun X : ℝ =>
      ⨆ (J : ℕ) (k : Fin (J + 1) → ℕ) (_ : Monotone k),
        ENNReal.rpow (Finset.univ.sum fun i : Fin J =>
          ENNReal.rpow (eLpNorm (fun θ : ZMod Q => w (k i.succ) X θ - w (k i.castSucc) X θ) 2
            (zmodProb Q)) R) (1 / R)) := by
    refine AEMeasurable.iSup (f := fun J X => ⨆ (k : Fin (J + 1) → ℕ) (_ : Monotone k),
      ENNReal.rpow (Finset.univ.sum fun i : Fin J =>
        ENNReal.rpow (eLpNorm (fun θ : ZMod Q => w (k i.succ) X θ - w (k i.castSucc) X θ) 2
          (zmodProb Q)) R) (1 / R)) (fun J => ?_)
    refine AEMeasurable.iSup (f := fun k X => ⨆ (_ : Monotone k),
      ENNReal.rpow (Finset.univ.sum fun i : Fin J =>
        ENNReal.rpow (eLpNorm (fun θ : ZMod Q => w (k i.succ) X θ - w (k i.castSucc) X θ) 2
          (zmodProb Q)) R) (1 / R)) (fun k => ?_)
    exact aemeasurable_iSup_prop_const (aemeasurable_varTermP R J k hw)
  refine (hfirst.add hvar).congr ?_
  filter_upwards with X
  rfl

/-! ## 4. `ofReal` bookkeeping -/

/-- `ofReal (1 + 2C) * ofReal M = ofReal M + 2 * ofReal (C * M)` for `M, C ≥ 0`. -/
theorem ofReal_one_add_two_mul (M C : ℝ) (hM : 0 ≤ M) (hC : 0 ≤ C) :
    ENNReal.ofReal (1 + 2 * C) * ENNReal.ofReal M
      = ENNReal.ofReal M + 2 * ENNReal.ofReal (C * M) := by
  have h2 : ENNReal.ofReal (2 * C) = 2 * ENNReal.ofReal C := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [ENNReal.ofReal_add (by norm_num) (by linarith), h2, ENNReal.ofReal_mul hC,
    ENNReal.ofReal_one]
  ring

/-! ## 5. The chain -/

/-- **The `ZMod Q` variational chain in the probability normalization** (§8 of
Krause--Mirek--Tao, at `(p₁,p₂,p) = (2,2,1)`). -/
theorem ZModVariationalChainProb : Work.KMTPlan.A6.ZModChainPropP := by
  intro r hr R hR hRr
  obtain ⟨C, hCpos, hC⟩ := bilinearFkrPacketsGen (R := R) (r := r) hR hRr
  refine ⟨1 + 2 * C, by linarith, ?_⟩
  intro Q hQ M Ku Kv hM hKu hKv B hadd₁ hadd₂ u v humeas hvmeas hbase hB1 hB2 hSu hSv
  haveI hQne : NeZero Q := ⟨by omega⟩
  haveI hprob : IsProbabilityMeasure (zmodProb Q) := ⟨zmodProb_univ⟩
  have hUmeas : AEMeasurable (fun X : ℝ => VrLiftDataP R Q (fun n : ℕ => u n X)) volume :=
    aemeasurable_vrLiftDataP R (fun n a => humeas n a)
  have hVmeas : AEMeasurable (fun X : ℝ => VrLiftDataP R Q (fun n : ℕ => v n X)) volume :=
    aemeasurable_vrLiftDataP R (fun n a => hvmeas n a)
  -- ## the pointwise bound in `X`
  have hpt : ∀ X : ℝ, (Q : ENNReal)⁻¹ * ∑ ρ ∈ Finset.range Q,
        variationalNorm r (fun n : ℕ => B (u n X) (v n X) ((ρ : ℤ) : ZMod Q))
      ≤ ENNReal.ofReal (1 + 2 * C) * ENNReal.ofReal M *
          (VrLiftDataP R Q (fun n : ℕ => u n X) * VrLiftDataP R Q (fun n : ℕ => v n X)) := by
    intro X
    rw [inv_mul_sum_range_eq_lintegral (Q := Q) hQ
      (F := fun θ : ZMod Q => variationalNorm r (fun n : ℕ => B (u n X) (v n X) θ))]
    have hfmeas : Measurable (fun θ : ZMod Q => ‖B (u 0 X) (v 0 X) θ‖ₑ) :=
      measurable_enorm.comp (by fun_prop : Measurable (fun θ : ZMod Q => B (u 0 X) (v 0 X) θ))
    have hpt_pt : ∀ θ : ZMod Q, variationalNorm r (fun n : ℕ => B (u n X) (v n X) θ)
        ≤ ‖B (u 0 X) (v 0 X) θ‖ₑ + 2 * varPart r (fun n : ℕ => B (u n X) (v n X) θ) := by
      intro θ
      rw [variationalNorm_eq_add]
      have hsup : (⨆ n : ℕ, ‖(fun n : ℕ => B (u n X) (v n X) θ) n‖ₑ)
          ≤ ‖(fun n : ℕ => B (u n X) (v n X) θ) 0‖ₑ
            + varPart r (fun n : ℕ => B (u n X) (v n X) θ) :=
        iSup_enorm_le_enorm_zero_add_varPart hr _
      calc (⨆ n : ℕ, ‖(fun n : ℕ => B (u n X) (v n X) θ) n‖ₑ)
            + varPart r (fun n : ℕ => B (u n X) (v n X) θ)
          ≤ (‖(fun n : ℕ => B (u n X) (v n X) θ) 0‖ₑ
              + varPart r (fun n : ℕ => B (u n X) (v n X) θ))
            + varPart r (fun n : ℕ => B (u n X) (v n X) θ) := add_le_add hsup le_rfl
        _ = ‖(fun n : ℕ => B (u n X) (v n X) θ) 0‖ₑ
            + 2 * varPart r (fun n : ℕ => B (u n X) (v n X) θ) := by ring
    have h1 : ∫⁻ θ : ZMod Q, variationalNorm r (fun n : ℕ => B (u n X) (v n X) θ)
          ∂(zmodProb Q)
        ≤ (∫⁻ θ : ZMod Q, ‖B (u 0 X) (v 0 X) θ‖ₑ ∂(zmodProb Q))
          + 2 * (∫⁻ θ : ZMod Q, varPart r (fun n : ℕ => B (u n X) (v n X) θ)
              ∂(zmodProb Q)) := by
      refine (lintegral_mono hpt_pt).trans (le_of_eq ?_)
      rw [lintegral_add_left hfmeas, lintegral_const_mul' 2 _ (by norm_num)]
    have h2 : (∫⁻ θ : ZMod Q, ‖B (u 0 X) (v 0 X) θ‖ₑ ∂(zmodProb Q))
        ≤ (ENNReal.ofReal M * VrLiftDataP R Q (fun n : ℕ => u n X))
            * VrLiftDataP R Q (fun n : ℕ => v n X) := by
      rw [← eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)]
      refine (eLpNorm_one_le_eLpNorm_zmodProb (fun θ : ZMod Q => B (u 0 X) (v 0 X) θ) r
        hr).trans ?_
      refine (hbase X 0).trans ?_
      exact mul_le_mul'
        (mul_le_mul' le_rfl (eLpNorm_le_VrLiftDataP R Q (fun n : ℕ => u n X) 0))
        (eLpNorm_le_VrLiftDataP R Q (fun n : ℕ => v n X) 0)
    have h3 : (∫⁻ θ : ZMod Q, varPart r (fun n : ℕ => B (u n X) (v n X) θ) ∂(zmodProb Q))
        ≤ (ENNReal.ofReal (C * M) * VrLiftDataP R Q (fun n : ℕ => u n X))
            * VrLiftDataP R Q (fun n : ℕ => v n X) := by
      refine (lintegral_le_eLpNorm_zmodProb
        (fun θ : ZMod Q => varPart r (fun n : ℕ => B (u n X) (v n X) θ)) r hr).trans ?_
      exact hC (X := ZMod Q) (zmodProb Q)
        (fun f => (by fun_prop : Measurable f).aestronglyMeasurable)
        hM B hadd₁ hadd₂ (fun n θ => u n X θ) (fun n θ => v n X θ)
        (fun m n l => hB1 X m n l) (fun m n l => hB2 X m n l)
    refine h1.trans ?_
    refine (add_le_add h2 (mul_le_mul' le_rfl h3)).trans ?_
    refine le_of_eq ?_
    rw [ofReal_one_add_two_mul M C hM hCpos.le]
    ring
  -- ## the Cauchy--Schwarz in the real variable
  have hU₂ : (∫⁻ X : ℝ, (VrLiftDataP R Q (fun n : ℕ => u n X)) ^ (2 : ℝ))
      = ∫⁻ X : ℝ, (VrLiftDataP R Q (fun n : ℕ => u n X)) ^ (2 : ℕ) :=
    lintegral_congr (fun X => by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast])
  have hV₂ : (∫⁻ X : ℝ, (VrLiftDataP R Q (fun n : ℕ => v n X)) ^ (2 : ℝ))
      = ∫⁻ X : ℝ, (VrLiftDataP R Q (fun n : ℕ => v n X)) ^ (2 : ℕ) :=
    lintegral_congr (fun X => by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast])
  have hSu' : ∫⁻ X : ℝ, (VrLiftDataP R Q (fun n : ℕ => u n X)) ^ (2 : ℝ)
      ≤ ENNReal.ofReal (Ku ^ 2) := by
    rw [hU₂]; exact hSu
  have hSv' : ∫⁻ X : ℝ, (VrLiftDataP R Q (fun n : ℕ => v n X)) ^ (2 : ℝ)
      ≤ ENNReal.ofReal (Kv ^ 2) := by
    rw [hV₂]; exact hSv
  have hKu2 : (ENNReal.ofReal (Ku ^ 2)) ^ ((1 : ℝ) / 2) = ENNReal.ofReal Ku := by
    have h1 : ENNReal.ofReal (Ku ^ 2) = (ENNReal.ofReal Ku) ^ (2 : ℝ) := by
      rw [ENNReal.ofReal_pow hKu, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
        ENNReal.rpow_natCast]
    rw [h1, ← ENNReal.rpow_mul, show (2 : ℝ) * ((1 : ℝ) / 2) = 1 by norm_num,
      ENNReal.rpow_one]
  have hKv2 : (ENNReal.ofReal (Kv ^ 2)) ^ ((1 : ℝ) / 2) = ENNReal.ofReal Kv := by
    have h1 : ENNReal.ofReal (Kv ^ 2) = (ENNReal.ofReal Kv) ^ (2 : ℝ) := by
      rw [ENNReal.ofReal_pow hKv, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
        ENNReal.rpow_natCast]
    rw [h1, ← ENNReal.rpow_mul, show (2 : ℝ) * ((1 : ℝ) / 2) = 1 by norm_num,
      ENNReal.rpow_one]
  have hholder : ∫⁻ X : ℝ,
        VrLiftDataP R Q (fun n : ℕ => u n X) * VrLiftDataP R Q (fun n : ℕ => v n X)
      ≤ ENNReal.ofReal Ku * ENNReal.ofReal Kv := by
    calc ∫⁻ X : ℝ, VrLiftDataP R Q (fun n : ℕ => u n X) * VrLiftDataP R Q (fun n : ℕ => v n X)
        ≤ (∫⁻ X : ℝ, (VrLiftDataP R Q (fun n : ℕ => u n X)) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
            * (∫⁻ X : ℝ, (VrLiftDataP R Q (fun n : ℕ => v n X)) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) :=
          ENNReal.lintegral_mul_le_Lp_mul_Lq volume
            (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩) hUmeas hVmeas
      _ ≤ (ENNReal.ofReal (Ku ^ 2)) ^ ((1 : ℝ) / 2)
            * (ENNReal.ofReal (Kv ^ 2)) ^ ((1 : ℝ) / 2) :=
          mul_le_mul' (ENNReal.rpow_le_rpow hSu' (by norm_num))
            (ENNReal.rpow_le_rpow hSv' (by norm_num))
      _ = ENNReal.ofReal Ku * ENNReal.ofReal Kv := by rw [hKu2, hKv2]
  calc ∫⁻ X : ℝ, (Q : ENNReal)⁻¹ * ∑ ρ ∈ Finset.range Q,
        variationalNorm r (fun n : ℕ => B (u n X) (v n X) ((ρ : ℤ) : ZMod Q))
      ≤ ∫⁻ X : ℝ, ENNReal.ofReal (1 + 2 * C) * ENNReal.ofReal M *
          (VrLiftDataP R Q (fun n : ℕ => u n X) * VrLiftDataP R Q (fun n : ℕ => v n X)) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (1 + 2 * C) * ENNReal.ofReal M *
          ∫⁻ X : ℝ, VrLiftDataP R Q (fun n : ℕ => u n X)
            * VrLiftDataP R Q (fun n : ℕ => v n X) :=
        lintegral_const_mul' _ _
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    _ ≤ ENNReal.ofReal (1 + 2 * C) * ENNReal.ofReal M
          * (ENNReal.ofReal Ku * ENNReal.ofReal Kv) := mul_le_mul' le_rfl hholder
    _ = ENNReal.ofReal (1 + 2 * C) * ENNReal.ofReal M * ENNReal.ofReal Ku
          * ENNReal.ofReal Kv := by
        ring

end

end Work.KMTPlan.A6

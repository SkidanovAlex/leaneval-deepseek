import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.block13_aux
import Submission.Work.BoseBoxFock.rowShape13_pinCond_gen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.block13_dict` — the block-I box ↔ word dictionary

The identity

    ℓ⁻³·re (rowShape13 Θ (c·θ) (c·θ) (qmqKernel ℓ k) p)
      = ∫_{abox n ℓ} (P_{p.1}Q_{p.2}Ψ)·(P_{p.2}Q_{p.1}Ψ)·k(x_{p.1},x_{p.2}) ,

i.e. the block-`I` Fock row of the `Q₂` word equals the position-space pair word of
`qmqDefs.q1WordK` at the `Q M Q` kernel.  The four steps:

* **Step A** (`rowShape13` ⟶ slot means): the first conjunct of `rowShape_pinCond` at a free
  box side `ℓ` (`rowShape13_pinCond_gen`), then `aPC_rowShape13_core`:
  `ℓ⁻³·rowShape13 Θ A A K p = ∫_x Θ̄(x)·P_{p.1}(z ↦ K(z_{p.2},z_{p.1})·P_{p.2}Θ z)(x)`;
* **Step B** (complex ⟶ real): `Θ = boxRestrictC ℓ Ψ` is the cast of the real restriction
  `boxRestrR ℓ Ψ`, `aPC_ofReal` turns the slot means into `aP`'s, and `qmqKernel ℓ k` is the
  cast of the real kernel `qmqKernelR ℓ k` (`qmqKernel_eq_ofReal`);
* **Step C** (the `Q M Q` algebra): `block13_main`;
* **Step D** (restriction ⟶ `Ψ`): on the box the slot means of `boxRestrR ℓ Ψ` and of `Ψ` agree,
  so `P_{p.1}θ − P_{p.1}P_{p.2}θ = P_{p.1}Q_{p.2}Ψ` and `P_{p.2}θ − P_{p.1}P_{p.2}θ = P_{p.2}Q_{p.1}Ψ`
  there.

Everything in this file and in its companion `block13_aux` is complete and axiom-clean.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local notation "Xn" => Submission.BoseGases.X
local notation "abx" => Submission.BoseGases.abox
local notation "aP" => Submission.BoseGases.aP
local notation "aQ" => Submission.BoseGases.aQ

set_option autoImplicit false

theorem block13_dict {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Ψ : Submission.BoseGases.X n → ℝ}
    (hΨc : Continuous Ψ) (hΨsym : Submission.BoseGases.PermInvariant n Ψ)
    {k : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hkm : Measurable (Function.uncurry k))
    (hkb : ∃ C : ℝ, ∀ w y, |k w y| ≤ C) (hksym : ∀ w y, k w y = k y w)
    {c : ℂ} (hc : (starRingEnd ℂ) c * c * ((ℓ ^ 3 : ℝ) : ℂ) = 1) (hr : (starRingEnd ℂ) c = c)
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2) :
    ((ℓ ^ 3)⁻¹ : ℝ) *
        (Work.BoseBoxFock.rowShape13 (Work.BoseBoxFock.boxRestrictC ℓ Ψ)
          (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
          (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
          (Work.BoseBoxFock.qmqKernel ℓ k) p).re
      = ∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Ψ) x
            * Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Ψ) x
            * k (x p.1) (x p.2) := by
  -- ### basic facts about the box restriction
  have hcast : boxRestrictC ℓ Ψ = fun y => ((boxRestrR ℓ Ψ y : ℝ) : ℂ) := by
    funext y
    simp only [boxRestrictC, boxRestrR, Complex.ofReal_mul]
  have hsupp : Function.support (boxRestrictC ℓ Ψ) ⊆ Work.MB.boxPow n ℓ := by
    intro x hx
    refine boxRestrR_support_boxPow hℓ Ψ ?_
    rw [Function.mem_support]
    intro h0
    exact hx (by rw [hcast]; simp [h0])
  have hRmeas : Measurable (boxRestrR ℓ Ψ) := boxRestrR_measurable hΨc.measurable
  obtain ⟨CR, hCR⟩ := boxRestrR_abs_le hℓ hΨc
  have hCR0 : 0 ≤ max CR 0 := le_max_right _ _
  have hCRb : ∀ x, |boxRestrR ℓ Ψ x| ≤ max CR 0 :=
    fun x => le_trans (hCR x) (le_max_left _ _)
  -- ### Step A: the row shape is the slot-mean integral
  have hc' : (starRingEnd ℂ) c * c = (((ℓ ^ 3 : ℝ)) : ℂ)⁻¹ :=
    eq_inv_of_mul_eq_one_left hc
  have hcc : c * (starRingEnd ℂ) c = (((ℓ ^ 3 : ℝ)) : ℂ)⁻¹ := by
    rw [mul_comm]; exact hc'
  have hc1 : ((1 / ℓ ^ 3 : ℝ) : ℂ) = (((ℓ ^ 3 : ℝ)) : ℂ)⁻¹ := by
    rw [one_div, Complex.ofReal_inv]
  have hL3 : (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) = (((ℓ ^ 3 : ℝ)) : ℂ)⁻¹ := Complex.ofReal_inv _
  have hA : (((ℓ ^ 3)⁻¹ : ℝ) : ℂ)
        * rowShape13 (boxRestrictC ℓ Ψ) (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
          (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y) (qmqKernel ℓ k) p
      = ∫ x : Xn n, star (boxRestrictC ℓ Ψ x) * aPC ℓ p.1
          (fun z => qmqKernel ℓ k (z p.2) (z p.1) * aPC ℓ p.2 (boxRestrictC ℓ Ψ) z) x := by
    rw [hL3, rowShape13_pinCond_gen hℓ p hp hsupp, hcc,
      aPC_rowShape13_core hℓ hp hsupp, hc1]
    try ring
  -- ### Step B: pass to the real restriction
  have hpc : ∀ z : Xn n, aPC ℓ p.2 (fun y => ((boxRestrR ℓ Ψ y : ℝ) : ℂ)) z
      = ((aP ℓ p.2 (boxRestrR ℓ Ψ) z : ℝ) : ℂ) :=
    fun z => aPC_ofReal ℓ p.2 (boxRestrR ℓ Ψ) z
  have hfun : (fun z : Xn n => qmqKernel ℓ k (z p.2) (z p.1)
        * aPC ℓ p.2 (fun y => ((boxRestrR ℓ Ψ y : ℝ) : ℂ)) z)
      = fun z => ((qmqKernelR ℓ k (z p.2) (z p.1) * aP ℓ p.2 (boxRestrR ℓ Ψ) z : ℝ) : ℂ) := by
    funext z
    rw [hpc z, qmqKernel_eq_ofReal]
    push_cast
    ring
  have hB : (∫ x : Xn n, star (boxRestrictC ℓ Ψ x) * aPC ℓ p.1
        (fun z => qmqKernel ℓ k (z p.2) (z p.1) * aPC ℓ p.2 (boxRestrictC ℓ Ψ) z) x)
      = ((∫ x in abx n ℓ, boxRestrR ℓ Ψ x * aP ℓ p.1
            (fun z => qmqKernelR ℓ k (z p.2) (z p.1) * aP ℓ p.2 (boxRestrR ℓ Ψ) z) x : ℝ) : ℂ) := by
    rw [show (∫ x : Xn n, star (boxRestrictC ℓ Ψ x) * aPC ℓ p.1
          (fun z => qmqKernel ℓ k (z p.2) (z p.1) * aPC ℓ p.2 (boxRestrictC ℓ Ψ) z) x)
        = ∫ x : Xn n, ((boxRestrR ℓ Ψ x * aP ℓ p.1
            (fun z => qmqKernelR ℓ k (z p.2) (z p.1) * aP ℓ p.2 (boxRestrR ℓ Ψ) z) x : ℝ) : ℂ) from by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only []
      rw [hcast, hfun, aPC_ofReal, Complex.ofReal_mul]
      simp]
    trans ((∫ x : Xn n, boxRestrR ℓ Ψ x * aP ℓ p.1
      (fun z => qmqKernelR ℓ k (z p.2) (z p.1) * aP ℓ p.2 (boxRestrR ℓ Ψ) z) x : ℝ) : ℂ)
    · exact integral_ofReal
    · congr 1
      exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := abx n ℓ) (fun x hx => by rw [boxRestrR_eq_zero_of_notMem hx, zero_mul])).symm
  -- ### Step C: the `Q M Q` algebra
  have hmain := block13_main hℓ hRmeas ⟨max CR 0, hCRb⟩ hkm hkb hksym hp
  -- ### Step D: replace the restriction by `Ψ` on the box
  have hbox : ∀ y ∈ abx n ℓ, boxRestrR ℓ Ψ y = Ψ y := fun y hy => boxRestrR_eq_of_mem hy
  have haP1 : ∀ x ∈ abx n ℓ, aP ℓ p.1 (boxRestrR ℓ Ψ) x = aP ℓ p.1 Ψ x :=
    fun x hx => aP_congr_of_eqOn_abox p.1 hbox hx
  have haP2 : ∀ x ∈ abx n ℓ, aP ℓ p.2 (boxRestrR ℓ Ψ) x = aP ℓ p.2 Ψ x :=
    fun x hx => aP_congr_of_eqOn_abox p.2 hbox hx
  have hBm : Measurable (aP ℓ p.2 (boxRestrR ℓ Ψ)) := Weak.aP_measurable p.2 hRmeas
  have hBb : ∀ y, |aP ℓ p.2 (boxRestrR ℓ Ψ) y| ≤ max CR 0 :=
    Weak.aP_abs_le hℓ p.2 hCR0 hCRb
  have hB1m : Measurable (aP ℓ p.1 (boxRestrR ℓ Ψ)) := Weak.aP_measurable p.1 hRmeas
  have hB1b : ∀ y, |aP ℓ p.1 (boxRestrR ℓ Ψ) y| ≤ max CR 0 :=
    Weak.aP_abs_le hℓ p.1 hCR0 hCRb
  have hD : (∫ x in abx n ℓ, (aP ℓ p.1 (boxRestrR ℓ Ψ) x
          - aP ℓ p.1 (aP ℓ p.2 (boxRestrR ℓ Ψ)) x)
        * (aP ℓ p.2 (boxRestrR ℓ Ψ) x - aP ℓ p.1 (aP ℓ p.2 (boxRestrR ℓ Ψ)) x)
        * k (x p.1) (x p.2))
      = ∫ x in abx n ℓ, aP ℓ p.1 (aQ ℓ p.2 Ψ) x * aP ℓ p.2 (aQ ℓ p.1 Ψ) x
          * k (x p.1) (x p.2) := by
    refine integral_congr_ae ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (Submission.BoseGases.abox_measurable n ℓ)] with x hx
    have hf1 : aP ℓ p.1 (boxRestrR ℓ Ψ) x - aP ℓ p.1 (aP ℓ p.2 (boxRestrR ℓ Ψ)) x
        = aP ℓ p.1 (aQ ℓ p.2 Ψ) x := by
      rw [← Weak.aP_sub hℓ p.1 hCR0 (le_trans (abs_nonneg _) (hBb (0 : Xn n)))
        hRmeas hCRb hBm hBb x]
      refine aP_congr_of_eqOn_abox p.1 (fun y hy => ?_) hx
      rw [Pi.sub_apply, boxRestrR_eq_of_mem hy, haP2 y hy]
      rfl
    have hf2 : aP ℓ p.2 (boxRestrR ℓ Ψ) x - aP ℓ p.1 (aP ℓ p.2 (boxRestrR ℓ Ψ)) x
        = aP ℓ p.2 (aQ ℓ p.1 Ψ) x := by
      rw [Weak.aP_comm hℓ hp hCR0 hRmeas hCRb]
      rw [← Weak.aP_sub hℓ p.2 hCR0 (le_trans (abs_nonneg _) (hB1b (0 : Xn n)))
        hRmeas hCRb hB1m hB1b x]
      refine aP_congr_of_eqOn_abox p.2 (fun y hy => ?_) hx
      rw [Pi.sub_apply, boxRestrR_eq_of_mem hy, haP1 y hy]
      rfl
    rw [hf1, hf2]
  -- ### assemble
  have hchain : (((ℓ ^ 3)⁻¹ : ℝ) : ℂ)
        * rowShape13 (boxRestrictC ℓ Ψ) (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
          (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y) (qmqKernel ℓ k) p
      = ((∫ x in abx n ℓ, aP ℓ p.1 (aQ ℓ p.2 Ψ) x * aP ℓ p.2 (aQ ℓ p.1 Ψ) x
            * k (x p.1) (x p.2) : ℝ) : ℂ) := by
    rw [hA, hB, hmain, hD]
  have hre := congrArg Complex.re hchain
  rw [Complex.mul_re] at hre
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hre
  exact hre

end Work.BoseBoxFock

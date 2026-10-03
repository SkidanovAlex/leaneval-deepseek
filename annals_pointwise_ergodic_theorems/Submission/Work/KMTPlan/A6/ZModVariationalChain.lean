/-
# The `ZMod Q` variational chain (area A6, §8)

This module proves `Work.KMTPlan.A6.ZModChainProp`, the "ZMod `Q` variational chain" input of the
reduction of `Work.KMTPlan.A6.MdlAdelicDefs`.

The argument is the chain of §8 after `form-2`:

* on the finite cyclic group `ZMod Q` with the counting measure every singleton has mass one, so the
  pointwise modulus is dominated by the `L^r`-seminorm (`iSup_enorm_le_eLpNorm_count`, and the
  `ℝ≥0∞`-valued version `iSup_le_eLpNorm_count`);
* the packet form of the paper's Corollary `bilinear-fkr`
  (`Work.KMTPlan.A6.BilinearFkrCyclic`) bounds the `L^r(ZMod Q)`-seminorm of `varPart r` of the
  bilinear averages by `M · V^R(L²(ZMod Q)) · V^R(L²(ZMod Q))` of the two packet families;
* the pointwise decomposition `variationalNorm r a = sup_n ‖a n‖ + varPart r a`, whose sup part is
  controlled by the individual-packet estimate `hbase`;
* Cauchy--Schwarz in the `ℝ`-variable, using the `L²(ℝ; V^R(ℓ²(ZMod Q)))`-bounds `Ku`, `Kv`.

The only structural point is the a.e.-measurability of `X ↦ VrLiftData R Q (fun n => w n X)`, which
is what makes the final Cauchy--Schwarz applicable; it is proved from the (finitely many, hence
measurable) coordinates `X ↦ w n X θ`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlAdelicDefs
import Submission.Work.KMTPlan.A6.BilinearFkrCyclic
import Submission.Port.Aesm

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

noncomputable section

/-! ## The body of `VrLiftData` -/

/-- The two summands of `VrLiftData`, exposed (`rfl`). -/
theorem vrLiftData_eq (R : ℝ) (Q : ℕ) (u : ℕ → ZMod Q → ℂ) :
    VrLiftData R Q u = (⨆ n : ℕ, eLpNorm (u n) 2 (Measure.count : Measure (ZMod Q))) +
      (⨆ (J : ℕ) (k : Fin (J + 1) → ℕ) (_ : Monotone k),
        ENNReal.rpow (Finset.univ.sum fun i : Fin J =>
          ENNReal.rpow (eLpNorm (u (k i.succ) - u (k i.castSucc)) 2
            (Measure.count : Measure (ZMod Q))) R) (1 / R)) := rfl

/-! ## Elementary finite-type facts for the counting measure -/

/-- On a finite type with the counting measure, the pointwise supremum of a `ℝ≥0∞`-valued
function is at most its `L^r`-seminorm (`0 < r`). -/
theorem iSup_le_eLpNorm_count {α : Type*} [MeasurableSpace α] [Fintype α]
    [MeasurableSingletonClass α] {r : NNReal} (hr : 0 < r) (G : α → ENNReal) :
    (iSup fun a => G a) ≤ eLpNorm G (r : ENNReal) (Measure.count : Measure α) := by
  have hcoet : ((r : ENNReal)).toReal = (r : ℝ) := by simp
  have hne0 : (r : ENNReal) ≠ 0 := by
    simp only [ne_eq, ENNReal.coe_eq_zero]
    exact ne_of_gt hr
  have hnet : (r : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hne0 hnet, hcoet]
  rw [show (∫⁻ a, ‖G a‖ₑ ^ (r : ℝ) ∂(Measure.count : Measure α))
      = (∑ a, G a ^ (r : ℝ)) from by
    rw [MeasureTheory.lintegral_fintype]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Measure.count_singleton, mul_one, enorm_eq_self]]
  refine iSup_le (fun a => ?_)
  calc G a = (G a ^ (r : ℝ)) ^ ((1 : ℝ) / r) := by
        rw [← ENNReal.rpow_mul, show (r : ℝ) * ((1 : ℝ) / r) = 1 by field_simp,
          ENNReal.rpow_one]
    _ ≤ (∑ b, G b ^ (r : ℝ)) ^ ((1 : ℝ) / r) :=
        ENNReal.rpow_le_rpow
          (Finset.single_le_sum (f := fun b => G b ^ (r : ℝ)) (fun i _ => zero_le)
            (Finset.mem_univ a)) (by positivity)

/-- On a finite type with the counting measure, the pointwise supremum of the modulus of a
`ℂ`-valued function is at most its `L^r`-seminorm (`0 < r`). -/
theorem iSup_enorm_le_eLpNorm_count {α : Type*} [MeasurableSpace α] [Fintype α]
    [MeasurableSingletonClass α] {r : NNReal} (hr : 0 < r) (f : α → ℂ) :
    (iSup fun a => ‖f a‖ₑ) ≤ eLpNorm f (r : ENNReal) (Measure.count : Measure α) := by
  have h := iSup_le_eLpNorm_count (α := α) hr (fun a => ‖f a‖ₑ)
  have heq : eLpNorm (fun a => ‖f a‖ₑ) (r : ENNReal) (Measure.count : Measure α)
      = eLpNorm f (r : ENNReal) (Measure.count : Measure α) := by
    have hne0 : (r : ENNReal) ≠ 0 := by
      simp only [ne_eq, ENNReal.coe_eq_zero]
      exact ne_of_gt hr
    have hnet : (r : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hne0 hnet,
      MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hne0 hnet]
    rw [show (∫⁻ a, ‖‖f a‖ₑ‖ₑ ^ (((r : ENNReal))).toReal ∂(Measure.count : Measure α))
        = (∫⁻ a, ‖f a‖ₑ ^ (((r : ENNReal))).toReal ∂(Measure.count : Measure α)) from
      lintegral_congr (fun a => by rw [enorm_eq_self])]
  rw [heq] at h
  exact h

/-- On `ZMod Q` with the counting measure the `L²`-seminorm is the finite sum formula. -/
theorem eLpNorm_two_count_zmod {Q : ℕ} [NeZero Q] (g : ZMod Q → ℂ) :
    eLpNorm g 2 (Measure.count : Measure (ZMod Q))
      = (Finset.univ.sum fun a : ZMod Q => ‖g a‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (by norm_num) (by norm_num),
    ENNReal.toReal_ofNat]
  rw [MeasureTheory.lintegral_fintype]
  refine congrArg (fun t => t ^ ((1 : ℝ) / 2)) ?_
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Measure.count_singleton, mul_one]

/-! ## A.e.-measurability of the `V^R`-data of a packet family -/

/-- A supremum of a constant family over a proposition is a.e.-measurable. -/
theorem aemeasurable_iSup_prop_const {p : Prop} {F : ℝ → ENNReal}
    (hF : AEMeasurable F volume) :
    AEMeasurable (fun X : ℝ => ⨆ (_ : p), F X) volume := by
  by_cases hp : p
  · have heq : (fun X : ℝ => ⨆ (_ : p), F X) = F := by
      funext X
      exact le_antisymm (iSup_le (f := fun _ : p => F X) (fun _ => le_rfl))
        (le_iSup (fun _ : p => F X) hp)
    rw [heq]
    exact hF
  · have heq : (fun X : ℝ => ⨆ (_ : p), F X) = fun _ : ℝ => ⊥ := by
      funext X
      exact le_antisymm (iSup_le (f := fun _ : p => F X) (fun h => (hp h).elim)) bot_le
    rw [heq]
    exact aemeasurable_const

/-- The `L²(ZMod Q)`-seminorm of a coordinatewise a.e.-measurable family is a.e.-measurable. -/
theorem aemeasurable_eLpNorm_two_zmod {Q : ℕ} [NeZero Q] (φ : ℝ → ZMod Q → ℂ)
    (hφ : ∀ a : ZMod Q, AEMeasurable (fun X : ℝ => φ X a)) :
    AEMeasurable (fun X : ℝ => eLpNorm (φ X) 2 (Measure.count : Measure (ZMod Q))) := by
  have hsum : AEMeasurable (fun X : ℝ =>
      Finset.univ.sum fun a : ZMod Q => ‖φ X a‖ₑ ^ (2 : ℝ)) := by
    have h := Finset.aemeasurable_sum (f := fun a X => ‖φ X a‖ₑ ^ (2 : ℝ))
      (Finset.univ : Finset (ZMod Q)) (fun a _ =>
        (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable.comp_aemeasurable
          (measurable_enorm.comp_aemeasurable (hφ a)))
    exact h.congr (Filter.Eventually.of_forall (fun X => by rw [Finset.sum_apply]))
  exact ((ENNReal.continuous_rpow_const (y := ((1 : ℝ) / 2))).measurable.comp_aemeasurable
    hsum).congr (Filter.Eventually.of_forall
      (fun X => (eLpNorm_two_count_zmod (φ X)).symm))

/-- One summand of the variation part of `VrLiftData` (for a fixed `J` and `k`) is
a.e.-measurable. -/
theorem aemeasurable_varTerm {Q : ℕ} [NeZero Q] (R : ℝ) (J : ℕ) (k : Fin (J + 1) → ℕ)
    {w : ℕ → ℝ → ZMod Q → ℂ}
    (hw : ∀ (n : ℕ) (a : ZMod Q), AEMeasurable (fun X : ℝ => w n X a)) :
    AEMeasurable (fun X : ℝ => ENNReal.rpow (Finset.univ.sum fun i : Fin J =>
      ENNReal.rpow (eLpNorm (fun θ : ZMod Q => w (k i.succ) X θ - w (k i.castSucc) X θ) 2
        (Measure.count : Measure (ZMod Q))) R) (1 / R)) := by
  have hsum' := Finset.aemeasurable_sum (f := fun i X => ENNReal.rpow (eLpNorm
      (fun θ : ZMod Q => w (k i.succ) X θ - w (k i.castSucc) X θ) 2
        (Measure.count : Measure (ZMod Q))) R) (Finset.univ : Finset (Fin J))
    (fun i _ => (aemeasurable_eLpNorm_two_zmod (φ := fun X : ℝ => fun θ : ZMod Q =>
        w (k i.succ) X θ - w (k i.castSucc) X θ)
      (fun a => (hw (k i.succ) a).sub (hw (k i.castSucc) a))).pow_const R)
  have hsum : AEMeasurable (fun X : ℝ => Finset.univ.sum fun i : Fin J => ENNReal.rpow (eLpNorm
      (fun θ : ZMod Q => w (k i.succ) X θ - w (k i.castSucc) X θ) 2
        (Measure.count : Measure (ZMod Q))) R) :=
    hsum'.congr (Filter.Eventually.of_forall (fun X => by rw [Finset.sum_apply]))
  exact hsum.pow_const ((1 : ℝ) / R)

/-- **The `VrLiftData` of a family that is a.e.-measurable in every coordinate is a.e.-measurable.**
This is the measurability input of the final Cauchy--Schwarz in the `ℝ`-variable. -/
theorem aemeasurable_vrLiftData {Q : ℕ} [NeZero Q] (R : ℝ) {w : ℕ → ℝ → ZMod Q → ℂ}
    (hw : ∀ (n : ℕ) (a : ZMod Q), AEMeasurable (fun X : ℝ => w n X a)) :
    AEMeasurable (fun X : ℝ => VrLiftData R Q (fun n : ℕ => w n X)) := by
  have hfirst : AEMeasurable (fun X : ℝ =>
      ⨆ n : ℕ, eLpNorm (w n X) 2 (Measure.count : Measure (ZMod Q))) :=
    AEMeasurable.iSup (f := fun n X => eLpNorm (w n X) 2 (Measure.count : Measure (ZMod Q)))
      (fun n => aemeasurable_eLpNorm_two_zmod (φ := fun X : ℝ => w n X) (fun a => hw n a))
  have hvar : AEMeasurable (fun X : ℝ =>
      ⨆ (J : ℕ) (k : Fin (J + 1) → ℕ) (_ : Monotone k),
        ENNReal.rpow (Finset.univ.sum fun i : Fin J =>
          ENNReal.rpow (eLpNorm (fun θ : ZMod Q => w (k i.succ) X θ - w (k i.castSucc) X θ) 2
            (Measure.count : Measure (ZMod Q))) R) (1 / R)) := by
    refine AEMeasurable.iSup (f := fun J X => ⨆ (k : Fin (J + 1) → ℕ) (_ : Monotone k),
      ENNReal.rpow (Finset.univ.sum fun i : Fin J =>
        ENNReal.rpow (eLpNorm (fun θ : ZMod Q => w (k i.succ) X θ - w (k i.castSucc) X θ) 2
          (Measure.count : Measure (ZMod Q))) R) (1 / R)) (fun J => ?_)
    refine AEMeasurable.iSup (f := fun k X => ⨆ (_ : Monotone k),
      ENNReal.rpow (Finset.univ.sum fun i : Fin J =>
        ENNReal.rpow (eLpNorm (fun θ : ZMod Q => w (k i.succ) X θ - w (k i.castSucc) X θ) 2
          (Measure.count : Measure (ZMod Q))) R) (1 / R)) (fun k => ?_)
    exact aemeasurable_iSup_prop_const (aemeasurable_varTerm R J k hw)
  refine (hfirst.add hvar).congr ?_
  filter_upwards with X
  exact (vrLiftData_eq R Q (fun n : ℕ => w n X)).symm

/-! ## The chain -/

/-- **The `ZMod Q` variational chain** (the paper's §8 argument at `(p₁,p₂,p) = (2,2,1)`). -/
theorem ZModVariationalChain : Work.KMTPlan.A6.ZModChainProp := by
  intro r hr R hR hRr
  obtain ⟨C, hCpos, hC⟩ := BilinearFkrCyclic (R := R) (r := r) hR hRr
  refine ⟨1 + C, by linarith, ?_⟩
  intro Q hQ M Ku Kv hM hKu hKv B hadd₁ hadd₂ u v humeas hvmeas hbase hB1 hB2 hSu hSv
  haveI : NeZero Q := ⟨by omega⟩
  have hrpos : (0 : NNReal) < r := lt_of_lt_of_le zero_lt_one hr
  have hQ0 : (Q : ENNReal) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hQtop : (Q : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top Q
  have hUmeas : AEMeasurable (fun X : ℝ => VrLiftData R Q (fun n : ℕ => u n X)) :=
    aemeasurable_vrLiftData R (fun n θ => humeas n θ)
  have hVmeas : AEMeasurable (fun X : ℝ => VrLiftData R Q (fun n : ℕ => v n X)) :=
    aemeasurable_vrLiftData R (fun n θ => hvmeas n θ)
  -- the pointwise bound
  have hpt : ∀ X : ℝ, (Q : ENNReal)⁻¹ * ∑ ρ ∈ Finset.range Q,
      variationalNorm r (fun n : ℕ => B (u n X) (v n X) ((ρ : ℤ) : ZMod Q))
      ≤ ENNReal.ofReal (1 + C) * ENNReal.ofReal M *
          (VrLiftData R Q (fun n : ℕ => u n X) * VrLiftData R Q (fun n : ℕ => v n X)) := by
    intro X
    have hleU : (⨆ n : ℕ, eLpNorm (u n X) 2 (Measure.count : Measure (ZMod Q)))
        ≤ VrLiftData R Q (fun n : ℕ => u n X) := by
      rw [vrLiftData_eq]
      exact le_add_right le_rfl
    have hleV : (⨆ n : ℕ, eLpNorm (v n X) 2 (Measure.count : Measure (ZMod Q)))
        ≤ VrLiftData R Q (fun n : ℕ => v n X) := by
      rw [vrLiftData_eq]
      exact le_add_right le_rfl
    have hA : (⨆ ρ : ZMod Q, ⨆ n : ℕ, ‖B (u n X) (v n X) ρ‖ₑ)
        ≤ ENNReal.ofReal M * VrLiftData R Q (fun n : ℕ => u n X)
            * VrLiftData R Q (fun n : ℕ => v n X) := by
      calc (⨆ ρ : ZMod Q, ⨆ n : ℕ, ‖B (u n X) (v n X) ρ‖ₑ)
          = ⨆ n : ℕ, ⨆ ρ : ZMod Q, ‖B (u n X) (v n X) ρ‖ₑ := iSup_comm
        _ ≤ ENNReal.ofReal M * VrLiftData R Q (fun n : ℕ => u n X)
              * VrLiftData R Q (fun n : ℕ => v n X) := by
            refine iSup_le (fun n => ?_)
            calc (⨆ ρ : ZMod Q, ‖B (u n X) (v n X) ρ‖ₑ)
                ≤ eLpNorm (fun ρ : ZMod Q => B (u n X) (v n X) ρ) (r : ENNReal)
                    (Measure.count : Measure (ZMod Q)) :=
                  iSup_enorm_le_eLpNorm_count hrpos _
              _ ≤ ENNReal.ofReal M * eLpNorm (u n X) 2 (Measure.count : Measure (ZMod Q))
                    * eLpNorm (v n X) 2 (Measure.count : Measure (ZMod Q)) := hbase X n
              _ ≤ ENNReal.ofReal M * VrLiftData R Q (fun n : ℕ => u n X)
                    * VrLiftData R Q (fun n : ℕ => v n X) :=
                  mul_le_mul'
                    (mul_le_mul' le_rfl
                      (le_trans (le_iSup (fun n : ℕ =>
                        eLpNorm (u n X) 2 (Measure.count : Measure (ZMod Q))) n) hleU))
                    (le_trans (le_iSup (fun n : ℕ =>
                      eLpNorm (v n X) 2 (Measure.count : Measure (ZMod Q))) n) hleV)
    have hBv : (⨆ ρ : ZMod Q, varPart r (fun n : ℕ => B (u n X) (v n X) ρ))
        ≤ ENNReal.ofReal (C * M) * VrLiftData R Q (fun n : ℕ => u n X)
            * VrLiftData R Q (fun n : ℕ => v n X) :=
      le_trans (iSup_le_eLpNorm_count hrpos
          (fun ρ : ZMod Q => varPart r (fun n : ℕ => B (u n X) (v n X) ρ)))
        (hC (Q := Q) hQ (M := M) hM B hadd₁ hadd₂ (fun n => u n X) (fun n => v n X)
          (fun m n l => hB1 X m n l) (fun m n l => hB2 X m n l))
    have hS : (⨆ ρ : ZMod Q, variationalNorm r (fun n : ℕ => B (u n X) (v n X) ρ))
        ≤ ENNReal.ofReal (1 + C) * ENNReal.ofReal M *
            (VrLiftData R Q (fun n : ℕ => u n X) * VrLiftData R Q (fun n : ℕ => v n X)) := by
      calc (⨆ ρ : ZMod Q, variationalNorm r (fun n : ℕ => B (u n X) (v n X) ρ))
          = ⨆ ρ : ZMod Q, ((⨆ n : ℕ, ‖B (u n X) (v n X) ρ‖ₑ)
              + varPart r (fun n : ℕ => B (u n X) (v n X) ρ)) :=
            iSup_congr (fun ρ => variationalNorm_eq_add r _)
        _ ≤ (⨆ ρ : ZMod Q, ⨆ n : ℕ, ‖B (u n X) (v n X) ρ‖ₑ)
              + (⨆ ρ : ZMod Q, varPart r (fun n : ℕ => B (u n X) (v n X) ρ)) :=
            iSup_add_le _ _
        _ ≤ ENNReal.ofReal M * VrLiftData R Q (fun n : ℕ => u n X)
              * VrLiftData R Q (fun n : ℕ => v n X)
            + ENNReal.ofReal (C * M) * VrLiftData R Q (fun n : ℕ => u n X)
              * VrLiftData R Q (fun n : ℕ => v n X) :=
            add_le_add hA hBv
        _ = ENNReal.ofReal (1 + C) * ENNReal.ofReal M *
              (VrLiftData R Q (fun n : ℕ => u n X) * VrLiftData R Q (fun n : ℕ => v n X)) := by
            have h1 : ENNReal.ofReal (1 + C) = 1 + ENNReal.ofReal C := by
              rw [ENNReal.ofReal_add (by norm_num) hCpos.le, ENNReal.ofReal_one]
            have h2 : ENNReal.ofReal (C * M) = ENNReal.ofReal C * ENNReal.ofReal M :=
              ENNReal.ofReal_mul hCpos.le
            rw [h1, h2]
            ring
    have hsum : ∑ ρ ∈ Finset.range Q,
          variationalNorm r (fun n : ℕ => B (u n X) (v n X) ((ρ : ℤ) : ZMod Q))
        ≤ (Q : ENNReal) * (⨆ ρ : ZMod Q,
            variationalNorm r (fun n : ℕ => B (u n X) (v n X) ρ)) := by
      calc ∑ ρ ∈ Finset.range Q,
            variationalNorm r (fun n : ℕ => B (u n X) (v n X) ((ρ : ℤ) : ZMod Q))
          ≤ ∑ _ρ ∈ Finset.range Q, (⨆ ρ : ZMod Q,
              variationalNorm r (fun n : ℕ => B (u n X) (v n X) ρ)) :=
            Finset.sum_le_sum (fun ρ _ => le_iSup
              (fun ρ' : ZMod Q => variationalNorm r (fun n : ℕ => B (u n X) (v n X) ρ'))
              ((ρ : ℤ) : ZMod Q))
        _ = (Finset.range Q).card • (⨆ ρ : ZMod Q,
              variationalNorm r (fun n : ℕ => B (u n X) (v n X) ρ)) := Finset.sum_const _
        _ = (Q : ENNReal) * (⨆ ρ : ZMod Q,
              variationalNorm r (fun n : ℕ => B (u n X) (v n X) ρ)) := by
            rw [Finset.card_range, nsmul_eq_mul]
    calc (Q : ENNReal)⁻¹ * ∑ ρ ∈ Finset.range Q,
          variationalNorm r (fun n : ℕ => B (u n X) (v n X) ((ρ : ℤ) : ZMod Q))
        ≤ (Q : ENNReal)⁻¹ * ((Q : ENNReal) * (⨆ ρ : ZMod Q,
            variationalNorm r (fun n : ℕ => B (u n X) (v n X) ρ))) := mul_le_mul' le_rfl hsum
      _ = (⨆ ρ : ZMod Q, variationalNorm r (fun n : ℕ => B (u n X) (v n X) ρ)) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hQ0 hQtop, one_mul]
      _ ≤ ENNReal.ofReal (1 + C) * ENNReal.ofReal M *
            (VrLiftData R Q (fun n : ℕ => u n X) * VrLiftData R Q (fun n : ℕ => v n X)) := hS
  -- the Cauchy--Schwarz in the `ℝ`-variable
  have hU₂ : (∫⁻ X : ℝ, (VrLiftData R Q (fun n : ℕ => u n X)) ^ (2 : ℝ))
      = ∫⁻ X : ℝ, (VrLiftData R Q (fun n : ℕ => u n X)) ^ (2 : ℕ) :=
    lintegral_congr (fun X => by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast])
  have hV₂ : (∫⁻ X : ℝ, (VrLiftData R Q (fun n : ℕ => v n X)) ^ (2 : ℝ))
      = ∫⁻ X : ℝ, (VrLiftData R Q (fun n : ℕ => v n X)) ^ (2 : ℕ) :=
    lintegral_congr (fun X => by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast])
  have hSu' : ∫⁻ X : ℝ, (VrLiftData R Q (fun n : ℕ => u n X)) ^ (2 : ℝ)
      ≤ ENNReal.ofReal (Ku ^ 2) := by
    rw [hU₂]
    exact hSu
  have hSv' : ∫⁻ X : ℝ, (VrLiftData R Q (fun n : ℕ => v n X)) ^ (2 : ℝ)
      ≤ ENNReal.ofReal (Kv ^ 2) := by
    rw [hV₂]
    exact hSv
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
        VrLiftData R Q (fun n : ℕ => u n X) * VrLiftData R Q (fun n : ℕ => v n X)
      ≤ ENNReal.ofReal Ku * ENNReal.ofReal Kv := by
    calc ∫⁻ X : ℝ, VrLiftData R Q (fun n : ℕ => u n X) * VrLiftData R Q (fun n : ℕ => v n X)
        ≤ (∫⁻ X : ℝ, (VrLiftData R Q (fun n : ℕ => u n X)) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
            * (∫⁻ X : ℝ, (VrLiftData R Q (fun n : ℕ => v n X)) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) :=
          ENNReal.lintegral_mul_le_Lp_mul_Lq volume
            (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩) hUmeas hVmeas
      _ ≤ (ENNReal.ofReal (Ku ^ 2)) ^ ((1 : ℝ) / 2)
            * (ENNReal.ofReal (Kv ^ 2)) ^ ((1 : ℝ) / 2) :=
          mul_le_mul' (ENNReal.rpow_le_rpow hSu' (by norm_num))
            (ENNReal.rpow_le_rpow hSv' (by norm_num))
      _ = ENNReal.ofReal Ku * ENNReal.ofReal Kv := by rw [hKu2, hKv2]
  calc ∫⁻ X : ℝ, (Q : ENNReal)⁻¹ * ∑ ρ ∈ Finset.range Q,
        variationalNorm r (fun n : ℕ => B (u n X) (v n X) ((ρ : ℤ) : ZMod Q))
      ≤ ∫⁻ X : ℝ, ENNReal.ofReal (1 + C) * ENNReal.ofReal M *
          (VrLiftData R Q (fun n : ℕ => u n X) * VrLiftData R Q (fun n : ℕ => v n X)) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (1 + C) * ENNReal.ofReal M *
          ∫⁻ X : ℝ, VrLiftData R Q (fun n : ℕ => u n X) * VrLiftData R Q (fun n : ℕ => v n X) :=
        lintegral_const_mul' (ENNReal.ofReal (1 + C) * ENNReal.ofReal M)
          (fun X : ℝ => VrLiftData R Q (fun n : ℕ => u n X)
            * VrLiftData R Q (fun n : ℕ => v n X))
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    _ ≤ ENNReal.ofReal (1 + C) * ENNReal.ofReal M * (ENNReal.ofReal Ku * ENNReal.ofReal Kv) :=
        mul_le_mul' le_rfl hholder
    _ = ENNReal.ofReal (1 + C) * ENNReal.ofReal M * ENNReal.ofReal Ku * ENNReal.ofReal Kv := by
        ring

end

end Work.KMTPlan.A6

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiRow_muEvalAux
import Submission.Work.BoseBoxFock.chiRow_pairSlot_split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiRow_muEvalSelf` — the two orientations of the `χ`-row `μ`-evaluation

This module proves, in one file, the two half-rows into which the `μ`-line of the FS `Q₁`
`χ`-sandwich splits:

    `(cIPn n Ψ (boxSlotSum e (|C⟩⟨e₀|) Ψ)).re = ∑ j, ∫_{abox} (P_jΦ)·Φ·χ_w(x_j)`   (row 1),
    `(cIPn n Ψ (boxSlotSum e (|e₀⟩⟨C|) Ψ)).re = ∑ j, ∫_{abox} (P_jΦ)·Φ·χ_w(x_j)`   (row 2),

with `Ψ = boxRestrictC ℓ Φ` and `χ_w = chiW ℓ N`.  Their sum is `muForm n ℓ (chiW ℓ N) Φ`
(the factor `2` of `muForm`).

Row 1 is the dictionary `chiRow_chiMode_dict` (the slot sum at `|C⟩⟨e₀|` is
`∑_j chiMode(x_j)·aPC_j Ψ` a.e. on the box), the box-relative identification
`aPC_j Ψ = ↑(aP_j Φ)` and `Re chiMode = chiW` on the cube.
Row 2 is the transpose dictionary `chiRow_chiModeT_dict` (the slot sum at `|e₀⟩⟨C|` is
`∑_j aPC_j(conj(chiMode(·_j))·Ψ)`), the real-part identification
`Re aPC_j F = aP_j (Re ∘ F)` (`chiRow_aPC_dict`), the pointwise reduction
`(conj(chiMode(y_j))·Ψ y).re = chiW(y_j)·Φ y` on the box, and the *mixed-hypothesis*
self-adjointness of the slot mean `aP_sym_sum_pt_of_boundOn`
(`chiRow_pairSlot_split.lean`), which both commutes `aP_j` with the multiplication by `Φ` and
performs the finite-sum interchange.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

/-! ## Row 1: the `|C⟩⟨e₀|` orientation -/

theorem chiRow_muEval_row1_self {n m : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ}
    {e : Fin m → Sp → ℂ}
    (hpin : e 0 =ᵐ[MeasureTheory.volume] fun z =>
      ((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ z)
    (hmeas : ∀ l, Measurable (e l)) (hemem : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {C : Fin m → ℝ} (hC : (fun z => ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * Work.BoseDict.etaOf e C z)
      =ᵐ[MeasureTheory.volume] Work.BoseBoxFock.chiMode ℓ N)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    (Work.BoseDict.cIPn n (Work.BoseBoxFock.boxRestrictC ℓ Φ)
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair C (Work.BoseBoxFock.evec0 m))
          (Work.BoseBoxFock.boxRestrictC ℓ Φ))).re
      = ∑ j : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.aP ℓ j Φ x) * Φ x * Work.BoseBoxFock.chiW ℓ N (x j) := by
  classical
  have hΨm : Measurable (boxRestrictC ℓ Φ) := boxRestrictC_measurable ℓ hΦc
  obtain ⟨Cw, hCw0, hCw⟩ := chiW_norm_bound
  obtain ⟨CΨ, hCΨ0, hCΨ⟩ := boxRestrictC_norm_bound (n := n) (ℓ := ℓ) hℓ hΦc
  -- the slot dictionary at the pinned `χ`-mode
  have hdict := chiRow_chiMode_dict (m := m) (d := n) (N := N) hℓ hpin hmeas hbdd hsupp hC
    (boxRestrictC ℓ Φ) hΨm ⟨CΨ, hCΨ⟩
  -- integrability of the `Φ`-weighted slot sum (transferred from the `aPC` presentation)
  have hIntG : IntegrableOn (fun x : Submission.BoseGases.X n => (((Φ x : ℝ)) : ℂ) *
      (Work.BoseDict.boxSlotSum e (rankOnePair C (evec0 m)) (boxRestrictC ℓ Φ) x))
      (Submission.BoseGases.abox n ℓ) := by
    refine (integrableOn_rowIntegrand_first (n := n) (ℓ := ℓ) hℓ (N := N) hΦc).congr ?_
    filter_upwards [hdict] with x hx
    rw [hx]
  -- per-slot integrability for the finite-sum interchange
  have hint : ∀ j : Fin n, IntegrableOn (fun x : Submission.BoseGases.X n =>
      Φ x * (chiW ℓ N (x j) * Submission.BoseGases.aP ℓ j Φ x))
      (Submission.BoseGases.abox n ℓ) := by
    intro j
    have h1 : IntegrableOn (fun x : Submission.BoseGases.X n =>
        Φ x * Submission.BoseGases.aP ℓ j Φ x) (Submission.BoseGases.abox n ℓ) :=
      Submission.BoseGases.integrableOn_abox_of_continuous hℓ
        (hΦc.mul (Submission.BoseGases.aP_continuous hℓ j hΦc))
    have h2 : AEStronglyMeasurable (fun x : Submission.BoseGases.X n => chiW ℓ N (x j))
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)) :=
      ((chiW_measurable ℓ N).comp (measurable_pi_apply j)).aestronglyMeasurable
    have h3 : ∀ᵐ x ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)), ‖chiW ℓ N (x j)‖ ≤ Cw :=
      Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs]
        exact hCw ℓ hℓ N (x j))
    refine (h1.mul_bdd h2 h3).congr (Filter.Eventually.of_forall (fun x => ?_))
    ring
  -- the pointwise real evaluation of the `aPC` presentation on the box
  have hSre : ∀ x ∈ Submission.BoseGases.abox n ℓ,
      (∑ j : Fin n, chiMode ℓ N (x j) * aPC ℓ j (boxRestrictC ℓ Φ) x).re
        = ∑ j : Fin n, chiW ℓ N (x j) * Submission.BoseGases.aP ℓ j Φ x := by
    intro x hx
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hj : x j ∈ Submission.BoseGases.acube ℓ :=
      (Submission.BoseGases.mem_abox_iff n ℓ x).mp hx j
    have h1 : aPC ℓ j (boxRestrictC ℓ Φ) x
        = ((Submission.BoseGases.aP ℓ j Φ x : ℝ) : ℂ) :=
      (chiRow_aPC_dict (n := n) (ℓ := ℓ) hℓ).2.1 j Φ x hx
    rw [h1, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      chiMode_re_of_theta_eq_one ℓ N (thetaFun_eq_one_of_mem_acube hℓ hj)]
  rw [cIPn_boxRestrictC_re hIntG]
  rw [show (∫ x in Submission.BoseGases.abox n ℓ, Φ x *
        (Work.BoseDict.boxSlotSum e (rankOnePair C (evec0 m)) (boxRestrictC ℓ Φ) x).re)
      = ∫ x in Submission.BoseGases.abox n ℓ, Φ x *
        ((∑ j : Fin n, chiMode ℓ N (x j) * aPC ℓ j (boxRestrictC ℓ Φ) x)).re from by
    refine integral_congr_ae ?_
    filter_upwards [hdict] with x hx
    rw [hx]]
  rw [show (∫ x in Submission.BoseGases.abox n ℓ, Φ x *
        ((∑ j : Fin n, chiMode ℓ N (x j) * aPC ℓ j (boxRestrictC ℓ Φ) x)).re)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          ∑ j : Fin n, Φ x * (chiW ℓ N (x j) * Submission.BoseGases.aP ℓ j Φ x) from by
    refine integral_congr_ae ?_
    filter_upwards [self_mem_ae_restrict (Submission.BoseGases.abox_measurable n ℓ)] with x hx
    rw [hSre x hx, Finset.mul_sum]]
  have hswap : (∫ x in Submission.BoseGases.abox n ℓ,
        ∑ j : Fin n, Φ x * (chiW ℓ N (x j) * Submission.BoseGases.aP ℓ j Φ x))
      = ∑ j : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          Φ x * (chiW ℓ N (x j) * Submission.BoseGases.aP ℓ j Φ x) :=
    MeasureTheory.integral_finsetSum (Finset.univ : Finset (Fin n)) (fun j _ => hint j)
  rw [hswap]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  ring

/-! ## Row 2: the `|e₀⟩⟨C|` orientation -/

theorem chiRow_muEval_row2_self {n m : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ}
    {e : Fin m → Sp → ℂ}
    (hpin : e 0 =ᵐ[MeasureTheory.volume] fun z =>
      ((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ z)
    (hmeas : ∀ l, Measurable (e l)) (hemem : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {C : Fin m → ℝ} (hC : (fun z => ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * Work.BoseDict.etaOf e C z)
      =ᵐ[MeasureTheory.volume] Work.BoseBoxFock.chiMode ℓ N)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    (Work.BoseDict.cIPn n (Work.BoseBoxFock.boxRestrictC ℓ Φ)
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair (Work.BoseBoxFock.evec0 m) C)
          (Work.BoseBoxFock.boxRestrictC ℓ Φ))).re
      = ∑ j : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.aP ℓ j Φ x) * Φ x * Work.BoseBoxFock.chiW ℓ N (x j) := by
  classical
  have hΨm : Measurable (boxRestrictC ℓ Φ) := boxRestrictC_measurable ℓ hΦc
  obtain ⟨Cm, hCm0, hCm⟩ := chiMode_norm_bound
  obtain ⟨CΨ, hCΨ0, hCΨ⟩ := boxRestrictC_norm_bound (n := n) (ℓ := ℓ) hℓ hΦc
  obtain ⟨Cw, hCw0, hCw⟩ := chiW_norm_bound
  obtain ⟨CΦ, hCΦ⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    hΦc.continuousOn
  -- the slot dictionary at the pinned `χ`-mode (transpose orientation)
  have hdict := chiRow_chiModeT_dict (m := m) (d := n) (N := N) hℓ hpin hmeas hbdd hsupp hC
    (boxRestrictC ℓ Φ) hΨm ⟨CΨ, hCΨ⟩
  -- integrability of the `Φ`-weighted slot sum (transferred from the `aPC` presentation)
  have hIntG : IntegrableOn (fun x : Submission.BoseGases.X n => (((Φ x : ℝ)) : ℂ) *
      (Work.BoseDict.boxSlotSum e (rankOnePair (evec0 m) C) (boxRestrictC ℓ Φ) x))
      (Submission.BoseGases.abox n ℓ) := by
    refine (integrableOn_rowIntegrand_second (n := n) (ℓ := ℓ) hℓ (N := N) hΦc).congr ?_
    filter_upwards [hdict] with x hx
    rw [hx]
  -- the twisted states and their basic facts
  set F : Fin n → Submission.BoseGases.X n → ℂ :=
    fun j y => (starRingEnd ℂ) (chiMode ℓ N (y j)) * boxRestrictC ℓ Φ y with hF
  have hFm : ∀ j : Fin n, Measurable (F j) := by
    intro j
    rw [hF]
    exact (Complex.continuous_conj.measurable.comp
      ((chiMode_measurable ℓ N).comp (measurable_pi_apply j))).mul
      (boxRestrictC_measurable ℓ hΦc)
  have hFb : ∀ j : Fin n, ∃ D : ℝ, ∀ x : Submission.BoseGases.X n, ‖F j x‖ ≤ D := by
    intro j
    exact ⟨Cm * CΨ, fun x => by
      rw [hF]
      simp only []
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (hCm ℓ hℓ N (x j)) (hCΨ x) (norm_nonneg _) hCm0⟩
  -- the real weights `F j` and their bounds on the box
  set W : Fin n → Submission.BoseGases.X n → ℝ :=
    fun j y => chiW ℓ N (y j) * Φ y with hW
  have hWm : ∀ j : Fin n, Measurable (W j) := by
    intro j
    rw [hW]
    exact ((chiW_measurable ℓ N).comp (measurable_pi_apply j)).mul hΦc.measurable
  have hWb : ∀ j : Fin n, ∀ x ∈ Submission.BoseGases.abox n ℓ,
      |W j x| ≤ Cw * max CΦ 0 := by
    intro j x hx
    rw [hW]
    rw [abs_mul]
    refine mul_le_mul (hCw ℓ hℓ N (x j))
      ((hCΦ x hx).trans (le_max_left _ _)) (abs_nonneg _) hCw0
  -- the pointwise real evaluation on the box
  have hSre : ∀ x ∈ Submission.BoseGases.abox n ℓ,
      (∑ j : Fin n, aPC ℓ j (F j) x).re
        = ∑ j : Fin n, Submission.BoseGases.aP ℓ j (W j) x := by
    intro x hx
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hrow1x : (aPC ℓ j (F j) x).re = Submission.BoseGases.aP ℓ j (fun y => (F j y).re) x :=
      congrFun ((chiRow_aPC_dict (n := n) (ℓ := ℓ) hℓ).1 j (hFm j) (hFb j)) x
    rw [hrow1x]
    refine (chiRow_aP_abox_facts hℓ).2.2 j (fun y hy => ?_) x hx
    have hyj : y j ∈ Submission.BoseGases.acube ℓ :=
      (Submission.BoseGases.mem_abox_iff n ℓ y).mp hy j
    have hΨy : boxRestrictC ℓ Φ y = ((Φ y : ℝ) : ℂ) := by
      rw [show boxRestrictC ℓ Φ y = ((Φ y : ℝ) : ℂ) *
          ((((Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) y : ℝ)) : ℂ) from rfl,
        Set.indicator_of_mem hy]
      simp
    show ((starRingEnd ℂ) (chiMode ℓ N (y j)) * boxRestrictC ℓ Φ y).re
      = chiW ℓ N (y j) * Φ y
    rw [hΨy, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero,
      chiMode_re_of_theta_eq_one ℓ N (thetaFun_eq_one_of_mem_acube hℓ hyj)]
  rw [cIPn_boxRestrictC_re hIntG]
  rw [show (∫ x in Submission.BoseGases.abox n ℓ, Φ x *
        (Work.BoseDict.boxSlotSum e (rankOnePair (evec0 m) C) (boxRestrictC ℓ Φ) x).re)
      = ∫ x in Submission.BoseGases.abox n ℓ, Φ x *
        ((∑ j : Fin n, aPC ℓ j (F j) x)).re from by
    refine integral_congr_ae ?_
    filter_upwards [hdict] with x hx
    rw [hx]]
  rw [show (∫ x in Submission.BoseGases.abox n ℓ, Φ x *
        ((∑ j : Fin n, aPC ℓ j (F j) x)).re)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          Φ x * (∑ j : Fin n, Submission.BoseGases.aP ℓ j (W j) x) from by
    refine integral_congr_ae ?_
    filter_upwards [self_mem_ae_restrict (Submission.BoseGases.abox_measurable n ℓ)] with x hx
    rw [hSre x hx]]
  rw [aP_sym_sum_pt_of_boundOn (n := n) (ℓ := ℓ) hℓ hΦc hWm
    (mul_nonneg hCw0 (le_max_right _ _)) hWb]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp only [hW]
  ring

end Work.BoseBoxFock

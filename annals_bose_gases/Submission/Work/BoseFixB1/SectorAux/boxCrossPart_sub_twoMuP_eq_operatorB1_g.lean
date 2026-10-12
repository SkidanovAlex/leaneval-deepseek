import ChallengeDeps
import Submission.Work.BoseFixB1.SectorAux.boxMuLine_slot_split_g
import Submission.Work.BoseFixB1.SectorAux.boxQ1_pair_replace_fibre_g
import Submission.Work.BoseFixB1.SectorAux.integrableOn_pairCross_pieces_w1_g
import Submission.Work.BoseFixB1.SectorAux.integrableOn_pairG0_fibre_g
import Submission.Work.BoseFixB1.boxCrossPart_sub_twoMuP_eq_operatorB1
import Submission.Work.BoseFixB1P.boxPeel_general
import Submission.Work.BoseFixB1S.boxPInd_boxComp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.SectorAux.boxCrossPart_sub_twoMuP_eq_operatorB1_g`

The **generalised** (`_g`) form of `Work.BoseFixB1.boxCrossPart_sub_twoMuP_eq_operatorB1`:
FS `eq:Q1n0` for the cross term of the box-projected pair block, with the state assumed only
*measurable* and *bounded on the analysis box* (`hΦm`, `hΦb`) instead of *continuous*, and with
the parameters `ℓ d μ` quantified inside the statement.

    boxCrossPart V ℓ A w₁ Φ − 2μ·Σᵢ∫(QᵢΦ)·fib₁(xᵢ)·(PᵢΦ)
       = (2/V)·Σᵢ∫(QᵢΦ)·fib₁(xᵢ)·((Σⱼ PⱼPᵢΦ) − (1+μV)·(PᵢΦ)),

`V = |B(u)| = boxMass ℓ d u`, `A = dlBox ℓ d u`, `w₁ = wSmall1Pair h M ℓ d u`,
`Pᵢ = boxPInd V A i`, `Qᵢ = boxQInd V A i`, `fib₁ = w1Fibre ℓ w₁`.

## Proof

The argument is that of the original (`Continuous`) lemma, with every use of continuity replaced
by the two given hypotheses:

* the one-slot **peel** (`boxPInd_pair_peel_fibre_gen`, fully general in the integrands) with the
  two integrability inputs supplied by the generalised children
  `integrableOn_pairCross_pieces_w1_g` (kernel reading) and `integrableOn_pairG0_fibre_g`
  (fibre reading);
* the **replacement** `boxQ1_pair_replace_fibre_g`;
* the **`μ`-line split** `boxMuLine_slot_split_g`;
* the commutation `P_iP_j = P_jP_i` on the box is the `GoodState` form
  `Work.BoseFixB1S.boxPInd_boxPInd_comm_good` at `⟨hΦm, Cb, hΦb⟩`.

Everything else (the double-sum expansion `boxCrossPart_doubleSum`, the fibre bookkeeping, the
final `V⁻¹`-algebra) is unchanged from the original proof.
-/

namespace Work.BoseFixB1.SectorAux

open MeasureTheory
open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private noncomputable def ixPP {N : ℕ} (V ℓ : ℝ) (A : Set E3)
    (W : E3 → E3 → ℝ) (Φ : Submission.BoseGases.X N → ℝ) (i j : Fin N) : ℝ :=
  ∫ x in Submission.BoseGases.abox N ℓ,
    (Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxQInd V A j Φ) x)
      * (Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Φ) x)
      * W (x i) (x j)

private noncomputable def ixQP {N : ℕ} (V ℓ : ℝ) (A : Set E3)
    (W : E3 → E3 → ℝ) (Φ : Submission.BoseGases.X N → ℝ) (i j : Fin N) : ℝ :=
  ∫ x in Submission.BoseGases.abox N ℓ,
    (Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxQInd V A i Φ) x)
      * (Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Φ) x)
      * W (x i) (x j)

private noncomputable def ixZ {N : ℕ} (V ℓ : ℝ) (A : Set E3)
    (fib : E3 → ℝ) (Φ : Submission.BoseGases.X N → ℝ) (i j : Fin N) : ℝ :=
  ∫ x in Submission.BoseGases.abox N ℓ,
    (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
      * (Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x)

private noncomputable def ixP {N : ℕ} (V ℓ : ℝ) (A : Set E3)
    (fib : E3 → ℝ) (Φ : Submission.BoseGases.X N → ℝ) (i : Fin N) : ℝ :=
  ∫ x in Submission.BoseGases.abox N ℓ,
    (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
      * (Work.UBBInputs8.boxPInd V A i Φ x)

theorem boxCrossPart_sub_twoMuP_eq_operatorB1_g {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) :
    ∀ {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
      (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
      (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
      {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦm : Measurable Φ) {Cb : ℝ}
      (hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ Cb),
      Work.BoseFixB1.boxCrossPart (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
          (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ
        - 2 * μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) i Φ x)
              * Submission.BoseGases.w1Fibre ℓ
                  (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)
              * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i Φ x))
        = (2 / Work.SmallBoxSliding.boxMass ℓ d u)
          * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i Φ x)
                * Submission.BoseGases.w1Fibre ℓ
                    (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)
                * ((∑ j : Fin N, Work.UBBInputs8.boxPInd
                      (Work.SmallBoxSliding.boxMass ℓ d u)
                      (Submission.BoseGases.dlBox ℓ d u) j
                      (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                        (Submission.BoseGases.dlBox ℓ d u) i Φ) x)
                  - (1 + μ * Work.SmallBoxSliding.boxMass ℓ d u)
                      * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                          (Submission.BoseGases.dlBox ℓ d u) i Φ x))) := by
  intro ℓ d μ hℓ hd hR hRχ u hvol N Φ hΦm Cb hΦb
  classical
  set V : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hVdef
  set A : Set E3 := Submission.BoseGases.dlBox ℓ d u with hAdef
  set W : E3 → E3 → ℝ := Submission.BoseGases.wSmall1Pair h M ℓ d u with hWdef
  set fib : E3 → ℝ := Submission.BoseGases.w1Fibre ℓ W with hfibdef
  -- ## basic facts about the box and the fibre
  have hAmeas : MeasurableSet A := by
    rw [hAdef]; exact Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : A ⊆ Submission.BoseGases.acube ℓ := by
    rw [hAdef]; exact Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hVpos : 0 < V := hvol
  have hVne : V ≠ 0 := ne_of_gt hVpos
  have hVeq : V = (MeasureTheory.volume : MeasureTheory.Measure E3).real A := by
    rw [hVdef, hAdef]; exact Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u
  have hVeq' : V = ((MeasureTheory.volume : MeasureTheory.Measure E3) A).toReal := by
    rw [← MeasureTheory.Measure.real_def]; exact hVeq
  have hFm : MeasureTheory.AEStronglyMeasurable fib
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)) := by
    rw [hfibdef, hWdef]
    have hint : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
      Submission.BoseGases.g0_integrable hR0 hv_supp h
    exact Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre (ℓ := ℓ) (d := d) M u
      (f := Submission.BoseGases.g0 v h) hint.aestronglyMeasurable.aemeasurable
  have hCf : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤
      (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
        * ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
            / Work.SmallBoxSliding.smallConvLower M) * (8 * Real.pi * _root_.BoseGases.a v)) := by
    intro z _
    rw [hfibdef, hWdef]
    exact Work.BoseFixB1.wSmall1Pair_fibre_abs_le (v := v) (R0 := R0) hv_supp hR0 hv hvrad h
      hM hℓ hd hR hRχ u z
  have hWsym : ∀ x y : E3, W x y = W y x := by
    intro x y
    rw [hWdef]
    exact Submission.BoseGases.wSmallPair_symm hM u (Submission.BoseGases.g0_even hvrad h) x y
  have hGood : Work.BoseFixB1S.GoodState ℓ Φ := ⟨hΦm, Cb, hΦb⟩
  -- ## the one-slot peel (general form, integrability supplied by the `_g` children)
  have hpeel : ∀ {s t : Fin N}, s ≠ t →
      (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd V A s (Work.UBBInputs8.boxQInd V A t Φ) x)
          * (Work.UBBInputs8.boxPInd V A s (Work.UBBInputs8.boxPInd V A t Φ) x)
          * W (x s) (x t))
      = V⁻¹ * (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd V A s (Work.UBBInputs8.boxQInd V A t Φ) x)
          * (Work.UBBInputs8.boxPInd V A s (Work.UBBInputs8.boxPInd V A t Φ) x)
          * fib (x t)) := by
    intro s t hst
    cases N with
    | zero => exact (Nat.not_lt_zero s.val s.isLt).elim
    | succ n =>
      obtain ⟨t', ht'⟩ := Fin.exists_succAbove_eq (x := t) (y := s) hst.symm
      subst ht'
      exact boxPInd_pair_peel_fibre_gen (n := n) (ℓ := ℓ) (d := d) hℓ u hvol
        (W := W) (fib := fib) (Φ := Φ) (s := s) (t' := t')
        (by
          exact (integrableOn_pairCross_pieces_w1_g (v := v) (R0 := R0) hv_supp hR0 hv hvrad hv1
            h (M := M) hM (ℓ := ℓ) (d := d) hℓ hd hR hRχ u hvol (Φ := Φ) hΦm (Cb := Cb) hΦb
            (s := s) (t := s.succAbove t') (Fin.succAbove_ne s t').symm).1)
        (integrableOn_pairG0_fibre_g (v := v) (R0 := R0) hv_supp hR0 hv hvrad h
          (M := M) hM (ℓ := ℓ) (d := d) hℓ hd hR hRχ u hvol (Φ := Φ) hΦm (Cb := Cb) hΦb
          (s := s) (t := s.succAbove t') (Fin.succAbove_ne s t').symm)
        (fun z => wSmall1Pair_fibre_indicator hvrad h hM hℓ hd u z)
  -- ## the per-pair replacement (general form)
  have hrepl : ∀ {s t : Fin N}, s ≠ t →
      (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd V A s (Work.UBBInputs8.boxQInd V A t Φ) x)
          * (Work.UBBInputs8.boxPInd V A s (Work.UBBInputs8.boxPInd V A t Φ) x)
          * fib (x t))
      = ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd V A t Φ x) * fib (x t)
            * (Work.UBBInputs8.boxPInd V A s (Work.UBBInputs8.boxPInd V A t Φ) x) := by
    intro s t hst
    exact boxQ1_pair_replace_fibre_g (N := N) (ℓ := ℓ) (V := V) hℓ hVpos hAmeas hAc hVeq
      (fib := fib) hFm hCf hΦm hΦb hst
  -- ## (B) the integrand split and the double-sum expansion
  have hE1 : ∀ i j : Fin N, i ≠ j → MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      (Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxQInd V A j Φ) x)
        * (Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Φ) x)
        * W (x i) (x j))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
    intro i j hij
    exact (integrableOn_pairCross_pieces_w1_g (v := v) (R0 := R0) hv_supp hR0 hv hvrad hv1 h
      (M := M) hM (ℓ := ℓ) (d := d) hℓ hd hR hRχ u hvol (Φ := Φ) hΦm (Cb := Cb) hΦb
      (s := i) (t := j) hij).1
  have hE2 : ∀ i j : Fin N, i ≠ j → MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      (Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxQInd V A i Φ) x)
        * (Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Φ) x)
        * W (x i) (x j))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
    intro i j hij
    exact (integrableOn_pairCross_pieces_w1_g (v := v) (R0 := R0) hv_supp hR0 hv hvrad hv1 h
      (M := M) hM (ℓ := ℓ) (d := d) hℓ hd hR hRχ u hvol (Φ := Φ) hΦm (Cb := Cb) hΦb
      (s := i) (t := j) hij).2
  have hsplit : ∀ i j : Fin N, i ≠ j →
      (∫ x in Submission.BoseGases.abox N ℓ,
        ((Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxQInd V A j Φ) x)
            + (Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxQInd V A i Φ) x))
          * (Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Φ) x)
          * W (x i) (x j))
      = ixPP V ℓ A W Φ i j + ixQP V ℓ A W Φ i j := by
    intro i j hij
    have hpt : (fun x : Submission.BoseGases.X N =>
        ((Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxQInd V A j Φ) x)
            + (Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxQInd V A i Φ) x))
          * (Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Φ) x)
          * W (x i) (x j))
        = fun x => (Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxQInd V A j Φ) x)
              * (Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Φ) x)
              * W (x i) (x j)
            + (Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxQInd V A i Φ) x)
              * (Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Φ) x)
              * W (x i) (x j) := by
      funext x; ring
    rw [hpt, MeasureTheory.integral_add (hE1 i j hij) (hE2 i j hij)]
    simp only [ixPP, ixQP]
  have hF2 : Work.BoseFixB1.boxCrossPart V ℓ A W Φ
      = (∑ i : Fin N, ∑ j : Fin N, (if i ≠ j then ixPP V ℓ A W Φ i j else 0))
        + (∑ i : Fin N, ∑ j : Fin N, (if i ≠ j then ixQP V ℓ A W Φ i j else 0)) := by
    have h1 : Work.BoseFixB1.boxCrossPart V ℓ A W Φ
        = ∑ i : Fin N, ∑ j : Fin N,
            (if i ≠ j then ∫ x in Submission.BoseGases.abox N ℓ,
              ((Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxQInd V A j Φ) x)
                  + (Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxQInd V A i Φ) x))
                * (Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Φ) x)
                * W (x i) (x j)
              else 0) := boxCrossPart_doubleSum V ℓ A W Φ
    have h2 : (∑ i : Fin N, ∑ j : Fin N,
            (if i ≠ j then ∫ x in Submission.BoseGases.abox N ℓ,
              ((Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxQInd V A j Φ) x)
                  + (Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxQInd V A i Φ) x))
                * (Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Φ) x)
                * W (x i) (x j)
              else 0))
        = ∑ i : Fin N, ∑ j : Fin N,
            (if i ≠ j then ixPP V ℓ A W Φ i j + ixQP V ℓ A W Φ i j else 0) := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      split_ifs with hij
      · exact hsplit i j hij
      · ring
    have h3 : (∑ i : Fin N, ∑ j : Fin N,
            (if i ≠ j then ixPP V ℓ A W Φ i j + ixQP V ℓ A W Φ i j else 0))
        = (∑ i : Fin N, ∑ j : Fin N, (if i ≠ j then ixPP V ℓ A W Φ i j else 0))
          + (∑ i : Fin N, ∑ j : Fin N, (if i ≠ j then ixQP V ℓ A W Φ i j else 0)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      split_ifs with hij
      · ring
      · ring
    exact h1.trans (h2.trans h3)
  -- ## (C) the collapse: each pair term equals `V⁻¹` times the sandwich term
  have hXapp : ∀ i j : Fin N, i ≠ j → ixPP V ℓ A W Φ i j = V⁻¹ * ixZ V ℓ A fib Φ j i := by
    intro i j hij
    simp only [ixPP, ixZ]
    rw [hpeel (s := i) (t := j) hij, hrepl (s := i) (t := j) hij]
  have hYapp : ∀ i j : Fin N, i ≠ j → ixQP V ℓ A W Φ i j = V⁻¹ * ixZ V ℓ A fib Φ i j := by
    intro i j hij
    simp only [ixQP, ixZ]
    have hpt : (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxQInd V A i Φ) x)
          * (Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Φ) x)
          * W (x i) (x j))
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)]
        fun x => (Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxQInd V A i Φ) x)
            * (Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x)
            * W (x j) (x i) := by
      filter_upwards [MeasureTheory.ae_restrict_mem (Submission.BoseGases.abox_measurable N ℓ)]
        with x hx
      have hcomm := Work.BoseFixB1S.boxPInd_boxPInd_comm_good (N := N) hℓ hVpos hAmeas hVeq'
        hAc hij hGood x hx
      rw [← hcomm, hWsym (x i) (x j)]
    rw [MeasureTheory.integral_congr_ae hpt, hpeel (s := j) (t := i) hij.symm,
      hrepl (s := j) (t := i) hij.symm]
  have hX : (∑ i : Fin N, ∑ j : Fin N, (if i ≠ j then ixPP V ℓ A W Φ i j else 0))
      = V⁻¹ * (∑ i : Fin N, ∑ j : Fin N, (if j ≠ i then ixZ V ℓ A fib Φ i j else 0)) := by
    have h1 : (∑ i : Fin N, ∑ j : Fin N, (if i ≠ j then ixPP V ℓ A W Φ i j else 0))
        = ∑ i : Fin N, ∑ j : Fin N,
            (if i ≠ j then V⁻¹ * ixZ V ℓ A fib Φ j i else 0) := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      split_ifs with hij
      · exact hXapp i j hij
      · ring
    have h2 : (∑ i : Fin N, ∑ j : Fin N, (if i ≠ j then V⁻¹ * ixZ V ℓ A fib Φ j i else 0))
        = V⁻¹ * (∑ i : Fin N, ∑ j : Fin N,
            (if i ≠ j then ixZ V ℓ A fib Φ j i else 0)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      split_ifs with hij
      · ring
      · ring
    have h3 : (∑ i : Fin N, ∑ j : Fin N, (if i ≠ j then ixZ V ℓ A fib Φ j i else 0))
        = ∑ i : Fin N, ∑ j : Fin N, (if j ≠ i then ixZ V ℓ A fib Φ i j else 0) := by
      rw [Finset.sum_comm]
    exact h1.trans (h2.trans (by rw [h3]))
  have hY : (∑ i : Fin N, ∑ j : Fin N, (if i ≠ j then ixQP V ℓ A W Φ i j else 0))
      = V⁻¹ * (∑ i : Fin N, ∑ j : Fin N, (if j ≠ i then ixZ V ℓ A fib Φ i j else 0)) := by
    have h1 : (∑ i : Fin N, ∑ j : Fin N, (if i ≠ j then ixQP V ℓ A W Φ i j else 0))
        = ∑ i : Fin N, ∑ j : Fin N,
            (if i ≠ j then V⁻¹ * ixZ V ℓ A fib Φ i j else 0) := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      split_ifs with hij
      · exact hYapp i j hij
      · ring
    have h2 : (∑ i : Fin N, ∑ j : Fin N, (if i ≠ j then V⁻¹ * ixZ V ℓ A fib Φ i j else 0))
        = V⁻¹ * (∑ i : Fin N, ∑ j : Fin N,
            (if i ≠ j then ixZ V ℓ A fib Φ i j else 0)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      split_ifs with hij
      · ring
      · ring
    have h3 : (∑ i : Fin N, ∑ j : Fin N, (if i ≠ j then ixZ V ℓ A fib Φ i j else 0))
        = ∑ i : Fin N, ∑ j : Fin N, (if j ≠ i then ixZ V ℓ A fib Φ i j else 0) := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      by_cases hij : i ≠ j
      · have hji : j ≠ i := fun hh => hij hh.symm
        rw [if_pos hij, if_pos hji]
      · have hji : ¬ (j ≠ i) := fun hh => hij hh.symm
        rw [if_neg hij, if_neg hji]
    exact h1.trans (h2.trans (by rw [h3]))
  have hF : Work.BoseFixB1.boxCrossPart V ℓ A W Φ
      = 2 * V⁻¹ * (∑ i : Fin N, ∑ j : Fin N, (if j ≠ i then ixZ V ℓ A fib Φ i j else 0)) := by
    rw [hF2, hX, hY]
    ring
  -- ## (D) the `μ`-line split, summed over the slots
  have hD : ∀ i : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
          * ((∑ j : Fin N, Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x)
              - (1 + μ * V) * Work.UBBInputs8.boxPInd V A i Φ x))
      = (∑ j : Fin N, (if j ≠ i then ixZ V ℓ A fib Φ i j else 0)) - μ * V * ixP V ℓ A fib Φ i := by
    intro i
    have h1 := boxMuLine_slot_split_g (N := N) (ℓ := ℓ) (V := V) (μ := μ) hℓ hVpos hAmeas hVeq
      hAc (fib := fib) hFm hCf hΦm hΦb i
    simpa only [ixZ, ixP] using h1
  have hCsum : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
          * ((∑ j : Fin N, Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x)
              - (1 + μ * V) * Work.UBBInputs8.boxPInd V A i Φ x))
      = (∑ i : Fin N, ∑ j : Fin N, (if j ≠ i then ixZ V ℓ A fib Φ i j else 0))
        - μ * V * (∑ i : Fin N, ixP V ℓ A fib Φ i) := by
    rw [Finset.sum_congr rfl (fun i _ => hD i), Finset.sum_sub_distrib, Finset.mul_sum]
  have hS2 : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
          * (Work.UBBInputs8.boxPInd V A i Φ x))
      = ∑ i : Fin N, ixP V ℓ A fib Φ i := rfl
  rw [hF, hS2, hCsum, div_eq_mul_inv]
  have hkey : ∀ (S P : ℝ), (2 * V⁻¹) * (S - μ * V * P) = 2 * V⁻¹ * S - 2 * μ * P := by
    intro S P
    rw [show (2 * V⁻¹) * (S - μ * V * P) = 2 * V⁻¹ * S - 2 * μ * (V⁻¹ * V) * P by ring,
      inv_mul_cancel₀ hVne]
    ring
  rw [hkey]

end Work.BoseFixB1.SectorAux

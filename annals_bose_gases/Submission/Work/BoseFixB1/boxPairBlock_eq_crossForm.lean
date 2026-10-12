import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1.boxPairBlock_pointwise
import Submission.Work.BoseFixB1.integrableOn_crossForm_pieces
import Submission.Work.BoseFixB1.sum_pairSq_w2_eq
import Submission.Work.BoseFixB1S.a0A2QPaymentB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.boxPairBlock_eq_crossForm`

The block-level cross form of the box-projected pair word: with
`A = dlBox ℓ d u`, `V = |A| = boxMass ℓ d u`, `P_i = boxPInd V A i`, `Q_i = boxQInd V A i`
(FS's box projections `P_B = |B|⁻¹⟨1_B,·⟩1_B`, `Q_B = 1_B − P_B`), `w = wSmallPair M ℓ d u v`,
`w₁ = wSmall1Pair h M ℓ d u = w(1−ω)`, `w₂ = wSmallPair M ℓ d u (g₂) = w(1−ω²)` and
`X_p := 1_A(x_{p.1})·(1_A(x_{p.2})·Φ x)`, the two-orientation pair block
`(D + s + ωB)²w + 2(1−ω)sBw` (`D = Q_qQ_pΦ`, `s = P_pQ_qΦ + P_qQ_pΦ`, `B = P_pP_qΦ`)
satisfies, pointwise on `abox N ℓ`,

    boxPairBlock = X_p²·w − B²·w₂ − 2·D·B·w₁ ,

which is `(D+s+ωB)² + 2(1−ω)sB = (D+s+B)² − (1−ω²)B² − 2(1−ω)DB` combined with the slot
algebra `D + s + B = 1_A(x_p)·1_A(x_q)·Φ x`.  Summing over the unordered pairs and using the
two-slot value identity `Q0C.pair_value` for the `w₂`-term gives the statement below.

The three ingredients are the delegated lemmas `boxPairBlock_pointwise`,
`integrableOn_crossForm_pieces` and `sum_pairSq_w2_eq`; the assembly is here.
-/

namespace Work.BoseFixB1

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

theorem boxPairBlock_eq_crossForm {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ}
    (hΦc : Continuous Φ) :
    (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          Work.BoseFixB1S.boxPairBlock (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmallPair M ℓ d u v)
            (Submission.BoseGases.omC (Classical.choose h)) Φ p x)
      = (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
          ∫ x in Submission.BoseGases.abox N ℓ,
            (((Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x p.1))
              * ((Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x)) ^ 2
              * (Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)))
        - (1 / 2) * (Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
            / (Work.SmallBoxSliding.boxMass ℓ d u) ^ 2)
            * Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                (Submission.BoseGases.dlBox ℓ d u) Φ
        - (∑ p ∈ Submission.BoseGases.pairSet N,
            ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) p.2
                  (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) p.1 Φ) x)
              * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) p.1
                  (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x)
              * (Submission.BoseGases.wSmall1Pair h M ℓ d u (x p.1) (x p.2))) := by
  classical
  have hbb : Work.BoseFixB1S.boxPairBlock = Work.BoseFixB1.pairBlock := rfl
  rw [hbb]
  classical
  let Xf : Fin N × Fin N → Submission.BoseGases.X N → ℝ := fun p x =>
    ((Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x p.1)
        * ((Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x)) ^ 2
      * (Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2))
  let Yf : Fin N × Fin N → Submission.BoseGases.X N → ℝ := fun p x =>
    (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) p.1
        (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x) ^ 2
      * (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) (x p.1) (x p.2))
  let Zf : Fin N × Fin N → Submission.BoseGases.X N → ℝ := fun p x =>
    (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) p.2
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) p.1 Φ) x)
      * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) p.1
          (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x)
      * (Submission.BoseGases.wSmall1Pair h M ℓ d u (x p.1) (x p.2))
  by_cases hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u
  · -- =============== main branch: |B(u)| > 0 ===============
    have hpt : ∀ p ∈ Submission.BoseGases.pairSet N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
        pairBlock (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u v)
          (Submission.BoseGases.omC (Classical.choose h)) Φ p x = Xf p x - Yf p x - 2 * Zf p x := by
      intro p hp x hx
      simpa only [Xf, Yf, Zf] using
        boxPairBlock_pointwise (v := v) h (ℓ := ℓ) (d := d) hℓ u hvol (Φ := Φ) hΦc hp hx
    have hint : ∀ p ∈ Submission.BoseGases.pairSet N,
        IntegrableOn (Xf p) (Submission.BoseGases.abox N ℓ) volume
        ∧ IntegrableOn (Yf p) (Submission.BoseGases.abox N ℓ) volume
        ∧ IntegrableOn (Zf p) (Submission.BoseGases.abox N ℓ) volume := by
      intro p hp
      simpa only [Xf, Yf, Zf] using
        integrableOn_crossForm_pieces (v := v) (R0 := R0) hv_supp hR0 hv hvrad hv1 h
          hM hℓ hd hR hRχ u hvol (Φ := Φ) hΦc (p := p) hp
    have hper : ∀ p ∈ Submission.BoseGases.pairSet N,
        (∫ x in Submission.BoseGases.abox N ℓ,
            pairBlock (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmallPair M ℓ d u v)
              (Submission.BoseGases.omC (Classical.choose h)) Φ p x)
          = (∫ x in Submission.BoseGases.abox N ℓ, Xf p x)
            - (∫ x in Submission.BoseGases.abox N ℓ, Yf p x)
            - 2 * (∫ x in Submission.BoseGases.abox N ℓ, Zf p x) := by
      intro p hp
      have h1 : (∫ x in Submission.BoseGases.abox N ℓ,
            pairBlock (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmallPair M ℓ d u v)
              (Submission.BoseGases.omC (Classical.choose h)) Φ p x)
          = ∫ x in Submission.BoseGases.abox N ℓ, (Xf p x - Yf p x - 2 * Zf p x) :=
        setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ) (hpt p hp)
      obtain ⟨hXi, hYi, hZi⟩ := hint p hp
      have hXi' : IntegrableOn (fun x => Xf p x - Yf p x) (Submission.BoseGases.abox N ℓ) volume :=
        hXi.sub hYi
      have hZi' : IntegrableOn (fun x => 2 * Zf p x) (Submission.BoseGases.abox N ℓ) volume :=
        hZi.const_mul 2
      have hs1 : (∫ x in Submission.BoseGases.abox N ℓ, Xf p x - Yf p x - 2 * Zf p x)
          = (∫ x in Submission.BoseGases.abox N ℓ, Xf p x - Yf p x)
            - (∫ x in Submission.BoseGases.abox N ℓ, 2 * Zf p x) :=
        MeasureTheory.integral_sub (f := fun x => Xf p x - Yf p x) (g := fun x => 2 * Zf p x)
          hXi' hZi'
      have hs2 : (∫ x in Submission.BoseGases.abox N ℓ, Xf p x - Yf p x)
          = (∫ x in Submission.BoseGases.abox N ℓ, Xf p x)
            - (∫ x in Submission.BoseGases.abox N ℓ, Yf p x) :=
        MeasureTheory.integral_sub (f := fun x => Xf p x) (g := fun x => Yf p x) hXi hYi
      have hs3 : (∫ x in Submission.BoseGases.abox N ℓ, 2 * Zf p x)
          = 2 * (∫ x in Submission.BoseGases.abox N ℓ, Zf p x) :=
        MeasureTheory.integral_const_mul 2 (fun x => Zf p x)
      rw [h1, hs1, hs2, hs3]
    have hsum1 : (∑ p ∈ Submission.BoseGases.pairSet N,
          ∫ x in Submission.BoseGases.abox N ℓ,
            pairBlock (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmallPair M ℓ d u v)
              (Submission.BoseGases.omC (Classical.choose h)) Φ p x)
        = (∑ p ∈ Submission.BoseGases.pairSet N,
              ∫ x in Submission.BoseGases.abox N ℓ, Xf p x)
          - (∑ p ∈ Submission.BoseGases.pairSet N,
              ∫ x in Submission.BoseGases.abox N ℓ, Yf p x)
          - 2 * (∑ p ∈ Submission.BoseGases.pairSet N,
              ∫ x in Submission.BoseGases.abox N ℓ, Zf p x) := by
      rw [Finset.sum_congr rfl hper]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hYsum : (∑ p ∈ Submission.BoseGases.pairSet N,
          ∫ x in Submission.BoseGases.abox N ℓ, Yf p x)
        = (Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
            / (Work.SmallBoxSliding.boxMass ℓ d u) ^ 2)
          * Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) Φ := by
      simpa only [Yf] using
        sum_pairSq_w2_eq (v := v) (R0 := R0) hv_supp hR0 hv hvrad hv1 h
          hM hℓ hd hR hRχ u hvol (Φ := Φ) hΦc
    rw [hsum1, hYsum]
    simp only [Xf, Zf]
    ring
  · -- =============== degenerate branch: |B(u)| = 0 ===============
    have hV0 : Work.SmallBoxSliding.boxMass ℓ d u = 0 := by
      refine le_antisymm (not_lt.mp hvol) ?_
      rw [Work.SmallBoxSliding.boxMass_eq_measureReal]
      exact MeasureTheory.measureReal_nonneg
    have hP0 : ∀ (i : Fin N) (Ψ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N),
        Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i Ψ x = 0 := by
      intro i Ψ x
      simp only [Work.UBBInputs8.boxPInd, hV0, div_zero, zero_mul]
    have hQ0 : ∀ (i : Fin N) (Ψ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N),
        Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Ψ x
          = (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i) * Ψ x := by
      intro i Ψ x
      simp only [Work.UBBInputs8.boxQInd, hP0 i Ψ x, sub_zero]
    have hpt0 : ∀ (p : Fin N × Fin N) (x : Submission.BoseGases.X N),
        pairBlock (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u v)
          (Submission.BoseGases.omC (Classical.choose h)) Φ p x = Xf p x := by
      intro p x
      simp only [pairBlock, Xf, hP0, hQ0]
      ring
    have hZ0 : ∀ (p : Fin N × Fin N) (x : Submission.BoseGases.X N), Zf p x = 0 := by
      intro p x
      simp only [Zf, hP0]
      ring
    have hL0 : (∑ p ∈ Submission.BoseGases.pairSet N,
          ∫ x in Submission.BoseGases.abox N ℓ,
            pairBlock (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmallPair M ℓ d u v)
              (Submission.BoseGases.omC (Classical.choose h)) Φ p x)
        = ∑ p ∈ Submission.BoseGases.pairSet N,
            ∫ x in Submission.BoseGases.abox N ℓ, Xf p x := by
      apply Finset.sum_congr rfl
      intro p hp
      exact setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
        (fun x hx => hpt0 p x)
    have hZint : (∑ p ∈ Submission.BoseGases.pairSet N,
          ∫ x in Submission.BoseGases.abox N ℓ, Zf p x) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      rw [setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
        (fun x hx => hZ0 p x)]
      simp
    have hM20 : (1 / 2) * (Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
          / (Work.SmallBoxSliding.boxMass ℓ d u) ^ 2)
        * Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u) Φ = 0 := by
      rw [hV0]
      simp
    simp only [Xf, Zf] at hL0 hZint ⊢
    rw [hL0, hZint, hM20]
    ring


end

end Work.BoseFixB1

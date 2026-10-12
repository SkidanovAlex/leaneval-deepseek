import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1.boxPairBlock_eq_crossForm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.boxPairManifestSumB1S` — the integrated σ-manifest identity

With `V = boxMass ℓ d u`, `A = dlBox ℓ d u`, `w = wSmallPair M ℓ d u v`,
`w₁ = wSmall1Pair h M ℓ d u`, `w₂ = wSmallPair M ℓ d u (g₂ v h)`, `ω = omC (choose h)`,
`Pᵢ = boxPInd V A i`, `Qᵢ = boxQInd V A i`, the target says

    boxSqPart V ℓ A w ω Φ + boxCrossPart V ℓ A w₁ Φ
      = ½·Σ_{p∈pairSet N}∫_{abox} (1_A(x_{p.1})·(1_A(x_{p.2})·Φ x))²·w(x_{p.1},x_{p.2})
        − Σ_{p∈pairSet N}∫_{abox} (P_{p.1}P_{p.2}Φ)·(Q_{p.2}Q_{p.1}Φ)·w₁(x_{p.1},x_{p.2})
        − ½·(M₂/V²)·boxPairCount ,

i.e. the manifest-square/cross split of the pair-block sum, with the pair-condensate term
`½Σ_p∫(P_{p.1}P_{p.2}Φ)²w₂ = ½(M₂/V²)·Pc` collapsed (the `w₂`-term is what the `σ`-manifest
square hides: `pairBlock = σ_p²w − 2·A_pD_p·w₁ − A_p²w₂`, `σ_p := 1_A(x_{p.1})·1_A(x_{p.2})`).

Assembly of three proved corpus lemmas (all with the target's own hypotheses):

* `Work.BoseFixB1.boxPairBlockIntegrable` — the per-pair `IntegrableOn` statements for
  `pairSq`, `pairCross`, `pairBlock` (needed to split the integrals);
* `Work.BoseFixB1.boxSqPart_add_boxCrossPart_eq_blockSum` —
  `boxSqPart + boxCrossPart = ½Σ_p∫pairBlock`;
* `Work.BoseFixB1.boxPairBlock_eq_crossForm` — the same pair-block sum rewritten in cross
  form, `½Σ_p∫σ_p²w − ½(M₂/V²)Pc − Σ_p∫(Q_{p.2}Q_{p.1}Φ)(P_{p.1}P_{p.2}Φ)w₁`, with
  `Work.BoseFixB1.sum_pairSq_w2_eq` collapsing the `w₂`-term.

The only mismatch between the two displayed cross sums is the order of the two factors
`P_{p.1}P_{p.2}Φ` and `Q_{p.2}Q_{p.1}Φ` inside each integrand, which is repaired pointwise by
commutativity of multiplication in `ℝ`.
-/

namespace Work.BoseFixB1S

theorem boxPairManifestSumB1S {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    Work.BoseFixB1.boxSqPart (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
        (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmallPair M ℓ d u v)
        (Submission.BoseGases.omC (Classical.choose h)) Φ
      + Work.BoseFixB1.boxCrossPart (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
        (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ
      = (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
            ∫ x in Submission.BoseGases.abox N ℓ,
              ((Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x p.1)
                  * ((Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x p.2)
                      * Φ x)) ^ 2
                * (Submission.BoseGases.wSmallPair M ℓ d u v) (x p.1) (x p.2))
        - (∑ p ∈ Submission.BoseGases.pairSet N,
            ∫ x in Submission.BoseGases.abox N ℓ,
              ((Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) p.1
                  (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x)
                * (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) p.2
                    (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                      (Submission.BoseGases.dlBox ℓ d u) p.1 Φ) x)
                * (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x p.1) (x p.2)))
        - (1 / 2) * (Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u)
                (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
              / (Work.SmallBoxSliding.boxMass ℓ d u) ^ 2)
            * Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                (Submission.BoseGases.dlBox ℓ d u) Φ := by
  classical
  -- ## The three per-pair integrability statements (at the target's own hypotheses).
  obtain ⟨hBlk, hSq, hCr⟩ :=
    Work.BoseFixB1.boxPairBlockIntegrable (v := v) (R0 := R0) (M := M) (ℓ := ℓ) (d := d)
      (N := N) (Φ := Φ) hv_supp hR0 hv hvrad hv1 h hM hℓ hd hR hRχ u hΦc
  -- ## The kernel relation `w₁ = w(1−ω)`.
  have hw1rel : ∀ a b : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.wSmall1Pair h M ℓ d u a b
        = Submission.BoseGases.wSmallPair M ℓ d u v a b
            * (1 - Submission.BoseGases.omC (Classical.choose h) a b) := by
    intro a b
    simpa only [Submission.BoseGases.omC] using
      Work.BoseFixB1.wSmall1Pair_eq_mul (v := v) h (M := M) (ℓ := ℓ) (d := d) u a b
  -- ## `boxSqPart + boxCrossPart = ½·Σ_p∫pairBlock`.
  have hsplit := Work.BoseFixB1.boxSqPart_add_boxCrossPart_eq_blockSum (N := N) (ℓ := ℓ)
    (volA := Work.SmallBoxSliding.boxMass ℓ d u) (A := Submission.BoseGases.dlBox ℓ d u)
    (w := Submission.BoseGases.wSmallPair M ℓ d u v)
    (w₁ := Submission.BoseGases.wSmall1Pair h M ℓ d u)
    (om := Submission.BoseGases.omC (Classical.choose h)) (Φ := Φ) hSq hCr hBlk hw1rel
  -- ## The same sum in cross form.
  have hcross := Work.BoseFixB1.boxPairBlock_eq_crossForm (v := v) (R0 := R0) (M := M)
    (ℓ := ℓ) (d := d) (N := N) (Φ := Φ) hv_supp hR0 hv hvrad hv1 h hM hℓ hd hR hRχ u hΦc
  -- `boxPairBlock` and `pairBlock` are the same function (definitionally).
  have hsum_eq : (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          Work.BoseFixB1S.boxPairBlock (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmallPair M ℓ d u v)
            (Submission.BoseGases.omC (Classical.choose h)) Φ p x)
      = (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          Work.BoseFixB1.pairBlock (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmallPair M ℓ d u v)
            (Submission.BoseGases.omC (Classical.choose h)) Φ p x) := rfl
  -- ## The two orientations of the cross sum agree (the factors are commuted inside).
  have hZ : (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) p.1
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x)
            * (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.2
                (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) p.1 Φ) x)
            * (Submission.BoseGases.wSmall1Pair h M ℓ d u (x p.1) (x p.2)))
      = (∑ p ∈ Submission.BoseGases.pairSet N,
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
    refine Finset.sum_congr rfl (fun p _ => ?_)
    exact MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
      (fun x _ => by ring)
  rw [hsum_eq] at hcross
  rw [← hsplit, hZ]
  linarith [hcross]

end Work.BoseFixB1S

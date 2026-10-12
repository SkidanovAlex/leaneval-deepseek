import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1S_boxQCount_eq_sum_compT
import Submission.Work.BoseFixB1.SectorAux.boxCompTOrthMeas
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.SectorAux.goodBoxQCount_eq_sum_compT`

The spectral form of the mean-free (excited) box count

    boxQCount volA ℓ A Φ = ∑ᵢ ∫_{abox N ℓ} (QᵢΦ)² ,   Qᵢ = UBBInputs8.boxQInd volA A i

in the state class `GoodState ℓ Φ := Measurable Φ ∧ (bounded on the box)` — the weaker hypothesis
under which the corpus states its structural facts (all the continuity hypotheses of
`Work.BoseFixB1S.boxQCount_eq_sum_compT` are used only to manufacture a `GoodState`).  The claim is

    ∑ᵢ ∫_{abox} (QᵢΦ)² = Σ_{(S,T), S ⊥ T} |T| · ∫_{abox} (ψ_{S,T})² ,

where `ψ_{S,T} = boxCompT volA A S T Φ = (∏_{i∈S}Pᵢ)(∏_{j∈T}Qⱼ)(∏_{k∉S∪T}Rₖ)Φ` is the joint
component of the commuting family of FS box projections (`Pᵢ, Qᵢ, Rᵢ = 1 − 1_A(xᵢ)`), and
`|T|` is the eigenvalue of `n₊ = ΣⱼQⱼ` on the range of `ψ_{S,T}`.

## Proof (the same three steps as in the sibling `Continuous`-version)

* **Component decomposition of `QᵢΦ`** — on the box, `Φ = Σ_p ψ_p`
  (`Work.BoseFixB1S.boxCompT_sum_eq`, which is a *pointwise* identity valid for every `Φ`),
  `Qᵢ` reads its argument only through the box values (`agreeBox_boxQInd`), is additive over finite
  sums (`boxQInd_finset_sum_gen`) and acts on `ψ_p` by the eigenvalue `[i ∈ p.2]`
  (`boxQInd_boxCompT`, restated here as `qBoxQInd_boxCompT_good` for `GoodState`s).  Hence
  `QᵢΦ = Σ_{p ∋ i} ψ_p` on the box.
* **Pythagoras** for the pairwise orthogonal components (`boxCompT_orth`, restated for
  `GoodState`s in the companion module `SectorAux.boxCompTOrthMeas` as `boxCompT_orth_good`):
  the cross terms vanish, leaving `qIntegral_sum_compT_sq_good`.
* **Cardinality count**: exchanging the two finite sums turns `[i ∈ p.2]` into `|p.2|`
  (`Work.BoseFixB1S.sum_i_sum_filter_card_mul`).

All integrability side conditions come from `GoodState` (measurable + box-bounded) via
`slotInt_of_bound` and `integrableOn_mul_of_bound`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1.SectorAux

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. The pointwise resolution of the identity (no hypothesis on `Φ`) -/

/-- `Σ_{(S,T), S ⊥ T} boxCompT volA A S T Φ x = Φ x`: the three-way joint components resolve the
identity **pointwise**, with no hypothesis on `Φ` (the sibling
`Work.BoseFixB1S.boxCompT_sum_eq` carries a continuity hypothesis that it never uses). -/
theorem qBoxCompT_sum_eq_pt {N : ℕ} (volA : ℝ) (A : Set E3)
    (Φ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) :
    (∑ p ∈ Work.BoseFixB1S.qPairSet N,
        Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) = Φ x := by
  have hlit : (∑ p ∈ (Finset.univ :
        Finset (Finset (Fin N) × Finset (Fin N))).filter (fun p => Disjoint p.1 p.2),
        Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ) = Φ := by
    calc (∑ p ∈ (Finset.univ :
            Finset (Finset (Fin N) × Finset (Fin N))).filter (fun p => Disjoint p.1 p.2),
            Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ)
        = ∑ p ∈ (Finset.univ :
              Finset (Finset (Fin N) × Finset (Fin N))).filter (fun p => Disjoint p.1 p.2),
            (List.finRange N).foldl (fun g i => Work.BoseFixB1S.boxPatOp volA A i
              (if i ∈ p.1 then 0 else if i ∈ p.2 then 1 else 2) g) Φ :=
          Finset.sum_congr rfl (fun p _ => Work.BoseFixB1S.boxCompT_eq_foldl volA A p.1 p.2 Φ)
      _ = ∑ c : Fin N → Fin 3, (List.finRange N).foldl (fun g i =>
            Work.BoseFixB1S.boxPatOp volA A i (c i) g) Φ :=
          Work.BoseFixB1S.sumFilterDisjointFin3 (fun c => (List.finRange N).foldl (fun g i =>
            Work.BoseFixB1S.boxPatOp volA A i (c i) g) Φ)
      _ = Φ := Work.BoseFixB1S.sumFoldFinRangeTriple
          (fun i b g => Work.BoseFixB1S.boxPatOp volA A i b g)
          (fun i Ψ => Work.BoseFixB1S.boxPatOp_sum volA A i Ψ) Φ
  have hsum : (∑ p ∈ Work.BoseFixB1S.qPairSet N,
        Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ) = Φ := by
    simpa only [Work.BoseFixB1S.qPairSet] using hlit
  simpa [Finset.sum_apply] using congr_fun hsum x

/-! ## 2. The `Q`-eigenvalue rule on the joint components, for `GoodState`s -/

/-- `Work.BoseFixB1S.boxQInd_boxCompT` with the continuity hypothesis weakened to `GoodState`:
on the box, `Qⱼ (boxCompT volA A S T Φ) = [j ∈ T] · boxCompT volA A S T Φ`. -/
theorem qBoxQInd_boxCompT_good {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {S T : Finset (Fin N)} (hST : Disjoint S T)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦg : Work.BoseFixB1S.GoodState ℓ Φ) (j : Fin N) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxQInd volA A j (Work.BoseFixB1S.boxCompT volA A S T Φ) x
        = (if j ∈ T then Work.BoseFixB1S.boxCompT volA A S T Φ x else 0) := by
  intro x hx
  obtain ⟨hC, _⟩ :=
    Work.BoseFixB1S.boxCompTAux_indQ hℓ hvol hA hvolA hAc S T hST j
      (List.finRange N) (List.nodup_finRange N)
  have hres := hC (List.mem_finRange j) Φ hΦg x hx
  rw [Work.BoseFixB1S.boxCompT_eq_aux]
  exact hres

/-! ## 3. Pythagoras for the orthogonal joint components, for `GoodState`s -/

/-- `Work.BoseFixB1S.integral_sum_compT_sq` with continuity replaced by `GoodState`: for a family
of disjoint pairs, the squared box-`L²`-norm of the sum of the joint components is the sum of the
squared norms (the cross terms vanish by `boxCompT_orth_good`). -/
theorem qIntegral_sum_compT_sq_good {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) {Φ : X N → ℝ} (hΦg : Work.BoseFixB1S.GoodState ℓ Φ)
    (s : Finset (Finset (Fin N) × Finset (Fin N))) (hs : ∀ p ∈ s, Disjoint p.1 p.2) :
    (∫ x in abox N ℓ, (∑ p ∈ s, Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2)
      = ∑ p ∈ s, ∫ x in abox N ℓ,
          (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 := by
  have hG : ∀ p : Finset (Fin N) × Finset (Fin N),
      Work.BoseFixB1S.GoodState ℓ (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ) :=
    fun p => Work.BoseFixB1S.goodState_boxCompT hℓ hvol hA hvolA hAc p.1 p.2 hΦg
  -- the pairwise products of components are integrable on the box
  have hprod : ∀ p ∈ s, ∀ q ∈ s,
      IntegrableOn (fun x => Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
        * Work.BoseFixB1S.boxCompT volA A q.1 q.2 Φ x) (abox N ℓ) volume := by
    intro p _ q _
    obtain ⟨Cf, hCf⟩ := (hG p).2
    obtain ⟨Cg, hCg⟩ := (hG q).2
    exact Work.BoseFixB1S.integrableOn_mul_of_bound hℓ (hG p).1 (hG q).1 hCf hCg
  -- the pointwise expansion of the square into the double sum
  have hpt : ∀ x : X N,
      (∑ p ∈ s, Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2
        = ∑ p ∈ s, ∑ q ∈ s,
            Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
              * Work.BoseFixB1S.boxCompT volA A q.1 q.2 Φ x := by
    intro x
    rw [sq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.mul_sum]
  calc (∫ x in abox N ℓ, (∑ p ∈ s, Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2)
      = ∫ x in abox N ℓ, ∑ p ∈ s, ∑ q ∈ s,
          Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
            * Work.BoseFixB1S.boxCompT volA A q.1 q.2 Φ x :=
        setIntegral_congr_fun (abox_measurable N ℓ) (fun x _ => hpt x)
    _ = ∑ p ∈ s, ∫ x in abox N ℓ, ∑ q ∈ s,
          Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
            * Work.BoseFixB1S.boxCompT volA A q.1 q.2 Φ x :=
        MeasureTheory.integral_finsetSum s
          (f := fun p x => ∑ q ∈ s, Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
            * Work.BoseFixB1S.boxCompT volA A q.1 q.2 Φ x)
          (fun p hp => integrable_finsetSum
            (μ := (volume : Measure (X N)).restrict (abox N ℓ)) s
            (f := fun q x => Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
              * Work.BoseFixB1S.boxCompT volA A q.1 q.2 Φ x)
            (fun q hq => hprod p hp q hq))
    _ = ∑ p ∈ s, ∑ q ∈ s,
          ∫ x in abox N ℓ, Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
            * Work.BoseFixB1S.boxCompT volA A q.1 q.2 Φ x := by
        apply Finset.sum_congr rfl
        intro p hp
        exact MeasureTheory.integral_finsetSum s
          (f := fun q x => Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
            * Work.BoseFixB1S.boxCompT volA A q.1 q.2 Φ x)
          (fun q hq => hprod p hp q hq)
    _ = ∑ p ∈ s, ∫ x in abox N ℓ,
          (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.sum_eq_single p]
        · apply integral_congr_ae
          filter_upwards with x
          ring
        · intro q hq hqp
          exact boxCompT_orth_good hℓ hvol hA hvolA hAc (hs p hp) (hs q hq)
            (Work.BoseFixB1S.ne_fst_or_ne_snd hqp.symm) hΦg hΦg
        · intro hpn
          exact absurd hp hpn

/-! ## 4. The spectral form of the mean-free count -/

theorem goodBoxQCount_eq_sum_compT {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦg : Work.BoseFixB1S.GoodState ℓ Φ) :
    Work.BoseFixB1S.boxQCount volA ℓ A Φ
      = ∑ p ∈ (Finset.univ : Finset (Finset (Fin N) × Finset (Fin N))).filter
            (fun p => Disjoint p.1 p.2),
          (p.2.card : ℝ)
            * ∫ x in Submission.BoseGases.abox N ℓ,
                (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 := by
  have hG : ∀ p : Finset (Fin N) × Finset (Fin N),
      Work.BoseFixB1S.GoodState ℓ (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ) :=
    fun p => Work.BoseFixB1S.goodState_boxCompT hℓ hvol hA hvolA hAc p.1 p.2 hΦg
  have master : Work.BoseFixB1S.boxQCount volA ℓ A Φ
      = ∑ p ∈ Work.BoseFixB1S.qPairSet N, (p.2.card : ℝ)
          * ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 := by
    -- the pointwise component decomposition of `QᵢΦ` on the box
    have hQdecomp : ∀ i : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxQInd volA A i Φ x
          = ∑ p ∈ (Work.BoseFixB1S.qPairSet N).filter (fun p => i ∈ p.2),
              Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x := by
      intro i x hx
      have hsum : ∀ y ∈ Submission.BoseGases.abox N ℓ,
          Φ y = ∑ p ∈ Work.BoseFixB1S.qPairSet N,
            Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ y :=
        fun y _ => (qBoxCompT_sum_eq_pt volA A Φ y).symm
      have h1 : Work.UBBInputs8.boxQInd volA A i Φ x
          = Work.UBBInputs8.boxQInd volA A i
              (fun y => ∑ p ∈ Work.BoseFixB1S.qPairSet N,
                Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ y) x :=
        Work.BoseFixB1S.agreeBox_boxQInd hA hAc i hsum x hx
      have h2 : Work.UBBInputs8.boxQInd volA A i
            (fun y => ∑ p ∈ Work.BoseFixB1S.qPairSet N,
              Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ y) x
          = ∑ p ∈ Work.BoseFixB1S.qPairSet N,
              Work.UBBInputs8.boxQInd volA A i
                (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ) x :=
        Work.BoseFixB1S.boxQInd_finset_sum_gen volA A i x (Work.BoseFixB1S.qPairSet N)
          (fun p => Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ)
          (fun p _ => Work.BoseFixB1S.slotInt_of_bound hℓ hA hAc i x hx
            (hG p).1 (hG p).2.choose_spec)
      have h3 : (∑ p ∈ Work.BoseFixB1S.qPairSet N,
            Work.UBBInputs8.boxQInd volA A i
              (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ) x)
          = ∑ p ∈ (Work.BoseFixB1S.qPairSet N).filter (fun p => i ∈ p.2),
              Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro p hp
        exact qBoxQInd_boxCompT_good hℓ hvol hA hvolA hAc
          (Work.BoseFixB1S.mem_qPairSet.mp hp) hΦg i x hx
      rw [h1, h2, h3]
    -- Pythagoras for each slot
    have hstep : ∀ i : Fin N,
        (∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
          = ∑ p ∈ (Work.BoseFixB1S.qPairSet N).filter (fun p => i ∈ p.2),
              ∫ x in abox N ℓ,
                (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 := by
      intro i
      calc (∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
          = ∫ x in abox N ℓ,
              (∑ p ∈ (Work.BoseFixB1S.qPairSet N).filter (fun p => i ∈ p.2),
                Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 :=
            setIntegral_congr_fun (abox_measurable N ℓ)
              (fun x hx => by rw [hQdecomp i x hx])
        _ = ∑ p ∈ (Work.BoseFixB1S.qPairSet N).filter (fun p => i ∈ p.2),
              ∫ x in abox N ℓ,
                (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 :=
            qIntegral_sum_compT_sq_good hℓ hvol hA hvolA hAc hΦg _
              (fun p hp => Work.BoseFixB1S.mem_qPairSet.mp (Finset.mem_filter.mp hp).1)
    rw [Work.BoseFixB1S.boxQCount]
    calc (∑ i : Fin N, ∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
        = ∑ i : Fin N, ∑ p ∈ (Work.BoseFixB1S.qPairSet N).filter (fun p => i ∈ p.2),
            ∫ x in abox N ℓ, (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 :=
          Finset.sum_congr rfl (fun i _ => hstep i)
      _ = ∑ p ∈ Work.BoseFixB1S.qPairSet N, (p.2.card : ℝ)
            * ∫ x in abox N ℓ,
                (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 :=
          Work.BoseFixB1S.sum_i_sum_filter_card_mul (Work.BoseFixB1S.qPairSet N)
            (fun p => ∫ x in abox N ℓ,
              (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2)
  simpa only [Work.BoseFixB1S.qPairSet] using master

end Work.BoseFixB1.SectorAux

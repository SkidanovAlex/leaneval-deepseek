import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1B.setIntegral_abox_mul_prod_indicator
import Submission.Work.BoseFixB1S.BoxQWords
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.pairKernel_flatIntegralCone`

A **cone-compatible** proof of the flat pair-kernel integral identity

  `∫_{abox n ℓ} (∏ᵢ 1_A(xᵢ)) · (½ Σ_{p ∈ pairSet n} w (x_{p.1}) (x_{p.2}))
      = (n(n−1)/2) · (vol A)^{n−2} · ∫_{A × A} w`

for `A ⊆ acube ℓ` measurable and a pair kernel `w` bounded by `D` and a.e. strongly
measurable on `A × A`.

The statement is byte-identical to `Work.BoseB1Cube.pairKernel_flatIntegral`, whose proof
however imports `BoseFixB1S.FlatQLHS.{flatPairSumValue, weightedPairSlotIntegrable}` and
therefore lands in the **`boxConstCalibB1`** cone — incompatible with the `boxPairValue` cone
of the dense band arm (`Work.BoseB1Cube.chiSquarePeelYoung`), with which this twin must
coexist (the two modules declare `Work.BoseFixB1S.pairMass_eq_setIntegral` twice).

So everything is proved here directly from `hwm` + `hwD` and Mathlib, the only corpus input
being the measure-theoretic bookkeeping lemma
`Work.BoseFixB1B.setIntegral_abox_mul_prod_indicator` (itself cone-inert).  The two
measure-theoretic ingredients are re-proved locally (marked `private`, so they cannot clash
with the sibling module's copies):

* `cone_integral_pi_pair_peel` — the two-slot peel of an arbitrary product measure
  `Measure.pi (fun _ ↦ μ)`, by induction on the number of untouched coordinates
  (`measurePreserving_piFinSuccAbove`, `MeasurableEquiv.finTwoArrow`);
* `cone_pairSlotPiIntegrable` — the corresponding integrability, by the same induction.

The mathematical content: `pairSet n = {p : Fin n × Fin n | p.1 ≠ p.2}` is the set of
*ordered* off-diagonal pairs, of cardinality `n(n−1)`; every one of them contributes
`(vol A)^{n−2} ∫_{A×A} w`, and the outer `½` combines with the `n(n−1)` ordered pairs into the
factor `n(n−1)/2` of the right-hand side.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseB1Cube

set_option autoImplicit false
set_option maxHeartbeats 1000000
-- the statement carries `hℓ : 0 < ℓ` and `hV : 0 < V`, which the identity does not use
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 0. Index bookkeeping for `pairSet` -/

/-- Two distinct indices of `Fin N` force `2 ≤ N`. -/
private lemma cone_two_le_of_ne_fin {N : ℕ} {i j : Fin N} (hij : i ≠ j) : 2 ≤ N := by
  by_contra h
  refine hij (Fin.ext ?_)
  have hi := i.isLt
  have hj := j.isLt
  omega

/-- `Submission.BoseGases.pairSet N` is the off-diagonal of `Finset.univ`. -/
private lemma cone_card_pairSet_nat (N : ℕ) :
    (Submission.BoseGases.pairSet N).card = N * (N - 1) := by
  have h : Submission.BoseGases.pairSet N = (Finset.univ : Finset (Fin N)).offDiag := by
    ext p
    simp [Submission.BoseGases.pairSet, Finset.mem_offDiag]
  rw [h, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
  exact (Nat.mul_sub_one N N).symm

/-- The cardinality of `pairSet N`, as a real number. -/
private lemma cone_card_pairSet_cast (N : ℕ) :
    ((Submission.BoseGases.pairSet N).card : ℝ) = (N : ℝ) * ((N : ℝ) - 1) := by
  rw [cone_card_pairSet_nat]
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · rw [Nat.cast_mul, Nat.cast_sub h, Nat.cast_one]

/-- The centred cube has finite volume for *every* side length `ℓ`. -/
private lemma cone_acube_volume_ne_top (ℓ : ℝ) :
    (MeasureTheory.volume : MeasureTheory.Measure E3) (Submission.BoseGases.acube ℓ) ≠ ⊤ := by
  by_cases hℓ : 0 ≤ ℓ
  · rw [Submission.BoseGases.acube_volume ℓ hℓ]
    exact ENNReal.ofReal_lt_top.ne
  · have hneg : ℓ < 0 := lt_of_not_ge hℓ
    have hemp : Submission.BoseGases.acube ℓ = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro y hy
      have h0 := (Submission.BoseGases.mem_acube_iff ℓ y).mp hy 0
      simp only [Set.mem_Icc] at h0
      linarith [h0.1, h0.2, hneg]
    rw [hemp, MeasureTheory.measure_empty]
    exact ENNReal.zero_ne_top

/-! ## 1. The measure-theoretic peel of two slots of a product measure -/

/-- Among `m ≥ 3` indices there is one different from any prescribed pair. -/
private lemma cone_exists_fin_ne_two {m : ℕ} (hm : 3 ≤ m) (i j : Fin m) :
    ∃ k : Fin m, k ≠ i ∧ k ≠ j := by
  by_contra hcon
  have hcon' : ∀ k : Fin m, k = i ∨ k = j := by
    intro k
    by_contra h
    exact hcon ⟨k, fun hki => h (Or.inl hki), fun hkj => h (Or.inr hkj)⟩
  have hsurj : Function.Surjective (fun b : Bool => if b then i else j) := by
    intro x
    rcases hcon' x with h | h
    · exact ⟨true, by simpa using h.symm⟩
    · exact ⟨false, by simpa using h.symm⟩
  have hcard : Fintype.card (Fin m) ≤ 2 := Fintype.card_le_of_surjective _ hsurj
  rw [Fintype.card_fin] at hcard
  omega

/-- The inverse of `MeasurableEquiv.piFinSuccAbove` at a coordinate of the form
`k.succAbove t` reads off the `t`-th coordinate of the tail. -/
private lemma cone_piFinSuccAbove_symm_succAbove {β : Type*} [MeasurableSpace β] {n : ℕ}
    (k : Fin (n + 1)) (p : β × (Fin n → β)) (t : Fin n) :
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => β) k).symm p) (k.succAbove t)
      = p.2 t := by
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply]
  exact Fin.insertNth_apply_succAbove (α := fun _ : Fin (n + 1) => β) k p.1 p.2 t

/-- **Pair peel for `Measure.pi`.**  For any sigma-finite measure `μ` on `α`, two distinct
coordinates `i ≠ j` of `Fin (n + 2)` and a kernel `h` integrable on `μ.prod μ`,

  `∫ x, h (x i) (x j) ∂(Measure.pi (fun _ ↦ μ))
      = (μ univ).toReal ^ n · ∫ p, h p.1 p.2 ∂(μ.prod μ)`. -/
private theorem cone_integral_pi_pair_peel {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} [SigmaFinite μ] :
    ∀ n : ℕ, ∀ (i j : Fin (n + 2)), i ≠ j → ∀ {h : α → α → ℝ},
      MeasureTheory.Integrable (fun p : α × α => h p.1 p.2) (μ.prod μ) →
      (∫ x : Fin (n + 2) → α, h (x i) (x j)
          ∂(MeasureTheory.Measure.pi (fun _ : Fin (n + 2) => μ)))
        = (μ Set.univ).toReal ^ n * ∫ p : α × α, h p.1 p.2 ∂(μ.prod μ) := by
  intro n
  induction n with
  | zero =>
      intro i j hij h hint
      rw [pow_zero, one_mul]
      have hsymm := MeasureTheory.MeasurePreserving.symm MeasurableEquiv.finTwoArrow
        (measurePreserving_finTwoArrow μ)
      by_cases hi : i = 0
      · subst i
        have hj : j = 1 := Fin.eq_one_of_ne_zero j (fun hj0 => hij hj0.symm)
        subst j
        have hA := hsymm.integral_comp' (g := fun x : Fin 2 → α => h (x 0) (x 1))
        simpa [MeasurableEquiv.finTwoArrow_symm_apply] using hA.symm
      · have hi1 : i = 1 := Fin.eq_one_of_ne_zero i hi
        subst i
        have hj : j = 0 := by
          have hj1 : j ≠ 1 := fun hh => hij (by rw [hh])
          by_contra h0
          exact hj1 (Fin.eq_one_of_ne_zero j h0)
        subst j
        have hA := hsymm.integral_comp' (g := fun x : Fin 2 → α => h (x 1) (x 0))
        have hA' : (∫ p : α × α, h p.2 p.1 ∂(μ.prod μ))
            = ∫ x : Fin 2 → α, h (x 1) (x 0) ∂(Measure.pi (fun _ : Fin 2 => μ)) := by
          simpa [MeasurableEquiv.finTwoArrow_symm_apply] using hA
        exact hA'.symm.trans
          (MeasureTheory.integral_prod_swap (μ := μ) (ν := μ) (fun z : α × α => h z.1 z.2))
  | succ n ih =>
      intro i j hij h hint
      obtain ⟨k, hki, hkj⟩ := cone_exists_fin_ne_two (by omega : 3 ≤ n + 1 + 2) i j
      obtain ⟨i', hi'⟩ := Fin.exists_succAbove_eq (x := i) (y := k) hki.symm
      obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq (x := j) (y := k) hkj.symm
      have hij' : i' ≠ j' := fun hh => hij (by rw [← hi', ← hj', hh])
      have hmp : MeasureTheory.MeasurePreserving
          (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1 + 2) => α) k))
          (Measure.pi (fun _ : Fin (n + 1 + 2) => μ))
          (μ.prod (Measure.pi (fun _ : Fin (n + 2) => μ))) :=
        measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1 + 2) => μ) k
      have hcomp := (MeasureTheory.MeasurePreserving.symm
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1 + 2) => α) k) hmp).integral_comp'
        (g := fun x : Fin (n + 1 + 2) → α => h (x i) (x j))
      have hstep : (∫ x : Fin (n + 1 + 2) → α, h (x i) (x j)
            ∂(Measure.pi (fun _ : Fin (n + 1 + 2) => μ)))
          = ∫ p : α × (Fin (n + 2) → α), h (p.2 i') (p.2 j')
              ∂(μ.prod (Measure.pi (fun _ : Fin (n + 2) => μ))) := by
        refine hcomp.symm.trans (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_))
        intro p
        show h (((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1 + 2) => α) k).symm p) i)
                (((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1 + 2) => α) k).symm p) j)
              = h (p.2 i') (p.2 j')
        have h1 : ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1 + 2) => α) k).symm p) i
            = p.2 i' := by
          rw [← hi']
          exact cone_piFinSuccAbove_symm_succAbove k p i'
        have h2 : ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1 + 2) => α) k).symm p) j
            = p.2 j' := by
          rw [← hj']
          exact cone_piFinSuccAbove_symm_succAbove k p j'
        rw [h1, h2]
      have hsplit : (∫ p : α × (Fin (n + 2) → α), h (p.2 i') (p.2 j')
            ∂(μ.prod (Measure.pi (fun _ : Fin (n + 2) => μ))))
          = (μ Set.univ).toReal * (∫ r : Fin (n + 2) → α, h (r i') (r j')
              ∂(Measure.pi (fun _ : Fin (n + 2) => μ))) := by
        have h1 : (∫ p : α × (Fin (n + 2) → α), h (p.2 i') (p.2 j')
              ∂(μ.prod (Measure.pi (fun _ : Fin (n + 2) => μ))))
            = ∫ p : α × (Fin (n + 2) → α),
                (fun _ : α => (1 : ℝ)) p.1 * (fun r : Fin (n + 2) → α => h (r i') (r j')) p.2
                ∂(μ.prod (Measure.pi (fun _ : Fin (n + 2) => μ))) :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => by simp)
        have h2 : (∫ p : α × (Fin (n + 2) → α),
                (fun _ : α => (1 : ℝ)) p.1 * (fun r : Fin (n + 2) → α => h (r i') (r j')) p.2
                ∂(μ.prod (Measure.pi (fun _ : Fin (n + 2) => μ))))
            = (∫ y : α, (1 : ℝ) ∂μ) * (∫ r : Fin (n + 2) → α, h (r i') (r j')
                ∂(Measure.pi (fun _ : Fin (n + 2) => μ))) :=
          MeasureTheory.integral_prod_mul (fun _ : α => (1 : ℝ))
            (fun r : Fin (n + 2) → α => h (r i') (r j'))
        have h3 : (∫ y : α, (1 : ℝ) ∂μ) = (μ Set.univ).toReal := by
          rw [MeasureTheory.integral_const, MeasureTheory.Measure.real_def]
          simp
        rw [h1, h2, h3]
      have hIH := ih i' j' hij' (h := h) hint
      calc (∫ x : Fin (n + 1 + 2) → α, h (x i) (x j)
            ∂(Measure.pi (fun _ : Fin (n + 1 + 2) => μ)))
          = ∫ p : α × (Fin (n + 2) → α), h (p.2 i') (p.2 j')
              ∂(μ.prod (Measure.pi (fun _ : Fin (n + 2) => μ))) := hstep
        _ = (μ Set.univ).toReal * (∫ r : Fin (n + 2) → α, h (r i') (r j')
              ∂(Measure.pi (fun _ : Fin (n + 2) => μ))) := hsplit
        _ = (μ Set.univ).toReal
              * ((μ Set.univ).toReal ^ n * ∫ p : α × α, h p.1 p.2 ∂(μ.prod μ)) := by rw [hIH]
        _ = (μ Set.univ).toReal ^ (n + 1) * ∫ p : α × α, h p.1 p.2 ∂(μ.prod μ) := by
              rw [pow_succ]; ring

/-! ## 2. Integrability of the two-slot function on a finite product measure -/

/-- **Two slots of a finite product measure.**  If a kernel `h` is integrable with respect to
the product `μ.prod μ` of a *finite* measure `μ`, then for any two distinct slots `i ≠ j`
the function `x ↦ h (xᵢ) (xⱼ)` is integrable with respect to `Measure.pi (fun _ ↦ μ)`. -/
private theorem cone_pairSlotPiIntegrable_succ {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ] :
    ∀ n : ℕ, ∀ (i j : Fin (n + 2)), i ≠ j → ∀ {h : α → α → ℝ},
      MeasureTheory.Integrable (fun p : α × α => h p.1 p.2) (μ.prod μ) →
      MeasureTheory.Integrable (fun x : Fin (n + 2) → α => h (x i) (x j))
        (MeasureTheory.Measure.pi (fun _ : Fin (n + 2) => μ)) := by
  intro n
  induction n with
  | zero =>
      intro i j hij h hint
      have key : ∀ {h' : α → α → ℝ},
          MeasureTheory.Integrable (fun p : α × α => h' p.1 p.2) (μ.prod μ) →
          MeasureTheory.Integrable (fun x : Fin 2 → α => h' (x 0) (x 1))
            (MeasureTheory.Measure.pi (fun _ : Fin 2 => μ)) := by
        intro h' hh
        have h2 := ((MeasureTheory.measurePreserving_finTwoArrow μ).integrable_comp_emb
          (MeasurableEquiv.measurableEmbedding _)).mpr hh
        simpa [Function.comp_def, MeasurableEquiv.finTwoArrow_apply] using h2
      by_cases hi : i = 0
      · subst i
        have hj : j = 1 := Fin.eq_one_of_ne_zero j (fun hj0 => hij hj0.symm)
        subst j
        exact key hint
      · have hi1 : i = 1 := Fin.eq_one_of_ne_zero i hi
        subst i
        have hj : j = 0 := by
          have hj1 : j ≠ 1 := fun hh => hij (by rw [hh])
          by_contra h0
          exact hj1 (Fin.eq_one_of_ne_zero j h0)
        subst j
        have hswap : MeasureTheory.Integrable (fun p : α × α => h p.2 p.1) (μ.prod μ) :=
          MeasureTheory.Integrable.congr
            ((MeasureTheory.integrable_swap_iff (μ := μ) (ν := μ)
              (f := fun p : α × α => h p.1 p.2)).mpr hint)
            (Filter.Eventually.of_forall fun p => rfl)
        exact key (h' := fun u v => h v u) hswap
  | succ n ih =>
      intro i j hij h hint
      obtain ⟨k, hki, hkj⟩ := cone_exists_fin_ne_two (by omega : 3 ≤ n + 1 + 2) i j
      obtain ⟨i', hi'⟩ := Fin.exists_succAbove_eq (x := i) (y := k) hki.symm
      obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq (x := j) (y := k) hkj.symm
      have hij' : i' ≠ j' := fun hh => hij (by rw [← hi', ← hj', hh])
      have hmp : MeasureTheory.MeasurePreserving
          (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1 + 2) => α) k))
          (MeasureTheory.Measure.pi (fun _ : Fin (n + 1 + 2) => μ))
          (μ.prod (MeasureTheory.Measure.pi (fun _ : Fin (n + 2) => μ))) :=
        MeasureTheory.measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1 + 2) => μ) k
      have htail : MeasureTheory.Integrable
          (fun p : α × (Fin (n + 2) → α) => h (p.2 i') (p.2 j'))
          (μ.prod (MeasureTheory.Measure.pi (fun _ : Fin (n + 2) => μ))) :=
        MeasureTheory.Integrable.comp_snd (ih i' j' hij' hint) μ
      have hcomp := (MeasureTheory.MeasurePreserving.symm
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1 + 2) => α) k) hmp).integrable_comp_emb
        (MeasurableEquiv.measurableEmbedding _)
        (g := fun x : Fin (n + 1 + 2) → α => h (x i) (x j))
      refine hcomp.mp ?_
      refine MeasureTheory.Integrable.congr htail ?_
      filter_upwards with p
      show h (p.2 i') (p.2 j')
        = h (((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1 + 2) => α) k).symm p) i)
            (((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1 + 2) => α) k).symm p) j)
      rw [← hi', ← hj', cone_piFinSuccAbove_symm_succAbove k p i',
        cone_piFinSuccAbove_symm_succAbove k p j']

/-- **Two slots of a finite product measure**, `Fin N` form. -/
private theorem cone_pairSlotPiIntegrableFin {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ] {N : ℕ} (hN : 2 ≤ N)
    (i j : Fin N) (hij : i ≠ j) {h : α → α → ℝ}
    (hint : MeasureTheory.Integrable (fun p : α × α => h p.1 p.2) (μ.prod μ)) :
    MeasureTheory.Integrable (fun x : Fin N → α => h (x i) (x j))
      (MeasureTheory.Measure.pi (fun _ : Fin N => μ)) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  exact cone_pairSlotPiIntegrable_succ n i j hij hint

/-! ## 3. The two `A`-weighted facts used by the assembly -/

/-- Integrability of the two-slot integrand `w (xᵢ) (xⱼ)` over the product set `Aᴺ`, for
`w` integrable on `A × A` and `A ⊆ acube ℓ`. -/
private lemma cone_pairSlotIntegrable {n : ℕ} {ℓ : ℝ} {A : Set E3}
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {w : E3 → E3 → ℝ}
    (hint : MeasureTheory.Integrable (fun p : E3 × E3 => w p.1 p.2)
      ((MeasureTheory.volume.restrict A).prod (MeasureTheory.volume.restrict A)))
    {i j : Fin n} (hij : i ≠ j) :
    MeasureTheory.Integrable (fun x : Submission.BoseGases.X n => w (x i) (x j))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Set.univ.pi (fun _ : Fin n => A))) := by
  have hN : 2 ≤ n := cone_two_le_of_ne_fin hij
  have hAbdd : (MeasureTheory.volume : MeasureTheory.Measure E3) A ≠ ⊤ :=
    ne_top_of_le_ne_top (cone_acube_volume_ne_top ℓ) (MeasureTheory.measure_mono hAc)
  have _instFin : MeasureTheory.IsFiniteMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict A) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr hAbdd
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hpi : (MeasureTheory.volume : MeasureTheory.Measure
          (Submission.BoseGases.X (m + 2))).restrict
        (Set.univ.pi (fun _ : Fin (m + 2) => A))
      = MeasureTheory.Measure.pi (fun _ : Fin (m + 2) =>
          (MeasureTheory.volume : MeasureTheory.Measure E3).restrict A) := by
    rw [show (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (m + 2)))
        = MeasureTheory.Measure.pi (fun _ : Fin (m + 2) =>
            (MeasureTheory.volume : MeasureTheory.Measure E3)) from rfl]
    exact MeasureTheory.Measure.restrict_pi_pi (fun _ : Fin (m + 2) =>
      (MeasureTheory.volume : MeasureTheory.Measure E3)) (fun _ : Fin (m + 2) => A)
  rw [hpi]
  exact cone_pairSlotPiIntegrableFin (by omega) i j hij hint

/-- **The value of the two-slot integral over the product set `Aᴺ`**: for `w` integrable on
`A × A` and `A ⊆ acube ℓ`, `∫_{Aᴺ} w (xᵢ) (xⱼ) = (vol A)^{n−2} ∫_{A × A} w`. -/
private lemma cone_pairSlotValue {n : ℕ} (hn : 2 ≤ n) {ℓ : ℝ} {A : Set E3}
    (_hAc : A ⊆ Submission.BoseGases.acube ℓ) {w : E3 → E3 → ℝ}
    (hint : MeasureTheory.Integrable (fun p : E3 × E3 => w p.1 p.2)
      ((MeasureTheory.volume.restrict A).prod (MeasureTheory.volume.restrict A)))
    {i j : Fin n} (hij : i ≠ j) :
    (∫ x in Set.univ.pi (fun _ : Fin n => A), w (x i) (x j))
      = (MeasureTheory.volume A).toReal ^ (n - 2) * (∫ p in A ×ˢ A, w p.1 p.2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [Nat.add_sub_cancel]
  have hpi : (MeasureTheory.volume : MeasureTheory.Measure
          (Submission.BoseGases.X (m + 2))).restrict
        (Set.univ.pi (fun _ : Fin (m + 2) => A))
      = MeasureTheory.Measure.pi (fun _ : Fin (m + 2) =>
          (MeasureTheory.volume : MeasureTheory.Measure E3).restrict A) := by
    rw [show (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (m + 2)))
        = MeasureTheory.Measure.pi (fun _ : Fin (m + 2) =>
            (MeasureTheory.volume : MeasureTheory.Measure E3)) from rfl]
    exact MeasureTheory.Measure.restrict_pi_pi (fun _ : Fin (m + 2) =>
      (MeasureTheory.volume : MeasureTheory.Measure E3)) (fun _ : Fin (m + 2) => A)
  rw [show (∫ x in Set.univ.pi (fun _ : Fin (m + 2) => A), w (x i) (x j))
      = ∫ x : Submission.BoseGases.X (m + 2), w (x i) (x j)
          ∂((MeasureTheory.volume : MeasureTheory.Measure
              (Submission.BoseGases.X (m + 2))).restrict
            (Set.univ.pi (fun _ : Fin (m + 2) => A))) from rfl]
  rw [hpi]
  rw [cone_integral_pi_pair_peel (μ := (MeasureTheory.volume : MeasureTheory.Measure E3).restrict A)
    (h := w) m i j hij hint]
  rw [MeasureTheory.Measure.restrict_apply_univ]
  congr 1
  rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod E3 E3]

/-! ## 4. The target -/

theorem pairKernel_flatIntegralCone {n : ℕ} {ℓ V D : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {w : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hwm : MeasureTheory.AEStronglyMeasurable (Function.uncurry w)
      (MeasureTheory.volume.restrict (A ×ˢ A)))
    (hwD : ∀ a b, |w a b| ≤ D) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        (∏ i : Fin n, A.indicator (fun _ => (1 : ℝ)) (x i))
          * ((1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n, w (x p.1) (x p.2)))
      = ((n : ℝ) * ((n : ℝ) - 1) / 2) * V ^ (n - 2)
          * (∫ p in A ×ˢ A, w p.1 p.2) := by
  classical
  -- finiteness of `A` and of `A × A`, and integrability of the kernel
  have hAbdd : (MeasureTheory.volume : MeasureTheory.Measure E3) A ≠ ⊤ :=
    ne_top_of_le_ne_top (cone_acube_volume_ne_top ℓ) (MeasureTheory.measure_mono hAc)
  have hprodeq : (MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)).restrict (A ×ˢ A)
      = (MeasureTheory.volume.restrict A).prod (MeasureTheory.volume.restrict A) :=
    (MeasureTheory.Measure.prod_restrict (μ := (MeasureTheory.volume : MeasureTheory.Measure E3))
      (ν := (MeasureTheory.volume : MeasureTheory.Measure E3)) A A).symm
  have hfin : (MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)) (A ×ˢ A) ≠ ⊤ := by
    rw [MeasureTheory.Measure.volume_eq_prod E3 E3, MeasureTheory.Measure.prod_prod]
    exact ENNReal.mul_ne_top hAbdd hAbdd
  have _instFin : MeasureTheory.IsFiniteMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)).restrict (A ×ˢ A)) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr hfin
  have hint1 : MeasureTheory.Integrable (fun p : E3 × E3 => w p.1 p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)).restrict (A ×ˢ A)) :=
    MeasureTheory.Integrable.of_bound
      (by simpa only [Function.uncurry_def] using hwm) D
      (Filter.Eventually.of_forall (fun p => by
        rw [Real.norm_eq_abs]
        exact hwD p.1 p.2))
  have hint : MeasureTheory.Integrable (fun p : E3 × E3 => w p.1 p.2)
      ((MeasureTheory.volume.restrict A).prod (MeasureTheory.volume.restrict A)) := by
    rw [← hprodeq]
    exact hint1
  by_cases hlt : n < 2
  · -- the sum over `pairSet n` is empty and the right-hand side vanishes
    have hemp : Submission.BoseGases.pairSet n = ∅ := by
      rw [← Finset.card_eq_zero, cone_card_pairSet_nat]
      rcases (by omega : n = 0 ∨ n = 1) with h | h <;> subst h <;> simp
    have hzero : (∫ x in Submission.BoseGases.abox n ℓ,
        (∏ i : Fin n, A.indicator (fun _ => (1 : ℝ)) (x i))
          * ((1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n, w (x p.1) (x p.2))) = 0 := by
      have hfun : (∫ x in Submission.BoseGases.abox n ℓ,
          (∏ i : Fin n, A.indicator (fun _ => (1 : ℝ)) (x i))
            * ((1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n, w (x p.1) (x p.2)))
          = ∫ x in Submission.BoseGases.abox n ℓ, (0 : ℝ) := by
        refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
          (fun x _ => ?_)
        rw [hemp, Finset.sum_empty, mul_zero, mul_zero]
      rw [hfun]
      simp
    have hrhs : ((n : ℝ) * ((n : ℝ) - 1) / 2) * V ^ (n - 2)
        * (∫ p in A ×ˢ A, w p.1 p.2) = 0 := by
      rcases (by omega : n = 0 ∨ n = 1) with h0 | h0 <;> subst h0 <;> norm_num
    rw [hzero, hrhs]
  · have hn : 2 ≤ n := by omega
    have hne_of_mem : ∀ p ∈ Submission.BoseGases.pairSet n, p.1 ≠ p.2 := by
      intro p hp
      simpa [Submission.BoseGases.pairSet] using hp
    have hInt : ∀ p ∈ Submission.BoseGases.pairSet n,
        MeasureTheory.Integrable (fun x : Submission.BoseGases.X n => w (x p.1) (x p.2))
          ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
            (Set.univ.pi (fun _ : Fin n => A))) :=
      fun p hp => cone_pairSlotIntegrable hAc hint (hne_of_mem p hp)
    have hVal : ∀ p ∈ Submission.BoseGases.pairSet n,
        (∫ x in Set.univ.pi (fun _ : Fin n => A), w (x p.1) (x p.2))
          = (MeasureTheory.volume A).toReal ^ (n - 2) * (∫ q in A ×ˢ A, w q.1 q.2) :=
      fun p hp => cone_pairSlotValue hn hAc hint (hne_of_mem p hp)
    calc (∫ x in Submission.BoseGases.abox n ℓ,
        (∏ i : Fin n, A.indicator (fun _ => (1 : ℝ)) (x i))
          * ((1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n, w (x p.1) (x p.2)))
        = ∫ x in Submission.BoseGases.abox n ℓ,
            ((1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n, w (x p.1) (x p.2))
              * (∏ i : Fin n, A.indicator (fun _ => (1 : ℝ)) (x i)) := by
          refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
            (fun x _ => ?_)
          ring
      _ = ∫ x in Set.univ.pi (fun _ : Fin n => A),
            (1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n, w (x p.1) (x p.2) :=
          Work.BoseFixB1B.setIntegral_abox_mul_prod_indicator hA hAc _
      _ = (1 / 2) * ∫ x in Set.univ.pi (fun _ : Fin n => A),
            ∑ p ∈ Submission.BoseGases.pairSet n, w (x p.1) (x p.2) := by
          rw [MeasureTheory.integral_const_mul]
      _ = (1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
            ∫ x in Set.univ.pi (fun _ : Fin n => A), w (x p.1) (x p.2) := by
          congr 1
          exact MeasureTheory.integral_finsetSum (Submission.BoseGases.pairSet n) hInt
      _ = (1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
            ((MeasureTheory.volume A).toReal ^ (n - 2) * (∫ q in A ×ˢ A, w q.1 q.2)) := by
          congr 1
          exact Finset.sum_congr rfl hVal
      _ = ((n : ℝ) * ((n : ℝ) - 1) / 2) * V ^ (n - 2) * (∫ p in A ×ˢ A, w p.1 p.2) := by
          rw [Finset.sum_const, nsmul_eq_mul, cone_card_pairSet_cast, ← hVeq]
          ring

end Work.BoseB1Cube

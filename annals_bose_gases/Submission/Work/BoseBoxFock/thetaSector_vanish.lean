import Mathlib.CategoryTheory.Countable
import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.meanProj_continuous
import Submission.Work.BoseFixB2.Sector.aQ_sym_box
import Submission.Work.BoseFixB2.Sector.jointProj_resolution
import Submission.Work.BoseFixB2.Sector.nPlusPow_jointProj
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.thetaSector_vanish`

The `θ`-sector `thetaSector ℓ S Φ` (`BF3cDefs`) is the component of a box state in which exactly
the slots of `S` sit in the condensate, i.e. the `n₊ = n − |S|` sector of the excitation operator
`n₊ = Σᵢ aQ ℓ i`.  The spectral hypothesis `Work.BoseBox.SpectralNPlusLe ℓ M Φ` (all moments
`⟨Φ, n₊^m Φ⟩ ≤ M^m ‖Φ‖²`) therefore forces the sector to vanish as soon as `n − |S| > M`.

The proof has two halves.

* **Structural half (analysis).**  `meanProj ℓ T` is the iterated slot mean `∏_{i ∈ T} aP ℓ i`;
  this is `meanProj_insert`.  Feeding it into the `blockOp` recursion of
  `Work.BoseFixB2` identifies `thetaSector ℓ S Φ` with the joint sector projection
  `jointProj ℓ V Φ`, `V = {0,…,n−1} \ S`.  (`Work.BoseFixB2.jointProj` is exactly the iterated
  product `∏_{j ∈ V} aQ_j ∏_{j ∉ V} aP_j`, whose reso- / ortho- / self-adjointness / eigenvalue
  theory is already in the corpus.)
* **Spectral half (algebra).**  With `Φ = Σ_V E_V Φ` and the sectors `E_V` orthogonal and
  eigenstates of `n₊` with eigenvalue `|V|`, the moment inequalities give
  `λ^{2k}‖E_UΦ‖² ≤ M^{2k}‖Φ‖²` for the sector `U` of the claim and all `k`; `λ = n − |S| > M`
  forces `‖E_UΦ‖² = 0`.
-/

namespace Work.BoseBoxFock

open MeasureTheory
open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. The peel of one slot mean out of a product of slot means

`meanProj_insert_aux` is the measure-theoretic heart: averaging a state over the slots of
`insert i T` is the same as averaging over the slot `i` after averaging over the slots of `T`.
It is proved by splitting the product integral along the measure-preserving equivalence
`Eeq hi : (↑T → ℝ³) × ℝ³ ≃ᵐ ↑(T ∪ {i}) → ℝ³` (`SlotProjAux`) and applying Fubini; the slot
`i ∉ T` is precisely what makes the restricted box measures split as a product.
The continuity of `meanProj ℓ S Φ` in `Φ` is `meanProj_continuous` (sibling module). -/

theorem meanProj_insert_aux (ℓ : ℝ) (hℓ : 0 < ℓ) {n : ℕ} {T : Finset (Fin n)} {i : Fin n}
    (hi : i ∉ T) {Φ : X n → ℝ} (hΦ : Continuous Φ) :
    meanProj ℓ (insert i T) Φ = aP ℓ i (meanProj ℓ T Φ) := by
  funext x
  have hmp : MeasurePreserving (Eeq hi)
      ((Measure.pi (fun _ : ↑T => (volume : Measure ℝ³).restrict (acube ℓ))).prod
        ((volume : Measure ℝ³).restrict (acube ℓ)))
      (Measure.pi (fun _ : ↑(T ∪ {i}) => (volume : Measure ℝ³).restrict (acube ℓ))) := by
    have h1 : MeasurePreserving
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (↑T → ℝ³))
          (MeasurableEquiv.funUnique (↑({i} : Finset (Fin n))) ℝ³).symm)
        ((Measure.pi fun _ : ↑T => (volume : Measure ℝ³).restrict (acube ℓ)).prod
          ((volume : Measure ℝ³).restrict (acube ℓ)))
        ((Measure.pi fun _ : ↑T => (volume : Measure ℝ³).restrict (acube ℓ)).prod
          (Measure.pi fun _ : ↑({i} : Finset (Fin n)) =>
            (volume : Measure ℝ³).restrict (acube ℓ))) :=
      MeasurePreserving.prod (MeasurePreserving.id _)
        (measurePreserving_funUnique ((volume : Measure ℝ³).restrict (acube ℓ))
          (↑({i} : Finset (Fin n)))).symm
    have h2 : MeasurePreserving
        (MeasurableEquiv.piFinsetUnion (fun _ : Fin n => ℝ³)
          (Finset.disjoint_singleton_right.mpr hi))
        ((Measure.pi fun _ : ↑T => (volume : Measure ℝ³).restrict (acube ℓ)).prod
          (Measure.pi fun _ : ↑({i} : Finset (Fin n)) =>
            (volume : Measure ℝ³).restrict (acube ℓ)))
        (Measure.pi fun _ : ↑(T ∪ {i}) => (volume : Measure ℝ³).restrict (acube ℓ)) :=
      measurePreserving_piFinsetUnion (Finset.disjoint_singleton_right.mpr hi)
        (fun _ : Fin n => (volume : Measure ℝ³).restrict (acube ℓ))
    exact h1.trans h2
  have hL : meanProj ℓ (insert i T) Φ x
      = ∫ z : ↑(T ∪ {i}) → ℝ³, (∏ _ : ↑(T ∪ {i}), (ℓ ^ 3)⁻¹) *
          Φ (Function.updateFinset x (T ∪ {i}) z)
          ∂(Measure.pi fun _ : ↑(T ∪ {i}) => (volume : Measure ℝ³).restrict (acube ℓ)) := by
    rw [meanProj, (Finset.union_singleton i T).symm,
      show (volume : Measure (↑(T ∪ {i}) → ℝ³)).restrict
            (Set.pi Set.univ (fun _ : ↑(T ∪ {i}) => acube ℓ))
          = Measure.pi (fun _ : ↑(T ∪ {i}) => (volume : Measure ℝ³).restrict (acube ℓ)) from
        Measure.restrict_pi_pi (μ := fun _ : ↑(T ∪ {i}) => (volume : Measure ℝ³))
          (s := fun _ => acube ℓ)]
    simp only [Function.updateFinset_def]
  have hR : aP ℓ i (meanProj ℓ T Φ) x
      = (1 / ℓ ^ 3) * ∫ w : ℝ³, ∫ z' : ↑T → ℝ³, (∏ _ : ↑T, (ℓ ^ 3)⁻¹) *
          Φ (Function.update
            (fun j : Fin n => if h : j ∈ T then z' ⟨j, h⟩ else x j) i w)
          ∂(Measure.pi fun _ : ↑T => (volume : Measure ℝ³).restrict (acube ℓ))
          ∂((volume : Measure ℝ³).restrict (acube ℓ)) := by
    have hcfg : ∀ (y : ℝ³) (z : ↑T → ℝ³),
        (fun j : Fin n => if h : j ∈ T then z ⟨j, h⟩ else Function.update x i y j)
          = Function.update (fun j : Fin n => if h : j ∈ T then z ⟨j, h⟩ else x j) i y := by
      intro y z
      funext j
      by_cases hjT : j ∈ T
      · have hji : j ≠ i := fun h => hi (h ▸ hjT)
        simp only [hjT, dif_pos, Function.update_of_ne hji]
      · by_cases hji : j = i
        · subst hji
          simp only [hjT, dif_neg, not_false_eq_true, Function.update_self]
        · simp only [hjT, dif_neg, not_false_eq_true, Function.update_of_ne hji]
    simp only [aP, meanProj]
    rw [show (volume : Measure (↑T → ℝ³)).restrict
            (Set.pi Set.univ (fun _ : ↑T => acube ℓ))
          = Measure.pi (fun _ : ↑T => (volume : Measure ℝ³).restrict (acube ℓ)) from
        Measure.restrict_pi_pi (μ := fun _ : ↑T => (volume : Measure ℝ³))
          (s := fun _ => acube ℓ)]
    simp only [hcfg]

  rw [hL, hR]
  have hcont : Continuous (fun z : ↑(T ∪ {i}) → ℝ³ => (∏ _ : ↑(T ∪ {i}), (ℓ ^ 3)⁻¹) *
      Φ (Function.updateFinset x (T ∪ {i}) z)) :=
    continuous_const.mul (hΦ.comp ((slotContinuous_updateFinset (T ∪ {i})).comp
      (continuous_const.prodMk continuous_id)))
  have hcompact : IsCompact (Set.pi Set.univ (fun _ : ↑(T ∪ {i}) => acube ℓ)) :=
    isCompact_univ_pi (fun _ => acube_compact hℓ)
  have hg : Integrable (fun z : ↑(T ∪ {i}) → ℝ³ => (∏ _ : ↑(T ∪ {i}), (ℓ ^ 3)⁻¹) *
      Φ (Function.updateFinset x (T ∪ {i}) z))
      (Measure.pi fun _ : ↑(T ∪ {i}) => (volume : Measure ℝ³).restrict (acube ℓ)) := by
    rw [← Measure.restrict_pi_pi (μ := fun _ : ↑(T ∪ {i}) => (volume : Measure ℝ³))
      (s := fun _ => acube ℓ)]
    exact ContinuousOn.integrableOn_compact hcompact hcont.continuousOn
  have hcomp : ∀ p : (↑T → ℝ³) × ℝ³,
      (∏ _ : ↑(T ∪ {i}), (ℓ ^ 3)⁻¹) * Φ (Function.updateFinset x (T ∪ {i}) (Eeq hi p))
        = (∏ _ : ↑T, (ℓ ^ 3)⁻¹) * (ℓ ^ 3)⁻¹ *
            Φ (Function.update (Function.updateFinset x T p.1) i p.2) := by
    rintro ⟨z', w⟩
    have hcard : (T ∪ {i}).card = T.card + 1 :=
      Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hi)
    have hprod : (∏ _ : ↑(T ∪ {i}), (ℓ ^ 3)⁻¹) = (∏ _ : ↑T, (ℓ ^ 3)⁻¹) * (ℓ ^ 3)⁻¹ := by
      rw [Finset.prod_const, Finset.prod_const, Finset.card_univ, Finset.card_univ,
        Fintype.card_coe, Fintype.card_coe, hcard, pow_succ]
    rw [updateFinset_Eeq hi x z' w, hprod]
  have hInt : Integrable (fun p : (↑T → ℝ³) × ℝ³ =>
      (∏ _ : ↑(T ∪ {i}), (ℓ ^ 3)⁻¹) * Φ (Function.updateFinset x (T ∪ {i}) (Eeq hi p)))
      ((Measure.pi fun _ : ↑T => (volume : Measure ℝ³).restrict (acube ℓ)).prod
        ((volume : Measure ℝ³).restrict (acube ℓ))) :=
    (hmp.integrable_comp_emb (Eeq hi).measurableEmbedding).mpr hg
  have htransport : (∫ z : ↑(T ∪ {i}) → ℝ³, (∏ _ : ↑(T ∪ {i}), (ℓ ^ 3)⁻¹) *
        Φ (Function.updateFinset x (T ∪ {i}) z)
        ∂(Measure.pi fun _ : ↑(T ∪ {i}) => (volume : Measure ℝ³).restrict (acube ℓ)))
      = ∫ p : (↑T → ℝ³) × ℝ³, (∏ _ : ↑(T ∪ {i}), (ℓ ^ 3)⁻¹) *
          Φ (Function.updateFinset x (T ∪ {i}) (Eeq hi p))
          ∂((Measure.pi fun _ : ↑T => (volume : Measure ℝ³).restrict (acube ℓ)).prod
            ((volume : Measure ℝ³).restrict (acube ℓ))) :=
    (hmp.integral_comp (Eeq hi).measurableEmbedding _).symm
  rw [htransport]
  rw [MeasureTheory.integral_prod_symm (fun p : (↑T → ℝ³) × ℝ³ =>
      (∏ _ : ↑(T ∪ {i}), (ℓ ^ 3)⁻¹) * Φ (Function.updateFinset x (T ∪ {i}) (Eeq hi p))) hInt]
  have hinner : ∀ w : ℝ³, (∫ z' : ↑T → ℝ³, (∏ _ : ↑(T ∪ {i}), (ℓ ^ 3)⁻¹) *
        Φ (Function.updateFinset x (T ∪ {i}) (Eeq hi (z', w)))
        ∂(Measure.pi fun _ : ↑T => (volume : Measure ℝ³).restrict (acube ℓ)))
      = ∫ z' : ↑T → ℝ³, (∏ _ : ↑T, (ℓ ^ 3)⁻¹) * (ℓ ^ 3)⁻¹ *
          Φ (Function.update (Function.updateFinset x T z') i w)
          ∂(Measure.pi fun _ : ↑T => (volume : Measure ℝ³).restrict (acube ℓ)) := by
    intro w
    exact integral_congr_ae (Filter.Eventually.of_forall (fun z' => hcomp (z', w)))
  simp only [hinner]
  simp only [Function.updateFinset_def]
  simp_rw [MeasureTheory.integral_const_mul]
  rw [one_div]
  ring

/-! ## 1. Slot sets in `Fin n` and in `ℕ` -/

/-- The set of natural-number slot indices of a `Fin n`-slot set. -/
def tsImS {n : ℕ} (S : Finset (Fin n)) : Finset ℕ := S.image Fin.val

/-- The `Fin n`-slots whose natural-number index lies in a given set. -/
def tsPreS (n : ℕ) (V : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (i : ℕ) ∈ V)

@[simp] lemma mem_tsPreS {n : ℕ} (V : Finset ℕ) (i : Fin n) : i ∈ tsPreS n V ↔ (i : ℕ) ∈ V := by
  simp [tsPreS]

lemma mem_tsImS {n : ℕ} (S : Finset (Fin n)) (k : ℕ) :
    k ∈ tsImS S ↔ ∃ i ∈ S, (i : ℕ) = k := by
  simp [tsImS, Finset.mem_image]

lemma tsImS_subset_range {n : ℕ} (S : Finset (Fin n)) : tsImS S ⊆ Finset.range n := by
  intro k hk
  rw [mem_tsImS] at hk
  obtain ⟨i, -, rfl⟩ := hk
  exact Finset.mem_range.mpr i.isLt

lemma tsPreS_tsImS {n : ℕ} (S : Finset (Fin n)) : tsPreS n (tsImS S) = S := by
  ext i
  rw [mem_tsPreS, mem_tsImS]
  constructor
  · rintro ⟨j, hj, hji⟩
    rw [← Fin.ext hji]
    exact hj
  · intro hi
    exact ⟨i, hi, rfl⟩

lemma tsImS_tsPreS {n : ℕ} (V : Finset ℕ) : tsImS (tsPreS n V) = V ∩ Finset.range n := by
  ext k
  rw [mem_tsImS, Finset.mem_inter, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [mem_tsPreS] at hi
    exact ⟨hi, i.isLt⟩
  · rintro ⟨hk, hkn⟩
    exact ⟨⟨k, hkn⟩, by rwa [mem_tsPreS], rfl⟩

lemma tsImS_card {n : ℕ} (S : Finset (Fin n)) : (tsImS S).card = S.card :=
  Finset.card_image_of_injective S Fin.val_injective

lemma tsPreS_union {n : ℕ} (V W : Finset ℕ) :
    tsPreS n (V ∪ W) = tsPreS n V ∪ tsPreS n W := by
  ext i
  simp only [mem_tsPreS, Finset.mem_union]

lemma tsPreS_empty {n : ℕ} : tsPreS n (∅ : Finset ℕ) = (∅ : Finset (Fin n)) := by
  ext i
  simp [mem_tsPreS]

lemma tsPreS_mono {n : ℕ} {V W : Finset ℕ} (h : V ⊆ W) : tsPreS n V ⊆ tsPreS n W := by
  intro i hi
  rw [mem_tsPreS] at hi ⊢
  exact h hi

lemma tsImS_mem_iff {n : ℕ} (S : Finset (Fin n)) (k : ℕ) (hk : k < n) :
    (⟨k, hk⟩ : Fin n) ∈ S ↔ k ∈ tsImS S := by
  rw [mem_tsImS]
  constructor
  · intro h
    exact ⟨⟨k, hk⟩, h, rfl⟩
  · rintro ⟨j, hj, hjk⟩
    have hji : j = (⟨k, hk⟩ : Fin n) := Fin.ext hjk
    rw [← hji]
    exact hj

lemma tsPreS_insert {n : ℕ} {V : Finset ℕ} {k : ℕ} (hk : k < n) (hkV : k ∉ V) :
    tsPreS n (insert k V) = insert ⟨k, hk⟩ (tsPreS n V) := by
  ext i
  rw [mem_tsPreS, Finset.mem_insert, Finset.mem_insert, mem_tsPreS]
  constructor
  · rintro (h | h)
    · exact Or.inl (Fin.ext h)
    · exact Or.inr h
  · rintro (h | h)
    · rw [h]
      exact Or.inl rfl
    · exact Or.inr h

/-! ## 2. The slot mean over natural-number slot sets -/

/-- The iterated slot mean over a set of natural slot numbers (only the slots `< n` matter). -/
noncomputable def meanProjN {n : ℕ} (ℓ : ℝ) (V : Finset ℕ) (Φ : X n → ℝ) : X n → ℝ :=
  meanProj ℓ (tsPreS n V) Φ

/-- The empty product of slot means is the identity. -/
lemma meanProj_empty {n : ℕ} (ℓ : ℝ) (Φ : X n → ℝ) :
    meanProj ℓ (∅ : Finset (Fin n)) Φ = Φ := by
  have hE : IsEmpty {i : Fin n // i ∈ (∅ : Finset (Fin n))} :=
    ⟨fun a => Finset.notMem_empty a.1 a.2⟩
  funext x
  rw [meanProj]
  have hpi : Set.univ.pi (fun _ : {i : Fin n // i ∈ (∅ : Finset (Fin n))} => acube ℓ)
      = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro z
    rw [Set.mem_pi]
    exact fun i _ => absurd i.2 (Finset.notMem_empty i.1)
  rw [hpi, setIntegral_univ]
  have hconst : (fun z : {i : Fin n // i ∈ (∅ : Finset (Fin n))} → EuclideanSpace ℝ (Fin 3) =>
      (∏ _i : {i : Fin n // i ∈ (∅ : Finset (Fin n))}, (ℓ ^ 3)⁻¹) *
        Φ (fun i => if h : i ∈ (∅ : Finset (Fin n)) then z ⟨i, h⟩ else x i))
      = fun _ : {i : Fin n // i ∈ (∅ : Finset (Fin n))} → EuclideanSpace ℝ (Fin 3) => Φ x := by
    funext z
    have h1 : (fun i : Fin n => if h : i ∈ (∅ : Finset (Fin n)) then z ⟨i, h⟩ else x i) = x := by
      funext i
      simp
    rw [h1]
    haveI := hE
    rw [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
  rw [hconst, integral_const]
  haveI := hE
  haveI : IsProbabilityMeasure
      (Measure.pi (fun _ : {i : Fin n // i ∈ (∅ : Finset (Fin n))} => (volume : Measure ℝ³))) := by
    rw [Measure.pi_of_empty]
    infer_instance
  rw [probReal_univ, one_smul]

lemma meanProjN_empty {n : ℕ} (ℓ : ℝ) (Φ : X n → ℝ) : meanProjN ℓ (∅ : Finset ℕ) Φ = Φ := by
  rw [meanProjN, tsPreS_empty]
  exact meanProj_empty ℓ Φ

lemma meanProjN_continuous {n : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) (V : Finset ℕ) {Φ : X n → ℝ}
    (hΦ : Continuous Φ) : Continuous (meanProjN ℓ V Φ) :=
  meanProj_continuous ℓ hℓ (tsPreS n V) hΦ

/-- The peel of one slot mean out of an iterated slot mean. -/
lemma meanProjN_insert {n : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) {V : Finset ℕ} {k : ℕ} (hk : k < n)
    (hkV : k ∉ V) {Φ : X n → ℝ} (hΦ : Continuous Φ) :
    meanProjN ℓ (insert k V) Φ = aP ℓ ⟨k, hk⟩ (meanProjN ℓ V Φ) := by
  rw [meanProjN, meanProjN, tsPreS_insert hk hkV]
  exact meanProj_insert_aux ℓ hℓ (by rwa [mem_tsPreS]) hΦ

/-! ## 3. Linearity of the slot operators in the state -/

/-- One slot mean is linear over a finite sum of continuous states. -/
lemma aP_finset_sum {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n) {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (f : ι → X n → ℝ) (hf : ∀ W ∈ s, Continuous (f W)) (x : X n) :
    aP ℓ i (fun y => ∑ W ∈ s, c W * f W y) x
      = ∑ W ∈ s, c W * aP ℓ i (f W) x := by
  rw [aP]
  rw [integral_finsetSum s]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun W hW => ?_)
    rw [integral_const_mul, aP]
    ring
  · intro W hW
    have hg : Continuous (fun y : ℝ³ => c W * f W (Function.update x i y)) :=
      continuous_const.mul ((hf W hW).comp (by fun_prop))
    exact (integrableOn_acube_of_continuous hℓ hg)

/-- The excitation number is linear over a finite sum of continuous states. -/
lemma nPlusFun_finset_sum {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (f : ι → X n → ℝ) (hf : ∀ W ∈ s, Continuous (f W)) (x : X n) :
    Work.BoseBox.nPlusFun ℓ (fun y => ∑ W ∈ s, c W * f W y) x
      = ∑ W ∈ s, c W * Work.BoseBox.nPlusFun ℓ (f W) x := by
  simp only [Work.BoseBox.nPlusFun, aQ]
  calc ∑ i : Fin n, ((∑ W ∈ s, c W * f W x)
        - aP ℓ i (fun y => ∑ W ∈ s, c W * f W y) x)
      = ∑ i : Fin n, ∑ W ∈ s, (c W * f W x - c W * aP ℓ i (f W) x) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [aP_finset_sum hℓ i s c f hf x, ← Finset.sum_sub_distrib]
    _ = ∑ W ∈ s, ∑ i : Fin n, (c W * f W x - c W * aP ℓ i (f W) x) := Finset.sum_comm
    _ = ∑ W ∈ s, c W * ∑ i : Fin n, (f W x - aP ℓ i (f W) x) := by
        refine Finset.sum_congr rfl (fun W _ => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)

/-! ## 4. The sector expansion of `n₊^m` -/

/-- The moments of `n₊` expanded in the joint sectors `E_W = jointProj ℓ W`:
`n₊^m Φ = Σ_W |W|^m E_W Φ`. -/
lemma nPlusPow_sector_expansion {n : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) {Φ : X n → ℝ}
    (hΦ : Continuous Φ) (m : ℕ) :
    Work.BoseBox.nPlusPow ℓ n m Φ
      = fun x => ∑ W ∈ (Finset.range n).powerset,
          (W.card : ℝ) ^ m * Work.BoseFixB2.jointProj ℓ W Φ x := by
  induction m with
  | zero =>
      funext x
      rw [show Work.BoseBox.nPlusPow ℓ n 0 Φ = Φ from rfl,
        ← congrFun (Work.BoseFixB2.Sector.jointProj_resolution hℓ Φ hΦ) x]
      simp only [Finset.sum_apply, pow_zero, one_mul]
  | succ m ih =>
      rw [show Work.BoseBox.nPlusPow ℓ n (m + 1) Φ
            = Work.BoseBox.nPlusFun ℓ (Work.BoseBox.nPlusPow ℓ n m Φ) from rfl, ih]
      funext x
      rw [nPlusFun_finset_sum hℓ _ (fun W => (W.card : ℝ) ^ m)
        (fun W => Work.BoseFixB2.jointProj ℓ W Φ)
        (fun W _ => Work.BoseFixB2.Sector.jointProj_continuous hℓ W hΦ) x]
      refine Finset.sum_congr rfl (fun W hW => ?_)
      rw [congrFun (Work.BoseFixB2.Sector.nPlusFun_jointProj hℓ
        (Finset.mem_powerset.mp hW) hΦ) x, pow_succ]
      ring

/-! ## 5. The `blockOp` expansion of the iterated slot mean -/

lemma range_succ_inter_of_mem {V : Finset ℕ} {m : ℕ} (hm : m ∈ V) :
    V ∩ Finset.range (m + 1) = insert m (V ∩ Finset.range m) := by
  ext k
  simp only [Finset.mem_inter, Finset.mem_range, Finset.mem_insert]
  constructor
  · rintro ⟨hkV, hklt⟩
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hklt) with h | h
    · exact Or.inr ⟨hkV, h⟩
    · exact Or.inl h
  · rintro (h | ⟨hkV, hklt⟩)
    · exact ⟨h ▸ hm, by omega⟩
    · exact ⟨hkV, by omega⟩

lemma range_succ_sdiff_of_mem {V : Finset ℕ} {m : ℕ} (hm : m ∈ V) :
    Finset.range (m + 1) \ V = Finset.range m \ V := by
  ext k
  simp only [Finset.mem_sdiff, Finset.mem_range]
  constructor
  · rintro ⟨hklt, hkV⟩
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hklt) with h | h
    · exact ⟨h, hkV⟩
    · exact absurd (h ▸ hm) hkV
  · rintro ⟨h, hkV⟩
    exact ⟨by omega, hkV⟩

lemma range_succ_inter_of_notMem {V : Finset ℕ} {m : ℕ} (hm : m ∉ V) :
    V ∩ Finset.range (m + 1) = V ∩ Finset.range m := by
  ext k
  simp only [Finset.mem_inter, Finset.mem_range]
  constructor
  · rintro ⟨hkV, hklt⟩
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hklt) with h | h
    · exact ⟨hkV, h⟩
    · exact absurd (h ▸ hkV) hm
  · rintro ⟨hkV, hklt⟩
    exact ⟨hkV, by omega⟩

lemma range_succ_sdiff_of_notMem {V : Finset ℕ} {m : ℕ} (hm : m ∉ V) :
    Finset.range (m + 1) \ V = insert m (Finset.range m \ V) := by
  ext k
  simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_insert]
  constructor
  · rintro ⟨hklt, hkV⟩
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hklt) with h | h
    · exact Or.inr ⟨h, hkV⟩
    · exact Or.inl h
  · rintro (h | ⟨hklt, hkV⟩)
    · exact ⟨by omega, h ▸ hm⟩
    · exact ⟨by omega, hkV⟩

/-- **The expansion of the iterated slot mean over the joint sectors**: the product
`blockOp ℓ V m` of the slot operators (`aQ` on `V`, `aP` elsewhere) over the slots `0,…,m−1`
is the Möbius sum `Σ_W (−1)^{|W|} meanProjN(W ∪ (range m \ V))` over the subsets `W ⊆ V`. -/
lemma blockOp_expansion {n : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) (V : Finset ℕ) {Φ : X n → ℝ}
    (hΦ : Continuous Φ) :
    ∀ m ≤ n, Work.BoseFixB2.blockOp ℓ V m Φ
      = fun x => ∑ W ∈ (V ∩ Finset.range m).powerset,
          (-1 : ℝ) ^ W.card * meanProjN ℓ (W ∪ (Finset.range m \ V)) Φ x := by
  intro m
  induction m with
  | zero =>
      intro _
      funext x
      rw [Work.BoseFixB2.blockOp_zero]
      have hset : V ∩ Finset.range 0 = (∅ : Finset ℕ) := by simp
      rw [hset, Finset.powerset_empty, Finset.sum_singleton]
      simp only [Finset.range_zero, Finset.empty_sdiff, Finset.empty_union, Finset.card_empty,
        pow_zero, one_mul]
      exact (congrFun (meanProjN_empty ℓ Φ) x).symm
  | succ m ih =>
      intro hm
      have hmn : m < n := hm
      have ih' := ih (Nat.le_of_lt hmn)
      have hmem : m ∉ V ∩ Finset.range m := fun h =>
        Finset.notMem_range_self (Finset.mem_inter.mp h).2
      rw [Work.BoseFixB2.blockOp_succ V hmn Φ, ih']
      by_cases hmV : m ∈ V
      · rw [if_pos hmV, range_succ_inter_of_mem hmV, range_succ_sdiff_of_mem hmV]
        funext x
        have hR : (∑ W ∈ (insert m (V ∩ Finset.range m)).powerset,
              (-1 : ℝ) ^ W.card * meanProjN ℓ (W ∪ (Finset.range m \ V)) Φ x)
            = (∑ W ∈ (V ∩ Finset.range m).powerset,
                (-1 : ℝ) ^ W.card * meanProjN ℓ (W ∪ (Finset.range m \ V)) Φ x)
              - ∑ W ∈ (V ∩ Finset.range m).powerset,
                (-1 : ℝ) ^ W.card *
                  aP ℓ ⟨m, hmn⟩ (meanProjN ℓ (W ∪ (Finset.range m \ V)) Φ) x := by
          rw [Finset.sum_powerset_insert hmem]
          have hS2 : (∑ t ∈ (V ∩ Finset.range m).powerset,
                (-1 : ℝ) ^ (insert m t).card * meanProjN ℓ (insert m t ∪ (Finset.range m \ V)) Φ x)
              = -∑ t ∈ (V ∩ Finset.range m).powerset,
                  (-1 : ℝ) ^ t.card *
                    aP ℓ ⟨m, hmn⟩ (meanProjN ℓ (t ∪ (Finset.range m \ V)) Φ) x := by
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl (fun W hW => ?_)
            have hmW : m ∉ W := fun hc => hmem ((Finset.mem_powerset.mp hW) hc)
            have hmK : m ∉ W ∪ (Finset.range m \ V) := by
              refine Finset.notMem_union.mpr ⟨hmW, ?_⟩
              simp only [Finset.mem_sdiff, Finset.mem_range, not_and]
              exact fun hlt _ => absurd hlt (by omega)
            rw [Finset.card_insert_of_notMem hmW,
              show insert m W ∪ (Finset.range m \ V) = insert m (W ∪ (Finset.range m \ V)) from
                Finset.insert_union m W (Finset.range m \ V),
              meanProjN_insert (V := W ∪ (Finset.range m \ V)) (k := m) ℓ hℓ hmn hmK hΦ,
              pow_succ]
            ring
          rw [hS2]
          ring
        rw [hR]
        show (∑ W ∈ (V ∩ Finset.range m).powerset,
                (-1 : ℝ) ^ W.card * meanProjN ℓ (W ∪ (Finset.range m \ V)) Φ x)
              - aP ℓ ⟨m, hmn⟩ (fun y => ∑ W ∈ (V ∩ Finset.range m).powerset,
                  (-1 : ℝ) ^ W.card * meanProjN ℓ (W ∪ (Finset.range m \ V)) Φ y) x
            = (∑ W ∈ (V ∩ Finset.range m).powerset,
                (-1 : ℝ) ^ W.card * meanProjN ℓ (W ∪ (Finset.range m \ V)) Φ x)
              - ∑ W ∈ (V ∩ Finset.range m).powerset,
                (-1 : ℝ) ^ W.card *
                  aP ℓ ⟨m, hmn⟩ (meanProjN ℓ (W ∪ (Finset.range m \ V)) Φ) x
        rw [aP_finset_sum hℓ ⟨m, hmn⟩ _ (fun W => (-1 : ℝ) ^ W.card)
          (fun W => meanProjN ℓ (W ∪ (Finset.range m \ V)) Φ)
          (fun W _ => meanProjN_continuous ℓ hℓ _ hΦ) x]
      · rw [if_neg hmV, range_succ_inter_of_notMem hmV, range_succ_sdiff_of_notMem hmV]
        funext x
        show aP ℓ ⟨m, hmn⟩ (fun y => ∑ W ∈ (V ∩ Finset.range m).powerset,
              (-1 : ℝ) ^ W.card * meanProjN ℓ (W ∪ (Finset.range m \ V)) Φ y) x
            = ∑ W ∈ (V ∩ Finset.range m).powerset,
                (-1 : ℝ) ^ W.card *
                  meanProjN ℓ (W ∪ insert m (Finset.range m \ V)) Φ x
        rw [aP_finset_sum hℓ ⟨m, hmn⟩ _ (fun W => (-1 : ℝ) ^ W.card)
          (fun W => meanProjN ℓ (W ∪ (Finset.range m \ V)) Φ)
          (fun W _ => meanProjN_continuous ℓ hℓ _ hΦ) x]
        refine Finset.sum_congr rfl (fun W hW => ?_)
        have hmW : m ∉ W := fun hc => hmem ((Finset.mem_powerset.mp hW) hc)
        have hmK : m ∉ W ∪ (Finset.range m \ V) := by
          refine Finset.notMem_union.mpr ⟨hmW, ?_⟩
          simp only [Finset.mem_sdiff, Finset.mem_range, not_and]
          exact fun hlt _ => absurd hlt (by omega)
        rw [show W ∪ insert m (Finset.range m \ V) = insert m (W ∪ (Finset.range m \ V)) from
          Finset.union_insert m W (Finset.range m \ V),
          meanProjN_insert (V := W ∪ (Finset.range m \ V)) (k := m) ℓ hℓ hmn hmK hΦ]

/-! ## 6. The bridge: `thetaSector` is a joint sector projection -/

lemma tsPreS_sdiff {n : ℕ} (V W : Finset ℕ) :
    tsPreS n (V \ W) = tsPreS n V \ tsPreS n W := by
  ext i
  simp only [mem_tsPreS, Finset.mem_sdiff]

lemma tsPreS_range {n : ℕ} : tsPreS n (Finset.range n) = (Finset.univ : Finset (Fin n)) := by
  ext i
  simp [mem_tsPreS, Finset.mem_range, i.isLt]

lemma tsPreS_sdiff_range {n : ℕ} (S : Finset (Fin n)) :
    tsPreS n (Finset.range n \ tsImS S) = Finset.univ \ S := by
  rw [tsPreS_sdiff, tsPreS_tsImS, tsPreS_range]

lemma tsPreS_card_of_subset_range {n : ℕ} {W : Finset ℕ} (hW : W ⊆ Finset.range n) :
    (tsPreS n W).card = W.card := by
  rw [← tsImS_card (tsPreS n W), tsImS_tsPreS, Finset.inter_eq_left.mpr hW]

lemma tsPreS_injOn {n : ℕ} {W W' : Finset ℕ} (hW : W ⊆ Finset.range n)
    (hW' : W' ⊆ Finset.range n) (h : tsPreS n W = tsPreS n W') : W = W' := by
  have h1 : tsImS (tsPreS n W) = tsImS (tsPreS n W') := by rw [h]
  rwa [tsImS_tsPreS, tsImS_tsPreS, Finset.inter_eq_left.mpr hW,
    Finset.inter_eq_left.mpr hW'] at h1

/-- `range n \ tsImS S` is the natural-number image of the complement slot set. -/
lemma range_sdiff_tsImS {n : ℕ} (S : Finset (Fin n)) :
    Finset.range n \ tsImS S = tsImS (Finset.univ \ S) := by
  rw [← tsPreS_sdiff_range S, tsImS_tsPreS, Finset.inter_eq_left.mpr Finset.sdiff_subset]

/-- Removing a disjoint set after adjoining it is the identity. -/
lemma union_sdiff_of_disjoint {α : Type*} [DecidableEq α] {X S : Finset α} (h : X ∩ S = ∅) :
    (X ∪ S) \ S = X := by
  ext k
  rw [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨h1 | h1, h2⟩
    · exact h1
    · exact absurd h1 h2
  · intro hk
    exact ⟨Or.inl hk, fun hc => by
      have hmem : k ∈ X ∩ S := Finset.mem_inter.mpr ⟨hk, hc⟩
      rw [h] at hmem
      exact Finset.notMem_empty k hmem⟩

/-- `range n` minus its part outside `tsImS S` is `tsImS S`. -/
lemma range_sdiff_range_sdiff {n : ℕ} (S : Finset (Fin n)) :
    Finset.range n \ (Finset.range n \ tsImS S) = tsImS S := by
  ext k
  rw [Finset.mem_sdiff, Finset.mem_sdiff, Finset.mem_range]
  constructor
  · rintro ⟨hkn, h2⟩
    by_contra hk
    exact h2 ⟨hkn, hk⟩
  · intro hk
    exact ⟨Finset.mem_range.mp (tsImS_subset_range S hk), fun h => h.2 hk⟩

/-- **The `θ`-sector is the joint sector projection** with the complementary slot set: the slots
`∉ S` carry the `Q`-projection and those in `S` the `P`-projection. -/
theorem thetaSector_eq_jointProj {n : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) (S : Finset (Fin n))
    {Φ : X n → ℝ} (hΦ : Continuous Φ) :
    thetaSector ℓ S Φ = Work.BoseFixB2.jointProj ℓ (Finset.range n \ tsImS S) Φ := by
  set U : Finset ℕ := Finset.range n \ tsImS S with hUdef
  have hUrange : U ⊆ Finset.range n := by
    rw [hUdef]
    exact Finset.sdiff_subset
  have hcomp : tsPreS n U = Finset.univ \ S := by
    rw [hUdef]
    exact tsPreS_sdiff_range S
  have hImU : tsImS (Finset.univ \ S) = U := by
    rw [hUdef, range_sdiff_tsImS]
  have hA : ∀ x, thetaSector ℓ S Φ x
      = ∑ X ∈ (Finset.univ \ S).powerset,
          (-1 : ℝ) ^ X.card * meanProj ℓ (X ∪ S) Φ x := by
    intro x
    rw [thetaSector]
    refine (Finset.sum_bij (fun X _ => X ∪ S) ?_ ?_ ?_ ?_).symm
    · intro X hX
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, Finset.subset_union_right (s₁ := X) (s₂ := S)⟩
    · intro X1 hX1 X2 hX2 h
      have h1 : X1 ⊆ Finset.univ \ S := Finset.mem_powerset.mp hX1
      have h2 : X2 ⊆ Finset.univ \ S := Finset.mem_powerset.mp hX2
      have hX1 : X1 ∩ S = ∅ := Finset.disjoint_iff_inter_eq_empty.mp
        (Finset.disjoint_of_subset_left h1 (Finset.disjoint_sdiff (s := S) (t := Finset.univ)).symm)
      have hX2 : X2 ∩ S = ∅ := Finset.disjoint_iff_inter_eq_empty.mp
        (Finset.disjoint_of_subset_left h2 (Finset.disjoint_sdiff (s := S) (t := Finset.univ)).symm)
      calc X1 = (X1 ∪ S) \ S := (union_sdiff_of_disjoint hX1).symm
        _ = (X2 ∪ S) \ S := by rw [h]
        _ = X2 := union_sdiff_of_disjoint hX2
    · intro T hT
      rw [Finset.mem_filter] at hT
      refine ⟨T \ S, Finset.mem_powerset.mpr ?_, ?_⟩
      · intro i hi
        rw [Finset.mem_sdiff] at hi
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi.2⟩
      · exact Finset.sdiff_union_of_subset hT.2
    · intro X hX
      have h1 : X ⊆ Finset.univ \ S := Finset.mem_powerset.mp hX
      have hX1 : X ∩ S = ∅ := Finset.disjoint_iff_inter_eq_empty.mp
        (Finset.disjoint_of_subset_left h1 (Finset.disjoint_sdiff (s := S) (t := Finset.univ)).symm)
      have hcard : (X ∪ S).card - S.card = X.card := by
        rw [Finset.card_union_of_disjoint (Finset.disjoint_iff_inter_eq_empty.mpr hX1),
          Nat.add_sub_cancel]
      rw [hcard]
  have hB : ∀ x, Work.BoseFixB2.jointProj ℓ U Φ x
      = ∑ X ∈ (Finset.univ \ S).powerset,
          (-1 : ℝ) ^ X.card * meanProj ℓ (X ∪ S) Φ x := by
    intro x
    have hexp := congrFun (blockOp_expansion ℓ hℓ U hΦ n le_rfl) x
    have hjoint : Work.BoseFixB2.jointProj ℓ U Φ
        = Work.BoseFixB2.blockOp ℓ U n Φ := rfl
    rw [congrFun hjoint x, hexp]
    have h1 : U ∩ Finset.range n = U := Finset.inter_eq_left.mpr hUrange
    have h2 : Finset.range n \ U = tsImS S := by
      rw [hUdef]
      exact range_sdiff_range_sdiff S
    rw [h1, h2]
    refine Finset.sum_bij (fun W _ => tsPreS n W) ?_ ?_ ?_ ?_
    · intro W hW
      refine Finset.mem_powerset.mpr ?_
      have hWU : W ⊆ U := Finset.mem_powerset.mp hW
      rw [← hcomp]
      exact tsPreS_mono hWU
    · intro W1 hW1 W2 hW2 h
      exact tsPreS_injOn (Finset.Subset.trans (Finset.mem_powerset.mp hW1) hUrange)
        (Finset.Subset.trans (Finset.mem_powerset.mp hW2) hUrange) h
    · intro X hX
      refine ⟨tsImS X, Finset.mem_powerset.mpr ?_, ?_⟩
      · rw [← hImU]
        refine Finset.image_subset_iff.mpr (fun i hi => ?_)
        rw [mem_tsImS]
        exact ⟨i, (Finset.mem_powerset.mp hX) hi, rfl⟩
      · rw [tsPreS_tsImS]
    · intro W hW
      have hWU : W ⊆ U := Finset.mem_powerset.mp hW
      have hcard : (tsPreS n W).card = W.card :=
        tsPreS_card_of_subset_range (Finset.Subset.trans hWU hUrange)
      simp only [meanProjN, tsPreS_union, tsPreS_tsImS]
      rw [hcard]
  have hfun : thetaSector ℓ S Φ = Work.BoseFixB2.jointProj ℓ U Φ := by
    funext x
    rw [hA x, hB x]
  exact hfun

/-! ## 7. The pairing of a sector with the state, and the moments of `n₊` -/

/-- A joint sector pairs with the state exactly as with itself: `⟨E_UΦ, Φ⟩ = ‖E_UΦ‖²`. -/
lemma sector_pairing {n : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) {Φ : X n → ℝ} (hΦ : Continuous Φ)
    {U : Finset ℕ} (hU : U ⊆ Finset.range n) :
    (∫ x in abox n ℓ, Work.BoseFixB2.jointProj ℓ U Φ x * Φ x)
      = ∫ x in abox n ℓ, (Work.BoseFixB2.jointProj ℓ U Φ x) ^ 2 := by
  have hres := Work.BoseFixB2.Sector.jointProj_resolution hℓ Φ hΦ
  have hcontU : Continuous (Work.BoseFixB2.jointProj ℓ U Φ) :=
    Work.BoseFixB2.Sector.jointProj_continuous hℓ U hΦ
  have hstep1 : (∫ x in abox n ℓ, Work.BoseFixB2.jointProj ℓ U Φ x * Φ x)
      = ∫ x in abox n ℓ, Work.BoseFixB2.jointProj ℓ U Φ x *
          (∑ W ∈ (Finset.range n).powerset, Work.BoseFixB2.jointProj ℓ W Φ x) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    show Work.BoseFixB2.jointProj ℓ U Φ x * Φ x
      = Work.BoseFixB2.jointProj ℓ U Φ x *
        (∑ W ∈ (Finset.range n).powerset, Work.BoseFixB2.jointProj ℓ W Φ x)
    rw [← congrFun hres x, Finset.sum_apply]
  rw [hstep1]
  let h : Finset ℕ → X n → ℝ := fun W y =>
    Work.BoseFixB2.jointProj ℓ U Φ y * Work.BoseFixB2.jointProj ℓ W Φ y
  have hsum : (fun x : X n => Work.BoseFixB2.jointProj ℓ U Φ x *
        (∑ W ∈ (Finset.range n).powerset, Work.BoseFixB2.jointProj ℓ W Φ x))
      = fun x => ∑ W ∈ (Finset.range n).powerset, h W x := by
    funext x
    rw [Finset.mul_sum]
  rw [hsum]
  have hint : (∫ x in abox n ℓ, ∑ W ∈ (Finset.range n).powerset, h W x)
      = ∑ W ∈ (Finset.range n).powerset, ∫ x in abox n ℓ, h W x :=
    integral_finsetSum _ (fun W hW => integrableOn_abox_of_continuous hℓ
      (hcontU.mul (Work.BoseFixB2.Sector.jointProj_continuous hℓ W hΦ)))
  rw [hint]
  rw [Finset.sum_eq_single U]
  · rw [show (fun x => h U x) = fun x => (Work.BoseFixB2.jointProj ℓ U Φ x) ^ 2 from by
      funext x
      simp only [h]
      ring]
  · intro W hW hne
    refine Work.BoseFixB2.Sector.jointProj_orthogonal hℓ (?_ne) Φ Φ hΦ hΦ
    intro hc
    exact hne (by
      have h1 : U ∩ Finset.range n = U := Finset.inter_eq_left.mpr hU
      have h2 : W ∩ Finset.range n = W :=
        Finset.inter_eq_left.mpr (Finset.mem_powerset.mp hW)
      rw [h1, h2] at hc
      exact hc.symm)
  · intro hUmem
    exact absurd (Finset.mem_powerset.mpr hU) hUmem

/-- The moments of the excitation number expand in the joint sectors. -/
lemma moment_expansion {n : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) {Φ : X n → ℝ} (hΦ : Continuous Φ)
    (k : ℕ) :
    (∫ x in abox n ℓ, Work.BoseBox.nPlusPow ℓ n (2 * k) Φ x * Φ x)
      = ∑ W ∈ (Finset.range n).powerset,
          (W.card : ℝ) ^ (2 * k) *
            ∫ x in abox n ℓ, (Work.BoseFixB2.jointProj ℓ W Φ x) ^ 2 := by
  have hfun : (fun x : X n => Work.BoseBox.nPlusPow ℓ n (2 * k) Φ x * Φ x)
      = fun x => (∑ W ∈ (Finset.range n).powerset,
            (W.card : ℝ) ^ (2 * k) * Work.BoseFixB2.jointProj ℓ W Φ x) * Φ x := by
    funext x
    rw [congrFun (nPlusPow_sector_expansion ℓ hℓ hΦ (2 * k)) x]
  rw [hfun]
  let g : Finset ℕ → X n → ℝ := fun W y =>
    (W.card : ℝ) ^ (2 * k) * (Work.BoseFixB2.jointProj ℓ W Φ y * Φ y)
  have hsum : (fun x : X n => (∑ W ∈ (Finset.range n).powerset,
          (W.card : ℝ) ^ (2 * k) * Work.BoseFixB2.jointProj ℓ W Φ x) * Φ x)
      = fun x => ∑ W ∈ (Finset.range n).powerset, g W x := by
    funext x
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun W _ => by ring)
  rw [hsum]
  have hint : (∫ x in abox n ℓ, ∑ W ∈ (Finset.range n).powerset, g W x)
      = ∑ W ∈ (Finset.range n).powerset, ∫ x in abox n ℓ, g W x :=
    integral_finsetSum _ (fun W hW => integrableOn_abox_of_continuous hℓ
      (continuous_const.mul ((Work.BoseFixB2.Sector.jointProj_continuous hℓ W hΦ).mul hΦ)))
  rw [hint]
  refine Finset.sum_congr rfl (fun W hW => ?_)
  rw [integral_const_mul, sector_pairing ℓ hℓ hΦ (Finset.mem_powerset.mp hW)]

theorem thetaSector_vanish (ℓ : ℝ) (hℓ : 0 < ℓ) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ)
    (hΦc : tsupport Φ ⊆ Submission.BoseGases.abox n ℓ)
    {M : ℝ} (hM : 0 ≤ M)
    (hmom : Work.BoseBox.SpectralNPlusLe ℓ M Φ)
    (S : Finset (Fin n)) (hS : (S.card : ℝ) + M < (n : ℝ)) :
    ∫ x in Submission.BoseGases.abox n ℓ, (Work.BoseBoxFock.thetaSector ℓ S Φ x) ^ 2 = 0 := by
  set U : Finset ℕ := Finset.range n \ tsImS S with hUdef
  have hUsub : U ⊆ Finset.range n := by
    rw [hUdef]
    exact Finset.sdiff_subset
  have hUcard' : U.card = n - S.card := by
    rw [hUdef, Finset.card_sdiff, Finset.card_range,
      Finset.inter_eq_left.mpr (tsImS_subset_range S), tsImS_card]
  have hUcard : (U.card : ℝ) = (n : ℝ) - S.card := by
    rw [hUcard', Nat.cast_sub (by simpa using Finset.card_le_univ S)]
  have hgt : M < (U.card : ℝ) := by
    rw [hUcard]
    linarith [hS]
  have hpos : 0 < (U.card : ℝ) := lt_of_le_of_lt hM hgt
  have hbridge : Work.BoseBoxFock.thetaSector ℓ S Φ = Work.BoseFixB2.jointProj ℓ U Φ := by
    have h := thetaSector_eq_jointProj ℓ hℓ S hΦ
    rwa [← hUdef] at h
  have ha : (∫ x in Submission.BoseGases.abox n ℓ,
      (Work.BoseFixB2.jointProj ℓ U Φ x) ^ 2) = 0 := by
    set a : ℝ := ∫ x in Submission.BoseGases.abox n ℓ,
      (Work.BoseFixB2.jointProj ℓ U Φ x) ^ 2 with hadef
    set B : ℝ := ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 with hBdef
    have ha_nonneg : 0 ≤ a := integral_nonneg (fun x => sq_nonneg _)
    have hkey : ∀ k : ℕ, a ≤ B * (M / (U.card : ℝ)) ^ (2 * k) := by
      intro k
      have hm := hmom (2 * k)
      rw [moment_expansion ℓ hℓ hΦ k] at hm
      have hsingle := Finset.single_le_sum
        (s := (Finset.range n).powerset)
        (f := fun W => (W.card : ℝ) ^ (2 * k) *
          ∫ x in Submission.BoseGases.abox n ℓ,
            (Work.BoseFixB2.jointProj ℓ W Φ x) ^ 2)
        (fun W _ => mul_nonneg (pow_nonneg (Nat.cast_nonneg W.card) _)
          (integral_nonneg (fun x => sq_nonneg _)))
        (Finset.mem_powerset.mpr hUsub)
      have h1 : (U.card : ℝ) ^ (2 * k) * a ≤ M ^ (2 * k) * B := le_trans hsingle hm
      have hdiv : a ≤ M ^ (2 * k) * B / (U.card : ℝ) ^ (2 * k) :=
        (le_div_iff₀ (pow_pos hpos _)).mpr (by rw [mul_comm]; exact h1)
      calc a ≤ M ^ (2 * k) * B / (U.card : ℝ) ^ (2 * k) := hdiv
        _ = B * (M / (U.card : ℝ)) ^ (2 * k) := by rw [div_pow]; ring
    have hr : (M / (U.card : ℝ)) ^ 2 < 1 := by
      have h0 : 0 ≤ M / (U.card : ℝ) := div_nonneg hM (le_of_lt hpos)
      have h1 : M / (U.card : ℝ) < 1 := (div_lt_one hpos).mpr hgt
      nlinarith
    have hpow : Filter.Tendsto (fun k : ℕ => ((M / (U.card : ℝ)) ^ 2) ^ k)
        Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (pow_nonneg (div_nonneg hM (le_of_lt hpos)) 2) hr
    have hlim : Filter.Tendsto (fun k : ℕ => B * ((M / (U.card : ℝ)) ^ 2) ^ k)
        Filter.atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hpow
    have hle : a ≤ 0 := le_of_tendsto_of_tendsto' tendsto_const_nhds hlim
      (fun k => by simpa [pow_mul] using hkey k)
    exact le_antisymm hle ha_nonneg
  rw [hbridge]
  exact ha

end Work.BoseBoxFock

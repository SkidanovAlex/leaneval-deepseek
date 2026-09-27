import Mathlib
import Submission.Work.EKLC6Core.borel_atom_saturated_measurable
import Submission.Work.EKLC6Core.measurableSet_avoid
import Submission.Work.EKLComp.X3Background

/-!
# `Work.EKLC6Core.analyticSet_compl_goodShape`

Let `U ≤ SL₃(ℝ)` be a **closed** subgroup, `A = σ(range b)` a countably generated sub-σ-algebra
of the Borel σ-algebra of `X₃ = SL₃(ℝ)/SL₃(ℤ)`, and `δ, R ∈ ℝ`.  We show that the set of
`y : X₃` at which the *shape*

`shape A U y = {u ∈ U | u • y ∈ atom A y}`

**fails** to satisfy `V δ ∩ U ⊆ shape A U y ⊆ V R` is **analytic** (in the descriptive-set-theoretic
sense, `MeasureTheory.AnalyticSet`).

## The proof

Write `π y := (fun n ↦ decide (y ∈ b n)) : ℕ → Bool`; since `A = σ(range b)`, the `A`-atoms are
exactly the fibres of `π` (`mem_atom_generateFrom_range_iff`), i.e.

`z ∈ atom A y ↔ ∀ n, (z ∈ b n ↔ y ∈ b n)`.

Consequently the *atom graph*

`ZG := {(y,z) ∈ X₃ × X₃ | z ∈ atom A y}`

is Borel — it is `⋂ n, ((b n ×ˢ b n) ∪ ((b n)ᶜ ×ˢ (b n)ᶜ))` — hence analytic, because `X₃` is
Polish.  The two ways in which the "good shape" condition can fail are

`∃ u ∈ V δ ∩ U, u • y ∉ atom A y`  and  `∃ u ∈ U, u ∉ V R, u • y ∈ atom A y`,

and each of these is the image under the (continuous) first projection of the Borel set

`D₁ = {q : X₃ × SL₃ | q.₂ ∈ V δ ∩ U, (q.₁, q.₂ • q.₁) ∉ ZG}`,
`D₂ = {q : X₃ × SL₃ | q.₂ ∈ U ∖ V R, (q.₁, q.₂ • q.₁) ∈ ZG}`

of `X₃ × SL₃` (`U` closed, `V δ` open, and `q ↦ (q.₁, q.₂ • q.₁)` continuous).  Borel sets of a
Polish space are analytic and continuous images of analytic sets are analytic, so the desired
set — the union of the two images — is analytic.

## Why analyticity (rather than Borelness) is what is available

The conditions quantify over the *uncountable* set `V δ ∩ U` (resp. `U`).  This is why one passes
through the Borel *graph* of the atom map in the product `X₃ × SL₃` and then projects: the
projection of a Borel set is analytic but need not be Borel.  This is exactly the dichotomy used
in the analytic-hull step of the plaque-algebra construction (Pisa §7).
-/

open MeasureTheory Set Topology
open Work.EKLContract

set_option linter.style.haveILetI false

namespace Work.EKLC6Core

/-- `V δ` is open, for every real `δ`. -/
private lemma isOpen_V_local (δ : ℝ) : IsOpen (V δ) := by
  have h : V δ = ⋂ i : Fin 3, ⋂ j : Fin 3,
      {g : SL3 | |(g : Matrix (Fin 3) (Fin 3) ℝ) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < δ} := by
    ext g; simp [V]
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    isOpen_lt (by fun_prop) continuous_const

/-- The graph of the atom map of `A = σ(range b)`: pairs `(y, z)` with `z ∈ atom A y`. -/
private def ZGdef (b : ℕ → Set X3) : Set (X3 × X3) :=
  {p | p.2 ∈ atom (MeasurableSpace.generateFrom (Set.range b)) p.1}

/-- Witnesses for the failure of `V δ ∩ U ⊆ shape A U y`: pairs `(y,u)` with `u ∈ V δ ∩ U` but
`u • y ∉ atom A y`. -/
private def D1def (b : ℕ → Set X3) (U : Subgroup SL3) (δ : ℝ) : Set (X3 × SL3) :=
  (Set.univ ×ˢ (V δ ∩ (U : Set SL3))) ∩
    (fun q : X3 × SL3 => (q.1, q.2 • q.1)) ⁻¹' (ZGdef b)ᶜ

/-- Witnesses for the failure of `shape A U y ⊆ V R`: pairs `(y,u)` with `u ∈ U`, `u • y ∈ atom A y`
but `u ∉ V R`. -/
private def D2def (b : ℕ → Set X3) (U : Subgroup SL3) (R : ℝ) : Set (X3 × SL3) :=
  (Set.univ ×ˢ ((U : Set SL3) ∩ (V R)ᶜ)) ∩
    (fun q : X3 × SL3 => (q.1, q.2 • q.1)) ⁻¹' (ZGdef b)

/-- The complement of the "good shape" set is analytic, in the case `A = σ(range b)`. -/
private lemma analyticSet_badShape {b : ℕ → Set X3}
    (hb : ∀ n, MeasurableSet[borel X3] (b n)) (U : Subgroup SL3)
    (hU : IsClosed (U : Set SL3)) (δ R : ℝ) :
    AnalyticSet {y : X3 | ¬ ((V δ ∩ (U : Set SL3)) ⊆
        shape (MeasurableSpace.generateFrom (Set.range b)) U y ∧
      shape (MeasurableSpace.generateFrom (Set.range b)) U y ⊆ V R)} := by
  haveI : PolishSpace X3 := Work.EKLComp.X3Background.2.2.2.1
  haveI : PolishSpace SL3 := Work.EKLContract.Lemmas.polishSpace_specialLinearGroup
  -- The atom graph is Borel (hence analytic, `X₃` being Polish).
  have hZG : MeasurableSet (ZGdef b) := by
    rw [ZGdef]
    have hset : {p : X3 × X3 | p.2 ∈ atom (MeasurableSpace.generateFrom (Set.range b)) p.1}
        = ⋂ n, ((b n ×ˢ b n) ∪ ((b n)ᶜ ×ˢ (b n)ᶜ)) := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union, Set.mem_prod,
        Set.mem_compl_iff]
      rw [mem_atom_generateFrom_range_iff]
      refine forall_congr' fun n => ?_
      rw [iff_iff_and_or_not_and_not]
      tauto
    rw [hset]
    exact MeasurableSet.iInter fun n =>
      ((hb n).prod (hb n)).union ((hb n).compl.prod (hb n).compl)
  have hψ : Measurable (fun q : X3 × SL3 => (q.1, q.2 • q.1)) :=
    Measurable.prodMk measurable_fst
      ((continuous_smul.measurable).comp (Measurable.prodMk measurable_snd measurable_fst))
  have hD1 : MeasurableSet (D1def b U δ) := by
    rw [D1def]
    exact (MeasurableSet.prod MeasurableSet.univ
        ((isOpen_V_local δ).measurableSet.inter hU.measurableSet)).inter
      (hZG.compl.preimage hψ)
  have hD2 : MeasurableSet (D2def b U R) := by
    rw [D2def]
    exact (MeasurableSet.prod MeasurableSet.univ
        (hU.measurableSet.inter (isOpen_V_local R).measurableSet.compl)).inter
      (hZG.preimage hψ)
  have h1 : AnalyticSet (Prod.fst '' (D1def b U δ)) :=
    hD1.analyticSet.image_of_continuous continuous_fst
  have h2 : AnalyticSet (Prod.fst '' (D2def b U R)) :=
    hD2.analyticSet.image_of_continuous continuous_fst
  -- The "bad shape" set is the union of the two projections.
  have hkey : {y : X3 | ¬ ((V δ ∩ (U : Set SL3)) ⊆
        shape (MeasurableSpace.generateFrom (Set.range b)) U y ∧
      shape (MeasurableSpace.generateFrom (Set.range b)) U y ⊆ V R)}
      = Prod.fst '' (D1def b U δ ∪ D2def b U R) := by
    have hmem1 : ∀ q : X3 × SL3, q ∈ D1def b U δ ↔ q.2 ∈ V δ ∧ q.2 ∈ (U : Set SL3) ∧
        q.2 • q.1 ∉ atom (MeasurableSpace.generateFrom (Set.range b)) q.1 := by
      intro q
      simp only [D1def, ZGdef, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
        Set.mem_prod, Set.mem_univ, Set.mem_ofPred_eq, true_and]
      tauto
    have hmem2 : ∀ q : X3 × SL3, q ∈ D2def b U R ↔ q.2 ∈ (U : Set SL3) ∧
        q.2 • q.1 ∈ atom (MeasurableSpace.generateFrom (Set.range b)) q.1 ∧ q.2 ∉ V R := by
      intro q
      simp only [D2def, ZGdef, Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_univ,
        Set.mem_ofPred_eq, Set.mem_compl_iff, true_and]
      tauto
    have hiff : ∀ y : X3, ((V δ ∩ (U : Set SL3)) ⊆
          shape (MeasurableSpace.generateFrom (Set.range b)) U y ∧
          shape (MeasurableSpace.generateFrom (Set.range b)) U y ⊆ V R)
        ↔ ((∀ u, u ∈ V δ → u ∈ (U : Set SL3) →
              u • y ∈ atom (MeasurableSpace.generateFrom (Set.range b)) y) ∧
            (∀ u, u ∈ (U : Set SL3) →
              u • y ∈ atom (MeasurableSpace.generateFrom (Set.range b)) y → u ∈ V R)) := by
      intro y
      simp only [shape, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.subset_def]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun u huV huU => (h1 u ⟨huV, huU⟩).2, fun u huU huA => h2 u ⟨huU, huA⟩⟩
      · rintro ⟨h1, h2⟩
        exact ⟨fun u hu => ⟨hu.2, h1 u hu.1 hu.2⟩, fun u hu => h2 u hu.1 hu.2⟩
    have himg : ∀ y : X3, (y ∈ Prod.fst '' (D1def b U δ ∪ D2def b U R)) ↔
        (∃ u : SL3, u ∈ V δ ∧ u ∈ (U : Set SL3) ∧
            u • y ∉ atom (MeasurableSpace.generateFrom (Set.range b)) y) ∨
        (∃ u : SL3, u ∈ (U : Set SL3) ∧
            u • y ∈ atom (MeasurableSpace.generateFrom (Set.range b)) y ∧ u ∉ V R) := by
      intro y
      rw [Set.mem_image]
      constructor
      · rintro ⟨q, hq, hqy⟩
        rw [Set.mem_union] at hq
        rcases hq with hq | hq
        · rw [hmem1] at hq
          exact Or.inl ⟨q.2, hq.1, hq.2.1, by simpa [hqy] using hq.2.2⟩
        · rw [hmem2] at hq
          exact Or.inr ⟨q.2, hq.1, by simpa [hqy] using hq.2.1, hq.2.2⟩
      · rintro (⟨u, huV, huU, huc⟩ | ⟨u, huU, huA, huc⟩)
        · exact ⟨(y, u), by
            rw [Set.mem_union]; left; rw [hmem1]; exact ⟨huV, huU, by simpa⟩, rfl⟩
        · exact ⟨(y, u), by
            rw [Set.mem_union]; right; rw [hmem2]; exact ⟨huU, by simpa, huc⟩, rfl⟩
    ext y
    simp only [Set.mem_ofPred_eq]
    rw [hiff y, himg y, not_and_or]
    constructor
    · intro h
      rcases h with h | h
      · push Not at h
        obtain ⟨u, huV, huU, huc⟩ := h
        exact Or.inl ⟨u, huV, huU, huc⟩
      · push Not at h
        obtain ⟨u, huU, huA, huc⟩ := h
        exact Or.inr ⟨u, huU, huA, huc⟩
    · intro h
      rcases h with ⟨u, huV, huU, huc⟩ | ⟨u, huU, huA, huc⟩
      · exact Or.inl (not_forall.mpr ⟨u, fun h' => huc (h' huV huU)⟩)
      · exact Or.inr (not_forall.mpr ⟨u, fun h' => huc (h' huU huA)⟩)
  rw [hkey]
  rw [Set.image_union, Set.union_eq_iUnion]
  refine AnalyticSet.iUnion fun c => ?_
  cases c
  · simpa using h2
  · simpa using h1

theorem analyticSet_compl_goodShape {U : Subgroup Work.EKLContract.SL3}
    (hU : IsClosed (U : Set Work.EKLContract.SL3))
    {A : MeasurableSpace Work.EKLContract.X3} {b : ℕ → Set Work.EKLContract.X3}
    (hb : ∀ n, @MeasurableSet Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 (b n))
    (hA : A = MeasurableSpace.generateFrom (Set.range b)) (δ R : ℝ) :
    MeasureTheory.AnalyticSet
      {y : Work.EKLContract.X3 |
        ¬ ((Work.EKLContract.V δ ∩ (U : Set Work.EKLContract.SL3)) ⊆
              Work.EKLContract.shape A U y ∧
            Work.EKLContract.shape A U y ⊆ Work.EKLContract.V R)} := by
  rw [hA]
  exact analyticSet_badShape (b := b) hb U hU δ R

end Work.EKLC6Core

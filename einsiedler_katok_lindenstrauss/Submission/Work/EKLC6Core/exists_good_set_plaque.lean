import Mathlib
import Submission.Work.EKLC6Core.growth_le_atomInfo_sandwich
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLC6Core.measurableSet_avoid
import Submission.Work.EKLC6Core.borel_atom_saturated_measurable
import Submission.Work.EKLC6Core.ae_frequently_of_conull_iUnion
import Submission.Work.EKLComp.X3Background
import Submission.Work.EKLComp.V_hasBasis_nhds_one
import Submission.Work.Topology.analyticSet_isCompact_inner
import Submission.Work.Topology.analyticSet_nullMeasurableSet
import Submission.Work.EKLC6Core.ae_frequently_of_forall_pos_compl
import Submission.Work.EKLC6Core.analyticSet_compl_goodShape

/-!
# `Work.EKLC6Core.exists_good_set_plaque`

The last bookkeeping step between the *geometry* (a plaque algebra `(Z, A)` subordinate to the
contracted horospherical subgroup `U = Uminus t`, with `μ Zᶜ = 0`) and the *analysis* of Pisa §7.34
/ EKL (7): the existence of a countable "good family" `Y k` with radii `δ k`, `R k` on which the
atom shapes are sandwiched between `V (δ k)` and `V (R k)`, and which is visited infinitely often
by almost every orbit.

## The construction

For every scale `(δ, R)` let

`goodShape U A δ R = {y | (V δ ∩ U) ⊆ shape A U y ∧ shape A U y ⊆ V R}`

be the *sandwich set* and let `badShape` be its complement.  Two facts about it:

* **(the plaque condition is eventually satisfied)** every `y ∈ Z` lies in
  `goodShape U A δ R` for all small `δ > 0` and all large `R`
  (`exists_sandwich_of_isPlaqueAlgebra`, directly from `IsPlaqueAlgebra`: the shape is `O ∩ U`
  with `O` open containing `1`, and the shape is entrywise bounded);
* **(the bad set is analytic)** the complement of `goodShape U A δ R` is a countable union of
  projections (onto the second factor of `SL₃(ℝ) × X₃`) of Borel sets, hence *analytic*: the
  membership `z ∈ atom A x` is decidable from the membership pattern in a generating sequence
  `b` of `A` (`borel_atom_saturated_measurable.mem_atom_generateFrom_range_iff`), so
  `(u, y) ↦ (u • y ∈ b n ↔ y ∈ b n)` is Borel.  Analyticity is what makes the sandwich sets
  usable measure-theoretically.

With `δ k = ((k : ℝ) + 1)⁻¹ ↓ 0`, `R k = (k : ℝ) + 1 ↑ ∞`, `S k = badShape U A (δ k) (R k)` and
`G k = (S k)ᶜ`:

* `G` is monotone *increasing* and `Z ⊆ ⋃ k, G k`, so by continuity from below for measures
  (`Monotone.measure_iUnion`; no measurability is needed) `⨆ k, μ (G k) = 1`;
* `S k` is analytic, hence `NullMeasurableSet (S k) μ` (analytic sets are universally
  measurable), which gives `μ (S k) = 1 - μ (G k)`;
* the good family is `Y k := (toMeasurable μ (S k))ᶜ`: it is Borel, it is contained in `G k`
  (so the sandwich holds on it) and `μ (Y k)ᶜ = μ (S k) = 1 - μ (G k)` has infimum `0`;
* Poincaré recurrence (`measure_eventually_mem_le`) applied to the sets `Y k` gives the a.e.
  visit condition.

So no geometry beyond `IsPlaqueAlgebra` is used: the cut/stratification input of
`EKLC6Core/good_family_of_geometry.lean` is *derived* here from the plaque algebra alone.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- The *sandwich set*: points at which the `A`-atom shape is trapped between the `δ`-ball and
the `R`-ball of the identity. -/
private def goodShape (U : Subgroup SL3) (A : MeasurableSpace X3) (δ R : ℝ) : Set X3 :=
  {y | (V δ ∩ (U : Set SL3)) ⊆ shape A U y ∧ shape A U y ⊆ V R}

private theorem mem_goodShape {U : Subgroup SL3} {A : MeasurableSpace X3} {δ R : ℝ} {y : X3} :
    y ∈ goodShape U A δ R ↔
      (V δ ∩ (U : Set SL3)) ⊆ shape A U y ∧ shape A U y ⊆ V R := Iff.rfl

/-- `goodShape` is monotone: shrinking `δ` and growing `R` only makes the sandwich easier. -/
private theorem goodShape_mono {U : Subgroup SL3} {A : MeasurableSpace X3} {δ δ' R R' : ℝ}
    (hδ : δ' ≤ δ) (hR : R ≤ R') : goodShape U A δ R ⊆ goodShape U A δ' R' := by
  intro y hy
  have hV : V δ' ⊆ V δ := fun g hg i j => lt_of_lt_of_le (hg i j) hδ
  have hV' : V R ⊆ V R' := fun g hg i j => lt_of_lt_of_le (hg i j) hR
  exact ⟨Set.inter_subset_inter_left _ hV |>.trans hy.1, hy.2.trans hV'⟩

/-- **Every point of `Z` has a plaque.**  If `A` is a plaque algebra for `U` on `Z`, then at
every `y ∈ Z` the shape is sandwiched between a small `V δ` and a large `V R`. -/
private theorem exists_sandwich_of_isPlaqueAlgebra {U : Subgroup SL3} {A : MeasurableSpace X3}
    {Z : Set X3} (hplq : IsPlaqueAlgebra U Z A) {y : X3} (hy : y ∈ Z) :
    ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ y ∈ goodShape U A δ R := by
  obtain ⟨-, -, ⟨O, hOopen, hOshape⟩, ⟨C, hC⟩⟩ := hplq.2.2.2 y hy
  have hone : (1 : SL3) ∈ shape A U y :=
    ⟨U.one_mem, by rw [one_smul]; exact Set.mem_sInter.mpr fun s hs => hs.2⟩
  have h1O : (1 : SL3) ∈ O := by
    have h : (1 : SL3) ∈ O ∩ (U : Set SL3) := hOshape ▸ hone
    exact h.1
  obtain ⟨δ, hδpos, hδO⟩ :=
    (Work.EKLComp.V_hasBasis_nhds_one.mem_iff).mp (hOopen.mem_nhds h1O)
  have hC1 : (1 : ℝ) ≤ C := by
    have h := hC 1 hone 0 0
    simpa [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply] using h
  refine ⟨δ, C + 2, hδpos, by linarith, ?_, ?_⟩
  · intro u hu
    rw [hOshape]
    exact ⟨hδO hu.1, hu.2⟩
  · intro u hu i j
    have hb : |(u : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ C := hC u hu i j
    have h1 : |((1 : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
      rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
      split <;> simp
    calc |(u : Matrix (Fin 3) (Fin 3) ℝ) i j
            - ((1 : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j|
        = |(u : Matrix (Fin 3) (Fin 3) ℝ) i j
            + -(((1 : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j)| := by ring_nf
      _ ≤ |(u : Matrix (Fin 3) (Fin 3) ℝ) i j|
            + |-(((1 : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j)| := abs_add_le _ _
      _ = |(u : Matrix (Fin 3) (Fin 3) ℝ) i j|
            + |((1 : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j| := by rw [abs_neg]
      _ ≤ C + 1 := add_le_add hb h1
      _ < C + 2 := by linarith

/-- **A generating sequence for a countably generated sub-σ-algebra of the Borel sets.** -/
private theorem exists_gen_seq {A : MeasurableSpace X3} (hA : A ≤ borel X3)
    (hgen : @MeasurableSpace.CountablyGenerated X3 A) :
    ∃ b : ℕ → Set X3, (∀ n, @MeasurableSet X3 instMeasurableSpaceX3 (b n)) ∧
      A = MeasurableSpace.generateFrom (Set.range b) := by
  classical
  letI : MeasurableSpace X3 := A
  haveI : MeasurableSpace.CountablyGenerated X3 := hgen
  refine ⟨MeasurableSpace.natGeneratingSequence X3, ?_, ?_⟩
  · intro n
    exact hA _ (MeasurableSpace.measurableSet_natGeneratingSequence n)
  · exact (MeasurableSpace.generateFrom_natGeneratingSequence X3).symm

theorem exists_good_set_plaque {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplq : Work.EKLContract.IsPlaqueAlgebra (Work.EKLC6Core.Uminus t) Z A) (hZ : μ Zᶜ = 0) :
    ∃ (Y : ℕ → Set Work.EKLContract.X3) (δ R : ℕ → ℝ),
      (∀ k, @MeasurableSet Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 (Y k)) ∧
      (∀ k, 0 < δ k) ∧ (∀ k, 0 < R k) ∧
      (∀ (k : ℕ) (y : Work.EKLContract.X3), y ∈ Y k →
        (Work.EKLContract.V (δ k) ∩ (Work.EKLC6Core.Uminus t : Set Work.EKLContract.SL3)) ⊆
            Work.EKLContract.shape A (Work.EKLC6Core.Uminus t) y ∧
          Work.EKLContract.shape A (Work.EKLC6Core.Uminus t) y ⊆ Work.EKLContract.V (R k)) ∧
      (∀ᵐ x ∂μ, ∃ k : ℕ, ∃ᶠ n in Filter.atTop,
        (Work.EKLContract.aDiag t ^ n) • x ∈ Y k) := by
  classical
  -- the ambient measurable structure of `X₃` is the Borel one (the plaque algebra `A` is a
  -- local instance of class type and would otherwise be captured by type class search)
  letI : MeasurableSpace X3 := instMeasurableSpaceX3
  haveI hT2 : T2Space X3 := Work.EKLComp.X3Background.1
  haveI hSC : SecondCountableTopology X3 := Work.EKLComp.X3Background.2.2.1
  haveI hPol : PolishSpace X3 := Work.EKLComp.X3Background.2.2.2.1
  haveI hSB : StandardBorelSpace X3 := Work.EKLComp.X3Background.2.2.2.2
  -- the contracted horospherical subgroup
  set U : Subgroup SL3 := Uminus t with hUdef
  have hUcl : IsClosed (U : Set SL3) := by
    have h : IsClosed ((Uminus t : Subgroup SL3) : Set SL3) := (Work.EKLC6Core.uminus_isHoro t).1.1
    rwa [← hUdef] at h
  -- a generating sequence of the plaque σ-algebra
  obtain ⟨b, hbmeas, hbgen⟩ := exists_gen_seq (A := A) hplq.1
    (@MeasurableSpace.CountablyGenerated.mk X3 A hplq.2.1)
  -- the scales and the good sets
  let δ : ℕ → ℝ := fun k => ((k : ℝ) + 1)⁻¹
  let R : ℕ → ℝ := fun k => (k : ℝ) + 1
  have hδpos : ∀ k, 0 < δ k := fun k => inv_pos.mpr (by positivity)
  have hRpos : ∀ k, 0 < R k := fun k => by positivity
  let G : ℕ → Set X3 := fun k => goodShape U A (δ k) (R k)
  let S : ℕ → Set X3 := fun k => (G k)ᶜ
  have hSG : ∀ k, S k = {y : X3 | ¬ ((V (δ k) ∩ (U : Set SL3)) ⊆ shape A U y ∧
      shape A U y ⊆ V (R k))} := by
    intro k
    ext y
    simp only [S, G, goodShape, Set.mem_compl_iff, Set.mem_ofPred_eq]
  -- the bad sets are analytic
  have hSana : ∀ k, AnalyticSet (S k) := by
    intro k
    rw [hSG k]
    exact analyticSet_compl_goodShape (U := U) hUcl (A := A) (b := b) hbmeas hbgen
      (δ k) (R k)
  have hNullG : ∀ k, NullMeasurableSet (G k) μ := by
    intro k
    simpa only [S, compl_compl] using
      (Work.Topology.analyticSet_nullMeasurableSet μ (hSana k)).compl
  -- `Z` is conull
  have hZmeas : MeasurableSet Z := hplq.1 Z hplq.2.2.1
  have hZeq : μ Z = 1 := by
    have h := measure_add_measure_compl₀ (μ := μ) hZmeas.nullMeasurableSet
    rw [hZ, add_zero, measure_univ] at h
    exact h
  -- `G` is increasing and covers `Z`
  have hGmono : Monotone G := by
    intro i j hij
    have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    have hδij : δ j ≤ δ i := by
      have h1 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
      have h2 : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by linarith
      simpa only [δ, one_div] using one_div_le_one_div_of_le h1 h2
    have hRij : R i ≤ R j := by
      simp only [R]
      linarith
    exact goodShape_mono hδij hRij
  have hZG : Z ⊆ ⋃ k, G k := by
    intro y hy
    obtain ⟨δy, Ry, hδy, hRy, hyG⟩ :=
      exists_sandwich_of_isPlaqueAlgebra (U := U) (A := A) hplq hy
    obtain ⟨k₁, hk₁⟩ := exists_nat_one_div_lt hδy
    obtain ⟨k₂, hk₂⟩ := exists_nat_gt Ry
    have hδle : δ (max k₁ k₂) ≤ δy := by
      refine le_of_lt (lt_of_le_of_lt ?_ hk₁)
      have h2 : (k₁ : ℝ) + 1 ≤ ((max k₁ k₂ : ℕ) : ℝ) + 1 := by
        have h3 : (k₁ : ℝ) ≤ ((max k₁ k₂ : ℕ) : ℝ) := by
          exact_mod_cast le_max_left k₁ k₂
        linarith
      simpa only [δ, one_div] using
        one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (k₁ : ℝ) + 1) h2
    have hRle : Ry ≤ R (max k₁ k₂) := by
      have h2 : (k₂ : ℝ) ≤ ((max k₁ k₂ : ℕ) : ℝ) := by exact_mod_cast le_max_right k₁ k₂
      simp only [R]
      linarith
    exact Set.mem_iUnion.mpr ⟨max k₁ k₂, goodShape_mono hδle hRle hyG⟩
  have hUnivG : μ (⋃ k, G k) = 1 := by
    refine le_antisymm ?_ ?_
    · calc μ (⋃ k, G k) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    · calc (1 : ENNReal) = μ Z := hZeq.symm
        _ ≤ μ (⋃ k, G k) := measure_mono hZG
  have hsupG : ⨆ k, μ (G k) = 1 := by
    rw [← Monotone.measure_iUnion hGmono, hUnivG]
  -- the measure of the bad set
  have hmeasure : ∀ k, μ (S k) = 1 - μ (G k) := by
    intro k
    have h1 : μ (S k) + μ (G k) = (1 : ENNReal) := by
      rw [add_comm]
      simpa only [S, measure_univ] using measure_add_measure_compl₀ (μ := μ) (hNullG k)
    have hGtop : μ (G k) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (by
        calc μ (G k) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ)
    exact ENNReal.eq_sub_of_add_eq hGtop h1
  -- the good family
  let Y : ℕ → Set X3 := fun k => (toMeasurable μ (S k))ᶜ
  refine ⟨Y, δ, R, ?_, hδpos, hRpos, ?_, ?_⟩
  · intro k
    exact (measurableSet_toMeasurable μ (S k)).compl
  · intro k y hy
    have hyS : y ∈ (S k)ᶜ := fun hys => hy (subset_toMeasurable μ (S k) hys)
    have hyG : y ∈ G k := by simpa only [S, compl_compl] using hyS
    exact mem_goodShape.mp (show y ∈ goodShape U A (δ k) (R k) from hyG)
  · have h0 : ∀ ε : ENNReal, 0 < ε → ∃ k, μ ((Y k)ᶜ) < ε := by
      intro ε hε
      have hlt : 1 - ε < ⨆ k, μ (G k) := by
        rw [hsupG]
        exact ENNReal.sub_lt_self (by simp) (by simp) (ne_of_gt hε)
      obtain ⟨k, hk⟩ := lt_iSup_iff.mp hlt
      refine ⟨k, ?_⟩
      have hcomp : μ ((Y k)ᶜ) = μ (S k) := by
        simp only [Y, compl_compl]
        exact measure_toMeasurable (μ := μ) (S k)
      rw [hcomp, hmeasure k]
      have hGle : μ (G k) ≤ 1 := by
        calc μ (G k) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
      have h2 : (1 : ENNReal) < ε + μ (G k) :=
        ENNReal.lt_add_of_sub_lt_left (Or.inl (by simp)) hk
      exact (ENNReal.sub_lt_iff_lt_left (ne_top_of_le_ne_top (by simp) hGle) hGle).mpr
        (by rwa [add_comm] at h2)
    have hrec := ae_frequently_of_forall_pos_compl (T := fun x : X3 => aDiag t • x)
      hmp (A := Y) (fun k => (measurableSet_toMeasurable μ (S k)).compl) h0
    filter_upwards [hrec] with x hx
    obtain ⟨k, hk⟩ := hx
    exact ⟨k, hk.mono fun n hn => by simpa only [smul_iterate_apply] using hn⟩

end Work.EKLC6Core

end

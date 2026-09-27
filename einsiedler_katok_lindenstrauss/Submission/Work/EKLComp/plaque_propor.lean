import Mathlib
import Submission.Work.EKLComp.LeafAux
import Submission.Work.EKLComp.kernel_restrict
import Submission.Work.EKLComp.weight_pos
import Submission.Work.EKLComp.nested_propor

/-!
# Proportionality of the conditional measures of two plaque algebras

This file proves `Work.EKLComp.plaque_propor`: for two plaque algebras `(Z₁, 𝔪₁)` and `(Z₂, 𝔪₂)`
for the same subgroup `U ≤ SL₃(ℝ)` and a probability measure `μ` on `X₃`, the conditional measures
`condExpKernel (μ|Z₁) 𝔪₁ x` and `condExpKernel (μ|Z₂) 𝔪₂ x` are proportional on the common atom
`[x]_{𝔪₁} ∩ [x]_{𝔪₂}` for `μ`-a.e. `x ∈ Z₁ ∩ Z₂`.

The mathematical route (Pisa §5–6) is

* `plaque_cover`: the atoms of two plaque algebras for the same `U` refine each other up to
  countably many atoms (Pisa Lemma 6.17);
* `nested_propor`: for `𝔪 ⊆ 𝔫`, the conditional measure of `𝔪` restricted to an `𝔫`-atom is a
  multiple of the conditional measure of `𝔫` (nested case of Pisa Prop. 5.17);
* `weight_pos`: the two proportionality constants are non-zero a.e. — the countable refinement is
  what rules out a weight vanishing on a set of positive measure;
* `kernel_restrict`: restricting `μ` to an `𝔪`-measurable set `Z` does not change the
  `𝔪`-conditional kernel on `Z`.

The two lemmas `kernel_comp_self_inline` and `plaque_cover_inline` below are copies of the fleet's
`Work.EKLComp.kernel_comp_self` and `Work.EKLComp.plaque_cover` (proved in this workspace); they
are inlined privately here because the modules holding them import this file, so importing them
would close an import cycle.
-/

open MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal
open Work.EKLContract (X3)

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLComp

/-! ## 0. Inlined auxiliary lemmas (tower property and countable refinement) -/

private lemma exists_countable_piSystem_borel :
    ∃ C : Set (Set X3), C.Countable ∧ IsPiSystem C ∧ (Set.univ : Set X3) ∈ C ∧
      (∀ s ∈ C, MeasurableSet s) ∧
      (borel X3 : MeasurableSpace X3) = MeasurableSpace.generateFrom C := by
  let A : ℕ → Set X3 := MeasurableSpace.natGeneratingSequence X3
  have hgen : MeasurableSpace.generateFrom (Set.range A)
      = (borel X3 : MeasurableSpace X3) := MeasurableSpace.generateFrom_natGeneratingSequence X3
  refine ⟨Set.range (fun t : Finset ℕ => ⋂ n ∈ t, A n), countable_range _, ?_, ⟨∅, ?_⟩, ?_, ?_⟩
  · rintro s ⟨t₁, rfl⟩ s' ⟨t₂, rfl⟩ -
    refine ⟨t₁ ∪ t₂, ?_⟩
    ext x
    simp only [Set.mem_iInter, Set.mem_inter_iff, Finset.mem_union]
    constructor
    · intro h; exact ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩
    · rintro ⟨h₁, h₂⟩ i (hi | hi)
      · exact h₁ i hi
      · exact h₂ i hi
  · ext x; simp
  · rintro s ⟨t, rfl⟩
    exact MeasurableSet.biInter t.countable_toSet (fun n _ =>
      MeasurableSpace.measurableSet_natGeneratingSequence n)
  · rw [← hgen]
    apply le_antisymm
    · apply MeasurableSpace.generateFrom_mono
      rintro s ⟨n, rfl⟩
      exact ⟨{n}, by ext x; simp⟩
    · apply MeasurableSpace.generateFrom_le
      rintro s ⟨t, rfl⟩
      exact MeasurableSet.biInter t.countable_toSet (fun n _ =>
        MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self n))

/-- For a fixed measurable `s`, the composition of the two conditional kernels agrees with the
conditional kernel of `𝔪` almost everywhere. -/
private lemma condExpKernel_bind_apply_ae (μ : Measure X3) [IsFiniteMeasure μ] [StandardBorelSpace X3]
    (𝔪 𝔫 : SigAlg) (hm : 𝔪.m ≤ borel X3) (hn : 𝔫.m ≤ borel X3) (hmn : 𝔪.m ≤ 𝔫.m)
    {s : Set X3} (hs : MeasurableSet s) :
    ∀ᵐ x ∂μ, (Measure.bind (condExpKernel μ 𝔪.m x) (condExpKernel μ 𝔫.m)) s
      = (condExpKernel μ 𝔪.m x) s := by
  -- the two ingredients: measurability of the integrand and its bound by `1`
  have hK₂ : Measurable (fun y : X3 => condExpKernel μ 𝔫.m y) :=
    (condExpKernel μ 𝔫.m).measurable.mono hn le_rfl
  have hmeas₂ : Measurable (fun y : X3 => (condExpKernel μ 𝔫.m y).real s) :=
    (((condExpKernel μ 𝔫.m).measurable_coe hs).mono hn le_rfl).ennreal_toReal
  have hbound : ∀ y : X3, ‖(condExpKernel μ 𝔫.m y).real s‖ ≤ 1 := fun y => by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (by rw [Measure.real_def]; exact ENNReal.toReal_nonneg), Measure.real_def]
    calc ((condExpKernel μ 𝔫.m y) s).toReal
        ≤ ((condExpKernel μ 𝔫.m y) Set.univ).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ s))
      _ = 1 := by rw [measure_univ]; simp
  have hfr_int : Integrable (fun y : X3 => (condExpKernel μ 𝔫.m y).real s) μ :=
    Integrable.of_bound hmeas₂.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbound)
  -- the tower property, in the form needed
  have h5 : (fun x : X3 => ∫ y, (condExpKernel μ 𝔫.m y).real s ∂(condExpKernel μ 𝔪.m x)) =ᵐ[μ]
      (fun x : X3 => (condExpKernel μ 𝔪.m x).real s) := by
    have h1 : μ[(fun y : X3 => (condExpKernel μ 𝔫.m y).real s) | 𝔪.m] =ᵐ[μ]
        fun x => ∫ y, (condExpKernel μ 𝔫.m y).real s ∂(condExpKernel μ 𝔪.m x) :=
      condExp_ae_eq_integral_condExpKernel hm hfr_int
    have h2 : (fun y : X3 => (condExpKernel μ 𝔫.m y).real s) =ᵐ[μ]
        (fun y => μ[s.indicator (fun _ => (1 : ℝ)) | 𝔫.m] y) :=
      condExpKernel_ae_eq_condExp hn hs
    have h3 : μ[(fun y => μ[s.indicator (fun _ => (1 : ℝ)) | 𝔫.m] y) | 𝔪.m]
        =ᵐ[μ] μ[s.indicator (fun _ => (1 : ℝ)) | 𝔪.m] := condExp_condExp_of_le hmn hn
    have h4 : μ[(fun y : X3 => (condExpKernel μ 𝔫.m y).real s) | 𝔪.m] =ᵐ[μ]
        μ[(fun y => μ[s.indicator (fun _ => (1 : ℝ)) | 𝔫.m] y) | 𝔪.m] := condExp_congr_ae h2
    exact h1.symm.trans (h4.trans (h3.trans (condExpKernel_ae_eq_condExp hm hs).symm))
  filter_upwards [h5] with x hx
  -- convert the ℕ∞-valued statement into the real one
  rw [Measure.bind_apply hs hK₂.aemeasurable]
  have hofreal : ∀ b : X3, (condExpKernel μ 𝔫.m b) s
      = ENNReal.ofReal ((condExpKernel μ 𝔫.m b).real s) := fun b => by
    rw [Measure.real_def]
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  simp_rw [hofreal]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [hx, Measure.real_def]
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  · haveI : IsFiniteMeasure (condExpKernel μ 𝔪.m x) := inferInstance
    exact Integrable.of_bound hmeas₂.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbound)
  · filter_upwards with y
    rw [Measure.real_def]; exact ENNReal.toReal_nonneg

private theorem kernel_comp_self_inline (μ : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsFiniteMeasure μ] [StandardBorelSpace Work.EKLContract.X3]
    (𝔪 𝔫 : Work.EKLComp.SigAlg) (hm : 𝔪.m ≤ borel Work.EKLContract.X3)
    (hn : 𝔫.m ≤ borel Work.EKLContract.X3) (hmn : 𝔪.m ≤ 𝔫.m) :
    ∀ᵐ x ∂μ, ProbabilityTheory.condExpKernel μ 𝔪.m x =
      MeasureTheory.Measure.bind (ProbabilityTheory.condExpKernel μ 𝔪.m x)
        (ProbabilityTheory.condExpKernel μ 𝔫.m) := by
  obtain ⟨C, hCcnt, hCpi, hCuniv, hCmeas, hCgen⟩ := exists_countable_piSystem_borel
  haveI hcount : Countable ↥C := hCcnt.to_subtype
  have hae : ∀ s ∈ C, ∀ᵐ x ∂μ,
      (Measure.bind (condExpKernel μ 𝔪.m x) (condExpKernel μ 𝔫.m)) s
        = (condExpKernel μ 𝔪.m x) s :=
    fun s hs => condExpKernel_bind_apply_ae μ 𝔪 𝔫 hm hn hmn (hCmeas s hs)
  have hall : ∀ᵐ x ∂μ, ∀ s : ↥C,
      (Measure.bind (condExpKernel μ 𝔪.m x) (condExpKernel μ 𝔫.m)) (s : Set X3)
        = (condExpKernel μ 𝔪.m x) (s : Set X3) :=
    ae_all_iff.mpr fun s => hae s s.2
  filter_upwards [hall] with x hx
  exact Measure.ext_of_generateFrom_of_iUnion (μ := condExpKernel μ 𝔪.m x)
    (ν := Measure.bind (condExpKernel μ 𝔪.m x) (condExpKernel μ 𝔫.m))
    C (fun _ => Set.univ) hCgen hCpi (by ext x; simp) (fun _ => hCuniv)
    (fun _ => by rw [measure_univ]; exact ENNReal.one_ne_top)
    (fun s hs => (hx ⟨s, hs⟩).symm)
private lemma plaque_cover_aux (U : Subgroup Work.EKLContract.SL3)
    (Z₁ Z₂ : Set Work.EKLContract.X3) (m₁ m₂ : MeasurableSpace Work.EKLContract.X3)
    (h₁ : Work.EKLContract.IsPlaqueAlgebra U Z₁ m₁)
    (h₂ : Work.EKLContract.IsPlaqueAlgebra U Z₂ m₂) :
    ∀ x ∈ Z₁, ∃ s : Set (Set Work.EKLContract.X3), s.Countable ∧
        (∀ t ∈ s, ∃ y ∈ Z₁ ∩ Z₂,
          t = Work.EKLContract.atom m₁ y ∩ Work.EKLContract.atom m₂ y) ∧
        Work.EKLContract.atom m₁ x ∩ (Z₁ ∩ Z₂) ⊆ ⋃₀ s := by
  intro x hx1

  obtain ⟨hZatom1, horb1, -, -⟩ := h₁.2.2.2 x hx1
  -- `I` indexes the elements `u ∈ shape m₁ U x` with `u • x ∈ Z₂`.
  let I : Set Work.EKLContract.SL3 :=
    {u : Work.EKLContract.SL3 | u ∈ U ∧ u • x ∈ Work.EKLContract.atom m₁ x ∧ u • x ∈ Z₂}
  -- The shape of the second plaque algebra at `u • x` is relatively open in `U`.
  have hshape : ∀ i : I, ∃ O : Set Work.EKLContract.SL3, IsOpen O ∧
      Work.EKLContract.shape m₂ U ((i : Work.EKLContract.SL3) • x) =
        O ∩ (U : Set Work.EKLContract.SL3) := by
    intro i
    exact (h₂.2.2.2 ((i : Work.EKLContract.SL3) • x) i.2.2.2).2.2.1
  choose O hOopen hOshape using hshape
  -- `1 ∈ O i`, since `1 • (i • x) = i • x` lies in the atom of `i • x`.
  have hone : ∀ i : I, (1 : Work.EKLContract.SL3) ∈ O i := by
    intro i
    have h1 : (1 : Work.EKLContract.SL3) ∈
        Work.EKLContract.shape m₂ U ((i : Work.EKLContract.SL3) • x) := by
      refine ⟨Subgroup.one_mem U, ?_⟩
      simpa using Work.EKLContract.mem_atom m₂ ((i : Work.EKLContract.SL3) • x)
    rw [hOshape i] at h1
    exact h1.1
  -- The covering sets are the images of `O i` under right multiplication by `i`.
  have hGopen : ∀ i : I,
      IsOpen ((fun g : Work.EKLContract.SL3 => g * (i : Work.EKLContract.SL3)) '' (O i)) := by
    intro i
    exact (Homeomorph.mulRight (i : Work.EKLContract.SL3)).isOpenMap (O i) (hOopen i)
  -- The parameter set of the points of `[x]_{m₁} ∩ (Z₁ ∩ Z₂)` inside `U`.
  let P : Set Work.EKLContract.SL3 :=
    {s : Work.EKLContract.SL3 |
      s ∈ U ∧ s • x ∈ Work.EKLContract.atom m₁ x ∩ (Z₁ ∩ Z₂)}
  have hPcover : P ⊆ ⋃ i : I,
      (fun g : Work.EKLContract.SL3 => g * (i : Work.EKLContract.SL3)) '' (O i) := by
    intro s hs
    have hsU : s ∈ U := hs.1
    have hsA : s • x ∈ Work.EKLContract.atom m₁ x ∩ (Z₁ ∩ Z₂) := hs.2
    have hsI : s ∈ I := ⟨hsU, hsA.1, hsA.2.2⟩
    refine Set.mem_iUnion.mpr ⟨⟨s, hsI⟩, ?_⟩
    exact ⟨1, hone ⟨s, hsI⟩, by simp⟩
  -- Lindelöf: countably many of the (relatively open) sets `W u` cover `P`.
  obtain ⟨r, hrc, hPsub⟩ :=
    (HereditarilyLindelofSpace.isLindelof P).elim_countable_subcover
      (fun i : I => (fun g : Work.EKLContract.SL3 => g * (i : Work.EKLContract.SL3)) '' (O i))
      hGopen hPcover
  refine ⟨Set.range (fun i : r => Work.EKLContract.atom m₁ ((i : Work.EKLContract.SL3) • x) ∩
      Work.EKLContract.atom m₂ ((i : Work.EKLContract.SL3) • x)), ?_, ?_, ?_⟩
  · haveI : Countable r := hrc.to_subtype
    exact Set.countable_range _
  · rintro t ⟨i, rfl⟩
    exact ⟨(i : Work.EKLContract.SL3) • x, ⟨hZatom1 i.1.2.2.1, i.1.2.2.2⟩, rfl⟩
  · intro a ha
    -- Write `a = s • x` with `s ∈ U`.
    obtain ⟨s, hsU, hsx⟩ := horb1 ha.1
    have hsx' : s • x = a := hsx
    have hsP : s ∈ P := ⟨hsU, by rw [hsx']; exact ha⟩
    obtain ⟨i, hir, hi⟩ := Set.mem_iUnion₂.mp (hPsub hsP)
    obtain ⟨g, hgO, hgeq⟩ := hi
    have hgeq' : g * (i : Work.EKLContract.SL3) = s := hgeq
    refine Set.mem_sUnion.mpr ⟨Work.EKLContract.atom m₁ ((i : Work.EKLContract.SL3) • x) ∩
        Work.EKLContract.atom m₂ ((i : Work.EKLContract.SL3) • x),
      ⟨⟨i, hir⟩, rfl⟩, ?_⟩
    refine ⟨?_, ?_⟩
    · rw [Work.EKLComp.atom_eq_of_mem m₁ i.2.2.1]
      exact ha.1
    · rw [← hsx', ← hgeq', mul_smul]
      have hgU : g ∈ U := by
        have h1 : g = s * (i : Work.EKLContract.SL3)⁻¹ := by rw [← hgeq']; group
        rw [h1]; exact U.mul_mem hsU (U.inv_mem i.2.1)
      have hgin : g ∈ Work.EKLContract.shape m₂ U ((i : Work.EKLContract.SL3) • x) := by
        rw [hOshape i]; exact ⟨hgO, hgU⟩
      exact hgin.2

/-! ## 1. The join of two countably generated σ-algebras -/

lemma countablyGen_sup {m n : MeasurableSpace Work.EKLContract.X3}
    (hm : Work.EKLComp.CountablyGen m) (hn : Work.EKLComp.CountablyGen n) :
    Work.EKLComp.CountablyGen (m ⊔ n) := by
  obtain ⟨bm, hbmc, hbm⟩ := hm
  obtain ⟨bn, hbnc, hbn⟩ := hn
  exact ⟨bm ∪ bn, hbmc.union hbnc, by
    rw [hbm, hbn, MeasurableSpace.generateFrom_sup_generateFrom]⟩

/-! ## 2. The cover hypothesis of `weight_pos` (Pisa 6.17)

The countable refinement `plaque_cover_aux` supplies, for every `x` in the first domain, a
countable family of pieces `[y]_{m₁} ∩ [y]_{m₂}` covering `[x]_{m₁} ∩ (Z₁ ∩ Z₂)`.  For
`weight_pos` the pieces must be of the form `[y]_𝔪 ∩ [y]_𝔫` for the *join* `𝔫 = 𝔪₁ ⊔ 𝔪₂`, and the
cover must be available for *every* `x` (a point outside `Z₁` has an empty cover, because its
`𝔪₁`-atom is disjoint from the `𝔪₁`-measurable set `Z₁`). -/

private lemma cover_of_plaque (U : Subgroup Work.EKLContract.SL3)
    (Z Z' Y : Set Work.EKLContract.X3) (hY : Y = Z ∩ Z')
    (m m' n : MeasurableSpace Work.EKLContract.X3) (hn : n = m ⊔ m')
    (h : Work.EKLContract.IsPlaqueAlgebra U Z m)
    (h' : Work.EKLContract.IsPlaqueAlgebra U Z' m')
    (hgen : Work.EKLComp.CountablyGen m) (hgen' : Work.EKLComp.CountablyGen m')
    (hraw : ∀ x ∈ Z, ∃ s : Set (Set Work.EKLContract.X3), s.Countable ∧
        (∀ t ∈ s, ∃ y ∈ Y, t = Work.EKLContract.atom m y ∩ Work.EKLContract.atom m' y) ∧
        Work.EKLContract.atom m x ∩ Y ⊆ ⋃₀ s) :
    ∀ x ∈ Z, ∃ s : Set (Set Work.EKLContract.X3), s.Countable ∧
        (∀ t ∈ s, ∃ y ∈ Y, t = Work.EKLContract.atom m y ∩ Work.EKLContract.atom n y) ∧
        (∀ t ∈ s, t ⊆ Y) ∧
        Work.EKLContract.atom m x ∩ Y ⊆ ⋃₀ s := by
  intro x hx
  obtain ⟨s, hsc, hform, hcov⟩ := hraw x hx
  refine ⟨s, hsc, ?_, ?_, hcov⟩
  · intro t ht
    obtain ⟨y, hy, hty⟩ := hform t ht
    exact ⟨y, hy, by
      rw [hty, hn, Work.EKLComp.atom_join m m' hgen hgen' y,
        Set.inter_eq_right.mpr Set.inter_subset_left]⟩
  · intro t ht
    obtain ⟨y, hy, hty⟩ := hform t ht
    have hy' : y ∈ Z ∩ Z' := hY ▸ hy
    rw [hty, hY]
    exact Set.inter_subset_inter ((h.2.2.2 y hy'.1).1) ((h'.2.2.2 y hy'.2).1)

private lemma cover_all (U : Subgroup Work.EKLContract.SL3)
    (Z Z' Y : Set Work.EKLContract.X3) (hY : Y = Z ∩ Z')
    (m m' n : MeasurableSpace Work.EKLContract.X3) (hn : n = m ⊔ m')
    (h : Work.EKLContract.IsPlaqueAlgebra U Z m)
    (h' : Work.EKLContract.IsPlaqueAlgebra U Z' m')
    (hgen : Work.EKLComp.CountablyGen m) (hgen' : Work.EKLComp.CountablyGen m')
    (hraw : ∀ x ∈ Z, ∃ s : Set (Set Work.EKLContract.X3), s.Countable ∧
        (∀ t ∈ s, ∃ y ∈ Y, t = Work.EKLContract.atom m y ∩ Work.EKLContract.atom m' y) ∧
        Work.EKLContract.atom m x ∩ Y ⊆ ⋃₀ s) :
    ∀ x : Work.EKLContract.X3, ∃ s : Set (Set Work.EKLContract.X3), s.Countable ∧
        (∀ t ∈ s, ∃ y ∈ Y, t = Work.EKLContract.atom m y ∩ Work.EKLContract.atom n y) ∧
        (∀ t ∈ s, t ⊆ Y) ∧
        Work.EKLContract.atom m x ∩ Y ⊆ ⋃₀ s := by
  intro x
  by_cases hx : x ∈ Z
  · exact cover_of_plaque U Z Z' Y hY m m' n hn h h' hgen hgen' hraw x hx
  · refine ⟨∅, Set.countable_empty, by simp, by simp, ?_⟩
    intro y hy
    have hyZ : y ∈ Z := (hY ▸ hy.2).1
    exact absurd (Work.EKLComp.mem_of_mem_atom_of_mem m (h.2.2.1) hy.1 hyZ) hx

/-! ## 3. The assembly of the proportionality -/

/-- The proportionality of the two conditional measures, given the nested identities of Pisa
Prop. 5.17 for the pairs `(𝔪₁, 𝔫)` and `(𝔪₂, 𝔫)` with `𝔫 = 𝔪₁ ⊔ 𝔪₂`.

Everything else is supplied here: the restriction `kernel_restrict` (to replace the
`𝔫`-conditional kernel of `μ|Zᵢ` by that of `μ`), the countable cover `plaque_cover_aux` (through
`cover_all`), and the positivity of the two weights `weight_pos`. -/
private theorem plaque_propor_aux (U : Subgroup Work.EKLContract.SL3)
    (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    [StandardBorelSpace Work.EKLContract.X3] (Z₁ Z₂ : Set Work.EKLContract.X3)
    (𝔪₁ 𝔪₂ : Work.EKLComp.SigAlg)
    (h₁ : Work.EKLContract.IsPlaqueAlgebra U Z₁ 𝔪₁.m)
    (h₂ : Work.EKLContract.IsPlaqueAlgebra U Z₂ 𝔪₂.m)
    (hnested₁ : ∀ᵐ x ∂(μ.restrict Z₁),
      (ProbabilityTheory.condExpKernel (μ.restrict Z₁) 𝔪₁.m x).restrict
          (Work.EKLContract.atom (𝔪₁.m ⊔ 𝔪₂.m) x) =
        ProbabilityTheory.condExpKernel (μ.restrict Z₁) 𝔪₁.m x
            (Work.EKLContract.atom (𝔪₁.m ⊔ 𝔪₂.m) x) •
          (ProbabilityTheory.condExpKernel (μ.restrict Z₁) (𝔪₁.m ⊔ 𝔪₂.m) x).restrict
            (Work.EKLContract.atom (𝔪₁.m ⊔ 𝔪₂.m) x))
    (hnested₂ : ∀ᵐ x ∂(μ.restrict Z₂),
      (ProbabilityTheory.condExpKernel (μ.restrict Z₂) 𝔪₂.m x).restrict
          (Work.EKLContract.atom (𝔪₁.m ⊔ 𝔪₂.m) x) =
        ProbabilityTheory.condExpKernel (μ.restrict Z₂) 𝔪₂.m x
            (Work.EKLContract.atom (𝔪₁.m ⊔ 𝔪₂.m) x) •
          (ProbabilityTheory.condExpKernel (μ.restrict Z₂) (𝔪₁.m ⊔ 𝔪₂.m) x).restrict
            (Work.EKLContract.atom (𝔪₁.m ⊔ 𝔪₂.m) x)) :
    ∀ᵐ x ∂μ, x ∈ Z₁ ∩ Z₂ →
      Work.EKLComp.ProporOn (ProbabilityTheory.condExpKernel (μ.restrict Z₁) 𝔪₁.m x)
        (ProbabilityTheory.condExpKernel (μ.restrict Z₂) 𝔪₂.m x)
        (Work.EKLContract.atom 𝔪₁.m x ∩ Work.EKLContract.atom 𝔪₂.m x) := by
  classical
  have hm₁ : 𝔪₁.m ≤ borel X3 := h₁.1
  have hgen₁ : Work.EKLComp.CountablyGen 𝔪₁.m := h₁.2.1
  have hZ₁meas : 𝔪₁.m.MeasurableSet' Z₁ := h₁.2.2.1
  have hm₂ : 𝔪₂.m ≤ borel X3 := h₂.1
  have hgen₂ : Work.EKLComp.CountablyGen 𝔪₂.m := h₂.2.1
  have hZ₂meas : 𝔪₂.m.MeasurableSet' Z₂ := h₂.2.2.1
  have hZ₁borel : MeasurableSet Z₁ := hm₁ Z₁ hZ₁meas
  have hZ₂borel : MeasurableSet Z₂ := hm₂ Z₂ hZ₂meas
  have hYmeas : MeasurableSet (Z₁ ∩ Z₂) := hZ₁borel.inter hZ₂borel
  have hgenn : Work.EKLComp.CountablyGen (𝔪₁.m ⊔ 𝔪₂.m) := countablyGen_sup hgen₁ hgen₂
  have hnm : 𝔪₁.m ⊔ 𝔪₂.m ≤ borel X3 := sup_le hm₁ hm₂
  have hjoin : ∀ y : X3, Work.EKLContract.atom (𝔪₁.m ⊔ 𝔪₂.m) y =
      Work.EKLContract.atom 𝔪₁.m y ∩ Work.EKLContract.atom 𝔪₂.m y :=
    fun y => Work.EKLComp.atom_join 𝔪₁.m 𝔪₂.m hgen₁ hgen₂ y
  -- `μ|Zᵢ` has the same `𝔫`-conditional kernel as `μ` on `Zᵢ`
  have hsup₁set : ∀ s : Set X3, 𝔪₁.m.MeasurableSet' s → (𝔪₁.m ⊔ 𝔪₂.m).MeasurableSet' s :=
    MeasurableSpace.le_def.mp le_sup_left
  have hsup₂set : ∀ s : Set X3, 𝔪₂.m.MeasurableSet' s → (𝔪₁.m ⊔ 𝔪₂.m).MeasurableSet' s :=
    MeasurableSpace.le_def.mp le_sup_right
  have hresn₁ : ∀ᵐ x ∂μ, x ∈ Z₁ →
      ProbabilityTheory.condExpKernel (μ.restrict Z₁) (𝔪₁.m ⊔ 𝔪₂.m) x =
        ProbabilityTheory.condExpKernel μ (𝔪₁.m ⊔ 𝔪₂.m) x :=
    (MeasureTheory.ae_restrict_iff' hZ₁borel).mp
      (Work.EKLComp.kernel_restrict μ ⟨𝔪₁.m ⊔ 𝔪₂.m⟩ hnm Z₁ (hsup₁set Z₁ hZ₁meas))
  have hresn₂ : ∀ᵐ x ∂μ, x ∈ Z₂ →
      ProbabilityTheory.condExpKernel (μ.restrict Z₂) (𝔪₁.m ⊔ 𝔪₂.m) x =
        ProbabilityTheory.condExpKernel μ (𝔪₁.m ⊔ 𝔪₂.m) x :=
    (MeasureTheory.ae_restrict_iff' hZ₂borel).mp
      (Work.EKLComp.kernel_restrict μ ⟨𝔪₁.m ⊔ 𝔪₂.m⟩ hnm Z₂ (hsup₂set Z₂ hZ₂meas))
  have hnest₁ : ∀ᵐ x ∂μ, x ∈ Z₁ →
      (ProbabilityTheory.condExpKernel (μ.restrict Z₁) 𝔪₁.m x).restrict
          (Work.EKLContract.atom (𝔪₁.m ⊔ 𝔪₂.m) x) =
        ProbabilityTheory.condExpKernel (μ.restrict Z₁) 𝔪₁.m x
            (Work.EKLContract.atom (𝔪₁.m ⊔ 𝔪₂.m) x) •
          (ProbabilityTheory.condExpKernel μ (𝔪₁.m ⊔ 𝔪₂.m) x).restrict
            (Work.EKLContract.atom (𝔪₁.m ⊔ 𝔪₂.m) x) := by
    have h0 := (MeasureTheory.ae_restrict_iff' hZ₁borel).mp hnested₁
    filter_upwards [h0, hresn₁] with x h0x hresx
    intro hxZ
    rw [h0x hxZ, hresx hxZ]
  have hnest₂ : ∀ᵐ x ∂μ, x ∈ Z₂ →
      (ProbabilityTheory.condExpKernel (μ.restrict Z₂) 𝔪₂.m x).restrict
          (Work.EKLContract.atom (𝔪₁.m ⊔ 𝔪₂.m) x) =
        ProbabilityTheory.condExpKernel (μ.restrict Z₂) 𝔪₂.m x
            (Work.EKLContract.atom (𝔪₁.m ⊔ 𝔪₂.m) x) •
          (ProbabilityTheory.condExpKernel μ (𝔪₁.m ⊔ 𝔪₂.m) x).restrict
            (Work.EKLContract.atom (𝔪₁.m ⊔ 𝔪₂.m) x) := by
    have h0 := (MeasureTheory.ae_restrict_iff' hZ₂borel).mp hnested₂
    filter_upwards [h0, hresn₂] with x h0x hresx
    intro hxZ
    rw [h0x hxZ, hresx hxZ]
  -- the countable covers, in the form required by `weight_pos`
  have hraw₁ : ∀ x ∈ Z₁, ∃ s : Set (Set X3), s.Countable ∧
      (∀ t ∈ s, ∃ y ∈ Z₁ ∩ Z₂,
        t = Work.EKLContract.atom 𝔪₁.m y ∩ Work.EKLContract.atom 𝔪₂.m y) ∧
      Work.EKLContract.atom 𝔪₁.m x ∩ (Z₁ ∩ Z₂) ⊆ ⋃₀ s :=
    fun x hx => plaque_cover_aux U Z₁ Z₂ 𝔪₁.m 𝔪₂.m h₁ h₂ x hx
  have hraw₂ : ∀ x ∈ Z₂, ∃ s : Set (Set X3), s.Countable ∧
      (∀ t ∈ s, ∃ y ∈ Z₁ ∩ Z₂,
        t = Work.EKLContract.atom 𝔪₂.m y ∩ Work.EKLContract.atom 𝔪₁.m y) ∧
      Work.EKLContract.atom 𝔪₂.m x ∩ (Z₁ ∩ Z₂) ⊆ ⋃₀ s := by
    intro x hx
    obtain ⟨s, hsc, hform, hcov⟩ := plaque_cover_aux U Z₂ Z₁ 𝔪₂.m 𝔪₁.m h₂ h₁ x hx
    refine ⟨s, hsc, ?_, ?_⟩
    · intro t ht
      obtain ⟨y, hy, hty⟩ := hform t ht
      exact ⟨y, ⟨hy.2, hy.1⟩, hty⟩
    · intro y hy
      exact hcov ⟨hy.1, hy.2.2, hy.2.1⟩
  have hcover₁ : ∀ x : X3, ∃ s : Set (Set X3), s.Countable ∧
      (∀ t ∈ s, ∃ y ∈ Z₁ ∩ Z₂,
        t = Work.EKLContract.atom 𝔪₁.m y ∩ Work.EKLContract.atom (𝔪₁.m ⊔ 𝔪₂.m) y) ∧
      (∀ t ∈ s, t ⊆ Z₁ ∩ Z₂) ∧
      Work.EKLContract.atom 𝔪₁.m x ∩ (Z₁ ∩ Z₂) ⊆ ⋃₀ s :=
    cover_all U Z₁ Z₂ (Z₁ ∩ Z₂) rfl 𝔪₁.m 𝔪₂.m (𝔪₁.m ⊔ 𝔪₂.m) rfl h₁ h₂ hgen₁ hgen₂ hraw₁
  have hcover₂ : ∀ x : X3, ∃ s : Set (Set X3), s.Countable ∧
      (∀ t ∈ s, ∃ y ∈ Z₁ ∩ Z₂,
        t = Work.EKLContract.atom 𝔪₂.m y ∩ Work.EKLContract.atom (𝔪₁.m ⊔ 𝔪₂.m) y) ∧
      (∀ t ∈ s, t ⊆ Z₁ ∩ Z₂) ∧
      Work.EKLContract.atom 𝔪₂.m x ∩ (Z₁ ∩ Z₂) ⊆ ⋃₀ s :=
    cover_all U Z₂ Z₁ (Z₁ ∩ Z₂) (Set.inter_comm Z₁ Z₂) 𝔪₂.m 𝔪₁.m (𝔪₁.m ⊔ 𝔪₂.m)
      (by rw [sup_comm]) h₂ h₁ hgen₂ hgen₁ hraw₂
  -- positivity of the two weights
  have hpos₁ : ∀ᵐ x ∂μ, x ∈ Z₁ ∩ Z₂ →
      0 < ProbabilityTheory.condExpKernel (μ.restrict Z₁) 𝔪₁.m x
            (Work.EKLContract.atom (𝔪₁.m ⊔ 𝔪₂.m) x) := by
    have h0 := Work.EKLComp.weight_pos (μ.restrict Z₁) 𝔪₁ ⟨𝔪₁.m ⊔ 𝔪₂.m⟩ hm₁ hnm
      le_sup_left hgen₁ hgenn (Y := Z₁ ∩ Z₂) hYmeas hcover₁
    have h1 := (MeasureTheory.ae_restrict_iff' hZ₁borel).mp h0
    filter_upwards [h1] with x hx
    intro hxY
    exact hx hxY.1 hxY
  have hpos₂ : ∀ᵐ x ∂μ, x ∈ Z₁ ∩ Z₂ →
      0 < ProbabilityTheory.condExpKernel (μ.restrict Z₂) 𝔪₂.m x
            (Work.EKLContract.atom (𝔪₁.m ⊔ 𝔪₂.m) x) := by
    have h0 := Work.EKLComp.weight_pos (μ.restrict Z₂) 𝔪₂ ⟨𝔪₁.m ⊔ 𝔪₂.m⟩ hm₂ hnm
      le_sup_right hgen₂ hgenn (Y := Z₁ ∩ Z₂) hYmeas hcover₂
    have h1 := (MeasureTheory.ae_restrict_iff' hZ₂borel).mp h0
    filter_upwards [h1] with x hx
    intro hxY
    exact hx hxY.2 hxY
  -- conclusion
  filter_upwards [hnest₁, hnest₂, hpos₁, hpos₂] with x hx1 hx2 hp1 hp2
  intro hxY
  have hA : Work.EKLContract.atom (𝔪₁.m ⊔ 𝔪₂.m) x =
      Work.EKLContract.atom 𝔪₁.m x ∩ Work.EKLContract.atom 𝔪₂.m x := hjoin x
  rw [← hA]
  let w₁ : ℝ≥0∞ := ProbabilityTheory.condExpKernel (μ.restrict Z₁) 𝔪₁.m x
    (Work.EKLContract.atom (𝔪₁.m ⊔ 𝔪₂.m) x)
  let w₂ : ℝ≥0∞ := ProbabilityTheory.condExpKernel (μ.restrict Z₂) 𝔪₂.m x
    (Work.EKLContract.atom (𝔪₁.m ⊔ 𝔪₂.m) x)
  let V : Measure X3 := (ProbabilityTheory.condExpKernel μ (𝔪₁.m ⊔ 𝔪₂.m) x).restrict
    (Work.EKLContract.atom (𝔪₁.m ⊔ 𝔪₂.m) x)
  have h1' : (ProbabilityTheory.condExpKernel (μ.restrict Z₁) 𝔪₁.m x).restrict
      (Work.EKLContract.atom (𝔪₁.m ⊔ 𝔪₂.m) x) = w₁ • V := hx1 hxY.1
  have h2' : (ProbabilityTheory.condExpKernel (μ.restrict Z₂) 𝔪₂.m x).restrict
      (Work.EKLContract.atom (𝔪₁.m ⊔ 𝔪₂.m) x) = w₂ • V := hx2 hxY.2
  have hp1' : 0 < w₁ := hp1 hxY
  have hp2' : 0 < w₂ := hp2 hxY
  haveI : IsProbabilityMeasure (ProbabilityTheory.condExpKernel (μ.restrict Z₁) 𝔪₁.m x) :=
    ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure x
  haveI : IsProbabilityMeasure (ProbabilityTheory.condExpKernel (μ.restrict Z₂) 𝔪₂.m x) :=
    ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure x
  have hw₁lt : w₁ < ⊤ :=
    calc w₁ ≤ (ProbabilityTheory.condExpKernel (μ.restrict Z₁) 𝔪₁.m x) Set.univ :=
          measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ < ⊤ := ENNReal.one_lt_top
  have hw₂lt : w₂ < ⊤ :=
    calc w₂ ≤ (ProbabilityTheory.condExpKernel (μ.restrict Z₂) 𝔪₂.m x) Set.univ :=
          measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ < ⊤ := ENNReal.one_lt_top
  show ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
    (ProbabilityTheory.condExpKernel (μ.restrict Z₂) 𝔪₂.m x).restrict
        (Work.EKLContract.atom (𝔪₁.m ⊔ 𝔪₂.m) x) =
      c • (ProbabilityTheory.condExpKernel (μ.restrict Z₁) 𝔪₁.m x).restrict
        (Work.EKLContract.atom (𝔪₁.m ⊔ 𝔪₂.m) x)
  refine ⟨w₂ * w₁⁻¹, ?_, ?_, ?_⟩
  · exact mul_ne_zero (ne_of_gt hp2') (ENNReal.inv_ne_zero.mpr (ne_of_lt hw₁lt))
  · exact ENNReal.mul_ne_top (ne_of_lt hw₂lt) (ENNReal.inv_ne_top.mpr (ne_of_gt hp1'))
  · have hscal : w₁⁻¹ * w₁ = 1 := ENNReal.inv_mul_cancel (ne_of_gt hp1') (ne_of_lt hw₁lt)
    rw [h2', h1', smul_smul, mul_assoc, hscal, mul_one]

/-! ## 4. The target theorem -/

/-- **Pisa Prop. 5.17 / EKL 6.3 (proportionality of two plaque systems).**  For two plaque
algebras `(Z₁, 𝔪₁)`, `(Z₂, 𝔪₂)` for the same subgroup `U ≤ SL₃(ℝ)` and a probability measure `μ`,
the conditional measures of `μ|Z₁` and `μ|Z₂` are proportional on the common atom
`[x]_{𝔪₁} ∩ [x]_{𝔪₂}`, for `μ`-a.e. `x ∈ Z₁ ∩ Z₂`.

The nested case (`nested_propor`) is applied to the two pairs `(𝔪ᵢ, 𝔫)` with the join
`𝔫 = 𝔪₁ ⊔ 𝔪₂`, the tower property being supplied by `kernel_comp_self_inline`; the countable
refinement of the two plaque algebras is `plaque_cover_aux`, and the positivity of the two
weights is `weight_pos`. -/
theorem plaque_propor (U : Subgroup Work.EKLContract.SL3)
    (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    [StandardBorelSpace Work.EKLContract.X3] (Z₁ Z₂ : Set Work.EKLContract.X3)
    (𝔪₁ 𝔪₂ : Work.EKLComp.SigAlg)
    (h₁ : Work.EKLContract.IsPlaqueAlgebra U Z₁ 𝔪₁.m)
    (h₂ : Work.EKLContract.IsPlaqueAlgebra U Z₂ 𝔪₂.m) :
    ∀ᵐ x ∂μ, x ∈ Z₁ ∩ Z₂ →
      Work.EKLComp.ProporOn (ProbabilityTheory.condExpKernel (μ.restrict Z₁) 𝔪₁.m x)
        (ProbabilityTheory.condExpKernel (μ.restrict Z₂) 𝔪₂.m x)
        (Work.EKLContract.atom 𝔪₁.m x ∩ Work.EKLContract.atom 𝔪₂.m x) := by
  have hm₁ : 𝔪₁.m ≤ borel X3 := h₁.1
  have hm₂ : 𝔪₂.m ≤ borel X3 := h₂.1
  have hgenn : Work.EKLComp.CountablyGen (𝔪₁.m ⊔ 𝔪₂.m) :=
    countablyGen_sup h₁.2.1 h₂.2.1
  have hnm : 𝔪₁.m ⊔ 𝔪₂.m ≤ borel X3 := sup_le hm₁ hm₂
  refine plaque_propor_aux U μ Z₁ Z₂ 𝔪₁ 𝔪₂ h₁ h₂ ?_ ?_
  · exact Work.EKLComp.nested_propor (μ.restrict Z₁) 𝔪₁ ⟨𝔪₁.m ⊔ 𝔪₂.m⟩ hm₁ hnm le_sup_left
      hgenn (kernel_comp_self_inline (μ.restrict Z₁) 𝔪₁ ⟨𝔪₁.m ⊔ 𝔪₂.m⟩ hm₁ hnm le_sup_left)
  · exact Work.EKLComp.nested_propor (μ.restrict Z₂) 𝔪₂ ⟨𝔪₁.m ⊔ 𝔪₂.m⟩ hm₂ hnm le_sup_right
      hgenn (kernel_comp_self_inline (μ.restrict Z₂) 𝔪₂ ⟨𝔪₁.m ⊔ 𝔪₂.m⟩ hm₂ hnm le_sup_right)

end Work.EKLComp

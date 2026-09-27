import Mathlib
import Submission.Work.EKLC6Core.C6Aux

/-!
# Convergence of the conditional probabilities of the atoms of a refining sequence

Let `μ` be an `A`-invariant probability on `X₃`, `U` a horospherical subgroup, `ν` a leafwise
system (`IsLeafwise μ U ν X'`), `S` a plaque algebra (`IsPlaqueAlgebra U Z S.m`) which is
`aDiag t`-descending (`comap (aDiag t ·) S.m ≤ S.m`), and let `P n` be a sequence of finite
partitions whose atoms shrink to the atoms of `S.m`
(`⋂ n, [x]_{partSigma (P n)} = [x]_{S.m}`).

Then for `μ`-a.e. `x` the numbers

`atomCondProb μ S t (P n) x = E[1_{[x]_{P n}} | comap (aDiag t ·) S.m](x)`

are positive, decrease in `n`, and converge to

`ν x (shape S.m U x) / ν x (shape (comap (aDiag t ·) S.m) U x)`.

The two ingredients are:

* the `condexp` field of `IsLeafwise` (`Work.EKLC6Core.condExp_shape_eq_pullback`) which computes
  the conditional expectation against the pulled-back plaque algebra as the `ν x`-average over
  the shape `shape (comap (aDiag t ·) S.m) U x`, turning each `atomCondProb` into the `ν x`-ratio
  of two sets;
* continuity from above for the decreasing sequence of sets `{u | u • x ∈ [x]_{P n}}`, isolated
  in the elementary lemma `Work.EKLC6Core.antitone_tendsto_ratio`.
-/

open MeasureTheory Filter
open scoped ENNReal MeasureTheory

noncomputable section

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## The pulled-back σ-algebra -/

/-- The σ-algebra `comap (aDiag t ·) S.m` occurring in the definition of `atomCondProb`, as a
named (reducible) abbreviation so that the main theorem and its proof agree literally. -/
abbrev comapV (S : Work.EKLRelCross.MSAlg) (t : Fin 3 → ℝ) : MeasurableSpace X3 :=
  MeasurableSpace.comap (fun y : X3 => aDiag t • y) S.m

/-! ## Atoms of finite partitions, and monotonicity of `partSigma` -/

/-- A smaller σ-algebra has larger atoms. -/
theorem atom_antitone {m₁ m₂ : MeasurableSpace X3} (h : m₁ ≤ m₂) (x : X3) :
    atom m₂ x ⊆ atom m₁ x :=
  Set.sInter_subset_sInter (fun s hs => ⟨h s hs.1, hs.2⟩)

/-- If `Q` refines `P` then `partSigma P ≤ partSigma Q`. -/
theorem partSigma_mono {P Q : FinPart X3} (h : Refines Q P) : partSigma P ≤ partSigma Q := by
  apply MeasurableSpace.generateFrom_le
  rintro t ⟨i, rfl⟩
  have hEq : P.parts i = ⋃ j : {j : Fin Q.n // Q.parts j ⊆ P.parts i}, Q.parts j := by
    ext z
    simp only [Set.mem_iUnion, Subtype.exists, exists_prop]
    constructor
    · intro hz
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (by rw [Q.cover]; trivial : z ∈ ⋃ j, Q.parts j)
      refine ⟨j, ?_, hj⟩
      obtain ⟨j', hj'⟩ := h j
      have hz' : z ∈ P.parts j' := hj' hj
      have : j' = i := by
        by_contra hne
        exact (Set.disjoint_left.mp (P.disjoint hne) hz' hz)
      rwa [this] at hj'
    · rintro ⟨j, hji, hzj⟩
      exact hji hzj
  rw [hEq]
  exact MeasurableSet.iUnion (fun j =>
    MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self j.1))

/-- The atoms of `partSigma P` are exactly the parts of `P`. -/
theorem atom_partSigma_eq_part (P : FinPart X3) (x : X3) (i : Fin P.n) (hx : x ∈ P.parts i) :
    atom (partSigma P) x = P.parts i := by
  classical
  let f : X3 → (Fin P.n → Bool) := fun z j => decide (z ∈ P.parts j)
  have hle : partSigma P ≤ MeasurableSpace.comap f ⊤ := by
    apply MeasurableSpace.generateFrom_le
    rintro t ⟨i, rfl⟩
    exact ⟨{b : Fin P.n → Bool | b i = true}, trivial, by ext z; simp [f]⟩
  have hatom : atom (MeasurableSpace.comap f ⊤) x = f ⁻¹' {f x} := by
    rw [atom]
    ext y
    simp only [Set.mem_sInter, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      exact h (f ⁻¹' {f x}) ⟨MeasurableSpace.measurableSet_comap.mpr ⟨{f x}, trivial, rfl⟩, rfl⟩
    · intro h t ht
      obtain ⟨u, -, rfl⟩ := MeasurableSpace.measurableSet_comap.mp ht.1
      show f y ∈ u
      rw [h]; exact ht.2
  have hpre : f ⁻¹' {f x} = P.parts i := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      have h' : f y i = true := by
        rw [congrFun h i]
        simp [f, hx]
      simpa [f, decide_eq_true_iff] using h'
    · intro hy
      funext j
      simp only [f]
      by_cases hxj : x ∈ P.parts j
      · have hji : j = i := by
          by_contra hne
          exact Set.disjoint_left.mp (P.disjoint hne) hxj hx
        rw [hji, decide_eq_true hy, decide_eq_true hx]
      · have hyj : y ∉ P.parts j := by
          intro hyj
          have hji : j = i := by
            by_contra hne
            exact Set.disjoint_left.mp (P.disjoint hne) hyj hy
          rw [hji] at hxj
          exact hxj hx
        rw [decide_eq_false hyj, decide_eq_false hxj]
  refine Set.Subset.antisymm ?_ ?_
  · rw [atom]
    exact Set.sInter_subset_of_mem
      ⟨MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self i), hx⟩
  · rw [← hpre, ← hatom]
    exact Set.sInter_subset_sInter (fun s hs => ⟨hle s hs.1, hs.2⟩)

/-! ## The elementary measure-theoretic core -/

/-- **Continuity from above for ratios.**  If `W` has finite `ν`-measure and `T n` is a
decreasing sequence of measurable sets with intersection `Tlim`, then the ratios
`ν (W ∩ T n) / ν W` decrease and converge to `ν (W ∩ Tlim) / ν W`. -/
theorem antitone_tendsto_ratio {ν : Measure SL3} {W : Set SL3} (hW : ν W < ⊤)
    {T : ℕ → Set SL3} {Tlim : Set SL3} (hWm : MeasurableSet W)
    (hTm : ∀ n, MeasurableSet (T n)) (hTanti : Antitone T) (hTint : (⋂ n, T n) = Tlim) :
    Antitone (fun n : ℕ => (ν (W ∩ T n)).toReal / (ν W).toReal) ∧
      Tendsto (fun n : ℕ => (ν (W ∩ T n)).toReal / (ν W).toReal) atTop
        (nhds ((ν (W ∩ Tlim)).toReal / (ν W).toReal)) := by
  have hantiS : Antitone (fun n : ℕ => W ∩ T n) :=
    fun a b hab => Set.inter_subset_inter_right W (hTanti hab)
  have hantiM : Antitone (fun n : ℕ => ν (W ∩ T n)) := by
    refine antitone_nat_of_succ_le (fun n => ?_)
    exact measure_mono (Set.inter_subset_inter_right W (hTanti (Nat.le_succ n)))
  have hWtop : ν W ≠ ⊤ := hW.ne
  have hfin : ∃ i, ν (W ∩ T i) ≠ ⊤ :=
    ⟨0, ne_top_of_le_ne_top hWtop (measure_mono Set.inter_subset_left)⟩
  have hnull : ∀ n, NullMeasurableSet (W ∩ T n) ν :=
    fun n => (hWm.inter (hTm n)).nullMeasurableSet
  have hInterEq : (⨅ n, ν (W ∩ T n)) = ν (W ∩ Tlim) := by
    rw [← hantiS.measure_iInter hnull hfin, ← Set.inter_iInter, hTint]
  have hfinT : ν (W ∩ Tlim) ≠ ⊤ :=
    ne_top_of_le_ne_top hWtop (measure_mono Set.inter_subset_left)
  have hlim : Tendsto (fun n : ℕ => (ν (W ∩ T n)).toReal) atTop
      (nhds ((ν (W ∩ Tlim)).toReal)) := by
    have h1 : Tendsto (fun n : ℕ => ν (W ∩ T n)) atTop (nhds (ν (W ∩ Tlim))) := by
      rw [← hInterEq]
      exact tendsto_atTop_iInf hantiM
    have h2 := (ENNReal.tendsto_toReal hfinT).comp h1
    exact h2
  refine ⟨?_, ?_⟩
  · refine antitone_nat_of_succ_le (fun n => ?_)
    refine div_le_div_of_nonneg_right ?_ ENNReal.toReal_nonneg
    exact ENNReal.toReal_mono
      (ne_top_of_le_ne_top hWtop (measure_mono Set.inter_subset_left))
      (measure_mono (Set.inter_subset_inter_right W (hTanti (Nat.le_succ n))))
  · have := hlim.div_const ((ν W).toReal)
    exact this

/-! ## The main theorem -/

theorem tendsto_atomCondProb {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} {t : Fin 3 → ℝ}
    (hL : Work.EKLContract.IsLeafwise μ U ν X') (hU : Work.EKLContract.IsHoro U)
    (hAinv : Work.EKLContract.IsAInvariant μ)
    (S : Work.EKLRelCross.MSAlg) {Z : Set Work.EKLContract.X3}
    (hplaq : Work.EKLContract.IsPlaqueAlgebra U Z S.m)
    (hdec : MeasurableSpace.comap (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y) S.m ≤ S.m)
    (hZ : μ Zᶜ = 0)
    {P : ℕ → Work.EKLContract.FinPart Work.EKLContract.X3}
    (hPle : ∀ n, Work.EKLContract.partSigma (P n) ≤ S.m)
    (hPmono : ∀ n, Work.EKLContract.Refines (P (n + 1)) (P n))
    (hPatom : ∀ x : Work.EKLContract.X3,
      (⋂ n, Work.EKLContract.atom (Work.EKLContract.partSigma (P n)) x) =
        Work.EKLContract.atom S.m x) :
    ∀ᵐ x ∂μ, Antitone (fun n : ℕ => Work.EKLC6Core.atomCondProb μ S t (P n) x) ∧
      (∀ n : ℕ, 0 < Work.EKLC6Core.atomCondProb μ S t (P n) x) ∧
      0 < (ν x (Work.EKLContract.shape S.m U x)).toReal ∧
      Filter.Tendsto (fun n : ℕ => Work.EKLC6Core.atomCondProb μ S t (P n) x) Filter.atTop
        (nhds ((ν x (Work.EKLContract.shape S.m U x)).toReal /
          (ν x (Work.EKLContract.shape (MeasurableSpace.comap
            (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y) S.m) U x)).toReal)) := by
  classical
  -- ### Step 0: basic a.e. facts
  have hAZ : MeasurableSet Z := hplaq.1 Z hplaq.2.2.1
  have hTZ : μ ((fun y : X3 => aDiag t • y) ⁻¹' Z)ᶜ = 0 := by
    rw [← Set.preimage_compl]
    rw [(hAinv t).measure_preimage hAZ.compl.nullMeasurableSet]
    exact hZ
  have haeX' : ∀ᵐ x ∂μ, x ∈ X' := MeasureTheory.ae_iff.mpr hL.conull
  have haeZ : ∀ᵐ x ∂μ, x ∈ Z := MeasureTheory.ae_iff.mpr hZ
  have haeZ' : ∀ᵐ x ∂μ, x ∈ (fun y : X3 => aDiag t • y) ⁻¹' Z :=
    MeasureTheory.ae_iff.mpr hTZ
  -- ### Step 1: the `condexp` of the indicator of a part, as a leafwise ratio
  have hpair : ∀ (n : ℕ) (i : Fin (P n).n), ∀ᵐ x ∂μ,
      condExp (comapV S t) μ (((P n).parts i).indicator (fun _ => (1 : ℝ))) x =
        (ν x (shape (comapV S t) U x ∩ {u : SL3 | u • x ∈ (P n).parts i})).toReal /
          (ν x (shape (comapV S t) U x)).toReal := by
    intro n i
    have hf : Measurable (((P n).parts i).indicator (fun _ => (1 : ℝ))) :=
      Measurable.indicator measurable_const ((P n).measurable i)
    have hb : ∃ C, ∀ y, |(((P n).parts i).indicator (fun _ => (1 : ℝ))) y| ≤ C := by
      refine ⟨1, fun y => ?_⟩
      by_cases hy : y ∈ (P n).parts i
      · simp [Set.indicator_of_mem hy]
      · simp [Set.indicator_of_notMem hy]
    filter_upwards [condExp_shape_eq_pullback hU hL hplaq t (hAinv t) hZ _ hf hb,
      haeZ'] with x hx hxZ'
    have hW : MeasurableSet (shape (comapV S t) U x) :=
      measurableSet_shape_of_plaque hU (isPlaqueAlgebra_comap hU t hplaq) hxZ'
    rw [hx, setIntegral_indicator_smul hW ((P n).measurable i) x]
  have hpairall : ∀ᵐ x ∂μ, ∀ (n : ℕ) (i : Fin (P n).n),
      condExp (comapV S t) μ (((P n).parts i).indicator (fun _ => (1 : ℝ))) x =
        (ν x (shape (comapV S t) U x ∩ {u : SL3 | u • x ∈ (P n).parts i})).toReal /
          (ν x (shape (comapV S t) U x)).toReal := by
    have h := ae_all_iff.mpr (fun p : (Σ n : ℕ, Fin (P n).n) => hpair p.1 p.2)
    filter_upwards [h] with x hx n i
    exact hx ⟨n, i⟩
  -- ### Step 2: the master identity, atom-wise
  have hmain : ∀ᵐ x ∂μ, ∀ n : ℕ, atomCondProb μ S t (P n) x =
      (ν x (shape (comapV S t) U x
        ∩ {u : SL3 | u • x ∈ atom (partSigma (P n)) x})).toReal /
        (ν x (shape (comapV S t) U x)).toReal := by
    filter_upwards [hpairall] with x hx
    intro n
    obtain ⟨i₀, hi₀⟩ : ∃ i, x ∈ (P n).parts i := by
      have : x ∈ ⋃ i, (P n).parts i := by rw [(P n).cover]; trivial
      simpa using this
    have hsum : (∑ i : Fin (P n).n, ((P n).parts i).indicator
          (fun _ => condExp (comapV S t) μ (((P n).parts i).indicator (fun _ => (1 : ℝ))) x) x)
        = condExp (comapV S t) μ (((P n).parts i₀).indicator (fun _ => (1 : ℝ))) x := by
      rw [Finset.sum_eq_single_of_mem
        (f := fun i : Fin (P n).n => ((P n).parts i).indicator
          (fun _ => condExp (comapV S t) μ (((P n).parts i).indicator (fun _ => (1 : ℝ))) x) x)
        i₀ (Finset.mem_univ i₀) (fun i _ hne => Set.indicator_of_notMem
          (fun hxi => hne (by
            by_contra h
            exact (Set.disjoint_left.mp ((P n).disjoint h) hxi) hi₀)) _)]
      exact Set.indicator_of_mem hi₀ _
    rw [atomCondProb_apply, hsum, hx n i₀, atom_partSigma_eq_part (P n) x i₀ hi₀]
  -- ### Step 3: pointwise conclusion
  filter_upwards [hmain, haeX', haeZ, haeZ'] with x hx hxX' hxZ hxZ'
  have hWm : MeasurableSet (shape (comapV S t) U x) :=
    measurableSet_shape_of_plaque hU (isPlaqueAlgebra_comap hU t hplaq) hxZ'
  obtain ⟨hWpos, hWfin⟩ :=
    shape_mass_pos_and_lt_top_of_plaque hU hL (isPlaqueAlgebra_comap hU t hplaq) hxX' hxZ'
  obtain ⟨hSpos, hSfin⟩ := shape_mass_pos_and_lt_top_of_plaque hU hL hplaq hxX' hxZ
  have hshapeSub : shape S.m U x ⊆ shape (comapV S t) U x :=
    fun u hu => ⟨hu.1, atom_antitone hdec x hu.2⟩
  have hWcap : shape (comapV S t) U x ∩ {u : SL3 | u • x ∈ atom S.m x} = shape S.m U x := by
    ext u
    constructor
    · rintro ⟨⟨huU, -⟩, hu'⟩
      exact ⟨huU, hu'⟩
    · intro hu
      exact ⟨⟨hu.1, atom_antitone hdec x hu.2⟩, hu.2⟩
  have hTmeas : ∀ n : ℕ, MeasurableSet {u : SL3 | u • x ∈ atom (partSigma (P n)) x} := by
    intro n
    obtain ⟨i, hi⟩ : ∃ i, x ∈ (P n).parts i := by
      have : x ∈ ⋃ i, (P n).parts i := by rw [(P n).cover]; trivial
      simpa using this
    rw [atom_partSigma_eq_part (P n) x i hi]
    exact ((P n).measurable i).preimage (by measurability)
  have hTanti : Antitone (fun n : ℕ => {u : SL3 | u • x ∈ atom (partSigma (P n)) x}) := by
    refine antitone_nat_of_succ_le (fun n u hu => ?_)
    exact atom_antitone (partSigma_mono (hPmono n)) x hu
  have hTint : (⋂ n : ℕ, {u : SL3 | u • x ∈ atom (partSigma (P n)) x})
      = {u : SL3 | u • x ∈ atom S.m x} := by
    ext u
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rw [← hPatom x, Set.mem_iInter]
  obtain ⟨hAntiRatio, hLimRatio⟩ :=
    antitone_tendsto_ratio (ν := ν x) (W := shape (comapV S t) U x)
      (T := fun n : ℕ => {u : SL3 | u • x ∈ atom (partSigma (P n)) x})
      (Tlim := {u : SL3 | u • x ∈ atom S.m x}) hWfin hWm hTmeas hTanti hTint
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b hab
    show atomCondProb μ S t (P b) x ≤ atomCondProb μ S t (P a) x
    rw [hx b, hx a]
    exact hAntiRatio hab
  · intro n
    rw [hx n]
    apply div_pos
    · apply ENNReal.toReal_pos
      · refine ne_of_gt (lt_of_lt_of_le hSpos (measure_mono ?_))
        intro u hu
        exact ⟨hshapeSub hu, atom_antitone (hPle n) x hu.2⟩
      · exact ne_top_of_le_ne_top hWfin.ne (measure_mono Set.inter_subset_left)
    · exact ENNReal.toReal_pos hWpos.ne' hWfin.ne
  · exact ENNReal.toReal_pos hSpos.ne' hSfin.ne
  · have hcongr : (fun n : ℕ => (ν x (shape (comapV S t) U x
          ∩ {u : SL3 | u • x ∈ atom (partSigma (P n)) x})).toReal
            / (ν x (shape (comapV S t) U x)).toReal)
        = fun n : ℕ => atomCondProb μ S t (P n) x := funext fun n => (hx n).symm
    rw [hcongr, hWcap] at hLimRatio
    exact hLimRatio

end Work.EKLC6Core

import Mathlib
import Submission.Work.EKLRelCross.LeafCtor
import Submission.Work.EKLRelCross.ae_pairfree_of_ae_free
import Submission.Work.EKLRelCross.measure_domain_ne_zero
import Submission.Work.EKLC7.LeafwiseGeom

/-!
# `Work.EKLRelCross.flowerData_of_localFlower`

From the *local* flower input `Work.EKLRelCross.LocalFlowerInput U` (Pisa 6.7 + 6.9–6.15 in the
"one flower per free point" form: near every point with free `U`-orbit there is a plaque algebra
whose atoms contain the whole `V R`-plaque of every point of the free part of an open
neighbourhood) and the hypothesis that `U`-orbits are `μ`-a.e. free, we build the *bundled*
flower data `Work.EKLRelCross.FlowerData U μ` (Pisa Def. 6.14 / Cor. 6.15): for every level
`k ∈ ℕ` countably many plaque algebras `(Z k i, m k i)` with measurable bases `G k i` of
positive-measure domains, on which the shape contains `V (k+3) ∩ U`, whose bases cover a.e.

## The construction

* `flowers_at_radius` is the countable extraction at a *fixed* radius `R > 0` (the standard
  second-countable-basis argument, as in `Work.EKLRelCross.flower_family`): let

  `S = {x | x is pair-free and every open neighbourhood of x has positive μ-measure}`,

  a conull set (`ae_pairfree_of_ae_free` + `Work.EKLC7.ae_isOpen_pos`); it is nonempty because
  `μ` is a probability measure.  For each good point `s : S` take a local flower
  `(Z_s, m_s, G_s, O_s)`; a point `n` of a countable basis is *good* if some basis element
  `basis n` lies inside `O_s`.  The family is indexed by `n ∈ ℕ`,
  `(Z n, m n, G n) = (Z_{s n}, m_{s n}, G_{s n})` for good `n` and the flower at a fixed point
  `s₀ ∈ S` for the remaining `n` (so that no index is degenerate, hence
  `neZero : ∀ i, μ (Z i) ≠ 0` holds for *every* `i`).
  The bases cover a.e.: for a.e. `y ∈ S` some basis element `basis n ∋ y` lies inside
  `O_{⟨y,·⟩}`, so `n` is good and `y ∈ O_{s n} ∩ {free points} ⊆ G_{s n} = G n`.
  Every chosen flower is a flower at a point of `S`, so its domain has positive measure
  (`measure_domain_ne_zero`, using `μ`-a.e. freeness and the positivity of neighbourhoods on
  `S`).

* `flowerData_of_localFlower` assembles the radius-`(k+3)` families over `k ∈ ℕ` into the
  two-indexed `FlowerData`; `k + 3 > 1` for every level, so every flower of level `k` carries
  in particular the whole plaque of radius `1 ⊇ Box1 U` (needed by the patching of Pisa 6.19).
-/

namespace Work.EKLRelCross

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **Countably many flowers at a fixed radius, covering almost every point.**

The countable extraction of Pisa Corollary 6.15 from the local flower input: for every `R > 0`
there are countably many plaque algebras `(Z i, m i)` with measurable bases `G i ⊆ Z i` of
positive-measure domains, on which the shape contains `V R ∩ U`, and whose bases cover a.e. -/
theorem flowers_at_radius {U : Subgroup SL3} {μ : Measure X3} [IsProbabilityMeasure μ]
    (hloc : LocalFlowerInput U) (hfree : ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1)
    (R : ℝ) (hR : 0 < R) :
    ∃ (Z : ℕ → Set X3) (m : ℕ → MeasurableSpace X3) (G : ℕ → Set X3),
      (∀ i, IsPlaqueAlgebra U (Z i) (m i)) ∧ (∀ i, MeasurableSet (G i)) ∧
      (∀ i, G i ⊆ Z i) ∧ (∀ i, μ (Z i) ≠ 0) ∧
      (∀ i, ∀ x ∈ G i, V R ∩ (U : Set SL3) ⊆ shape (m i) U x) ∧
      μ (⋃ i, G i)ᶜ = 0 := by
  classical
  -- a.e. pair-freeness, and positivity of the open neighbourhoods of a.e. point
  have hpair : ∀ᵐ x ∂μ, ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x = u₂ • x → u₁ = u₂ :=
    ae_pairfree_of_ae_free (U := U) hfree
  have hpos : ∀ᵐ x ∂μ, ∀ s : Set X3, IsOpen s → x ∈ s → 0 < μ s :=
    Work.EKLC7.ae_isOpen_pos (μ := μ)
  -- the good points
  set S : Set X3 := {x | (∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x = u₂ • x → u₁ = u₂) ∧
    (∀ s : Set X3, IsOpen s → x ∈ s → 0 < μ s)}
  have hSae : ∀ᵐ x ∂μ, x ∈ S := by
    filter_upwards [hpair, hpos] with x h₁ h₂
    exact ⟨h₁, h₂⟩
  have hScompl : μ Sᶜ = 0 := by
    have h := MeasureTheory.ae_iff.mp hSae
    simpa [Set.compl_def] using h
  -- `S` is nonempty (`μ` is a probability measure and `S` is conull)
  have hSne : S.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h0
    rw [h0] at hScompl
    rw [Set.compl_empty, measure_univ] at hScompl
    exact one_ne_zero hScompl
  -- the local flower at every good point
  have hlocx : ∀ x : S, ∃ (Z : Set X3) (m : MeasurableSpace X3) (G O : Set X3),
      IsOpen O ∧ (x : X3) ∈ O ∧ @MeasurableSet X3 instMeasurableSpaceX3 G ∧ G ⊆ Z ∧
      IsPlaqueAlgebra U Z m ∧ (x : X3) ∈ G ∧
      O ∩ {y : X3 | ∀ u ∈ U, u • y = y → u = 1} ⊆ G ∧
      (∀ y ∈ G, V R ∩ (U : Set SL3) ⊆ shape m U y) := by
    intro x
    exact hloc x x.property.1 R hR
  choose Zfun mfun Gfun Ofun hOopen hxO hGmeas hGsub hplaq hxG hOG hshape using hlocx
  let s₀ : S := ⟨Classical.choose hSne, Classical.choose_spec hSne⟩
  obtain ⟨basis, hbas⟩ := TopologicalSpace.exists_seq_basis X3
  -- a basis element is *good* if it sits inside the neighbourhood of some good point
  let good : ℕ → Prop := fun n => ∃ s : S, basis n ⊆ Ofun s
  let wit : (n : ℕ) → good n → S := fun n h => Classical.choose h
  have hwit : ∀ (n : ℕ) (h : good n), basis n ⊆ Ofun (wit n h) :=
    fun n h => Classical.choose_spec h
  -- the family, with the flower at `s₀` as the value at the bad indices
  let Z : ℕ → Set X3 := fun n => if h : good n then Zfun (wit n h) else Zfun s₀
  let m : ℕ → MeasurableSpace X3 := fun n => if h : good n then mfun (wit n h) else mfun s₀
  let G : ℕ → Set X3 := fun n => if h : good n then Gfun (wit n h) else Gfun s₀
  -- every chosen flower sits at a point of `S`, so its domain has positive measure
  have hZne : ∀ s : S, μ (Zfun s) ≠ 0 := fun s =>
    measure_domain_ne_zero (U := U) (x₀ := (s : X3)) hfree s.property.2 (hOopen s) (hxO s)
      (hOG s) (hGsub s)
  refine ⟨Z, m, G, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    by_cases h : good n
    · simp only [Z, m, dif_pos h]; exact hplaq (wit n h)
    · simp only [Z, m, dif_neg h]; exact hplaq s₀
  · intro n
    by_cases h : good n
    · simp only [G, dif_pos h]; exact hGmeas (wit n h)
    · simp only [G, dif_neg h]; exact hGmeas s₀
  · intro n
    by_cases h : good n
    · simp only [G, Z, dif_pos h]; exact hGsub (wit n h)
    · simp only [G, Z, dif_neg h]; exact hGsub s₀
  · intro n
    by_cases h : good n
    · simp only [Z, dif_pos h]; exact hZne (wit n h)
    · simp only [Z, dif_neg h]; exact hZne s₀
  · intro n y hy
    by_cases h : good n
    · simp only [G, dif_pos h] at hy
      simp only [m, dif_pos h]
      exact hshape (wit n h) y hy
    · simp only [G, dif_neg h] at hy
      simp only [m, dif_neg h]
      exact hshape s₀ y hy
  · -- the bases cover almost every point
    have hcover : ∀ᵐ y ∂μ, y ∈ ⋃ n : ℕ, G n := by
      filter_upwards [hSae] with y hyS
      have hyO : y ∈ Ofun ⟨y, hyS⟩ := hxO ⟨y, hyS⟩
      have hyF : y ∈ {z : X3 | ∀ u ∈ U, u • z = z → u = 1} :=
        fun u hu huy => hyS.1 u hu 1 U.one_mem (by rw [huy, one_smul])
      obtain ⟨t, htB, hyt, hts⟩ := hbas.exists_subset_of_mem_open hyO (hOopen ⟨y, hyS⟩)
      obtain ⟨n, rfl⟩ := htB
      have hg : good n := ⟨⟨y, hyS⟩, hts⟩
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      simp only [G, dif_pos hg]
      exact hOG (wit n hg) ⟨hwit n hg hyt, hyF⟩
    have hEq : (⋃ n : ℕ, G n)ᶜ = {y : X3 | ¬ y ∈ ⋃ n : ℕ, G n} := rfl
    rw [hEq]
    exact MeasureTheory.ae_iff.mp hcover

/-- **The flower data from the local flower input** (Pisa Def. 6.14 / Cor. 6.15, bundled form):
if near every point with free `U`-orbit the `V R`-plaques are contained in the atoms of a plaque
algebra, and `U`-orbits are `μ`-a.e. free, then for every level `k` there are countably many
plaque algebras with measurable bases of positive-measure domains carrying the `V (k+3)`-plaques,
and the bases of each level cover almost every point. -/
theorem flowerData_of_localFlower {U : Subgroup Work.EKLContract.SL3}
    {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    (hloc : Work.EKLRelCross.LocalFlowerInput U)
    (hfree : ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1) :
    Nonempty (Work.EKLRelCross.FlowerData U μ) := by
  classical
  have hfam : ∀ k : ℕ, ∃ (Z : ℕ → Set X3) (m : ℕ → MeasurableSpace X3) (G : ℕ → Set X3),
      (∀ i, IsPlaqueAlgebra U (Z i) (m i)) ∧ (∀ i, MeasurableSet (G i)) ∧
      (∀ i, G i ⊆ Z i) ∧ (∀ i, μ (Z i) ≠ 0) ∧
      (∀ i, ∀ x ∈ G i, V ((k : ℝ) + 3) ∩ (U : Set SL3) ⊆ shape (m i) U x) ∧
      μ (⋃ i, G i)ᶜ = 0 :=
    fun k => flowers_at_radius (U := U) (μ := μ) hloc hfree ((k : ℝ) + 3) (by positivity)
  choose Z m G hplaq hmeas hsub hne hshape hcov using hfam
  exact ⟨FlowerData.mk Z m G hplaq hmeas hsub hne hshape hcov⟩

end Work.EKLRelCross

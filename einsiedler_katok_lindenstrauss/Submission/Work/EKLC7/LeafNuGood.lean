import Mathlib
import Submission.Work.EKLC7.LeafNuDefs
import Submission.Work.EKLC7.AeFreeStab
import Submission.Work.EKLComp.condExpKernel_pos
import Submission.Work.EKLComp.U_generated_by_Uball

/-!
# `Work.EKLC7.LeafNuGood` — the conull set of good points for the leafwise construction

Collects the almost-everywhere facts which make the patched measure `F.raw coord x`
(`Submission/Work/EKLC7/LeafNuDefs.lean`) well behaved:

* the `U`-orbit at `x` is free (`Work.EKLC7.AeFreeStab`, Pisa 7.12);
* for every level `n` there is a flower of radius at least `n+2` whose base contains `x`
  (the cover condition of `FlowerFam`);
* the conditional measures of the flowers are probability measures on their atoms
  (`Work.EKLComp.condExpKernel_atom`);
* the normalising constants are positive (`Work.EKLComp.condExpKernel_pos`, Pisa 6.20);
* the conditional measures of any two flowers are proportional on the intersection of their
  atoms (`Work.EKLComp.plaque_propor`, Pisa 5.17 + 6.17).
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open Classical

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC7.FlowerFam

open Work.EKLContract Work.EKLComp

variable {U : Subgroup SL3} {μ : Measure X3}

/-- The conditional measure of the `j`-th flower at `x`: `condExpKernel (μ|Z_j) m_j x`. -/
def kappa (F : FlowerFam U μ) [IsFiniteMeasure μ] (j : ℕ) (x : X3) : Measure X3 :=
  ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3) (μ.restrict (F.Z j)) (F.m j) x

/-- The normalising constant of the `j`-th flower at `x`: the mass of the plaque of `Box1 U`. -/
def ddAt (F : FlowerFam U μ) [IsFiniteMeasure μ] (j : ℕ) (x : X3) : ℝ≥0∞ :=
  F.kappa j x ((fun g : SL3 => g • x) '' (Box1 U))

/-- **Pisa 5.17 + 6.17 for plaque algebras** (proved as `Work.EKLComp.plaque_propor`):
the conditional measures of two plaque algebras are proportional on the intersection of their
atoms, a.e. on the intersection of the domains.  Stated here as a hypothesis so that the
construction is independent of the churn in that file. -/
def ProporHyp (U : Subgroup SL3) (μ : Measure X3) [IsFiniteMeasure μ] : Prop :=
  ∀ (Z₁ Z₂ : Set X3) (𝔪₁ 𝔪₂ : SigAlg),
    IsPlaqueAlgebra U Z₁ 𝔪₁.m → IsPlaqueAlgebra U Z₂ 𝔪₂.m →
    ∀ᵐ x ∂μ, x ∈ Z₁ ∩ Z₂ →
      ProporOn (ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3) (μ.restrict Z₁)
          𝔪₁.m x)
        (ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3) (μ.restrict Z₂)
          𝔪₂.m x)
        (atom 𝔪₁.m x ∩ atom 𝔪₂.m x)

theorem zmeas (F : FlowerFam U μ) (j : ℕ) : MeasurableSet (F.Z j) :=
  (F.big j).1.1 (F.Z j) (F.big j).1.2.2.1

theorem kap_eq_kappa (F : FlowerFam U μ) [IsFiniteMeasure μ] (n : ℕ) (x : X3) :
    F.kap n x = F.kappa (F.chose n x) x := rfl

theorem dd_eq_ddAt (F : FlowerFam U μ) [IsFiniteMeasure μ] (n : ℕ) (x : X3) :
    F.dd n x = F.ddAt (F.chose n x) x := rfl

theorem prp_eq (F : FlowerFam U μ) [IsFiniteMeasure μ] (coord : X3 → X3 → SL3)
    (n : ℕ) (x : X3) : F.prp coord n x = (F.kappa (F.chose n x) x).map (coord x) := rfl

/-! ## The good set -/

/-- **The good set** for the construction: a measurable conull set on which all the
measure-theoretic inputs hold pointwise. -/
structure Good (F : FlowerFam U μ) [IsFiniteMeasure μ] (X' : Set X3) : Prop where
  /-- the domain is measurable -/
  meas : MeasurableSet X'
  /-- the domain is conull -/
  null : μ X'ᶜ = 0
  /-- the `U`-orbit at every point of the domain is free -/
  free : ∀ x ∈ X', ∀ u ∈ U, u • x = x → u = 1
  /-- every radius occurs at every point of the domain -/
  cover : ∀ n : ℕ, ∀ x ∈ X', ∃ j : ℕ, (n : ℝ) + 2 ≤ F.R j ∧ x ∈ F.E j
  /-- the conditional measures are probability measures on their atoms -/
  atom_one : ∀ j : ℕ, ∀ x ∈ X', x ∈ F.Z j → F.kappa j x (atom (F.m j) x) = 1
  /-- the conditional measure is positive on plaques at points of the domain -/
  pos : ∀ j : ℕ, ∀ x ∈ X', x ∈ F.Z j → ∀ q : ℝ, 0 < q →
    0 < F.kappa j x ((fun g : SL3 => g • x) '' (Uball U q))
  /-- conditional measures of different flowers are proportional on the atom intersection -/
  propor : ∀ j j' : ℕ, ∀ x ∈ X', x ∈ F.Z j ∩ F.Z j' →
    ProporOn (F.kappa j x) (F.kappa j' x) (atom (F.m j) x ∩ atom (F.m j') x)

/-! ## Elementary consequences on the good set -/

theorem good_facts (F : FlowerFam U μ) [IsFiniteMeasure μ] {X' : Set X3} (h : F.Good X') :
    (∀ x ∈ X', ∀ u ∈ U, u • x = x → u = 1) ∧
    (∀ j : ℕ, ∀ x ∈ X', x ∈ F.Z j → F.kappa j x (atom (F.m j) x) = 1) ∧
    (∀ j : ℕ, ∀ x ∈ X', x ∈ F.Z j → ∀ q : ℝ, 0 < q →
      0 < F.kappa j x ((fun g : SL3 => g • x) '' (Uball U q))) :=
  ⟨h.free, h.atom_one, h.pos⟩

/-- On the good set the chosen flower of level `n` really is a flower of radius `≥ n+2` whose
base contains `x`. -/
theorem chose_mem (F : FlowerFam U μ) [IsFiniteMeasure μ] {X' : Set X3} (h : F.Good X')
    {x : X3} (hx : x ∈ X') (n : ℕ) :
    x ∈ F.E (F.chose n x) ∧ (n : ℝ) + 2 ≤ F.R (F.chose n x) := by
  obtain ⟨j, hj⟩ := h.cover n x hx
  exact chose_spec F ⟨j, hj.2, hj.1⟩

theorem chose_mem_Z (F : FlowerFam U μ) [IsFiniteMeasure μ] {X' : Set X3} (h : F.Good X')
    {x : X3} (hx : x ∈ X') (n : ℕ) : x ∈ F.Z (F.chose n x) :=
  (F.big _).2.1 (F.chose_mem h hx n).1

theorem chose_two_le (F : FlowerFam U μ) [IsFiniteMeasure μ] {X' : Set X3} (h : F.Good X')
    {x : X3} (hx : x ∈ X') (n : ℕ) : (2 : ℝ) ≤ F.R (F.chose n x) := by
  have := (F.chose_mem h hx n).2
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- The normalising constants are nonzero on the good set. -/
theorem dd_ne_zero (F : FlowerFam U μ) [IsFiniteMeasure μ] {X' : Set X3} (h : F.Good X')
    {x : X3} (hx : x ∈ X') (n : ℕ) : F.dd n x ≠ 0 := by
  rw [F.dd_eq_ddAt]
  refine ne_of_gt (lt_of_lt_of_le
    (h.pos _ x hx (F.chose_mem_Z h hx n) (1 / 2) (by norm_num)) ?_)
  exact measure_mono (Set.image_mono (fun g hg =>
    ⟨hg.1, fun i j => le_of_lt (lt_trans (hg.2 i j) (by norm_num))⟩))

theorem dd_ne_top (F : FlowerFam U μ) [IsProbabilityMeasure μ] {X' : Set X3} (h : F.Good X')
    {x : X3} (hx : x ∈ X') (n : ℕ) : F.dd n x ≠ ⊤ := by
  rw [F.dd_eq_ddAt]
  have h1 : F.ddAt (F.chose n x) x ≤ F.kappa (F.chose n x) x Set.univ :=
    measure_mono (Set.subset_univ _)
  have h2 : F.kappa (F.chose n x) x Set.univ = 1 := by
    simp only [kappa]
    exact measure_univ
  rw [h2] at h1
  exact ne_of_lt (lt_of_le_of_lt h1 (by norm_num))

/-- The atoms of the chosen flowers contain the plaque of radius `n+2` at `x`. -/
theorem pla_pla_subset_atom (F : FlowerFam U μ) [IsFiniteMeasure μ] {X' : Set X3}
    (h : F.Good X') {x : X3} (hx : x ∈ X') (n : ℕ) :
    Upla U ((n : ℝ) + 2) x ⊆ atom (F.m (F.chose n x)) x :=
  Set.Subset.trans (Upla_mono (F.chose_mem h hx n).2 x)
    ((F.big _).2.2 x (F.chose_mem h hx n).1)

end Work.EKLC7.FlowerFam

namespace Work.EKLC7.FlowerFam

open Work.EKLContract Work.EKLComp

variable {U : Subgroup SL3} {μ : Measure X3}

/-- **The a.e. assembly**: for an `A`-invariant probability measure `μ` and a horospherical `U`,
the good set of the flower family is conull.  This is where the four measure-theoretic inputs of
the construction are consumed: a.e. freeness (Pisa 7.12), the covering condition of the flowers
(Pisa 6.15), `condExpKernel_atom`, `condExpKernel_pos` (Pisa 6.20) and `plaque_propor`
(Pisa 5.17 + 6.17). -/
theorem exists_good (F : FlowerFam U μ) [IsProbabilityMeasure μ] (hU : IsHoro U)
    (hA : IsAInvariant μ) (hprop : ProporHyp U μ) : ∃ X', F.Good X' := by
  classical
  -- (1) the free-orbit condition
  have h1 : μ {x : X3 | ¬ (∀ u ∈ U, u • x = x → u = 1)} = 0 := by
    have h := AeFreeStab μ hA U hU
    rwa [MeasureTheory.ae_iff] at h
  -- (2) the covering condition of the flowers
  have h2 : μ {x : X3 | ¬ (∀ n : ℕ, ∃ j, (n : ℝ) + 2 ≤ F.R j ∧ x ∈ F.E j)} = 0 := by
    have hstep : ∀ n : ℕ, μ {x : X3 | ¬ (∃ j, (n : ℝ) + 2 ≤ F.R j ∧ x ∈ F.E j)} = 0 := by
      intro n
      have h := F.cover ((n : ℝ) + 2) (by positivity)
      rwa [MeasureTheory.ae_iff] at h
    have hset : {x : X3 | ¬ (∀ n : ℕ, ∃ j, (n : ℝ) + 2 ≤ F.R j ∧ x ∈ F.E j)}
        = ⋃ (n : ℕ), {x : X3 | ¬ (∃ j, (n : ℝ) + 2 ≤ F.R j ∧ x ∈ F.E j)} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      exact not_forall
    rw [hset]
    exact MeasureTheory.measure_iUnion_null hstep
  -- (3) the conditional measures are probability measures on their atoms
  have h3 : μ (⋃ j : ℕ, {x : X3 | x ∈ F.Z j ∧ F.kappa j x (atom (F.m j) x) ≠ 1}) = 0 := by
    refine MeasureTheory.measure_iUnion_null fun j => ?_
    have h : ∀ᵐ x ∂(μ.restrict (F.Z j)), F.kappa j x (atom (F.m j) x) = 1 :=
      Work.EKLComp.condExpKernel_atom ⟨F.m j⟩ (F.big j).1.1 (F.big j).1.2.1 (μ.restrict (F.Z j))
    have h' : ∀ᵐ x ∂μ, x ∈ F.Z j → F.kappa j x (atom (F.m j) x) = 1 :=
      (MeasureTheory.ae_restrict_iff' (F.zmeas j)).mp h
    have h'' : μ {x : X3 | ¬ (x ∈ F.Z j → F.kappa j x (atom (F.m j) x) = 1)} = 0 :=
      MeasureTheory.ae_iff.mp h'
    refine measure_mono_null ?_ h''
    intro x hx h
    exact hx.2 (h hx.1)
  -- (4) positivity of the normalising constants
  have h4 : μ (⋃ j : ℕ, ⋃ q : ℚ, {x : X3 | x ∈ F.Z j ∧
      ¬ (0 < F.kappa j x ((fun g : SL3 => g • x) '' (Uball U (q : ℝ)))) ∧ 0 < (q : ℝ)}) = 0 := by
    refine MeasureTheory.measure_iUnion_null fun j => ?_
    refine MeasureTheory.measure_iUnion_null fun q => ?_
    by_cases hq : 0 < (q : ℝ)
    · have h := Work.EKLComp.condExpKernel_pos U hU.1 (F.Z j) ⟨F.m j⟩ (F.big j).1 μ
        (UballOpen (q : ℝ)) (isOpen_UballOpen _) (one_mem_UballOpen hq)
      have hset : UballOpen (q : ℝ) ∩ (U : Set SL3) = Uball U (q : ℝ) := by
        rw [Set.inter_comm, ← Uball_eq_inter]
      rw [hset] at h
      have h' : ∀ᵐ x ∂μ, x ∈ F.Z j →
          0 < F.kappa j x ((fun g : SL3 => g • x) '' Uball U (q : ℝ)) :=
        (MeasureTheory.ae_restrict_iff' (F.zmeas j)).mp h
      have h'' : μ {x : X3 | ¬ (x ∈ F.Z j →
          0 < F.kappa j x ((fun g : SL3 => g • x) '' Uball U (q : ℝ)))} = 0 :=
        MeasureTheory.ae_iff.mp h'
      refine measure_mono_null ?_ h''
      intro x hx h
      refine hx.2.1 (h hx.1)
    · refine measure_mono_null ?_ (MeasureTheory.measure_empty (μ := μ))
      intro x hx
      exact absurd hx.2.2 hq
  -- (5) proportionality of the conditional measures of two flowers
  have h5 : μ (⋃ j : ℕ, ⋃ j' : ℕ, {x : X3 | x ∈ F.Z j ∩ F.Z j' ∧
      ¬ ProporOn (F.kappa j x) (F.kappa j' x)
        (atom (F.m j) x ∩ atom (F.m j') x)}) = 0 := by
    refine MeasureTheory.measure_iUnion_null fun j => ?_
    refine MeasureTheory.measure_iUnion_null fun j' => ?_
    have hp : ∀ᵐ x ∂μ, x ∈ F.Z j ∩ F.Z j' →
        ProporOn (F.kappa j x) (F.kappa j' x) (atom (F.m j) x ∩ atom (F.m j') x) := by
      simpa only [kappa] using hprop (F.Z j) (F.Z j') ⟨F.m j⟩ ⟨F.m j'⟩
        (F.big j).1 (F.big j').1
    have hp' : μ {x : X3 | ¬ (x ∈ F.Z j ∩ F.Z j' →
        ProporOn (F.kappa j x) (F.kappa j' x) (atom (F.m j) x ∩ atom (F.m j') x))} = 0 :=
      MeasureTheory.ae_iff.mp hp
    refine measure_mono_null ?_ hp'
    intro x hx h
    exact hx.2 (h hx.1)
  -- combine
  set bad : Set X3 := ({x : X3 | ¬ (∀ u ∈ U, u • x = x → u = 1)} ∪
      {x : X3 | ¬ (∀ n : ℕ, ∃ j, (n : ℝ) + 2 ≤ F.R j ∧ x ∈ F.E j)} ∪
      (⋃ j : ℕ, {x : X3 | x ∈ F.Z j ∧ F.kappa j x (atom (F.m j) x) ≠ 1}) ∪
      (⋃ j : ℕ, ⋃ q : ℚ, {x : X3 | x ∈ F.Z j ∧
        ¬ (0 < F.kappa j x ((fun g : SL3 => g • x) '' (Uball U (q : ℝ)))) ∧ 0 < (q : ℝ)})) ∪
      (⋃ j : ℕ, ⋃ j' : ℕ, {x : X3 | x ∈ F.Z j ∩ F.Z j' ∧
        ¬ ProporOn (F.kappa j x) (F.kappa j' x)
          (atom (F.m j) x ∩ atom (F.m j') x)}) with hbad_def
  have hbad : μ bad = 0 := by
    rw [hbad_def]
    exact MeasureTheory.measure_union_null
      (MeasureTheory.measure_union_null (MeasureTheory.measure_union_null
        (MeasureTheory.measure_union_null h1 h2) h3) h4) h5
  obtain ⟨t, hsub, htmeas, htnull⟩ := MeasureTheory.exists_measurable_superset_of_null hbad
  refine ⟨tᶜ, htmeas.compl, by simpa using htnull, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx u hu hux
    by_contra hne
    refine hx (hsub ?_)
    rw [hbad_def]
    exact Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
      (Set.mem_union_left _ (fun h => hne (h u hu hux)))))
  · intro n x hx
    by_contra hcon
    refine hx (hsub ?_)
    rw [hbad_def]
    exact Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
      (Set.mem_union_right _ (fun h => hcon (h n)))))
  · intro j x hx hxZ
    by_contra hcon
    refine hx (hsub ?_)
    rw [hbad_def]
    exact Set.mem_union_left _ (Set.mem_union_left _
      (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨j, ⟨hxZ, hcon⟩⟩)))
  · intro j x hx hxZ q hq
    by_contra hcon
    obtain ⟨q', hq'pos, hq'lt⟩ := exists_rat_btwn hq
    refine hx (hsub ?_)
    rw [hbad_def]
    refine Set.mem_union_left _ (Set.mem_union_right _
      (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨q', ⟨hxZ, ?_, hq'pos⟩⟩⟩))
    intro hpos
    exact hcon (lt_of_lt_of_le hpos (measure_mono (Set.image_mono (Uball_mono (le_of_lt hq'lt)))))
  · intro j j' x hx hxZ
    by_contra hcon
    refine hx (hsub ?_)
    rw [hbad_def]
    exact Set.mem_union_right _
      (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨j', ⟨hxZ, hcon⟩⟩⟩)

end Work.EKLC7.FlowerFam

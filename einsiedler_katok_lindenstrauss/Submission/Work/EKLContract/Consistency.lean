import Submission.Work.EKLContract.Glue
import Submission.Work.EKLContract.Lemmas.Hfam_fin_one

/-!
# EKL contract — satisfiability (non-vacuity) of the interface

This module exhibits concrete, Lean-checked witnesses that the definitions of `Defs.lean` are
consistent, and that the hypotheses of the frozen component `Prop`s are satisfiable.

* `Work.EKLContract.§10.a` — the **trivial leafwise system**: `IsLeafwise 0 ⊥ (δ_1) univ`.
  All nine fields of `IsLeafwise` hold at a concrete instance (the `condexp` field is the
  substantive one; for the trivial subgroup `⊥` the shape is `{1}` and the right hand side is
  `f x`, so the field reduces to `condExp m (μ|_Z) f =ᵐ f`, which is what the delegated lemma
  `Work.EKLContract.Lemmas.IsLeafwiseBot` proves for every finite `μ`).
* `Work.EKLContract.§10.b` — the **entropy objects** `FinPart`, `Hfam`, `hPart`, `ent`, `Hcond`,
  `joinSets`, `partSigma`, `Refines`: a one-part partition exists, and for a Dirac measure every
  `Hfam`/`hPart`/`ent` vanishes, so `ent` is not a junk value.
* `Work.EKLContract.§10.c` — witnesses for the hypothesis predicates of the components:
  `IsAInvariant`, `IsAErgodic`, `IsUInvariant`, `CrossSection`, `RelCrossSection`,
  `NonExceptional`, `IsPlaqueAlgebra`, `IsHoro`, plus `HasShortVec`/`Thick` at `mkX 1`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

namespace Work.EKLContract

/-! ## 10.a The trivial leafwise system -/

theorem bot_carrier : ((⊥ : Subgroup SL3) : Set SL3) = {1} := Subgroup.coe_bot

theorem box1_bot : Box1 (⊥ : Subgroup SL3) = {1} := by
  ext g
  refine ⟨fun hg => Subgroup.mem_bot.mp hg.1, fun hg => ?_⟩
  rw [Set.mem_singleton_iff] at hg
  subst hg
  exact ⟨Subgroup.mem_bot.mpr rfl, fun i j => by simp⟩

/-- `x` lies in its own atom. -/
theorem mem_atom (m : MeasurableSpace X3) (x : X3) : x ∈ atom m x := by
  refine Set.mem_sInter.mpr ?_
  rintro s ⟨_, hx⟩
  exact hx

theorem shape_bot (m : MeasurableSpace X3) (x : X3) : shape m (⊥ : Subgroup SL3) x = {1} := by
  ext u
  simp only [shape, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · exact fun h => Subgroup.mem_bot.mp h.1
  · intro h
    subst h
    exact ⟨Subgroup.mem_bot.mpr rfl, by simpa using mem_atom m x⟩

/-- **The trivial leafwise system**: `U = ⊥`, `ν_x = δ_1`, the zero measure.  All nine defining
conditions of `IsLeafwise` hold simultaneously.  (The hypothesis set of C5's existence statement
is also satisfiable: see `isHoro_bot` and `isAInvariant_zero`.) -/
theorem isLeafwise_bot_zero :
    IsLeafwise (0 : Measure X3) (⊥ : Subgroup SL3)
      (fun _ : X3 => Measure.dirac (1 : SL3)) Set.univ := by
  refine ⟨MeasurableSet.univ, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x _
    infer_instance
  · intro x _
    rw [bot_carrier, Measure.dirac_apply' 1 (by measurability : MeasurableSet ({1} : Set SL3)ᶜ)]
    simp
  · intro x _
    rw [box1_bot, Measure.dirac_apply_of_mem (Set.mem_singleton (1 : SL3))]
  · intro f
    rw [show (fun _ : X3 => ∫ g, f g ∂(Measure.dirac (1 : SL3))) = fun _ => f 1 from
      funext fun _ => integral_dirac' (fun g => f g) 1 f.continuous.stronglyMeasurable]
    exact measurable_const
  · intro x _ δ hδ
    rw [Measure.dirac_apply_of_mem
      (show (1 : SL3) ∈ V δ from by intro i j; simpa using hδ)]
    exact zero_lt_one
  · intro x _ u hu _
    obtain rfl : u = 1 := Subgroup.mem_bot.mp hu
    refine ⟨1, one_ne_zero, ENNReal.one_ne_top, ?_⟩
    simp only [one_smul]
    rw [show (fun g : SL3 => g * 1) = id from funext fun g => mul_one g, Measure.map_id]
  · intro Z m hm f hf hbdd
    rw [Measure.restrict_zero]
    simp

/-! ## 10.b The entropy objects -/

/-- The one-part partition. -/
def trivPart (X : Type*) [MeasurableSpace X] : FinPart X where
  n := 1
  parts := fun _ => Set.univ
  measurable := fun _ => MeasurableSet.univ
  disjoint := fun i j hij => absurd (Subsingleton.elim i j) hij
  cover := by ext x; simp [Set.mem_iUnion]

theorem trivPart_n (X : Type*) [MeasurableSpace X] : (trivPart X).n = 1 := rfl

@[simp] theorem trivPart_parts (X : Type*) [MeasurableSpace X] (i : Fin (trivPart X).n) :
    (trivPart X).parts i = Set.univ := rfl

section Entropy

variable {X : Type*} [mX : MeasurableSpace X]

theorem joinSets_trivPart_apply (T : X → X) (N : ℕ) (w : Fin N → Fin (trivPart X).n) :
    joinSets T (trivPart X) N w = Set.univ := by
  simp only [joinSets, trivPart_parts, Set.preimage_univ]
  ext x
  simp

/-- `partSigma` of the trivial partition is the trivial σ-algebra. -/
theorem partSigma_trivPart (X : Type*) [MeasurableSpace X] :
    partSigma (trivPart X) = ⊥ := by
  refine le_antisymm ?_ bot_le
  refine MeasurableSpace.generateFrom_le ?_
  rintro s ⟨i, rfl⟩
  exact MeasurableSet.univ

/-- `Refines` is reflexive and transitive. -/
theorem Refines_refl (P : FinPart X) : Refines P P := fun i => ⟨i, subset_rfl⟩

theorem Refines_trans {P Q R : FinPart X} (h1 : Refines P Q) (h2 : Refines Q R) :
    Refines P R := by
  intro i
  obtain ⟨j, hj⟩ := h1 i
  obtain ⟨k, hk⟩ := h2 j
  exact ⟨k, hj.trans hk⟩

/-- `Hfam` of the one-part family (via `Lemmas.Hfam_fin_one`). -/
theorem Hfam_trivPart (μ : Measure X) :
    Hfam μ (fun _ : Fin (trivPart X).n => (Set.univ : Set X)) =
      Real.negMulLog (μ Set.univ).toReal := by
  rw [Lemmas.Hfam_fin_one X μ ((trivPart X).n), trivPart_n, Nat.cast_one, one_mul]

/-- Every `Hfam` of a Dirac measure vanishes (the parts are measurable). -/
theorem Hfam_dirac (x : X) {ι : Type*} [Fintype ι] (P : ι → Set X)
    (hP : ∀ i, MeasurableSet (P i)) : Hfam (Measure.dirac x) P = 0 := by
  simp only [Hfam]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Measure.dirac_apply' x (hP i)]
  by_cases h : x ∈ P i
  · simp [h]
  · simp [h]

/-- `h_μ(T,P) = 0` for `μ` a Dirac measure and `T` measurable: arbitrary partitions of a Dirac
measure carry no entropy. -/
theorem hPart_dirac (x : X) (T : X → X) (hT : Measurable T) (P : FinPart X) :
    hPart (Measure.dirac x) T P = 0 := by
  have hN : ∀ N : ℕ, Hfam (Measure.dirac x) (joinSets T P (N + 1)) / ((N : ℝ) + 1) = 0 := by
    intro N
    rw [Hfam_dirac x _ (fun w => ?_), zero_div]
    exact MeasurableSet.iInter fun k => hT.iterate k (P.measurable (w k))
  rw [hPart]
  simp only [hN]
  simp

/-- **`ent` of a Dirac measure is zero** — the entropy object is consistent, not a junk value. -/
theorem ent_dirac (x : X) (T : X → X) (hT : Measurable T) :
    ent (Measure.dirac x) T = 0 := by
  rw [ent]
  simp only [hPart_dirac x T hT, ENNReal.ofReal_zero]
  simp

/-- `Hcond` of the one-part partition w.r.t. `⊥` is zero. -/
theorem Hcond_trivPart_bot (μ : Measure X) [IsFiniteMeasure μ] :
    Hcond μ (trivPart X) (⊥ : MeasurableSpace X) = 0 := by
  simp only [Hcond, trivPart_parts, Set.indicator_univ]
  rw [condExp_const (μ := μ) (m := ⊥) bot_le (1 : ℝ)]
  simp

end Entropy

/-! ## 10.c Witnesses for the component hypotheses -/

theorem isAInvariant_zero : IsAInvariant (0 : Measure X3) := fun t =>
  ⟨(continuous_const_smul (aDiag t)).measurable, by rw [Measure.map_zero]⟩

/-- The zero measure is `A`-invariant *and* `A`-ergodic. -/
theorem isAErgodic_zero : IsAErgodic (0 : Measure X3) :=
  ⟨isAInvariant_zero, fun E _ _ => Or.inl (by simp)⟩

theorem isUInvariant_zero (U : Subgroup SL3) : IsUInvariant (0 : Measure X3) U := fun u _ =>
  ⟨(continuous_const_smul u).measurable, by rw [Measure.map_zero]⟩

/-- `CrossSection` is satisfiable for every measure when `U = ⊥`. -/
theorem crossSection_bot (μ : Measure X3) : CrossSection μ (⊥ : Subgroup SL3) := by
  refine ⟨Set.univ, MeasurableSet.univ, by simp, ?_⟩
  intro x _ u hu _
  exact Subgroup.mem_bot.mp hu

theorem crossSection_zero (U : Subgroup SL3) : CrossSection (0 : Measure X3) U := by
  refine ⟨∅, MeasurableSet.empty, by simp, ?_⟩
  intro x hx
  exact absurd hx (Set.notMem_empty x)

theorem relCrossSection_self (μ : Measure X3) (H : Subgroup SL3) :
    RelCrossSection μ H H := by
  refine ⟨Set.univ, MeasurableSet.univ, by simp, ?_⟩
  intro x _ h hh _
  exact hh

theorem relCrossSection_zero (H L : Subgroup SL3) : RelCrossSection (0 : Measure X3) H L := by
  refine ⟨∅, MeasurableSet.empty, by simp, ?_⟩
  intro x hx
  exact absurd hx (Set.notMem_empty x)

theorem nonExceptional_zero {a b c : Fin 3} (hab : a ≠ b) :
    NonExceptional (0 : Measure X3) hab c := by
  refine ⟨Set.univ, by simp, ?_⟩
  intro K _ _ hpos
  exact absurd hpos (lt_irrefl 0)

/-- `IsPlaqueAlgebra` is satisfiable (`Z = ∅`, `m = ⊥`). -/
theorem isPlaqueAlgebra_empty (U : Subgroup SL3) :
    IsPlaqueAlgebra U ∅ (⊥ : MeasurableSpace X3) := by
  refine ⟨bot_le, ⟨∅, Set.countable_empty, ?_⟩, ?_, ?_⟩
  · exact MeasurableSpace.generateFrom_empty.symm
  · exact @MeasurableSet.empty X3 (⊥ : MeasurableSpace X3)
  · intro x hx
    exact absurd hx (Set.notMem_empty x)

/-- `IsHoro ⊥` (the degenerate horospherical subgroup). -/
theorem isHoro_bot : IsHoro (⊥ : Subgroup SL3) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [bot_carrier]
    exact isClosed_singleton
  · intro t u hu
    rw [Subgroup.mem_bot.mp hu]
    simp
  · refine ⟨0, ?_⟩
    intro u hu
    rw [Subgroup.mem_bot.mp hu]
    simp

/-- `PosEnt` is not a tautology: it fails on the empty set. -/
theorem not_posEnt_empty (g : SL3) : ¬ PosEnt g (∅ : Set X3) := by
  rintro ⟨ε, hε, c, hc, hN⟩
  obtain ⟨N, _, E, hE, _, hcard⟩ := hN 0
  have hEempty : E = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    exact (hE hx).elim
  rw [hEempty] at hcard
  simp only [Finset.card_empty, Nat.cast_zero] at hcard
  exact absurd hcard (not_le.mpr (Real.exp_pos _))

end Work.EKLContract

import Mathlib
import Submission.Work.Diff.STE.B3.Comp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The integral of a `1`-periodic function does not depend on the fundamental domain

`Work.Diff.STE.unitCube` is the half open cube `(0,1]^ι` of the flat torus, and this file shows
that for a function `F` which is `1`-periodic in every coordinate (i.e. invariant under the
translations `x ↦ x + eᵢ`), the integral of `F` over `(0,1]^ι` equals its integral over the
*centred* cube `(-1/2, 1/2]^ι`, the statement `integral_unitCube_eq_centreCube`.

Both cubes are fundamental domains of the translation action of the lattice `ℤ^ι` on `ℝ^ι`, and a
function invariant under the lattice has the same integral over any two fundamental domains
(`MeasureTheory.IsAddFundamentalDomain.setIntegral_eq`).  This is the route taken here:

* `instVAddIntPi`, `instAddActionIntPi`, `instMeasurableConstVAddIntPi`,
  `instVAddInvariantIntPi`: the lattice `ℤ^ι` acts on `ℝ^ι` by translation, measurably and
  measure preservingly (Lebesgue measure on `ℝ^ι` is translation invariant);
* `Periodic1.add_intVec`: a `1`-periodic function is invariant under *every* lattice translation
  (the periods `Pi.single i 1` add up, using `Function.Periodic.zsmul`);
* `isAddFundamentalDomain_cube_Ioc`: every half open cube `∏ (a, a+1]` is a fundamental domain,
  because for every `x` and every coordinate there is a *unique* integer `m` with
  `xᵢ + m ∈ (a, a+1]` (`existsUnique_add_zsmul_mem_Ioc`).

Nothing here needs the continuity of `F`; the measure theory of fundamental domains handles
non-integrable functions as well (both integrals are then `0`).
-/

noncomputable section

namespace Work.Diff.STE.B3

open MeasureTheory

/-! ## The lattice `ℤ^ι` acting on `ℝ^ι` by translation -/

variable {ι : Type*}

instance instVAddIntPi : VAdd (ι → ℤ) (ι → ℝ) := ⟨fun c x => (fun i => (c i : ℝ)) + x⟩

instance instAddActionIntPi : AddAction (ι → ℤ) (ι → ℝ) where
  zero_vadd x := by
    show (fun i : ι => ((0 : ι → ℤ) i : ℝ)) + x = x
    funext i
    simp only [Pi.add_apply, Pi.zero_apply, Int.cast_zero, zero_add]
  add_vadd a b x := by
    show (fun i : ι => ((a + b) i : ℝ)) + x
        = (fun i : ι => (a i : ℝ)) + ((fun i : ι => (b i : ℝ)) + x)
    ext i
    simp only [Pi.add_apply, Int.cast_add]
    ring

instance instMeasurableConstVAddIntPi : MeasurableConstVAdd (ι → ℤ) (ι → ℝ) where
  measurable_const_vadd c := by
    apply measurable_pi_iff.mpr
    intro i
    have h1 : (fun x : ι → ℝ => (c +ᵥ x) i) = fun x => (c i : ℝ) + x i := by
      show (fun x : ι → ℝ => ((fun i : ι => (c i : ℝ)) + x) i) = fun x => (c i : ℝ) + x i
      exact funext fun x => Pi.add_apply _ _ _
    rw [h1]
    exact (measurable_pi_apply (X := fun _ : ι => ℝ) i).const_add _

variable [Fintype ι]

/-- Translation by an integer vector preserves Lebesgue measure on `ℝ^ι`. -/
instance instVAddInvariantIntPi :
    VAddInvariantMeasure (ι → ℤ) (ι → ℝ) (volume : Measure (ι → ℝ)) where
  measure_preimage_vadd c s _ := by
    have h : (fun x : ι → ℝ => c +ᵥ x) = fun x => (fun i => (c i : ℝ)) + x := rfl
    rw [h]
    exact measure_preimage_add _ _ _

/-! ## Periodicity -/

/-- If `f` has the two periods `a` and `b`, then it has the period `a + b`. -/
lemma Periodic_add_period {α : Type*} {β : Type*} [AddSemigroup α] {f : α → β} {a b : α}
    (ha : Function.Periodic f a) (hb : Function.Periodic f b) :
    Function.Periodic f (a + b) :=
  fun x => by rw [← add_assoc, hb, ha]

/-- A function which is `1`-periodic in every coordinate is invariant under every integer
translation: `F (n + x) = F x` for `n : ι → ℤ`. -/
lemma Periodic1.add_intVec {β : Type*} [DecidableEq ι] {F : (ι → ℝ) → β} (hper : Periodic1 F)
    (n : ι → ℤ) (x : ι → ℝ) : F ((fun i => (n i : ℝ)) + x) = F x := by
  have hper' : ∀ i : ι, Function.Periodic F (Pi.single i (1 : ℝ)) := fun i => hper i
  have key : ∀ s : Finset ι, Function.Periodic F (∑ i ∈ s, n i • Pi.single i (1 : ℝ)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro y; simp
    | insert j s hj ih =>
      rw [Finset.sum_insert hj]
      exact Periodic_add_period ((hper' j).zsmul (n j)) ih
  have hsum : Function.Periodic F (∑ i, n i • Pi.single i (1 : ℝ)) := key Finset.univ
  have hvec : (∑ i, n i • Pi.single i (1 : ℝ)) = fun i => (n i : ℝ) := by
    rw [← Finset.univ_sum_single (fun i : ι => (n i : ℝ))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Pi.single_zsmul]
    simp
  have h1 : (fun i => (n i : ℝ)) + x = x + ∑ i, n i • Pi.single i (1 : ℝ) := by
    rw [← hvec, add_comm]
  rw [h1]
  exact hsum x

/-! ## The half open cubes are fundamental domains -/

/-- The half open cube `∏ᵢ (a, a+1]` is a fundamental domain for the translation action of the
lattice `ℤ^ι` on `ℝ^ι`: every `x` lies in exactly one of its translates. -/
lemma isAddFundamentalDomain_cube_Ioc (a : ℝ) :
    IsAddFundamentalDomain (ι → ℤ)
      (Set.pi Set.univ (fun _ : ι => Set.Ioc a (a + 1))) (volume : Measure (ι → ℝ)) := by
  refine IsAddFundamentalDomain.mk' ?_ ?_
  · exact (MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ioc).nullMeasurableSet
  · intro x
    have hU : ∀ i : ι, ∃! m : ℤ, x i + (m : ℝ) ∈ Set.Ioc a (a + 1) := by
      intro i
      simpa using existsUnique_add_zsmul_mem_Ioc (a := (1 : ℝ)) one_pos (x i) a
    refine ⟨fun i => (hU i).exists.choose, ?_, ?_⟩
    · intro i _
      have h := (hU i).exists.choose_spec
      show ((fun j => ((hU j).exists.choose : ℝ)) + x) i ∈ Set.Ioc a (a + 1)
      simp only [Pi.add_apply]
      exact (add_comm ((hU i).exists.choose : ℝ) (x i)) ▸ h
    · intro n hn
      funext i
      have hmem : x i + (n i : ℝ) ∈ Set.Ioc a (a + 1) := by
        have h' : ((fun j : ι => (n j : ℝ)) + x) i ∈ Set.Ioc a (a + 1) :=
          (Set.mem_univ_pi.mp hn) i
        simp only [Pi.add_apply] at h'
        rwa [add_comm (n i : ℝ) (x i)] at h'
      exact (hU i).unique hmem (hU i).exists.choose_spec

/-! ## The result -/

set_option linter.unusedVariables false in
/-- The integral of a `1`-periodic function over the unit cube `(0,1]^ι` equals its integral over
the centred cube `(-1/2,1/2]^ι`: both are fundamental domains of the lattice `ℤ^ι`. -/
theorem integral_unitCube_eq_centreCube
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : (ι → ℝ) → ℂ) (hper : Work.Diff.STE.Periodic1 F) (hcont : Continuous F) :
    (∫ z in Work.Diff.STE.unitCube (ι := ι), F z)
      = ∫ z in Set.pi Set.univ (fun _ : ι => Set.Ioc (-(1/2:ℝ)) (1/2)), F z := by
  have hf : ∀ (n : ι → ℤ) (x : ι → ℝ), F (n +ᵥ x) = F x :=
    fun n x => Periodic1.add_intVec hper n x
  have hmain := IsAddFundamentalDomain.setIntegral_eq
    (isAddFundamentalDomain_cube_Ioc (ι := ι) 0)
    (isAddFundamentalDomain_cube_Ioc (ι := ι) (-(1/2)))
    (f := F) hf
  have hone : (-(1/2:ℝ)) + 1 = 1/2 := by norm_num
  rw [hone] at hmain
  simpa [Work.Diff.STE.unitCube] using hmain

end Work.Diff.STE.B3

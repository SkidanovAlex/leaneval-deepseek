import Mathlib
import Submission.Work.EKLC6Core.TrivAeDefs
import Submission.Work.EKLC6Core.dirac_of_mass

/-!
# `Work.EKLC6Core.goodSet_subset_dirac`

An element of the good set `goodSet ν X'` (see `TrivAeDefs`) has leafwise measure `ν x = δ₁`.

The good set is `X' ∩ ⋂_{i,j,m,N} {x | ∫ testFun i j m N dν_x = 0}`, where the compactly
supported continuous functions `testFun i j m N ≥ 0` have too-small support to see `1` and
whose positivity sets cover `{1}ᶜ` (`exists_testFun_pos`).  Since a nonnegative integrable
function with vanishing integral has null support, `ν x` gives mass `0` to the countable union
of these supports, i.e. to `{1}ᶜ`.  Because `1 ∈ Box1 U` and `ν x (Box1 U) = 1`, this forces
`ν x {1} = 1`; the total mass is then `1`, so `ν x` is the Dirac mass at `1` (`dirac_of_mass`).
-/

open MeasureTheory
open scoped ENNReal
open Work.EKLContract

namespace Work.EKLC6Core

/-- The test function `testFun i j m N` vanishes at `1`: the identity has `absEntry = 0`. -/
theorem testFun_eval_one (i j : Fin 3) (m N : ℕ) :
    testFun i j m N (1 : Work.EKLContract.SL3) = 0 := by
  rw [testFun_coe, testFunFun]
  have h0 : absEntry i j (1 : Work.EKLContract.SL3) = 0 := by simp [absEntry]
  rw [h0]
  have h1 : max 0 (0 - ((m : ℝ) + 1)⁻¹) = 0 := by
    rw [max_eq_left]
    linarith [inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1)]
  rw [h1]; simp

theorem goodSet_subset_dirac {μ : MeasureTheory.Measure Work.EKLContract.X3}
    {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3}
    (hL : Work.EKLContract.IsLeafwise μ U ν X') {x : Work.EKLContract.X3}
    (hx : x ∈ Work.EKLC6Core.goodSet ν X') :
    ν x = MeasureTheory.Measure.dirac 1 := by
  rw [goodSet, Set.mem_inter_iff, Set.mem_iInter] at hx
  obtain ⟨hxX', hxtest⟩ := hx
  simp only [Set.mem_ofPred_eq] at hxtest
  haveI : IsFiniteMeasureOnCompacts (ν x) := hL.radon x hxX'
  -- Step 1: each test function has null support under `ν x`.
  have hsupp_zero : ∀ p : Fin 3 × Fin 3 × ℕ × ℕ,
      ν x (Function.support (testFun p.1 p.2.1 p.2.2.1 p.2.2.2)) = 0 := by
    intro p
    have hint : Integrable (⇑(testFun p.1 p.2.1 p.2.2.1 p.2.2.2)) (ν x) :=
      (testFun p.1 p.2.1 p.2.2.1 p.2.2.2).integrable
    have hnn : 0 ≤ ⇑(testFun p.1 p.2.1 p.2.2.1 p.2.2.2) :=
      fun g => testFun_nonneg _ _ _ _ g
    have hae : (⇑(testFun p.1 p.2.1 p.2.2.1 p.2.2.2)) =ᵐ[ν x] 0 :=
      (integral_eq_zero_iff_of_nonneg hnn hint).mp (hxtest p)
    have := MeasureTheory.ae_iff.mp hae
    simpa [Function.support] using this
  -- Step 2: the supports cover `{1}ᶜ`.
  have hunion : (⋃ p : Fin 3 × Fin 3 × ℕ × ℕ,
      Function.support (testFun p.1 p.2.1 p.2.2.1 p.2.2.2)) = ({1} : Set SL3)ᶜ := by
    ext g
    simp only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨p, hp⟩ rfl
      obtain ⟨i, j, m, N⟩ := p
      rw [Function.mem_support, testFun_eval_one i j m N] at hp
      exact hp rfl
    · intro hg
      obtain ⟨i, j, m, N, hmem⟩ := exists_testFun_pos hg
      exact ⟨(i, j, m, N), by simpa using hmem⟩
  -- Step 3: `ν x` gives `{1}ᶜ` measure zero.
  have hcompl : ν x ({1} : Set SL3)ᶜ = 0 := by
    rw [← hunion]
    exact measure_iUnion_null hsupp_zero
  -- Step 4: `ν x {1} = 1`.
  have hbox : ν x (Box1 U) = 1 := hL.normalised x hxX'
  have hone_mem : (1 : SL3) ∈ Box1 U := ⟨U.one_mem, fun i j => by simp⟩
  have hone : ν x ({1} : Set SL3) = 1 := by
    have hkey : ν x (Box1 U) = ν x ({1} : Set SL3) := by
      have hdecomp : Box1 U = (Box1 U \ ({1} : Set SL3)) ∪ ({1} : Set SL3) := by
        ext a
        constructor
        · intro ha
          by_cases h : a = 1
          · exact Or.inr h
          · exact Or.inl ⟨ha, h⟩
        · rintro (⟨ha, _⟩ | rfl)
          · exact ha
          · exact hone_mem
      have hdisj : Disjoint (Box1 U \ ({1} : Set SL3)) ({1} : Set SL3) := by
        rw [Set.disjoint_left]
        intro a ha ha1
        exact ha.2 ha1
      have h0 : ν x (Box1 U \ ({1} : Set SL3)) = 0 :=
        measure_mono_null (fun a ha => ha.2) hcompl
      rw [hdecomp, measure_union hdisj (measurableSet_singleton 1), h0, zero_add]
    rw [← hkey, hbox]
  -- Step 5: the total mass is `1`, hence so is the mass of `U`.
  have huniv : ν x Set.univ = 1 := by
    have h : (Set.univ : Set SL3) = ({1} : Set SL3) ∪ ({1} : Set SL3)ᶜ :=
      (Set.union_compl_self _).symm
    rw [h, measure_union disjoint_compl_right (measurableSet_singleton 1).compl,
      hone, hcompl, add_zero]
  have hmassU : ν x (U : Set SL3) = 1 := by
    refine le_antisymm ?_ ?_
    · rw [← huniv]; exact measure_mono (Set.subset_univ _)
    · have h1 : (1 : ℝ≥0∞) = ν x ({1} : Set SL3) := hone.symm
      rw [h1]
      exact measure_mono (Set.singleton_subset_iff.mpr U.one_mem)
  exact dirac_of_mass (hL.carried x hxX') hmassU hone

end Work.EKLC6Core

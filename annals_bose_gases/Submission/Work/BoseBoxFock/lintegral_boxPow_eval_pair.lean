import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.integral_fibre_two
import Submission.Work.BoseFixB2.Pot.lintegral_pair_abox
import Submission.Work.MB.SlotWeakBase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.lintegral_boxPow_eval_pair` — the two-coordinate evaluation of the box product

This module proves the elementary Fubini fact behind the two-coordinate (`pair`) rows of the
box ↔ model dictionary: integrating over the `n`-particle box
`Work.MB.boxPow n l = (Work.BoseK15.corpusBox.boxL l)^n` a function which sees only the two
distinct coordinates `i ≠ j` produces the free two-particle integral over
`boxL l × boxL l`, with the volume of the *remaining* `n - 2` particle box as the fibre volume.

The proof splits as follows (all of it is elementary measure theory on product measures):

* `two_le_of_ne` — `i ≠ j` in `Fin n` forces `n ≥ 2`, so we may write `n = m + 2`;
* `card_subtype_ne_ne` — the complement of two distinct points of `Fin (m + 2)` has `m` elements,
  which identifies the fibre volume `volume (univ.pi fun _ : {k // k ≠ i ∧ k ≠ j} => A)` with
  `(volume A)^m`;
* the indicator `1_{A^n}` is traded for the restricted measure
  `(volume : Measure (Fin (m+2) → E3)).restrict (univ.pi fun _ => A)`
  (`lintegral_indicator`), which by `Measure.restrict_pi_pi` and `volume_pi` is the product
  measure of `ν = (volume : Measure E3).restrict A`;
* `Work.BoseFixB2.Pot.lintegral_pi_pair_aux` (the two-coordinate peel of a product measure,
  already available in the workspace) evaluates the resulting integral;
* the right hand side is brought into the same normal form by
  `volume_pi_pi`, `Measure.prod_restrict`, `Measure.volume_eq_prod` and `lintegral_prod`.

Nothing here uses the geometry of the corpus box: only its measurability.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Two distinct elements of `Fin n` force `2 ≤ n`. -/
private lemma two_le_of_ne {n : ℕ} {i j : Fin n} (hij : i ≠ j) : 2 ≤ n := by
  by_contra h
  refine hij (Fin.ext ?_)
  have hi : (i : ℕ) < n := i.isLt
  have hj : (j : ℕ) < n := j.isLt
  omega

/-- The complement of two distinct points of `Fin (m+2)` has `m` elements. -/
private lemma card_subtype_ne_ne (m : ℕ) (i j : Fin (m + 2)) (hij : i ≠ j) :
    Fintype.card {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} = m := by
  rw [Fintype.card_subtype]
  have h1 : (Finset.univ.filter (fun k : Fin (m + 2) => k ≠ i ∧ k ≠ j))
      = (Finset.univ.erase i).erase j := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [h1, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩),
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  omega

theorem lintegral_boxPow_eval_pair {n : ℕ} {l : ℝ} {i j : Fin n} (hij : i ≠ j)
    {g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ENNReal}
    (hg : Measurable (Function.uncurry g)) :
    (∫⁻ x : Work.BoseDict.Xn n,
        (Work.MB.boxPow n l).indicator (fun _ => 1) x * g (x i) (x j))
      = MeasureTheory.volume (Set.univ.pi (fun _ : {k : Fin n // k ≠ i ∧ k ≠ j} =>
            Work.BoseK15.corpusBox.boxL l))
        * ∫⁻ q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
            (Work.BoseK15.corpusBox.boxL l).indicator (fun _ => 1) q.1
              * ((Work.BoseK15.corpusBox.boxL l).indicator (fun _ => 1) q.2 * g q.1 q.2) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by have := two_le_of_ne hij; omega⟩
  simp only [Work.MB.boxPow]
  set A : Set E3 := Work.BoseK15.corpusBox.boxL l with hAdef
  have hA : MeasurableSet A := Work.BoseB4.BoxData.boxL_measurableSet _ l
  set ν : Measure E3 := (volume : Measure E3).restrict A with hνdef
  have hν : ν Set.univ = volume A := by rw [hνdef, Measure.restrict_apply_univ]
  have hS : MeasurableSet (Set.univ.pi (fun _ : Fin (m + 2) => A)) :=
    MeasurableSet.univ_pi (fun _ => hA)
  -- Step 1: trade the indicator of the box for the restricted measure.
  have hstep1 : (∫⁻ x : Fin (m + 2) → E3,
        (Set.univ.pi (fun _ : Fin (m + 2) => A)).indicator (fun _ => (1 : ENNReal)) x
          * g (x i) (x j))
      = ∫⁻ x : Fin (m + 2) → E3, g (x i) (x j)
          ∂((volume : Measure (Fin (m + 2) → E3)).restrict
            (Set.univ.pi (fun _ : Fin (m + 2) => A))) := by
    have hp : ∀ x : Fin (m + 2) → E3,
        (Set.univ.pi (fun _ : Fin (m + 2) => A)).indicator (fun _ => (1 : ENNReal)) x
          * g (x i) (x j)
        = (Set.univ.pi (fun _ : Fin (m + 2) => A)).indicator
            (fun x => g (x i) (x j)) x := by
      intro x
      by_cases hx : x ∈ Set.univ.pi (fun _ : Fin (m + 2) => A)
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
    rw [lintegral_congr hp]
    exact lintegral_indicator hS (fun x => g (x i) (x j))
  -- Step 2: the restricted box product is the product of the restricted one-particle measures.
  have hvolpi : (volume : Measure (Fin (m + 2) → E3)).restrict
        (Set.univ.pi (fun _ : Fin (m + 2) => A)) = Measure.pi (fun _ : Fin (m + 2) => ν) := by
    have hv : (volume : Measure (Fin (m + 2) → E3))
        = Measure.pi (fun _ : Fin (m + 2) => (volume : Measure E3)) := MeasureTheory.volume_pi
    rw [hv, Measure.restrict_pi_pi, hνdef]
  -- Step 3: the two-coordinate peel of the product measure.
  have hpeel : (∫⁻ x : Fin (m + 2) → E3, g (x i) (x j)
        ∂(Measure.pi (fun _ : Fin (m + 2) => ν)))
      = (ν Set.univ) ^ m * ∫⁻ a, ∫⁻ b, g a b ∂ν ∂ν :=
    Work.BoseFixB2.Pot.lintegral_pi_pair_aux ν i j hij hg
  -- Step 4: the fibre volume of the right hand side.
  have hRHS : MeasureTheory.volume
        (Set.univ.pi (fun _ : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} => A))
      = (ν Set.univ) ^ m := by
    rw [MeasureTheory.volume_pi_pi, Finset.prod_const, Finset.card_univ,
      card_subtype_ne_ne m i j hij, hν]
  -- Step 5: the free two-particle integral of the right hand side.
  have hinner : (∫⁻ q : E3 × E3, A.indicator (fun _ => (1 : ENNReal)) q.1
        * (A.indicator (fun _ => (1 : ENNReal)) q.2 * g q.1 q.2))
      = ∫⁻ a, ∫⁻ b, g a b ∂ν ∂ν := by
    have hA2 : MeasurableSet (A ×ˢ A) := hA.prod hA
    have hp : ∀ q : E3 × E3, A.indicator (fun _ => (1 : ENNReal)) q.1
        * (A.indicator (fun _ => (1 : ENNReal)) q.2 * g q.1 q.2)
        = (A ×ˢ A).indicator (fun q : E3 × E3 => g q.1 q.2) q := by
      rintro ⟨a, b⟩
      simp only [Set.indicator_apply]
      by_cases ha : a ∈ A <;> by_cases hb : b ∈ A <;> simp [ha, hb, Set.mem_prod]
    have hkey : (∫⁻ q : E3 × E3, (A ×ˢ A).indicator (fun q : E3 × E3 => g q.1 q.2) q)
        = ∫⁻ a, ∫⁻ b, g a b ∂ν ∂ν := by
      rw [lintegral_indicator hA2 (fun q : E3 × E3 => g q.1 q.2)]
      have hv2 : (volume : Measure (E3 × E3))
          = (volume : Measure E3).prod (volume : Measure E3) := Measure.volume_eq_prod E3 E3
      rw [hv2, ← Measure.prod_restrict A A]
      rw [lintegral_prod (f := fun q : E3 × E3 => g q.1 q.2) hg.aemeasurable, hνdef]
    rw [lintegral_congr hp]
    exact hkey
  -- Assembly.
  have hL : (∫⁻ x : Fin (m + 2) → E3,
        (Set.univ.pi (fun _ : Fin (m + 2) => A)).indicator (fun _ => (1 : ENNReal)) x
          * g (x i) (x j)) = (ν Set.univ) ^ m * ∫⁻ a, ∫⁻ b, g a b ∂ν ∂ν := by
    rw [hstep1, hvolpi]
    exact hpeel
  rw [hRHS, hinner]
  exact hL

end Work.BoseBoxFock

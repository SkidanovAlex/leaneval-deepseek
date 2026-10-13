import Mathlib
import Submission.Work.WilC4.monoDefs
import Submission.Work.WilC2.fibre_definable

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

/-!
# `MonoLset`/`MonoHset` are finite unions of order-connected sets

`MonoLset Y a` and `MonoHset Y a` are (verbatim) the fibres over `a` of the `∅`-definable
relations `MonoLA Y` and `MonoHA Y`.  Since `MonoLA Y`, `MonoHA Y ⊆ ℝ²` are `∅`-definable and
`OMinModels` says that every `LRc`-definable subset of the line, with parameters from the whole
model, is a finite union of order-connected sets, the only thing to do is to produce the fibre as
a definable subset of `Fin 1 → ℝ` (`fibre_definable`) and to identify it with `MonoLset Y a`
(`MonoHset Y a`).
-/

/-! ## The two `Fin 2` index reductions

`fibre_definable` substitutes the point `a` into the second coordinate using the function
`fun i : Fin 2 => if i = 0 then v 0 else a`, whereas `MonoLA`/`MonoHA` use the vector notation
`![·, ·]`.  These are the two pointwise reductions relating the two descriptions of a `Fin 2`-vector
(the index `0` and the index `1`). -/

private lemma fin2_if_zero (x a : ℝ) :
    (fun i : Fin 2 => if i = 0 then x else a) 0 = x := by
  show (if (0 : Fin 2) = 0 then x else a) = x
  rw [ite_eq_left rfl]

private lemma fin2_if_one (x a : ℝ) :
    (fun i : Fin 2 => if i = 0 then x else a) 1 = a := by
  show (if (1 : Fin 2) = 0 then x else a) = a
  rw [ite_eq_right (by decide)]

/-! ## The fibres as `Fin 1 → ℝ`-sets -/

/-- The `a`-fibre of `MonoLA Y`, in the `Fin 1 → ℝ` shape produced by `fibre_definable`. -/
private def monoLfibre (Y : Set (Fin 2 → ℝ)) (a : ℝ) : Set (Fin 1 → ℝ) :=
  {v : Fin 1 → ℝ | (fun i : Fin 2 => if i = 0 then v 0 else a) ∈ MonoLA Y}

/-- The `a`-fibre of `MonoHA Y`, in the `Fin 1 → ℝ` shape produced by `fibre_definable`. -/
private def monoHfibre (Y : Set (Fin 2 → ℝ)) (a : ℝ) : Set (Fin 1 → ℝ) :=
  {v : Fin 1 → ℝ | (fun i : Fin 2 => if i = 0 then v 0 else a) ∈ MonoHA Y}

private lemma mem_monoLfibre {Y : Set (Fin 2 → ℝ)} {a : ℝ} {v : Fin 1 → ℝ} :
    (fun i : Fin 2 => if i = 0 then v 0 else a) ∈ MonoLA Y ↔ v 0 ∈ MonoLset Y a := by
  have h0 : (fun i : Fin 2 => if i = 0 then v 0 else a) 0 = v 0 := fin2_if_zero (v 0) a
  have h1 : (fun i : Fin 2 => if i = 0 then v 0 else a) 1 = a := fin2_if_one (v 0) a
  show (∃ y y', ![(fun i : Fin 2 => if i = 0 then v 0 else a) 0, y] ∈ Y ∧
        ![(fun i : Fin 2 => if i = 0 then v 0 else a) 1, y'] ∈ Y ∧ y < y') ↔
      ∃ y y', ![v 0, y] ∈ Y ∧ ![a, y'] ∈ Y ∧ y < y'
  constructor
  · rintro ⟨y, y', H1, H2, H3⟩
    rw [h0] at H1
    rw [h1] at H2
    exact ⟨y, y', H1, H2, H3⟩
  · rintro ⟨y, y', H1, H2, H3⟩
    rw [← h0] at H1
    rw [← h1] at H2
    exact ⟨y, y', H1, H2, H3⟩

private lemma mem_monoHfibre {Y : Set (Fin 2 → ℝ)} {a : ℝ} {v : Fin 1 → ℝ} :
    (fun i : Fin 2 => if i = 0 then v 0 else a) ∈ MonoHA Y ↔ v 0 ∈ MonoHset Y a := by
  have h0 : (fun i : Fin 2 => if i = 0 then v 0 else a) 0 = v 0 := fin2_if_zero (v 0) a
  have h1 : (fun i : Fin 2 => if i = 0 then v 0 else a) 1 = a := fin2_if_one (v 0) a
  show (∃ y y', ![(fun i : Fin 2 => if i = 0 then v 0 else a) 0, y] ∈ Y ∧
        ![(fun i : Fin 2 => if i = 0 then v 0 else a) 1, y'] ∈ Y ∧ y' < y) ↔
      ∃ y y', ![v 0, y] ∈ Y ∧ ![a, y'] ∈ Y ∧ y' < y
  constructor
  · rintro ⟨y, y', H1, H2, H3⟩
    rw [h0] at H1
    rw [h1] at H2
    exact ⟨y, y', H1, H2, H3⟩
  · rintro ⟨y, y', H1, H2, H3⟩
    rw [← h0] at H1
    rw [← h1] at H2
    exact ⟨y, y', H1, H2, H3⟩

private lemma monoLfibre_eq (Y : Set (Fin 2 → ℝ)) (a : ℝ) :
    monoLfibre Y a = {v : Fin 1 → ℝ | v 0 ∈ MonoLset Y a} := by
  ext v
  exact mem_monoLfibre

private lemma monoHfibre_eq (Y : Set (Fin 2 → ℝ)) (a : ℝ) :
    monoHfibre Y a = {v : Fin 1 → ℝ | v 0 ∈ MonoHset Y a} := by
  ext v
  exact mem_monoHfibre

/-- A `Fin 1 → ℝ`-set defined by a predicate on the first coordinate determines that predicate. -/
private lemma eq_of_finOne_eq {A B : Set ℝ}
    (h : {v : Fin 1 → ℝ | v 0 ∈ A} = {v : Fin 1 → ℝ | v 0 ∈ B}) : A = B := by
  ext x
  have hx := Set.ext_iff.mp h (fun _ : Fin 1 => x)
  simpa using hx

/-! ## The theorem -/

theorem monoLHset_ordConnected {Y : Set (Fin 2 → ℝ)}
    (hLA : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (MonoLA Y))
    (hHA : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (MonoHA Y))
    (hOM : WilkiesDesign.CG.OMinModels) :
    (∀ a : ℝ, ∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧
        MonoLset Y a = ⋃₀ (s : Set (Set ℝ))) ∧
      (∀ a : ℝ, ∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧
        MonoHset Y a = ⋃₀ (s : Set (Set ℝ))) := by
  haveI : ℝ ⊨ WilkiesDesign.CG.TR :=
    inferInstanceAs (ℝ ⊨ WilkiesDesign.CG.LRc.completeTheory ℝ)
  refine ⟨?_, ?_⟩
  · intro a
    have hd : (Set.univ : Set ℝ).Definable WilkiesDesign.CG.LRc (monoLfibre Y a) :=
      Set.Definable.mono (WilC2.fibre_definable hLA (u := a)) (Set.subset_univ _)
    obtain ⟨s, hs, hX⟩ := hOM ℝ (monoLfibre Y a) hd
    refine ⟨s, hs, eq_of_finOne_eq ?_⟩
    rw [← monoLfibre_eq Y a, hX]
  · intro a
    have hd : (Set.univ : Set ℝ).Definable WilkiesDesign.CG.LRc (monoHfibre Y a) :=
      Set.Definable.mono (WilC2.fibre_definable hHA (u := a)) (Set.subset_univ _)
    obtain ⟨s, hs, hX⟩ := hOM ℝ (monoHfibre Y a) hd
    refine ⟨s, hs, eq_of_finOne_eq ?_⟩
    rw [← monoHfibre_eq Y a, hX]

end Work.WilC4

import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

set_option linter.style.haveILetI false

namespace Commons.LinearAlgebra.Submodule

open Module

/-- The number of submodules of a finite-dimensional vector space `U` over a finite field `K`
is at most `|K| ^ (finrank K U * finrank K U)`.  Indeed every submodule `W ≤ U` is the span of
at most `finrank K U` vectors, so it is the image of some element of `Fin (finrank K U) → U`
under `f ↦ span (range f)`; hence
`|Submodule K U| ≤ |U| ^ (finrank K U) = |K| ^ (finrank K U * finrank K U)`. -/
theorem natCard_submodule_le (K : Type*) [Field K] [Fintype K]
    {U : Type*} [AddCommGroup U] [Module K U] [FiniteDimensional K U] :
    Nat.card (Submodule K U) ≤
      Nat.card K ^ (Module.finrank K U * Module.finrank K U) := by
  classical
  haveI : Finite U := Module.finite_of_finite K
  set d := Module.finrank K U with hd
  have hsurj : Function.Surjective
      (fun f : Fin d → U => Submodule.span K (Set.range f)) := by
    intro W
    have hm : Module.finrank K W ≤ d := by
      rw [hd]; exact Submodule.finrank_le W
    let b : Basis (Fin (Module.finrank K W)) K W := Module.finBasis K W
    let g : Fin d → U := fun i =>
      if h : (i : ℕ) < Module.finrank K W then (b ⟨i, h⟩ : U) else 0
    have hg_apply : ∀ (i : Fin d) (h : (i : ℕ) < Module.finrank K W),
        g i = (b ⟨i, h⟩ : U) := by
      intro i h
      show (if h' : (i : ℕ) < Module.finrank K W then (b ⟨i, h'⟩ : U) else 0) = _
      rw [dif_pos h]
    have hg_zero : ∀ (i : Fin d), ¬ (i : ℕ) < Module.finrank K W → g i = 0 := by
      intro i h
      show (if h' : (i : ℕ) < Module.finrank K W then (b ⟨i, h'⟩ : U) else 0) = 0
      rw [dif_neg h]
    refine ⟨g, ?_⟩
    show Submodule.span K (Set.range g) = W
    have hbspan : Submodule.span K
        (Set.range (fun j : Fin (Module.finrank K W) => (b j : U))) = W := by
      have h1 : Set.range (fun j : Fin (Module.finrank K W) => (b j : U))
          = Submodule.subtype W '' Set.range (⇑b) := by
        ext x; constructor
        · rintro ⟨j, rfl⟩; exact ⟨b j, ⟨j, rfl⟩, rfl⟩
        · rintro ⟨y, ⟨j, rfl⟩, rfl⟩; exact ⟨j, rfl⟩
      rw [h1, ← Submodule.map_span (Submodule.subtype W), b.span_eq]
      rw [← LinearMap.range_eq_map (Submodule.subtype W), Submodule.range_subtype W]
    have hspan_eq : Submodule.span K (Set.range g)
        = Submodule.span K (Set.range (fun j : Fin (Module.finrank K W) => (b j : U))) := by
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro x ⟨i, rfl⟩
        by_cases hi : (i : ℕ) < Module.finrank K W
        · rw [hg_apply i hi]
          exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
        · rw [hg_zero i hi]
          exact Submodule.zero_mem _
      · rw [Submodule.span_le]
        rintro x ⟨j, rfl⟩
        have hj : (j : ℕ) < d := by have := j.isLt; omega
        have hgi : g ⟨j.val, hj⟩ = (b j : U) := by
          rw [hg_apply ⟨j.val, hj⟩ (by simpa only [Fin.val_mk] using j.isLt)]
        exact Submodule.subset_span
          (show (b j : U) ∈ Set.range g from ⟨⟨j.val, hj⟩, hgi⟩)
    rw [hspan_eq, hbspan]
  calc Nat.card (Submodule K U) ≤ Nat.card (Fin d → U) :=
        Nat.card_le_card_of_surjective _ hsurj
    _ = Nat.card U ^ d := by rw [Nat.card_fun, Nat.card_fin]
    _ = (Nat.card K ^ Module.finrank K U) ^ d := by
          rw [Module.natCard_eq_pow_finrank (K := K) (V := U)]
    _ = Nat.card K ^ (Module.finrank K U * d) := by rw [pow_mul]
    _ = Nat.card K ^ (Module.finrank K U * Module.finrank K U) := by rw [hd]

theorem card_submodule_le_le_pow {n : ℕ} (U : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Nat.card {W : Submodule (ZMod 2) (Fin n → ZMod 2) // W ≤ U} ≤
      2 ^ (Module.finrank (ZMod 2) U * Module.finrank (ZMod 2) U) := by
  have hbij : Nat.card {W : Submodule (ZMod 2) (Fin n → ZMod 2) // W ≤ U} =
      Nat.card (Submodule (ZMod 2) U) :=
    (Nat.card_congr (Submodule.MapSubtype.orderIso U).toEquiv).symm
  rw [hbij]
  have h := natCard_submodule_le (K := ZMod 2) (U := U)
  rwa [Nat.card_zmod] at h

end Commons.LinearAlgebra.Submodule
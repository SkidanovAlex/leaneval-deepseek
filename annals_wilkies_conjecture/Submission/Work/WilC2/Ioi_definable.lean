/-
  Area C2 (WilC2): the half-line `Set.Ioi c = {x | c < x}` is definable over any parameter set
  `T` containing `c`, in any model of `TR`.

  The mathematical input is that in a model of `TR` every nonnegative element is a square
  (`model_exists_sq`), so the field order is `LRc`-definable by the formula
  `leF x y := ∃ z, x + z * z = y` (`Basic.lean`, `definable_le`).  With order available the
  argument is elementary: over the parameters `T ∋ c`,
    `{x | c < x} = {x | c ≤ x} \ {x | x = c}`,
  where `{x | x = c}` is a singleton (defined using `c` as a parameter) and `{x | c ≤ x}` is
  obtained from the two-variable `∅`-definable set `{(x, y) | y ≤ x}` by intersecting with
  `{y = c}` and existentially quantifying `y`.  (This is the mirror image of `Iio_definable`.)
-/
import Mathlib
import Submission.Work.WilC2.Basic
import Submission.Work.WilC2.finite_definable_singleton

noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace Work.WilC2

open WilkiesDesign.CG (LR LRc TR rexpL)

/-- The singleton `{c}` is definable over any parameter set containing `c`, in the `Definable`
form used by `Definable₁`. -/
private lemma definable_eq_const_Ioi {M : Type} [LRc.Structure M] {T : Set M} {c : M}
    (hc : c ∈ T) : T.Definable LRc {v : Fin 1 → M | v 0 = c} := by
  have h := Set.Definable.singleton_of_mem (L := LRc) (A := T) hc
  simpa [Set.Definable₁, Set.mem_singleton_iff] using h

theorem Ioi_definable
    {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    (hM : M ⊨ WilkiesDesign.CG.TR) {T : Set M} {c : M} (hc : c ∈ T) :
    T.Definable₁ WilkiesDesign.CG.LRc (Set.Ioi c) := by
  classical
  have hExp : ringToLRc.IsExpansionOn M := instRingToLRcIsExpansionOn M
  -- in a model of `TR` every nonnegative element is a square, hence `≤` is definable
  have hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z := model_exists_sq hM
  -- `y ≤ x` on two-tuples is definable
  have hB : T.Definable LRc
      {w : (Fin 1 ⊕ Fin 1) → M | w (Sum.inr 0) ≤ w (Sum.inl 0)} :=
    definable_le (A := T) hsq (Sum.inr (0 : Fin 1)) (Sum.inl (0 : Fin 1))
  -- the parameter equation `y = c` on the quantified coordinate
  have hC : T.Definable LRc {w : (Fin 1 ⊕ Fin 1) → M | w (Sum.inr 0) = c} := by
    have h1 : T.Definable LRc {x : Fin 1 → M | x 0 = c} := definable_eq_const_Ioi hc
    have h2 := h1.preimage_comp (Sum.inr : Fin 1 → Fin 1 ⊕ Fin 1)
    simpa [Function.comp_apply] using h2
  -- eliminate the quantified coordinate: this leaves `{x | c ≤ x}`
  have hge : T.Definable LRc {v : Fin 1 → M | c ≤ v 0} := by
    have h := Set.Definable.exists_of_finite (hB.inter hC)
    have hset : ({v : Fin 1 → M | ∃ u : Fin 1 → M,
        Sum.elim v u ∈ ({w : (Fin 1 ⊕ Fin 1) → M | w (Sum.inr 0) ≤ w (Sum.inl 0)} ∩
          {w : (Fin 1 ⊕ Fin 1) → M | w (Sum.inr 0) = c})} : Set (Fin 1 → M))
        = {v : Fin 1 → M | c ≤ v 0} := by
      ext v
      simp only [Set.mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr, Set.mem_inter_iff]
      constructor
      · rintro ⟨u, h1, h2⟩
        rw [← h2]; exact h1
      · intro hv
        exact ⟨fun _ => c, hv, rfl⟩
    rw [hset] at h
    exact h
  -- the point `c` itself
  have heq : T.Definable LRc {v : Fin 1 → M | v 0 = c} := definable_eq_const_Ioi hc
  -- `c < x ↔ c ≤ x ∧ x ≠ c`
  have hlt : T.Definable LRc ({v : Fin 1 → M | c ≤ v 0} \ {v : Fin 1 → M | v 0 = c}) :=
    hge.sdiff heq
  have hset : ({v : Fin 1 → M | v 0 ∈ Set.Ioi c} : Set (Fin 1 → M)) =
      ({v : Fin 1 → M | c ≤ v 0} \ {v : Fin 1 → M | v 0 = c}) := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_Ioi, Set.mem_sdiff]
    constructor
    · intro h
      exact ⟨le_of_lt h, ne_of_gt h⟩
    · rintro ⟨h1, h2⟩
      exact lt_of_le_of_ne h1 (Ne.symm h2)
  unfold Set.Definable₁
  rw [hset]
  exact hlt

end Work.WilC2

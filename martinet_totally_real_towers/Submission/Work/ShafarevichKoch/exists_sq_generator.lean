import Mathlib
import Submission.Work.ShafarevichKoch.Defs

/-!
# `Work.ShafarevichKoch.exists_sq_generator`

Let `L/F` be a quadratic extension of number fields.  Then `L = F(z)` where
`z * z ∈ F`, i.e. `L` is obtained from `F` by adjoining a square root of an
element of `F` (in fact of a *unit* `x : Fˣ` of `F`).

This is the "Kummer description" of a quadratic extension used by the
Shafarevich--Koch two-descent: over a quadratic extension every element
generating the extension has square in the base field, so the extension is
Kummer and its arithmetic can be read off from `Fˣ/Fˣ²`.

## Proof

Since `[L : F] = 2` is prime, the lattice of `F`-subalgebras of `L` is a
simple order (`Subalgebra.isSimpleOrder_of_finrank_prime`).  Pick `w ∈ L \ F`.
The two vectors `1, w` are linearly independent and `L` has dimension `2`, so
`w * w = a + b * w` for some `a b : F`.  Then

`z := 2 * w - b`  satisfies  `z * z = 4 * a + b * b ∈ F`

(completing the square; we scale by `2` to avoid divisions).  Since `z ∉ F`
and `z * z ∈ F`, the subalgebra `F[z]` is neither `⊥` nor `⊤`-trivial, hence
equal to `⊤`; and `x := 4 * a + b * b` is a unit because `z ≠ 0`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ShafarevichKoch

theorem exists_sq_generator (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [FiniteDimensional F L] [IsGalois F L] (h2 : Module.finrank F L = 2) :
    ∃ (x : Fˣ) (z : L), z * z = algebraMap F L (x : F) ∧ Algebra.adjoin F ({z} : Set L) = ⊤ := by
  classical
  have hprime : Nat.Prime (Module.finrank F L) := h2 ▸ Nat.prime_two
  haveI hsimple : IsSimpleOrder (Subalgebra F L) :=
    Subalgebra.isSimpleOrder_of_finrank_prime F L hprime
  -- Step 1: an element `w` of `L` which does not lie in the image of `F`.
  have hne : (⊥ : IntermediateField F L) ≠ ⊤ := by
    intro h
    have := IntermediateField.bot_eq_top_iff_finrank_eq_one.mp h
    omega
  obtain ⟨w, hw⟩ := SetLike.exists_not_mem_of_ne_top (⊥ : IntermediateField F L) hne
  have hwr : w ∉ Set.range (algebraMap F L) := fun h => hw (IntermediateField.mem_bot.mpr h)
  -- Step 2: `{1, w}` spans `L` over `F`.
  have hspan : Submodule.span F ({1, w} : Set L) = ⊤ := by
    have hw1 : (1 : L) ≠ w := by
      intro h; exact hwr ⟨1, by rw [← h]; simp⟩
    have hle : Module.finrank F (Submodule.span F ({1, w} : Set L)) ≤ 2 := by
      have h := finrank_span_le_card (R := F) ({1, w} : Set L)
      have hcard : ({1, w} : Set L).toFinset.card = 2 := by
        rw [Set.toFinset_insert, Set.toFinset_singleton]
        rw [Finset.card_insert_of_notMem (by simpa [Finset.mem_singleton] using hw1),
          Finset.card_singleton]
      omega
    have hge : 2 ≤ Module.finrank F (Submodule.span F ({1, w} : Set L)) := by
      have hsing : Module.finrank F (Submodule.span F ({1} : Set L)) = 1 := by
        simpa using finrank_span_singleton (K := F) (v := (1 : L)) one_ne_zero
      have hlt : Submodule.span F ({1} : Set L) < Submodule.span F ({1, w} : Set L) := by
        refine lt_of_le_of_ne (Submodule.span_mono ?_) ?_
        · rw [Set.singleton_subset_iff]; simp
        · intro h
          have hwmem : w ∈ Submodule.span F ({1, w} : Set L) :=
            Submodule.subset_span (by simp)
          rw [← h] at hwmem
          obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hwmem
          exact hwr ⟨a, by rw [← ha, Algebra.algebraMap_eq_smul_one]⟩
      have := Submodule.finrank_lt_finrank_of_lt hlt
      omega
    exact Submodule.eq_top_of_finrank_eq (by rw [h2]; exact le_antisymm hle hge)
  -- Step 3: the quadratic relation `w * w = a + b * w`.
  obtain ⟨a, b, hab⟩ : ∃ a b : F, w * w = algebraMap F L a + algebraMap F L b * w := by
    have hmem : w * w ∈ Submodule.span F ({1, w} : Set L) := by
      rw [hspan]; exact Submodule.mem_top
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hmem
    exact ⟨a, b, by rw [← hab]; simp only [Algebra.smul_def, mul_one]⟩
  -- Step 4: `z := 2 * w - b` is a square root of `4 * a + b * b ∈ F`.
  set z : L := 2 * w - algebraMap F L b with hzdef
  have hzsq : z * z = algebraMap F L (4 * a + b * b) := by
    rw [hzdef]
    have h4 : (2 * w - algebraMap F L b) * (2 * w - algebraMap F L b)
        = 4 * (w * w) - 4 * (algebraMap F L b * w)
          + algebraMap F L b * algebraMap F L b := by ring
    rw [h4, hab]
    simp only [map_add, map_mul, map_ofNat]
    ring
  -- Step 5: `z` does not lie in `F`.
  have hzr : z ∉ Set.range (algebraMap F L) := by
    rw [hzdef]
    intro h
    obtain ⟨d, hd⟩ := h
    have h2L : (2 : L) ≠ 0 := by norm_num
    have h2F : (2 : F) ≠ 0 := by norm_num
    have hmul : (2 : L) * w = algebraMap F L (d + b) := by
      rw [map_add, hd]; ring
    refine hwr ⟨(d + b) / 2, ?_⟩
    have hmap : algebraMap F L ((d + b) / 2) = algebraMap F L (d + b) / 2 := by
      rw [map_div₀, map_ofNat]
    rw [hmap, ← hmul, mul_div_cancel_left₀ _ h2L]
  -- Step 6: `F[z] = ⊤`, since the lattice of `F`-subalgebras is a simple order.
  have hadj : Algebra.adjoin F ({z} : Set L) = ⊤ := by
    rcases eq_bot_or_eq_top (Algebra.adjoin F ({z} : Set L)) with h | h
    · exfalso
      have hzmem : z ∈ (⊥ : Subalgebra F L) := h ▸ Algebra.self_mem_adjoin_singleton F z
      exact hzr (Algebra.mem_bot.mp hzmem)
    · exact h
  -- Step 7: package the unit `x := 4 * a + b * b`.
  have hz0 : z ≠ 0 := fun h0 => hzr ⟨0, by rw [h0, map_zero]⟩
  have hx0 : (4 * a + b * b : F) ≠ 0 := by
    intro hx
    have h1 : z * z = 0 := by rw [hzsq, hx, map_zero]
    exact hz0 (mul_self_eq_zero.mp h1)
  refine ⟨Units.mk0 (4 * a + b * b) hx0, z, ?_, hadj⟩
  simp only [Units.val_mk0]
  exact hzsq

end Work.ShafarevichKoch

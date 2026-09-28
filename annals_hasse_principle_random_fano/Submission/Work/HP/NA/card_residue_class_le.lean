import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.NA.Setup
import Submission.Work.HP.DiagDefs
import Submission.Work.HP.NA.card_int_residue_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Number of integer coefficient vectors of bounded height in a residue class mod `W`

For `W ≥ 1`, `A ≥ 0` and a residue vector `c : Mon d n → ZMod W`,

`#{a : Mon d n → ℤ | ‖a‖ ≤ A and a ≡ c (mod W)} ≤ (2A/W + 1)^{N_{d,n}}`.

The estimate is coordinatewise: on the height ball every coordinate obeys `|a m| ≤ A`, and the
integers congruent to `c m` modulo `W` inside `[-A,A]` are `W`-separated, hence number at most
`2A/W + 1`; the total count is the product of the `N_{d,n}` coordinate bounds, which is exactly
the origin of the factor `W^{-N}` in the local (non-archimedean) main term.
-/

set_option autoImplicit false
noncomputable section

open Finset

namespace Work.HP.NA

/-- The integers in the residue class of `v` modulo `W` whose absolute value is at most `A`. -/
def resClass (W : ℕ) (A : ℝ) (v : ZMod W) : Set ℤ :=
  {x | |(x : ℝ)| ≤ A ∧ ((x : ℤ) : ZMod W) = v}

lemma mem_resClass {W : ℕ} {A : ℝ} {v : ZMod W} {x : ℤ} :
    x ∈ resClass W A v ↔ |(x : ℝ)| ≤ A ∧ ((x : ℤ) : ZMod W) = v := Iff.rfl

lemma resClass_finite (W : ℕ) (A : ℝ) (v : ZMod W) : (resClass W A v).Finite := by
  refine (Set.finite_Icc (-(⌈A⌉₊ : ℤ)) (⌈A⌉₊ : ℤ)).subset ?_
  intro x hx
  have h1 : |(x : ℝ)| ≤ A := hx.1
  obtain ⟨hlo, hhi⟩ := abs_le.mp h1
  have hle : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
  rw [Set.mem_Icc]
  constructor
  · have : ((-(⌈A⌉₊ : ℤ)) : ℝ) ≤ (x : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have : (x : ℝ) ≤ ((⌈A⌉₊ : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this

theorem card_residue_class_le (d n W : ℕ) (hW : 0 < W) (A : ℝ) (hA : 0 ≤ A)
    (c : Work.HP.Mon d n → ZMod W) :
    (Nat.card {a : Work.HP.Mon d n → ℤ // Work.HP.eNorm a ≤ A ∧ ∀ m, ((a m : ℤ) : ZMod W) = c m} : ℝ)
      ≤ (2 * A / W + 1) ^ (Work.HP.NN d n) := by
  classical
  -- the coordinatewise residue classes
  let Tm : Mon d n → Finset ℤ := fun m => (resClass_finite W A (c m)).toFinset
  have hmem : ∀ m x, x ∈ Tm m ↔ |(x : ℝ)| ≤ A ∧ ((x : ℤ) : ZMod W) = c m := by
    intro m x
    change x ∈ (resClass_finite W A (c m)).toFinset ↔ _
    rw [Set.Finite.mem_toFinset]
    exact mem_resClass
  -- the ball of the residue class is contained in the product of the coordinate classes
  have hsub : ({a : Mon d n → ℤ | eNorm a ≤ A ∧ ∀ m, ((a m : ℤ) : ZMod W) = c m} : Set _)
      ⊆ ↑(Fintype.piFinset Tm) := by
    intro a ha
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro m
    rw [hmem]
    exact ⟨le_trans (abs_coord_le_eNorm a m) ha.1, ha.2 m⟩
  have h1 : ({a : Mon d n → ℤ | eNorm a ≤ A ∧ ∀ m, ((a m : ℤ) : ZMod W) = c m} : Set _).ncard
      ≤ ∏ m, (Tm m).card := by
    calc ({a : Mon d n → ℤ | eNorm a ≤ A ∧ ∀ m, ((a m : ℤ) : ZMod W) = c m} : Set _).ncard
        ≤ ((Fintype.piFinset Tm : Finset (Mon d n → ℤ)) : Set _).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = (Fintype.piFinset Tm).card := Set.ncard_coe_finset _
      _ = ∏ m, (Tm m).card := Fintype.card_piFinset Tm
  -- the coordinatewise bound
  have hcoord : ∀ m, ((Tm m).card : ℝ) ≤ 2 * A / W + 1 := by
    intro m
    refine card_int_residue_le (W := W) (A := A) hW hA (Tm m) ?_ ?_
    · intro x hx
      exact ((hmem m x).mp hx).1
    · intro x hx y hy
      rw [hmem m x] at hx
      rw [hmem m y] at hy
      rw [hx.2, hy.2]
  have h3 : ((∏ m, (Tm m).card : ℕ) : ℝ) ≤ (2 * A / W + 1) ^ (NN d n) := by
    rw [Nat.cast_prod]
    calc ∏ m, ((Tm m).card : ℝ) ≤ ∏ _m : Mon d n, (2 * A / W + 1) :=
          Finset.prod_le_prod₀ (fun m _ => Nat.cast_nonneg _) (fun m _ => hcoord m)
      _ = (2 * A / W + 1) ^ (NN d n) := by
          rw [Finset.prod_const, Finset.card_univ]
  calc (Nat.card {a : Mon d n → ℤ // eNorm a ≤ A ∧ ∀ m, ((a m : ℤ) : ZMod W) = c m} : ℝ)
      = (({a : Mon d n → ℤ | eNorm a ≤ A ∧ ∀ m, ((a m : ℤ) : ZMod W) = c m} : Set _).ncard : ℝ) :=
        rfl
    _ ≤ ((∏ m, (Tm m).card : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ (2 * A / W + 1) ^ (NN d n) := h3

end Work.HP.NA

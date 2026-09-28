import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.Q44Setup
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.Q44Child.latZero_bound
import Submission.Work.HP.Q44Child.ballCount_le
import Submission.Work.HP.num_lattices
import Submission.Work.HP.prim_lat_window_finite

/-!
# `Work.HP.Q44Main.parts` — per-lattice counting for `quartic44`

The two per-lattice bounds used in the layer decomposition of `Work.HP.quartic44`:
`q44_perlat_T` (the form `c` does not vanish on `L`) and `q44_perlat_S` (it does), together
with the finiteness of the dyadic lattice layers.
-/

set_option autoImplicit false
noncomputable section

namespace Work.HP

open Finset

/-- The pairs of linearly independent vectors of `L ∩ B(Z)` on which `c` vanishes. -/
def pairSetT (L : Submodule ℤ (Fin 5 → ℤ)) (c : Mon 4 4 → ℤ) (Z : ℝ) :
    Set ((Fin 5 → ℤ) × (Fin 5 → ℤ)) :=
  {p | p.1 ∈ L ∧ p.2 ∈ L ∧ eNorm p.1 ≤ Z ∧ eNorm p.2 ≤ Z ∧
    LinearIndependent ℤ ![p.1, p.2] ∧ formEval 4 4 c p.1 = 0 ∧ formEval 4 4 c p.2 = 0}

/-- The pairs of linearly independent vectors of `L ∩ B(Z)`. -/
def pairSetS (L : Submodule ℤ (Fin 5 → ℤ)) (Z : ℝ) :
    Set ((Fin 5 → ℤ) × (Fin 5 → ℤ)) :=
  {p | p.1 ∈ L ∧ p.2 ∈ L ∧ eNorm p.1 ≤ Z ∧ eNorm p.2 ≤ Z ∧ LinearIndependent ℤ ![p.1, p.2]}

/-- **T-case per lattice.**  If the form `c` does not vanish identically on the rank-`3`
lattice `L`, the number of pairs of `L ∩ B(Z)` on which it vanishes is at most the square of
the `latZero_bound` count `(1 + Z/λ₁)(1 + Z/λ₂)`. -/
theorem q44_perlat_T :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : Submodule ℤ (Fin 5 → ℤ)), rk L = 3 → ∀ (c : Mon 4 4 → ℤ),
      c ∉ vanishOn L → ∀ Z : ℝ, 1 ≤ Z →
      ((pairSetT L c Z).ncard : ℝ) ≤ C * (1 + Z / lam L 1) ^ 2 * (1 + Z / lam L 2) ^ 2 := by
  obtain ⟨C, hCpos, hC⟩ := Q44Child.latZero_bound
  refine ⟨C ^ 2, by positivity, ?_⟩
  intro L hL c hc Z hZ
  classical
  set S : Set (Fin 5 → ℤ) := {x | x ∈ L ∧ eNorm x ≤ Z ∧ formEval 4 4 c x = 0} with hS
  have hSfin : S.Finite := (MDBasic.finite_eNorm_le Z).subset (fun x hx => hx.2.1)
  have hP : pairSetT L c Z ⊆ S ×ˢ S := by
    rintro ⟨x, y⟩ ⟨h1, h2, h3, h4, -, h5, h6⟩
    exact ⟨⟨h1, h3, h5⟩, ⟨h2, h4, h6⟩⟩
  have h1 : ((pairSetT L c Z).ncard : ℝ) ≤ (((S ×ˢ S).ncard : ℕ) : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hP (hSfin.prod hSfin)
  have h2 : ((S ×ˢ S).ncard : ℕ) = S.ncard * S.ncard := Set.ncard_prod
  have h3 : (S.ncard : ℝ) ≤ C * (1 + Z / lam L 1) * (1 + Z / lam L 2) := hC L hL c hc Z hZ
  have h4 : (0 : ℝ) ≤ (S.ncard : ℝ) := Nat.cast_nonneg _
  calc ((pairSetT L c Z).ncard : ℝ)
      ≤ (((S ×ˢ S).ncard : ℕ) : ℝ) := h1
    _ = (S.ncard : ℝ) * (S.ncard : ℝ) := by rw [h2]; push_cast; ring
    _ ≤ C * (1 + Z / lam L 1) * (1 + Z / lam L 2) * (C * (1 + Z / lam L 1) * (1 + Z / lam L 2)) := by
        exact mul_le_mul h3 h3 h4 (le_trans h4 h3)
    _ = C ^ 2 * (1 + Z / lam L 1) ^ 2 * (1 + Z / lam L 2) ^ 2 := by ring

/-- **S-case per lattice.**  If the form `c` vanishes identically on `L`, the number of pairs
of `L ∩ B(Z)` is at most `(ballCount L Z)²`. -/
theorem q44_perlat_S (L : Submodule ℤ (Fin 5 → ℤ)) (Z : ℝ) :
    ((pairSetS L Z).ncard : ℝ) ≤ ((ballCount L Z : ℕ) : ℝ) ^ 2 := by
  classical
  have hfin : ({x : Fin 5 → ℤ | x ∈ L ∧ eNorm x ≤ Z}).Finite :=
    (MDBasic.finite_eNorm_le Z).subset (fun x hx => hx.2)
  have hP : pairSetS L Z ⊆ ({x : Fin 5 → ℤ | x ∈ L ∧ eNorm x ≤ Z} ×ˢ
      {x : Fin 5 → ℤ | x ∈ L ∧ eNorm x ≤ Z}) := by
    rintro ⟨x, y⟩ ⟨h1, h2, h3, h4, -⟩
    exact ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
  have h1 : ((pairSetS L Z).ncard : ℝ) ≤
      ((({x : Fin 5 → ℤ | x ∈ L ∧ eNorm x ≤ Z} ×ˢ {x : Fin 5 → ℤ | x ∈ L ∧ eNorm x ≤ Z}).ncard : ℕ) : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hP (hfin.prod hfin)
  have h2 : (({x : Fin 5 → ℤ | x ∈ L ∧ eNorm x ≤ Z} ×ˢ
      {x : Fin 5 → ℤ | x ∈ L ∧ eNorm x ≤ Z}).ncard : ℕ) = ballCount L Z * ballCount L Z := by
    rw [Set.ncard_prod]; rfl
  calc ((pairSetS L Z).ncard : ℝ)
      ≤ _ := h1
    _ = ((ballCount L Z : ℕ) : ℝ) ^ 2 := by rw [h2]; push_cast; ring

/-- The dyadic lattice layer is finite. -/
theorem q44_layer_finite (s : Fin 3 → ℝ) (hs : ∀ j, 1 ≤ s j) :
    ({L : Submodule ℤ (Fin 5 → ℤ) |
        IsPrimLat L ∧ rk L = 3 ∧ ∀ j : Fin 3, lam L (j.val + 1) ≤ s j}).Finite :=
  prim_lat_window_finite (Fin 5) 3 s hs

end Work.HP

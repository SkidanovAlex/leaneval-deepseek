import Mathlib
import Submission.Work.BW.DefsMult

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Auxiliary definitions for `Work.BW.zero_estimate_stepwise` (Philippon's stepwise zero
estimate, P86*).

We collect the small combinatorial objects that the zero estimate needs:

* `boxIdx N D` — the box of exponent vectors `∏_{i : Fin N} [0, D_{i+1}]` in the torus
  directions;
* `numTheta N D θ` — the number of distinct monomial characters `θ^b`, `b ∈ boxIdx N D`;
* `cycPoint θ s` — the point `s·γ = ptTheta θ s` of `G = G_a × G_m^N`, and `cycSet θ` — the
  semigroup `{s·γ : s ∈ ℕ}`.

These are the only "new" objects: everything else is from `Defs`/`DefsMult`. -/

namespace Work.BW

/-- The box of exponent vectors `∏_{i : Fin N} [0, D_{i+1}]` in the torus directions. -/
noncomputable def boxIdx (N : ℕ) (D : Fin (N + 1) → ℕ) : Finset (Fin N → ℕ) :=
  ((Finset.univ : Finset (Fin N)).pi (fun i => Finset.range (D i.succ + 1))).image
    (fun g => fun i => g i (Finset.mem_univ i))

/-- The number of distinct monomial characters `θ^b` with `b ∈ boxIdx N D`. -/
noncomputable def numTheta (N : ℕ) (D : Fin (N + 1) → ℕ) (θ : Fin N → ℂ) : ℕ :=
  (boxIdx N D).image (fun b => ∏ i, θ i ^ (b i)) |>.card

/-- The semigroup `{s · γ : s ∈ ℕ}` inside `G = G_a × G_m^N`, where `s·γ = ptTheta θ s`. -/
def cycSet (N : ℕ) (θ : Fin N → ℂ) : Set (Fin (N + 1) → ℂ) :=
  Set.range (ptTheta θ)

/-- The exponent vector of `P` is contained in the box `∏_{i} [0, D_i]`: the monomials of `P`
with non-zero coefficient, projected. -/
noncomputable def suppIdx {N : ℕ} (P : MvPolynomial (Fin (N + 1)) ℂ) : Finset (Fin (N + 1) → ℕ) :=
  P.support.image fun s => fun i => s i

lemma boxIdx_card_le (N : ℕ) (D : Fin (N + 1) → ℕ) :
    (boxIdx N D).card ≤ ∏ i : Fin N, (D i.succ + 1) := by
  classical
  unfold boxIdx
  refine le_trans (Finset.card_image_le) (le_of_eq ?_)
  rw [Finset.card_pi]
  simp [Finset.card_range]

lemma numTheta_le (N : ℕ) (D : Fin (N + 1) → ℕ) (θ : Fin N → ℂ) :
    numTheta N D θ ≤ ∏ i : Fin N, (D i.succ + 1) :=
  le_trans (Finset.card_image_le) (boxIdx_card_le N D)

/-- For `ε = false` the class-count `cardMod` is just `S + 1`: the first coordinate identifies the
class. -/
lemma cardMod_false {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (θ : Fin N → ℂ) (S : ℕ) :
    cardMod false M θ S = S + 1 := by
  classical
  unfold cardMod
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [Finset.card_image_of_injective]
  · simp
  · intro a b h
    have h1 : ((a : ℂ)) = ((b : ℂ)) := congrArg Prod.fst h
    exact Nat.cast_injective h1

end Work.BW

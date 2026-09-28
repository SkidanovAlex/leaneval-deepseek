import Mathlib
import Submission.Work.HP.Defs

/-!
# `orth_witness`

For `x y : Fin (n+1) → ℤ`, the values `⟨u, y⟩` over the orthogonal complement
`{u : ⟨u, x⟩ = 0}` form an additive subgroup of `ℤ`.  It contains every `2×2` minor
`x_i y_j - x_j y_i`: the two-term vector with `-x_j` in coordinate `i` and `x_i` in coordinate `j`
is orthogonal to `x` and pairs with `y` to that minor.  Being a subgroup, it then contains the gcd
of the minors `gcdMinors2 x y`, which is an integer combination of them (Bézout).  Combining the
witnesses with those Bézout coefficients produces `u` with `⟨u,x⟩ = 0` and
`⟨u,y⟩ = gcdMinors2 x y`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.HP.Vero

open Finset

/-- Integer combination of "coordinate witnesses": if the vector `w b` has `f`-value `c b`, then the
combination `∑ b, w b i * ν b` has `f`-value `∑ b, c b * ν b`. -/
lemma sum_wsum_mul {ι β : Type*} [Fintype ι] [Fintype β] (w : β → ι → ℤ) (f : ι → ℤ)
    (c ν : β → ℤ) (h : ∀ b, ∑ i, w b i * f i = c b) :
    ∑ i, (∑ b, w b i * ν b) * f i = ∑ b, c b * ν b := by
  rw [show ∑ i, (∑ b, w b i * ν b) * f i = ∑ i, ∑ b, (w b i * ν b) * f i from
        Finset.sum_congr rfl (fun i _ => Finset.sum_mul ..)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  have : ∑ i, (w b i * ν b) * f i = ν b * (∑ i, w b i * f i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [this, h b]
  ring

/-- The value of `f` against a vector supported at a single point. -/
lemma sum_single_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) (c : ℤ) (f : ι → ℤ) :
    ∑ i, (Pi.single a c : ι → ℤ) i * f i = c * f a := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; rw [Pi.single_eq_of_ne hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ a) h

theorem orth_witness {n : ℕ} (x y : Fin (n + 1) → ℤ)
    (hxy : LinearIndependent ℤ ![x, y]) :
    ∃ u : Fin (n + 1) → ℤ, (∑ i, u i * x i = 0) ∧ (∑ i, u i * y i = gcdMinors2 x y) := by
  classical
  -- Bézout coefficients for the gcd of the `2 × 2` minors.
  obtain ⟨ν, hν⟩ := Finset.gcd_eq_sum_mul (R := ℤ)
    (Finset.univ : Finset (Fin (n + 1) × Fin (n + 1)))
    (fun ij : Fin (n + 1) × Fin (n + 1) => x ij.1 * y ij.2 - x ij.2 * y ij.1)
  -- For each pair of coordinates, the two-term witness `-x_{ij.2} e_{ij.1} + x_{ij.1} e_{ij.2}`.
  set wk : (Fin (n + 1) × Fin (n + 1)) → (Fin (n + 1) → ℤ) :=
    fun b => (Pi.single b.1 (-(x b.2)) : Fin (n + 1) → ℤ) + Pi.single b.2 (x b.1) with hwk
  have hwx : ∀ b, ∑ i, wk b i * x i = 0 := by
    intro b
    simp only [hwk]
    rw [show ∑ i, (((Pi.single b.1 (-(x b.2)) : Fin (n + 1) → ℤ)
            + (Pi.single b.2 (x b.1) : Fin (n + 1) → ℤ)) i * x i)
          = ∑ i, (((Pi.single b.1 (-(x b.2)) : Fin (n + 1) → ℤ)) i * x i
              + ((Pi.single b.2 (x b.1) : Fin (n + 1) → ℤ)) i * x i) from
        Finset.sum_congr rfl (fun i _ => by rw [Pi.add_apply, add_mul])]
    rw [Finset.sum_add_distrib, sum_single_mul, sum_single_mul]
    ring
  have hwy : ∀ b, ∑ i, wk b i * y i = x b.1 * y b.2 - x b.2 * y b.1 := by
    intro b
    simp only [hwk]
    rw [show ∑ i, (((Pi.single b.1 (-(x b.2)) : Fin (n + 1) → ℤ)
            + (Pi.single b.2 (x b.1) : Fin (n + 1) → ℤ)) i * y i)
          = ∑ i, (((Pi.single b.1 (-(x b.2)) : Fin (n + 1) → ℤ)) i * y i
              + ((Pi.single b.2 (x b.1) : Fin (n + 1) → ℤ)) i * y i) from
        Finset.sum_congr rfl (fun i _ => by rw [Pi.add_apply, add_mul])]
    rw [Finset.sum_add_distrib, sum_single_mul, sum_single_mul]
    ring
  refine ⟨fun i => ∑ b, wk b i * ν b, ?_, ?_⟩
  · rw [sum_wsum_mul wk x (fun _ => (0 : ℤ)) ν hwx]
    simp
  · rw [sum_wsum_mul wk y (fun b => x b.1 * y b.2 - x b.2 * y b.1) ν hwy]
    rw [← hν]
    rfl

end Work.HP.Vero

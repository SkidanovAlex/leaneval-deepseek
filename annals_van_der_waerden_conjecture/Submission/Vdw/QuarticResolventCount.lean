import Mathlib
import Submission.Vdw.QuarticImprimitive

open Polynomial

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-!
# The Chow–Dietmann count for the cubic resolvent (first part)

S. Chow and R. Dietmann, *Enumerative Galois theory for cubics and quartics*,
Adv. Math. **372** (2020) 107282, Proposition (counting): the number `R(H)` of
integer solutions `(x,a,b,c,d) ∈ [-2H,2H] × [-H,H]⁴` of

  `r(x;a,b,c,d) = x³ - b x² + (ac - 4d) x - (a²d - 4bd + c²) = 0`

satisfies `R(H) ≪ H² (log H)²`.  Combined with
`QuarticImprimitive.quartic_imprimitive_resolvent_root` (an imprimitive quartic
in the box has such a root with `|x| ≤ 4H`) this gives
`#ImprimitiveBad 4 H ≪ H³`.

This module sets up the counting: the *symmetry equation*

  `(x² - 4d) · (a² - 4(b - x)) = (xa - 2c)²`

(the "remarkable symmetry" `four_mul_resolventCubic_eval`), the two boxes
`resBox` (resolvent solutions) and `symmBox` (symmetry solutions) and the
injection `resBox H → symmBox H`, `(x,a,b,c,d) ↦ (x,a,c,d,b-x)`.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

/-- The symmetry equation `(x² - 4d)(a² - 4e) = (xa - 2c)²`. -/
def symmEq (x a c d e : ℤ) : Prop := (x ^ 2 - 4 * d) * (a ^ 2 - 4 * e) = (x * a - 2 * c) ^ 2

/-- Solutions of the resolvent equation in the box: `(x, a, b, c, d)` with
`|x| ≤ 4H`, `|a|,|b|,|c|,|d| ≤ H` and `r(x;a,b,c,d) = 0`. -/
def resBox (H : ℕ) : Set (ℤ × ℤ × ℤ × ℤ × ℤ) :=
  {t | |t.1| ≤ 4 * (H : ℤ) ∧ |t.2.1| ≤ (H : ℤ) ∧ |t.2.2.1| ≤ (H : ℤ) ∧
    |t.2.2.2.1| ≤ (H : ℤ) ∧ |t.2.2.2.2| ≤ (H : ℤ) ∧
    (resolventCubic t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2).eval t.1 = 0}

/-- Solutions of the symmetry equation in the box: `(x, a, c, d, e)` with
`|x| ≤ 4H`, `|a|,|c|,|d| ≤ H`, `|e| ≤ 5H` and `(x² - 4d)(a² - 4e) = (xa - 2c)²`. -/
def symmBox (H : ℕ) : Set (ℤ × ℤ × ℤ × ℤ × ℤ) :=
  {t | |t.1| ≤ 4 * (H : ℤ) ∧ |t.2.1| ≤ (H : ℤ) ∧ |t.2.2.1| ≤ (H : ℤ) ∧
    |t.2.2.2.1| ≤ (H : ℤ) ∧ |t.2.2.2.2| ≤ 5 * (H : ℤ) ∧
    symmEq t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2}

/-- **The reduction to the symmetry equation.**  Substituting `e = b - x` turns a solution
of the resolvent equation into a solution of the symmetry equation (via the identity
`4 * r(x) = (x² - 4d)(a² - 4(b - x)) - (xa - 2c)²`, `four_mul_resolventCubic_eval`). -/
theorem resBox_image_subset_symmBox (H : ℕ) :
    ((fun t : ℤ × ℤ × ℤ × ℤ × ℤ => (t.1, t.2.1, t.2.2.2.1, t.2.2.2.2, t.2.2.1 - t.1)) ''
      resBox H) ⊆ symmBox H := by
  rintro u ⟨t, ht, rfl⟩
  obtain ⟨hx, ha, hb, hc, hd, hr⟩ := ht
  refine ⟨hx, ha, hc, hd, ?_, ?_⟩
  · -- `|b - x| ≤ 5H`
    calc |t.2.2.1 - t.1| ≤ |t.2.2.1| + |t.1| := abs_sub _ _
      _ ≤ (H : ℤ) + 4 * (H : ℤ) := add_le_add hb hx
      _ = 5 * (H : ℤ) := by ring
  · -- the symmetry equation
    have h4 := four_mul_resolventCubic_eval t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 t.1
    rw [hr, mul_zero] at h4
    have hsub : (t.1 ^ 2 - 4 * t.2.2.2.2) * (t.2.1 ^ 2 - 4 * (t.2.2.1 - t.1))
        - (t.1 * t.2.1 - 2 * t.2.2.2.1) ^ 2 = 0 := by linarith [h4]
    show (t.1 ^ 2 - 4 * t.2.2.2.2) * (t.2.1 ^ 2 - 4 * (t.2.2.1 - t.1))
        = (t.1 * t.2.1 - 2 * t.2.2.2.1) ^ 2
    linarith [hsub]

/-- The map `(x,a,b,c,d) ↦ (x,a,c,d,b-x)` of the reduction is injective. -/
theorem resMap_injective :
    Function.Injective
      (fun t : ℤ × ℤ × ℤ × ℤ × ℤ => (t.1, t.2.1, t.2.2.2.1, t.2.2.2.2, t.2.2.1 - t.1)) := by
  rintro ⟨x, a, b, c, d⟩ ⟨x', a', b', c', d'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  subst h1 h2 h3 h4
  have : b = b' := by linarith [h5]
  subst this
  rfl

/-- The box conditions are finite. -/
theorem symmBox_finite (H : ℕ) : (symmBox H).Finite := by
  have hI (K : ℤ) : ({z : ℤ | |z| ≤ K}).Finite :=
    (Set.finite_Icc (-K) K).subset (fun z hz => by simpa [abs_le] using hz)
  refine Set.Finite.subset
    ((hI (4 * (H : ℤ))).prod ((hI (H : ℤ)).prod ((hI (H : ℤ)).prod
      ((hI (H : ℤ)).prod (hI (5 * (H : ℤ))))))) ?_
  intro t ht
  exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1⟩

/-- `#resBox H ≤ #symmBox H`. -/
theorem resBox_ncard_le_symmBox (H : ℕ) : (resBox H).ncard ≤ (symmBox H).ncard := by
  refine Set.ncard_le_ncard_of_injOn
    (f := fun t : ℤ × ℤ × ℤ × ℤ × ℤ => (t.1, t.2.1, t.2.2.2.1, t.2.2.2.2, t.2.2.1 - t.1))
    (fun a ha => resBox_image_subset_symmBox H ⟨a, ha, rfl⟩) ?_ (symmBox_finite H)
  intro a _ b _ h
  exact resMap_injective h

end Submission.Vdw

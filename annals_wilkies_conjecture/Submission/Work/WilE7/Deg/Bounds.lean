/-
  Area E7, module `Submission.Work.WilE7.Deg.Bounds`: small helper lemmas for the *degree and count
  bookkeeping* of BV's fibre-cutting recursion (`Work.WilE7.cover_cut_deg`).

  * `Work.WilE7.Deg.eval_mono_nat` — evaluation of a `ℕ`-polynomial is monotone in the argument
    (all coefficients are non-negative, so there is no need for a "monotone majorant"); this is
    what lets us turn a bound `S.deg ≤ q.eval D` into a bound on `p.eval S.deg`.
  * `Work.WilE7.Deg.subset_fiberClosure`, `Work.WilE7.Deg.fiberClosure_mono`,
    `Work.WilE7.Deg.fiberClosure_idem` — the elementary order theory of the fibrewise closure, used
    in the assembly to keep the invariant `⋃_{S ∈ worklist} π(fiberClosure S.X.set)` under control.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.projFirst_fiberClosure

set_option autoImplicit false
noncomputable section
open Classical Topology
open scoped Topology
namespace Work.WilE7.Deg
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## Polynomial evaluation -/

/-- **Evaluation of a `ℕ`-polynomial is monotone.** -/
theorem eval_mono_nat (q : Polynomial ℕ) : Monotone (fun n => q.eval n) := by
  intro a b hab
  show q.eval a ≤ q.eval b
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab i))

/-- The monotonicity of `q.eval` in usable form. -/
theorem eval_mono_eval {q : Polynomial ℕ} {a b : ℕ} (h : a ≤ b) : q.eval a ≤ q.eval b :=
  eval_mono_nat q h

/-- Composition evaluates by substitution. -/
theorem eval_comp_eval (p q : Polynomial ℕ) (D : ℕ) :
    (p.comp q).eval D = p.eval (q.eval D) := by
  rw [Polynomial.eval_comp]

/-- Evaluation is additive. -/
theorem eval_add_eval (p q : Polynomial ℕ) (D : ℕ) :
    (p + q).eval D = p.eval D + q.eval D := by
  rw [Polynomial.eval_add]

/-- Evaluation of a product. -/
theorem eval_mul_eval (p q : Polynomial ℕ) (D : ℕ) :
    (p * q).eval D = p.eval D * q.eval D := by
  rw [Polynomial.eval_mul]

/-! ## The fibrewise closure -/

/-- A set is contained in its fibrewise closure. -/
theorem subset_fiberClosure {p q : ℕ} (A : Set (Fin (p + q) → ℝ)) :
    A ⊆ WilkiesDesign.E.fiberClosure A := by
  intro z hz
  show WilkiesDesign.E.projSnd p q z ∈ closure (WilkiesDesign.E.fiber A (WilkiesDesign.E.projFirst p q z))
  apply subset_closure
  show Fin.append (WilkiesDesign.E.projFirst p q z) (WilkiesDesign.E.projSnd p q z) ∈ A
  rwa [Work.WilE7.append_projFirst_projSnd]

/-- The fibrewise closure is monotone in the set. -/
theorem fiberClosure_mono {p q : ℕ} {A B : Set (Fin (p + q) → ℝ)} (h : A ⊆ B) :
    WilkiesDesign.E.fiberClosure A ⊆ WilkiesDesign.E.fiberClosure B := by
  intro z hz
  have hz' : WilkiesDesign.E.projSnd p q z ∈
      closure (WilkiesDesign.E.fiber A (WilkiesDesign.E.projFirst p q z)) := hz
  show WilkiesDesign.E.projSnd p q z ∈ closure (WilkiesDesign.E.fiber B (WilkiesDesign.E.projFirst p q z))
  exact closure_mono (s := WilkiesDesign.E.fiber A (WilkiesDesign.E.projFirst p q z))
    (t := WilkiesDesign.E.fiber B (WilkiesDesign.E.projFirst p q z)) (fun y hy => h hy) hz'

/-- The fibrewise closure is idempotent. -/
theorem fiberClosure_idem {p q : ℕ} (A : Set (Fin (p + q) → ℝ)) :
    WilkiesDesign.E.fiberClosure (WilkiesDesign.E.fiberClosure A) =
      WilkiesDesign.E.fiberClosure A := by
  apply Set.Subset.antisymm
  · intro z hz
    have hz' : WilkiesDesign.E.projSnd p q z ∈
        closure (WilkiesDesign.E.fiber (WilkiesDesign.E.fiberClosure A)
          (WilkiesDesign.E.projFirst p q z)) := hz
    have hfib : WilkiesDesign.E.fiber (WilkiesDesign.E.fiberClosure A) (WilkiesDesign.E.projFirst p q z)
        = closure (WilkiesDesign.E.fiber A (WilkiesDesign.E.projFirst p q z)) := by
      ext y
      show Fin.append (WilkiesDesign.E.projFirst p q z) y ∈ WilkiesDesign.E.fiberClosure A ↔
        y ∈ closure (WilkiesDesign.E.fiber A (WilkiesDesign.E.projFirst p q z))
      show WilkiesDesign.E.projSnd p q (Fin.append (WilkiesDesign.E.projFirst p q z) y) ∈
          closure (WilkiesDesign.E.fiber A
            (WilkiesDesign.E.projFirst p q (Fin.append (WilkiesDesign.E.projFirst p q z) y))) ↔ _
      rw [Work.WilE7.projFirst_append, Work.WilE7.projSnd_append]
    rw [hfib, closure_closure] at hz'
    exact hz'
  · exact fiberClosure_mono (subset_fiberClosure A)

/-- The projection of the fibrewise closure of `A` contains the projection of `A`. -/
theorem projFirst_subset_projFirst_fiberClosure {n m : ℕ} (A : Set (Fin (n + m) → ℝ)) :
    WilkiesDesign.E.projFirst n m '' A ⊆
      WilkiesDesign.E.projFirst n m '' WilkiesDesign.E.fiberClosure A :=
  Set.image_mono (subset_fiberClosure A)

end Work.WilE7.Deg

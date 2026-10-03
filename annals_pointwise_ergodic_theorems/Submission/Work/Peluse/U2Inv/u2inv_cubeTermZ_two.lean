import Mathlib
import Submission.Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow
import Submission.Work.Peluse.U2Inv.Defs

/-!
# The `t = 2` cube term of the box norm is a second difference

For two shift tuples `z, z' : Fin 2 → Q₀` the cube term of Peluse's box norm at dimension `2` is
the product over the four corners `ω : Fin 2 → Bool` of the conjugated values
`C^{|ω|} f (x + ω·z + (1-ω)·z')`.  Identifying the four corners with the corners of the square
with lower corner `z'` and increment `z - z'`, the cube term is exactly the second difference
operator `Δ_{z₀-z'₀, z₁-z'₁} f` evaluated at `x + z'₀ + z'₁` (up to the order of the factors,
which is irrelevant in the commutative ring `ℂ`).

This identity is the first bookkeeping step of the `U²`-inverse argument
(`u2inv_boxSum_eq_triple`), which expands the `t = 2` box sum into a `μ_m`-weighted average of
`Δ`-operators.

The four corners `ω : Fin 2 → Bool` are indexed by the auxiliary map
`finTwoB c₀ c₁ = ![c₀, c₁] : Fin 2 → Bool`; in the order `(ff, tf, ft, tt)` used below they have
weights `0, 1, 1, 2` and corner shifts `z'₀+z'₁, z₀+z'₁, z'₀+z₁, z₀+z₁` respectively.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.U2Inv

/-! ## Indexing the four corners of a `t = 2` cube -/

/-- `finTwoB c₀ c₁` is the function `Fin 2 → Bool` with values `c₀, c₁`. -/
private def finTwoB (c₀ c₁ : Bool) : Fin 2 → Bool := fun i => if i = 0 then c₀ else c₁

@[simp] private lemma finTwoB_zero (c₀ c₁ : Bool) : finTwoB c₀ c₁ 0 = c₀ := by simp [finTwoB]
@[simp] private lemma finTwoB_one (c₀ c₁ : Bool) : finTwoB c₀ c₁ 1 = c₁ := by simp [finTwoB]

/-- The product over all `ω : Fin 2 → Bool` splits into the four corners `ff, tf, ft, tt`
(associativity and commutativity make the indicated bracketing immaterial). -/
private lemma prod_univ_finTwoB {M : Type*} [CommMonoid M] (g : (Fin 2 → Bool) → M) :
    (∏ ω : Fin 2 → Bool, g ω)
      = g (finTwoB false false) * g (finTwoB true false)
        * g (finTwoB false true) * g (finTwoB true true) := by
  let e : (Fin 2 → Bool) ≃ Bool × Bool :=
    { toFun := fun ω => (ω 0, ω 1)
      invFun := fun p => finTwoB p.1 p.2
      left_inv := by intro ω; funext i; fin_cases i <;> simp
      right_inv := by intro p; obtain ⟨a, b⟩ := p; simp [finTwoB] }
  have hes : ∀ p : Bool × Bool, e.symm p = finTwoB p.1 p.2 := by intro p; rfl
  rw [← Equiv.prod_comp e.symm g, Fintype.prod_prod_type]
  simp only [hes, Fintype.prod_bool]
  ac_rfl

/-! ## The weight `|ω|` and the corner shift at the four corners -/

@[simp] private lemma weight_finTwoB_ff : Work.Peluse.weight (finTwoB false false) = 0 := by
  decide
@[simp] private lemma weight_finTwoB_tf : Work.Peluse.weight (finTwoB true false) = 1 := by
  decide
@[simp] private lemma weight_finTwoB_ft : Work.Peluse.weight (finTwoB false true) = 1 := by
  decide
@[simp] private lemma weight_finTwoB_tt : Work.Peluse.weight (finTwoB true true) = 2 := by
  decide

private lemma cornerShift_finTwoB_ff (h h' : Fin 2 → ℤ) :
    Work.Peluse.cornerShift h h' (finTwoB false false) = h' 0 + h' 1 := by
  rw [Work.Peluse.cornerShift, Fin.sum_univ_two]; simp [finTwoB]

private lemma cornerShift_finTwoB_tf (h h' : Fin 2 → ℤ) :
    Work.Peluse.cornerShift h h' (finTwoB true false) = h 0 + h' 1 := by
  rw [Work.Peluse.cornerShift, Fin.sum_univ_two]; simp [finTwoB]

private lemma cornerShift_finTwoB_ft (h h' : Fin 2 → ℤ) :
    Work.Peluse.cornerShift h h' (finTwoB false true) = h' 0 + h 1 := by
  rw [Work.Peluse.cornerShift, Fin.sum_univ_two]; simp [finTwoB]

private lemma cornerShift_finTwoB_tt (h h' : Fin 2 → ℤ) :
    Work.Peluse.cornerShift h h' (finTwoB true true) = h 0 + h 1 := by
  rw [Work.Peluse.cornerShift, Fin.sum_univ_two]; simp [finTwoB]

/-! ## The iterates of `star` occurring as `C^{|ω|}` -/

private lemma starIterate_zero (a : ℂ) : (star^[0]) a = a := rfl

private lemma starIterate_one (a : ℂ) : (star^[1]) a = star a := by
  rw [Function.iterate_one]

private lemma starIterate_two (a : ℂ) : (star^[2]) a = a := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply', Function.iterate_one]
  simp

/-! ## The identity -/

theorem u2inv_cubeTermZ_two (Q0 : Finset ℤ) (f : ℤ → ℂ)
    (z z' : (i : Fin 2) → {x : ℤ // x ∈ Q0}) (x : ℤ) :
    Work.Peluse.BoxNorm.cubeTermZ (fun _ : Fin 2 => Q0) f z z' x
      = Work.Peluse.U2Inv.DeltaZ ((z 0).1 - (z' 0).1) ((z 1).1 - (z' 1).1)
          f (x + (z' 0).1 + (z' 1).1) := by
  rw [Work.Peluse.BoxNorm.cubeTermZ, prod_univ_finTwoB]
  simp only [weight_finTwoB_ff, weight_finTwoB_tf, weight_finTwoB_ft, weight_finTwoB_tt,
    cornerShift_finTwoB_ff, cornerShift_finTwoB_tf, cornerShift_finTwoB_ft, cornerShift_finTwoB_tt,
    starIterate_zero, starIterate_one, starIterate_two]
  rw [Work.Peluse.U2Inv.DeltaZ]
  ring_nf

end Work.Peluse.U2Inv

/-
# The raw (unnormalised) box quantity of order `t`

Peluse's box-norm power of order `t` on the direction sets `Q : Fin t → Finset ℤ`, the window `S`
and the function `f` is (Definition 2.1 of S. Peluse, *Bounds for sets with no polynomial
progressions*, Forum of Math. Pi **8** (2020), e16)

`boxNormPow t Q S f = |S|⁻¹ (∏_i |Q i|⁻¹)² · ‖∑_{h,h'} ∑_x ∏_{ω} C^{|ω|} f (x + ω·h + (1-ω)·h')‖`,

i.e. the cube average normalised by the *cardinalities* of the direction sets.  For the
"comparison at different scales" arguments (`Submission/Work/Peluse/TransferUp/`) it is convenient
to work with the *unnormalised* quantity, in which the directions `h, h'` are summed over the full
product `∏_i Q i` without dividing by `∏_i |Q i|²`:

`rawPow t Q S f = (∏_i |Q i|²) · boxNormPow t Q S f`.

The point of the normalisation is that `rawPow` is *monotone* in the direction sets: growing `Q i`
(each coordinate separately) enlarges the range of the cube sum, all of whose terms are nonnegative
reals.  For `t = 1` this fails (the level-one cube sum is `∑_x ‖∑_{h ∈ Q 0} f (x + h)‖²`, whose
summands change with `Q 0`), which is exactly why the target statement
`Work.Peluse.TransferUp.boxNormPow_arithIcc_raw_mono` assumes `2 ≤ t`.

## Main definitions

* `Work.Peluse.TransferUp.rawPow`
-/
import Mathlib
import Submission.Work.Peluse.Basic

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.TransferUp

noncomputable section

/-- The **raw box quantity** of order `t`: the `2^t`-th power of Peluse's box norm with the
normalising factor `∏_i |Q i|²` removed, i.e. `(∏_i |Q i|²) · ‖f‖^{2^t}_{□^t_{Q}(S)}`. -/
def rawPow (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) : ℝ :=
  (∏ i : Fin t, ((Q i).card : ℝ) ^ 2) * Work.Peluse.boxNormPow t Q S f

/-- `rawPow` is nonnegative (it is the product of the nonnegative normalising factor with the
modulus `boxNormPow`). -/
lemma rawPow_nonneg (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) :
    0 ≤ rawPow t Q S f := by
  rw [rawPow]
  exact mul_nonneg (Finset.prod_nonneg fun i _ => sq_nonneg _) (norm_nonneg _)

end


/-- The tuple obtained by putting `A` in front of the tuple `Q : Fin t → Finset ℤ`.  (A
non-dependent stand-in for `Fin.cons`, with the two computation rules as `simp` lemmas.) -/
def consTup {t : ℕ} (A : Finset ℤ) (Q : Fin t → Finset ℤ) : Fin (t + 1) → Finset ℤ :=
  Fin.cases A Q

@[simp] lemma consTup_zero {t : ℕ} (A : Finset ℤ) (Q : Fin t → Finset ℤ) :
    consTup A Q 0 = A := rfl

@[simp] lemma consTup_succ {t : ℕ} (A : Finset ℤ) (Q : Fin t → Finset ℤ) (i : Fin t) :
    consTup A Q i.succ = Q i := rfl

/-- Every tuple is its own cons against its tail. -/
lemma consTup_self {t : ℕ} (Q : Fin (t + 1) → Finset ℤ) :
    consTup (Q 0) (fun i => Q i.succ) = Q := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j => rfl

end Work.Peluse.TransferUp

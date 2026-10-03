import Mathlib
import Submission.Work.Peluse.SwapE.linearInLawAux

/-!
# `SwapE` — the cube mass of a slot value with a large coordinate vanishes

`cubeMassRaw d f n` is the un-normalised cube mass of the slot value `n ∈ ℤ^d`:
`∑'_x ∏_{ω : Fin d → Bool} C^{|ω|} f (x + ω·n)`.

The lemma below is the vanishing half of the *support* of the cube mass as a function of `n`:
if `f` is supported in `[-N,N]` and the `k`-th slot coordinate has modulus `> 2N`, then the
cube mass is `0`.  The point is that the cube summand is a *product* over all corners `ω`, and
the two corners `ω ≡ false` and `ω = {k}` already force one of the two factors `f x`,
`C f (x + n k)` to vanish: either `|x| > N`, or `|x + n k| ≥ |n k| − |x| > 2N − N = N`.
Hence every summand is `0`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.SwapE

open Work.Peluse

noncomputable section

/-- Iterated conjugation kills `0` whatever the exponent. -/
private lemma starIterate_zero (m : ℕ) : ((star)^[m]) (0 : ℂ) = 0 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Function.iterate_succ_apply', ih, star_zero]

/-- At the corner `ω ≡ false` the cube shift is `0`. -/
private lemma cornerShift_zero_allFalse {d : ℕ} (n : Fin d → ℤ) :
    cornerShift n (0 : Fin d → ℤ) (fun _ : Fin d => false) = 0 := by
  simp [cornerShift]

/-- The weight of the corner `ω ≡ false` is `0`. -/
private lemma weight_allFalse {d : ℕ} :
    weight (fun _ : Fin d => false) = 0 := by
  simp [weight]

/-- At the corner which is `true` exactly at the slot `k`, the cube shift is `n k`. -/
private lemma cornerShift_zero_update {d : ℕ} (n : Fin d → ℤ) (k : Fin d) :
    cornerShift n (0 : Fin d → ℤ) (Function.update (fun _ : Fin d => false) k true) = n k := by
  simp only [cornerShift]
  rw [Finset.sum_eq_single k]
  · simp
  · intro i _ hi
    simp [hi]
  · intro hk'
    exact absurd (Finset.mem_univ k) hk'

/-- `|n k| ≤ |x + n k| + |x|`, by the triangle inequality. -/
private lemma natAbs_le_natAbs_add {d : ℕ} (n : Fin d → ℤ) (k : Fin d) (x : ℤ) :
    (n k).natAbs ≤ (x + n k).natAbs + x.natAbs := by
  have := Int.natAbs_add_le (x + n k) (-x)
  rw [Int.natAbs_neg] at this
  rwa [show (x + n k) + -x = n k by ring] at this

theorem cubeMassRaw_eq_zero {d : ℕ} {N : ℕ} {f : ℤ → ℂ} (hf : Work.Peluse.SupportIn f N)
    (n : Fin d → ℤ) (k : Fin d) (hk : 2 * N < (n k).natAbs) :
    Work.Peluse.SwapE.cubeMassRaw d f n = 0 := by
  -- Every single summand of the `∑'` vanishes.
  have hprod : ∀ x : ℤ, (∏ ω : Fin d → Bool,
      (star^[Work.Peluse.weight ω])
        (f (x + cornerShift n (0 : Fin d → ℤ) ω))) = 0 := by
    intro x
    by_cases hx : N < x.natAbs
    · -- the corner `ω ≡ false` contributes the factor `f x`, which vanishes
      refine Finset.prod_eq_zero (Finset.mem_univ (fun _ : Fin d => false)) ?_
      rw [weight_allFalse, cornerShift_zero_allFalse, Function.iterate_zero_apply]
      simpa using hf x hx
    · -- otherwise the corner which is `true` at `k` contributes `C (f (x + n k)) = 0`
      have hx' : x.natAbs ≤ N := not_lt.mp hx
      refine Finset.prod_eq_zero
        (Finset.mem_univ (Function.update (fun _ : Fin d => false) k true)) ?_
      rw [cornerShift_zero_update]
      have hfar : N < (x + n k).natAbs := by
        have h1 := natAbs_le_natAbs_add n k x
        omega
      rw [hf _ hfar, starIterate_zero]
  rw [Work.Peluse.SwapE.cubeMassRaw]
  have h0 : (fun x : ℤ => ∏ ω : Fin d → Bool,
      (star^[Work.Peluse.weight ω])
        (f (x + cornerShift n (0 : Fin d → ℤ) ω))) = 0 := by
    funext x
    exact hprod x
  rw [h0]
  exact tsum_zero

end

end Work.Peluse.SwapE

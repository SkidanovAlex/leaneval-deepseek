import Mathlib
import Submission.Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow

/-!
# Peeling the first coordinate of the raw box sum

The raw (unnormalised) box sum of order `t + 1` on `Q : Fin (t+1) → Finset ℤ` is

`rawSum (t+1) Q f = ∑_{h, h'} ∑'_x ∏_{ω : Fin (t+1) → Bool} C^{|ω|} f (x + ω·h + (1-ω)·h')`.

Splitting off the first coordinate of both shift tuples, `h = (a, hs)`, `h' = (b, hs')`, the cube
term factorises (Peluse, *Bounds for sets with no polynomial progressions*, §2) as

`∏_{ω} C^{|ω|} f (x + ω·(a,hs) + (1-ω)·(b,hs'))
    = redCube Q hs hs' f (x + b) · conj (redCube Q hs hs' f (x + a))`,

where `redCube Q hs hs' f` is the cube term of one lower dimension.  The present lemma records
exactly this factorisation of the whole raw sum, i.e. the peels the two outermost shift sums of
`rawSum (t+1)` into the `Q 0`-sums `a`, `b` and the halved shift sums `hs`, `hs'`.

## Reference

S. Peluse, *Bounds for sets with no polynomial progressions*, Forum of Math. Pi **8** (2020), e16,
§2 (Definitions 2.1–2.2 and Lemma 2.3).
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Peel

/-- Peeling the first coordinate of the two shift tuples of the raw box sum. -/
theorem rawSum_succ_peel (t : ℕ) (Q : Fin (t + 1) → Finset ℤ) (f : ℤ → ℂ) :
    Work.Peluse.BoxNorm.rawSum (t + 1) Q f
      = ∑ hs : (i : Fin t) → {x : ℤ // x ∈ Q i.succ},
        ∑ hs' : (i : Fin t) → {x : ℤ // x ∈ Q i.succ},
        ∑ a : {y : ℤ // y ∈ Q 0}, ∑ b : {y : ℤ // y ∈ Q 0},
          ∑' x : ℤ, Work.Peluse.BoxNorm.redCube Q hs hs' f (x + (b : ℤ))
            * star (Work.Peluse.BoxNorm.redCube Q hs hs' f (x + (a : ℤ))) := by
  rw [Work.Peluse.BoxNorm.rawSum]
  -- split both shift sums along their first coordinate
  simp only [Work.Peluse.BoxNorm.Aux.sum_cons_equiv]
  -- bring the two `Q 0`-sums to the inside
  refine (Finset.sum_congr rfl (fun hs _ => Finset.sum_comm)).trans ?_
  refine Finset.sum_congr rfl fun hs _ => Finset.sum_congr rfl fun hs' _ => ?_
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  -- the cube term factorises into `redCube · conj redCube`
  refine tsum_congr fun x => ?_
  rw [Work.Peluse.BoxNorm.Aux.cons_val a hs, Work.Peluse.BoxNorm.Aux.cons_val b hs']
  rw [Work.Peluse.BoxNorm.cubeTerm_cons]
  simp only [Work.Peluse.BoxNorm.redCube]

end Work.Peluse.Peel

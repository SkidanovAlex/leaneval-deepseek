import Mathlib
import Submission.Work.Higman.QuadAux
import Submission.Work.Higman.polyRep_add

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The double Frobenius expansion of a biadditive map

This is the first half of the proof of `Work.Higman.bilinear_frob`, with the symmetry and
diagonal hypotheses (and the corresponding conclusions) removed.  It is what the final step of
Higman's Lemma 8 needs: the bracket pairing `V × W → W` is biadditive but not symmetric.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

/-- A biadditive map `F × F → F` over a finite field of cardinality `2 ^ n` is a double sum of
Frobenius monomials. -/
theorem biadditive_frob {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2] {n : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (B : F → F → F)
    (hx : ∀ y x x', B (x + x') y = B x y + B x' y)
    (hy : ∀ x y y', B x (y + y') = B x y + B x y') :
    ∃ d : ℕ → ℕ → F, ∀ x y, B x y = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
        d k l * x ^ (2 ^ k) * y ^ (2 ^ l) := by
  classical
  -- coefficient of `x ^ (2 ^ k)` in the Frobenius expansion of `B · y`
  let a : ℕ → F → F := fun k y => (polyRep (fun x => B x y)).coeff (2 ^ k)
  have hA : ∀ y x, B x y = ∑ k ∈ Finset.range n, a k y * x ^ (2 ^ k) := by
    intro y x
    exact additive_frob hcard (fun x => B x y) (fun x x' => hx y x x') x
  -- additivity of each `a k`, from linearity of `polyRep`
  have ha_add : ∀ k, ∀ y y', a k (y + y') = a k y + a k y' := by
    intro k y y'
    have hp : polyRep (fun x => B x (y + y')) =
        polyRep (fun x => B x y) + polyRep (fun x => B x y') := by
      rw [show (fun x => B x (y + y')) = (fun x => B x y + B x y') from
        funext (fun x => hy x y y')]
      exact polyRep_add (fun x => B x y) (fun x => B x y')
    show (polyRep (fun x => B x (y + y'))).coeff (2 ^ k) =
      (polyRep (fun x => B x y)).coeff (2 ^ k) + (polyRep (fun x => B x y')).coeff (2 ^ k)
    rw [hp, Polynomial.coeff_add]
  -- the two-variable coefficients
  let d : ℕ → ℕ → F := fun k l => (polyRep (a k)).coeff (2 ^ l)
  have hd : ∀ k y, a k y = ∑ l ∈ Finset.range n, d k l * y ^ (2 ^ l) := by
    intro k y
    exact additive_frob hcard (a k) (ha_add k) y
  refine ⟨d, fun x y => ?_⟩
  rw [hA y x]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hd k y, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

end Work.Higman

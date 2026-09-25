import Mathlib
import Submission.Work.LT.relT_defs
import Submission.Work.LT.relT_l2

/-!
# Contraction of the partial `U`-Fourier synthesis

Let `G = SL₃(ℤ/p)` and let `fhat p a b c z h` be the `z`-th `U`-Fourier coefficient of `h`
along the column subgroup `U ≅ (ℤ/p)²` (`Submission/Work/LT/relT_defs.lean`).  Writing
`P_B h = ∑_{z ∈ B} fhat p a b c z h` for the synthesis operator attached to a set `B` of
characters, the two hypotheses below say

* (Fourier inversion) `∑_{z} fhat p a b c z h = h`, and
* (orthogonality of the isotypic components) `l2sq (P_B h) = ∑_{z ∈ B} l2sq (fhat p a b c z h)`
  for every `B`.

Under these two hypotheses the partial synthesis `P_B` is a contraction in `ℓ²`:
`l2norm (P_B h) ≤ l2norm h`.  Indeed, `l2sq (P_B h) = ∑_{z ∈ B} l2sq (fhat p a b c z h)` is a
sub-sum of the nonnegative numbers `l2sq (fhat p a b c z h)`, whose total is
`l2sq (∑_z fhat p a b c z h) = l2sq h`, and `l2norm = √(l2sq ·)` is monotone.
-/

namespace Work.LT

theorem relT_smooth_contract :
    ∀ (p : ℕ) [Fact p.Prime] {a b c : Fin 3},
      (∀ (h : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ)
           (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)),
          ∑ z : ZMod p × ZMod p, fhat p a b c z h g = h g) →
      (∀ (h : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ) (B : Finset (ZMod p × ZMod p)),
          l2sq (fun g => ∑ z ∈ B, fhat p a b c z h g) = ∑ z ∈ B, l2sq (fhat p a b c z h)) →
      ∀ (B : Finset (ZMod p × ZMod p))
        (h : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ),
        l2norm (fun g => ∑ z ∈ B, fhat p a b c z h g) ≤ l2norm h := by
  intro p hp a b c hsum horth B h
  -- Orthogonality together with Fourier inversion identifies the total mass `l2sq h` with the
  -- sum of the `l2sq`-masses of the individual Fourier coefficients.
  have hu : l2sq (fun g => ∑ z : ZMod p × ZMod p, fhat p a b c z h g)
      = ∑ z : ZMod p × ZMod p, l2sq (fhat p a b c z h) := by
    simpa using horth h Finset.univ
  have hfun : (fun g => ∑ z : ZMod p × ZMod p, fhat p a b c z h g) = h :=
    funext fun g => hsum h g
  rw [hfun] at hu
  -- The partial sum over `B` is a sub-sum of nonnegative terms.
  have hle : ∑ z ∈ B, l2sq (fhat p a b c z h)
      ≤ ∑ z : ZMod p × ZMod p, l2sq (fhat p a b c z h) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
      (fun i _ _ => l2sq_nonneg _)
  have hle' : ∑ z ∈ B, l2sq (fhat p a b c z h) ≤ l2sq h := by
    rw [hu]
    exact hle
  rw [l2norm, l2norm, horth h B]
  exact Real.sqrt_le_sqrt hle'

end Work.LT

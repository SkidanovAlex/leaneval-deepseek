import Mathlib
import Submission.Work.BW.DefsB
import Submission.Work.BW.wuestholzDefs
import Submission.Work.BW.prodX_mem_homPiece
import Submission.Work.BW.eval_prodX_conePt
import Submission.Work.BW.prod_zpow_eq_prod_toNat

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! # The monomial family behind `unitMon`/`dualMon`

`unitMon M j = ∏_i X_{i+1,1}^{M_j i⁺} X_{i+1,0}^{M_j i⁻}` and `dualMon M j` is the same
product with the two exponents exchanged.  Both are instances of the two-parameter family
`genMul a b = ∏_i X_{i+1,1}^{a i} X_{i+1,0}^{b i}`, collected here so that the facts about it
(multihomogeneity, evaluation at a cone point, and the `derH`-eigenvalue identity
`derH w (genMul a b) = (∑_i a i · w_{i+1}) · genMul a b`) can be proved once and reused. -/

namespace Work.BW

/-- The torus monomial `∏_i X_{i+1,1}^{a i} · X_{i+1,0}^{b i}` on the `N` torus factors of
`(P¹)^{N+1}` (no `X_{0,0}`/`X_{0,1}` factor). -/
noncomputable def genMul {N : ℕ} (a b : Fin N → ℕ) : MR N :=
  ∏ i : Fin N, MvPolynomial.X (((i.succ : Fin (N + 1)), (1 : Fin 2))) ^ (a i) *
    MvPolynomial.X (((i.succ : Fin (N + 1)), (0 : Fin 2))) ^ (b i)

/-- The multidegree of `genMul a b`: `∑_i (a i · e_{i+1} + b i · e_{i+1})`
(both variables of the `i`-th `P¹` factor have weight `e_i`). -/
noncomputable def gdeg {N : ℕ} (a b : Fin N → ℕ) : Fin (N + 1) →₀ ℕ :=
  ∑ i : Fin N, (a i • (Finsupp.single (i.succ : Fin (N + 1)) 1 : Fin (N + 1) →₀ ℕ) +
    b i • (Finsupp.single (i.succ : Fin (N + 1)) 1 : Fin (N + 1) →₀ ℕ))

/-- Swapping the two exponent families does not change the multidegree. -/
lemma gdeg_comm {N : ℕ} (a b : Fin N → ℕ) : gdeg a b = gdeg b a := by
  simp only [gdeg]
  exact Finset.sum_congr rfl fun i _ => add_comm _ _

/-- `unitMon` is `genMul` with the exponents `(M j i)⁺`, `(M j i)⁻`. -/
lemma unitMon_eq_genMul {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (j : Fin ρ) :
    unitMon M j = genMul (fun i => (M j i).toNat) (fun i => (-(M j i)).toNat) := rfl

/-- `dualMon` is `genMul` with the two exponent families exchanged. -/
lemma dualMon_eq_genMul {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (j : Fin ρ) :
    dualMon M j = genMul (fun i => (-(M j i)).toNat) (fun i => (M j i).toNat) := by
  simp only [dualMon, genMul, mul_comm]

end Work.BW

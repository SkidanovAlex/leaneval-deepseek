import Submission.Work.Stems.Hur2c.PsiLinGen
import Submission.Work.Stems.HomAdd.psiKills

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Hutchings' `(2.5)` in additive form: `ΨLin` kills boundaries

`Work.Stems.HomAdd.PsiKillsBoundary` (which is `Work.RatHurewicz.Psi_kills_boundary`, Hutchings'
`(2.5)`) says that for every `(m+3)`-cube `τ` the *multiplicative* alternating product of the
classes of the based-ifications of its faces is `1`.

Here it is converted into the additive statement about the linearised map
`Work.Stems.Hur2c.psiLinGen`, which is the form in which the Hurewicz argument consumes it:

* `psiLinGen_cubD_single` — `ΨLin (∂ τ) = 0` for a single `(m+3)`-cube `τ`;
* `psiLinGen_cubD_eq_zero` — `ΨLin (∂ c) = 0` for every `(m+3)`-chain `c` (by linearity).

Together with **(Z)** (`Work.Stems.Hur2c.psiLinGen_single_based`) these are the two structural
properties of `Ψ` used in the proof of the Hurewicz theorem recorded in
`Submission/Work/Stems/PSI_DEG_NOTES.md`.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical
open Work.RatHurewicz

namespace Work.Stems.Hur2c

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- **(Y)**, single cube, in additive form: `ΨLin` kills the boundary of every `(m+3)`-cube. -/
theorem psiLinGen_cubD_single (N m : ℕ) [Nontrivial (Fin (m + 2))] {x₀ : X}
    (K : Tower x₀ N) (hN : m + 1 ≤ N) (τ : C(IC (m + 3), X)) :
    psiLinGen N m K hN (cubD (m + 2) X (Finsupp.single τ 1)) = 0 := by
  letI : Group (HomotopyGroup (Fin (m + 2)) X x₀) := HomotopyGroup.group (Fin (m + 2))
  have h := Work.Stems.HomAdd.PsiKillsBoundary N m K hN τ
  -- the same product, indexed by `i` alone
  have hprod : (∏ i : Fin (m + 3),
        (clPsi N m K hN (faceCube i (cval 0) τ)) ^ ((-1 : ℤ) ^ (i : ℕ)) *
          (clPsi N m K hN (faceCube i (cval 1) τ)) ^ (-((-1 : ℤ) ^ (i : ℕ)))) = 1 := by
    rw [← show (∏ i : Fin (m + 3), ∏ b : Fin 2,
          (clPsi N m K hN (faceCube i (cval b) τ)) ^ ((-1 : ℤ) ^ ((i : ℕ) + (b : ℕ))))
        = ∏ i : Fin (m + 3),
          ((clPsi N m K hN (faceCube i (cval 0) τ)) ^ ((-1 : ℤ) ^ (i : ℕ)) *
            (clPsi N m K hN (faceCube i (cval 1) τ)) ^ (-((-1 : ℤ) ^ (i : ℕ)))) from by
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Fin.prod_univ_two]
      have h0 : (-1 : ℤ) ^ ((i : ℕ) + ((0 : Fin 2) : ℕ)) = (-1 : ℤ) ^ (i : ℕ) := by
        rw [Fin.val_zero, Nat.add_zero]
      have h1 : (-1 : ℤ) ^ ((i : ℕ) + ((1 : Fin 2) : ℕ)) = -((-1 : ℤ) ^ (i : ℕ)) := by
        rw [Fin.val_one, pow_succ]
        ring
      rw [h0, h1]]
    exact h
  -- its additive counterpart
  have hsum : (∑ i : Fin (m + 3), Additive.ofMul
        ((clPsi N m K hN (faceCube i (cval 0) τ)) ^ ((-1 : ℤ) ^ (i : ℕ)) *
          (clPsi N m K hN (faceCube i (cval 1) τ)) ^ (-((-1 : ℤ) ^ (i : ℕ))))) = 0 := by
    rw [← ofMul_prod Finset.univ, hprod, ofMul_one]
  rw [cubD_single, map_sum]
  simp only [map_zsmul, map_sub, psiLinGen_single]
  refine (Finset.sum_congr rfl (fun i _ => ?_)).trans hsum
  rw [← ofMul_div, ← ofMul_zpow, div_eq_mul_inv, mul_zpow, inv_zpow, zpow_neg]
  rfl

/-- **(Y)** for chains: `ΨLin` kills the boundary of every `(m+3)`-chain. -/
theorem psiLinGen_cubD_eq_zero (N m : ℕ) [Nontrivial (Fin (m + 2))] {x₀ : X}
    (K : Tower x₀ N) (hN : m + 1 ≤ N) (c : Cub (m + 3) X) :
    psiLinGen N m K hN (cubD (m + 2) X c) = 0 := by
  refine Finsupp.induction_linear
    (motive := fun c => psiLinGen N m K hN (cubD (m + 2) X c) = 0) c ?_ ?_ ?_
  · rw [map_zero, map_zero]
  · intro f g hf hg
    rw [map_add, map_add, hf, hg, add_zero]
  · intro a k
    rw [show Finsupp.single a k = k • Finsupp.single a (1 : ℤ) from by
      rw [Finsupp.smul_single', mul_one]]
    rw [map_smul, map_smul, psiLinGen_cubD_single N m K hN a, smul_zero]

end

end Work.Stems.Hur2c

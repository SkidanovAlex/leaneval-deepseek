/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# The dyadic matrix quantities of a Krawczyk certificate, as real numbers

`Work.SeedCert.KrawData` (`A1Cert.lean`) computes the four *dyadic* scalars of the Krawczyk
criterion — `α = Σ_{ij} |(M A - 1)_{ij}|`, `β = Σ_{ij} |M_{ij}|`, `ε = Σ_{ij} Δ_{ij}`, and the
residual bound `residBound = ‖Φ u₀‖`, together with `etaBound = β · residBound` — as exact
dyadics, using the dyadic matrix operations `matSumDya`, `matAbsDya`, `matSubDya`, `matMulDya`,
`matIdDya`.

The analytic layer (`krawczyk_numeric.lean`) needs the corresponding *real* quantities
`α = ‖1 - matLin M · matLin A‖`-type bounds, `β = Σ|M_{ij}|`, `ε = Σ Δ_{ij}` and the
nonnegativity of all of them, phrased with the real matrix operations `matSum`, `matAbs`,
`matSub`, `matMul`, `matId` of `Mat3.lean`.  This file provides the bridge: the coercion
`Dya.toReal` commutes with every one of those operations, so the dyadic certificate really does
certify the real inequalities.

## Contents

* `matdya_matSumDya_toReal`, `matdya_matSumDya_matAbsDya_toReal` — `toReal` commutes with the
  right-nested entrywise sum, and `matAbsDya` becomes `matAbs`;
* `matdya_matMulDya_toReal`, `matdya_matIdDya_toReal`, `matdya_matSubDya_toReal_apply` — the
  entrywise commutation for the remaining matrix operations;
* `matdya_eps_toReal`, `matdya_beta_toReal`, `matdya_alpha_toReal` — the three identities;
* `matdya_matSum_matAbs_nonneg`, `matdya_maxAbs_toReal_nonneg`, `matdya_max_toReal_nonneg` —
  nonnegativity of the sums of absolute values and of the `Dya.max`/`Dya.maxAbs` combinations;
* `matdya_eps_nonneg`, `matdya_beta_nonneg`, `matdya_alpha_nonneg`,
  `matdya_residBound_nonneg`, `matdya_etaBound_nonneg`.

Nothing here uses the tricorn; it is pure bookkeeping between `A1Cert.lean` and `Mat3.lean`.
-/
import Mathlib
import Submission.Work.SeedCertNum.A1Cert
import Submission.Work.SeedCertNum.Mat3

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertNum

open Work.SeedCert

/-! ## `toReal` commutes with the dyadic matrix operations -/

/-- `Dya.toReal` commutes with the right-nested entrywise sum `matSumDya`. -/
theorem matdya_matSumDya_toReal (a : Fin 3 → Fin 3 → Dya) :
    (matSumDya a).toReal = matSum (fun i j => (a i j).toReal) := by
  simp only [matSumDya, matSum, Fin.sum_univ_three, Dya.toReal_add]
  ring

/-- `Dya.toReal` commutes with the entrywise absolute value `matAbsDya`, which becomes the real
entrywise absolute value `matAbs`. -/
theorem matdya_matSumDya_matAbsDya_toReal (a : Fin 3 → Fin 3 → Dya) :
    (matSumDya (matAbsDya a)).toReal = matSum (matAbs (fun i j => (a i j).toReal)) := by
  rw [matdya_matSumDya_toReal]
  congr 1
  ext i j
  simp [matAbsDya, matAbs, Dya.toReal_abs]

/-- Entrywise: `Dya.toReal` commutes with the entrywise absolute value. -/
theorem matdya_matAbsDya_toReal_apply (a : Fin 3 → Fin 3 → Dya) (i j : Fin 3) :
    (matAbsDya a i j).toReal = matAbs (fun i j => (a i j).toReal) i j := by
  simp [matAbsDya, matAbs, Dya.toReal_abs]

/-- Entrywise: `Dya.toReal` commutes with the dyadic matrix product `matMulDya`, which becomes
the real matrix product `matMul`. -/
theorem matdya_matMulDya_toReal (a b : Fin 3 → Fin 3 → Dya) (i j : Fin 3) :
    (matMulDya a b i j).toReal =
      matMul (fun i j => (a i j).toReal) (fun i j => (b i j).toReal) i j := by
  simp only [matMulDya, matMul, Dya.toReal_add, Dya.toReal_mul, Fin.sum_univ_three]
  ring

/-- Entrywise: `Dya.toReal` commutes with the dyadic identity matrix. -/
theorem matdya_matIdDya_toReal (i j : Fin 3) : (matIdDya i j).toReal = matId i j := by
  by_cases h : i = j <;> simp [matIdDya, matId, h]

/-- Entrywise: `Dya.toReal` commutes with the dyadic matrix difference. -/
theorem matdya_matSubDya_toReal_apply (a b : Fin 3 → Fin 3 → Dya) (i j : Fin 3) :
    (matSubDya a b i j).toReal =
      matSub (fun i j => (a i j).toReal) (fun i j => (b i j).toReal) i j := by
  simp [matSubDya, matSub, Dya.toReal_sub]

/-! ## Nonnegativity -/

/-- A sum of absolute values of matrix entries is nonnegative. -/
theorem matdya_matSum_matAbs_nonneg (b : Fin 3 → Fin 3 → ℝ) : 0 ≤ matSum (matAbs b) := by
  simp only [matSum, matAbs]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- `Dya.maxAbs` is nonnegative, as a real number. -/
theorem matdya_maxAbs_toReal_nonneg (a b : Dya) : 0 ≤ (Dya.maxAbs a b).toReal := by
  rw [Dya.maxAbs, Dya.toReal_max, Dya.toReal_abs, Dya.toReal_abs]
  exact le_max_of_le_left (abs_nonneg _)

/-- The dyadic maximum of two nonnegative dyadics is nonnegative, as a real number. -/
theorem matdya_max_toReal_nonneg {a b : Dya} (ha : 0 ≤ a.toReal) (_hb : 0 ≤ b.toReal) :
    0 ≤ (Dya.max a b).toReal := by
  rw [Dya.toReal_max]
  exact le_max_of_le_left ha

/-! ## The three identities -/

/-- `ε = Σ_{ij} Δ_{ij}`, over the reals. -/
theorem matdya_eps_toReal (D : Work.SeedCert.KrawData) :
    (D.eps).toReal = matSum (matAbs D.Δr) := by
  rw [Work.SeedCert.KrawData.eps, matdya_matSumDya_matAbsDya_toReal]
  rfl

/-- `β = Σ_{ij} |M_{ij}|`, over the reals. -/
theorem matdya_beta_toReal (D : Work.SeedCert.KrawData) :
    (D.beta).toReal = matSum (matAbs D.Mbr) := by
  rw [Work.SeedCert.KrawData.beta, matdya_matSumDya_matAbsDya_toReal]
  rfl

/-- Entrywise form of the identity for `α`: `(M A - 1)_{ij}` is the `toReal` of the
corresponding dyadic entry. -/
theorem matdya_alpha_apply (D : Work.SeedCert.KrawData) (i j : Fin 3) :
    (matSubDya (matMulDya D.Mb D.Ac) matIdDya i j).toReal =
      matSub (matMul D.Mbr D.Acr) matId i j := by
  simp only [matSubDya, matSub, Dya.toReal_sub, matdya_matMulDya_toReal,
    matdya_matIdDya_toReal, Work.SeedCert.KrawData.Mbr, Work.SeedCert.KrawData.Acr, matMul]

/-- `α = Σ_{ij} |(M A - 1)_{ij}|`, over the reals. -/
theorem matdya_alpha_toReal (D : Work.SeedCert.KrawData) :
    (D.alpha).toReal = matSum (matAbs (matSub (matMul D.Mbr D.Acr) matId)) := by
  rw [Work.SeedCert.KrawData.alpha, matdya_matSumDya_matAbsDya_toReal]
  congr 1
  ext i j
  simp only [matAbs]
  rw [matdya_alpha_apply D i j]

/-! ## The nonnegativity of the five dyadic quantities -/

theorem matdya_eps_nonneg (D : Work.SeedCert.KrawData) : 0 ≤ (D.eps).toReal := by
  rw [matdya_eps_toReal D]
  exact matdya_matSum_matAbs_nonneg _

theorem matdya_beta_nonneg (D : Work.SeedCert.KrawData) : 0 ≤ (D.beta).toReal := by
  rw [matdya_beta_toReal D]
  exact matdya_matSum_matAbs_nonneg _

theorem matdya_alpha_nonneg (D : Work.SeedCert.KrawData) : 0 ≤ (D.alpha).toReal := by
  rw [matdya_alpha_toReal D]
  exact matdya_matSum_matAbs_nonneg _

theorem matdya_residBound_nonneg (D : Work.SeedCert.KrawData) :
    0 ≤ (D.residBound).toReal := by
  simp only [Work.SeedCert.KrawData.residBound]
  exact matdya_max_toReal_nonneg
    (matdya_max_toReal_nonneg (matdya_maxAbs_toReal_nonneg _ _) (matdya_maxAbs_toReal_nonneg _ _))
    (matdya_maxAbs_toReal_nonneg _ _)

theorem matdya_etaBound_nonneg (D : Work.SeedCert.KrawData) : 0 ≤ (D.etaBound).toReal := by
  rw [Work.SeedCert.KrawData.etaBound, Dya.toReal_mul]
  exact mul_nonneg (matdya_beta_nonneg D) (matdya_residBound_nonneg D)

/-! ## The requested statement -/

theorem matdya_toReal (D : Work.SeedCert.KrawData) :
    (Work.SeedCert.KrawData.eps D).toReal = Work.SeedCert.matSum (Work.SeedCert.matAbs (Work.SeedCert.KrawData.Δr D)) ∧
    (Work.SeedCert.KrawData.beta D).toReal = Work.SeedCert.matSum (Work.SeedCert.matAbs (Work.SeedCert.KrawData.Mbr D)) ∧
    (Work.SeedCert.KrawData.alpha D).toReal =
      Work.SeedCert.matSum (Work.SeedCert.matAbs (Work.SeedCert.matSub (Work.SeedCert.matMul (Work.SeedCert.KrawData.Mbr D) (Work.SeedCert.KrawData.Acr D)) Work.SeedCert.matId)) ∧
    0 ≤ (Work.SeedCert.KrawData.eps D).toReal ∧
    0 ≤ (Work.SeedCert.KrawData.beta D).toReal ∧
    0 ≤ (Work.SeedCert.KrawData.alpha D).toReal ∧
    0 ≤ (Work.SeedCert.KrawData.residBound D).toReal ∧
    0 ≤ (Work.SeedCert.KrawData.etaBound D).toReal :=
  ⟨matdya_eps_toReal D, matdya_beta_toReal D, matdya_alpha_toReal D, matdya_eps_nonneg D,
    matdya_beta_nonneg D, matdya_alpha_nonneg D, matdya_residBound_nonneg D,
    matdya_etaBound_nonneg D⟩

end Work.SeedCertNum

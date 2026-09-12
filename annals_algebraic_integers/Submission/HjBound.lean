import Mathlib
import Submission.AdjustLemma
import Submission.RemezComplex
import Submission.Cwnorm
import Submission.WnormToolkit
import Submission.Contracts
import Submission.RootData

/-!
# Weighted-norm bound for `G · H_j` (Smith `lem:second_squeeze`, GON.tex, eq:HjGk)

Context: `A, G ∈ ℤ[X]` with `natDegree A = m`, `G ≠ 0`, `natDegree (A·G) ≤ n`
(`n ≥ m ≥ 2`); `α : Fin m → ℂ` the distinct roots of `A` with the factorization
`Ac = C(lc)·∏ᵢ (X − C(α i))`.  For one `j : Fin m`, `R : ℤ[X]`,
`β : Fin m → ℂ` give the integer polynomial `H := X^j − 2·R` whose
complexification is `Hc = 2·(∑ᵢ βᵢ · qDiv A (αᵢ))` with `∑ᵢ ‖βᵢ‖ ≤ m^{Cadj}`
(these come from the adjust theorem applied to `A` with `P = ½·X^j`).

We prove `wnorm n (zmap (H·G)) ≤ 2·m^{Cadj}·(2n)^{Crem}·bnd` assuming
`wnorm n (zmap (A·G)) ≤ bnd` (`bnd ≥ 0`) and Remez with constant `Crem ≥ 0`.

## Proof route (any correct route accepted)
1. Real↔complex norms: `cwnorm n ((A·G).map ℤ→ℂ) = wnorm n (zmap (A·G))` and
   similarly for `H·G` — via `Submission.Cwnorm.cwnorm_map_eq_wnorm`:
   `(zmap P).map ℝ→ℂ = P.map ℤ→ℂ` for integer `P`.
2. Rewrite the complexified product using `hH`: `(H·G)c = Gc·Hc =
   2·(∑ᵢ βᵢ • (qDiv A (αᵢ)·Gc))` (module/scalar arithmetic in `ℂ[X]`,
   `smul_eq_C_mul`, `mul_comm`, `mul_assoc`, `map_mul`, `Finset.smul_sum`...).
3. Sub-additivity + scalar rule of `cwnorm`: `cwnorm n (∑ᵢ βᵢ • Xᵢ) ≤
   ∑ᵢ ‖βᵢ‖ · cwnorm n Xᵢ` (`cwnorm_sum_le`, `cwnorm_smul`).
4. For each `i`, apply `hrem` (Remez) at `N := n`, `m := (A·G).natDegree`,
   `P := (A·G).map ℤ→ℂ`, root `α i` (show `P.eval (α i) = 0` from `hfac`:
   `A(α i) = 0`).  This gives `Q'` with `P = (X − C(α i))·Q'` and
   `cwnorm n Q' ≤ (2·max n (natDegree(A·G)))^{Crem} · cwnorm n P`.
   Show `Q' = qDiv A (α i) · Gc`: both factor `P` by `X − C(α i)` (the other
   factorization via `Submission.AdjustLemma.qDiv_mul A α hfac i` and
   `Polynomial.map_mul`), cancel the nonzero factor `X − C(α i)` in `ℂ[X]`
   (`mul_left_cancel₀`).  Conclude
   `cwnorm n (qDiv A (α i)·Gc) ≤ (2·max n (natDegree(A·G)))^{Crem} · cwnorm n P`.
5. Absorb: `cwnorm n P = wnorm n (zmap (A·G)) ≤ bnd`, and
   `(2·max n (natDegree(A·G))) ≤ 2n` (`hdegAG`), so with `Crem ≥ 0`,
   `(2·max n d)^{Crem} ≤ (2n)^{Crem}` (`Real.rpow_le_rpow` / `pow_le_pow_left₀`).
6. Assemble with `hβ`.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace Submission.HjBound

open Submission.Contracts
open Submission.Cwnorm
open Submission.AdjustLemma

/-- Weighted-norm bound for `G·H_j` (per-`j` Remez/adjust datum). -/
theorem hj_wn_bound {n m k : ℕ} (hmn : m ≤ n) (hn2 : 2 ≤ n)
    (Cadj Crem : ℝ) (hCadj0 : 0 ≤ Cadj) (hCrem0 : 0 ≤ Crem)
    (hrem : ∀ (N m : ℕ), 1 ≤ m → ∀ (P : Polynomial ℂ), P.natDegree = m → ∀ (α : ℂ),
      P.eval α = 0 → ∃ (Q : Polynomial ℂ), P = (Polynomial.X - Polynomial.C α) * Q ∧
        cwnorm N Q ≤ ((2 * max N m : ℕ) : ℝ) ^ Crem * cwnorm N P)
    (A G : Polynomial ℤ) (hA0 : A ≠ 0) (hdegA : A.natDegree = m)
    (hG0 : G ≠ 0) (hdegAG : (A * G).natDegree ≤ n) (hdegAG1 : 1 ≤ (A * G).natDegree)
    (α : Fin m → ℂ)
    (hfac : A.map (algebraMap ℤ ℂ) = Polynomial.C (A.leadingCoeff : ℂ) *
      ∏ i : Fin m, (Polynomial.X - Polynomial.C (α i)))
    (bnd : ℝ) (hbnd : 0 ≤ bnd)
    (hAwn : wnorm n (zmap (A * G)) ≤ bnd)
    {j : Fin m} (R : Polynomial ℤ) (β : Fin m → ℂ)
    (hβ : ∑ i : Fin m, ‖β i‖ ≤ (m : ℝ) ^ Cadj)
    (hH : (Polynomial.X ^ (j : ℕ) - (2 : ℤ) • R).map (algebraMap ℤ ℂ) =
      (2 : ℂ) • (∑ i : Fin m, β i • qDiv A (α i))) :
    wnorm n (zmap ((Polynomial.X ^ (j : ℕ) - (2 : ℤ) • R) * G)) ≤
      2 * (m : ℝ) ^ Cadj * (((2 * n : ℕ) : ℝ) ^ Crem) * bnd := by
  classical
  set H : Polynomial ℤ := Polynomial.X ^ (j : ℕ) - (2 : ℤ) • R with hHdef
  set Gc : Polynomial ℂ := G.map (algebraMap ℤ ℂ) with hGcdef
  set Pc : Polynomial ℂ := (A * G).map (algebraMap ℤ ℂ) with hPcdef
  set d : ℕ := (A * G).natDegree with hddef
  set M : ℝ := (m : ℝ) ^ Cadj with hMdef
  set D : ℝ := ((2 * n : ℕ) : ℝ) ^ Crem with hDdef
  let T : Polynomial ℂ := ∑ i : Fin m, β i • (qDiv A (α i) * Gc)
  have hmax : max n d = n := by
    apply le_antisymm
    · exact max_le le_rfl hdegAG
    · exact le_max_left n d
  -- the map of H (complexification) is the scalar sum from hH
  have hHc : H.map (algebraMap ℤ ℂ) =
      (2 : ℂ) • (∑ i : Fin m, β i • qDiv A (α i)) := by
    rw [hHdef]
    exact hH
  -- (H*G) complexifies to Hc * Gc
  have hmapmul : (H * G).map (algebraMap ℤ ℂ) = H.map (algebraMap ℤ ℂ) * Gc := by
    rw [hGcdef]
    rw [Polynomial.map_mul]
  -- distribute Gc into the scalar sum
  have hSmul : (∑ i : Fin m, β i • qDiv A (α i)) * Gc =
      ∑ i : Fin m, β i • (qDiv A (α i) * Gc) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul]
    ring
  have hpoly2 : ((2 : ℂ) • (∑ i : Fin m, β i • qDiv A (α i))) * Gc =
      (2 : ℂ) • (∑ i : Fin m, β i • (qDiv A (α i) * Gc)) := by
    calc
      ((2 : ℂ) • (∑ i : Fin m, β i • qDiv A (α i))) * Gc
          = (Polynomial.C (2 : ℂ) * (∑ i : Fin m, β i • qDiv A (α i))) * Gc := by
              rw [Polynomial.smul_eq_C_mul]
      _ = Polynomial.C (2 : ℂ) * ((∑ i : Fin m, β i • qDiv A (α i)) * Gc) := by
              rw [mul_assoc]
      _ = Polynomial.C (2 : ℂ) * (∑ i : Fin m, β i • (qDiv A (α i) * Gc)) := by
              rw [hSmul]
      _ = (2 : ℂ) • (∑ i : Fin m, β i • (qDiv A (α i) * Gc)) := by
              rw [Polynomial.smul_eq_C_mul]
  -- complex weighted norm of the LHS equals that of the RHS scalar sum
  have hcwn : cwnorm n ((H * G).map (algebraMap ℤ ℂ)) = cwnorm n ((2 : ℂ) • T) := by
    calc
      cwnorm n ((H * G).map (algebraMap ℤ ℂ))
          = cwnorm n (H.map (algebraMap ℤ ℂ) * Gc) := by rw [hmapmul]
      _ = cwnorm n (((2 : ℂ) • (∑ i : Fin m, β i • qDiv A (α i))) * Gc) := by rw [hHc]
      _ = cwnorm n ((2 : ℂ) • (∑ i : Fin m, β i • (qDiv A (α i) * Gc))) := by rw [hpoly2]
  -- roots and degree for the Remez hypothesis
  have hAc_eval : ∀ i : Fin m, (A.map (algebraMap ℤ ℂ)).eval (α i) = 0 :=
    fun i => alpha_root A α hfac i
  have hdegPc : Pc.natDegree = d := by
    rw [hPcdef, hddef]
    rw [Polynomial.natDegree_map_eq_of_injective (f := algebraMap ℤ ℂ) Int.cast_injective]
  have hrootPc : ∀ i : Fin m, Pc.eval (α i) = 0 := by
    intro i
    rw [hPcdef, Polynomial.map_mul, Polynomial.eval_mul, hAc_eval i]
    simp
  -- per-index Remez bound
  have hqi : ∀ i : Fin m, cwnorm n (qDiv A (α i) * Gc) ≤ D * cwnorm n Pc := by
    intro i
    rcases hrem n d hdegAG1 Pc hdegPc (α i) (hrootPc i) with ⟨Q', hfacQ', hbound⟩
    have hAc_fac : A.map (algebraMap ℤ ℂ) =
        (X - Polynomial.C (α i)) * qDiv A (α i) := qDiv_mul A α hfac i
    have hPc_fac : Pc = (X - Polynomial.C (α i)) * (qDiv A (α i) * Gc) := by
      calc
        Pc = (A.map (algebraMap ℤ ℂ)) * (G.map (algebraMap ℤ ℂ)) := by
            rw [hPcdef]
            rw [Polynomial.map_mul]
        _ = (A.map (algebraMap ℤ ℂ)) * Gc := by rw [hGcdef]
        _ = ((X - Polynomial.C (α i)) * qDiv A (α i)) * Gc := by rw [hAc_fac]
        _ = (X - Polynomial.C (α i)) * (qDiv A (α i) * Gc) := by rw [mul_assoc]
    have hQ' : qDiv A (α i) * Gc = Q' := by
      have hmonic : (X - Polynomial.C (α i)).Monic := Polynomial.monic_X_sub_C (α i)
      calc
        qDiv A (α i) * Gc
            = ((X - Polynomial.C (α i)) * (qDiv A (α i) * Gc)) /ₘ (X - Polynomial.C (α i)) := by
                rw [Polynomial.mul_divByMonic_cancel_left (qDiv A (α i) * Gc) hmonic]
        _ = Pc /ₘ (X - Polynomial.C (α i)) := by rw [hPc_fac]
        _ = ((X - Polynomial.C (α i)) * Q') /ₘ (X - Polynomial.C (α i)) := by rw [← hfacQ']
        _ = Q' := by rw [Polynomial.mul_divByMonic_cancel_left Q' hmonic]
    have hDd : ((2 * max n d : ℕ) : ℝ) ^ Crem = D := by
      rw [hmax, hDdef]
    have hQ'le : cwnorm n (qDiv A (α i) * Gc) ≤
        ((2 * max n d : ℕ) : ℝ) ^ Crem * cwnorm n Pc := by
      simpa [hQ'] using hbound
    rw [hDd] at hQ'le
    exact hQ'le
  -- real↔complex conversion of the A*G norm
  have hPcwn : cwnorm n Pc ≤ bnd := by
    calc
      cwnorm n Pc = cwnorm n ((A * G).map (algebraMap ℤ ℂ)) := by rw [hPcdef]
      _ = cwnorm n ((zmap (A * G)).map (algebraMap ℝ ℂ)) := by
            rw [← zmap_map_eq (A * G)]
      _ = wnorm n (zmap (A * G)) := by
            rw [cwnorm_map_eq_wnorm n (zmap (A * G))]
      _ ≤ bnd := hAwn
  have hD0 : 0 ≤ D := by
    rw [hDdef]
    exact Real.rpow_nonneg (by positivity : 0 ≤ ((2 * n : ℕ) : ℝ)) Crem
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact Real.rpow_nonneg (by positivity : 0 ≤ (m : ℝ)) Cadj
  have hnorm2c : ‖(2 : ℂ)‖ = 2 := by norm_num
  -- triangle / scalar bounds
  have hTsum : cwnorm n T ≤ ∑ i : Fin m, ‖β i‖ * (D * cwnorm n Pc) := by
    calc
      cwnorm n T = cwnorm n (∑ i : Fin m, β i • (qDiv A (α i) * Gc)) := rfl
      _ ≤ ∑ i : Fin m, cwnorm n (β i • (qDiv A (α i) * Gc)) := by
            have h1 := cwnorm_sum_le n (Finset.univ : Finset (Fin m))
              (fun i : Fin m => β i • (qDiv A (α i) * Gc))
            calc
              cwnorm n (∑ i : Fin m, β i • (qDiv A (α i) * Gc))
                  = cwnorm n (∑ i ∈ (Finset.univ : Finset (Fin m)),
                      β i • (qDiv A (α i) * Gc)) := rfl
              _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin m)),
                      cwnorm n (β i • (qDiv A (α i) * Gc)) := h1
              _ = ∑ i : Fin m, cwnorm n (β i • (qDiv A (α i) * Gc)) := rfl
      _ ≤ ∑ i : Fin m, ‖β i‖ * (D * cwnorm n Pc) := by
            apply Finset.sum_le_sum
            intro i hi
            calc
              cwnorm n (β i • (qDiv A (α i) * Gc)) = ‖β i‖ * cwnorm n (qDiv A (α i) * Gc) := by
                    rw [cwnorm_smul n (β i) (qDiv A (α i) * Gc)]
              _ ≤ ‖β i‖ * (D * cwnorm n Pc) := by
                    exact mul_le_mul_of_nonneg_left (hqi i) (norm_nonneg (β i))
  have hTle : cwnorm n T ≤ (∑ i : Fin m, ‖β i‖) * (D * cwnorm n Pc) := by
    calc
      cwnorm n T ≤ ∑ i : Fin m, ‖β i‖ * (D * cwnorm n Pc) := hTsum
      _ = (∑ i : Fin m, ‖β i‖) * (D * cwnorm n Pc) := by rw [Finset.sum_mul]
  have hmain2 : cwnorm n ((2 : ℂ) • T) ≤ 2 * M * D * bnd := by
    calc
      cwnorm n ((2 : ℂ) • T) = ‖(2 : ℂ)‖ * cwnorm n T := by
            rw [cwnorm_smul n (2 : ℂ) T]
      _ = 2 * cwnorm n T := by rw [hnorm2c]
      _ ≤ 2 * ((∑ i : Fin m, ‖β i‖) * (D * cwnorm n Pc)) := by
            exact mul_le_mul_of_nonneg_left hTle (by norm_num : 0 ≤ (2 : ℝ))
      _ ≤ 2 * (M * (D * cwnorm n Pc)) := by
            have hDc : 0 ≤ D * cwnorm n Pc := mul_nonneg hD0 (cwnorm_nonneg n Pc)
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hβ hDc) (by norm_num : 0 ≤ (2 : ℝ))
      _ ≤ 2 * (M * (D * bnd)) := by
            have hDbc : D * cwnorm n Pc ≤ D * bnd := mul_le_mul_of_nonneg_left hPcwn hD0
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hDbc hM0) (by norm_num : 0 ≤ (2 : ℝ))
      _ = 2 * M * D * bnd := by ring
  have hwn : wnorm n (zmap (H * G)) = cwnorm n ((H * G).map (algebraMap ℤ ℂ)) := by
    rw [← cwnorm_map_eq_wnorm n (zmap (H * G))]
    rw [zmap_map_eq (H * G)]
  calc
    wnorm n (zmap (H * G)) = cwnorm n ((H * G).map (algebraMap ℤ ℂ)) := hwn
    _ = cwnorm n ((2 : ℂ) • T) := hcwn
    _ ≤ 2 * M * D * bnd := hmain2

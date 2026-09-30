import Mathlib
import Submission.Work.BW.Est17Ext
import Submission.Work.BW.Qdesc_val_mem
import Submission.Work.BW.est14_defs
import Submission.Work.BW.est15defs
import Submission.Work.BW.phi_gKJ_eq_acg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Complex

/-! ### The Kummer extension `L = ℚ(φ(K), ρ₁,…,ρ_r)`

`L = EL φ ρ` (`Submission.Work.BW.Est17Ext`) is the subfield of `ℂ` generated over `ℚ` by the
images `φ (kbasis K i)` of a `ℚ`-basis of `K` and by the `ρ_j`.  Here we collect the closure
facts used below, and the two half-integer facts: the value `Θ(2^{-J}(s/2) + m)` of the rational
polynomial `hasseDeriv t0 (deltaPoly h ^ l)` is a rational (so lies in `L`), and
`exp ((s/2) ℓ_j) = ρ_j ^ s` for `ρ_j = exp (ℓ_j / 2)`. -/

section ELmem

variable {K : Type*} [Field K] [NumberField K] {r : ℕ} {φ : K →+* ℂ} {ρ : Fin r → ℂ}

/-- The image of `K` under `φ` lies in `L`. -/
theorem e17_mem_phi (x : K) : φ x ∈ (EL φ ρ : Set ℂ) := by
  simpa using (inclE φ ρ x).2

/-- The generators `ρ_j` lie in `L`. -/
theorem e17_mem_rho (j : Fin r) : ρ j ∈ (EL φ ρ : Set ℂ) := by
  simpa using (rhoE φ ρ j).2

/-- `L` contains `ℚ`. -/
theorem e17_mem_rat (q : ℚ) : (q : ℂ) ∈ (EL φ ρ : Set ℂ) :=
  SubfieldClass.ratCast_mem (EL φ ρ) q

/-- `L` is closed under natural powers. -/
theorem e17_mem_pow {x : ℂ} (hx : x ∈ (EL φ ρ : Set ℂ)) (m : ℕ) : x ^ m ∈ (EL φ ρ : Set ℂ) := by
  simpa [zpow_natCast] using IntermediateField.pow_mem (EL φ ρ) hx (m : ℤ)

/-- `L` is closed under integer powers. -/
theorem e17_mem_zpow {x : ℂ} (hx : x ∈ (EL φ ρ : Set ℂ)) (m : ℤ) : x ^ m ∈ (EL φ ρ : Set ℂ) :=
  IntermediateField.pow_mem (EL φ ρ) hx m

/-- `L` contains the values of rational polynomials at rational points. -/
theorem e17_mem_aeval_rat (q : ℚ) (P : Polynomial ℚ) :
    Polynomial.aeval (q : ℂ) P ∈ (EL φ ρ : Set ℂ) := by
  rw [qvm_aeval_ratCast]
  exact e17_mem_rat _

/-- The half-integer `Θ`-value `Θ(2^{-J}(s/2) + m; h, l, t₀)` lies in `L`: it is the image of
the rational `Polynomial.aeval (2^{-J}(s/2) + m) (hasseDeriv t0 (deltaPoly h ^ l))`. -/
theorem e17_mem_aeval_half (J t0 h l : ℕ) (s : ℤ) (m : ℕ) :
    Polynomial.aeval (((2 : ℂ) ^ J)⁻¹ * ((s : ℂ) / 2) + ((m : ℕ) : ℂ))
      (Polynomial.hasseDeriv t0 (deltaPoly h ^ l)) ∈ (EL φ ρ : Set ℂ) := by
  have harg : ((((2 : ℚ) ^ J)⁻¹ * ((s : ℚ) / 2) + ((m : ℕ) : ℚ) : ℚ) : ℂ)
      = ((2 : ℂ) ^ J)⁻¹ * ((s : ℂ) / 2) + ((m : ℕ) : ℂ) := by
    push_cast
    rw [div_eq_mul_inv]
  rw [← harg]
  exact e17_mem_aeval_rat _ _

end ELmem

/-- With `ρ_j = exp (ℓ_j / 2)`, one has `exp ((s/2) ℓ_j) = ρ_j ^ s`. -/
theorem e17_rhoC_zpow {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ) (α : Fin n → K) (v : ℕ)
    (Lm : Fin r → Fin n → ℤ) (j : Fin r) (s : ℤ) :
    Complex.exp (((s : ℂ) / 2) * lamP φ α v Lm j) = (rhoC φ α v Lm j) ^ s := by
  rw [rhoC, ← Complex.exp_int_mul (lamP φ α v Lm j / 2) s]
  congr 1
  ring

/-- The powers of the square roots `ρ_j = exp (ℓ_j / 2)`: `(exp ((s/2) ℓ_j))^n = ρ_j ^ (s n)`. -/
theorem e17_exp_half_pow {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ) (α : Fin n → K) (v : ℕ)
    (Lm : Fin r → Fin n → ℤ) (j : Fin r) (s : ℤ) (n0 : ℕ) :
    (Complex.exp (((s : ℂ) / 2) * lamP φ α v Lm j)) ^ n0
      = (rhoC φ α v Lm j) ^ (s * (n0 : ℤ)) := by
  rw [← Complex.exp_nat_mul (((s : ℂ) / 2) * lamP φ α v Lm j) n0]
  rw [rhoC, ← Complex.exp_int_mul (lamP φ α v Lm j / 2) (s * (n0 : ℤ))]
  congr 1
  push_cast
  ring

/-- The half-integer value `g(s/2) = acg … (s/2)` of the descended auxiliary function lies in
the Kummer extension `L = ℚ(φ(K), ρ₁,…,ρ_r)`, where `ρ_j = exp (lamP_j / 2)` is a square root
of `φ(α'_j)` (so that `exp ((s/2) lamP_j) = ρ_j ^ s`). -/
theorem est17_acg_mem {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {Lm : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σl : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σl) (pDj r (dK K) σl) → K}
    (H : ACHyp φ α b k c v Lm α' σl ι p) (J : ℕ) (μ : Fin r → ℕ) (t0 : ℕ)
    (t : Fin (r - 1) → ℕ) (s : ℤ) :
    acg φ α b k Lm ι v σl p J μ t0 t ((s : ℂ) / 2) ∈ (EL φ (rhoC φ α v Lm) : Set ℂ) := by
  rw [acg_eq_sum (z := (s : ℂ) / 2)]
  refine IntermediateField.sum_mem (EL φ (rhoC φ α v Lm)) (fun lm _ => ?_)
  by_cases hc : estCond J μ lm
  · rw [if_pos hc, estGT, estCoeff, estTorus]
    have hK : φ (p lm) ∈ (EL φ (rhoC φ α v Lm) : Set ℂ) :=
      e17_mem_phi (φ := φ) (ρ := rhoC φ α v Lm) (p lm)
    have hPi : (∏ m, Delta (gam b k Lm (ι m) (fun i => (lm.2.2 i : ℕ))) (t m))
        ∈ (EL φ (rhoC φ α v Lm) : Set ℂ) := by
      rw [← pgk_phi_piRat φ b k Lm ι (acH K b v) (pD0 r (dK K) σl) (pDj r (dK K) σl) t lm]
      exact e17_mem_phi (φ := φ) (ρ := rhoC φ α v Lm) _
    have hU : (ulcm (acH K b v) : ℂ) ^ t0 ∈ (EL φ (rhoC φ α v Lm) : Set ℂ) := by
      rw [← pgk_phi_ulcm φ (acH K b v)]
      exact e17_mem_pow (φ := φ) (ρ := rhoC φ α v Lm)
        (e17_mem_phi (φ := φ) (ρ := rhoC φ α v Lm) _) t0
    have hTh : Polynomial.aeval (((2 : ℂ) ^ J)⁻¹ * ((s : ℂ) / 2) + ((lm.1 : ℕ) : ℂ))
        (Polynomial.hasseDeriv t0 (deltaPoly (acH K b v) ^ ((lm.2.1 : ℕ) + 1)))
        ∈ (EL φ (rhoC φ α v Lm) : Set ℂ) :=
      e17_mem_aeval_half (φ := φ) (ρ := rhoC φ α v Lm)
        J t0 (acH K b v) ((lm.2.1 : ℕ) + 1) s (lm.1 : ℕ)
    have hExp : (∏ j : Fin r,
        (Complex.exp (((s : ℂ) / 2) * lamP φ α v Lm j)) ^ ((lm.2.2 j : ℕ) / 2 ^ J))
        ∈ (EL φ (rhoC φ α v Lm) : Set ℂ) := by
      refine IntermediateField.prod_mem _ (fun j _ => ?_)
      rw [e17_exp_half_pow φ α v Lm j s ((lm.2.2 j : ℕ) / 2 ^ J)]
      exact e17_mem_zpow (φ := φ) (ρ := rhoC φ α v Lm)
        (e17_mem_rho (φ := φ) (ρ := rhoC φ α v Lm) j) _
    exact IntermediateField.mul_mem _ (IntermediateField.mul_mem _
      (IntermediateField.mul_mem _ (IntermediateField.mul_mem _ hK hPi) hU) hTh) hExp
  · rw [if_neg hc]
    exact IntermediateField.zero_mem _

end Work.BW

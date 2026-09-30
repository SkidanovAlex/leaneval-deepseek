import Mathlib
import Submission.Work.BW.Est17Ext
import Submission.Work.BW.est14_defs
import Submission.Work.BW.est15defs
import Submission.Work.BW.est17_acg_mem
import Submission.Work.BW.phi_gKJ_eq_acg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-! ### Coercion lemmas for the Kummer field `L = EL φ ρ`

All of these are the functoriality of the coercion `L ↪ ℂ` (`IntermediateField.val`), stated
with `IntermediateField.val` explicitly so that they do not clash with the analogous lemmas for
`algebraMap`. -/

lemma EL_coe_sum {K : Type*} [Field K] [NumberField K] {r : ℕ} {φ : K →+* ℂ} {ρ : Fin r → ℂ}
    {ι' : Type*} [Fintype ι'] (F : ι' → EL φ ρ) :
    ((∑ i, F i : EL φ ρ) : ℂ) = ∑ i, ((F i : EL φ ρ) : ℂ) :=
  map_sum (IntermediateField.val (EL φ ρ)) F Finset.univ

lemma EL_coe_mul {K : Type*} [Field K] [NumberField K] {r : ℕ} {φ : K →+* ℂ} {ρ : Fin r → ℂ}
    (a b : EL φ ρ) : ((a * b : EL φ ρ) : ℂ) = (a : ℂ) * (b : ℂ) :=
  map_mul (IntermediateField.val (EL φ ρ)) a b

lemma EL_coe_prod {K : Type*} [Field K] [NumberField K] {r : ℕ} {φ : K →+* ℂ} {ρ : Fin r → ℂ}
    {ι' : Type*} [Fintype ι'] (F : ι' → EL φ ρ) :
    ((∏ i, F i : EL φ ρ) : ℂ) = ∏ i, ((F i : EL φ ρ) : ℂ) :=
  map_prod (IntermediateField.val (EL φ ρ)) F Finset.univ

lemma EL_coe_zpow {K : Type*} [Field K] [NumberField K] {r : ℕ} {φ : K →+* ℂ} {ρ : Fin r → ℂ}
    (x : EL φ ρ) (n : ℤ) : ((x ^ n : EL φ ρ) : ℂ) = (x : ℂ) ^ n :=
  map_zpow₀ (IntermediateField.val (EL φ ρ)) x n

lemma EL_coe_rat {K : Type*} [Field K] [NumberField K] {r : ℕ} {φ : K →+* ℂ} {ρ : Fin r → ℂ}
    (q : ℚ) : ((algebraMap ℚ (EL φ ρ) q : EL φ ρ) : ℂ) = algebraMap ℚ ℂ q :=
  Subalgebra.coe_algebraMap (EL φ ρ).toSubalgebra q

/-- Integer division of a natural number by `2 ^ J` is the cast of the natural quotient
(used to identify the exponent `s⌊λ_j/2^J⌋` in its integer-division form). -/
lemma int_ediv_pow (n J : ℕ) : ((n : ℤ) / (2 : ℤ) ^ J) = ((n / 2 ^ J : ℕ) : ℤ) := by
  rw [Int.natCast_div, Nat.cast_pow]
  norm_num

/-- The rational factor `∏_m Δ(γ_m(λ);t_m)·u(h)^{t₀}·Θ(2^{-J}(s/2)+λ₋₁; …)` of the expansion,
viewed in `ℂ`: `algebraMap ℚ ℂ` of it is the product of the corresponding `Δ`-values, `u(h)^{t₀}`
and the `Θ`-value at the complex point `2^{-J}(s/2) + λ₋₁`. -/
lemma est17_rat_map {K : Type*} [Field K] [NumberField K] {n r : ℕ}
    {v : ℕ} {b : Fin n → ℤ} {k : Fin n} {Lm : Fin r → Fin n → ℤ}
    {ι : Fin (r - 1) → Fin n} {σl : Fin r → ℝ}
    (J : ℕ) (t0 : ℕ) (t : Fin (r - 1) → ℕ) (s : ℤ)
    (lm : AuxIdx r (acH K b v) (pD0 r (dK K) σl) (pDj r (dK K) σl)) :
    (algebraMap ℚ ℂ
        ((∏ m, Polynomial.aeval (((∑ i, derVec b k Lm (ι m) i * (lm.2.2 i : ℤ)) : ℤ) : ℚ)
              (deltaPoly (t m)))
          * (ulcm (acH K b v) : ℚ) ^ t0
          * Polynomial.aeval ((s : ℚ) / 2 / 2 ^ J + (lm.1 : ℕ))
              (Polynomial.hasseDeriv t0 (deltaPoly (acH K b v) ^ ((lm.2.1 : ℕ) + 1)))))
      = (∏ m, Delta (gam b k Lm (ι m) (fun i => (lm.2.2 i : ℕ))) (t m))
          * (ulcm (acH K b v) : ℂ) ^ t0
          * Polynomial.aeval (((2 : ℂ) ^ J)⁻¹ * ((s : ℂ) / 2) + ((lm.1 : ℕ) : ℂ))
              (Polynomial.hasseDeriv t0 (deltaPoly (acH K b v) ^ ((lm.2.1 : ℕ) + 1))) := by
  rw [map_mul, map_mul, map_pow, map_prod]
  have hB : algebraMap ℚ ℂ (ulcm (acH K b v) : ℚ) = (ulcm (acH K b v) : ℂ) := by
    rw [map_natCast]
  have hA : (∏ m, algebraMap ℚ ℂ
        (Polynomial.aeval (((∑ i, derVec b k Lm (ι m) i * (lm.2.2 i : ℤ)) : ℤ) : ℚ)
          (deltaPoly (t m))))
      = (∏ m, Delta (gam b k Lm (ι m) (fun i => (lm.2.2 i : ℕ))) (t m)) := by
    refine Finset.prod_congr rfl (fun m _ => ?_)
    have h1 : algebraMap ℚ ℂ (((∑ i, derVec b k Lm (ι m) i * (lm.2.2 i : ℤ)) : ℤ) : ℚ)
        = gam b k Lm (ι m) (fun i => (lm.2.2 i : ℕ)) := by
      rw [map_intCast]
      exact gamInt_cast b k Lm (ι m) _
    rw [← Polynomial.aeval_algebraMap_apply ℂ, Delta, h1]
  have hC : algebraMap ℚ ℂ
        (Polynomial.aeval ((s : ℚ) / 2 / 2 ^ J + (lm.1 : ℕ))
          (Polynomial.hasseDeriv t0 (deltaPoly (acH K b v) ^ ((lm.2.1 : ℕ) + 1))))
      = Polynomial.aeval (((2 : ℂ) ^ J)⁻¹ * ((s : ℂ) / 2) + ((lm.1 : ℕ) : ℂ))
          (Polynomial.hasseDeriv t0 (deltaPoly (acH K b v) ^ ((lm.2.1 : ℕ) + 1))) := by
    have h2q : (s : ℚ) / 2 / 2 ^ J + (lm.1 : ℕ)
        = ((2 : ℚ) ^ J)⁻¹ * ((s : ℚ) / 2) + (lm.1 : ℕ) := by
      simp only [div_eq_mul_inv]
      ring
    have h2 : algebraMap ℚ ℂ ((s : ℚ) / 2 / 2 ^ J + (lm.1 : ℕ))
        = ((2 : ℂ) ^ J)⁻¹ * ((s : ℂ) / 2) + ((lm.1 : ℕ) : ℂ) := by
      have h := congrArg (algebraMap ℚ ℂ) h2q
      simpa only [map_add, map_mul, map_inv₀, map_pow, map_div₀, map_natCast, map_intCast,
        map_ofNat] using h
    rw [← Polynomial.aeval_algebraMap_apply ℂ, h2]
  rw [hA, hB, hC]

/-- The value `g(s/2) = acg … (s/2)`, as an element of the Kummer extension
`L = ℚ(φ(K), ρ)`, is the sum over the auxiliary index set of `φ(p lm)` times the
rational factor `∏ Δ(γ;t)·ulcm^{t₀}·Θ((s/2^{J+1})+λ₋₁; h, λ₀+1, t₀)` times
`∏_j ρ_j^{s·⌊λ_j/2^J⌋}` (the parity condition selecting the residue `μ` mod `2^J`),
i.e. the explicit expansion of `Qdesc` at `X₀ = s/2` with `exp((s/2)λ_j) = ρ_j^s`. -/
theorem est17_gexp {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {Lm : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σl : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σl) (pDj r (dK K) σl) → K}
    (H : ACHyp φ α b k c v Lm α' σl ι p) (J : ℕ) (μ : Fin r → ℕ) (t0 : ℕ)
    (t : Fin (r - 1) → ℕ) (s : ℤ)
    [inst : NumberField (EL φ (rhoC φ α v Lm))]
    (hmem : acg φ α b k Lm ι v σl p J μ t0 t ((s : ℂ) / 2) ∈ (EL φ (rhoC φ α v Lm) : Set ℂ)) :
    gamE α v Lm φ b k p J μ t0 t s hmem =
      ∑ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σl) (pDj r (dK K) σl),
        if (∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j) then
          inclE φ (rhoC φ α v Lm) (p lm)
            * algebraMap ℚ (EL φ (rhoC φ α v Lm))
                ((∏ m, Polynomial.aeval (((∑ i, derVec b k Lm (ι m) i * (lm.2.2 i : ℤ)) : ℤ) : ℚ)
                    (deltaPoly (t m)))
                  * (ulcm (acH K b v) : ℚ) ^ t0
                  * Polynomial.aeval ((s : ℚ) / 2 / 2 ^ J + (lm.1 : ℕ))
                      (Polynomial.hasseDeriv t0 (deltaPoly (acH K b v) ^ ((lm.2.1 : ℕ) + 1))))
            * ∏ j, rhoE φ (rhoC φ α v Lm) j ^ (s * ((lm.2.2 j : ℕ) / 2 ^ J))
        else 0 := by
  classical
  apply Subtype.ext
  rw [gamE_coe]
  rw [EL_coe_sum]
  rw [acg_eq_sum]
  refine Finset.sum_congr rfl (fun lm _ => ?_)
  by_cases hc : (∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j)
  · rw [if_pos hc, if_pos hc]
    rw [estGT, estCoeff, estTorus]
    rw [EL_coe_mul, EL_coe_mul, EL_coe_prod]
    rw [inclE_coe, EL_coe_rat]
    rw [Finset.prod_congr rfl (fun j _ =>
          EL_coe_zpow (rhoE φ (rhoC φ α v Lm) j) (s * ((lm.2.2 j : ℕ) / 2 ^ J)))]
    simp only [rhoE_coe]
    rw [est17_rat_map]
    have hprod : (∏ j : Fin r,
          Complex.exp (((s : ℂ) / 2) * lamP φ α v Lm j) ^ ((lm.2.2 j : ℕ) / 2 ^ J))
        = ∏ j : Fin r,
          rhoC φ α v Lm j ^ (s * (((lm.2.2 j : ℕ) : ℤ) / (2 : ℤ) ^ J)) := by
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [e17_exp_half_pow φ α v Lm j s ((lm.2.2 j : ℕ) / 2 ^ J),
          ← int_ediv_pow (lm.2.2 j) J]
    rw [hprod]
    ring
  · rw [if_neg hc, if_neg hc]
    simp

end Work.BW

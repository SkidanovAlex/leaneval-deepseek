import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseC3QAll.Prep
import Submission.Work.BoseC3QAll.errA_bounds
import Submission.Work.BoseC3QAll.eta_mul_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseC3QAll.Est1.OpZ_Bterm`

The scalar prefactor ("B-term") of the `OpZ` estimate for piece B of FS
`eq:EstimateQ3Tilde1`: the product `2²² K₀⁷ ρ_z a (K_ℓK_L)⁶ 𝓁² η²`, which multiplies
the lattice sums of `T₂,op`, is dominated by a constant times the error bracket
`e1A E`.

At FS's parameter point (`FSParamsView E`) every factor is a monomial in
`X = (μa³)^{1/323}`:

| factor | value |
|---|---|
| `(K_ℓK_L)⁶` | `X^{-72}` |
| `𝓁²` | `X^{97}` |
| `η²` | `X^{2472}` |
| `μℓ³` | `X^{-166}` |
| `K_ℓ³` | `X^{-9/2}` |

so the product is `2²²K₀⁷ ρ_z a X^{2497}`, while the first monomial of `e1A` is
`E0·(μa³)^{1/2}K_ℓ³K_L⁶η² = μ²aℓ³X^{2566} = μaX^{2400}`.  The comparison reduces
to the *single* elementary bound

`ρ_z𝓁² ≤ (3/2)μ`

(which is `ρ_z ≤ (3/2)μ`, FS `eq:Close`, times `𝓁² ≤ 1`), the identity
`μK_ℓ³ = μ²ℓ³(μa³)^{1/2}` turning the `K_ℓ⁶` of the product into the `K_ℓ³` of
`e1A`'s first monomial, and `e1A ≥ E0·(first monomial)`.

The constant is `C = 2²²·(3/2)·|K₀|⁷`; the seventh power of `K₀` is handled by
`K₀⁷ ≤ |K₀⁷|` together with the non-negativity of the Fock-system-independent
factor, so no sign hypothesis on `K₀` is needed.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseC3QAll.Est1

open Work.BoseB7 Work.BoseB7AK Work.BoseBox

theorem OpZ_Bterm (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : Work.BoseB7.FockData Mode) (T : Work.BoseC3QAll.TildeData F)
        (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E),
        b₀ ≤ E.b → Work.BoseC3QAll.Q3KernelFSAll K₀ F T E →
          4194304 * E.rho * K₀ ^ 7 * E.aScat * (E.Kl * E.KL) ^ 6 * E.lille ^ 2
              * Work.BoseC3QAll.eta E ^ 2
            ≤ C * Work.BoseC3QAll.e1A E := by
  refine ⟨4194304 * |K₀| ^ 7 * (3 / 2), by positivity, ?_⟩
  intro Mode _ _ _ F T E hv hb hK
  have hb0 : 0 < E.b := lt_of_lt_of_le hb₀ hb
  have ht0 : 0 < hv.t := hv.t_pos
  have hKl0 : 0 ≤ E.Kl := le_trans zero_le_one hv.one_le_Kl
  have hKL0 : 0 ≤ E.KL := le_trans zero_le_one hv.one_le_KL
  have hll0 : 0 ≤ E.lille := (lille_pos E hv).le
  have ha0 : 0 ≤ E.aScat := (a_pos E hv).le
  have hrho0 : 0 ≤ E.rho := (rho_pos E hv).le
  have heta0 : 0 ≤ eta E := by
    rw [errA_eta E hv]; exact (fsXp_pos ht0).le
  -- ## 1. `ρ_z𝓁² ≤ (3/2)μ`
  have hρ : E.rho * E.lille ^ 2 ≤ 3 * E.mu / 2 := by
    have h1 : E.lille ^ 2 ≤ 1 := lille_sq_le_one E hv
    have h2 : E.rho ≤ 3 * E.mu / 2 := rho_le E hv
    have h3 : 0 ≤ E.lille ^ 2 := sq_nonneg _
    have h4 : 0 ≤ 3 * E.mu / 2 := by linarith [mu_pos E hv]
    calc E.rho * E.lille ^ 2 ≤ (3 * E.mu / 2) * 1 := mul_le_mul h2 h1 h3 h4
      _ = 3 * E.mu / 2 := by ring
  -- ## 2. `μK_ℓ³ = μ²ℓ³(μa³)^{1/2}` (and the `K_ℓ⁶` form)
  have hKl3 : E.Kl ^ 3 = fsXp hv.t (-(9 / 2)) := by
    rw [errA_Kl E hv,
      show (fsXp hv.t (-(3 / 2))) ^ (3 : ℕ) = fsXp hv.t (-(3 / 2) * 3) from
        fsXp_pow ht0.le _ _]
    congr 1
    norm_num
  have hmu3 : E.mu * E.Kl ^ 3 = E.mu ^ 2 * E.ell ^ 3 * dil E (1 / 2) := by
    rw [hKl3]
    rw [show E.mu ^ 2 * E.ell ^ 3 * dil E (1 / 2)
        = E.mu * (E.mu * E.ell ^ 3) * dil E (1 / 2) by ring]
    rw [errA_mue E hv, errA_dil E hv (1 / 2), mul_assoc, fsXp_mul ht0]
    ring_nf
  have hmuKl6 : E.mu * E.Kl ^ 6 = (E.mu ^ 2 * E.ell ^ 3 * dil E (1 / 2)) * E.Kl ^ 3 := by
    calc E.mu * E.Kl ^ 6 = E.mu * E.Kl ^ 3 * E.Kl ^ 3 := by ring
      _ = (E.mu ^ 2 * E.ell ^ 3 * dil E (1 / 2)) * E.Kl ^ 3 := by rw [hmu3]
  -- ## 3. `e1A ≥ E0 · (its first monomial)`
  have he1 : E0 E * (dil E (1 / 2) * E.Kl ^ 3 * E.KL ^ 6 * eta E ^ 2) ≤ e1A E := by
    rw [e1A]
    apply mul_le_mul_of_nonneg_left _ (errA_E0_nonneg E hv)
    have ht2 : 0 ≤ dil E (1 / 2) * E.KL ^ 3 * E.lille ^ 2 :=
      mul_nonneg (mul_nonneg (dil_nonneg E hv (1 / 2)) (pow_nonneg hKL0 3)) (pow_nonneg hll0 2)
    have ht3 : 0 ≤ E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5 / E.b :=
      div_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hKl0 5) (pow_nonneg hKL0 5))
        (pow_nonneg hll0 5)) hb0.le
    have ht4 : 0 ≤ E.Kl ^ (3 / 2 : ℝ) * E.KL ^ 3 * dil E (1 / 4) * E.lille ^ 2 * eta E :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hKl0 (3 / 2))
        (pow_nonneg hKL0 3)) (dil_nonneg E hv (1 / 4))) (pow_nonneg hll0 2)) heta0
    linarith
  -- ## 4. the core comparison
  have hcore : E.rho * E.aScat * (E.Kl * E.KL) ^ 6 * E.lille ^ 2 * eta E ^ 2
      ≤ (3 / 2) * e1A E := by
    have hKl6 : (E.Kl * E.KL) ^ 6 = E.Kl ^ 6 * E.KL ^ 6 := by rw [mul_pow]
    have hR0 : 0 ≤ E.aScat * E.Kl ^ 6 * E.KL ^ 6 * eta E ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg ha0 (pow_nonneg hKl0 6)) (pow_nonneg hKL0 6))
        (sq_nonneg _)
    calc E.rho * E.aScat * (E.Kl * E.KL) ^ 6 * E.lille ^ 2 * eta E ^ 2
        = (E.rho * E.lille ^ 2) * (E.aScat * E.Kl ^ 6 * E.KL ^ 6 * eta E ^ 2) := by
          rw [hKl6]; ring
      _ ≤ (3 * E.mu / 2) * (E.aScat * E.Kl ^ 6 * E.KL ^ 6 * eta E ^ 2) :=
          mul_le_mul_of_nonneg_right hρ hR0
      _ = (3 / 2) * (E.mu * E.Kl ^ 6) * (E.aScat * E.KL ^ 6 * eta E ^ 2) := by ring
      _ = (3 / 2) * ((E.mu ^ 2 * E.ell ^ 3 * dil E (1 / 2)) * E.Kl ^ 3)
            * (E.aScat * E.KL ^ 6 * eta E ^ 2) := by rw [hmuKl6]
      _ = (3 / 2) * (E0 E * (dil E (1 / 2) * E.Kl ^ 3 * E.KL ^ 6 * eta E ^ 2)) := by
          rw [E0]; ring
      _ ≤ (3 / 2) * e1A E := mul_le_mul_of_nonneg_left he1 (by norm_num)
  -- ## 5. the sign of `K₀⁷`
  have hA0 : 0 ≤ E.rho * E.aScat * (E.Kl * E.KL) ^ 6 * E.lille ^ 2 * eta E ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hrho0 ha0)
      (pow_nonneg (mul_nonneg hKl0 hKL0) 6)) (pow_nonneg hll0 2)) (sq_nonneg _)
  calc 4194304 * E.rho * K₀ ^ 7 * E.aScat * (E.Kl * E.KL) ^ 6 * E.lille ^ 2 * eta E ^ 2
      = 4194304 * (K₀ ^ 7
          * (E.rho * E.aScat * (E.Kl * E.KL) ^ 6 * E.lille ^ 2 * eta E ^ 2)) := by ring
    _ ≤ 4194304 * (|K₀ ^ 7|
          * (E.rho * E.aScat * (E.Kl * E.KL) ^ 6 * E.lille ^ 2 * eta E ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_right (le_abs_self _) hA0
    _ ≤ 4194304 * (|K₀ ^ 7| * ((3 / 2) * e1A E)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_left hcore (abs_nonneg _)
    _ = (4194304 * |K₀| ^ 7 * (3 / 2)) * e1A E := by
        rw [abs_pow]; ring

end Work.BoseC3QAll.Est1

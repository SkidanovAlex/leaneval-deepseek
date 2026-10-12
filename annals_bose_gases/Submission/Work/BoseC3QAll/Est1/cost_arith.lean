import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseC3QAll.Est1.estR1_defs
import Submission.Work.BoseC3QAll.errA_bounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.Est1.cost_arith` — the arithmetic of the `R1` brackets

The three error brackets of the `R1` estimate (`Est1.costTa`, `Est1.costB2`,
`Est1.costB3`) are dominated by `e1A`, uniformly in the parameter point:
there is a constant `C = C(K₀)` with

`costTa K₀ E hv + costB2 K₀ E + costB3 K₀ E ≤ C·e1A E`

for **every** `FSParamsView E` with `t = μa³ ≤ 1` and `b ≥ b₀ > 0`.

## The θ-word

`costTa = (800/b)·ℓ²·K₀·(K_ℓK_L)³·Mc²` with
`Mc = (1+K₀²)·1024·|z|·K₀³·𝓁²·K_HK_L√t·ρ_z·a`, so (FS `thm:Kafz` `z² = ρ_zℓ³`)

`costTa = (800/b)(1+K₀²)²1024²K₀⁷·ℓ²K_ℓ³K_L⁵K_H²·z²·𝓁⁴·t·ρ_z²·a²`,

and the **exact identity** `ca_arith_identity` below (using `ℓ = K_ℓ(μa)^{-1/2}`,
`𝓁 = (μa³)K_H²`, `z² = ρ_zℓ³`) is

`μ³·(ℓ²K_ℓ³K_L⁵K_H²z²𝓁⁴tρ_z²a²) = ρ_z³·(μ²aℓ³)·K_ℓ⁵K_L⁵𝓁⁵`,

i.e. `ℓ²K_ℓ³K_L⁵K_H²z²𝓁⁴tρ_z²a² = (ρ_z/μ)³·E₀K_ℓ⁵K_L⁵𝓁⁵`.  Hence

`costTa = (800/b)(1+K₀²)²1024²K₀⁷(ρ_z/μ)³·E₀K_ℓ⁵K_L⁵𝓁⁵
       ≤ 800·1024²(1+K₀²)²K₀⁷·(27/8)·e1A`

by `ρ_z ≤ (3/2)μ` (FS `eq:Close`) and the fact that `e1A` contains the summand
`E₀K_ℓ⁵K_L⁵𝓁⁵/b`.  (Here `ℓ²` is the *box side* squared: this is exactly the
factor the `ε_s`-trick of the θ-word produces — the gap `(b/800)ℓ⁻²n₊` pays
`(800/b)ℓ²Σ_s|cTa(s)|²`.  Replacing `ℓ` by the *lille* `𝓁` inserts
`(𝓁/ℓ)² = (μa³)K_H⁴·(μa)/K_ℓ²`, which is *unbounded* in the regime `a → 0` at
fixed `μa³`; that variant is refuted in
`Submission/Work/BoseB7A/Est1/cost_arith_false.lean`.)

## The squeezed words

`costB2 + costB3 = 2560·64⁶K₀¹¹(K_ℓK_L)⁶𝓁⁴η²ρ_za` is dominated by the
`E₀(μa³)^{1/2}K_ℓ³K_L⁶η²` summand of `e1A` through `K_ℓ³𝓁⁴ρ_z ≤ (3/2)μK_ℓ³`
(i.e. `𝓁 ≤ 1`, `ρ_z ≤ (3/2)μ` and `μ²ℓ³·(μa³)^{1/2} = μK_ℓ³`).

Both comparisons are absolute: no `t`-threshold is needed beyond `t ≤ 1`, so the
theorem holds with `t₀ = 1`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseC3QAll.Est1

open Work.BoseB7 Work.BoseBox

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]

/-! ## 1. Unpacking `costTa` -/

/-- `costTa` with `Mc²` expanded (pure ring algebra). -/
lemma ca_costTa_expand (K₀ : ℝ) (E : Q3Env Mode) (hv : FSParamsView E) :
    costTa K₀ E hv = (800 / E.b) * E.ell ^ 2 * K₀ ^ 7 * (1 + K₀ ^ 2) ^ 2
      * 1024 ^ 2 * E.Kl ^ 3 * E.KL ^ 5 * E.KH ^ 2 * E.z ^ 2 * E.lille ^ 4 * hv.t
      * E.rho ^ 2 * E.aScat ^ 2 := by
  rw [costTa, Mc]
  simp only [mul_pow]
  rw [sq_abs, Real.sq_sqrt hv.t_pos.le]
  ring

/-- `ℓ²(μa) = K_ℓ²` (FS `eq:def_ell`). -/
lemma ca_ell_sq_mul (E : Q3Env Mode) (hv : FSParamsView E) :
    E.ell ^ 2 * (E.mu * E.aScat) = E.Kl ^ 2 := by
  have hmu : 0 < E.mu := mu_pos E hv
  have ha : 0 < E.aScat := hv.a_pos
  have hmua : 0 < E.mu * E.aScat := mul_pos hmu ha
  have hsq : ((E.mu * E.aScat) ^ (-(1 / 2 : ℝ))) ^ 2 = (E.mu * E.aScat)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hmua.le]
    norm_num
    rw [Real.rpow_neg_one, mul_inv, mul_comm]
  rw [hv.ell_eq, side, mul_pow, hsq, mul_assoc, inv_mul_cancel₀ (ne_of_gt hmua), mul_one]

/-- **The exact `θ`-word identity** (cleared form):
`μ³·(ℓ²K_ℓ³K_L⁵K_H²z²𝓁⁴tρ_z²a²) = ρ_z³·(μ²aℓ³)·K_ℓ⁵K_L⁵𝓁⁵`.

This uses only `ℓ = K_ℓ(μa)^{-1/2}`, `𝓁 = (μa³)K_H²` and `z² = ρ_zℓ³`. -/
lemma ca_arith_identity (E : Q3Env Mode) (hv : FSParamsView E) :
    E.mu ^ 3 * (E.ell ^ 2 * E.Kl ^ 3 * E.KL ^ 5 * E.KH ^ 2 * E.z ^ 2 * E.lille ^ 4
        * hv.t * E.rho ^ 2 * E.aScat ^ 2)
      = E.rho ^ 3 * (E.mu ^ 2 * E.aScat * E.ell ^ 3) * E.Kl ^ 5 * E.KL ^ 5
        * E.lille ^ 5 := by
  have hℓ2 : E.ell ^ 2 * (E.mu * E.aScat) = E.Kl ^ 2 := ca_ell_sq_mul E hv
  have hz : E.z ^ 2 = E.rho * E.ell ^ 3 := zsq_eq E hv
  have h𝓁 : E.lille = hv.t * E.KH ^ 2 := by rw [Q3Env.lille, lille, ← hv.mu_eq]
  have hK : E.Kl ^ 5 = E.Kl ^ 3 * (E.ell ^ 2 * (E.mu * E.aScat)) := by rw [hℓ2]; ring
  rw [hz, h𝓁, hK]
  ring

/-! ## 2. `e1A` dominates its two summands -/

/-- `e1A` dominates its `E₀K_ℓ⁵K_L⁵𝓁⁵/b` summand. -/
lemma ca_e1A_ge_K (E : Q3Env Mode) (hv : FSParamsView E) (hb : 0 < E.b) :
    E0 E * E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5 / E.b ≤ e1A E := by
  have hKl : 0 ≤ E.Kl := (lt_of_lt_of_le zero_lt_one hv.one_le_Kl).le
  have hKL : 0 ≤ E.KL := (lt_of_lt_of_le zero_lt_one hv.one_le_KL).le
  have h𝓁 : 0 ≤ E.lille := (lille_pos E hv).le
  have hη : 0 ≤ eta E := by rw [errA_eta E hv]; exact fsXp_nonneg hv.t_pos.le
  have hd1 : 0 ≤ dil E (1 / 2) := dil_nonneg E hv _
  have hd4 : 0 ≤ dil E (1 / 4) := dil_nonneg E hv _
  have hE0 : 0 ≤ E0 E := (errA_E0_pos E hv).le
  have h1 : 0 ≤ dil E (1 / 2) * E.Kl ^ 3 * E.KL ^ 6 * (eta E) ^ 2 := by positivity
  have h2 : 0 ≤ dil E (1 / 2) * E.KL ^ 3 * E.lille ^ 2 := by positivity
  have h4 : 0 ≤ E.Kl ^ (3 / 2 : ℝ) * E.KL ^ 3 * dil E (1 / 4) * E.lille ^ 2
      * eta E := by positivity
  have hshape : E0 E * (E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5 / E.b)
      = E0 E * E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5 / E.b := by ring
  rw [← hshape, e1A]
  refine mul_le_mul_of_nonneg_left ?_ hE0
  linarith

/-- `e1A` dominates its `E₀(μa³)^{1/2}K_ℓ³K_L⁶η²` summand. -/
lemma ca_e1A_ge_eta (E : Q3Env Mode) (hv : FSParamsView E) (hb : 0 < E.b) :
    E0 E * dil E (1 / 2) * E.Kl ^ 3 * E.KL ^ 6 * (eta E) ^ 2 ≤ e1A E := by
  have hKl : 0 ≤ E.Kl := (lt_of_lt_of_le zero_lt_one hv.one_le_Kl).le
  have hKL : 0 ≤ E.KL := (lt_of_lt_of_le zero_lt_one hv.one_le_KL).le
  have h𝓁 : 0 ≤ E.lille := (lille_pos E hv).le
  have hη : 0 ≤ eta E := by rw [errA_eta E hv]; exact fsXp_nonneg hv.t_pos.le
  have hd1 : 0 ≤ dil E (1 / 2) := dil_nonneg E hv _
  have hd4 : 0 ≤ dil E (1 / 4) := dil_nonneg E hv _
  have hE0 : 0 ≤ E0 E := (errA_E0_pos E hv).le
  have h2 : 0 ≤ dil E (1 / 2) * E.KL ^ 3 * E.lille ^ 2 := by positivity
  have h3 : 0 ≤ E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5 / E.b := by positivity
  have h4 : 0 ≤ E.Kl ^ (3 / 2 : ℝ) * E.KL ^ 3 * dil E (1 / 4) * E.lille ^ 2
      * eta E := by positivity
  have hshape : E0 E * (dil E (1 / 2) * E.Kl ^ 3 * E.KL ^ 6 * (eta E) ^ 2)
      = E0 E * dil E (1 / 2) * E.Kl ^ 3 * E.KL ^ 6 * (eta E) ^ 2 := by ring
  rw [← hshape, e1A]
  refine mul_le_mul_of_nonneg_left ?_ hE0
  linarith

/-! ## 3. The two cost comparisons -/

/-- `ρ_z³ ≤ (27/8)μ³` (FS `eq:Close`). -/
lemma ca_rho_cube_le (E : Q3Env Mode) (hv : FSParamsView E) :
    E.rho ^ 3 ≤ (27 / 8) * E.mu ^ 3 := by
  have hμ : 0 < E.mu := mu_pos E hv
  have hρ : E.rho ≤ 3 * E.mu / 2 := rho_le E hv
  have hρ0 : 0 ≤ E.rho := (rho_pos E hv).le
  have h := pow_le_pow_left₀ hρ0 hρ 3
  have h2 : (3 * E.mu / 2) ^ 3 = 27 / 8 * E.mu ^ 3 := by ring
  linarith [h, h2.le, h2.ge]

/-- **The θ-word bracket is dominated by `e1A`.** -/
theorem ca_costTa_le_e1A (K₀ : ℝ) (hK₀ : 0 ≤ K₀) (E : Q3Env Mode) (hv : FSParamsView E)
    (hb : 0 < E.b) :
    costTa K₀ E hv ≤ 800 * 1024 ^ 2 * (1 + K₀ ^ 2) ^ 2 * K₀ ^ 7 * (27 / 8) * e1A E := by
  have hμ : 0 < E.mu := mu_pos E hv
  have hbne : E.b ≠ 0 := ne_of_gt hb
  have hρ3 := ca_rho_cube_le E hv
  have hident := ca_arith_identity E hv
  -- `ρ_z³ ≤ (27/8)μ³` inside the bracket
  have hstep : E.rho ^ 3 * (E.mu ^ 2 * E.aScat * E.ell ^ 3) * E.Kl ^ 5 * E.KL ^ 5
        * E.lille ^ 5
      ≤ ((27 / 8) * E.mu ^ 3) * (E.mu ^ 2 * E.aScat * E.ell ^ 3) * E.Kl ^ 5 * E.KL ^ 5
        * E.lille ^ 5 := by
    calc E.rho ^ 3 * (E.mu ^ 2 * E.aScat * E.ell ^ 3) * E.Kl ^ 5 * E.KL ^ 5
          * E.lille ^ 5
        = E.rho ^ 3 * ((E.mu ^ 2 * E.aScat * E.ell ^ 3) * E.Kl ^ 5 * E.KL ^ 5
            * E.lille ^ 5) := by ring
      _ ≤ ((27 / 8) * E.mu ^ 3) * ((E.mu ^ 2 * E.aScat * E.ell ^ 3) * E.Kl ^ 5
            * E.KL ^ 5 * E.lille ^ 5) := by
          refine mul_le_mul_of_nonneg_right hρ3 ?_
          have ha : 0 < E.aScat := hv.a_pos
          have hℓ : 0 < E.ell := ell_pos E hv
          have hKl : 0 ≤ E.Kl := (lt_of_lt_of_le zero_lt_one hv.one_le_Kl).le
          have hKL : 0 ≤ E.KL := (lt_of_lt_of_le zero_lt_one hv.one_le_KL).le
          have h𝓁 : 0 ≤ E.lille := (lille_pos E hv).le
          positivity
      _ = ((27 / 8) * E.mu ^ 3) * (E.mu ^ 2 * E.aScat * E.ell ^ 3) * E.Kl ^ 5
            * E.KL ^ 5 * E.lille ^ 5 := by ring
  have hmain : costTa K₀ E hv * E.mu ^ 3
      ≤ (800 * 1024 ^ 2 * (1 + K₀ ^ 2) ^ 2 * K₀ ^ 7 * (27 / 8))
        * (E0 E * E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5 / E.b) * E.mu ^ 3 := by
    calc costTa K₀ E hv * E.mu ^ 3
        = (800 / E.b) * K₀ ^ 7 * (1 + K₀ ^ 2) ^ 2 * 1024 ^ 2
          * (E.mu ^ 3 * (E.ell ^ 2 * E.Kl ^ 3 * E.KL ^ 5 * E.KH ^ 2 * E.z ^ 2
              * E.lille ^ 4 * hv.t * E.rho ^ 2 * E.aScat ^ 2)) := by
          rw [ca_costTa_expand]
          ring
      _ = (800 / E.b) * K₀ ^ 7 * (1 + K₀ ^ 2) ^ 2 * 1024 ^ 2
          * (E.rho ^ 3 * (E.mu ^ 2 * E.aScat * E.ell ^ 3) * E.Kl ^ 5 * E.KL ^ 5
              * E.lille ^ 5) := by
          rw [hident]
      _ ≤ (800 / E.b) * K₀ ^ 7 * (1 + K₀ ^ 2) ^ 2 * 1024 ^ 2
          * (((27 / 8) * E.mu ^ 3) * (E.mu ^ 2 * E.aScat * E.ell ^ 3) * E.Kl ^ 5
              * E.KL ^ 5 * E.lille ^ 5) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = (800 * 1024 ^ 2 * (1 + K₀ ^ 2) ^ 2 * K₀ ^ 7 * (27 / 8))
            * (E0 E * E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5 / E.b) * E.mu ^ 3 := by
          rw [E0]
          field_simp
  have hdiv : costTa K₀ E hv
      ≤ (800 * 1024 ^ 2 * (1 + K₀ ^ 2) ^ 2 * K₀ ^ 7 * (27 / 8))
        * (E0 E * E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5 / E.b) :=
    le_of_mul_le_mul_right hmain (pow_pos hμ 3)
  calc costTa K₀ E hv
      ≤ (800 * 1024 ^ 2 * (1 + K₀ ^ 2) ^ 2 * K₀ ^ 7 * (27 / 8))
        * (E0 E * E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5 / E.b) := hdiv
    _ ≤ 800 * 1024 ^ 2 * (1 + K₀ ^ 2) ^ 2 * K₀ ^ 7 * (27 / 8) * e1A E :=
        mul_le_mul_of_nonneg_left (ca_e1A_ge_K E hv hb) (by positivity)

/-- **The two squeezed-word brackets are dominated by `e1A`.** -/
theorem ca_costB_le_e1A (K₀ : ℝ) (hK₀ : 0 ≤ K₀) (E : Q3Env Mode) (hv : FSParamsView E)
    (hb : 0 < E.b) :
    costB2 K₀ E + costB3 K₀ E ≤ 2560 * 64 ^ 6 * K₀ ^ 11 * (3 / 2) * e1A E := by
  have hKl : 0 ≤ E.Kl := (lt_of_lt_of_le zero_lt_one hv.one_le_Kl).le
  have hKL : 0 ≤ E.KL := (lt_of_lt_of_le zero_lt_one hv.one_le_KL).le
  have h𝓁 : 0 ≤ E.lille := (lille_pos E hv).le
  have hη : 0 ≤ eta E := by rw [errA_eta E hv]; exact fsXp_nonneg hv.t_pos.le
  have h𝓁1 : E.lille ^ 4 ≤ 1 := pow_le_one₀ h𝓁 (lille_le_one E hv)
  have hρ : E.rho ≤ 3 * E.mu / 2 := rho_le E hv
  have hρ0 : 0 ≤ E.rho := (rho_pos E hv).le
  have hsum : costB2 K₀ E + costB3 K₀ E
      = 2560 * 64 ^ 6 * K₀ ^ 11 * ((E.Kl * E.KL) ^ 6 * E.lille ^ 4 * (eta E) ^ 2
        * E.rho * E.aScat) := by
    rw [costB2, costB3]
    ring
  -- `μ²ℓ³·(μa³)^{1/2} = μK_ℓ³`
  have hX : E.mu ^ 2 * E.ell ^ 3 * dil E (1 / 2) = E.mu * E.Kl ^ 3 := by
    have hm : E.mu ^ 2 * E.ell ^ 3 = E.mu * fsXp hv.t (-166) := by
      rw [show E.mu ^ 2 * E.ell ^ 3 = E.mu * (E.mu * E.ell ^ 3) by ring, errA_mue E hv]
    have hd : dil E (1 / 2) = fsXp hv.t (323 / 2) := by
      rw [errA_dil E hv (1 / 2)]
      congr 1
      norm_num
    have h3 : E.Kl ^ 3 = fsXp hv.t (-(9 / 2)) := by
      rw [errA_Kl E hv, fsXp_pow hv.t_pos.le]
      congr 1
      norm_num
    have hprod : fsXp hv.t (-166) * fsXp hv.t (323 / 2) = fsXp hv.t (-(9 / 2)) := by
      rw [fsXp_mul hv.t_pos]
      congr 1
      norm_num
    rw [hm, hd, h3, mul_assoc, hprod]
  -- the scalar core `K_ℓ³𝓁⁴ρ_z ≤ (3/2)μ²ℓ³(μa³)^{1/2}`
  have hcore : E.Kl ^ 3 * E.lille ^ 4 * E.rho
      ≤ (3 / 2) * (E.mu ^ 2 * E.ell ^ 3 * dil E (1 / 2)) := by
    rw [hX]
    have h2 : E.lille ^ 4 * E.rho ≤ (3 / 2) * E.mu := by
      have h := mul_le_mul h𝓁1 hρ hρ0 (by norm_num : (0 : ℝ) ≤ 1)
      linarith [h]
    calc E.Kl ^ 3 * E.lille ^ 4 * E.rho = E.Kl ^ 3 * (E.lille ^ 4 * E.rho) := by ring
      _ ≤ E.Kl ^ 3 * ((3 / 2) * E.mu) := mul_le_mul_of_nonneg_left h2 (pow_nonneg hKl 3)
      _ = (3 / 2) * (E.mu * E.Kl ^ 3) := by ring
  have hmid : (E.Kl * E.KL) ^ 6 * E.lille ^ 4 * (eta E) ^ 2 * E.rho * E.aScat
      ≤ (3 / 2) * (E0 E * dil E (1 / 2) * E.Kl ^ 3 * E.KL ^ 6 * (eta E) ^ 2) := by
    have ha : 0 < E.aScat := hv.a_pos
    have hc : 0 ≤ E.KL ^ 6 * (eta E) ^ 2 * E.aScat * E.Kl ^ 3 := by positivity
    have hstep := mul_le_mul_of_nonneg_right hcore hc
    calc (E.Kl * E.KL) ^ 6 * E.lille ^ 4 * (eta E) ^ 2 * E.rho * E.aScat
        = (E.Kl ^ 3 * E.lille ^ 4 * E.rho) * (E.KL ^ 6 * (eta E) ^ 2 * E.aScat
            * E.Kl ^ 3) := by ring
      _ ≤ ((3 / 2) * (E.mu ^ 2 * E.ell ^ 3 * dil E (1 / 2))) * (E.KL ^ 6 * (eta E) ^ 2
            * E.aScat * E.Kl ^ 3) := hstep
      _ = (3 / 2) * (E0 E * dil E (1 / 2) * E.Kl ^ 3 * E.KL ^ 6 * (eta E) ^ 2) := by
        rw [E0]
        ring
  calc costB2 K₀ E + costB3 K₀ E
      = 2560 * 64 ^ 6 * K₀ ^ 11 * ((E.Kl * E.KL) ^ 6 * E.lille ^ 4 * (eta E) ^ 2
          * E.rho * E.aScat) := hsum
    _ ≤ 2560 * 64 ^ 6 * K₀ ^ 11 * ((3 / 2) * (E0 E * dil E (1 / 2) * E.Kl ^ 3
          * E.KL ^ 6 * (eta E) ^ 2)) :=
        mul_le_mul_of_nonneg_left hmid (by positivity)
    _ = 2560 * 64 ^ 6 * K₀ ^ 11 * (3 / 2) * (E0 E * dil E (1 / 2) * E.Kl ^ 3
          * E.KL ^ 6 * (eta E) ^ 2) := by ring
    _ ≤ 2560 * 64 ^ 6 * K₀ ^ 11 * (3 / 2) * e1A E :=
        mul_le_mul_of_nonneg_left (ca_e1A_ge_eta E hv hb) (by positivity)

/-! ## 4. The theorem -/

theorem cost_arith (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) :
    ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
        (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b →
        Work.BoseC3QAll.Est1.costTa K₀ E hv + Work.BoseC3QAll.Est1.costB2 K₀ E
          + Work.BoseC3QAll.Est1.costB3 K₀ E ≤ C * Work.BoseC3QAll.e1A E := by
  by_cases hK : 0 ≤ K₀
  · refine ⟨800 * 1024 ^ 2 * (1 + K₀ ^ 2) ^ 2 * K₀ ^ 7 * (27 / 8)
      + 2560 * 64 ^ 6 * K₀ ^ 11 * (3 / 2), 1, ?_, one_pos, ?_⟩
    · positivity
    · intro Mode _ _ E hv _ hb
      have hbpos : 0 < E.b := lt_of_lt_of_le hb₀ hb
      have h1 := ca_costTa_le_e1A K₀ hK E hv hbpos
      have h2 := ca_costB_le_e1A K₀ hK E hv hbpos
      have h3 := e1A_nonneg E hv hbpos
      nlinarith [h1, h2, h3]
  · have hKlt : K₀ < 0 := not_le.mp hK
    refine ⟨1, 1, by norm_num, one_pos, ?_⟩
    intro Mode _ _ E hv _ hb
    have hbpos : 0 < E.b := lt_of_lt_of_le hb₀ hb
    have hKl : 0 ≤ E.Kl := (lt_of_lt_of_le zero_lt_one hv.one_le_Kl).le
    have hKL : 0 ≤ E.KL := (lt_of_lt_of_le zero_lt_one hv.one_le_KL).le
    have h𝓁 : 0 ≤ E.lille := (lille_pos E hv).le
    have hη : 0 ≤ eta E := by rw [errA_eta E hv]; exact fsXp_nonneg hv.t_pos.le
    have hρ0 : 0 ≤ E.rho := (rho_pos E hv).le
    have ha : 0 ≤ E.aScat := (hv.a_pos).le
    have hK11 : K₀ ^ 11 ≤ 0 := by
      have h := mul_nonpos_of_nonpos_of_nonneg hKlt.le (pow_nonneg (sq_nonneg K₀) 5)
      have he : K₀ ^ 11 = K₀ * (K₀ ^ 2) ^ 5 := by ring
      linarith [h, he.le, he.ge]
    have hTa : costTa K₀ E hv ≤ 0 := by
      rw [costTa]
      have harr : (800 / E.b) * E.ell ^ 2 * K₀ * (E.Kl * E.KL) ^ 3 * (Mc K₀ E hv) ^ 2
          = K₀ * ((800 / E.b) * E.ell ^ 2 * (E.Kl * E.KL) ^ 3 * (Mc K₀ E hv) ^ 2) := by
        ring
      rw [harr]
      have h1 : 0 ≤ 800 / E.b := div_nonneg (by norm_num) hbpos.le
      have hbr : 0 ≤ (800 / E.b) * E.ell ^ 2 * (E.Kl * E.KL) ^ 3 * (Mc K₀ E hv) ^ 2 :=
        mul_nonneg (mul_nonneg (mul_nonneg h1 (sq_nonneg _))
          (pow_nonneg (mul_nonneg hKl hKL) 3)) (sq_nonneg _)
      exact mul_nonpos_of_nonpos_of_nonneg hKlt.le hbr
    have hB2 : costB2 K₀ E ≤ 0 := by
      rw [costB2]
      have hQ : 0 ≤ (E.Kl * E.KL) ^ 6 * E.lille ^ 4 * (eta E) ^ 2 * E.rho * E.aScat :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
          (pow_nonneg (mul_nonneg hKl hKL) 6) (pow_nonneg h𝓁 4)) (sq_nonneg _)) hρ0) ha
      have harr : 512 * 64 ^ 6 * K₀ ^ 11 * (E.Kl * E.KL) ^ 6 * E.lille ^ 4 * (eta E) ^ 2
            * E.rho * E.aScat
          = (512 * 64 ^ 6 * K₀ ^ 11) * ((E.Kl * E.KL) ^ 6 * E.lille ^ 4 * (eta E) ^ 2
              * E.rho * E.aScat) := by ring
      rw [harr]
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hK11) hQ
    have hB3 : costB3 K₀ E ≤ 0 := by
      rw [costB3]
      have hQ : 0 ≤ (E.Kl * E.KL) ^ 6 * E.lille ^ 4 * (eta E) ^ 2 * E.rho * E.aScat :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
          (pow_nonneg (mul_nonneg hKl hKL) 6) (pow_nonneg h𝓁 4)) (sq_nonneg _)) hρ0) ha
      have harr : 2048 * 64 ^ 6 * K₀ ^ 11 * (E.Kl * E.KL) ^ 6 * E.lille ^ 4 * (eta E) ^ 2
            * E.rho * E.aScat
          = (2048 * 64 ^ 6 * K₀ ^ 11) * ((E.Kl * E.KL) ^ 6 * E.lille ^ 4 * (eta E) ^ 2
              * E.rho * E.aScat) := by ring
      rw [harr]
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hK11) hQ
    have hsum0 : costTa K₀ E hv + costB2 K₀ E + costB3 K₀ E ≤ 0 := by
      linarith [hTa, hB2, hB3]
    have h3 := e1A_nonneg E hv hbpos
    linarith [hsum0, h3]

end Work.BoseC3QAll.Est1

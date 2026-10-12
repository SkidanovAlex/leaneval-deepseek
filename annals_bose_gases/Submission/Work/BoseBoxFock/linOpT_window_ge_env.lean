import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.GrowthEnv
import Submission.Work.BoseBoxFock.bddBelow_valFS_honest
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.linOpT_window_ge_env` — the linear row `T.linOpT` in the growth envelope

FS's substituted Hamiltonian `𝒦(z)` (`Work.BoseFixR.KzOp`) contains the linear word

  `T.linOpT (KzEnvAt E ρ) = (ρ_z z Ŵ₁ω(0)) • Σ_{s≠0} χ̂²(s) • (ã_s† + ã_s)`

(`Work.BoseB7A.TildeData.linOpT`, FS `eq:Kz`'s `𝒬₁^ex`); at condensate density `ρ` the
`z`-dependence of the coefficient is `E'.rho * E'.z * E'.W1omega0` with
`E' = KzEnvAt E ρ`, i.e. `E'.z = √(ρ ℓ³)` and `E'.rho = z²/ℓ³ = ρ` (for `ℓ > 0`).  The
coefficient therefore grows like `ρ^{3/2}` (times an `E`-dependent constant), which is
exactly the growth of the design envelope `genv ρ = 1 + √ρ·ρ`.

**This module proves the row is bounded below in that envelope.**  For every `M ≥ 0`
there is `C ≥ 0` (explicit: `√(ℓ³)·|Ŵ₁ω(0)|·2√M·√(Σ_s χ̂²(s)²)`) with

  `-(C · genv ρ) ‖g‖² ≤ ⟨g, T.linOpT (KzEnvAt E ρ) g⟩`

for all `ρ ≥ 0` and every `g` in FS's spectral window `1_{[0,𝓜]}(n₊)`
(`TildeData.NWindow M g`, `eq:LocalizedAftercNumber`).

The proof is the `ℓ²`-form of the window linear bound
(`Work.BoseB7A.NWindow_linear_bound`):

  `|⟨g, Σ_s c_s(ã_s†+ã_s)g⟩| ≤ 2√M √(Σ_s c_s²) ‖g‖²`,

applied with the `ρ`-independent coefficients `c_s = χ̂²(s)`, together with the one
arithmetic input `KzEnvAt_coeff_abs_le` — the growth bound
`|E'.rho * E'.z * Ŵ₁ω(0)| ≤ √(ℓ³)|Ŵ₁ω(0)| · genv ρ`, which is where the `ρ^{3/2}` is paid
by `√ρ·ρ ≤ genv ρ`.  (In particular no Bessel hypothesis `Σ_k n_k ≤ Cn·n₊` is needed for
this row, unlike the `KzBogFS`/`Q3T` rows.)

Sibling rows (`Q3T_window_ge_env`, `KzBogFS_window_ge_env`) are proved by the same shape of
argument; this file is self-contained apart from the corpus lemmas named above.
-/

namespace Work.BoseBoxFock

/-- **The `ρ`-growth of the `linOpT` coefficient.**  At condensate density `ρ ≥ 0` the
coefficient `ρ_z z Ŵ₁ω(0)` of FS's linear word (`Work.BoseB7A.TildeData.linOpT`, FS
`𝒬₁^ex`) is bounded by the envelope `genv ρ = 1 + √ρ·ρ` times the `ρ`-independent constant
`√(ℓ³)|Ŵ₁ω(0)|`.

Indeed `KzEnvAt E ρ` replaces `z` by `√(ρℓ³)` and leaves `ℓ`, `Ŵ₁ω(0)` fixed, so for
`ℓ > 0`

  `ρ_z z Ŵ₁ω(0) = (ρ) · √ρ·√(ℓ³) · Ŵ₁ω(0) = (√ρ·ρ)·(√(ℓ³)|Ŵ₁ω(0)|)`

(`z² = ρℓ³` cancels the `ℓ³` in `ρ_z = z²/ℓ³`), and `√ρ·ρ ≤ genv ρ`
(`sqrt_mul_self_le_genv`).  For `ℓ ≤ 0` the square root `√(ρℓ³)` vanishes, so the
coefficient is `0` and the bound is trivial. -/
lemma KzEnvAt_coeff_abs_le {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    |(Work.BoseFixR.KzEnvAt E ρ).rho * (Work.BoseFixR.KzEnvAt E ρ).z * E.W1omega0|
      ≤ Real.sqrt (E.ell ^ 3) * |E.W1omega0| * genv ρ := by
  have hz : (Work.BoseFixR.KzEnvAt E ρ).z = Real.sqrt (ρ * E.ell ^ 3) := rfl
  have hell : (Work.BoseFixR.KzEnvAt E ρ).ell = E.ell := rfl
  have hrho : (Work.BoseFixR.KzEnvAt E ρ).rho
      = Real.sqrt (ρ * E.ell ^ 3) ^ 2 / E.ell ^ 3 := by
    rw [Work.BoseB7.Q3Env.rho, hz, hell, Work.BoseB7.rhoZ]
  rw [hrho, hz]
  rcases lt_or_ge 0 E.ell with hℓ | hℓ
  · -- `ℓ > 0`: `z² = ρℓ³` cancels the `ℓ³`, leaving `ρ·z = (√ρ·ρ)·√(ℓ³)`
    have hpow_ne : E.ell ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
    have hρℓ : 0 ≤ ρ * E.ell ^ 3 := mul_nonneg hρ (by positivity)
    have hs2 : Real.sqrt (ρ * E.ell ^ 3) ^ 2 = ρ * E.ell ^ 3 := Real.sq_sqrt hρℓ
    have hsmul : Real.sqrt (ρ * E.ell ^ 3) = Real.sqrt ρ * Real.sqrt (E.ell ^ 3) :=
      Real.sqrt_mul hρ (E.ell ^ 3)
    have hfrac : ρ * E.ell ^ 3 / E.ell ^ 3 = ρ := by
      rw [mul_div_assoc, div_self hpow_ne, mul_one]
    have hval : Real.sqrt (ρ * E.ell ^ 3) ^ 2 / E.ell ^ 3 * Real.sqrt (ρ * E.ell ^ 3)
        * E.W1omega0 = ρ * (Real.sqrt ρ * Real.sqrt (E.ell ^ 3)) * E.W1omega0 := by
      rw [hs2, hfrac, hsmul]
    rw [hval]
    simp only [abs_mul, abs_of_nonneg hρ, abs_of_nonneg (Real.sqrt_nonneg ρ),
      abs_of_nonneg (Real.sqrt_nonneg (E.ell ^ 3))]
    calc ρ * (Real.sqrt ρ * Real.sqrt (E.ell ^ 3)) * |E.W1omega0|
        = (Real.sqrt ρ * ρ) * (Real.sqrt (E.ell ^ 3) * |E.W1omega0|) := by ring
      _ ≤ genv ρ * (Real.sqrt (E.ell ^ 3) * |E.W1omega0|) :=
          mul_le_mul_of_nonneg_right (sqrt_mul_self_le_genv ρ)
            (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
      _ = Real.sqrt (E.ell ^ 3) * |E.W1omega0| * genv ρ := by ring
  · -- `ℓ ≤ 0`: `ρℓ³ ≤ 0`, so `z = √(ρℓ³) = 0` and the coefficient vanishes
    have hℓ3 : E.ell ^ 3 ≤ 0 := by nlinarith [sq_nonneg E.ell, hℓ]
    have hs0 : Real.sqrt (ρ * E.ell ^ 3) = 0 :=
      Real.sqrt_eq_zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hρ hℓ3)
    have hzero : |Real.sqrt (ρ * E.ell ^ 3) ^ 2 / E.ell ^ 3 * Real.sqrt (ρ * E.ell ^ 3)
        * E.W1omega0| = 0 := by rw [hs0]; simp
    rw [hzero]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) (le_of_lt (genv_pos ρ))

/-- **The linear row `T.linOpT` is bounded below in the growth envelope `genv`.**

For FS's linear word `T.linOpT (KzEnvAt E ρ) = (ρ_zzŴ₁ω(0)) • Σ_{s≠0}χ̂²(s)•(ã_s†+ã_s)`
(`eq:Kz`'s `𝒬₁^ex`) there is `C ≥ 0`, *independent of `ρ`*, with

  `-(C·genv ρ)·‖g‖² ≤ ⟨g, T.linOpT (KzEnvAt E ρ) g⟩`

for every `ρ ≥ 0` and every window vector `g` (`TildeData.NWindow M g`, `M ≥ 0`).
Explicitly `C = √(ℓ³)·|Ŵ₁ω(0)|·2√M·√(Σ_{s≠0}χ̂²(s)²)`.

Proof: expand the `•` and `Σ` (`qw_smul`), pull the coefficient
`d = ρ_z z Ŵ₁ω(0)` out of the quadratic form, and bound the remaining linear word with
the `ρ`-independent coefficients `χ̂²(s)` by the window linear bound
(`Work.BoseB7A.NWindow_linear_bound`, the `ℓ²`-Cauchy–Schwarz form of
`eq:EstimateQ3Tilde4`).  The `ρ`-dependence sits entirely in `d`, which is paid by
`KzEnvAt_coeff_abs_le`; the envelope's `√ρ·ρ` is exactly its `ρ^{3/2}` growth. -/
theorem linOpT_window_ge_env {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env Mode)
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 0 ≤ ρ → ∀ g : F.H, T.NWindow M g →
      -(C * Work.BoseBoxFock.genv ρ) * F.normSq g
        ≤ F.qw g (T.linOpT (Work.BoseFixR.KzEnvAt E ρ)) := by
  refine ⟨Real.sqrt (E.ell ^ 3) * |E.W1omega0|
      * (2 * Real.sqrt M * Real.sqrt (∑ s ∈ Work.BoseB7.excited Mode, E.hatChiSq s ^ 2)),
    ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  · intro ρ hρ g hg
    -- the coefficient of the linear word, and its growth bound
    have hdabs := KzEnvAt_coeff_abs_le E hρ
    -- `linOpT` is the scalar `d` times the `χ̂²`-weighted linear word
    have hexp : F.qw g (T.linOpT (Work.BoseFixR.KzEnvAt E ρ))
        = ((Work.BoseFixR.KzEnvAt E ρ).rho * (Work.BoseFixR.KzEnvAt E ρ).z * E.W1omega0)
          * F.qw g (∑ s ∈ Work.BoseB7.excited Mode,
              (E.hatChiSq s) • (T.taDag s + T.ta s)) := by
      rw [Work.BoseB7A.TildeData.linOpT, Work.BoseB7.FockData.qw_smul]
      rfl
    -- the window linear bound at the `ρ`-independent coefficients `χ̂²`
    have hlin := Work.BoseB7A.NWindow_linear_bound F T hM hg (Work.BoseB7.excited Mode)
      (fun s hs => (Finset.mem_erase.mp hs).1) E.hatChiSq
    have h2 : |F.qw g (T.linOpT (Work.BoseFixR.KzEnvAt E ρ))| ≤
        (Real.sqrt (E.ell ^ 3) * |E.W1omega0|
          * (2 * Real.sqrt M * Real.sqrt (∑ s ∈ Work.BoseB7.excited Mode, E.hatChiSq s ^ 2)))
          * genv ρ * F.normSq g := by
      rw [hexp, abs_mul]
      calc |(Work.BoseFixR.KzEnvAt E ρ).rho * (Work.BoseFixR.KzEnvAt E ρ).z * E.W1omega0|
            * |F.qw g (∑ s ∈ Work.BoseB7.excited Mode,
                (E.hatChiSq s) • (T.taDag s + T.ta s))|
          ≤ (Real.sqrt (E.ell ^ 3) * |E.W1omega0| * genv ρ)
              * (2 * Real.sqrt M
                * Real.sqrt (∑ s ∈ Work.BoseB7.excited Mode, E.hatChiSq s ^ 2)
                * F.normSq g) :=
            mul_le_mul hdabs hlin (abs_nonneg _)
              (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
                (le_of_lt (genv_pos ρ)))
        _ = (Real.sqrt (E.ell ^ 3) * |E.W1omega0|
              * (2 * Real.sqrt M
                * Real.sqrt (∑ s ∈ Work.BoseB7.excited Mode, E.hatChiSq s ^ 2)))
              * genv ρ * F.normSq g := by ring
    have h3 := neg_abs_le (F.qw g (T.linOpT (Work.BoseFixR.KzEnvAt E ρ)))
    linarith [h2, h3]

end Work.BoseBoxFock

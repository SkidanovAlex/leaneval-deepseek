import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.GrowthEnv
import Submission.Work.BoseBoxFock.bddBelow_valFS_honest
import Submission.Work.BoseBoxFock.normSq_a_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.Q2ex_window_ge_env` — the diagonal row `Q₂^ex` in the growth envelope

FS's substituted Hamiltonian `𝒦(z)` (`Work.BoseFixR.KzOp`) contains the *diagonal*
number row

  `F.Q2ex (KzEnvAt E ρ) = Σ_{k ≠ 0} (ρ_z (Ŵ₁ω(k) + Ŵ₁ω(0))) • n_k`

(`Work.BoseB7.Q3Defs`, FS `eq:Kz`; `n_k = a_k†a_k`), re-pointed at the condensate density
`ρ` through `KzEnvAt E ρ`, which replaces `z` by `√(ρℓ³)` and hence `ρ_z = z²/ℓ³` by a
density that is *at most* `ρ` (and, for `ℓ > 0`, equal to `ρ`).

**This module proves the row is bounded below in the design envelope**
`genv ρ = 1 + √ρ·ρ`: there is `C ≥ 0`, independent of `ρ`, with

  `-(C · genv ρ) ‖g‖² ≤ ⟨g, F.Q2ex (KzEnvAt E ρ) g⟩`

for every `ρ ≥ 0` and every `g` in FS's spectral window `1_{[0,𝓜]}(n₊)`
(`Work.BoseB7A.TildeData.NWindow M g`, `eq:LocalizedAftercNumber`).

Route (the crudest one; the sibling rows `Q3T_window_ge_env`, `KzBogFS_window_ge_env`,
`linOpT_window_ge_env` are proved by the same shape of argument):

* the row is a finite sum of `c_k • n_k` with `c_k = ρ_z(Ŵ₁ω(k)+Ŵ₁ω(0))`, and the
  quadratic form expands as `Σ_k c_k ⟨g, n_k g⟩`
  (`F.qw` is linear in the operator, `bp` is linear in its first argument);
* each term is *nonnegative* (`⟨g, n_k g⟩ = ‖a_k g‖² ≥ 0`), and on the window the
  Bessel hypothesis `Σ_k a_k†a_k ≤ Cn·n₊` together with `⟨g, n₊ g⟩ ≤ 𝓜‖g‖²`
  (`Work.BoseB7A.NWindow_bp_N_le`) gives the single-mode bound
  `⟨g, n_k g⟩ ≤ Cn·𝓜‖g‖²` (`normSq_a_le`, `Work.BoseBoxFock.normSq_a_le`);
* the `ρ`-dependence sits entirely in `ρ_z`, which grows like `ρ ≤ genv ρ`
  (`KzEnvAt_rho_le_genv`), not like the `ρ^{3/2}` of the linear row;
* summing the termwise bound `c_k⟨g,n_kg⟩ ≥ -|c_k|·Cn𝓜‖g‖²` gives the explicit constant
  `C = (Σ_{k≠0}|Ŵ₁ω(k)+Ŵ₁ω(0)|)·Cn·𝓜`.

No Cauchy–Schwarz, no completeness and no diagonalisation is used.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## 1. The density `ρ_z` of `KzEnvAt` is at most `ρ` (and `≤ genv ρ`) -/

/-- **The growth of `KzEnvAt`'s density.**  `KzEnvAt E ρ` sets `z := √(ρℓ³)` and leaves `ℓ`
fixed, so its condensate density `ρ_z = z²/ℓ³` is nonnegative and at most `ρ` for `ρ ≥ 0`:
for `ℓ > 0` the square root cancels the `ℓ³` (`z² = ρℓ³`), while for `ℓ ≤ 0` one has
`ρℓ³ ≤ 0`, hence `z = 0`.  In particular `ρ_z ≤ genv ρ = 1 + √ρ·ρ`. -/
lemma KzEnvAt_rho_le_genv {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    0 ≤ (Work.BoseFixR.KzEnvAt E ρ).rho ∧ (Work.BoseFixR.KzEnvAt E ρ).rho ≤ genv ρ := by
  have hz : (Work.BoseFixR.KzEnvAt E ρ).z = Real.sqrt (ρ * E.ell ^ 3) := rfl
  have hell : (Work.BoseFixR.KzEnvAt E ρ).ell = E.ell := rfl
  have hrho : (Work.BoseFixR.KzEnvAt E ρ).rho
      = Real.sqrt (ρ * E.ell ^ 3) ^ 2 / E.ell ^ 3 := by
    rw [Work.BoseB7.Q3Env.rho, hz, hell, Work.BoseB7.rhoZ]
  rw [hrho]
  rcases lt_or_ge 0 E.ell with hℓ | hℓ
  · -- `ℓ > 0`: `ρ_z = ρ`, and `ρ ≤ genv ρ`
    have hpow_ne : E.ell ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
    have hρℓ : 0 ≤ ρ * E.ell ^ 3 := mul_nonneg hρ (by positivity)
    rw [Real.sq_sqrt hρℓ, mul_div_assoc, div_self hpow_ne, mul_one]
    exact ⟨hρ, self_le_genv hρ⟩
  · -- `ℓ ≤ 0`: `ρℓ³ ≤ 0`, so `z = √(ρℓ³) = 0` and `ρ_z = 0 ≤ genv ρ`
    have hℓ3 : E.ell ^ 3 ≤ 0 := by nlinarith [sq_nonneg E.ell, hℓ]
    have hs0 : Real.sqrt (ρ * E.ell ^ 3) = 0 :=
      Real.sqrt_eq_zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hρ hℓ3)
    rw [hs0]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]
    exact ⟨le_refl 0, genv_nonneg ρ⟩

/-! ## 2. The expansion of the diagonal row -/

/-- **The diagonal form of `Q₂^ex`.**  `F.Q2ex E` is the finite sum of the `•`-multiples of
the diagonal number operators `n_k = a_k†a_k` over the excited modes, so at a state `g` its
quadratic form is `Σ_k c_k ⟨g, n_k g⟩` with `c_k = E.rho(Ŵ₁ω(k)+Ŵ₁ω(0))` (linearity of `qw`
in the operator and of `bp` in its first argument). -/
private lemma qw_Q2ex_eq (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode)
    (g : F.H) :
    F.qw g (F.Q2ex E) = ∑ k ∈ Work.BoseB7.excited Mode,
      (E.rho * (E.W1omega k + E.W1omega0)) * F.qw g (F.nOp k) := by
  simp only [Work.BoseB7.FockData.qw, Work.BoseB7.FockData.Q2ex, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul]

/-! ## 3. The single-mode window bounds -/

omit [DecidableEq Mode] in
/-- `⟨g, n_k g⟩ = ‖a_k g‖² ≥ 0` for every mode `k`. -/
private lemma qw_nOp_nonneg (F : Work.BoseB7.FockData Mode) (k : Mode) (g : F.H) :
    0 ≤ F.qw g (F.nOp k) := by
  show 0 ≤ F.bp (F.aDag k (F.a k g)) g
  rw [F.aDag_adjoint k (F.a k g) g]
  exact F.bp_nonneg _

/-- **The single-mode window bound.**  On a window state every diagonal number form is at
most `Cn·𝓜‖g‖²`: the Bessel hypothesis converts the single mode into `n₊` and
`NWindow_bp_N_le` converts `n₊` into `𝓜`. -/
private lemma qw_nOp_le_window (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (Cn M : ℝ) (hCn0 : 0 ≤ Cn) (hM : 0 ≤ M)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f)
    (k : Mode) (g : F.H) (hg : T.NWindow M g) :
    F.qw g (F.nOp k) ≤ Cn * M * F.normSq g := by
  have hself : F.qw g (F.nOp k) = F.normSq (F.a k g) := by
    show F.bp (F.aDag k (F.a k g)) g = F.bp (F.a k g) (F.a k g)
    exact F.aDag_adjoint k (F.a k g) g
  rw [hself]
  exact normSq_a_le F T Cn M hCn0 hM hBessel k g hg

/-! ## 4. The `ρ`-growth of the coefficients -/

omit [DecidableEq Mode] in
/-- **The coefficient of a single mode grows at most like `genv ρ`.**  Since
`0 ≤ (KzEnvAt E ρ).rho ≤ genv ρ` (`KzEnvAt_rho_le_genv`), the weight
`ρ_z(Ŵ₁ω(k)+Ŵ₁ω(0))` is at least `-genv ρ·|Ŵ₁ω(k)+Ŵ₁ω(0)|`. -/
private lemma Q2ex_coeff_ge (E : Work.BoseB7.Q3Env Mode) {ρ : ℝ} (hρ : 0 ≤ ρ) (k : Mode) :
    -(genv ρ * |E.W1omega k + E.W1omega0|)
      ≤ (Work.BoseFixR.KzEnvAt E ρ).rho * (E.W1omega k + E.W1omega0) := by
  obtain ⟨hrho0, hrhoρ⟩ := KzEnvAt_rho_le_genv E hρ
  rcases le_or_gt 0 (E.W1omega k + E.W1omega0) with hw | hw
  · rw [abs_of_nonneg hw]
    have h1 : 0 ≤ (Work.BoseFixR.KzEnvAt E ρ).rho * (E.W1omega k + E.W1omega0) :=
      mul_nonneg hrho0 hw
    have h2 : 0 ≤ genv ρ * (E.W1omega k + E.W1omega0) :=
      mul_nonneg (genv_nonneg ρ) hw
    linarith
  · rw [abs_of_neg hw]
    have h2 : genv ρ * (E.W1omega k + E.W1omega0)
        ≤ (Work.BoseFixR.KzEnvAt E ρ).rho * (E.W1omega k + E.W1omega0) :=
      mul_le_mul_of_nonpos_right hrhoρ hw.le
    nlinarith [h2]

/-! ## 5. The row in the envelope -/

theorem Q2ex_window_ge_env {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env Mode)
    (Cn M : ℝ) (hM : 0 ≤ M) (hCn0 : 0 ≤ Cn)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 0 ≤ ρ → ∀ g : F.H, T.NWindow M g →
      -(C * Work.BoseBoxFock.genv ρ) * F.normSq g
        ≤ F.qw g (F.Q2ex (Work.BoseFixR.KzEnvAt E ρ)) := by
  refine ⟨(∑ k ∈ Work.BoseB7.excited Mode, |E.W1omega k + E.W1omega0|) * (Cn * M), ?_, ?_⟩
  · exact mul_nonneg (Finset.sum_nonneg (fun k _ => abs_nonneg _)) (mul_nonneg hCn0 hM)
  · intro ρ hρ g hg
    rw [qw_Q2ex_eq F (Work.BoseFixR.KzEnvAt E ρ) g]
    have hcoeff : ∀ k : Mode,
        -(genv ρ * |E.W1omega k + E.W1omega0|)
          ≤ (Work.BoseFixR.KzEnvAt E ρ).rho * (E.W1omega k + E.W1omega0) :=
      fun k => Q2ex_coeff_ge E hρ k
    have hQ0 : ∀ k : Mode, 0 ≤ F.qw g (F.nOp k) := fun k => qw_nOp_nonneg F k g
    have hQle : ∀ k : Mode, F.qw g (F.nOp k) ≤ Cn * M * F.normSq g :=
      fun k => qw_nOp_le_window F T Cn M hCn0 hM hBessel k g hg
    -- termwise: `c_k⟨g,n_kg⟩ ≥ -(genv ρ)·|Ŵ₁ω(k)+Ŵ₁ω(0)|·⟨g,n_kg⟩`
    have hterm : ∀ k ∈ Work.BoseB7.excited Mode,
        -(genv ρ) * (|E.W1omega k + E.W1omega0| * F.qw g (F.nOp k))
          ≤ (Work.BoseFixR.KzEnvAt E ρ).rho * (E.W1omega k + E.W1omega0)
              * F.qw g (F.nOp k) := by
      intro k _
      calc -(genv ρ) * (|E.W1omega k + E.W1omega0| * F.qw g (F.nOp k))
          = -(genv ρ * |E.W1omega k + E.W1omega0|) * F.qw g (F.nOp k) := by ring
        _ ≤ (Work.BoseFixR.KzEnvAt E ρ).rho * (E.W1omega k + E.W1omega0)
              * F.qw g (F.nOp k) := mul_le_mul_of_nonneg_right (hcoeff k) (hQ0 k)
    -- summing: the weighted mode sum is bounded by the constant times `‖g‖²`
    have hsum : ∑ k ∈ Work.BoseB7.excited Mode,
          |E.W1omega k + E.W1omega0| * F.qw g (F.nOp k)
        ≤ (∑ k ∈ Work.BoseB7.excited Mode, |E.W1omega k + E.W1omega0|)
          * (Cn * M * F.normSq g) := by
      calc ∑ k ∈ Work.BoseB7.excited Mode,
            |E.W1omega k + E.W1omega0| * F.qw g (F.nOp k)
          ≤ ∑ k ∈ Work.BoseB7.excited Mode,
              |E.W1omega k + E.W1omega0| * (Cn * M * F.normSq g) :=
            Finset.sum_le_sum
              (fun k _ => mul_le_mul_of_nonneg_left (hQle k) (abs_nonneg _))
        _ = (∑ k ∈ Work.BoseB7.excited Mode, |E.W1omega k + E.W1omega0|)
              * (Cn * M * F.normSq g) := by rw [Finset.sum_mul]
    have hA : -(genv ρ) * (∑ k ∈ Work.BoseB7.excited Mode,
          |E.W1omega k + E.W1omega0| * F.qw g (F.nOp k))
        ≤ ∑ k ∈ Work.BoseB7.excited Mode,
            (Work.BoseFixR.KzEnvAt E ρ).rho * (E.W1omega k + E.W1omega0)
              * F.qw g (F.nOp k) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hterm
    have hmain : -(genv ρ) * ((∑ k ∈ Work.BoseB7.excited Mode,
          |E.W1omega k + E.W1omega0|) * (Cn * M * F.normSq g))
        ≤ ∑ k ∈ Work.BoseB7.excited Mode,
            (Work.BoseFixR.KzEnvAt E ρ).rho * (E.W1omega k + E.W1omega0)
              * F.qw g (F.nOp k) :=
      le_trans (mul_le_mul_of_nonpos_left hsum (by linarith [genv_nonneg ρ] : -(genv ρ) ≤ 0))
        hA
    have hgoal : -((∑ k ∈ Work.BoseB7.excited Mode, |E.W1omega k + E.W1omega0|) * (Cn * M)
          * genv ρ) * F.normSq g
        = -(genv ρ) * ((∑ k ∈ Work.BoseB7.excited Mode,
            |E.W1omega k + E.W1omega0|) * (Cn * M * F.normSq g)) := by ring
    rw [hgoal]
    exact hmain

end Work.BoseBoxFock

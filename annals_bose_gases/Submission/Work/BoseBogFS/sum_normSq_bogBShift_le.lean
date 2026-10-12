import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.Gate
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.sum_normSq_bogBShift_le`

The summed shifted-squeezing bound: on a window state `f` (`T.NWindow E.bigM f`) the
total energy of the shifted squeezed modes `b_k + c_k` (`bogBShift F E ρ k`, FS
`eq:Defb_k`) is controlled by the window parameter and the number of mode labels,

  `Σ_k ‖(b_k + c_k) f‖² ≤ (600 𝓜 + 32 #Mode + 32) ‖f‖²`.

The proof is the elementary bookkeeping behind FS's `Σ_k ½(⟨b_k†b_k⟩ + ...)` estimates:

* `Σ_k ‖a_k f‖² = ⟨f, (Σ_k n_k) f⟩ ≤ Cn ⟨f, N f⟩ ≤ 16 𝓜 ‖f‖²` (Bessel hypothesis + the
  window, `NWindow_bp_N_le`): `sum_normSq_a_le`;
* `Σ_k ‖a_k† f‖² = Σ_k ‖a_k f‖² + (Σ_k [a_k,a_k†]) ‖f‖²` (`a_k a_k† = a_k†a_k + ccrK k k`,
  `FockData.ccr`): `sum_normSq_aDag_eq`, and `Σ_k [a_k,a_k†] ≤ #Mode` from the per-pair
  commutator bound `BogNumeric.hccr`: `sum_ccrK_diag_le_card`;
* the two Cauchy–Schwarz steps per mode (`‖u + c v‖² ≤ 2‖u‖² + (1+c²)‖v‖²` for
  `c² ≤ 1`): `normSq_bogBShift_le`, applied with `u = a_k f`, `v = a_{-k}† f`, `c = α_k`
  and then `u = b_k f`, `v = f`, `c = γ_k`, using `α_k² ≤ 1`, `γ_k² ≤ 1`.

No hypothesis on the sign of `Cn` is needed: `Cn ≤ 16` and `⟨f, N f⟩ ≥ 0` suffice.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBogFS

open Work.BoseB7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## 1. The elementary pieces -/

/-- `Σ_k ‖a_k f‖²` is the quadratic form of the total number `Σ_k a_k†a_k`
(linearity of the Fock form in its first argument + `a_k†` adjoint to `a_k`). -/
theorem bp_nOp_sum_eq (F : FockData Mode) (f : F.H) :
    F.bp ((∑ k : Mode, F.nOp k) f) f = ∑ k : Mode, F.normSq (F.a k f) := by
  rw [LinearMap.sum_apply, map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun k _ => by
    rw [FockData.nOp, LinearMap.comp_apply, F.aDag_adjoint, FockData.normSq]

/-- Cauchy–Schwarz in the Fock form: for `c² ≤ 1`, `‖u + c·v‖² ≤ 2‖u‖² + (1+c²)‖v‖²`.
This is the standard expansion `‖u+cv‖² = ‖u‖² + 2c⟨u,v⟩ + c²‖v‖²` together with
`2c⟨u,v⟩ ≤ 2|⟨u,v⟩| ≤ ‖u‖² + ‖v‖²` (`Work.BoseB7.SumABound.bp_abs_le`). -/
theorem normSq_add_smul_le (F : FockData Mode) (u v : F.H) {c : ℝ} (hc : c ^ 2 ≤ 1) :
    F.normSq (u + c • v) ≤ 2 * F.normSq u + (1 + c ^ 2) * F.normSq v := by
  have hcabs : |c| ≤ 1 := (sq_le_one_iff_abs_le_one c).mp hc
  have h := Work.BoseB7.SumABound.bp_abs_le F u v
  have hexp : F.bp (u + c • v) (u + c • v)
      = F.bp u u + 2 * c * F.bp u v + c ^ 2 * F.bp v v := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [F.bp_symm v u]
    ring
  have h1 : 2 * c * F.bp u v ≤ 2 * |c| * |F.bp u v| := by
    have hle : c * F.bp u v ≤ |c| * |F.bp u v| := by
      calc c * F.bp u v ≤ |c * F.bp u v| := le_abs_self _
        _ = |c| * |F.bp u v| := abs_mul _ _
    linarith
  have h2 : 2 * |c| * |F.bp u v| ≤ 2 * |F.bp u v| := by
    have h0 : 0 ≤ |F.bp u v| := abs_nonneg _
    nlinarith [hcabs, h0]
  have h3 : 2 * F.normSq u + (1 + c ^ 2) * F.normSq v
      = 2 * F.bp u u + (1 + c ^ 2) * F.bp v v := by
    rw [FockData.normSq, FockData.normSq]
  rw [FockData.normSq, hexp, h3]
  nlinarith [h, h1, h2, F.bp_nonneg u, F.bp_nonneg v]

/-- The per-mode expansion of the shifted squeezing operator: `b_k + c_k` is
`a_k + α_k a_{-k}† + γ_k·1`, so two Cauchy–Schwarz steps (`normSq_add_smul_le`) give

  `‖(b_k+c_k)f‖² ≤ 4‖a_k f‖² + 2(1+α_k²)‖a_{-k}† f‖² + (1+γ_k²)‖f‖²`. -/
theorem normSq_bogBShift_le (F : FockData Mode) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ)
    (k : Mode) (f : F.H) (hα : (bogAlpha E ρ k) ^ 2 ≤ 1)
    (hγ : (bogGamma E ρ k) ^ 2 ≤ 1) :
    F.normSq ((bogBShift F E ρ k) f)
      ≤ 4 * F.normSq (F.a k f) + 2 * (1 + (bogAlpha E ρ k) ^ 2) * F.normSq (F.aDag (-k) f)
        + (1 + (bogGamma E ρ k) ^ 2) * F.normSq f := by
  have hshift : (bogBShift F E ρ k) f
      = (F.bOp (bogAlpha E ρ) k) f + (bogGamma E ρ k) • f := by
    simp only [bogBShift, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
  have hbop : (F.bOp (bogAlpha E ρ) k) f
      = F.a k f + (bogAlpha E ρ k) • F.aDag (-k) f := by
    simp only [FockData.bOp, LinearMap.add_apply, LinearMap.smul_apply]
  have h1 := normSq_add_smul_le F ((F.bOp (bogAlpha E ρ) k) f) f hγ
  have h2 := normSq_add_smul_le F (F.a k f) (F.aDag (-k) f) hα
  have h2' : F.normSq ((F.bOp (bogAlpha E ρ) k) f)
      ≤ 2 * F.normSq (F.a k f) + (1 + (bogAlpha E ρ k) ^ 2) * F.normSq (F.aDag (-k) f) := by
    rw [hbop]
    exact h2
  calc F.normSq ((bogBShift F E ρ k) f)
      = F.normSq ((F.bOp (bogAlpha E ρ) k) f + (bogGamma E ρ k) • f) := by rw [hshift]
    _ ≤ 2 * F.normSq ((F.bOp (bogAlpha E ρ) k) f)
          + (1 + (bogGamma E ρ k) ^ 2) * F.normSq f := h1
    _ ≤ 2 * (2 * F.normSq (F.a k f)
            + (1 + (bogAlpha E ρ k) ^ 2) * F.normSq (F.aDag (-k) f))
          + (1 + (bogGamma E ρ k) ^ 2) * F.normSq f := by linarith [h2']
    _ = 4 * F.normSq (F.a k f) + 2 * (1 + (bogAlpha E ρ k) ^ 2) * F.normSq (F.aDag (-k) f)
          + (1 + (bogGamma E ρ k) ^ 2) * F.normSq f := by ring

/-- `Σ_k ‖a_k† f‖²` against `Σ_k ‖a_k f‖²`: the CCR `a_k a_k† = a_k†a_k + [a_k,a_k†]`
(`FockData.ccr`, the commutator a scalar) term by term. -/
theorem sum_normSq_aDag_eq (F : FockData Mode) (f : F.H) :
    ∑ k : Mode, F.normSq (F.aDag k f)
      = ∑ k : Mode, F.normSq (F.a k f) + (∑ k : Mode, F.ccrK k k) * F.normSq f := by
  have hpt : ∀ k : Mode, F.a k (F.aDag k f) = F.aDag k (F.a k f) + (F.ccrK k k) • f := by
    intro k
    have h := congrArg (fun (T : F.H →ₗ[ℝ] F.H) => T f) (F.ccr k k)
    simpa using h
  have hterm : ∀ k : Mode, F.normSq (F.aDag k f)
      = F.normSq (F.a k f) + F.ccrK k k * F.normSq f := by
    intro k
    rw [FockData.normSq, F.aDag_adjoint k f (F.aDag k f), F.bp_symm f (F.a k (F.aDag k f)),
      hpt k]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      FockData.normSq]
    rw [F.aDag_adjoint k (F.a k f) f]
  calc ∑ k : Mode, F.normSq (F.aDag k f)
      = ∑ k : Mode, (F.normSq (F.a k f) + F.ccrK k k * F.normSq f) :=
        Finset.sum_congr rfl fun k _ => hterm k
    _ = ∑ k : Mode, F.normSq (F.a k f) + ∑ k : Mode, F.ccrK k k * F.normSq f :=
        Finset.sum_add_distrib
    _ = ∑ k : Mode, F.normSq (F.a k f) + (∑ k : Mode, F.ccrK k k) * F.normSq f := by
        rw [Finset.sum_mul]

/-- The diagonal commutator total is at most the number of labels: summing the per-pair
bound `[a_k,a_k†] + [a_{-k},a_{-k}†] ≤ 2` over `k` and reindexing by `k ↦ -k` gives
`2 Σ_k [a_k,a_k†] ≤ 2 #Mode`. -/
theorem sum_ccrK_diag_le_card (F : FockData Mode)
    (hccr : ∀ k : Mode, F.ccrK k k + F.ccrK (-k) (-k) ≤ 2) :
    ∑ k : Mode, F.ccrK k k ≤ (Fintype.card Mode : ℝ) := by
  have h2 : ∑ k : Mode, (F.ccrK k k + F.ccrK (-k) (-k)) ≤ ∑ _k : Mode, (2 : ℝ) :=
    Finset.sum_le_sum fun k _ => hccr k
  have h3 : ∑ k : Mode, (F.ccrK k k + F.ccrK (-k) (-k)) = 2 * ∑ k : Mode, F.ccrK k k := by
    rw [Finset.sum_add_distrib, sum_neg_index (fun k => F.ccrK k k)]
    ring
  have h4 : (∑ _k : Mode, (2 : ℝ)) = 2 * (Fintype.card Mode : ℝ) := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
  linarith [h2, h3, h4]

/-- The `a`-energy sum on a window state, from the Bessel hypothesis and the window:
`Σ_k ‖a_k f‖² = ⟨f, (Σ_k n_k)f⟩ ≤ Cn⟨f, N f⟩ ≤ Cn 𝓜 ‖f‖² ≤ 16 𝓜 ‖f‖²`.
(No sign hypothesis on `Cn`: `Cn ≤ 16` is multiplied by the non-negative `⟨f,Nf⟩`.) -/
theorem sum_normSq_a_le (F : FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (Cn : ℝ) (hbigM : 0 ≤ E.bigM)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f)
    (hCn : Cn ≤ 16) (f : F.H) (hf : T.NWindow E.bigM f) :
    (∑ k : Mode, F.normSq (F.a k f)) ≤ 16 * E.bigM * F.normSq f := by
  have hwin : F.bp (T.N f) f ≤ E.bigM * F.normSq f :=
    Work.BoseB7A.NWindow_bp_N_le F T hbigM hf
  have hNnn : 0 ≤ F.bp (T.N f) f := T.N_nonneg f
  have h1 : F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f := hBessel f
  have h2 : Cn * F.bp (T.N f) f ≤ 16 * F.bp (T.N f) f :=
    mul_le_mul_of_nonneg_right hCn hNnn
  have h3 : 16 * F.bp (T.N f) f ≤ 16 * (E.bigM * F.normSq f) :=
    mul_le_mul_of_nonneg_left hwin (by norm_num)
  rw [← bp_nOp_sum_eq F f]
  linarith [h1, h2, h3]

/-! ## 2. The summed bound -/

theorem sum_normSq_bogBShift_le {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (ρ Cn : ℝ) (hnum : Work.BoseBogFS.BogNumeric F E ρ)
    (hbigM : 0 ≤ E.bigM)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f)
    (hCn : Cn ≤ 16) (hγ : ∀ k : Mode, (Work.BoseBogFS.bogGamma E ρ k) ^ 2 ≤ 1)
    (hα : ∀ k : Mode, (Work.BoseBogFS.bogAlpha E ρ k) ^ 2 ≤ 1)
    (f : F.H) (hf : T.NWindow E.bigM f) :
    (∑ k : Mode, F.normSq ((Work.BoseBogFS.bogBShift F E ρ k) f))
      ≤ (600 * E.bigM + 32 * (Fintype.card Mode : ℝ) + 32) * F.normSq f := by
  classical
  have hfnn : 0 ≤ F.normSq f := F.bp_nonneg f
  have hcard : 0 ≤ (Fintype.card Mode : ℝ) := Nat.cast_nonneg _
  -- the per-mode bound, summed
  have hsum_le : (∑ k : Mode, F.normSq ((bogBShift F E ρ k) f))
      ≤ ∑ k : Mode, (4 * F.normSq (F.a k f)
          + 2 * (1 + (bogAlpha E ρ k) ^ 2) * F.normSq (F.aDag (-k) f)
          + (1 + (bogGamma E ρ k) ^ 2) * F.normSq f) :=
    Finset.sum_le_sum fun k _ => normSq_bogBShift_le F E ρ k f (hα k) (hγ k)
  have hsplit : (∑ k : Mode, (4 * F.normSq (F.a k f)
          + 2 * (1 + (bogAlpha E ρ k) ^ 2) * F.normSq (F.aDag (-k) f)
          + (1 + (bogGamma E ρ k) ^ 2) * F.normSq f))
      = 4 * (∑ k : Mode, F.normSq (F.a k f))
        + 2 * (∑ k : Mode, (1 + (bogAlpha E ρ k) ^ 2) * F.normSq (F.aDag (-k) f))
        + (∑ k : Mode, (1 + (bogGamma E ρ k) ^ 2) * F.normSq f) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  -- the `a`-sum
  have hA : (∑ k : Mode, F.normSq (F.a k f)) ≤ 16 * E.bigM * F.normSq f :=
    sum_normSq_a_le F T E Cn hbigM hBessel hCn f hf
  -- the `a†`-sum
  have hQ : (∑ k : Mode, F.normSq (F.aDag k f))
      ≤ 16 * E.bigM * F.normSq f + (Fintype.card Mode : ℝ) * F.normSq f := by
    rw [sum_normSq_aDag_eq]
    have hccr : (∑ k : Mode, F.ccrK k k) ≤ (Fintype.card Mode : ℝ) :=
      sum_ccrK_diag_le_card F fun k => hnum.hccr k
    have hccr' : (∑ k : Mode, F.ccrK k k) * F.normSq f
        ≤ (Fintype.card Mode : ℝ) * F.normSq f :=
      mul_le_mul_of_nonneg_right hccr hfnn
    linarith [hA, hccr']
  -- the `α`-weighted `a†`-sum
  have hB : (∑ k : Mode, (1 + (bogAlpha E ρ k) ^ 2) * F.normSq (F.aDag (-k) f))
      ≤ 2 * (16 * E.bigM * F.normSq f + (Fintype.card Mode : ℝ) * F.normSq f) := by
    have h1 : ∀ k : Mode, (1 + (bogAlpha E ρ k) ^ 2) * F.normSq (F.aDag (-k) f)
        ≤ 2 * F.normSq (F.aDag (-k) f) := by
      intro k
      have h2 : (1 + (bogAlpha E ρ k) ^ 2) ≤ 2 := by linarith [hα k]
      exact mul_le_mul_of_nonneg_right h2 (F.bp_nonneg _)
    calc (∑ k : Mode, (1 + (bogAlpha E ρ k) ^ 2) * F.normSq (F.aDag (-k) f))
        ≤ ∑ k : Mode, 2 * F.normSq (F.aDag (-k) f) := Finset.sum_le_sum fun k _ => h1 k
      _ = 2 * (∑ k : Mode, F.normSq (F.aDag (-k) f)) := (Finset.mul_sum _ _ _).symm
      _ = 2 * (∑ k : Mode, F.normSq (F.aDag k f)) := by
            rw [sum_neg_index (fun k => F.normSq (F.aDag k f))]
      _ ≤ 2 * (16 * E.bigM * F.normSq f + (Fintype.card Mode : ℝ) * F.normSq f) := by
            linarith [hQ]
  -- the `γ`-weighted sum
  have hG : (∑ k : Mode, (1 + (bogGamma E ρ k) ^ 2) * F.normSq f)
      ≤ 2 * (Fintype.card Mode : ℝ) * F.normSq f := by
    have h1 : ∀ k : Mode, (1 + (bogGamma E ρ k) ^ 2) * F.normSq f ≤ 2 * F.normSq f := by
      intro k
      have h2 : (1 + (bogGamma E ρ k) ^ 2) ≤ 2 := by linarith [hγ k]
      exact mul_le_mul_of_nonneg_right h2 hfnn
    calc (∑ k : Mode, (1 + (bogGamma E ρ k) ^ 2) * F.normSq f)
        ≤ ∑ _k : Mode, 2 * F.normSq f := Finset.sum_le_sum fun k _ => h1 k
      _ = (Fintype.card Mode : ℝ) * (2 * F.normSq f) := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = 2 * (Fintype.card Mode : ℝ) * F.normSq f := by ring
  -- the arithmetic
  have hfin : 4 * (16 * E.bigM * F.normSq f)
        + 2 * (2 * (16 * E.bigM * F.normSq f + (Fintype.card Mode : ℝ) * F.normSq f))
        + 2 * (Fintype.card Mode : ℝ) * F.normSq f
      ≤ (600 * E.bigM + 32 * (Fintype.card Mode : ℝ) + 32) * F.normSq f := by
    have h1 : 0 ≤ E.bigM * F.normSq f := mul_nonneg hbigM hfnn
    have h2 : 0 ≤ (Fintype.card Mode : ℝ) * F.normSq f := mul_nonneg hcard hfnn
    nlinarith [h1, h2, hfnn]
  linarith [hsum_le, hsplit, hfin]

end Work.BoseBogFS

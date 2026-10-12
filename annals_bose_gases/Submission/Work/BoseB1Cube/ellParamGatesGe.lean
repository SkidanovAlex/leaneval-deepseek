import ChallengeDeps
import Submission.Work.BoseFixB1.corner_regime
import Submission.Work.BoseFixB1B.sectorCountDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.ellParamGatesGe` — the elementary box-size gates

At FS's parameter block (`paramsAt μ A = fsParams (μA³)`) the box side and the
small-box parameter are the monomials

    `ℓ = PBℓ v μ = sideAt μ (a v) = A·t^{-163/323}`,  `d = PBd v μ = t^{6/323}`,
    `t = μ (a v)³`, `A = a v`,

and the mean interparticle spacing is `μ^{-1/3} = A·t^{-1/3}`.  The scattering
length `A` cancels in every ratio, so the gates

    `ℓ ≥ 512 μ^{-1/3}`, `ℓ·d ≥ 8 μ^{-1/3}`, `d ≤ 1/2`

are the pure monomial statements

    `t^{166/969} ≤ 1/512`, `t^{148/969} ≤ 1/8`, `t^{6/323} ≤ 1/2`,

i.e. they hold as soon as the diluteness is below a fixed threshold.  This
module proves them at the explicit (generous) threshold `ε₀ = (1/2)^{1000}`; the
whole proof is `rpow` bookkeeping.

Everything is stated over a bare real `A = a v > 0` (`gates_aux`) and only at the
end transported to the corpus vocabulary `PBℓ`/`PBd`, so the file needs no
analytic input at all.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseB1Cube

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. `rpow` bookkeeping at the threshold `(1/2)^{1000}` -/

/-- `t^r ≤ (1/2)^(1000 r)` for `0 ≤ t ≤ (1/2)^{1000}` and `0 ≤ r`. -/
private lemma rpow_le_half {t r : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ (1 / 2 : ℝ) ^ 1000)
    (hr : 0 ≤ r) : t ^ r ≤ (1 / 2 : ℝ) ^ (1000 * r) := by
  calc t ^ r ≤ ((1 / 2 : ℝ) ^ 1000) ^ r := Real.rpow_le_rpow ht0 ht hr
    _ = (1 / 2 : ℝ) ^ ((1000 : ℝ) * r) := by
        rw [show ((1 / 2 : ℝ) ^ 1000) = (1 / 2 : ℝ) ^ ((1000 : ℕ) : ℝ) from
          (Real.rpow_natCast (1 / 2 : ℝ) 1000).symm]
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        norm_num

/-- **The lower gate**: `fsXp t (-c) ≥ 2^N` whenever `t ≤ (1/2)^{1000}` (with
`t > 0`) and `N ≤ 1000·c/323`.  Since `fsXp t (-c) = (t^{c/323})^{-1}`, this is
`t^{c/323} ≤ (1/2)^N`. -/
private lemma two_pow_le_fsXp_neg {t : ℝ} (ht0 : 0 < t) (ht : t ≤ (1 / 2 : ℝ) ^ 1000)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : (N : ℝ) ≤ 1000 * (c / 323)) :
    (2 : ℝ) ^ N ≤ Work.BoseBox.fsXp t (-c) := by
  have hval : Work.BoseBox.fsXp t (-c) = (t ^ (c / 323))⁻¹ := by
    rw [Work.BoseBox.fsXp, ← Real.rpow_neg ht0.le]
    congr 1
    ring
  rw [hval]
  have hp : 0 < t ^ (c / 323) := Real.rpow_pos_of_pos ht0 _
  have h2 : (((1 / 2 : ℝ) ^ N))⁻¹ ≤ (t ^ (c / 323))⁻¹ := by
    refine (inv_le_inv₀ (by positivity) hp).mpr ?_
    rw [← Real.rpow_natCast (1 / 2 : ℝ) N]
    exact le_trans (rpow_le_half ht0.le ht (by positivity))
      (Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hN)
  have hconv : (((1 / 2 : ℝ) ^ N))⁻¹ = (2 : ℝ) ^ N := by
    rw [← inv_pow]
    norm_num
  rwa [hconv] at h2

/-- **The upper gate**: `fsXp t c ≤ (1/2)^N` whenever `t ≤ (1/2)^{1000}` (with
`t > 0`), `c > 0` and `N ≤ 1000·c/323`. -/
private lemma fsXp_pos_le_half {t : ℝ} (ht0 : 0 < t) (ht : t ≤ (1 / 2 : ℝ) ^ 1000)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : (N : ℝ) ≤ 1000 * (c / 323)) :
    Work.BoseBox.fsXp t c ≤ (1 / 2 : ℝ) ^ N := by
  rw [show Work.BoseBox.fsXp t c = t ^ (c / 323) from rfl,
    ← Real.rpow_natCast (1 / 2 : ℝ) N]
  exact le_trans (rpow_le_half ht0.le ht (by positivity))
    (Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hN)

/-- The three monomial gates at diluteness `t`: `t^{-148/969} ≥ 8`,
`t^{-166/969} ≥ 512` and `t^{6/323} ≤ 1/2`. -/
private lemma gates_of_small {t : ℝ} (ht0 : 0 < t) (ht : t ≤ (1 / 2 : ℝ) ^ 1000) :
    (8 : ℝ) ≤ Work.BoseBox.fsXp t (-(148 / 3)) ∧
    (512 : ℝ) ≤ Work.BoseBox.fsXp t (-(166 / 3)) ∧
    Work.BoseBox.fsXp t 6 ≤ 1 / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · have h := two_pow_le_fsXp_neg ht0 ht (c := 148 / 3) (by norm_num) (N := 3) (by norm_num)
    have h28 : (2 : ℝ) ^ 3 = 8 := by norm_num
    simpa only [h28] using h
  · have h := two_pow_le_fsXp_neg ht0 ht (c := 166 / 3) (by norm_num) (N := 9) (by norm_num)
    have h29 : (2 : ℝ) ^ 9 = 512 := by norm_num
    simpa only [h29] using h
  · have h : Work.BoseBox.fsXp t 6 ≤ (1 / 2 : ℝ) ^ (1 : ℕ) :=
      fsXp_pos_le_half ht0 ht (c := 6) (by norm_num) (N := 1) (by norm_num)
    simpa using h

/-! ## 2. The gates at the parameters `paramsAt μ A` -/

/-- The five gates, in the shape of the target, over a bare `A = a v > 0`. -/
private lemma gates_aux {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ)
    (hsmall : μ * A ^ 3 ≤ (1 / 2 : ℝ) ^ 1000) :
    (8 * μ ^ (-(1 / 3 : ℝ)) ≤ Work.BoseBox.sideAt μ A * (Work.BoseBox.paramsAt μ A).d) ∧
    (512 * μ ^ (-(1 / 3 : ℝ)) ≤ Work.BoseBox.sideAt μ A) ∧
    ((Work.BoseBox.paramsAt μ A).d ≤ 1 / 2) ∧
    (0 < μ ^ (-(1 / 3 : ℝ))) ∧
    (μ ^ (-(1 / 3 : ℝ)) ≤ Work.BoseBox.sideAt μ A * (Work.BoseBox.paramsAt μ A).d) := by
  have ht : 0 < μ * A ^ 3 := by positivity
  obtain ⟨h8, h512, hhalf⟩ := gates_of_small ht hsmall
  have hℓ : Work.BoseBox.sideAt μ A = A * Work.BoseBox.fsXp (μ * A ^ 3) (-163) :=
    Work.BoseFixB1.sideAt_eq_fsXp hA hμ
  have hd : (Work.BoseBox.paramsAt μ A).d = Work.BoseBox.fsXp (μ * A ^ 3) 6 :=
    Work.BoseFixB1.d_eq_fsXp μ A
  have hm : μ ^ (-(1 / 3 : ℝ)) = A * Work.BoseBox.fsXp (μ * A ^ 3) (-(323 / 3)) :=
    Work.BoseFixB1.mu_inv_third_eq hA hμ
  have hp : 0 < Work.BoseBox.fsXp (μ * A ^ 3) (-(323 / 3)) :=
    Work.BoseBox.fsXp_pos ht
  have hAp : 0 < A * Work.BoseBox.fsXp (μ * A ^ 3) (-(323 / 3)) := mul_pos hA hp
  -- the two `fsXp` product identities
  have e1 : Work.BoseBox.fsXp (μ * A ^ 3) (-163) * Work.BoseBox.fsXp (μ * A ^ 3) 6
      = Work.BoseBox.fsXp (μ * A ^ 3) (-(148 / 3))
        * Work.BoseBox.fsXp (μ * A ^ 3) (-(323 / 3)) := by
    rw [Work.BoseBox.fsXp_mul ht, Work.BoseBox.fsXp_mul ht]
    congr 1
    norm_num
  have e2 : Work.BoseBox.fsXp (μ * A ^ 3) (-163)
      = Work.BoseBox.fsXp (μ * A ^ 3) (-(166 / 3))
        * Work.BoseBox.fsXp (μ * A ^ 3) (-(323 / 3)) := by
    rw [Work.BoseBox.fsXp_mul ht]
    congr 1
    norm_num
  have h1 : 8 * μ ^ (-(1 / 3 : ℝ)) ≤ Work.BoseBox.sideAt μ A * (Work.BoseBox.paramsAt μ A).d := by
    rw [hm, hℓ, hd]
    have hR : (A * Work.BoseBox.fsXp (μ * A ^ 3) (-163)) * Work.BoseBox.fsXp (μ * A ^ 3) 6
        = Work.BoseBox.fsXp (μ * A ^ 3) (-(148 / 3))
          * (A * Work.BoseBox.fsXp (μ * A ^ 3) (-(323 / 3))) := by
      rw [show (A * Work.BoseBox.fsXp (μ * A ^ 3) (-163)) * Work.BoseBox.fsXp (μ * A ^ 3) 6
            = A * (Work.BoseBox.fsXp (μ * A ^ 3) (-163)
              * Work.BoseBox.fsXp (μ * A ^ 3) 6) from by ring,
        e1]
      ring
    rw [hR]
    exact mul_le_mul_of_nonneg_right h8 hAp.le
  have h2 : 512 * μ ^ (-(1 / 3 : ℝ)) ≤ Work.BoseBox.sideAt μ A := by
    rw [hm, hℓ]
    have hR : A * Work.BoseBox.fsXp (μ * A ^ 3) (-163)
        = Work.BoseBox.fsXp (μ * A ^ 3) (-(166 / 3))
          * (A * Work.BoseBox.fsXp (μ * A ^ 3) (-(323 / 3))) := by
      rw [e2]
      ring
    rw [hR]
    exact mul_le_mul_of_nonneg_right h512 hAp.le
  have h3 : (Work.BoseBox.paramsAt μ A).d ≤ 1 / 2 := by rw [hd]; exact hhalf
  have h4 : 0 < μ ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hμ _
  refine ⟨h1, h2, h3, h4, ?_⟩
  linarith

/-! ## 3. The target -/

theorem ellParamGatesGe {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      (8 * μ ^ (-(1 / 3 : ℝ)) ≤ Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ) ∧
      (512 * μ ^ (-(1 / 3 : ℝ)) ≤ Work.BoseFixB1B.PBℓ v μ) ∧
      (Work.BoseFixB1B.PBd v μ ≤ 1 / 2) ∧
      (0 < μ ^ (-(1 / 3 : ℝ))) ∧
      (μ ^ (-(1 / 3 : ℝ)) ≤ Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ) := by
  refine ⟨(1 / 2 : ℝ) ^ 1000, by positivity, pow_le_one₀ (by norm_num) (by norm_num), ?_⟩
  intro μ hAdm
  obtain ⟨hμ, hμa3, _⟩ := hAdm
  have hg := gates_aux hav hμ hμa3
  simpa only [Work.BoseFixB1B.PBℓ, Work.BoseFixB1B.PBd] using hg

end Work.BoseB1Cube

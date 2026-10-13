/-
# `H6Rows/ScalarRows` — the scalar bounds `|μ̄|`, `|muDyn|` of the level-six modulation

`dynRHS = -μ̄·AK + N₀ + N + N_*`, with `μ̄ = L₁₂(N₀)(0) + L₁₂(N)(0)` *defined* from the pieces
(`Construction.mubar`), and the modulation constant

`muDyn = mufunS α (N₀) (N) f = (1/(2α))·(μ̄ + L₁₂(3D_θf/(1+z))(0))`

(`Construction.mufunS`, `Construction.two_mul_mufunS`).  So the two scalars are priced by the
three zero-mode bounds: `H6Pair6Aux.h6pair_N0_zero` (proved), the transport bound
`H6Pair6Aux.transport_zero_le'` (proved) and the `N`-zero-mode bound (the delegated
`H6Rows.NZzero6`).  The lemma below consumes the first two and the third as a hypothesis.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.h6pair_mod
import Submission.Work.FTS.IPGen.OpenBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn Fam slice dynRHS)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Elementary helpers -/

/-- `a·d ≤ b·c·d` for `a ≤ b`, `b ≥ 0`, `c ≥ 1`, `d ≥ 0`. -/
theorem mul_le_mul_of_le_of_one_le {a b c d : ℝ} (hab : a ≤ b) (hb : 0 ≤ b)
    (hc : 1 ≤ c) (hd : 0 ≤ d) : a * d ≤ b * c * d := by
  calc a * d ≤ b * d := mul_le_mul_of_nonneg_right hab hd
    _ ≤ b * (c * d) := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hd hc) hb
    _ = b * c * d := by ring

/-- `a·c·d ≤ b·c·d` for `a ≤ b` and nonnegative `c`, `d`. -/
theorem mul_le_mul_left₃ {a b c d : ℝ} (hab : a ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    a * c * d ≤ b * c * d :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hab hc) hd

/-- **Four-factor product monotonicity**: `a·p·s ≤ b·t·q·s` when `a ≤ b`, `p ≤ q`, `1 ≤ t` and
everything is nonnegative. -/
theorem mul_four_le {a b p q s t : ℝ} (hab : a ≤ b) (hpq : p ≤ q) (ht : 1 ≤ t)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 ≤ p) (hq : 0 ≤ q) (hs : 0 ≤ s) :
    a * p * s ≤ b * t * q * s := by
  have h1 : a * p * s ≤ b * p * s :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hab hp) hs
  have h2 : b * p * s ≤ b * q * s :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpq hb) hs
  have h3 : b * q * s ≤ b * (t * q) * s := by
    have h : q ≤ t * q := le_mul_of_one_le_left hq ht
    calc b * q * s = b * (q * s) := by ring
      _ ≤ b * ((t * q) * s) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h hs) hb
      _ = b * (t * q) * s := by ring
  have h4 : b * (t * q) * s = b * t * q * s := by ring
  linarith [h1, h2, h3, le_of_eq h4]

/-- `α^{-1}·α^{-9} = α^{-10}`. -/
theorem rpow_neg_one_mul_nine {α : ℝ} (hα : 0 < α) :
    α ^ (-(1 : ℝ)) * α ^ (-(9 : ℝ)) = α ^ (-(10 : ℝ)) := by
  have h := Real.rpow_add hα (-(1 : ℝ)) (-(9 : ℝ))
  rw [show -(1 : ℝ) + -(9 : ℝ) = -(10 : ℝ) by norm_num] at h
  exact h.symm

/-- `α^{-10}·α = α^{-9}`. -/
theorem rpow_neg_ten_mul {α : ℝ} (hα : 0 < α) :
    α ^ (-(10 : ℝ)) * α = α ^ (-(9 : ℝ)) := by
  have h := Real.rpow_add hα (-(9 : ℝ)) (-(1 : ℝ))
  rw [show -(9 : ℝ) + -(1 : ℝ) = -(10 : ℝ) by norm_num] at h
  rw [Real.rpow_neg_one] at h
  have hαne : α ≠ 0 := ne_of_gt hα
  calc α ^ (-(10 : ℝ)) * α = (α ^ (-(9 : ℝ)) * α⁻¹) * α := by rw [h]
    _ = α ^ (-(9 : ℝ)) := by field_simp

/-- `α^{-9} ≤ α^{-10}` for `0 < α ≤ 1`. -/
theorem rpow_neg_nine_le {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    α ^ (-(9 : ℝ)) ≤ α ^ (-(10 : ℝ)) := by
  have hQ0 : 0 ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα0.le _
  rw [← rpow_neg_ten_mul hα0]
  calc α ^ (-(10 : ℝ)) * α ≤ α ^ (-(10 : ℝ)) * 1 := mul_le_mul_of_nonneg_left hα1 hQ0
    _ = α ^ (-(10 : ℝ)) := by ring

/-- `1 ≤ α^{-q}` for `0 < α ≤ 1` and `q ≥ 0`. -/
theorem one_le_rpow_neg_of {α q : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hq : 0 ≤ q) :
    (1 : ℝ) ≤ α ^ (-q) := by
  have h1 : α ^ q ≤ 1 := Real.rpow_le_one hα0.le hα1 hq
  have h2 : 0 < α ^ q := Real.rpow_pos_of_pos hα0 q
  rw [Real.rpow_neg hα0.le q]
  exact (one_le_inv₀ h2).mpr h1

/-- `M ≤ (1+M)⁴` for `M ≥ 0`. -/
theorem self_le_one_add_pow_four {M : ℝ} (hM0 : 0 ≤ M) : M ≤ (1 + M) ^ 4 := by
  nlinarith [hM0, sq_nonneg M, sq_nonneg (M + 1)]

/-- `(1/(2α))·(C·α^{-9}) = (C/2)·α^{-10}`. -/
theorem half_inv_mul_rpow {α C : ℝ} (hα : 0 < α) :
    (1 / (2 * α)) * (C * α ^ (-(9 : ℝ))) = (C / 2) * α ^ (-(10 : ℝ)) := by
  rw [show (1 : ℝ) / (2 * α) = (1 / 2) * α ^ (-(1 : ℝ)) by
      rw [Real.rpow_neg_one]; ring,
    show (1 / 2 : ℝ) * α ^ (-(1 : ℝ)) * (C * α ^ (-(9 : ℝ)))
        = (C / 2) * (α ^ (-(1 : ℝ)) * α ^ (-(9 : ℝ))) by ring,
    rpow_neg_one_mul_nine hα]

/-! ## The `α`-arithmetic of the modulation bound -/

/-- **The `α`-arithmetic of the modulation bound.**  With `S = (1+M)⁴`, `T = (1+|Ce|+|Cs|)⁴`,
`K := 3(K₀+K_Z+C_T+1)`,

`(1/(2α))(K₀·α^{-9}S + K_Z·T·α^{-9}S + C_T·M) ≤ K·T·α^{-10}·S`.

The three summands are absorbed by `α^{-9} ≥ 1`, `T ≥ 1`, `M ≤ S`; the only `rpow` input is
`α^{-1}·α^{-9} = α^{-10}`. -/
theorem scalar_arith {α K0 KZ CT M Ce Cs : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hM0 : 0 ≤ M) (hK0 : 0 ≤ K0) (hKZ : 0 ≤ KZ) (hCT : 0 ≤ CT) :
    (1 / (2 * α)) * (K0 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4
        + KZ * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 + CT * M)
      ≤ (3 * (K0 + KZ + CT + 1)) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
          * (1 + M) ^ 4 := by
  have hP0 : 0 ≤ α ^ (-(9 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hP1 : 1 ≤ α ^ (-(9 : ℝ)) := one_le_rpow_neg_of hα0 hα1 (by norm_num)
  have hS0 : 0 ≤ (1 + M) ^ 4 := by positivity
  have hMle : M ≤ (1 + M) ^ 4 := self_le_one_add_pow_four hM0
  have hT1 : 1 ≤ (1 + |Ce| + |Cs|) ^ 4 :=
    one_le_pow₀ (by have h1 := abs_nonneg Ce; have h2 := abs_nonneg Cs; linarith)
  have hT0 : 0 ≤ (1 + |Ce| + |Cs|) ^ 4 := le_trans zero_le_one hT1
  have hPS0 : 0 ≤ α ^ (-(9 : ℝ)) * (1 + M) ^ 4 := mul_nonneg hP0 hS0
  have hK'0 : 0 ≤ K0 + KZ + CT + 1 := by linarith
  have hTQ0 : 0 ≤ (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 := by positivity
  -- the three summands, each bounded by the common `K'·T·(P·S)`
  have h1 : K0 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4
      ≤ (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4) := by
    calc K0 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 = K0 * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4) := by ring
      _ ≤ (K0 + KZ + CT + 1) * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4) :=
          mul_le_mul_of_nonneg_right (by linarith) hPS0
      _ ≤ (K0 + KZ + CT + 1) * ((1 + |Ce| + |Cs|) ^ 4 * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4)) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hPS0 hT1) hK'0
      _ = (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4) := by ring
  have h2 : KZ * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4
      ≤ (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4) := by
    have hkt : 0 ≤ (1 + |Ce| + |Cs|) ^ 4 * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4) := by positivity
    calc KZ * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4
        = KZ * ((1 + |Ce| + |Cs|) ^ 4 * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4)) := by ring
      _ ≤ (K0 + KZ + CT + 1) * ((1 + |Ce| + |Cs|) ^ 4 * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4)) :=
          mul_le_mul_of_nonneg_right (by linarith) hkt
      _ = (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4) := by ring
  have h3 : CT * M
      ≤ (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4) := by
    have h1 : CT * M ≤ CT * (1 + M) ^ 4 := mul_le_mul_of_nonneg_left hMle hCT
    have h2 : CT * (1 + M) ^ 4
        ≤ (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 := by
      calc CT * (1 + M) ^ 4 ≤ (K0 + KZ + CT + 1) * (1 + M) ^ 4 :=
            mul_le_mul_of_nonneg_right (by linarith) hS0
        _ ≤ (K0 + KZ + CT + 1) * ((1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4) :=
            mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hS0 hT1) hK'0
        _ = (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 := by ring
    have h3 : (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
        ≤ (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4) := by
      calc (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
          = (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (1 * (1 + M) ^ 4) := by ring
        _ ≤ (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4
              * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hP1 hS0) (by positivity)
    linarith [h1, h2, h3]
  have hZ : K0 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4
        + KZ * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 + CT * M
      ≤ 3 * ((K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4
          * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4)) := by
    have e : 3 * ((K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4
          * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4))
        = (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4)
          + (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4)
          + (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4) := by
      ring
    rw [e]
    linarith [h1, h2, h3]
  -- the factor `1/(2α)`
  have hfac : 0 ≤ (1 : ℝ) / (2 * α) := by positivity
  have hstep : (1 / (2 * α)) * (K0 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4
        + KZ * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 + CT * M)
      ≤ (1 / (2 * α)) * (3 * ((K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4
          * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4))) :=
    mul_le_mul_of_nonneg_left hZ hfac
  have hhalf : (1 / (2 * α)) * (3 * ((K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4
        * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4)))
      = (3 * (K0 + KZ + CT + 1) / 2) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
          * (1 + M) ^ 4 := by
    have h := half_inv_mul_rpow (α := α) (C := (1 : ℝ)) hα0
    rw [one_mul] at h
    calc (1 / (2 * α)) * (3 * ((K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4
          * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4)))
        = (3 * ((K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4))
            * ((1 / (2 * α)) * α ^ (-(9 : ℝ))) := by ring
      _ = (3 * ((K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4))
            * ((1 / 2) * α ^ (-(10 : ℝ))) := by rw [h]
      _ = (3 * (K0 + KZ + CT + 1) / 2) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
            * (1 + M) ^ 4 := by ring
  have hfin : (3 * (K0 + KZ + CT + 1) / 2) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
        * (1 + M) ^ 4
      ≤ (3 * (K0 + KZ + CT + 1)) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
          * (1 + M) ^ 4 := by
    have hk : 3 * (K0 + KZ + CT + 1) / 2 ≤ 3 * (K0 + KZ + CT + 1) := by linarith
    calc (3 * (K0 + KZ + CT + 1) / 2) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
          * (1 + M) ^ 4
        = (3 * (K0 + KZ + CT + 1) / 2) * ((1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
            * (1 + M) ^ 4) := by ring
      _ ≤ (3 * (K0 + KZ + CT + 1)) * ((1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
            * (1 + M) ^ 4) := mul_le_mul_of_nonneg_right hk hTQ0
      _ = (3 * (K0 + KZ + CT + 1)) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
            * (1 + M) ^ 4 := by ring
  linarith [hstep, le_of_eq hhalf, hfin]

/-- **The two scalars from the zero-mode bounds.**  With `K := 3(K₀+K_Z+C_T+1)`, the `N₀`- and
transport zero modes are the *proved* lemmas, the `N`-zero mode is the hypothesis `hZ` (the
delegated `H6Rows.NZzero6`). -/
theorem muBdd_of_zeroModes {Ce : ℝ}
    (hZ : ∃ K α₂ : ℝ, 0 < K ∧ 0 < α₂ ∧ α₂ ≤ 1 ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ (f Ψ Φs : Fn) (M Cs : ℝ) (E : Fn → Fn),
        H6Adm α f → Work.Spaces.HkMem α 7 f → Work.FTS.Nonlin.Xn α f ≤ M →
        Ell6Ctx α Ce Cs E Φs f Ψ →
        |Work.Construction.L12 (Work.Construction.N α
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) Ψ) 0|
          ≤ K * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4) :
    ∃ K α₂ : ℝ, 0 < K ∧ 0 < α₂ ∧ α₂ ≤ 1 ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ (g Φ : Fam) (τ M Cs : ℝ) (E : Fn → Fn) (Φs : Fn), 0 ≤ τ →
        L6Ctx (IP6 1 1 1 1 1 1 1 1 1 1) α M Ce Cs E Φs g Φ τ →
        |Work.FTS.Galerkin.muDyn α Φ g τ|
            ≤ K * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 ∧
        |Work.Construction.mubar
            (Work.Construction.N0 α (Work.Construction.Ftau α g τ)
              (Work.FTS.Galerkin.slice g τ))
            (Work.Construction.N α (Work.Construction.Ftau α g τ)
              (Work.FTS.Galerkin.slice Φ τ))|
          ≤ K * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 := by
  obtain ⟨KZ, αZ, hKZ, hαZ, hαZle, hZb⟩ := hZ
  obtain ⟨K0, α0, hK0, hα0, hQb⟩ := H6Pair6Aux.h6pair_N0_zero
  obtain ⟨CT, hCT, hCTb⟩ := H6Pair6Aux.transport_zero_le'
  refine ⟨3 * (K0 + KZ + CT + 1), min (min α0 αZ) 1, by linarith,
    lt_min (lt_min hα0 hαZ) one_pos, min_le_right _ _, ?_⟩
  intro α hα g Φ τ M Cs E Φs hτ hctx
  have hαpos : 0 < α := hα.1
  have hαmin : α ≤ min α0 αZ := le_trans hα.2 (min_le_left _ _)
  have hαone : α ≤ 1 := le_trans hα.2 (min_le_right _ _)
  have hα0' : α ∈ Set.Ioc 0 α0 := ⟨hαpos, le_trans hαmin (min_le_left _ _)⟩
  have hαZ' : α ∈ Set.Ioc 0 αZ := ⟨hαpos, le_trans hαmin (min_le_right _ _)⟩
  set f : Fn := Work.FTS.Galerkin.slice g τ with hf
  set Ψ : Fn := Work.FTS.Galerkin.slice Φ τ with hΨ
  set F : Fn := Work.Construction.Ftau α g τ with hF
  have hreg : H6Adm α f := hctx.hreg
  have h7 : Work.Spaces.HkMem α 7 f := hctx.h7
  have hbdM : Work.FTS.Nonlin.Xn α f ≤ M := hctx.hbdd
  have hso : Work.FTS.EllipticEst.SmoothOpen f := hreg.reg.1
  have hmem6 : Work.Spaces.HkMem α 6 f := hreg.reg.2
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.IPGen.HkMem_mono_le hso 4 (by norm_num) hmem6
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hbdM
  have h0 : |Work.Construction.L12 (Work.Construction.N0 α F f) 0|
      ≤ K0 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 := hQb α hα0' f M hreg h7 hbdM
  have hZb' : |Work.Construction.L12 (Work.Construction.N α F Ψ) 0|
      ≤ KZ * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 :=
    hZb α hαZ' f Ψ Φs M Cs E hreg h7 hbdM hctx.hell
  have hTb : |Work.Construction.L12 (Work.Coercivity.Transport f) 0| ≤ CT * M := by
    have h := hCTb α f hαpos hαone hmem4
    calc |Work.Construction.L12 (Work.Coercivity.Transport f) 0|
        ≤ CT * Work.FTS.Nonlin.Xn α f := h
      _ ≤ CT * M := mul_le_mul_of_nonneg_left hbdM hCT.le
  have hmudyn : Work.FTS.Galerkin.muDyn α Φ g τ
      = (1 / (2 * α)) * (Work.Construction.mubar (Work.Construction.N0 α F f)
          (Work.Construction.N α F Ψ)
          + Work.Construction.L12 (Work.Coercivity.Transport f) 0) := by
    have htwo := Work.Construction.two_mul_mufunS α (Work.Construction.N0 α F f)
      (Work.Construction.N α F Ψ) f (ne_of_gt hαpos)
    rw [Work.FTS.Galerkin.muDyn_eq, ← hF, ← hf, ← hΨ, ← htwo]
    have hne : (2 : ℝ) * α ≠ 0 := by positivity
    field_simp
  have hmubar_eq : Work.Construction.mubar (Work.Construction.N0 α F f)
      (Work.Construction.N α F Ψ)
      = Work.Construction.L12 (Work.Construction.N0 α F f) 0
        + Work.Construction.L12 (Work.Construction.N α F Ψ) 0 := rfl
  have hQ0 : 0 ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hαpos.le _
  have hP0 : 0 ≤ α ^ (-(9 : ℝ)) := Real.rpow_nonneg hαpos.le _
  have hS0 : 0 ≤ (1 + M) ^ 4 := by positivity
  have hT0 : 0 ≤ (1 + |Ce| + |Cs|) ^ 4 := by positivity
  have hPQ : α ^ (-(9 : ℝ)) ≤ α ^ (-(10 : ℝ)) := rpow_neg_nine_le hαpos hαone
  have hT1' : 1 ≤ (1 + |Ce| + |Cs|) ^ 4 :=
    one_le_pow₀ (by have h1 := abs_nonneg Ce; have h2 := abs_nonneg Cs; linarith)
  refine ⟨?_, ?_⟩
  · rw [hmudyn, hmubar_eq, abs_mul]
    have hc0 : 0 ≤ (1 / (2 * α)) := by positivity
    rw [abs_of_nonneg hc0]
    have htri : |Work.Construction.L12 (Work.Construction.N0 α F f) 0
          + Work.Construction.L12 (Work.Construction.N α F Ψ) 0
          + Work.Construction.L12 (Work.Coercivity.Transport f) 0|
        ≤ K0 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4
          + KZ * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 + CT * M := by
      linarith [abs_add_le (Work.Construction.L12 (Work.Construction.N0 α F f) 0
          + Work.Construction.L12 (Work.Construction.N α F Ψ) 0)
          (Work.Construction.L12 (Work.Coercivity.Transport f) 0),
        abs_add_le (Work.Construction.L12 (Work.Construction.N0 α F f) 0)
          (Work.Construction.L12 (Work.Construction.N α F Ψ) 0), h0, hZb', hTb]
    exact le_trans (mul_le_mul_of_nonneg_left htri hc0)
      (scalar_arith hαpos hαone hM0 hK0.le hKZ.le hCT.le)
  · rw [hmubar_eq]
    have htri : |Work.Construction.L12 (Work.Construction.N0 α F f) 0
          + Work.Construction.L12 (Work.Construction.N α F Ψ) 0|
        ≤ K0 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4
          + KZ * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 := by
      linarith [abs_add_le (Work.Construction.L12 (Work.Construction.N0 α F f) 0)
        (Work.Construction.L12 (Work.Construction.N α F Ψ) 0), h0, hZb']
    have hK0le : K0 ≤ K0 + KZ + CT + 1 := by linarith
    have hKZle : KZ ≤ K0 + KZ + CT + 1 := by linarith
    have hK'0 : 0 ≤ K0 + KZ + CT + 1 := by linarith
    have hTX0 : 0 ≤ (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 := mul_nonneg hK'0 hT0
    have hR0 : 0 ≤ (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
        * (1 + M) ^ 4 := mul_nonneg (mul_nonneg hTX0 hQ0) hS0
    have h1 : K0 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4
        ≤ (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
            * (1 + M) ^ 4 :=
      mul_four_le hK0le hPQ hT1' hK0.le hK'0 hP0 hQ0 hS0
    have h2 : KZ * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4
        ≤ (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
            * (1 + M) ^ 4 := by
      have h := mul_four_le (a := KZ * (1 + |Ce| + |Cs|) ^ 4)
        (b := (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4)
        (p := α ^ (-(9 : ℝ))) (q := α ^ (-(10 : ℝ))) (s := (1 + M) ^ 4) (t := 1)
        (by exact mul_le_mul_of_nonneg_right hKZle hT0) hPQ le_rfl
        (by positivity) (mul_nonneg hK'0 hT0) hP0 hQ0 hS0
      simpa only [mul_one, one_mul] using h
    have hgoal : |Work.Construction.L12 (Work.Construction.N0 α F f) 0
          + Work.Construction.L12 (Work.Construction.N α F Ψ) 0|
        ≤ (3 * (K0 + KZ + CT + 1)) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
            * (1 + M) ^ 4 := by
      calc |Work.Construction.L12 (Work.Construction.N0 α F f) 0
            + Work.Construction.L12 (Work.Construction.N α F Ψ) 0|
          ≤ K0 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4
              + KZ * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 := htri
        _ ≤ (K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4
              + ((K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
                  * (1 + M) ^ 4) := add_le_add h1 h2
        _ ≤ 3 * ((K0 + KZ + CT + 1) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
              * (1 + M) ^ 4) := by linarith [hR0]
        _ = (3 * (K0 + KZ + CT + 1)) * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ))
              * (1 + M) ^ 4 := by ring
    exact hgoal

end Work.FTS.StrongPersist

/-
# `H6Pair6Aux/RowMuAux/fk_open` — the six `FK`-rows of `N` in the open class

The rows `N₄^{gg}, N₅^{gg}, N₄^{gs}, N₅^{gs}, N₄^{sg}, N₅^{sg}` are the pieces of `N` whose
coefficient is the angular moment `FK g = ∫_θ g(·,θ)K(θ)dθ` (resp. the explicit profile
`FK(F_*) = α·2r/(1+r)²`).  Their closed-quadrant counterparts are
`Work.FTS.NonlinRows.Rl1.ggRows45`, `gsRows45`, `sgRows45` and
`Work.FTS.NonlinRows.Rl1.gssgFKBounds` (all phrased in the envelope
`Env α g = α² + √α·|g|_{ℋ⁴} + α^{-3/2}|g|²_{ℋ⁴}`).

Here the same six rows are proved for the *open* class `SmoothOpen f` + `HkMem α 4 f` — the
class actually available on this route (`H6Adm α f` gives `SmoothOpen`, while the
closed-quadrant class `SmoothQuad` is unavailable) — and in the envelope

  `α^{-2} · (1 + |f|_{ℋ⁴})²`

that the level-six assembly consumes.  The bridge is the elementary comparison

  `Env α f ≤ 3 · α^{-2} · (1 + |f|_{ℋ⁴})²`   (`Env_le_envelope`),

valid for `0 < α ≤ 1`.

The three row groups are proved separately (`gg_fk_open_rows` here, `gs_open_rows`,
`sg_fk_open_rows`); the slot data (`Φ₀ f`, `Φ₁ f`, `Φ₂ f`) is read off from
`SmoothOpen`+`HkMem` alone by `RowMuAux/SlotDataOpen`, which is what replaces the
closed-quadrant `slot0`/`slot1`/`slot2` of the `Rl1` development.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.SlotDataOpen
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.gs_open_rows
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.sg_fk_open_rows
import Submission.Work.FTS.NonlinRows.Rl1.gssgFKBounds
import Submission.Work.FTS.NonlinRows.Rl1.tools
import Submission.Work.FTS.NonlinRows.Rl1.Rows45
import Submission.Work.FTS.NonlinRows.Rl1.FaCoefSlot

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)

/-! ## The envelope comparison `Env ≤ 3·α^{-2}(1+X)²` -/

/-- **The envelope comparison.**  For `0 < α ≤ 1` and any datum `f`,
`Env α f = α² + √α·X + α^{-3/2}X² ≤ 3·α^{-2}·(1+X)²`, `X = |f|_{ℋ⁴}`. -/
theorem Env_le_envelope {α : ℝ} (f : Fn) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.NonlinRows.Rl1.Env α f
      ≤ 3 * α ^ (-(2 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 2 := by
  set X : ℝ := Work.FTS.Nonlin.Xn α f with hX
  have hX0 : 0 ≤ X := Work.Spaces.HkNorm_nonneg α 4 f
  have hr : (1 : ℝ) ≤ α ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hα.le]
    rw [one_le_inv₀ (Real.rpow_pos_of_pos hα 2)]
    exact Real.rpow_le_one hα.le hα1 (by norm_num)
  have hr0 : (0 : ℝ) < α ^ (-(2 : ℝ)) := lt_of_lt_of_le zero_lt_one hr
  -- `α^{-3/2} ≤ α^{-2}` for `α ≤ 1`
  have h32 : α ^ (-(3 / 2 : ℝ)) ≤ α ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hα hα1 (by norm_num)
  -- `√α ≤ 1`
  have hsq : Real.sqrt α ≤ 1 := Real.sqrt_le_one.mpr hα1
  rw [Work.FTS.NonlinRows.Rl1.Env, ← hX]
  have hXle : X ≤ (1 + X) ^ 2 := by nlinarith [hX0]
  have hX2le : X ^ 2 ≤ (1 + X) ^ 2 := by nlinarith [hX0, sq_nonneg X]
  have h1sq : (1 : ℝ) ≤ (1 + X) ^ 2 := by nlinarith [hX0]
  have hrb : (1 : ℝ) ≤ α ^ (-(2 : ℝ)) * (1 + X) ^ 2 :=
    h1sq.trans (le_mul_of_one_le_left (sq_nonneg (1 + X)) hr)
  have hsrb : (1 + X) ^ 2 ≤ α ^ (-(2 : ℝ)) * (1 + X) ^ 2 :=
    le_mul_of_one_le_left (sq_nonneg (1 + X)) hr
  have e1 : α ^ 2 ≤ α ^ (-(2 : ℝ)) * (1 + X) ^ 2 := by
    have h1 : α ^ 2 ≤ 1 := by
      have h := mul_self_le_mul_self hα.le hα1
      nlinarith [h]
    linarith
  have e2 : Real.sqrt α * X ≤ α ^ (-(2 : ℝ)) * (1 + X) ^ 2 := by
    have h1 : Real.sqrt α * X ≤ 1 * X := mul_le_mul_of_nonneg_right hsq hX0
    have h2 : X ≤ (1 + X) ^ 2 := hXle
    linarith
  have e3 : α ^ (-(3 / 2 : ℝ)) * X ^ 2 ≤ α ^ (-(2 : ℝ)) * (1 + X) ^ 2 := by
    have h1 : α ^ (-(3 / 2 : ℝ)) * X ^ 2 ≤ α ^ (-(2 : ℝ)) * X ^ 2 :=
      mul_le_mul_of_nonneg_right h32 (sq_nonneg X)
    have h2 : α ^ (-(2 : ℝ)) * X ^ 2 ≤ α ^ (-(2 : ℝ)) * (1 + X) ^ 2 :=
      mul_le_mul_of_nonneg_left hX2le hr0.le
    linarith
  linarith [e1, e2, e3]

/-! ## The two `FK(g)`-rows `N₄^{gg}`, `N₅^{gg}` -/

/-- **Rows `N₄^{gg}`, `N₅^{gg}` in the open class.**  `N₄^{gg} = -(1/2)FK(f)·D_θf` and
`N₅^{gg} = -sin²θ·FK(f)·f` are bounded by `K·Env α f`; this is the verbatim open-class version
of `Work.FTS.NonlinRows.Rl1.ggRows45`, with the slot data supplied by
`slotData_open_g`/`slotData_open_dth` in place of `slot0`/`slot1`. -/
theorem gg_fk_open_rows : ∃ K : ℝ, 0 < K ∧
    ∀ {α : ℝ} {f : Fn},
      0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Fa (Work.FTS.Nonlin.N4gg α f)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) ∧
      Fa (Work.FTS.Nonlin.N5gg f)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) := by
  refine ⟨12 * Real.sqrt (Real.pi / 2) + 1, by positivity, ?_⟩
  intro α f hα hα1 hso hmem
  have hXs : 0 ≤ Work.Spaces.HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
  have s0 : Work.FTS.NonlinRows.Rl1.SlotData α f
      (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f) (Work.Spaces.HkSq α 4 f) :=
    slotData_open_g (α := α) (f := f) hα hso hmem
  have s1 : Work.FTS.NonlinRows.Rl1.SlotData α (Work.Spaces.Dth f)
      (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi1 f) (Work.Spaces.HkSq α 4 f) :=
    slotData_open_dth (α := α) (f := f) hα hso hmem
  have hΦ1w := Work.FTS.NonlinRows.Rl1.invSq_mul_integrable_le
    (Φ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi1 f) (Xs := Work.Spaces.HkSq α 4 f)
    s1.nonneg s1.meas s1.intw s1.lew
  have hΦ0w := Work.FTS.NonlinRows.Rl1.invSq_mul_integrable_le
    (Φ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f) (Xs := Work.Spaces.HkSq α 4 f)
    s0.nonneg s0.meas s0.intw s0.lew
  have hEnvn : 0 ≤ Work.FTS.NonlinRows.Rl1.Env α f :=
    Work.FTS.NonlinRows.Rl1.Env_nonneg f hα.le
  have hX2 := Work.FTS.NonlinRows.Rl1.Xn_sq_le_Env f hα hα1
  have hfinal : ∀ {N : Fn}, Fa N ≤ ENNReal.ofReal (12 * Real.sqrt (Real.pi / 2)
      * (Work.FTS.Nonlin.Xn α f) ^ 2) →
      Fa N ≤ ENNReal.ofReal ((12 * Real.sqrt (Real.pi / 2) + 1)
        * Work.FTS.NonlinRows.Rl1.Env α f) := by
    intro N hN
    refine hN.trans (ENNReal.ofReal_le_ofReal ?_)
    have h12 : 0 ≤ 12 * Real.sqrt (Real.pi / 2) := by positivity
    calc 12 * Real.sqrt (Real.pi / 2) * (Work.FTS.Nonlin.Xn α f) ^ 2
        ≤ 12 * Real.sqrt (Real.pi / 2) * Work.FTS.NonlinRows.Rl1.Env α f :=
          mul_le_mul_of_nonneg_left hX2 h12
      _ ≤ (12 * Real.sqrt (Real.pi / 2) + 1) * Work.FTS.NonlinRows.Rl1.Env α f := by
          nlinarith [hEnvn, Real.sqrt_nonneg (Real.pi / 2)]
  constructor
  · -- `N₄^{gg} = -(1/2)·FK f·D_θ f`
    have hmain := Work.FTS.NonlinRows.Rl1.Fa_le_coef_slot
      (N := Work.FTS.Nonlin.N4gg α f)
      (A := fun r _ => 3 * Work.Construction.FK f r) (B := Work.Spaces.Dth f)
      (C := 144) (Ys := Work.Spaces.HkSq α 4 f) (Zs := Work.Spaces.HkSq α 4 f)
      (Ψ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f)
      (Φ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi1 f)
      (by norm_num) hXs hXs s0.nonneg s0.meas s0.int s0.le
      s1.nonneg s1.meas hΦ1w.1 hΦ1w.2
      (fun r _ => aestronglyMeasurable_const)
      (fun r hr => s1.aesm r hr)
      (fun r hr => s1.sqint r hr)
      (fun r hr => Filter.Eventually.of_forall fun θ => by
        have h := Work.FTS.NonlinRows.Rl1.FK_sq_le_sixteen_Phi0 (g := f) hr
          (s0.sqint r hr) (s0.aesm r hr)
        have h9 : (3 * Work.Construction.FK f r) ^ 2
            = 9 * (Work.Construction.FK f r) ^ 2 := by ring
        rw [h9]
        linarith [h])
      (fun r hr => (Work.FTS.NonlinRows.Rl1.slot_lintegral_eq (s1.sqint r hr) rfl).le)
      (fun r hr θ hθ => by
        have hK : |Work.Spaces.K θ| ≤ 3 := Work.FTS.NonlinRows.Rl1.K_abs_le_three' hθ
        have h1 : |Work.Spaces.K θ * Work.FTS.Nonlin.N4gg α f r θ|
            = |Work.Spaces.K θ| * (1 / 2) * |Work.Construction.FK f r|
              * |Work.Spaces.Dth f r θ| := by
          rw [Work.FTS.Nonlin.N4gg]
          simp only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2))]
          ring
        have h2 : |Work.Spaces.K θ| * (1 / 2) * |Work.Construction.FK f r|
              * |Work.Spaces.Dth f r θ|
            ≤ 3 * (1 / 2) * |Work.Construction.FK f r| * |Work.Spaces.Dth f r θ| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_right hK (by norm_num)
        have h3 : 3 * (1 / 2) * |Work.Construction.FK f r| * |Work.Spaces.Dth f r θ|
            ≤ |3 * Work.Construction.FK f r| * |Work.Spaces.Dth f r θ| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
          nlinarith [abs_nonneg (Work.Construction.FK f r),
            abs_nonneg (Work.Spaces.Dth f r θ)]
        exact (le_of_eq h1).trans (h2.trans h3))
    have hsimp : ENNReal.ofReal (Real.sqrt 144 * Real.sqrt (Real.pi / 2)
          * Real.sqrt (Work.Spaces.HkSq α 4 f) * Real.sqrt (Work.Spaces.HkSq α 4 f))
        = ENNReal.ofReal (12 * Real.sqrt (Real.pi / 2)
          * (Work.FTS.Nonlin.Xn α f) ^ 2) := by
      have hK : Real.sqrt (144 : ℝ) = 12 := by
        rw [show (144 : ℝ) = 12 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have hX : Real.sqrt (Work.Spaces.HkSq α 4 f) = Work.FTS.Nonlin.Xn α f := rfl
      rw [hK, hX]
      congr 1
      ring
    rw [hsimp] at hmain
    exact hfinal hmain
  · -- `N₅^{gg} = -sin²θ·FK f·f`
    have hmain := Work.FTS.NonlinRows.Rl1.Fa_le_coef_slot
      (N := Work.FTS.Nonlin.N5gg f)
      (A := fun r _ => 3 * Work.Construction.FK f r) (B := f)
      (C := 144) (Ys := Work.Spaces.HkSq α 4 f) (Zs := Work.Spaces.HkSq α 4 f)
      (Ψ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f)
      (Φ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f)
      (by norm_num) hXs hXs s0.nonneg s0.meas s0.int s0.le
      s0.nonneg s0.meas hΦ0w.1 hΦ0w.2
      (fun r _ => aestronglyMeasurable_const)
      (fun r hr => s0.aesm r hr)
      (fun r hr => s0.sqint r hr)
      (fun r hr => Filter.Eventually.of_forall fun θ => by
        have h := Work.FTS.NonlinRows.Rl1.FK_sq_le_sixteen_Phi0 (g := f) hr
          (s0.sqint r hr) (s0.aesm r hr)
        have h9 : (3 * Work.Construction.FK f r) ^ 2
            = 9 * (Work.Construction.FK f r) ^ 2 := by ring
        rw [h9]
        linarith [h])
      (fun r hr => (Work.FTS.NonlinRows.Rl1.slot_lintegral_eq (s0.sqint r hr) rfl).le)
      (fun r hr θ hθ => by
        have hK : |Work.Spaces.K θ| ≤ 3 := Work.FTS.NonlinRows.Rl1.K_abs_le_three' hθ
        have hs : (Real.sin θ) ^ 2 ≤ 1 := by
          nlinarith [Real.neg_one_le_sin θ, Real.sin_le_one θ]
        have h1 : |Work.Spaces.K θ * Work.FTS.Nonlin.N5gg f r θ|
            = |Work.Spaces.K θ| * (Real.sin θ) ^ 2 * |Work.Construction.FK f r|
              * |f r θ| := by
          rw [Work.FTS.Nonlin.N5gg]
          simp only [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg (Real.sin θ))]
          ring
        have h2 : |Work.Spaces.K θ| * (Real.sin θ) ^ 2 * |Work.Construction.FK f r|
              * |f r θ|
            ≤ 3 * 1 * |Work.Construction.FK f r| * |f r θ| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          exact mul_le_mul hK hs (sq_nonneg _) (by norm_num)
        have h3 : 3 * 1 * |Work.Construction.FK f r| * |f r θ|
            ≤ |3 * Work.Construction.FK f r| * |f r θ| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), mul_one]
        exact (le_of_eq h1).trans (h2.trans h3))
    have hsimp : ENNReal.ofReal (Real.sqrt 144 * Real.sqrt (Real.pi / 2)
          * Real.sqrt (Work.Spaces.HkSq α 4 f) * Real.sqrt (Work.Spaces.HkSq α 4 f))
        = ENNReal.ofReal (12 * Real.sqrt (Real.pi / 2)
          * (Work.FTS.Nonlin.Xn α f) ^ 2) := by
      have hK : Real.sqrt (144 : ℝ) = 12 := by
        rw [show (144 : ℝ) = 12 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have hX : Real.sqrt (Work.Spaces.HkSq α 4 f) = Work.FTS.Nonlin.Xn α f := rfl
      rw [hK, hX]
      congr 1
      ring
    rw [hsimp] at hmain
    exact hfinal hmain

/-! ## The three row groups and the assembly -/

theorem fk_open :
    ∃ K : ℝ, 0 < K ∧
    ∀ {α : ℝ} {f : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N4gg α f)
        ≤ ENNReal.ofReal (K * α ^ (-(2 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 2) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N5gg f)
        ≤ ENNReal.ofReal (K * α ^ (-(2 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 2) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N4gs α f)
        ≤ ENNReal.ofReal (K * α ^ (-(2 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 2) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N5gs α f)
        ≤ ENNReal.ofReal (K * α ^ (-(2 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 2) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N4sg α f)
        ≤ ENNReal.ofReal (K * α ^ (-(2 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 2) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N5sg α f)
        ≤ ENNReal.ofReal (K * α ^ (-(2 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 2) := by
  obtain ⟨K1, hK1, hrow1⟩ := gg_fk_open_rows
  obtain ⟨K2, hK2, hrow2⟩ := gs_open_rows
  obtain ⟨K3, hK3, hrow3⟩ := sg_fk_open_rows
  refine ⟨3 * (K1 + K2 + K3), by positivity, ?_⟩
  intro α f hα hα1 hso hmem
  have hEnv : Work.FTS.NonlinRows.Rl1.Env α f
      ≤ 3 * α ^ (-(2 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 2 :=
    Env_le_envelope f hα hα1
  have key : ∀ {N : Fn} {K : ℝ}, 0 < K → K ≤ K1 + K2 + K3 →
      Fa N ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) →
      Fa N ≤ ENNReal.ofReal (3 * (K1 + K2 + K3) * α ^ (-(2 : ℝ))
        * (1 + Work.FTS.Nonlin.Xn α f) ^ 2) := by
    intro N K hK hKK hN
    refine hN.trans (ENNReal.ofReal_le_ofReal ?_)
    calc K * Work.FTS.NonlinRows.Rl1.Env α f
        ≤ K * (3 * α ^ (-(2 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 2) :=
          mul_le_mul_of_nonneg_left hEnv hK.le
      _ = (3 * K) * α ^ (-(2 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 2 := by ring
      _ ≤ 3 * (K1 + K2 + K3) * α ^ (-(2 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h1 := hrow1 hα hα1 hso hmem
  have h2 := hrow2 hα hα1 hso hmem
  have h3 := hrow3 hα hα1 hso hmem
  refine ⟨key hK1 (by linarith) h1.1, key hK1 (by linarith) h1.2,
    key hK2 (by linarith) h2.1, key hK2 (by linarith) h2.2,
    key hK3 (by linarith) h3.1, key hK3 (by linarith) h3.2⟩

end

end Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux

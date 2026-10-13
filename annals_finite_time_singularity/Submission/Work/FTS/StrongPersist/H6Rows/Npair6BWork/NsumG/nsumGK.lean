import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.NDefs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.fstarDat
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.ksDat
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.ksMixed
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.rowDthWlInf
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowStarFam
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowStarP
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG.nsumG2
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.N0coefA4_WlInf6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)
open Work.FTS.StrongPersist.H6Rows.Npair6SupAux
open Work.FTS.StrongPersist.H6Rows.N0pair6Aux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Elementary helpers for the four pieces -/

/-- The angular factor `(α + sin 2θ)·sin(2θ)^{α/5}` (or `1` on the `i = 0` slot) is
nonnegative on the closed quadrant `0 ≤ θ ≤ π/2`. -/
theorem angFac_nonneg {α θ : ℝ} (hα : 0 ≤ α) (hθ0 : 0 ≤ θ) (hθ2 : θ ≤ Real.pi / 2)
    (i : ℕ) :
    0 ≤ (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1) := by
  split_ifs with hi
  · have hs : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩
    exact mul_nonneg (by linarith) (Real.rpow_nonneg hs _)
  · norm_num

/-- The star price bound `1 + C₀α ≤ (1 + C₀)·(1+|Ce|+|Cs|)²` for `0 < α ≤ 1` and `C₀ ≥ 0`. -/
theorem one_add_alpha_price_le {α Ce Cs C0 : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hC0 : 0 ≤ C0) :
    1 + C0 * α ≤ (1 + C0) * (1 + |Ce| + |Cs|) ^ 2 := by
  have hD1 : (1 : ℝ) ≤ 1 + |Ce| + |Cs| := by linarith [abs_nonneg Ce, abs_nonneg Cs]
  have hD2 : (1 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 2 := by nlinarith
  have h1 : C0 * α ≤ C0 := mul_le_of_le_one_right hC0 hα1
  have h2 : 1 + C0 ≤ (1 + C0) * (1 + |Ce| + |Cs|) ^ 2 := by nlinarith [hC0, hD2]
  linarith

/-- The same with the exponent `4` on the star factor. -/
theorem one_add_alpha_price_le4 {α Ce Cs C0 : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hC0 : 0 ≤ C0) :
    1 + C0 * α ≤ (1 + C0) * (1 + |Ce| + |Cs|) ^ 4 := by
  have h2 := one_add_alpha_price_le (Ce := Ce) (Cs := Cs) hα0 hα1 hC0
  have hD1 : (1 : ℝ) ≤ 1 + |Ce| + |Cs| := by linarith [abs_nonneg Ce, abs_nonneg Cs]
  have hD24 : (1 + |Ce| + |Cs|) ^ 2 ≤ (1 + |Ce| + |Cs|) ^ 4 :=
    pow_le_pow_right₀ hD1 (by norm_num)
  calc 1 + C0 * α ≤ (1 + C0) * (1 + |Ce| + |Cs|) ^ 2 := h2
    _ ≤ (1 + C0) * (1 + |Ce| + |Cs|) ^ 4 := mul_le_mul_of_nonneg_left hD24 (by linarith)

/-- One coefficient price `1 + KA` is absorbed into the `α^{-10}(1+|Ce|+|Cs|)^4(1+M)^4` budget. -/
theorem arithK1 {α M Ce Cs C KA A0 W : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hC : 0 ≤ C) (hKA0 : 0 ≤ KA)
    (hKA : 1 + KA ≤ A0 * (1 + |Ce| + |Cs|) ^ 4)
    (hA0 : 0 ≤ A0) (hM : 0 ≤ M) (hW : 0 ≤ W) :
    C * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + M) * W
      ≤ (C * A0) * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 * W := by
  have hα3 : α ^ (-(3 : ℝ)) ≤ α ^ (-(10 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (by norm_num)
  have hαnn : 0 ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hXnn : 0 ≤ (1 + |Ce| + |Cs|) ^ 4 := by positivity
  have hM4nn : 0 ≤ (1 + M) ^ 4 := by positivity
  have hM4 : 1 + M ≤ (1 + M) ^ 4 := by
    have h1 : (1 : ℝ) ≤ 1 + M := by linarith
    nlinarith [sq_nonneg (1 + M), sq_nonneg ((1 + M) ^ 2 - 1)]
  have hA : 0 ≤ A0 * (1 + |Ce| + |Cs|) ^ 4 := mul_nonneg hA0 hXnn
  have hstep1 : C * α ^ (-(3 : ℝ)) ≤ C * α ^ (-(10 : ℝ)) :=
    mul_le_mul_of_nonneg_left hα3 hC
  have hstep2 : C * α ^ (-(3 : ℝ)) * (1 + KA)
      ≤ C * α ^ (-(10 : ℝ)) * (A0 * (1 + |Ce| + |Cs|) ^ 4) :=
    mul_le_mul hstep1 hKA (by linarith) (mul_nonneg hC hαnn)
  have hstep3 : C * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + M)
      ≤ C * α ^ (-(10 : ℝ)) * (A0 * (1 + |Ce| + |Cs|) ^ 4) * (1 + M) ^ 4 :=
    mul_le_mul hstep2 hM4 (by linarith) (mul_nonneg (mul_nonneg hC hαnn) hA)
  have hstep4 := mul_le_mul hstep3 (le_refl W) hW
    (mul_nonneg (mul_nonneg (mul_nonneg hC hαnn) hA) hM4nn)
  calc C * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + M) * W
      ≤ C * α ^ (-(10 : ℝ)) * (A0 * (1 + |Ce| + |Cs|) ^ 4) * (1 + M) ^ 4 * W := hstep4
    _ = (C * A0) * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 * W := by ring

/-- The two coefficient prices `1 + KA`, `1 + KQ` are absorbed into the budget. -/
theorem arithK2 {α M Ce Cs C KA KQ A0 B0 W : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hC : 0 ≤ C) (hKA0 : 0 ≤ KA) (hKQ0 : 0 ≤ KQ)
    (hKA : 1 + KA ≤ A0 * (1 + |Ce| + |Cs|) ^ 2)
    (hKQ : 1 + KQ ≤ B0 * (1 + |Ce| + |Cs|) ^ 2)
    (hA0 : 0 ≤ A0) (hB0 : 0 ≤ B0) (hM : 0 ≤ M) (hW : 0 ≤ W) :
    C * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + KQ) * (1 + M) * W
      ≤ (C * A0 * B0) * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 * W := by
  have hD1 : (1 : ℝ) ≤ 1 + |Ce| + |Cs| := by linarith [abs_nonneg Ce, abs_nonneg Cs]
  have hD0 : 0 ≤ (1 + |Ce| + |Cs|) ^ 2 := by positivity
  have hprod : (1 + KA) * (1 + KQ) ≤ (A0 * B0) * (1 + |Ce| + |Cs|) ^ 4 := by
    have := mul_le_mul hKA hKQ (by linarith) (mul_nonneg hA0 hD0)
    calc (1 + KA) * (1 + KQ)
        ≤ (A0 * (1 + |Ce| + |Cs|) ^ 2) * (B0 * (1 + |Ce| + |Cs|) ^ 2) := this
      _ = (A0 * B0) * (1 + |Ce| + |Cs|) ^ 4 := by ring
  have hprod0 : 0 ≤ (1 + KA) * (1 + KQ) := by
    have h1 : (0 : ℝ) < 1 + KA := by linarith
    have h2 : (0 : ℝ) < 1 + KQ := by linarith
    positivity
  have hα3 : α ^ (-(3 : ℝ)) ≤ α ^ (-(10 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (by norm_num)
  have hαnn : 0 ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hXnn : 0 ≤ (1 + |Ce| + |Cs|) ^ 4 := by positivity
  have hM4nn : 0 ≤ (1 + M) ^ 4 := by positivity
  have hM4 : 1 + M ≤ (1 + M) ^ 4 := by
    have h1 : (1 : ℝ) ≤ 1 + M := by linarith
    nlinarith [sq_nonneg (1 + M), sq_nonneg ((1 + M) ^ 2 - 1)]
  have hA : 0 ≤ (A0 * B0) * (1 + |Ce| + |Cs|) ^ 4 := mul_nonneg (mul_nonneg hA0 hB0) hXnn
  have hstep1 : C * α ^ (-(3 : ℝ)) ≤ C * α ^ (-(10 : ℝ)) :=
    mul_le_mul_of_nonneg_left hα3 hC
  have hstep2 : C * α ^ (-(3 : ℝ)) * ((1 + KA) * (1 + KQ))
      ≤ C * α ^ (-(10 : ℝ)) * ((A0 * B0) * (1 + |Ce| + |Cs|) ^ 4) :=
    mul_le_mul hstep1 hprod hprod0 (mul_nonneg hC hαnn)
  have hstep3 : C * α ^ (-(3 : ℝ)) * ((1 + KA) * (1 + KQ)) * (1 + M)
      ≤ C * α ^ (-(10 : ℝ)) * ((A0 * B0) * (1 + |Ce| + |Cs|) ^ 4) * (1 + M) ^ 4 :=
    mul_le_mul hstep2 hM4 (by linarith) (mul_nonneg (mul_nonneg hC hαnn) hA)
  have hstep4 := mul_le_mul hstep3 (le_refl W) hW
    (mul_nonneg (mul_nonneg (mul_nonneg hC hαnn) hA) hM4nn)
  calc C * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + KQ) * (1 + M) * W
      = C * α ^ (-(3 : ℝ)) * ((1 + KA) * (1 + KQ)) * (1 + M) * W := by ring
    _ ≤ C * α ^ (-(10 : ℝ)) * ((A0 * B0) * (1 + |Ce| + |Cs|) ^ 4) * (1 + M) ^ 4 * W :=
        hstep4
    _ = (C * A0 * B0) * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 * W := by ring

/-- Piece bounds for the four "angular-moment of the star profile" pieces of the level-six `N`-row,
with `Ks := FK (Fstar α)`:
`nsP12 = -(1/2)·Ks·D_θF_*`, `nsP13 = -(1/2)·Ks·D_θf`, `nsP16 = -sin²θ·Ks·F_*`,
`nsP17 = -sin²θ·Ks·f`.  The profile is explicit: `FK (Fstar α) z = 2α·z/(1+z)^2 = α·FM.Fstar z`
(since `Fstar α = α·(Gam α θ / c α)·FM.Fstar` with `∫_0^{π/2} Gam α·K = c α`), so all the data is
elementary: `SmoothOpen Ks`, `SmoothOpen (fun z θ => sin θ^2 * Ks z)`, `WlInfMem α 6` of both,
`WlInf α 6 ≤ C α`, and the flat pointwise price
`|mixed j i Ks| ≤ C α (z/(1+z)) (if 1 ≤ i then (α+σ)σ^{α/5} else 1)` (the `i ≥ 1` slots vanish).
Route: `rowDthWlInf` for `nsP13`; `rowStarFam`-type for `nsP17`; a pointwise-priced `A·Q` slot row
for `nsP12`/`nsP16` (with `fstarDat` for the star slots).  The proved module
`Npair6BWork.ksDat` (together with `Npair6BWork.ksMixed`) states/prives exactly this data. -/
theorem nsumGK (Ce : ℝ) : ∃ C : ℝ, 0 < C ∧
    ∀ α ∈ Set.Ioc 0 1, ∀ (g Φ : Work.FTS.Galerkin.Fam) (τ M Cs : ℝ)
      (E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn) (Φs : Work.FTS.Galerkin.Fn),
      0 ≤ τ →
      Work.FTS.StrongPersist.L6Ctx (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1)
        α M Ce Cs E Φs g Φ τ →
      ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      (|Work.FTS.TransportS.slotPairing ρ a b (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP12 α) (Work.FTS.Galerkin.slice g τ)|
          ≤ C * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
              * (1 + Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g τ)) ∧
       |Work.FTS.TransportS.slotPairing ρ a b (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP13 α (Work.FTS.Galerkin.slice g τ)) (Work.FTS.Galerkin.slice g τ)|
          ≤ C * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
              * (1 + Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g τ)) ∧
       |Work.FTS.TransportS.slotPairing ρ a b (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP16 α) (Work.FTS.Galerkin.slice g τ)|
          ≤ C * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
              * (1 + Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g τ)) ∧
       |Work.FTS.TransportS.slotPairing ρ a b (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP17 α (Work.FTS.Galerkin.slice g τ)) (Work.FTS.Galerkin.slice g τ)|
          ≤ C * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
              * (1 + Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g τ))) := by
  obtain ⟨C1, hC1pos, hFam⟩ := rowStarFam
  obtain ⟨C2, hC2pos, hP⟩ := rowStarP
  obtain ⟨C3, hC3pos, hKS⟩ := ksDat
  obtain ⟨C4, hC4pos, hFS⟩ := fstarDat
  refine ⟨max (C1 * (1 + C3)) (C2 * (1 + C3) * (1 + C4)) + 1, by positivity, ?_⟩
  set Cf : ℝ := max (C1 * (1 + C3)) (C2 * (1 + C3) * (1 + C4)) + 1 with hCf
  have hCfin1 : C1 * (1 + C3) ≤ Cf := by
    rw [hCf]
    exact le_trans (le_max_left _ _) (le_add_of_nonneg_right (by norm_num))
  have hCfin2 : C2 * (1 + C3) * (1 + C4) ≤ Cf := by
    rw [hCf]
    exact le_trans (le_max_right _ _) (le_add_of_nonneg_right (by norm_num))
  intro α hαI g Φ τ M Cs E Φs hτ hctx a b ρ hab hleaf
  have hα0 : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  set f : Fn := Work.FTS.Galerkin.slice g τ with hf
  have hdat : Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M := by
    simpa only [hf] using
      (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.datData_of_H6Adm hctx.hreg hctx.h7 hctx.hbdd)
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hdat.bdd
  have hW0 : 0 ≤ 1 + Work.Spaces.HkSq α 6 f := by
    have := Work.Spaces.HkSq_nonneg α 6 f
    linarith
  have hαnn : 0 ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hDnn4 : 0 ≤ (1 + |Ce| + |Cs|) ^ 4 := by positivity
  have hM4nn : 0 ≤ (1 + M) ^ 4 := by positivity
  have hbig0 : 0 ≤ α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
      * (1 + Work.Spaces.HkSq α 6 f) :=
    mul_nonneg (mul_nonneg (mul_nonneg hαnn hDnn4) hM4nn) hW0
  obtain ⟨hKsm, hKTsm, -, -, -, -, hKpt⟩ := hKS α hαI
  obtain ⟨hFsm, hTsm, -, -, -, -, -, -, -, hFpt⟩ := hFS α hαI
  -- ## smoothness of the four coefficient/slot fields
  have hA12sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-(1 / 2) : ℝ) * coefKs α z θ) :=
    smoothOpen_const_mul (-(1 / 2)) hKsm
  have hA16sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-(1 : ℝ)) * (Real.sin θ ^ 2 * coefKs α z θ)) :=
    smoothOpen_const_mul (-(1 : ℝ)) hKTsm
  have hQ1sm : Work.FTS.EllipticEst.SmoothOpen (slotTs α) := hTsm
  have hQ2sm : Work.FTS.EllipticEst.SmoothOpen (slotFs α) := hFsm
  -- ## the four pointwise prices
  have hdecA12 : ∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ => (-(1 / 2) : ℝ) * coefKs α z θ) z θ|
        ≤ (C3 * α) * (z / (1 + z)) *
          (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1) := by
    intro j i hji z θ hz hθ hθ2
    have hh := hKpt (coefKs α) (Or.inl rfl) j i hji z θ hz hθ hθ2
    rw [mixed_const_mul (-(1 / 2)) (coefKs α) j i]
    rw [abs_mul, show |(-(1 / 2) : ℝ)| = 1 / 2 from by norm_num]
    have hang := angFac_nonneg hα0.le hθ.le (le_of_lt hθ2) i
    have hz0 : 0 ≤ z / (1 + z) := by positivity
    have hC3a : 0 ≤ C3 * α := mul_nonneg hC3pos.le hα0.le
    have hprod : 0 ≤ ((C3 * α) * (z / (1 + z))) *
        (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1) :=
      mul_nonneg (mul_nonneg hC3a hz0) hang
    calc (1 / 2) * |Work.Spaces.mixed j i (coefKs α) z θ|
        ≤ (1 / 2) * (C3 * α * (z / (1 + z)) *
            (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1)) :=
          mul_le_mul_of_nonneg_left hh (by norm_num)
      _ ≤ (C3 * α) * (z / (1 + z)) *
            (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1) := by
          nlinarith [hprod]
  have hdecA16 : ∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ => (-(1 : ℝ)) * (Real.sin θ ^ 2 * coefKs α z θ)) z θ|
        ≤ (C3 * α) * (z / (1 + z)) *
          (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1) := by
    intro j i hji z θ hz hθ hθ2
    have hh := hKpt (fun z θ => Real.sin θ ^ 2 * coefKs α z θ) (Or.inr rfl)
      j i hji z θ hz hθ hθ2
    rw [mixed_const_mul (-(1 : ℝ)) (fun z θ => Real.sin θ ^ 2 * coefKs α z θ) j i]
    rw [abs_mul, abs_neg, abs_one, one_mul]
    exact hh
  have hdecQ1 : ∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (slotTs α) z θ| ≤ (C4 * α) * (z / (1 + z) ^ 2) *
        (if 1 ≤ i then (Real.sin (2 * θ)) ^ (α / 3) else 1) := by
    intro j i hji z θ hz hθ hθ2
    exact hFpt (Work.Spaces.Dth (Work.Construction.Fstar α)) (Or.inr (Or.inl rfl))
      j i hji z θ hz hθ hθ2
  have hdecQ2 : ∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (slotFs α) z θ| ≤ (C4 * α) * (z / (1 + z) ^ 2) *
        (if 1 ≤ i then (Real.sin (2 * θ)) ^ (α / 3) else 1) := by
    intro j i hji z θ hz hθ hθ2
    exact hFpt (Work.Construction.Fstar α) (Or.inl rfl) j i hji z θ hz hθ hθ2
  -- ## the arithmetic side conditions
  have hKA0 : 0 ≤ C3 * α := mul_nonneg hC3pos.le hα0.le
  have hKQ0 : 0 ≤ C4 * α := mul_nonneg hC4pos.le hα0.le
  have hA0 : 0 ≤ 1 + C3 := by linarith
  have hB0 : 0 ≤ 1 + C4 := by linarith
  have hKAle2 := one_add_alpha_price_le (Ce := Ce) (Cs := Cs) hα0 hα1 hC3pos.le
  have hKAle4 := one_add_alpha_price_le4 (Ce := Ce) (Cs := Cs) hα0 hα1 hC3pos.le
  have hKQle2 := one_add_alpha_price_le (Ce := Ce) (Cs := Cs) hα0 hα1 hC4pos.le
  -- ## the piece `nsP12 = -(1/2)·Ks·D_θF_*` (`rowStarP`)
  have h12 : |Work.FTS.TransportS.slotPairing ρ a b (nsP12 α) f|
      ≤ Cf * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
          * (1 + Work.Spaces.HkSq α 6 f) := by
    have hrow := hP α hαI (fun z θ => (-(1 / 2) : ℝ) * coefKs α z θ) (slotTs α) f
      (C3 * α) (C4 * α) M a b ρ hA12sm hQ1sm hdat hdecA12 hdecQ1 hab hleaf
    have hP12 : (fun z θ => ((fun z θ => (-(1 / 2) : ℝ) * coefKs α z θ) z θ)
        * slotTs α z θ) = nsP12 α := by
      funext z θ
      simp only [nsP12, coefKs]
      try ring
    rw [← hP12]
    refine le_trans hrow ?_
    calc C2 * α ^ (-(3 : ℝ)) * (1 + C3 * α) * (1 + C4 * α) * (1 + M)
          * (1 + Work.Spaces.HkSq α 6 f)
        ≤ (C2 * (1 + C3) * (1 + C4)) * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
            * (1 + M) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) :=
          arithK2 hα0 hα1 hC2pos.le hKA0 hKQ0 hKAle2 hKQle2 hA0 hB0 hM0 hW0
      _ ≤ Cf * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f) := by
          have h := mul_le_mul_of_nonneg_right hCfin2 hbig0
          calc (C2 * (1 + C3) * (1 + C4)) * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
                * (1 + M) ^ 4 * (1 + Work.Spaces.HkSq α 6 f)
              = (C2 * (1 + C3) * (1 + C4)) * (α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
                  * (1 + M) ^ 4 * (1 + Work.Spaces.HkSq α 6 f)) := by ring
            _ ≤ Cf * (α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
                  * (1 + Work.Spaces.HkSq α 6 f)) := h
            _ = Cf * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
                  * (1 + Work.Spaces.HkSq α 6 f) := by ring
  -- ## the piece `nsP13 = -(1/2)·Ks·D_θf` (`rowStarFam`)
  have h13 : |Work.FTS.TransportS.slotPairing ρ a b (nsP13 α f) f|
      ≤ Cf * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
          * (1 + Work.Spaces.HkSq α 6 f) := by
    have hrow := (hFam α hαI (fun z θ => (-(1 / 2) : ℝ) * coefKs α z θ) f
      (C3 * α) M a b ρ hA12sm hdat hdecA12 hab hleaf).2
    have hP13 : (fun z θ => ((fun z θ => (-(1 / 2) : ℝ) * coefKs α z θ) z θ)
        * Work.Spaces.Dth f z θ) = nsP13 α f := by
      funext z θ
      simp only [nsP13, slotTf, coefKs]
      try ring
    rw [← hP13]
    refine le_trans hrow ?_
    calc C1 * α ^ (-(3 : ℝ)) * (1 + C3 * α) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)
        ≤ (C1 * (1 + C3)) * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f) :=
          arithK1 hα0 hα1 hC1pos.le hKA0 hKAle4 hA0 hM0 hW0
      _ ≤ Cf * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f) := by
          have h := mul_le_mul_of_nonneg_right hCfin1 hbig0
          calc (C1 * (1 + C3)) * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
                * (1 + M) ^ 4 * (1 + Work.Spaces.HkSq α 6 f)
              = (C1 * (1 + C3)) * (α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
                  * (1 + M) ^ 4 * (1 + Work.Spaces.HkSq α 6 f)) := by ring
            _ ≤ Cf * (α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
                  * (1 + Work.Spaces.HkSq α 6 f)) := h
            _ = Cf * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
                  * (1 + Work.Spaces.HkSq α 6 f) := by ring
  -- ## the piece `nsP16 = -sin²θ·Ks·F_*` (`rowStarP`)
  have h16 : |Work.FTS.TransportS.slotPairing ρ a b (nsP16 α) f|
      ≤ Cf * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
          * (1 + Work.Spaces.HkSq α 6 f) := by
    have hrow := hP α hαI (fun z θ => (-(1 : ℝ)) * (Real.sin θ ^ 2 * coefKs α z θ))
      (slotFs α) f (C3 * α) (C4 * α) M a b ρ hA16sm hQ2sm hdat hdecA16 hdecQ2 hab hleaf
    have hP16 : (fun z θ => ((fun z θ => (-(1 : ℝ)) * (Real.sin θ ^ 2 * coefKs α z θ)) z θ)
        * slotFs α z θ) = nsP16 α := by
      funext z θ
      simp only [nsP16, angSin2, slotFs, coefKs]
      try ring
    rw [← hP16]
    refine le_trans hrow ?_
    calc C2 * α ^ (-(3 : ℝ)) * (1 + C3 * α) * (1 + C4 * α) * (1 + M)
          * (1 + Work.Spaces.HkSq α 6 f)
        ≤ (C2 * (1 + C3) * (1 + C4)) * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
            * (1 + M) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) :=
          arithK2 hα0 hα1 hC2pos.le hKA0 hKQ0 hKAle2 hKQle2 hA0 hB0 hM0 hW0
      _ ≤ Cf * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f) := by
          have h := mul_le_mul_of_nonneg_right hCfin2 hbig0
          calc (C2 * (1 + C3) * (1 + C4)) * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
                * (1 + M) ^ 4 * (1 + Work.Spaces.HkSq α 6 f)
              = (C2 * (1 + C3) * (1 + C4)) * (α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
                  * (1 + M) ^ 4 * (1 + Work.Spaces.HkSq α 6 f)) := by ring
            _ ≤ Cf * (α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
                  * (1 + Work.Spaces.HkSq α 6 f)) := h
            _ = Cf * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
                  * (1 + Work.Spaces.HkSq α 6 f) := by ring
  -- ## the piece `nsP17 = -sin²θ·Ks·f` (`rowStarFam`)
  have h17 : |Work.FTS.TransportS.slotPairing ρ a b (nsP17 α f) f|
      ≤ Cf * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
          * (1 + Work.Spaces.HkSq α 6 f) := by
    have hrow := (hFam α hαI (fun z θ => (-(1 : ℝ)) * (Real.sin θ ^ 2 * coefKs α z θ)) f
      (C3 * α) M a b ρ hA16sm hdat hdecA16 hab hleaf).1
    have hP17 : (fun z θ => ((fun z θ => (-(1 : ℝ)) * (Real.sin θ ^ 2 * coefKs α z θ)) z θ)
        * f z θ) = nsP17 α f := by
      funext z θ
      simp only [nsP17, angSin2, coefKs]
      try ring
    rw [← hP17]
    refine le_trans hrow ?_
    calc C1 * α ^ (-(3 : ℝ)) * (1 + C3 * α) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)
        ≤ (C1 * (1 + C3)) * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f) :=
          arithK1 hα0 hα1 hC1pos.le hKA0 hKAle4 hA0 hM0 hW0
      _ ≤ Cf * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f) := by
          have h := mul_le_mul_of_nonneg_right hCfin1 hbig0
          calc (C1 * (1 + C3)) * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
                * (1 + M) ^ 4 * (1 + Work.Spaces.HkSq α 6 f)
              = (C1 * (1 + C3)) * (α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4
                  * (1 + M) ^ 4 * (1 + Work.Spaces.HkSq α 6 f)) := by ring
            _ ≤ Cf * (α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
                  * (1 + Work.Spaces.HkSq α 6 f)) := h
            _ = Cf * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
                  * (1 + Work.Spaces.HkSq α 6 f) := by ring
  exact ⟨h12, h13, h16, h17⟩

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG

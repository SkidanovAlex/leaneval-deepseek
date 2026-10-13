/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `θ`-integration-by-parts piece of the `(FK f)·D_θf` slot

This file proves `Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkThetaIbpPiece`, the
exceptional piece of the level-six coefficient rows in which the datum-slot of the coefficient
pairing carries **one more** angular derivative than the leaf weight can pay for:

  `|∫_z (FK f)(z)·(∫_θ ρ·(D_z^bD_θ^{a+1}f)·(D_z^bD_θ^a f))| ≤ C(1+M)²(1+|f|²_{ℋ⁶})`

for `DatData α f M` (`|f|_{ℋ⁴} = Xn α f ≤ M`), `a + b ≤ 6` and a leaf weight
`ρ ∈ {w²σ^{-η}, w², w²σ^{-γ}}` (`IsLeafW α a ρ`).  Here `(FK f)(z) = ∫_θ f(z,θ)K(θ) dθ` is the
angular moment of `f`, which is **radial** (independent of `θ`).

## Why the plain Cauchy–Schwarz is not enough

At the top slot `a + b = 6` the two factors of the angular pairing have slot orders `a+b = 6`
resp. `a+b+1 = 7`; the level-`7` slot is not controlled by `HkSq α 6 f` (the hypothesis `h7` of
`DatData` is only a *finiteness* statement).  The repair is the angular integration by parts

  `∫_θ σ^{-q}·(D_θh)·h = (q-1)·∫_θ cos(2θ)σ^{-q}·h²`   (`h = D_z^bD_θ^a f`, `σ = sin 2θ`),

which trades the level-`7` slot `D_z^bD_θ^{a+1}f = D_θh` for the level-`6` slot `h` (this is
`Work.FTS.StrongPersist.H6Aux.wip_Dth_ibp`, whose end-point terms vanish automatically from the
integrability of the two sides — no separate `lim σ^{1-q}h² = 0` hypothesis is needed).  Since
`|q-1| ≤ 1` for the three leaf exponents (`q = η`, `0`, `γ` with `γ = 1 + α/10` and `α ≤ 1`), the
whole pairing is then dominated by `|(FK f)|_∞ · ∫∫ρh² ≤ C·M·HkSq α 6 f`.

## The pieces

* `fk_cont_FK` (`fkThetaAux`) — continuity of `z ↦ (FK f)(z)` on `(0,∞)`;
* `fk_ibp_integrable` (`fkThetaAux`) — the integrability inputs of the angular IBP for an
  arbitrary bounded radial multiplier `g`;
* `fk_end_bound`, `fk_radial_shift` (`fkThetaEnd`) — the closed estimate `≤ A·HkSq α 6 f`;
* the pointwise price `|(FK f)(z)| ≤ 4√(C₀|f|²_{ℋ⁴})` (the θ-Cauchy–Schwarz of
  `Work.FTS.Nonlinear.Pieces.Rl1.n5_FK_abs_le` with the uniform slice energy bound
  `Work.FTS.TransportS.SupDzAux.sup_dz_avg_le` at `b = 0`), and the final arithmetic.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkThetaAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkThetaEnd
import Submission.Work.FTS.CoercivityFix.Coer1.thetaIBP
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12ShiftThetaAux
import Submission.Work.FTS.StrongPersist.H6Aux.wip_Dth_ibp
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.leaf_slot_le6
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen
import Submission.Work.FTS.MeridianDyn.Bridge.ProfDerivData_of_regPkg_closed
import Submission.Work.Construction.Basic
import Submission.Work.FTS.TransportS.SupDzAux.sup_dz_avg_le
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.n5Bound
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

set_option maxHeartbeats 1600000
/-! ## The requested piece -/

theorem fkThetaIbpPiece : ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ} {f : Work.FTS.Galerkin.Fn} {M : ℝ},
    0 < α → α ≤ 1 →
    Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
    ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |∫ z in Work.Spaces.Iz, Work.Construction.FK f z
          * (∫ θ in Work.Spaces.Iθ, ρ z θ
              * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ)|
        ≤ C * (1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.FTS.TransportS.SupDzAux.sup_dz_avg_le
  obtain ⟨C₁, hC₁pos, hC₁⟩ := fk_radial_shift
  refine ⟨C₁ * (4 * Real.sqrt C₀) + 1, by positivity, ?_⟩
  intro α f M hα hα1 hdd a b ρ hab hρ
  obtain ⟨hO, hmem6, hmem7, _hvanish, haxis, hM⟩ := hdd
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.IPGen.HkMem_mono_le hO 4 (by norm_num) hmem6
  have hsq6nn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hMnn : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hM
  -- the `θ`-Cauchy–Schwarz bound on the angular moment
  have haesm : ∀ z : ℝ, 0 < z → MeasureTheory.AEStronglyMeasurable (fun θ => f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := fun z hz =>
    Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry f) hO.continuousOn hz
  have hgA : ∀ z : ℝ, 0 < z → |Work.Construction.FK f z|
      ≤ 4 * Real.sqrt (C₀ * Work.Spaces.HkSq α 4 f) := by
    intro z hz
    have hsqint : MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2) Work.Spaces.Iθ := by
      have hw1 : 1 ≤ (Work.Spaces.w z) ^ 2 :=
        one_le_pow₀ (Work.FTS.TransportS.one_le_w hz)
      refine MeasureTheory.Integrable.mono' (hmem4.1 z (Set.mem_Ici.mpr (le_of_lt hz)))
        ((haesm z hz).pow 2) ?_
      filter_upwards [Work.FTS.IPGen.ip_ae_mem_Ioo_Iθ] with θ hθ
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have hh := Work.FTS.StrongPersist.H6Pair6Aux.leafdom_rpow (α := α) (h := f) hα
        (q := 0) (a := 0) (b := 0) (k := 4) (by norm_num)
        (by rw [Work.Spaces.gam]; linarith)
        (fun _ => by rw [Work.Spaces.eta]; norm_num)
        (Set.mem_Ici.mpr (le_of_lt hz)) hθ
      rw [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero, neg_zero,
        Real.rpow_zero, mul_one] at hh
      calc (f z θ) ^ 2 = 1 * (f z θ) ^ 2 := by ring
        _ ≤ (Work.Spaces.w z) ^ 2 * (f z θ) ^ 2 :=
            mul_le_mul_of_nonneg_right hw1 (sq_nonneg _)
        _ ≤ Work.Spaces.HkIntegrand α 4 f z θ := hh
    have hslice := hC₀ α f 0 hα hα1 hO hmem4 (by norm_num) z hz
    have hslice' : (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2)
        ≤ C₀ * Work.Spaces.HkSq α 4 f := by simpa using hslice
    have hFK := Work.FTS.Nonlinear.Pieces.Rl1.n5_FK_abs_le hz hsqint (haesm z hz)
    refine hFK.trans ?_
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hslice') (by norm_num)
  have hcont : ContinuousOn (fun z => Work.Construction.FK f z) (Set.Ioi 0) :=
    fk_cont_FK hO hmem4
  have hAnn : 0 ≤ 4 * Real.sqrt (C₀ * Work.Spaces.HkSq α 4 f) := by positivity
  have hbound := hC₁ (g := fun z => Work.Construction.FK f z) hα hα1 hO hmem6 hmem7
    hcont hAnn hgA a b ρ hab hρ
  -- the arithmetic
  have hsqrt : Real.sqrt (Work.Spaces.HkSq α 4 f) = Work.FTS.Nonlin.Xn α f := rfl
  have hAeq : 4 * Real.sqrt (C₀ * Work.Spaces.HkSq α 4 f)
      = 4 * Real.sqrt C₀ * Work.FTS.Nonlin.Xn α f := by
    rw [Real.sqrt_mul hC₀pos.le, hsqrt]
    ring
  have hAM : 4 * Real.sqrt C₀ * Work.FTS.Nonlin.Xn α f ≤ 4 * Real.sqrt C₀ * M :=
    mul_le_mul_of_nonneg_left hM (by positivity)
  have hAM' : C₁ * (4 * Real.sqrt C₀ * Work.FTS.Nonlin.Xn α f)
      ≤ C₁ * (4 * Real.sqrt C₀ * M) := mul_le_mul_of_nonneg_left hAM hC₁pos.le
  have hMS : M * Work.Spaces.HkSq α 6 f
      ≤ (1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by
    have h1 : M ≤ 1 + M := by linarith
    have h2 : Work.Spaces.HkSq α 6 f ≤ 1 + Work.Spaces.HkSq α 6 f := by linarith
    have h3 : (1 : ℝ) + M ≤ (1 + M) * (1 + M) := by nlinarith [hMnn, sq_nonneg M]
    calc M * Work.Spaces.HkSq α 6 f
        ≤ (1 + M) * (1 + Work.Spaces.HkSq α 6 f) :=
          mul_le_mul h1 h2 hsq6nn (by linarith)
      _ ≤ (1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) :=
          mul_le_mul_of_nonneg_right h3 (by linarith)
  have hgoal : (C₁ * (4 * Real.sqrt (C₀ * Work.Spaces.HkSq α 4 f)))
        * Work.Spaces.HkSq α 6 f
      ≤ (C₁ * (4 * Real.sqrt C₀) + 1) * (1 + M) * (1 + M)
        * (1 + Work.Spaces.HkSq α 6 f) := by
    rw [hAeq]
    calc (C₁ * (4 * Real.sqrt C₀ * Work.FTS.Nonlin.Xn α f)) * Work.Spaces.HkSq α 6 f
        ≤ (C₁ * (4 * Real.sqrt C₀ * M)) * Work.Spaces.HkSq α 6 f :=
          mul_le_mul_of_nonneg_right hAM' hsq6nn
      _ = C₁ * (4 * Real.sqrt C₀) * (M * Work.Spaces.HkSq α 6 f) := by ring
      _ ≤ C₁ * (4 * Real.sqrt C₀)
            * ((1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)) :=
          mul_le_mul_of_nonneg_left hMS (by positivity)
      _ ≤ (C₁ * (4 * Real.sqrt C₀) + 1)
            * ((1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (C₁ * (4 * Real.sqrt C₀) + 1) * (1 + M) * (1 + M)
            * (1 + Work.Spaces.HkSq α 6 f) := by ring
  exact hbound.trans hgoal


end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

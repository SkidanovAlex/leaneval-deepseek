import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_RegExport.RXT.Sys.pert_tilde_contDiffOn
import Submission.Work.FTS_RegExport.RXT.Slots.v2_SlotJetsTendsto
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_RegExport.RXT.Slots.v2_thetaJetsTendsto
import Submission.Work.FTS_RegExport.RXT.Slots.v2_paramC2
import Submission.Work.FTS_RegExport.RXT.Slots.v2_hkMem_pointwise_min
import Submission.Work.FTS_RegExport.RXT.velPert
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.FinalV2.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.pth_vop_pert_tendsto` — the `∂_θ`-jet of `𝒱(Φ̃_n)` converges

For the perturbation residual `Φ̃(τ) = PhiTil (pExp α) (g(τ)) (E (g(τ)))` of the dynamic
modulation, the angular transport coefficient `𝒱(Φ̃) = ∂_θΦ̃ - tan θ · Φ̃` is bounded (in
`pth_vop_slot_bd`) by `max Ce 0 · α^{-1/2} · (max C₀ 0 · α²)`.  The liminf step of that bound is
taken along the class-`C` approximating sequence `gn` of the `LimApprox` clause of `DynOK'`,
and it needs exactly the statement proved here: for every point `(z,θ)` of the open quadrant
(`z > 0`, `0 < θ < π/2`) the `∂_θ`-jets of the coefficients
`𝒱(Φ̃_n)` — with `Φ̃_n = PhiTil (pExp α) (gn n (τ)) (E (gn n (τ)))` — converge to the
`∂_θ`-jet of the limit coefficient `𝒱(Φ̃)`.

## Route

1. `∂_θ𝒱(Φ̃) = D_θ(𝒱(Φ̃))/sin 2θ` on the open quadrant (`D_θ = sin 2θ · ∂_θ`), so it suffices
   to prove the convergence of the mixed jet `D_z^0 D_θ^1` of the *function*
   `(z,θ) ↦ 𝒱(Φ̃_n)(z,θ)`;
2. that is the `(j,i) = (0,1)` instance of the slot-convergence theorem
   `Slots.v2_SlotJetsTendsto`, whose hypotheses are the `C³`-regularity of the residuals and the
   convergence of their mixed jets up to order `3`;
3. the jets of the residual split as the difference of the jets of `E(gn n(τ))` and of
   `Θ(gn n(τ)) = (1/(4α)) sin 2θ · L₁₂(gn n(τ))`:
   * the `E`-jets converge by the limit closure `EllLimOK3` at order `3` (the limit clause of
     `LimApprox` at order `4` supplies its hypotheses), and `E` of the *approximants* is `C³`
     because `EllLimOK3` may also be applied to the constant sequence `n ↦ gn n(τ)` with itself
     as limit (a constant sequence converges trivially);
   * the `Θ`-jets converge by `Slots.v2_thetaJetsTendsto` from the convergence of the `D_z`-jets
     of `L₁₂(gn n(τ))` (`Slots.v2_L12DzIterTendsto`, whose pointwise bound is the trace-free
     `ℋ⁴ → L^∞` trade-off `RXA1w.abs_mixed_le_HkNorm_C4_w_proved`); the `C³`-regularity of `Θ`
     of a class-`C` datum is `ClassC.fsm` fed into `contDiffOn_three_L12`;
4. the `C³`-regularity of the *limit* residual is `pert_tilde_contDiffOn`, and that of `Θ` of
   the limit is obtained by subtraction from the former and `E` of the limit.
-/

namespace Work.FTS_RegExport.RXT.Sys

open scoped Real Topology
open Set Filter

set_option autoImplicit false

open Work.FTS.Galerkin (Fn Fam slice)

/-- `D_z^0D_θ^1f = sin(2θ)·∂_θf`: the plain `θ`-derivative is the mixed jet divided by
`sin(2θ)`. -/
private theorem pth_eq_mixed_zero_one_div {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hs : Real.sin (2 * θ) ≠ 0) :
    Work.Spaces.pth f z θ = Work.Spaces.mixed 0 1 f z θ / Real.sin (2 * θ) := by
  rw [show Work.Spaces.mixed 0 1 f z θ = Real.sin (2 * θ) * Work.Spaces.pth f z θ from by
    simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero, Work.Spaces.Dth]]
  field_simp

theorem pth_vop_pert_tendsto {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) S)
    {gn : ℕ → Work.FTS.Galerkin.Fam} {B : ℝ}
    (hApprox : ∀ n, ∀ σ ∈ Set.Icc (0 : ℝ) S,
      Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) σ) ∧
      Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) σ)
        ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2 ∧
      Work.FTS.StrongGlobal.Xn6 (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) σ) ≤ B)
    (hJet : ∀ σ ∈ Set.Icc (0 : ℝ) S, ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (gn n) σ) z θ)
        Filter.atTop (nhds (Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g σ) z θ))) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun n => Work.Spaces.pth (Work.Construction.Vop (fun z θ =>
          Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) τ)
            (E (Work.FTS.Galerkin.slice (gn n) τ)) z θ)) z θ)
        Filter.atTop
        (nhds (Work.Spaces.pth (Work.Construction.Vop (fun z θ =>
          Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice g τ)
            (E (Work.FTS.Galerkin.slice g τ)) z θ)) z θ)) := by
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hτ0 : (0 : ℝ) ≤ τ := hτ.1
  -- ## the data of the limit slice
  have hF4 : ContDiffOn ℝ 4 (Function.uncurry (slice g τ)) Work.FTS.EllipticEst.Q0 :=
    hOK.1.1.c4 τ hτ0
  -- ## the regularity of the class-`C` approximants
  have hReg : ∀ n : ℕ,
      ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ)) Work.FTS.EllipticEst.Q0 ∧
      Work.Spaces.HkMem (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ) ∧
      Work.FTS.Nonlin.BdryTraces (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ) ∧
      Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ)
        ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 := by
    intro n
    obtain ⟨hCn, hXn, _⟩ := hApprox n τ hτ
    have h2 : C₀ * (Work.FTS.Regularity.pExp α) ^ 2
        ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (sq_nonneg _)
    exact ⟨hCn.reg.of_le (by norm_num),
      Work.FTS.IPGen.HkMem_mono_le hCn.reg 4 (by norm_num) hCn.mem,
      hCn.bdry_le_six (by norm_num), le_trans hXn h2⟩
  -- ## the `E`-jets of the limit slice (order `3`); `E` of the limit is `C³`
  obtain ⟨_hBsl, hElim3, hEconv⟩ := hEL3 (fun n => slice (gn n) τ) (slice g τ) B
    (fun n => (hApprox n τ hτ).1) (fun n => (hApprox n τ hτ).2.2) hF4
    (fun j i hji z' θ' hzθ => hJet τ hτ j i hji z' θ' hzθ)
  -- ## `E` of the approximants is `C³` (the constant-sequence instance of `EllLimOK3`)
  have hΦ3c : ∀ n : ℕ, ContDiffOn ℝ 3
      (Function.uncurry (fun z θ => E (slice (gn n) τ) z θ)) Work.FTS.EllipticEst.Q0 := by
    intro n
    exact (hEL3 (fun _ => slice (gn n) τ) (slice (gn n) τ) B
      (fun _ => (hApprox n τ hτ).1) (fun _ => (hApprox n τ hτ).2.2)
      (hReg n).1
      (fun j i hji z' θ' hzθ => tendsto_const_nhds)).2.1
  -- ## `Θ` of a class-`C` datum is `C³` (all-order smoothness of the angular moment)
  have hΘ3 : ∀ n : ℕ, ContDiffOn ℝ 3 (Function.uncurry
      (Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice (gn n) τ)))
      Work.FTS.EllipticEst.Q0 := by
    intro n
    refine velPert_contDiffOn_Theta (α := Work.FTS.Regularity.pExp α) ?_
    refine contDiffOn_three_L12 ?_
    have h1 : ContDiffOn ℝ 2 (fun z => 3 * Work.Elliptic.Fstar (slice (gn n) τ) z) (Set.Ioi 0) :=
      contDiffOn_const.mul ((hApprox n τ hτ).1.fsm 2)
    refine h1.congr fun z' _ => ?_
    rw [velPert_FK_eq]
  -- ## the residual `Φ̃_n = E(gn n(τ)) - Θ(gn n(τ))` is `C³`
  have hΞ3 : ∀ n : ℕ, ContDiffOn ℝ 3 (Function.uncurry (fun z θ =>
      Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
        (E (slice (gn n) τ)) z θ)) Work.FTS.EllipticEst.Q0 := by
    intro n
    refine ((hΦ3c n).sub (hΘ3 n)).congr fun p _ => ?_
    rcases p with ⟨z', θ'⟩
    simp only [Function.uncurry, Pi.sub_apply, Work.Construction.PhiTil]
  -- ## the limit residual and `Θ` of the limit
  have hΞ3lim : ContDiffOn ℝ 3 (Function.uncurry (fun z θ =>
      Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
        (E (slice g τ)) z θ)) Work.FTS.EllipticEst.Q0 :=
    pert_tilde_contDiffOn hα hα13 hEL3 hOK τ hτ0
  have hΘ3lim : ContDiffOn ℝ 3 (Function.uncurry
      (Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice g τ)))
      Work.FTS.EllipticEst.Q0 := by
    refine ((hElim3.sub hΞ3lim)).congr fun p _ => ?_
    rcases p with ⟨z', θ'⟩
    simp only [Function.uncurry, Pi.sub_apply, Work.Construction.PhiTil]
    ring
  -- ## the trace-free `ℋ⁴ → L^∞` trade-off for the approximants
  obtain ⟨CA1, hCA10, hA1⟩ := Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved hαG hαG1
  -- ## the `D_z`-jets of `L₁₂` converge
  have hL12jets : ∀ j : ℕ, j ≤ 3 → ∀ z' : ℝ, 0 < z' →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.DzIter j
          (fun z _ => Work.Construction.L12 (slice (gn n) τ) z) z' 0) Filter.atTop
        (nhds (Work.Spaces.DzIter j
          (fun z _ => Work.Construction.L12 (slice g τ) z) z' 0)) := by
    intro j hj z' hz'
    refine Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
      (C0 := CA1 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2))
      (F := fun n => slice (gn n) τ) (G := slice g τ) (by positivity) ?_ hF4 ?_ ?_ j hj z' hz'
    · intro n; exact (hReg n).1
    · intro n b a hba z'' θ'' hz'' hθ'' hθ''2
      have h1 := hA1 (slice (gn n) τ) (hReg n).1 (hReg n).2.1 (hReg n).2.2.1 b a hba
        z'' θ'' hz'' hθ'' hθ''2
      have h2 : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ)
          ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 := (hReg n).2.2.2
      have hA0 : 0 ≤ CA1 * (z'' ^ ((3 : ℝ) / 2) / (1 + z'') ^ 2) :=
        mul_nonneg hCA10 (div_nonneg (Real.rpow_nonneg hz''.le _) (by positivity))
      calc |Work.Spaces.mixed b a (slice (gn n) τ) z'' θ''|
          ≤ CA1 * (z'' ^ ((3 : ℝ) / 2) / (1 + z'') ^ 2)
              * Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ) := h1
        _ ≤ CA1 * (z'' ^ ((3 : ℝ) / 2) / (1 + z'') ^ 2)
              * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) :=
            mul_le_mul_of_nonneg_left h2 hA0
        _ = CA1 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2)
              * (z'' ^ ((3 : ℝ) / 2) / (1 + z'') ^ 2) := by ring
    · intro b a hab z'' θ'' hz'' hθ'' hθ''2
      exact hJet τ hτ b a (by omega) z'' θ'' ⟨hz'', hθ'', hθ''2⟩
  -- ## the `Θ`-jets converge
  have hΘconv := Work.FTS_RegExport.RXT.Slots.v2_thetaJetsTendsto
    (α := Work.FTS.Regularity.pExp α) (F := fun n => slice (gn n) τ) (G := slice g τ) hL12jets
  -- ## the residual jets converge (difference of the two families)
  have hΞconv : ∀ b a : ℕ, a + b ≤ 3 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed b a (fun z θ =>
          Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            (E (slice (gn n) τ)) z θ) z' θ') Filter.atTop
        (nhds (Work.Spaces.mixed b a (fun z θ =>
          Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ)) z θ) z' θ')) := by
    intro b a hba z' θ' hz' hθ' hθ'2
    have hfun : (fun n : ℕ => Work.Spaces.mixed b a (fun z θ =>
          Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            (E (slice (gn n) τ)) z θ) z' θ')
        = fun n : ℕ => Work.Spaces.mixed b a (fun z θ => E (slice (gn n) τ) z θ) z' θ'
            - Work.Spaces.mixed b a (fun z θ =>
                Work.Construction.Theta (Work.FTS.Regularity.pExp α)
                  (slice (gn n) τ) z θ) z' θ' := by
      funext n
      exact velPert_mixed_sub_three (b := b) (a := a) hba (hΦ3c n) (hΘ3 n) hz' hθ' hθ'2
    have hlim : Work.Spaces.mixed b a (fun z θ =>
          Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ)) z θ) z' θ'
        = Work.Spaces.mixed b a (fun z θ => E (slice g τ) z θ) z' θ'
            - Work.Spaces.mixed b a (fun z θ =>
                Work.Construction.Theta (Work.FTS.Regularity.pExp α)
                  (slice g τ) z θ) z' θ' :=
      velPert_mixed_sub_three (b := b) (a := a) hba hElim3 hΘ3lim hz' hθ' hθ'2
    rw [hfun, hlim]
    exact (hEconv b a (by omega) z' θ' ⟨hz', hθ', hθ'2⟩).sub
      (hΘconv b a (by omega) z' θ' hz' hθ' hθ'2)
  -- ## the mixed jets of the transport coefficient `𝒱(Φ̃)`
  have hslot := Work.FTS_RegExport.RXT.Slots.v2_SlotJetsTendsto (α := Work.FTS.Regularity.pExp α)
    (Ξ := fun n => fun z θ => Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
      (slice (gn n) τ) (E (slice (gn n) τ)) z θ)
    (Ξlim := fun z θ => Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
      (slice g τ) (E (slice g τ)) z θ) hΞ3 hΞ3lim hΞconv
  -- ## the plain `∂_θ`-jet
  intro z θ hz hθ hθ2
  have hs : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  have hVop := (hslot 0 1 (by norm_num) z θ hz hθ hθ2).2.1
  have e1 : (fun n : ℕ => Work.Spaces.pth (Work.Construction.Vop (fun z θ =>
      Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
        (E (slice (gn n) τ)) z θ)) z θ)
      = fun n : ℕ => Work.Spaces.mixed 0 1 (Work.Construction.Vop (fun z θ =>
      Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
        (E (slice (gn n) τ)) z θ)) z θ / Real.sin (2 * θ) := by
    funext n
    exact pth_eq_mixed_zero_one_div hs
  have e2 : Work.Spaces.pth (Work.Construction.Vop (fun z θ =>
      Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
        (E (slice g τ)) z θ)) z θ
      = Work.Spaces.mixed 0 1 (Work.Construction.Vop (fun z θ =>
      Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
        (E (slice g τ)) z θ)) z θ / Real.sin (2 * θ) := pth_eq_mixed_zero_one_div hs
  rw [e1, e2]
  exact hVop.div_const _

end Work.FTS_RegExport.RXT.Sys

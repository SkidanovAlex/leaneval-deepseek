import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.FTS_RegExport.RXT.Slots.v2_velPert
import Submission.Work.FTS_RegExport.RXT.Slots.v2_SlotJetsTendsto
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_RegExport.RXT.Slots.v2_thetaJetsTendsto
import Submission.Work.FTS_RegExport.RXT.Slots.v2_paramC2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT.SysAux

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# `Work.FTS_RegExport.RXT.SysAux.pertSlot_tendsto`

The three perturbation slots `ℛ(Φ̃)`, `𝒱(Φ̃)`, `𝒰(Φ̃)/sin 2θ` of the residual
`Φ̃(τ) = PhiTil (pExp α) (g(τ)) (E (g(τ)))` converge pointwise along the class-`C`
approximating sequence `gn` of the `LimApprox` clause of `DynOK'`.

The proof is the jet-convergence block of `RXT.Slots.v2_velPert` (which computes convergence
of the mixed jets of `Φ̃(τ)` to order `3` from `EllLimOK3` for the `E`-part and from the
`L₁₂`-tower for the singular part `Θ = (1/(4α))·sin 2θ·L₁₂`), followed by
`Slots.v2_SlotJetsTendsto` at order `(0,0)` (every slot is a combination
`a(θ)·Ψ + b(θ)·D_zΨ + c(θ)·∂_θΨ`, whose *value* is a function of the jets of order `≤ 1`,
the `∂_θ`-factor being `D_θΨ/sin 2θ`).
-/

theorem pertSlot_tendsto {α Ce C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S) {gn : ℕ → Work.FTS.Galerkin.Fam} {B : ℝ}
    (hApprox : ∀ (n : ℕ), ∀ τ ∈ Set.Icc (0:ℝ) S,
      Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) τ) ∧
      Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) τ)
        ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2 ∧
      Work.FTS.StrongGlobal.Xn6 (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) τ) ≤ B)
    (hJet : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (gn n) τ) z θ)
        Filter.atTop (nhds (Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0:ℝ) S) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Filter.Tendsto (fun n : ℕ => Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) τ)
            (E (Work.FTS.Galerkin.slice (gn n) τ))) z θ) Filter.atTop
        (nhds (Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice g τ)
            (E (Work.FTS.Galerkin.slice g τ))) z θ))) ∧
      (Filter.Tendsto (fun n : ℕ => Work.Construction.Vop
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) τ)
            (E (Work.FTS.Galerkin.slice (gn n) τ))) z θ) Filter.atTop
        (nhds (Work.Construction.Vop
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice g τ)
            (E (Work.FTS.Galerkin.slice g τ))) z θ))) ∧
      (Filter.Tendsto (fun n : ℕ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) τ)
            (E (Work.FTS.Galerkin.slice (gn n) τ))) z θ / Real.sin (2 * θ)) Filter.atTop
        (nhds (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice g τ)
            (E (Work.FTS.Galerkin.slice g τ))) z θ / Real.sin (2 * θ)))) := by
  intro z θ hz hθ hθ2
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- the two trace-free `ℋ⁴ → L^∞` trade-offs
  obtain ⟨CA1, hCA10, hA1⟩ := Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved hαG hαG1
  obtain ⟨C4, hC40, hC4⟩ := Work.FTS_RegExport.RXT.velPert_hkMem_bound hαG hαG1
  -- ## regularity of the class-`C` approximants
  have hReg : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ))
        Work.FTS.EllipticEst.Q0 ∧ Work.Spaces.HkMem (Work.FTS.Regularity.pExp α) 4
          (slice (gn n) τ) ∧
      Work.FTS.Nonlin.BdryTraces (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ) ∧
      Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ)
        ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 := by
    intro n
    obtain ⟨hCn, hXn, _⟩ := hApprox n τ hτ
    have h2 : C₀ * (Work.FTS.Regularity.pExp α) ^ 2
        ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (sq_nonneg (Work.FTS.Regularity.pExp α))
    exact ⟨hCn.reg.of_le (by norm_num),
      Work.FTS.IPGen.HkMem_mono_le hCn.reg 4 (by norm_num) hCn.mem,
      hCn.bdry_le_six (by norm_num), le_trans hXn h2⟩
  -- ## the limit slice and its data
  have hF4 : ContDiffOn ℝ 4 (Function.uncurry (slice g τ)) Work.FTS.EllipticEst.Q0 :=
    hOK.1.1.c4 τ hτ.1
  have hFmem : Work.Spaces.HkMem (Work.FTS.Regularity.pExp α) 4 (slice g τ) :=
    hOK.1.1.mem4 τ hτ.1
  have hFnorm : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (slice g τ)
      ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 := by
    have h2 : C₀ * (Work.FTS.Regularity.pExp α) ^ 2
        ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (sq_nonneg (Work.FTS.Regularity.pExp α))
    exact le_trans (hOK.1.2 τ hτ.1) h2
  -- ## the `E`-jets of the limit slice
  obtain ⟨_hBsl, hE3lim, hEconv⟩ := hEL3 (fun n => slice (gn n) τ) (slice g τ) B
    (fun n => (hApprox n τ hτ).1) (fun n => (hApprox n τ hτ).2.2) hF4
    (fun j i hji z' θ' hzθ => hJet τ hτ j i hji z' θ' hzθ)
  -- ## `𝔽K` and `L₁₂` of the limit slice
  have hFKlim : ContDiffOn ℝ 2 (Work.Construction.FK (slice g τ)) (Set.Ioi 0) := by
    have hF2 : ContDiffOn ℝ 2 (Function.uncurry (slice g τ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hF4.of_le (by norm_num)
    have hbase : ∀ (b : ℕ), b ≤ 2 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
        |Work.Spaces.mixed b 0 (slice g τ) z' θ'|
          ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) := by
      intro b hb z' θ' hz' hθ' hθ'2
      have h1 := hC4 (slice g τ) (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) hF4 hFmem
        hFnorm b 0 (by omega) z' θ' hz' hθ' hθ'2
      have h2 : C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) * min z' 1
          ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left (min_le_right _ _)
          (mul_nonneg hC40 (mul_nonneg (le_max_right C₀ 0)
            (sq_nonneg (Work.FTS.Regularity.pExp α))))
      linarith [h1, h2]
    have hb : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
        |slice g τ z' θ'| ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) ∧
        |Work.Spaces.Dz (slice g τ) z' θ'|
          ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) ∧
        |Work.Spaces.DzIter 2 (slice g τ) z' θ'|
          ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) :=
      fun z' θ' hz' hθ' hθ'2 =>
        ⟨by simpa using hbase 0 (by norm_num) z' θ' hz' hθ' hθ'2,
         by simpa using hbase 1 (by norm_num) z' θ' hz' hθ' hθ'2,
         by simpa using hbase 2 (by norm_num) z' θ' hz' hθ' hθ'2⟩
    exact Work.FTS_RegExport.RXT.Slots.v2_paramC2 (φ := Work.Spaces.K)
      (C := C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2))
      Work.FTS_RegExport.RXT.velPert_continuousOn_K hF2 hb
  have hL12lim : ContDiffOn ℝ 3 (Work.Construction.L12 (slice g τ)) (Set.Ioi 0) :=
    Work.FTS_RegExport.RXT.contDiffOn_three_L12 hFKlim
  have hΘ3lim : ContDiffOn ℝ 3
      (Function.uncurry (Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice g τ)))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.velPert_contDiffOn_Theta (α := Work.FTS.Regularity.pExp α) hL12lim
  have hElim3 : ContDiffOn ℝ 3 (Function.uncurry (fun z θ => E (slice g τ) z θ))
      Work.FTS.EllipticEst.Q0 := hE3lim
  -- ## `𝔽K`-jets of the approximants and the `Θ`-jets
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
  have hΘconv : ∀ j i : ℕ, j + i ≤ 3 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' →
      θ' < Real.pi / 2 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i
          (Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice (gn n) τ)) z' θ')
        Filter.atTop
        (nhds (Work.Spaces.mixed j i
          (Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice g τ)) z' θ')) :=
    Work.FTS_RegExport.RXT.Slots.v2_thetaJetsTendsto (α := Work.FTS.Regularity.pExp α)
      (F := fun n => slice (gn n) τ) (G := slice g τ) hL12jets
  -- ## `C³`-regularity of the residuals
  have hΦ3 : ∀ n : ℕ, ContDiffOn ℝ 3
      (Function.uncurry (fun z θ => E (slice (gn n) τ) z θ)) Work.FTS.EllipticEst.Q0 := by
    intro n
    exact ((hEll _ (hApprox n τ hτ).1).1.smooth).of_le (by norm_num)
  have hΘ3 : ∀ n : ℕ, ContDiffOn ℝ 3 (Function.uncurry
      (Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice (gn n) τ)))
      Work.FTS.EllipticEst.Q0 := by
    intro n
    refine Work.FTS_RegExport.RXT.velPert_contDiffOn_Theta
      (α := Work.FTS.Regularity.pExp α) ?_
    refine Work.FTS_RegExport.RXT.contDiffOn_three_L12 ?_
    have h1 : ContDiffOn ℝ 2 (fun z => 3 * Work.Elliptic.Fstar (slice (gn n) τ) z)
        (Set.Ioi 0) := contDiffOn_const.mul ((hApprox n τ hτ).1.fsm 2)
    refine h1.congr fun z' _ => ?_
    rw [Work.FTS_RegExport.RXT.velPert_FK_eq]
  have hΞ3 : ∀ n : ℕ, ContDiffOn ℝ 3 (Function.uncurry (fun z θ =>
      Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
        (E (slice (gn n) τ)) z θ)) Work.FTS.EllipticEst.Q0 := by
    intro n
    refine ((hΦ3 n).sub (hΘ3 n)).congr fun p _ => ?_
    rcases p with ⟨z', θ'⟩
    simp only [Function.uncurry, Pi.sub_apply, Work.Construction.PhiTil]
  have hΞ3lim : ContDiffOn ℝ 3 (Function.uncurry (fun z θ =>
      Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
        (E (slice g τ)) z θ)) Work.FTS.EllipticEst.Q0 := by
    refine ((hElim3.sub hΘ3lim)).congr fun p _ => ?_
    rcases p with ⟨z', θ'⟩
    simp only [Function.uncurry, Pi.sub_apply, Work.Construction.PhiTil]
  -- ## the jets of the residuals converge
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
                Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice (gn n) τ) z θ)
                z' θ' := by
      funext n
      exact Work.FTS_RegExport.RXT.velPert_mixed_sub_three (b := b) (a := a) hba
        (hΦ3 n) (hΘ3 n) hz' hθ' hθ'2
    have hlim : Work.Spaces.mixed b a (fun z θ =>
          Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ)) z θ) z' θ'
        = Work.Spaces.mixed b a (fun z θ => E (slice g τ) z θ) z' θ'
            - Work.Spaces.mixed b a (fun z θ =>
                Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice g τ) z θ)
                z' θ' :=
      Work.FTS_RegExport.RXT.velPert_mixed_sub_three (b := b) (a := a) hba hElim3 hΘ3lim
        hz' hθ' hθ'2
    rw [hfun, hlim]
    exact (hEconv b a (by omega) z' θ' ⟨hz', hθ', hθ'2⟩).sub
      (hΘconv b a (by omega) z' θ' hz' hθ' hθ'2)
  -- ## the slot values converge: `Slots.v2_SlotJetsTendsto` at order `(0,0)`
  have hslot := Work.FTS_RegExport.RXT.Slots.v2_SlotJetsTendsto
    (α := Work.FTS.Regularity.pExp α)
    (Ξ := fun n => fun z θ => Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
      (slice (gn n) τ) (E (slice (gn n) τ)) z θ)
    (Ξlim := fun z θ => Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
      (slice g τ) (E (slice g τ)) z θ) hΞ3 hΞ3lim hΞconv 0 0 (by norm_num) z θ hz hθ hθ2
  exact ⟨by simpa using hslot.1, by simpa using hslot.2.1, by simpa using hslot.2.2⟩

end Work.FTS_RegExport.RXT.SysAux

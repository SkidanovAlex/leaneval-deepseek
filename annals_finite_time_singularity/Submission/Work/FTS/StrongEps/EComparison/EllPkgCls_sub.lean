/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EComparison/EllPkgCls_sub.lean`

The closure of `EllPkgCls` under differences (see the module headers of
`EllPkgClsSliceAux.lean` / `EllPkgClsVop.lean` for the strategy).  The `pz`-split of the
`PhiTil`s — the only non-formal input, since `SmoothOpen Ψ` alone does not make `PhiTil α F Ψ`
smooth — is supplied by the `V`-slot via `differentiableAt_L12_of_Vop`; the `α = 0` case is
degenerate and is handled by `EllPkgCls_sub_zero`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EComparison.Reduction
import Submission.Work.FTS.StrongEps.EComparison.EllPkgClsSlots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The class `EllPkgCls` is closed under differences.**  If `(F₁, Ψ₁)` and `(F₂, Ψ₂)` are both
controlled by the packages, and the `L₁₂`-part of the source is additive
(`Theta α (F₁ - F₂) = Theta α F₁ - Theta α F₂` on the half-line `z ∈ Iz`, which is the content of
the delegated `EComparison.L12_sub_HkMem`), then so is the pair
`(F₁ - F₂, Ψ₁ - Ψ₂)`.

`EllPkgCls α Ce F Ψ` (in `Submission.Work.FTS.StrongEps.EComparison.Reduction`) is the membership
half of the two elliptic packages, with the packages' slot shape kept: `SmoothOpen Ψ`, the elliptic
law `IsBslSol α F Ψ`, and `HQo α 6` of `Rop α (PhiTil α F Ψ)`, of `Uop α (PhiTil α F Ψ) / sin 2θ`
and of `Vop (PhiTil α F Ψ)` (`HQo α 6 X = SmoothOpen X ∧ HkMem α 6 X`).  (An earlier form of the
class dropped the smoothness halves; a review pointed out that this blocks the closure, so the
`HQo` slots are the ones to use.)

Ingredients (all on disk, `sorry`-free):
* `SmoothOpen` is closed under subtraction (`Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_sub'`);
* `IsBslSol α (F₁ - F₂) (Ψ₁ - Ψ₂)` from `IsBslSol α F₁ Ψ₁`, `IsBslSol α F₂ Ψ₂`: the pointwise law is
  `Work.FTS.EllipticEst.bslOp_sub` (the `C²`-at-a-point hypotheses come from `SmoothOpen` of the two
  stream functions at a point of the open quadrant, and `Real.cos θ ≠ 0` holds there), and the two
  Dirichlet conjuncts and the `z`-decay conjunct are difference-stable;
* the three `ℋ⁶`-memberships and their smoothness: `PhiTil α (F₁ - F₂) (Ψ₁ - Ψ₂) = PhiTil α F₁ Ψ₁ -
  PhiTil α F₂ Ψ₂` by the hypothesis on `Theta` (and only on `z > 0`, where it is needed: the weights
  `Work.Spaces.w` and `Work.Spaces.Wt` vanish at `z = 0`, so `HkIntegrand α k f 0 θ = 0` for every
  `f`, and `HkSq α k`/`HkMem α k` see only `z ∈ Iz`), and `Rop α`, `Uop α`, `Vop` are additive in
  their argument at every point of the open quadrant.  The `pz`-additivity is *not* a consequence
  of the smoothness of the two `PhiTil`s (their `z`-regularity is not available: the `L₁₂`-part is
  an integral of the source over `(z,∞)`); it is supplied here by the `V`-slot, whose smoothness
  forces `z ↦ L₁₂(Fᵢ)(z)` to be differentiable on `(0,∞)` (`differentiableAt_L12_of_Vop`), and
  hence the `z`-derivative of `PhiTil α (F₁-F₂)(Ψ₁-Ψ₂)` to split.  `HQo α 6` of the difference then
  follows from `HQo α 6` of the two summands (`smoothOpen_sub_bsl` for the smoothness,
  `HkMem_sub_of_HkMem` for the membership, plus the open-quadrant congruence
  `Cert.GbarSin.HkMem_congr_Q0`).  The case `α = 0` is degenerate (`Theta 0 F = 0`, so
  `PhiTil 0 F Ψ = Ψ`) and is handled by `EllPkgCls_sub_zero`. -/
theorem EllPkgCls_sub {α Ce : ℝ} {F₁ F₂ Ψ₁ Ψ₂ : Work.FTS.Galerkin.Fn}
    (h₁ : Work.FTS.StrongEps.EComparison.EllPkgCls α Ce F₁ Ψ₁)
    (h₂ : Work.FTS.StrongEps.EComparison.EllPkgCls α Ce F₂ Ψ₂)
    (hΘ : ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      Work.Construction.Theta α (fun z θ => F₁ z θ - F₂ z θ) z θ
        = Work.Construction.Theta α F₁ z θ - Work.Construction.Theta α F₂ z θ) :
    Work.FTS.StrongEps.EComparison.EllPkgCls α Ce
      (fun z θ => F₁ z θ - F₂ z θ) (fun z θ => Ψ₁ z θ - Ψ₂ z θ) := by
  rcases eq_or_ne α 0 with hα0 | hαne
  · subst hα0
    exact EllPkgCls_sub_zero h₁ h₂
  · set A : Fn := Work.Construction.PhiTil α (fun z θ => F₁ z θ - F₂ z θ)
      (fun z θ => Ψ₁ z θ - Ψ₂ z θ) with hA
    set P₁ : Fn := Work.Construction.PhiTil α F₁ Ψ₁ with hP₁
    set P₂ : Fn := Work.Construction.PhiTil α F₂ Ψ₂ with hP₂
    -- the value identity `A = P₁ - P₂` on the open half-line
    have hAeq : ∀ z, 0 < z → ∀ θ, A z θ = P₁ z θ - P₂ z θ := by
      intro z hz θ
      rw [hA, hP₁, hP₂]
      simp only [Work.Construction.PhiTil]
      rw [hΘ z (Set.mem_Ici.mpr (le_of_lt hz)) θ]
      ring
    -- the `L₁₂`-differentiabilities on `(0,∞)`, from the `V`-slots
    have hd₁ : ∀ z, 0 < z → DifferentiableAt ℝ (fun z' => Work.Construction.L12 F₁ z') z :=
      fun z hz => differentiableAt_L12_of_Vop hαne h₁.1 h₁.2.2.2.2.1 hz
    have hd₂ : ∀ z, 0 < z → DifferentiableAt ℝ (fun z' => Work.Construction.L12 F₂ z') z :=
      fun z hz => differentiableAt_L12_of_Vop hαne h₂.1 h₂.2.2.2.2.1 hz
    have hlin : ∀ z, 0 < z → Work.Construction.L12 (fun z θ => F₁ z θ - F₂ z θ) z
        = Work.Construction.L12 F₁ z - Work.Construction.L12 F₂ z :=
      fun z hz => L12_sub_of_Theta hαne hΘ z (Set.mem_Ioi.mpr hz)
    have hu₁ : ∀ z, 0 < z → DifferentiableAt ℝ
        (fun z' => (1 / (4 * α)) * Work.Construction.L12 F₁ z') z :=
      fun z hz => (hd₁ z hz).const_mul _
    have hu₂ : ∀ z, 0 < z → DifferentiableAt ℝ
        (fun z' => (1 / (4 * α)) * Work.Construction.L12 F₂ z') z :=
      fun z hz => (hd₂ z hz).const_mul _
    have huU : ∀ z, 0 < z → DifferentiableAt ℝ
        (fun z' => (1 / (4 * α))
          * Work.Construction.L12 (fun z θ => F₁ z θ - F₂ z θ) z') z := by
      intro z hz
      refine (((hd₁ z hz).sub (hd₂ z hz)).const_mul (1 / (4 * α))).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      simp only [Pi.sub_apply]
      rw [hlin z' (Set.mem_Ioi.mp hz')]
    -- the `z`-derivative split on the open quadrant
    have hsplit_z : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
        Work.Spaces.pz A z θ = Work.Spaces.pz P₁ z θ - Work.Spaces.pz P₂ z θ := by
      intro z θ hz h0 h1
      have hA' : Work.Spaces.pz A z θ
          = Work.Spaces.pz (fun z θ => Ψ₁ z θ - Ψ₂ z θ) z θ
            - deriv (fun z' => (1 / (4 * α)) * Real.sin (2 * θ)
                * Work.Construction.L12 (fun z θ => F₁ z θ - F₂ z θ) z') z := by
        rw [hA]
        exact pz_PhiTil_eq (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_sub' h₁.1 h₂.1)
          (huU z hz) hz h0 h1
      have hP₁' : Work.Spaces.pz P₁ z θ
          = Work.Spaces.pz Ψ₁ z θ
            - deriv (fun z' => (1 / (4 * α)) * Real.sin (2 * θ)
                * Work.Construction.L12 F₁ z') z := by
        rw [hP₁]
        exact pz_PhiTil_eq h₁.1 (hu₁ z hz) hz h0 h1
      have hP₂' : Work.Spaces.pz P₂ z θ
          = Work.Spaces.pz Ψ₂ z θ
            - deriv (fun z' => (1 / (4 * α)) * Real.sin (2 * θ)
                * Work.Construction.L12 F₂ z') z := by
        rw [hP₂]
        exact pz_PhiTil_eq h₂.1 (hu₂ z hz) hz h0 h1
      -- the `z`-derivative of the `L₁₂`-slot splits
      have hdU : DifferentiableAt ℝ (fun z' => Work.Construction.L12
          (fun z θ => F₁ z θ - F₂ z θ) z') z := by
        refine ((hd₁ z hz).sub (hd₂ z hz)).congr_of_eventuallyEq ?_
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        simp only [Pi.sub_apply]
        exact hlin z' (Set.mem_Ioi.mp hz')
      have hB₁ : DifferentiableAt ℝ (fun z' => (1 / (4 * α)) * Real.sin (2 * θ)
          * Work.Construction.L12 F₁ z') z :=
        ((hu₁ z hz).const_mul (Real.sin (2 * θ))).congr_of_eventuallyEq
          (Filter.Eventually.of_forall (fun z' => by ring))
      have hB₂ : DifferentiableAt ℝ (fun z' => (1 / (4 * α)) * Real.sin (2 * θ)
          * Work.Construction.L12 F₂ z') z :=
        ((hu₂ z hz).const_mul (Real.sin (2 * θ))).congr_of_eventuallyEq
          (Filter.Eventually.of_forall (fun z' => by ring))
      have hBU : DifferentiableAt ℝ (fun z' => (1 / (4 * α)) * Real.sin (2 * θ)
          * Work.Construction.L12 (fun z θ => F₁ z θ - F₂ z θ) z') z :=
        ((huU z hz).const_mul (Real.sin (2 * θ))).congr_of_eventuallyEq
          (Filter.Eventually.of_forall (fun z' => by ring))
      have hevU : (fun z' => (1 / (4 * α)) * Real.sin (2 * θ)
            * Work.Construction.L12 (fun z θ => F₁ z θ - F₂ z θ) z')
          =ᶠ[𝓝 z] (fun z' => (1 / (4 * α)) * Real.sin (2 * θ) * Work.Construction.L12 F₁ z')
            - (fun z' => (1 / (4 * α)) * Real.sin (2 * θ) * Work.Construction.L12 F₂ z') := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        simp only [Pi.sub_apply]
        rw [hlin z' (Set.mem_Ioi.mp hz')]
        ring
      rw [hA', hP₁', hP₂', pz_sub h₁.1 h₂.1 hz h0 h1, hevU.deriv_eq, deriv_sub hB₁ hB₂]
      ring
    -- the `θ`-derivative split on the open quadrant
    have hsplit_t : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
        Work.Spaces.pth A z θ = Work.Spaces.pth P₁ z θ - Work.Spaces.pth P₂ z θ := by
      intro z θ hz h0 h1
      have hA' : Work.Spaces.pth A z θ
          = Work.Spaces.pth (fun z θ => Ψ₁ z θ - Ψ₂ z θ) z θ
            - deriv (fun θ' => (1 / (4 * α)) * Real.sin (2 * θ')
                * Work.Construction.L12 (fun z θ => F₁ z θ - F₂ z θ) z) θ := by
        rw [hA]
        exact pth_PhiTil_eq (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_sub' h₁.1 h₂.1)
          hz h0 h1
      have hP₁' : Work.Spaces.pth P₁ z θ
          = Work.Spaces.pth Ψ₁ z θ
            - deriv (fun θ' => (1 / (4 * α)) * Real.sin (2 * θ')
                * Work.Construction.L12 F₁ z) θ := by
        rw [hP₁]
        exact pth_PhiTil_eq h₁.1 hz h0 h1
      have hP₂' : Work.Spaces.pth P₂ z θ
          = Work.Spaces.pth Ψ₂ z θ
            - deriv (fun θ' => (1 / (4 * α)) * Real.sin (2 * θ')
                * Work.Construction.L12 F₂ z) θ := by
        rw [hP₂]
        exact pth_PhiTil_eq h₂.1 hz h0 h1
      rw [hA', hP₁', hP₂', pth_sub h₁.1 h₂.1 hz h0 h1,
        deriv_const_sin_two_mul, deriv_const_sin_two_mul, deriv_const_sin_two_mul,
        hlin z hz]
      ring
    obtain ⟨hsR, hsU, hsV⟩ := slot_identities (α := α) (A := A) (P₁ := P₁) (P₂ := P₂)
      (fun z θ hz h0 h1 => hAeq z hz θ) hsplit_z hsplit_t
    refine ⟨Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_sub' h₁.1 h₂.1, ?_, ?_, ?_, ?_⟩
    · -- the elliptic law
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro z hz θ h0 h1
        have hc : Real.cos θ ≠ 0 :=
          ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩)
        have hC2₁ : ContDiffAt ℝ 2 (Function.uncurry Ψ₁) (z, θ) :=
          (h₁.1.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds ⟨hz, h0, h1⟩)
        have hC2₂ : ContDiffAt ℝ 2 (Function.uncurry Ψ₂) (z, θ) :=
          (h₂.1.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds ⟨hz, h0, h1⟩)
        rw [Work.FTS.EllipticEst.bslOp_sub α Ψ₁ Ψ₂ z θ hc hC2₁ hC2₂,
          h₁.2.1.1 z hz θ h0 h1, h₂.2.1.1 z hz θ h0 h1]
      · intro z
        show Ψ₁ z 0 - Ψ₂ z 0 = 0
        rw [h₁.2.1.2.1 z, h₂.2.1.2.1 z]
        ring
      · intro z
        show Ψ₁ z (π / 2) - Ψ₂ z (π / 2) = 0
        rw [h₁.2.1.2.2.1 z, h₂.2.1.2.2.1 z]
        ring
      · intro θ hθ
        simpa using (h₁.2.1.2.2.2 θ hθ).sub (h₂.2.1.2.2.2 θ hθ)
    · -- the `ℛ`-slot
      exact HQo_sub_of_slot 6 h₁.2.2.1 h₂.2.2.1
        (fun z θ hz h0 h1 => (hsR z θ hz h0 h1).symm)
    · -- the `U`-slot
      refine HQo_sub_of_slot 6 h₁.2.2.2.1 h₂.2.2.2.1 (fun z θ hz h0 h1 => ?_)
      rw [← sub_div, ← hsU z θ hz h0 h1]
    · -- the `V`-slot
      exact HQo_sub_of_slot 6 h₁.2.2.2.2 h₂.2.2.2.2
        (fun z θ hz h0 h1 => (hsV z θ hz h0 h1).symm)

end Work.FTS.StrongEps.EComparison

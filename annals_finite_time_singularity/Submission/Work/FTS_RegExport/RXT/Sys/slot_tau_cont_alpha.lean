import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_RegExport.RXT.velVanish2Aux
import Submission.Work.FTS_RegExport.RXT.velVanish2
import Submission.Work.FTS_RegExport.RXT.Slots.v2_velPert
import Submission.Work.FTS_RegExport.RXT.SysAux.pertSlot_lip_approx
import Submission.Work.FTS_RegExport.RXT.SysAux.pertSlot_tendsto
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS_RegExport.RXR5.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set Filter
open scoped Topology Real

namespace Work.FTS_RegExport.RXT.Sys

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-!
# `Work.FTS_RegExport.RXT.Sys.slot_tau_cont_alpha`

**C3 of the `Sys/coeff_jets` plan**: the three transport slots `ℛ(Φ̃_τ)`, `𝒱(Φ̃_τ)`,
`𝒰(Φ̃_τ)/sin 2θ` of the modulated residual `Φ̃_τ = PhiTil (pExp α) (F_* + g(τ)) (Φs + E(g(τ)))`
depend continuously on the fake time `τ` on every horizon `[0,S]`, at every point `(z,θ)` of the
open quadrant.

The route (documented in `Submission/Work/FTS_RegExport/RXT/Sys/NOTES_coeff_jets.md`):

* on the open quadrant the residual splits as `Φ̃_τ = Φ̃_* + Ξ_τ` with `Φ̃_* = PhiTil F_* Φs`
  independent of `τ` (`v2_phiTil_split`) and `Ξ_τ = PhiTil (g(τ)) (E(g(τ)))`; the three slots are
  additive on the quadrant (`v2_rop_add_at`/`v2_vop_add_at`/`v2_uop_div_add_at`), so it suffices to
  treat `Ξ_τ`;
* `Ξ_τ` is approximated by the class-`C` sequence `Ξ_n(τ) = PhiTil (g_n(τ)) (E(g_n(τ)))` of the
  `LimApprox` clause of `DynOK'`; each `Ξ_n` is *uniformly Lipschitz in* `τ`
  (`SysAux.pertSlot_lip_approx`, from `EllPkgGo` applied to the class-`C` difference
  `g_n(τ) - g_n(τ')`) and converges pointwise (`SysAux.pertSlot_tendsto`);
* the two combine (`lipschitz_of_approx`) into a Lipschitz bound in `τ` for the limit slots, hence
  continuity.
-/

/-- **A uniformly Lipschitz sequence with a pointwise limit has a Lipschitz limit**: if every
`A n` satisfies `|A n τ - A n τ'| ≤ K|τ - τ'|` on `[0,S]` and `A n τ → Alim τ` for every
`τ ∈ [0,S]`, then `Alim` satisfies the same Lipschitz bound. -/
theorem lipschitz_of_approx {A : ℕ → ℝ → ℝ} {Alim : ℝ → ℝ} {S K : ℝ}
    (hLip : ∀ n (τ : ℝ), τ ∈ Set.Icc 0 S → ∀ τ' ∈ Set.Icc 0 S,
      |A n τ - A n τ'| ≤ K * |τ - τ'|)
    (hconv : ∀ τ ∈ Set.Icc (0:ℝ) S,
      Filter.Tendsto (fun n => A n τ) Filter.atTop (nhds (Alim τ))) :
    ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S, |Alim τ - Alim τ'| ≤ K * |τ - τ'| := by
  intro τ hτ τ' hτ'
  have h1 : Filter.Tendsto (fun n => |A n τ - A n τ'|) Filter.atTop
      (nhds (|Alim τ - Alim τ'|)) :=
    ((hconv τ hτ).sub (hconv τ' hτ')).abs
  exact le_of_tendsto' h1 (fun n => hLip n τ hτ τ' hτ')

theorem slot_tau_cont_alpha {α Ce C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g) :
    ∀ S > 0, ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ContinuousOn (fun τ => Work.FTS_RegExport.RXT.v2_SlotR α
          (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ) (Set.Icc 0 S) ∧
      ContinuousOn (fun τ => Work.FTS_RegExport.RXT.v2_SlotV α
          (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ) (Set.Icc 0 S) ∧
      ContinuousOn (fun τ => Work.FTS_RegExport.RXT.v2_SlotU α
          (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ) (Set.Icc 0 S) := by
  intro S hS z θ hz hθ hθ2
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  obtain ⟨gn, B, L, hAppx, hLipC, hJetC, _hμc⟩ := hOK.2 S hS
  -- the two children: the uniform Lipschitz bound and the pointwise convergence
  obtain ⟨K, hK0, hB⟩ := Work.FTS_RegExport.RXT.SysAux.pertSlot_lip_approx
    (α := α) (Ce := Ce) (L := L) (E := E) hα hα13 hEll
    (fun n τ hτ => (hAppx n τ hτ).1) (fun n τ hτ τ' hτ' => hLipC n τ hτ τ' hτ')
  have hC : ∀ τ ∈ Set.Icc (0:ℝ) S,
      (Filter.Tendsto (fun n : ℕ => Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            (E (slice (gn n) τ))) z θ) Filter.atTop
        (nhds (Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ))) z θ))) ∧
      (Filter.Tendsto (fun n : ℕ => Work.Construction.Vop
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            (E (slice (gn n) τ))) z θ) Filter.atTop
        (nhds (Work.Construction.Vop
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ))) z θ))) ∧
      (Filter.Tendsto (fun n : ℕ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            (E (slice (gn n) τ))) z θ / Real.sin (2 * θ)) Filter.atTop
        (nhds (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ))) z θ / Real.sin (2 * θ)))) :=
    fun τ hτ => Work.FTS_RegExport.RXT.SysAux.pertSlot_tendsto
      (α := α) (Ce := Ce) (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
      hα hα13 hEll hEL3 hOK hS hAppx hJetC hτ z θ hz hθ hθ2
  -- ## regularity of the split pieces
  have hStar3 : ContDiffOn ℝ 3 (Function.uncurry (v2_PhiStar α Φs))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.PhiStar.CoreAux.fields_smooth hαG hαG1 hStar.smooth).1.of_le
      (by simp [Work.Stability.smoothOrder])
  have hStar1 : ContDiffOn ℝ 1 (Function.uncurry (v2_PhiStar α Φs))
      Work.FTS.EllipticEst.Q0 := hStar3.of_le (by norm_num)
  have hTheta3 : ∀ τ : ℝ, 0 ≤ τ → ContDiffOn ℝ 3 (Function.uncurry
      (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ))) Work.FTS.EllipticEst.Q0 := by
    intro τ hτ
    refine Work.FTS_RegExport.RXT.velPert_contDiffOn_Theta
      (α := Work.FTS.Regularity.pExp α) ?_
    refine Work.FTS_RegExport.RXT.contDiffOn_three_L12 ?_
    obtain ⟨C, _hC0, hCb⟩ := Work.FTS_RegExport.RXT.Ftau_bounds
      (Φs := Φs) (E := E) hα hα13 hOK τ hτ
    exact Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta (φ := Work.Spaces.K)
      Work.FTS_RegExport.RXT.v2_continuousOn_K_Iθ
      (Work.FTS_RegExport.RXT.contDiffOn_Ftau_Q0 (Φs := Φs) (E := E) hα hα13 hOK τ hτ)
      (fun z₁ θ₁ hz₁ hθ₁ hθ₁2 => ⟨(hCb z₁ θ₁ hz₁ hθ₁ hθ₁2).1,
        (hCb z₁ θ₁ hz₁ hθ₁ hθ₁2).2.1, (hCb z₁ θ₁ hz₁ hθ₁ hθ₁2).2.2⟩)
  have hFull3 : ∀ τ : ℝ, 0 ≤ τ → ContDiffOn ℝ 3 (Function.uncurry (v2_PhiT α Φs E g τ))
      Work.FTS.EllipticEst.Q0 := by
    intro τ hτ
    have hP := Work.FTS_RegExport.RXT.contDiffOn_slice_PhiR_Q0
      (α := α) (C₀ := C₀) (Cs := Cs) hEL3 hStar hOK τ hτ
    exact hP.sub (hTheta3 τ hτ)
  have hPert3 : ∀ τ : ℝ, 0 ≤ τ → ContDiffOn ℝ 3 (Function.uncurry (v2_PhiPert α E g τ))
      Work.FTS.EllipticEst.Q0 := by
    intro τ hτ
    refine ((hFull3 τ hτ).sub hStar3).congr ?_
    intro p hp
    obtain ⟨z₁, θ₁⟩ := p
    simp only [Function.uncurry]
    linarith [v2_phiTil_split (C₀ := C₀) hα hα13 hOK hτ z₁ θ₁ hp]
  have hPert1 : ∀ τ : ℝ, 0 ≤ τ → ContDiffOn ℝ 1 (Function.uncurry (v2_PhiPert α E g τ))
      Work.FTS.EllipticEst.Q0 := fun τ hτ => (hPert3 τ hτ).of_le (by norm_num)
  -- ## the split identities of the three slots at `(z,θ)`
  have hsplitFun : ∀ τ : ℝ, 0 ≤ τ → Work.FTS_RegExport.RXR5.AgreeOnQ (v2_PhiT α Φs E g τ)
      (v2_PhiStar α Φs + v2_PhiPert α E g τ) := fun τ hτ z₁ θ₁ hz₁ hθ₁ hθ₁2 =>
    v2_phiTil_split (C₀ := C₀) hα hα13 hOK hτ z₁ θ₁
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz₁, hθ₁, hθ₁2⟩)
  have hsplitR : ∀ τ ∈ Set.Icc (0:ℝ) S, v2_SlotR α (v2_PhiT α Φs E g τ) z θ
      = v2_SlotR α (v2_PhiStar α Φs) z θ + v2_SlotR α (v2_PhiPert α E g τ) z θ := by
    intro τ hτ
    show Work.Construction.Rop (Work.FTS.Regularity.pExp α) (v2_PhiT α Φs E g τ) z θ
      = Work.Construction.Rop (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ
        + Work.Construction.Rop (Work.FTS.Regularity.pExp α) (v2_PhiPert α E g τ) z θ
    rw [Work.FTS_RegExport.RXR5.Rop_congr_of_agreeOnQ (α := Work.FTS.Regularity.pExp α)
      (h := hsplitFun τ hτ.1) hz hθ hθ2]
    exact v2_rop_add_at hStar1 (hPert1 τ hτ.1) ⟨hz, hθ, hθ2⟩
  have hsplitV : ∀ τ ∈ Set.Icc (0:ℝ) S, v2_SlotV α (v2_PhiT α Φs E g τ) z θ
      = v2_SlotV α (v2_PhiStar α Φs) z θ + v2_SlotV α (v2_PhiPert α E g τ) z θ := by
    intro τ hτ
    show Work.Construction.Vop (v2_PhiT α Φs E g τ) z θ
      = Work.Construction.Vop (v2_PhiStar α Φs) z θ
        + Work.Construction.Vop (v2_PhiPert α E g τ) z θ
    rw [Work.FTS_RegExport.RXR5.Vop_congr_of_agreeOnQ (h := hsplitFun τ hτ.1) hz hθ hθ2]
    exact v2_vop_add_at hStar1 (hPert1 τ hτ.1) ⟨hz, hθ, hθ2⟩
  have hsplitU : ∀ τ ∈ Set.Icc (0:ℝ) S, v2_SlotU α (v2_PhiT α Φs E g τ) z θ
      = v2_SlotU α (v2_PhiStar α Φs) z θ + v2_SlotU α (v2_PhiPert α E g τ) z θ := by
    intro τ hτ
    show Work.Construction.Uop (Work.FTS.Regularity.pExp α) (v2_PhiT α Φs E g τ) z θ
        / Real.sin (2 * θ)
      = Work.Construction.Uop (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ
          / Real.sin (2 * θ)
        + Work.Construction.Uop (Work.FTS.Regularity.pExp α) (v2_PhiPert α E g τ) z θ
          / Real.sin (2 * θ)
    rw [Work.FTS_RegExport.RXR5.Uop_congr_of_agreeOnQ (α := Work.FTS.Regularity.pExp α)
      (h := hsplitFun τ hτ.1) hz hθ hθ2]
    exact v2_uop_div_add_at (αG := Work.FTS.Regularity.pExp α) hStar1 (hPert1 τ hτ.1)
      ⟨hz, hθ, hθ2⟩
  -- ## the Lipschitz bound for the limit slot families
  have hLR : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      |Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ))) z θ
        - Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ')
            (E (slice g τ'))) z θ| ≤ K * |τ - τ'| :=
    lipschitz_of_approx (A := fun n τ => Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
          (E (slice (gn n) τ))) z θ)
      (Alim := fun τ => Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
          (E (slice g τ))) z θ)
      (fun n τ hτ τ' hτ' => (hB n τ hτ τ' hτ' z θ hz hθ hθ2).1)
      (fun τ hτ => (hC τ hτ).1)
  have hLV : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      |Work.Construction.Vop
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ))) z θ
        - Work.Construction.Vop
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ')
            (E (slice g τ'))) z θ| ≤ K * |τ - τ'| :=
    lipschitz_of_approx (A := fun n τ => Work.Construction.Vop
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
          (E (slice (gn n) τ))) z θ)
      (Alim := fun τ => Work.Construction.Vop
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
          (E (slice g τ))) z θ)
      (fun n τ hτ τ' hτ' => (hB n τ hτ τ' hτ' z θ hz hθ hθ2).2.1)
      (fun τ hτ => (hC τ hτ).2.1)
  have hLU : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      |Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ))) z θ / Real.sin (2 * θ)
        - Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ')
            (E (slice g τ'))) z θ / Real.sin (2 * θ)| ≤ K * |τ - τ'| :=
    lipschitz_of_approx (A := fun n τ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
          (E (slice (gn n) τ))) z θ / Real.sin (2 * θ))
      (Alim := fun τ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
          (E (slice g τ))) z θ / Real.sin (2 * θ))
      (fun n τ hτ τ' hτ' => (hB n τ hτ τ' hτ' z θ hz hθ hθ2).2.2)
      (fun τ hτ => (hC τ hτ).2.2)
  -- ## continuity of a Lipschitz family on `[0,S]`
  have hcontaux : ∀ (P : ℝ → ℝ) (hP : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
        |P τ - P τ'| ≤ K * |τ - τ'|),
      ContinuousOn P (Set.Icc 0 S) := by
    intro P hP τ₀ hτ₀
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    refine ⟨ε / (K + 1), by positivity, fun τ hτ hd => ?_⟩
    have hK1 : (0:ℝ) < K + 1 := by linarith
    have hb := hP τ hτ τ₀ hτ₀
    rw [Real.dist_eq] at hd ⊢
    have h2 : K * |τ - τ₀| ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left (le_of_lt hd) hK0
    have h3 : K * (ε / (K + 1)) < ε := by
      rw [← mul_div_assoc, div_lt_iff₀ hK1]
      nlinarith [hε, hK0]
    linarith
  refine ⟨?_, ?_, ?_⟩
  · refine ContinuousOn.congr (f := fun τ => v2_SlotR α (v2_PhiStar α Φs) z θ
        + v2_SlotR α (v2_PhiPert α E g τ) z θ) ?_ (fun τ hτ => hsplitR τ hτ)
    have hP : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
        |v2_SlotR α (v2_PhiPert α E g τ) z θ - v2_SlotR α (v2_PhiPert α E g τ') z θ|
          ≤ K * |τ - τ'| := by
      intro τ hτ τ' hτ'
      simpa only [v2_SlotR, v2_PhiPert] using hLR τ hτ τ' hτ'
    exact continuousOn_const.add (hcontaux _ hP)
  · refine ContinuousOn.congr (f := fun τ => v2_SlotV α (v2_PhiStar α Φs) z θ
        + v2_SlotV α (v2_PhiPert α E g τ) z θ) ?_ (fun τ hτ => hsplitV τ hτ)
    have hP : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
        |v2_SlotV α (v2_PhiPert α E g τ) z θ - v2_SlotV α (v2_PhiPert α E g τ') z θ|
          ≤ K * |τ - τ'| := by
      intro τ hτ τ' hτ'
      simpa only [v2_SlotV, v2_PhiPert] using hLV τ hτ τ' hτ'
    exact continuousOn_const.add (hcontaux _ hP)
  · refine ContinuousOn.congr (f := fun τ => v2_SlotU α (v2_PhiStar α Φs) z θ
        + v2_SlotU α (v2_PhiPert α E g τ) z θ) ?_ (fun τ hτ => hsplitU τ hτ)
    have hP : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
        |v2_SlotU α (v2_PhiPert α E g τ) z θ - v2_SlotU α (v2_PhiPert α E g τ') z θ|
          ≤ K * |τ - τ'| := by
      intro τ hτ τ' hτ'
      simpa only [v2_SlotU, v2_PhiPert] using hLU τ hτ τ' hτ'
    exact continuousOn_const.add (hcontaux _ hP)

end Work.FTS_RegExport.RXT.Sys

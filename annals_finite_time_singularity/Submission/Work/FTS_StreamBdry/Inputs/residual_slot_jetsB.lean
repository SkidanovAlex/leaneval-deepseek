import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_RegExport.RXT.Slots.v2_velPert
import Submission.Work.FTS_RegExport.RXT.Slots.v2_starUop
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.FTS_RegExport.RXT.velVanish2Aux
import Submission.Work.FTS_RegExport.RXT.velVanish2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `residual_slot_jetsB` — the two residual slots, jets of order `≤ 2`, without the clock

The residual of the modulated stream function at profile exponent `α` is
`Φ̃ = v2_PhiT α Φs E g τ = PhiTil (pExp α) (Ftau (pExp α) (GR α g) τ) (slice (ΦR α Φs E g) τ)`.
This file bounds the order-`≤ 2` mixed jets of the two slots

* `v2_SlotU α Φ̃ = Uop (pExp α) Φ̃ / sin 2θ` and
* `Vop Φ̃`

on the open quadrant, at a single fake time `τ ≥ 0`, by a constant depending only on `τ`.

The argument is the one of `RXT.velVanish2` restricted to these two slots and with the *unused*
clock hypothesis `ClockBd` dropped: split `Φ̃ = Φ̃_* + Φ̃_pert` on the open quadrant
(`v2_phiTil_split`), bound the two halves by `starVop` / `v2_starUop` (`StarPkgo2` with the
explicit fields of the star residual) and by `v2_velPert` (`EllPkgGo` + `EllLimOK3` + `Sol` +
`DynOK'`), and add them with `v2_slot_bound_of_split`.

The main theorem `residual_slot_jetsB` below is the instance `α := a` of the general statement
`v2_slots_jets_aux`.
-/

namespace Work.FTS_StreamBdry.Inputs

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS_RegExport.RXT

/- **The two residual slots, jets of order `≤ 2` bounded** (general profile exponent).  This is
`RXT.velVanish2` for the slots `𝒰/sin 2θ` and `𝒱`, without the (unused) clock hypothesis
`ClockBd`, at a single time `τ ≥ 0`. -/
set_option autoImplicit false in
theorem v2_slots_jets_aux {α Ce C₀ Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.VocabO.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.VocabO2.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    {g : Fam} (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∀ τ, 0 ≤ τ → ∃ M : ℝ,
      (∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (v2_SlotU α (v2_PhiT α Φs E g τ)) z θ| ≤ M) ∧
      (∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (Work.Construction.Vop (v2_PhiT α Φs E g τ)) z θ| ≤ M) := by
  intro τ hτ
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  obtain ⟨CV, hCV0, hCV⟩ := starVop hαG hαG1 hStar
  obtain ⟨CU, hCU0, hCU⟩ := Work.FTS_RegExport.RXT.Slots.v2_starUop hαG hαG1 hStar
  have hS1 : (0 : ℝ) < max τ 1 := lt_of_lt_of_le zero_lt_one (le_max_right τ 1)
  obtain ⟨MP, hMP⟩ := v2_velPert (Φs := Φs) (E := E)
    hα hα13 hEll hEL hSol hOK (max τ 1) hS1
  have hτS : τ ∈ Set.Icc (0 : ℝ) (max τ 1) := ⟨hτ, le_max_left τ 1⟩
  set TOTAL : ℝ := CV * (max Cs 1 * Work.FTS.Regularity.pExp α)
    + CU * (max Cs 1 * Work.FTS.Regularity.pExp α) + MP with hTOTAL
  have hCVa : 0 ≤ CV * (max Cs 1 * Work.FTS.Regularity.pExp α) :=
    mul_nonneg hCV0 (le_of_lt (mul_pos (lt_of_lt_of_le zero_lt_one (le_max_right Cs 1)) hαG))
  have hCUa : 0 ≤ CU * (max Cs 1 * Work.FTS.Regularity.pExp α) :=
    mul_nonneg hCU0 (le_of_lt (mul_pos (lt_of_lt_of_le zero_lt_one (le_max_right Cs 1)) hαG))
  have key : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (v2_SlotU α (v2_PhiT α Φs E g τ)) z θ| ≤ max TOTAL 0 ∧
      |Work.Spaces.mixed j i (Work.Construction.Vop (v2_PhiT α Φs E g τ)) z θ|
        ≤ max TOTAL 0 := by
    intro j i hji z θ hz hθ hθ2
    -- ## the pointwise split of the stream functions on the quadrant
    have hsplit : ∀ z₁ θ₁ : ℝ, (z₁, θ₁) ∈ Work.FTS.EllipticEst.Q0 →
        v2_PhiT α Φs E g τ z₁ θ₁ = v2_PhiStar α Φs z₁ θ₁ + v2_PhiPert α E g τ z₁ θ₁ :=
      fun z₁ θ₁ hp => v2_phiTil_split (C₀ := C₀) hα hα13 hOK hτ z₁ θ₁ hp
    have hsplitFun : Work.FTS_RegExport.RXR5.AgreeOnQ (v2_PhiT α Φs E g τ)
        (v2_PhiStar α Φs + v2_PhiPert α E g τ) :=
      fun z₁ θ₁ hz₁ hθ₁ hθ₁2 =>
        hsplit z₁ θ₁ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz₁, hθ₁, hθ₁2⟩)
    -- ## regularity of the pieces
    have hPhi3 : ContDiffOn ℝ 3
        (Function.uncurry (slice (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ))
        Work.FTS.EllipticEst.Q0 :=
      contDiffOn_slice_PhiR_Q0 (α := α) (C₀ := C₀) (Cs := Cs) hEL hStar hOK τ hτ
    have hFK2 : ContDiffOn ℝ 2
        (Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ)) (Set.Ioi 0) := by
      obtain ⟨C, _hC0, hC⟩ := Ftau_bounds (Φs := Φs) (E := E) hα hα13 hOK τ hτ
      exact contDiffOn_two_integral_Itheta (φ := Work.Spaces.K) v2_continuousOn_K_Iθ
        (contDiffOn_Ftau_Q0 (Φs := Φs) (E := E) hα hα13 hOK τ hτ)
        (fun z₁ θ₁ hz₁ hθ₁ hθ₁2 => ⟨(hC z₁ θ₁ hz₁ hθ₁ hθ₁2).1, (hC z₁ θ₁ hz₁ hθ₁ hθ₁2).2.1,
          (hC z₁ θ₁ hz₁ hθ₁ hθ₁2).2.2⟩)
    have hL12 : ContDiffOn ℝ 3
        (Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ)) (Set.Ioi 0) := contDiffOn_three_L12 hFK2
    have hTheta3 : ContDiffOn ℝ 3 (Function.uncurry (Work.Construction.Theta
        (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ))) Work.FTS.EllipticEst.Q0 :=
      velPert_contDiffOn_Theta (α := Work.FTS.Regularity.pExp α) hL12
    have hFull3 : ContDiffOn ℝ 3 (Function.uncurry (v2_PhiT α Φs E g τ))
        Work.FTS.EllipticEst.Q0 := hPhi3.sub hTheta3
    have hStar3 : ContDiffOn ℝ 3 (Function.uncurry (v2_PhiStar α Φs)) Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.PhiStar.CoreAux.fields_smooth hαG hαG1 hStar.smooth).1.of_le
        (by simp [Work.Stability.smoothOrder])
    have hPert3 : ContDiffOn ℝ 3 (Function.uncurry (v2_PhiPert α E g τ))
        Work.FTS.EllipticEst.Q0 := by
      refine (hFull3.sub hStar3).congr ?_
      intro p hp
      obtain ⟨z₁, θ₁⟩ := p
      simp only [Function.uncurry]
      linarith [hsplit z₁ θ₁ hp]
    have hStarC1 : ContDiffOn ℝ 1 (Function.uncurry (v2_PhiStar α Φs)) Work.FTS.EllipticEst.Q0 :=
      hStar3.of_le (by norm_num)
    have hPertC1 : ContDiffOn ℝ 1 (Function.uncurry (v2_PhiPert α E g τ))
        Work.FTS.EllipticEst.Q0 := hPert3.of_le (by norm_num)
    -- ## the four slot bounds of the two halves
    have hstarU : ∀ j' i' : ℕ, j' + i' ≤ 2 → ∀ z₁ θ₁ : ℝ, 0 < z₁ → 0 < θ₁ →
        θ₁ < Real.pi / 2 →
        |Work.Spaces.mixed j' i' (v2_SlotU α (v2_PhiStar α Φs)) z₁ θ₁|
          ≤ (CU * (max Cs 1 * Work.FTS.Regularity.pExp α)) * min z₁ 1 :=
      fun j' i' hji' z₁ θ₁ hz₁ hθ₁ hθ₁2 => hCU j' i' hji' z₁ θ₁ hz₁ hθ₁ hθ₁2
    have hstarV : ∀ j' i' : ℕ, j' + i' ≤ 2 → ∀ z₁ θ₁ : ℝ, 0 < z₁ → 0 < θ₁ →
        θ₁ < Real.pi / 2 →
        |Work.Spaces.mixed j' i' (Work.Construction.Vop (v2_PhiStar α Φs)) z₁ θ₁|
          ≤ (CV * (max Cs 1 * Work.FTS.Regularity.pExp α)) * min z₁ 1 :=
      fun j' i' hji' z₁ θ₁ hz₁ hθ₁ hθ₁2 => hCV j' i' hji' z₁ θ₁ hz₁ hθ₁ hθ₁2
    have hpertU : ∀ j' i' : ℕ, j' + i' ≤ 2 → ∀ z₁ θ₁ : ℝ, 0 < z₁ → 0 < θ₁ →
        θ₁ < Real.pi / 2 →
        |Work.Spaces.mixed j' i' (v2_SlotU α (v2_PhiPert α E g τ)) z₁ θ₁| ≤ MP * min z₁ 1 :=
      fun j' i' hji' z₁ θ₁ hz₁ hθ₁ hθ₁2 =>
        hMP τ hτS z₁ θ₁ hz₁ hθ₁ hθ₁2 (v2_SlotU α (v2_PhiPert α E g τ))
          (by exact Or.inr (Or.inr rfl)) j' i' hji'
    have hpertV : ∀ j' i' : ℕ, j' + i' ≤ 2 → ∀ z₁ θ₁ : ℝ, 0 < z₁ → 0 < θ₁ →
        θ₁ < Real.pi / 2 →
        |Work.Spaces.mixed j' i' (Work.Construction.Vop (v2_PhiPert α E g τ)) z₁ θ₁|
          ≤ MP * min z₁ 1 :=
      fun j' i' hji' z₁ θ₁ hz₁ hθ₁ hθ₁2 =>
        hMP τ hτS z₁ θ₁ hz₁ hθ₁ hθ₁2 (Work.Construction.Vop (v2_PhiPert α E g τ))
          (by exact Or.inr (Or.inl rfl)) j' i' hji'
    -- ## `C²` of the four slot functions
    have hSC2U : ContDiffOn ℝ 2 (Function.uncurry (v2_SlotU α (v2_PhiStar α Φs)))
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.PhiStar.CoreAux.fields_smooth hαG hαG1 hStar.smooth).2.2.2.2.1.of_le
        (by simp [Work.Stability.smoothOrder])
    have hSC2V : ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Vop (v2_PhiStar α Φs)))
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.PhiStar.CoreAux.fields_smooth hαG hαG1 hStar.smooth).2.2.1.of_le
        (by simp [Work.Stability.smoothOrder])
    have hPC2U : ContDiffOn ℝ 2 (Function.uncurry (v2_SlotU α (v2_PhiPert α E g τ)))
        Work.FTS.EllipticEst.Q0 :=
      contDiffOn_uncurry_div_sin_two (contDiffOn_uncurry_Uop
        (α := Work.FTS.Regularity.pExp α) hPert3)
    have hPC2V : ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Vop (v2_PhiPert α E g τ)))
        Work.FTS.EllipticEst.Q0 := contDiffOn_uncurry_Vop hPert3
    -- ## the arithmetic of the `min z 1`-trade-off
    have hmm : (0 : ℝ) ≤ min z 1 := le_min hz.le zero_le_one
    have hM0 : 0 ≤ max TOTAL 0 := le_max_right _ _
    have hstep : ∀ c : ℝ, c ≤ max TOTAL 0 → c * min z 1 ≤ max TOTAL 0 := fun c hc => by
      calc c * min z 1 ≤ max TOTAL 0 * min z 1 := mul_le_mul_of_nonneg_right hc hmm
        _ ≤ max TOTAL 0 * 1 := mul_le_mul_of_nonneg_left (min_le_right z 1) hM0
        _ = max TOTAL 0 := mul_one _
    constructor
    · -- the `𝒰/sin 2θ`-slot
      have heq : Set.EqOn (Function.uncurry (v2_SlotU α (v2_PhiT α Φs E g τ)))
          (Function.uncurry (v2_SlotU α (v2_PhiStar α Φs) + v2_SlotU α (v2_PhiPert α E g τ)))
          Work.FTS.EllipticEst.Q0 := by
        intro p hp
        obtain ⟨z₁, θ₁⟩ := p
        obtain ⟨hz₁, hθ₁, hθ₁2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
        simp only [Function.uncurry, Pi.add_apply, v2_SlotU]
        rw [Work.FTS_RegExport.RXR5.Uop_congr_of_agreeOnQ (α := Work.FTS.Regularity.pExp α)
          (h := hsplitFun) (Φ := v2_PhiT α Φs E g τ)
          (Φ' := v2_PhiStar α Φs + v2_PhiPert α E g τ) hz₁ hθ₁ hθ₁2]
        exact v2_uop_div_add_at hStarC1 hPertC1 ⟨hz₁, hθ₁, hθ₁2⟩
      have hres := v2_slot_bound_of_split heq hSC2U hPC2U hstarU hpertU j i hji z θ hz hθ hθ2
      have hA : CU * (max Cs 1 * Work.FTS.Regularity.pExp α) + MP ≤ max TOTAL 0 := by
        rw [hTOTAL]
        exact le_max_of_le_left (by linarith [hCVa])
      exact le_trans hres (hstep _ hA)
    · -- the `𝒱`-slot
      have heq : Set.EqOn (Function.uncurry (Work.Construction.Vop (v2_PhiT α Φs E g τ)))
          (Function.uncurry (Work.Construction.Vop (v2_PhiStar α Φs)
            + Work.Construction.Vop (v2_PhiPert α E g τ)))
          Work.FTS.EllipticEst.Q0 := by
        intro p hp
        obtain ⟨z₁, θ₁⟩ := p
        obtain ⟨hz₁, hθ₁, hθ₁2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
        simp only [Function.uncurry, Pi.add_apply]
        rw [Work.FTS_RegExport.RXR5.Vop_congr_of_agreeOnQ (h := hsplitFun)
          (Φ := v2_PhiT α Φs E g τ)
          (Φ' := v2_PhiStar α Φs + v2_PhiPert α E g τ) hz₁ hθ₁ hθ₁2]
        exact v2_vop_add_at hStarC1 hPertC1 ⟨hz₁, hθ₁, hθ₁2⟩
      have hres := v2_slot_bound_of_split heq hSC2V hPC2V hstarV hpertV j i hji z θ hz hθ hθ2
      have hA : CV * (max Cs 1 * Work.FTS.Regularity.pExp α) + MP ≤ max TOTAL 0 := by
        rw [hTOTAL]
        exact le_max_of_le_left (by linarith [hCUa])
      exact le_trans hres (hstep _ hA)
  exact ⟨max TOTAL 0,
    fun j' i' hji' z θ hz hθ hθ2 => (key j' i' hji' z θ hz hθ hθ2).1,
    fun j' i' hji' z θ hz hθ hθ2 => (key j' i' hji' z θ hz hθ hθ2).2⟩

theorem residual_slot_jetsB {a C₀ Ce Cs : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp a) u →
      Work.FTS.VocabO.EllPkgGo (Work.FTS.Regularity.pExp a) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp a) 6 Ce u (E u))
    (hEL : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp a) E)
    (hStar : Work.FTS.VocabO2.StarPkgo2 (Work.FTS.Regularity.pExp a) Cs Φs)
    {g : Work.FTS.Galerkin.Fam} (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp a) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp a) C₀ Φs E g) :
    ∀ τ, 0 ≤ τ → ∃ M : ℝ,
      (∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (Work.FTS_RegExport.RXT.v2_SlotU a
          (Work.FTS_RegExport.RXT.v2_PhiT a Φs E g τ)) z θ| ≤ M) ∧
      (∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (Work.Construction.Vop
          (Work.FTS_RegExport.RXT.v2_PhiT a Φs E g τ)) z θ| ≤ M) :=
  v2_slots_jets_aux ha ha13 hEll hEL hStar hSol hOK

end Work.FTS_StreamBdry.Inputs

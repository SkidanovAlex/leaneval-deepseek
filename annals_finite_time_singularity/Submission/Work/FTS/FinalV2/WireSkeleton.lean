import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.ClassC.pth_Vop_EllResid_classC
import Submission.Work.FTS.FinalV2.ESlot
import Submission.Work.FTS.FinalV2.Mer8
import Submission.Work.FTS.PhiStar.StarCoreInhabitant
import Submission.Work.FTS.PressureOn.Main
import Submission.Work.FTS.StrongEps.E5G.ExistsLimG_assembly
import Submission.Work.FTS.StrongEps.EpsE4R
import Submission.Work.FTS.StrongEps.EpsHlim4
import Submission.Work.FTS.StrongEps.EpsODE
import Submission.Work.FTS.StrongPersist.SP6.EUz6
import Submission.Work.FTS.StrongPersist.StarPkg6OfCore
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Slice
import Submission.Work.FTS_LocDatum3a.Assembly
import Submission.Work.FTS_MuLamOK.Main
import Submission.Work.FTS_RegExport.RXB.l12_zero_lim_proved
import Submission.Work.FTS_RegExport.RXR5L.Auxiliary.Tlim_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.FinalV2.WireSkeleton` — `∃ α, Inputs' α` from the producers in the tree
(curric-46 lead install, 2026-10-10; REVIEW FIX-1 `fts_inputs_wire'`)

Instantiates every conjunct of `Inputs'` from an existing producer where one fits, and from the
named open producers of `FinalV2.Producers` otherwise (no inline `sorry` in this file). The
threshold arithmetic is checked: `gam a = 1 + a/10`, `Cg = 10/√(gam (3α) - 1) = 10/√(3α/10)`, and
`α·600·Cg·C₀ ≤ 1` holds for `C₀ ≥ 1` and `α ≤ 8·10⁻⁹/C₀²` (`scale_ok_gen`; the old `scale_ok`
is the case `C₀ = 1`, now unused).

`theorem_1_v2` is the challenge statement through the corrected bundle; its `sorryAx` leaves are
exactly the open producers (reach-walk in `cbc/fts_v2_install.md`).
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS.FinalV2

open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Final
open Work.FTS.Regularity (pExp)

set_option autoImplicit false


/-- The sup-bound constant of `sup5'` at `αG = pExp α`. -/
def CgOf (α : ℝ) : ℝ := 10 / Real.sqrt (Work.Spaces.gam (pExp α) - 1)


theorem CgOf_nonneg (α : ℝ) : 0 ≤ CgOf α := div_nonneg (by norm_num) (Real.sqrt_nonneg _)

/-- **The wire's threshold arithmetic at a general `C₀ ≥ 1`** (C1–C5 ruling §6; replaces `scale_ok`,
which is hard-wired to `C₀ = 1`).  PROVED. -/
theorem scale_ok_gen {α C₀ : ℝ} (hα : 0 < α) (hC₀ : 1 ≤ C₀)
    (hαs : α ≤ 8 / 10 ^ 9 / C₀ ^ 2) :
    α * (600 * CgOf α * C₀) ≤ 1 := by
  have hg : Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1 = 3 * α / 10 := by
    rw [Work.FTS.Regularity.pExp_eq]; simp only [Work.Spaces.gam]; ring
  set s : ℝ := Real.sqrt (3 * α / 10) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hC0 : 0 < C₀ := lt_of_lt_of_le one_pos hC₀
  have hαC : α * C₀ ^ 2 ≤ 8 / 10 ^ 9 := by
    have := mul_le_mul_of_nonneg_right hαs (le_of_lt (pow_pos hC0 2))
    rwa [div_mul_cancel₀ _ (pow_ne_zero 2 hC0.ne')] at this
  have hkey : 6000 * α * C₀ ≤ s := by
    have h1 : (6000 * α * C₀) ^ 2 ≤ 3 * α / 10 := by
      have : (6000 * α * C₀) ^ 2 = 36000000 * α * (α * C₀ ^ 2) := by ring
      rw [this]
      have hα' : 0 ≤ 36000000 * α := by positivity
      calc 36000000 * α * (α * C₀ ^ 2) ≤ 36000000 * α * (8 / 10 ^ 9) :=
            mul_le_mul_of_nonneg_left hαC hα'
        _ ≤ 3 * α / 10 := by nlinarith
    calc 6000 * α * C₀ = Real.sqrt ((6000 * α * C₀) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ s := Real.sqrt_le_sqrt h1
  have hC : CgOf α = 10 / s := by rw [CgOf, hg]
  rw [hC]
  have : α * (600 * (10 / s) * C₀) = 6000 * α * C₀ / s := by field_simp; ring
  rw [this, div_le_one hs0]
  exact hkey

/-- **(4′) producer at the `StarCore` hypothesis** (curric-46 E5 swap, 2026-10-12,
`cbc/fts_e5swap_e4chapters.md` Task A): `global_strong2'` with `StarPkgo2 αG Cs Φs` replaced by
`StarCore αG Cs Φs ∧ 0 < Cs`; body = E6 from the PROVED `E5G.exists_limG_core`. -/
theorem global_strong2'_core {C₀ Ce Cs : ℝ} : ∃ α₂ : ℝ, 0 < α₂ ∧ ∀ αG ∈ Set.Ioc 0 α₂,
    ∀ {K : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g₀ : Fn},
    Work.FTS.StrongEps.IsSmoothKernel ρ →
    (∀ u : Fn, Work.FTS.ClassC.ClassC αG u →
      Work.FTS.VocabO.EllPkgGo αG Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK αG 6 Ce u (E u)) →
    EllLimOK3 αG E → Work.FTS.VocabO2.StarCore αG Cs Φs → 0 < Cs →
    Work.FTS.StrongEps.MuLamOK αG C₀ Φs E →
    Work.FTS.StrongEps.EpsUniformMem αG ρ Φs E g₀ C₀ K →
      ∃ g : Fam, Sol αG Φs E g ∧ (∀ z θ, g z θ 0 = g₀ z θ) ∧ DynOK' αG C₀ Φs E g := by
  obtain ⟨α₂, hα₂, h⟩ := Work.FTS.StrongEps.E5G.exists_limG_core (C₀ := C₀) (Ce := Ce) (Cs := Cs)
  refine ⟨α₂, hα₂, ?_⟩
  intro αG hαG K ρ Φs E g₀ hρ hEll hEL3 hcore hCs hml hU
  obtain ⟨g, hSol, hinit, hreg, hXn, hApprox⟩ :=
    Work.FTS.StrongEps.global_strong2_of_limG
      (h αG hαG hρ hEll ((Work.FTS.StrongEps.ellLimOK3_iff αG E).mpr hEL3) hcore hCs hml hU)
  exact ⟨g, hSol, hinit, ⟨⟨hreg, hXn⟩, (Work.FTS.StrongEps.limApproxSE_iff αG C₀ Φs (⇑E) g).mp hApprox⟩⟩

/-- **The wire**: `∃ α, Inputs' α` from the producers.  curric-46 lead install 2026-10-11 (C1–C5
ruling `cbc/fts_strongeps_c1c5_ruling.md` §6/§7 items 6+8, review F3/F5): `C₀ := C★` of `EpsE4R`,
α also below `α₄/3` and `8·10⁻⁹/C₀²` (`scale_ok_gen`); (4′) receives `EllLimOK3` itself. -/
theorem fts_inputs' : ∃ α : ℝ, Inputs' α := by
  -- uniform constants
  -- 2026-10-12 (`cbc/fts_apriori6_ruling.md` §4 + REVIEW): the kernel is symmetric (centred bump)
  obtain ⟨ρ, hρ, hρs⟩ := Work.FTS.StrongEps.EpsE4Thr.E4R4.kernel_exists_symm
  obtain ⟨Ce, hCe, α₀, hα₀, hEllF⟩ := core1_1a3 Work.FTS.ClassC.ellClassOk_exists_of_classC
  -- E5 swap (2026-10-12): the star node as `StarCore` (constant `Cc`) + the algebraic lift
  -- lift; since 2026-10-12 the order-six lift `StrongPersist.StarPkg6OfCore` at `Cs := C6 * Cc`
  -- (`StarPkgo2` is its `toStarPkgo2` at the same `Cs`; apriori6 ruling §4 + REVIEW)
  obtain ⟨Cc, hCc, hCoreF⟩ := Work.FTS.PhiStar.StarCore_inhabitant
  obtain ⟨C6, hC6, h6F⟩ := Work.FTS.StrongPersist.StarPkg6OfCore
  set Cs : ℝ := C6 * Cc with hCsdef
  obtain ⟨αs, hαsdef⟩ : ∃ αs : ℝ, αs = 1 / 5 := ⟨_, rfl⟩
  have hαs : (0 : ℝ) < αs := by rw [hαsdef]; norm_num
  -- E4 (`EpsE4R`, room ruling §6): `C★` before `C₀`; the wire sets `C₀ := C★` (review F3:
  -- `Ce`, `Cs` explicit)
  obtain ⟨Cstar, hC1, hE4⟩ := Work.FTS.StrongEps.EpsE4R (Ce := Ce) (Cs := Cs) hρ hρs
  set C₀ : ℝ := Cstar with hC₀def
  have hC₀ : (0 : ℝ) < C₀ := lt_of_lt_of_le one_pos hC1
  obtain ⟨α₄, hα₄, hE4α⟩ := hE4 C₀ le_rfl
  -- (4′) E5/E6, α₂ after `C₀, Ce, Cs` (review F5)
  obtain ⟨α₂, hα₂, hGlob⟩ := global_strong2'_core (C₀ := C₀) (Ce := Ce) (Cs := Cc)
  obtain ⟨αμ, hαμ, hMuF⟩ := Work.FTS_MuLamOK.MuLamOK_proved_pExp (Ce := Ce) (Cs := Cs) hC₀
  obtain ⟨αL, hαL, hLipF⟩ := muLipC_pExp (Ce := Ce) (Cs := Cs) hC₀
  -- the `V(E slice)` constant, then the tie threshold `αT` (constants fixed before `α`;
  -- 2026-10-11, `cbc/fts_hvop_design.md`)
  obtain ⟨KV, hKV, hESF⟩ := Work.FTS.FinalV2.ESlot.eSlotBd_of_wire
  set CE : ℝ := KV * (Ce + 1) * C₀ with hCEdef
  set αT : ℝ := 1 / (48 * (1 + |Cs| + |CE|)) with hαTdef
  have hαT : 0 < αT := by positivity
  -- the exponent: below every threshold
  set α : ℝ := min (min (min (min (min (α₀ / 3) (αs / 3)) (min (α₂ / 3) αμ))
      (min αL (8 / 10 ^ 9))) αT) (min (α₄ / 3) (8 / 10 ^ 9 / C₀ ^ 2)) with hαdef
  have hα : 0 < α := lt_min (lt_min (lt_min (lt_min (lt_min (by linarith) (by linarith))
    (lt_min (by linarith) hαμ)) (lt_min hαL (by norm_num))) hαT)
    (lt_min (by linarith) (by positivity))
  have hαold : α ≤ min (min (min (min (α₀ / 3) (αs / 3)) (min (α₂ / 3) αμ))
      (min αL (8 / 10 ^ 9))) αT := min_le_left _ _
  have hαnew : α ≤ min (α₄ / 3) (8 / 10 ^ 9 / C₀ ^ 2) := min_le_right _ _
  have hα4 : α ≤ α₄ / 3 := hαnew.trans (min_le_left _ _)
  have h8' : α ≤ 8 / 10 ^ 9 / C₀ ^ 2 := hαnew.trans (min_le_right _ _)
  have hαo : α ≤ min (min (min (α₀ / 3) (αs / 3)) (min (α₂ / 3) αμ)) (min αL (8 / 10 ^ 9)) :=
    hαold.trans (min_le_left _ _)
  have hαTle : α ≤ αT := hαold.trans (min_le_right _ _)
  have h0 : α ≤ α₀ / 3 :=
    hαo.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hs : α ≤ αs / 3 :=
    hαo.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have h2 : α ≤ α₂ / 3 :=
    hαo.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hμ : α ≤ αμ := hαo.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hL : α ≤ αL := hαo.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h8 : α ≤ 8 / 10 ^ 9 := hαo.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hα13 : α ≤ 1 / 3 := h8.trans (by norm_num)
  have hα1 : α ≤ 1 := hα13.trans (by norm_num)
  have hpE : pExp α ≤ α₀ := by rw [Work.FTS.Regularity.pExp_eq]; linarith
  have hpS : pExp α ≤ αs := by rw [Work.FTS.Regularity.pExp_eq]; linarith
  have hpG : pExp α ∈ Ioc 0 α₂ :=
    ⟨Work.FTS.Regularity.pExp_pos hα, by rw [Work.FTS.Regularity.pExp_eq]; linarith⟩
  have hp4 : pExp α ∈ Ioc 0 α₄ :=
    ⟨Work.FTS.Regularity.pExp_pos hα, by rw [Work.FTS.Regularity.pExp_eq]; linarith⟩
  have hαG : 0 < pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- the tie at `pExp α = 3α`
  have htie : 4 * pExp α + 2 * Cs * pExp α ^ 2 + 2 * CE * pExp α ^ 2 ≤ 1 / 2 := by
    have hD : 0 < 48 * (1 + |Cs| + |CE|) := by positivity
    have hm : α * (48 * (1 + |Cs| + |CE|)) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hαTle hD.le
      rwa [hαTdef, one_div, inv_mul_cancel₀ hD.ne'] at this
    refine Work.FTS.FinalV2.ESlot.tie_of_small hαG ?_ ?_
    · rw [Work.FTS.Regularity.pExp_eq]
      nlinarith [abs_nonneg Cs, abs_nonneg CE]
    · rw [Work.FTS.Regularity.pExp_eq]
      nlinarith [abs_nonneg Cs, abs_nonneg CE]
  -- α-dependent objects
  obtain ⟨E, hEll, hEL3⟩ := hEllF α hα hpE
  obtain ⟨Φs, hCore⟩ := hCoreF (pExp α) hαG (hpS.trans hαsdef.le)
  have hStar6 : Work.FTS.StrongPersist.StarPkg6 (pExp α) Cs Φs :=
    h6F (pExp α) Cc Φs hαG (hpS.trans (by rw [hαsdef]; norm_num)) hCc hCore
  have hStar : StarPkgo2 (pExp α) Cs Φs := hStar6.toStarPkgo2
  have hML : Work.FTS.StrongEps.MuLamOK (pExp α) C₀ Φs E :=
    hMuF α ⟨hα, hμ⟩ hStar (fun f hf => (hEll f hf).1)
  have hLip : MuLipC (pExp α) C₀ Φs E := hLipF α ⟨hα, hL⟩ hStar (fun f hf => (hEll f hf).1)
  have hES : ∀ g : Fam, DynOK' (pExp α) C₀ Φs E g → Work.FTS_RegExport.ESlotBd α Cs g ⇑E :=
    fun g hOK => hESF hα hα13 hCe.le hEll hEL3 hOK htie
  set K : ℝ := 1 with hKdef
  refine ⟨α, ⟨hα, hα13, Work.FTS.PressureOn.pressureReconstructionOn ⟨α, hα.le⟩, ?_⟩⟩
  refine ⟨Ce, Cs, CgOf α, C₀, K, ρ, E, Φs, hCe, CgOf_nonneg α, hC₀, one_pos,
    scale_ok_gen hα hC1 h8',
    hρ, hEll, hEL3, hML, hLip, hStar, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (3) E4: `StrongEps.EpsE4R` at `C₀ = C★` (open leaf); `0 ≤ K'` from `Xn6 ≥ 0`
    intro K' g₀ _hRegQ hvan hd h4 h6'
    have hK' : 0 ≤ K' := by
      have h0' : 0 ≤ Work.FTS.StrongGlobal.Xn6 (pExp α) g₀ := Work.Spaces.HkNorm_nonneg _ _ _
      have hp2 : 0 < (pExp α) ^ 2 := by positivity
      by_contra hneg
      push Not at hneg
      nlinarith
    exact hE4α (pExp α) hp4 hK' hvan hEll hStar hStar6 hML hd h4 h6'
  · -- (3a′) LocDatum3a, exact
    exact Work.FTS_LocDatum3a.core3a'_of_locG6 hα hα13 hρ
  · -- (4′) `global_strong2'_core` (proved from `E5G.exists_limG_core`; StarCore + `0 < Cc`),
    -- KEEPING the initial-value clause (RegExport REVIEW F1); (1a) is `EllLimOK3` itself
    intro g₀ K' hU
    exact hGlob (pExp α) hpG hρ hEll hEL3 hCore hCc hML hU
  · -- (5′) `sup5'` at `αG = pExp α`
    intro g hOK τ hτ z hz θ hθ
    exact sup5' hαG hαG1 hOK τ hτ z hz θ hθ
  · -- (6′) `mu6'`, Hölder exponent `β := α`
    intro g _hSol hOK
    obtain ⟨hb, hc, hh⟩ := mu6' hαG hαG1 hML hLip hOK
    exact ⟨hb, hc, hh α hα hα1⟩
  · -- (7″) `regPkg7'` (proved from `RegExportIface.regExport` + `mu6'` + `hES` from `FinalV2.ESlot`)
    exact regPkg7' hα hα13 hEll hEL3 hML hLip hStar hES
  · -- (8′) `mer8'` (proved modulo `sol_fire`, `psiCan_C3`, `profDerivData_min`)
    intro g A B C hSol hOK hClock
    exact mer8' hα hα13 hEL3 hStar hSol hOK hClock
  · -- (9″) `hid9''` (proved from `StreamBdryIface.hid9''_of_parts`)
    exact hid9'' (C₀ := C₀) hα hα13 hEll hEL3 hStar
  · -- (10′) `merPsi_C3` from `psiCan_C3`
    intro g A B C _hSol hOK hClock
    exact merPsi_C3 (psiCan_C3 hEL3 hStar hOK) (fun τ hτ => hClock.2.2.2.2 τ hτ)


open FiniteTimeSingularity Gradient Matrix MeasureTheory in
/-- **The challenge statement through the corrected bundle** (reach-walk target). -/
theorem theorem_1_v2 :
    ∃ β > 0, ∃ u₀ : Work.FTS.Top.R3 → Work.FTS.Top.R3, div u₀ = 0 ∧ IsOdd u₀ ∧
      IsContDiffHolder ℝ β u₀ ∧
      (∃ C : ℝ, 0 < C ∧ ∀ x : Work.FTS.Top.R3, ‖vorticity u₀ x‖ ≤ C / (‖x‖ ^ (β : ℝ) + 1)) ∧
        ∃ p : Work.FTS.Top.R3 → ℝ → ℝ, ∃ u : Work.FTS.Top.R3 → ℝ → Work.FTS.Top.R3,
            (∀ t ∈ Set.Ico 0 1, IsOdd (u · t)) ∧
            IsLocalEulerEquationSolution p u₀ 1 u ∧
              (∀ T ∈ Set.Ioo 0 1,
                IsContDiffHolderOn ℝ β u.uncurry (Set.univ ×ˢ Set.Icc 0 T)) ∧
                Filter.Tendsto (fun t => ∫ s in 0..t, ⨆ x, ‖vorticity (fun y => u y s) x‖)
                  (𝓝[<] 1) Filter.atTop :=
  theorem_1_of_inputs' fts_inputs'

end Work.FTS.FinalV2

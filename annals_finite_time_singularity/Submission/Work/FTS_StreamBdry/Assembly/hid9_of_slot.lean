import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.sb0_psiField_proved
import Submission.Work.FTS_StreamBdry.sb1_gauge_proved
import Submission.Work.FTS_StreamBdry.sb2_c2_proved
import Submission.Work.FTS_StreamBdry.sb2_dthDV_proved
import Submission.Work.FTS_StreamBdry.sb6_rates_proved
import Submission.Work.FTS_StreamBdry.SB5.sb5_decay
import Submission.Work.FTS_StreamBdry.Inputs.slice_inputs_of_slot
import Submission.Work.FTS_StreamBdry.SB3.psiP_c2
import Submission.Work.FTS_StreamBdry.SB3.psiP_DzLe
import Submission.Work.FTS_StreamBdry.SB3.psiP_D3_le
import Submission.Work.FTS_StreamBdry.SB3.law_psiP
import Submission.Work.FTS_StreamBdry.SB25.gaugeMode_facts
import Submission.Work.FTS_StreamBdry.SB25.bslOp_lincombQd
import Submission.Work.FTS_StreamBdry.SB25.oddPerS_pieces
import Submission.Work.FTS_StreamBdry.Assembly.srcOK_of_slot
import Submission.Work.FTS_StreamBdry.Assembly.near0_of_slot
import Submission.Work.FTS_BSIdentP.Producers
import Submission.Work.FTS_FinalLeaves.psiCan_C3_proved
import Submission.Work.FTS.H2.PhiStarE5.Locality

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.Assembly

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StreamBdryIface
open scoped Real
open scoped Topology
open Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## §1 The physical vorticity only sees the slice on the quadrant

`physOmega a A B (extG g) C` and `physOmega a A B (extG G) C` agree at every point whose clock
time is nonnegative, provided `G = g` on `z > 0`, `θ ∈ Iθ`, `τ ≥ 0`: the profile tested at a point
only involves the slice at `z = ρ(x)^{3a}/B(τ)` (or at `z = 0`, where `extG` vanishes) and at the
two angles `±θ(x)`, both of which lie in `Iθ`. -/

/-- On the closed strip `z > 0`, `θ ∈ Iθ`, `τ ≥ 0`, the two extensions `extG g` and `extG G` agree
wherever the profile tests them. -/
theorem gSlice_extG_congr {g G : Fam} {τ z θ : ℝ} (hτ : 0 ≤ τ)
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ)
    (h : z = 0 ∨ (0 < z ∧ θ ∈ Work.Spaces.Iθ)) :
    Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG g) τ z θ
      = Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG G) τ z θ := by
  rcases h with rfl | ⟨hz, hθ⟩
  · simp only [Work.FTS.Regularity.gSlice, Work.FTS.RegPkgGal.extG_of_nonpos (le_refl (0 : ℝ))]
  · simp only [Work.FTS.Regularity.gSlice, Work.FTS.RegPkgGal.extG_of_pos hz hτ,
      hG z θ τ hz hθ hτ]

/-- The profile only tests the slice at `z > 0` (or `z = 0`) and `|θ| ≤ π/2`. -/
theorem profile_extG_congr {a : ℝ} {g G : Fam} {τ z θ : ℝ} (hτ : 0 ≤ τ)
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ)
    (hz : z = 0 ∨ 0 < z) (hθ : |θ| ≤ π / 2) :
    Work.ConstructionInstance.profile (Work.FTS.Regularity.pExp a)
        (Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG g) τ) z θ
      = Work.ConstructionInstance.profile (Work.FTS.Regularity.pExp a)
        (Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG G) τ) z θ := by
  have hθ' := abs_le.mp hθ
  by_cases hθ0 : 0 ≤ θ
  · rw [Work.ConstructionInstance.profile_of_nonneg hθ0,
      Work.ConstructionInstance.profile_of_nonneg hθ0,
      gSlice_extG_congr hτ hG (hz.elim Or.inl (fun hz => Or.inr ⟨hz, ⟨hθ0, hθ'.2⟩⟩))]
  · rw [Work.ConstructionInstance.profile_of_neg hθ0,
      Work.ConstructionInstance.profile_of_neg hθ0,
      gSlice_extG_congr hτ hG (hz.elim Or.inl (fun hz => Or.inr ⟨hz, ⟨by linarith [hθ'.1],
        by linarith [hθ'.2]⟩⟩))]

/-- **`physOmega` only sees the slice on `z > 0`, `θ ∈ Iθ`, `τ ≥ 0`**: two families `g`, `G`
agreeing there (in the `extG` extension) give the same physical vorticity. -/
theorem physOmega_extG_congr {a : ℝ} {A B : ℝ → ℝ} {g G : Fam}
    {C : Work.FTS.Physical.PhysClock} (hB : ∀ τ : ℝ, 0 ≤ τ → 0 < B τ)
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) {t : ℝ}
    (hτ : 0 ≤ Work.FTS.Physical.clockInv C t) (x : Work.FTS.Physical.R3) :
    Work.FTS.Physical.physOmega a A B (Work.FTS.RegPkgGal.extG g) C x t
      = Work.FTS.Physical.physOmega a A B (Work.FTS.RegPkgGal.extG G) C x t := by
  rw [Work.FTS.Physical.physOmega_apply, Work.FTS.Physical.physOmega_apply,
    Work.FTS.Regularity.physVort_apply, Work.FTS.Regularity.physVort_apply,
    Work.ConstructionInstance.omegaSz_apply, Work.ConstructionInstance.omegaSz_apply]
  have hz0 : 0 ≤ Work.Cyl.rho x ^ Work.FTS.Regularity.pExp a
      / B (Work.FTS.Physical.clockInv C t) :=
    div_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (le_of_lt (hB _ hτ))
  have hz : Work.Cyl.rho x ^ Work.FTS.Regularity.pExp a / B (Work.FTS.Physical.clockInv C t) = 0
      ∨ 0 < Work.Cyl.rho x ^ Work.FTS.Regularity.pExp a
          / B (Work.FTS.Physical.clockInv C t) := by
    rcases eq_or_lt_of_le hz0 with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  have hθab : |Work.Cyl.theta x| ≤ π / 2 := by
    rw [Work.Cyl.theta, abs_le]
    exact ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _), le_of_lt (Real.arctan_lt_pi_div_two _)⟩
  rw [profile_extG_congr hτ hG hz hθab]

/-! ## §2 The elliptic law for the family handed to BSIdent -/

/-- The elliptic law `bslOp αG (psiP αG Ψ) = F` for the `U`-slot part, on the open quadrant:
`Ψ = psiP αG Ψ + κ·gaugeMode αG` (SB1′), `bslOp` is linear on the quadrant and kills the gauge
mode (`SB25.gaugeMode_facts`), and `bslOp Ψ = F` is the first conjunct of `IsBslSolPos`. -/
theorem bslOp_psiP_slice {a M : ℝ} (ha : 0 < a) {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    {τ : ℝ}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos (Work.FTS.Regularity.pExp a)
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ)
      (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ))
    (h3 : ContDiffOn ℝ 3 (Function.uncurry (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ))
      Work.Construction.Qd)
    (hslot : SlotBd (Work.FTS.Regularity.pExp a)
      (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ) M) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Elliptic.bslOp (Work.FTS.Regularity.pExp a)
        (psiP (Work.FTS.Regularity.pExp a) (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ)) z θ
        = Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ z θ := by
  intro z θ hmem
  obtain ⟨hz, hθ1, hθ2⟩ := Work.FTS_StreamBdry.mem_Qd.mp hmem
  have hαG : 0 < Work.FTS.Regularity.pExp a := Work.FTS.Regularity.pExp_pos ha
  obtain ⟨κ, hκ⟩ := Work.FTS_StreamBdry.sb1_gauge_proved (αG := Work.FTS.Regularity.pExp a)
    (M := M) hαG h3 hslot
  have hC2 : ContDiffOn ℝ 2 (Function.uncurry (psiP (Work.FTS.Regularity.pExp a)
      (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ))) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.psiP_c2 hαG h3 hslot
  have hgau : ContDiffOn ℝ 2 (Function.uncurry (gaugeMode (Work.FTS.Regularity.pExp a)))
      Work.Construction.Qd :=
    (Work.FTS_StreamBdry.SB25.contDiffOn_uncurry_gaugeMode
      (Work.FTS.Regularity.pExp a)).of_le le_top
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (Work.FTS_StreamBdry.cos_pos_of_Qd hmem)
  have hnbhd : Work.Construction.Qd ∈ 𝓝 (z, θ) :=
    Work.FTS_StreamBdry.SB25.qd_isOpen.mem_nhds ⟨hz, hθ1, hθ2⟩
  have hev : ∀ᶠ q in 𝓝 (z, θ),
      (fun z θ => slice (Work.FTS.Nonlin.PsiCan Φs E g) τ z θ) q.1 q.2
        = (fun z θ =>
            psiP (Work.FTS.Regularity.pExp a) (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ) z θ
              + κ * gaugeMode (Work.FTS.Regularity.pExp a) z θ) q.1 q.2 :=
    Filter.mem_of_superset hnbhd (fun q hq => hκ q.1 q.2 hq)
  have hcongr : Work.Elliptic.bslOp (Work.FTS.Regularity.pExp a)
        (fun z θ => slice (Work.FTS.Nonlin.PsiCan Φs E g) τ z θ) z θ
      = Work.Elliptic.bslOp (Work.FTS.Regularity.pExp a) (fun z θ =>
          psiP (Work.FTS.Regularity.pExp a) (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ) z θ
            + κ * gaugeMode (Work.FTS.Regularity.pExp a) z θ) z θ :=
    Work.FTS.H2.PhiStarE5.bslOp_congr_of_eventuallyEq (Work.FTS.Regularity.pExp a) hev
  have hg2 : ContDiffAt ℝ 2 (Function.uncurry (fun z θ =>
      κ * gaugeMode (Work.FTS.Regularity.pExp a) z θ)) (z, θ) :=
    (hgau.contDiffAt hnbhd).const_smul κ
  have hadd := Work.Elliptic.bslOp_add (Work.FTS.Regularity.pExp a)
    (psiP (Work.FTS.Regularity.pExp a) (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ))
    (fun z θ => κ * gaugeMode (Work.FTS.Regularity.pExp a) z θ) z θ hcos
    (hC2.contDiffAt hnbhd) hg2
  have hD0 : Work.Elliptic.bslOp (Work.FTS.Regularity.pExp a)
      (fun z θ => κ * gaugeMode (Work.FTS.Regularity.pExp a) z θ) z θ = 0 := by
    rw [Work.FTS.BSIdent.OddExt.bslOp_const_mul (Work.FTS.Regularity.pExp a) κ
        (gaugeMode (Work.FTS.Regularity.pExp a)) z θ,
      ((Work.FTS_StreamBdry.SB25.gaugeMode_facts hαG).2 z θ hmem).2, mul_zero]
  calc Work.Elliptic.bslOp (Work.FTS.Regularity.pExp a)
        (psiP (Work.FTS.Regularity.pExp a) (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ)) z θ
      = Work.Elliptic.bslOp (Work.FTS.Regularity.pExp a) (fun z θ =>
          psiP (Work.FTS.Regularity.pExp a) (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ) z θ
            + κ * gaugeMode (Work.FTS.Regularity.pExp a) z θ) z θ := by
        rw [hadd, hD0, add_zero]
    _ = Work.Elliptic.bslOp (Work.FTS.Regularity.pExp a)
          (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ) z θ := hcongr.symm
    _ = Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ z θ := hsol.1 z hz θ hθ1 hθ2

/-- The elliptic law for the family `psiHatP` handed to BSIdent: on the quadrant `psiHatP` *is* the
`U`-slot part of the canonical slice (`oddPerS` is the identity there), so its law is that of
`psiP`, and `Ftau = F_* + g` with `g = extG G` on the quadrant. -/
theorem hlaw_of_slot {a C₀ Ce Cs : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g G : Work.FTS.Galerkin.Fam} {A B : ℝ → ℝ}
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp a) Φs E g)
    (h3 : ∀ τ : ℝ, 0 ≤ τ → ContDiffOn ℝ 3
      (Function.uncurry (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ)) Work.Construction.Qd)
    (hslot : ∀ τ : ℝ, 0 ≤ τ → ∃ M : ℝ,
      SlotBd (Work.FTS.Regularity.pExp a) (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ) M)
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) :
    ∀ (C : Work.FTS.Physical.PhysClock) (t : ℝ), t ∈ Set.Ioo (0 : ℝ) C.T →
      ∀ w θ : ℝ, 0 < w → 0 < θ → θ < π / 2 →
        Work.Elliptic.bslOp (Work.FTS.Regularity.pExp a)
            (fun z θ' => psiHatP (Work.FTS.Regularity.pExp a) Φs E g z θ'
              (Work.FTS.Physical.clockInv C t)) w θ
          = Work.Construction.Fstar (Work.FTS.Regularity.pExp a) w θ
            + Work.FTS.RegPkgGal.extG G w θ (Work.FTS.Physical.clockInv C t) := by
  intro C t ht w θ hw hθ1 hθ2
  have htIco : t ∈ Set.Ico (0 : ℝ) C.T := ⟨le_of_lt ht.1, ht.2⟩
  have hτ : 0 ≤ Work.FTS.Physical.clockInv C t := Work.FTS.Physical.clockInv_nonneg C htIco
  have hmem : (w, θ) ∈ Work.Construction.Qd := ⟨hw, hθ1, hθ2⟩
  obtain ⟨M, hM⟩ := hslot (Work.FTS.Physical.clockInv C t) hτ
  have hev : ∀ᶠ q in 𝓝 (w, θ),
      (fun z θ' => psiHatP (Work.FTS.Regularity.pExp a) Φs E g z θ'
          (Work.FTS.Physical.clockInv C t)) q.1 q.2
        = (fun z θ' => psiP (Work.FTS.Regularity.pExp a)
            (slice (Work.FTS.Nonlin.PsiCan Φs E g) (Work.FTS.Physical.clockInv C t)) z θ')
          q.1 q.2 := by
    filter_upwards [Work.FTS_StreamBdry.SB25.qd_isOpen.mem_nhds hmem] with p hp
    obtain ⟨z, θ'⟩ := p
    obtain ⟨hz, hθ'1, hθ'2⟩ := Work.FTS_StreamBdry.mem_Qd.mp hp
    simp only [psiHatP, if_pos hz,
      Work.FTS_StreamBdry.SB25.oddPerS_of_mid (P := psiP (Work.FTS.Regularity.pExp a)
        (slice (Work.FTS.Nonlin.PsiCan Φs E g) (Work.FTS.Physical.clockInv C t)))
        (by linarith [Real.pi_pos]) (le_of_lt hθ'2),
      Work.FTS_StreamBdry.SB25.oddCore_of_pos _ _ _ hθ'1]
  have hcongr : Work.Elliptic.bslOp (Work.FTS.Regularity.pExp a)
        (fun z θ' => psiHatP (Work.FTS.Regularity.pExp a) Φs E g z θ'
          (Work.FTS.Physical.clockInv C t)) w θ
      = Work.Elliptic.bslOp (Work.FTS.Regularity.pExp a)
          (psiP (Work.FTS.Regularity.pExp a)
            (slice (Work.FTS.Nonlin.PsiCan Φs E g) (Work.FTS.Physical.clockInv C t))) w θ :=
    Work.FTS.H2.PhiStarE5.bslOp_congr_of_eventuallyEq (Work.FTS.Regularity.pExp a) hev
  rw [hcongr]
  rw [bslOp_psiP_slice (ha := ha) (Φs := Φs) (E := E) (g := g)
      (τ := Work.FTS.Physical.clockInv C t) (M := M)
      (hsol := hSol.1 (Work.FTS.Physical.clockInv C t) hτ) (h3 _ hτ) hM w θ hmem]
  simp only [Work.Construction.Ftau]
  rw [← (Work.FTS.RegPkgGal.extG_of_pos hw hτ).trans
    (hG w θ (Work.FTS.Physical.clockInv C t) hw ⟨le_of_lt hθ1, le_of_lt hθ2⟩ hτ)]

/-! ## §3 The assembly -/

theorem hid9_of_slot {a C₀ Ce Cs : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp a) u →
      Work.FTS.VocabO.EllPkgGo (Work.FTS.Regularity.pExp a) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp a) 6 Ce u (E u))
    (hEL : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp a) E)
    (hStar : Work.FTS.VocabO2.StarPkgo2 (Work.FTS.Regularity.pExp a) Cs Φs) :
    ∀ (g G : Work.FTS.Galerkin.Fam) (A B : ℝ → ℝ) (C : Work.FTS.Physical.PhysClock),
      Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp a) Φs E g →
      Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp a) C₀ Φs E g →
      Work.FTS.Final.ClockData (Work.FTS.Regularity.pExp a)
        (Work.FTS.Nonlin.PsiCan Φs E g) g A B C →
      (∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G)) →
      (∀ τ : ℝ, 0 ≤ τ → ∃ M : ℝ, Work.FTS.StreamBdryIface.SlotBd (Work.FTS.Regularity.pExp a)
        (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ) M) →
      (∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) →
      ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ x ∈ Work.FTS.BSIdent.Uax,
        Work.FTS.Physical.physVel
          (fun x s => - Work.FTS.Physical.physOmega a A B (Work.FTS.RegPkgGal.extG g) C x s) x t
          = Work.Cyl.psiField
              (fun r z => Work.FTS.MeridianDyn.merPsi (Work.FTS.Regularity.pExp a) A B
                (Work.FTS.FinalV2.psiFire Φs E g) C r z t) x := by
  intro g G A B C hSol hOK hClock hreg hslot hG t ht x hx
  have hpa : 0 < Work.FTS.Regularity.pExp a := Work.FTS.Regularity.pExp_pos ha
  have htIco : t ∈ Set.Ico (0 : ℝ) C.T := ⟨le_of_lt ht.1, ht.2⟩
  have hτnn : 0 ≤ Work.FTS.Physical.clockInv C t :=
    Work.FTS.Physical.clockInv_nonneg C htIco
  have hB : ∀ τ : ℝ, 0 ≤ τ → 0 < B τ := hClock.2.2.2.2
  -- (13′) `C³` of the slices
  have hC3 : ∀ τ : ℝ, 0 ≤ τ → ContDiffOn ℝ 3
      (Function.uncurry (fun z θ => Work.FTS.Nonlin.PsiCan Φs E g z θ τ))
      Work.Construction.Qd :=
    Work.FTS_FinalLeaves.psiCan_C3_proved hEL hStar hOK
  -- the adapter: `SrcOK` of the source family
  have hSrc := srcOK_of_slot (a := a) (A := A) (B := B) ha ha13 hreg hG
  -- the third-order bound on `psiP`
  have hD3 : ∀ τ : ℝ, 0 ≤ τ → ∃ K : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 3,
      |Work.Spaces.DzIter j (psiP (Work.FTS.Regularity.pExp a)
        (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ)) z θ|
        ≤ K * Work.Construction.s2 θ := by
    intro τ hτ
    obtain ⟨M, hM⟩ := hslot τ hτ
    refine ⟨max M (2 * M / Work.FTS.Regularity.pExp a), fun z θ hzθ j hj => ?_⟩
    rcases Nat.lt_or_ge j 3 with hj3 | hj3
    · have h := (Work.FTS_StreamBdry.SB3.psiP_DzLe hpa (hC3 τ hτ) hM) z θ hzθ j (by omega)
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Work.FTS_StreamBdry.s2_nonneg_of_Iθ (Work.FTS_StreamBdry.Qd_theta_Iθ hzθ)))
    · have hj3' : j = 3 := by omega
      subst hj3'
      have h := Work.FTS_StreamBdry.SB3.psiP_D3_le hpa (hC3 τ hτ) hM z θ hzθ
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Work.FTS_StreamBdry.s2_nonneg_of_Iθ (Work.FTS_StreamBdry.Qd_theta_Iθ hzθ)))
  -- SB2: the `C²` regularity of the odd extension of `psiP`
  have hPsm : ∀ τ : ℝ, 0 ≤ τ → ContDiffOn ℝ 2
      (Function.uncurry (oddPerS (psiP (Work.FTS.Regularity.pExp a)
        (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ))))
      (Set.Ioi 0 ×ˢ Set.Ioo (-(π / 2) - 1) (π / 2 + 1)) := by
    intro τ hτ
    obtain ⟨M, hM⟩ := hslot τ hτ
    obtain ⟨L, Mf, hF⟩ := hSrc τ hτ
    exact sb2_c2_proved (αG := Work.FTS.Regularity.pExp a) (M := M) hpa (hSol.1 τ hτ)
      (hC3 τ hτ) hM hF
      (sb2_dthDV_proved (αG := Work.FTS.Regularity.pExp a) (M := M) (L := L) (Mf := Mf) hpa
        (hSol.1 τ hτ) (hC3 τ hτ) hM hF (hD3 τ hτ))
  -- SB1′: the gauge decomposition
  have hdec : ∀ τ : ℝ, 0 ≤ τ → ∃ κ : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      slice (Work.FTS.Nonlin.PsiCan Φs E g) τ z θ
        = psiP (Work.FTS.Regularity.pExp a)
            (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ) z θ
          + κ * gaugeMode (Work.FTS.Regularity.pExp a) z θ := by
    intro τ hτ
    obtain ⟨M, hM⟩ := hslot τ hτ
    exact sb1_gauge_proved (αG := Work.FTS.Regularity.pExp a) (M := M) hpa (hC3 τ hτ) hM
  -- SB0: the gauge mode is invisible to `Cyl.psiField`
  have hSB0 := sb0_psiField_proved (a := a) (ha := ha) (A := A) (B := B) (C := C)
    (hC3 := hC3) (hdec := hdec) (hPsm := hPsm) (hB := hB)
  -- the BSIdent-P2 inputs for `Φ := psiHatP`
  have hΦsm : ∀ t' ∈ Set.Ioo (0 : ℝ) C.T, ∀ w θ : ℝ, 0 < w → -π / 2 - 1 < θ →
      θ < π / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ =>
        psiHatP (Work.FTS.Regularity.pExp a) Φs E g p.1 p.2 (Work.FTS.Physical.clockInv C t'))
        (w, θ) := by
    intro t' ht' w θ hw hθ1 hθ2
    have hτ' : 0 ≤ Work.FTS.Physical.clockInv C t' :=
      Work.FTS.Physical.clockInv_nonneg C ⟨le_of_lt ht'.1, ht'.2⟩
    have hmem : (w, θ) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(π / 2) - 1) (π / 2 + 1) :=
      ⟨hw, by linarith, hθ2⟩
    have hev : (fun p : ℝ × ℝ =>
          psiHatP (Work.FTS.Regularity.pExp a) Φs E g p.1 p.2 (Work.FTS.Physical.clockInv C t'))
        =ᶠ[nhds (w, θ)]
        Function.uncurry (oddPerS (psiP (Work.FTS.Regularity.pExp a)
          (slice (Work.FTS.Nonlin.PsiCan Φs E g) (Work.FTS.Physical.clockInv C t')))) := by
      have hset : IsOpen ((Prod.fst : ℝ × ℝ → ℝ) ⁻¹' Set.Ioi (0 : ℝ)) :=
        isOpen_Ioi.preimage (continuous_fst : Continuous (Prod.fst : ℝ × ℝ → ℝ))
      filter_upwards [hset.mem_nhds (show (w, θ) ∈ (Prod.fst) ⁻¹' Set.Ioi (0 : ℝ) from hw)]
        with p hp
      simp only [Function.uncurry, psiHatP]
      rw [if_pos (show (0 : ℝ) < p.1 from hp)]
    exact (ContDiffWithinAt.contDiffAt
      ((hPsm (Work.FTS.Physical.clockInv C t') hτ').contDiffWithinAt hmem)
      ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds hmem)).congr_of_eventuallyEq hev
  have hΦplane : ∀ t' ∈ Set.Ioo (0 : ℝ) C.T, ∀ w : ℝ, 0 < w →
      psiHatP (Work.FTS.Regularity.pExp a) Φs E g w 0 (Work.FTS.Physical.clockInv C t') = 0 := by
    intro t' ht' w hw
    simp only [psiHatP, if_pos hw, oddPerS]
    rw [if_neg (by linarith [Real.pi_pos] : ¬ ((0 : ℝ) < -(π / 2))),
      if_pos (by linarith [Real.pi_pos] : (0 : ℝ) ≤ π / 2)]
    norm_num
  have hΦaxis : ∀ t' ∈ Set.Ioo (0 : ℝ) C.T, ∀ w : ℝ, 0 < w →
      psiHatP (Work.FTS.Regularity.pExp a) Φs E g w (π / 2)
        (Work.FTS.Physical.clockInv C t') = 0 := by
    intro t' ht' w hw
    simp only [psiHatP, if_pos hw, oddPerS]
    rw [if_neg (by linarith [Real.pi_pos] : ¬ (π / 2 < -(π / 2))), if_pos le_rfl,
      if_pos (by linarith [Real.pi_pos] : (0 : ℝ) < π / 2)]
    exact Work.FTS_StreamBdry.SB6.psiP_pi_div_two _ _ _
  have hrate : ∀ t' ∈ Set.Ioo (0 : ℝ) C.T, ∃ lam C₀' : ℝ, 0 < lam ∧ 0 < C₀' ∧
      2 ≤ Work.FTS.Regularity.pExp a * lam ∧ ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < π / 2 →
      |psiHatP (Work.FTS.Regularity.pExp a) Φs E g w θ (Work.FTS.Physical.clockInv C t')|
          ≤ C₀' * (π / 2 - θ) * (1 + w) ^ (-lam) ∧
      |deriv (fun w' : ℝ =>
          psiHatP (Work.FTS.Regularity.pExp a) Φs E g w' θ
            (Work.FTS.Physical.clockInv C t')) w|
        ≤ C₀' * (π / 2 - θ) * (1 + w) ^ (-lam - 1) ∧
      |deriv (fun θ' : ℝ =>
          psiHatP (Work.FTS.Regularity.pExp a) Φs E g w θ'
            (Work.FTS.Physical.clockInv C t')) θ|
        ≤ C₀' * (1 + w) ^ (-lam) := by
    intro t' ht'
    have hτ' : 0 ≤ Work.FTS.Physical.clockInv C t' :=
      Work.FTS.Physical.clockInv_nonneg C ⟨le_of_lt ht'.1, ht'.2⟩
    obtain ⟨M, hM⟩ := hslot (Work.FTS.Physical.clockInv C t') hτ'
    obtain ⟨L, Mf, hF⟩ := hSrc (Work.FTS.Physical.clockInv C t') hτ'
    obtain ⟨c, hcpos, hc⟩ := sb6_rates_proved (αG := Work.FTS.Regularity.pExp a) (M := M)
      (L := L) (Mf := Mf) hpa (hSol.1 (Work.FTS.Physical.clockInv C t') hτ')
      (hC3 (Work.FTS.Physical.clockInv C t') hτ') hM hF
      (near0_of_slot (C₀ := C₀) (Ce := Ce) (Cs := Cs) ha ha13 hEll hEL hStar hSol hOK hreg hG
        (Work.FTS.Physical.clockInv C t') hτ')
    refine ⟨4 / Work.FTS.Regularity.pExp a, c, by positivity, hcpos, ?_, ?_⟩
    · have : Work.FTS.Regularity.pExp a * (4 / Work.FTS.Regularity.pExp a) = 4 := by
        rw [mul_div_cancel₀ _ (ne_of_gt hpa)]
      linarith
    · intro w θ hw hθ hθ2
      obtain ⟨h1, h2, h3⟩ := hc w θ hw hθ hθ2
      exact ⟨by simpa only [psiHatP] using h1, by simpa only [psiHatP] using h2,
        by simpa only [psiHatP] using h3⟩
  -- BSIdent-P2
  have hP2 := Work.FTS_BSIdentP.hid_of_corrected'_slim_proved (α := ⟨a, ha.le⟩) (A := A) (B := B)
    (g := Work.FTS.RegPkgGal.extG G) (C := C) (Φ := psiHatP (Work.FTS.Regularity.pExp a) Φs E g)
    hreg (hlaw_of_slot (A := A) (B := B) (C₀ := C₀) (Ce := Ce) (Cs := Cs) ha ha13 hSol hC3 hslot hG C)
    hΦsm hΦplane hΦaxis hrate
  have hP2' : Work.FTS.Physical.physVel
      (fun x s => - Work.FTS.Physical.physOmega a A B (Work.FTS.RegPkgGal.extG G) C x s) x t
      = Work.Cyl.psiField (fun r z => Work.FTS.BSIdent.merPsi a A B
          (psiHatP (Work.FTS.Regularity.pExp a) Φs E g) C r z t) x :=
    hP2 t ht x hx
  -- the two vorticity families agree at the clock time
  have hcong : (fun y =>
        - Work.FTS.Physical.physOmega a A B (Work.FTS.RegPkgGal.extG g) C y t)
      = (fun y =>
        - Work.FTS.Physical.physOmega a A B (Work.FTS.RegPkgGal.extG G) C y t) := by
    funext y
    rw [physOmega_extG_congr (a := a) (A := A) (B := B) (C := C) (t := t) hB hG hτnn y]
  have hSB0' := hSB0 t ht x hx
  calc Work.FTS.Physical.physVel
        (fun x s => - Work.FTS.Physical.physOmega a A B (Work.FTS.RegPkgGal.extG g) C x s) x t
      = Work.FTS.Physical.physVel
        (fun x s => - Work.FTS.Physical.physOmega a A B (Work.FTS.RegPkgGal.extG G) C x s) x t := by
        change Work.LWP.biotSavart (fun y =>
              - Work.FTS.Physical.physOmega a A B (Work.FTS.RegPkgGal.extG g) C y t) x
            = Work.LWP.biotSavart (fun y =>
              - Work.FTS.Physical.physOmega a A B (Work.FTS.RegPkgGal.extG G) C y t) x
        rw [hcong]
    _ = Work.Cyl.psiField (fun r z => Work.FTS.BSIdent.merPsi a A B
          (psiHatP (Work.FTS.Regularity.pExp a) Φs E g) C r z t) x := hP2'
    _ = Work.Cyl.psiField
          (fun r z => Work.FTS.MeridianDyn.merPsi (Work.FTS.Regularity.pExp a) A B
            (Work.FTS.FinalV2.psiFire Φs E g) C r z t) x := hSB0'.symm

end Work.FTS_StreamBdry.Assembly

/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.Lavaurs.Defs` — chain C: the exact real transit phase

Design: `Submission/Work/NOTES_LEAD_mandelbar_implosion.md` §2.  The delivered transit coordinate
`Work.PARIMPL.transU P nIn c = −approxUin P c (entryPt P nIn c)` evaluates the **approximate**
model coordinate at a **fixed-depth** entry point; its phase therefore carries a fixed error that
does not vanish as `c → c₀` (note §1, F2–F4), so `LockstepAll … transU …` is false in general.

Chain C replaces it by the **exact real Lavaurs phase**

`transPh P x₀ θ c = x₀ + θ − π/λ_c`

with `x₀ = Re φa(z_e)` the (real part of the) flower's attracting coordinate of the entry point and
`θ` an existential **real** constant (the Lavaurs constant, `s_r − s_a` in the design).  Its
imaginary part is `0` *exactly*, its continuity is the continuity of `λ` on `Nm`, and its
blow-up at the parabolic locus is the blow-up of `π/λ_c` — all three are trivial (this file).

The **single** analytic export of the whole implosion endgame is then

`LavaursPhase d P Pa φa Ψ nIn := ∃ θ : ℝ, LockstepAll c₀ P.Nm (transPh P (Re φa z_e) θ) nIn …`.

## Contents

* `transPh`, `LavaursPhase` — the definition and the export;
* `transPh_im`, `continuousOn_transPh`, `tendsto_transPh`, `transPh_blow` — the trivial
  properties of §2.2 of the design;
* the vocabulary of §3.0 for the proof chain: the `c₀`-chart coordinate `w0`, the repelling model
  coordinate `approxCoordRep`, and the two **geometric** windows `WinG`/`WoutG` (compact, defined
  in the `c₀`-chart, with no spurious components — cf. F1 of the design note, which is why the
  level-set windows `Win`/`Wout` of chain A cannot be used).
-/
import Submission.Work.PARIMPL2.ExitTracking
import Submission.Work.PARIMPL.Nm_mem_closure

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.PARIMPL (ParNormal entryPt Ft gtc chartZeta)

variable {c₀ : ℂ}

/-! ## The phase and the export -/

/-- **The exact transit phase** (`NOTES_LEAD_mandelbar_implosion.md` §2.1): a **real** number,
`x₀ + θ − π/λ_c`, where `x₀ = Re φa (z_e)` is the real part of the flower's attracting coordinate
of the entry point and `θ : ℝ` is the Lavaurs constant. -/
noncomputable def transPh {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : ParNormal d)
    (x₀ θ : ℝ) (c : ℂ) : ℂ :=
  ((x₀ + θ - Real.pi / P.lam c : ℝ) : ℂ)

@[simp] theorem transPh_apply {d : Work.EL.RootParabolic c₀} (P : ParNormal d)
    (x₀ θ : ℝ) (c : ℂ) : transPh P x₀ θ c = ((x₀ + θ - Real.pi / P.lam c : ℝ) : ℂ) := rfl

/-- **The single implosion export.**  With `x₀ := (φa (entryPt P nIn c₀)).re` and `v := x₀ − nIn`,
`Work.PARIMPL2.LockstepAll`'s level is `u = θ − π/λ_c + n + φa y`, and the transit starts at the
`nIn`-th iterate of the critical point of `c`. -/
def LavaursPhase {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) (P : ParNormal d)
    (Pa : Set ℂ) (φa Ψ : ℂ → ℂ) (nIn : ℕ) : Prop :=
  ∃ θ : ℝ, LockstepAll c₀ P.Nm (transPh P (φa (entryPt P nIn c₀)).re θ) nIn
    (fun c z => Ft c z) Pa φa Ψ ((φa (entryPt P nIn c₀)).re - (nIn : ℝ))

/-! ## The trivial properties (§2.2 of the design) -/

/-- The phase is **real**: its imaginary part is `0` exactly. -/
@[simp] theorem transPh_im {d : Work.EL.RootParabolic c₀} (P : ParNormal d)
    (x₀ θ : ℝ) (c : ℂ) : (transPh P x₀ θ c).im = 0 := by
  simp [transPh]

/-- The phase is a real number. -/
theorem transPh_eq_ofReal {d : Work.EL.RootParabolic c₀} (P : ParNormal d)
    (x₀ θ : ℝ) (c : ℂ) :
    transPh P x₀ θ c = ((x₀ + θ - Real.pi / P.lam c : ℝ) : ℂ) := rfl

/-- **Continuity** on the implosion side: `π/λ` is continuous there (`λ` is, and `λ ≠ 0`). -/
theorem continuousOn_transPh {d : Work.EL.RootParabolic c₀} (P : ParNormal d) (x₀ θ : ℝ) :
    ContinuousOn (transPh P x₀ θ) P.Nm := by
  have hC : ContinuousOn (fun c : ℂ => ((x₀ + θ - Real.pi / P.lam c : ℝ) : ℂ)) P.Nm := by
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    refine ContinuousOn.sub continuousOn_const ?_
    exact ContinuousOn.div continuousOn_const P.continuousOn_lam_Nm
      (fun c hc => ne_of_gt (P.lam_pos_of_mem_Nm hc))
  exact hC

/-- **The phase blow-up**: along the implosion side at a point of the parabolic locus,
`Re (transPh …) → −∞`. -/
theorem tendsto_transPh {d : Work.EL.RootParabolic c₀} (P : ParNormal d) (x₀ θ : ℝ)
    (a : ℂ) (ha : P.a2 a = 0) (hab : a ∈ ball c₀ P.ρ₀) :
    Tendsto (fun c => (transPh P x₀ θ c).re) (𝓝[P.Nm] a) atBot := by
  have hlam : Tendsto P.lam (𝓝[P.Nm] a) (𝓝 0) := P.tendsto_lam a ha hab
  rw [tendsto_atBot]
  intro b
  by_cases hK : x₀ + θ - b ≤ 0
  · filter_upwards [self_mem_nhdsWithin] with c hc
    have hpos : 0 < Real.pi / P.lam c := div_pos Real.pi_pos (P.lam_pos_of_mem_Nm hc)
    simp only [transPh, Complex.ofReal_re]
    linarith
  · push_neg at hK
    have hKpos : 0 < x₀ + θ - b := hK
    have hpos : 0 < Real.pi / (x₀ + θ - b) := div_pos Real.pi_pos hKpos
    filter_upwards [self_mem_nhdsWithin,
      hlam.eventually (Iic_mem_nhds hpos)] with c hcNm hc
    have hlampos : 0 < P.lam c := P.lam_pos_of_mem_Nm hcNm
    have hstep : (x₀ + θ - b) * P.lam c ≤ Real.pi := by
      have h1 : (x₀ + θ - b) * (Real.pi / (x₀ + θ - b)) = Real.pi :=
        mul_div_cancel₀ _ (ne_of_gt hKpos)
      calc (x₀ + θ - b) * P.lam c
          ≤ (x₀ + θ - b) * (Real.pi / (x₀ + θ - b)) :=
            mul_le_mul_of_nonneg_left hc hKpos.le
        _ = Real.pi := h1
    have hgoal : x₀ + θ - b ≤ Real.pi / P.lam c := by
      rw [le_div_iff₀ hlampos]
      linarith
    simp only [transPh, Complex.ofReal_re]
    linarith

/-- **The quantitative blow-up**: for every depth `R` there is a ball on `Nm` around `c₀` on which
the phase is below `−R`.  This is the `hblow` hypothesis of
`Work.PARIMPL2.exitTrackedWindow_of_lockstep`. -/
theorem transPh_blow {d : Work.EL.RootParabolic c₀} (P : ParNormal d) (x₀ θ : ℝ) :
    ∀ R : ℝ, ∃ ρ : ℝ, 0 < ρ ∧
      ∀ c ∈ P.Nm ∩ ball c₀ ρ, (transPh P x₀ θ c).re ≤ -R := by
  intro R
  have h := tendsto_transPh P x₀ θ c₀ P.a2₀ (by simpa using P.hρ₀)
  rw [tendsto_atBot] at h
  have hev : ∀ᶠ c in 𝓝[P.Nm] c₀, (transPh P x₀ θ c).re ≤ -R := h (-R)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ρ, hρ, hρ'⟩ := hev
  refine ⟨ρ, hρ, fun c hc => ?_⟩
  exact hρ' (by simpa [mem_ball] using hc.2) hc.1

/-! ## The vocabulary of the proof chain (§3.0 of the design) -/

/-- The **`c₀`-chart coordinate** `w₀ = −1/ζ_{c₀} = −P.s c₀/(z − d.z₁)`. -/
noncomputable def w0 {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : ParNormal d) (z : ℂ) : ℂ :=
  -P.s c₀ / (z - d.z₁)

/-- The **repelling model coordinate**: `approxCoordRep κ w = w − κ log (−w)`, the principal
branch of `log (−w)` (fine where `Re w < 0`, which is the repelling region).  It is the reflected
partner of `Work.FatouCoord.approxCoord κ w = w − κ log w`, and the target of the repelling
coordinate on `WoutG`. -/
noncomputable def approxCoordRep (κ w : ℂ) : ℂ := w - κ * Complex.log (-w)

/-- The **incoming geometric window** in the `c₀`-chart (§3.0): compact, defined by the *real and
imaginary parts* of `w₀` (so that it has no far annulus and no log-spirals, unlike the level-set
window `Work.PARIMPL.Win`, cf. F1 of the design note). -/
def WinG {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : ParNormal d) (R H : ℝ) : Set ℂ :=
  {z : ℂ | z ≠ d.z₁ ∧ (w0 P z).re ∈ Set.Icc R (R + 2) ∧ |(w0 P z).im| ≤ H}

/-- The **outgoing geometric window** in the `c₀`-chart. -/
def WoutG {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : ParNormal d) (R H : ℝ) : Set ℂ :=
  {z : ℂ | z ≠ d.z₁ ∧ (w0 P z).re ∈ Set.Icc (-R - 2) (-R) ∧ |(w0 P z).im| ≤ H}

end Work.PARIMPL2

end

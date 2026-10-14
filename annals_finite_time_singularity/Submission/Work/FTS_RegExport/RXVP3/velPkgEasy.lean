import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_RegExport.RXB.l12_aux
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.SysAux.FK_jet_pkg_uniform
import Submission.Work.FTS_RegExport.RXT.SysAux.L12_jet_pkg_uniform
import Submission.Work.FTS_RegExport.RegExportProved
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_majorant
import Submission.Work.Spaces.pz_mixed_mul_le_4

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXVP3.velPkgEasy` — the three *provable* clauses of `VelPkg`

The frozen `VelPkg` (RX-VP) is documented to be unprovable: its `cont` clause is equivalent to the
axis-slope condition (★), see `NOTES_area_state.md` §2(a).  The present lemma isolates the three
clauses of `VelPkg`/`VelPkgSup`/`VelPkgEnd` that are *not* tied to (★):

* `VelPkgEnd.vanishK` — the `O(z)` vanishing of `FK(g)` and `L₁₂(g)` at `z = 0`;
* `VelPkgEnd.c2` — the stream-function slice is `C²` on the open quadrant;
* `VelPkgSup.vth_ends` — `Vθ7 = 2·Uop(Φ)` vanishes at `θ = 0` and `θ = π/2`.

The ingredients are all already in the tree (and axiom-clean):

* `RXT/SysAux/FK_jet_pkg_uniform`, `RXT/SysAux/L12_jet_pkg_uniform` — the weighted jet packages of
  `𝔽K u` and `L₁₂ u` for a *generic* slice, with constants depending only on the weighted bound
  `B` of the slice (this is what makes them uniform in `τ`: `B = Cw·C₀α²` is `τ`-independent);
* `RXA2w/lim_mixed_weighted_proved` — that weighted bound for the strong solution (RX-A2w);
* `RXB/l12_zero_lim_proved` — `L₁₂(slice g τ)(0) = 0` (RX-B);
* `RXT/C2Psi/contDiffOn_slice_PhiR_Q0` — `C³` of the `psiR`-slice on the open quadrant;
* `RXR5/Basic` — the quadrant-congruence plumbing (`AgreeOnQ`, `L12_congr_of_agreeOnQ`, …).

The only genuinely new analytic step is the *large*-`z` bound on `L₁₂`: the weighted bound
`|𝔽K u| ≲ z^{3/2}/(1+z)²` decays, so `L₁₂(z) = L₁₂(1) - ∫₁^z 𝔽K(s)/s ds` (the `L₁₂'`-identity of
the package) is uniformly bounded by `|L₁₂(1)| + ∫₁^∞ C₁ s^{-3/2} ds ≤ C₂ + 2C₁`.
-/

namespace Work.FTS_RegExport.RXVP3

open scoped Real Topology NNReal
open Set Filter MeasureTheory
open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp Jet)
open Work.FTS.RegPkgGal (extG RegPkg' St1Class R5Parts Avort Bdyn)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)
open Work.FTS.RegExportIface

set_option autoImplicit false
set_option maxHeartbeats 800000

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-! ## §1 Elementary estimates for the weight `z^{3/2}/(1+z)²` -/

/-- For `0 < z ≤ 1` the weight `z^{3/2}` is dominated by `z`. -/
private theorem three_halves_le_self {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1) :
    z ^ ((3 : ℝ) / 2) ≤ z := by
  have h32 : z ^ ((3 : ℝ) / 2) = z * Real.sqrt z := by
    rw [show (3 : ℝ) / 2 = (1 : ℝ) + 1 / 2 from by norm_num, Real.rpow_add hz0,
      Real.rpow_one, Real.sqrt_eq_rpow, mul_comm]
  rw [h32]
  have h1 := Real.sqrt_le_one.mpr hz1
  have h2 := Real.sqrt_nonneg z
  nlinarith

/-- For `1 ≤ z` the weight `z^{3/2}` is dominated by `(1+z)^2`. -/
private theorem three_halves_le_sq {z : ℝ} (hz1 : 1 ≤ z) :
    z ^ ((3 : ℝ) / 2) ≤ (1 + z) ^ 2 := by
  have hz0 : (0 : ℝ) < z := lt_of_lt_of_le one_pos hz1
  have h1 : z ^ ((3 : ℝ) / 2) ≤ (1 + z) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow hz0.le (by linarith) (by norm_num)
  have h2 : (1 + z) ^ ((3 : ℝ) / 2) ≤ (1 + z) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have h3 : (1 + z) ^ (2 : ℝ) = (1 + z) ^ 2 := Real.rpow_two _
  exact h1.trans (h2.trans h3.le)

/-- `z^{3/2}/(1+z)² ≤ z` for `0 < z ≤ 1`. -/
private theorem rpow_div_le_self {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1) :
    z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 ≤ z := by
  have h := three_halves_le_self hz0 hz1
  have hden : (1 : ℝ) ≤ (1 + z) ^ 2 := by nlinarith [sq_nonneg z, hz0]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
  nlinarith [Real.rpow_nonneg hz0.le ((3 : ℝ) / 2)]

/-- `z^{3/2}/(1+z)² ≤ 1` for `1 ≤ z`. -/
private theorem rpow_div_le_one {z : ℝ} (hz1 : 1 ≤ z) :
    z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 ≤ 1 := by
  rw [div_le_one (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
  exact three_halves_le_sq hz1

/-- For `1 ≤ s`, `s^{3/2}/((1+s)²·s) ≤ s^{-3/2}`: the integrand of the `L₁₂`-tail is dominated
by the integrable profile `s^{-3/2}`. -/
private theorem rpow_ratio_le {s : ℝ} (hs : 1 ≤ s) :
    s ^ ((3 : ℝ) / 2) / ((1 + s) ^ 2 * s) ≤ s ^ (-(3 / 2 : ℝ)) := by
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le one_pos hs
  have hsp : (0 : ℝ) < (1 + s) ^ 2 := by positivity
  have h32 : s ^ ((3 : ℝ) / 2) = s * Real.sqrt s := by
    rw [show (3 : ℝ) / 2 = (1 : ℝ) + 1 / 2 from by norm_num, Real.rpow_add hs0,
      Real.rpow_one, Real.sqrt_eq_rpow, mul_comm]
  have hsimp : s ^ ((3 : ℝ) / 2) / ((1 + s) ^ 2 * s) = Real.sqrt s / (1 + s) ^ 2 := by
    rw [h32]; field_simp
  have hneg : s ^ (-(3 / 2 : ℝ)) = 1 / s ^ ((3 : ℝ) / 2) := by
    rw [Real.rpow_neg hs0.le (3 / 2), inv_eq_one_div]
  rw [hsimp, hneg,
    div_le_div_iff₀ hsp (by positivity : (0 : ℝ) < s ^ ((3 : ℝ) / 2)), h32]
  have hsq : Real.sqrt s * Real.sqrt s = s := by rw [← sq]; exact Real.sq_sqrt hs0.le
  nlinarith [sq_nonneg s, hs]

/-- `∫₁^z s^{-3/2} ds ≤ 2` for `1 ≤ z`. -/
private theorem integral_rpow_neg_three_halves_le {z : ℝ} (hz : 1 ≤ z) :
    ∫ s in (1 : ℝ)..z, s ^ (-(3 / 2 : ℝ)) ≤ 2 := by
  have hz0 : (0 : ℝ) < z := lt_of_lt_of_le one_pos hz
  have hneq : (0 : ℝ) ∉ Set.uIcc 1 z := by
    rw [Set.uIcc_of_le hz]
    intro h
    linarith [h.1]
  have hval : ∫ s in (1 : ℝ)..z, s ^ (-(3 / 2 : ℝ)) = 2 - 2 * z ^ (-(1 / 2 : ℝ)) := by
    rw [integral_rpow (Or.inr ⟨by norm_num, hneq⟩)]
    rw [show (-(3 / 2 : ℝ)) + 1 = -(1 / 2 : ℝ) from by norm_num, Real.one_rpow]
    field_simp
    ring
  rw [hval]
  have := Real.rpow_nonneg hz0.le (-(1 / 2 : ℝ))
  linarith

/-! ## §2 The lemma -/

theorem velPkgEasy (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    (hEL3 : EllLimOK3 (pExp α) E) (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    {g : Fam} (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 = Work.FTS.LocData6.locG6 (pExp α) L β z θ)
    (hμ : ClockBd α Φs E g) :
    (∀ S > 0, ∃ M : ℝ, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z, 0 < z →
      |Work.Construction.FK (slice (gS α (tauExt g)) τ) z|
        + |Work.Construction.L12 (slice (gS α (tauExt g)) τ) z| ≤ M * min z 1) ∧
    (∀ S > 0, ∀ τ ∈ Set.Icc (0:ℝ) S,
      ContDiffOn ℝ 2 (Function.uncurry (slice (psiR α Φs E (tauExt g)) τ)) Work.FTS.EllipticEst.Q0) ∧
    (∀ S > 0, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z, 0 < z →
      Vθ7 (pExp α) (psiR α Φs E (tauExt g)) z 0 τ = 0 ∧
      Vθ7 (pExp α) (psiR α Φs E (tauExt g)) z (Real.pi / 2) τ = 0) := by
  have hαG : 0 < pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  refine ⟨?_, ?_, ?_⟩
  · -- (1) `vanishK`: `O(z)`-vanishing of `FK` and `L₁₂`, uniformly in `τ`
    intro S hS
    -- the `τ`-independent weighted bound `B` of the slice (`RX-A2w`) and the two uniform packages
    obtain ⟨Cw, _hCw0, hCw⟩ :=
      Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved (αG := pExp α) (C₀ := C₀)
        (Φs := Φs) (E := E) (g := g) hαG hαG1 hOK.2 S hS
    obtain ⟨C₁, hC₁pos, hFKuni⟩ := Work.FTS_RegExport.RXT.SysAux.FK_jet_pkg_uniform Cw
    obtain ⟨C₂, hC₂pos, hL12uni⟩ := Work.FTS_RegExport.RXT.SysAux.L12_jet_pkg_uniform Cw
    refine ⟨5 * (C₁ + C₂) + 1, ?_⟩
    intro τ hτ z hz
    -- the three inputs of the packages for the sanitised slice at `τ`
    have hCd : ContDiffOn ℝ 4 (Function.uncurry (slice (gS α (tauExt g)) τ))
        Work.FTS.EllipticEst.Q0 := by
      refine (hOK.1.1.c4 τ hτ.1).congr (fun p hp => ?_)
      exact Work.FTS_RegExport.RXT.slice_GR_eq (g := g) hτ.1 hp.1 hp.2.1.le hp.2.2.le
    have hEqOn : Set.EqOn (Function.uncurry (slice (gS α (tauExt g)) τ))
        (Function.uncurry (slice g τ)) Work.FTS.EllipticEst.Q0 :=
      fun p hp => Work.FTS_RegExport.RXT.slice_GR_eq (g := g) hτ.1 hp.1 hp.2.1.le hp.2.2.le
    have hb : ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a (slice (gS α (tauExt g)) τ) z θ|
          ≤ Cw * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
      intro b a hba z θ hz hθ hθ2
      rw [Work.FTS_RegExport.RXT.SysAux.mixed_congr_of_isOpen
        Work.FTS.EllipticEst.isOpen_Q0 hEqOn b a z θ
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩)]
      exact hCw τ hτ b a hba z θ hz hθ hθ2
    have h0 : Work.Construction.L12 (slice (gS α (tauExt g)) τ) 0 = 0 := by
      rw [Work.FTS_RegExport.RXR5.L12_congr_of_agreeOnQ
        (Work.FTS_RegExport.RXR5.SG_slice_agreeOnQ α g τ) (le_refl (0 : ℝ))]
      rw [Work.FTS.FinalV2.slice_tauExt g hτ.1]
      exact Work.FTS_RegExport.RXB.l12_zero_lim_proved hαG hOK.2 τ hτ.1
    obtain ⟨_hFKjets, hFK0, hFKcont, _hgint, _hgcont⟩ :=
      hFKuni (slice (gS α (tauExt g)) τ) hCd hb
    obtain ⟨_hL12jets, _hL12c3, hL12deriv⟩ :=
      hL12uni (slice (gS α (tauExt g)) τ) hCd hb h0
    have hL120 : ∀ z : ℝ, 0 < z →
        |Work.Construction.L12 (slice (gS α (tauExt g)) τ) z|
          ≤ C₂ * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) :=
      fun z hz => _hL12jets 0 (by norm_num) z hz
    -- the `L₁₂`-tail bound for `z ≥ 1`, via the derivative identity `L₁₂' = -𝔽K/z`
    have hL12big : ∀ z : ℝ, 1 ≤ z →
        |Work.Construction.L12 (slice (gS α (tauExt g)) τ) z| ≤ 3 * C₁ + C₂ := by
      intro z hz1
      have hsub : Set.uIcc 1 z ⊆ Set.Ioi (0 : ℝ) := by
        intro s hs
        rw [Set.uIcc_of_le hz1] at hs
        exact lt_of_lt_of_le zero_lt_one hs.1
      have hcont : ContinuousOn
          (fun s : ℝ => -(Work.Construction.FK (slice (gS α (tauExt g)) τ) s) / s)
          (Set.uIcc 1 z) := by
        refine ((hFKcont.continuousOn.mono hsub).neg).div continuousOn_id (fun s hs => ?_)
        exact ne_of_gt (hsub hs)
      have hint : IntervalIntegrable
          (fun s : ℝ => -(Work.Construction.FK (slice (gS α (tauExt g)) τ) s) / s)
          volume 1 z := hcont.intervalIntegrable
      have hFTC : ∫ s in (1 : ℝ)..z,
            (-(Work.Construction.FK (slice (gS α (tauExt g)) τ) s) / s)
          = Work.Construction.L12 (slice (gS α (tauExt g)) τ) z
            - Work.Construction.L12 (slice (gS α (tauExt g)) τ) 1 :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x hx => hL12deriv x (by
            rw [Set.uIcc_of_le hz1] at hx
            exact lt_of_lt_of_le zero_lt_one hx.1))
          hint
      have hnorm : |∫ s in (1 : ℝ)..z,
            (-(Work.Construction.FK (slice (gS α (tauExt g)) τ) s) / s)|
          ≤ ∫ s in (1 : ℝ)..z,
              |Work.Construction.FK (slice (gS α (tauExt g)) τ) s| / s := by
        have h := intervalIntegral.norm_integral_le_integral_norm
          (f := fun s : ℝ => -(Work.Construction.FK (slice (gS α (tauExt g)) τ) s) / s)
          (a := (1 : ℝ)) (b := z) (μ := volume) hz1
        rw [Real.norm_eq_abs] at h
        refine h.trans_eq ?_
        refine intervalIntegral.integral_congr (fun s hs => ?_)
        have hs0 : (0 : ℝ) < s := by
          rw [Set.uIcc_of_le hz1] at hs
          exact lt_of_lt_of_le zero_lt_one hs.1
        rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hs0]
      have hmain : ∫ s in (1 : ℝ)..z,
            |Work.Construction.FK (slice (gS α (tauExt g)) τ) s| / s ≤ 2 * C₁ := by
        have hmono : ∫ s in (1 : ℝ)..z,
              |Work.Construction.FK (slice (gS α (tauExt g)) τ) s| / s
            ≤ ∫ s in (1 : ℝ)..z, C₁ * s ^ (-(3 / 2 : ℝ)) := by
          refine intervalIntegral.integral_mono_on hz1 ?_ ?_ (fun s hs => ?_)
          · exact ((hFKcont.continuousOn.mono (fun s hs => by
                rw [Set.uIcc_of_le hz1] at hs
                exact lt_of_lt_of_le zero_lt_one hs.1)).abs).div
              continuousOn_id (fun s hs => by
                rw [Set.uIcc_of_le hz1] at hs
                exact ne_of_gt (lt_of_lt_of_le zero_lt_one hs.1)) |>.intervalIntegrable
          · have hc : ContinuousOn (fun s : ℝ => s ^ (-(3 / 2 : ℝ))) (Set.uIcc 1 z) := by
              refine continuousOn_id.rpow_const (fun s hs => ?_)
              rw [Set.uIcc_of_le hz1] at hs
              exact Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one hs.1))
            exact (continuousOn_const.mul hc).intervalIntegrable
          · have hs0 : (0 : ℝ) < s := lt_of_lt_of_le zero_lt_one hs.1
            calc |Work.Construction.FK (slice (gS α (tauExt g)) τ) s| / s
                ≤ (C₁ * (s ^ ((3 : ℝ) / 2) / (1 + s) ^ 2)) / s :=
                  div_le_div_of_nonneg_right (hFK0 s hs0) hs0.le
              _ = C₁ * (s ^ ((3 : ℝ) / 2) / ((1 + s) ^ 2 * s)) := by
                  rw [mul_div_assoc, div_div]
              _ ≤ C₁ * s ^ (-(3 / 2 : ℝ)) :=
                  mul_le_mul_of_nonneg_left (rpow_ratio_le hs.1) hC₁pos.le
        refine hmono.trans ?_
        calc ∫ s in (1 : ℝ)..z, C₁ * s ^ (-(3 / 2 : ℝ))
            = C₁ * ∫ s in (1 : ℝ)..z, s ^ (-(3 / 2 : ℝ)) :=
              intervalIntegral.integral_const_mul _ _
          _ ≤ C₁ * 2 := mul_le_mul_of_nonneg_left (integral_rpow_neg_three_halves_le hz1)
              hC₁pos.le
          _ = 2 * C₁ := by ring
      have hval : Work.Construction.L12 (slice (gS α (tauExt g)) τ) z
          = Work.Construction.L12 (slice (gS α (tauExt g)) τ) 1
            + ∫ s in (1 : ℝ)..z,
                (-(Work.Construction.FK (slice (gS α (tauExt g)) τ) s) / s) := by
        linarith [hFTC]
      have h1 : |Work.Construction.L12 (slice (gS α (tauExt g)) τ) 1| ≤ C₂ :=
        (hL120 1 one_pos).trans
          (mul_le_of_le_one_right hC₂pos.le (rpow_div_le_one le_rfl))
      rw [hval]
      calc |Work.Construction.L12 (slice (gS α (tauExt g)) τ) 1
              + ∫ s in (1 : ℝ)..z,
                  (-(Work.Construction.FK (slice (gS α (tauExt g)) τ) s) / s)|
          ≤ |Work.Construction.L12 (slice (gS α (tauExt g)) τ) 1|
            + |∫ s in (1 : ℝ)..z,
                (-(Work.Construction.FK (slice (gS α (tauExt g)) τ) s) / s)| := abs_add_le _ _
        _ ≤ C₂ + 2 * C₁ := add_le_add h1 (hnorm.trans hmain)
        _ ≤ 3 * C₁ + C₂ := by linarith [hC₁pos]
    rcases le_or_gt z 1 with hzle | hzgt
    · -- small `z`: both are bounded by `(C₁ + C₂)·z`
      have hmin : min z 1 = z := min_eq_left hzle
      rw [hmin]
      have h1 : |Work.Construction.FK (slice (gS α (tauExt g)) τ) z| ≤ C₁ * z :=
        (hFK0 z hz).trans (mul_le_mul_of_nonneg_left (rpow_div_le_self hz hzle) hC₁pos.le)
      have h2 : |Work.Construction.L12 (slice (gS α (tauExt g)) τ) z| ≤ C₂ * z :=
        (hL120 z hz).trans (mul_le_mul_of_nonneg_left (rpow_div_le_self hz hzle) hC₂pos.le)
      nlinarith [h1, h2, hC₁pos, hC₂pos, hz]
    · -- large `z`: `𝔽K` is bounded by `C₁`, `L₁₂` by `3C₁ + C₂`
      have hz1 : 1 ≤ z := le_of_lt hzgt
      have hmin : min z 1 = 1 := min_eq_right hz1
      rw [hmin]
      have h1 : |Work.Construction.FK (slice (gS α (tauExt g)) τ) z| ≤ C₁ :=
        (hFK0 z hz).trans (mul_le_of_le_one_right hC₁pos.le (rpow_div_le_one hz1))
      have h2 := hL12big z hz1
      nlinarith [h1, h2, hC₁pos, hC₂pos]
  · -- (2) `c2`: the stream-function slice is `C²` on the open quadrant
    intro S _hS τ hτ
    exact (Work.FTS_RegExport.RXT.contDiffOn_slice_PhiR_Q0 (Φs := Φs) (E := E) (g := g)
      hEL3 hStar hOK τ hτ.1).of_le (by norm_num)
  · -- (3) `vth_ends`: `Vθ7 = 2·Uop(Φ)` vanishes at `θ = 0` and `θ = π/2`
    intro S _hS τ _hτ z hz
    have hpz0 : Work.Spaces.pz
        (slice (Work.FTS.RegExportIface.psiR α Φs E (tauExt g)) τ) z 0 = 0 := by
      have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 z]
          fun w => Work.FTS.RegExportIface.psiR α Φs E (tauExt g) w 0 τ := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        exact (Work.FTS.RegExportIface.psiR_zero (α := α) (Φs := Φs) (E := E)
          (G := tauExt g) hw).symm
      show deriv (fun w => Work.FTS.RegExportIface.psiR α Φs E (tauExt g) w 0 τ) z = 0
      rw [← Filter.EventuallyEq.deriv_eq hev, deriv_const]
    have hpzπ : Work.Spaces.pz
        (slice (Work.FTS.RegExportIface.psiR α Φs E (tauExt g)) τ) z (Real.pi / 2) = 0 := by
      have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 z]
          fun w => Work.FTS.RegExportIface.psiR α Φs E (tauExt g) w (Real.pi / 2) τ := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        exact (Work.FTS.RegExportIface.psiR_pi_div_two (α := α) (Φs := Φs) (E := E)
          (G := tauExt g) hw).symm
      show deriv (fun w => Work.FTS.RegExportIface.psiR α Φs E (tauExt g) w (Real.pi / 2) τ) z
        = 0
      rw [← Filter.EventuallyEq.deriv_eq hev, deriv_const]
    have hz0 : slice (Work.FTS.RegExportIface.psiR α Φs E (tauExt g)) τ z 0 = 0 :=
      Work.FTS.RegExportIface.psiR_zero (α := α) (Φs := Φs) (E := E) (G := tauExt g) hz
    have hzπ : slice (Work.FTS.RegExportIface.psiR α Φs E (tauExt g)) τ z (Real.pi / 2) = 0 :=
      Work.FTS.RegExportIface.psiR_pi_div_two (α := α) (Φs := Φs) (E := E)
        (G := tauExt g) hz
    have hU : ∀ θ : ℝ,
        Vθ7 (pExp α) (Work.FTS.RegExportIface.psiR α Φs E (tauExt g)) z θ τ
          = 2 * (-3 * slice (Work.FTS.RegExportIface.psiR α Φs E (tauExt g)) τ z θ
              - pExp α * z
                * Work.Spaces.pz (slice (Work.FTS.RegExportIface.psiR α Φs E (tauExt g)) τ)
                    z θ) := by
      intro θ
      rw [show Vθ7 (pExp α) (Work.FTS.RegExportIface.psiR α Φs E (tauExt g)) z θ τ
            = 2 * Work.Construction.Uop (pExp α)
                (slice (Work.FTS.RegExportIface.psiR α Φs E (tauExt g)) τ) z θ from rfl]
      rw [show Work.Construction.Uop (pExp α)
              (slice (Work.FTS.RegExportIface.psiR α Φs E (tauExt g)) τ) z θ
            = -3 * slice (Work.FTS.RegExportIface.psiR α Φs E (tauExt g)) τ z θ
              - pExp α * z
                * Work.Spaces.pz (slice (Work.FTS.RegExportIface.psiR α Φs E (tauExt g)) τ)
                    z θ from rfl]
    constructor
    · rw [hU 0, hz0, hpz0]
      ring
    · rw [hU (Real.pi / 2), hzπ, hpzπ]
      ring

end Work.FTS_RegExport.RXVP3

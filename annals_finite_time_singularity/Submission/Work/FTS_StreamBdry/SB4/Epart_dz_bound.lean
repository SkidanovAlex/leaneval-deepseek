import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_RegExport.RXT.Slots.v2_hkMem_pointwise_min
import Submission.Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Epart_dz_bound` — the near-`0` bound for the `U`-slot of the elliptic part

Target: for `α = 3a ∈ (0,1]`, a horizon datum `slice g τ` of a `DynOK'`-family and the elliptic
solution `E (slice g τ)`, the `z`-derivative of the `U`-slot
`Uop α (PhiTil α (slice g τ) (E (slice g τ))) / sin 2θ` is of size `O(z)` on the open quadrant
for `z ≤ 1`.

The route is the weighted `ℋ⁴ → L^∞` trade-off `RXT.v2_hkMem_pointwise_min` applied to the
class-`C` approximants `slice (gn n) τ` of the approximation scheme `LimApprox` (a conjunct of
`DynOK'`), followed by a limit.  The limit needs the *identification* of the `z`-derivative of
the `U`-slot at a point in terms of the mixed jets of the elliptic solution and the angular
moments `Qang` of the datum (the file `SB4/Aux/Dz_Epart_eq.lean`), together with the pointwise
convergence of the mixed jets (`EllLimOK3`) and of the angular moments
(`RXT.Slots.QangTendsto_conv`).
-/

noncomputable section

namespace Work.FTS_StreamBdry.SB4

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The `U`-slot of a datum: `Uop α (PhiTil α F Φ) / sin 2θ`. -/
def Uslot (α : ℝ) (F Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z θ / Work.Construction.s2 θ

/-- **The general form of `Epart_dz_bound`**, with the profile exponent as a free parameter
`α ∈ (0,1]` (the target is the instance `α = pExp a = 3a`). -/
theorem Epart_dz_bound_gen {α C₀ Ce : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hEL : Work.FTS.FinalV2.EllLimOK3 α E)
    (hOK : Work.FTS.FinalV2.DynOK' α C₀ Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ → ∃ K : ℝ, 0 ≤ K ∧ ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → z ≤ 1 →
      |Work.Spaces.Dz (Uslot α (Work.FTS.Galerkin.slice g τ)
        (E (Work.FTS.Galerkin.slice g τ))) z θ| ≤ K * z := by
  intro τ hτ
  -- the approximation scheme at the horizon `τ + 1`
  obtain ⟨gn, B, Lc, hC, hLip, hjet, hmu⟩ := hOK.2 (τ + 1) (by linarith)
  have hτT : τ ∈ Set.Icc (0 : ℝ) (τ + 1) := ⟨hτ, by linarith⟩
  -- the weighted `ℋ⁴ → L^∞` transfer constant
  obtain ⟨Cw, hCw0, hCw⟩ :=
    Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved (β := α) hα hα1
  -- the ℋ⁴-bound of the scheme is nonnegative, hence so is the jet constant
  have hX0 : 0 ≤ Work.Spaces.HkNorm α 4 (Work.FTS.Galerkin.slice (gn 0) τ) :=
    Work.Spaces.HkNorm_nonneg α 4 _
  have hC0sq : 0 ≤ C₀ * α ^ 2 := le_trans hX0 (hC 0 τ hτT).2.1
  have hC0nn : 0 ≤ Cw * (C₀ * α ^ 2) := mul_nonneg hCw0 hC0sq
  -- regularity of the approximants and of the limit
  have hF4n : ∀ n : ℕ, ContDiffOn ℝ 4
      (Function.uncurry (Work.FTS.Galerkin.slice (gn n) τ)) Work.FTS.EllipticEst.Q0 :=
    fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hC n τ hτT).1.reg 4
  have hF4L : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
      Work.FTS.EllipticEst.Q0 := hOK.1.1.c4 τ hτ
  -- the pointwise jet bound `JetBnd`, with a constant uniform in `n` and for the limit
  have hJetN : ∀ n : ℕ, Work.FTS_RegExport.RXT.Slots.JetBnd (Cw * (C₀ * α ^ 2))
      (Work.FTS.Galerkin.slice (gn n) τ) := by
    intro n b a hab z θ hz h0 h1
    have hmem : Work.Spaces.HkMem α 4 (Work.FTS.Galerkin.slice (gn n) τ) :=
      Work.FTS.OpenPkg.HkMem_mono_open (hC n τ hτT).1.reg 4 (by norm_num) (hC n τ hτT).1.mem
    have htr : Work.FTS.Nonlin.BdryTraces α 4 (Work.FTS.Galerkin.slice (gn n) τ) :=
      Work.FTS.ClassC.bdryTraces_mono (by norm_num) (hC n τ hτT).1.tr
    have h1' := hCw _ (hF4n n) hmem htr b a hab z θ hz h0 h1
    have h2 : Work.Spaces.HkNorm α 4 (Work.FTS.Galerkin.slice (gn n) τ) ≤ C₀ * α ^ 2 :=
      (hC n τ hτT).2.1
    have hw : 0 ≤ z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 :=
      div_nonneg (Real.rpow_nonneg hz.le _) (by positivity)
    calc |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ) z θ|
        ≤ Cw * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)
            * Work.Spaces.HkNorm α 4 (Work.FTS.Galerkin.slice (gn n) τ) := h1'
      _ ≤ Cw * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * (C₀ * α ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hCw0 hw)
      _ = (Cw * (C₀ * α ^ 2)) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by ring
  have hJetL : Work.FTS_RegExport.RXT.Slots.JetBnd (Cw * (C₀ * α ^ 2))
      (Work.FTS.Galerkin.slice g τ) :=
    Work.FTS_RegExport.RXT.Slots.JetBnd.of_tendsto hJetN
      (fun b a hab z θ hz h0 h1 => hjet τ hτT b a (by omega) z θ ⟨hz, h0, h1⟩)
  -- the elliptic limit closure along the scheme
  obtain ⟨-, hEdiff, hEconv⟩ := hEL (fun n => Work.FTS.Galerkin.slice (gn n) τ)
    (Work.FTS.Galerkin.slice g τ) B (fun n => (hC n τ hτT).1) (fun n => (hC n τ hτT).2.2)
    hF4L (fun j i hji z θ hzθ => hjet τ hτT j i hji z θ hzθ)
  -- the angular density of any datum of the class is continuous, so the `L₁₂`-tower and the
  -- `z`-derivative of `Qang · 0` are available
  have hcontD : ∀ F : ℝ → ℝ → ℝ, ContDiffOn ℝ 4 (Function.uncurry F) Work.FTS.EllipticEst.Q0 →
      Work.FTS_RegExport.RXT.Slots.JetBnd (Cw * (C₀ * α ^ 2)) F →
        ContinuousOn (fun s => Work.Elliptic.L12dens F s) (Set.Ioi 0) := by
    intro F h4 hb
    refine ContinuousOn.congr (s := Set.Ioi 0)
      (f := fun s => Work.Elliptic.Qang F 0 s / s)
      (g := fun s => Work.Elliptic.L12dens F s) ?_ ?_
    · intro s hs
      exact ((Work.FTS_RegExport.RXT.Slots.QangZeroDeriv_jet hC0nn h4 hb hs).continuousAt.div
        continuousAt_id (ne_of_gt hs)).continuousWithinAt
    · intro s _
      exact Work.Elliptic.L12dens_eq_Qang_div F s
  -- the pointwise transfer constant
  obtain ⟨Cpt, hCpt0, hCpt⟩ :=
    Work.FTS_RegExport.RXT.v2_hkMem_pointwise_min (α := α) hα hα1
  let M : ℝ := max (Ce * (C₀ * α ^ 2)) 0
  let K : ℝ := max (Cpt * M) 0
  have hK0 : 0 ≤ K := le_max_right _ _
  refine ⟨K, hK0, ?_⟩
  intro z θ hzθ hz1
  obtain ⟨hz, h0, h1⟩ :=
    Work.FTS.EllipticEst.mem_Q0.mp (show (z, θ) ∈ Work.FTS.EllipticEst.Q0 from hzθ)
  have hθmem : θ ∈ Set.Ioo 0 (π / 2) := ⟨h0, h1⟩
  -- (1) the pointwise bound, uniformly in `n`
  have hbound : ∀ n : ℕ, |Work.Spaces.Dz (Uslot α (Work.FTS.Galerkin.slice (gn n) τ)
      (E (Work.FTS.Galerkin.slice (gn n) τ))) z θ| ≤ K * z := by
    intro n
    obtain ⟨hGo, -⟩ := hEll (Work.FTS.Galerkin.slice (gn n) τ) (hC n τ hτT).1
    have hsm : Work.FTS.EllipticEst.SmoothOpen (Uslot α (Work.FTS.Galerkin.slice (gn n) τ)
        (E (Work.FTS.Galerkin.slice (gn n) τ))) := hGo.U.1.1
    have hmem4 : Work.Spaces.HkMem α 4 (Uslot α (Work.FTS.Galerkin.slice (gn n) τ)
        (E (Work.FTS.Galerkin.slice (gn n) τ))) := hGo.U.1.2
    have hM : Work.Spaces.HkNorm α 4 (Uslot α (Work.FTS.Galerkin.slice (gn n) τ)
        (E (Work.FTS.Galerkin.slice (gn n) τ))) ≤ M := by
      have h1 := hGo.U.2
      have h2 : Work.Spaces.HkNorm α 4 (Work.FTS.Galerkin.slice (gn n) τ) ≤ C₀ * α ^ 2 :=
        (hC n τ hτT).2.1
      rcases le_or_gt 0 Ce with hCe | hCe
      · exact le_trans (le_trans h1 (mul_le_mul_of_nonneg_left h2 hCe)) (le_max_left _ _)
      · have h3 : Ce * Work.Spaces.HkNorm α 4 (Work.FTS.Galerkin.slice (gn n) τ) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hCe.le (Work.Spaces.HkNorm_nonneg α 4 _)
        exact le_trans (le_trans h1 h3) (le_max_right _ _)
    have hpt := hCpt (Uslot α (Work.FTS.Galerkin.slice (gn n) τ)
        (E (Work.FTS.Galerkin.slice (gn n) τ)))
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsm 4) hmem4 1 0 (by norm_num) z θ
      hz h0 h1
    have hpt' : |Work.Spaces.Dz (Uslot α (Work.FTS.Galerkin.slice (gn n) τ)
        (E (Work.FTS.Galerkin.slice (gn n) τ))) z θ|
        ≤ Cpt * min z 1 * Work.Spaces.HkNorm α 4 (Uslot α (Work.FTS.Galerkin.slice (gn n) τ)
        (E (Work.FTS.Galerkin.slice (gn n) τ))) := by
      simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
        using hpt
    have hmin : min z 1 = z := min_eq_left hz1
    have hstep : Cpt * min z 1 * Work.Spaces.HkNorm α 4
        (Uslot α (Work.FTS.Galerkin.slice (gn n) τ)
        (E (Work.FTS.Galerkin.slice (gn n) τ))) ≤ Cpt * z * M := by
      rw [hmin]
      exact mul_le_mul_of_nonneg_left hM (mul_nonneg hCpt0 hz.le)
    have hK' : Cpt * z * M ≤ K * z := by
      have h : Cpt * M ≤ K := le_max_left _ _
      have heq : Cpt * z * M = (Cpt * M) * z := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right h hz.le
    exact le_trans (le_trans hpt' hstep) hK'
  -- (2) the identification of the `z`-derivative at a point, for every approximant and in the limit
  have keyN : ∀ n : ℕ, Work.Spaces.Dz (Uslot α (Work.FTS.Galerkin.slice (gn n) τ)
      (E (Work.FTS.Galerkin.slice (gn n) τ))) z θ
      = (-3 * Work.Spaces.mixed 1 0 (E (Work.FTS.Galerkin.slice (gn n) τ)) z θ
          - α * Work.Spaces.mixed 2 0 (E (Work.FTS.Galerkin.slice (gn n) τ)) z θ)
          / Work.Construction.s2 θ
        - (3 / (4 * α)) * Work.Elliptic.Qang (Work.FTS.Galerkin.slice (gn n) τ) 0 z
        - (1 / 4) * Work.Elliptic.Qang (Work.FTS.Galerkin.slice (gn n) τ) 1 z := by
    intro n
    have hsm : Work.FTS.EllipticEst.SmoothOpen (E (Work.FTS.Galerkin.slice (gn n) τ)) :=
      (hEll (Work.FTS.Galerkin.slice (gn n) τ) (hC n τ hτT).1).1.smooth
    have hC2 : ContDiffOn ℝ 2 (Function.uncurry (E (Work.FTS.Galerkin.slice (gn n) τ)))
        Work.FTS.EllipticEst.Q0 := (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsm 2
    have hcont := hcontD (Work.FTS.Galerkin.slice (gn n) τ) (hF4n n) (hJetN n)
    refine Dz_Epart_eq (α := α) (ne_of_gt hα)
      (F := Work.FTS.Galerkin.slice (gn n) τ)
      (Φ := E (Work.FTS.Galerkin.slice (gn n) τ)) hz hθmem hC2 ?_ ?_
    · intro z' hz'
      exact Work.FTS_RegExport.RXT.Slots.Construction_L12_hasDerivAt_jet hC0nn (hJetN n) hcont hz'
    · exact Work.FTS_RegExport.RXT.Slots.QangZeroDeriv_jet hC0nn (hF4n n) (hJetN n) hz
  have keyL : Work.Spaces.Dz (Uslot α (Work.FTS.Galerkin.slice g τ)
      (E (Work.FTS.Galerkin.slice g τ))) z θ
      = (-3 * Work.Spaces.mixed 1 0 (E (Work.FTS.Galerkin.slice g τ)) z θ
          - α * Work.Spaces.mixed 2 0 (E (Work.FTS.Galerkin.slice g τ)) z θ)
          / Work.Construction.s2 θ
        - (3 / (4 * α)) * Work.Elliptic.Qang (Work.FTS.Galerkin.slice g τ) 0 z
        - (1 / 4) * Work.Elliptic.Qang (Work.FTS.Galerkin.slice g τ) 1 z := by
    have hC2 : ContDiffOn ℝ 2 (Function.uncurry (E (Work.FTS.Galerkin.slice g τ)))
        Work.FTS.EllipticEst.Q0 := hEdiff.of_le (by norm_num)
    have hcont := hcontD (Work.FTS.Galerkin.slice g τ) hF4L hJetL
    refine Dz_Epart_eq (α := α) (ne_of_gt hα) hz hθmem hC2 ?_ ?_
    · intro z' hz'
      exact Work.FTS_RegExport.RXT.Slots.Construction_L12_hasDerivAt_jet hC0nn hJetL hcont hz'
    · exact Work.FTS_RegExport.RXT.Slots.QangZeroDeriv_jet hC0nn hF4L hJetL hz
  -- (3) convergence of the identified expression
  have hq0 : Tendsto (fun n : ℕ => Work.Elliptic.Qang (Work.FTS.Galerkin.slice (gn n) τ) 0 z)
      atTop (𝓝 (Work.Elliptic.Qang (Work.FTS.Galerkin.slice g τ) 0 z)) :=
    Work.FTS_RegExport.RXT.Slots.QangTendsto_conv (C0 := Cw * (C₀ * α ^ 2)) hC0nn hF4n hJetN hJetL
      (fun b a hab z' θ' hz' h0' h1' => hjet τ hτT b a (by omega) z' θ' ⟨hz', h0', h1'⟩)
      (k := 0) (by norm_num) hz
  have hq1 : Tendsto (fun n : ℕ => Work.Elliptic.Qang (Work.FTS.Galerkin.slice (gn n) τ) 1 z)
      atTop (𝓝 (Work.Elliptic.Qang (Work.FTS.Galerkin.slice g τ) 1 z)) :=
    Work.FTS_RegExport.RXT.Slots.QangTendsto_conv (C0 := Cw * (C₀ * α ^ 2)) hC0nn hF4n hJetN hJetL
      (fun b a hab z' θ' hz' h0' h1' => hjet τ hτT b a (by omega) z' θ' ⟨hz', h0', h1'⟩)
      (k := 1) (by norm_num) hz
  have hAB : Tendsto (fun n : ℕ => (-3 * Work.Spaces.mixed 1 0
        (E (Work.FTS.Galerkin.slice (gn n) τ)) z θ
        - α * Work.Spaces.mixed 2 0 (E (Work.FTS.Galerkin.slice (gn n) τ)) z θ)
        / Work.Construction.s2 θ) atTop
      (𝓝 ((-3 * Work.Spaces.mixed 1 0 (E (Work.FTS.Galerkin.slice g τ)) z θ
        - α * Work.Spaces.mixed 2 0 (E (Work.FTS.Galerkin.slice g τ)) z θ)
        / Work.Construction.s2 θ)) :=
    (((hEconv 1 0 (by norm_num) z θ hzθ).const_mul (-3)).sub
      ((hEconv 2 0 (by norm_num) z θ hzθ).const_mul α)).div_const (Work.Construction.s2 θ)
  have hexpr : Tendsto (fun n : ℕ => (-3 * Work.Spaces.mixed 1 0
        (E (Work.FTS.Galerkin.slice (gn n) τ)) z θ
        - α * Work.Spaces.mixed 2 0 (E (Work.FTS.Galerkin.slice (gn n) τ)) z θ)
        / Work.Construction.s2 θ
        - (3 / (4 * α)) * Work.Elliptic.Qang (Work.FTS.Galerkin.slice (gn n) τ) 0 z
        - (1 / 4) * Work.Elliptic.Qang (Work.FTS.Galerkin.slice (gn n) τ) 1 z) atTop
      (𝓝 ((-3 * Work.Spaces.mixed 1 0 (E (Work.FTS.Galerkin.slice g τ)) z θ
        - α * Work.Spaces.mixed 2 0 (E (Work.FTS.Galerkin.slice g τ)) z θ)
        / Work.Construction.s2 θ
        - (3 / (4 * α)) * Work.Elliptic.Qang (Work.FTS.Galerkin.slice g τ) 0 z
        - (1 / 4) * Work.Elliptic.Qang (Work.FTS.Galerkin.slice g τ) 1 z)) :=
    (hAB.sub (hq0.const_mul (3 / (4 * α)))).sub (hq1.const_mul (1 / 4))
  have hconv : Tendsto (fun n : ℕ => Work.Spaces.Dz (Uslot α (Work.FTS.Galerkin.slice (gn n) τ)
      (E (Work.FTS.Galerkin.slice (gn n) τ))) z θ) atTop
      (𝓝 (Work.Spaces.Dz (Uslot α (Work.FTS.Galerkin.slice g τ)
        (E (Work.FTS.Galerkin.slice g τ))) z θ)) := by
    rw [keyL]
    exact hexpr.congr' (Eventually.of_forall (fun n => (keyN n).symm))
  exact le_of_tendsto (hconv.abs) (Eventually.of_forall (fun n => hbound n))

theorem Epart_dz_bound {a C₀ Ce : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp a) u →
      Work.FTS.VocabO.EllPkgGo (Work.FTS.Regularity.pExp a) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp a) 6 Ce u (E u))
    (hEL : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp a) E)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp a) C₀ Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ → ∃ K : ℝ, 0 ≤ K ∧ ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → z ≤ 1 →
      |Work.Spaces.Dz (fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp a)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp a) (Work.FTS.Galerkin.slice g τ)
          (E (Work.FTS.Galerkin.slice g τ))) z θ / Work.Construction.s2 θ) z θ| ≤ K * z := by
  intro τ hτ
  exact Epart_dz_bound_gen (Work.FTS.Regularity.pExp_pos ha)
    (Work.FTS.Regularity.pExp_le_one ha13) hEll hEL hOK τ hτ

end Work.FTS_StreamBdry.SB4

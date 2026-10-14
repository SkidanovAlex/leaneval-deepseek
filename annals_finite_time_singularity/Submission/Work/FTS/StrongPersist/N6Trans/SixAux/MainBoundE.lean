import Mathlib
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.zibp_cut
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.RPFresh.straight_transfers
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.GalBasis.hk_sq_api
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.Nonlinear.N4Fields.angmul_field_smooth
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.prod_field
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Gmaj6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Majorant6
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.L3MulDzBackupM
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.FkJets
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.NfkSmooth
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.ProdRadSup
import Submission.Work.FTS.StrongPersist.L6Aux.LinMem6Aux
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Asm
import Submission.Work.FTS.StrongPersist.N6_L12H
import Submission.Work.FTS.StrongPersist.N6_prod
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.T2Sup.GenSlot
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxUniform
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.identity =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeI1Fts/identity` — the weak-class `I₁` chain identity

The identity `IP (AA u) (BB u) = ⟨V,V⟩ - 2η⟨U,U⟩ - 2η(1+η)N - ⟨cw·U, BB⟩` of Step 2 of the
paper (Elgindi, Annals 194 (3) 2021), where `U = z∂_zu`, `V = z∂_z∂_θu`, `AA = z²∂_zzu`,
`BB = ∂_θθu`, `N = ∫∫U²cos²(2θ)sin(2θ)^{-(2+η)}w²`, and `⟨g,h⟩ = AngSecond.IP g h` is the
`w²sin(2θ)^{-η}`-pairing.

The proof combines the two integration-by-parts halves, both proved in this directory:

* `radial_identity` — the radial `z`-integration by parts together with the angular
  `θ`-integration by parts of the mixed term:
  `⟨AA,BB⟩ + ⟨cw·U,BB⟩ = ⟨V,V⟩ - 2η∫∫U·V·cos(2θ)sin(2θ)^{-(1+η)}w²`;
* `cross_joint_h` — the second angular integration by parts, which converts the cross term into
  the diagonal angular energy and the `N`-term:
  `∫∫UVcos(2θ)σ₁w² = ∫∫U²σw² + (1+η)N`.
-/

namespace Work.FTS.EllipticEst.AeI1Fts

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-! ## Interval bookkeeping for the pairing `IP` -/




/-! ## The slicewise integrability facts feeding the cross identity -/



/-! ## The target -/


end

end Work.FTS.EllipticEst.AeI1Fts
end
-- ===== merged: Submission.Work.FTS.GalFields.RHS.sharpN0_defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The angular profiles `c2m` and `s2`, and the generic helpers -/

/-- `(z,θ) ↦ c2m θ` is `C^∞` on the open quadrant. -/
theorem smoothOpen_c2m_ang :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Construction.c2m θ) := by
  have hsnd : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => p.2) := contDiff_snd
  have hcos : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => Real.cos (2 * p.2)) :=
    Real.contDiff_cos.comp (contDiff_const.mul hsnd)
  have hsin2 : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => Real.sin p.2 ^ 2) :=
    (Real.contDiff_sin.comp hsnd).pow 2
  have h1 : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => Real.cos (2 * p.2) - Real.sin p.2 ^ 2) :=
    hcos.sub hsin2
  have h2 : ContDiff ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos (2 * p.2) - Real.sin p.2 ^ 2) := h1.of_le le_top
  exact h2.contDiffOn.mono (Set.subset_univ _)


/-- The negation of a `SmoothOpen` function is `SmoothOpen`. -/
theorem smoothOpen_neg' {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => -f z θ) :=
  hf.neg

/-- `|c2m θ| ≤ 1000`. -/
theorem abs_c2m_le_thousand (θ : ℝ) : |Work.Construction.c2m θ| ≤ 1000 := by
  have hc : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have hs : |Real.sin θ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [Real.sin_sq_le_one θ]
  have hcm : Work.Construction.c2m θ = Real.cos (2 * θ) - Real.sin θ ^ 2 := rfl
  rw [hcm]
  calc |Real.cos (2 * θ) - Real.sin θ ^ 2|
      ≤ |Real.cos (2 * θ)| + |Real.sin θ ^ 2| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add hc hs
    _ ≤ 1000 := by norm_num

/-- `|D_θ^i (c2m)| ≤ 1000 sin(2θ)` on `Iθ` for `1 ≤ i ≤ 4`. -/
theorem DthIter_c2m_le_sin (i : ℕ) (hi : 1 ≤ i) (hi4 : i ≤ 4) (θ : ℝ)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Construction.c2m θ') 0 θ|
      ≤ 1000 * Real.sin (2 * θ) := by
  have h := Work.FTS.Nonlinear.Pieces.DthIter_c2m_le i hi hi4 θ
  rw [show (Real.sin (2 * θ)) ^ (2 : ℝ) = (Real.sin (2 * θ)) ^ (2 : ℕ) from
    Real.rpow_natCast _ 2] at h
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsq : Real.sin (2 * θ) ^ 2 ≤ Real.sin (2 * θ) := by nlinarith
  calc |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Construction.c2m θ') 0 θ|
      ≤ 1000 * Real.sin (2 * θ) ^ 2 := h
    _ ≤ 1000 * Real.sin (2 * θ) := by linarith

/-- `∂_z` is additive on the open quadrant for a pointwise decomposition `f = f' + k` of
`SmoothOpen` data. -/
theorem pz_add_of_smoothOpen {f f' k : ℝ → ℝ → ℝ}
    (hf' : Work.FTS.EllipticEst.SmoothOpen f') (hk : Work.FTS.EllipticEst.SmoothOpen k)
    (h : ∀ z θ, f z θ = f' z θ + k z θ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pz f z θ = Work.Spaces.pz f' z θ + Work.Spaces.pz k z θ := by
  intro z θ hz hθ0 hθ1
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩
  have hd' : DifferentiableAt ℝ (Function.uncurry f') (z, θ) :=
    ((hf'.forall 1).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)).differentiableAt
      (by norm_num)
  have hdk : DifferentiableAt ℝ (Function.uncurry k) (z, θ) :=
    ((hk.forall 1).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)).differentiableAt
      (by norm_num)
  have h1 : DifferentiableAt ℝ (fun z' => f' z' θ) z :=
    Work.Spaces.differentiableAt_curry_left hd'
  have h2 : DifferentiableAt ℝ (fun z' => k z' θ) z :=
    Work.Spaces.differentiableAt_curry_left hdk
  have hkey : (fun z' => f z' θ) = fun z' => f' z' θ + k z' θ := by
    funext z'
    exact h z' θ
  simp only [Work.Spaces.pz]
  rw [hkey]
  exact deriv_add h1 h2

/-- `∂_θ` is additive on the open quadrant for a pointwise decomposition `f = f' + k` of
`SmoothOpen` data. -/
theorem pth_add_of_smoothOpen {f f' k : ℝ → ℝ → ℝ}
    (hf' : Work.FTS.EllipticEst.SmoothOpen f') (hk : Work.FTS.EllipticEst.SmoothOpen k)
    (h : ∀ z θ, f z θ = f' z θ + k z θ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pth f z θ = Work.Spaces.pth f' z θ + Work.Spaces.pth k z θ := by
  intro z θ hz hθ0 hθ1
  have h1 : DifferentiableAt ℝ (fun θ' => f' z θ') θ :=
    Work.FTS.NonlinRows.differentiableAt_slice_snd_of_smoothOpen hf' hz ⟨hθ0, hθ1⟩
  have h2 : DifferentiableAt ℝ (fun θ' => k z θ') θ :=
    Work.FTS.NonlinRows.differentiableAt_slice_snd_of_smoothOpen hk hz ⟨hθ0, hθ1⟩
  have hkey : (fun θ' => f z θ') = fun θ' => f' z θ' + k z θ' := by
    funext θ'
    exact h z θ'
  simp only [Work.Spaces.pth]
  rw [hkey]
  exact deriv_add h1 h2

/-- **Linearity of `L₁₂` in the profile**: for `C^∞`-on-the-open-quadrant, `ℋ⁴`-honest `a`, `b`
and `z ≥ 0`, `L₁₂(a)(z) - L₁₂(b)(z) = L₁₂(a-b)(z)`. -/
theorem L12_sub_eq_of_smoothOpen {α : ℝ} {a b : ℝ → ℝ → ℝ}
    (hasm : Work.FTS.EllipticEst.SmoothOpen a) (hbsm : Work.FTS.EllipticEst.SmoothOpen b)
    (hamem : Work.Spaces.HkMem α 4 a) (hbmem : Work.Spaces.HkMem α 4 b) :
    ∀ z, 0 ≤ z → Work.Construction.L12 a z - Work.Construction.L12 b z
      = Work.Construction.L12 (fun z θ => a z θ - b z θ) z := by
  intro z hz
  set b' : ℝ → ℝ → ℝ := fun z θ => -b z θ with hb'def
  have h1 : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * a s θ / s) Work.Spaces.Iθ :=
    fun s hs => Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hasm hamem
      (lt_of_le_of_lt hz hs)
  have h2 : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * b' s θ / s) Work.Spaces.Iθ := by
    intro s hs
    have h := Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hbsm hbmem
      (lt_of_le_of_lt hz hs)
    refine (h.neg).congr ?_
    filter_upwards with θ
    simp only [hb'def, Pi.neg_apply]
    ring
  have h3 : MeasureTheory.IntegrableOn (Work.Construction.L12dens a) (Set.Ioi z) :=
    (Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem hasm hamem).mono_set
      (fun s hs => lt_of_le_of_lt hz hs)
  have h4 : MeasureTheory.IntegrableOn (Work.Construction.L12dens b') (Set.Ioi z) := by
    have hb4 : MeasureTheory.IntegrableOn
        (fun s => -(Work.Construction.L12dens b s)) (Set.Ioi z) :=
      ((Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem hbsm hbmem).mono_set
        (fun s hs => lt_of_le_of_lt hz hs)).neg
    refine hb4.congr ?_
    filter_upwards with s
    show -(Work.Construction.L12dens b s) = Work.Construction.L12dens b' s
    rw [hb'def]
    show -(Work.FM.L12dens Work.Spaces.K b s)
      = Work.FM.L12dens Work.Spaces.K (fun z θ => -b z θ) s
    exact (Work.FTS.FinalClock.L12dens_neg' (K := Work.Spaces.K) (f := b) (s := s)).symm
  have hadd := (Work.FTS.LocData.L12_add_mul (c := (0 : ℝ)) (a := a) (b := b') (z := z)
    h1 h2 h3 h4).1
  have hb'neg : Work.Construction.L12 b' z = -Work.Construction.L12 b z := by
    rw [hb'def]
    exact Work.Construction.L12_neg b z
  have hfun : (fun z θ => a z θ - b z θ) = fun z θ => a z θ + b' z θ := by
    funext z θ
    simp only [hb'def]
    exact sub_eq_add_neg (a z θ) (b z θ)
  rw [hfun, hadd, hb'neg]
  ring

/-- From an `HkSq`-comparison, the corresponding `Xn`-comparison. -/
theorem Xn_le_of_HkSq_le {α : ℝ} {f g : ℝ → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : Work.Spaces.HkSq α 4 f ≤ C * Work.Spaces.HkSq α 4 g) :
    Work.FTS.Nonlin.Xn α f ≤ Real.sqrt C * Work.FTS.Nonlin.Xn α g := by
  have h1 : Real.sqrt (Work.Spaces.HkSq α 4 f) ≤ Real.sqrt (C * Work.Spaces.HkSq α 4 g) :=
    Real.sqrt_le_sqrt h
  have h2 : Real.sqrt (C * Work.Spaces.HkSq α 4 g)
      = Real.sqrt C * Real.sqrt (Work.Spaces.HkSq α 4 g) := Real.sqrt_mul hC _
  calc Work.FTS.Nonlin.Xn α f = Real.sqrt (Work.Spaces.HkSq α 4 f) := rfl
    _ ≤ Real.sqrt (C * Work.Spaces.HkSq α 4 g) := h1
    _ = Real.sqrt C * Work.FTS.Nonlin.Xn α g := by
        rw [h2]
        rfl

/-! ## The nine pieces of the difference `N₀(g) - N₀(g')` -/

/-- `(1/α)·L₁₂(g)·h` — the first half of the `N₀₃`-difference. -/
def P1 (α : ℝ) (g h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (1 / α) * (Work.Construction.L12 g z * h z θ)

/-- `(1/α)·L₁₂(h)·g'` — the second half of the `N₀₃`-difference. -/
def P2 (α : ℝ) (g' h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (1 / α) * (Work.Construction.L12 h z * g' z θ)

/-- `(3/2α)·D_θF_*·L₁₂(h)` — the `N₀₄ᵃ`-difference. -/
def P3 (α : ℝ) (h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (3 / (2 * α)) *
    (Work.Spaces.Dth (Work.Construction.Fstar α) z θ * Work.Construction.L12 h z)

/-- `(3/2α)·L₁₂(g)·D_θh` — the first half of the `N₀₄ᵇ`-difference. -/
def P4 (α : ℝ) (g h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (3 / (2 * α)) * (Work.Construction.L12 g z * Work.Spaces.Dth h z θ)

/-- `(3/2α)·L₁₂(h)·D_θg'` — the second half of the `N₀₄ᵇ`-difference. -/
def P5 (α : ℝ) (g' h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (3 / (2 * α)) * (Work.Construction.L12 h z * Work.Spaces.Dth g' z θ)

/-- `-c2m·(D_zF_*·L₁₂(h))` — the `N₀₅ᵃ`-difference. -/
def P6 (α : ℝ) (h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(Work.Construction.c2m θ *
    (Work.Spaces.Dz (Work.Construction.Fstar α) z θ * Work.Construction.L12 h z))

/-- `-c2m·(L₁₂(g)·D_zh)` — the first half of the `N₀₅ᵇ`-difference. -/
def P7 (α : ℝ) (g h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(Work.Construction.c2m θ * (Work.Construction.L12 g z * Work.Spaces.Dz h z θ))

/-- `-c2m·(L₁₂(h)·D_zg')` — the second half of the `N₀₅ᵇ`-difference. -/
def P8 (α : ℝ) (g' h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(Work.Construction.c2m θ * (Work.Construction.L12 h z * Work.Spaces.Dz g' z θ))

/-- `-(c2m·L₁₂(F_*))·D_zh` — the `N₀₆`-difference. -/
def P9 (α : ℝ) (h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -((Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z)
    * Work.Spaces.Dz h z θ)

/-! ## The right-nested sum of the nine pieces, the constants, and the package constants -/

/-- The right-nested sum `P1 + (P2 + … + P9)` of the nine pieces. -/
def Rsum (α : ℝ) (g g' h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  P1 α g h + (P2 α g' h + (P3 α h + (P4 α g h + (P5 α g' h + (P6 α h
    + (P7 α g h + (P8 α g' h + P9 α h)))))))

/-- The factor `(1 + |g|_{ℋ⁵} + |g'|_{ℋ⁵})·|h|_{ℋ⁵}` of the estimates. -/
def TOf (α : ℝ) (g g' h : ℝ → ℝ → ℝ) : ℝ :=
  (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g') * Work.FTS.GalFields.Xn5 α h

theorem TOf_nonneg (α : ℝ) (g g' h : ℝ → ℝ → ℝ) : 0 ≤ TOf α g g' h := by
  rw [TOf]
  exact mul_nonneg (by linarith [Work.Spaces.HkNorm_nonneg α 5 g,
    Work.Spaces.HkNorm_nonneg α 5 g']) (Work.Spaces.HkNorm_nonneg α 5 h)

/-- The package constant of `D_θF_*` in the norm `𝒲^{4,∞}`. -/
noncomputable def CFdef : ℝ := Classical.choose Work.FTS.Nonlinear.FstarPkg.DthFstar_W

theorem CFdef_spec : 0 < CFdef ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    Work.Spaces.WlInfMem α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) ∧
    Work.Spaces.WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ CFdef * α ^ 2 :=
  Classical.choose_spec Work.FTS.Nonlinear.FstarPkg.DthFstar_W

theorem CFdef_pos : 0 < CFdef := CFdef_spec.1

/-- The package constant of `D_zF_*` in the norm `𝒲^{4,∞}`. -/
noncomputable def Cdzdef : ℝ := Classical.choose Work.FTS.Nonlinear.FstarPkg.DzFstar_W

theorem Cdzdef_spec : 0 < Cdzdef ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    Work.Spaces.WlInfMem α 4 (Work.Spaces.Dz (Work.Construction.Fstar α)) ∧
    Work.Spaces.WlInf α 4 (Work.Spaces.Dz (Work.Construction.Fstar α)) ≤ Cdzdef * α :=
  Classical.choose_spec Work.FTS.Nonlinear.FstarPkg.DzFstar_W

theorem Cdzdef_pos : 0 < Cdzdef := Cdzdef_spec.1

/-- The package constant of `c2m·L₁₂(F_*)` in the norm `𝒲^{4,∞}`. -/
noncomputable def Cwdef : ℝ := Classical.choose Work.FTS.Nonlinear.FstarPkg.c2m_L12Fstar_W

theorem Cwdef_spec : 0 < Cwdef ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    Work.Spaces.WlInfMem α 4 (fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z) ∧
    Work.Spaces.WlInf α 4 (fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z) ≤ Cwdef * α :=
  Classical.choose_spec Work.FTS.Nonlinear.FstarPkg.c2m_L12Fstar_W

theorem Cwdef_pos : 0 < Cwdef := Cwdef_spec.1

/-- **Multiplication by `c2m` preserves `ℋ⁴` and its energy**, with a universal constant: the
angular factor `c2m` is bounded by `1000` and its `D_θ`-iterates (orders `1..4`) are
`≤ 1000 sin 2θ`, which is exactly the hypothesis of `ang_mul_HkSq_le`. -/
theorem c2m_mul_HkSq_le : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.c2m θ * f z θ) ∧
    Work.Spaces.HkSq α 4 (fun z θ => Work.Construction.c2m θ * f z θ)
      ≤ C * Work.Spaces.HkSq α 4 f := by
  obtain ⟨C1, hC1pos, hC1⟩ := Work.FTS.StrongPersist.L3Rhs.ang_mul_HkSq_le 4
  refine ⟨C1 * 1000 ^ 2, by positivity, ?_⟩
  intro α f hα hα1 hfsm hfmem
  exact hC1 α hα hα1 (fun θ => Work.Construction.c2m θ) 1000 (by norm_num)
    smoothOpen_c2m_ang (fun θ _ => abs_c2m_le_thousand θ)
    (fun i hi hi4 θ hθ => DthIter_c2m_le_sin i hi hi4 θ hθ) f hfsm hfmem

/-- The universal constant of the `c2m`-multiplier. -/
noncomputable def Cangdef : ℝ := Classical.choose c2m_mul_HkSq_le

theorem Cangdef_spec : 0 < Cangdef ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.c2m θ * f z θ) ∧
    Work.Spaces.HkSq α 4 (fun z θ => Work.Construction.c2m θ * f z θ)
      ≤ Cangdef * Work.Spaces.HkSq α 4 f :=
  Classical.choose_spec c2m_mul_HkSq_le

theorem Cangdef_pos : 0 < Cangdef := Cangdef_spec.1

/-! ## The nine per-piece constants -/

noncomputable def kA1 (α Ci : ℝ) : ℝ := (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci

noncomputable def kA2 (α Ci : ℝ) : ℝ := (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci

noncomputable def kA3 (α Ci CF : ℝ) : ℝ :=
  (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2) * Ci)

noncomputable def kA4 (α Ci : ℝ) : ℝ := (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci)

noncomputable def kA5 (α Ci : ℝ) : ℝ := (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci)

noncomputable def kA6 (α Ci Cdz : ℝ) : ℝ :=
  Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * (Cdz * α) * Ci)

noncomputable def kA7 (α Ci : ℝ) : ℝ := Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci)

noncomputable def kA8 (α Ci : ℝ) : ℝ := Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci)

noncomputable def kA9 (α Ci Cw : ℝ) : ℝ := Ci * α ^ (-(1 / 2 : ℝ)) * (Cw * α)

/-- The sum of the nine per-piece constants. -/
noncomputable def ksum (α Ci CF Cdz Cw : ℝ) : ℝ :=
  kA1 α Ci + kA2 α Ci + kA3 α Ci CF + kA4 α Ci + kA5 α Ci
    + kA6 α Ci Cdz + kA7 α Ci + kA8 α Ci + kA9 α Ci Cw

theorem ksum_nonneg {α Ci CF Cdz Cw : ℝ} (hα : 0 < α) (hCi : 0 < Ci) (hCF : 0 < CF)
    (hCdz : 0 < Cdz) (hCw : 0 < Cw) : 0 ≤ ksum α Ci CF Cdz Cw := by
  have h1 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h2 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h3 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2) * Ci) := by positivity
  have h4 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h5 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h6 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * (Cdz * α) * Ci) := by positivity
  have h7 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h8 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h9 : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cw * α) := by positivity
  rw [ksum, kA1, kA2, kA3, kA4, kA5, kA6, kA7, kA8, kA9]
  linarith

theorem kA1_le_ksum {α Ci CF Cdz Cw : ℝ} (hα : 0 < α) (hCi : 0 < Ci) (hCF : 0 < CF)
    (hCdz : 0 < Cdz) (hCw : 0 < Cw) :
    kA1 α Ci ≤ ksum α Ci CF Cdz Cw := by
  have h2 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h3 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2) * Ci) := by positivity
  have h4 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h5 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h6 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * (Cdz * α) * Ci) := by positivity
  have h7 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h8 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h9 : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cw * α) := by positivity
  rw [ksum, kA1, kA2, kA3, kA4, kA5, kA6, kA7, kA8, kA9]
  linarith

theorem kA2_le_ksum {α Ci CF Cdz Cw : ℝ} (hα : 0 < α) (hCi : 0 < Ci) (hCF : 0 < CF)
    (hCdz : 0 < Cdz) (hCw : 0 < Cw) :
    kA2 α Ci ≤ ksum α Ci CF Cdz Cw := by
  have h1 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h3 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2) * Ci) := by positivity
  have h4 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h5 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h6 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * (Cdz * α) * Ci) := by positivity
  have h7 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h8 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h9 : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cw * α) := by positivity
  rw [ksum, kA1, kA2, kA3, kA4, kA5, kA6, kA7, kA8, kA9]
  linarith

theorem kA3_le_ksum {α Ci CF Cdz Cw : ℝ} (hα : 0 < α) (hCi : 0 < Ci) (hCF : 0 < CF)
    (hCdz : 0 < Cdz) (hCw : 0 < Cw) :
    kA3 α Ci CF ≤ ksum α Ci CF Cdz Cw := by
  have h1 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h2 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h4 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h5 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h6 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * (Cdz * α) * Ci) := by positivity
  have h7 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h8 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h9 : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cw * α) := by positivity
  rw [ksum, kA1, kA2, kA3, kA4, kA5, kA6, kA7, kA8, kA9]
  linarith

theorem kA4_le_ksum {α Ci CF Cdz Cw : ℝ} (hα : 0 < α) (hCi : 0 < Ci) (hCF : 0 < CF)
    (hCdz : 0 < Cdz) (hCw : 0 < Cw) :
    kA4 α Ci ≤ ksum α Ci CF Cdz Cw := by
  have h1 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h2 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h3 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2) * Ci) := by positivity
  have h5 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h6 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * (Cdz * α) * Ci) := by positivity
  have h7 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h8 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h9 : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cw * α) := by positivity
  rw [ksum, kA1, kA2, kA3, kA4, kA5, kA6, kA7, kA8, kA9]
  linarith

theorem kA5_le_ksum {α Ci CF Cdz Cw : ℝ} (hα : 0 < α) (hCi : 0 < Ci) (hCF : 0 < CF)
    (hCdz : 0 < Cdz) (hCw : 0 < Cw) :
    kA5 α Ci ≤ ksum α Ci CF Cdz Cw := by
  have h1 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h2 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h3 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2) * Ci) := by positivity
  have h4 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h6 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * (Cdz * α) * Ci) := by positivity
  have h7 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h8 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h9 : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cw * α) := by positivity
  rw [ksum, kA1, kA2, kA3, kA4, kA5, kA6, kA7, kA8, kA9]
  linarith

theorem kA6_le_ksum {α Ci CF Cdz Cw : ℝ} (hα : 0 < α) (hCi : 0 < Ci) (hCF : 0 < CF)
    (hCdz : 0 < Cdz) (hCw : 0 < Cw) :
    kA6 α Ci Cdz ≤ ksum α Ci CF Cdz Cw := by
  have h1 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h2 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h3 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2) * Ci) := by positivity
  have h4 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h5 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h7 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h8 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h9 : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cw * α) := by positivity
  rw [ksum, kA1, kA2, kA3, kA4, kA5, kA6, kA7, kA8, kA9]
  linarith

theorem kA7_le_ksum {α Ci CF Cdz Cw : ℝ} (hα : 0 < α) (hCi : 0 < Ci) (hCF : 0 < CF)
    (hCdz : 0 < Cdz) (hCw : 0 < Cw) :
    kA7 α Ci ≤ ksum α Ci CF Cdz Cw := by
  have h1 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h2 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h3 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2) * Ci) := by positivity
  have h4 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h5 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h6 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * (Cdz * α) * Ci) := by positivity
  have h8 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h9 : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cw * α) := by positivity
  rw [ksum, kA1, kA2, kA3, kA4, kA5, kA6, kA7, kA8, kA9]
  linarith

theorem kA8_le_ksum {α Ci CF Cdz Cw : ℝ} (hα : 0 < α) (hCi : 0 < Ci) (hCF : 0 < CF)
    (hCdz : 0 < Cdz) (hCw : 0 < Cw) :
    kA8 α Ci ≤ ksum α Ci CF Cdz Cw := by
  have h1 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h2 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h3 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2) * Ci) := by positivity
  have h4 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h5 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h6 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * (Cdz * α) * Ci) := by positivity
  have h7 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h9 : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cw * α) := by positivity
  rw [ksum, kA1, kA2, kA3, kA4, kA5, kA6, kA7, kA8, kA9]
  linarith

theorem kA9_le_ksum {α Ci CF Cdz Cw : ℝ} (hα : 0 < α) (hCi : 0 < Ci) (hCF : 0 < CF)
    (hCdz : 0 < Cdz) (hCw : 0 < Cw) :
    kA9 α Ci Cw ≤ ksum α Ci CF Cdz Cw := by
  have h1 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h2 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h3 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2) * Ci) := by positivity
  have h4 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h5 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h6 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * (Cdz * α) * Ci) := by positivity
  have h7 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h8 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  rw [ksum, kA1, kA2, kA3, kA4, kA5, kA6, kA7, kA8, kA9]
  linarith

end Work.FTS.GalFields.RHS
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.WordEnergy =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## Slot words of bounded length -/

/-- The slot words of length at most `n`: the free monoid generated by `D_θ` and `D_z`, with the
length of a word recorded in the index (so that `IsWordLe n X` is `IsWord X` together with the
bound `length X ≤ n`). -/
inductive IsWordLe : ℕ → (Fn → Fn) → Prop
  | id {n : ℕ} : IsWordLe n id
  | dth {n : ℕ} {X : Fn → Fn} : IsWordLe n X → IsWordLe (n + 1) (fun f => X (Work.Spaces.Dth f))
  | dz {n : ℕ} {X : Fn → Fn} : IsWordLe n X → IsWordLe (n + 1) (fun f => X (Work.Spaces.Dz f))

/-- Appending `D_θ` on the right increases the length by one, so a word of length at most `n` is
also a word of length at most `n + 1` (with the *same* action: the left argument is `D_θ`). -/
theorem IsWordLe.succ {n : ℕ} {X : Fn → Fn} (hX : IsWordLe n X) : IsWordLe (n + 1) X := by
  induction hX with
  | id => exact IsWordLe.id
  | dth _ ih => exact IsWordLe.dth ih
  | dz _ ih => exact IsWordLe.dz ih

/-- Weakening of the length bound. -/
theorem IsWordLe.mono {n m : ℕ} (h : n ≤ m) {X : Fn → Fn} (hX : IsWordLe n X) :
    IsWordLe m X :=
  Nat.le_induction hX (fun _ _ ih => ih.succ) m h

/-! ## The refined recursion -/


/-! ## The two instances the `ε`-scheme needs -/



end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.Data =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5

open Work.Spaces
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Leibniz for the first-order operators on the open quadrant -/

/-- `D_z(f·g) = D_z f·g + f·D_z g` on the open quadrant. -/
theorem Dz_mul_eqOn_Q0 {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Dz (fun z θ => f z θ * g z θ) z θ = Dz f z θ * g z θ + f z θ * Dz g z θ := by
  intro z θ hz hθ hθ'
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ'⟩
  have hdf : DifferentiableAt ℝ (fun z' => f z' θ) z :=
    Work.Spaces.differentiableAt_slice_fst
      ((hf.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)).differentiableAt
        (by norm_num))
  have hdg : DifferentiableAt ℝ (fun z' => g z' θ) z :=
    Work.Spaces.differentiableAt_slice_fst
      ((hg.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)).differentiableAt
        (by norm_num))
  show z * deriv (fun z' => f z' θ * g z' θ) z
      = z * deriv (fun z' => f z' θ) z * g z θ + f z θ * (z * deriv (fun z' => g z' θ) z)
  rw [show (fun z' => f z' θ * g z' θ)
        = (fun z' => f z' θ) * (fun z' => g z' θ) from rfl, deriv_mul hdf hdg]
  ring

/-- `D_θ(f·g) = D_θ f·g + f·D_θ g` on the open quadrant. -/
theorem Dth_mul_eqOn_Q0 {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Dth (fun z θ => f z θ * g z θ) z θ = Dth f z θ * g z θ + f z θ * Dth g z θ := by
  intro z θ hz hθ hθ'
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ'⟩
  have hdf : DifferentiableAt ℝ (fun θ' => f z θ') θ :=
    Work.Spaces.differentiableAt_slice_snd
      ((hf.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)).differentiableAt
        (by norm_num))
  have hdg : DifferentiableAt ℝ (fun θ' => g z θ') θ :=
    Work.Spaces.differentiableAt_slice_snd
      ((hg.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)).differentiableAt
        (by norm_num))
  show Real.sin (2 * θ) * deriv (fun θ' => f z θ' * g z θ') θ
      = Real.sin (2 * θ) * deriv (fun θ' => f z θ') θ * g z θ
        + f z θ * (Real.sin (2 * θ) * deriv (fun θ' => g z θ') θ)
  rw [show (fun θ' => f z θ' * g z θ') = (fun θ' => f z θ') * (fun θ' => g z θ') from rfl,
    deriv_mul hdf hdg]
  ring

/-! ## The level-`5` data bundles -/

/-- **The level-`5` data of a factor**, at level four: `HQo α 4 f` and an `Xn`-bound, and the
same for `D_z f` and `D_θ f`.  This is exactly what the level shift (`HkSq_succ_le`) consumes
for a product of two such factors. -/
structure L5 (α : ℝ) (f : Fn) (C : ℝ) : Prop where
  qo : Work.FTS.VocabO.HQo α 4 f
  bd : Work.FTS.Nonlin.Xn α f ≤ C
  qoDz : Work.FTS.VocabO.HQo α 4 (Dz f)
  bdDz : Work.FTS.Nonlin.Xn α (Dz f) ≤ C
  qoDth : Work.FTS.VocabO.HQo α 4 (Dth f)
  bdDth : Work.FTS.Nonlin.Xn α (Dth f) ≤ C

/-- **The `𝒲^{4,∞}`-priced level-`5` data of a factor**: smoothness and a `𝒲^{4,∞}`-bound, and
the same for `D_z f` and `D_θ f`. -/
structure W5 (α : ℝ) (f : Fn) (C : ℝ) : Prop where
  sm : Work.FTS.EllipticEst.SmoothOpen f
  wm : Work.Spaces.WlInfMem α 4 f
  wb : Work.Spaces.WlInf α 4 f ≤ C
  smDz : Work.FTS.EllipticEst.SmoothOpen (Dz f)
  wmDz : Work.Spaces.WlInfMem α 4 (Dz f)
  wbDz : Work.Spaces.WlInf α 4 (Dz f) ≤ C
  smDth : Work.FTS.EllipticEst.SmoothOpen (Dth f)
  wmDth : Work.Spaces.WlInfMem α 4 (Dth f)
  wbDth : Work.Spaces.WlInf α 4 (Dth f) ≤ C

/-! ## The level-`5` product wrappers -/

/-- The rearrangement behind every level-four majorant: if `x ≤ a`, `y ≤ b` and the coefficients
are nonnegative, then `C α^{-1/2} x y ≤ C α^{-1/2} a b`. -/
theorem Pd_le {C α a b x y : ℝ} (hC : 0 ≤ C * α ^ (-(1 / 2 : ℝ))) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hx : x ≤ a) (hy : y ≤ b) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) :
    C * α ^ (-(1 / 2 : ℝ)) * x * y ≤ C * α ^ (-(1 / 2 : ℝ)) * a * b := by
  have h1 : C * α ^ (-(1 / 2 : ℝ)) * x ≤ C * α ^ (-(1 / 2 : ℝ)) * a :=
    mul_le_mul_of_nonneg_left hx hC
  have h2 : C * α ^ (-(1 / 2 : ℝ)) * x * y ≤ C * α ^ (-(1 / 2 : ℝ)) * a * y :=
    mul_le_mul_of_nonneg_right h1 hy0
  have h3 : C * α ^ (-(1 / 2 : ℝ)) * a * y ≤ C * α ^ (-(1 / 2 : ℝ)) * a * b :=
    mul_le_mul_of_nonneg_left hy (mul_nonneg hC ha)
  exact le_trans h2 h3

/-- `HkSq α 4 f = (Xn α f)²`. -/
theorem sq_eq_Xn_sq (α : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 4 f = (Work.FTS.Nonlin.Xn α f) ^ 2 := by
  have : Work.FTS.Nonlin.Xn α f = Real.sqrt (Work.Spaces.HkSq α 4 f) := rfl
  rw [this, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 f)]

/-- **The level-`5` product of two `ℋ⁴`-honest factors**, from the level-four product rule and
the level shift. -/
theorem L5_mul {α Cprod : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCprod : 0 < Cprod)
    (hfield : ∀ f g : Fn, Work.FTS.VocabO.HQo α 4 f → Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Cprod * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g)
    {C G : Fn} {c a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hC : L5 α C a) (hG : L5 α G b) :
    Work.Spaces.HkMem α 5 (fun z θ => c * (C z θ * G z θ)) ∧
      Work.Spaces.HkNorm α 5 (fun z θ => c * (C z θ * G z θ))
        ≤ |c| * (3 * (Cprod * α ^ (-(1 / 2 : ℝ)) * a * b)) := by
  have hAr : 0 ≤ Cprod * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hCprod.le (Real.rpow_nonneg hα.le _)
  set P : ℝ := Cprod * α ^ (-(1 / 2 : ℝ)) * a * b with hPdef
  have hPnn : 0 ≤ P := by
    rw [hPdef]
    exact mul_nonneg (mul_nonneg hAr ha) hb
  -- ### the six level-four product estimates
  have hCG := hfield C G hC.qo hG.qo
  have hDzCG := hfield (Dz C) G hC.qoDz hG.qo
  have hCDzG := hfield C (Dz G) hC.qo hG.qoDz
  have hDthCG := hfield (Dth C) G hC.qoDth hG.qo
  have hCDthG := hfield C (Dth G) hC.qo hG.qoDth
  have hsqCG : Work.Spaces.HkSq α 4 (fun z θ => C z θ * G z θ) ≤ P ^ 2 := by
    have hXn : Work.FTS.Nonlin.Xn α (fun z θ => C z θ * G z θ)
        ≤ Cprod * α ^ (-(1 / 2 : ℝ)) * a * b :=
      le_trans hCG.2 (Pd_le hAr ha hb hC.bd hG.bd
        (Work.Spaces.HkNorm_nonneg α 4 C) (Work.Spaces.HkNorm_nonneg α 4 G))
    rw [sq_eq_Xn_sq α, hPdef]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hXn 2
  have hsqDz : Work.Spaces.HkSq α 4 (fun z θ => Dz C z θ * G z θ) ≤ P ^ 2 := by
    have hXn : Work.FTS.Nonlin.Xn α (fun z θ => Dz C z θ * G z θ)
        ≤ Cprod * α ^ (-(1 / 2 : ℝ)) * a * b :=
      le_trans hDzCG.2 (Pd_le hAr ha hb hC.bdDz hG.bd
        (Work.Spaces.HkNorm_nonneg α 4 (Dz C)) (Work.Spaces.HkNorm_nonneg α 4 G))
    rw [sq_eq_Xn_sq α, hPdef]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hXn 2
  have hsqCDz : Work.Spaces.HkSq α 4 (fun z θ => C z θ * Dz G z θ) ≤ P ^ 2 := by
    have hXn : Work.FTS.Nonlin.Xn α (fun z θ => C z θ * Dz G z θ)
        ≤ Cprod * α ^ (-(1 / 2 : ℝ)) * a * b :=
      le_trans hCDzG.2 (Pd_le hAr ha hb hC.bd hG.bdDz
        (Work.Spaces.HkNorm_nonneg α 4 C) (Work.Spaces.HkNorm_nonneg α 4 (Dz G)))
    rw [sq_eq_Xn_sq α, hPdef]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hXn 2
  have hsqDth : Work.Spaces.HkSq α 4 (fun z θ => Dth C z θ * G z θ) ≤ P ^ 2 := by
    have hXn : Work.FTS.Nonlin.Xn α (fun z θ => Dth C z θ * G z θ)
        ≤ Cprod * α ^ (-(1 / 2 : ℝ)) * a * b :=
      le_trans hDthCG.2 (Pd_le hAr ha hb hC.bdDth hG.bd
        (Work.Spaces.HkNorm_nonneg α 4 (Dth C)) (Work.Spaces.HkNorm_nonneg α 4 G))
    rw [sq_eq_Xn_sq α, hPdef]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hXn 2
  have hsqCDth : Work.Spaces.HkSq α 4 (fun z θ => C z θ * Dth G z θ) ≤ P ^ 2 := by
    have hXn : Work.FTS.Nonlin.Xn α (fun z θ => C z θ * Dth G z θ)
        ≤ Cprod * α ^ (-(1 / 2 : ℝ)) * a * b :=
      le_trans hCDthG.2 (Pd_le hAr ha hb hC.bd hG.bdDth
        (Work.Spaces.HkNorm_nonneg α 4 C) (Work.Spaces.HkNorm_nonneg α 4 (Dth G)))
    rw [sq_eq_Xn_sq α, hPdef]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hXn 2
  -- ### the level shift
  have hsmC : Work.FTS.EllipticEst.SmoothOpen C := hC.qo.1
  have hsmG : Work.FTS.EllipticEst.SmoothOpen G := hG.qo.1
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => C z θ * G z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hsmC hsmG
  have hsmDz : Work.FTS.EllipticEst.SmoothOpen (Dz (fun z θ => C z θ * G z θ)) := hsm.Dz
  have hsmDth : Work.FTS.EllipticEst.SmoothOpen (Dth (fun z θ => C z θ * G z θ)) := hsm.Dth
  have hsmDzC : Work.FTS.EllipticEst.SmoothOpen (Dz C) := hC.qoDz.1
  have hsmDzG : Work.FTS.EllipticEst.SmoothOpen (Dz G) := hG.qoDz.1
  have hsmDthC : Work.FTS.EllipticEst.SmoothOpen (Dth C) := hC.qoDth.1
  have hsmDthG : Work.FTS.EllipticEst.SmoothOpen (Dth G) := hG.qoDth.1
  have hDzm : Work.Spaces.HkMem α 4 (Dz (fun z θ => C z θ * G z θ)) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4
      (Work.FTS.EllipticEst.RPFresh.HkMem_add_open α 4
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hsmDzC hsmG)
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hsmC hsmDzG)
        hDzCG.1 hCDzG.1)
      (fun z hz θ hθ => (Dz_mul_eqOn_Q0 hsmC hsmG z θ hz hθ.1 hθ.2).symm)
  have hDthm : Work.Spaces.HkMem α 4 (Dth (fun z θ => C z θ * G z θ)) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4
      (Work.FTS.EllipticEst.RPFresh.HkMem_add_open α 4
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hsmDthC hsmG)
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hsmC hsmDthG)
        hDthCG.1 hCDthG.1)
      (fun z hz θ hθ => (Dth_mul_eqOn_Q0 hsmC hsmG z θ hz hθ.1 hθ.2).symm)
  have hsq5 : Work.Spaces.HkSq α 5 (fun z θ => C z θ * G z θ) ≤ 9 * P ^ 2 := by
    have hshift := HkSq_succ_le (α := α) (k := 4) hα hsm (by norm_num) hCG.1 hDzm hDthm
    have hDzsq : Work.Spaces.HkSq α 4 (Dz (fun z θ => C z θ * G z θ))
        ≤ 2 * (Work.Spaces.HkSq α 4 (fun z θ => Dz C z θ * G z θ)
            + Work.Spaces.HkSq α 4 (fun z θ => C z θ * Dz G z θ)) := by
      have h1 := Work.FTS.GalFields.RHS.HkSq_add_le_open α 4 hα
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hsmDzC hsmG)
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hsmC hsmDzG) hDzCG.1 hCDzG.1
      rwa [Work.FTS.EllipticEst.HkSq_congr_open α 4
        (fun z θ hz hθ hθ' => (Dz_mul_eqOn_Q0 hsmC hsmG z θ hz hθ hθ').symm)] at h1
    have hDthsq : Work.Spaces.HkSq α 4 (Dth (fun z θ => C z θ * G z θ))
        ≤ 2 * (Work.Spaces.HkSq α 4 (fun z θ => Dth C z θ * G z θ)
            + Work.Spaces.HkSq α 4 (fun z θ => C z θ * Dth G z θ)) := by
      have h1 := Work.FTS.GalFields.RHS.HkSq_add_le_open α 4 hα
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hsmDthC hsmG)
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hsmC hsmDthG) hDthCG.1 hCDthG.1
      rwa [Work.FTS.EllipticEst.HkSq_congr_open α 4
        (fun z θ hz hθ hθ' => (Dth_mul_eqOn_Q0 hsmC hsmG z θ hz hθ hθ').symm)] at h1
    linarith [hshift, hsqCG, hsqDz, hsqCDz, hsqDth, hsqCDth, hDzsq, hDthsq, hPnn]
  -- ### the membership and the norm
  have hmemCG : Work.Spaces.HkMem α 4 (fun z θ => C z θ * G z θ) := hCG.1
  have hmem5 : Work.Spaces.HkMem α 5 (fun z θ => C z θ * G z θ) :=
    HkMem_succ_of hα hsm (k := 4) (by norm_num) hmemCG hDzm hDthm
  refine ⟨Work.FTS.LocData.HkMem_const_mul α 5 c hmem5, ?_⟩
  have hsqc : Work.Spaces.HkSq α 5 (fun z θ => c * (C z θ * G z θ))
      = c ^ 2 * Work.Spaces.HkSq α 5 (fun z θ => C z θ * G z θ) :=
    Work.FTS.StrongEps.HkSq_const_mul α 5 c (fun z θ => C z θ * G z θ)
  have hroot : Work.Spaces.HkNorm α 5 (fun z θ => c * (C z θ * G z θ))
      = Real.sqrt (Work.Spaces.HkSq α 5 (fun z θ => c * (C z θ * G z θ))) := rfl
  have hsqc' : Work.Spaces.HkSq α 5 (fun z θ => c * (C z θ * G z θ))
      ≤ (|c| * (3 * P)) ^ 2 := by
    rw [hsqc]
    calc c ^ 2 * Work.Spaces.HkSq α 5 (fun z θ => C z θ * G z θ)
        ≤ c ^ 2 * (9 * P ^ 2) := mul_le_mul_of_nonneg_left hsq5 (sq_nonneg c)
      _ = (|c| * (3 * P)) ^ 2 := by
          rw [← sq_abs c]
          ring
  calc Work.Spaces.HkNorm α 5 (fun z θ => c * (C z θ * G z θ))
      = Real.sqrt (Work.Spaces.HkSq α 5 (fun z θ => c * (C z θ * G z θ))) := hroot
    _ ≤ Real.sqrt ((|c| * (3 * P)) ^ 2) := Real.sqrt_le_sqrt hsqc'
    _ = |c| * (3 * P) := Real.sqrt_sq (by positivity)
    _ = |c| * (3 * (Cprod * α ^ (-(1 / 2 : ℝ)) * a * b)) := by rw [hPdef]

end Work.FTS.StrongEps.H5
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.Lhat_integrand_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.StrongPersist.H6Aux

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.FTS.StrongPersist.L6Aux (coeffSum P3 coeffSum_nonneg eqOn_three_div_gpoly
  abs_eval_le_coeffSum)
open Work.FTS.CoercivityFix.E2Bound (Tmul gpoly zchart)

/-! ## The `Zop`-iterates of `z ↦ 3/(1+z)` up to order `m` -/

/-- **The `Zop`-iterates of the multiplier `z ↦ 3/(1+z)` up to order `m` are uniformly
bounded**, the bound depending on `m`.  This is `PhiZopBound6` with the level six replaced by
the general level `m`. -/
lemma three_div_zop_bound (m : ℕ) : ∃ K : ℝ, 0 < K ∧ ∀ b ≤ m, ∀ z ∈ Set.Ioi (0 : ℝ),
    |Work.Spaces.Zop^[b] (fun z : ℝ => 3 / (1 + z)) z| ≤ K := by
  refine ⟨max 3 (∑ b ∈ Finset.range (m + 1), coeffSum (Tmul^[b] P3)) + 1,
    by positivity, ?_⟩
  intro b hb z hz
  have hbmem : b ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hb)
  have hle : coeffSum (Tmul^[b] P3)
      ≤ ∑ b' ∈ Finset.range (m + 1), coeffSum (Tmul^[b'] P3) :=
    Finset.single_le_sum (f := fun b' => coeffSum (Tmul^[b'] P3))
      (fun i _ => coeffSum_nonneg _) hbmem
  have hBig : (∑ b' ∈ Finset.range (m + 1), coeffSum (Tmul^[b'] P3))
      ≤ max 3 (∑ b' ∈ Finset.range (m + 1), coeffSum (Tmul^[b'] P3)) + 1 := by
    have := le_max_right (3 : ℝ) (∑ b' ∈ Finset.range (m + 1), coeffSum (Tmul^[b'] P3))
    linarith
  have h1 : Work.Spaces.Zop^[b] (fun z : ℝ => 3 / (1 + z)) z
      = (Tmul^[b] P3).eval (zchart z) := by
    rw [Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_eqOn_of_eqOn b isOpen_Ioi
          eqOn_three_div_gpoly hz,
        Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_gpoly_iterate P3 b z hz]
    rfl
  rw [h1]
  have h2 : |(Tmul^[b] P3).eval (zchart z)| ≤ coeffSum (Tmul^[b] P3) :=
    abs_eval_le_coeffSum _ (Work.FTS.CoercivityFix.E2Bound.abs_zchart_le_one hz)
  linarith

/-! ## The integrand bound -/

theorem Lhat_integrand_le (α : ℝ) (hα : 0 < α) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℝ → ℝ → ℝ, Work.FTS.EllipticEst.SmoothOpen g →
      ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        Work.Spaces.HkIntegrand α m (Work.FTS.CoercivityFix.Lhat g) z θ
          ≤ C * Work.Spaces.HkIntegrand α (m + 1) g z θ := by
  obtain ⟨K, hKpos, hKb⟩ := three_div_zop_bound m
  have hK : (0 : ℝ) ≤ K := hKpos.le
  refine ⟨8 * (Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2) + 9, ?_, ?_⟩
  · have h1 : 0 ≤ Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2 :=
      mul_nonneg (Work.FTS.StrongPersist.L3Aux.zmulConst_pos m).le (sq_nonneg _)
    linarith
  · intro g hg z hz θ hθ
    have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr (le_of_lt hz)
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hZnn : 0 ≤ Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2 :=
      mul_nonneg (Work.FTS.StrongPersist.L3Aux.zmulConst_pos m).le (sq_nonneg _)
    have hRnn : 0 ≤ Work.Spaces.HkIntegrand α (m + 1) g z θ :=
      Work.Spaces.HkIntegrand_nonneg α (m + 1) g z θ
    have hφsm : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 3 / (1 + z))
        (Set.Ioi (-1)) :=
      contDiffOn_iff_forall_nat_le.mpr (fun k _ => Work.FTS.FinalClock.contDiffOn_phiThree k)
    -- the multiplier estimate for `φ(z) = 3/(1+z)`, for an arbitrary `SmoothOpen` factor
    have hmul (X : ℝ → ℝ → ℝ) (hX : Work.FTS.EllipticEst.SmoothOpen X) :
        Work.Spaces.HkIntegrand α m (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * X z θ) z θ
          ≤ (Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
              * Work.Spaces.HkIntegrand α m X z θ :=
      Work.FTS.StrongPersist.L3Aux.zmul_open α m (fun z : ℝ => 3 / (1 + z)) X hK hKb hφsm hX
        z hz θ hθ
    -- the index shifts
    have hshiftZ : Work.Spaces.HkIntegrand α m (Work.Spaces.Dz g) z θ
        ≤ Work.Spaces.HkIntegrand α (m + 1) g z θ := by
      have h := Work.FTS.StrongPersist.L3Aux.HkIntegrand_mixed_shift α hα m 0 1 hg z hzIz θ hθI
      simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
        Nat.reduceAdd] using h
    have hshiftT : Work.Spaces.HkIntegrand α m (Work.Spaces.Dth g) z θ
        ≤ Work.Spaces.HkIntegrand α (m + 1) g z θ := by
      have h := Work.FTS.StrongPersist.L3Aux.HkIntegrand_mixed_shift α hα m 1 0 hg z hzIz θ hθI
      simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero,
        Nat.reduceAdd, Nat.add_zero] using h
    have hmono : Work.Spaces.HkIntegrand α m g z θ ≤ Work.Spaces.HkIntegrand α (m + 1) g z θ :=
      Work.FTS.StrongPersist.HkIntegrand_le_of_le α (Nat.le_succ m) g z θ
    -- smoothness of the three new summands of the decomposition
    have hφopen : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => (fun z : ℝ => 3 / (1 + z)) z) :=
      Work.FTS.StrongPersist.linMem_radial hφsm
    have hBsm : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (-(2 / 3)) * ((fun z : ℝ => 3 / (1 + z)) z * g z θ)) :=
      Work.FTS.StrongPersist.linMem_const_mul (-(2 / 3))
        (Work.FTS.StrongPersist.linMem_mul hφopen hg)
    have hDsm : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (-1) * ((fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth g z θ)) :=
      Work.FTS.StrongPersist.linMem_const_mul (-1)
        (Work.FTS.StrongPersist.linMem_mul hφopen hg.Dth)
    -- the bound for each of the three summands
    have hA : Work.Spaces.HkIntegrand α m (fun z θ => g z θ + Work.Spaces.Dz g z θ) z θ
        ≤ 4 * Work.Spaces.HkIntegrand α (m + 1) g z θ := by
      have h := Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α m
        (f := g) (g := Work.Spaces.Dz g) (hg.forall m) ((hg.Dz).forall m) z hzIz θ hθI
      linarith [h, hmono, hshiftZ]
    have hB : Work.Spaces.HkIntegrand α m
        (fun z θ => (-(2 / 3)) * ((fun z : ℝ => 3 / (1 + z)) z * g z θ)) z θ
        ≤ (4 / 9) * ((Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
            * Work.Spaces.HkIntegrand α (m + 1) g z θ) := by
      rw [Work.FTS.LocData.HkIntegrand_const_mul]
      have hsq : (-(2 / 3) : ℝ) ^ 2 = 4 / 9 := by norm_num
      rw [hsq]
      have h2 : Work.Spaces.HkIntegrand α m
            (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * g z θ) z θ
          ≤ (Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
              * Work.Spaces.HkIntegrand α (m + 1) g z θ :=
        le_trans (hmul g hg) (mul_le_mul_of_nonneg_left hmono hZnn)
      exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    have hD : Work.Spaces.HkIntegrand α m
        (fun z θ => (-1) * ((fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth g z θ)) z θ
        ≤ (Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
            * Work.Spaces.HkIntegrand α (m + 1) g z θ := by
      rw [Work.FTS.LocData.HkIntegrand_const_mul]
      have h2 : Work.Spaces.HkIntegrand α m
            (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth g z θ) z θ
          ≤ (Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
              * Work.Spaces.HkIntegrand α (m + 1) g z θ :=
        le_trans (hmul (Work.Spaces.Dth g) hg.Dth)
          (mul_le_mul_of_nonneg_left hshiftT hZnn)
      norm_num
      exact h2
    have hBD : Work.Spaces.HkIntegrand α m
        (fun z θ => (-(2 / 3)) * ((fun z : ℝ => 3 / (1 + z)) z * g z θ)
          + (-1) * ((fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth g z θ)) z θ
        ≤ 2 * ((4 / 9) * ((Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
              * Work.Spaces.HkIntegrand α (m + 1) g z θ))
          + 2 * ((Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
              * Work.Spaces.HkIntegrand α (m + 1) g z θ) := by
      have h := Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α m
        (f := fun z θ => (-(2 / 3)) * ((fun z : ℝ => 3 / (1 + z)) z * g z θ))
        (g := fun z θ => (-1) * ((fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth g z θ))
        (hBsm.forall m) (hDsm.forall m) z hzIz θ hθI
      linarith [h, hB, hD]
    -- assemble along `𝓛̂g = (g + D_z g) + [(−2/3)·(φ g) + (−1)·(φ D_θ g)]`
    have hLhat : Work.FTS.CoercivityFix.Lhat g
        = fun z θ => (g z θ + Work.Spaces.Dz g z θ)
            + ((-(2 / 3)) * ((fun z : ℝ => 3 / (1 + z)) z * g z θ)
               + (-1) * ((fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth g z θ)) := by
      funext z θ
      rw [Work.FTS.CoercivityFix.Lhat_eq]
      ring
    rw [hLhat]
    have hfinal := Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α m
      (f := fun z θ => g z θ + Work.Spaces.Dz g z θ)
      (g := fun z θ => (-(2 / 3)) * ((fun z : ℝ => 3 / (1 + z)) z * g z θ)
        + (-1) * ((fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth g z θ))
      ((hg.forall m).add ((hg.Dz).forall m)) ((hBsm.forall m).add (hDsm.forall m)) z hzIz θ hθI
    have hkey : 2 * (4 * Work.Spaces.HkIntegrand α (m + 1) g z θ)
        + 2 * (2 * ((4 / 9) * ((Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
                * Work.Spaces.HkIntegrand α (m + 1) g z θ))
          + 2 * ((Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
              * Work.Spaces.HkIntegrand α (m + 1) g z θ))
        ≤ (8 * (Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2) + 9)
            * Work.Spaces.HkIntegrand α (m + 1) g z θ := by
      nlinarith [hRnn, hZnn]
    linarith [hfinal, hA, hBD, hkey]

end Work.FTS.StrongPersist.H6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.N0PieceHelpers =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

/-- `Zop` commutes with multiplication by a constant. -/
lemma nzZop_iter_const_mul (c : ℝ) (u : ℝ → ℝ) (b : ℕ) :
    Work.Spaces.Zop^[b] (fun z => c * u z) = fun z => c * (Work.Spaces.Zop^[b] u) z := by
  have hgen : ∀ w : ℝ → ℝ,
      Work.Spaces.Zop (fun z => c * w z) = fun z => c * Work.Spaces.Zop w z := by
    intro w
    funext z
    simp only [Work.Spaces.Zop]
    rw [Work.Spaces.deriv_const_mul']
    ring
  induction b generalizing u with
  | zero => rfl
  | succ n ih =>
      calc Work.Spaces.Zop^[n + 1] (fun z => c * u z)
          = Work.Spaces.Zop (Work.Spaces.Zop^[n] (fun z => c * u z)) :=
            Function.iterate_succ_apply' Work.Spaces.Zop n (fun z => c * u z)
        _ = Work.Spaces.Zop (fun z => c * (Work.Spaces.Zop^[n] u) z) := by rw [ih u]
        _ = fun z => c * (Work.Spaces.Zop (Work.Spaces.Zop^[n] u)) z := hgen _
        _ = fun z => c * (Work.Spaces.Zop^[n + 1] u) z := by
              rw [← Function.iterate_succ_apply' Work.Spaces.Zop n u]

/-- `c₂ₘ θ = (3/2)·qfun θ`, where `qfun θ = cos 2θ - 1/3`. -/
lemma nzc2m_eq_qfun (θ : ℝ) :
    Work.Construction.c2m θ = (3 / 2) * Work.Spaces.qfun θ := by
  have h1 : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq θ]
  simp only [Work.Construction.c2m, Work.Spaces.qfun, Real.cos_two_mul]
  rw [h1]; ring





/-- `F_*`'s radial profile `2z/(1+z)²` is `C^∞` on `(0,∞)`. -/
theorem nzsmoothOn_FMFstar :
    ContDiffOn ℝ Work.Stability.smoothOrder Work.FM.Fstar (Set.Ioi 0) := by
  have h : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 2 * z / (1 + z) ^ 2)
      (Set.Ioi (-1 : ℝ)) := by
    have hnum : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 2 * z) (Set.Ioi (-1 : ℝ)) :=
      contDiffOn_const.mul contDiffOn_id
    have hden : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => (1 + z) ^ 2)
        (Set.Ioi (-1 : ℝ)) :=
      (contDiffOn_const.add contDiffOn_id).pow 2
    exact hnum.div hden (fun z hz => by
      simp only [Set.mem_Ioi] at hz
      have : (0 : ℝ) < 1 + z := by linarith
      positivity)
  refine (h.mono (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0))).congr ?_
  intro z hz
  rfl

/-- The radial profile `H(z) = 2z(1-z)/(1+z)³` of `D_z F_*` is `C^∞` on `(0,∞)`. -/
theorem nzsmoothOn_Hz :
    ContDiffOn ℝ Work.Stability.smoothOrder Work.FTS.Nonlinear.FstarPkg.Hz (Set.Ioi 0) := by
  have h : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 2 * z * (1 - z) / (1 + z) ^ 3)
      (Set.Ioi (-1 : ℝ)) := by
    have hnum : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 2 * z * (1 - z))
        (Set.Ioi (-1 : ℝ)) :=
      (contDiffOn_const.mul contDiffOn_id).mul (contDiffOn_const.sub contDiffOn_id)
    have hden : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => (1 + z) ^ 3)
        (Set.Ioi (-1 : ℝ)) :=
      (contDiffOn_const.add contDiffOn_id).pow 3
    exact hnum.div hden (fun z hz => by
      simp only [Set.mem_Ioi] at hz
      have : (0 : ℝ) < 1 + z := by linarith
      positivity)
  refine (h.mono (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0))).congr ?_
  intro z hz
  rfl

/-- The `Zop`-iterates of the two radial profiles of the `F_*`-pieces are bounded. -/
theorem nzradZop_bound6 : ∃ Kr : ℝ, 0 < Kr ∧
    (∀ b ≤ 6, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] Work.FM.Fstar z| ≤ Kr) ∧
    (∀ b ≤ 6, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Spaces.Zop^[b] Work.FTS.Nonlinear.FstarPkg.Hz z| ≤ Kr) := by
  obtain ⟨K, hKnn, hK⟩ := Work.FTS.CoercivityFix.E2Bound.zop_phi_bound 7
  have hfun : Work.FM.Fstar = fun y : ℝ => 2 * (y / (1 + y) ^ 2) := by
    funext y
    simp only [Work.FM.Fstar]
    ring
  have hHz : ∀ y : ℝ, 0 < y → Work.FTS.Nonlinear.FstarPkg.Hz y
      = (Work.Spaces.Zop Work.FM.Fstar) y := by
    intro y hy
    rw [Work.Spaces.Zop, Work.FM.deriv_Fstar y (by linarith)]
    simp only [Work.FTS.Nonlinear.FstarPkg.Hz]
    ring
  refine ⟨2 * K + 1, by linarith, ?_, ?_⟩
  · intro b hb z hz
    rw [hfun, nzZop_iter_const_mul]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h := hK b (by omega) z hz
    linarith
  · intro b hb z hz
    have hcongr : Work.Elliptic.DzdIter b Work.FTS.Nonlinear.FstarPkg.Hz z
        = Work.Elliptic.DzdIter b (Work.Spaces.Zop Work.FM.Fstar) z :=
      Work.FTS.StrongPersist.DzdIter_congr_Ioi hHz b z hz
    have key1 : Work.Spaces.Zop^[b] Work.FTS.Nonlinear.FstarPkg.Hz z
        = Work.Spaces.Zop^[b] (Work.Spaces.Zop Work.FM.Fstar) z := by
      rw [Zop_iter_eq_DzdIter, Zop_iter_eq_DzdIter]
      exact hcongr
    rw [key1]
    rw [show Work.Spaces.Zop^[b] (Work.Spaces.Zop Work.FM.Fstar)
        = Work.Spaces.Zop^[b + 1] Work.FM.Fstar from
      (Function.iterate_succ_apply Work.Spaces.Zop b Work.FM.Fstar).symm]
    rw [hfun, nzZop_iter_const_mul]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h := hK (b + 1) (by omega) z hz
    linarith


/-- **The separability identity for `N₀₄ₐ`.** -/
lemma nzN04a_sep {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ} :
    ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Construction.N04a α (fun z θ => Work.Construction.Fstar α z θ + f z θ) f z θ
        = (3 * α / (2 * Work.Spaces.c α)) * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)
            * (Work.Construction.L12 f z * Work.FM.Fstar z) := by
  intro z θ hz hθ
  have hαne : α ≠ 0 := ne_of_gt hα
  have hcne : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0; rw [h0] at h; norm_num at h
  have hpth : Work.Spaces.pth (Work.Construction.Fstar α) z θ
      = (α * Work.FM.Fstar z / Work.Spaces.c α) * deriv (fun t => Work.Spaces.Gam α t) θ := by
    simp only [Work.Spaces.pth, Work.Construction.Fstar]
    rw [show (fun θ' : ℝ => α * (Work.Spaces.Gam α θ' / Work.Spaces.c α) * Work.FM.Fstar z)
        = fun θ' : ℝ => (α * Work.FM.Fstar z / Work.Spaces.c α) * Work.Spaces.Gam α θ' from by
      funext θ'; ring]
    rw [Work.Spaces.deriv_const_mul']
  have hdth : Real.sin (2 * θ) * deriv (fun t => Work.Spaces.Gam α t) θ
      = α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ := by
    have h := Work.Spaces.dthU_Gam α θ hα hθ
    simpa only [Work.Spaces.dthU] using h
  simp only [Work.Construction.N04a, Work.Construction.s2]
  rw [hpth]
  rw [show (3 / (2 * α)) * Real.sin (2 * θ) * Work.Construction.L12 f z
        * ((α * Work.FM.Fstar z / Work.Spaces.c α) * deriv (fun t => Work.Spaces.Gam α t) θ)
      = (3 / (2 * α)) * Work.Construction.L12 f z * (α * Work.FM.Fstar z / Work.Spaces.c α)
          * (Real.sin (2 * θ) * deriv (fun t => Work.Spaces.Gam α t) θ) from by ring]
  rw [hdth]
  field_simp
  try ring

/-- **The separability identity for `N₀₅ₐ`.** -/
lemma nzN05a_sep {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ} :
    ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Construction.N05a α (fun z θ => Work.Construction.Fstar α z θ + f z θ) f z θ
        = (-(3 * α / (2 * Work.Spaces.c α))) * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)
            * (Work.Construction.L12 f z * Work.FTS.Nonlinear.FstarPkg.Hz z) := by
  intro z θ hz hθ
  have hαne : α ≠ 0 := ne_of_gt hα
  have hcne : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0; rw [h0] at h; norm_num at h
  rw [Work.Construction.N05a, Work.FTS.Nonlinear.FstarPkg.Dz_Fstar_eq_Hz hα (by linarith),
    nzc2m_eq_qfun]
  field_simp
  try ring



end Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.mixedRadialThetaMul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Leibniz rule for the mixed operator with a radial and an angular factor

`Work.Spaces.mixed b a = D_z^b D_θ^a` (`D_z = z ∂_z`, `D_θ = sin(2θ) ∂_θ`).  For a product

  `(z,θ) ↦ X z * (γ θ * f z θ)`

of a *radial* factor `X` which is only `C^6` on `(0,∞)` (so not smooth on the closed quadrant and
therefore outside the derivation-like API of `Work.Spaces`, which is stated for classes smooth on
a *neighbourhood* of the closed quadrant or for analytic data), an *angular* factor `γ` which is
smooth on the open quadrant, and a datum `f` smooth on the open quadrant, the iterated mixed
derivative splits as a double binomial convolution:

`D_z^b D_θ^a (X·γ·f) = Σ_{k ≤ b} Σ_{i ≤ a} C(b,k)·C(a,i)·(D_z^k X)·(D_θ^i γ)·(D_z^{b-k}D_θ^{a-i} f)`.

The proof is the composition of the two available Leibniz rules:

* `Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul` splits off the radial factor `X` (all
  the resulting `z`-derivatives fall on `X` and `f`, none on `γ`);
* `thetaOnlyLeibniz` (below) splits the angular factor `γ` off the remaining mixed derivative.

The second rule is the pair Leibniz rule `Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed` for the
open quadrant, in which the factor `γ` only depends on `θ`: all the `D_z`-derivatives of `γ̃` with
positive order vanish (`mixed_zindep_zero`), so the double sum collapses to a single one.

Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Work.FTS.StrongPersist.H6Pair6Aux.T5bAux

open scoped Real Topology
open Set Filter

set_option autoImplicit false

/-! ## `z`-independent data -/

/-- If `u` does not depend on `z`, then nor does any of its `D_θ`-iterates. -/
lemma DthIter_zindep {u : ℝ → ℝ → ℝ} (h : ∀ z z' θ, u z θ = u z' θ) :
    ∀ x z z' θ, Work.Spaces.DthIter x u z θ = Work.Spaces.DthIter x u z' θ := by
  intro x
  induction x with
  | zero => exact fun z z' θ => h z z' θ
  | succ n ih =>
      intro z z' θ
      show Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DthIter n u) z θ
        = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DthIter n u) z' θ
      congr 1
      show deriv (fun θ' => Work.Spaces.DthIter n u z θ') θ
        = deriv (fun θ' => Work.Spaces.DthIter n u z' θ') θ
      congr 1
      funext θ'
      exact ih z z' θ'

/-- The iterate of `Zop u = z u'` vanishes on constants (in positive order). -/
private lemma Zop_iterate_const_succ (y : ℕ) (c : ℝ) :
    Work.Spaces.Zop^[y + 1] (fun _ : ℝ => c) = fun _ => 0 := by
  induction y with
  | zero =>
      funext z
      simp [Work.Spaces.Zop, deriv_const]
  | succ y ih =>
      rw [Function.iterate_succ_apply', ih]
      funext z
      simp [Work.Spaces.Zop, deriv_const]

/-- All the mixed derivatives `D_z^y D_θ^x u` with `y ≥ 1` of a `z`-independent `u` vanish. -/
lemma mixed_zindep_zero {u : ℝ → ℝ → ℝ} (h : ∀ z z' θ, u z θ = u z' θ) :
    ∀ y, 1 ≤ y → ∀ x z θ, Work.Spaces.mixed y x u z θ = 0 := by
  intro y hy x z θ
  have hz : (fun z' => Work.Spaces.DthIter x u z' θ) = fun _ => Work.Spaces.DthIter x u z θ := by
    funext z'
    exact DthIter_zindep h x z' z θ
  have h1 : Work.Spaces.DzIter y (Work.Spaces.DthIter x u) z θ
      = Work.Spaces.Zop^[y] (fun z' => Work.Spaces.DthIter x u z' θ) z :=
    congrFun (Work.Spaces.Zop_slice y (Work.Spaces.DthIter x u) θ) z
  show Work.Spaces.DzIter y (Work.Spaces.DthIter x u) z θ = 0
  rw [h1, hz]
  obtain ⟨k, rfl⟩ : ∃ k, y = k + 1 := ⟨y - 1, by omega⟩
  rw [Zop_iterate_const_succ]

/-! ## The Leibniz rule for an angular factor -/

/-- **Leibniz rule for a `θ`-only factor.**  For `γ` smooth on the open quadrant (viewed as
`(z,θ) ↦ γ θ`) and a datum `f` smooth on the open quadrant,

`D_z^j D_θ^a (γ·f) = Σ_{i ≤ a} C(a,i)·(D_θ^i γ)·(D_z^j D_θ^{a-i} f)` on `Q0`.

This is the pair Leibniz rule `leibniz_open_mixed` in which all the terms with a positive number
of `z`-derivatives on `γ` are killed by `mixed_zindep_zero`. -/
lemma thetaOnlyLeibniz {γ : ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    (hγ : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => γ θ))
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ (j a : ℕ) (z θ : ℝ), 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed j a (fun z θ => γ θ * f z θ) z θ
        = ∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ)
            * (Work.Spaces.DthIter i (fun _ θ : ℝ => γ θ) z θ
                * Work.Spaces.mixed j (a - i) f z θ) := by
  intro j a z θ hz hθ0 hθ1
  have h := Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed j a (fun _ θ : ℝ => γ θ) f hγ hf
    z θ hz hθ0 hθ1
  rw [h]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.sum_eq_single 0]
  · simp only [Nat.choose_zero_right, Nat.cast_one, mul_one, tsub_zero]
    rfl
  · intro y hy hy0
    have hy1 : 1 ≤ y := Nat.one_le_iff_ne_zero.mpr hy0
    have hzero : Work.Spaces.mixed y x (fun _ θ : ℝ => γ θ) z θ = 0 :=
      mixed_zindep_zero (fun z z' θ => rfl) y hy1 x z θ
    rw [hzero]
    ring
  · intro h0
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos j)) h0

/-! ## The main lemma -/

theorem mixedRadialThetaMul {X : ℝ → ℝ} {γ : ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    (hX : ContDiffOn ℝ 6 X (Set.Ioi 0))
    (hγ : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => γ θ))
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ (b a : ℕ), b ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed b a (fun z θ => X z * (γ θ * f z θ)) z θ
        = ∑ k ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
            ((b.choose k : ℝ) * (a.choose i : ℝ))
              * (Work.Elliptic.DzdIter k X z
                  * (Work.Spaces.DthIter i (fun _ θ : ℝ => γ θ) z θ
                      * Work.Spaces.mixed (b - k) (a - i) f z θ)) := by
  intro b a hb z θ hz hθ0 hθ1
  have hF : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => γ θ * f z θ) := by
    show ContDiffOn ℝ Work.Stability.smoothOrder (fun x : ℝ × ℝ => γ x.2 * f x.1 x.2)
      Work.FTS.EllipticEst.Q0
    exact hγ.mul hf
  have h1 := Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul (X := X)
    (f := fun z θ : ℝ => γ θ * f z θ) hX hF b a hb z θ hz hθ0 hθ1
  rw [h1]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [thetaOnlyLeibniz hγ hf (b - k) a z θ hz hθ0 hθ1]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  ring

end Work.FTS.StrongPersist.H6Pair6Aux.T5bAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6.zopIter_one_add_rhoR_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `(1+z)·ρ` companion of the radial `ℋ⁶` bound

The task statement asks for the `Zop`-iterate bound of the *shifted* radial profile
`(1+z)·ρ(z)` (`ρ = Work.Construction.rhoR`), given the corresponding bound for `ρ` itself:

`|(Zop^[j] ρ)(z)·w(z)| ≤ M/(1+z)²`  ⟹  `|(Zop^[j] ((1+z)·ρ))(z)·w(z)| ≤ 64M/(1+z)`  (`j ≤ 6`).

The whole content is the **iterated Leibniz rule** for the radial derivation
`Zop u = z u'` (`Work.FTS.FinalClock.ZopIterLeibniz`), applied to the product
`(fun z => 1 + z) * ρ` on the open set `Ioi (-1)` (where both factors are `C^j`), together with
the elementary fact that

* `Zop^[0] (fun z => 1 + z) = fun z => 1 + z`, and
* `Zop^[b+1] (fun z => 1 + z) = fun z => z`   (since `Zop (1+·) = 1·(1+·)' ·z = z` and `Zop z = z`);

hence `0 ≤ Zop^[b](1+·) z ≤ 1 + z` for `z ≥ 0`.  The Leibniz sum therefore factors as

`|Zop^[j]((1+z)ρ) z · w z| ≤ ∑_{b ≤ j} C(j,b) · (1+z) · M/(1+z)² = 2^j · M/(1+z) ≤ 64 M/(1+z)`

for `j ≤ 6`.  The case `z = 0` is trivial because `w 0 = 0` (`w` is totalised division).

This is the standard `2^j`-loss one expects from a Leibniz expansion; the constant `64 = 2^6`
of the statement is exactly `2^j` at the top order `j = 6`, so the bound is sharp as an
application of this method.
-/

open scoped Real Topology
open Set Filter

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6

/-! ## The `Zop`-iterates of `fun z => 1 + z` -/

/-- `Zop` sends `fun z => 1 + z` to `fun z => z`. -/
theorem zop_one_eq_id : Work.Spaces.Zop (fun z : ℝ => 1 + z) = fun z : ℝ => z := by
  funext z; simp [Work.Spaces.Zop]

/-- `fun z => z` is a fixed point of `Zop`. -/
theorem zop_id_eq_id : Work.Spaces.Zop (fun z : ℝ => z) = fun z : ℝ => z := by
  funext z; simp [Work.Spaces.Zop]

/-- Every `Zop`-iterate of `fun z => z` is `fun z => z`. -/
theorem zop_iter_self (b : ℕ) : Work.Spaces.Zop^[b] (fun z : ℝ => z) = fun z : ℝ => z := by
  induction b with
  | zero => rfl
  | succ b ih => rw [Function.iterate_succ, Function.comp_apply, zop_id_eq_id, ih]

/-- The `(b+1)`-st `Zop`-iterate of `fun z => 1 + z` is `fun z => z`. -/
theorem zop_iter_one_add_succ (b : ℕ) :
    Work.Spaces.Zop^[b + 1] (fun z : ℝ => 1 + z) = fun z : ℝ => z := by
  rw [Function.iterate_succ, Function.comp_apply, zop_one_eq_id]
  exact zop_iter_self b

/-- The pointwise value of the `Zop`-iterates of `fun z => 1 + z`. -/
theorem zop_one_add_val (b : ℕ) (z : ℝ) :
    Work.Spaces.Zop^[b] (fun w : ℝ => 1 + w) z = (if b = 0 then 1 + z else z) := by
  rcases Nat.eq_zero_or_pos b with h | h
  · subst h; simp
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp h)
    rw [zop_iter_one_add_succ c]
    simp

/-- For `z ≥ 0` every `Zop`-iterate of `fun z => 1 + z` lies in `[0, 1+z]`. -/
theorem zop_one_add_le (b : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    0 ≤ Work.Spaces.Zop^[b] (fun w : ℝ => 1 + w) z ∧
      Work.Spaces.Zop^[b] (fun w : ℝ => 1 + w) z ≤ 1 + z := by
  rw [zop_one_add_val b z]
  split_ifs <;> constructor <;> linarith

/-! ## Smoothness of `ρ` on `(-1,∞)` -/

/-- `ρ(z) = z²/(1+z)⁴` is `C^j` on `(-1,∞)`. -/
theorem rhoR_contDiffOn (j : ℕ) :
    ContDiffOn ℝ j Work.Construction.rhoR (Set.Ioi (-1 : ℝ)) := by
  have hnum : ContDiffOn ℝ j (fun z : ℝ => z ^ 2) (Set.Ioi (-1 : ℝ)) :=
    (contDiff_id.contDiffOn).pow 2
  have hden : ContDiffOn ℝ j (fun z : ℝ => (1 + z) ^ 4) (Set.Ioi (-1 : ℝ)) :=
    ((contDiff_const.add contDiff_id).contDiffOn).pow 4
  have hne : ∀ z ∈ Set.Ioi (-1 : ℝ), (1 + z) ^ 4 ≠ 0 := by
    intro z hz
    have h : (-1 : ℝ) < z := hz
    have h2 : (0 : ℝ) < 1 + z := by linarith
    positivity
  have h := hnum.div hden hne
  have hfun : Work.Construction.rhoR = ((fun z : ℝ => z ^ 2) / fun z : ℝ => (1 + z) ^ 4) := by
    funext z
    simp [Work.Construction.rhoR, Pi.div_apply]
  rw [hfun]
  exact h

/-! ## The bound -/

theorem zopIter_one_add_rhoR_bound {M : ℝ} (hM : 0 < M)
    (hMr : ∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 0 ≤ z →
      |(Work.Spaces.Zop^[j] Work.Construction.rhoR) z * Work.Spaces.w z| ≤ M / (1 + z) ^ 2) :
    ∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 0 ≤ z →
      |(Work.Spaces.Zop^[j] (fun z : ℝ => (1 + z) * Work.Construction.rhoR z)) z
        * Work.Spaces.w z| ≤ (64 * M) / (1 + z) := by
  intro j hj z hz
  -- the total weight of the Leibniz sum is `2^j`
  have hchoose2j : ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) = (2 : ℝ) ^ j := by
    rw [← Nat.cast_sum, Nat.sum_range_choose]
    push_cast
    ring
  rcases eq_or_lt_of_le hz with h0 | hzpos
  · -- `z = 0` is trivial since `w 0 = 0`
    subst h0
    rw [show Work.Spaces.w 0 = 0 by norm_num [Work.Spaces.w], mul_zero, abs_zero]
    positivity
  · have h1z : (0 : ℝ) < 1 + z := by linarith
    have hV : IsOpen (Set.Ioi (-1 : ℝ)) := isOpen_Ioi
    have hzV : z ∈ Set.Ioi (-1 : ℝ) := by show (-1 : ℝ) < z; linarith
    have hu : ContDiffOn ℝ j (fun w : ℝ => 1 + w) (Set.Ioi (-1 : ℝ)) :=
      (contDiff_const.add contDiff_id).contDiffOn
    have hv : ContDiffOn ℝ j Work.Construction.rhoR (Set.Ioi (-1 : ℝ)) := rhoR_contDiffOn j
    -- the iterated Leibniz rule for `Zop u = z u'` on `(-1,∞)`
    have hleib : Work.Spaces.Zop^[j] (fun w : ℝ => (1 + w) * Work.Construction.rhoR w) z
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Spaces.Zop^[b] (fun w : ℝ => 1 + w) z
                * (Work.Spaces.Zop^[j - b] Work.Construction.rhoR) z) := by
      have hfun : (fun w : ℝ => (1 + w) * Work.Construction.rhoR w)
          = (fun w : ℝ => 1 + w) * Work.Construction.rhoR := by
        funext w; rfl
      rw [hfun]
      exact Work.FTS.FinalClock.ZopIterLeibniz hV hu hv hzV
    rw [hleib]
    -- every summand of the Leibniz expansion is at most `C(j,b)·(1+z)·M/(1+z)²`
    have hterm : ∀ b ∈ Finset.range (j + 1),
        |((j.choose b : ℝ) * (Work.Spaces.Zop^[b] (fun w : ℝ => 1 + w) z
            * (Work.Spaces.Zop^[j - b] Work.Construction.rhoR) z)) * Work.Spaces.w z|
          ≤ (j.choose b : ℝ) * ((1 + z) * (M / (1 + z) ^ 2)) := by
      intro b hb
      have hbj : b ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
      have hjb : j - b ≤ 6 := by omega
      have hX := zop_one_add_le b z hz
      have hY := hMr (j - b) hjb z hz
      calc |((j.choose b : ℝ) * (Work.Spaces.Zop^[b] (fun w : ℝ => 1 + w) z
              * (Work.Spaces.Zop^[j - b] Work.Construction.rhoR) z)) * Work.Spaces.w z|
          = (j.choose b : ℝ) * (Work.Spaces.Zop^[b] (fun w : ℝ => 1 + w) z
              * |(Work.Spaces.Zop^[j - b] Work.Construction.rhoR) z * Work.Spaces.w z|) := by
            rw [show ((j.choose b : ℝ) * (Work.Spaces.Zop^[b] (fun w : ℝ => 1 + w) z
                * (Work.Spaces.Zop^[j - b] Work.Construction.rhoR) z)) * Work.Spaces.w z
                = (j.choose b : ℝ) * (Work.Spaces.Zop^[b] (fun w : ℝ => 1 + w) z
                  * ((Work.Spaces.Zop^[j - b] Work.Construction.rhoR) z * Work.Spaces.w z))
                from by ring]
            rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg hX.1]
        _ ≤ (j.choose b : ℝ) * ((1 + z) * (M / (1 + z) ^ 2)) := by
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
            exact mul_le_mul hX.2 hY (abs_nonneg _) (by linarith)
    calc |(∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
              * (Work.Spaces.Zop^[b] (fun w : ℝ => 1 + w) z
                  * (Work.Spaces.Zop^[j - b] Work.Construction.rhoR) z)) * Work.Spaces.w z|
        = |∑ b ∈ Finset.range (j + 1), ((j.choose b : ℝ)
              * (Work.Spaces.Zop^[b] (fun w : ℝ => 1 + w) z
                  * (Work.Spaces.Zop^[j - b] Work.Construction.rhoR) z)) * Work.Spaces.w z| := by
            rw [Finset.sum_mul]
      _ ≤ ∑ b ∈ Finset.range (j + 1), |((j.choose b : ℝ)
              * (Work.Spaces.Zop^[b] (fun w : ℝ => 1 + w) z
                  * (Work.Spaces.Zop^[j - b] Work.Construction.rhoR) z)) * Work.Spaces.w z| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) * ((1 + z) * (M / (1 + z) ^ 2)) :=
            Finset.sum_le_sum hterm
      _ = (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)) * ((1 + z) * (M / (1 + z) ^ 2)) := by
            rw [Finset.sum_mul]
      _ = (2 : ℝ) ^ j * ((1 + z) * (M / (1 + z) ^ 2)) := by rw [hchoose2j]
      _ ≤ (64 * M) / (1 + z) := by
            have h2j : (2 : ℝ) ^ j ≤ 64 := by
              have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj
              norm_num at h
              linarith
            have hbnd : (1 + z) * (M / (1 + z) ^ 2) = M / (1 + z) := by
              field_simp
            rw [hbnd]
            have hMdiv : 0 ≤ M / (1 + z) := by positivity
            calc (2 : ℝ) ^ j * (M / (1 + z)) ≤ 64 * (M / (1 + z)) :=
                  mul_le_mul_of_nonneg_right h2j hMdiv
              _ = (64 * M) / (1 + z) := by ring

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.radialMaj6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

noncomputable section

open scoped Real Topology
open Set Filter

set_option maxHeartbeats 1600000

/-!
## Multiplication by a `C^6` radial factor with bounded `D_z`-iterates costs a constant

The `ℋ⁶`-integrand of the product `(z,θ) ↦ X z · f z θ` (with `X` radial, `C⁶` on `(0,∞)`,
all of whose `D_z`-iterates up to order `6` are bounded by `B`) is pointwise dominated by a
multiple of the `ℋ⁶`-integrand of `f`, the constant depending only on `B` (not on `α`, `z`, `θ`).

The proof: the Leibniz rule `leibniz_radial_mul` expands `D_z^bD_θ^a (X·f)` as
`Σ_k C(b,k) (D_z^k X)(D_z^{b-k}D_θ^a f)` (all angular derivatives fall on `f`, since `X` is
radial); Cauchy–Schwarz (`sq_sum_le_card_mul_sum_sq`) together with the binomial bound
`b.choose k ≤ 2^b ≤ 64` (for `b ≤ 6`) gives, for each slot, the bound
`4096 · B² · HkIntegrand α 6 f`; summing over the at most `7` resp. `7 × 7` slots yields the
constant `2·10⁷·B² + 1`.
-/

/-- At `z = 0` the weight `w` vanishes (`w 0 = (1+0)²/0² = 1/0 = 0`, Lean's totalised
division), so every term of the weighted integrand vanishes there. -/
private theorem HkIntegrand_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta, Work.Spaces.w]
  simp

/-- `b.choose k ≤ 2^b ≤ 64` for `b ≤ 6`, hence `((b.choose k : ℝ))² ≤ 4096`. -/
private theorem choose_sq_le_4096 (b k : ℕ) (_hk : k ≤ b) (hb : b ≤ 6) :
    ((b.choose k : ℕ) : ℝ) ^ 2 ≤ 4096 := by
  have h1 : b.choose k ≤ 2 ^ b := Nat.choose_le_two_pow b k
  have h2 : 2 ^ b ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hb
  have h3 : ((b.choose k : ℕ) : ℝ) ≤ 64 := by
    have h : b.choose k ≤ 64 := by omega
    exact_mod_cast h
  nlinarith [h3, Nat.cast_nonneg (α := ℝ) (b.choose k)]

/-- A single pure `D_z`-slot of the `ℋ⁶`-integrand of the radial product `X · f`. -/
private theorem zslot6 {α B : ℝ} {X : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hB : 0 ≤ B)
    (hX : ContDiffOn ℝ 6 X (Set.Ioi 0))
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hR : ∀ b : ℕ, b ≤ 6 → |Work.Elliptic.DzdIter b X z| ≤ B)
    (i : ℕ) (hi : i ≤ 6) :
    (Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ 200704 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ := by
  have hHk : 0 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 6 f z θ
  have hlei :=
    Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul hX hf i 0 hi z θ hz hθ0 hθ1
  have hmm : Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
      = Work.Spaces.mixed i 0 (fun z θ => X z * f z θ) z θ := rfl
  have hsum : Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      = ∑ b ∈ Finset.range (i + 1),
          (((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) := by
    rw [hmm, hlei, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by
      rw [Work.Spaces.mixed_zero_right]
      ring
  rw [hsum]
  have hper : ∀ b ∈ Finset.range (i + 1),
      ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2)
      ≤ 4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ := by
    intro b hbmem
    have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hbmem)
    have hchoose : (((i.choose b : ℕ) : ℝ)) ^ 2 ≤ 4096 := choose_sq_le_4096 i b hbi hi
    have hRd : (Work.Elliptic.DzdIter b X z) ^ 2 ≤ B ^ 2 := by
      have hx := hR b (by omega)
      rw [← sq_abs]
      nlinarith [hx, abs_nonneg (Work.Elliptic.DzdIter b X z), hB]
    have hG : (Work.Spaces.DzIter (i - b) f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
      Work.Spaces.sq_le_HkIntegrand_z α 6 f z θ (i - b) (by omega)
    calc ((((i.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2
        = (((i.choose b : ℕ) : ℝ)) ^ 2 * (Work.Elliptic.DzdIter b X z) ^ 2
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
      _ ≤ 4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ := by
          have hc : (0 : ℝ) ≤ 4096 * B ^ 2 :=
            mul_nonneg (by norm_num : (0 : ℝ) ≤ 4096) (sq_nonneg B)
          exact mul_le_mul (mul_le_mul hchoose hRd (sq_nonneg _) (by norm_num)) hG
            (sq_nonneg _) hc
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
    (f := fun b => (((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))))
  have hcard : (((Finset.range (i + 1)).card : ℕ) : ℝ) ≤ 7 := by
    rw [Finset.card_range]
    exact_mod_cast (by omega : i + 1 ≤ 7)
  have hsum2 : (∑ b ∈ Finset.range (i + 1),
        ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2))
      ≤ 7 * (4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) := by
    calc (∑ b ∈ Finset.range (i + 1),
          ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
              * (Work.Spaces.DzIter (i - b) f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2))
        ≤ ∑ _b ∈ Finset.range (i + 1),
            (4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) :=
          Finset.sum_le_sum hper
      _ = ((i + 1 : ℕ) : ℝ) * (4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 7 * (4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) := by
          have hc : (0 : ℝ) ≤ 4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ :=
            mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4096) (sq_nonneg B)) hHk
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : i + 1 ≤ 7)) hc
  refine hcs.trans ?_
  calc (((Finset.range (i + 1)).card : ℕ) : ℝ)
          * ∑ b ∈ Finset.range (i + 1),
              ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
                * (Work.Spaces.DzIter (i - b) f z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2)
      ≤ 7 * (7 * (4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ)) :=
        mul_le_mul hcard hsum2 (Finset.sum_nonneg fun b _ => sq_nonneg _) (by norm_num)
    _ = 200704 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ := by ring

/-- A single mixed slot (`1 ≤ i`) of the `ℋ⁶`-integrand of the radial product `X · f`. -/
private theorem mslot6 {α B : ℝ} {X : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hB : 0 ≤ B)
    (hX : ContDiffOn ℝ 6 X (Set.Ioi 0))
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hR : ∀ b : ℕ, b ≤ 6 → |Work.Elliptic.DzdIter b X z| ≤ B)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 6) :
    (Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ 200704 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ := by
  have hHk : 0 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 6 f z θ
  have hj6 : j ≤ 6 := by omega
  have hlei :=
    Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul hX hf j i hj6 z θ hz hθ0 hθ1
  have hsum : Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ
      = ∑ b ∈ Finset.range (j + 1),
          (((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) := by
    rw [hlei, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hsum]
  have hper : ∀ b ∈ Finset.range (j + 1),
      ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2)
      ≤ 4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ := by
    intro b hbmem
    have hbj : b ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hbmem)
    have hchoose : (((j.choose b : ℕ) : ℝ)) ^ 2 ≤ 4096 := choose_sq_le_4096 j b hbj hj6
    have hRd : (Work.Elliptic.DzdIter b X z) ^ 2 ≤ B ^ 2 := by
      have hx := hR b (by omega)
      rw [← sq_abs]
      nlinarith [hx, abs_nonneg (Work.Elliptic.DzdIter b X z), hB]
    have hG : (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
      Work.Spaces.sq_le_HkIntegrand_mixed α 6 f z θ i (j - b) hi (by omega)
    calc ((((j.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2
        = (((j.choose b : ℕ) : ℝ)) ^ 2 * (Work.Elliptic.DzdIter b X z) ^ 2
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
      _ ≤ 4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ := by
          have hc : (0 : ℝ) ≤ 4096 * B ^ 2 :=
            mul_nonneg (by norm_num : (0 : ℝ) ≤ 4096) (sq_nonneg B)
          exact mul_le_mul (mul_le_mul hchoose hRd (sq_nonneg _) (by norm_num)) hG
            (sq_nonneg _) hc
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1))
    (f := fun b => (((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))))
  have hcard : (((Finset.range (j + 1)).card : ℕ) : ℝ) ≤ 7 := by
    rw [Finset.card_range]
    exact_mod_cast (by omega : j + 1 ≤ 7)
  have hsum2 : (∑ b ∈ Finset.range (j + 1),
        ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2))
      ≤ 7 * (4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) := by
    calc (∑ b ∈ Finset.range (j + 1),
          ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
              * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2))
        ≤ ∑ _b ∈ Finset.range (j + 1),
            (4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) :=
          Finset.sum_le_sum hper
      _ = ((j + 1 : ℕ) : ℝ) * (4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 7 * (4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) := by
          have hc : (0 : ℝ) ≤ 4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ :=
            mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4096) (sq_nonneg B)) hHk
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : j + 1 ≤ 7)) hc
  refine hcs.trans ?_
  calc (((Finset.range (j + 1)).card : ℕ) : ℝ)
          * ∑ b ∈ Finset.range (j + 1),
              ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
                * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2)
      ≤ 7 * (7 * (4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ)) :=
        mul_le_mul hcard hsum2 (Finset.sum_nonneg fun b _ => sq_nonneg _) (by norm_num)
    _ = 200704 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ := by ring

/-- **Multiplication by a bounded radial `C^6` factor is bounded on the `ℋ⁶`-integrand.** -/
theorem radialMaj6 (α B : ℝ) (X : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (hB : 0 ≤ B) (hX : ContDiffOn ℝ 6 X (Set.Ioi 0))
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hbnd : ∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 0 < z → |Work.Elliptic.DzdIter j X z| ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Spaces.HkIntegrand α 6 (fun z θ => X z * f z θ) z θ
        ≤ K * Work.Spaces.HkIntegrand α 6 f z θ := by
  refine ⟨20000000 * B ^ 2 + 1, by nlinarith [sq_nonneg B], ?_⟩
  intro z hz θ hθ
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · rw [← hz0, HkIntegrand_zero, HkIntegrand_zero, mul_zero]
  · have hHk : 0 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
      Work.Spaces.HkIntegrand_nonneg α 6 f z θ
    have hR : ∀ b : ℕ, b ≤ 6 → |Work.Elliptic.DzdIter b X z| ≤ B :=
      fun b hb => hbnd b hb z hzpos
    conv_lhs => rw [Work.Spaces.HkIntegrand]
    have hA : (∑ i ∈ Finset.range (6 + 1), (Work.Spaces.DzIter i
          (fun z θ => X z * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ 7 * (200704 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) := by
      calc (∑ i ∈ Finset.range (6 + 1), (Work.Spaces.DzIter i
            (fun z θ => X z * f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ ∑ _i ∈ Finset.range (6 + 1),
              (200704 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) :=
            Finset.sum_le_sum fun i hi =>
              zslot6 hB hX hf hzpos hθ.1 hθ.2 hR i
                (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
        _ = 7 * (200704 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            norm_num
    have hB' : (∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
          (if 1 ≤ i ∧ i + j ≤ 6 then
            (Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ 49 * (200704 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) := by
      calc (∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
            (if 1 ≤ i ∧ i + j ≤ 6 then
              (Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ∑ _i ∈ Finset.range (6 + 1), ∑ _j ∈ Finset.range (6 + 1),
              (200704 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
            by_cases hc : 1 ≤ i ∧ i + j ≤ 6
            · rw [if_pos hc]
              exact mslot6 hB hX hf hzpos hθ.1 hθ.2 hR i j hc.1 hc.2
            · rw [if_neg hc]
              exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 200704) (sq_nonneg B)) hHk
        _ = 49 * (200704 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    linarith [hA, hB', hHk, mul_nonneg (sq_nonneg B) hHk]

end

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L6Aux.LinMem6Acf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkMem HkSq HkNorm HkIntegrand Dz Dth mixed)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## §4 The nonlocal summand `Acoef α · Mf f` -/


/-- Lowering the order of a `C^n`-statement on the open half-line. -/
theorem linMem_le_of_le {B : ℝ → ℝ} {n m : ℕ}
    (h : ContDiffOn ℝ n B (Set.Ioi (0 : ℝ))) (hmn : m ≤ n) :
    ContDiffOn ℝ m B (Set.Ioi (0 : ℝ)) :=
  h.of_le (by exact_mod_cast hmn)

/-- `gamCoef α = Γ(θ)/c(α)` is `C^n` on the open angular interval, for every `n`. -/
theorem contDiffOn_gamCoef (α : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (gamCoef α) (Set.Ioo (0 : ℝ) (π / 2)) := by
  have hbase : ContDiffOn ℝ ⊤ (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    (Real.contDiff_sin.contDiffOn).mul ((Real.contDiff_cos.contDiffOn).pow 2)
  have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), Real.sin θ * Real.cos θ ^ 2 ≠ 0 := by
    intro θ hθ
    have h1 : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have h2 : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    positivity
  have hgam : ContDiffOn ℝ ⊤ (fun θ : ℝ => Work.Spaces.Gam α θ)
      (Set.Ioo (0 : ℝ) (π / 2)) := hbase.rpow_const_of_ne hne
  have hgc : ContDiffOn ℝ ⊤ (gamCoef α) (Set.Ioo (0 : ℝ) (π / 2)) := by
    refine (hgam.div_const (Work.Spaces.c α)).congr (fun θ _ => ?_)
    rw [gamCoef]
  exact hgc.of_le le_top

/-- Joint `C^n`-smoothness of a separated product `(z,θ) ↦ gamCoef α θ · B z`. -/
theorem linMem_sep_mul {n : ℕ} {B : ℝ → ℝ} {α : ℝ}
    (hB : ContDiffOn ℝ n B (Set.Ioi (0 : ℝ))) :
    ContDiffOn ℝ n (Function.uncurry (fun z θ => gamCoef α θ * B z))
      Work.FTS.EllipticEst.Q0 := by
  have hθ : ContDiffOn ℝ n (fun p : ℝ × ℝ => gamCoef α p.2) Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_gamCoef α n).comp contDiffOn_snd
      (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).2)
  have hz : ContDiffOn ℝ n (fun p : ℝ × ℝ => B p.1) Work.FTS.EllipticEst.Q0 :=
    hB.comp contDiffOn_fst (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hfun : Function.uncurry (fun z θ => gamCoef α θ * B z)
      = fun p : ℝ × ℝ => gamCoef α p.2 * B p.1 := rfl
  rw [hfun]
  exact hθ.mul hz

/-- The radial factor `acoef` is `C^n` on the open half-line. -/
theorem linMem_acoef (n : ℕ) :
    ContDiffOn ℝ n acoef (Set.Ioi (0 : ℝ)) := by
  refine (Work.FTS.StrongPersist.L3Aux.contDiffOn_two_z_div.mono ?_).of_le le_top
  intro z hz
  simp only [Set.mem_Ioi] at hz ⊢
  linarith


/-- `C⁶`-smoothness of `L₁₂ f` on the open half-line, from `ℋ⁷`-honesty of `f`. -/
theorem contDiffOn6_L12_of {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem7 : Work.Spaces.HkMem α 7 f) :
    ContDiffOn ℝ 6 (fun z => Work.Construction.L12 f z) (Set.Ioi (0 : ℝ)) := by
  have h := (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk α 7 f hsm hmem7
    (by norm_num)).1
  rw [Work.FTS.H2.constructionL12_eq_ellipticL12 f]
  exact h

/-- **`C⁶`-smoothness of the nonlocal summand on the open quadrant**, from `C⁶`-smoothness of
`L₁₂ f` on the open half-line. -/
theorem contDiffOn6_Acf {α : ℝ} {f : ℝ → ℝ → ℝ}
    (h12 : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 f z) (Set.Ioi (0 : ℝ))) :
    ContDiffOn ℝ 6 (Function.uncurry (fun z θ => Acoef α z θ * Mf f z θ))
      Work.FTS.EllipticEst.Q0 := by
  have hgz : ContDiffOn ℝ 6
      (Function.uncurry (fun z θ => gamCoef α θ * Work.Construction.L12 f z))
      Work.FTS.EllipticEst.Q0 := linMem_sep_mul h12
  have h1 : ContDiffOn ℝ 6 (Function.uncurry
      (fun z θ => acoef z * (gamCoef α θ * Work.Construction.L12 f z)))
      Work.FTS.EllipticEst.Q0 :=
    linMem_zmul_joint (n := 6) (linMem_acoef 6) hgz
  refine h1.congr (fun p hp => ?_)
  rcases p with ⟨z, θ⟩
  show Acoef α z θ * Mf f z θ = acoef z * (gamCoef α θ * Work.Construction.L12 f z)
  rw [Acoef_eq_mul]
  have hMf : Mf f z θ = Work.Construction.L12 f z := rfl
  rw [hMf]
  ring

/-- **The nonlocal summand is in `ℋ⁶`.**  The multiplier step (`zmul_finite6`, with
`φ = acoef` and `g = gamCoef α · L₁₂ f`) reduces the `ℋ⁶`-integrand to that of `g`, which the
separation lemma factorises into the angular majorant `Mth6 α` and the radial slot sum of
`L₁₂ f`; both factors are integrable (`Mth6_integrable`, `hslot`).

The hypothesis `hsep` is the level-six separation lemma for `k = 6`
(`L6Aux.HkIntegrandSepLeGen`), stated in the `Mth6`/`SlotSum` vocabulary. -/
theorem Acf_mem6_of {α : ℝ} {f : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    {K C₁ : ℝ} (hK : 0 ≤ K)
    (hzb : ∀ b ≤ 6, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] acoef z| ≤ K)
    (hslot : MeasureTheory.IntegrableOn (SlotSum (fun z => Work.Construction.L12 f z))
        Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, SlotSum (fun z => Work.Construction.L12 f z) z)
        ≤ C₁ * Work.Spaces.HkSq α 6 f)
    (hsep : ∀ {z θ : ℝ}, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.HkIntegrand α 6
          (fun z' θ' => gamCoef α θ' * Work.Construction.L12 f z') z θ
        ≤ Mth6 α θ * SlotSum (fun z => Work.Construction.L12 f z) z)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem7 : Work.Spaces.HkMem α 7 f)
    (h0 : Work.Construction.L12 f 0 = 0) :
    Work.Spaces.HkMem α 6 (fun z θ => Acoef α z θ * Mf f z θ) := by
  have hmem6 : Work.Spaces.HkMem α 6 f :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hsm hmem7
  have h12 : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 f z) (Set.Ioi (0 : ℝ)) :=
    contDiffOn6_L12_of hsm hmem7
  set g : ℝ → ℝ → ℝ := fun z θ => gamCoef α θ * Work.Construction.L12 f z with hgdef
  have hgz : ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0 := by
    rw [hgdef]
    exact linMem_sep_mul h12
  have hgsm : ∀ (i : ℕ), i ≤ 6 → ∀ θ : ℝ,
      ContDiffOn ℝ i (fun z => g z θ) (Set.Ioi (0 : ℝ)) := by
    intro i hi θ
    rw [hgdef]
    exact (contDiffOn_const (c := gamCoef α θ)).mul (linMem_le_of_le (n := 6) (m := i) h12 hi)
  have hgθsm : ∀ (j i : ℕ), 1 ≤ i → i + j ≤ 6 → ∀ θ : ℝ,
      ContDiffOn ℝ j (fun z => Work.Spaces.DthIter i g z θ) (Set.Ioi (0 : ℝ)) := by
    intro j i hi hij θ
    have hdec : (fun z => Work.Spaces.DthIter i g z θ)
        = fun z => Work.Spaces.dthU^[i] (gamCoef α) θ * Work.Construction.L12 f z := by
      funext z
      rw [hgdef]
      exact Work.Spaces.DthIter_decomp i (gamCoef α) (fun z => Work.Construction.L12 f z) z θ
    rw [hdec]
    exact (contDiffOn_const (c := Work.Spaces.dthU^[i] (gamCoef α) θ)).mul
      (linMem_le_of_le (n := 6) (m := j) h12 (by omega))
  have hZnn : 0 ≤ Work.FTS.StrongPersist.L3Aux.zmulConst 6 * (1 + K) ^ 2 :=
    mul_nonneg (Work.FTS.StrongPersist.L3Aux.zmulConst_pos 6).le (sq_nonneg _)
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (fun z θ => acoef z * g z θ) z θ
        ≤ (Work.FTS.StrongPersist.L3Aux.zmulConst 6 * (1 + K) ^ 2)
            * (Mth6 α θ * SlotSum (fun z => Work.Construction.L12 f z) z) := by
    intro z hz θ hθ
    have h1 := zmul_finite6 α acoef g hK hzb (fun b _ => linMem_acoef b) hgsm hgθsm z hz θ hθ
    have h2 : Work.Spaces.HkIntegrand α 6 g z θ
        ≤ Mth6 α θ * SlotSum (fun z => Work.Construction.L12 f z) z := by
      rw [hgdef]
      exact hsep hθ
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hZnn)
  have hAcf : (fun z θ => Acoef α z θ * Mf f z θ) = fun z θ => acoef z * g z θ := by
    funext z θ
    rw [hgdef, Acoef_eq_mul]
    have hMf : Mf f z θ = Work.Construction.L12 f z := rfl
    rw [hMf]
    ring
  rw [hAcf]
  refine Work.FTS.LocData.HkMem_of_majorant α 6
    (f := fun z θ => acoef z * g z θ)
    (M := fun z θ => (Work.FTS.StrongPersist.L3Aux.zmulConst 6 * (1 + K) ^ 2)
      * (Mth6 α θ * SlotSum (fun z => Work.Construction.L12 f z) z)) ?_ ?_ ?_ ?_
  · exact Work.FTS.EllipticEst.Cores.DiagEstEllT.continuousOn_HkIntegrand_of_contDiffOn
      (linMem_zmul_joint (n := 6) (linMem_acoef 6) hgz) α
  · intro z hz
    exact (((Mth6_integrable hα hα1).mul_const
      (SlotSum (fun z => Work.Construction.L12 f z) z)).const_mul _)
  · have h1 : (fun z => ∫ θ in Work.Spaces.Iθ,
          (Work.FTS.StrongPersist.L3Aux.zmulConst 6 * (1 + K) ^ 2)
            * (Mth6 α θ * SlotSum (fun z => Work.Construction.L12 f z) z))
        = fun z => (Work.FTS.StrongPersist.L3Aux.zmulConst 6 * (1 + K) ^ 2)
            * ((∫ θ in Work.Spaces.Iθ, Mth6 α θ)
              * SlotSum (fun z => Work.Construction.L12 f z) z) := by
      funext z
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const]
    rw [h1]
    exact (hslot.1.const_mul (∫ θ in Work.Spaces.Iθ, Mth6 α θ)).const_mul _
  · exact hpt


end Work.FTS.StrongPersist
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L6Aux.LinMem6LocOp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkMem HkSq HkNorm HkIntegrand Dz Dth mixed)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## §3 The local summand `locOp = -(𝓛 f) + Transport f`

`locOp` is a first-order operator with smooth coefficients; its `ℋ⁶`-integrand is dominated by
the `ℋ⁷`-integrand of `f`. -/

private theorem smoothOpen_DzCoeff {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => -(2 * f z θ / (1 + z))) := by
  have h2 : (fun z θ => -(2 * f z θ / (1 + z)))
      = fun z θ => (fun z : ℝ => -(2 / (1 + z))) z * f z θ := by
    funext z θ
    ring
  rw [h2]
  exact linMem_mul (linMem_radial linMem_two_div_smooth.neg) hf

private theorem smoothOpen_L {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Coercivity.L f) := by
  have hL : Work.Coercivity.L f
      = fun z θ => (f z θ + Work.Spaces.Dz f z θ) + (-(2 * f z θ / (1 + z))) := by
    funext z θ
    simp only [Work.Coercivity.L, Work.Spaces.Dz, Work.Spaces.pz]
    ring
  rw [hL]
  exact Work.FTS.EllipticEst.smoothOpen_add
    (Work.FTS.EllipticEst.smoothOpen_add hf (hf.DzIter 1)) (smoothOpen_DzCoeff hf)

private theorem smoothOpen_Transport {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Coercivity.Transport f) := by
  have hT : Work.Coercivity.Transport f
      = fun z θ => (fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth f z θ := by
    funext z θ
    simp only [Work.Coercivity.Transport, Work.Spaces.Dth, Work.Spaces.pth]
    ring
  rw [hT]
  exact linMem_mul
    (linMem_radial (contDiffOn_iff_forall_nat_le.mpr
      (fun m _ => Work.FTS.FinalClock.contDiffOn_phiThree m))) hf.Dth

/-- `locOp f` is `C^∞` on the open quadrant whenever `f` is. -/
theorem locOp_smoothOpen {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (locOp f) := by
  have h : locOp f
      = fun z θ => -(Work.Coercivity.L f z θ) + Work.Coercivity.Transport f z θ := rfl
  rw [h]
  exact Work.FTS.EllipticEst.smoothOpen_add
    (linMem_neg (smoothOpen_L hf)) (smoothOpen_Transport hf)

/-- The `ℋ⁶`-integrand of `locOp f` is dominated by `100(1+C_{zmul}(1+K)²)` times the
`ℋ⁷`-integrand of `f`. -/
theorem locOp_integrand_le {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α) {K : ℝ} (hK : 0 ≤ K)
    (hzb : ∀ b ≤ 6, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] (fun z : ℝ => 3 / (1 + z)) z| ≤ K)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (locOp f) z θ
        ≤ (100 * (1 + Work.FTS.StrongPersist.L3Aux.zmulConst 6 * (1 + K) ^ 2))
            * Work.Spaces.HkIntegrand α 7 f z θ := by
  intro z hz θ hθ
  set Z : ℝ := Work.FTS.StrongPersist.L3Aux.zmulConst 6 * (1 + K) ^ 2 with hZdef
  have hZnn : 0 ≤ Z := by
    rw [hZdef]
    exact mul_nonneg (Work.FTS.StrongPersist.L3Aux.zmulConst_pos 6).le (sq_nonneg _)
  have hphism : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 3 / (1 + z))
      (Set.Ioi (-1)) :=
    contDiffOn_iff_forall_nat_le.mpr (fun m _ => Work.FTS.FinalClock.contDiffOn_phiThree m)
  have hAnn : 0 ≤ Work.Spaces.HkIntegrand α 7 f z θ := Work.Spaces.HkIntegrand_nonneg α 7 f z θ
  -- the three individual slot bounds
  have hf6 : Work.Spaces.HkIntegrand α 6 f z θ ≤ Work.Spaces.HkIntegrand α 7 f z θ :=
    Work.FTS.StrongPersist.HkIntegrand_le_of_le α (by norm_num) f z θ
  have hDz : Work.Spaces.HkIntegrand α 6 (Work.Spaces.Dz f) z θ
      ≤ Work.Spaces.HkIntegrand α 7 f z θ := by
    have h := Work.FTS.StrongPersist.L3Aux.HkIntegrand_mixed_shift α hα 6 0 1 hf z hz θ hθ
    simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
      Nat.reduceAdd] using h
  have hDth : Work.Spaces.HkIntegrand α 6 (Work.Spaces.Dth f) z θ
      ≤ Work.Spaces.HkIntegrand α 7 f z θ := by
    have h := Work.FTS.StrongPersist.L3Aux.HkIntegrand_mixed_shift α hα 6 1 0 hf z hz θ hθ
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero,
      Nat.reduceAdd] using h
  have hzmu : Work.Spaces.HkIntegrand α 6
        (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * f z θ) z θ
      ≤ Z * Work.Spaces.HkIntegrand α 6 f z θ := by
    rw [hZdef]
    exact Work.FTS.StrongPersist.L3Aux.zmul_quad α 6 (fun z : ℝ => 3 / (1 + z)) f hK hzb
      hphism hf z hz θ hθ
  have hzmd : Work.Spaces.HkIntegrand α 6
        (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth f z θ) z θ
      ≤ Z * Work.Spaces.HkIntegrand α 6 (Work.Spaces.Dth f) z θ := by
    rw [hZdef]
    exact Work.FTS.StrongPersist.L3Aux.zmul_quad α 6 (fun z : ℝ => 3 / (1 + z))
      (Work.Spaces.Dth f) hK hzb hphism hf.Dth z hz θ hθ
  -- `f + D_z f`
  have hsum1 : Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ + Work.Spaces.Dz f z θ) z θ
      ≤ 4 * Work.Spaces.HkIntegrand α 7 f z θ := by
    have h := Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α 6
      (f := f) (g := Work.Spaces.Dz f) (hf.forall 6) ((hf.DzIter 1).forall 6) z hz θ hθ
    linarith
  -- `-(2f/(1+z))`
  have hmid : Work.Spaces.HkIntegrand α 6 (fun z θ => -(2 * f z θ / (1 + z))) z θ
      ≤ (2 / 3) ^ 2 * Z * Work.Spaces.HkIntegrand α 7 f z θ := by
    have hfun : (fun z θ => -(2 * f z θ / (1 + z)))
        = fun z θ => (-(2 / 3)) * ((fun z : ℝ => 3 / (1 + z)) z * f z θ) := by
      funext z θ
      rw [linMem_two_mul_div_eq (f z θ) (1 + z)]
      ring
    rw [hfun, Work.FTS.LocData.hkIntegrand_const_mul]
    have h2 : (-(2 / 3)) ^ 2 * Work.Spaces.HkIntegrand α 6
          (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * f z θ) z θ
        ≤ (-(2 / 3)) ^ 2 * (Z * Work.Spaces.HkIntegrand α 7 f z θ) :=
      mul_le_mul_of_nonneg_left (le_trans hzmu (mul_le_mul_of_nonneg_left hf6 hZnn)) (sq_nonneg _)
    calc (-(2 / 3)) ^ 2 * Work.Spaces.HkIntegrand α 6
          (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * f z θ) z θ
        ≤ (-(2 / 3)) ^ 2 * (Z * Work.Spaces.HkIntegrand α 7 f z θ) := h2
      _ = (2 / 3) ^ 2 * Z * Work.Spaces.HkIntegrand α 7 f z θ := by ring
  -- `Transport f`
  have htrans : Work.Spaces.HkIntegrand α 6 (Work.Coercivity.Transport f) z θ
      ≤ Z * Work.Spaces.HkIntegrand α 7 f z θ := by
    have hfun : Work.Coercivity.Transport f
        = fun z θ => (fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth f z θ := by
      funext z θ
      simp only [Work.Coercivity.Transport, Work.Spaces.Dth, Work.Spaces.pth]
      ring
    rw [hfun]
    nlinarith [hzmd, hDth, hZnn, Work.Spaces.HkIntegrand_nonneg α 6 (Work.Spaces.Dth f) z θ, hAnn]
  -- `𝓛 f`
  have hLf : Work.Spaces.HkIntegrand α 6 (Work.Coercivity.L f) z θ
      ≤ 2 * (4 * Work.Spaces.HkIntegrand α 7 f z θ)
        + 2 * ((2 / 3) ^ 2 * Z * Work.Spaces.HkIntegrand α 7 f z θ) := by
    have hL : Work.Coercivity.L f
        = fun z θ => (f z θ + Work.Spaces.Dz f z θ) + (-(2 * f z θ / (1 + z))) := by
      funext z θ
      simp only [Work.Coercivity.L, Work.Spaces.Dz, Work.Spaces.pz]
      ring
    rw [hL]
    have h := Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α 6
      (f := fun z θ => f z θ + Work.Spaces.Dz f z θ)
      (g := fun z θ => -(2 * f z θ / (1 + z))) ((hf.forall 6).add ((hf.DzIter 1).forall 6)) ?_ z hz θ hθ
    · linarith
    · have h2 : (fun z θ => -(2 * f z θ / (1 + z)))
          = fun z θ => (fun z : ℝ => -(2 / (1 + z))) z * f z θ := by
        funext z θ; ring
      rw [h2]
      refine linMem_zmul_joint (n := 6) ?_ (hf.forall 6)
      exact ((linMem_two_div 6).neg).mono (fun z hz' => by
        simp only [Set.mem_Ioi] at hz' ⊢
        linarith)
  -- `locOp`
  change Work.Spaces.HkIntegrand α 6 (fun z θ => -(Work.Coercivity.L f z θ)
      + Work.Coercivity.Transport f z θ) z θ ≤ _
  have h := Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α 6
    (f := fun z θ => -(Work.Coercivity.L f z θ)) (g := Work.Coercivity.Transport f)
    ((smoothOpen_L hf).forall 6).neg ((smoothOpen_Transport hf).forall 6) z hz θ hθ
  have hneg : Work.Spaces.HkIntegrand α 6 (fun z θ => -(Work.Coercivity.L f z θ)) z θ
      = Work.Spaces.HkIntegrand α 6 (Work.Coercivity.L f) z θ :=
    Work.FTS.LocData.HkIntegrand_neg α 6 (Work.Coercivity.L f) z θ
  rw [hneg] at h
  nlinarith [h, hLf, htrans, hZnn, hAnn]

/-- **The local summand is in `ℋ⁶`.** -/
theorem LocOp_mem6_of {α : ℝ} {f : Fn} (hα : 0 < α) {K : ℝ} (hK : 0 ≤ K)
    (hzb : ∀ b ≤ 6, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] (fun z : ℝ => 3 / (1 + z)) z| ≤ K)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 7 f) :
    Work.Spaces.HkMem α 6 (locOp f) := by
  refine Work.FTS.LocData.HkMem_of_majorant α 6 (f := locOp f)
    (M := fun z θ => (100 * (1 + Work.FTS.StrongPersist.L3Aux.zmulConst 6 * (1 + K) ^ 2))
      * Work.Spaces.HkIntegrand α 7 f z θ) ?_ ?_ ?_ ?_
  · exact Work.FTS.EllipticEst.Cores.DiagEstEllT.continuousOn_HkIntegrand_of_contDiffOn
      ((locOp_smoothOpen hsm).forall 6) α
  · intro z hz
    exact (hmem.1 z hz).const_mul _
  · have h1 : (fun z => ∫ θ in Work.Spaces.Iθ,
          (100 * (1 + Work.FTS.StrongPersist.L3Aux.zmulConst 6 * (1 + K) ^ 2))
            * Work.Spaces.HkIntegrand α 7 f z θ)
        = fun z => (100 * (1 + Work.FTS.StrongPersist.L3Aux.zmulConst 6 * (1 + K) ^ 2))
            * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 7 f z θ := by
      funext z
      rw [MeasureTheory.integral_const_mul]
    rw [h1]
    exact hmem.2.const_mul _
  · intro z hz θ hθ
    exact locOp_integrand_le hα hK hzb hsm z hz θ hθ



end Work.FTS.StrongPersist
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundE =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The level-6 `T2` slot: the exceptional (`f·D_z g`) term

The top term of the Leibniz expansion of `D_z^bD_θ^a (f·D_z g)`, in which all derivatives fall on
`g`.  For `a + b ≤ 5` it is bounded pointwise (the `g`-block stays inside the level-6 slot); for
`a + b = 6` the second `g`-factor is at level 7, where only the *signed* radial integration by
parts `fluxSix` applies.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixAux

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z canonW_mono)
open Work.FTS.StrongPersist.N6Trans.T1SixAux (SlotW6 slotW6_z slotW6_mixed)

set_option autoImplicit false
set_option maxHeartbeats 3200000


end Work.FTS.StrongPersist.N6Trans.SixAux
end
end

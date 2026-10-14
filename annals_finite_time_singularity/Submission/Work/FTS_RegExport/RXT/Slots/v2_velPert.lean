import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.StrongEps.SupPort.classC_sup_le
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_RegExport.RXT.Slots.v2_paramC2
import Submission.Work.FTS_RegExport.RXT.Slots.v2_theta_sup_uniform
import Submission.Work.FTS_RegExport.RXT.SysAux.bR_decomp
import Submission.Work.FTS_RegExport.RXT.st1_stdata
import Submission.Work.FTS_RegExport.THL.Defs
import Submission.Work.FTS_RegExport.THL.angular_L2_noTrace
import Submission.Work.R1G.DecayInZ_gA

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Auxiliary lemmas for `velPert`

`velPert` controls the three perturbation slots `ℛ(Φ̃)`, `𝒱(Φ̃)`, `𝒰(Φ̃)/sin 2θ` of the
residual `Φ̃ = PhiTil (g(τ)) (E (g(τ)))`: by `EllPkgGo` the three slots of the class-`C`
approximants of `LimApprox` are in `ℋ⁴` with `ℋ⁴`-norm at most `Ce · C₀α²`, so the trace-free
`ℋ⁴ → L^∞` trade-off controls them pointwise; the limit is taken with the order-`3` jet
convergence of the residual (`EllLimOK3` for the `E`-part and dominated convergence for the
singular part `Θ = (1/(4α)) sin 2θ L₁₂`). -/

/-- `𝔽K(F) = 3 F_*(F)`: the angular moment of `Work.Construction` is three times the
`sin θ cos²θ`-moment of `Work.Elliptic`. -/
theorem velPert_FK_eq (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Construction.FK F z = 3 * Work.Elliptic.Fstar F z := by
  rw [Work.Construction.FK, Work.Elliptic.Fstar]
  rw [← MeasureTheory.integral_const_mul]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by
    simp only [Work.Spaces.K, Work.Elliptic.sinCos2]; ring)

theorem velPert_continuousOn_K : ContinuousOn Work.Spaces.K Work.Spaces.Iθ :=
  ((continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2)).continuousOn

/-- `Θ α F` is `C³` on the open quadrant as soon as `L₁₂(F)` is. -/
theorem velPert_contDiffOn_Theta {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hL12 : ContDiffOn ℝ 3 (Work.Construction.L12 F) (Set.Ioi 0)) :
    ContDiffOn ℝ 3 (Function.uncurry (Work.Construction.Theta α F)) Work.FTS.EllipticEst.Q0 := by
  have h1 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => (1 / (4 * α)) * Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    contDiffOn_const.mul (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  have h2 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Work.Construction.L12 F p.1)
      Work.FTS.EllipticEst.Q0 := contDiffOn_slice_fst hL12
  refine (h1.mul h2).congr fun p _ => ?_
  simp only [Function.uncurry, Pi.mul_apply, Work.Construction.Theta, Work.Construction.s2]

/-- Mixed derivatives of order `≤ 3` split over a difference of `C³`-functions. -/
theorem velPert_mixed_sub_three {f g : ℝ → ℝ → ℝ} {b a : ℕ} (hba : a + b ≤ 3)
    (hf : ContDiffOn ℝ 3 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ 3 (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Spaces.mixed b a (fun z θ => f z θ - g z θ) z θ
      = Work.Spaces.mixed b a f z θ - Work.Spaces.mixed b a g z θ := by
  have hneg : ContDiffOn ℝ 3 (Function.uncurry (fun z θ => -g z θ))
      Work.FTS.EllipticEst.Q0 := by
    have hfun : Function.uncurry (fun z θ => -g z θ)
        = fun p : ℝ × ℝ => -(Function.uncurry g p) := by
      funext p; rcases p with ⟨z', θ'⟩; rfl
    rw [hfun]; exact hg.neg
  have hfun2 : (fun z θ => f z θ - g z θ) = f + (fun z θ => -g z θ) := by
    funext z θ; simp only [Pi.add_apply]; ring
  have hsum := Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn (n := 3)
    Work.FTS.EllipticEst.isOpen_Q0 hf hneg a b hba (z, θ)
    (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩)
  rw [show (z, θ).1 = z from rfl, show (z, θ).2 = θ from rfl] at hsum
  rw [hfun2, hsum, Work.FTS.StrongEps.mixed_neg]
  ring

/-- The trace-free `ℋ⁴ → L^∞` trade-off with the radial vanishing: there is a universal constant
`C` with `|D_z^jD_θ^if(z,θ)| ≤ C · M · min z 1` for every `C⁴`-datum on the open quadrant which
is honestly in `ℋ⁴` and whose `ℋ⁴`-norm is at most `M`. -/
theorem velPert_hkMem_bound {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℝ → ℝ → ℝ) (M : ℝ),
      ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 → Work.Spaces.HkMem α 4 f →
      Work.Spaces.HkNorm α 4 f ≤ M →
      ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i f z θ| ≤ C * M * min z 1 := by
  obtain ⟨C, hC0, hC⟩ := v2_hkMem_pointwise_min hα hα1
  refine ⟨C, hC0, ?_⟩
  intro f M hsm hmem hMn j i hji z θ hz hθ hθ2
  have h1 := hC f hsm hmem j i (by omega) z θ hz hθ hθ2
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hMn
  have hm0 : 0 ≤ min z 1 := le_min hz.le zero_le_one
  calc |Work.Spaces.mixed j i f z θ| ≤ C * min z 1 * Work.Spaces.HkNorm α 4 f := h1
    _ ≤ C * min z 1 * M := mul_le_mul_of_nonneg_left hMn (mul_nonneg hC0 hm0)
    _ = C * M * min z 1 := by ring

/-- The generic liminf step: a uniform `min z 1`-bound for a sequence of slots passes to the
pointwise limit of the slots. -/
theorem velPert_limit_bound {A : ℕ → ℝ → ℝ → ℝ} {Alim : ℝ → ℝ → ℝ} {M : ℝ}
    (hbound : ∀ n j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (A n) z θ| ≤ M * min z 1)
    (hconv : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (A n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i Alim z θ))) :
    ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i Alim z θ| ≤ M * min z 1 := by
  intro j i hji z θ hz hθ hθ2
  exact le_of_tendsto' ((hconv j i hji z θ hz hθ hθ2).abs)
    (fun n => hbound n j i hji z θ hz hθ hθ2)

theorem v2_velPert {α Ce C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    {g : Work.FTS.Galerkin.Fam} (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∀ S > 0, ∃ M : ℝ, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      ∀ Q ∈ ({(Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ)))),
          Work.Construction.Vop
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))),
          fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))) z θ
            / Real.sin (2 * θ)} : Set (ℝ → ℝ → ℝ)),
        ∀ j i : ℕ, j + i ≤ 2 → |Work.Spaces.mixed j i Q z θ| ≤ M * min z 1 := by
  intro S hS
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- the class-`C` approximants of `LimApprox`
  obtain ⟨gn, B, L, hApprox, _hLip, hJet, _hμ⟩ := hOK.2 S hS
  -- the `ℋ⁴ → L^∞` trade-offs
  obtain ⟨CA1, hCA10, hA1⟩ := Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved hαG hαG1
  obtain ⟨C4, hC40, hC4⟩ := velPert_hkMem_bound hαG hαG1
  refine ⟨C4 * (max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2)), ?_⟩
  intro τ hτ z θ hz hθ hθ2 Q hQ j i hji
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
  -- the `E`-jets of the limit slice
  obtain ⟨_hBsl, hE3lim, hEconv⟩ := hEL3 (fun n => slice (gn n) τ) (slice g τ) B
    (fun n => (hApprox n τ hτ).1) (fun n => (hApprox n τ hτ).2.2) hF4
    (fun j i hji z' θ' hzθ => hJet τ hτ j i hji z' θ' hzθ)
  -- ## `𝔽K` and `L₁₂` of the limit slice
  have hFKlim : ContDiffOn ℝ 2 (Work.Construction.FK (slice g τ)) (Set.Ioi 0) := by
    have hF2 : ContDiffOn ℝ 2 (Function.uncurry (slice g τ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hF4.of_le (by norm_num)
    have hbase : ∀ (b : ℕ), b ≤ 2 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
        |Work.Spaces.mixed b 0 (slice g τ) z' θ'| ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) := by
      intro b hb z' θ' hz' hθ' hθ'2
      have h1 := hC4 (slice g τ) (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) hF4 hFmem hFnorm b 0 (by omega) z' θ'
        hz' hθ' hθ'2
      have h2 : C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) * min z' 1 ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left (min_le_right _ _)
          (mul_nonneg hC40 (mul_nonneg (le_max_right C₀ 0) (sq_nonneg (Work.FTS.Regularity.pExp α))))
      linarith [h1, h2]
    have hb : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
        |slice g τ z' θ'| ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) ∧
        |Work.Spaces.Dz (slice g τ) z' θ'| ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) ∧
        |Work.Spaces.DzIter 2 (slice g τ) z' θ'| ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) :=
      fun z' θ' hz' hθ' hθ'2 =>
        ⟨by simpa using hbase 0 (by norm_num) z' θ' hz' hθ' hθ'2,
         by simpa using hbase 1 (by norm_num) z' θ' hz' hθ' hθ'2,
         by simpa using hbase 2 (by norm_num) z' θ' hz' hθ' hθ'2⟩
    exact Work.FTS_RegExport.RXT.Slots.v2_paramC2 (φ := Work.Spaces.K)
      (C := C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2))
      velPert_continuousOn_K hF2 hb
  have hL12lim : ContDiffOn ℝ 3 (Work.Construction.L12 (slice g τ)) (Set.Ioi 0) :=
    contDiffOn_three_L12 hFKlim
  have hΘ3lim : ContDiffOn ℝ 3
      (Function.uncurry (Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice g τ)))
      Work.FTS.EllipticEst.Q0 :=
    velPert_contDiffOn_Theta (α := Work.FTS.Regularity.pExp α) hL12lim
  have hElim3 : ContDiffOn ℝ 3 (Function.uncurry (fun z θ => E (slice g τ) z θ))
      Work.FTS.EllipticEst.Q0 := hE3lim
  -- ## `𝔽K`-jets of the approximants and the `Θ`-jets
  have hL12jets : ∀ j : ℕ, j ≤ 3 → ∀ z' : ℝ, 0 < z' →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.DzIter j
          (fun z _ => Work.Construction.L12 (slice (gn n) τ) z) z' 0) Filter.atTop
        (nhds (Work.Spaces.DzIter j
          (fun z _ => Work.Construction.L12 (slice g τ) z) z' 0)) := by
    intro j hj z' hz'
    refine Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto (C0 := CA1 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2))
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
        _ ≤ CA1 * (z'' ^ ((3 : ℝ) / 2) / (1 + z'') ^ 2) * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) :=
            mul_le_mul_of_nonneg_left h2 hA0
        _ = CA1 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) * (z'' ^ ((3 : ℝ) / 2) / (1 + z'') ^ 2) := by ring
    · intro b a hab z'' θ'' hz'' hθ'' hθ''2
      exact hJet τ hτ b a (by omega) z'' θ'' ⟨hz'', hθ'', hθ''2⟩
  have hΘconv : ∀ j i : ℕ, j + i ≤ 3 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
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
    refine velPert_contDiffOn_Theta (α := Work.FTS.Regularity.pExp α) ?_
    refine contDiffOn_three_L12 ?_
    have h1 : ContDiffOn ℝ 2 (fun z => 3 * Work.Elliptic.Fstar (slice (gn n) τ) z)
        (Set.Ioi 0) := contDiffOn_const.mul ((hApprox n τ hτ).1.fsm 2)
    refine h1.congr fun z' _ => ?_
    rw [velPert_FK_eq]
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
      exact velPert_mixed_sub_three (b := b) (a := a) hba (hΦ3 n) (hΘ3 n) hz' hθ' hθ'2
    have hlim : Work.Spaces.mixed b a (fun z θ =>
          Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ)) z θ) z' θ'
        = Work.Spaces.mixed b a (fun z θ => E (slice g τ) z θ) z' θ'
            - Work.Spaces.mixed b a (fun z θ =>
                Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice g τ) z θ)
                z' θ' :=
      velPert_mixed_sub_three (b := b) (a := a) hba hElim3 hΘ3lim hz' hθ' hθ'2
    rw [hfun, hlim]
    exact (hEconv b a (by omega) z' θ' ⟨hz', hθ', hθ'2⟩).sub
      (hΘconv b a (by omega) z' θ' hz' hθ' hθ'2)
  -- ## the slot jets converge
  have hslotconv := Work.FTS_RegExport.RXT.Slots.v2_SlotJetsTendsto (α := Work.FTS.Regularity.pExp α)
    (Ξ := fun n => fun z θ => Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
      (slice (gn n) τ) (E (slice (gn n) τ)) z θ)
    (Ξlim := fun z θ => Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
      (slice g τ) (E (slice g τ)) z θ) hΞ3 hΞ3lim hΞconv
  -- ## the final liminf, slotwise
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hQ
  rcases hQ with rfl | rfl | rfl
  · -- the `ℛ`-slot
    refine velPert_limit_bound (M := C4 * (max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2)))
      (A := fun n => fun z θ => Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
          (E (slice (gn n) τ))) z θ) ?_ ?_ j i hji z θ hz hθ hθ2
    · intro n j' i' hji' z' θ' hz' hθ' hθ'2
      obtain ⟨hCn, _⟩ := hApprox n τ hτ
      obtain ⟨hGo, _⟩ := hEll _ hCn
      have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ) :=
        Work.Spaces.HkNorm_nonneg _ _ _
      have hkey : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4
          (Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
              (E (slice (gn n) τ))))
          ≤ max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) := by
        refine le_trans hGo.R.2 ?_
        calc Ce * Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            ≤ max Ce 0 * Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ) :=
              mul_le_mul_of_nonneg_right (le_max_left Ce 0) hXn0
          _ ≤ max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) :=
              mul_le_mul_of_nonneg_left (hReg n).2.2.2 (le_max_right Ce 0)
      exact hC4 _ _ (hGo.R.1.1.of_le (by norm_num)) hGo.R.1.2 hkey j' i' hji'
        z' θ' hz' hθ' hθ'2
    · intro b a hba z' θ' hz' hθ' hθ'2
      exact (hslotconv b a hba z' θ' hz' hθ' hθ'2).1
  · -- the `𝒱`-slot
    refine velPert_limit_bound (M := C4 * (max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2)))
      (A := fun n => fun z θ => Work.Construction.Vop
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
          (E (slice (gn n) τ))) z θ) ?_ ?_ j i hji z θ hz hθ hθ2
    · intro n j' i' hji' z' θ' hz' hθ' hθ'2
      obtain ⟨hCn, _⟩ := hApprox n τ hτ
      obtain ⟨hGo, _⟩ := hEll _ hCn
      have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ) :=
        Work.Spaces.HkNorm_nonneg _ _ _
      have hkey : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4
          (Work.Construction.Vop
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
              (E (slice (gn n) τ))))
          ≤ max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) := by
        refine le_trans hGo.V.2 ?_
        calc Ce * Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            ≤ max Ce 0 * Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ) :=
              mul_le_mul_of_nonneg_right (le_max_left Ce 0) hXn0
          _ ≤ max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) :=
              mul_le_mul_of_nonneg_left (hReg n).2.2.2 (le_max_right Ce 0)
      exact hC4 _ _ (hGo.V.1.1.of_le (by norm_num)) hGo.V.1.2 hkey j' i' hji'
        z' θ' hz' hθ' hθ'2
    · intro b a hba z' θ' hz' hθ' hθ'2
      exact (hslotconv b a hba z' θ' hz' hθ' hθ'2).2.1
  · -- the `𝒰/sin 2θ`-slot
    refine velPert_limit_bound (M := C4 * (max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2)))
      (A := fun n => fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
          (E (slice (gn n) τ))) z θ / Real.sin (2 * θ)) ?_ ?_ j i hji z θ hz hθ hθ2
    · intro n j' i' hji' z' θ' hz' hθ' hθ'2
      obtain ⟨hCn, _⟩ := hApprox n τ hτ
      obtain ⟨hGo, _⟩ := hEll _ hCn
      have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ) :=
        Work.Spaces.HkNorm_nonneg _ _ _
      have hkey : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4
          (fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
              (E (slice (gn n) τ))) z θ / Real.sin (2 * θ))
          ≤ max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) := by
        refine le_trans hGo.U.2 ?_
        calc Ce * Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            ≤ max Ce 0 * Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ) :=
              mul_le_mul_of_nonneg_right (le_max_left Ce 0) hXn0
          _ ≤ max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) :=
              mul_le_mul_of_nonneg_left (hReg n).2.2.2 (le_max_right Ce 0)
      exact hC4 _ _ (hGo.U.1.1.of_le (by norm_num)) hGo.U.1.2 hkey j' i' hji'
        z' θ' hz' hθ' hθ'2
    · intro b a hba z' θ' hz' hθ' hθ'2
      exact (hslotconv b a hba z' θ' hz' hθ' hθ'2).2.2

end Work.FTS_RegExport.RXT

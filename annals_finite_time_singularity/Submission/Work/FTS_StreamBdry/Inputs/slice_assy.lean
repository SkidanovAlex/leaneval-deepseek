import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_StreamBdry.Inputs.slice_slots
import Submission.Work.FTS_RegExport.RXT.Sys.CoeffSmooth
import Submission.Work.FTS_FinalLeaves.psiCan_C3_proved

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.Inputs.slice_assy` — assembly of the `SlotBd` conjunct of `slice_inputs`

`slotBd_of_pieces` turns the order-`≤ 2` jet bounds of the residual slots (`residual_slot_jetsB`)
and of the singular part (`theta_part_jets`) into a `SlotBd` for `slice (ΦR a Φs E g) τ`; the
`-! ##` sections below then transfer it to `slice (PsiCan Φs E g) τ` (`SlotBd_of_eqOn`) and add the
`C³` and `SrcOK` conjuncts (`slice_inputs_of_pieces`).
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.Inputs

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Regularity (pExp)

set_option autoImplicit false

/-! ## `SlotBd` from the two jet bounds -/

/-- `SlotBd` of the slice of `ΦR` from the jet bounds of the residual slots and of the singular
part. -/
theorem slotBd_of_pieces {a Mv C : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ)
    (hSΨ1 : ContDiffOn ℝ 1 (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiT a Φs E g τ))
      Work.FTS.EllipticEst.Q0)
    (hSΘ1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Construction.Theta (pExp a)
      (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ)))
      Work.FTS.EllipticEst.Q0)
    (hSΨ3 : ContDiffOn ℝ 3 (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiT a Φs E g τ))
      Work.FTS.EllipticEst.Q0)
    (hSΘ3 : ContDiffOn ℝ 3 (Function.uncurry (Work.Construction.Theta (pExp a)
      (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ)))
      Work.FTS.EllipticEst.Q0)
    (hUres : ContDiffOn ℝ 2 (Function.uncurry (Ures a Φs E g τ)) Work.FTS.EllipticEst.Q0)
    (hUthS : ContDiffOn ℝ 2 (Function.uncurry (UthS a g τ)) Work.FTS.EllipticEst.Q0)
    (hVres : ContDiffOn ℝ 2 (Function.uncurry (Vres a Φs E g τ)) Work.FTS.EllipticEst.Q0)
    (hVthS : ContDiffOn ℝ 2 (Function.uncurry (VthS a g τ)) Work.FTS.EllipticEst.Q0)
    (hres : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i (Ures a Φs E g τ) z θ| ≤ Mv)
    (hresV : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i (Vres a Φs E g τ) z θ| ≤ Mv)
    (hth : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i (Uth a g τ) z θ| ≤ C)
    (hthV : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i (Vth a g τ) z θ| ≤ C) :
    Work.FTS.StreamBdryIface.SlotBd (pExp a)
      (slice (Work.FTS.RegExportIface.RXT.ΦR a Φs E g) τ) (Mv + C) := by
  have hQ0 : IsOpen Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.isOpen_Q0
  have hopen : IsOpen (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hUeq := eqOn_Uprime_split (a := a) (Φs := Φs) (E := E) (g := g) (τ := τ) hSΨ3 hSΘ3
  have hVeq := eqOn_Vop_split (a := a) (Φs := Φs) (E := E) (g := g) (τ := τ) hSΨ1 hSΘ1
  have hUthEq := eqOn_UthS_Uth (a := a) (g := g) (τ := τ) hτ
  have hVthEq := eqOn_VthS_Vth (a := a) (g := g) (τ := τ) hτ
  intro z θ hzθ
  obtain ⟨hz, hθ, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
  have hzI : (z, θ) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ) := ⟨hz, trivial⟩
  have keyU : ∀ j i : ℕ, j + i ≤ 2 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < π / 2 →
      |Work.Spaces.mixed j i (Work.FTS.StreamBdryIface.Uprime (pExp a)
        (slice (Work.FTS.RegExportIface.RXT.ΦR a Φs E g) τ)) z' θ'| ≤ Mv + C := by
    intro j i hji z' θ' hz' hθ' hθ2'
    have hzθ' : (z', θ') ∈ Work.FTS.EllipticEst.Q0 := ⟨hz', hθ', hθ2'⟩
    have h1 : Work.Spaces.mixed j i (Work.FTS.StreamBdryIface.Uprime (pExp a)
        (slice (Work.FTS.RegExportIface.RXT.ΦR a Φs E g) τ)) z' θ'
        = Work.Spaces.mixed j i (Ures a Φs E g τ + UthS a g τ) z' θ' :=
      Work.FTS_RegExport.RXT.Sys.mixed_congr_of_isOpen hQ0 hUeq j i z' θ' hzθ'
    have h2 := mixed_add_of (f := Ures a Φs E g τ) (h := UthS a g τ) hUres hUthS hji hzθ'
    have h3 : Work.Spaces.mixed j i (UthS a g τ) z' θ' = Work.Spaces.mixed j i (Uth a g τ) z' θ' :=
      Work.FTS_RegExport.RXT.Sys.mixed_congr_of_isOpen hopen hUthEq j i z' θ' ⟨hz', trivial⟩
    rw [h1, h2, h3]
    have h4 := hres j i hji z' θ' hz' hθ' hθ2'
    have h5 := hth j i hji z' θ' hz' hθ' hθ2'
    calc |Work.Spaces.mixed j i (Ures a Φs E g τ) z' θ'
            + Work.Spaces.mixed j i (Uth a g τ) z' θ'|
        ≤ |Work.Spaces.mixed j i (Ures a Φs E g τ) z' θ'|
            + |Work.Spaces.mixed j i (Uth a g τ) z' θ'| := abs_add_le _ _
      _ ≤ Mv + C := add_le_add h4 h5
  have keyV : ∀ j i : ℕ, j + i ≤ 2 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < π / 2 →
      |Work.Spaces.mixed j i (Work.Construction.Vop
        (slice (Work.FTS.RegExportIface.RXT.ΦR a Φs E g) τ)) z' θ'| ≤ Mv + C := by
    intro j i hji z' θ' hz' hθ' hθ2'
    have hzθ' : (z', θ') ∈ Work.FTS.EllipticEst.Q0 := ⟨hz', hθ', hθ2'⟩
    have h1 : Work.Spaces.mixed j i (Work.Construction.Vop
        (slice (Work.FTS.RegExportIface.RXT.ΦR a Φs E g) τ)) z' θ'
        = Work.Spaces.mixed j i (Vres a Φs E g τ + VthS a g τ) z' θ' :=
      Work.FTS_RegExport.RXT.Sys.mixed_congr_of_isOpen hQ0 hVeq j i z' θ' hzθ'
    have h2 := mixed_add_of (f := Vres a Φs E g τ) (h := VthS a g τ) hVres hVthS hji hzθ'
    have h3 : Work.Spaces.mixed j i (VthS a g τ) z' θ' = Work.Spaces.mixed j i (Vth a g τ) z' θ' :=
      Work.FTS_RegExport.RXT.Sys.mixed_congr_of_isOpen hopen hVthEq j i z' θ' ⟨hz', trivial⟩
    rw [h1, h2, h3]
    have h4 := hresV j i hji z' θ' hz' hθ' hθ2'
    have h5 := hthV j i hji z' θ' hz' hθ' hθ2'
    calc |Work.Spaces.mixed j i (Vres a Φs E g τ) z' θ'
            + Work.Spaces.mixed j i (Vth a g τ) z' θ'|
        ≤ |Work.Spaces.mixed j i (Vres a Φs E g τ) z' θ'|
            + |Work.Spaces.mixed j i (Vth a g τ) z' θ'| := abs_add_le _ _
      _ ≤ Mv + C := add_le_add h4 h5
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    rw [← Work.Spaces.mixed_zero_right j]
    exact keyU j 0 (by omega) z θ hz hθ hθ2
  · exact keyU 0 1 (by norm_num) z θ hz hθ hθ2
  · intro j hj
    rw [← Work.Spaces.mixed_zero_right j]
    exact keyV j 0 (by omega) z θ hz hθ hθ2

/-! ## Congruence of the slots under equality on an open set -/

/-- `Uop` is congruent under equality of the stream functions on an open set. -/
theorem Uop_congr_of_eqOn {αG : ℝ} {f f' : Fn} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry f') V) :
    Set.EqOn (Function.uncurry (Work.Construction.Uop αG f))
      (Function.uncurry (Work.Construction.Uop αG f')) V := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hs : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ V := by
    have hsec : IsOpen {z' : ℝ | (z', θ) ∈ V} :=
      hV.preimage (continuous_id.prodMk continuous_const)
    exact hsec.mem_nhds hp
  have hf : (fun z' : ℝ => f z' θ) =ᶠ[𝓝 z] (fun z' : ℝ => f' z' θ) := by
    filter_upwards [hs] with z' hz'
    exact h hz'
  have hval : f z θ = f' z θ := h hp
  simp only [Function.uncurry, Work.Construction.Uop, Work.Spaces.pz, hf.deriv_eq, hval]

/-- `Vop` is congruent under equality of the stream functions on an open set. -/
theorem Vop_congr_of_eqOn {f f' : Fn} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry f') V) :
    Set.EqOn (Function.uncurry (Work.Construction.Vop f))
      (Function.uncurry (Work.Construction.Vop f')) V := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hs : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ V := by
    have hsec : IsOpen {θ' : ℝ | (z, θ') ∈ V} :=
      hV.preimage (continuous_const.prodMk continuous_id)
    exact hsec.mem_nhds hp
  have hf : (fun θ' : ℝ => f z θ') =ᶠ[𝓝 θ] (fun θ' : ℝ => f' z θ') := by
    filter_upwards [hs] with θ' hθ'
    exact h hθ'
  have hval : f z θ = f' z θ := h hp
  simp only [Function.uncurry, Work.Construction.Vop, Work.Spaces.pth, hf.deriv_eq, hval]

/-- `Uprime` is congruent under equality of the stream functions on an open set. -/
theorem Uprime_congr_of_eqOn {αG : ℝ} {f f' : Fn} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry f') V) :
    Set.EqOn (Function.uncurry (Work.FTS.StreamBdryIface.Uprime αG f))
      (Function.uncurry (Work.FTS.StreamBdryIface.Uprime αG f')) V := by
  have hU := Uop_congr_of_eqOn (αG := αG) hV h
  intro p hp
  have h1 := hU hp
  simp only [Function.uncurry, Work.FTS.StreamBdryIface.Uprime] at h1 ⊢
  rw [h1]

/-- `SlotBd` is invariant under equality of the stream functions on the open quadrant. -/
theorem SlotBd_of_eqOn {αG M : ℝ} {f f' : Fn}
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry f') Work.Construction.Qd)
    (hbd : Work.FTS.StreamBdryIface.SlotBd αG f M) :
    Work.FTS.StreamBdryIface.SlotBd αG f' M := by
  have hV : IsOpen (Work.Construction.Qd) := Work.FTS.EllipticEst.isOpen_Q0
  have hU := Uprime_congr_of_eqOn (αG := αG) hV h
  have hW := Vop_congr_of_eqOn hV h
  intro z θ hzθ
  obtain ⟨h1, h2, h3⟩ := hbd z θ hzθ
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    rw [← Work.Spaces.mixed_zero_right j]
    rw [← Work.FTS_RegExport.RXT.Sys.mixed_congr_of_isOpen hV hU j 0 z θ hzθ]
    exact h1 j hj
  · rw [← Work.FTS_RegExport.RXT.Sys.mixed_congr_of_isOpen hV hU 0 1 z θ hzθ]
    exact h2
  · intro j hj
    rw [← Work.Spaces.mixed_zero_right j]
    rw [← Work.FTS_RegExport.RXT.Sys.mixed_congr_of_isOpen hV hW j 0 z θ hzθ]
    exact h3 j hj

/-! ## The `slice_inputs` assembly, with the three delegated pieces as hypotheses -/

/-- `Work.FTS_StreamBdry.Inputs.slice_inputs`, assembled from

* the `SrcOK` leaf (delegated as `srcOK_Ftau`),
* the residual slot jets (delegated as `residual_slot_jetsB`),
* the singular-part slot jets (delegated as `theta_part_jets`),

and `psiCan_C3_proved` for the `C³` clause. -/
theorem slice_inputs_of_pieces {a C₀ Ce Cs : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp a) u →
      Work.FTS.VocabO.EllPkgGo (pExp a) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (pExp a) 6 Ce u (E u))
    (hEL : Work.FTS.FinalV2.EllLimOK3 (pExp a) E)
    (hStar : Work.FTS.VocabO2.StarPkgo2 (pExp a) Cs Φs)
    {g G : Fam} {A B : ℝ → ℝ}
    (hSol : Work.FTS.FinalV2.Sol (pExp a) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (pExp a) C₀ Φs E g)
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G))
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ)
    (hSrc : ∀ τ, 0 ≤ τ → ∃ L Mf : ℝ, Work.FTS.StreamBdryIface.SrcOK
      (Work.Construction.Ftau (pExp a) g τ) L Mf)
    (hRes : ∀ τ, 0 ≤ τ → ∃ M : ℝ,
      (∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (Work.FTS_RegExport.RXT.v2_SlotU a
          (Work.FTS_RegExport.RXT.v2_PhiT a Φs E g τ)) z θ| ≤ M) ∧
      (∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (Work.Construction.Vop
          (Work.FTS_RegExport.RXT.v2_PhiT a Φs E g τ)) z θ| ≤ M))
    (hΘ : ∀ τ, 0 ≤ τ → ∃ C : ℝ, 0 < C ∧
      (∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (Uth a g τ) z θ| ≤ C) ∧
      (∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (Vth a g τ) z θ| ≤ C)) :
    ∀ τ, 0 ≤ τ → ∃ M L Mf : ℝ,
      ContDiffOn ℝ 3 (Function.uncurry (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ))
        Work.Construction.Qd ∧
      Work.FTS.StreamBdryIface.SlotBd (pExp a) (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ) M ∧
      Work.FTS.StreamBdryIface.SrcOK (Work.Construction.Ftau (pExp a) g τ) L Mf := by
  have hpE : (0 : ℝ) < pExp a := Work.FTS.Regularity.pExp_pos ha
  intro τ hτ
  obtain ⟨hsm1, hsm2, hsm3, hsm4, hsm5, hsm6, hsm7, hsm8, hsm9, hsm10, hsm11, hsmPsi3,
    hsmTheta3⟩ :=
    Work.FTS_RegExport.RXT.Sys.coeff_pieces_contDiffOn (α := a) (C₀ := C₀) (Cs := Cs)
      ha ha13 hEL hStar hOK hτ
  obtain ⟨Mv, hMvU, hMvV⟩ := hRes τ hτ
  obtain ⟨C, -, hC_Uth, hC_Vth⟩ := hΘ τ hτ
  -- smoothness of the four slot functions
  have hUres : ContDiffOn ℝ 2 (Function.uncurry (Ures a Φs E g τ))
      Work.FTS.EllipticEst.Q0 := by
    refine (ContDiffOn.const_smul (1 / 2 : ℝ) hsm10).congr ?_
    intro p _
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry, Ures, Work.FTS_RegExport.RXT.v2_SlotU]
    ring
  have hUthS : ContDiffOn ℝ 2 (Function.uncurry (UthS a g τ))
      Work.FTS.EllipticEst.Q0 := by
    refine (ContDiffOn.const_smul (1 / 2 : ℝ) hsm11).congr ?_
    intro p _
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry, UthS]
    ring
  have hVres : ContDiffOn ℝ 2 (Function.uncurry (Vres a Φs E g τ))
      Work.FTS.EllipticEst.Q0 := by
    refine (ContDiffOn.const_smul (1 / (2 * pExp a)) hsm2).congr ?_
    intro p _
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry, Vres, Work.FTS_RegExport.RXT.v2_SlotV]
    have hne : (2 * pExp a) ≠ 0 := ne_of_gt (by positivity)
    rw [smul_eq_mul, one_div, inv_mul_cancel_left₀ hne]
  have hVthS : ContDiffOn ℝ 2 (Function.uncurry (VthS a g τ))
      Work.FTS.EllipticEst.Q0 := by
    refine (ContDiffOn.const_smul (1 / (2 * pExp a)) hsm3).congr ?_
    intro p hp
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry, VthS]
    rw [Vop_Theta_closed (αG := pExp a) (F := Work.Construction.Ftau (pExp a)
      (Work.FTS.RegExportIface.RXT.GR a g) τ) hp.2.1 hp.2.2]
    ring
  have hslotR := slotBd_of_pieces (a := a) (Mv := Mv) (C := C) hτ
    (hsmPsi3.of_le (by norm_num)) (hsmTheta3.of_le (by norm_num)) hsmPsi3 hsmTheta3
    hUres hUthS hVres hVthS
    (fun j i hji z θ hz hθ hθ2 => hMvU j i hji z θ hz hθ hθ2)
    (fun j i hji z θ hz hθ hθ2 => hMvV j i hji z θ hz hθ hθ2) hC_Uth hC_Vth
  have hslot : Work.FTS.StreamBdryIface.SlotBd (pExp a)
      (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ) (Mv + C) :=
    SlotBd_of_eqOn (αG := pExp a) (M := Mv + C)
      (f := slice (Work.FTS.RegExportIface.RXT.ΦR a Φs E g) τ)
      (f' := slice (Work.FTS.Nonlin.PsiCan Φs E g) τ)
      (fun p hp => by
        obtain ⟨z, θ⟩ := p
        exact (slice_PsiCan_eq_slice_PhiR (a := a) (Φs := Φs) (E := E) (g := g) hτ hp).symm)
      hslotR
  have hC3 : ContDiffOn ℝ 3 (Function.uncurry (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ))
      Work.Construction.Qd := by
    have h := Work.FTS_FinalLeaves.psiCan_C3_proved (α := pExp a) hEL hStar hOK τ hτ
    have hfun : Function.uncurry (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ)
        = fun q : ℝ × ℝ => Work.FTS.Nonlin.PsiCan Φs E g q.1 q.2 τ := by
      funext q
      obtain ⟨z, θ⟩ := q
      simp only [Function.uncurry, Work.FTS.Galerkin.slice_apply]
    rw [hfun]
    exact h
  obtain ⟨L, Mf, hSrc'⟩ := hSrc τ hτ
  exact ⟨Mv + C, L, Mf, hC3, hslot, hSrc'⟩

end Work.FTS_StreamBdry.Inputs

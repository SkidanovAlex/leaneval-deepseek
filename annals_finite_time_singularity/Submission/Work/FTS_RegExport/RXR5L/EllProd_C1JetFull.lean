import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_RegExport.RXR5.R5PiecesF
import Submission.Work.FTS_RegExport.RXR5L.ProdAuxC
import Submission.Work.FTS_RegExport.RXR5L.coef_tau_lip
import Submission.Work.FTS_RegExport.RXR5L.factor_gam_bounds
import Submission.Work.FTS_RegExport.RXT.weighted_system
import Submission.Work.FTS_RegExport.THL.L.DzDthSG_C1Jet_of_inputs
import Submission.Work.FTS_StreamBdry.Inputs.ftau_Dz_cont
import Submission.Work.FTS_StreamBdry.Inputs.ftau_cont
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_majorant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS_RegExport.RXR5L

theorem EllProd_C1JetFull {α Ce C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 =
      Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β z θ)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g)
    (hVP : ∀ S > 0, Work.FTS.RegExportIface.VelPkg (Work.FTS.Regularity.pExp α)
      (Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g)
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
      (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) S)
    (hSt1 : ∀ S > 0, Work.FTS.RegPkgGal.St1Class α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)))
    {S : ℝ} (hS : 0 < S) :
    ∃ N₁₂ N₁₃ N₁₄ : ℝ, 0 ≤ N₁₂ ∧ 0 ≤ N₁₃ ∧ 0 ≤ N₁₄ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₁₂
        (fun z θ τ => Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ)
              (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ)) z θ
          * Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ z θ) ∧
      Work.FTS.RegPkgGal.C1Jet α S N₁₃
        (fun z θ τ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ)
              (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ)) z θ
          * Work.Spaces.pth (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ z θ) z θ) ∧
      Work.FTS.RegPkgGal.C1Jet α S N₁₄
        (fun z θ τ => Work.Construction.Vop (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ)
              (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ)) z θ
          * Work.Spaces.Dz (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ z θ) z θ) := by
  have hα1 : α ≤ 1 := by linarith
  -- ## the O1 input (`C1Jet` of the `D_z`/`D_θ` slots of the sanitised family)
  have hO1 : ∃ N₂ N₃ : ℝ, 0 ≤ N₂ ∧ 0 ≤ N₃ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₂
        (fun z θ τ => Work.Spaces.Dz (fun z θ => Work.FTS_RegExport.RXR5.SG α g z θ τ) z θ) ∧
      Work.FTS.RegPkgGal.C1Jet α S N₃
        (fun z θ τ => Work.Spaces.Dth
          (fun z θ => Work.FTS_RegExport.RXR5.SG α g z θ τ) z θ) :=
    Work.FTS_RegExport.THL.L.DzDthSG_C1Jet_of_inputs (Φs := Φs) (E := E)
      hα hα13 hEll hEL3 hStar hSol hOK hdat hμ S hS
  -- ## the three factors and their `Γ`-bounds
  obtain ⟨N₄, hN₄0, hFlt⟩ := Ftau_C1Jet (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
    hα hα13 hOK hS (hSt1 S hS) hO1
  obtain ⟨N₅, _hN₅0, hDthF⟩ := DthFtau_C1Jet (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
    hα hα13 hOK hS (hSt1 S hS) hO1
  obtain ⟨N₆, _hN₆0, hDzF⟩ := DzFtau_C1Jet (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
    hα hα13 hOK hS (hSt1 S hS) hO1
  obtain ⟨B₀, hB₀0, hΓ1, hΓ2, hΓ3⟩ := factor_gam_bounds (Φs := Φs) (E := E)
    hα hα13 hEll hEL3 hStar hSol hOK hdat hμ hS
  -- ## the coefficient data
  obtain ⟨A₀, hA₀0, hQbR, hQthR, hQzR, hQbV, hQthV, hQzV, hQbU, hQthU, hQzU, hQ0⟩ :=
    coef_bounds (Φs := Φs) (E := E) hα hα13 hEll hEL3 hStar hSol hOK hμ S hS
  obtain ⟨K, hK0, hKlip⟩ := coef_tau_lip (Φs := Φs) (E := E)
    hα hα13 hEll hEL3 hStar hSol hOK hμ S hS
  -- the common coefficient constant
  set A : ℝ := A₀ + K with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; linarith
  have hAle : A₀ ≤ A := by rw [hAdef]; linarith
  have hKle : K ≤ A := by rw [hAdef]; linarith
  -- ## the bundling helper
  have jetMono : ∀ {N N' : ℝ} {F : ℝ → ℝ → ℝ → ℝ},
      Work.FTS.RegPkgGal.C1Jet α S N F → N ≤ N' → Work.FTS.RegPkgGal.C1Jet α S N' F := by
    intro N N' F H hN
    refine ⟨Jet_mono H.1 hN, ?_⟩
    intro τ hτ θ hθ z hz
    obtain ⟨d, hd, hdb⟩ := H.2 τ hτ θ hθ z hz
    exact ⟨d, hd, le_trans hdb hN⟩
  have mkProd : ∀ {Q R : ℝ → ℝ → ℝ → ℝ} {B : ℝ}, 0 ≤ B → B₀ ≤ B →
      (∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Set.Icc 0 S →
        |Q z θ τ| ≤ A₀ * min z 1) →
      (∀ θ τ, θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S → Q 0 θ τ = 0) →
      (∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Set.Icc 0 S →
        |Work.Spaces.Dth (fun z θ => Q z θ τ) z θ| ≤ A₀ * min z 1) →
      (∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Set.Icc 0 S →
        |Work.Spaces.Dz (fun z θ => Q z θ τ) z θ| ≤ A₀ * min z 1) →
      (∀ z θ τ τ', 0 < z → 0 < θ → θ < π / 2 → τ ∈ Set.Icc 0 S → τ' ∈ Set.Icc 0 S →
        |Q z θ τ - Q z θ τ'| ≤ K * |τ - τ'|) →
      (∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Set.Icc 0 S →
        DifferentiableAt ℝ (fun z' => Q z' θ τ) z) →
      (∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Set.Icc 0 S →
        DifferentiableAt ℝ (fun θ' => Q z θ' τ) θ) →
      Work.FTS.RegPkgGal.C1Jet α S B R →
      (∀ z θ τ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
        |R z θ τ| ≤ B₀ * Gmp α θ) → ProdData α S A B Q R := by
    intro Q R B hB hBle hQb hQ0 hQth hQz hQtau hQdz hQdth hRjet hRGam
    refine ⟨hA0, hB, ?_, hQ0, ?_, ?_, ?_, hQdz, hQdth, hRjet, ?_⟩
    · intro z θ τ hz hθ0 hθ2 hτ
      exact le_trans (hQb z θ τ hz hθ0 hθ2 hτ)
        (mul_le_mul_of_nonneg_right hAle (le_min hz.le zero_le_one))
    · intro z θ τ hz hθ0 hθ2 hτ
      exact le_trans (hQth z θ τ hz hθ0 hθ2 hτ)
        (mul_le_mul_of_nonneg_right hAle (le_min hz.le zero_le_one))
    · intro z θ τ hz hθ0 hθ2 hτ
      exact le_trans (hQz z θ τ hz hθ0 hθ2 hτ)
        (mul_le_mul_of_nonneg_right hAle (le_min hz.le zero_le_one))
    · intro z θ τ τ' hz hθ0 hθ2 hτ hτ'
      exact le_trans (hQtau z θ τ τ' hz hθ0 hθ2 hτ hτ')
        (mul_le_mul_of_nonneg_right hKle (abs_nonneg _))
    · intro z θ τ hz hθ hτ
      exact le_trans (hRGam z θ τ hz hθ hτ)
        (mul_le_mul_of_nonneg_right hBle (Gmp_nonneg hθ))
  -- ## the three bundled data
  have hPD1 : ProdData α S A (B₀ + N₄) (fun z θ τ => CoefR α Φs E g τ z θ)
      (fun z θ τ => Fp α g τ z θ) :=
    mkProd (Q := fun z θ τ => CoefR α Φs E g τ z θ) (R := fun z θ τ => Fp α g τ z θ)
      (B := B₀ + N₄)
      (by linarith) (by linarith)
      (fun z θ τ hz hθ0 hθ2 hτ => hQbR z θ τ hz hθ0 hθ2 hτ)
      (fun θ τ hθ hτ => (hQ0 θ τ hθ hτ).1)
      (fun z θ τ hz hθ0 hθ2 hτ => hQthR z θ τ hz hθ0 hθ2 hτ)
      (fun z θ τ hz hθ0 hθ2 hτ => hQzR z θ τ hz hθ0 hθ2 hτ)
      (fun z θ τ τ' hz hθ0 hθ2 hτ hτ' => (hKlip τ hτ τ' hτ' z θ hz hθ0 hθ2).1)
      (fun z θ τ hz hθ0 hθ2 hτ => (coef_diff (Ce := Ce) (C₀ := C₀) (Cs := Cs) (Φs := Φs) (E := E) hα hα13 hEL3 hStar hOK
        S hS τ hτ z θ hz hθ0 hθ2).1)
      (fun z θ τ hz hθ0 hθ2 hτ => (coef_diff (Ce := Ce) (C₀ := C₀) (Cs := Cs) (Φs := Φs) (E := E) hα hα13 hEL3 hStar hOK
        S hS τ hτ z θ hz hθ0 hθ2).2.1)
      (jetMono (N := N₄) (N' := B₀ + N₄) (by simpa only [Fp] using hFlt) (by linarith))
      (fun z θ τ hz hθ hτ => hΓ1 z θ τ hz hθ hτ)
  have hPD2 : ProdData α S A (B₀ + N₅) (fun z θ τ => CoefU α Φs E g τ z θ)
      (fun z θ τ => FpDth α g τ z θ) :=
    mkProd (Q := fun z θ τ => CoefU α Φs E g τ z θ) (R := fun z θ τ => FpDth α g τ z θ)
      (B := B₀ + N₅)
      (by linarith) (by linarith)
      (fun z θ τ hz hθ0 hθ2 hτ => hQbU z θ τ hz hθ0 hθ2 hτ)
      (fun θ τ hθ hτ => (hQ0 θ τ hθ hτ).2.2)
      (fun z θ τ hz hθ0 hθ2 hτ => hQthU z θ τ hz hθ0 hθ2 hτ)
      (fun z θ τ hz hθ0 hθ2 hτ => hQzU z θ τ hz hθ0 hθ2 hτ)
      (fun z θ τ τ' hz hθ0 hθ2 hτ hτ' => (hKlip τ hτ τ' hτ' z θ hz hθ0 hθ2).2.2)
      (fun z θ τ hz hθ0 hθ2 hτ => (coef_diff (Ce := Ce) (C₀ := C₀) (Cs := Cs) (Φs := Φs) (E := E) hα hα13 hEL3 hStar hOK
        S hS τ hτ z θ hz hθ0 hθ2).2.2.2.2.1)
      (fun z θ τ hz hθ0 hθ2 hτ => (coef_diff (Ce := Ce) (C₀ := C₀) (Cs := Cs) (Φs := Φs) (E := E) hα hα13 hEL3 hStar hOK
        S hS τ hτ z θ hz hθ0 hθ2).2.2.2.2.2)
      (jetMono (N := N₅) (N' := B₀ + N₅) (by simpa only [FpDth, Fp] using hDthF) (by linarith))
      (fun z θ τ hz hθ hτ => hΓ2 z θ τ hz hθ hτ)
  have hPD3 : ProdData α S A (B₀ + N₆) (fun z θ τ => CoefV α Φs E g τ z θ)
      (fun z θ τ => FpDz α g τ z θ) :=
    mkProd (Q := fun z θ τ => CoefV α Φs E g τ z θ) (R := fun z θ τ => FpDz α g τ z θ)
      (B := B₀ + N₆)
      (by linarith) (by linarith)
      (fun z θ τ hz hθ0 hθ2 hτ => hQbV z θ τ hz hθ0 hθ2 hτ)
      (fun θ τ hθ hτ => (hQ0 θ τ hθ hτ).2.1)
      (fun z θ τ hz hθ0 hθ2 hτ => hQthV z θ τ hz hθ0 hθ2 hτ)
      (fun z θ τ hz hθ0 hθ2 hτ => hQzV z θ τ hz hθ0 hθ2 hτ)
      (fun z θ τ τ' hz hθ0 hθ2 hτ hτ' => (hKlip τ hτ τ' hτ' z θ hz hθ0 hθ2).2.1)
      (fun z θ τ hz hθ0 hθ2 hτ => (coef_diff (Ce := Ce) (C₀ := C₀) (Cs := Cs) (Φs := Φs) (E := E) hα hα13 hEL3 hStar hOK
        S hS τ hτ z θ hz hθ0 hθ2).2.2.1)
      (fun z θ τ hz hθ0 hθ2 hτ => (coef_diff (Ce := Ce) (C₀ := C₀) (Cs := Cs) (Φs := Φs) (E := E) hα hα13 hEL3 hStar hOK
        S hS τ hτ z θ hz hθ0 hθ2).2.2.2.1)
      (jetMono (N := N₆) (N' := B₀ + N₆) (by simpa only [FpDz, Fp] using hDzF) (by linarith))
      (fun z θ τ hz hθ hτ => hΓ3 z θ τ hz hθ hτ)
  -- ## the three products are `C1Jet`s
  obtain ⟨M₁, hM₁0, hC1⟩ := prod_C1Jet_of_vanish (Q := fun z θ τ => CoefR α Φs E g τ z θ)
    (R := fun z θ τ => Fp α g τ z θ) hα hα1 hPD1
  obtain ⟨M₂, hM₂0, hC2⟩ := prod_C1Jet_of_vanish (Q := fun z θ τ => CoefU α Φs E g τ z θ)
    (R := fun z θ τ => FpDth α g τ z θ) hα hα1 hPD2
  obtain ⟨M₃, hM₃0, hC3⟩ := prod_C1Jet_of_vanish (Q := fun z θ τ => CoefV α Φs E g τ z θ)
    (R := fun z θ τ => FpDz α g τ z θ) hα hα1 hPD3
  refine ⟨M₁, M₂, M₃, hM₁0, hM₂0, hM₃0, ?_, ?_, ?_⟩
  · -- the first slot `Rop Φ̃_τ·F_τ`
    refine hC1.congr fun z θ τ _hz _hθ _hτ => ?_
    show CoefR α Φs E g τ z θ * Fp α g τ z θ
      = Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ)
            (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ)) z θ
        * Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ z θ
    rfl
  · -- the second slot `Uop Φ̃_τ·∂_θF_τ`, in the split form
    refine hC2.congr fun z θ τ _hz hθ _hτ => ?_
    show CoefU α Φs E g τ z θ * FpDth α g τ z θ
      = Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ)
            (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ)) z θ
        * Work.Spaces.pth (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ z θ) z θ
    show Work.Construction.Uop (Work.FTS.Regularity.pExp α) (PhiT α Φs E g τ) z θ
        / Real.sin (2 * θ) * (Real.sin (2 * θ) * Work.Spaces.pth (Fp α g τ) z θ)
      = Work.Construction.Uop (Work.FTS.Regularity.pExp α) (PhiT α Φs E g τ) z θ
        * Work.Spaces.pth (Fp α g τ) z θ
    by_cases hθ0 : θ = 0 ∨ θ = π / 2
    · rw [Uop_PhiT_endpoint (Φs := Φs) (E := E) (g := g) (τ := τ) (z := z) hθ0]
      ring
    · push_neg at hθ0
      have hθpos : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hθ0.1)
      have hθlt : θ < π / 2 := lt_of_le_of_ne hθ.2 hθ0.2
      have hpos : 0 < Real.sin (2 * θ) := by
        apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]
      have hs : Real.sin (2 * θ) ≠ 0 := ne_of_gt hpos
      field_simp
  · -- the third slot `Vop Φ̃_τ·D_zF_τ`
    refine hC3.congr fun z θ τ _hz _hθ _hτ => ?_
    show CoefV α Φs E g τ z θ * FpDz α g τ z θ
      = Work.Construction.Vop (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ)
            (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ)) z θ
        * Work.Spaces.Dz (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ z θ) z θ
    rfl

end Work.FTS_RegExport.RXR5L

/-
Copyright: work module for the Elgindi finite-time singularity project.

# The level-`0` (`η`-weighted) estimate: the assembly

Verbatim copy (fresh namespace) of `TT.l2eta_weak_of_pieces` from
`Submission/Work/FTS/EllipticEst/TT/l2eta_weak.lean` (lines 243--244); see `Prop/l2etaL0Aux.lean`
for the auxiliary lemmas it uses.  The copy is needed because the original module is above the
build guard's per-file size limit.-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.Prop.l2etaL0Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

set_option maxHeartbeats 1000000

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop.L0

set_option autoImplicit false

/-- **The assembly of the level-`0` `η`-weighted estimate from the three analytic steps** of
Elgindi's `prop:L2` (Steps 1–3 of `prop:H2`).  See the module docstring. -/
theorem l2eta_weak_of_pieces
    (hPsi : ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
        Work.Spaces.HkMem α 0 Ψ ∧
        Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) ∧
        Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
          ≤ C * Real.sqrt (Work.Spaces.HkSq α 0 F) ∧
        Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ))
          ≤ C * Real.sqrt (Work.Spaces.HkSq α 0 F))
    (hG : ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
        Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) ∧
        α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))
          ≤ C * Real.sqrt (Work.Spaces.HkSq α 0 F))
    (hB : ∀ (C₁ : ℝ), 0 < C₁ →
      (∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
        Work.Spaces.HkMem α 0 Ψ ∧
        Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) ∧
        Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) ∧
        Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
          + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))
          + Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ))
          ≤ C₁ * Real.sqrt (Work.Spaces.HkSq α 0 F)) →
      ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
        Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ))
          ≤ C * (Real.sqrt (Work.Spaces.HkSq α 0 F)
              + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))))
    (hu : ∀ (C₁ C_B : ℝ), 0 < C₁ → 0 < C_B →
      (∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
        Work.Spaces.HkMem α 0 Ψ ∧
        Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) ∧
        Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) ∧
        Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
          + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))
          + Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ))
          ≤ C₁ * Real.sqrt (Work.Spaces.HkSq α 0 F)) →
      (∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
        Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ))
          ≤ C_B * (Real.sqrt (Work.Spaces.HkSq α 0 F)
              + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ)))) →
      ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
        Work.Spaces.HkMem α 0 (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ)) ∧
        Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ)))
          ≤ C * (Real.sqrt (Work.Spaces.HkSq α 0 F)
              + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))))
    : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ),
      0 < α → α ≤ 1 / 4 →
      (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ) →
      (∀ z, Ψ z 0 = 0) → (∀ z, Ψ z (Real.pi / 2) = 0) →
      (∀ z, 0 < z → Work.Elliptic.Fstar F z = 0) →
      (∀ z, 0 < z → Work.Elliptic.Fstar Ψ z = 0) →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      Work.Spaces.HkMem α 0 F →
      Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) →
      Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ) →
      Work.Spaces.HkMem α 0
        (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) →
      α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ)
      ≤ C * Work.Spaces.HkSq α 0 F := by
  obtain ⟨C1, hC1, hpsi⟩ := hPsi
  obtain ⟨Cg, hCg, hgrad⟩ := hG
  -- ### the combined first-order constant and bound
  obtain ⟨Cf, hCf, hfirst⟩ : ∃ Cf : ℝ, 0 < Cf ∧
      ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
        Work.Spaces.HkMem α 0 Ψ ∧
        Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) ∧
        Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) ∧
        Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
          + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))
          + Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ))
          ≤ Cf * Real.sqrt (Work.Spaces.HkSq α 0 F) := by
    refine ⟨2 * C1 + Cg + 1, by linarith, ?_⟩
    intro α F Ψ hα hα4 hw
    obtain ⟨hmΨ, hmCos, hbΨ, hbCos⟩ := hpsi α F Ψ hα hα4 hw
    obtain ⟨hmG, hbG⟩ := hgrad α F Ψ hα hα4 hw
    refine ⟨hmΨ, hmG, hmCos, ?_⟩
    have hF0 : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 F) := Real.sqrt_nonneg _
    nlinarith [hbΨ, hbCos, hbG, mul_nonneg (le_of_lt hCg) hF0,
      mul_nonneg (le_of_lt hC1) hF0, hF0]
  -- ### Step 2 and Step 3
  obtain ⟨CB, hCB, hBsq⟩ := hB Cf hCf hfirst
  obtain ⟨Cu, hCu, hulemma⟩ := hu Cf CB hCf hCB hfirst hBsq
  refine ⟨5 * (1 + 36 * Cg ^ 2 + ((1 + Cg) * CB) ^ 2 + ((1 + Cg) * Cu) ^ 2 + 36 * C1 ^ 2)
      + ((1 + Cg) * CB) ^ 2 + 1, by positivity, ?_⟩
  intro α F Ψ hα hα4 heq h0 h1 horthF horthP hsm hmF hmA hmB hmC
  have hw : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ :=
    ⟨heq, h0, h1, horthF, horthP, hsm, hmF, hmA, hmB, hmC⟩
  obtain ⟨hmΨ, hmG, hmCos, hfirstle⟩ := hfirst α F Ψ hα hα4 hw
  have hBle : Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ))
      ≤ CB * (Real.sqrt (Work.Spaces.HkSq α 0 F)
          + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))) :=
    hBsq α F Ψ hα hα4 hw
  obtain ⟨hmu, hule⟩ := hulemma α F Ψ hα hα4 hw
  -- ### abbreviations
  set gG : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pz Ψ z θ with hgG
  set gu : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ with hgu
  set gcG : ℝ → ℝ → ℝ := fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ) with hgcG
  set g6 : ℝ → ℝ → ℝ := fun z θ => 6 * Ψ z θ with hg6
  set fA : ℝ → ℝ → ℝ := fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) with hfA
  have hAeq : Work.Spaces.HkSq α 0 fA
      = α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := by
    rw [HkSq_zero_const_mul α (α ^ 2) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)]
    ring
  -- ### the pointwise identity on the open quadrant
  have hident : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      fA z θ = -F z θ - gcG z θ - Work.Spaces.pthIter 2 Ψ z θ + gu z θ - g6 z θ := by
    intro z θ hz hθ0 hθ1
    have h := heq z hz θ hθ0 hθ1
    rw [Work.Elliptic.bslOp_apply] at h
    simp only [Work.Elliptic.Lzero, hfA, hgcG, hgu, hg6] at h ⊢
    ring_nf at h ⊢
    linarith [h]
  -- ### the majorant bound on the whole domain
  have hmaj : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 fA z θ
        ≤ 5 * (Work.Spaces.HkIntegrand α 0 F z θ
            + Work.Spaces.HkIntegrand α 0 gcG z θ
            + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ
            + Work.Spaces.HkIntegrand α 0 gu z θ
            + Work.Spaces.HkIntegrand α 0 g6 z θ) := by
    intro z hz θ hθ
    have hnn1 := Work.Spaces.HkIntegrand_nonneg α 0 F z θ
    have hnn2 := Work.Spaces.HkIntegrand_nonneg α 0 gcG z θ
    have hnn3 := Work.Spaces.HkIntegrand_nonneg α 0 (Work.Spaces.pthIter 2 Ψ) z θ
    have hnn4 := Work.Spaces.HkIntegrand_nonneg α 0 gu z θ
    have hnn5 := Work.Spaces.HkIntegrand_nonneg α 0 g6 z θ
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [HkIntegrand_zero_boundary α _ (Or.inl hz0.symm)]
      have h0' : (0 : ℝ) ≤ Work.Spaces.HkIntegrand α 0 F z θ := hnn1
      nlinarith [hnn1, hnn2, hnn3, hnn4, hnn5]
    · rcases eq_or_lt_of_le (Set.mem_Icc.mp hθ).1 with hθ0 | hθ0pos
      · rw [HkIntegrand_zero_boundary α _ (Or.inr (Or.inl hθ0.symm))]
        nlinarith [hnn1, hnn2, hnn3, hnn4, hnn5]
      · rcases eq_or_lt_of_le (Set.mem_Icc.mp hθ).2 with hθπ | hθlt
        · rw [HkIntegrand_zero_boundary α _ (Or.inr (Or.inr hθπ))]
          nlinarith [hnn1, hnn2, hnn3, hnn4, hnn5]
        · rw [HkIntegrand_zero_eq, HkIntegrand_zero_eq, HkIntegrand_zero_eq,
            HkIntegrand_zero_eq, HkIntegrand_zero_eq, HkIntegrand_zero_eq]
          set W : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hW
          have hid := hident z θ hzpos hθ0pos hθlt
          simp only [hfA, hgcG, hgu, hg6] at hid ⊢
          have hsplit : (α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) * W
              = -(F z θ * W) + -((α * (5 + α) * (z * Work.Spaces.pz Ψ z θ)) * W)
                + -((Work.Spaces.pthIter 2 Ψ z θ) * W)
                + (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ) * W
                + -((6 * Ψ z θ) * W) := by
            rw [hid]; ring
          rw [hsplit]
          have hkey := sum_five_sq_le (-(F z θ * W))
            (-((α * (5 + α) * (z * Work.Spaces.pz Ψ z θ)) * W))
            (-((Work.Spaces.pthIter 2 Ψ z θ) * W))
            ((Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ) * W)
            (-((6 * Ψ z θ) * W))
          linarith [hkey]
  -- ### the honesty of the majorant
  have hMd : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 0 F z θ
          + Work.Spaces.HkIntegrand α 0 gcG z θ
          + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ
          + Work.Spaces.HkIntegrand α 0 gu z θ
          + Work.Spaces.HkIntegrand α 0 g6 z θ) Work.Spaces.Iθ := by
    intro z hz
    exact ((((hmF.1 z hz).add ((HkMem_zero_const_mul α (α * (5 + α)) hmG).1 z hz)).add
      (hmB.1 z hz)).add (hmu.1 z hz)).add
      ((HkMem_zero_const_mul α 6 hmΨ).1 z hz)
  have hMθ : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn
        (fun θ => 5 * (Work.Spaces.HkIntegrand α 0 F z θ
            + Work.Spaces.HkIntegrand α 0 gcG z θ
            + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ
            + Work.Spaces.HkIntegrand α 0 gu z θ
            + Work.Spaces.HkIntegrand α 0 g6 z θ)) Work.Spaces.Iθ :=
    fun z hz => (hMd z hz).const_mul 5
  -- ### the value of the majorant integral
  have hstep1 : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, 5 * (Work.Spaces.HkIntegrand α 0 F z θ
          + Work.Spaces.HkIntegrand α 0 gcG z θ
          + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ
          + Work.Spaces.HkIntegrand α 0 gu z θ
          + Work.Spaces.HkIntegrand α 0 g6 z θ))
        = 5 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 gcG z θ)
            + (∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 gu z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g6 z θ)) := by
    intro z hz
    have h1 : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 F z θ)
        Work.Spaces.Iθ := hmF.1 z hz
    have h2 : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 gcG z θ)
        Work.Spaces.Iθ := (HkMem_zero_const_mul α (α * (5 + α)) hmG).1 z hz
    have h3 : MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ)
        Work.Spaces.Iθ := hmB.1 z hz
    have h4 : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 gu z θ)
        Work.Spaces.Iθ := hmu.1 z hz
    have h5 : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 g6 z θ)
        Work.Spaces.Iθ := (HkMem_zero_const_mul α 6 hmΨ).1 z hz
    rw [MeasureTheory.integral_const_mul]
    congr 1
    exact integral_five_eq h1 h2 h3 h4 h5
  have hsumInt : MeasureTheory.IntegrableOn
      (fun z => (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ)
        + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 gcG z θ)
        + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ)
        + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 gu z θ)
        + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g6 z θ)) Work.Spaces.Iz :=
    (((hmF.2.add (HkMem_zero_const_mul α (α * (5 + α)) hmG).2).add hmB.2).add hmu.2).add
      (HkMem_zero_const_mul α 6 hmΨ).2
  have hMz : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ,
        5 * (Work.Spaces.HkIntegrand α 0 F z θ
            + Work.Spaces.HkIntegrand α 0 gcG z θ
            + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ
            + Work.Spaces.HkIntegrand α 0 gu z θ
            + Work.Spaces.HkIntegrand α 0 g6 z θ)) Work.Spaces.Iz := by
    refine MeasureTheory.IntegrableOn.congr_fun (μ := volume)
      (hsumInt.const_mul 5) ?_ (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)
    intro z hz
    exact (hstep1 z hz).symm
  -- ### the value of the majorant integral
  have hval : (∫ z in Set.Ici (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
      5 * (Work.Spaces.HkIntegrand α 0 F z θ
          + Work.Spaces.HkIntegrand α 0 gcG z θ
          + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ
          + Work.Spaces.HkIntegrand α 0 gu z θ
          + Work.Spaces.HkIntegrand α 0 g6 z θ))
      = 5 * (Work.Spaces.HkSq α 0 F
          + ((α * (5 + α)) ^ 2) * Work.Spaces.HkSq α 0 gG
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ)
          + Work.Spaces.HkSq α 0 gu
          + 36 * Work.Spaces.HkSq α 0 Ψ) := by
    rw [MeasureTheory.setIntegral_congr_fun (μ := volume) measurableSet_Ici
      (fun x hx => hstep1 x hx)]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    have hz1 : MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ)
        Work.Spaces.Iz := hmF.2
    have hz2 : MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 gcG z θ)
        Work.Spaces.Iz := (HkMem_zero_const_mul α (α * (5 + α)) hmG).2
    have hz3 : MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ) Work.Spaces.Iz := hmB.2
    have hz4 : MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 gu z θ) Work.Spaces.Iz :=
      hmu.2
    have hz5 : MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g6 z θ)
        Work.Spaces.Iz := (HkMem_zero_const_mul α 6 hmΨ).2
    rw [integral_five_eq (s := Set.Ici (0 : ℝ)) hz1 hz2 hz3 hz4 hz5]
    have e1 : (∫ z in Set.Ici (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 F z θ) = Work.Spaces.HkSq α 0 F := rfl
    have e2 : (∫ z in Set.Ici (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 gcG z θ)
        = ((α * (5 + α)) ^ 2) * Work.Spaces.HkSq α 0 gG := by
      rw [← HkSq_zero_const_mul α (α * (5 + α)) gG]
      rfl
    have e3 : (∫ z in Set.Ici (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ)
        = Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ) := rfl
    have e4 : (∫ z in Set.Ici (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 gu z θ) = Work.Spaces.HkSq α 0 gu := rfl
    have e5 : (∫ z in Set.Ici (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 g6 z θ) = 36 * Work.Spaces.HkSq α 0 Ψ := by
      rw [show (36 : ℝ) = 6 ^ 2 by norm_num]
      rw [← HkSq_zero_const_mul α 6 Ψ]
      rfl
    rw [e1, e2, e3, e4, e5]
  -- ### the `A`-bound
  have hA : Work.Spaces.HkSq α 0 fA
      ≤ 5 * (Work.Spaces.HkSq α 0 F
          + ((α * (5 + α)) ^ 2) * Work.Spaces.HkSq α 0 gG
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ)
          + Work.Spaces.HkSq α 0 gu
          + 36 * Work.Spaces.HkSq α 0 Ψ) := by
    have hmemfA : Work.Spaces.HkMem α 0 fA :=
      HkMem_zero_const_mul α (α ^ 2)
        (f := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) hmA
    exact (HkSq_zero_le_of_integrand_le α hmemfA hMθ hMz hmaj).trans hval.le
  -- ### the individual `HkSq` bounds
  have hF0 : 0 ≤ Work.Spaces.HkSq α 0 F := Work.Spaces.HkSq_nonneg α 0 F
  have hG0 : 0 ≤ Work.Spaces.HkSq α 0 gG := Work.Spaces.HkSq_nonneg α 0 gG
  have hB0 : 0 ≤ Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ) :=
    Work.Spaces.HkSq_nonneg α 0 _
  have hu0 : 0 ≤ Work.Spaces.HkSq α 0 gu := Work.Spaces.HkSq_nonneg α 0 gu
  have hP0 : 0 ≤ Work.Spaces.HkSq α 0 Ψ := Work.Spaces.HkSq_nonneg α 0 Ψ
  have hF0s : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 F) := Real.sqrt_nonneg _
  have hbG := (hgrad α F Ψ hα hα4 hw).2
  have hbPsi := (hpsi α F Ψ hα hα4 hw).2.2.1
  -- `((α(5+α))²)·HkSq gG ≤ 36 Cg² HkSq F`
  have hcGsq : ((α * (5 + α)) ^ 2) * Work.Spaces.HkSq α 0 gG
      ≤ 36 * Cg ^ 2 * Work.Spaces.HkSq α 0 F := by
    have hs : (α * Real.sqrt (Work.Spaces.HkSq α 0 gG)) ^ 2
        ≤ (Cg * Real.sqrt (Work.Spaces.HkSq α 0 F)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hbG 2
    rw [mul_pow, Real.sq_sqrt hG0, mul_pow, Real.sq_sqrt hF0] at hs
    have h5 : (5 + α) ^ 2 ≤ 36 := by nlinarith [hα4]
    have hstep : ((α * (5 + α)) ^ 2) * Work.Spaces.HkSq α 0 gG
        = ((5 + α) ^ 2) * (α ^ 2 * Work.Spaces.HkSq α 0 gG) := by ring
    rw [hstep]
    calc ((5 + α) ^ 2) * (α ^ 2 * Work.Spaces.HkSq α 0 gG)
        ≤ ((5 + α) ^ 2) * (Cg ^ 2 * Work.Spaces.HkSq α 0 F) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ 36 * (Cg ^ 2 * Work.Spaces.HkSq α 0 F) :=
          mul_le_mul_of_nonneg_right h5 (by positivity)
      _ = 36 * Cg ^ 2 * Work.Spaces.HkSq α 0 F := by ring
  -- `HkSq B ≤ ((1+Cg)CB)² HkSq F`
  have hBsq : Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ)
      ≤ ((1 + Cg) * CB) ^ 2 * Work.Spaces.HkSq α 0 F := by
    have hαG : α * Real.sqrt (Work.Spaces.HkSq α 0 gG)
        ≤ Cg * Real.sqrt (Work.Spaces.HkSq α 0 F) := hbG
    have hcomb : Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ))
        ≤ (1 + Cg) * CB * Real.sqrt (Work.Spaces.HkSq α 0 F) := by
      have h2 : CB * (Real.sqrt (Work.Spaces.HkSq α 0 F)
            + α * Real.sqrt (Work.Spaces.HkSq α 0 gG))
          ≤ CB * ((1 + Cg) * Real.sqrt (Work.Spaces.HkSq α 0 F)) := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hCB)
        nlinarith [hαG]
      nlinarith [hBle, h2, mul_nonneg (le_of_lt hCB) hF0s,
        mul_nonneg (mul_nonneg (le_of_lt hCB) (le_of_lt hCg)) hF0s]
    have hs : (Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ))) ^ 2
        ≤ ((1 + Cg) * CB * Real.sqrt (Work.Spaces.HkSq α 0 F)) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hcomb 2
    rw [Real.sq_sqrt hB0, mul_pow, mul_pow, Real.sq_sqrt hF0] at hs
    have hgoal : ((1 + Cg) * CB) ^ 2 * Work.Spaces.HkSq α 0 F
        = (1 + Cg) ^ 2 * CB ^ 2 * Work.Spaces.HkSq α 0 F := by ring
    rw [hgoal]
    exact hs
  -- `HkSq u ≤ ((1+Cg)Cu)² HkSq F`
  have husq : Work.Spaces.HkSq α 0 gu ≤ ((1 + Cg) * Cu) ^ 2 * Work.Spaces.HkSq α 0 F := by
    have hαG : α * Real.sqrt (Work.Spaces.HkSq α 0 gG)
        ≤ Cg * Real.sqrt (Work.Spaces.HkSq α 0 F) := hbG
    have hcomb : Real.sqrt (Work.Spaces.HkSq α 0 gu)
        ≤ (1 + Cg) * Cu * Real.sqrt (Work.Spaces.HkSq α 0 F) := by
      have h2 : Cu * (Real.sqrt (Work.Spaces.HkSq α 0 F)
            + α * Real.sqrt (Work.Spaces.HkSq α 0 gG))
          ≤ Cu * ((1 + Cg) * Real.sqrt (Work.Spaces.HkSq α 0 F)) := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hCu)
        nlinarith [hαG]
      nlinarith [hule, h2, mul_nonneg (le_of_lt hCu) hF0s,
        mul_nonneg (mul_nonneg (le_of_lt hCu) (le_of_lt hCg)) hF0s]
    have hs : (Real.sqrt (Work.Spaces.HkSq α 0 gu)) ^ 2
        ≤ ((1 + Cg) * Cu * Real.sqrt (Work.Spaces.HkSq α 0 F)) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hcomb 2
    rw [Real.sq_sqrt hu0, mul_pow, mul_pow, Real.sq_sqrt hF0] at hs
    have hgoal : ((1 + Cg) * Cu) ^ 2 * Work.Spaces.HkSq α 0 F
        = (1 + Cg) ^ 2 * Cu ^ 2 * Work.Spaces.HkSq α 0 F := by ring
    rw [hgoal]
    exact hs
  -- `36 HkSq Ψ ≤ 36 C1² HkSq F`
  have hPsisq : 36 * Work.Spaces.HkSq α 0 Ψ ≤ 36 * C1 ^ 2 * Work.Spaces.HkSq α 0 F := by
    have hs : (Real.sqrt (Work.Spaces.HkSq α 0 Ψ)) ^ 2
        ≤ (C1 * Real.sqrt (Work.Spaces.HkSq α 0 F)) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hbPsi 2
    rw [Real.sq_sqrt hP0, mul_pow, Real.sq_sqrt hF0] at hs
    nlinarith [hs]
  -- ### the final square-root assembly
  have hAfin : α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      ≤ (5 * (1 + 36 * Cg ^ 2 + ((1 + Cg) * CB) ^ 2 + ((1 + Cg) * Cu) ^ 2 + 36 * C1 ^ 2))
        * Work.Spaces.HkSq α 0 F := by
    have hA0 : 0 ≤ Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
      Work.Spaces.HkSq_nonneg α 0 _
    have hAeq : Work.Spaces.HkSq α 0 fA
        = α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := by
      rw [HkSq_zero_const_mul α (α ^ 2) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)]
      ring
    rw [← hAeq]
    have hc1 : 0 ≤ ((α * (5 + α)) ^ 2) * Work.Spaces.HkSq α 0 gG := mul_nonneg (sq_nonneg _) hG0
    have hc2 : 0 ≤ 36 * Work.Spaces.HkSq α 0 Ψ := by linarith
    calc Work.Spaces.HkSq α 0 fA
        ≤ 5 * (Work.Spaces.HkSq α 0 F + ((α * (5 + α)) ^ 2) * Work.Spaces.HkSq α 0 gG
            + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ) + Work.Spaces.HkSq α 0 gu
            + 36 * Work.Spaces.HkSq α 0 Ψ) := hA
      _ ≤ 5 * ((1 + 36 * Cg ^ 2 + ((1 + Cg) * CB) ^ 2 + ((1 + Cg) * Cu) ^ 2 + 36 * C1 ^ 2)
            * Work.Spaces.HkSq α 0 F) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          nlinarith [hcGsq, hBsq, husq, hPsisq, hF0]
      _ = (5 * (1 + 36 * Cg ^ 2 + ((1 + Cg) * CB) ^ 2 + ((1 + Cg) * Cu) ^ 2 + 36 * C1 ^ 2))
            * Work.Spaces.HkSq α 0 F := by ring
  -- ### the target
  have hfinal : α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ)
      ≤ (5 * (1 + 36 * Cg ^ 2 + ((1 + Cg) * CB) ^ 2 + ((1 + Cg) * Cu) ^ 2 + 36 * C1 ^ 2)
          + ((1 + Cg) * CB) ^ 2 + 1) * Work.Spaces.HkSq α 0 F := by
    have hmain : Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ)
        ≤ ((1 + Cg) * CB) ^ 2 * Work.Spaces.HkSq α 0 F := hBsq
    have hK : (0 : ℝ) ≤ 5 * (1 + 36 * Cg ^ 2 + ((1 + Cg) * CB) ^ 2 + ((1 + Cg) * Cu) ^ 2
        + 36 * C1 ^ 2) := by positivity
    calc α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ)
        ≤ (5 * (1 + 36 * Cg ^ 2 + ((1 + Cg) * CB) ^ 2 + ((1 + Cg) * Cu) ^ 2 + 36 * C1 ^ 2))
            * Work.Spaces.HkSq α 0 F + ((1 + Cg) * CB) ^ 2 * Work.Spaces.HkSq α 0 F :=
          add_le_add hAfin hmain
      _ = (5 * (1 + 36 * Cg ^ 2 + ((1 + Cg) * CB) ^ 2 + ((1 + Cg) * Cu) ^ 2 + 36 * C1 ^ 2)
            + ((1 + Cg) * CB) ^ 2) * Work.Spaces.HkSq α 0 F := by ring
      _ ≤ (5 * (1 + 36 * Cg ^ 2 + ((1 + Cg) * CB) ^ 2 + ((1 + Cg) * Cu) ^ 2 + 36 * C1 ^ 2)
            + ((1 + Cg) * CB) ^ 2 + 1) * Work.Spaces.HkSq α 0 F := by
          refine mul_le_mul_of_nonneg_right ?_ hF0
          linarith
  exact hfinal

end Work.FTS.EllipticEst.Prop.L0

import Mathlib
import Submission.Work.Mostow.geodSetup
import Submission.Work.Mostow.torsionNearIdGeodesic
import Submission.Work.Mostow.axisNearIdMarg
import Submission.Work.Mostow.nearIdPairCommuteTorsion
import Submission.Work.Mostow.conjGeodStabOfCommuting

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section


private lemma mri_coordEmb_zero (k m : ℕ) : Submission.Mostow.coordEmb k m (0 : Submission.Mostow.E k) = (0 : Submission.Mostow.E (k + m)) := by
  apply WithLp.ofLp_injective
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [Submission.Mostow.coordEmb]

theorem margRegionInvariant (m : ℕ) (hm : 4 ≤ m) (hev : Even m)
    (hA : Submission.Mostow.POActionProp (1 + m)) (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (hA1 : Submission.Mostow.POActionProp 1) (hI1 : Submission.Mostow.HypIsometryProp 1) :
    ∃ η₁max : ℝ, 0 < η₁max ∧ ∀ η₁ : ℝ, 0 < η₁ → η₁ ≤ η₁max →
      ∀ (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1)),
        _root_.IsDiscrete (SetLike.coe Λ) →
        (∀ (a : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1) (u : Submission.Mostow.E (1 + m)), a ∈ Λ → a ∈ Submission.Mostow.SetStabStd 1 m →
          Submission.Mostow.resStd 1 m a = 1 → a ≠ 1 → Submission.Mostow.NearIdAt a u η₁ → Submission.Mostow.fixSet a = Submission.Mostow.stdTG 1 m) →
        ∀ u v : Submission.Mostow.E (1 + m), u ∈ Work.Mostow.margRegion m Λ η₁ → v ∈ Work.Mostow.margRegion m Λ η₁ →
          ∀ γ : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1, γ ∈ Λ → γ • u = v → γ ∈ Work.Mostow.geodStab m hA Λ := by
  have hm2 : 2 ≤ 1 + m := by omega
  obtain ⟨θP, hθPpos, hθP⟩ := nearIdPairCommuteTorsion m hm2 hA hI
  have hb := POBasic.ofProp hA
  refine ⟨min (1 / 48) (θP / 48), lt_min (by norm_num) (by linarith), ?_⟩
  intro η₁ hη₁pos hη₁le Λ hdisc hT u v hu hv γ hγΛ hγuv
  have hη₁le48 : η₁ ≤ 1 / 48 := le_trans hη₁le (min_le_left _ _)
  have hη₁leθd : η₁ ≤ θP / 48 := le_trans hη₁le (min_le_right _ _)
  have hη₁le1 : η₁ ≤ 1 := by linarith
  have hη₁leθP : η₁ ≤ θP := by linarith
  have h48leθP : 48 * η₁ ≤ θP := by linarith
  have h48le1 : 48 * η₁ ≤ 1 := by linarith
  have h48lt2 : 48 * η₁ < 2 := by linarith
  obtain ⟨a, haΛ, haS, haR, ha1, haN⟩ := hu
  obtain ⟨b, hbΛ, hbS, hbR, hb1, hbN⟩ := hv
  have haFix : fixSet a = stdTG 1 m := hT a u haΛ haS haR ha1 haN
  have hbFix : fixSet b = stdTG 1 m := hT b v hbΛ hbS hbR hb1 hbN
  have haFix' : ∀ y : E (1 + m), a • y = y ↔ y ∈ stdTG 1 m := by
    intro y; rw [← haFix]; rfl
  have hbFix' : ∀ y : E (1 + m), b • y = y ↔ y ∈ stdTG 1 m := by
    intro y; rw [← hbFix]; rfl
  let c : PO (1 + m) 1 := γ⁻¹ * b * γ
  have hcΛ : c ∈ Λ := Λ.mul_mem (Λ.mul_mem (Λ.inv_mem hγΛ) hbΛ) hγΛ
  have hcN : NearIdAt c u η₁ := by
    show NearIdAt (γ⁻¹ * b * γ) u η₁
    exact (nearIdAt_conj_iff hA hI γ b u η₁).mpr (by rw [hγuv]; exact hbN)
  have hcFix' : ∀ y : E (1 + m), c • y = y ↔ γ • y ∈ stdTG 1 m := by
    intro y
    have hmul : c • y = γ⁻¹ • (b • (γ • y)) := by
      show (γ⁻¹ * b * γ) • y = γ⁻¹ • (b • (γ • y))
      rw [show (γ⁻¹ * b * γ : PO (1 + m) 1) = γ⁻¹ * (b * γ) from mul_assoc _ _ _,
          hb.mul_smul γ⁻¹ (b * γ) y, hb.mul_smul b γ y]
    have hiff : (γ⁻¹ • (b • (γ • y)) = y) ↔ (b • (γ • y) = γ • y) := by
      constructor
      · intro h
        have h2 : γ • (γ⁻¹ • (b • (γ • y))) = γ • y := by rw [h]
        rwa [← hb.mul_smul γ γ⁻¹ (b • (γ • y)), mul_inv_cancel, hb.one_smul] at h2
      · intro h
        rw [h, ← hb.mul_smul γ⁻¹ γ y, inv_mul_cancel, hb.one_smul]
    rw [hmul, hiff]
    exact hbFix' (γ • y)
  have hnax_a : ∀ x : E (1 + m), x ∈ stdTG 1 m → NearIdAt a x (48 * η₁) :=
    axisNearIdMarg m hA1 hI1 hA hI a u η₁ hη₁pos hη₁le1 haS haR haN
  have hnax_b : ∀ x : E (1 + m), x ∈ stdTG 1 m → NearIdAt b x (48 * η₁) :=
    axisNearIdMarg m hA1 hI1 hA hI b v η₁ hη₁pos hη₁le1 hbS hbR hbN
  have hnax_a' : ∀ x : E (1 + m), a • x = x → NearIdAt a x (48 * η₁) :=
    fun x hx => hnax_a x ((haFix' x).mp hx)
  have hnax_b' : ∀ x : E (1 + m), b • x = x → NearIdAt b x (48 * η₁) :=
    fun x hx => hnax_b x ((hbFix' x).mp hx)
  have hnax_c' : ∀ x : E (1 + m), c • x = x → NearIdAt c x (48 * η₁) := by
    intro x hx
    have hγx : γ • x ∈ stdTG 1 m := (hcFix' x).mp hx
    show NearIdAt (γ⁻¹ * b * γ) x (48 * η₁)
    exact (nearIdAt_conj_iff hA hI γ b x (48 * η₁)).mpr (hnax_b (γ • x) hγx)
  have h0mem : (0 : E (1 + m)) ∈ stdTG 1 m := ⟨0, mri_coordEmb_zero 1 m⟩
  have hafix0 : a • (0 : E (1 + m)) = 0 := (haFix' 0).mpr h0mem
  have hcfix : c • (γ⁻¹ • (0 : E (1 + m))) = γ⁻¹ • (0 : E (1 + m)) := by
    show (γ⁻¹ * b * γ) • (γ⁻¹ • (0 : E (1 + m))) = γ⁻¹ • (0 : E (1 + m))
    rw [show (γ⁻¹ * b * γ : PO (1 + m) 1) = γ⁻¹ * (b * γ) from mul_assoc _ _ _,
        hb.mul_smul γ⁻¹ (b * γ) (γ⁻¹ • (0 : E (1 + m))),
        hb.mul_smul b γ (γ⁻¹ • (0 : E (1 + m))),
        ← hb.mul_smul γ γ⁻¹ (0 : E (1 + m)), mul_inv_cancel, hb.one_smul,
        (hbFix' 0).mpr h0mem]
  obtain ⟨p, hap, hcp, hcomm⟩ :=
    hθP Λ hdisc a c u haΛ hcΛ
      (NearIdAt.mono haN hη₁leθP) (NearIdAt.mono hcN hη₁leθP)
      ⟨0, hafix0⟩ ⟨γ⁻¹ • 0, hcfix⟩
      (fun x hx => NearIdAt.mono (hnax_a' x hx) h48leθP)
      (fun x hx => NearIdAt.mono (hnax_c' x hx) h48leθP)
  have hneara : NearIdAt a p (48 * η₁) := hnax_a' p hap
  have hnearc : NearIdAt c p (48 * η₁) := hnax_c' p hcp
  have hγS : γ ∈ SetStabStd 1 m :=
    conjGeodStabOfCommuting m hA hI a c γ p (48 * η₁) h48lt2 hcomm haFix' hcFix' hap hcp
      hneara hnearc
  have hmem : γ ∈ Λ ⊓ stabStdGeod m hA := ⟨hγΛ, hγS⟩
  simpa [geodStab] using hmem

end

end Work.Mostow

import Mathlib
import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.PinchLemma3.ClosedDiscA.exists_alternating_partition
import Submission.Work.SurgeryInvariance.WindingOf.homotopic_eq
import Submission.Work.PinchLemma3.ClosedDiscA.exists_functional_kernel_eq
import Submission.Work.PinchLemma3.ClosedDiscA.windingSpan_union_le_sup_of_isPathConnected_inter
import Submission.Work.PinchLemma3.ClosedDiscA.potential_helpers
import Submission.Work.PinchLemma3.ClosedDiscA.two_component_intersection

namespace Work.PinchLemma3.ClosedDiscA

open LeanEval.KnotTheory.PardonDistortion Set

/-- **Linear algebra of `ℚ²`.**  A proper `ℚ`-subspace of `ℚ × ℚ` does not contain any of the
lines `ℚ · v` with `v ≠ 0`. -/
theorem exists_ne_zero_inf_span_le_of_ne_top (W : Submodule ℚ (ℚ × ℚ)) (h : W ≠ ⊤) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧ W ⊓ Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤ ⊥ := by
  obtain ⟨v, hv⟩ : ∃ v : ℚ × ℚ, v ∉ W := by
    by_contra hcon
    push_neg at hcon
    exact h (Submodule.eq_top_iff'.mpr (fun x => hcon x))
  refine ⟨v, fun hv0 => hv (by rw [hv0]; exact W.zero_mem), ?_⟩
  rw [le_bot_iff]
  refine (Submodule.eq_bot_iff _).mpr (fun x hx => ?_)
  obtain ⟨hxW, hxsp⟩ := hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxsp
  rcases eq_or_ne c 0 with hc0 | hc0
  · rw [hc0, zero_smul] at hc; exact hc.symm
  · exact absurd (show v ∈ W from by
      have hveq : v = c⁻¹ • x := by rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [hveq]; exact W.smul_mem _ hxW) hv

theorem exists_ne_zero_inf_span_le_of_intersection_pair {P : Work.CoreTopology.ParamTorus}
    {A B : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hAc : A ⊆ P.carrier) (hBc : B ⊆ P.carrier)
    (hAop : Work.SurgeryInvariance.IsOpenInCarrier P A)
    (hBop : Work.SurgeryInvariance.IsOpenInCarrier P B)
    (hApc : IsPathConnected A) (hBpc : IsPathConnected B)
    (hVA : Work.SurgeryInvariance.WindingSpan P A = ⊥)
    (hVB : Work.SurgeryInvariance.WindingSpan P B = ⊥)
    {K₁ K₂ : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hK₁c : K₁ ⊆ P.carrier) (hK₂c : K₂ ⊆ P.carrier)
    (hK₁op : Work.SurgeryInvariance.IsOpenInCarrier P K₁)
    (hK₂op : Work.SurgeryInvariance.IsOpenInCarrier P K₂)
    (hK₁pc : IsPathConnected K₁) (hK₂pc : IsPathConnected K₂)
    (hdisj : Disjoint K₁ K₂) (hinter : A ∩ B = K₁ ∪ K₂) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (A ∪ B) ⊓ Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
        Work.SurgeryInvariance.WindingSpan P A ⊔ Work.SurgeryInvariance.WindingSpan P B := by
  rw [hVA, hVB, bot_sup_eq]
  -- the two "gates"
  obtain ⟨a₀, ha₀⟩ := hK₁pc.nonempty
  obtain ⟨b₀, hb₀⟩ := hK₂pc.nonempty
  have haA : a₀ ∈ A := (hinter.symm ▸ Set.mem_union_left K₂ ha₀).1
  have haB : a₀ ∈ B := (hinter.symm ▸ Set.mem_union_left K₂ ha₀).2
  have hbA : b₀ ∈ A := (hinter.symm ▸ Set.mem_union_right K₁ hb₀).1
  have hbB : b₀ ∈ B := (hinter.symm ▸ Set.mem_union_right K₁ hb₀).2
  set a : P.carrier := ⟨a₀, hAc haA⟩ with hadef
  set b : P.carrier := ⟨b₀, hAc hbA⟩ with hbdef
  obtain ⟨cA, hcA⟩ := exists_carrierPath (p := a) (q := b) hAc (hApc.joinedIn a₀ haA b₀ hbA)
  obtain ⟨cB, hcB⟩ := exists_carrierPath (p := a) (q := b) hBc (hBpc.joinedIn a₀ haB b₀ hbB)
  -- the test loop and its winding
  set w : ℤ × ℤ := Work.SurgeryInvariance.windingOf P (closedCurveOfPath (cA.trans cB.symm)) with hwdef
  -- the integer coefficients of the killing functional
  set Ac : ℤ := if w = 0 then 1 else w.1 with hAcdef
  set Bc : ℤ := if w = 0 then 0 else w.2 with hBcdef
  have hcoef : Bc * w.1 = Ac * w.2 := by
    by_cases hw0 : w = 0
    · rw [hw0]; simp
    · rw [hAcdef, hBcdef, if_neg hw0, if_neg hw0]; ring
  have hne : (Ac, Bc) ≠ 0 := by
    by_cases hw0 : w = 0
    · rw [hAcdef, hBcdef, if_pos hw0, if_pos hw0]; decide
    · rw [hAcdef, hBcdef, if_neg hw0, if_neg hw0]
      intro hcon
      exact hw0 (Prod.ext (by simpa using congrArg Prod.fst hcon)
        (by simpa using congrArg Prod.snd hcon))
  -- the real functional killing the test winding
  set ψR : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun p => (Bc : ℝ) * p.1 - (Ac : ℝ) * p.2
      map_add' := by intro p q; simp only [Prod.fst_add, Prod.snd_add]; ring
      map_smul' := by intro c p; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring } with hψRdef
  have hψRZ : ∀ k l : ℤ, ψR (((k : ℤ) : ℝ), ((l : ℤ) : ℝ)) = ((Bc * k - Ac * l : ℤ) : ℝ) := by
    intro k l
    rw [hψRdef]
    show (Bc : ℝ) * (k : ℝ) - (Ac : ℝ) * (l : ℝ) = ((Bc * k - Ac * l : ℤ) : ℝ)
    push_cast
    ring
  have hψw : psiDisp ψR (cA.trans cB.symm) = 0 := by
    rw [psiDisp_eq_psi_periodShift ψR (cA.trans cB.symm), ← hwdef]
    rw [show Work.TorusCover.periodShift w
        = (2 * Real.pi) • (((w.1 : ℝ), (w.2 : ℝ)) : ℝ × ℝ) from by
          ext <;> simp [Work.TorusCover.periodShift, smul_eq_mul, mul_comm]]
    rw [map_smul, hψRZ w.1 w.2]
    have : ((Bc * w.1 - Ac * w.2 : ℤ) : ℝ) = 0 := by rw [hcoef]; simp
    rw [this, smul_zero]
  -- every winding of a curve in `A ∪ B` is killed
  have hkill : ∀ (γ : Work.CoreTopology.ClosedCurve P), (∀ t : ℝ, γ t ∈ A ∪ B) →
      ψR (((Work.SurgeryInvariance.windingOf P γ).1 : ℝ),
           ((Work.SurgeryInvariance.windingOf P γ).2 : ℝ)) = 0 :=
    fun γ hγ => winding_psi_eq_zero_of_two_component_inter hAc hBc hAop hBop hApc hBpc hVA hVB
      hK₁c hK₂c hK₁pc hK₂pc hinter ha₀ hb₀ cA hcA cB hcB ψR hψw γ hγ
  -- the rational functional with the same coefficients
  set ψQ : (ℚ × ℚ) →ₗ[ℚ] ℚ :=
    { toFun := fun p => (Bc : ℚ) * p.1 - (Ac : ℚ) * p.2
      map_add' := by intro p q; simp only [Prod.fst_add, Prod.snd_add]; ring
      map_smul' := by intro c p; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring } with hψQdef
  have hψQZ : ∀ k l : ℤ, ψQ (((k : ℤ) : ℚ), ((l : ℤ) : ℚ)) = ((Bc * k - Ac * l : ℤ) : ℚ) := by
    intro k l
    rw [hψQdef]
    show (Bc : ℚ) * (k : ℚ) - (Ac : ℚ) * (l : ℚ) = ((Bc * k - Ac * l : ℤ) : ℚ)
    push_cast
    ring
  have hker : Work.SurgeryInvariance.WindingSpan P (A ∪ B) ≤ LinearMap.ker ψQ := by
    rw [Work.SurgeryInvariance.WindingSpan, Submodule.span_le]
    rintro v ⟨γ, hγ, rfl⟩
    change ψQ ((((Work.SurgeryInvariance.windingOf P γ).1 : ℤ) : ℚ),
      (((Work.SurgeryInvariance.windingOf P γ).2 : ℤ) : ℚ)) = 0
    have hR := hkill γ hγ
    have hZ : Bc * (Work.SurgeryInvariance.windingOf P γ).1
        - Ac * (Work.SurgeryInvariance.windingOf P γ).2 = 0 := by
      have hcast : (((Bc * (Work.SurgeryInvariance.windingOf P γ).1
          - Ac * (Work.SurgeryInvariance.windingOf P γ).2 : ℤ)) : ℝ) = 0 := by
        rw [← hψRZ (Work.SurgeryInvariance.windingOf P γ).1
          (Work.SurgeryInvariance.windingOf P γ).2]
        exact hR
      exact_mod_cast hcast
    rw [hψQZ, hZ, Int.cast_zero]
  have hψQne : ψQ ≠ 0 := by
    intro h0
    have h1 : ((Bc : ℚ)) = 0 := by
      have hc := congrArg (fun f : (ℚ × ℚ) →ₗ[ℚ] ℚ => f ((1 : ℚ), (0 : ℚ))) h0
      simp only [LinearMap.zero_apply] at hc
      rw [hψQdef] at hc
      simpa using hc
    have h2 : ((Ac : ℚ)) = 0 := by
      have hc := congrArg (fun f : (ℚ × ℚ) →ₗ[ℚ] ℚ => f ((0 : ℚ), (1 : ℚ))) h0
      simp only [LinearMap.zero_apply] at hc
      rw [hψQdef] at hc
      simpa using hc
    apply hne
    have hB : Bc = 0 := by exact_mod_cast h1
    have hA : Ac = 0 := by exact_mod_cast h2
    rw [hA, hB]; rfl
  have hne_top : Work.SurgeryInvariance.WindingSpan P (A ∪ B) ≠ ⊤ := by
    intro htop
    have hkertop : LinearMap.ker ψQ = ⊤ := le_antisymm le_top (htop ▸ hker)
    exact hψQne (LinearMap.ker_eq_top.mp hkertop)
  exact exists_ne_zero_inf_span_le_of_ne_top _ hne_top

end Work.PinchLemma3.ClosedDiscA

import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.opArc_opArc
import Submission.Work.BourgainPlan.IonescuWainger.opArc_arcShift
import Submission.Work.BourgainPlan.IonescuWainger.opArc_l2_endpoint_strata
import Submission.Work.BourgainPlan.IonescuWainger.OpArcLinear

namespace Work.IonescuWainger

open MeasureTheory ENNReal
open scoped ENNReal BigOperators
open Work.BourgainPlan.IonescuWainger

/-- **Tao's `ortho`(i) for the shifted strata arcs.**  If `A₀ ⊆ S` has `A₀.card ≤ k` and
`α ∈ Σ_{(A₀)} = strataCompFinset S k A₀`, then the points of the shifted arc set
`α + Σ_{A₀} = arcShift (sigmaStrataFinset A₀) α` are `1/qmax^{2k}`-separated.

Indeed each `γ ∈ Σ_{A₀}` is a rational point `arcPt (QA B) b` with `B ⊆ S`, `B.card ≤ k`
(`exists_arcPt_of_strataPairSet`), and distinct such points are `1/qmax^{2k}`-separated by
`sigmaLe_separation`; since the shift by `α` is common, it does not affect the distances. -/
theorem arcShift_sigmaStrataFinset_separation {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q) {k : ℕ} {qmax : ℕ}
    (hmax : ∀ q ∈ S, q ≤ qmax) {A₀ : Finset ℕ} (hA₀ : A₀ ⊆ S) (hk₀ : A₀.card ≤ k)
    {α : Work.BourgainPlan.IonescuWainger.Circle}
    (hα : α ∈ Work.BourgainPlan.IonescuWainger.strataCompFinset S k A₀)
    {β β' : Work.BourgainPlan.IonescuWainger.Circle}
    (hβ : β ∈ Work.BourgainPlan.IonescuWainger.arcShift
      (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A₀) α)
    (hβ' : β' ∈ Work.BourgainPlan.IonescuWainger.arcShift
      (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A₀) α)
    (hne : β ≠ β') :
    1 / (qmax : ℝ) ^ (2 * k) ≤ ‖β - β'‖ := by
  have hp : (A₀, α) ∈ Work.BourgainPlan.IonescuWainger.strataCompPairSet S k :=
    Work.BourgainPlan.IonescuWainger.mem_strataCompPairSet.mpr ⟨hA₀, hk₀, hα⟩
  rw [Work.BourgainPlan.IonescuWainger.mem_arcShift] at hβ hβ'
  obtain ⟨γ, hγ, rfl⟩ := hβ
  obtain ⟨γ', hγ', rfl⟩ := hβ'
  obtain ⟨B, b, hB, hkB, hBeq⟩ :=
    Work.BourgainPlan.IonescuWainger.exists_arcPt_of_strataPairSet h2 hS hp hγ
  obtain ⟨B', b', hB', hkB', hB'eq⟩ :=
    Work.BourgainPlan.IonescuWainger.exists_arcPt_of_strataPairSet h2 hS hp hγ'
  have hne' : Work.BourgainPlan.IonescuWainger.arcPt (Work.BourgainPlan.IonescuWainger.QA B) b ≠
      Work.BourgainPlan.IonescuWainger.arcPt (Work.BourgainPlan.IonescuWainger.QA B') b' := fun hc =>
    hne (by rw [hBeq, hc, ← hB'eq])
  have hsep' := Work.BourgainPlan.IonescuWainger.sigmaLe_separation h2 hS hB hB' hkB hkB' hmax hne'
  rwa [← hBeq, ← hB'eq] at hsep'

-- Design note: Submission/Work/BourgainPlan/IonescuWainger/A6_ASSEMBLY_GUIDE.md (read it first).
theorem main_real_of_inputs {S : Finset ℕ} (h2S : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {k r : ℕ} (hr : 2 ≤ r) (hk : 1 ≤ k) {qmax : ℕ}
    (hmax : ∀ q ∈ S, q ≤ qmax) (hqmax : 1 ≤ qmax)
    {ε η : ℝ} (hε0 : 0 < ε) (hεη : ε + η < 1 / (qmax : ℝ) ^ (2 * k))
    (ψ φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
    (hψ : MeasureTheory.MemLp ψ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (hφ : MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (hψsupp : ∀ ξ : Work.BourgainPlan.IonescuWainger.Circle, ε < ‖ξ‖ → ψ ξ = 0)
    (hφsupp : ∀ ξ : Work.BourgainPlan.IonescuWainger.Circle, η < ‖ξ‖ → φ ξ = 0)
    (hφone : ∀ ξ : Work.BourgainPlan.IonescuWainger.Circle, ‖ξ‖ ≤ ε → φ ξ = 1)
    {εs : Finset ℕ → ℂ} (hεs : ∀ A, ‖εs A‖ ≤ 1) (f : ℤ →₀ ℂ)
    {C₁ W C₄ : ℝ} (hC₁ : 0 ≤ C₁) (hW : 0 ≤ W) (hC₄ : 0 ≤ C₄)
    (hstep1 : ∑' x : ℤ, ENNReal.ofReal (‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        εs A * Work.BourgainPlan.IonescuWainger.opArc ψ hψ
          (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A) (⇑f)
          (Work.BourgainPlan.IonescuWainger.memℓp_finsupp f) x‖ ^ (2 * r))
      ≤ ENNReal.ofReal C₁ *
        ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
          ∑' x : ℤ, (∑ α ∈ Work.BourgainPlan.IonescuWainger.strataCompFinset S k A₀,
              ENNReal.ofReal (‖Work.BourgainPlan.IonescuWainger.opArc ψ hψ
                (Work.BourgainPlan.IonescuWainger.arcShift
                  (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A₀) α) (⇑f)
                (Work.BourgainPlan.IonescuWainger.memℓp_finsupp f) x‖ ^ 2)) ^ (r : ℝ))
    (hstep3 : ∀ (A₀ : Finset ℕ), A₀ ⊆ S → A₀.card ≤ k →
      ∀ (F : ↥(Work.BourgainPlan.IonescuWainger.strataCompFinset S k A₀) → ℤ → ℂ)
        (hF : ∀ t, Memℓp (F t) 2),
      ∑' n : ℤ, (∑ α : ↥(Work.BourgainPlan.IonescuWainger.strataCompFinset S k A₀),
          ENNReal.ofReal (‖Work.BourgainPlan.IonescuWainger.opArc ψ hψ
            (Work.BourgainPlan.IonescuWainger.arcShift
              (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A₀) α.1)
            (F α) (hF α) n‖ ^ 2)) ^ (r : ℝ)
        ≤ ENNReal.ofReal W *
          ∑' n : ℤ, (∑ α : ↥(Work.BourgainPlan.IonescuWainger.strataCompFinset S k A₀),
            ENNReal.ofReal (‖F α n‖ ^ 2)) ^ (r : ℝ))
    (hstep4 : ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
        ∑' n : ℤ, (∑ α ∈ Work.BourgainPlan.IonescuWainger.strataCompFinset S k A₀,
            ENNReal.ofReal (‖Work.BourgainPlan.IonescuWainger.opArc φ hφ
              (Work.BourgainPlan.IonescuWainger.arcShift
                (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A₀) α) (⇑f)
              (Work.BourgainPlan.IonescuWainger.memℓp_finsupp f) n‖ ^ 2)) ^ (r : ℝ)
      ≤ ENNReal.ofReal C₄ * ∑' n : ℤ, ENNReal.ofReal (‖(⇑f : ℤ → ℂ) n‖ ^ (2 * r))) :
    ∑' n : ℤ, ENNReal.ofReal (‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        εs A * Work.BourgainPlan.IonescuWainger.opArc ψ hψ
          (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A) (⇑f)
          (Work.BourgainPlan.IonescuWainger.memℓp_finsupp f) n‖ ^ (2 * r))
      ≤ ENNReal.ofReal (C₁ * W * C₄) *
        ∑' n : ℤ, ENNReal.ofReal (‖(⇑f : ℤ → ℂ) n‖ ^ (2 * r)) := by
  classical
  -- ## Step 2: the insertion of the wide bump `φ` over each `A₀`
  have key : ∀ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
      (∑' n : ℤ, (∑ α ∈ strataCompFinset S k A₀,
          ENNReal.ofReal (‖opArc ψ hψ (arcShift (sigmaStrataFinset A₀) α) (⇑f)
            (memℓp_finsupp f) n‖ ^ 2)) ^ (r : ℝ))
        ≤ ENNReal.ofReal W *
          ∑' n : ℤ, (∑ α ∈ strataCompFinset S k A₀,
            ENNReal.ofReal (‖opArc φ hφ (arcShift (sigmaStrataFinset A₀) α) (⇑f)
              (memℓp_finsupp f) n‖ ^ 2)) ^ (r : ℝ) := by
    intro A₀ hA₀
    obtain ⟨hA₀pow, hk₀⟩ := Finset.mem_filter.mp hA₀
    have hA₀S : A₀ ⊆ S := Finset.mem_powerset.mp hA₀pow
    have hsepfun : ∀ α ∈ strataCompFinset S k A₀,
        ∀ β ∈ arcShift (sigmaStrataFinset A₀) α,
        ∀ β' ∈ arcShift (sigmaStrataFinset A₀) α, β ≠ β' →
          1 / (qmax : ℝ) ^ (2 * k) ≤ ‖β - β'‖ :=
      fun α hα β hβ β' hβ' hne =>
        arcShift_sigmaStrataFinset_separation h2S hS hmax hA₀S hk₀ hα hβ hβ' hne
    have h3 : (∑' n : ℤ, (∑ α : ↥(strataCompFinset S k A₀), ENNReal.ofReal
          (‖opArc ψ hψ (arcShift (sigmaStrataFinset A₀) α.1)
              (opArc φ hφ (arcShift (sigmaStrataFinset A₀) α.1) (⇑f) (memℓp_finsupp f))
              (opMul_memℓp (arcSymbolLp φ hφ (arcShift (sigmaStrataFinset A₀) α.1))
                (⇑f) (memℓp_finsupp f)) n‖ ^ 2)) ^ (r : ℝ))
        ≤ ENNReal.ofReal W * ∑' n : ℤ, (∑ α : ↥(strataCompFinset S k A₀),
            ENNReal.ofReal (‖opArc φ hφ (arcShift (sigmaStrataFinset A₀) α.1) (⇑f)
              (memℓp_finsupp f) n‖ ^ 2)) ^ (r : ℝ) :=
      hstep3 A₀ hA₀S hk₀ _ _
    have hleft : (∑' n : ℤ, (∑ α : ↥(strataCompFinset S k A₀), ENNReal.ofReal
          (‖opArc ψ hψ (arcShift (sigmaStrataFinset A₀) α.1)
              (opArc φ hφ (arcShift (sigmaStrataFinset A₀) α.1) (⇑f) (memℓp_finsupp f))
              (opMul_memℓp (arcSymbolLp φ hφ (arcShift (sigmaStrataFinset A₀) α.1))
                (⇑f) (memℓp_finsupp f)) n‖ ^ 2)) ^ (r : ℝ))
        = ∑' n : ℤ, (∑ α : ↥(strataCompFinset S k A₀),
            ENNReal.ofReal (‖opArc ψ hψ (arcShift (sigmaStrataFinset A₀) α.1) (⇑f)
              (memℓp_finsupp f) n‖ ^ 2)) ^ (r : ℝ) := by
      refine tsum_congr fun n => congrArg (fun z => z ^ (r : ℝ)) ?_
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [opArc_opArc hψsupp hφsupp hφone (hsepfun α.1 α.2) hεη (⇑f) (memℓp_finsupp f)]
    have hmid : (∑' n : ℤ, (∑ α : ↥(strataCompFinset S k A₀),
            ENNReal.ofReal (‖opArc ψ hψ (arcShift (sigmaStrataFinset A₀) α.1) (⇑f)
              (memℓp_finsupp f) n‖ ^ 2)) ^ (r : ℝ))
        = ∑' n : ℤ, (∑ α ∈ strataCompFinset S k A₀,
            ENNReal.ofReal (‖opArc ψ hψ (arcShift (sigmaStrataFinset A₀) α) (⇑f)
              (memℓp_finsupp f) n‖ ^ 2)) ^ (r : ℝ) := by
      refine tsum_congr fun n => congrArg (fun z => z ^ (r : ℝ)) ?_
      exact Finset.sum_coe_sort (strataCompFinset S k A₀)
        (fun α => ENNReal.ofReal (‖opArc ψ hψ (arcShift (sigmaStrataFinset A₀) α) (⇑f)
          (memℓp_finsupp f) n‖ ^ 2))
    have hright : (∑' n : ℤ, (∑ α : ↥(strataCompFinset S k A₀),
            ENNReal.ofReal (‖opArc φ hφ (arcShift (sigmaStrataFinset A₀) α.1) (⇑f)
              (memℓp_finsupp f) n‖ ^ 2)) ^ (r : ℝ))
        = ∑' n : ℤ, (∑ α ∈ strataCompFinset S k A₀,
            ENNReal.ofReal (‖opArc φ hφ (arcShift (sigmaStrataFinset A₀) α) (⇑f)
              (memℓp_finsupp f) n‖ ^ 2)) ^ (r : ℝ) := by
      refine tsum_congr fun n => congrArg (fun z => z ^ (r : ℝ)) ?_
      exact Finset.sum_coe_sort (strataCompFinset S k A₀)
        (fun α => ENNReal.ofReal (‖opArc φ hφ (arcShift (sigmaStrataFinset A₀) α) (⇑f)
          (memℓp_finsupp f) n‖ ^ 2))
    calc (∑' n : ℤ, (∑ α ∈ strataCompFinset S k A₀,
          ENNReal.ofReal (‖opArc ψ hψ (arcShift (sigmaStrataFinset A₀) α) (⇑f)
            (memℓp_finsupp f) n‖ ^ 2)) ^ (r : ℝ))
        = (∑' n : ℤ, (∑ α : ↥(strataCompFinset S k A₀),
            ENNReal.ofReal (‖opArc ψ hψ (arcShift (sigmaStrataFinset A₀) α.1) (⇑f)
              (memℓp_finsupp f) n‖ ^ 2)) ^ (r : ℝ)) := hmid.symm
      _ = (∑' n : ℤ, (∑ α : ↥(strataCompFinset S k A₀), ENNReal.ofReal
            (‖opArc ψ hψ (arcShift (sigmaStrataFinset A₀) α.1)
                (opArc φ hφ (arcShift (sigmaStrataFinset A₀) α.1) (⇑f) (memℓp_finsupp f))
                (opMul_memℓp (arcSymbolLp φ hφ (arcShift (sigmaStrataFinset A₀) α.1))
                  (⇑f) (memℓp_finsupp f)) n‖ ^ 2)) ^ (r : ℝ)) := hleft.symm
      _ ≤ ENNReal.ofReal W * ∑' n : ℤ, (∑ α : ↥(strataCompFinset S k A₀),
            ENNReal.ofReal (‖opArc φ hφ (arcShift (sigmaStrataFinset A₀) α.1) (⇑f)
              (memℓp_finsupp f) n‖ ^ 2)) ^ (r : ℝ) := h3
      _ = ENNReal.ofReal W * ∑' n : ℤ, (∑ α ∈ strataCompFinset S k A₀,
            ENNReal.ofReal (‖opArc φ hφ (arcShift (sigmaStrataFinset A₀) α) (⇑f)
              (memℓp_finsupp f) n‖ ^ 2)) ^ (r : ℝ) := by
          rw [hright]
  -- ## Step 3: sum the per-`A₀` bounds (step 3 with `F = Op_φ f`)
  have hsum : (∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
        ∑' n : ℤ, (∑ α ∈ strataCompFinset S k A₀,
          ENNReal.ofReal (‖opArc ψ hψ (arcShift (sigmaStrataFinset A₀) α) (⇑f)
            (memℓp_finsupp f) n‖ ^ 2)) ^ (r : ℝ))
      ≤ ENNReal.ofReal W * ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
        ∑' n : ℤ, (∑ α ∈ strataCompFinset S k A₀,
          ENNReal.ofReal (‖opArc φ hφ (arcShift (sigmaStrataFinset A₀) α) (⇑f)
            (memℓp_finsupp f) n‖ ^ 2)) ^ (r : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun A₀ hA₀ => key A₀ hA₀
  -- ## Step 4: combine with `hstep1` and `hstep4`
  calc ∑' n : ℤ, ENNReal.ofReal (‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        εs A * opArc ψ hψ (sigmaStrataFinset A) (⇑f) (memℓp_finsupp f) n‖ ^ (2 * r))
      ≤ ENNReal.ofReal C₁ * (∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
          ∑' n : ℤ, (∑ α ∈ strataCompFinset S k A₀,
            ENNReal.ofReal (‖opArc ψ hψ (arcShift (sigmaStrataFinset A₀) α) (⇑f)
              (memℓp_finsupp f) n‖ ^ 2)) ^ (r : ℝ)) := hstep1
    _ ≤ ENNReal.ofReal C₁ * (ENNReal.ofReal W *
          ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
            ∑' n : ℤ, (∑ α ∈ strataCompFinset S k A₀,
              ENNReal.ofReal (‖opArc φ hφ (arcShift (sigmaStrataFinset A₀) α) (⇑f)
                (memℓp_finsupp f) n‖ ^ 2)) ^ (r : ℝ)) :=
        mul_le_mul_right hsum (ENNReal.ofReal C₁)
    _ ≤ ENNReal.ofReal C₁ * (ENNReal.ofReal W * (ENNReal.ofReal C₄ *
          ∑' n : ℤ, ENNReal.ofReal (‖(⇑f : ℤ → ℂ) n‖ ^ (2 * r)))) :=
        mul_le_mul_right (mul_le_mul_right hstep4 (ENNReal.ofReal W)) (ENNReal.ofReal C₁)
    _ = ENNReal.ofReal (C₁ * W * C₄) *
        ∑' n : ℤ, ENNReal.ofReal (‖(⇑f : ℤ → ℂ) n‖ ^ (2 * r)) := by
        rw [show C₁ * W * C₄ = (C₁ * W) * C₄ by ring,
          ENNReal.ofReal_mul (mul_nonneg hC₁ hW), ENNReal.ofReal_mul hC₁]
        ring

end Work.IonescuWainger

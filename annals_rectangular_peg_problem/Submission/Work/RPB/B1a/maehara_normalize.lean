import Mathlib
import Submission.Work.RPB1a.Caratheodory.Brouwer.MaeharaDefs
import Submission.Work.RPB.B1a.maehara_diametral
import Submission.Work.RPB.B1a.maehara_lens
import Submission.Work.RPB.B1a.maehara_similarity

set_option autoImplicit false

namespace Work.RPB.B1a

open Set Metric

noncomputable section

theorem maehara_normalize (γ : Circle → ℝ × ℝ) (hγ : Continuous γ)
    (hinj : Function.Injective γ) :
    ∃ e : (ℝ × ℝ) ≃ₜ (ℝ × ℝ),
      (∀ S : Set (ℝ × ℝ), Bornology.IsBounded S → Bornology.IsBounded (e '' S)) ∧
      (∀ S : Set (ℝ × ℝ), Bornology.IsBounded S → Bornology.IsBounded (e.symm '' S)) ∧
      Set.range (fun c : Circle => e (γ c)) ⊆ Work.RPB1a.Caratheodory.Brouwer.rect ∧
      (((-1 : ℝ), (0 : ℝ)) ∈ Set.range (fun c : Circle => e (γ c))) ∧
      (((1 : ℝ), (0 : ℝ)) ∈ Set.range (fun c : Circle => e (γ c))) ∧
      (Set.range (fun c : Circle => e (γ c)) ∩ Work.RPB1a.Caratheodory.Brouwer.rectB =
        {((-1 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))}) := by
  -- Transport the curve to `ℂ`.
  let γC : Circle → ℂ := fun c => Complex.equivRealProdCLM.symm (γ c)
  have hγCcont : Continuous γC := Complex.equivRealProdCLM.symm.continuous.comp hγ
  have hinjC : Function.Injective γC :=
    (Complex.equivRealProdCLM.symm.injective).comp hinj
  -- Diametral pair.
  obtain ⟨α, β, hαmem, hβmem, hpos, hmax⟩ := maehara_diametral γC hγCcont hinjC
  have hab : α ≠ β := (sub_ne_zero.mp (norm_pos_iff.mp hpos)).symm
  have hbα : β - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hαmem' : α ∈ Set.range γC := hαmem
  have hβmem' : β ∈ Set.range γC := hβmem
  obtain ⟨c₀, hc₀⟩ := hαmem
  obtain ⟨c₁, hc₁⟩ := hβmem
  -- The normalising similarity.
  obtain ⟨e, hbdd, hbdd', heα, heβ, hform⟩ := maehara_similarity α β hab
  have heq : ∀ z : ℂ, Complex.equivRealProd z = Complex.equivRealProdCLM z :=
    fun z => by simp [Complex.equivRealProd_apply, Complex.equivRealProdCLM_apply]
  have hgam : ∀ c : Circle, Complex.equivRealProd (γC c) = γ c := by
    intro c
    rw [heq]
    show Complex.equivRealProdCLM (Complex.equivRealProdCLM.symm (γ c)) = γ c
    rw [ContinuousLinearEquiv.apply_symm_apply]
  refine ⟨e, hbdd, hbdd', ?_, ?_, ?_, ?_⟩
  · -- `range (e ∘ γ) ⊆ rect`
    intro x hx
    obtain ⟨c, rfl⟩ := hx
    have hkey : (2:ℂ)*(γC c - (α+β)/2)/(β-α) = 2*((γC c - α)/(β-α)) - 1 := by
      field_simp
      ring
    have h1 : ‖(γC c - α)/(β-α)‖ ≤ 1 := by
      rw [norm_div]
      exact (div_le_one hpos).mpr (hmax (γC c) (Set.mem_range_self c) α hαmem')
    have h2 : ‖(γC c - α)/(β-α) - 1‖ ≤ 1 := by
      have hsub : (γC c - α)/(β-α) - 1 = (γC c - β)/(β-α) := by
        field_simp
        ring
      rw [hsub, norm_div]
      exact (div_le_one hpos).mpr (hmax (γC c) (Set.mem_range_self c) β hβmem')
    obtain ⟨l1, l2, l3, l4, -, -, -, -⟩ :=
      maehara_lens ((γC c - α)/(β-α)) h1 h2
    simp only [Work.RPB1a.Caratheodory.Brouwer.mem_rect]
    rw [← hgam c, hform, hkey]
    exact ⟨l1, l2, l3, l4⟩
  · -- `(-1,0) ∈ range (e ∘ γ)`
    exact ⟨c₀, by show e (γ c₀) = (-1, 0); rw [← hgam c₀, hc₀, heα]⟩
  · -- `(1,0) ∈ range (e ∘ γ)`
    exact ⟨c₁, by show e (γ c₁) = (1, 0); rw [← hgam c₁, hc₁, heβ]⟩
  · -- the boundary intersection
    apply Set.Subset.antisymm
    · rintro y ⟨hy1, hy2⟩
      obtain ⟨c, rfl⟩ := hy1
      dsimp only at hy2 ⊢
      have hkey : (2:ℂ)*(γC c - (α+β)/2)/(β-α) = 2*((γC c - α)/(β-α)) - 1 := by
        field_simp
        ring
      have h1 : ‖(γC c - α)/(β-α)‖ ≤ 1 := by
        rw [norm_div]
        exact (div_le_one hpos).mpr (hmax (γC c) (Set.mem_range_self c) α hαmem')
      have h2 : ‖(γC c - α)/(β-α) - 1‖ ≤ 1 := by
        have hsub : (γC c - α)/(β-α) - 1 = (γC c - β)/(β-α) := by
          field_simp
          ring
        rw [hsub, norm_div]
        exact (div_le_one hpos).mpr (hmax (γC c) (Set.mem_range_self c) β hβmem')
      obtain ⟨-, -, -, -, he1, he2, he3, he4⟩ :=
        maehara_lens ((γC c - α)/(β-α)) h1 h2
      rw [← hgam c, hform, hkey] at hy2
      simp only [Work.RPB1a.Caratheodory.Brouwer.mem_rectB] at hy2
      rcases hy2 with h | h | h | h
      · -- `x = -1`
        have hval : e (γ c) = ((-1:ℝ), (0:ℝ)) := by
          have hp : (γC c - α)/(β-α) = 0 := he2 h
          have hzc : γC c = α := by
            have hz : γC c - α = 0 := by
              rcases div_eq_zero_iff.mp hp with h' | h'
              · exact h'
              · exact absurd h' hbα
            exact sub_eq_zero.mp hz
          rw [← hgam c, hzc, heα]
        rw [hval]; simp
      · -- `x = 1`
        have hval : e (γ c) = ((1:ℝ), (0:ℝ)) := by
          have hp : (γC c - α)/(β-α) = 1 := he1 h
          have hzc : γC c = β := by
            have hmul := congrArg (fun w => w * (β-α)) hp
            rw [div_mul_cancel₀ _ hbα] at hmul
            linear_combination hmul
          rw [← hgam c, hzc, heβ]
        rw [hval]; simp
      · exact absurd h he4
      · exact absurd h he3
    · -- the two points are in the intersection
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact ⟨⟨c₀, by show e (γ c₀) = (-1, 0); rw [← hgam c₀, hc₀, heα]⟩,
          by simp [Work.RPB1a.Caratheodory.Brouwer.mem_rectB]⟩
      · exact ⟨⟨c₁, by show e (γ c₁) = (1, 0); rw [← hgam c₁, hc₁, heβ]⟩,
          by simp [Work.RPB1a.Caratheodory.Brouwer.mem_rectB]⟩

end

end Work.RPB.B1a

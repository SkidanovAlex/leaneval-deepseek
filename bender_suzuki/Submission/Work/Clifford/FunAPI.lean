import Submission.Work.Clifford.Orbit

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.FunAPI`: elementary API for the functions used in Clifford theory

Small lemmas about the principal character, inflation from `G ⧸ N`, the Frobenius twists
`powChar`/`autChar`, and the predicates `IsConstituentOf`, `Extends`, `LiesOver`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Classical

namespace Work.Clifford

universe u

variable {G : Type u} [Group G] [Fintype G]

/-! ### The principal character -/

theorem isClassFun_principalChar : IsClassFun (principalChar G) := fun _ _ => rfl

theorem cfInner_principalChar_right (f : G → ℂ) :
    cfInner f (principalChar G) = (Fintype.card G : ℂ)⁻¹ * ∑ x, f x := by
  simp [cfInner, principalChar]

theorem cfInner_principalChar_left (f : G → ℂ) :
    cfInner (principalChar G) f = (Fintype.card G : ℂ)⁻¹ * ∑ x, starRingEnd ℂ (f x) := by
  simp [cfInner, principalChar]

/-! ### Inflation from `G ⧸ N` -/

section Inflate

variable {N : Subgroup G} [N.Normal]

theorem inflateFun_apply (f : G ⧸ N → ℂ) (g : G) :
    inflateFun N f g = f (QuotientGroup.mk (s := N) g) := rfl

theorem quotientGroup_mk_mul_of_mem {n g : G} (hn : n ∈ N) :
    QuotientGroup.mk (s := N) (n * g) = QuotientGroup.mk (s := N) g := by
  rw [QuotientGroup.eq]
  have h : (n * g)⁻¹ * g = g⁻¹ * n⁻¹ * g := by group
  rw [h]
  simpa using Subgroup.Normal.conj_mem (inferInstance : N.Normal) n⁻¹ (N.inv_mem hn) g⁻¹

theorem quotientGroup_mk_mul_of_mem' {g n : G} (hn : n ∈ N) :
    QuotientGroup.mk (s := N) (g * n) = QuotientGroup.mk (s := N) g := by
  rw [QuotientGroup.eq]
  have h : (g * n)⁻¹ * g = n⁻¹ := by group
  rw [h]
  exact N.inv_mem hn

/-- Inflation of a class function on `G ⧸ N` is a class function on `G`. -/
theorem isClassFun_inflateFun {f : G ⧸ N → ℂ} (hf : IsClassFun f) :
    IsClassFun (inflateFun N f) := by
  intro g h
  change f (↑(h * g * h⁻¹) : G ⧸ N) = f (↑g : G ⧸ N)
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  exact hf _ _

/-- Inflation is constant on left cosets of `N`. -/
theorem inflateFun_mul_of_mem (f : G ⧸ N → ℂ) {n : G} (hn : n ∈ N) (g : G) :
    inflateFun N f (n * g) = inflateFun N f g := by
  simp only [inflateFun, quotientGroup_mk_mul_of_mem hn]

/-- Inflation is constant on right cosets of `N`. -/
theorem inflateFun_mul_of_mem' (f : G ⧸ N → ℂ) (g : G) {n : G} (hn : n ∈ N) :
    inflateFun N f (g * n) = inflateFun N f g := by
  simp only [inflateFun, quotientGroup_mk_mul_of_mem' hn]

theorem inflateFun_one : inflateFun N (1 : G ⧸ N → ℂ) = principalChar G := by
  ext g
  simp [inflateFun, principalChar]

theorem inflateFun_add (f g : G ⧸ N → ℂ) :
    inflateFun N (f + g) = inflateFun N f + inflateFun N g := rfl

theorem inflateFun_mul (f g : G ⧸ N → ℂ) :
    inflateFun N (f * g) = inflateFun N f * inflateFun N g := rfl

theorem inflateFun_smul (c : ℂ) (f : G ⧸ N → ℂ) :
    inflateFun N (c • f) = c • inflateFun N f := rfl

end Inflate

/-! ### Frobenius twists -/

@[simp] theorem autChar_refl_apply (χ : G → ℂ) : autChar (MulEquiv.refl G) χ = χ := by
  ext g
  simp [autChar]

theorem autChar_mul_apply (e₁ e₂ : G ≃* G) (χ : G → ℂ) :
    autChar (e₁ * e₂) χ = autChar e₁ (autChar e₂ χ) := by
  ext g
  show χ ((e₁ * e₂).symm g) = χ (e₂.symm (e₁.symm g))
  congr 1

@[simp] theorem powChar_one_apply (χ : G → ℂ) : powChar 1 χ = χ := by
  ext g
  simp [powChar]

theorem powChar_mul_apply (k l : ℕ) (χ : G → ℂ) :
    powChar (k * l) χ = powChar k (powChar l χ) := by
  ext g
  simp only [powChar]
  rw [pow_mul]

theorem isClassFun_powChar {χ : G → ℂ} (hχ : IsClassFun χ) (k : ℕ) :
    IsClassFun (powChar k χ) := by
  intro g h
  simp only [powChar]
  rw [show h * g * h⁻¹ = h * g * h⁻¹ from rfl]
  have hpow : (h * g * h⁻¹) ^ k = h * g ^ k * h⁻¹ := by
    rw [← MulAut.conj_apply h g, ← map_pow (MulAut.conj h) g k, MulAut.conj_apply h (g ^ k)]
  rw [hpow]
  exact hχ (g ^ k) h

theorem isClassFun_autChar {χ : G → ℂ} (hχ : IsClassFun χ) (e : G ≃* G) :
    IsClassFun (autChar e χ) := by
  intro g h
  simp only [autChar]
  rw [show e.symm (h * g * h⁻¹) = e.symm h * e.symm g * (e.symm h)⁻¹ by simp [map_mul]]
  exact hχ (e.symm g) (e.symm h)

/-! ### Constituents, extensions -/

theorem isConstituentOf_iff {H : Type*} [Group H] [Fintype H] {θ f : H → ℂ} :
    IsConstituentOf θ f ↔ cfInner f θ ≠ 0 := Iff.rfl

theorem extents_iff {N : Subgroup G} {χ : G → ℂ} {θ : N → ℂ} :
    Extends N χ θ ↔ resFun N χ = θ := Iff.rfl

theorem liesOver_iff {N T : Subgroup G} {h : N ≤ T} {θ : N → ℂ} {ψ : T → ℂ} :
    LiesOver N T h θ ψ ↔ IsConstituentOf θ (resFunOfLe h ψ) := Iff.rfl

/-- The class function `f` lies over `θ` iff some constituent does; monotonicity of `θ ↦ ⟪f,θ⟫`. -/
theorem isConstituentOf_add_left {H : Type*} [Group H] [Fintype H] {θ f g : H → ℂ} :
    IsConstituentOf θ (f + g) ↔ cfInner f θ + cfInner g θ ≠ 0 := by
  simp only [IsConstituentOf, cfInner_add_left]

end Work.Clifford

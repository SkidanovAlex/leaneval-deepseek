import Mathlib
import Submission.Work.Coprime.Basic
import Submission.Work.Frobenius.Complement.crossed_hom_coboundary_of_solvable

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Pointwise

namespace Work.Coprime

/-- An automorphism of `N` carrying a subgroup `P` to itself carries `N_N(P)` to itself. -/
private theorem normalizer_smul_eq_self {A N : Type*} [Group A] [Group N]
    [MulDistribMulAction A N] (a : A) {P : Subgroup N} (hP : a • P = P) :
    a • Subgroup.normalizer (P : Set N) = Subgroup.normalizer (P : Set N) := by
  have h1 : ∀ x : N, (x ∈ P) ↔ (a⁻¹ • x ∈ P) := fun x => by
    rw [← Subgroup.mem_pointwise_smul_iff_inv_smul_mem (a := a) (S := P), hP]
  have h2 : ∀ x : N, (a • x ∈ P) ↔ (x ∈ P) := fun x => by
    rw [h1 (a • x), inv_smul_smul]
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    rw [Subgroup.mem_normalizer_iff] at hx ⊢
    intro y
    have key := hx (a⁻¹ • y)
    have hconj : (a⁻¹ • x) * (a⁻¹ • y) * (a⁻¹ • x)⁻¹ = a⁻¹ • (x * y * x⁻¹) := by
      rw [smul_mul', smul_mul', smul_inv']
    rw [← h1 y, hconj, ← h1 (x * y * x⁻¹)] at key
    exact key
  · intro x hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    rw [Subgroup.mem_normalizer_iff] at hx ⊢
    intro y
    have key := hx (a • y)
    have hconj : a⁻¹ • (x * (a • y) * x⁻¹) = (a⁻¹ • x) * y * (a⁻¹ • x)⁻¹ := by
      rw [smul_mul', smul_mul', smul_inv', inv_smul_smul]
    rw [h2 y, h1 (x * (a • y) * x⁻¹), hconj] at key
    exact key

/-- **Coprime action, solvable case.**  Two `A`-invariant subgroups of `N` that are conjugate
(one is the image of the other under conjugation by `x₀`) are conjugate by an element of `C_N(A)`,
when `A` is finite solvable and `|A|`, `|N|` are coprime. -/
theorem conj_fixed_of_invariant {A N : Type*} [Group A] [Group N] [Finite A] [Finite N]
    [MulDistribMulAction A N] (hsol : Group.IsSolvable A) (hcop : (Nat.card A).Coprime (Nat.card N))
    {P P' : Subgroup N} (hP : ∀ a : A, ∀ x : N, (x ∈ P ↔ a • x ∈ P))
    (hP' : ∀ a : A, ∀ x : N, (x ∈ P' ↔ a • x ∈ P'))
    {x₀ : N} (hx₀ : P' = P.map (MulAut.conj x₀).toMonoidHom) :
    ∃ c : N, (∀ a : A, a • c = c) ∧ P' = P.map (MulAut.conj c).toMonoidHom := by
  classical
  have hPsmul : ∀ a : A, a • P = P := by
    intro a
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    exact (hP a⁻¹ x).symm
  have hF1 : ∀ y : N, y ∈ P' ↔ x₀⁻¹ * y * x₀ ∈ P := by
    intro y
    rw [hx₀, Subgroup.mem_map]
    constructor
    · rintro ⟨p, hp, hpeq⟩
      have hpe : x₀⁻¹ * y * x₀ = p := by
        rw [← hpeq]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rwa [hpe]
    · rintro hy
      exact ⟨x₀⁻¹ * y * x₀, hy, by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group⟩
  let M : Subgroup N := Subgroup.normalizer ((P : Subgroup N) : Set N)
  have hMinv : ∀ a : A, a • M = M := fun a => normalizer_smul_eq_self a (hPsmul a)
  haveI hMI : FT.IsInvariant A M := ⟨hMinv⟩
  have hηmem : ∀ a : A, x₀⁻¹ * (a • x₀) ∈ M := by
    intro a
    show x₀⁻¹ * (a • x₀) ∈ Subgroup.normalizer ((P : Subgroup N) : Set N)
    rw [Subgroup.mem_normalizer_iff]
    intro p
    have hconv : (a • x₀) * p * (a • x₀)⁻¹ = a • (x₀ * (a⁻¹ • p) * x₀⁻¹) := by
      rw [smul_mul', smul_mul', smul_inv', smul_inv_smul]
    have hsub : (x₀⁻¹ * (a • x₀)) * p * (x₀⁻¹ * (a • x₀))⁻¹
        = x₀⁻¹ * ((a • x₀) * p * (a • x₀)⁻¹) * x₀ := by group
    rw [hsub, hconv, ← hF1 (a • (x₀ * (a⁻¹ • p) * x₀⁻¹)),
      ← hP' a (x₀ * (a⁻¹ • p) * x₀⁻¹), hF1 (x₀ * (a⁻¹ • p) * x₀⁻¹),
      show x₀⁻¹ * (x₀ * (a⁻¹ • p) * x₀⁻¹) * x₀ = a⁻¹ • p from by group]
    exact hP a⁻¹ p
  let η : A → ↥M := fun a => ⟨x₀⁻¹ * (a • x₀), hηmem a⟩
  have hη1 : η 1 = 1 := by ext; simp [η]
  have hηcross : ∀ a b : A, η (a * b) = η a * (a • η b) := by
    intro a b
    ext
    simp only [η, Subgroup.coe_mul, FT.coe_subgroup_smul, mul_smul, smul_mul',
      smul_inv']
    group
  have hcopM : (Nat.card A).Coprime (Nat.card ↥M) :=
    hcop.coprime_dvd_right ⟨M.index, (Subgroup.card_mul_index M).symm⟩
  obtain ⟨m, hm⟩ :=
    Work.Frobenius.Complement.crossed_hom_coboundary_of_solvable (M := ↥M) hsol hcopM η hη1 hηcross
  refine ⟨x₀ * (m : N), ?_, ?_⟩
  · intro a
    have hmv := congrArg Subtype.val (hm a)
    simp only [η, Subgroup.coe_mul, Subgroup.coe_inv, FT.coe_subgroup_smul] at hmv
    have h1 : a • x₀ = x₀ * ((m : N) * (a • (m : N))⁻¹) := by
      rw [← hmv]; group
    rw [smul_mul', h1]
    group
  · rw [hx₀]
    have hmP : P.map (MulAut.conj (m : N)).toMonoidHom = P :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp m.2
    have hmul : (MulAut.conj (x₀ * (m : N))).toMonoidHom
        = ((MulAut.conj x₀).toMonoidHom).comp ((MulAut.conj (m : N)).toMonoidHom) := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hmul, ← Subgroup.map_map, hmP]

end Work.Coprime

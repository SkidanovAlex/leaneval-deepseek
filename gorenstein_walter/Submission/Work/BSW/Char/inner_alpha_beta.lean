import Mathlib
import Submission.Work.BSW.Char.Alpha
import Submission.Work.BSW.Char.isTISubset_Kdiff

open scoped MatrixGroups

namespace Work.BSW.Char

open Subgroup Work.GW2
open OddOrder.RepresentationTheory

open Work.BSW

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-- `C_G(t)`. -/
abbrev centralizerT {G : Type*} [Group G] (t : G) : Subgroup G :=
  Subgroup.centralizer ({t} : Set G)

/-- `Invertible` for the cardinality of a subgroup of a finite group. -/
noncomputable def invertible_natCard_subgroup {G : Type*} [Group G] [Fintype G]
    (S : Subgroup G) : Invertible (Nat.card ↥S : ℂ) :=
  invertibleOfNonzero (by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr ⟨⟨⟨1, S.one_mem⟩⟩, inferInstance⟩)

/-- `(1 : ℂˣ) ≠ -1`. -/
theorem units_one_ne_neg_one : (1 : ℂˣ) ≠ -1 := by
  intro h
  have := congrArg (fun u : ℂˣ => (u : ℂ)) h
  rw [Units.val_one, Units.val_neg, Units.val_one] at this
  norm_num at this

/-- The class function `y ↦ θ y⁻¹`. -/
def thetaInv {G : Type*} [Group G] (θ : ClassFunction G ℂ) : ClassFunction G ℂ :=
  ⟨fun y => θ y⁻¹, fun g h => by
    have h1 : (h * g * h⁻¹)⁻¹ = h * g⁻¹ * h⁻¹ := by group
    show θ (h * g * h⁻¹)⁻¹ = θ g⁻¹
    rw [h1]
    exact θ.conj_eq g⁻¹ h⟩

@[simp] theorem thetaInv_apply {G : Type*} [Group G] (θ : ClassFunction G ℂ) (y : G) :
    thetaInv θ y = θ y⁻¹ := rfl

theorem thetaInv_add {G : Type*} [Group G] (θ θ' : ClassFunction G ℂ) :
    thetaInv (θ + θ') = thetaInv θ + thetaInv θ' := by
  ext y; rfl

theorem thetaInv_sub {G : Type*} [Group G] (θ θ' : ClassFunction G ℂ) :
    thetaInv (θ - θ') = thetaInv θ - thetaInv θ' := by
  ext y; rfl

theorem thetaInv_lin {G : Type*} [Group G] (χ : G →* ℂˣ) :
    thetaInv (linearClassFunction χ) = linearClassFunction χ⁻¹ := by
  ext y
  show (χ y⁻¹ : ℂ) = ((χ⁻¹) y : ℂ)
  simp

/-- For a normal subgroup `N ⊴ H` whose quotient has order two — witnessed by `σ : H` with
`σ * σ = 1`, `σ ∉ N` and the covering property `hcover : b ∉ N → b * σ ∈ N` — and which `σ`
inverts (`hinv`), the class function induced from `N` to `H` evaluates on `N` as
`Ind_N^H ψ (m) = ψ m + ψ m⁻¹`. -/
theorem induce_apply_normal_index_two
    {H : Type*} [Group H] [Fintype H] {N : Subgroup H} [N.Normal]
    {σ : H} (hσ : σ * σ = 1) (hσN : σ ∉ N)
    (hcover : ∀ b : H, b ∉ N → b * σ ∈ N)
    (hinv : ∀ n : H, n ∈ N → σ * n * σ⁻¹ = n⁻¹)
    [Invertible (Nat.card H : ℂ)] [Invertible (Nat.card ↥N : ℂ)]
    (ψ : ClassFunction ↥N ℂ) (m : ↥N) :
    ClassFunction.induce N ψ (m : H) = ψ m + ψ ⟨(m : H)⁻¹, N.inv_mem m.2⟩ := by
  classical
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_left hσ
  set F : H → ℂ := fun x =>
    ψ ⟨x⁻¹ * (m : H) * x, (inferInstance : N.Normal).conj_mem' (m : H) m.2 x⟩ with hF
  have hterm : ∀ x : H, ClassFunction.induceTerm N ψ x (m : H) = F x := by
    intro x
    rw [ClassFunction.induceTerm_of_mem ψ
      ((inferInstance : N.Normal).conj_mem' (m : H) m.2 x)]
  rw [ClassFunction.induce_apply, Finset.sum_congr rfl (fun x _ => hterm x)]
  have hvalN : ∀ a : ↥N, F (a : H) = ψ m := by
    intro a
    rw [hF]
    show ψ ⟨(a : H)⁻¹ * (m : H) * (a : H), _⟩ = ψ m
    have he : (⟨(a : H)⁻¹ * (m : H) * (a : H),
        (inferInstance : N.Normal).conj_mem' (m : H) m.2 (a : H)⟩ : ↥N) = a⁻¹ * m * a :=
      Subtype.ext rfl
    rw [he]
    rw [show a⁻¹ * m * a = a⁻¹ * m * (a⁻¹)⁻¹ from by rw [inv_inv]]
    exact ψ.conj_eq m a⁻¹
  have hvalC : ∀ k : ↥N, F ((k : H) * σ) = ψ ⟨(m : H)⁻¹, N.inv_mem m.2⟩ := by
    intro k
    rw [hF]
    show ψ ⟨((k : H) * σ)⁻¹ * (m : H) * ((k : H) * σ), _⟩
      = ψ ⟨(m : H)⁻¹, N.inv_mem m.2⟩
    have hw : (⟨((k : H) * σ)⁻¹ * (m : H) * ((k : H) * σ),
        (inferInstance : N.Normal).conj_mem' (m : H) m.2 ((k : H) * σ)⟩ : ↥N) = k⁻¹ * m⁻¹ * k := by
      apply Subtype.ext
      show ((k : H) * σ)⁻¹ * (m : H) * ((k : H) * σ) = (k : H)⁻¹ * (m : H)⁻¹ * (k : H)
      rw [mul_inv_rev, hσinv]
      have h1 : σ * (k : H)⁻¹ * (m : H) * ((k : H) * σ)
          = σ * ((k : H)⁻¹ * (m : H) * (k : H)) * σ := by group
      rw [h1]
      have h2 : σ * ((k : H)⁻¹ * (m : H) * (k : H)) * σ
          = ((k : H)⁻¹ * (m : H) * (k : H))⁻¹ := by
        have h3 : σ * ((k : H)⁻¹ * (m : H) * (k : H)) * σ
            = σ * ((k : H)⁻¹ * (m : H) * (k : H)) * σ⁻¹ := by rw [hσinv]
        exact h3.trans (hinv _ (N.mul_mem (N.mul_mem (N.inv_mem k.2) m.2) k.2))
      rw [h2]
      group
    rw [hw]
    rw [show k⁻¹ * m⁻¹ * k = k⁻¹ * m⁻¹ * (k⁻¹)⁻¹ from by rw [inv_inv]]
    rw [ψ.conj_eq m⁻¹ k⁻¹]
    rfl
  have hexcl : ∀ k : ↥N, (k : H) * σ ∉ N := by
    intro k hk
    have h1 : (k : H)⁻¹ * ((k : H) * σ) ∈ N := N.mul_mem (N.inv_mem k.2) hk
    refine hσN ?_
    have h2 : σ = (k : H)⁻¹ * ((k : H) * σ) := by group
    rw [h2]; exact h1
  let e : ↥N ≃ {x : H // x ∉ N} :=
    { toFun := fun k => ⟨(k : H) * σ, hexcl k⟩
      invFun := fun a => ⟨(a : H) * σ, hcover (a : H) a.2⟩
      left_inv := by
        intro k
        apply Subtype.ext
        show ((k : H) * σ) * σ = (k : H)
        rw [mul_assoc, hσ, mul_one]
      right_inv := by
        intro a
        apply Subtype.ext
        show ((a : H) * σ) * σ = (a : H)
        rw [mul_assoc, hσ, mul_one] }
  have hsplit : (∑ x : H, F x)
      = (∑ a : ↥N, F (a : H)) + (∑ a : {x : H // x ∉ N}, F (a : H)) :=
    (Fintype.sum_subtype_add_sum_subtype (fun x : H => x ∈ N) F).symm
  rw [hsplit]
  have hNsum : (∑ a : ↥N, F (a : H)) = (Nat.card ↥N : ℂ) * ψ m := by
    rw [Finset.sum_congr rfl (fun a _ => hvalN a)]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  have hCsum : (∑ a : {x : H // x ∉ N}, F (a : H))
      = (Nat.card ↥N : ℂ) * ψ ⟨(m : H)⁻¹, N.inv_mem m.2⟩ := by
    rw [← Equiv.sum_comp e (fun a : {x : H // x ∉ N} => F (a : H))]
    rw [Finset.sum_congr rfl (fun k _ => by
      show F ((k : H) * σ) = ψ ⟨(m : H)⁻¹, N.inv_mem m.2⟩
      exact hvalC k)]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  rw [hNsum, hCsum, ← mul_add, ← mul_assoc, invOf_mul_self, one_mul]

/-- Orthonormality of `linearClassFunction`: two linear characters are orthonormal. -/
theorem inner_linearClassFunction {H : Type*} [Group H] [Finite H] [Fintype H]
    [Invertible (Nat.card H : ℂ)] (χ χ' : H →* ℂˣ) :
    (linearClassFunction χ).inner (linearClassFunction χ') = if χ = χ' then 1 else 0 := by
  by_cases hχ : χ = χ'
  · subst hχ
    rw [if_pos rfl, ← linearIrreducibleCharacter_coe χ,
      irr_cf_inner (linearIrreducibleCharacter χ).mem_irreducibleCharacters
        (linearIrreducibleCharacter χ).mem_irreducibleCharacters]
    simp
  · rw [if_neg hχ, ← linearIrreducibleCharacter_coe χ, ← linearIrreducibleCharacter_coe χ',
      irr_cf_inner (linearIrreducibleCharacter χ).mem_irreducibleCharacters
        (linearIrreducibleCharacter χ').mem_irreducibleCharacters]
    rw [if_neg]
    intro hh
    exact hχ (linearIrreducibleCharacter_injective (Subtype.ext hh))

/-- The three inner products over a finite group `H` of the class functions built from two linear
characters `ρ₁, ρ₂` (Bender 1974 §2). -/
theorem inner_lin_combinations {H : Type*} [Group H] [Fintype H]
    [Invertible (Nat.card H : ℂ)]
    (ρ₁ ρ₂ : H →* ℂˣ)
    (h1 : ρ₁ ≠ 1) (h2 : ρ₂ ≠ 1) (h1inv : ρ₁⁻¹ ≠ 1) (h2inv : ρ₂⁻¹ ≠ 1)
    (h1sq : ρ₁ * ρ₁ ≠ 1) (h2sq : ρ₂ * ρ₂ ≠ 1)
    (h12 : ρ₁ ≠ ρ₂) (h12inv : ρ₁ * ρ₂ ≠ 1) :
    (linearClassFunction (1 : H →* ℂˣ) - linearClassFunction ρ₁).inner
        ((linearClassFunction (1 : H →* ℂˣ) - linearClassFunction ρ₁) +
         (linearClassFunction (1 : H →* ℂˣ) - linearClassFunction ρ₁⁻¹)) = 3 ∧
    (linearClassFunction (1 : H →* ℂˣ) - linearClassFunction ρ₁).inner
        ((linearClassFunction ρ₁ - linearClassFunction ρ₂) +
         (linearClassFunction ρ₁⁻¹ - linearClassFunction ρ₂⁻¹)) = -1 ∧
    (linearClassFunction ρ₁ - linearClassFunction ρ₂).inner
        ((linearClassFunction ρ₁ - linearClassFunction ρ₂) +
         (linearClassFunction ρ₁⁻¹ - linearClassFunction ρ₂⁻¹)) = 2 := by
  have hδ : ∀ χ χ' : H →* ℂˣ,
      (linearClassFunction χ).inner (linearClassFunction χ') = if χ = χ' then 1 else 0 :=
    fun χ χ' => inner_linearClassFunction χ χ'
  have hself : ∀ χ : H →* ℂˣ, (linearClassFunction χ).inner (linearClassFunction χ) = 1 := by
    intro χ; rw [inner_linearClassFunction, if_pos rfl]
  have hne : ∀ χ χ' : H →* ℂˣ, χ ≠ χ' →
      (linearClassFunction χ).inner (linearClassFunction χ') = 0 := by
    intro χ χ' h; rw [inner_linearClassFunction, if_neg h]
  have hρ1inv : ρ₁ ≠ ρ₁⁻¹ := by
    intro hh
    have h2 : ρ₁ * ρ₁⁻¹ = 1 := mul_inv_cancel ρ₁
    rw [← hh] at h2
    exact h1sq h2
  have hρ2inv : ρ₂ ≠ ρ₂⁻¹ := by
    intro hh
    have h2 : ρ₂ * ρ₂⁻¹ = 1 := mul_inv_cancel ρ₂
    rw [← hh] at h2
    exact h2sq h2
  have hρ1ρ2inv : ρ₁ ≠ ρ₂⁻¹ := by
    intro hh
    refine h12inv ?_
    calc ρ₁ * ρ₂ = ρ₂⁻¹ * ρ₂ := by rw [hh]
      _ = 1 := inv_mul_cancel ρ₂
  have hρ2ρ1inv : ρ₂ ≠ ρ₁⁻¹ := by
    intro hh
    refine h12inv ?_
    calc ρ₁ * ρ₂ = ρ₁ * ρ₁⁻¹ := by rw [hh]
      _ = 1 := mul_inv_cancel ρ₁
  constructor
  · simp only [ClassFunction.inner_sub_left, ClassFunction.inner_add_right,
      ClassFunction.inner_sub_right]
    simp only [hself,
      hne (1 : H →* ℂˣ) ρ₁ (Ne.symm h1), hne (1 : H →* ℂˣ) ρ₁⁻¹ (Ne.symm h1inv),
      hne ρ₁ (1 : H →* ℂˣ) h1, hne ρ₁ ρ₁⁻¹ hρ1inv]
    norm_num
  constructor
  · simp only [ClassFunction.inner_sub_left, ClassFunction.inner_add_right,
      ClassFunction.inner_sub_right]
    simp only [hself,
      hne (1 : H →* ℂˣ) ρ₁ (Ne.symm h1), hne (1 : H →* ℂˣ) ρ₂ (Ne.symm h2),
      hne (1 : H →* ℂˣ) ρ₁⁻¹ (Ne.symm h1inv), hne (1 : H →* ℂˣ) ρ₂⁻¹ (Ne.symm h2inv),
      hne ρ₁ ρ₂ h12, hne ρ₁ ρ₁⁻¹ hρ1inv, hne ρ₁ ρ₂⁻¹ hρ1ρ2inv]
    norm_num
  · simp only [ClassFunction.inner_sub_left, ClassFunction.inner_add_right,
      ClassFunction.inner_sub_right]
    simp only [hself,
      hne ρ₁ ρ₂ h12, hne ρ₁ ρ₁⁻¹ hρ1inv, hne ρ₁ ρ₂⁻¹ hρ1ρ2inv,
      hne ρ₂ ρ₁ (Ne.symm h12), hne ρ₂ ρ₁⁻¹ hρ2ρ1inv, hne ρ₂ ρ₂⁻¹ hρ2inv]
    norm_num

/-- **Index-two induction norm.**  For a normal subgroup `N ⊴ H` with quotient of order two
(witnessed by `σ`, `hcover`) that `σ` inverts (`hinv`), inducing class functions from `N`
transported along an isomorphism `e : ↥N ≃* L` yields the norm
`⟨Ind ψ₁, Ind ψ₂⟩_H = ⟨θ₁, θ₂ + θ₂∘inv⟩_L`. -/
theorem inner_induce_normal_index_two
    {H : Type*} [Group H] [Fintype H] {N : Subgroup H} [N.Normal]
    {σ : H} (hσ : σ * σ = 1) (hσN : σ ∉ N)
    (hcover : ∀ b : H, b ∉ N → b * σ ∈ N)
    (hinv : ∀ n : H, n ∈ N → σ * n * σ⁻¹ = n⁻¹)
    [Invertible (Nat.card H : ℂ)] [Invertible (Nat.card ↥N : ℂ)]
    {L : Type*} [Group L] [Fintype L] [Invertible (Nat.card L : ℂ)]
    (e : ↥N ≃* L) (θ₁ θ₂ : ClassFunction L ℂ) :
    ClassFunction.inner (ClassFunction.induce N (ClassFunction.compHom e.toMonoidHom θ₁))
      (ClassFunction.induce N (ClassFunction.compHom e.toMonoidHom θ₂))
    = ClassFunction.inner θ₁ (θ₂ + thetaInv θ₂) := by
  classical
  rw [ClassFunction.inner_induce_eq_inner_restrict]
  have hres : ClassFunction.restrict N
        (ClassFunction.induce N (ClassFunction.compHom e.toMonoidHom θ₂))
      = ClassFunction.compHom e.toMonoidHom (θ₂ + thetaInv θ₂) := by
    ext m
    rw [ClassFunction.restrict_apply,
      induce_apply_normal_index_two hσ hσN hcover hinv
        (ClassFunction.compHom e.toMonoidHom θ₂) m]
    simp only [ClassFunction.compHom_apply, ClassFunction.add_apply, thetaInv_apply]
    rw [show e.toMonoidHom ⟨(m : H)⁻¹, N.inv_mem m.2⟩ = (e.toMonoidHom m)⁻¹ from by
      rw [show (⟨(m : H)⁻¹, N.inv_mem m.2⟩ : ↥N) = m⁻¹ from Subtype.ext rfl]
      exact map_inv e.toMonoidHom m]
  rw [hres]
  exact inner_compHom_of_mulEquiv e θ₁ (θ₂ + thetaInv θ₂)

/-- **Bender 1974, §2** (the Brauer–Suzuki isometry, pp. 230–231): the norms of the two induced
generalized characters.  With `t, s, K` as in `BSWHyps2` and linear characters `ρ₁, ρ₂` of `K`
with `ρ₁(t) = 1`, `ρ₂(t) = -1`, neither fixed by conjugation by `s` (`hs1`, `hs2`), the class
functions `α* = ind_K^G (1_K − ρ₁)` and `β* = ind_K^G (ρ₁ − ρ₂)` (`Work.BSW.alphaFun`,
`Work.BSW.betaFun`) satisfy `⟨α*,α*⟩ = 3`, `⟨α*,β*⟩ = -1`, `⟨β*,β*⟩ = 2`.

Route (see `Submission/Work/BSW/NOTES_BSW_order.md`, Step 2): writing `H = C_G(t) = K⟨s⟩` of order
`2k` and `α = ind_K^H (1_K − ρ₁)`, `β = ind_K^H (ρ₁ − ρ₂)` (class functions of `H` vanishing
outside `K`, with `α|_K = 2 − 2 Re ρ₁`, `β|_K = 2 Re ρ₁ − 2 Re ρ₂`), the
`ind_K^H` computation gives `⟨α,α⟩_H = 3`, `⟨α,β⟩_H = -1`, `⟨β,β⟩_H = 2`: with `u = Re ρ₁`,
`v = Re ρ₂` one has `Σ_K u = Σ_K v = 0`, `Σ_K u² = Σ_K v² = k/2` (the characters are not real
valued, i.e. `ρᵢ ≠ ρ̄ᵢ`, which is what `hs1`, `hs2` say) and `Σ_K uv = 0` (`h1`, `h2` force
`ρ₁ ≠ ρ₂` and `ρ₁ ≠ ρ̄₂`); hence `Σ_K (2 − 2u)² = 6k`, `Σ_K (2 − 2u)(2u − 2v) = −2k`,
`Σ_K (2u − 2v)² = 4k`, and dividing by `|H| = 2k` gives `3`, `-1`, `2`.  The Brauer–Suzuki TI
isometry `ClassFunction.inner_induce_eq_of_isTISubset` with normalizer bound `H = C_G(t)` and
TI-subset `A = K ∖ {1}` (`Work.BSW.Char.isTISubset_Kdiff`) carries these to the `G`-norms of the
`H`-induced characters; induction is transitive (`ClassFunction.induce_induce_subgroupOf`), so
`ind_H^G α = ind_K^G (1_K − ρ₁) = α*` (and likewise for `β*`).  Numerically checked on `K = C₆`
with `ρ₁ = ρ_{j=2}`, `ρ₂ = ρ_{j=1}` and on `K = C₄ × C₃`. -/
theorem inner_alpha_beta {G : Type} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {t s : G} {K : Subgroup G} [Invertible (Nat.card ↥K : ℂ)] (h : Work.GW2.BSWHyps2 G t s K)
    (ρ₁ ρ₂ : ↥K →* ℂˣ)
    (h1 : ρ₁ ⟨t, Work.BSW.t_mem_K h⟩ = 1) (h2 : ρ₂ ⟨t, Work.BSW.t_mem_K h⟩ = -1)
    (hs1 : ∃ y : ↥K, ρ₁ y ≠ ρ₁ (Work.BSW.conjHomK h y))
    (hs2 : ∃ y : ↥K, ρ₂ y ≠ ρ₂ (Work.BSW.conjHomK h y)) :
    (Work.BSW.alphaFun K ρ₁).inner (Work.BSW.alphaFun K ρ₁) = 3 ∧
      (Work.BSW.alphaFun K ρ₁).inner (Work.BSW.betaFun K ρ₁ ρ₂) = -1 ∧
      (Work.BSW.betaFun K ρ₁ ρ₂).inner (Work.BSW.betaFun K ρ₁ ρ₂) = 2 := by
  classical
  haveI : Invertible (Nat.card ↥(centralizerT t) : ℂ) := invertible_natCard_subgroup _
  haveI : Invertible (Nat.card ↥(K.subgroupOf (centralizerT t)) : ℂ) :=
    invertible_natCard_subgroup _
  have hKH : K ≤ centralizerT t := K_le_centralizer_t h
  set e : ↥(K.subgroupOf (centralizerT t)) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKH with he
  set θ₁ : ClassFunction ↥K ℂ :=
    linearClassFunction (1 : ↥K →* ℂˣ) - linearClassFunction ρ₁ with hθ₁
  set θ₂ : ClassFunction ↥K ℂ := linearClassFunction ρ₁ - linearClassFunction ρ₂ with hθ₂
  -- the nontriviality of the linear characters
  have hconj₁ : ∀ y : ↥K, ρ₁ (conjHomK h y) = (ρ₁ y)⁻¹ := by
    intro y
    have hc : (conjHomK h y : ↥K) = y⁻¹ := by
      apply Subtype.ext
      rw [conjHomK_apply, inverts_s_K h (y : G) y.2]
      rfl
    rw [hc, map_inv]
  have hconj₂ : ∀ y : ↥K, ρ₂ (conjHomK h y) = (ρ₂ y)⁻¹ := by
    intro y
    have hc : (conjHomK h y : ↥K) = y⁻¹ := by
      apply Subtype.ext
      rw [conjHomK_apply, inverts_s_K h (y : G) y.2]
      rfl
    rw [hc, map_inv]
  have hρ₁ne : ρ₁ ≠ 1 := by
    intro hc
    obtain ⟨y, hy⟩ := hs1
    rw [hconj₁ y, hc] at hy
    simpa using hy
  have hρ₂ne : ρ₂ ≠ 1 := by
    intro hc
    rw [hc] at h2
    have hcast := congrArg (fun u : ℂˣ => (u : ℂ)) h2
    simp only [MonoidHom.one_apply, Units.val_one, Units.val_neg] at hcast
    norm_num at hcast
  have hρ₁sq : ρ₁ * ρ₁ ≠ 1 := by
    intro hc
    obtain ⟨y, hy⟩ := hs1
    rw [hconj₁ y] at hy
    refine hy ?_
    have hy2 : ρ₁ y * ρ₁ y = 1 := by
      have hh := congrArg (fun f : ↥K →* ℂˣ => f y) hc
      rw [MonoidHom.mul_apply, MonoidHom.one_apply] at hh
      exact hh
    calc ρ₁ y = (ρ₁ y)⁻¹ * ((ρ₁ y) * (ρ₁ y)) := by group
      _ = (ρ₁ y)⁻¹ := by rw [hy2, mul_one]
  have hρ₂sq : ρ₂ * ρ₂ ≠ 1 := by
    intro hc
    obtain ⟨y, hy⟩ := hs2
    rw [hconj₂ y] at hy
    refine hy ?_
    have hy2 : ρ₂ y * ρ₂ y = 1 := by
      have hh := congrArg (fun f : ↥K →* ℂˣ => f y) hc
      rw [MonoidHom.mul_apply, MonoidHom.one_apply] at hh
      exact hh
    calc ρ₂ y = (ρ₂ y)⁻¹ * ((ρ₂ y) * (ρ₂ y)) := by group
      _ = (ρ₂ y)⁻¹ := by rw [hy2, mul_one]
  have hρ₁inv : ρ₁⁻¹ ≠ 1 := by
    intro hc
    refine hρ₁ne (MonoidHom.ext fun y => ?_)
    have hh : (ρ₁⁻¹) y = (1 : ↥K →* ℂˣ) y := by rw [hc]
    rw [MonoidHom.inv_apply, MonoidHom.one_apply] at hh
    calc ρ₁ y = ((ρ₁ y)⁻¹)⁻¹ := (inv_inv (ρ₁ y)).symm
      _ = 1 := by rw [hh, inv_one]
  have hρ₂inv : ρ₂⁻¹ ≠ 1 := by
    intro hc
    refine hρ₂ne (MonoidHom.ext fun y => ?_)
    have hh : (ρ₂⁻¹) y = (1 : ↥K →* ℂˣ) y := by rw [hc]
    rw [MonoidHom.inv_apply, MonoidHom.one_apply] at hh
    calc ρ₂ y = ((ρ₂ y)⁻¹)⁻¹ := (inv_inv (ρ₂ y)).symm
      _ = 1 := by rw [hh, inv_one]
  have h12 : ρ₁ ≠ ρ₂ := by
    intro hc
    have hh : ρ₁ ⟨t, t_mem_K h⟩ = ρ₂ ⟨t, t_mem_K h⟩ := by rw [hc]
    rw [h1, h2] at hh
    exact units_one_ne_neg_one hh
  have h12inv : ρ₁ * ρ₂ ≠ 1 := by
    intro hc
    have hh : (ρ₁ * ρ₂) ⟨t, t_mem_K h⟩ = (1 : ↥K →* ℂˣ) ⟨t, t_mem_K h⟩ := by rw [hc]
    rw [MonoidHom.mul_apply, h1, h2, MonoidHom.one_apply] at hh
    have hcast := congrArg (fun u : ℂˣ => (u : ℂ)) hh
    simp only [Units.val_mul, Units.val_neg, Units.val_one] at hcast
    norm_num at hcast
  -- the K-level inner products
  have h1inv : (1 : ↥K →* ℂˣ)⁻¹ = 1 := by
    ext y
    simp only [MonoidHom.inv_apply, MonoidHom.one_apply, inv_one]
  have hK₁ : ClassFunction.inner θ₁ (θ₁ + thetaInv θ₁) = 3 := by
    rw [hθ₁, thetaInv_sub, thetaInv_lin, thetaInv_lin, h1inv]
    exact (inner_lin_combinations ρ₁ ρ₂ hρ₁ne hρ₂ne hρ₁inv hρ₂inv hρ₁sq hρ₂sq h12 h12inv).1
  have hK₂ : ClassFunction.inner θ₁ (θ₂ + thetaInv θ₂) = -1 := by
    rw [hθ₁, hθ₂, thetaInv_sub, thetaInv_lin, thetaInv_lin]
    exact (inner_lin_combinations ρ₁ ρ₂ hρ₁ne hρ₂ne hρ₁inv hρ₂inv hρ₁sq hρ₂sq h12 h12inv).2.1
  have hK₃ : ClassFunction.inner θ₂ (θ₂ + thetaInv θ₂) = 2 := by
    rw [hθ₂, thetaInv_sub, thetaInv_lin, thetaInv_lin]
    exact (inner_lin_combinations ρ₁ ρ₂ hρ₁ne hρ₂ne hρ₁inv hρ₂inv hρ₁sq hρ₂sq h12 h12inv).2.2
  -- the index-two structure of `C_G(t)`
  have hσ : (⟨s, s_mem_centralizer_t h⟩ : ↥(centralizerT t)) * ⟨s, s_mem_centralizer_t h⟩ = 1 := by
    apply Subtype.ext
    show s * s = 1
    exact s_mul_self h
  have hσN : (⟨s, s_mem_centralizer_t h⟩ : ↥(centralizerT t)) ∉ K.subgroupOf (centralizerT t) := by
    rw [Subgroup.mem_subgroupOf]
    exact s_notMem_K h
  have hnrm : (zpowers s : Subgroup G) ≤ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      rw [inverts_s_K h k hk]
      exact K.inv_mem hk
    · intro hk
      have h4 : s * (s * k * s⁻¹) * s⁻¹ = k := by
        rw [s_inv h]
        calc s * (s * k * s) * s = (s * s) * k * (s * s) := by group
          _ = k := by rw [s_mul_self h]; group
      rw [← h4, inverts_s_K h (s * k * s⁻¹) hk]
      exact K.inv_mem hk
  have hcover : ∀ b : ↥(centralizerT t), b ∉ K.subgroupOf (centralizerT t) →
      b * ⟨s, s_mem_centralizer_t h⟩ ∈ K.subgroupOf (centralizerT t) := by
    intro b hb
    rw [Subgroup.mem_subgroupOf] at hb ⊢
    have hbH : (b : G) ∈ K ⊔ zpowers s := by
      simpa only [centralizer_t_eq h] using b.2
    have hmul : (b : G) ∈ ((K ⊔ zpowers s : Subgroup G) : Set G) := hbH
    rw [OddOrder.GroupTheory.coe_sup_eq_mul_of_le_normalizer hnrm] at hmul
    obtain ⟨k, hkK, y, hy, hky⟩ := hmul
    have hky' : k * y = (b : G) := by simpa using hky
    rcases mem_zpowers_s h hy with hy1 | hy2
    · exact absurd (by rw [← hky', hy1, mul_one]; exact hkK) hb
    · have hbs : (b : G) = k * s := by rw [← hky', hy2]
      rw [show ((b * (⟨s, s_mem_centralizer_t h⟩ : ↥(centralizerT t)) : ↥(centralizerT t)) : G) = k by
        show (b : G) * s = k
        rw [hbs, mul_assoc, s_mul_self h, mul_one]]
      exact hkK
  have hinv : ∀ n : ↥(centralizerT t), n ∈ K.subgroupOf (centralizerT t) →
      ⟨s, s_mem_centralizer_t h⟩ * n * ⟨s, s_mem_centralizer_t h⟩⁻¹ = n⁻¹ := by
    intro n hn
    rw [Subgroup.mem_subgroupOf] at hn
    apply Subtype.ext
    show s * (n : G) * s⁻¹ = (n : G)⁻¹
    exact inverts_s_K h n hn
  have hNnorm : (K.subgroupOf (centralizerT t)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKH]
    have hce : centralizerT t = K ⊔ zpowers s := centralizer_t_eq h
    rw [hce]
    refine sup_le ?_ ?_
    · exact Subgroup.le_normalizer
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_normalizer_iff.mpr (fun k => ⟨fun hk => by
        rw [inverts_s_K h k hk]; exact K.inv_mem hk, fun hk => by
        have h4 : s * (s * k * s⁻¹) * s⁻¹ = k := by
          rw [s_inv h]
          calc s * (s * k * s) * s = (s * s) * k * (s * s) := by group
            _ = k := by rw [s_mul_self h]; group
        rw [← h4, inverts_s_K h (s * k * s⁻¹) hk]
        exact K.inv_mem hk⟩)
  haveI := hNnorm
  -- transitivity of induction
  have hα : alphaFun K ρ₁ = ClassFunction.induce (centralizerT t)
      (ClassFunction.induce (K.subgroupOf (centralizerT t)) (ClassFunction.compHom e.toMonoidHom θ₁)) := by
    simp only [alphaFun]
    rw [← hθ₁, he]
    exact (induce_induce_subgroupOf hKH θ₁).symm
  have hβ : betaFun K ρ₁ ρ₂ = ClassFunction.induce (centralizerT t)
      (ClassFunction.induce (K.subgroupOf (centralizerT t)) (ClassFunction.compHom e.toMonoidHom θ₂)) := by
    simp only [betaFun]
    rw [← hθ₂, he]
    exact (induce_induce_subgroupOf hKH θ₂).symm
  -- vanishing off `K ∖ {1}`
  have hvanish : ∀ (θ : ClassFunction ↥K ℂ), θ 1 = 0 → ∀ x : ↥(centralizerT t),
      (x : G) ∉ ((K : Set G) \ {1}) →
      ClassFunction.induce (K.subgroupOf (centralizerT t))
        (ClassFunction.compHom e.toMonoidHom θ) x = 0 := by
    intro θ hθ1 x hx
    by_cases hxK : (x : G) ∈ K
    · have hx1 : (x : G) = 1 := by
        have : (x : G) ∈ ({1} : Set G) := by
          by_contra hne
          exact hx ⟨hxK, hne⟩
        exact Set.mem_singleton_iff.mp this
      have hxeq : x = 1 := Subtype.ext hx1
      rw [hxeq, ClassFunction.induce_apply_one]
      have hψ1 : ClassFunction.compHom e.toMonoidHom θ (1 : ↥(K.subgroupOf (centralizerT t))) = 0 := by
        rw [ClassFunction.compHom_apply, map_one, hθ1]
      rw [hψ1, mul_zero]
    · have hxN : x ∉ K.subgroupOf (centralizerT t) := by
        intro hmem
        exact hxK (by rwa [Subgroup.mem_subgroupOf] at hmem)
      by_contra hne
      exact hxN (ClassFunction.support_induce_subset_of_normal (K.subgroupOf (centralizerT t))
        (ClassFunction.compHom e.toMonoidHom θ) hne)
  have hθ₁1 : θ₁ 1 = 0 := by rw [hθ₁]; simp
  have hθ₂1 : θ₂ 1 = 0 := by rw [hθ₂]; simp
  -- the TI isometry at the level of `C_G(t)`
  have hTI : OddOrder.GroupTheory.IsTISubset ((K : Set G) \ {1}) (centralizerT t) :=
    isTISubset_Kdiff h
  have hmain₁ : ClassFunction.inner
        (ClassFunction.induce (centralizerT t)
          (ClassFunction.induce (K.subgroupOf (centralizerT t)) (ClassFunction.compHom e.toMonoidHom θ₁)))
        (ClassFunction.induce (centralizerT t)
          (ClassFunction.induce (K.subgroupOf (centralizerT t)) (ClassFunction.compHom e.toMonoidHom θ₁)))
      = ClassFunction.inner θ₁ (θ₁ + thetaInv θ₁) := by
    rw [ClassFunction.inner_induce_eq_of_isTISubset (centralizerT t) hTI
      (hvanish θ₁ hθ₁1) (hvanish θ₁ hθ₁1)]
    exact inner_induce_normal_index_two hσ hσN hcover hinv e θ₁ θ₁
  have hmain₂ : ClassFunction.inner
        (ClassFunction.induce (centralizerT t)
          (ClassFunction.induce (K.subgroupOf (centralizerT t)) (ClassFunction.compHom e.toMonoidHom θ₁)))
        (ClassFunction.induce (centralizerT t)
          (ClassFunction.induce (K.subgroupOf (centralizerT t)) (ClassFunction.compHom e.toMonoidHom θ₂)))
      = ClassFunction.inner θ₁ (θ₂ + thetaInv θ₂) := by
    rw [ClassFunction.inner_induce_eq_of_isTISubset (centralizerT t) hTI
      (hvanish θ₁ hθ₁1) (hvanish θ₂ hθ₂1)]
    exact inner_induce_normal_index_two hσ hσN hcover hinv e θ₁ θ₂
  have hmain₃ : ClassFunction.inner
        (ClassFunction.induce (centralizerT t)
          (ClassFunction.induce (K.subgroupOf (centralizerT t)) (ClassFunction.compHom e.toMonoidHom θ₂)))
        (ClassFunction.induce (centralizerT t)
          (ClassFunction.induce (K.subgroupOf (centralizerT t)) (ClassFunction.compHom e.toMonoidHom θ₂)))
      = ClassFunction.inner θ₂ (θ₂ + thetaInv θ₂) := by
    rw [ClassFunction.inner_induce_eq_of_isTISubset (centralizerT t) hTI
      (hvanish θ₂ hθ₂1) (hvanish θ₂ hθ₂1)]
    exact inner_induce_normal_index_two hσ hσN hcover hinv e θ₂ θ₂
  exact ⟨by rw [hα, hmain₁, hK₁], by rw [hα, hβ, hmain₂, hK₂], by rw [hβ, hmain₃, hK₃]⟩

end Work.BSW.Char

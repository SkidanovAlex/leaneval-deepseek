import Submission.Work.Tame.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Tame.Tau` — the Dade-type map `τ` of Feit–Thompson (9.4)

Feit–Thompson define (p. 805), for a tamely imbedded subset `L̂` of `X` with supporting subgroups
`𝔎_1, …, 𝔎_n` (and `𝔎_0 = 1`, `𝔏_0 = 𝔇`, `𝔄_L = {L}`):

* `α_i   = α|_{𝔏 ∩ 𝔑_i}`,
* `α_{i1}` the class function of `𝔑_i / 𝔎_i` restricting to `α_i` on `𝔏 ∩ 𝔑_i` (equivalently, the
  inflation of `α_i` along the projection `𝔑_i → 𝔏 ∩ 𝔑_i` of the decomposition
  `𝔑_i = 𝔎_i(𝔏 ∩ 𝔑_i)`),
* `α_{i2} = Ind_{𝔏 ∩ 𝔑_i}^{𝔑_i} α_i`,
* `α^τ = α^* + ∑_{i=1}^n (α_{i1} - α_{i2})^*`   (9.4),

where `^*` denotes induction to `X`.

This module defines `projEC` (the projection of the decomposition, totalised by `Classical.choose`
so that `τ` needs no hypotheses), the integral linear maps `indLM`, `resLM`, `alphaI1LM`,
`alphaI2LM`, and finally `tau : (↥𝔏 → ℂ) →ₗ[ℤ] (X → ℂ)`, together with the API of `projEC`.
-/

noncomputable section

open Classical
open scoped Pointwise

namespace Work.Tame

universe u

variable {X : Type u}

section Tau

variable [Group X] [Fintype X]

/-! ## Induction and restriction as integral linear maps -/

/-- Induction `Ind_K^X` as an integral linear map `(↥K → ℂ) →ₗ[ℤ] (X → ℂ)`. -/
noncomputable def indLM (K : Subgroup X) : (↥K → ℂ) →ₗ[ℤ] (X → ℂ) where
  toFun := Induction.indFun K
  map_add' f g := Induction.indFun_add K f g
  map_smul' c f := by
    have h1 : c • f = (c : ℂ) • f := by funext x; simp [zsmul_eq_mul, smul_eq_mul]
    have h2 : (c : ℂ) • Induction.indFun K f = c • Induction.indFun K f := by
      funext x; simp [zsmul_eq_mul, smul_eq_mul]
    rw [h1, Induction.indFun_smul]
    exact h2

@[simp] theorem indLM_apply (K : Subgroup X) (f : ↥K → ℂ) :
    indLM K f = Induction.indFun K f := rfl

/-- Restriction along a homomorphism `φ : H →* X`, as an integral linear map. -/
noncomputable def resLM {H : Type*} [Group H] (φ : H →* X) : (X → ℂ) →ₗ[ℤ] (H → ℂ) where
  toFun := Induction.resFunHom φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem resLM_apply {H : Type*} [Group H] (φ : H →* X) (f : X → ℂ) :
    resLM φ f = Induction.resFunHom φ f := rfl

/-! ## The projection `𝔑 = N(K) → 𝔏 ⊓ 𝔑` of the decomposition `𝔑 = 𝔎(𝔏 ∩ 𝔑)` -/

/-- The (totalised) projection `𝔑 = N(K) → 𝔏 ⊓ 𝔑` sending `N` to an element `M ∈ 𝔏 ⊓ 𝔑` with
`N * M⁻¹ ∈ K`.  Feit–Thompson's decomposition `𝔑_i = 𝔎_i(𝔏 ∩ 𝔑_i)` together with
`𝔎_i ∩ 𝔏 = 1` makes this a well defined group homomorphism (see `projEC_eq_of`), which is what
makes `α_{i1}` of (9.4) well defined. -/
noncomputable def projEC (Lhat : Set X) (K : Subgroup X) (N : ↥(Lgrp (K : Set X))) :
    ↥(Lgrp Lhat ⊓ Lgrp (K : Set X)) :=
  if h : ∃ m : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X)), (N : X) * ((m : X))⁻¹ ∈ K
  then Classical.choose h else 1

/-- Uniqueness of the element selected by `projEC`: if `N * M⁻¹ ∈ K` for some `M ∈ 𝔏 ⊓ 𝔑`, then
`M` is the element selected.  The hypothesis `K ⊓ 𝔏 = ⊥` is Feit–Thompson's `𝔎_i ∩ 𝔏 = 1`. -/
theorem projEC_eq_of {Lhat : Set X} {K : Subgroup X} (hinf : K ⊓ Lgrp Lhat = ⊥)
    {N : ↥(Lgrp (K : Set X))} {m : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X))}
    (hm : (N : X) * ((m : X))⁻¹ ∈ K) : projEC Lhat K N = m := by
  by_cases h : ∃ m' : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X)), (N : X) * ((m' : X))⁻¹ ∈ K
  · rw [projEC, dif_pos h]
    have hspec : (N : X) * ((Classical.choose h : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X))) : X)⁻¹ ∈ K :=
      Classical.choose_spec h
    have hmK : (((Classical.choose h : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X))) : X) * ((m : X))⁻¹) ∈ K := by
      have h3 : ((N : X) * ((Classical.choose h : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X))) : X)⁻¹)⁻¹ *
          ((N : X) * ((m : X))⁻¹) ∈ K := K.mul_mem (K.inv_mem hspec) hm
      have h4 : ((N : X) * ((Classical.choose h : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X))) : X)⁻¹)⁻¹ *
          ((N : X) * ((m : X))⁻¹) =
          ((Classical.choose h : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X))) : X) * ((m : X))⁻¹ := by
        simp [mul_assoc]
      rwa [h4] at h3
    have hL : (((Classical.choose h : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X))) : X) * ((m : X))⁻¹) ∈
        Lgrp Lhat :=
      (Lgrp Lhat).mul_mem (Classical.choose h).2.1 ((Lgrp Lhat).inv_mem m.2.1)
    have hbot : (((Classical.choose h : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X))) : X) * ((m : X))⁻¹) ∈
        (⊥ : Subgroup X) := by rw [← hinf]; exact ⟨hmK, hL⟩
    have hone : ((Classical.choose h : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X))) : X) * ((m : X))⁻¹ = 1 := by
      simpa using hbot
    have hmi : ((Classical.choose h : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X))) : X) = (m : X) := by
      have h1 : ((Classical.choose h : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X))) : X) * ((m : X))⁻¹ =
          (m : X) * ((m : X))⁻¹ := by rw [hone, mul_inv_cancel]
      exact mul_right_cancel h1
    exact Subtype.ext hmi
  · rw [projEC, dif_neg h]
    exact absurd ⟨m, hm⟩ h

/-- The key identity `N * (projEC N)⁻¹ ∈ K` when `𝔑 = K ⊔ (𝔏 ⊓ 𝔑)` (Feit–Thompson's (ii)(c)). -/
theorem mul_projEC_inv_mem {Lhat : Set X} {K : Subgroup X}
    (hsup : Lgrp (K : Set X) = K ⊔ (Lgrp Lhat ⊓ Lgrp (K : Set X)))
    (N : ↥(Lgrp (K : Set X))) :
    (N : X) * ((projEC Lhat K N : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X))) : X)⁻¹ ∈ K := by
  have hKN : K ≤ Lgrp (K : Set X) := Subgroup.le_normalizer
  have hCN : (Lgrp Lhat ⊓ Lgrp (K : Set X)) ≤ Lgrp (K : Set X) := inf_le_right
  have hsupNT : K.subgroupOf (Lgrp (K : Set X)) ⊔
      (Lgrp Lhat ⊓ Lgrp (K : Set X)).subgroupOf (Lgrp (K : Set X)) =
      (Lgrp (K : Set X)).subgroupOf (Lgrp (K : Set X)) := by
    conv_lhs => rw [← Subgroup.subgroupOf_sup hKN hCN, ← hsup]
  have hmem : (N : ↥(Lgrp (K : Set X))) ∈ K.subgroupOf (Lgrp (K : Set X)) ⊔
      (Lgrp Lhat ⊓ Lgrp (K : Set X)).subgroupOf (Lgrp (K : Set X)) := by
    rw [hsupNT, Subgroup.mem_subgroupOf]; exact N.2
  have hnorm : (K.subgroupOf (Lgrp (K : Set X))).Normal := Subgroup.normal_in_normalizer
  haveI := hnorm
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := K.subgroupOf (Lgrp (K : Set X)))
      (t := (Lgrp Lhat ⊓ Lgrp (K : Set X)).subgroupOf (Lgrp (K : Set X)))).mp hmem
  have hyX : (y : X) ∈ K := Subgroup.mem_subgroupOf.mp hy
  have hzX : (z : X) ∈ Lgrp Lhat ⊓ Lgrp (K : Set X) := Subgroup.mem_subgroupOf.mp hz
  have hNz : (N : X) = (y : X) * (z : X) := by
    have h' := congrArg (fun t : ↥(Lgrp (K : Set X)) => (t : X)) hyz
    simpa using h'.symm
  have hex : ∃ m : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X)), (N : X) * ((m : X))⁻¹ ∈ K := by
    refine ⟨⟨(z : X), hzX⟩, ?_⟩
    rw [hNz]; simp only [mul_assoc, mul_inv_cancel, mul_one]; exact hyX
  have hproj : projEC Lhat K N = Classical.choose hex := by
    rw [projEC, dif_pos hex]
  rw [hproj]
  exact Classical.choose_spec hex

/-! ## The maps `α ↦ α_{i1}` and `α ↦ α_{i2}` of (9.4), and `τ` -/

/-- `α ↦ α_{i1}` (Feit–Thompson (9.4)): the inflation of `α|_𝔏` along the projection
`𝔑_i → 𝔏 ∩ 𝔑_i`, i.e. `α_{i1}(N) = α(M)` where `N = H M`, `H ∈ 𝔎_i`, `M ∈ 𝔏 ∩ 𝔑_i`. -/
noncomputable def alphaI1LM (Lhat : Set X) (K : Subgroup X) :
    (↥(Lgrp Lhat) → ℂ) →ₗ[ℤ] (↥(Lgrp (K : Set X)) → ℂ) where
  toFun α := fun N => α (Subgroup.inclusion inf_le_left (projEC Lhat K N))
  map_add' f g := by funext N; rfl
  map_smul' c f := by funext N; rfl

/-- `α ↦ α_{i2}` (Feit–Thompson (9.4)): `α_i = α|_{𝔏 ∩ 𝔑_i}`, then
`α_{i2} = Ind_{𝔏 ∩ 𝔑_i}^{𝔑_i} α_i`. -/
noncomputable def alphaI2LM (Lhat : Set X) (K : Subgroup X) :
    (↥(Lgrp Lhat) → ℂ) →ₗ[ℤ] (↥(Lgrp (K : Set X)) → ℂ) :=
  (indLM ((Lgrp Lhat ⊓ Lgrp (K : Set X)).subgroupOf (Lgrp (K : Set X)))).comp
    (resLM ((Subgroup.inclusion (inf_le_left : Lgrp Lhat ⊓ Lgrp (K : Set X) ≤ Lgrp Lhat)).comp
      (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : Lgrp Lhat ⊓ Lgrp (K : Set X) ≤ Lgrp (K : Set X))).toMonoidHom))

@[simp] theorem alphaI1LM_apply (Lhat : Set X) (K : Subgroup X) (α : ↥(Lgrp Lhat) → ℂ)
    (N : ↥(Lgrp (K : Set X))) :
    alphaI1LM Lhat K α N = α (Subgroup.inclusion inf_le_left (projEC Lhat K N)) := rfl

@[simp] theorem alphaI2LM_apply (Lhat : Set X) (K : Subgroup X) (α : ↥(Lgrp Lhat) → ℂ)
    (N : ↥(Lgrp (K : Set X))) :
    alphaI2LM Lhat K α N = Induction.indFun
      ((Lgrp Lhat ⊓ Lgrp (K : Set X)).subgroupOf (Lgrp (K : Set X)))
      (fun m => α (Subgroup.inclusion inf_le_left
        ((Subgroup.subgroupOfEquivOfLe
          (inf_le_right : Lgrp Lhat ⊓ Lgrp (K : Set X) ≤ Lgrp (K : Set X))) m))) N := rfl

/-- **Feit–Thompson (9.4)**, p. 805: the Dade-type map
`α^τ = α^* + ∑_{i=1}^n (α_{i1} - α_{i2})^*`,
where `^*` is induction to `X` and `α_{i1}`, `α_{i2}` are as above. -/
noncomputable def tau (Lhat : Set X) (n : ℕ) (Hs : Fin n → Subgroup X) :
    (↥(Lgrp Lhat) → ℂ) →ₗ[ℤ] (X → ℂ) :=
  indLM (Lgrp Lhat) +
    ∑ i : Fin n, (indLM (Lgrp (Hs i : Set X))).comp (alphaI1LM Lhat (Hs i) - alphaI2LM Lhat (Hs i))

theorem tau_apply (Lhat : Set X) (n : ℕ) (Hs : Fin n → Subgroup X)
    (α : ↥(Lgrp Lhat) → ℂ) (x : X) :
    tau Lhat n Hs α x = Induction.indFun (Lgrp Lhat) α x +
      ∑ i : Fin n, Induction.indFun (Lgrp (Hs i : Set X))
        (alphaI1LM Lhat (Hs i) α - alphaI2LM Lhat (Hs i) α) x := by
  simp only [tau, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, indLM_apply,
    LinearMap.sum_apply, Pi.add_apply, Finset.sum_apply]

end Tau

end Work.Tame

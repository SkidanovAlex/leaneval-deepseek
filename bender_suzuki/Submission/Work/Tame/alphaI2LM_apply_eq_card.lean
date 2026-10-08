import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.Tau
import Submission.Work.Tame.projEC_mul
import Submission.Work.Tame.projEC_one
import Submission.Work.Tame.projEC_eq_self

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Tame.alphaI2LM_apply_eq_card` — the value of `α_{i2}` on `𝔑_i` (Feit–Thompson (9.5))

Feit–Thompson (9.5) computes the induced function `α_{i2} = Ind_{𝔏∩𝔑_i}^{𝔑_i}(α_i)` of (9.4) on
a supporting subgroup's normalizer.  With `𝔑 = N(K)`, `𝔏 = N(L̂)`, `M = 𝔏 ⊓ 𝔑` and
`N ∈ 𝔑` written `N = H·M` (`H ∈ K`, `M = projEC Lhat K N ∈ M`, Feit–Thompson's decomposition
`𝔑 = K(𝔏 ∩ 𝔑)` with `K ∩ 𝔏 = 1`), the induction formula

`α_{i2}(N) = |M|⁻¹ ∑_{x ∈ 𝔑, xNx⁻¹ ∈ M} α(xNx⁻¹)`

is evaluated by parametrising `𝔑 = M × K` as `x = m'·k`: for fixed `m'` the terms are non-zero
exactly when `kNk⁻¹ = projEC Lhat K N` and then equal to `α(projEC Lhat K N)` (here `α` is a
class function, i.e. `α ∈ 𝓒₀(L̂)`).  Summing the (m'-independent) count over `m' ∈ M` cancels the
factor `|M|⁻¹` and yields

`α_{i2}(N) = #{k ∈ K | k⁻¹Nk = projEC Lhat K N} · α(projEC Lhat K N)`.

This is exactly (9.5) `α_{i2}(L) = |C(L) ∩ 𝔎_i|·α(L)` for the special value `N = L ∈ 𝔏_i`.
-/

noncomputable section

open Classical
open scoped Pointwise

namespace Work.Tame

/-- The function `α : ↥𝔏 → ℂ` extended by `0` off `𝔏 = N(L̂)`.  This is the "member
indicator" form of the summands in the induction formula for `α_{i2}`. -/
def alphaExt {X : Type*} [Group X] {Lhat : Set X} (α : ↥(Lgrp Lhat) → ℂ) (y : X) : ℂ :=
  if h : y ∈ Lgrp Lhat then α ⟨y, h⟩ else 0

theorem alphaExt_of_mem {X : Type*} [Group X] {Lhat : Set X} {α : ↥(Lgrp Lhat) → ℂ} {y : X}
    (h : y ∈ Lgrp Lhat) : alphaExt α y = α ⟨y, h⟩ := dif_pos h

theorem alphaExt_of_not_mem {X : Type*} [Group X] {Lhat : Set X} {α : ↥(Lgrp Lhat) → ℂ}
    {y : X} (h : y ∉ Lgrp Lhat) : alphaExt α y = 0 := dif_neg h

/-- `alphaExt` of a class function is invariant under conjugation by an element of `𝔏`. -/
theorem alphaExt_conj {X : Type*} [Group X] {Lhat : Set X} {α : ↥(Lgrp Lhat) → ℂ}
    (hα : CharCore.IsClassFun α) {g y : X} (hg : g ∈ Lgrp Lhat) :
    alphaExt α (g * y * g⁻¹) = alphaExt α y := by
  by_cases hy : y ∈ Lgrp Lhat
  · have hgy : g * y * g⁻¹ ∈ Lgrp Lhat :=
      (Lgrp Lhat).mul_mem ((Lgrp Lhat).mul_mem hg hy) ((Lgrp Lhat).inv_mem hg)
    rw [alphaExt_of_mem hgy, alphaExt_of_mem hy]
    have heq : (⟨g, hg⟩ : ↥(Lgrp Lhat)) * (⟨y, hy⟩ : ↥(Lgrp Lhat)) *
        (⟨g, hg⟩ : ↥(Lgrp Lhat))⁻¹ = (⟨g * y * g⁻¹, hgy⟩ : ↥(Lgrp Lhat)) := Subtype.ext rfl
    rw [← heq]
    exact hα _ _
  · have hgy : g * y * g⁻¹ ∉ Lgrp Lhat := by
      intro hh
      apply hy
      have h1 : g⁻¹ * (g * y * g⁻¹) * g ∈ Lgrp Lhat :=
        (Lgrp Lhat).mul_mem ((Lgrp Lhat).mul_mem ((Lgrp Lhat).inv_mem hg) hh) hg
      rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at h1
    rw [alphaExt_of_not_mem hgy, alphaExt_of_not_mem hy]

/-- For `k ∈ K` the conjugate `kNk⁻¹ ∈ 𝔑` lies in `𝔏` only if it equals `projEC Lhat K N`: the
image of `kNk⁻¹` in `𝔑/K` equals that of `N`, and `M = 𝔏 ⊓ 𝔑` is a complement of `K` in `𝔑`. -/
theorem projEC_val_eq_of_mem {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {K : Subgroup X}
    (hsup : Lgrp (K : Set X) = K ⊔ (Lgrp Lhat ⊓ Lgrp (K : Set X)))
    (hinf : K ⊓ Lgrp Lhat = ⊥) (N : ↥(Lgrp (K : Set X))) (k : ↥K)
    (hk : (k : X) * (N : X) * (k : X)⁻¹ ∈ Lgrp Lhat) :
    (k : X) * (N : X) * (k : X)⁻¹ = (projEC Lhat K N : X) := by
  let k₁ : ↥(Lgrp (K : Set X)) := ⟨(k : X), Subgroup.le_normalizer k.2⟩
  have hk1 : (k₁ : X) = (k : X) := rfl
  have hone : projEC Lhat K k₁ = 1 := by
    refine projEC_eq_of hinf (m := 1) ?_
    rw [Subgroup.coe_one, inv_one, mul_one, hk1]; exact k.2
  have hone' : projEC Lhat K k₁⁻¹ = 1 := by
    refine projEC_eq_of hinf (m := 1) ?_
    rw [Subgroup.coe_one, inv_one, mul_one]
    show (k₁ : X)⁻¹ ∈ K
    rw [hk1]; exact K.inv_mem k.2
  have hz : projEC Lhat K (k₁ * N * k₁⁻¹) = projEC Lhat K N := by
    rw [projEC_mul hsup hinf (k₁ * N) k₁⁻¹, projEC_mul hsup hinf k₁ N, hone, hone']
    simp
  let μ : ↥(Lgrp Lhat ⊓ Lgrp (K:Set X)) :=
    ⟨(k:X)*(N:X)*(k:X)⁻¹, hk, (k₁*N*k₁⁻¹).2⟩
  have hsub : (⟨(μ:X), μ.2.2⟩ : ↥(Lgrp (K:Set X))) = k₁ * N * k₁⁻¹ := Subtype.ext rfl
  have hμ : projEC Lhat K (k₁*N*k₁⁻¹) = μ := by rw [← hsub, projEC_eq_self hinf μ]
  have hfin : μ = projEC Lhat K N := by rw [← hμ, hz]
  exact congrArg Subtype.val hfin

/-- The value of `alphaExt α` at `kNk⁻¹` (`k ∈ K`) is `α(projEC Lhat K N)` if `kNk⁻¹ = projEC Lhat K N`
and `0` otherwise. -/
theorem alphaExt_K_eq {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {K : Subgroup X}
    (hsup : Lgrp (K : Set X) = K ⊔ (Lgrp Lhat ⊓ Lgrp (K : Set X)))
    (hinf : K ⊓ Lgrp Lhat = ⊥) {α : ↥(Lgrp Lhat) → ℂ} (N : ↥(Lgrp (K : Set X))) (k : ↥K) :
    alphaExt α ((k:X)*(N:X)*(k:X)⁻¹) =
      if (k:X)*(N:X)*(k:X)⁻¹ = (projEC Lhat K N : X) then
        α (Subgroup.inclusion inf_le_left (projEC Lhat K N)) else 0 := by
  by_cases hk : (k:X)*(N:X)*(k:X)⁻¹ = (projEC Lhat K N : X)
  · rw [if_pos hk]
    have hmem : (k:X)*(N:X)*(k:X)⁻¹ ∈ Lgrp Lhat := by rw [hk]; exact (projEC Lhat K N).2.1
    rw [alphaExt_of_mem hmem]
    congr 1
    exact Subtype.ext hk
  · rw [if_neg hk]
    have hmem : (k:X)*(N:X)*(k:X)⁻¹ ∉ Lgrp Lhat := by
      intro hh
      exact hk (projEC_val_eq_of_mem hsup hinf N k hh)
    rw [alphaExt_of_not_mem hmem]

theorem sum_ite_card {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P] (c : ℂ) :
    (∑ k, if P k then c else 0) = (Nat.card {k // P k} : ℂ) * c := by
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The summand of `Induction.indFun` for `α_{i2}` at `N` is `alphaExt α (xNx⁻¹)`. -/
theorem alphaI2LM_summand_eq {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {K : Subgroup X}
    {α : ↥(Lgrp Lhat) → ℂ} (N : ↥(Lgrp (K : Set X))) (x : ↥(Lgrp (K : Set X))) :
    (if hx : x * N * x⁻¹ ∈ (Lgrp Lhat ⊓ Lgrp (K:Set X)).subgroupOf (Lgrp (K:Set X)) then
        α (Subgroup.inclusion inf_le_left
          ((Subgroup.subgroupOfEquivOfLe inf_le_right) ⟨x * N * x⁻¹, hx⟩))
      else 0)
      = alphaExt α ((x:X)*(N:X)*(x:X)⁻¹) := by
  by_cases h : (x:X)*(N:X)*(x:X)⁻¹ ∈ Lgrp Lhat
  · have hH : x * N * x⁻¹ ∈ (Lgrp Lhat ⊓ Lgrp (K:Set X)).subgroupOf (Lgrp (K:Set X)) := by
      rw [Subgroup.mem_subgroupOf]; exact ⟨h, (x * N * x⁻¹).2⟩
    rw [dif_pos hH, alphaExt_of_mem h]
    congr 1
  · have hH : ¬ (x * N * x⁻¹ ∈ (Lgrp Lhat ⊓ Lgrp (K:Set X)).subgroupOf (Lgrp (K:Set X))) := by
      intro hh; rw [Subgroup.mem_subgroupOf] at hh; exact h hh.1
    rw [dif_neg hH, alphaExt_of_not_mem h]

/-- **Feit–Thompson (9.5)** in the form used here, for an arbitrary supporting subgroup `K`:
if `𝔑 = K ⊔ (𝔏 ⊓ 𝔑)` and `K ⊓ 𝔏 = ⊥` (Definition 9.1(ii)(c)) then for every `N ∈ 𝔑` and every
class function `α` on `𝔏`, the induced function `α_{i2} = Ind_{𝔏⊓𝔑}^{𝔑}(α|)` satisfies
`α_{i2}(N) = #{k ∈ K | k⁻¹Nk = projEC Lhat K N} · α(projEC Lhat K N)`. -/
theorem alphaI2LM_apply_eq_card_gen {X : Type*} [Group X] [Fintype X] {Lhat : Set X}
    {K : Subgroup X}
    (hsup : Lgrp (K : Set X) = K ⊔ (Lgrp Lhat ⊓ Lgrp (K : Set X)))
    (hinf : K ⊓ Lgrp Lhat = ⊥) {α : ↥(Lgrp Lhat) → ℂ} (hα : α ∈ C0 Lhat)
    (N : ↥(Lgrp (K : Set X))) :
    alphaI2LM Lhat K α N =
      (Nat.card {k : ↥K // (k : X)⁻¹ * (N : X) * (k : X) =
        ((projEC Lhat K N : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X))) : X)} : ℂ) *
      α (Subgroup.inclusion (inf_le_left : Lgrp Lhat ⊓ Lgrp (K : Set X) ≤ Lgrp Lhat)
        (projEC Lhat K N)) := by
  have hclass : CharCore.IsClassFun α := (mem_C0.mp hα).1
  rw [alphaI2LM_apply, Induction.indFun_apply_def]
  have hsum_eq : (∑ x : ↥(Lgrp (K:Set X)),
      (if hx : x * N * x⁻¹ ∈ (Lgrp Lhat ⊓ Lgrp (K:Set X)).subgroupOf (Lgrp (K:Set X)) then
        α (Subgroup.inclusion inf_le_left
          ((Subgroup.subgroupOfEquivOfLe inf_le_right) ⟨x * N * x⁻¹, hx⟩))
      else 0))
      = ∑ x : ↥(Lgrp (K:Set X)), alphaExt α ((x:X)*(N:X)*(x:X)⁻¹) :=
    Finset.sum_congr rfl (fun x _ => alphaI2LM_summand_eq N x)
  rw [hsum_eq]
  -- Reindex `∑_{x ∈ 𝔑}` by the decomposition `𝔑 ≃ M × K`, `(m', k) ↦ m'·k`.
  let E : ↥(Lgrp Lhat ⊓ Lgrp (K:Set X)) × ↥K → ↥(Lgrp (K:Set X)) :=
    fun p => ⟨(p.1:X)*(p.2:X), (Lgrp (K:Set X)).mul_mem p.1.2.2 (Subgroup.le_normalizer p.2.2)⟩
  have hEval : ∀ p, (E p : X) = (p.1:X)*(p.2:X) := fun p => rfl
  have hdis : Disjoint (Lgrp Lhat ⊓ Lgrp (K:Set X)) K := by
    rw [Subgroup.disjoint_def]
    intro x hx hxK
    have hx2 : x ∈ K ⊓ Lgrp Lhat := ⟨hxK, hx.1⟩
    simpa [hinf] using hx2
  have hE_inj : Function.Injective E := by
    intro p q hpq
    have hv : (p.1:X)*(p.2:X) = (q.1:X)*(q.2:X) := by rw [← hEval p, ← hEval q, hpq]
    exact Subgroup.mul_injective_of_disjoint hdis hv
  have hE_surj : Function.Surjective E := by
    intro z
    let mm := projEC Lhat K z
    have hmem := mul_projEC_inv_mem hsup z
    have hz2 : (mm : X) ∈ Lgrp (K:Set X) := mm.2.2
    have hmem2 : (mm:X)⁻¹ * (z:X) ∈ K := by
      have h3 := (Subgroup.mem_normalizer_iff.mp hz2) ((mm:X)⁻¹ * (z:X))
      exact h3.mpr (by
        rw [show (mm:X) * ((mm:X)⁻¹ * (z:X)) * (mm:X)⁻¹ = (z:X) * (mm:X)⁻¹ by group]
        exact hmem)
    refine ⟨(mm, ⟨(mm:X)⁻¹ * (z:X), hmem2⟩), ?_⟩
    apply Subtype.ext
    change (mm:X) * ((mm:X)⁻¹ * (z:X)) = (z:X)
    group
  let Ee : ↥(Lgrp Lhat ⊓ Lgrp (K:Set X)) × ↥K ≃ ↥(Lgrp (K:Set X)) :=
    Equiv.ofBijective E ⟨hE_inj, hE_surj⟩
  have hreindex : (∑ x : ↥(Lgrp (K:Set X)), alphaExt α ((x:X)*(N:X)*(x:X)⁻¹))
      = ∑ p : ↥(Lgrp Lhat ⊓ Lgrp (K:Set X)) × ↥K,
          alphaExt α (((Ee p : ↥(Lgrp (K:Set X))) : X)*(N:X)*
            (((Ee p : ↥(Lgrp (K:Set X)))) : X)⁻¹) :=
    (Fintype.sum_equiv Ee
      (fun p : ↥(Lgrp Lhat ⊓ Lgrp (K:Set X)) × ↥K =>
        alphaExt α (((Ee p : ↥(Lgrp (K:Set X))) : X)*(N:X)*(((Ee p : ↥(Lgrp (K:Set X)))) : X)⁻¹))
      (fun x : ↥(Lgrp (K:Set X)) => alphaExt α ((x:X)*(N:X)*(x:X)⁻¹))
      (fun p => rfl)).symm
  rw [hreindex, Fintype.sum_prod_type]
  -- For `x = m'·k` the value is `alphaExt α (m'·(kNk⁻¹)·m'⁻¹) = alphaExt α (kNk⁻¹)`.
  have hkey : ∀ (m' : ↥(Lgrp Lhat ⊓ Lgrp (K:Set X))) (k : ↥K),
      alphaExt α (((Ee (m',k) : ↥(Lgrp (K:Set X))) : X)*(N:X)*
        (((Ee (m',k) : ↥(Lgrp (K:Set X)))) : X)⁻¹)
      = alphaExt α ((k:X)*(N:X)*(k:X)⁻¹) := by
    rintro m' k
    have hEv : ((Ee (m',k) : ↥(Lgrp (K:Set X))) : X) = (m':X)*(k:X) := by
      change (E (m',k) : X) = _; rw [hEval]
    rw [hEv]
    have heq : ((m':X)*(k:X))*(N:X)*(((m':X)*(k:X)))⁻¹
        = (m':X) * ((k:X)*(N:X)*(k:X)⁻¹) * (m':X)⁻¹ := by group
    rw [heq]
    exact alphaExt_conj hclass m'.2.1
  have hinner : ∀ m' : ↥(Lgrp Lhat ⊓ Lgrp (K:Set X)),
      (∑ k : ↥K, alphaExt α (((Ee (m',k) : ↥(Lgrp (K:Set X))) : X)*(N:X)*
          (((Ee (m',k) : ↥(Lgrp (K:Set X)))) : X)⁻¹))
      = (Nat.card {k : ↥K // (k:X)*(N:X)*(k:X)⁻¹ =
            ((projEC Lhat K N : ↥(Lgrp Lhat ⊓ Lgrp (K:Set X))) : X)} : ℂ)
        * α (Subgroup.inclusion inf_le_left (projEC Lhat K N)) := by
    intro m'
    rw [Finset.sum_congr rfl (fun k _ => hkey m' k)]
    rw [Finset.sum_congr rfl (fun k _ => alphaExt_K_eq hsup hinf N k)]
    exact sum_ite_card _ _
  rw [Finset.sum_congr rfl (fun m' _ => hinner m')]
  have hcardH : Nat.card ↥((Lgrp Lhat ⊓ Lgrp (K:Set X)).subgroupOf (Lgrp (K:Set X)))
      = Nat.card ↥(Lgrp Lhat ⊓ Lgrp (K:Set X)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : Lgrp Lhat ⊓ Lgrp (K:Set X) ≤ Lgrp (K:Set X))).toEquiv
  -- `#{k | kNk⁻¹ = m} = #{k | k⁻¹Nk = m}` via `k ↦ k⁻¹`.
  have hcardT : Nat.card {k : ↥K // (k:X)*(N:X)*(k:X)⁻¹ =
          ((projEC Lhat K N : ↥(Lgrp Lhat ⊓ Lgrp (K:Set X))) : X)}
      = Nat.card {k : ↥K // (k:X)⁻¹*(N:X)*(k:X) =
          ((projEC Lhat K N : ↥(Lgrp Lhat ⊓ Lgrp (K:Set X))) : X)} := by
    refine Nat.card_congr ?_
    refine Equiv.subtypeEquiv (Equiv.inv ↥K) ?_
    intro k
    constructor
    · intro hk; simpa using hk
    · intro hk; simpa using hk
  rw [hcardH, hcardT, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [Nat.card_eq_fintype_card]
  have hM0 : (Fintype.card ↥(Lgrp Lhat ⊓ Lgrp (K:Set X)) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card ↥(Lgrp Lhat ⊓ Lgrp (K:Set X)) ≠ 0)
  rw [← mul_assoc, inv_mul_cancel₀ hM0, one_mul]

theorem alphaI2LM_apply_eq_card {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hne : (Dset Lhat).Nonempty) (j : Fin n)
    {α : ↥(Lgrp Lhat) → ℂ} (hα : α ∈ C0 Lhat) (N : ↥(Lgrp (Hs j : Set X))) :
    alphaI2LM Lhat (Hs j) α N =
      (Nat.card {k : ↥(Hs j) // (k : X)⁻¹ * (N : X) * (k : X) =
        ((projEC Lhat (Hs j) N : ↥(Lgrp Lhat ⊓ Lgrp (Hs j : Set X))) : X)} : ℂ) *
      α (Subgroup.inclusion (inf_le_left : Lgrp Lhat ⊓ Lgrp (Hs j : Set X) ≤ Lgrp Lhat)
        (projEC Lhat (Hs j) N)) :=
  alphaI2LM_apply_eq_card_gen (h.supp_prod hne j) (h.supp_inf hne j) hα N

end Work.Tame

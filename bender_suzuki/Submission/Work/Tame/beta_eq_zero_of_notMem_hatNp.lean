import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.Tau
import Submission.Work.Tame.mem_hatNp_iff
import Submission.Work.Tame.projEC_mul
import Submission.Work.Tame.projEC_one
import Submission.Work.Tame.projEC_eq_self
import Submission.Work.Tame.alphaI2LM_apply_eq_card

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Tame

open Classical

/-! ## Counting the elements `k ∈ 𝔎` with `k⁻¹ N k = π N`

Let `𝔑 = N(K) = K ⊔ (𝔏 ⊓ 𝔑)` with `K ⊓ 𝔏 = 1` (Feit–Thompson Definition 9.1(ii)(c)) and let
`N ∈ 𝔑`.  Write `π N = projEC Lhat K N` for the `𝔏`-component of `N`.  The condition of
Feit–Thompson (ii)(e) — `N ∉ Ñ^#` — says, when `N ∉ K`, that no non-identity element of `K`
commutes with `N`; equivalently the map `k ↦ k⁻¹ N k π(N)⁻¹ : K → K` is injective, hence
bijective, so the set `{k ∈ K | k⁻¹ N k = π N}` is a singleton. -/
theorem card_kInvNk_eq_one {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {K : Subgroup X}
    (hsup : Lgrp (K : Set X) = K ⊔ (Lgrp Lhat ⊓ Lgrp (K : Set X)))
    (hinf : K ⊓ Lgrp Lhat = ⊥) (N : ↥(Lgrp (K : Set X)))
    (hcent : ∀ k : ↥K, (k : X)⁻¹ * (N : X) * (k : X) = (N : X) → k = 1) :
    Nat.card {k : ↥K // (k : X)⁻¹ * (N : X) * (k : X) =
      ((projEC Lhat K N : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X))) : X)} = 1 := by
  classical
  set M : ↥(Lgrp Lhat ⊓ Lgrp (K : Set X)) := projEC Lhat K N with hM
  -- `k⁻¹ N k π(N)⁻¹ ∈ K` for every `k ∈ K`
  have hψmem : ∀ k : ↥K, (k : X)⁻¹ * (N : X) * (k : X) * (M : X)⁻¹ ∈ K := by
    intro k
    let k' : ↥(Lgrp (K : Set X)) := ⟨(k : X), Subgroup.le_normalizer k.2⟩
    have hk' : projEC Lhat K k' = 1 := projEC_eq_of (m := 1) hinf (by
      rw [Subgroup.coe_one, inv_one, mul_one]
      exact k.2)
    have hk'i : projEC Lhat K k'⁻¹ = 1 := projEC_eq_of (m := 1) hinf (by
      rw [Subgroup.coe_one, inv_one, mul_one]
      exact K.inv_mem k.2)
    have hconj : projEC Lhat K (k'⁻¹ * N * k') = M := by
      rw [projEC_mul hsup hinf, projEC_mul hsup hinf, hk'i, hk', ← hM]
      simp
    have h1 := mul_projEC_inv_mem hsup (k'⁻¹ * N * k')
    rw [hconj] at h1
    simpa [k'] using h1
  let ψ : ↥K → ↥K := fun k => ⟨(k : X)⁻¹ * (N : X) * (k : X) * (M : X)⁻¹, hψmem k⟩
  have hψeq : ∀ k : ↥K, (ψ k : X) = (k : X)⁻¹ * (N : X) * (k : X) * (M : X)⁻¹ := fun _ => rfl
  have hψ : ∀ k : ↥K, ψ k = 1 ↔ (k : X)⁻¹ * (N : X) * (k : X) = (M : X) := by
    intro k
    constructor
    · intro h
      have h' : (k : X)⁻¹ * (N : X) * (k : X) * (M : X)⁻¹ = 1 := by
        rw [← hψeq k, h, Subgroup.coe_one]
      exact mul_inv_eq_one.mp h'
    · intro h
      apply Subtype.ext
      rw [hψeq k, h, Subgroup.coe_one, mul_inv_cancel]
  have hinj : Function.Injective ψ := by
    intro k₁ k₂ h
    have hv : (k₁ : X)⁻¹ * (N : X) * (k₁ : X) * (M : X)⁻¹
        = (k₂ : X)⁻¹ * (N : X) * (k₂ : X) * (M : X)⁻¹ := by
      rw [← hψeq k₁, ← hψeq k₂, h]
    have hc : (k₁ : X)⁻¹ * (N : X) * (k₁ : X) = (k₂ : X)⁻¹ * (N : X) * (k₂ : X) :=
      mul_right_cancel hv
    have h2 : ((k₂ : X) * (k₁ : X)⁻¹) * (N : X)
        = (N : X) * ((k₂ : X) * (k₁ : X)⁻¹) := by
      have h3 := congrArg (fun t => (k₂ : X) * t * (k₁ : X)⁻¹) hc
      rw [show (k₂ : X) * ((k₁ : X)⁻¹ * (N : X) * (k₁ : X)) * (k₁ : X)⁻¹
            = ((k₂ : X) * (k₁ : X)⁻¹) * (N : X) from by group,
          show (k₂ : X) * ((k₂ : X)⁻¹ * (N : X) * (k₂ : X)) * (k₁ : X)⁻¹
            = (N : X) * ((k₂ : X) * (k₁ : X)⁻¹) from by group] at h3
      exact h3
    have hmem2 : ((k₂ * k₁⁻¹ : ↥K) : X) = (k₂ : X) * (k₁ : X)⁻¹ := by simp
    have hcomm : ((k₂ * k₁⁻¹ : ↥K) : X)⁻¹ * (N : X) * ((k₂ * k₁⁻¹ : ↥K) : X) = (N : X) := by
      rw [hmem2]
      rw [show ((k₂ : X) * (k₁ : X)⁻¹)⁻¹ * (N : X) * ((k₂ : X) * (k₁ : X)⁻¹)
            = ((k₂ : X) * (k₁ : X)⁻¹)⁻¹ * ((N : X) * ((k₂ : X) * (k₁ : X)⁻¹)) from by group,
          ← h2]
      group
    exact (mul_inv_eq_one.mp (hcent (k₂ * k₁⁻¹) hcomm)).symm
  have hsurj : Function.Surjective ψ := Finite.surjective_of_injective hinj
  obtain ⟨k₀, hk₀⟩ := hsurj 1
  have hP₀ : (k₀ : X)⁻¹ * (N : X) * (k₀ : X) = (M : X) := (hψ k₀).mp hk₀
  refine Nat.card_eq_one_iff_exists.mpr ⟨⟨k₀, hP₀⟩, ?_⟩
  rintro ⟨k, hk⟩
  apply Subtype.ext
  exact hinj (by rw [(hψ k).mpr hk, hk₀])

theorem beta_eq_zero_of_notMem_hatNp {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} (h : IsTamelyImbedded Lhat n Hs) (hne : (Dset Lhat).Nonempty)
    {α : ↥(Lgrp Lhat) → ℂ} (hα : α ∈ C0 Lhat) (i : Fin n) {N : ↥(Lgrp (Hs i : Set X))}
    (hN : (N : X) ∉ hatNp (Hs i)) :
    alphaI1LM Lhat (Hs i) α N - alphaI2LM Lhat (Hs i) α N = 0 := by
  classical
  have hinf : Hs i ⊓ Lgrp Lhat = ⊥ := h.supp_inf hne i
  have hsup : Lgrp (Hs i : Set X) = Hs i ⊔ (Lgrp Lhat ⊓ Lgrp (Hs i : Set X)) :=
    h.supp_prod hne i
  rw [alphaI2LM_apply_eq_card h hne i hα N, alphaI1LM_apply]
  by_cases hNK : (N : X) ∈ Hs i
  · -- `N ∈ 𝔎_i`: then `π N = 1` and `α(1) = 0`, so both terms vanish
    have hproj : projEC Lhat (Hs i) N = 1 :=
      projEC_eq_of (m := 1) hinf (by simpa using hNK)
    have hA : α (Subgroup.inclusion (inf_le_left : Lgrp Lhat ⊓ Lgrp (Hs i : Set X) ≤ Lgrp Lhat)
        (projEC Lhat (Hs i) N)) = 0 := by
      rw [hproj, map_one, hα.2.2]
    rw [hA, mul_zero, sub_zero]
  · -- `N ∉ 𝔎_i`: `N ∉ Ñ_i^#` forces `C_{𝔎_i}(N) = 1`, and the count is `1`
    have hnot : ¬ ∃ H : X, H ∈ (Hs i : Set X) ∧ H ≠ 1 ∧ (N : X) * H = H * (N : X) := by
      rintro ⟨H, hHK, hH1, hc⟩
      exact hN (mem_hatNp_iff.mpr ⟨N.2, hNK, H, hHK, hH1, hc⟩)
    have hcent : ∀ k : ↥(Hs i), (k : X)⁻¹ * (N : X) * (k : X) = (N : X) → k = 1 := by
      intro k hk
      by_contra hk1
      have hc : (N : X) * (k : X) = (k : X) * (N : X) := by
        have hh := congrArg (fun t => (k : X) * t) hk
        simpa [mul_assoc] using hh
      exact hnot ⟨(k : X), k.2, fun h => hk1 (Subtype.ext h), hc⟩
    have hcard := card_kInvNk_eq_one hsup hinf N hcent
    rw [hcard, Nat.cast_one, one_mul, sub_self]

end Work.Tame

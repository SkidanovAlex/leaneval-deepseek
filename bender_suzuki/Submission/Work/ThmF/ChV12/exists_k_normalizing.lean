import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.ThmF.Bender.cardInvGeTwo

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.exists_k_normalizing` — Peterfalvi II, Ch. II §4 Prop. 3: `N_K(X) ≠ 1`

Let `H` be strongly embedded in the finite group `G`, let `t ∉ H` be an involution,
`D = H ∩ Hᵗ = twoPoint H t` and `V = C_D(t) = centD H t`.  For a subgroup `X ≤ V` which fixes at
least three points of `Ω = G ⧸ H` and such that `C_G(X)` has 2-rank `≥ 2`
(`HasFourGroup (C_G(X))`), the hypothesis of Ch. II §4 Prop. 3 — `N_K(X) ≠ 1`, where
`K = J(D,t) = {x ∈ D | xᵗ = x⁻¹} = invertedBy (twoPoint H t) t` — holds.

The mathematical content of the proposition (!) is that `K#` contains an element normalising `X`,
not merely commuting with it.

## Proof

Put `F = N_G(X)`.  Everything happens inside the group `↥F`:

* `X ≤ V ≤ D ≤ H` and `t` centralises `X` (as `X ≤ V ≤ C{t}`), so `X ≤ F` and `t ∈ F`; write
  `t_F = ⟨t, ·⟩ : ↥F` and `H_F = (F ⊓ H).subgroupOf F`.
* Hypothesis (P1b) with `X' = X`, the subgroup `F` itself, `F ≤ N_G(X)` and `g = 1` gives
  `IsStronglyEmbedded H_F` — this is exactly `H_F` strongly embedded in `↥F`.
* `HasFourGroup ↥F` follows from `HasFourGroup ↥(C_G(X))` because `C_G(X) ≤ N_G(X) = F` (the two
  commuting involutions of `C_G(X)` are elements of `F`).
* `t_F ∉ H_F` (as `t ∉ H`) and `orderOf t_F = 2`.  Hence Peterfalvi I Ch. I §2
  (`cardInvGeTwo`, then `cardKsetEqInv`, both in `ThmF/Bender/`) applied inside `↥F` gives
  `2 ≤ |Inv H_F| = |Kset H_F t_F|`, so `Kset H_F t_F` contains some `k' ≠ 1`.
* Untangling `k' ∈ Kset H_F t_F = invertedBy (twoPoint H_F t_F) t_F`: membership in
  `twoPoint (H_F) t_F` unfolds (through `twoPoint_subgroupOf_inf`) to
  `(k' : G) ∈ twoPoint H t`, the inversion relation is preserved by the coercion `↥F → G`
  (a monoid homomorphism), and `k' ≠ 1` gives `(k' : G) ≠ 1`.  Since `k' ∈ F = N_G(X)`, the
  element `k = (k' : G)` is the required witness.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV12

open LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF

/-- `HasFourGroup` is monotone along subgroup inclusions. -/
private lemma hasFourGroup_mono {G : Type} [Group G] {A B : Subgroup G} (hAB : A ≤ B)
    (h : HasFourGroup ↥A) : HasFourGroup ↥B := by
  obtain ⟨a, b, ha, hb, hne, hcomm⟩ := h
  refine ⟨⟨a, hAB a.2⟩, ⟨b, hAB b.2⟩, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]; exact ha
  · rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]; exact hb
  · intro hh
    have hh' : (a : G) = (b : G) := congrArg (fun z : ↥B => (z : G)) hh
    exact hne (Subtype.ext hh')
  · apply Subtype.ext
    exact congrArg (fun z : ↥A => (z : G)) hcomm

/-- The two-point stabiliser commutes with passing to `↥F`: for `t ∈ F`,
`twoPoint ((F ⊓ H).subgroupOf F) t = (twoPoint H t).subgroupOf F`.  (Conjugation by `t` on `↥F`
is conjugation by `t` in `G`, and `F` is `t`-invariant as `t ∈ F`.) -/
private lemma twoPoint_subgroupOf_inf {G : Type} [Group G] (F H : Subgroup G) {t : G}
    (htF : t ∈ F) :
    twoPoint ((F ⊓ H).subgroupOf F) (⟨t, htF⟩ : ↥F) = (twoPoint H t).subgroupOf F := by
  ext x
  constructor
  · intro hx
    have h1 : (↑x : G) ∈ F ⊓ H := Subgroup.mem_subgroupOf.mp hx.1
    have h2 : (((⟨t, htF⟩ : ↥F)⁻¹ * x * (⟨t, htF⟩ : ↥F)) : G) ∈ F ⊓ H :=
      Subgroup.mem_subgroupOf.mp (Work.Models.mem_conj_iff.mp hx.2)
    exact Subgroup.mem_subgroupOf.mpr ⟨h1.2, Work.Models.mem_conj_iff.mpr h2.2⟩
  · intro hx
    have hxA : (↑x : G) ∈ H := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).1
    have hxB : (↑x : G) ∈ conj t H := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).2
    have hxC : t⁻¹ * (↑x : G) * t ∈ H := Work.Models.mem_conj_iff.mp hxB
    refine ⟨?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr ⟨x.2, hxA⟩
    · refine Work.Models.mem_conj_iff.mpr ?_
      exact Subgroup.mem_subgroupOf.mpr
        ⟨F.mul_mem (F.mul_mem (F.inv_mem htF) x.2) htF, hxC⟩

open LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF in theorem exists_k_normalizing {G : Type} [Group G] [Finite G] {H X : Subgroup G} {t : G} (hH : IsStronglyEmbedded H) (ht2 : orderOf t = 2) (htH : t ∉ H) (hX : X ≤ centD H t) (hX3 : 3 ≤ (fixedPts H X).ncard) (hfour : HasFourGroup (Subgroup.centralizer (X : Set G))) (hP1b : ∀ X' F : Subgroup G, 3 ≤ (fixedPts H X').ncard → involutions (Subgroup.centralizer (X' : Set G) : Set G) ⊆ F → F ≤ Subgroup.normalizer (X' : Set G) → ∀ g : G, X' ≤ conj g H → IsStronglyEmbedded ((F ⊓ conj g H).subgroupOf F)) : ∃ k ∈ invertedBy (twoPoint H t) t, k ≠ 1 ∧ k ∈ Subgroup.normalizer (X : Set G) := by
  -- Work inside the normaliser `F = N_G(X)` of `X`.
  let F : Subgroup G := Subgroup.normalizer (X : Set G)
  -- `X ≤ V ≤ D ≤ H`.
  have hXH : X ≤ H := by
    intro x hx
    have h1 : x ∈ centD H t := hX hx
    change x ∈ twoPoint H t ⊓ Subgroup.centralizer ({t} : Set G) at h1
    exact (Subgroup.mem_inf.mp h1).1.1
  -- `X` commutes with `t`.
  have hXc : X ≤ Subgroup.centralizer ({t} : Set G) := by
    intro x hx
    have h1 : x ∈ centD H t := hX hx
    change x ∈ twoPoint H t ⊓ Subgroup.centralizer ({t} : Set G) at h1
    exact h1.2
  -- (P1b) with `F = N_G(X)`, `X' = X` and `g = 1`.
  have hse : IsStronglyEmbedded ((F ⊓ H).subgroupOf F) := by
    have h := hP1b X F hX3 (fun u hu => Subgroup.centralizer_le_normalizer (X : Set G) hu.1)
      (le_refl F) 1 (by rw [Work.Models.conj_one]; exact hXH)
    rwa [Work.Models.conj_one] at h
  -- The four-group of `C_G(X)` lies in `N_G(X)`.
  have hfourF : HasFourGroup ↥F :=
    hasFourGroup_mono (Subgroup.centralizer_le_normalizer (X : Set G)) hfour
  -- `t` normalises `X` because it centralises it.
  have htF : t ∈ F := by
    change t ∈ Subgroup.normalizer (X : Set G)
    have hy : ∀ y ∈ X, t * y * t⁻¹ = y := by
      intro y hy
      have hc : t * y = y * t := (Subgroup.mem_centralizer_iff.mp (hXc hy)) t (by simp)
      rw [hc]; group
    have hy' : ∀ y ∈ X, t⁻¹ * y * t = y := by
      intro y hy
      have hc : t * y = y * t := (Subgroup.mem_centralizer_iff.mp (hXc hy)) t (by simp)
      rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx; rwa [hy x hx]
    · intro hx
      have h3 : t⁻¹ * (t * x * t⁻¹) * t ∈ X := by
        rw [hy' (t * x * t⁻¹) hx]; exact hx
      rwa [show t⁻¹ * (t * x * t⁻¹) * t = x by group] at h3
  have htF2 : orderOf (⟨t, htF⟩ : ↥F) = 2 := by
    rw [Subgroup.orderOf_mk]; exact ht2
  have htHF : (⟨t, htF⟩ : ↥F) ∉ (F ⊓ H).subgroupOf F := by
    intro h
    rw [Subgroup.mem_subgroupOf] at h
    exact htH (Subgroup.mem_inf.mp h).2
  -- Peterfalvi I Ch. I §2 inside `↥F`: `H_F` has at least two involutions, hence `|K| ≥ 2`.
  have hcard2 : 2 ≤ (involutions (((F ⊓ H).subgroupOf F : Subgroup ↥F)) : Set ↥F).ncard :=
    Work.ThmF.Bender.cardInvGeTwo hse hfourF
  have hkcard : (Kset ((F ⊓ H).subgroupOf F) (⟨t, htF⟩ : ↥F)).ncard
      = (involutions (((F ⊓ H).subgroupOf F : Subgroup ↥F)) : Set ↥F).ncard :=
    Work.ThmF.Bender.cardKsetEqInv (H := (F ⊓ H).subgroupOf F) hse htF2 htHF
  have hex : ∃ k' ∈ Kset ((F ⊓ H).subgroupOf F) (⟨t, htF⟩ : ↥F), k' ≠ 1 := by
    by_contra hc
    have hc' : ∀ k' ∈ Kset ((F ⊓ H).subgroupOf F) (⟨t, htF⟩ : ↥F), k' = 1 := by
      intro k' hk'
      by_contra hne
      exact hc ⟨k', hk', hne⟩
    have hsub : Kset ((F ⊓ H).subgroupOf F) (⟨t, htF⟩ : ↥F) ⊆ ({1} : Set ↥F) := by
      intro x hx
      rw [Set.mem_singleton_iff]
      exact hc' x hx
    have hle : (Kset ((F ⊓ H).subgroupOf F) (⟨t, htF⟩ : ↥F)).ncard ≤ 1 := by
      have h := Set.ncard_le_ncard hsub
      simpa using h
    rw [hkcard] at hle
    omega
  obtain ⟨k', hk'K, hk'1⟩ := hex
  have hk' : k' ∈ twoPoint ((F ⊓ H).subgroupOf F) (⟨t, htF⟩ : ↥F)
      ∧ (⟨t, htF⟩ : ↥F) * k' * (⟨t, htF⟩ : ↥F)⁻¹ = k'⁻¹ :=
    (Work.ThmF.mem_Kset_iff).mp hk'K
  -- Untangle `k' ∈ Kset H_F t_F` back in `G`.
  refine ⟨(k' : G), ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · have h2 : k' ∈ (twoPoint H t).subgroupOf F := by
        rw [← twoPoint_subgroupOf_inf F H htF]
        exact hk'.1
      exact Subgroup.mem_subgroupOf.mp h2
    · have h := congrArg (fun z : ↥F => (z : G)) hk'.2
      simpa using h
  · intro h1
    exact hk'1 (Subtype.ext h1)
  · exact k'.2

end Work.ThmF.ChV12

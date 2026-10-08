import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.Tau
import Submission.Work.Tame.mem_AU_iff
import Submission.Work.Tame.inConjAU_iff
import Submission.Work.Tame.cfInner_tau_one
import Submission.Work.Tame.tau_apply_of_mem_AL
import Submission.Work.Tame.tau_eq_zero_of_not_isConj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Tame

open Classical

/-- For `L ∈ 𝔏_j` one has `L ∈ 𝔄_L` (take `H = 1` in (9.2), respectively `L ∈ {L}` when
`j = 0`).  This is the case `A = A' = L` in the hypothesis that `θ` is constant on `𝔄_L`. -/
theorem self_mem_ALofIdx {X : Type*} [Group X] {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    {j : Idx n} {L : ↥(Lgrp Lhat)} (hL : (L : X) ∈ LofIdx Lhat n Hs j) :
    (L : X) ∈ ALofIdx Lhat n Hs j (L : X) := by
  cases j <;> simp [ALofIdx, AL]

/-- A class function takes the same value on conjugate elements. -/
theorem IsClassFun.apply_of_isConj {X : Type*} [Group X] {f : X → ℂ}
    (hf : CharCore.IsClassFun f) {a b : X} (h : IsConj a b) : f a = f b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc]
  exact (hf a c).symm

/-- The Dade map `τ` of (9.4) is defined by induction from class functions, hence is a class
function of `X`. -/
theorem isClassFun_tau {X : Type*} [Group X] [Fintype X] (Lhat : Set X) (n : ℕ)
    (Hs : Fin n → Subgroup X) (α : ↥(Lgrp Lhat) → ℂ) :
    CharCore.IsClassFun (tau Lhat n Hs α) := by
  have heq : tau Lhat n Hs α =
      Induction.indFun (Lgrp Lhat) α +
        ∑ i : Fin n, Induction.indFun (Lgrp (Hs i : Set X))
          (alphaI1LM Lhat (Hs i) α - alphaI2LM Lhat (Hs i) α) := by
    funext x
    rw [tau_apply]
    simp only [Pi.add_apply, Finset.sum_apply]
  rw [heq]
  exact (Work.Induction.isClassFun_indFun _ _).add
    (CharCore.IsClassFun.sum _ _ (fun i _ => Work.Induction.isClassFun_indFun _ _))


/-- **Feit–Thompson Lemma 9.4, first identity** (p. 808).  Let `θ` be a class function of `𝔛`
which is constant on `𝔄_L` for every `L ∈ ⋃_{i=0}^n 𝔏_i`.  If `α ∈ 𝓘₀(L̂)` and `α^τ` is defined by
(9.4) then `(α^τ, θ)_𝔛 = (α, θ|_𝔏)_𝔏`.

Feit–Thompson's proof: since `θ` is constant on `𝔄_L`, Lemma 9.1 gives that
`{α·θ̄|_𝔏}^τ = α^τ·θ̄` pointwise; Lemma 9.3 applied to `α·θ̄|_𝔏` then gives the identity. -/
theorem cfInner_tau_theta {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} (h : IsTamelyImbedded Lhat n Hs) (hD : HasTameData Lhat n Hs)
    {α : ↥(Lgrp Lhat) → ℂ} (hα : α ∈ I0 Lhat) {θ : X → ℂ} (hθc : CharCore.IsClassFun θ)
    (hθ : ∀ j : Idx n, ∀ L : ↥(Lgrp Lhat), (L : X) ∈ LofIdx Lhat n Hs j →
      ∀ A ∈ ALofIdx Lhat n Hs j (L : X),
      ∀ A' ∈ ALofIdx Lhat n Hs j (L : X), θ A = θ A') :
    Coherence.cfInner (tau Lhat n Hs α) θ =
      Coherence.cfInner α (fun l : ↥(Lgrp Lhat) => θ (l : X)) := by
  -- `θ̄ = conj ∘ θ`, viewed as a function on `X`, and its restriction `α · θ̄|_𝔏` to `𝔏`
  set g : X → ℂ := fun x => starRingEnd ℂ (θ x) with hg
  have hgc : CharCore.IsClassFun g := by
    rw [hg]; exact hθc.conj
  set β : ↥(Lgrp Lhat) → ℂ := α * Induction.resFun (Lgrp Lhat) g with hβ
  -- `β = α · θ̄|_𝔏 ∈ 𝓒₀(L̂)`
  have hβC0 : β ∈ C0 Lhat := by
    rw [mem_C0]
    refine ⟨?_, ?_, ?_⟩
    · rw [hβ]
      exact CharCore.IsClassFun.mul hα.1.isClassFun (Work.Induction.isClassFun_resFun hgc)
    · intro l hl
      rw [hβ]
      simp only [Pi.mul_apply, Induction.resFun_apply]
      rw [hα.2.1 l hl, zero_mul]
    · rw [hβ]
      simp only [Pi.mul_apply, Induction.resFun_apply]
      rw [hα.2.2, zero_mul]
  -- Lemma 9.1: `{α θ̄|_𝔏}^τ = α^τ θ̄` pointwise
  have hprod : tau Lhat n Hs β = fun x => tau Lhat n Hs α x * g x := by
    funext x
    by_cases hx : inConjAU Lhat n Hs x
    · obtain ⟨j, L, hL, A, hA, hc⟩ := hx
      have hLmem := self_mem_ALofIdx hL
      have hθA : θ A = θ L := hθ j L hL A hA L hLmem
      have hθx : θ x = θ L := by
        rw [IsClassFun.apply_of_isConj hθc hc]; exact hθA
      have hαx : tau Lhat n Hs α x = α L := by
        rw [IsClassFun.apply_of_isConj (isClassFun_tau Lhat n Hs α) hc]
        exact tau_apply_of_mem_AL h hD (I0_subset_C0 hα) hL hA
      have hβx : tau Lhat n Hs β x = α L * g L := by
        rw [IsClassFun.apply_of_isConj (isClassFun_tau Lhat n Hs β) hc]
        rw [tau_apply_of_mem_AL h hD hβC0 hL hA]
        rw [hβ]
        simp only [Pi.mul_apply, Induction.resFun_apply]
      have hgx : g x = g L := by rw [hg]; simp [hθx]
      rw [hβx, hαx, hgx]
    · have hα0 : tau Lhat n Hs α x = 0 :=
        tau_eq_zero_of_not_isConj h hD (I0_subset_C0 hα) hx
      have hβ0 : tau Lhat n Hs β x = 0 := tau_eq_zero_of_not_isConj h hD hβC0 hx
      rw [hβ0, hα0, zero_mul]
  have hstep1 : Coherence.cfInner (tau Lhat n Hs α) θ
      = Coherence.cfInner (tau Lhat n Hs β) 1 := by
    rw [hprod, Coherence.cfInner_apply, Coherence.cfInner_apply]
    congr 1
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [hg]
    simp
  have hstep3 : Coherence.cfInner β 1
      = Coherence.cfInner α (fun l : ↥(Lgrp Lhat) => θ (l : X)) := by
    rw [Coherence.cfInner_apply, Coherence.cfInner_apply]
    congr 1
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hβ, hg]
    simp
  rw [hstep1, cfInner_tau_one h hD hβC0, hstep3]

end Work.Tame

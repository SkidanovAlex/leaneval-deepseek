import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.Tau
import Submission.Work.Tame.mem_AU_iff
import Submission.Work.Tame.punct_subset_conjAU
import Submission.Work.Tame.cfInner_tau_one
import Submission.Work.Tame.tau_apply_one
import Submission.Work.Tame.tau_apply_of_mem_AL
import Submission.Work.Tame.tau_eq_zero_of_not_isConj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Tame

open Classical

set_option linter.unusedSectionVars false

noncomputable section

variable {X : Type*} [Group X] [Fintype X]

/-! ### elementary helpers -/

theorem cftt_self_mem_ALofIdx {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    {j : Idx n} {L : ↥(Lgrp Lhat)} (hL : (L : X) ∈ LofIdx Lhat n Hs j) :
    (L : X) ∈ ALofIdx Lhat n Hs j (L : X) := by
  cases j <;> simp [ALofIdx, AL]

theorem cftt_apply_of_isConj {f : X → ℂ}
    (hf : CharCore.IsClassFun f) {a b : X} (hc : IsConj a b) : f a = f b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  rw [← hc]
  exact (hf a c).symm

theorem cftt_isClassFun_tau {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (α : ↥(Lgrp Lhat) → ℂ) :
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

/-- The normalisation `𝔎_i ⊓ 𝔏 = ⊥` supplied by `HasTameData`. -/
theorem cftt_hinf {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hD : HasTameData Lhat n Hs) :
    ∀ i : Fin n, Hs i ⊓ Lgrp Lhat = ⊥ := by
  rcases hD with hne | hn
  · exact h.supp_inf hne
  · subst hn; intro i; exact i.elim0

/-- **Feit–Thompson Lemma 9.1, value part, on `L̂` itself**: for `l ∈ 𝔏` with `l ∈ L̂`,
`α^τ(l) = α(l)`.  This is the form needed to compare `β^τ|_𝔏` with `β`. -/
theorem cftt_tau_at_mem_Lhat {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hD : HasTameData Lhat n Hs)
    {β : ↥(Lgrp Lhat) → ℂ} (hβ : β ∈ C0 Lhat) (l : ↥(Lgrp Lhat))
    (hl : (l : X) ∈ Lhat) : tau Lhat n Hs β (l : X) = β l := by
  by_cases h1 : (l : X) = 1
  · have hl1 : l = 1 := Subtype.ext h1
    rw [hl1]
    change tau Lhat n Hs β (1 : X) = β (1 : ↥(Lgrp Lhat))
    rw [tau_apply_one (cftt_hinf h hD) hβ.2.2, hβ.2.2]
  · by_cases h0 : (l : X) ∈ L0set Lhat
    · exact tau_apply_of_mem_AL h hD hβ (j := none) h0 (cftt_self_mem_ALofIdx (j := none) h0)
    · have hlD : (l : X) ∈ Dset Lhat := ⟨hl, h1, fun hc => h0 ⟨hl, h1, hc⟩⟩
      obtain ⟨l', hl', hc, i, _hcent, hle⟩ := h.cover (l : X) hlD
      have hl'd : l' ∈ Dset Lhat := mem_Dset_of_isConj h hlD hl' hc
      have hL' : ((⟨l', h.sub_norm hl'⟩ : ↥(Lgrp Lhat)) : X) ∈ LofIdx Lhat n Hs (some i) :=
        ⟨hl'd, hle⟩
      have hA' : l' ∈ ALofIdx Lhat n Hs (some i) l' := by
        simp only [ALofIdx, AL]
        exact ⟨1, (Hs i).one_mem, by simp, by simp⟩
      have hval : tau Lhat n Hs β l' = β ⟨l', h.sub_norm hl'⟩ :=
        tau_apply_of_mem_AL h hD hβ hL' hA'
      have hconj : IsConj (l : X) l' := hc
      have htau : tau Lhat n Hs β (l : X) = tau Lhat n Hs β l' :=
        cftt_apply_of_isConj (cftt_isClassFun_tau (Lhat := Lhat) (n := n) (Hs := Hs) β) hconj
      obtain ⟨m, hm, hm'⟩ := h.conj hl hl' hconj
      have hbeta : β ⟨l', h.sub_norm hl'⟩ = β l := by
        have hmem : (⟨l', h.sub_norm hl'⟩ : ↥(Lgrp Lhat)) = ⟨m, hm⟩ * l * ⟨m, hm⟩⁻¹ := by
          ext
          simpa using hm'
        rw [hmem, hβ.1 l ⟨m, hm⟩]
      rw [htau, hval, hbeta]

/-! ### the first identity of Lemma 9.4 -/

theorem cftt_cfInner_tau_theta {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} (h : IsTamelyImbedded Lhat n Hs) (hD : HasTameData Lhat n Hs)
    {α : ↥(Lgrp Lhat) → ℂ} (hα : α ∈ I0 Lhat) {θ : X → ℂ} (hθc : CharCore.IsClassFun θ)
    (hθ : ∀ j : Idx n, ∀ L : ↥(Lgrp Lhat), (L : X) ∈ LofIdx Lhat n Hs j →
      ∀ A ∈ ALofIdx Lhat n Hs j (L : X),
      ∀ A' ∈ ALofIdx Lhat n Hs j (L : X), θ A = θ A') :
    Coherence.cfInner (tau Lhat n Hs α) θ =
      Coherence.cfInner α (fun l : ↥(Lgrp Lhat) => θ (l : X)) := by
  set g : X → ℂ := fun x => starRingEnd ℂ (θ x) with hg
  have hgc : CharCore.IsClassFun g := by
    rw [hg]; exact hθc.conj
  set β : ↥(Lgrp Lhat) → ℂ := α * Induction.resFun (Lgrp Lhat) g with hβ
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
  have hprod : tau Lhat n Hs β = fun x => tau Lhat n Hs α x * g x := by
    funext x
    by_cases hx : inConjAU Lhat n Hs x
    · obtain ⟨j, L, hL, A, hA, hc⟩ := hx
      have hLmem := cftt_self_mem_ALofIdx hL
      have hθA : θ A = θ L := hθ j L hL A hA L hLmem
      have hθx : θ x = θ L := by
        rw [cftt_apply_of_isConj hθc hc]; exact hθA
      have hαx : tau Lhat n Hs α x = α L := by
        rw [cftt_apply_of_isConj (cftt_isClassFun_tau (Lhat := Lhat) (n := n) (Hs := Hs) α) hc]
        exact tau_apply_of_mem_AL h hD (I0_subset_C0 hα) hL hA
      have hβx : tau Lhat n Hs β x = α L * g L := by
        rw [cftt_apply_of_isConj (cftt_isClassFun_tau (Lhat := Lhat) (n := n) (Hs := Hs) β) hc]
        rw [tau_apply_of_mem_AL h hD hβC0 hL hA]
        rw [hβ]
        simp only [Pi.mul_apply, Induction.resFun_apply]
      have hgx : g x = g L := by rw [hg]; simp [hθx]
      rw [hβx, hαx, hgx]
    · have hα0 : tau Lhat n Hs α x = 0 := tau_eq_zero_of_not_isConj h hD (I0_subset_C0 hα) hx
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


end

/-- **Feit–Thompson Lemma 9.4, second identity** (p. 808).  If `L̂` is tamely imbedded in `X`,
`α, β ∈ 𝓘₀(L̂)` and `α^τ`, `β^τ` are defined by (9.4) then `(α^τ, β^τ)_𝔛 = (α, β)_𝔏`.

This is the *isometry* property of the Dade map on `𝓘₀(L̂)`, and the key hypothesis in
Definition 10.1.  Feit–Thompson's proof: by Lemma 9.1, `β^τ` is a generalized character of `𝔛`
which is constant on `𝔄_L` for every `L ∈ ⋃_{i=0}^n 𝔏_i`, so the first identity of Lemma 9.4 with
`θ = β^τ` gives `(α^τ, β^τ)_𝔛 = (α, β^τ|_𝔏)_𝔏`; then `β^τ|_𝔏 = β` on `L̂^#` (Lemma 9.1) while
`α` and `β^τ|_𝔏 - β` both vanish off `L̂^#` and at `1`, giving `(α, β^τ|_𝔏)_𝔏 = (α, β)_𝔏`. -/
theorem cfInner_tau_tau {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} (h : IsTamelyImbedded Lhat n Hs) (hD : HasTameData Lhat n Hs)
    {α β : ↥(Lgrp Lhat) → ℂ} (hα : α ∈ I0 Lhat) (hβ : β ∈ I0 Lhat) :
    Coherence.cfInner (tau Lhat n Hs α) (tau Lhat n Hs β) = Coherence.cfInner α β := by
  have hβc : β ∈ C0 Lhat := I0_subset_C0 hβ
  have hθc : CharCore.IsClassFun (tau Lhat n Hs β) :=
    cftt_isClassFun_tau (Lhat := Lhat) (n := n) (Hs := Hs) β
  have hθ : ∀ j : Idx n, ∀ L : ↥(Lgrp Lhat), (L : X) ∈ LofIdx Lhat n Hs j →
      ∀ A ∈ ALofIdx Lhat n Hs j (L : X),
      ∀ A' ∈ ALofIdx Lhat n Hs j (L : X),
      tau Lhat n Hs β A = tau Lhat n Hs β A' := by
    intro j L hL A hA A' hA'
    rw [tau_apply_of_mem_AL h hD hβc hL hA, tau_apply_of_mem_AL h hD hβc hL hA']
  have hfirst := cftt_cfInner_tau_theta h hD hα hθc hθ
  have hγ : Coherence.cfInner α
      (fun l : ↥(Lgrp Lhat) => tau Lhat n Hs β (l : X) - β l) = 0 := by
    rw [Coherence.cfInner_apply]
    have hzero : ∀ l : ↥(Lgrp Lhat),
        α l * starRingEnd ℂ (tau Lhat n Hs β (l : X) - β l) = 0 := by
      intro l
      by_cases hl : (l : X) ∈ Lhat
      · rw [cftt_tau_at_mem_Lhat h hD hβc l hl, sub_self, map_zero, mul_zero]
      · rw [hα.2.1 l hl, zero_mul]
    rw [Finset.sum_eq_zero (fun l _ => hzero l), mul_zero]
  have h2 : Coherence.cfInner α (fun l : ↥(Lgrp Lhat) => tau Lhat n Hs β (l : X))
      = Coherence.cfInner α β := by
    have hdecomp : (fun l : ↥(Lgrp Lhat) => tau Lhat n Hs β (l : X)) =
        β + (fun l : ↥(Lgrp Lhat) => tau Lhat n Hs β (l : X) - β l) := by
      funext l
      simp only [Pi.add_apply]
      ring
    rw [hdecomp, Coherence.cfInner_add_right, hγ, add_zero]
  rw [hfirst, h2]

end Work.Tame

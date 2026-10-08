import Mathlib
import Submission.Work.Tame.Instances
import Submission.Work.Tame.Defs
import Submission.Work.Tame.Tau
import Submission.Work.Tame.Hyp
import Submission.Work.Tame.Chapter10
import Submission.Work.Tame.irr_vanishes_off_hatN
import Submission.Work.Tame.indFun_eq_of_mem_hatNp
import Submission.Work.Tame.cfInner_tau_theta
import Submission.Work.Tame.irr_not_trivial_on_K
import Submission.Work.Tame.tau_apply_one
import Submission.Work.Tame.lem92b

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Tame

open Classical

/-- The degree `f 1` of a virtual character of a finite group is an integer. -/
private theorem vchar_apply_one_int {G : Type*} [Group G] [Fintype G] {f : G → ℂ}
    (hf : CharCore.IsVChar f) : ∃ z : ℤ, f 1 = (z : ℂ) := by
  classical
  obtain ⟨c, hc⟩ := CharCore.isVChar_iff_exists_int_coeffs.mp hf
  have hdeg : ∀ χ : {χ : G → ℂ // χ ∈ CharCore.Irr G},
      ∃ n : ℕ, 0 < n ∧ (χ : G → ℂ) 1 = (n : ℂ) :=
    fun χ => Coherence.irr_degree_pos ((CharCore.mem_Irr_iff_coherence).mp χ.2)
  choose n _hn hn1 using hdeg
  refine ⟨∑ χ, c χ * (n χ : ℤ), ?_⟩
  rw [hc, Finset.sum_apply]
  rw [Finset.sum_congr rfl (fun χ _ => by rw [Pi.smul_apply, smul_eq_mul, hn1 χ])]
  push_cast
  rfl

/-- **The Brauer/Feit "T. I. isometry" in the `Ñ`-setting.**  Let `η` be a class function of
`𝔑 = N(𝔎)` vanishing outside `Ñ^#`.  Then induction from `𝔑` to `X` preserves the inner product
of `η` with itself.

This is the statement "the map `θ₁ - θ₂ ↦ (θ₁ - θ₂)^*` is an isometry" used in the proof of
Feit–Thompson Lemma 10.3: by Frobenius reciprocity the inner product of `Ind η` with itself is
`⟨η, Res Ind η⟩`, and `Res_{𝔑}(Ind η)` agrees with `η` on the support of `η` by
`indFun_eq_of_mem_hatNp`. -/
private theorem indFun_norm_sq_hatNp_aux {X : Type*} [Group X] [Fintype X] {Lhat : Set X}
    {n : ℕ} {Hs : Fin n → Subgroup X} (h : IsTamelyImbedded Lhat n Hs)
    (hD : (Dset Lhat).Nonempty) (i : Fin n)
    {η : ↥(Lgrp (Hs i : Set X)) → ℂ} (hηc : CharCore.IsClassFun η)
    (hηv : ∀ N : ↥(Lgrp (Hs i : Set X)), (N : X) ∉ hatNp (Hs i) → η N = 0) :
    Coherence.cfInner (Induction.indFun (Lgrp (Hs i : Set X)) η)
      (Induction.indFun (Lgrp (Hs i : Set X)) η) = Coherence.cfInner η η := by
  classical
  change CharCore.cfInner (Induction.indFun (Lgrp (Hs i : Set X)) η)
      (Induction.indFun (Lgrp (Hs i : Set X)) η) = CharCore.cfInner η η
  rw [Work.Induction.frobenius_reciprocity (Lgrp (Hs i : Set X)) η
      (Induction.indFun (Lgrp (Hs i : Set X)) η) (Induction.isClassFun_indFun _ _)]
  rw [CharCore.cfInner_apply, CharCore.cfInner_apply]
  congr 1
  refine Finset.sum_congr rfl (fun N _ => ?_)
  by_cases hN : (N : X) ∈ hatNp (Hs i)
  · rw [Induction.resFun_apply, indFun_eq_of_mem_hatNp h hD i hηc hηv hN]
  · rw [hηv N hN]
    simp

theorem ft10_3_key_v2 {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} {i : Fin n} (h : Hyp10_2 Lhat n Hs i)
    {S : Finset (↥(Lgrp Lhat) → ℂ)} (hcoh : FTCoherent Lhat n Hs S)
    (hv : ∀ χ ∈ S, CharCore.IsVChar χ)
    (horth : ∀ χ ∈ S, ∀ ψ ∈ S, χ ≠ ψ → Coherence.cfInner χ ψ = 0)
    (h2 : ∃ χ ∈ S, ∃ ψ ∈ S, χ ≠ ψ ∧ χ ∈ CharCore.Irr ↥(Lgrp Lhat) ∧
      ψ ∈ CharCore.Irr ↥(Lgrp Lhat))
    {τ' : (↥(Lgrp Lhat) → ℂ) →ₗ[ℤ] (X → ℂ)} (hτ' : IsExtension Lhat n Hs S τ')
    {lam : ↥(Lgrp Lhat) → ℂ} (hlam : lam ∈ S)
    {θ₁ θ₂ : ↥(Lgrp (Hs i : Set X)) → ℂ}
    (hθ₁ : θ₁ ∈ CharCore.Irr ↥(Lgrp (Hs i : Set X)))
    (hθ₂ : θ₂ ∈ CharCore.Irr ↥(Lgrp (Hs i : Set X)))
    {α : ↥(Hs i) → ℂ}
    (hα1 : ∀ hh : ↥(Hs i), θ₁ ⟨(hh : X), (Hs i).le_normalizer hh.2⟩ = α hh)
    (hα2 : ∀ hh : ↥(Hs i), θ₂ ⟨(hh : X), (Hs i).le_normalizer hh.2⟩ = α hh)
    (hα0 : Coherence.cfInner α (1 : ↥(Hs i) → ℂ) = 0) :
    Coherence.cfInner (fun N : ↥(Lgrp (Hs i : Set X)) => τ' lam (N : X)) (θ₁ - θ₂) = 0 := by
  classical
  by_cases hθeq : θ₁ = θ₂
  · rw [hθeq, sub_self]; simp
  -- `𝔇 ≠ ∅`
  have hne : (Dset Lhat).Nonempty := by
    rcases h.tameData with hd | hn
    · exact hd
    · subst hn; exact Fin.elim0 i
  have hθ₁C : θ₁ ∈ Coherence.Irr ↥(Lgrp (Hs i : Set X)) :=
    (CharCore.mem_Irr_iff_coherence).mp hθ₁
  have hθ₂C : θ₂ ∈ Coherence.Irr ↥(Lgrp (Hs i : Set X)) :=
    (CharCore.mem_Irr_iff_coherence).mp hθ₂
  -- the two characters agree at `1`
  have hθ1one : θ₁ 1 = α 1 := by
    have h1 := hα1 (1 : ↥(Hs i))
    rwa [show (⟨(((1 : ↥(Hs i)) : X)), (Hs i).le_normalizer (1 : ↥(Hs i)).2⟩ :
        ↥(Lgrp (Hs i : Set X))) = 1 from by ext; simp] at h1
  have hθ2one : θ₂ 1 = α 1 := by
    have h1 := hα2 (1 : ↥(Hs i))
    rwa [show (⟨(((1 : ↥(Hs i)) : X)), (Hs i).le_normalizer (1 : ↥(Hs i)).2⟩ :
        ↥(Lgrp (Hs i : Set X))) = 1 from by ext; simp] at h1
  -- `θ_j|_𝔎` is orthogonal to the principal character of `𝔎`
  have hα01 : Coherence.cfInner
      (fun hh : ↥(Hs i) => θ₁ ⟨(hh : X), (Hs i).le_normalizer hh.2⟩) (1 : ↥(Hs i) → ℂ) = 0 := by
    rw [show (fun hh : ↥(Hs i) => θ₁ ⟨(hh : X), (Hs i).le_normalizer hh.2⟩) = α
      from funext hα1]
    exact hα0
  have hα02 : Coherence.cfInner
      (fun hh : ↥(Hs i) => θ₂ ⟨(hh : X), (Hs i).le_normalizer hh.2⟩) (1 : ↥(Hs i) → ℂ) = 0 := by
    rw [show (fun hh : ↥(Hs i) => θ₂ ⟨(hh : X), (Hs i).le_normalizer hh.2⟩) = α
      from funext hα2]
    exact hα0
  have hk₁ : ∃ H : ↥(Hs i), θ₁ ⟨(H : X), (Hs i).le_normalizer H.2⟩ ≠ θ₁ 1 :=
    irr_not_trivial_on_K (K := Hs i) hθ₁ hα01
  have hk₂ : ∃ H : ↥(Hs i), θ₂ ⟨(H : X), (Hs i).le_normalizer H.2⟩ ≠ θ₂ 1 :=
    irr_not_trivial_on_K (K := Hs i) hθ₂ hα02
  have hKne : Hs i ≠ ⊥ := h.tamely.supp_ne_bot hne i
  -- `η = θ₁ - θ₂` is a class function vanishing off `Ñ_i^#`
  have hηc : CharCore.IsClassFun (fun N : ↥(Lgrp (Hs i : Set X)) => θ₁ N - θ₂ N) :=
    (CharCore.isClassFun_of_mem_Irr hθ₁).sub (CharCore.isClassFun_of_mem_Irr hθ₂)
  have hηv : ∀ N : ↥(Lgrp (Hs i : Set X)), (N : X) ∉ hatNp (Hs i) → θ₁ N - θ₂ N = 0 := by
    intro N hN
    by_cases hN1 : (N : X) = 1
    · have hN1' : N = 1 := Subtype.ext hN1
      rw [hN1', hθ1one, hθ2one, sub_self]
    · have hNmem : (N : X) ∉ hatN (Hs i) := by
        intro hmem
        rw [hatN_eq_hatNp_union_singleton hKne] at hmem
        rcases hmem with hmem | hmem
        · exact hN hmem
        · exact hN1 (by simpa using hmem)
      by_cases hNK : (N : X) ∈ (Hs i : Set X)
      · have h1 : θ₁ N = α ⟨(N : X), hNK⟩ := by
          have h2 := hα1 ⟨(N : X), hNK⟩
          rwa [show (⟨((⟨(N : X), hNK⟩ : ↥(Hs i)) : X),
              (Hs i).le_normalizer (⟨(N : X), hNK⟩ : ↥(Hs i)).2⟩ :
              ↥(Lgrp (Hs i : Set X))) = N from by ext; rfl] at h2
        have h3 : θ₂ N = α ⟨(N : X), hNK⟩ := by
          have h2 := hα2 ⟨(N : X), hNK⟩
          rwa [show (⟨((⟨(N : X), hNK⟩ : ↥(Hs i)) : X),
              (Hs i).le_normalizer (⟨(N : X), hNK⟩ : ↥(Hs i)).2⟩ :
              ↥(Lgrp (Hs i : Set X))) = N from by ext; rfl] at h2
        rw [h1, h3, sub_self]
      · rw [irr_vanishes_off_hatN h.tamely hne i hθ₁ hk₁ hNmem hNK,
          irr_vanishes_off_hatN h.tamely hne i hθ₂ hk₂ hNmem hNK, sub_self]
  -- it suffices to prove the vanishing of the inner product with the induced character
  have hτlam_c : CharCore.IsClassFun (τ' lam) := (hτ'.2.2 lam hlam).isClassFun
  have hfr : Coherence.cfInner (τ' lam)
        (Induction.indFun (Lgrp (Hs i : Set X))
          (fun N : ↥(Lgrp (Hs i : Set X)) => θ₁ N - θ₂ N))
      = Coherence.cfInner (Work.Induction.resFun (Lgrp (Hs i : Set X)) (τ' lam))
          (fun N : ↥(Lgrp (Hs i : Set X)) => θ₁ N - θ₂ N) :=
    Work.Induction.frobenius_reciprocity_transposed _ _ _ hτlam_c
  change Coherence.cfInner (Work.Induction.resFun (Lgrp (Hs i : Set X)) (τ' lam))
      (fun N : ↥(Lgrp (Hs i : Set X)) => θ₁ N - θ₂ N) = 0
  rw [← hfr]
  set ηstar : X → ℂ := Induction.indFun (Lgrp (Hs i : Set X))
    (fun N : ↥(Lgrp (Hs i : Set X)) => θ₁ N - θ₂ N) with hηstardef
  by_contra hX0
  have hη2 : Coherence.cfInner (fun N : ↥(Lgrp (Hs i : Set X)) => θ₁ N - θ₂ N)
      (fun N : ↥(Lgrp (Hs i : Set X)) => θ₁ N - θ₂ N) = 2 := by
    show Coherence.cfInner (θ₁ - θ₂) (θ₁ - θ₂) = 2
    rw [Coherence.cfInner_sub_left, Coherence.cfInner_sub_right, Coherence.cfInner_sub_right,
      Coherence.irr_cfInner hθ₁C hθ₁C, Coherence.irr_cfInner hθ₁C hθ₂C,
      Coherence.irr_cfInner hθ₂C hθ₁C, Coherence.irr_cfInner hθ₂C hθ₂C]
    rw [if_pos rfl, if_neg hθeq, if_neg (Ne.symm hθeq), if_pos rfl]
    norm_num
  have hηstar1 : ηstar 1 = 0 := by
    rw [hηstardef, Induction.indFun_apply_one]
    simp [hθ1one, hθ2one]
  have hηstar_norm : Coherence.cfInner ηstar ηstar = 2 := by
    rw [hηstardef, indFun_norm_sq_hatNp_aux h.tamely hne i hηc hηv, hη2]
  have hηstar_v : Coherence.IsVChar ηstar := by
    rw [hηstardef]
    exact (CharCore.IsVChar_iff_coherence _).mp
      (Induction.isVChar_indFun ((CharCore.IsVChar.of_mem_Irr hθ₁).sub
        (CharCore.IsVChar.of_mem_Irr hθ₂)))
  obtain ⟨Θ₁, hΘ₁, Θ₂, hΘ₂, hΘne, hΘeq⟩ :=
    Coherence.vchar_norm_two_deg_zero_ordered hηstar_v hηstar1 hηstar_norm
  -- the two distinct irreducible members of `𝓢`
  obtain ⟨χ, hχS, ψ, hψS, hχψ, hχirr, hψirr⟩ := h2
  -- `λ(1)` is an integer
  obtain ⟨e, he⟩ := vchar_apply_one_int (hv lam hlam)
  set X0 : ℂ := Coherence.cfInner (τ' lam) ηstar with hX0def
  set Yχ : ℂ := Coherence.cfInner (τ' χ) ηstar with hYχdef
  set Yψ : ℂ := Coherence.cfInner (τ' ψ) ηstar with hYψdef
  -- the orthogonality of `(τ'(d λ' - e λ))|_𝔑` with `θ₁ - θ₂`
  have key : ∀ (lam2 : ↥(Lgrp Lhat) → ℂ) (hlam2S : lam2 ∈ S)
      (hlam2irr : lam2 ∈ CharCore.Irr ↥(Lgrp Lhat)) (Y : ℂ),
      Y = Coherence.cfInner (τ' lam2) ηstar →
      ((CharCore.irrDeg lam2 : ℤ) : ℂ) * X0 - (e : ℂ) * Y = 0 := by
    intro lam2 hlam2S hlam2irr Y hY
    set ρ : ↥(Lgrp Lhat) → ℂ := (CharCore.irrDeg lam2 : ℤ) • lam - e • lam2 with hρdef
    have hZ : ρ ∈ Coherence.ZSpan0 S := by
      refine Coherence.mem_zSpan0.mpr ⟨?_, ?_⟩
      · rw [hρdef]
        exact AddSubgroup.sub_mem _
          (AddSubgroup.zsmul_mem _ (Coherence.self_mem_zSpan hlam) _)
          (AddSubgroup.zsmul_mem _ (Coherence.self_mem_zSpan hlam2S) _)
      · rw [hρdef]
        have h1 : ((CharCore.irrDeg lam2 : ℤ) • lam) 1
            = ((CharCore.irrDeg lam2 : ℤ) : ℂ) * lam 1 := by
          rw [← Int.cast_smul_eq_zsmul ℂ (CharCore.irrDeg lam2) lam, Pi.smul_apply, smul_eq_mul]
        have h2 : (e • lam2) 1 = (e : ℂ) * lam2 1 := by
          rw [← Int.cast_smul_eq_zsmul ℂ e lam2, Pi.smul_apply, smul_eq_mul]
        rw [Pi.sub_apply, h1, h2, he, CharCore.irrDeg_spec hlam2irr]
        push_cast
        ring
    have hC0 : ρ ∈ C0 Lhat := by
      refine ⟨?_, ?_, (Coherence.mem_zSpan0.mp hZ).2⟩
      · rw [hρdef]
        exact (((hv lam hlam).zsmul _).sub ((CharCore.IsVChar.of_mem_Irr hlam2irr).zsmul _)).isClassFun
      · intro l hl
        exact hcoh.2.1 ρ hZ l hl
    have hτ'ρ : τ' ρ = tau Lhat n Hs ρ := hτ'.1 ρ hZ
    have hres : Coherence.cfInner (fun N : ↥(Lgrp (Hs i : Set X)) => tau Lhat n Hs ρ (N : X))
        (fun N : ↥(Lgrp (Hs i : Set X)) => θ₁ N - θ₂ N) = 0 := by
      change Coherence.cfInner (fun N : ↥(Lgrp (Hs i : Set X)) => tau Lhat n Hs ρ (N : X))
        (θ₁ - θ₂) = 0
      rw [Coherence.cfInner_sub_right, lem92b h.tamely hne hC0 hθ₁ hα01,
        lem92b h.tamely hne hC0 hθ₂ hα02, sub_self]
    have hfr2 : Coherence.cfInner (tau Lhat n Hs ρ) ηstar
        = Coherence.cfInner (Work.Induction.resFun (Lgrp (Hs i : Set X)) (tau Lhat n Hs ρ))
            (fun N : ↥(Lgrp (Hs i : Set X)) => θ₁ N - θ₂ N) :=
      Work.Induction.frobenius_reciprocity_transposed _ _ _ (isClassFun_tau Lhat n Hs ρ)
    have h1 : Coherence.cfInner (tau Lhat n Hs ρ) ηstar = 0 := by
      rw [hfr2]; exact hres
    have h2 : Coherence.cfInner (((CharCore.irrDeg lam2 : ℤ) • (τ' lam)) - (e • (τ' lam2)))
        ηstar = 0 := by
      rw [← h1, ← hτ'ρ, hρdef, map_sub, map_zsmul, map_zsmul]
    have h4 : Coherence.cfInner
        ((((CharCore.irrDeg lam2 : ℤ)) : ℂ) • (τ' lam) - ((e : ℤ) : ℂ) • (τ' lam2))
        ηstar = 0 := by
      rw [show ((CharCore.irrDeg lam2 : ℤ) • (τ' lam)) =
            ((CharCore.irrDeg lam2 : ℤ) : ℂ) • (τ' lam) from by rw [Int.cast_smul_eq_zsmul],
        show (e • (τ' lam2)) = ((e : ℤ) : ℂ) • (τ' lam2) from by rw [Int.cast_smul_eq_zsmul]]
        at h2
      exact h2
    rw [Coherence.cfInner_sub_left, Coherence.cfInner_smul_left, Coherence.cfInner_smul_left]
      at h4
    rw [← hX0def, ← hY] at h4
    exact h4
  have hEqχ : ((CharCore.irrDeg χ : ℤ) : ℂ) * X0 - (e : ℂ) * Yχ = 0 := key χ hχS hχirr Yχ rfl
  have hEqψ : ((CharCore.irrDeg ψ : ℤ) : ℂ) * X0 - (e : ℂ) * Yψ = 0 := key ψ hψS hψirr Yψ rfl
  have hX0ne : X0 ≠ 0 := hX0
  have hdχ : ((CharCore.irrDeg χ : ℤ) : ℂ) ≠ 0 := by
    rw [← Int.cast_zero]
    exact_mod_cast (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (CharCore.irrDeg_pos hχirr)) :
      (CharCore.irrDeg χ : ℤ) ≠ 0)
  have hdψ : ((CharCore.irrDeg ψ : ℤ) : ℂ) ≠ 0 := by
    rw [← Int.cast_zero]
    exact_mod_cast (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (CharCore.irrDeg_pos hψirr)) :
      (CharCore.irrDeg ψ : ℤ) ≠ 0)
  rcases eq_or_ne e 0 with he0 | he0
  · -- the case `λ(1) = 0`
    rw [he0] at hEqχ
    simp only [Int.cast_zero, zero_mul, sub_zero] at hEqχ
    exact (mul_ne_zero hdχ hX0ne) hEqχ
  -- now `Yχ, Yψ ≠ 0`
  have hYχne : Yχ ≠ 0 := by
    intro h0
    have hz : ((CharCore.irrDeg χ : ℤ) : ℂ) * X0 = 0 := by
      have h := sub_eq_zero.mp hEqχ
      rw [h, h0, mul_zero]
    exact (mul_ne_zero hdχ hX0ne) hz
  have hYψne : Yψ ≠ 0 := by
    intro h0
    have hz : ((CharCore.irrDeg ψ : ℤ) : ℂ) * X0 = 0 := by
      have h := sub_eq_zero.mp hEqψ
      rw [h, h0, mul_zero]
    exact (mul_ne_zero hdψ hX0ne) hz
  -- each `τ' λ'` is `±` an irreducible character which is `Θ₁` or `Θ₂`
  have get_pair : ∀ (lam2 : ↥(Lgrp Lhat) → ℂ) (hlam2S : lam2 ∈ S)
      (hlam2irr : lam2 ∈ CharCore.Irr ↥(Lgrp Lhat)) (Y : ℂ),
      Y = Coherence.cfInner (τ' lam2) ηstar → Y ≠ 0 →
      ∃ (σ : X → ℂ) (ε : ℂ), σ ∈ Coherence.Irr X ∧ (σ = Θ₁ ∨ σ = Θ₂) ∧
        (ε = 1 ∨ ε = -1) ∧ τ' lam2 = ε • σ ∧ Y = ε * Coherence.cfInner σ ηstar := by
    intro lam2 hlam2S hlam2irr Y hY hYne
    have hlam2C : lam2 ∈ Coherence.Irr ↥(Lgrp Lhat) := (CharCore.mem_Irr_iff_coherence).mp hlam2irr
    have hlam2v : Coherence.IsVChar (τ' lam2) :=
      (CharCore.IsVChar_iff_coherence _).mp (hτ'.2.2 lam2 hlam2S)
    have hlam2norm : Coherence.cfInner (τ' lam2) (τ' lam2) = 1 := by
      rw [hτ'.2.1.inner_eq lam2 (Coherence.self_mem_zSpan hlam2S) lam2
          (Coherence.self_mem_zSpan hlam2S),
        Coherence.irr_cfInner hlam2C hlam2C, if_pos rfl]
    obtain ⟨σ, hσIrr, hσcase⟩ := Coherence.vchar_norm_one hlam2v hlam2norm
    obtain ⟨ε, hε, hτε⟩ : ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ τ' lam2 = ε • σ := by
      rcases hσcase with h | h
      · exact ⟨1, Or.inl rfl, by rw [h]; simp⟩
      · exact ⟨-1, Or.inr rfl, by rw [h]; simp⟩
    have hYeq : Y = ε * Coherence.cfInner σ ηstar := by
      rw [hY, hτε, Coherence.cfInner_smul_left]
    have hσne : Coherence.cfInner σ ηstar ≠ 0 := by
      intro h0
      exact hYne (by rw [hYeq, h0, mul_zero])
    have hσmem : σ = Θ₁ ∨ σ = Θ₂ := by
      by_contra hc
      push_neg at hc
      apply hσne
      rw [hΘeq, Coherence.cfInner_sub_right, Coherence.irr_cfInner hσIrr hΘ₁,
        Coherence.irr_cfInner hσIrr hΘ₂, if_neg hc.1, if_neg hc.2, sub_zero]
    exact ⟨σ, ε, hσIrr, hσmem, hε, hτε, hYeq⟩
  obtain ⟨σχ, εχ, hσχIrr, hσχmem, hεχ, hτχ, hYχeq⟩ := get_pair χ hχS hχirr Yχ rfl hYχne
  obtain ⟨σψ, εψ, hσψIrr, hσψmem, hεψ, hτψ, hYψeq⟩ := get_pair ψ hψS hψirr Yψ rfl hYψne
  -- `σχ ≠ σψ`
  have hσne : σχ ≠ σψ := by
    intro hcon
    have h1 : Coherence.cfInner (τ' χ) (τ' ψ) = 0 := by
      rw [hτ'.2.1.inner_eq χ (Coherence.self_mem_zSpan hχS) ψ (Coherence.self_mem_zSpan hψS)]
      exact horth χ hχS ψ hψS hχψ
    have h2 : Coherence.cfInner (τ' χ) (τ' ψ) = εχ * (starRingEnd ℂ) εψ := by
      rw [hτχ, hτψ, hcon, Coherence.cfInner_smul_left, Coherence.cfInner_smul_right,
        Coherence.irr_cfInner hσψIrr hσψIrr, if_pos rfl]
      ring
    rw [h2] at h1
    have hεχne : εχ ≠ 0 := by rcases hεχ with h | h <;> rw [h] <;> norm_num
    have hεψne : (starRingEnd ℂ) εψ ≠ 0 := by
      rcases hεψ with h | h <;> rw [h] <;> simp
    exact (mul_ne_zero hεχne hεψne) h1
  -- the two `Θ`-components have opposite signs
  have hs : Coherence.cfInner σψ ηstar = - Coherence.cfInner σχ ηstar := by
    have h1 : Coherence.cfInner σψ ηstar
        = (if σψ = Θ₁ then (1:ℂ) else 0) - (if σψ = Θ₂ then 1 else 0) := by
      rw [hΘeq, Coherence.cfInner_sub_right, Coherence.irr_cfInner hσψIrr hΘ₁,
        Coherence.irr_cfInner hσψIrr hΘ₂]
    have h2 : Coherence.cfInner σχ ηstar
        = (if σχ = Θ₁ then (1:ℂ) else 0) - (if σχ = Θ₂ then 1 else 0) := by
      rw [hΘeq, Coherence.cfInner_sub_right, Coherence.irr_cfInner hσχIrr hΘ₁,
        Coherence.irr_cfInner hσχIrr hΘ₂]
    rw [h1, h2]
    rcases hσχmem with h | h <;> rcases hσψmem with h' | h'
    · exact absurd (h.trans h'.symm) hσne
    · rw [h, h']; simp [hΘne, Ne.symm hΘne]
    · rw [h, h']; simp [hΘne, Ne.symm hΘne]
    · exact absurd (h.trans h'.symm) hσne
  -- the degree relation `dχ · εψ + dψ · εχ = 0`
  have hD : ((CharCore.irrDeg χ : ℤ) : ℂ) * εψ + ((CharCore.irrDeg ψ : ℤ) : ℂ) * εχ = 0 := by
    have h1 : ((CharCore.irrDeg χ : ℤ) : ℂ) * X0
        = (e : ℂ) * εχ * Coherence.cfInner σχ ηstar := by
      have h := sub_eq_zero.mp hEqχ
      rw [hYχeq] at h
      rw [h]; ring
    have h2 : ((CharCore.irrDeg ψ : ℤ) : ℂ) * X0
        = -((e : ℂ) * εψ * Coherence.cfInner σχ ηstar) := by
      have h := sub_eq_zero.mp hEqψ
      rw [hYψeq, hs] at h
      rw [h]; ring
    have h3 : ((CharCore.irrDeg χ : ℤ) : ℂ) * X0 * εψ
        = (e : ℂ) * εχ * Coherence.cfInner σχ ηstar * εψ := by rw [h1]
    have h4 : ((CharCore.irrDeg ψ : ℤ) : ℂ) * X0 * εχ
        = -((e : ℂ) * εψ * Coherence.cfInner σχ ηstar) * εχ := by rw [h2]
    have h5 : ((CharCore.irrDeg χ : ℤ) : ℂ) * X0 * εψ
        + ((CharCore.irrDeg ψ : ℤ) : ℂ) * X0 * εχ = 0 := by
      rw [h3, h4]; ring
    have h6 : X0 * (((CharCore.irrDeg χ : ℤ) : ℂ) * εψ
        + ((CharCore.irrDeg ψ : ℤ) : ℂ) * εχ) = 0 := by
      rw [← h5]; ring
    exact (mul_eq_zero.mp h6).resolve_left hX0ne
  -- the sign analysis
  have hsign : CharCore.irrDeg χ = CharCore.irrDeg ψ ∧ εχ = -εψ := by
    have hDℝ : (CharCore.irrDeg χ : ℝ) * εψ.re + (CharCore.irrDeg ψ : ℝ) * εχ.re = 0 := by
      have h := congrArg Complex.re hD
      simpa using h
    have hεχre : εχ.re = 1 ∨ εχ.re = -1 := by
      rcases hεχ with h | h <;> rw [h] <;> norm_num
    have hεψre : εψ.re = 1 ∨ εψ.re = -1 := by
      rcases hεψ with h | h <;> rw [h] <;> norm_num
    have hεχ_eq : ((εχ.re : ℝ) : ℂ) = εχ := by
      rcases hεχ with h | h <;> rw [h] <;> norm_num
    have hεψ_eq : ((εψ.re : ℝ) : ℂ) = εψ := by
      rcases hεψ with h | h <;> rw [h] <;> norm_num
    have h1p : (0:ℝ) < (CharCore.irrDeg χ : ℝ) := Nat.cast_pos.mpr (CharCore.irrDeg_pos hχirr)
    have h2p : (0:ℝ) < (CharCore.irrDeg ψ : ℝ) := Nat.cast_pos.mpr (CharCore.irrDeg_pos hψirr)
    have hεeq : εχ = -εψ := by
      rcases hεχre with hχr | hχr <;> rcases hεψre with hψr | hψr
      · rw [hχr, hψr] at hDℝ; exfalso; linarith
      · rw [← hεχ_eq, ← hεψ_eq, hχr, hψr]; norm_num
      · rw [← hεχ_eq, ← hεψ_eq, hχr, hψr]; norm_num
      · rw [hχr, hψr] at hDℝ; exfalso; linarith
    refine ⟨?_, hεeq⟩
    rcases hεχre with hχr | hχr <;> rcases hεψre with hψr | hψr
    · rw [hχr, hψr] at hDℝ; exact absurd hDℝ (by linarith)
    · rw [hχr, hψr] at hDℝ
      have : (CharCore.irrDeg χ : ℝ) = (CharCore.irrDeg ψ : ℝ) := by linarith
      exact_mod_cast this
    · rw [hχr, hψr] at hDℝ
      have : (CharCore.irrDeg χ : ℝ) = (CharCore.irrDeg ψ : ℝ) := by linarith
      exact_mod_cast this
    · rw [hχr, hψr] at hDℝ; exact absurd hDℝ (by linarith)
  obtain ⟨hirrEq, hεeq⟩ := hsign
  -- `τ'(χ - ψ)` has degree `0`
  have hχ1ψ1 : χ 1 = ψ 1 := by
    rw [CharCore.irrDeg_spec hχirr, CharCore.irrDeg_spec hψirr, hirrEq]
  have hZ2 : (χ - ψ) ∈ Coherence.ZSpan0 S := by
    refine Coherence.mem_zSpan0.mpr ⟨AddSubgroup.sub_mem _
      (Coherence.self_mem_zSpan hχS) (Coherence.self_mem_zSpan hψS), ?_⟩
    simp only [Pi.sub_apply]
    exact sub_eq_zero.mpr hχ1ψ1
  have hτ'ρ2 : (τ' (χ - ψ)) 1 = 0 := by
    rw [hτ'.1 (χ - ψ) hZ2]
    exact tau_apply_one (fun j => h.tamely.supp_inf hne j) (Coherence.mem_zSpan0.mp hZ2).2
  have hval : (τ' (χ - ψ)) 1 = εχ * (σχ 1 + σψ 1) := by
    have hεψeq : εψ = - εχ := by rw [hεeq]; simp
    have hτψ' : τ' ψ = (-εχ) • σψ := by rw [hτψ, hεψeq]
    rw [map_sub, hτχ, hτψ']
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hsum0 : σχ 1 + σψ 1 = 0 := by
    have h0 := hval
    rw [hτ'ρ2] at h0
    have hεχne : εχ ≠ 0 := by rcases hεχ with h | h <;> rw [h] <;> norm_num
    exact (mul_eq_zero.mp h0.symm).resolve_left hεχne
  have hsum_ne : σχ 1 + σψ 1 ≠ 0 := by
    obtain ⟨nχ, hnχ, hχdeg⟩ := Coherence.irr_degree_pos hσχIrr
    obtain ⟨nψ, hnψ, hψdeg⟩ := Coherence.irr_degree_pos hσψIrr
    rw [hχdeg, hψdeg, ← Nat.cast_add]
    exact Nat.cast_ne_zero.mpr (by omega)
  exact hsum_ne hsum0

end Work.Tame

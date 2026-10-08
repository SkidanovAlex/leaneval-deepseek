import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.ZassenhausTwoGroup.etaStar_data
import Submission.Work.ZassenhausTwoGroup.doubleCoset_cover
import Submission.Work.ZassenhausTwoGroup.inflateFun_mem_Irr_triv
import Submission.Work.CharCore.Main
import Submission.Work.CharCore.isChar_norm_two
import Submission.Work.Induction.All
import Submission.Work.Induction.cfInner_indFun_self_twoDoubleCoset
import Submission.Work.Clifford.All
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.ThmG2.cfInner_indFun_self_twoDoubleCoset

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausTwoGroup

open Classical

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **Gallagher's formula for `Ind_Q^H 1_Q`.**  For a normal subgroup `N = Q.subgroupOf H` of
`↥H`, the induced character `Ind_Q^H 1_Q` is the sum over the irreducible characters `β` of the
quotient `↥H ⧸ N` of `β(1)` times the inflation of `β`.  This is `gallagher_ind_eq` applied to
the principal characters. -/
theorem indFun_subgroupOf_eq_sum_inflate {G : Type} [Group G] [Fintype G]
    {H Q : Subgroup G} [Fintype ↥H] [hN : (Q.subgroupOf H).Normal]
    [Fintype (↥H ⧸ Q.subgroupOf H)] :
    Work.Induction.indFun (Q.subgroupOf H) (fun _ : ↥(Q.subgroupOf H) => (1 : ℂ))
      = ∑ β ∈ Work.CharCore.Irr (↥H ⧸ Q.subgroupOf H),
          ((β 1 : ℂ)) • (fun h : ↥H => β (QuotientGroup.mk h)) := by
  classical
  haveI : (Q.subgroupOf H).Normal := hN
  have hθ : Work.Clifford.principalChar ↥(Q.subgroupOf H)
      ∈ Work.Clifford.Irr ↥(Q.subgroupOf H) := Work.Clifford.principalChar_mem_Irr
  have hχ : Work.Clifford.principalChar ↥H ∈ Work.Clifford.Irr ↥H :=
    Work.Clifford.principalChar_mem_Irr
  have hext : Work.Clifford.Extends (Q.subgroupOf H) (Work.Clifford.principalChar ↥H)
      (Work.Clifford.principalChar ↥(Q.subgroupOf H)) := rfl
  have key := Work.Clifford.gallagher_ind_eq (G := ↥H) (N := Q.subgroupOf H) hθ hχ hext
  have hbridge : Work.Induction.indFun (Q.subgroupOf H) (fun _ : ↥(Q.subgroupOf H) => (1 : ℂ))
      = Work.Clifford.indFun (Q.subgroupOf H)
          (Work.Clifford.principalChar ↥(Q.subgroupOf H)) := rfl
  rw [hbridge, key]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  congr 1
  funext h
  simp [Work.Clifford.inflateFun, Work.Clifford.principalChar]

/-- The inner product of the constant function `1` with itself is `1`. -/
theorem cfInner_one_self_const (X : Type) [Group X] [Fintype X] :
    Work.CharCore.cfInner (fun _ : X => (1 : ℂ)) (fun _ : X => (1 : ℂ)) = 1 := by
  rw [Work.CharCore.cfInner_apply]
  have hsum : (∑ x : X, (1 : ℂ) * starRingEnd ℂ (1 : ℂ)) = (Fintype.card X : ℂ) := by simp
  rw [hsum]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- **The permutation character of the split rank-one action.**  `Ind_H^G 1 = 1_G + θ` with
`θ ∈ Irr G` (the standard decomposition of the permutation character of a `2`-transitive
action). -/
theorem indFun_H_eq_one_add_irr {G : Type} [Group G] [Fintype G] {H Q : Subgroup G}
    {t : G} (h : Submission.Blueprint.IsSplitRankOne H Q t) :
    ∃ θ : G → ℂ, θ ∈ Work.CharCore.Irr G ∧
      Work.Induction.indFun H (fun _ : ↥H => (1 : ℂ)) = (fun _ : G => (1 : ℂ)) + θ := by
  classical
  have hnorm : Work.CharCore.cfInner (Work.Induction.indFun H (fun _ : ↥H => (1 : ℂ)))
      (Work.Induction.indFun H (fun _ : ↥H => (1 : ℂ))) = 2 := by
    have ht : t * t = 1 := Work.ZassenhausPSL2.t_mul_t h
    have hcover : ∀ g : G, g ∈ H ∨ ∃ a b : H, g = (a : G) * t * (b : G) :=
      doubleCoset_cover h
    have hDmap : ∀ d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom),
        (MulAut.conj t) (d : G) ∈ H ⊓ H.map (MulAut.conj t).toMonoidHom := by
      intro d
      have h1 : MulAut.conj t (d : G) = t * (d : G) * t := by
        rw [MulAut.conj_apply, Work.ZassenhausPSL2.t_inv h]
      rw [h1]
      exact Work.ZassenhausPSL2.dStab_conj_mem h d.2
    rw [Work.ThmG2.cfInner_indFun_self_twoDoubleCoset (G := G) ht h.not_mem hcover hDmap
      (fun _ : ↥H => (1 : ℂ)) (Work.CharCore.isClassFun_const 1)]
    have hself : Work.CharCore.cfInner (fun _ : ↥H => (1 : ℂ)) (fun _ : ↥H => (1 : ℂ)) = 1 :=
      cfInner_one_self_const ↥H
    have hcorr : (Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom) : ℂ)⁻¹ *
        ∑ d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom),
          (fun _ : ↥H => (1 : ℂ)) ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩ *
            star ((fun _ : ↥H => (1 : ℂ))
              ⟨(MulAut.conj t) (d : G), (Subgroup.mem_inf.mp (hDmap d)).1⟩) = 1 := by
      have hone : ∀ d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom),
          (fun _ : ↥H => (1 : ℂ)) ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩ *
            star ((fun _ : ↥H => (1 : ℂ))
              ⟨(MulAut.conj t) (d : G), (Subgroup.mem_inf.mp (hDmap d)).1⟩) = 1 :=
        fun d => by simp
      rw [Finset.sum_congr rfl (fun d _ => hone d), Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card]
      exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    rw [hself, hcorr]
    norm_num
  have hchar : Work.CharCore.IsChar (Work.Induction.indFun H (fun _ : ↥H => (1 : ℂ))) :=
    Work.Induction.isChar_indFun_irr (G := G) (Work.CharCore.principalChar_mem_Irr (G := ↥H))
  have hclass : Work.CharCore.IsClassFun (Work.Induction.indFun H (fun _ : ↥H => (1 : ℂ))) :=
    Work.Induction.isClassFun_indFun H _
  obtain ⟨f₁, hf₁, f₂, hf₂, hfne, hfsum⟩ :=
    Work.CharCore.isChar_norm_two hchar hclass hnorm
  have hone : Work.CharCore.cfInner (Work.Induction.indFun H (fun _ : ↥H => (1 : ℂ)))
      (fun _ : G => (1 : ℂ)) = 1 := by
    rw [Work.Induction.frobenius_reciprocity H (fun _ : ↥H => (1 : ℂ)) (fun _ : G => (1 : ℂ))
      (Work.CharCore.isClassFun_const 1)]
    exact cfInner_one_self_const ↥H
  have hpair : (if f₁ = (fun _ : G => (1 : ℂ)) then (1 : ℂ) else 0) +
      (if f₂ = (fun _ : G => (1 : ℂ)) then (1 : ℂ) else 0) = 1 := by
    rw [← Work.CharCore.irr_orthonormal f₁ (fun _ : G => (1 : ℂ)) hf₁
        (Work.CharCore.principalChar_mem_Irr),
      ← Work.CharCore.irr_orthonormal f₂ (fun _ : G => (1 : ℂ)) hf₂
        (Work.CharCore.principalChar_mem_Irr),
      ← Work.CharCore.cfInner_add_left, ← hfsum, hone]
  by_cases hf₁1 : f₁ = (fun _ : G => (1 : ℂ))
  · refine ⟨f₂, hf₂, ?_⟩
    rw [hfsum, hf₁1]
  · have hf₂1 : f₂ = (fun _ : G => (1 : ℂ)) := by
      by_contra hcon
      rw [ite_eq_right hf₁1, ite_eq_right hcon] at hpair
      norm_num at hpair
    refine ⟨f₁, hf₁, ?_⟩
    rw [hfsum, hf₂1, add_comm]

theorem ind_one_constituent_const {G : Type} [Group G] [Fintype G] {H Q : Subgroup G}
    [Fintype ↥H] [Fintype ↥Q] {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H)
    (hQ : Q ≠ ⊥) (hH' : _root_.commutator ↥H ≤ Q.subgroupOf H)
    {ψ : G → ℂ} (hψ : ψ ∈ Work.CharCore.Irr G)
    (hcon : Work.CharCore.cfInner ψ (Work.Induction.indFun Q (fun _ : ↥Q => (1 : ℂ))) ≠ 0) :
    ∀ y y' : ↥Q, y ≠ 1 → y' ≠ 1 → ψ (y : G) = ψ (y' : G) := by
  classical
  intro y y' hy hy'
  -- fix the `Fintype` instance on `↥H` (two candidates are in scope)
  letI hfinH : Fintype ↥H := H.instFintypeSubtypeMemOfDecidablePred
  -- the subgroup `N = Q` inside `H` is normal
  haveI hNnorm : (Q.subgroupOf H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer h.normal
  letI : Fintype (↥H ⧸ Q.subgroupOf H) := QuotientGroup.fintype (Q.subgroupOf H)
  -- (1) transitivity of induction: `Ind_Q^G 1 = Ind_H^G (Ind_Q^H 1)`
  have htrans : Work.Induction.indFun H
        (Work.Induction.indFun (Q.subgroupOf H) (fun _ : ↥(Q.subgroupOf H) => (1 : ℂ)))
      = Work.Induction.indFun Q (fun _ : ↥Q => (1 : ℂ)) := by
    have h0 := Work.Induction.indFun_trans (K := Q) (H := H) h.le (fun _ : ↥Q => (1 : ℂ))
    rw [show (fun x : ↥(Q.subgroupOf H) =>
          (fun _ : ↥Q => (1 : ℂ)) (Subgroup.subgroupOfEquivOfLe h.le x))
        = (fun _ : ↥(Q.subgroupOf H) => (1 : ℂ)) from rfl] at h0
    exact h0
  -- (2) Gallagher: `Ind_Q^H 1 = ∑_{β ∈ Irr(H/N)} β(1) • infl β`
  have hgal := indFun_subgroupOf_eq_sum_inflate (G := G) (H := H) (Q := Q) (hN := hNnorm)
  -- (3) the decomposition of `Ind_Q^G 1`
  have hdecomp : Work.Induction.indFun Q (fun _ : ↥Q => (1 : ℂ))
      = ∑ β ∈ Work.CharCore.Irr (↥H ⧸ Q.subgroupOf H),
          ((β 1 : ℂ)) • Work.Induction.indFun H (fun h : ↥H => β (QuotientGroup.mk h)) := by
    rw [← htrans, hgal, Work.Induction.indFun_sum]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    rw [Work.Induction.indFun_smul]
  -- (4) the pairing of `ψ` with the decomposition
  have hinner : Work.CharCore.cfInner ψ (Work.Induction.indFun Q (fun _ : ↥Q => (1 : ℂ)))
      = ∑ β ∈ Work.CharCore.Irr (↥H ⧸ Q.subgroupOf H),
          (β 1 : ℂ) * Work.CharCore.cfInner ψ
            (Work.Induction.indFun H (fun h : ↥H => β (QuotientGroup.mk h))) := by
    rw [hdecomp, Work.CharCore.cfInner_sum_right]
    refine Finset.sum_congr rfl (fun β hβ => ?_)
    rw [Work.CharCore.cfInner_smul_right]
    have hs : starRingEnd ℂ (β 1) = (β 1 : ℂ) := by
      rw [Work.CharCore.irrDeg_spec hβ]; simp
    rw [hs]
  have hcon' : (∑ β ∈ Work.CharCore.Irr (↥H ⧸ Q.subgroupOf H),
      (β 1 : ℂ) * Work.CharCore.cfInner ψ
        (Work.Induction.indFun H (fun h : ↥H => β (QuotientGroup.mk h)))) ≠ 0 := by
    rw [← hinner]; exact hcon
  -- (5) some `β` pairs nontrivially with `ψ`
  have hsome : ∃ β ∈ Work.CharCore.Irr (↥H ⧸ Q.subgroupOf H),
      Work.CharCore.cfInner ψ
        (Work.Induction.indFun H (fun h : ↥H => β (QuotientGroup.mk h))) ≠ 0 := by
    by_contra hc
    refine hcon' (Finset.sum_eq_zero (fun β hβ => ?_))
    push_neg at hc
    rw [hc β hβ, mul_zero]
  obtain ⟨β, hβmem, hβne⟩ := hsome
  by_cases hβpr : β = (fun _ : ↥H ⧸ Q.subgroupOf H => (1 : ℂ))
  · -- `β` trivial: `Ind_H^G η_β = Ind_H^G 1 = 1 + θ`
    have hη1 : (fun h : ↥H => β (QuotientGroup.mk h)) = (fun _ : ↥H => (1 : ℂ)) := by
      funext h; rw [hβpr]
    rw [hη1] at hβne
    obtain ⟨θ, hθIrr, hθeq⟩ := indFun_H_eq_one_add_irr (G := G) (H := H) (Q := Q) h
    rw [hθeq, Work.CharCore.cfInner_add_right] at hβne
    have hor : Work.CharCore.cfInner ψ (fun _ : G => (1 : ℂ)) ≠ 0 ∨
        Work.CharCore.cfInner ψ θ ≠ 0 := by
      rcases eq_or_ne (Work.CharCore.cfInner ψ (fun _ : G => (1 : ℂ))) 0 with h | h
      · right
        intro hθ0
        exact hβne (by rw [h, hθ0, add_zero])
      · exact Or.inl h
    rcases hor with h1 | h2
    · have hpsi1 : ψ = (fun _ : G => (1 : ℂ)) := by
        by_contra hne
        rw [Work.CharCore.irr_orthonormal ψ (fun _ : G => (1 : ℂ)) hψ
          (Work.CharCore.principalChar_mem_Irr), ite_eq_right hne] at h1
        exact h1 rfl
      rw [hpsi1]
    · have hpsiθ : ψ = θ := by
        by_contra hne
        rw [Work.CharCore.irr_orthonormal ψ θ hψ hθIrr, ite_eq_right hne] at h2
        exact h2 rfl
      have hθval : ∀ z : ↥Q, z ≠ 1 → θ (z : G) = 0 := by
        intro z hz
        have hzG : (z : G) ≠ 1 := fun hh => hz (Subtype.ext hh)
        have hval : Work.Induction.indFun H (fun _ : ↥H => (1 : ℂ)) (z : G) = 1 :=
          indFun_apply_mem_Q (G := G) h
            (Work.CharCore.principalChar_mem_Irr (G := ↥H)) (fun _ _ => rfl) z hzG
        have hh : (1 : ℂ) + θ (z : G) = 1 := by
          have hcong := congrFun hθeq (z : G)
          simp only [Pi.add_apply, Pi.one_apply] at hcong
          rw [← hcong]; exact hval
        linear_combination hh
      rw [hpsiθ, hθval y hy, hθval y' hy']
  · -- `β` nontrivial: `Ind_H^G η_β` is irreducible with value `1` on `Q#`
    have hIrr_triv := inflateFun_mem_Irr_triv (G := G) (H := H) (Q := Q) (hN := hNnorm) hH' hβmem
    obtain ⟨hηIrr, hηQ⟩ := hIrr_triv
    have hη1 : (fun h : ↥H => β (QuotientGroup.mk h)) ≠ (fun _ : ↥H => (1 : ℂ)) := by
      intro hcon
      apply hβpr
      funext a
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective a
      exact congrFun hcon h
    obtain ⟨hηGirr, _hηdeg, hηval, _hηorth⟩ :=
      etaStar_data (G := G) h hZ hQ hηIrr hηQ hη1
    have heq : ψ = Work.Induction.indFun H (fun h : ↥H => β (QuotientGroup.mk h)) := by
      by_contra hne
      rw [Work.CharCore.irr_orthonormal ψ _ hψ hηGirr, ite_eq_right hne] at hβne
      exact hβne rfl
    have hyG : (y : G) ≠ 1 := fun hh => hy (Subtype.ext hh)
    have hyG' : (y' : G) ≠ 1 := fun hh => hy' (Subtype.ext hh)
    rw [heq, hηval y hyG, hηval y' hyG']

end Work.ZassenhausTwoGroup

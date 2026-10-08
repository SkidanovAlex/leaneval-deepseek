import Mathlib
import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.ZassenhausPSL2.Feit.excl_aux
import Submission.Work.ZassenhausPSL2.Feit.excl_degree_support
import Submission.Work.ZassenhausPSL2.Feit.indFun_excl_apply
import Submission.Work.ZassenhausPSL2.Feit.not_excl_linear
import Submission.Work.ZassenhausPSL2.Feit.linear_of_trivial_on_Q
import Submission.Work.ZassenhausPSL2.Feit.cfInner_indFun_linear_self_notreal
import Submission.Work.CharCore.Defs
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.CFun
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.CharCore.principalChar_mem_Irr
import Submission.Work.CharCore.star_Irr
import Submission.Work.CharCore.classFun_eq_zero_of_orthogonal
import Submission.Work.CharCore.vchar_norm_one
import Submission.Work.CharCore.isChar_norm_two
import Submission.Work.Induction.Defs
import Submission.Work.Induction.Basic
import Submission.Work.Induction.frobenius_reciprocity
import Submission.Work.Induction.frobenius_reciprocity_transposed
import Submission.Work.Induction.isClassFun_indFun
import Submission.Work.Induction.isVChar_indFun
import Submission.Work.Induction.isChar_indFun
import Submission.Work.Induction.indFun_apply_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausPSL2.Feit.exceptional_res` (Feit's leaf F6)

In a split rank-one Zassenhaus configuration `H = Q ⋊ D` inside a finite simple group `G`,
the exceptional character `ξ ∈ Irr G` of the family `𝒮 = excludingKernel H Q` restricts to
`H` as the corresponding member `χ₁ ∈ 𝒮` of the family:

`ξ|_H = χ₁`.

## The argument

`η := (ξ|_H) - χ₁` is a class function on `H` (`ξ` is a class function on `G`, `χ₁ ∈ Irr H`).
We show that `η` is orthogonal to *every* irreducible character of `H`; then
`Work.CharCore.classFun_eq_zero_of_orthogonal` gives `η = 0`, and evaluating at `x : H` is the
claim.

By Frobenius reciprocity, `⟨ξ|_H, ψ⟩_H = ⟨ξ, Ind_H^G ψ⟩_G` for every `ψ ∈ Irr H`.
Every `ψ ∈ Irr H` is either in `𝒮` or trivial on `Q` (`not_excl_linear`, Feit's F2c).

* For `ψ ∈ 𝒮` the two inner products `⟨ξ, Ind_H^G ψ⟩` and `⟨χ₁, ψ⟩` are both `δ_{ψ,χ₁}`:
  the first by the hypotheses (`h1`, `h0`), the second by orthonormality of `Irr H`.
* For `ψ ∉ 𝒮` we must show `⟨ξ, Ind_H^G ψ⟩ = 0`.  Since `ψ` is trivial on `Q` (`not_excl_linear`):
  * if `ψ = 1_H`, the permutation character `Ind_H^G 1_H = 1_G + ξ₀` is the sum of two
    irreducibles (`cfInner_indFun_one_self`, via the two-double-coset Mackey formula
    `Work.ThmG2.cfInner_indFun_self_twoDoubleCoset` and `Work.CharCore.isChar_norm_two`), and
    `ξ` is neither of them: `ξ ≠ 1_G` because `⟨Ind_H^G χ₁, 1_G⟩ = ⟨χ₁, 1_H⟩ = 0`, and `ξ ≠ ξ₀`
    because `⟨Ind_H^G χ₂, ξ₀⟩ = ⟨Ind_H^G χ₂, Ind_H^G 1_H⟩ = 1 ≠ 0 = ⟨Ind_H^G χ₂, ξ⟩` for a
    second member `χ₂ ∈ 𝒮` (which exists by `hk`).
  * if `ψ ≠ 1_H` then `ψ` is not real-valued (`eq_one_of_trivial_on_Q_of_real`: a real
    character trivial on `Q` is constant `1` because `H/Q` has odd order), so
    `⟨Ind_H^G ψ, Ind_H^G ψ⟩ = 1` (`cfInner_indFun_linear_self_notreal`); hence `Ind_H^G ψ` is
    (up to sign, `Work.CharCore.vchar_norm_one`) a single irreducible character of `G`.  It
    cannot be `±ξ`, since `⟨Ind_H^G ψ, Ind_H^G χ₂⟩ = 1 ≠ 0 = ⟨ξ, Ind_H^G χ₂⟩`
    (Feit's F4'), so `⟨ξ, Ind_H^G ψ⟩ = 0` by orthonormality.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open Classical

namespace Work.ZassenhausPSL2.Feit

variable {G : Type} [Group G] [Fintype G]
variable {H Q : Subgroup G} {t : G}

/-- **Feit's F4'.**  For `lc ∈ Irr H` which is trivial on `Q` and `χ ∈ 𝒮 = excludingKernel H Q`,
`⟨Ind_H^G lc, Ind_H^G χ⟩_G = 1`.  By Frobenius reciprocity the inner product is
`⟨lc, Res_H^G (Ind_H^G χ)⟩_H = ⟨lc, χ + ρ_H⟩_H = 0 + lc 1 = 1` (`indFun_excl_apply`, Feit's F3).

Self-contained copy of `Work.ZassenhausPSL2.Feit.cfInner_indFun_linear_excl_mem`, so that this
file does not depend on a module containing a `sorry`. -/
private theorem cfInner_indFun_linear_excl' (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hz : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (hab : Submission.Blueprint.IsAbelianSubgroup Q) {lc χ : H → ℂ}
    (hlc : lc ∈ Work.CharCore.Irr H) (hlcQ : ∀ x : H, (x : G) ∈ Q → lc x = 1)
    (hχ : χ ∈ Submission.Blueprint.excludingKernel H Q) :
    Work.CharCore.cfInner (Work.Induction.indFun H lc) (Work.Induction.indFun H χ) = 1 := by
  classical
  obtain ⟨hχIrr, x₀, hx₀Q, hx₀ne⟩ := mem_excludingKernel_iff.mp hχ
  have hlc1 : lc 1 = 1 := hlcQ 1 (by simpa using Q.one_mem)
  have hne : lc ≠ χ := by
    intro hc
    have h1 : χ x₀ = χ 1 := by rw [← hc, hlcQ x₀ hx₀Q, hlc1]
    exact hx₀ne h1
  have hfr : Work.CharCore.cfInner (Work.Induction.indFun H lc) (Work.Induction.indFun H χ)
      = Work.CharCore.cfInner lc (Work.Induction.resFun H (Work.Induction.indFun H χ)) :=
    Work.Induction.frobenius_reciprocity H lc (Work.Induction.indFun H χ)
      (Work.Induction.isClassFun_indFun H χ)
  rw [hfr]
  let F : ↥H → ℂ := fun x => if x = 1 then (Nat.card ↥H : ℂ) else 0
  have hres : Work.Induction.resFun H (Work.Induction.indFun H χ) = χ + F := by
    funext x
    rw [Work.Induction.resFun_apply, Pi.add_apply,
      Work.ZassenhausPSL2.Feit.indFun_excl_apply h hz h2 hab hχ x]
  rw [hres, Work.CharCore.cfInner_add_right,
    Work.CharCore.irr_orthonormal lc χ hlc hχIrr, ite_eq_right hne]
  -- `⟨lc, F⟩ = lc 1 = 1`, because `F` is supported at the identity
  have hFv : Work.CharCore.cfInner lc F = lc 1 := by
    rw [Work.CharCore.cfInner_apply]
    have hsum : (∑ x : ↥H, lc x * starRingEnd ℂ (F x))
        = lc 1 * starRingEnd ℂ ((Nat.card ↥H : ℂ)) := by
      rw [Finset.sum_eq_single 1]
      · dsimp only [F]; simp
      · intro b _ hb; dsimp only [F]; simp [hb]
      · intro hh; exact absurd (Finset.mem_univ 1) hh
    rw [hsum, map_natCast]
    have hcard : (Fintype.card ↥H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [Nat.card_eq_fintype_card (α := ↥H), mul_comm (lc 1) (Fintype.card ↥H : ℂ),
      ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
  rw [hFv, hlc1, zero_add]

/-- The inner product of the constant function `1` with itself is `1`. -/
private lemma cfInner_one_self (X : Type) [Group X] [Fintype X] :
    Work.CharCore.cfInner (fun _ : X => (1 : ℂ)) (fun _ : X => (1 : ℂ)) = 1 := by
  rw [Work.CharCore.cfInner_apply]
  have hsum : (∑ x : X, (1 : ℂ) * starRingEnd ℂ (1 : ℂ)) = (Fintype.card X : ℂ) := by
    simp
  rw [hsum]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- **The norm of the induced principal character.**  For split rank-one data the action on
`G ⧸ H` has exactly two `(H,H)`-double cosets, `H` and `H t H`, so the Mackey formula
`Work.ThmG2.cfInner_indFun_self_twoDoubleCoset` gives
`⟨Ind_H^G 1, Ind_H^G 1⟩ = 1 + |D|⁻¹·|D| = 2`. -/
private theorem cfInner_indFun_one_self (h : Submission.Blueprint.IsSplitRankOne H Q t) :
    Work.CharCore.cfInner (Work.Induction.indFun H (fun _ : H => (1 : ℂ)))
      (Work.Induction.indFun H (fun _ : H => (1 : ℂ))) = 2 := by
  have ht : t * t = 1 := Work.ZassenhausPSL2.t_mul_t h
  have hcover : ∀ g : G, g ∈ H ∨ ∃ a b : H, g = (a : G) * t * (b : G) := by
    intro g
    by_cases hg : g ∈ H
    · exact Or.inl hg
    · right
      obtain ⟨⟨a, q⟩, hspec, -⟩ := Work.ZassenhausPSL2.exists_unique_decomp h hg
      exact ⟨a, ⟨(q : G), h.le q.2⟩, by simpa using hspec.symm⟩
  have hDmap : ∀ d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom),
      (MulAut.conj t) (d : G) ∈ H ⊓ H.map (MulAut.conj t).toMonoidHom := by
    intro d
    have h1 : MulAut.conj t (d : G) = t * (d : G) * t := by
      rw [MulAut.conj_apply, Work.ZassenhausPSL2.t_inv h]
    rw [h1]
    exact Work.ZassenhausPSL2.dStab_conj_mem h d.2
  rw [Work.ThmG2.cfInner_indFun_self_twoDoubleCoset (G := G) ht h.not_mem hcover hDmap
    (fun _ : H => (1 : ℂ)) (Work.CharCore.isClassFun_const 1)]
  have hself : Work.CharCore.cfInner (fun _ : H => (1 : ℂ)) (fun _ : H => (1 : ℂ)) = 1 :=
    cfInner_one_self ↥H
  have hcorr : (Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom) : ℂ)⁻¹ *
      ∑ d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom),
        (fun _ : H => (1 : ℂ)) ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩ *
          star ((fun _ : H => (1 : ℂ))
            ⟨(MulAut.conj t) (d : G), (Subgroup.mem_inf.mp (hDmap d)).1⟩) = 1 := by
    have hone : ∀ d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom),
        (fun _ : H => (1 : ℂ)) ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩ *
          star ((fun _ : H => (1 : ℂ))
            ⟨(MulAut.conj t) (d : G), (Subgroup.mem_inf.mp (hDmap d)).1⟩) = 1 :=
      fun d => by simp
    rw [Finset.sum_congr rfl (fun d _ => hone d), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  rw [hself, hcorr]
  norm_num

/-- **The permutation character of the split rank-one action.**  `Ind_H^G 1 = 1_G + ξ₀` with
`ξ₀ ∈ Irr G`, `ξ₀ ≠ 1_G` (the standard decomposition of the permutation character of a
`2`-transitive action). -/
private theorem indFun_one_eq_principal_add_irr (h : Submission.Blueprint.IsSplitRankOne H Q t) :
    ∃ ξ₀ ∈ Work.CharCore.Irr G, ξ₀ ≠ (fun _ : G => (1 : ℂ)) ∧
      Work.Induction.indFun H (fun _ : H => (1 : ℂ)) = (fun _ : G => (1 : ℂ)) + ξ₀ := by
  have hnorm : Work.CharCore.cfInner (Work.Induction.indFun H (fun _ : H => (1 : ℂ)))
      (Work.Induction.indFun H (fun _ : H => (1 : ℂ))) = 2 := cfInner_indFun_one_self h
  have hchar : Work.CharCore.IsChar (Work.Induction.indFun H (fun _ : H => (1 : ℂ))) :=
    Work.Induction.isChar_indFun_irr (G := G) (Work.CharCore.principalChar_mem_Irr (G := ↥H))
  have hclass : Work.CharCore.IsClassFun (Work.Induction.indFun H (fun _ : H => (1 : ℂ))) :=
    Work.Induction.isClassFun_indFun H _
  obtain ⟨f₁, hf₁, f₂, hf₂, hfne, hfsum⟩ :=
    Work.CharCore.isChar_norm_two hchar hclass hnorm
  -- the trivial character occurs exactly once in `Ind_H^G 1`
  have hone : Work.CharCore.cfInner (Work.Induction.indFun H (fun _ : H => (1 : ℂ)))
      (fun _ : G => (1 : ℂ)) = 1 := by
    rw [Work.Induction.frobenius_reciprocity H (fun _ : H => (1 : ℂ)) (fun _ : G => (1 : ℂ))
      (Work.CharCore.isClassFun_const 1)]
    exact cfInner_one_self ↥H
  have hpair : (if f₁ = (fun _ : G => (1 : ℂ)) then (1 : ℂ) else 0) +
      (if f₂ = (fun _ : G => (1 : ℂ)) then (1 : ℂ) else 0) = 1 := by
    rw [← Work.CharCore.irr_orthonormal f₁ (fun _ : G => (1 : ℂ)) hf₁
        (Work.CharCore.principalChar_mem_Irr),
      ← Work.CharCore.irr_orthonormal f₂ (fun _ : G => (1 : ℂ)) hf₂
        (Work.CharCore.principalChar_mem_Irr),
      ← Work.CharCore.cfInner_add_left, ← hfsum, hone]
  by_cases hf₁1 : f₁ = (fun _ : G => (1 : ℂ))
  · refine ⟨f₂, hf₂, ?_, ?_⟩
    · exact fun hcon => hfne (by rw [hf₁1, hcon])
    · rw [hfsum, hf₁1]
  · have hf₂1 : f₂ = (fun _ : G => (1 : ℂ)) := by
      by_contra hcon
      rw [ite_eq_right hf₁1, ite_eq_right hcon] at hpair
      norm_num at hpair
    refine ⟨f₁, hf₁, hf₁1, ?_⟩
    rw [hfsum, hf₂1, add_comm]

/-- **A real character trivial on `Q` is the trivial character.**  A character `ψ ∈ Irr H`
which is trivial on `Q` is *linear* (`linear_of_trivial_on_Q`), so every value `ψ x` is a root
of unity; if in addition `ψ` is real-valued then `ψ x = ±1`, and since `ψ` is trivial on the
normal subgroup `Q` of odd index (the index of `Q` in `H` is `|D|`, which is odd) one has
`(ψ x)^{[H:Q]} = ψ (x^{[H:Q]}) = 1`, so `ψ x = 1`. -/
private theorem eq_one_of_trivial_on_Q_of_real (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hz : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (hab : Submission.Blueprint.IsAbelianSubgroup Q) {ψ : H → ℂ}
    (hψ : ψ ∈ Work.CharCore.Irr H)
    (hψQ : ∀ x : H, (x : G) ∈ Q → ψ x = 1)
    (hreal : ψ = fun x => starRingEnd ℂ (ψ x)) : ∀ x : H, ψ x = 1 := by
  obtain ⟨φ, hφ⟩ := Work.ZassenhausPSL2.Feit.linear_of_trivial_on_Q h hz h2 hab hψ hψQ
  haveI hQn : (Q.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.le).mpr h.normal
  have hodd : Odd (Q.subgroupOf H).index := by
    rw [index_subgroupOf_Q h]
    exact Work.ZassenhausPSL2.dStab_odd H t h.stronglyEmbedded h.not_mem
  intro x
  -- multiplicativity of `ψ` on `H`
  have hmul : ∀ a b : H, ψ (a * b) = ψ a * ψ b := by
    intro a b
    rw [hφ (a * b), hφ a, hφ b, map_mul, Units.val_mul]
  have h1v : ψ 1 = 1 := hψQ 1 (by simpa using Q.one_mem)
  -- `ψ x` is real and of finite order, hence `±1`
  have hinv : ψ x⁻¹ = ψ x := by
    rw [← Work.CharCore.star_Irr ψ hψ x, ← congrFun hreal x]
  have hsq : (ψ x) ^ 2 = 1 := by
    calc (ψ x) ^ 2 = ψ x⁻¹ * ψ x := by rw [pow_two, hinv]
      _ = ψ (x⁻¹ * x) := (hmul x⁻¹ x).symm
      _ = ψ 1 := by rw [inv_mul_cancel]
      _ = 1 := h1v
  -- `ψ x` has odd order
  have hpow : (ψ x) ^ (Q.subgroupOf H).index = 1 := by
    have hmem : x ^ (Q.subgroupOf H).index ∈ Q.subgroupOf H :=
      Subgroup.pow_index_mem (Q.subgroupOf H) x
    have hQmem : (((x ^ (Q.subgroupOf H).index : ↥H)) : G) ∈ Q :=
      Subgroup.mem_subgroupOf.mp hmem
    have hval : ψ (x ^ (Q.subgroupOf H).index) = 1 := hψQ _ (by simpa using hQmem)
    calc (ψ x) ^ (Q.subgroupOf H).index
        = (φ x : ℂ) ^ (Q.subgroupOf H).index := by rw [hφ x]
      _ = ((φ x) ^ (Q.subgroupOf H).index : ℂˣ) := by rw [Units.val_pow_eq_pow_val]
      _ = (φ (x ^ (Q.subgroupOf H).index) : ℂˣ) := by rw [map_pow]
      _ = ψ (x ^ (Q.subgroupOf H).index) := by rw [hφ]
      _ = 1 := hval
  rcases sq_eq_one_iff.mp hsq with h1 | h1
  · exact h1
  · exfalso
    have hneg : (ψ x) ^ (Q.subgroupOf H).index = -1 := by rw [h1, hodd.neg_one_pow]
    rw [hpow] at hneg
    norm_num at hneg

/-- **Feit's F6, one irreducible at a time.**  For an irreducible character `ψ` of `H` outside
`𝒮 = excludingKernel H Q`, and an irreducible `ξ` of `G` which is orthogonal to `Ind_H^G χ` for
all `χ ∈ 𝒮` except `χ₁` (where the inner product is `1`), one has `⟨ξ, Ind_H^G ψ⟩ = 0`. -/
private theorem cfInner_indFun_eq_zero_of_notMem (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hz : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (hab : Submission.Blueprint.IsAbelianSubgroup Q)
    {χ₁ χ₂ : H → ℂ} (hχ₁ : χ₁ ∈ Submission.Blueprint.excludingKernel H Q)
    (hχ₂ : χ₂ ∈ Submission.Blueprint.excludingKernel H Q) (hχ₂ne : χ₂ ≠ χ₁)
    {ξ : G → ℂ} (hξ : ξ ∈ Work.CharCore.Irr G)
    (h1 : Work.CharCore.cfInner (Work.Induction.indFun H χ₁) ξ = 1)
    (h0 : Work.CharCore.cfInner (Work.Induction.indFun H χ₂) ξ = 0)
    {ψ : H → ℂ} (hψ : ψ ∈ Work.CharCore.Irr H)
    (hψ' : ψ ∉ Submission.Blueprint.excludingKernel H Q) :
    Work.CharCore.cfInner ξ (Work.Induction.indFun H ψ) = 0 := by
  have hχ₁Irr : χ₁ ∈ Work.CharCore.Irr H := (mem_excludingKernel_iff.mp hχ₁).1
  have hχ₂Irr : χ₂ ∈ Work.CharCore.Irr H := (mem_excludingKernel_iff.mp hχ₂).1
  have hχ₁ne1 : χ₁ ≠ (fun _ : H => (1 : ℂ)) := by
    intro hc
    obtain ⟨x, -, hxne⟩ := (mem_excludingKernel_iff.mp hχ₁).2
    rw [hc] at hxne
    exact hxne rfl
  have hχ₂ne1 : χ₂ ≠ (fun _ : H => (1 : ℂ)) := by
    intro hc
    obtain ⟨x, -, hxne⟩ := (mem_excludingKernel_iff.mp hχ₂).2
    rw [hc] at hxne
    exact hxne rfl
  -- `⟨Ind χ, 1_G⟩ = ⟨χ, 1_H⟩ = 0` for `χ ∈ Irr H`, `χ ≠ 1_H`
  have hInd1 : ∀ {χ : H → ℂ}, χ ∈ Work.CharCore.Irr H → χ ≠ (fun _ : H => (1 : ℂ)) →
      Work.CharCore.cfInner (Work.Induction.indFun H χ) (fun _ : G => (1 : ℂ)) = 0 := by
    intro χ hχIrr hχne
    have hfr : Work.CharCore.cfInner (Work.Induction.indFun H χ) (fun _ : G => (1 : ℂ))
        = Work.CharCore.cfInner χ (fun _ : H => (1 : ℂ)) :=
      Work.Induction.frobenius_reciprocity H χ (fun _ : G => (1 : ℂ))
        (Work.CharCore.isClassFun_const 1)
    rw [hfr, Work.CharCore.irr_orthonormal χ (fun _ : H => (1 : ℂ)) hχIrr
        (Work.CharCore.principalChar_mem_Irr (G := ↥H))]
    exact ite_eq_right hχne
  have h0' : Work.CharCore.cfInner ξ (Work.Induction.indFun H χ₂) = 0 := by
    rw [Work.CharCore.cfInner_conj_symm, h0]
    simp
  have honeχ₂ : Work.CharCore.cfInner (fun _ : G => (1 : ℂ)) (Work.Induction.indFun H χ₂) = 0 := by
    rw [Work.CharCore.cfInner_conj_symm, hInd1 hχ₂Irr hχ₂ne1]
    simp
  -- Feit's F4': for `lc ∈ Irr H` trivial on `Q`, `⟨Ind lc, Ind χ₂⟩ = 1`
  have hlin : ∀ {lc : H → ℂ}, lc ∈ Work.CharCore.Irr H →
      (∀ x : H, (x : G) ∈ Q → lc x = 1) →
      Work.CharCore.cfInner (Work.Induction.indFun H lc) (Work.Induction.indFun H χ₂) = 1 :=
    fun hlc hlcQ => cfInner_indFun_linear_excl' h hz h2 hab hlc hlcQ hχ₂
  by_cases hψone : ψ = fun _ : H => (1 : ℂ)
  · -- `ψ = 1_H`: `Ind 1_H = 1_G + ξ₀` and `ξ` is neither summand
    rw [hψone]
    obtain ⟨ξ₀, hξ₀Irr, hξ₀ne, hInd⟩ := indFun_one_eq_principal_add_irr h
    have hξne1 : ξ ≠ (fun _ : G => (1 : ℂ)) := by
      intro hcon
      have hcontra : (1 : ℂ) = 0 := by
        rw [← h1, hcon, hInd1 hχ₁Irr hχ₁ne1]
      exact one_ne_zero hcontra
    have hξ₀1 : Work.CharCore.cfInner ξ₀ (Work.Induction.indFun H χ₂) = 1 := by
      have hsplit : Work.CharCore.cfInner (Work.Induction.indFun H (fun _ : H => (1 : ℂ)))
            (Work.Induction.indFun H χ₂)
          = Work.CharCore.cfInner (fun _ : G => (1 : ℂ)) (Work.Induction.indFun H χ₂) +
            Work.CharCore.cfInner ξ₀ (Work.Induction.indFun H χ₂) := by
        rw [hInd, Work.CharCore.cfInner_add_left]
      have hlhs : Work.CharCore.cfInner (Work.Induction.indFun H (fun _ : H => (1 : ℂ)))
          (Work.Induction.indFun H χ₂) = 1 :=
        hlin (Work.CharCore.principalChar_mem_Irr (G := ↥H)) (fun _ _ => rfl)
      rw [hlhs, honeχ₂, zero_add] at hsplit
      exact hsplit.symm
    have hξξ₀ : ξ ≠ ξ₀ := by
      intro hcon
      have hcontra : Work.CharCore.cfInner (Work.Induction.indFun H χ₂) ξ = 1 := by
        rw [hcon, Work.CharCore.cfInner_conj_symm (Work.Induction.indFun H χ₂) ξ₀, hξ₀1]
        simp
      rw [h0] at hcontra
      exact one_ne_zero hcontra.symm
    have hξ1 : Work.CharCore.cfInner ξ (fun _ : G => (1 : ℂ)) = 0 := by
      rw [Work.CharCore.irr_orthonormal ξ (fun _ : G => (1 : ℂ)) hξ
        (Work.CharCore.principalChar_mem_Irr (G := G))]
      exact ite_eq_right hξne1
    have hξξ₀' : Work.CharCore.cfInner ξ ξ₀ = 0 := by
      rw [Work.CharCore.irr_orthonormal ξ ξ₀ hξ hξ₀Irr]
      exact ite_eq_right hξξ₀
    rw [hInd, Work.CharCore.cfInner_add_right, hξ1, hξξ₀', add_zero]
  · -- `ψ ∉ 𝒮`, `ψ ≠ 1_H`: `ψ` is not real-valued and `Ind ψ` is irreducible up to sign
    have hψQ : ∀ x : H, (x : G) ∈ Q → ψ x = 1 :=
      (Work.ZassenhausPSL2.Feit.not_excl_linear h hz h2 hab hψ hψ').2
    have hreal : ψ ≠ fun x => starRingEnd ℂ (ψ x) := by
      intro hcon
      exact hψone (funext (eq_one_of_trivial_on_Q_of_real h hz h2 hab hψ hψQ hcon))
    have hnorm : Work.CharCore.cfInner (Work.Induction.indFun H ψ)
        (Work.Induction.indFun H ψ) = 1 :=
      Work.ZassenhausPSL2.Feit.cfInner_indFun_linear_self_notreal h hz h2 hab hψ hψQ hreal
    have hv : Work.CharCore.IsVChar (Work.Induction.indFun H ψ) :=
      Work.Induction.isVChar_indFun
        (Work.CharCore.IsChar.toVChar (Work.CharCore.IsChar.of_mem_Irr hψ))
    obtain ⟨χ, hχIrr, hcase⟩ := Work.CharCore.vchar_norm_one hv hnorm
    have hne : ξ ≠ χ := by
      intro hcon
      have hB : Work.CharCore.cfInner χ (Work.Induction.indFun H χ₂) = 1 ∨
          Work.CharCore.cfInner χ (Work.Induction.indFun H χ₂) = -1 := by
        rcases hcase with hc | hc
        · left
          rw [← hc]
          exact hlin hψ hψQ
        · right
          have h1' : Work.CharCore.cfInner (-χ) (Work.Induction.indFun H χ₂) = 1 := by
            rw [← hc]
            exact hlin hψ hψQ
          rw [Work.CharCore.cfInner_neg_left] at h1'
          exact neg_eq_iff_eq_neg.mp h1'
      have hC : Work.CharCore.cfInner χ (Work.Induction.indFun H χ₂) = 0 := by
        rw [← hcon]
        exact h0'
      rw [hC] at hB
      norm_num at hB
    rcases hcase with hc | hc
    · rw [hc, Work.CharCore.irr_orthonormal ξ χ hξ hχIrr]
      exact ite_eq_right hne
    · rw [hc, Work.CharCore.cfInner_neg_right, Work.CharCore.irr_orthonormal ξ χ hξ hχIrr,
        ite_eq_right hne, neg_zero]

/-- **F6 (Feit).**  In a split rank-one Zassenhaus configuration with `Q` an abelian `2`-group,
inside a finite simple group `G`, an irreducible character `ξ` of `G` which is orthogonal to
`Ind_H^G χ` for every `χ ∈ 𝒮 = excludingKernel H Q` except `χ₁`, where the inner product is
`1` (and with `|𝒮| ≥ 2`), restricts to `H` as `χ₁`: `ξ|_H = χ₁`. -/
theorem exceptional_res {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G}
    [IsSimpleGroup G] (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hz : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (hab : Submission.Blueprint.IsAbelianSubgroup Q)
    (hk : 2 ≤ (Submission.Blueprint.excludingKernel H Q).card) {χ₁ : H → ℂ}
    (hχ₁ : χ₁ ∈ Submission.Blueprint.excludingKernel H Q) {ξ : G → ℂ}
    (hξ : ξ ∈ Work.CharCore.Irr G)
    (h1 : Work.CharCore.cfInner (Work.Induction.indFun H χ₁) ξ = 1)
    (h0 : ∀ χ ∈ Submission.Blueprint.excludingKernel H Q, χ ≠ χ₁ →
      Work.CharCore.cfInner (Work.Induction.indFun H χ) ξ = 0) :
    ∀ x : H, ξ x = χ₁ x := by
  -- a second member `χ₂ ∈ 𝒮`, `χ₂ ≠ χ₁`
  obtain ⟨χ₂, hχ₂S, hχ₂ne⟩ : ∃ χ₂ ∈ Submission.Blueprint.excludingKernel H Q, χ₂ ≠ χ₁ := by
    have hlt : 1 < (Submission.Blueprint.excludingKernel H Q).card := by omega
    obtain ⟨a, ha, b, hb, hab'⟩ := Finset.one_lt_card.mp hlt
    by_cases ha1 : a = χ₁
    · exact ⟨b, hb, fun hc => hab' (by rw [ha1, hc])⟩
    · exact ⟨a, ha, ha1⟩
  -- orthogonality of `ξ` with `Ind_H^G ψ` for all `ψ ∈ Irr H`
  have hkey : ∀ ψ ∈ Work.CharCore.Irr H, ψ ∉ Submission.Blueprint.excludingKernel H Q →
      Work.CharCore.cfInner ξ (Work.Induction.indFun H ψ) = 0 :=
    fun ψ hψ hψ' =>
      cfInner_indFun_eq_zero_of_notMem h hz h2 hab hχ₁ hχ₂S hχ₂ne hξ h1
        (h0 χ₂ hχ₂S hχ₂ne) hψ hψ'
  have hξcl : Work.CharCore.IsClassFun ξ := Work.CharCore.isClassFun_of_mem_Irr hξ
  have hχ₁Irr : χ₁ ∈ Work.CharCore.Irr H := (mem_excludingKernel_iff.mp hχ₁).1
  have hχ₁cl : Work.CharCore.IsClassFun χ₁ := Work.CharCore.isClassFun_of_mem_Irr hχ₁Irr
  have hηcl : Work.CharCore.IsClassFun (Work.Induction.resFun H ξ - χ₁) :=
    (Work.Induction.isClassFun_resFun hξcl).sub hχ₁cl
  -- the class function `η = ξ|_H - χ₁` is orthogonal to every irreducible character of `H`
  have hηorth : ∀ ψ ∈ Work.CharCore.Irr H,
      Work.CharCore.cfInner (Work.Induction.resFun H ξ - χ₁) ψ = 0 := by
    intro ψ hψ
    rw [Work.CharCore.cfInner_sub_left]
    have hres : Work.CharCore.cfInner (Work.Induction.resFun H ξ) ψ
        = Work.CharCore.cfInner ξ (Work.Induction.indFun H ψ) :=
      (Work.Induction.frobenius_reciprocity_transposed H ξ ψ hξcl).symm
    by_cases hψS : ψ ∈ Submission.Blueprint.excludingKernel H Q
    · have hcase : Work.CharCore.cfInner ξ (Work.Induction.indFun H ψ)
          = starRingEnd ℂ (if ψ = χ₁ then (1 : ℂ) else 0) := by
        rw [Work.CharCore.cfInner_conj_symm]
        congr 1
        by_cases hψχ₁ : ψ = χ₁
        · rw [ite_eq_left hψχ₁, hψχ₁]
          exact h1
        · rw [ite_eq_right hψχ₁]
          exact h0 ψ hψS hψχ₁
      have hχ₁ψ : Work.CharCore.cfInner χ₁ ψ = if χ₁ = ψ then (1 : ℂ) else 0 :=
        Work.CharCore.irr_orthonormal χ₁ ψ hχ₁Irr hψ
      rw [hres, hcase, hχ₁ψ]
      by_cases hψχ₁ : ψ = χ₁
      · rw [ite_eq_left hψχ₁, ite_eq_left hψχ₁.symm]
        simp
      · rw [ite_eq_right hψχ₁, ite_eq_right (fun hc => hψχ₁ hc.symm)]
        simp
    · have hz' : Work.CharCore.cfInner ξ (Work.Induction.indFun H ψ) = 0 := hkey ψ hψ hψS
      have hχ₁ψ : Work.CharCore.cfInner χ₁ ψ = 0 := by
        rw [Work.CharCore.irr_orthonormal χ₁ ψ hχ₁Irr hψ]
        exact ite_eq_right (fun hc => hψS (by rw [← hc]; exact hχ₁))
      rw [hres, hz', hχ₁ψ, sub_zero]
  have hηzero : Work.Induction.resFun H ξ - χ₁ = 0 :=
    Work.CharCore.classFun_eq_zero_of_orthogonal hηcl hηorth
  intro x
  have hx : ξ x - χ₁ x = 0 := by
    have := congrFun hηzero x
    simpa using this
  exact sub_eq_zero.mp hx

end Work.ZassenhausPSL2.Feit

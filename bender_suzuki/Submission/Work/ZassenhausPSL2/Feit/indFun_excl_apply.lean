import Mathlib
import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.ZassenhausPSL2.Feit.excl_degree_support
import Submission.Work.CharCore.Defs
import Submission.Work.CharCore.Basic
import Submission.Work.Induction.Defs
import Submission.Work.Induction.Basic
import Submission.Work.Induction.indFun_apply_one
import Submission.Work.ThmF.Setup
import Submission.Work.ThmG.rankOne_index
import Submission.Work.ThmG.rankOne_isTI
import Submission.Work.ThmG.resFun_indFun_eq_of_vanishes_off_hall

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausPSL2.Feit.indFun_excl_apply` (Feit's leaf F3)

In a split rank-one Zassenhaus configuration `H = Q ⋊ D` (`D = twoPoint H t = H ⊓ Hᵗ`,
`Q ⊴ H` a 2-group with `D` acting fixed-point-freely on `Q`), for every irreducible
character `χ` of `H` non-trivial on `Q` (i.e. `χ ∈ 𝓢 = excludingKernel H Q`) the induced
character, restricted to `H`, is `χ` plus the regular character of `H`:

`Ind_H^G χ (x) = χ x + (if x = 1 then |H| else 0)` for `x ∈ H`.

This is Feit's `(θ^G)|_H = θ + ρ_H` (Feit 1960; Peterfalvi II, Ch. VII §1, the "F3" step of
the `ZassenhausPSL2` area).  The proof is the standard TI/Hall computation:

* by `resFun_indFun_eq_of_vanishes_off_hall` (`Work.ThmG`), applied to the class function
  `ν = χ - χ(1)·δ` (where `δ` is the indicator of `1` in `H`, so that `ν 1 = 0` and `ν`
  vanishes off `Q`), one has `Res_H^G (Ind_H^G ν) = ν`;
* `Ind_H^G δ` is computed directly: `[G : H]` at `1` (`indFun_apply_one`) and `0` elsewhere;
* the additive decomposition `χ = ν + χ(1)·δ` finishes, the remaining arithmetic being
  `|D| · ([G:H] - 1) = |H|`, i.e. `|D| · |Q| = |H|` (`rankOne_index`, `split_card_H`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open Classical

namespace Work.ZassenhausPSL2.Feit

theorem indFun_excl_apply {G : Type} [Group G] [Fintype G] [DecidableEq G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (hab : Submission.Blueprint.IsAbelianSubgroup Q) {χ : H → ℂ}
    (hχ : χ ∈ Submission.Blueprint.excludingKernel H Q) (x : H) :
    Work.Induction.indFun H χ (x : G) = χ x + (if x = 1 then (Nat.card H : ℂ) else 0) := by
  classical
  -- F2a: `χ` has degree `|D|` and vanishes off `Q`.
  obtain ⟨hχ1, hχ0⟩ := excl_degree_support h hz h2 hab hχ
  -- `δ` = indicator of the identity in `H`; `ν = χ - χ(1)·δ`.
  set δ : H → ℂ := fun y => if y = 1 then (1 : ℂ) else 0 with hδ
  set ν : H → ℂ := χ - (χ 1) • δ with hν
  have hδ_class : Work.CharCore.IsClassFun δ := by
    rw [hδ]
    intro a b
    by_cases ha : a = 1
    · subst ha; simp
    · have hne : b * a * b⁻¹ ≠ 1 := by
        intro hc
        apply ha
        calc a = b⁻¹ * (b * a * b⁻¹) * b := by group
          _ = b⁻¹ * 1 * b := by rw [hc]
          _ = 1 := by group
      simp [ha, hne]
  have hχ_class : Work.CharCore.IsClassFun χ :=
    Work.CharCore.isClassFun_of_mem_Irr (Finset.mem_filter.mp hχ).1
  have hν_class : Work.CharCore.IsClassFun ν := by
    rw [hν]
    exact hχ_class.sub (hδ_class.smul (χ 1))
  have hν1 : ν 1 = 0 := by simp [hν, hδ]
  have hν0 : ∀ y : H, (y : G) ∉ Q → ν y = 0 := by
    intro y hy
    have hy1 : y ≠ 1 := by
      intro hc; apply hy; rw [hc]; exact Q.one_mem
    simp [hν, hδ, hχ0 y hy, hy1]
  -- `Q` is a 2-group and `D` has odd order, so their orders are coprime: `Q` is a Hall
  -- subgroup of `H`, the hypothesis of the Hall restriction identity.
  have hcop : Nat.Coprime (Nat.card (Submission.Blueprint.twoPoint H t)) (Nat.card Q) := by
    have hoddD : Odd (Nat.card (Submission.Blueprint.twoPoint H t)) :=
      Work.ThmF.split_odd_card_twoPoint h
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := Q)).mp h2
    rw [hn]
    exact Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hoddD)
  have hTI : ∀ y : G, y ∉ H → Q ⊓ Submission.Blueprint.conj y Q = ⊥ :=
    Work.ThmG.rankOne_isTI h
  -- `Res_H^G (Ind_H^G ν) = ν`.
  have hhall := Work.ThmG.resFun_indFun_eq_of_vanishes_off_hall
      (H := H) (Q := Q) (D := Submission.Blueprint.twoPoint H t)
      h.sup_eq h.inf_eq hcop h.normal hTI ν hν_class hν1 hν0
  have hν_apply : ∀ y : H, Work.Induction.indFun H ν (y : G) = ν y := by
    intro y
    have hh := congrFun hhall y
    rwa [Work.Induction.resFun_apply] at hh
  -- `Ind_H^G δ = [G : H]·δ`.
  have hδ_apply : ∀ y : H,
      Work.Induction.indFun H δ (y : G) = (if y = 1 then (H.index : ℂ) else 0) := by
    intro y
    by_cases hy : y = 1
    · subst hy
      simpa [hδ] using Work.Induction.indFun_apply_one H δ
    · rw [ite_eq_right hy, Work.Induction.indFun_apply_def]
      -- `z * y * z⁻¹ ≠ 1` for every `z`, since `y ≠ 1`.
      have hzero : ∀ z : G,
          (if hz : z * (y : G) * z⁻¹ ∈ H then δ ⟨z * (y : G) * z⁻¹, hz⟩ else 0) = 0 := by
        intro z
        split_ifs with hz
        · have hne : (⟨z * (y : G) * z⁻¹, hz⟩ : H) ≠ 1 := by
            intro hc
            apply hy
            have h1 : z * (y : G) * z⁻¹ = 1 := by
              have := congrArg (fun w : H => (w : G)) hc
              simpa using this
            have hy1 : (y : G) = 1 := by
              calc (y : G) = z⁻¹ * (z * (y : G) * z⁻¹) * z := by group
                _ = z⁻¹ * 1 * z := by rw [h1]
                _ = 1 := by group
            exact Subtype.ext hy1
          simp [hδ, hne]
        · rfl
      rw [Finset.sum_congr rfl (fun z _ => hzero z), Finset.sum_const, Finset.card_univ]
      simp
  -- the additive decomposition `χ = ν + χ(1)·δ`, pushed through `indFun`
  have hsplit : χ = ν + (χ 1) • δ := by
    rw [hν, sub_add_cancel]
  have hfun : Work.Induction.indFun H χ
      = Work.Induction.indFun H ν + (χ 1) • Work.Induction.indFun H δ := by
    have h1 : Work.Induction.indFun H χ
        = Work.Induction.indFun H (ν + (χ 1) • δ) :=
      Work.Induction.indFun_congr H hsplit
    rw [h1, Work.Induction.indFun_add, Work.Induction.indFun_smul]
  rw [hfun]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hν_apply x, hδ_apply x]
  -- the two arithmetic inputs
  have hcast : (Nat.card H : ℂ) = (Nat.card Q : ℂ) *
      (Nat.card (Submission.Blueprint.twoPoint H t) : ℂ) := by
    rw [Work.ThmF.split_card_H h]; push_cast; ring
  have hidx : (H.index : ℂ) = (Nat.card Q : ℂ) + 1 := by
    rw [Work.ThmG.rankOne_index h]; push_cast; ring
  by_cases hx : x = 1
  · -- at the identity: `ν 1 = 0`, `Ind δ 1 = [G : H]`, and `|D|·|Q| = |H|`
    rw [ite_eq_left hx, ite_eq_left hx, hx, hν1, hχ1, hidx, hcast]
    ring
  · -- away from the identity: `Ind δ x = 0` and `ν x = χ x`
    rw [ite_eq_right hx, ite_eq_right hx]
    have hδx : δ x = 0 := by rw [hδ]; simp [hx]
    have hνx : ν x = χ x := by
      rw [hν]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hδx]
      ring
    rw [hνx]
    ring

end Work.ZassenhausPSL2.Feit

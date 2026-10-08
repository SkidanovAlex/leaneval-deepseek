import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.Tau
import Submission.Work.Tame.inConjAU_iff
import Submission.Work.Tame.punct_subset_conjAU

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Tame

open scoped Pointwise

/-- **Feit–Thompson Lemma 9.1, vanishing part, second summand** (p. 805).  Let `L̂` be tamely
imbedded in `X` with supporting subgroups `Hs`, let `α ∈ 𝓒₀(L̂)` and let `i` be a supporting index.
If `N ∈ 𝔑_i = N(𝔎_i)` is not conjugate to any element of `AU` (`¬ inConjAU Lhat n Hs N`), then
`α_{i2}(N) = 0`, where `α_{i2} = Ind_{𝔏 ∩ 𝔑_i}^{𝔑_i}(α|_{𝔏 ∩ 𝔑_i})` is the second term of (9.4).

Proof route: by definition of `Induction.indFun`, `α_{i2}(N)` is `|𝔏 ∩ 𝔑_i|⁻¹` times a sum of terms
`α(y)`, one for each `y ∈ 𝔑_i` conjugate to `N` by an element of `𝔑_i` (`y = x*N*x⁻¹ ∈ 𝔏 ∩ 𝔑_i`).
A non-zero term requires `y ∈ L̂` (and `y ≠ 1`, as `α 1 = 0`), so `N` is conjugate to a non-identity
element of `L̂`, whose conjugacy class meets `AU` by `punct_subset_conjAU`; transitivity of `IsConj`
and `inConjAU_iff` then contradict `¬ inConjAU … N`.  Hence every summand vanishes.

The statement is the exact ingredient needed for the second sum in (9.4); it is not vacuous
(e.g. `N = 1` is conjugate to no element of `AU` when `AU` contains no conjugate of `1`, and then
`α_{i2}(1) = [𝔑_i : 𝔏 ∩ 𝔑_i] * α 1 = 0`). -/
theorem alphaI2_apply_eq_zero_of_not_inConjAU {X : Type*} [Group X] [Fintype X] {Lhat : Set X}
    {n : ℕ} {Hs : Fin n → Subgroup X} (h : IsTamelyImbedded Lhat n Hs)
    {α : ↥(Lgrp Lhat) → ℂ} (hα : α ∈ C0 Lhat) (i : Fin n)
    {N : ↥(Lgrp (Hs i : Set X))} (hN : ¬ inConjAU Lhat n Hs (N : X)) :
    alphaI2LM Lhat (Hs i) α N = 0 := by
  classical
  -- `α_{i2}` is the induced function `Ind_{𝔏 ⊓ 𝔑_i}^{𝔑_i}(α|_{𝔏 ⊓ 𝔑_i})`
  rw [alphaI2LM_apply, Work.Induction.indFun_apply_def]
  -- so `α_{i2}(N) = |𝔏 ⊓ 𝔑_i|⁻¹ * ∑_{x ∈ 𝔑_i} α(y_x)` with `y_x = x * N * x⁻¹ ∈ 𝔏 ⊓ 𝔑_i`;
  -- every summand vanishes, because a non-vanishing summand exhibits `N` as conjugate to a
  -- non-identity element of `L̂`, hence to an element of `AU`
  have hsum : (∑ x : ↥(Lgrp (Hs i : Set X)),
      if hx : x * N * x⁻¹ ∈
          (Lgrp Lhat ⊓ Lgrp (Hs i : Set X)).subgroupOf (Lgrp (Hs i : Set X))
        then (fun m => α (Subgroup.inclusion inf_le_left
          ((Subgroup.subgroupOfEquivOfLe
            (inf_le_right : Lgrp Lhat ⊓ Lgrp (Hs i : Set X) ≤ Lgrp (Hs i : Set X))) m)))
          ⟨x * N * x⁻¹, hx⟩
        else 0) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : x * N * x⁻¹ ∈
        (Lgrp Lhat ⊓ Lgrp (Hs i : Set X)).subgroupOf (Lgrp (Hs i : Set X))
    · rw [dif_pos hx]
      -- the summand is `α (m)`, where `m ∈ 𝔏` is the 𝔏-component of `x * N * x⁻¹`
      set y : ↥((Lgrp Lhat ⊓ Lgrp (Hs i : Set X)).subgroupOf (Lgrp (Hs i : Set X))) :=
        ⟨x * N * x⁻¹, hx⟩ with hy
      change α (Subgroup.inclusion inf_le_left
        (Subgroup.subgroupOfEquivOfLe
          (inf_le_right : Lgrp Lhat ⊓ Lgrp (Hs i : Set X) ≤ Lgrp (Hs i : Set X)) y)) = 0
      set m : ↥(Lgrp Lhat) := Subgroup.inclusion inf_le_left
        (Subgroup.subgroupOfEquivOfLe
          (inf_le_right : Lgrp Lhat ⊓ Lgrp (Hs i : Set X) ≤ Lgrp (Hs i : Set X)) y) with hm
      change α m = 0
      by_contra hne
      -- `(m : X) = x * N * x⁻¹`, so `N` and `m` are conjugate in `X`
      have hmX_eq : (m : X) = (x : X) * (N : X) * (x : X)⁻¹ := by
        simp only [hm, hy, Subgroup.coe_inclusion, Subgroup.subgroupOfEquivOfLe_apply_coe,
          Subgroup.coe_mul, Subgroup.coe_inv]
      -- `α m ≠ 0` forces `(m : X) ∈ L̂^#`
      have hmem : (m : X) ∈ Lhat := by
        by_contra hc
        exact hne (hα.2.1 m hc)
      have hone : (m : X) ≠ 1 := by
        intro hc
        have hm1 : m = 1 := Subtype.ext (by simpa using hc)
        exact hne (by rw [hm1]; exact hα.2.2)
      -- ... whose conjugacy class meets `AU`
      obtain ⟨a, ha, hconja⟩ := punct_subset_conjAU h hmem hone
      exact hN ((inConjAU_iff h).mpr ⟨a, ha,
        (isConj_iff.mpr ⟨(x : X), hmX_eq.symm⟩).trans hconja⟩)
    · rw [dif_neg hx]
  rw [hsum, mul_zero]

end Work.Tame

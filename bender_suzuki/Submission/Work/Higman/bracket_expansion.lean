import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.commutator_powSub_A_C

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-!
# Step 5: the bracket layer `⌊·,·⌋ : C/A × A/A² → A²/A⁴`

Higman 1963, §3–§5.  For `u ∈ C` and `a ∈ A` the commutator `⁅u,a⁆` lies in `A²` (unipotence), and
its class modulo `A⁴` depends only on `u` modulo `A` and on `a` modulo `A²` — that is the
well-defined biadditive pairing `⌊·,·⌋` whose monomial expansion (in the `𝔽_q`-coordinates of
Step 4) is what forces the contradiction at the end of the proof.

This file starts that layer with its first two identities:

* the bracket is **multiplicative in the second variable exactly**:
  `⁅u, a * b⁆ = ⁅u, a⁆ * ⁅u, b⁆` for `u ∈ C`, `a, b ∈ A` (both `⁅u,a⁆, ⁅u,b⁆ ∈ A² ⊆ A` and `A` is
  abelian, so the usual `[u, ab] = [u,a]·(a [u,b] a⁻¹)` collapses);
* hence `⌊·,·⌋` is **additive in the second variable** and, since `⁅C, A²⁆ = A⁴`
  (`commutator_powSub_A_C`), it **descends to `A / A²`**.
-/

/-- **Bracket layer, first monomial.**  For `u ∈ C` and `a, b ∈ A` the bracket is multiplicative in
the second variable: `⁅u, a * b⁆ = ⁅u, a⁆ * ⁅u, b⁆`. -/
theorem bracket_mul_right (h : IsSuzuki2Grp P) {A C : Subgroup P} (hA : IsXiAbelNormal h A)
    (hCd : ⁅C, C⁆ = A) {u : P} (hu : u ∈ C) {a b : P} (ha : a ∈ A) (hb : b ∈ A) :
    ⁅u, a * b⁆ = ⁅u, a⁆ * ⁅u, b⁆ := by
  have hub : ⁅u, b⁆ ∈ A :=
    powSub_le (by norm_num) (commutator_mem_powSub_two h hA u b hb)
  have hconj : a * ⁅u, b⁆ * a⁻¹ = ⁅u, b⁆ := by
    rw [hA.abelian a ha ⁅u, b⁆ hub]
    group
  have h1 : ⁅u, a * b⁆ = ⁅u, a⁆ * (a * ⁅u, b⁆ * a⁻¹) := by
    rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
    group
  rw [h1, hconj]

/-- **Bracket layer, first-variable companion.**  For `u, v ∈ C` and `a ∈ A` the bracket is additive
in the *first* variable only modulo `A⁴`: `⁅u * v, a⁆ ≡ ⁅u, a⁆ * ⁅v, a⁆ (mod A⁴)`.  The correction
is `⁅u, ⁅v, a⁆⁆`, which lies in `⁅C, A²⁆ = A⁴` (step 3 at `k = 1`) and need not vanish — this is
the asymmetry with `bracket_mul_right`. -/
theorem bracket_mul_left (h : IsSuzuki2Grp P) {A C : Subgroup P} (hA : IsXiAbelNormal h A)
    (hCn : C.Normal) (hCd : ⁅C, C⁆ = A) (hC2 : powSub C 2 ≤ A) {u v : P} (hu : u ∈ C)
    (hv : v ∈ C) {a : P} (ha : a ∈ A) :
    ⁅u * v, a⁆ * (⁅u, a⁆ * ⁅v, a⁆)⁻¹ ∈ powSub A 4 := by
  have hva : ⁅v, a⁆ ∈ powSub A 2 := commutator_mem_powSub_two h hA v a ha
  have hua : ⁅u, a⁆ ∈ powSub A 2 := commutator_mem_powSub_two h hA u a ha
  -- the correction `⁅u, ⁅v,a⁆⁆` lies in `⁅C, A²⁆ = A⁴`
  have h4 : ⁅u, ⁅v, a⁆⁆ ∈ powSub A 4 := by
    have hstep := commutator_powSub_A_C h hA hCn hC2 hCd 1
    rw [show (2:ℕ) ^ 1 = 2 from by norm_num, show (2:ℕ) ^ (1+1) = 4 from by norm_num] at hstep
    rw [← hstep, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hu hva
  -- `⁅u v, a⁆ = ⁅u, ⁅v,a⁆⁆ * (⁅v,a⁆ * ⁅u,a⁆)`
  have h1 : ⁅u * v, a⁆ = ⁅u, ⁅v, a⁆⁆ * (⁅v, a⁆ * ⁅u, a⁆) := by
    rw [commutatorElement_def, commutatorElement_def, commutatorElement_def,
      commutatorElement_def]
    group
  -- everything lives in the abelian `A`
  have hmemA : ⁅u, ⁅v, a⁆⁆ ∈ A := powSub_le (by norm_num) h4
  have hvam : ⁅v, a⁆ ∈ A := powSub_le (by norm_num) hva
  have huam : ⁅u, a⁆ ∈ A := powSub_le (by norm_num) hua
  have hkey : ⁅u, ⁅v, a⁆⁆ * (⁅v, a⁆ * ⁅u, a⁆) * (⁅u, a⁆ * ⁅v, a⁆)⁻¹ = ⁅u, ⁅v, a⁆⁆ := by
    rw [hA.abelian ⁅v, a⁆ hvam ⁅u, a⁆ huam]
    group
  rw [h1, hkey]
  exact h4

/-- **Bracket layer, well-definedness in the first variable.**  The class of `⁅u,a⁆` modulo `A⁴`
depends only on the class of `u` modulo `A`.  Together with `bracket_wd_right` this says that
`⌊u, a⌋ := ⁅u,a⁆ · A⁴` is a well-defined pairing `C/A × A/A² → A²/A⁴`. -/
theorem bracket_wd_left (h : IsSuzuki2Grp P) {A C : Subgroup P} (hA : IsXiAbelNormal h A)
    (hCn : C.Normal) (hCd : ⁅C, C⁆ = A) (hC2 : powSub C 2 ≤ A) {u u' : P} (hu : u ∈ C)
    (hu' : u' ∈ C) (h1 : u' * u⁻¹ ∈ A) {a : P} (ha : a ∈ A) :
    ⁅u', a⁆ * ⁅u, a⁆⁻¹ ∈ powSub A 4 := by
  have hAC : A ≤ C := by
    rw [← hCd, Subgroup.commutator_le]
    intro x hx y hy
    exact C.mul_mem (C.mul_mem (C.mul_mem hx hy) (C.inv_mem hx)) (C.inv_mem hy)
  have huA : u' * u⁻¹ ∈ C := hAC h1
  -- `u' = (u' u⁻¹) * u`, and `⁅u' u⁻¹, a⁆ = 1` as both lie in the abelian `A`
  have hdecomp : u' = (u' * u⁻¹) * u := by group
  have hone : ⁅u' * u⁻¹, a⁆ = 1 := by
    rw [commutatorElement_def, hA.abelian (u' * u⁻¹) h1 a ha]
    group
  have key : ⁅u', a⁆ * ⁅u, a⁆⁻¹
      = ⁅(u' * u⁻¹) * u, a⁆ * (⁅u' * u⁻¹, a⁆ * ⁅u, a⁆)⁻¹ := by
    conv_lhs => rw [hdecomp]
    rw [hone, one_mul]
  rw [key]
  exact bracket_mul_left h hA hCn hCd hC2 huA hu ha

/-- **Bracket layer, well-definedness in the second variable.**  The class of `⁅u,a⁆` modulo `A⁴`
depends only on the class of `a` modulo `A²`. -/
theorem bracket_wd_right (h : IsSuzuki2Grp P) {A C : Subgroup P} (hA : IsXiAbelNormal h A)
    (hCn : C.Normal) (hCd : ⁅C, C⁆ = A) (hC2 : powSub C 2 ≤ A) {u a a' : P} (hu : u ∈ C)
    (ha : a ∈ A) (ha' : a' ∈ A) (h2 : a' * a⁻¹ ∈ powSub A 2) :
    ⁅u, a'⁆ * ⁅u, a⁆⁻¹ ∈ powSub A 4 := by
  -- `a' = (a' a⁻¹) * a`
  have hdecomp : a' = (a' * a⁻¹) * a := by group
  -- the bracket is multiplicative in the second variable
  have hmul := bracket_mul_right h hA hCd hu (A.mul_mem ha' (A.inv_mem ha)) ha
  -- `⁅C, A²⁆ = A⁴`, so `⁅u, a' a⁻¹⁆ ∈ A⁴`
  have h4 : ⁅u, a' * a⁻¹⁆ ∈ powSub A 4 := by
    have hstep := commutator_powSub_A_C h hA hCn hC2 hCd 1
    rw [show (2:ℕ) ^ 1 = 2 from by norm_num, show (2:ℕ) ^ (1+1) = 4 from by norm_num] at hstep
    rw [← hstep, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hu h2
  -- `[u, a'] = [u, (a' a⁻¹) a] = [u, a' a⁻¹] * [u, a]`
  have key : ⁅u, a'⁆ = ⁅u, a' * a⁻¹⁆ * ⁅u, a⁆ := by
    conv_lhs => rw [hdecomp]
    exact hmul
  have key2 : ⁅u, a'⁆ * ⁅u, a⁆⁻¹ = ⁅u, a' * a⁻¹⁆ := by
    rw [key]
    group
  rw [key2]
  exact h4

end Work.Higman

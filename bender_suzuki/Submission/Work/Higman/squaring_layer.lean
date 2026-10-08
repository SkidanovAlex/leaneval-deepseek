import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.commutator_powSub_A_C
import Submission.Work.Higman.bracket_expansion

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
# Step 5: the squaring map `s : C/A → A/A²` and its polar identity

Higman 1963, §3–§5.  With `C ^ (2) ≤ A = ⁅C,C⁆`:

* the squaring map `s(uA) = u² A²` is well defined into `A / A²` (the `A`-coset does not matter);
* `s` is *quadratic* with polar form the bracket pairing `⌊·,·⌋` of `bracket_expansion.lean`:
  `(uv)² ≡ ⁅v,u⁆ · u² · v² (mod A²)`;
* the relation `⌊x, s(x)⌋ = 0` — `⁅u, u²⁆ = 1` — transferred by well-definedness of the bracket in
  its second variable: **`⁅u,a⁆ ∈ A⁴` whenever `a ≡ u² (mod A²)`**.  That is the last
  group-theoretic input before the monomial expansion.
-/

/-- The square of an element of `C` lies in `A`. -/
theorem sq_mem_A {A C : Subgroup P} (hC2 : powSub C 2 ≤ A) {u : P} (hu : u ∈ C) :
    u * u ∈ A := by
  have hmem : u ^ 2 ∈ powSub C 2 := pow_mem_powSub (A := C) hu
  simpa [pow_two] using hC2 hmem

/-- **Squaring layer: well-definedness.**  The class of `u²` modulo `A²` depends only on the class of
`u` modulo `A`: for `u ∈ C`, `a ∈ A`, `(u a)² ≡ u² (mod A²)`. -/
theorem sq_class_wd (h : IsSuzuki2Grp P) {A C : Subgroup P} (hA : IsXiAbelNormal h A)
    (hC2 : powSub C 2 ≤ A) {u a : P} (hu : u ∈ C) (ha : a ∈ A) :
    (u * a) * (u * a) * (u * u)⁻¹ ∈ powSub A 2 := by
  have hu2A : u * u ∈ A := sq_mem_A hC2 hu
  have hcomm : a * (u * u) = (u * u) * a := hA.abelian a ha (u * u) hu2A
  have h1 : (u * a) * (u * a) = (u * a * u⁻¹) * (u * u) * a := by group
  have h2 : u * a * u⁻¹ = ⁅u, a⁆ * a := by
    rw [commutatorElement_def]
    group
  have hgoal : (u * a) * (u * a) * (u * u)⁻¹ = ⁅u, a⁆ * (a * a) := by
    have hc2 : (u * u) * a * (u * u)⁻¹ = a := by
      rw [← hcomm]
      group
    rw [h1, h2]
    rw [show (⁅u, a⁆ * a * (u * u) * a) * (u * u)⁻¹
        = ⁅u, a⁆ * a * ((u * u) * a * (u * u)⁻¹) from by group, hc2]
    group
  rw [hgoal]
  exact Subgroup.mul_mem _ (commutator_mem_powSub_two h hA u a ha)
    (by simpa [pow_two] using pow_mem_powSub (A := A) (n := 2) ha)

/-- **Squaring layer: the polar identity.**  For `u, v ∈ C`,
`(u v)² ≡ ⁅v,u⁆ · u² · v² (mod A²)`: the squaring map is quadratic with polar form the bracket
pairing.  The correction `⁅u,⁅v,u⁆⁆` lies in `A²`. -/
theorem sq_polar (h : IsSuzuki2Grp P) {A C : Subgroup P} (hA : IsXiAbelNormal h A)
    (hCd : ⁅C, C⁆ = A) {u v : P} (hu : u ∈ C) (hv : v ∈ C) :
    (u * v) * (u * v) * (⁅v, u⁆ * (u * u) * (v * v))⁻¹ ∈ powSub A 2 := by
  have h1 : (u * v) * (u * v) = ⁅u, ⁅v, u⁆⁆ * (⁅v, u⁆ * (u * u) * (v * v)) := by
    simp only [commutatorElement_def]
    group
  have hchi : ⁅u, ⁅v, u⁆⁆ ∈ powSub A 2 :=
    commutator_mem_powSub_two h hA u ⁅v, u⁆ (by
      rw [← hCd]
      exact Subgroup.commutator_mem_commutator hv hu)
  have hkey : (u * v) * (u * v) * (⁅v, u⁆ * (u * u) * (v * v))⁻¹ = ⁅u, ⁅v, u⁆⁆ := by
    rw [h1]
    group
  rw [hkey]
  exact hchi

/-- **Squaring layer: the relation `⌊x, s(x)⌋ = 0`.**  If `a ∈ A` represents the square class of
`u ∈ C`, i.e. `a ≡ u² (mod A²)`, then `⁅u,a⁆ ∈ A⁴`.  (The representative `a = u²` itself gives
`⁅u,u²⁆ = 1`, and well-definedness of the bracket in its second variable transfers this to every
`a ≡ u²`.) -/
theorem bracket_sq_class (h : IsSuzuki2Grp P) {A C : Subgroup P} (hA : IsXiAbelNormal h A)
    (hCn : C.Normal) (hCd : ⁅C, C⁆ = A) (hC2 : powSub C 2 ≤ A) {u a : P} (hu : u ∈ C)
    (ha : a ∈ A) (hclass : a * (u * u)⁻¹ ∈ powSub A 2) : ⁅u, a⁆ ∈ powSub A 4 := by
  have hu2A : u * u ∈ A := sq_mem_A hC2 hu
  have hwd : ⁅u, a⁆ * ⁅u, u * u⁆⁻¹ ∈ powSub A 4 :=
    bracket_wd_right h hA hCn hCd hC2 hu hu2A ha hclass
  have hsq : ⁅u, u * u⁆ = 1 := by
    rw [commutatorElement_def]
    group
  rw [hsq, inv_one, mul_one] at hwd
  exact hwd

end Work.Higman

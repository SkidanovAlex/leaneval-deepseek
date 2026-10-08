import Mathlib
import Submission.Work.Higman.clo_hard_defs
import Submission.Work.Higman.bracket_expansion

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Elementary auxiliary facts for the bracket pairing `cloBetaV`

This file collects the small, reusable facts about the objects of `clo_hard_defs` that the
proof of the properties of `cloBetaV : C/A × Ω₁(P) → Ω₁(P)` needs:

* power subgroups of a `ξ`-invariant abelian normal subgroup have bounded exponent
  (`powSub_pow_exp_eq_one`, `powSub_four_exp`), and powers of products of commuting elements
  split (`mul_pow_of_mem`), whence the key "correction in `A⁴` dies under `^ 2 ^ (e-2)`" lemma
  (`mul_pow_sub_two_of_mem_four`);
* `A ≤ C` when `⁅C,C⁆ = A` (`le_commutator_eq`), and `⁅C,A⁆ = A²` (`commutator_C_A_eq`);
* the two "same class mod `A`" statements for `cloRepC` (`cloRepC_inv_mul_mem`,
  `cloRepC_mul_inv_mem`);
* the lift relation for `cloLiftA` (`cloLiftA_mul_inv_mem`);
* the action of `cloXiQuot` on a representative (`cloXiQuot_mk`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-! ## Powers in a homocyclic layer -/

/-- In an abelian subgroup, the `n`-th power of a product is the product of the `n`-th powers. -/
theorem mul_pow_of_mem (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A) {x y : P}
    (hx : x ∈ A) (hy : y ∈ A) (n : ℕ) : (x * y) ^ n = x ^ n * y ^ n :=
  Commute.mul_pow (show Commute x y from hA.abelian x hx y hy) n

/-- **The exponent of the layer `A ^ (2 ^ k)`.**  If `2 ^ e` is an exponent of the abelian
subgroup `A` and `k ≤ e`, then every element of `A ^ (2 ^ k)` has `2 ^ (e - k)`-th power `1`. -/
theorem powSub_pow_exp_eq_one (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    {e k : ℕ} (he1 : ∀ a ∈ A, a ^ 2 ^ e = 1) (hk : k ≤ e) {c : P}
    (hc : c ∈ powSub A (2 ^ k)) : c ^ 2 ^ (e - k) = 1 := by
  obtain ⟨d, hd, rfl⟩ := (mem_powSub_iff hA.abelian).mp hc
  rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hk]
  exact he1 d hd

/-- **Every element of `A⁴` has `2 ^ (e - 2)`-th power `1`** (here `2 ≤ e`). -/
theorem powSub_four_exp (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    {e : ℕ} (he1 : ∀ a ∈ A, a ^ 2 ^ e = 1) (he2 : 2 ≤ e) {c : P}
    (hc : c ∈ powSub A 4) : c ^ 2 ^ (e - 2) = 1 := by
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h4] at hc
  exact powSub_pow_exp_eq_one h hA he1 he2 hc

/-- **The corrections in `A⁴` are invisible after raising to the `2 ^ (e-2)`-nd power.**
For `c ∈ A⁴` and `y ∈ A` one has `(c * y) ^ 2 ^ (e-2) = y ^ 2 ^ (e-2)`. -/
theorem mul_pow_sub_two_of_mem_four (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hA : IsXiAbelNormal h A) {e : ℕ} (he1 : ∀ a ∈ A, a ^ 2 ^ e = 1) (he2 : 2 ≤ e)
    {c y : P} (hc : c ∈ powSub A 4) (hy : y ∈ A) :
    (c * y) ^ 2 ^ (e - 2) = y ^ 2 ^ (e - 2) := by
  have hcA : c ∈ A := powSub_le (by norm_num) hc
  rw [mul_pow_of_mem h hA hcA hy]
  rw [powSub_four_exp h hA he1 he2 hc, one_mul]

/-! ## The lower central series of `C` -/

/-- `⁅C,C⁆ = A` implies `A ≤ C`. -/
theorem le_commutator_eq {A C : Subgroup P} (hCd : ⁅C, C⁆ = A) : A ≤ C := by
  rw [← hCd, Subgroup.commutator_le]
  intro x hx y hy
  exact C.mul_mem (C.mul_mem (C.mul_mem hx hy) (C.inv_mem hx)) (C.inv_mem hy)

/-- **The bracket layer, in the form used below**: `⁅C,A⁆ = A²` (this is
`commutator_powSub_A_C` at `k = 0`, commuted). -/
theorem commutator_C_A_eq (h : IsSuzuki2Grp P) {A C : Subgroup P} (hA : IsXiAbelNormal h A)
    (hCn : C.Normal) (hC2 : powSub C 2 ≤ A) (hCd : ⁅C, C⁆ = A) :
    ⁅C, A⁆ = powSub A 2 := by
  have hstep := commutator_powSub_A_C h hA hCn hC2 hCd 0
  rw [pow_zero, powSub_one_eq, show (2 : ℕ) ^ (0 + 1) = 2 from by norm_num] at hstep
  rw [← hstep, Subgroup.commutator_comm]

/-! ## Representatives and lifts -/

variable {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]

/-- The other order of `cloRepC_mul_inv_mem`: the chosen representative of `x` and `u` differ by
an element of `A` in either order. -/
theorem cloRepC_mul_inv_mem' (x : ↥C ⧸ (A.subgroupOf C)) (u : ↥C)
    (hu : QuotientGroup.mk u = x) : ((cloRepC x * u⁻¹ : ↥C) : P) ∈ A := by
  classical
  have hmem : (((cloRepC x)⁻¹ * u : ↥C) : P) ∈ A := cloRepC_mul_inv_mem hu
  have hconj : (((cloRepC x * u⁻¹ : ↥C) : P))
      = (cloRepC x : P) * ((((cloRepC x)⁻¹ * u : ↥C) : P))⁻¹ * (cloRepC x : P)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [hconj]
  exact hAn.conj_mem
    ((((cloRepC x)⁻¹ * u : ↥C) : P))⁻¹ (A.inv_mem hmem) (cloRepC x : P)

/-- **Two lifts of the same `w ∈ Ω₁(P)` in `A` differ by an element of `A²`.** -/
theorem cloLiftA_mul_inv_mem (S : CloH8Data h A C) (w : ↥(omega1 P)) {a : P} (ha : a ∈ A)
    (haw : a ^ 2 ^ (S.e - 1) = (w : P)) :
    (cloLiftA S w : P) * a⁻¹ ∈ powSub A 2 := by
  have hb : (cloLiftA S w : P) ∈ A := (cloLiftA S w).2
  have hcomm : Commute (cloLiftA S w : P) a⁻¹ :=
    S.hA.abelian _ hb _ (A.inv_mem ha)
  have hpow : ((cloLiftA S w : P) * a⁻¹) ^ 2 ^ (S.e - 1) = 1 := by
    rw [hcomm.mul_pow, inv_pow, cloLiftA_spec S w, haw, mul_inv_cancel]
  exact (S.hkey _ (A.mul_mem hb (A.inv_mem ha))).mpr hpow

/-! ## The induced action on `C/A` -/

/-- **`cloXiQuot` on a representative.** -/
theorem cloXiQuot_mk (h : IsSuzuki2Grp P) (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) (u : ↥C) :
    cloXiQuot h hAinv hCinv (QuotientGroup.mk u) = QuotientGroup.mk (cloXiC h hCinv u) := by
  rw [cloXiQuot]
  exact QuotientGroup.congr_mk (A.subgroupOf C) (A.subgroupOf C) (cloXiC h hCinv)
    (clo_map_xi_subgroupOf h hAinv hCinv) u

end Work.Higman

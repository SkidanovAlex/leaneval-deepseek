/-
Feit--Thompson odd order drive: `Work.LocalPrelim.conjRep_sub_one_pow_four_eq_zero`.

If `[[[[M,A],A],A],A] = 1` for a normal elementary abelian `p`-subgroup `M`, then every `a ∈ A`
acts *nilpotently of index four* on `M`:

  `(conjRep M a - 1) ^ 4 = 0`.

This is the iterated version of `Work.PStable.conjRep_sub_one_sq_eq_zero`.  Writing
`δ = conjRep M a - 1`, one has `δ x = [a, x]` (transported to the abelian group `Additive ↥M`),
so by induction `δ ^ n x = [a, [a, ... [a, x] ...]]` (`n` copies of `a`), which lies in the
`n`-fold relative commutator subgroup `[M, A, ..., A]` (`n` copies of `A`).  For `n = 4` this
subgroup is `⊥` by hypothesis, whence `δ ^ 4 = 0`.
-/
import Mathlib
import Submission.Work.PStable.conjData

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped IsMulCommutative commutatorElement

namespace Work.LocalPrelim

open Work.PStable

/-- The map `x ↦ a x a⁻¹ x⁻¹` on `M`, i.e. `conjRep M a - 1` transported to the group `M`. -/
def conjMinusOne {G : Type*} [Group G] (M : Subgroup G) [M.Normal] (a : G) : ↥M → ↥M :=
  fun x => MulAut.conjNormal a x * x⁻¹

/-- The iterated relative commutator chain `C 0 = M`, `C (n+1) = ⁅C n, A⁆`. -/
def commChain {G : Type*} [Group G] (M A : Subgroup G) : ℕ → Subgroup G
  | 0 => M
  | n + 1 => ⁅commChain M A n, A⁆

/-- `conjMinusOne M a x` is the commutator `[x, a]⁻¹`. -/
lemma conjMinusOne_coe {G : Type*} [Group G] (M : Subgroup G) [M.Normal] (a : G) (x : ↥M) :
    ((conjMinusOne M a x : ↥M) : G) = ⁅(x : G), a⁆⁻¹ := by
  rw [conjMinusOne, Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply,
    commutatorElement_def]
  group

/-- `conjRep M a - 1` is `conjMinusOne M a`, transported to `Additive ↥M` on basis vectors. -/
lemma conjRep_sub_one_apply {G : Type*} [Group G] (M : Subgroup G) [M.Normal]
    [IsMulCommutative ↥M] {p : ℕ} [Fact (∀ x : ↥M, x ^ p = 1)] (a : G) (x : ↥M) :
    (conjRep (p := p) M a - 1) (Additive.ofMul x) = Additive.ofMul (conjMinusOne M a x) := by
  rw [LinearMap.sub_apply, Module.End.one_apply, conjRep_apply, sub_eq_add_neg]
  rfl

/-- `conjMinusOne M a` maps the `n`-fold commutator subgroup into the `(n+1)`-fold one. -/
lemma conjMinusOne_mem_succ {G : Type*} [Group G] (M A : Subgroup G) [M.Normal]
    (a : G) (ha : a ∈ A) {n : ℕ} {x : ↥M} (hx : (x : G) ∈ commChain M A n) :
    ((conjMinusOne M a x : ↥M) : G) ∈ commChain M A (n + 1) := by
  rw [conjMinusOne_coe]
  exact (commChain M A (n+1)).inv_mem (Subgroup.commutator_mem_commutator hx ha)

/-- The `n`-fold iterate of `conjMinusOne M a` maps `M = C 0` into `C n`. -/
lemma iterate_conjMinusOne_mem {G : Type*} [Group G] (M A : Subgroup G) [M.Normal]
    (a : G) (ha : a ∈ A) (m : ↥M) :
    ∀ n : ℕ, ((((conjMinusOne M a)^[n]) m) : G) ∈ commChain M A n := by
  intro n
  induction n with
  | zero => exact m.2
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact conjMinusOne_mem_succ M A a ha ih

/-- On basis vectors, `(conjRep M a - 1) ^ n` is the `n`-fold iterate of `conjMinusOne M a`. -/
lemma conjRep_sub_one_pow_apply {G : Type*} [Group G] (M : Subgroup G) [M.Normal]
    [IsMulCommutative ↥M] {p : ℕ} [Fact (∀ x : ↥M, x ^ p = 1)] (a : G) (n : ℕ) (m : ↥M) :
    ((conjRep (p := p) M a - 1)^n) (Additive.ofMul m)
      = Additive.ofMul (((conjMinusOne M a)^[n]) m) := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih m, conjRep_sub_one_apply, Function.iterate_succ_apply']

lemma conjRep_sub_one_pow_four_eq_zero {G : Type*} [Group G] (M : Subgroup G) [M.Normal]
    [IsMulCommutative ↥M] {p : ℕ} [Fact (∀ x : ↥M, x ^ p = 1)]
    {A : Subgroup G} (hcomm : ⁅⁅⁅⁅M, A⁆, A⁆, A⁆, A⁆ = ⊥) {a : G} (ha : a ∈ A) :
    (Work.PStable.conjRep (p := p) M a - 1) ^ 4 = 0 := by
  have hchain : commChain M A 4 = ⊥ := hcomm
  apply LinearMap.ext
  intro v
  obtain ⟨m, rfl⟩ := Additive.ofMul.surjective v
  rw [conjRep_sub_one_pow_apply (M := M) (p := p) a 4 m]
  have hm := iterate_conjMinusOne_mem M A a ha m 4
  rw [hchain, Subgroup.mem_bot] at hm
  have hz : (((conjMinusOne M a)^[4]) m) = 1 := Subtype.ext (by simpa using hm)
  rw [hz]
  rfl

end Work.LocalPrelim

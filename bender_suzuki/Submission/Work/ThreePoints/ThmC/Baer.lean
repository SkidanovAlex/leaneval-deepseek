import Mathlib
import Submission.Work.Coprime.Defs
import Submission.Work.Coprime.Internal
import Submission.Work.Coprime.abelian_split

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped commutatorElement Pointwise
open Subgroup

namespace Work.ThreePoints.ThmC

universe u

/-! ## 1. Square roots in finite groups of odd order -/

section SqRoot

variable {H : Type*} [Group H] [Finite H]

/-- In a finite group of odd order, squaring is injective. -/
theorem sq_injective_of_odd_card (hodd : Odd (Nat.card H)) :
    Function.Injective (fun x : H => x ^ 2) := by
  obtain ⟨k, hk⟩ := hodd
  have hkey : ∀ x : H, x = (x ^ 2) ^ (k + 1) := by
    intro x
    have h2 : 2 * (k + 1) = Nat.card H + 1 := by omega
    rw [← pow_mul, h2, pow_succ, orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_natCard x), one_mul]
  intro x y hxy
  rw [hkey x, hkey y]
  exact congrArg (fun t : H => t ^ (k + 1)) hxy

/-- In a finite group of odd order, squaring is bijective. -/
theorem sq_bijective_of_odd_card (hodd : Odd (Nat.card H)) :
    Function.Bijective (fun x : H => x ^ 2) :=
  ⟨sq_injective_of_odd_card hodd, Finite.surjective_of_injective (sq_injective_of_odd_card hodd)⟩

end SqRoot

section BaerBasic

variable {Q : Type*} [Group Q] [Finite Q] [Fact (Odd (Nat.card Q))]

/-- The unique square root of an element, in a finite group of odd order. -/
noncomputable def sqRoot (a : Q) : Q :=
  (Equiv.ofBijective (fun x : Q => x ^ 2) (sq_bijective_of_odd_card Fact.out)).symm a

theorem sqRoot_sq (a : Q) : sqRoot a ^ 2 = a := by
  show (fun x : Q => x ^ 2) (sqRoot a) = a
  exact (Equiv.ofBijective (fun x : Q => x ^ 2)
    (sq_bijective_of_odd_card Fact.out)).apply_symm_apply a

theorem sqRoot_eq_of_sq_eq {x a : Q} (h : x ^ 2 = a) : sqRoot a = x := by
  refine sq_injective_of_odd_card (H := Q) Fact.out ?_
  show sqRoot a ^ 2 = x ^ 2
  rw [sqRoot_sq, h]

theorem sqRoot_eq (a : Q) : sqRoot (a ^ 2) = a := sqRoot_eq_of_sq_eq rfl

@[simp]
theorem sqRoot_one : sqRoot (1 : Q) = 1 := sqRoot_eq_of_sq_eq (a := 1) (x := 1) (by rw [one_pow])

/-- The square root of a central element is central. -/
theorem sqRoot_mem_center {z : Q} (hz : z ∈ Subgroup.center Q) :
    sqRoot z ∈ Subgroup.center Q := by
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 : (g * sqRoot z * g⁻¹) ^ 2 = z := by
    show (MulAut.conj g (sqRoot z)) ^ 2 = z
    rw [← map_pow, sqRoot_sq]
    show MulAut.conj g z = z
    rw [show MulAut.conj g z = g * z * g⁻¹ from rfl, Subgroup.mem_center_iff.mp hz g]
    group
  have h2 : g * sqRoot z * g⁻¹ = sqRoot z := (sqRoot_eq_of_sq_eq (a := z) (x := g * sqRoot z * g⁻¹) h1).symm
  calc g * sqRoot z = (g * sqRoot z * g⁻¹) * g := by group
    _ = sqRoot z * g := by rw [h2]

theorem sqRoot_inv {z : Q} (hz : z ∈ Subgroup.center Q) : sqRoot z⁻¹ = (sqRoot z)⁻¹ := by
  refine sqRoot_eq_of_sq_eq (a := z⁻¹) (x := (sqRoot z)⁻¹) ?_
  show ((sqRoot z)⁻¹) ^ 2 = z⁻¹
  rw [show ((sqRoot z)⁻¹) ^ 2 = (sqRoot z ^ 2)⁻¹ from by group, sqRoot_sq]

theorem sqRoot_mul {z w : Q} (hz : z ∈ Subgroup.center Q) (hw : w ∈ Subgroup.center Q) :
    sqRoot (z * w) = sqRoot z * sqRoot w := by
  refine sqRoot_eq_of_sq_eq (a := z * w) (x := sqRoot z * sqRoot w) ?_
  have hz' := sqRoot_mem_center hz
  have hw' := sqRoot_mem_center hw
  have hcomm : Commute (sqRoot z) (sqRoot w) :=
    (Subgroup.mem_center_iff.mp hz' (sqRoot w)).symm
  show (sqRoot z * sqRoot w) ^ 2 = z * w
  rw [hcomm.mul_pow, sqRoot_sq, sqRoot_sq]

theorem sqRoot_pow {z : Q} (hz : z ∈ Subgroup.center Q) (n : ℕ) :
    sqRoot (z ^ n) = (sqRoot z) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, sqRoot_one]
  | succ n ih => rw [pow_succ, pow_succ, sqRoot_mul (Subgroup.pow_mem _ hz n) hz, ih]

end BaerBasic

/-! ## 2. Baer's abelian group law -/

section BaerMul

variable {Q : Type u} [Group Q] [Finite Q]
variable [Fact (Odd (Nat.card Q))]
variable [Fact (⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤ Subgroup.center Q)]

/-- Class `2`: every commutator is central. -/
theorem commutator_mem_center (a b : Q) : ⁅a, b⁆ ∈ Subgroup.center Q :=
  (Fact.out : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤ Subgroup.center Q)
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))

theorem sqRoot_commutator_mem_center (a b : Q) : sqRoot ⁅a, b⁆ ∈ Subgroup.center Q :=
  sqRoot_mem_center (commutator_mem_center a b)

theorem commutator_eq_one_of_mem_center {z w : Q} (hz : z ∈ Subgroup.center Q) : ⁅z, w⁆ = 1 :=
  Commute.commutator_eq ((Subgroup.mem_center_iff.mp hz w).symm)

theorem commutator_eq_one_of_mem_center' {z w : Q} (hw : w ∈ Subgroup.center Q) : ⁅z, w⁆ = 1 :=
  Commute.commutator_eq (Subgroup.mem_center_iff.mp hw z)

/-- A central factor can be moved past an element on its left. -/
theorem mul_central_comm {z : Q} (hz : z ∈ Subgroup.center Q) (a : Q) : a * z = z * a :=
  Subgroup.mem_center_iff.mp hz a

theorem commutator_swap (a b : Q) : ⁅a, b⁆ = ⁅b, a⁆⁻¹ := by
  rw [commutatorElement_def, commutatorElement_def]
  group

theorem commutator_inv_self (a : Q) : ⁅a, a⁻¹⁆ = 1 := by
  rw [commutatorElement_def]
  group

/-- In a group of class `2`, `[a,b] * (b * a) = a * b`. -/
theorem commutator_mul_mul_comm (a b : Q) : a * b = ⁅a, b⁆ * (b * a) := by
  rw [commutatorElement_def]
  group

/-- In a group of class `2`, `[a * b, c] = [a,c] * [b,c]`. -/
theorem commutator_mul_left (a b c : Q) : ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  have hb : ⁅b, c⁆ ∈ Subgroup.center Q := commutator_mem_center b c
  rw [commutatorElement_mul_left_eq_conj_mul,
    show a * ⁅b, c⁆ * a⁻¹ = ⁅b, c⁆ from by rw [mul_central_comm hb a]; group,
    mul_central_comm hb ⁅a, c⁆]

/-- Conjugating a central element is trivial. -/
theorem conj_central_cancel {z : Q} (hz : z ∈ Subgroup.center Q) (a : Q) :
    a * z * a⁻¹ = z := by
  rw [mul_central_comm hz a]
  group

/-- In a group of class `2`, `[a, b * c] = [a,b] * [a,c]`. -/
theorem commutator_mul_right (a b c : Q) : ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  have hc : ⁅a, c⁆ ∈ Subgroup.center Q := commutator_mem_center a c
  rw [commutatorElement_mul_right_eq_mul_conj,
    show ⁅a, b⁆ * b * ⁅a, c⁆ * b⁻¹ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) from by group,
    conj_central_cancel hc b]

/-- Inserting a central factor does not change a commutator. -/
theorem commutator_central_mul_left {z : Q} (hz : z ∈ Subgroup.center Q) (a b : Q) :
    ⁅z * a, b⁆ = ⁅a, b⁆ := by
  rw [commutator_mul_left, commutator_eq_one_of_mem_center hz, one_mul]

theorem commutator_central_mul_right {z : Q} (hz : z ∈ Subgroup.center Q) (a b : Q) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  rw [commutator_mul_right, commutator_eq_one_of_mem_center' hz, mul_one]

theorem commutator_central_mul_left' {z : Q} (hz : z ∈ Subgroup.center Q) (a b : Q) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  rw [commutator_mul_left, commutator_eq_one_of_mem_center hz, mul_one]

theorem commutator_central_mul_right' {z : Q} (hz : z ∈ Subgroup.center Q) (a b : Q) :
    ⁅a, z * b⁆ = ⁅a, b⁆ := by
  rw [commutator_mul_right, commutator_eq_one_of_mem_center' hz, one_mul]

/-- Baer's commutative law: `a + b = a * b * [a,b]⁻¹ᐟ²`. -/
noncomputable def badd (a b : Q) : Q := a * b * (sqRoot ⁅a, b⁆)⁻¹

theorem badd_eq (a b : Q) : badd a b = sqRoot ⁅a, b⁆ * (b * a) := by
  have hr : sqRoot ⁅a, b⁆ ∈ Subgroup.center Q := sqRoot_commutator_mem_center a b
  have key : a * b = (sqRoot ⁅a, b⁆ * sqRoot ⁅a, b⁆) * (b * a) := by
    conv_lhs => rw [commutator_mul_mul_comm, ← sqRoot_sq ⁅a, b⁆, pow_two]
  have hcancel : sqRoot ⁅a, b⁆ * (b * a) * (sqRoot ⁅a, b⁆)⁻¹ = b * a := by
    rw [mul_assoc (sqRoot ⁅a, b⁆) (b * a) (sqRoot ⁅a, b⁆)⁻¹,
      mul_central_comm (Subgroup.inv_mem _ hr) (b * a)]
    group
  show a * b * (sqRoot ⁅a, b⁆)⁻¹ = sqRoot ⁅a, b⁆ * (b * a)
  rw [key, show (sqRoot ⁅a, b⁆ * sqRoot ⁅a, b⁆) * (b * a) * (sqRoot ⁅a, b⁆)⁻¹
      = sqRoot ⁅a, b⁆ * (sqRoot ⁅a, b⁆ * (b * a) * (sqRoot ⁅a, b⁆)⁻¹) from by group,
    hcancel]

theorem commutator_badd_left (a b c : Q) : ⁅badd a b, c⁆ = ⁅b, c⁆ * ⁅a, c⁆ := by
  rw [badd_eq, commutator_central_mul_left (sqRoot_commutator_mem_center a b), commutator_mul_left]

theorem commutator_badd_right (a b c : Q) : ⁅a, badd b c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  rw [badd_eq, commutator_central_mul_right' (sqRoot_commutator_mem_center b c), commutator_mul_right,
    mul_central_comm (commutator_mem_center a b) ⁅a, c⁆]

theorem badd_comm (a b : Q) : badd a b = badd b a := by
  have hcm : ⁅a, b⁆ ∈ Subgroup.center Q := commutator_mem_center a b
  have hroot : sqRoot ⁅b, a⁆ = (sqRoot ⁅a, b⁆)⁻¹ := by
    rw [commutator_swap, sqRoot_inv hcm]
  have hab : a * b = (sqRoot ⁅a, b⁆ * sqRoot ⁅a, b⁆) * (b * a) := by
    conv_lhs => rw [commutator_mul_mul_comm, ← sqRoot_sq ⁅a, b⁆, pow_two]
  rw [badd_eq, badd_eq, hroot, hab]
  group

/-- The group identity behind the associativity of Baer's law. -/
theorem baer_assoc_aux {H : Type*} [Group H] {z₁ z₂ z₃ : H}
    (h₁ : ∀ x : H, x * z₁ = z₁ * x) (h₂ : ∀ x : H, x * z₂ = z₂ * x)
    (h₃ : ∀ x : H, x * z₃ = z₃ * x) (a b c : H) :
    (z₂ * z₃) * (c * (z₁ * (b * a))) = (z₁ * z₂) * (z₃ * (c * b) * a) := by
  have m₁ : ∀ u v : H, u * (z₁ * v) = z₁ * (u * v) := by
    intro u v
    rw [← mul_assoc, h₁ u, mul_assoc]
  rw [m₁ c (b * a), m₁ (z₂ * z₃) (c * (b * a))]
  rw [show (z₁ * z₂) * (z₃ * (c * b) * a) = z₁ * (z₂ * (z₃ * (c * b) * a)) from by
    rw [mul_assoc, mul_assoc]]
  rw [mul_assoc z₂ z₃ (c * (b * a)), mul_assoc z₃ (c * b) a, mul_assoc c b a]

theorem badd_assoc (a b c : Q) : badd (badd a b) c = badd a (badd b c) := by
  have hac : ⁅a, c⁆ ∈ Subgroup.center Q := commutator_mem_center a c
  have hab : ⁅a, b⁆ ∈ Subgroup.center Q := commutator_mem_center a b
  have hbc : ⁅b, c⁆ ∈ Subgroup.center Q := commutator_mem_center b c
  have hRac : sqRoot ⁅a, c⁆ ∈ Subgroup.center Q := sqRoot_mem_center hac
  have hRab : sqRoot ⁅a, b⁆ ∈ Subgroup.center Q := sqRoot_mem_center hab
  have hRbc : sqRoot ⁅b, c⁆ ∈ Subgroup.center Q := sqRoot_mem_center hbc
  have e1 : badd (badd a b) c
      = (sqRoot ⁅a, c⁆ * sqRoot ⁅b, c⁆) * (c * (sqRoot ⁅a, b⁆ * (b * a))) := by
    have h1 : badd (badd a b) c = sqRoot ⁅badd a b, c⁆ * (c * badd a b) := badd_eq _ _
    have h2 : ⁅badd a b, c⁆ = ⁅b, c⁆ * ⁅a, c⁆ := commutator_badd_left a b c
    have h3 : badd a b = sqRoot ⁅a, b⁆ * (b * a) := badd_eq a b
    rw [h1, h2, h3, sqRoot_mul hbc hac]
    rw [← mul_central_comm hRbc (sqRoot ⁅a, c⁆)]
  have e2 : badd a (badd b c)
      = (sqRoot ⁅a, b⁆ * sqRoot ⁅a, c⁆) * (sqRoot ⁅b, c⁆ * (c * b) * a) := by
    have h1 : badd a (badd b c) = sqRoot ⁅a, badd b c⁆ * (badd b c * a) := badd_eq _ _
    have h2 : ⁅a, badd b c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := commutator_badd_right a b c
    have h3 : badd b c = sqRoot ⁅b, c⁆ * (c * b) := badd_eq b c
    rw [h1, h2, h3, sqRoot_mul hab hac]
  rw [e1, e2]
  exact baer_assoc_aux (fun x => mul_central_comm hRab x) (fun x => mul_central_comm hRac x)
    (fun x => mul_central_comm hRbc x) a b c

theorem badd_one_left (a : Q) : badd 1 a = a := by
  rw [badd_eq, commutatorElement_one_left, sqRoot_one, one_mul, mul_one]

theorem badd_one_right (a : Q) : badd a 1 = a := by
  rw [badd_eq, commutatorElement_one_right, sqRoot_one, one_mul, one_mul]

theorem badd_inv_right (a : Q) : badd a a⁻¹ = 1 := by
  rw [badd_eq, commutator_inv_self, sqRoot_one, one_mul, inv_mul_cancel]

theorem badd_inv_left (a : Q) : badd a⁻¹ a = 1 := by
  rw [badd_comm a⁻¹ a]
  exact badd_inv_right a

theorem commutator_pow_self (a : Q) (n : ℕ) : ⁅a ^ n, a⁆ = 1 := by
  induction n with
  | zero => rw [pow_zero, commutatorElement_one_left]
  | succ n ih => rw [pow_succ, commutator_mul_left, ih, one_mul, commutatorElement_self]

/-- Every automorphism of `Q` is an automorphism of the Baer law. -/
theorem map_badd (φ : MulAut Q) (a b : Q) : φ (badd a b) = badd (φ a) (φ b) := by
  have hsq : φ (sqRoot ⁅a, b⁆) = sqRoot ⁅φ a, φ b⁆ := by
    refine (sqRoot_eq_of_sq_eq (a := ⁅φ a, φ b⁆) (x := φ (sqRoot ⁅a, b⁆)) ?_).symm
    show (φ (sqRoot ⁅a, b⁆)) ^ 2 = ⁅φ a, φ b⁆
    rw [← map_pow, sqRoot_sq, map_commutatorElement]
  rw [badd_eq, badd_eq, map_mul, map_mul, hsq]

end BaerMul

/-! ## 3. The Baer group as a wrapped copy of `Q` -/

/-- A wrapped copy of the underlying set of `Q`, carrying Baer's abelian group law. -/
structure BaerT (Q : Type u) where
  /-- The underlying element of `Q`. -/
  toQ : Q

namespace BaerT

variable {Q : Type u} [Group Q] [Finite Q] [Fact (Odd (Nat.card Q))]
  [Fact (⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤ Subgroup.center Q)]

theorem ext {a b : BaerT Q} (h : a.toQ = b.toQ) : a = b := by
  cases a
  cases b
  simpa using h

noncomputable def bmul (a b : BaerT Q) : BaerT Q := ⟨badd a.toQ b.toQ⟩

def bone : BaerT Q := ⟨1⟩

def binv (a : BaerT Q) : BaerT Q := ⟨a.toQ⁻¹⟩

@[simp] theorem bmul_toQ (a b : BaerT Q) : (bmul a b).toQ = badd a.toQ b.toQ := rfl

@[simp] theorem bone_toQ : (bone : BaerT Q).toQ = 1 := rfl

@[simp] theorem binv_toQ (a : BaerT Q) : (binv a).toQ = a.toQ⁻¹ := rfl

theorem bmul_assoc (a b c : BaerT Q) : bmul (bmul a b) c = bmul a (bmul b c) := by
  apply ext
  simp only [bmul_toQ]
  exact badd_assoc _ _ _

theorem bone_mul (a : BaerT Q) : bmul bone a = a := by
  apply ext
  simp only [bmul_toQ, bone_toQ]
  exact badd_one_left _

theorem bmul_bone (a : BaerT Q) : bmul a bone = a := by
  apply ext
  simp only [bmul_toQ, bone_toQ]
  exact badd_one_right _

theorem binv_mul (a : BaerT Q) : bmul (binv a) a = bone := by
  apply ext
  simp only [bmul_toQ, binv_toQ, bone_toQ]
  exact badd_inv_left _

theorem bmul_comm (a b : BaerT Q) : bmul a b = bmul b a := by
  apply ext
  simp only [bmul_toQ]
  exact badd_comm _ _

noncomputable instance instGroup : Group (BaerT Q) where
  mul := bmul
  one := bone
  inv := binv
  mul_assoc := bmul_assoc
  one_mul := bone_mul
  mul_one := bmul_bone
  inv_mul_cancel := binv_mul

instance instIsMulCommutative : IsMulCommutative (BaerT Q) :=
  isMulCommutative_iff.mpr fun a b => bmul_comm a b

@[simp] theorem toQ_mul (a b : BaerT Q) : (a * b).toQ = badd a.toQ b.toQ := rfl

@[simp] theorem toQ_one : (1 : BaerT Q).toQ = 1 := rfl

@[simp] theorem toQ_inv (a : BaerT Q) : (a⁻¹).toQ = a.toQ⁻¹ := rfl

/-- The canonical equivalence between `Q` and its Baer copy. -/
noncomputable def equivQ : Q ≃ BaerT Q where
  toFun q := ⟨q⟩
  invFun a := a.toQ
  left_inv q := rfl
  right_inv a := by cases a; rfl

/-- Powers in the Baer copy are the ordinary powers. -/
theorem pow_eq (x : Q) (n : ℕ) : ((equivQ x) ^ n).toQ = x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, toQ_mul, ih]
      show badd (x ^ n) x = x ^ (n + 1)
      rw [badd_eq, commutator_pow_self, sqRoot_one, one_mul, pow_succ']

end BaerT

/-! ## 4. Existence of the abelian group -/

/-- **Baer's construction** (Peterfalvi I App. IV, item 3). -/
theorem baer_group_exists (Q : Type u) [Group Q] [Finite Q] (hodd : Odd (Nat.card Q))
    (hclass : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤ Subgroup.center Q)
    (A : Type u) [Group A] [Finite A] [MulDistribMulAction A Q] :
    ∃ (G : Type u) (_ : Group G) (_ : IsMulCommutative G) (_ : MulDistribMulAction A G)
      (e : Q ≃ G),
      (∀ q : Q, orderOf (e q) = orderOf q) ∧ (∀ (a : A) (q : Q), e (a • q) = a • e q) := by
  haveI hodd' : Fact (Odd (Nat.card Q)) := ⟨hodd⟩
  haveI hclass' : Fact (⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤ Subgroup.center Q) := ⟨hclass⟩
  letI instSMul : SMul A (BaerT Q) :=
    ⟨fun a g => ⟨(MulDistribMulAction.toMulAut A Q a) g.toQ⟩⟩
  have hsmul_one : ∀ g : BaerT Q, (1 : A) • g = g := by
    intro g
    apply BaerT.ext
    show (MulDistribMulAction.toMulAut A Q 1) g.toQ = g.toQ
    rw [map_one, MulAut.one_apply]
  have hsmul_mul : ∀ (a b : A) (g : BaerT Q), (a * b) • g = a • b • g := by
    intro a b g
    apply BaerT.ext
    show (MulDistribMulAction.toMulAut A Q (a * b)) g.toQ =
      (MulDistribMulAction.toMulAut A Q a) ((MulDistribMulAction.toMulAut A Q b) g.toQ)
    rw [map_mul, MulAut.mul_apply]
  have hsmul_one' : ∀ a : A, a • (1 : BaerT Q) = 1 := by
    intro a
    apply BaerT.ext
    show (MulDistribMulAction.toMulAut A Q a) (1 : Q) = 1
    rw [map_one]
  have hsmul_mul' : ∀ (a : A) (g h : BaerT Q), a • (g * h) = a • g * a • h := by
    intro a g h
    apply BaerT.ext
    show (MulDistribMulAction.toMulAut A Q a) (BaerT.bmul g h).toQ =
      badd ((MulDistribMulAction.toMulAut A Q a) g.toQ)
        ((MulDistribMulAction.toMulAut A Q a) h.toQ)
    rw [show (BaerT.bmul g h).toQ = badd g.toQ h.toQ from rfl]
    exact map_badd (MulDistribMulAction.toMulAut A Q a) g.toQ h.toQ
  letI : MulDistribMulAction A (BaerT Q) :=
    { one_smul := hsmul_one
      mul_smul := hsmul_mul
      smul_one := hsmul_one'
      smul_mul := hsmul_mul' }
  refine ⟨BaerT Q, inferInstance, inferInstance, inferInstance, BaerT.equivQ, ?_, ?_⟩
  · intro q
    have hsplit : ∀ n : ℕ, (BaerT.equivQ q) ^ n = 1 ↔ q ^ n = 1 := by
      intro n
      constructor
      · intro hn
        have h := BaerT.pow_eq q n
        rw [hn, BaerT.toQ_one] at h
        rw [← h]
      · intro hn
        apply BaerT.ext
        rw [BaerT.pow_eq q n, hn, BaerT.toQ_one]
    refine Nat.dvd_antisymm ?_ ?_
    · rw [orderOf_dvd_iff_pow_eq_one]
      exact (hsplit (orderOf q)).mpr (pow_orderOf_eq_one q)
    · rw [orderOf_dvd_iff_pow_eq_one]
      exact (hsplit (orderOf (BaerT.equivQ q))).mp (pow_orderOf_eq_one _)
  · intro a q
    apply BaerT.ext
    show (a • q : Q) = (MulDistribMulAction.toMulAut A Q a) q
    rw [MulDistribMulAction.toMulAut_apply, MulDistribMulAction.toMulEquiv_apply]

end Work.ThreePoints.ThmC

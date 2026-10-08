import Mathlib
import Submission.Work.LocalPrelim.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Classical Pointwise

noncomputable section

namespace Work.LocalPrelim

/-! ### Restricting an automorphism to an invariant subgroup -/

/-- If the automorphism `A` of `X` maps the subgroup `Y` onto itself, then it restricts to an
automorphism of `Y`. -/
def restrictMulAut {X : Type*} [Group X] (A : MulAut X) (Y : Subgroup X)
    (h : Subgroup.map A.toMonoidHom Y = Y) : MulAut ↥Y where
  toFun y := ⟨A y, (mem_map_iff_of_map_eq h y).2 y.2⟩
  invFun y := ⟨A.symm y, (mem_map_iff_of_map_eq (map_symm_eq_of_map_eq h) y).2 y.2⟩
  left_inv y := by ext; simp
  right_inv y := by ext; simp
  map_mul' y z := by ext; simp

@[simp] lemma restrictMulAut_toMonoidHom_apply_coe {X : Type*} [Group X] (A : MulAut X)
    (Y : Subgroup X) (h : Subgroup.map A.toMonoidHom Y = Y) (y : ↥Y) :
    (((restrictMulAut A Y h).toMonoidHom) y : X) = A y := rfl

@[simp] lemma restrictMulAut_apply_coe {X : Type*} [Group X] (A : MulAut X) (Y : Subgroup X)
    (h : Subgroup.map A.toMonoidHom Y = Y) (y : ↥Y) :
    ((restrictMulAut A Y h y : ↥Y) : X) = A y := rfl

@[simp] lemma restrictMulAut_symm_apply_coe {X : Type*} [Group X] (A : MulAut X) (Y : Subgroup X)
    (h : Subgroup.map A.toMonoidHom Y = Y) (y : ↥Y) :
    ((restrictMulAut A Y h).symm y : X) = A.symm y := rfl

/-- The restriction of `A` to `Y` preserves any `A`-invariant subgroup `B`, viewed inside `Y`. -/
lemma map_restrictMulAut_subgroupOf {X : Type*} [Group X] (A : MulAut X) {B Y : Subgroup X}
    (hB : Subgroup.map A.toMonoidHom B = B) (hY : Subgroup.map A.toMonoidHom Y = Y) :
    Subgroup.map (restrictMulAut A Y hY).toMonoidHom (B.subgroupOf Y) = B.subgroupOf Y := by
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz
    rw [← hwz, Subgroup.mem_subgroupOf, restrictMulAut_toMonoidHom_apply_coe]
    exact (mem_map_iff_of_map_eq hB w).2 (Subgroup.mem_subgroupOf.mp hw)
  · intro hz
    refine Subgroup.mem_map.mpr ⟨(restrictMulAut A Y hY).symm z, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf, restrictMulAut_symm_apply_coe]
      exact (mem_map_iff_of_map_eq (map_symm_eq_of_map_eq hB) z).2 (Subgroup.mem_subgroupOf.mp hz)
    · exact (restrictMulAut A Y hY).apply_symm_apply z

lemma restrictMulAut_pow_apply_coe {X : Type*} [Group X] (A : MulAut X) (Y : Subgroup X)
    (h : Subgroup.map A.toMonoidHom Y = Y) (r : ℕ) (y : ↥Y) :
    (((restrictMulAut A Y h) ^ r) y : X) = (A ^ r) y := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', MulAut.mul_apply, restrictMulAut_apply_coe, ih, pow_succ', MulAut.mul_apply]

/-- The restriction of a chain-stabilizing automorphism `A` of `X` to the first subgroup `C 1` of
the chain stabilizes the tail chain `C 1 ⊇ C 2 ⊇ ⋯` (viewed inside `C 1`).  This is the induction
step of FT 8.1. -/
lemma restrictMulAut_mem_stabilityGroupAut {X : Type*} [Group X] {n : ℕ}
    (C : Fin (n + 2) → Subgroup X) {A : MulAut X} (hA : A ∈ stabilityGroupAut C) :
    restrictMulAut A (C 1) (hA.1 1) ∈
      stabilityGroupAut (fun j : Fin (n + 1) => (C j.succ).subgroupOf (C 1)) := by
  constructor
  · intro j
    exact map_restrictMulAut_subgroupOf A (hA.1 j.succ) (hA.1 1)
  · intro i y hy
    have hy' : ((y : ↥(C 1)) : X) ∈ C ((i.castSucc).succ) := Subgroup.mem_subgroupOf.mp hy
    rw [Fin.succ_castSucc] at hy'
    have h := hA.2 i.succ (y : X) hy'
    rw [Subgroup.mem_subgroupOf]
    simpa using h

/-! ### Two general group-theoretic lemmas -/

/-- If `A` sends `x` to `a * x` and fixes `a`, then `A ^ r` sends `x` to `a ^ r * x`. -/
lemma pow_apply_eq_of_fixes {X : Type*} [Group X] {A : MulAut X} {a x : X}
    (hax : A x = a * x) (hfix : A a = a) (r : ℕ) : (A ^ r) x = a ^ r * x := by
  have hpow : ∀ n : ℕ, A (a ^ n) = a ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, map_mul, ih, hfix, ← pow_succ]
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', MulAut.mul_apply, ih, map_mul, hpow, hax]
    group

/-- A finite group all of whose elements have `π`-order is a `π`-group (Cauchy's theorem). -/
theorem isPiNat_card_of_orderOf {H : Type*} [Group H] [Finite H] {π : ℕ → Prop}
    (h : ∀ x : H, IsPiNat π (orderOf x)) : IsPiNat π (Nat.card H) := by
  intro p hp hpdvd
  obtain ⟨x, hx⟩ := @exists_prime_orderOf_dvd_card' H _ _ p ⟨hp⟩ hpdvd
  exact h x p hp (by rw [hx])

/-- If `A` maps `x ↦ a * x` with `a ∈ B` for all `x`, and `A` fixes `B` pointwise, then the order
of `A` divides `|B|`.  This is the estimate `B ^ {|X_1|} = 1` in the proof of FT 8.1. -/
theorem orderOf_dvd_card_of_fixes {X : Type*} [Group X] [Finite X] {A : MulAut X} {B : Subgroup X}
    (hmem : ∀ x : X, A x * x⁻¹ ∈ B) (hcent : ∀ x ∈ B, A x = x) :
    orderOf A ∣ Nat.card ↥B := by
  rw [orderOf_dvd_iff_pow_eq_one]
  ext x
  have hax : A x = (A x * x⁻¹) * x := by group
  have hfix : A (A x * x⁻¹) = A x * x⁻¹ := hcent _ (hmem x)
  rw [pow_apply_eq_of_fixes hax hfix]
  have h2 : (A x * x⁻¹) ^ Nat.card ↥B = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard B (hmem x))
  rw [h2, one_mul, MulAut.one_apply]

/-! ### FT 8.1 -/

/-- FT 8.1, in the elementwise form: every element of the stability group of a chain
`X = C 0 ⊇ ⋯ ⊇ C n = 1` of a `π`-group `X` has `π`-order. -/
theorem ft8_1_aux (π : ℕ → Prop) : ∀ n : ℕ, ∀ (X : Type*) [Group X] [Finite X]
    (C : Fin (n + 1) → Subgroup X), (∀ i j : Fin (n + 1), i ≤ j → C j ≤ C i) →
    C 0 = ⊤ → C (Fin.last n) = ⊥ → IsPiNat π (Nat.card X) →
    ∀ x : MulAut X, x ∈ stabilityGroupAut C → IsPiNat π (orderOf x) := by
  intro n
  induction n with
  | zero =>
    intro X _ _ C _ hC0 hCn _ x _
    have htopbot : (⊤ : Subgroup X) = ⊥ := by
      have h : C (0 : Fin 1) = ⊥ := by simpa using hCn
      rw [← hC0, h]
    have hx1 : x = 1 := by
      ext y
      have hy : y = 1 := by
        have hmem : y ∈ (⊥ : Subgroup X) := by rw [← htopbot]; exact Subgroup.mem_top y
        exact Subgroup.mem_bot.mp hmem
      simp [hy]
    rw [hx1, orderOf_one]
    exact Work.Hall.IsPiNat.one
  | succ k ih =>
    intro X _ _ C hmono hC0 hCn hπ A hA
    have hπY : IsPiNat π (Nat.card ↥(C 1)) :=
      Work.Hall.IsPiNat.of_dvd (Subgroup.card_subgroup_dvd_card (C 1)) hπ
    have hmonoD : ∀ i j : Fin (k + 1), i ≤ j →
        (fun j : Fin (k + 1) => (C j.succ).subgroupOf (C 1)) j ≤
          (fun j : Fin (k + 1) => (C j.succ).subgroupOf (C 1)) i := by
      intro i j hij
      exact Subgroup.subgroupOf_mono (C 1) (hmono i.succ j.succ (Fin.succ_le_succ_iff.mpr hij))
    have hD0 : (fun j : Fin (k + 1) => (C j.succ).subgroupOf (C 1)) 0 = ⊤ := by
      show (C ((0 : Fin (k + 1)).succ)).subgroupOf (C 1) = ⊤
      rw [Fin.succ_zero_eq_one, Subgroup.subgroupOf_self]
    have hDn : (fun j : Fin (k + 1) => (C j.succ).subgroupOf (C 1)) (Fin.last k) = ⊥ := by
      show (C ((Fin.last k).succ)).subgroupOf (C 1) = ⊥
      rw [Fin.succ_last, hCn, Subgroup.bot_subgroupOf]
    have hmπ : IsPiNat π (orderOf (restrictMulAut A (C 1) (hA.1 1))) :=
      ih (↥(C 1)) (fun j : Fin (k + 1) => (C j.succ).subgroupOf (C 1)) hmonoD hD0 hDn hπY
        (restrictMulAut A (C 1) (hA.1 1)) (restrictMulAut_mem_stabilityGroupAut C hA)
    have hρm : restrictMulAut A (C 1) (hA.1 1) ^
        orderOf (restrictMulAut A (C 1) (hA.1 1)) = 1 := pow_orderOf_eq_one _
    have hcent : ∀ y ∈ C 1, (A ^ orderOf (restrictMulAut A (C 1) (hA.1 1))) y = y := by
      intro y hy
      have h1 : ((restrictMulAut A (C 1) (hA.1 1) ^
          orderOf (restrictMulAut A (C 1) (hA.1 1))) ⟨y, hy⟩ : X) = y := by
        rw [hρm]; rfl
      rw [← restrictMulAut_pow_apply_coe A (C 1) (hA.1 1) _ ⟨y, hy⟩]
      exact h1
    have hmemA : ∀ x : X, (A ^ orderOf (restrictMulAut A (C 1) (hA.1 1))) x * x⁻¹ ∈ C 1 := by
      intro x
      have hp : A ^ orderOf (restrictMulAut A (C 1) (hA.1 1)) ∈ stabilityGroupAut C :=
        Subgroup.pow_mem (stabilityGroupAut C) hA _
      have hx : x ∈ C ((0 : Fin (k + 1)).castSucc) := by
        rw [show ((0 : Fin (k + 1)).castSucc : Fin (k + 1 + 1)) = 0 from rfl, hC0]
        exact Subgroup.mem_top x
      have h := hp.2 0 x hx
      simpa [Fin.succ_zero_eq_one] using h
    have hdvd : orderOf (A ^ orderOf (restrictMulAut A (C 1) (hA.1 1))) ∣ Nat.card ↥(C 1) :=
      orderOf_dvd_card_of_fixes hmemA hcent
    have hAma : (A ^ orderOf (restrictMulAut A (C 1) (hA.1 1))) ^ Nat.card ↥(C 1) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp hdvd
    have hApow : A ^ (orderOf (restrictMulAut A (C 1) (hA.1 1)) * Nat.card ↥(C 1)) = 1 := by
      rw [pow_mul]; exact hAma
    have hfinal : orderOf A ∣ orderOf (restrictMulAut A (C 1) (hA.1 1)) * Nat.card ↥(C 1) :=
      orderOf_dvd_iff_pow_eq_one.mpr hApow
    exact Work.Hall.IsPiNat.of_dvd hfinal (Work.Hall.IsPiNat.mul hmπ hπY)

theorem ft8_1 {X : Type*} [Group X] [Finite X] (π : ℕ → Prop) {n : ℕ}
    (C : Fin (n + 1) → Subgroup X) (hmono : ∀ i j : Fin (n + 1), i ≤ j → C j ≤ C i)
    (hC0 : C 0 = ⊤) (hCn : C (Fin.last n) = ⊥) (hπ : IsPiNat π (Nat.card X)) :
    IsPiNat π (Nat.card (stabilityGroupAut C)) := by
  refine isPiNat_card_of_orderOf (fun x => ?_)
  rw [← Subgroup.orderOf_coe x]
  exact ft8_1_aux π n X C hmono hC0 hCn hπ (x : MulAut X) x.2

end Work.LocalPrelim

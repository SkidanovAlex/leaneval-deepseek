import Mathlib
import Submission.Work.Higman.MSA.l8_local
import Submission.Work.Higman.commutator_powSub_A_C
import Submission.Work.Higman.suzuki_unipotence

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.Higman.MSA.L8

variable {P : Type} [Group P] [Finite P]

/-- `⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆`. -/
theorem commutator_mul_left_eq (x y z : P) :
    ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by
  rw [commutatorElement_def]; group

/-- `⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹)`. -/
theorem commutator_mul_right_eq (x y z : P) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
  rw [commutatorElement_def]; group

/-- `⁅A, C⁆ = A ^ 2`. -/
theorem commutator_A_C_eq {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : D h A C) : ⁅A, C⁆ = powSub A 2 := by
  have h0 := commutator_powSub_A_C h S.hA S.hCn S.hC2 S.hCd 0
  rw [pow_zero, powSub_one_eq] at h0
  simpa using h0

/-- The `2 ^ (e-1)`-st power kills `A ^ 2`. -/
theorem pow_two_pow_sub_one_eq_one_of_mem_powSub_two {h : IsSuzuki2Grp P} {A C : Subgroup P}
    [hAn : A.Normal] (S : D h A C) {δ : P} (hδ : δ ∈ powSub A 2) :
    δ ^ 2 ^ (S.e - 1) = 1 := by
  have he : 1 ≤ S.e := S.he
  obtain ⟨a, ha, rfl⟩ := (mem_powSub_iff S.hA.abelian).mp hδ
  rw [← pow_mul,
    show (2 : ℕ) * 2 ^ (S.e - 1) = 2 ^ S.e from by rw [← pow_succ']; congr 1; omega]
  exact S.he1 a ha

/-- Conjugates of elements of `A ^ 2` lie in `A ^ 2`. -/
theorem conj_mem_powSub_two {A : Subgroup P} [hAn : A.Normal]
    (g : P) {δ : P} (hδ : δ ∈ powSub A 2) : g * δ * g⁻¹ ∈ powSub A 2 := by
  have hAconj : A.map (MulAut.conj g).toMonoidHom = A :=
    Subgroup.normal_iff_map_conj_eq.mp hAn g
  have hmap := map_powSub (MulAut.conj g) hAconj 2
  have hmem : (MulAut.conj g) δ ∈ (powSub A 2).map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hδ
  rw [hmap] at hmem
  simpa [MulAut.conj_apply] using hmem

/-- **Well-definedness step.**  Changing `x` by an element of `A` and `y` by an element of `A`
changes `⁅x, y⁆` only by a factor in `A ^ 2`. -/
theorem comm_step {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal] (S : D h A C)
    {x : P} (hx : x ∈ C) {a : P} (ha : a ∈ A) {y : P} (hy : y ∈ C) {b : P} (hb : b ∈ A) :
    ∃ δ ∈ powSub A 2, ⁅x * a, y * b⁆ = δ * ⁅x, y⁆ := by
  have hAC : ⁅A, C⁆ = powSub A 2 := commutator_A_C_eq S
  have h1 : ⁅a, y * b⁆ ∈ powSub A 2 := by
    have hmem : ⁅a, y * b⁆ ∈ ⁅A, C⁆ :=
      Subgroup.commutator_mem_commutator ha (C.mul_mem hy (S.hAC hb))
    rwa [hAC] at hmem
  have h2 : ⁅x, b⁆ ∈ powSub A 2 := by
    have hmem : ⁅x, b⁆ ∈ ⁅C, A⁆ :=
      Subgroup.commutator_mem_commutator (H₁ := C) (H₂ := A) hx hb
    rw [Subgroup.commutator_comm] at hmem
    rwa [hAC] at hmem
  have hc1 : x * ⁅a, y * b⁆ * x⁻¹ ∈ powSub A 2 := conj_mem_powSub_two x h1
  have hc2 : y * ⁅x, b⁆ * y⁻¹ ∈ powSub A 2 := conj_mem_powSub_two y h2
  refine ⟨(x * ⁅a, y * b⁆ * x⁻¹) * (y * ⁅x, b⁆ * y⁻¹),
    (powSub A 2).mul_mem hc1 hc2, ?_⟩
  have hxyA : ⁅x, y⁆ ∈ A := by
    have hmem : ⁅x, y⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hx hy
    rwa [S.hCd] at hmem
  have hcomm : ⁅x, y⁆ * (y * ⁅x, b⁆ * y⁻¹) = (y * ⁅x, b⁆ * y⁻¹) * ⁅x, y⁆ :=
    S.hA.abelian ⁅x, y⁆ hxyA _ (powSub_le (show 0 < 2 by norm_num) hc2)
  calc ⁅x * a, y * b⁆
      = x * ⁅a, y * b⁆ * x⁻¹ * ⁅x, y * b⁆ := commutator_mul_left_eq x a (y * b)
    _ = x * ⁅a, y * b⁆ * x⁻¹ * (⁅x, y⁆ * (y * ⁅x, b⁆ * y⁻¹)) := by
          rw [commutator_mul_right_eq x y b]
    _ = (x * ⁅a, y * b⁆ * x⁻¹) * (y * ⁅x, b⁆ * y⁻¹) * ⁅x, y⁆ := by
          rw [hcomm]; group

/-- **Independence of representatives for `BV`.** -/
theorem BV_congr {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal] (S : D h A C)
    {r s u v : P} (hr : r ∈ C) (hs : s ∈ C) (hu : u ∈ C) (hv : v ∈ C)
    (hru : r⁻¹ * u ∈ A) (hsv : s⁻¹ * v ∈ A) :
    (⁅r⁻¹, s⁆) ^ 2 ^ (S.e - 1) = (⁅u⁻¹, v⁆) ^ 2 ^ (S.e - 1) := by
  have hconj : r * (r⁻¹ * u)⁻¹ * r⁻¹ ∈ A := hAn.conj_mem (r⁻¹ * u)⁻¹ (A.inv_mem hru) r
  obtain ⟨δ, hδ, hδeq⟩ :=
    comm_step S (x := r⁻¹) (C.inv_mem hr) (a := r * (r⁻¹ * u)⁻¹ * r⁻¹) hconj
      (y := s) hs (b := s⁻¹ * v) hsv
  rw [show s * (s⁻¹ * v) = v from by group,
    show r⁻¹ * (r * (r⁻¹ * u)⁻¹ * r⁻¹) = u⁻¹ from by group] at hδeq
  have hrsA : ⁅r⁻¹, s⁆ ∈ A := by
    have hmem : ⁅r⁻¹, s⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator (C.inv_mem hr) hs
    rwa [S.hCd] at hmem
  have hcomm : δ * ⁅r⁻¹, s⁆ = ⁅r⁻¹, s⁆ * δ :=
    S.hA.abelian δ (powSub_le (show 0 < 2 by norm_num) hδ) ⁅r⁻¹, s⁆ hrsA
  have hXδ : Commute ⁅r⁻¹, s⁆ δ := hcomm.symm
  rw [hδeq, hcomm, Commute.mul_pow hXδ (2 ^ (S.e - 1)),
    pow_two_pow_sub_one_eq_one_of_mem_powSub_two S hδ, mul_one]

/-- `BV` on arbitrary representatives. -/
theorem BV_rep {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal] (S : D h A C)
    (x y : ↥C ⧸ (A.subgroupOf C)) (u v : ↥C)
    (hu : QuotientGroup.mk u = x) (hv : QuotientGroup.mk v = y) :
    ((BV S x y : ↥(omega1 P)) : P) = (⁅((u : P))⁻¹, ((v : P))⁆) ^ 2 ^ (S.e - 1) := by
  rw [BV_apply]
  exact BV_congr S (repC (A := A) (C := C) x).2 (repC (A := A) (C := C) y).2 u.2 v.2
    (repC_mul_inv_mem (A := A) (C := C) hu) (repC_mul_inv_mem (A := A) (C := C) hv)


/-- `a * b * a⁻¹ = b` when `a` and `b` commute. -/
theorem conj_eq_self_of_comm {a b : P} (h : a * b = b * a) : a * b * a⁻¹ = b := by
  rw [h]; group

/-- `y * (y * x)⁻¹ = x⁻¹` when `y` commutes with `x⁻¹`. -/
theorem mul_mul_inv_eq_inv_of_comm {x y : P} (h : y * x⁻¹ = x⁻¹ * y) :
    y * (y * x)⁻¹ = x⁻¹ := by
  rw [mul_inv_rev, ← mul_assoc, h]; group

/-- If `α, β ∈ A` and `α ≡ β` mod `A ^ 2`, then the `2 ^ (e-1)`-st powers agree. -/
theorem pow_eq_of_mul_inv_mem_powSub_two {h : IsSuzuki2Grp P} {A C : Subgroup P}
    [hAn : A.Normal] (S : D h A C) {α β : P} (hα : α ∈ A) (hβ : β ∈ A)
    (h : α * β⁻¹ ∈ powSub A 2) :
    α ^ 2 ^ (S.e - 1) = β ^ 2 ^ (S.e - 1) := by
  have hδA : α * β⁻¹ ∈ A := powSub_le (show 0 < 2 by norm_num) h
  have heq : α = β * (α * β⁻¹) := by
    have hc : β * α = α * β := S.hA.abelian β hβ α hα
    rw [← mul_assoc, hc, mul_assoc, mul_inv_cancel, mul_one]
  have hcβδ : Commute β (α * β⁻¹) := S.hA.abelian β hβ (α * β⁻¹) hδA
  rw [heq, Commute.mul_pow hcβδ (2 ^ (S.e - 1)),
    pow_two_pow_sub_one_eq_one_of_mem_powSub_two S h, mul_one]

/-- `⁅u * v, w⁆ ≡ ⁅u,w⁆ · ⁅v,w⁆` modulo `A ^ 2` (for `u, v, w ∈ C`). -/
theorem comm_mul_left_mod {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : D h A C) {u v w : P} (hu : u ∈ C) (hv : v ∈ C) (hw : w ∈ C) :
    ⁅u * v, w⁆ * (⁅u, w⁆ * ⁅v, w⁆)⁻¹ ∈ powSub A 2 := by
  have huw : ⁅u, w⁆ ∈ A := by
    have hmem : ⁅u, w⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hu hw
    rwa [S.hCd] at hmem
  have hvw : ⁅v, w⁆ ∈ A := by
    have hmem : ⁅v, w⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hv hw
    rwa [S.hCd] at hmem
  have hδ : ⁅⁅v, w⁆⁻¹, u⁆ ∈ powSub A 2 := by
    have hmem : ⁅⁅v, w⁆⁻¹, u⁆ ∈ ⁅A, C⁆ :=
      Subgroup.commutator_mem_commutator (A.inv_mem hvw) hu
    rwa [commutator_A_C_eq S] at hmem
  have hδA : ⁅⁅v, w⁆⁻¹, u⁆ ∈ A := powSub_le (show 0 < 2 by norm_num) hδ
  have hsplit : ⁅u * v, w⁆ = (⁅v, w⁆ * ⁅⁅v, w⁆⁻¹, u⁆) * ⁅u, w⁆ := by
    rw [commutator_mul_left_eq u v w]
    congr 1
    rw [commutatorElement_def]; group
  rw [hsplit]
  have hYX : ⁅u, w⁆ * ⁅v, w⁆⁻¹ = ⁅v, w⁆⁻¹ * ⁅u, w⁆ :=
    S.hA.abelian ⁅u, w⁆ huw ⁅v, w⁆⁻¹ (A.inv_mem hvw)
  have hδX : ⁅v, w⁆ * ⁅⁅v, w⁆⁻¹, u⁆ = ⁅⁅v, w⁆⁻¹, u⁆ * ⁅v, w⁆ :=
    S.hA.abelian ⁅v, w⁆ hvw _ hδA
  have key : (⁅v, w⁆ * ⁅⁅v, w⁆⁻¹, u⁆) * ⁅u, w⁆ * (⁅u, w⁆ * ⁅v, w⁆)⁻¹ = ⁅⁅v, w⁆⁻¹, u⁆ := by
    calc (⁅v, w⁆ * ⁅⁅v, w⁆⁻¹, u⁆) * ⁅u, w⁆ * (⁅u, w⁆ * ⁅v, w⁆)⁻¹
        = (⁅v, w⁆ * ⁅⁅v, w⁆⁻¹, u⁆) * (⁅u, w⁆ * (⁅u, w⁆ * ⁅v, w⁆)⁻¹) := by group
      _ = (⁅v, w⁆ * ⁅⁅v, w⁆⁻¹, u⁆) * ⁅v, w⁆⁻¹ := by
            rw [mul_mul_inv_eq_inv_of_comm (x := ⁅v, w⁆) hYX]
      _ = ⁅v, w⁆ * ⁅⁅v, w⁆⁻¹, u⁆ * ⁅v, w⁆⁻¹ := by group
      _ = ⁅⁅v, w⁆⁻¹, u⁆ := conj_eq_self_of_comm hδX
  rw [key]; exact hδ

/-- `⁅u, v * w⁆ ≡ ⁅u,v⁆ · ⁅u,w⁆` modulo `A ^ 2` (for `u, v, w ∈ C`). -/
theorem comm_mul_right_mod {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : D h A C) {u v w : P} (hu : u ∈ C) (hv : v ∈ C) (hw : w ∈ C) :
    ⁅u, v * w⁆ * (⁅u, v⁆ * ⁅u, w⁆)⁻¹ ∈ powSub A 2 := by
  have huv : ⁅u, v⁆ ∈ A := by
    have hmem : ⁅u, v⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hu hv
    rwa [S.hCd] at hmem
  have huw : ⁅u, w⁆ ∈ A := by
    have hmem : ⁅u, w⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hu hw
    rwa [S.hCd] at hmem
  have hδ : ⁅⁅u, w⁆⁻¹, v⁆ ∈ powSub A 2 := by
    have hmem : ⁅⁅u, w⁆⁻¹, v⁆ ∈ ⁅A, C⁆ :=
      Subgroup.commutator_mem_commutator (A.inv_mem huw) hv
    rwa [commutator_A_C_eq S] at hmem
  have hδA : ⁅⁅u, w⁆⁻¹, v⁆ ∈ A := powSub_le (show 0 < 2 by norm_num) hδ
  have hsplit : ⁅u, v * w⁆ = ⁅u, v⁆ * (⁅u, w⁆ * ⁅⁅u, w⁆⁻¹, v⁆) := by
    rw [commutator_mul_right_eq u v w]
    congr 1
    rw [commutatorElement_def]; group
  rw [hsplit]
  have hδXY : (⁅u, v⁆ * ⁅u, w⁆) * ⁅⁅u, w⁆⁻¹, v⁆
      = ⁅⁅u, w⁆⁻¹, v⁆ * (⁅u, v⁆ * ⁅u, w⁆) :=
    S.hA.abelian _ (A.mul_mem huv huw) _ hδA
  have key : ⁅u, v⁆ * (⁅u, w⁆ * ⁅⁅u, w⁆⁻¹, v⁆) * (⁅u, v⁆ * ⁅u, w⁆)⁻¹ = ⁅⁅u, w⁆⁻¹, v⁆ := by
    calc ⁅u, v⁆ * (⁅u, w⁆ * ⁅⁅u, w⁆⁻¹, v⁆) * (⁅u, v⁆ * ⁅u, w⁆)⁻¹
        = (⁅u, v⁆ * ⁅u, w⁆) * ⁅⁅u, w⁆⁻¹, v⁆ * (⁅u, v⁆ * ⁅u, w⁆)⁻¹ := by group
      _ = ⁅⁅u, w⁆⁻¹, v⁆ := conj_eq_self_of_comm hδXY
  rw [key]; exact hδ

/-- `ξ` acts on the quotient through `xiSubAut`. -/
theorem xiQuot_mk {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) (u : ↥C) :
    xiQuot h hAinv hCinv (QuotientGroup.mk u)
      = QuotientGroup.mk (xiSubAut h hCinv u) :=
  QuotientGroup.congr_mk (A.subgroupOf C) (A.subgroupOf C) (xiSubAut h hCinv) _ u

/-- `BV` is additive in its first argument. -/
theorem BV_mul_left {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal] (S : D h A C)
    (x y z : ↥C ⧸ (A.subgroupOf C)) :
    BV S (x * y) z = BV S x z * BV S y z := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective z
  rw [← QuotientGroup.mk_mul]
  apply Subtype.ext
  rw [Subgroup.coe_mul, BV_rep S _ _ (u * v) w rfl rfl, BV_rep S _ _ u w rfl rfl,
    BV_rep S _ _ v w rfl rfl]
  simp only [Subgroup.coe_mul, mul_inv_rev]
  have hXu : ⁅(v : P)⁻¹ * (u : P)⁻¹, (w : P)⁆ ∈ A := by
    have hmem := Subgroup.commutator_mem_commutator
      (C.mul_mem (C.inv_mem v.2) (C.inv_mem u.2)) w.2
    rw [S.hCd] at hmem
    simpa using hmem
  have hYu : ⁅(u : P)⁻¹, (w : P)⁆ ∈ A := by
    have hmem := Subgroup.commutator_mem_commutator (C.inv_mem u.2) w.2
    rw [S.hCd] at hmem
    simpa using hmem
  have hYv : ⁅(v : P)⁻¹, (w : P)⁆ ∈ A := by
    have hmem := Subgroup.commutator_mem_commutator (C.inv_mem v.2) w.2
    rw [S.hCd] at hmem
    simpa using hmem
  have hβA : ⁅(v : P)⁻¹, (w : P)⁆ * ⁅(u : P)⁻¹, (w : P)⁆ ∈ A := A.mul_mem hYv hYu
  have hmod : ⁅(v : P)⁻¹ * (u : P)⁻¹, (w : P)⁆
      * (⁅(v : P)⁻¹, (w : P)⁆ * ⁅(u : P)⁻¹, (w : P)⁆)⁻¹ ∈ powSub A 2 :=
    comm_mul_left_mod S (C.inv_mem v.2) (C.inv_mem u.2) w.2
  have hpow := pow_eq_of_mul_inv_mem_powSub_two S hXu hβA hmod
  rw [hpow, Commute.mul_pow (S.hA.abelian ⁅(v : P)⁻¹, (w : P)⁆ hYv ⁅(u : P)⁻¹, (w : P)⁆ hYu)
    (2 ^ (S.e - 1)),
    h.omega1_comm
      (mem_omega1_pow_two_pow_sub_one h S.hA S.he1 S.he hYv)
      (mem_omega1_pow_two_pow_sub_one h S.hA S.he1 S.he hYu)]

/-- `BV` is additive in its second argument. -/
theorem BV_mul_right {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal] (S : D h A C)
    (x y z : ↥C ⧸ (A.subgroupOf C)) :
    BV S x (y * z) = BV S x y * BV S x z := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective z
  rw [← QuotientGroup.mk_mul]
  apply Subtype.ext
  rw [Subgroup.coe_mul, BV_rep S _ _ u (v * w) rfl rfl, BV_rep S _ _ u v rfl rfl,
    BV_rep S _ _ u w rfl rfl]
  simp only [Subgroup.coe_mul]
  have hXu : ⁅(u : P)⁻¹, (v : P) * (w : P)⁆ ∈ A := by
    have hmem := Subgroup.commutator_mem_commutator (C.inv_mem u.2) (C.mul_mem v.2 w.2)
    rw [S.hCd] at hmem
    simpa using hmem
  have hYv : ⁅(u : P)⁻¹, (v : P)⁆ ∈ A := by
    have hmem := Subgroup.commutator_mem_commutator (C.inv_mem u.2) v.2
    rw [S.hCd] at hmem
    simpa using hmem
  have hYw : ⁅(u : P)⁻¹, (w : P)⁆ ∈ A := by
    have hmem := Subgroup.commutator_mem_commutator (C.inv_mem u.2) w.2
    rw [S.hCd] at hmem
    simpa using hmem
  have hβA : ⁅(u : P)⁻¹, (v : P)⁆ * ⁅(u : P)⁻¹, (w : P)⁆ ∈ A := A.mul_mem hYv hYw
  have hmod : ⁅(u : P)⁻¹, (v : P) * (w : P)⁆
      * (⁅(u : P)⁻¹, (v : P)⁆ * ⁅(u : P)⁻¹, (w : P)⁆)⁻¹ ∈ powSub A 2 :=
    comm_mul_right_mod S (C.inv_mem u.2) v.2 w.2
  have hpow := pow_eq_of_mul_inv_mem_powSub_two S hXu hβA hmod
  rw [hpow, Commute.mul_pow (S.hA.abelian ⁅(u : P)⁻¹, (v : P)⁆ hYv ⁅(u : P)⁻¹, (w : P)⁆ hYw)
    (2 ^ (S.e - 1)),
    (h.omega1_comm
      (mem_omega1_pow_two_pow_sub_one h S.hA S.he1 S.he hYw)
      (mem_omega1_pow_two_pow_sub_one h S.hA S.he1 S.he hYv)).symm]

/-- `BV` is alternating. -/
theorem BV_diag {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal] (S : D h A C)
    (x : ↥C ⧸ (A.subgroupOf C)) : BV S x x = 1 := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  apply Subtype.ext
  rw [BV_rep S _ _ u u rfl rfl]
  have h : ⁅(u : P)⁻¹, (u : P)⁆ = 1 := by rw [commutatorElement_def]; group
  rw [h, one_pow]
  rfl

/-- `BV` is `ξ`-equivariant. -/
theorem BV_xi {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal] (S : D h A C)
    (x y : ↥C ⧸ (A.subgroupOf C)) :
    xiZ h (BV S x y)
      = BV S (xiQuot h S.hA.map_eq S.hCinv x) (xiQuot h S.hA.map_eq S.hCinv y) := by
  apply Subtype.ext
  rw [xiZ_apply, BV_apply,
    BV_rep S _ _
      (xiSubAut h S.hCinv (repC (A := A) (C := C) x))
      (xiSubAut h S.hCinv (repC (A := A) (C := C) y))
      (by rw [← xiQuot_mk, repC_spec]) (by rw [← xiQuot_mk, repC_spec]),
    map_pow]
  congr 1
  rw [map_commutatorElement (h.xi : MulAut P), map_inv]
  simp only [xiSubAut_apply]

/-- `BV` is not identically trivial. -/
theorem BV_ne {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal] (S : D h A C) :
    ∃ x y : ↥C ⧸ (A.subgroupOf C), BV S x y ≠ 1 := by
  by_contra hcon
  push_neg at hcon
  have Rder : ∀ w ∈ C, ∀ z ∈ C, ⁅w⁻¹, z⁆ ∈ powSub A 2 := by
    intro w hw z hz
    have hmem : ⁅w⁻¹, z⁆ ∈ A := by
      have hmem := Subgroup.commutator_mem_commutator (C.inv_mem hw) hz
      rwa [S.hCd] at hmem
    have hk : ⁅w⁻¹, z⁆ ^ 2 ^ (S.e - 1) = 1 := by
      have hc := hcon (QuotientGroup.mk ⟨w, hw⟩) (QuotientGroup.mk ⟨z, hz⟩)
      have h2 := congrArg (fun t : ↥(omega1 P) => (t : P)) hc
      rw [BV_rep S _ _ ⟨w, hw⟩ ⟨z, hz⟩ rfl rfl] at h2
      simpa using h2
    exact (S.hkey ⁅w⁻¹, z⁆ hmem).mpr hk
  have hle : ⁅C, C⁆ ≤ powSub A 2 := by
    rw [Subgroup.commutator_le]
    intro u hu v hv
    have := Rder u⁻¹ (C.inv_mem hu) v hv
    simpa using this
  have hA2 : A = powSub A 2 := by
    refine le_antisymm ?_ (powSub_le (show 0 < 2 by norm_num))
    conv_lhs => rw [← S.hCd]
    exact hle
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (h.isPGroup.to_subgroup A)
  have hbot : powSub A (2 ^ n) = ⊥ := by
    refine powSub_eq_bot_of_exp S.hA.abelian le_rfl fun x hx => ?_
    haveI : Fintype ↥A := Fintype.ofFinite _
    have hxA : orderOf (⟨x, hx⟩ : ↥A) ∣ 2 ^ n := by
      have h := orderOf_dvd_card (x := (⟨x, hx⟩ : ↥A))
      rwa [← Nat.card_eq_fintype_card, hn] at h
    have h1 : (⟨x, hx⟩ : ↥A) ^ 2 ^ n = 1 := orderOf_dvd_iff_pow_eq_one.mp hxA
    simpa [Subgroup.coe_pow] using congrArg (fun t : ↥A => (t : P)) h1
  have hiter : ∀ k, A = powSub A (2 ^ k) := by
    intro k
    induction k with
    | zero => rw [pow_zero, powSub_one_eq]
    | succ k ih => rw [pow_succ, ← powSub_powSub S.hA.abelian, ← ih, ← hA2]
  exact S.hAne (by rw [hiter n, hbot])

/-- **Higman's Lemma 8, the commutator pairing.**  Collected properties of
`BV : C/A × C/A → Ω₁(P)`. -/
theorem l8_BV {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal] (S : D h A C) :
    (∀ (x y : ↥C ⧸ (A.subgroupOf C)) (u v : ↥C),
      QuotientGroup.mk u = x → QuotientGroup.mk v = y →
      ((BV S x y : ↥(omega1 P)) : P)
        = ((u : P)⁻¹ * (v : P) * (u : P) * (v : P)⁻¹) ^ 2 ^ (S.e - 1)) ∧
    (∀ x y z : ↥C ⧸ (A.subgroupOf C), BV S (x * y) z = BV S x z * BV S y z) ∧
    (∀ x y z : ↥C ⧸ (A.subgroupOf C), BV S x (y * z) = BV S x y * BV S x z) ∧
    (∀ x : ↥C ⧸ (A.subgroupOf C), BV S x x = 1) ∧
    (∀ x y : ↥C ⧸ (A.subgroupOf C),
      xiZ h (BV S x y) = BV S (xiQuot h S.hA.map_eq S.hCinv x)
        (xiQuot h S.hA.map_eq S.hCinv y)) ∧
    (∃ x y : ↥C ⧸ (A.subgroupOf C), BV S x y ≠ 1) := by
  refine ⟨?_, BV_mul_left S, BV_mul_right S, BV_diag S, BV_xi S, BV_ne S⟩
  intro x y u v hu hv
  rw [BV_rep S x y u v hu hv, commutatorElement_def, inv_inv]

end Work.Higman.MSA.L8

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.A_quot_irreducible
import Submission.Work.Higman.xi_trans_quot_sq
import Submission.Work.Higman.higman_lemma3_base
import Submission.Work.Higman.delta_uv_mem_powSub_four
import Submission.Work.Higman.MSA.basic
import Submission.Work.Higman.MSA.endgame
import Submission.Work.Higman.boolean_idempotent_family
import Submission.Work.Higman.clo_lemma3

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-! ## The derivation `u ↦ ⁅·, u⁆` modulo `A ^ (4)` -/

/-- `u` acts on `A` trivially modulo `A ^ (4)`: for every `a ∈ A` the commutator
`⁅a, u⁆ = a * u * a⁻¹ * u⁻¹` lies in `A ^ (4)`. -/
def derivZero (A : Subgroup P) (u : P) : Prop :=
  ∀ a ∈ A, a * u * a⁻¹ * u⁻¹ ∈ powSub A 4

/-- `A ^ (4)` is normal whenever `A` is. -/
theorem powSub_four_normal {A : Subgroup P} (hAn : A.Normal) : (powSub A 4).Normal := by
  refine Subgroup.Normal.mk ?_
  intro n hn g
  have h := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hn
  rw [map_powSub (MulAut.conj g) ((Subgroup.normal_iff_map_conj_eq.mp hAn) g) 4] at h
  simpa [MulAut.conj_apply] using h

theorem derivZero_one (A : Subgroup P) : derivZero A 1 := by
  intro a ha
  have hcomm : a * 1 = 1 * a := by rw [mul_one, one_mul]
  have hone : a * 1 * a⁻¹ * 1⁻¹ = 1 := by rw [hcomm]; group
  rw [hone]
  exact Subgroup.one_mem _

theorem derivZero_mul {A : Subgroup P} (hAn : A.Normal) {u v : P}
    (hu : derivZero A u) (hv : derivZero A v) : derivZero A (u * v) := by
  intro a ha
  have h4n : (powSub A 4).Normal := powSub_four_normal hAn
  have h1 := hu a ha
  have h2 := hv a ha
  have h3 : u * (a * v * a⁻¹ * v⁻¹) * u⁻¹ ∈ powSub A 4 := h4n.conj_mem _ h2 u
  have hid : a * (u * v) * a⁻¹ * (u * v)⁻¹
      = (a * u * a⁻¹ * u⁻¹) * (u * (a * v * a⁻¹ * v⁻¹) * u⁻¹) := by group
  rw [hid]
  exact Subgroup.mul_mem _ h1 h3

theorem derivZero_inv {A : Subgroup P} (hAn : A.Normal) {u : P}
    (hu : derivZero A u) : derivZero A u⁻¹ := by
  intro a ha
  rw [inv_inv]
  have h4n : (powSub A 4).Normal := powSub_four_normal hAn
  have h1 := hu a ha
  have h2 : u⁻¹ * (a * u * a⁻¹ * u⁻¹)⁻¹ * u ∈ powSub A 4 := by
    simpa using h4n.conj_mem _ ((powSub A 4).inv_mem h1) u⁻¹
  have hid : a * u⁻¹ * a⁻¹ * u = u⁻¹ * (a * u * a⁻¹ * u⁻¹)⁻¹ * u := by group
  rw [hid]
  exact h2

theorem derivZero_conj {A : Subgroup P} (hAn : A.Normal) {u p : P}
    (hu : derivZero A u) : derivZero A (p * u * p⁻¹) := by
  intro a ha
  have h4n : (powSub A 4).Normal := powSub_four_normal hAn
  have hpa : p⁻¹ * a * p ∈ A := by simpa using hAn.conj_mem a ha p⁻¹
  have h1 := hu (p⁻¹ * a * p) hpa
  have h2 : p * (p⁻¹ * a * p * u * (p⁻¹ * a * p)⁻¹ * u⁻¹) * p⁻¹ ∈ powSub A 4 :=
    h4n.conj_mem _ h1 p
  have hid : a * (p * u * p⁻¹) * a⁻¹ * (p * u * p⁻¹)⁻¹
      = p * (p⁻¹ * a * p * u * (p⁻¹ * a * p)⁻¹ * u⁻¹) * p⁻¹ := by group
  rw [hid]
  exact h2

/-- The subgroup of the elements acting trivially on `A` modulo `A ^ (4)`. -/
def derivKernel (A : Subgroup P) (hAn : A.Normal) : Subgroup P where
  carrier := {u | derivZero A u}
  mul_mem' := fun hu hv => derivZero_mul hAn hu hv
  one_mem' := derivZero_one A
  inv_mem' := fun hu => derivZero_inv hAn hu

theorem derivKernel_normal (A : Subgroup P) (hAn : A.Normal) :
    (derivKernel A hAn).Normal :=
  Subgroup.Normal.mk (fun _ hn _ => derivZero_conj hAn hn)

/-- The inverse-image of an invariant subgroup is itself. -/
theorem map_symm_eq_of_map_eq {A : Subgroup P} (φ : MulAut P)
    (h : A.map (φ : MulAut P).toMonoidHom = A) :
    A.map (φ.symm : MulAut P).toMonoidHom = A := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact symm_mem_of_map_eq φ h hy
  · intro x hx
    refine ⟨φ x, ?_, by simp⟩
    have hmem := Subgroup.mem_map_of_mem (φ : MulAut P).toMonoidHom hx
    rwa [h] at hmem

/-! ## Membership tests in power subgroups of `A` -/

theorem powSub_top_eq_bot_of_exp' {A : Subgroup P}
    (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    {e : ℕ} (he1 : ∀ a ∈ A, a ^ 2 ^ e = 1) : powSub A (2 ^ e) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (mem_powSub_iff hAb).mp hy
  simpa using he1 x hx

theorem mem_powSub_two_of_sq_mem_powSub_four' {A : Subgroup P}
    (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {e : ℕ} (he1 : ∀ a ∈ A, a ^ 2 ^ e = 1)
    (hkey : ∀ x ∈ A, x ∈ powSub A 2 ↔ x ^ 2 ^ (e - 1) = 1)
    (he : 2 ≤ e) {z : P} (hzA : z ∈ A) (hz : z ^ 2 ∈ powSub A 4) : z ∈ powSub A 2 := by
  refine (hkey z hzA).mpr ?_
  have h1 : z ^ 2 ^ (e - 1) = (z ^ 2) ^ 2 ^ (e - 2) := by
    rw [← pow_mul]
    congr 1
    rw [mul_comm, ← pow_succ]
    congr 1
    omega
  rw [h1]
  have h2 : (z ^ 2) ^ 2 ^ (e - 2) ∈ powSub (powSub A 4) (2 ^ (e - 2)) :=
    pow_mem_powSub hz
  rw [powSub_powSub hAb 4 (2 ^ (e - 2)), show 4 * 2 ^ (e - 2) = 2 ^ e from by
      rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_add]; congr 1; omega] at h2
  rw [powSub_top_eq_bot_of_exp' hAb he1] at h2
  simpa using h2

theorem mem_powSub_two_of_pow_four_eq_one' {A : Subgroup P}
    (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {e : ℕ}
    (hkey : ∀ x ∈ A, x ∈ powSub A 2 ↔ x ^ 2 ^ (e - 1) = 1) (he : 3 ≤ e)
    {z : P} (hzA : z ∈ A) (hz : z ^ 4 = 1) : z ∈ powSub A 2 := by
  refine (hkey z hzA).mpr ?_
  have h1 : 2 ^ (e - 1) = 4 * 2 ^ (e - 3) := by
    rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_add]
    congr 1
    omega
  rw [h1, pow_mul, hz, one_pow]

/-! ## `A / A ^ (2)` as a group -/

instance powSub_subgroupOf_normal (A : Subgroup P) : ((powSub A 2).subgroupOf A).Normal := by
  refine Subgroup.Normal.mk ?_
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hgA : (g : P) ∈ A := g.2
  have hgconj : A.map (MulAut.conj (g : P)).toMonoidHom = A := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      show (MulAut.conj (g : P)) y ∈ A
      rw [MulAut.conj_apply]
      exact A.mul_mem (A.mul_mem hgA hy) (A.inv_mem hgA)
    · intro x hx
      refine ⟨(g : P)⁻¹ * x * (g : P), ?_, ?_⟩
      · exact A.mul_mem (A.mul_mem (A.inv_mem hgA) hx) hgA
      · show (MulAut.conj (g : P)) ((g : P)⁻¹ * x * (g : P)) = x
        rw [MulAut.conj_apply]; group
  have hm := Subgroup.mem_map_of_mem (MulAut.conj (g : P)).toMonoidHom hn
  rw [map_powSub (MulAut.conj (g : P)) hgconj 2] at hm
  simpa [MulAut.conj_apply] using hm

/-! ## The derivation factor through `A / A ^ (2)` -/

/-- **The derivation-factor engine.**  For `u ∈ C` the square roots of the conjugation defects
`δ_u(a) = u⁻¹ a u a⁻¹ ∈ A ^ (2)` define an endomorphism `NB u` of `A / A ^ (2)`.  The family
`NB` is multiplicative in `u`, idempotent, `ξ`-stable (hence takes only the values `0` and `id`
by the scalar lemma), and `NB u = 0` exactly when `u` acts trivially on `A` modulo `A ^ (4)`. -/
theorem derivFactor_exists {h : IsSuzuki2Grp P} {A C : Subgroup P}
    (hA : IsXiAbelNormal h A) (hCn : C.Normal)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hC2 : powSub C 2 ≤ A)
    {e : ℕ} (he1 : ∀ a ∈ A, a ^ 2 ^ e = 1) (he2 : ∃ a ∈ A, orderOf a = 2 ^ e)
    (hkey : ∀ x ∈ A, x ∈ powSub A 2 ↔ x ^ 2 ^ (e - 1) = 1) (he : 3 ≤ e) :
    ∃ NB : ↥C → ((↥A ⧸ (powSub A 2).subgroupOf A) →* (↥A ⧸ (powSub A 2).subgroupOf A)),
      (∀ u, (NB u).comp (NB u) = NB u) ∧
      (∀ u v : ↥C, ∀ x, NB (u * v) x = NB u x * NB v x) ∧
      (∀ u : ↥C, (∀ x, NB u x = 1) ∨ NB u = MonoidHom.id _) ∧
      (∀ u : ↥C, (∀ x, NB u x = 1) ↔ derivZero A (u : P)) := by
  classical
  have hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.abelian
  have hAn : A.Normal := hA.normal
  have hsqrt4 : ∀ x ∈ A, x ^ 2 ∈ powSub A 4 → x ∈ powSub A 2 :=
    fun x hx hh => mem_powSub_two_of_sq_mem_powSub_four' hAb he1 hkey (by omega) hx hh
  have h4pow : ∀ x ∈ A, x ^ 4 = 1 → x ∈ powSub A 2 :=
    fun x hx hh => mem_powSub_two_of_pow_four_eq_one' hAb hkey he hx hh

  have hδmem : ∀ (u : P) (a : ↥A), u⁻¹ * (a : P) * u * (a : P)⁻¹ ∈ powSub A 2 := by
    intro u a
    have hh := commutator_mem_powSub_two h hA u⁻¹ (a : P) a.2
    rwa [commutatorElement_def, inv_inv] at hh
  -- `A` is abelian: install a `CommGroup` structure on `↥A`, keeping the ambient
  -- `Mul`/`Monoid` instances (which the type-class hierarchy must see consistently).
  letI hAcomm : CommGroup ↥A :=
    { (inferInstance : Group ↥A) with mul_comm := fun x y => Subtype.ext (hAb x x.2 y y.2) }
  letI : DivInvMonoid ↥A := (inferInstance : Group ↥A).toDivInvMonoid
  letI : Monoid ↥A := (inferInstance : Group ↥A).toMonoid
  let del : ↥C → ↥A → ↥A := fun u a =>
    ⟨(u:P)⁻¹ * (a:P) * (u:P) * (a:P)⁻¹, powSub_le (A := A) (n := 2) (by norm_num) (hδmem (u:P) a)⟩
  have del_coe : ∀ (u : ↥C) (a : ↥A),
      ((del u a : ↥A) : P) = (u:P)⁻¹ * (a:P) * (u:P) * (a:P)⁻¹ := fun _ _ => rfl
  have del_mul : ∀ (u : ↥C) (a b : ↥A), del u (a * b) = del u a * del u b := by
    intro u a b
    refine Subtype.ext ?_
    simp only [del_coe, Subgroup.coe_mul]
    exact delta_mul h hA (u:P) a b
  have del_inv : ∀ (u : ↥C) (a : ↥A), del u a⁻¹ = (del u a)⁻¹ := by
    intro u a
    refine Subtype.ext ?_
    simp only [del_coe, Subgroup.coe_inv, inv_inv]
    exact delta_inv h hA (u:P) a
  have del_pow : ∀ (u : ↥C) (a : ↥A), del u (a ^ 2) = del u a * del u a := by
    intro u a
    rw [pow_two, del_mul]
  have hrt_ex : ∀ (u : ↥C) (a : ↥A), ∃ x : ↥A, x ^ 2 = del u a := by
    intro u a
    obtain ⟨x, hxA, hx⟩ := (mem_powSub_iff hAb).mp (hδmem (u:P) a)
    exact ⟨⟨x, hxA⟩, Subtype.ext (by simpa [del_coe, Subgroup.coe_pow] using hx)⟩
  let rt : ↥C → ↥A → ↥A := fun u a => Classical.choose (hrt_ex u a)
  have rt_sq : ∀ (u : ↥C) (a : ↥A), rt u a ^ 2 = del u a :=
    fun u a => Classical.choose_spec (hrt_ex u a)
  have rt_mul : ∀ (u : ↥C) (a b : ↥A), ((rt u (a * b)) * ((rt u a) * (rt u b))⁻¹) ^ 2 = 1 := by
    intro u a b
    have key : rt u (a * b) ^ 2 = ((rt u a) * (rt u b)) ^ 2 := by
      rw [rt_sq, mul_pow, rt_sq, rt_sq, del_mul]
    rw [mul_pow, inv_pow, key, mul_inv_cancel]
  have rt_sq_mod : ∀ (u : ↥C) (z : ↥A), ((rt u (z ^ 2)) * ((rt u z) ^ 2)⁻¹) ^ 2 = 1 := by
    intro u z
    have key : rt u (z ^ 2) ^ 2 = ((rt u z) ^ 2) ^ 2 := by
      rw [pow_two z, rt_sq u (z * z), del_mul u z z, rt_sq u z, ← pow_two]
    rw [mul_pow, inv_pow, key, mul_inv_cancel]
  let sg : ↥C → ↥A → ↥A := fun u y => ⟨(u:P)⁻¹ * (y:P) * (u:P), by
    simpa using hA.normal.conj_mem (y:P) y.2 (u:P)⁻¹⟩
  have sg_coe : ∀ (u : ↥C) (y : ↥A),
      ((sg u y : ↥A) : P) = (u:P)⁻¹ * (y:P) * (u:P) := fun _ _ => rfl
  have sg_eq : ∀ (u : ↥C) (y : ↥A), sg u y = y * del u y := by
    intro u y
    refine Subtype.ext ?_
    simp only [sg_coe, del_coe, Subgroup.coe_mul]
    have hmem : (u:P)⁻¹ * (y:P) * (u:P) * (y:P)⁻¹ ∈ A :=
      A.mul_mem (by simpa using hA.normal.conj_mem (y:P) y.2 (u:P)⁻¹) (A.inv_mem y.2)
    calc (u:P)⁻¹ * (y:P) * (u:P)
        = ((u:P)⁻¹ * (y:P) * (u:P) * (y:P)⁻¹) * (y:P) := by group
      _ = (y:P) * ((u:P)⁻¹ * (y:P) * (u:P) * (y:P)⁻¹) := hAb _ hmem (y:P) y.2
  have hu2A : ∀ u : ↥C, (u:P) * (u:P) ∈ A := by
    intro u
    have h1 : (u:P) * (u:P) ∈ powSub C 2 := by
      rw [← pow_two]; exact pow_mem_powSub (A := C) (n := 2) u.2
    exact hC2 h1
  have sg_sg : ∀ (u : ↥C) (y : ↥A), sg u (sg u y) = y := by
    intro u y
    refine Subtype.ext ?_
    simp only [sg_coe]
    have hcomm : ((u:P) * (u:P))⁻¹ * (y:P) = (y:P) * ((u:P) * (u:P))⁻¹ :=
      hAb _ (A.inv_mem (hu2A u)) _ y.2
    calc (u:P)⁻¹ * ((u:P)⁻¹ * (y:P) * (u:P)) * (u:P)
        = ((u:P) * (u:P))⁻¹ * (y:P) * ((u:P) * (u:P)) := by group
      _ = (y:P) * ((u:P) * (u:P))⁻¹ * ((u:P) * (u:P)) := by rw [hcomm]
      _ = (y:P) := by group
  have hdel_rel : ∀ (u : ↥C) (y : ↥A), (del u y) ^ 2 * del u (del u y) = 1 := by
    intro u y
    have h1 : y = sg u y * del u (sg u y) := by
      have h2 : sg u (sg u y) = sg u y * del u (sg u y) := sg_eq u (sg u y)
      rwa [sg_sg] at h2
    rw [sg_eq u y, del_mul] at h1
    calc del u y ^ 2 * del u (del u y)
        = y⁻¹ * ((y * del u y) * (del u y * del u (del u y))) := by rw [pow_two]; group
      _ = y⁻¹ * y := by rw [← h1]
      _ = 1 := inv_mul_cancel _
  have hkey4 : ∀ (u : ↥C) (y : ↥A), (rt u y * rt u (rt u y)) ^ 4 = 1 := by
    intro u y
    have h1 : (rt u y) ^ 4 * (rt u (rt u y)) ^ 4 = 1 := by
      have h2 := hdel_rel u y
      rw [← rt_sq u y] at h2
      have h3 : del u ((rt u y) ^ 2) = (rt u (rt u y)) ^ 4 := by
        rw [pow_two (rt u y), del_mul u (rt u y) (rt u y), ← pow_two,
          ← rt_sq u (rt u y), ← pow_mul]
      rw [h3, ← pow_mul] at h2
      exact h2
    rw [mul_pow]
    exact h1
  let K : Subgroup ↥A := (powSub A 2).subgroupOf A
  have hKmem : ∀ c : ↥A, c ∈ K ↔ (c : P) ∈ powSub A 2 := fun c => Subgroup.mem_subgroupOf
  haveI hKn : K.Normal := ⟨fun n hn g => by
    rw [show g * n * g⁻¹ = n from Subtype.ext (by
      show (g:P) * (n:P) * (g:P)⁻¹ = (n:P)
      rw [hAb (g:P) g.2 (n:P) n.2]; group)]
    exact hn⟩
  have hVexp : ∀ v : (↥A ⧸ K), v * v = 1 := by
    intro v
    refine Quotient.inductionOn v (fun a => ?_)
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, hKmem]
    simpa [Subgroup.coe_mul, pow_two] using pow_mem_powSub (A := A) (n := 2) a.2
  have hwd : ∀ (u : ↥C) (a b : ↥A), a⁻¹ * b ∈ K → (rt u a)⁻¹ * rt u b ∈ K := by
    intro u a b hab
    rw [hKmem] at hab ⊢
    have h1 : ((rt u a)⁻¹ * rt u b) ^ 2 = del u (a⁻¹ * b) := by
      rw [mul_pow, inv_pow, rt_sq, rt_sq, del_mul, del_inv]
    have h2 : ((((rt u a)⁻¹ * rt u b : ↥A)) : P) ^ 2 ∈ powSub A 4 := by
      rw [← Subgroup.coe_pow, h1]
      simpa [del_coe] using delta_mem_powSub_four h hA (u:P) (A.mul_mem (A.inv_mem a.2) b.2) hab
    exact hsqrt4 _ (A.mul_mem (A.inv_mem (rt u a).2) (rt u b).2) h2
  let nbf : ↥C → (↥A ⧸ K) → (↥A ⧸ K) := fun u x =>
    Quotient.liftOn' x (fun a : ↥A => (QuotientGroup.mk (rt u a) : ↥A ⧸ K)) (by
      intro a b hab
      rw [QuotientGroup.eq]
      exact hwd u a b (QuotientGroup.leftRel_apply.mp hab))
  have nbf_mk : ∀ (u : ↥C) (a : ↥A),
      nbf u (QuotientGroup.mk a) = QuotientGroup.mk (rt u a) := fun u a => rfl
  have nbf_mul : ∀ (u : ↥C) (x y : ↥A ⧸ K), nbf u (x * y) = nbf u x * nbf u y := by
    intro u x y
    refine Quotient.inductionOn x (fun a => ?_)
    refine Quotient.inductionOn y (fun b => ?_)
    rw [← QuotientGroup.mk_mul]
    show (QuotientGroup.mk (rt u (a * b)) : ↥A ⧸ K)
      = QuotientGroup.mk (rt u a) * QuotientGroup.mk (rt u b)
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, hKmem]
    have h2 : ((rt u (a * b))⁻¹ * (rt u a * rt u b) : ↥A) ^ 2 = 1 := by
      have he : ((rt u (a * b))⁻¹ * (rt u a * rt u b) : ↥A)
          = ((rt u (a * b)) * (rt u a * rt u b)⁻¹)⁻¹ := by
        rw [mul_inv_rev, inv_inv]
        exact mul_comm _ _
      rw [he, inv_pow, rt_mul u a b, inv_one]
    have h1 : ((((rt u (a * b))⁻¹ * (rt u a * rt u b) : ↥A)) : P) ^ 2 ∈ powSub A 4 := by
      rw [← Subgroup.coe_pow, h2]
      simpa using Subgroup.one_mem (powSub A 4)
    exact hsqrt4 _ (A.mul_mem (A.inv_mem (rt u (a*b)).2) (A.mul_mem (rt u a).2 (rt u b).2)) h1
  let NB : ↥C → ((↥A ⧸ K) →* (↥A ⧸ K)) := fun u => MonoidHom.mk' (nbf u) (nbf_mul u)
  have NB_apply : ∀ (u : ↥C) (x : ↥A ⧸ K), NB u x = nbf u x := fun u x => rfl
  have nbf_mul_u : ∀ (u v : ↥C) (x : ↥A ⧸ K), nbf (u * v) x = nbf u x * nbf v x := by
    intro u v x
    refine Quotient.inductionOn x (fun a => ?_)
    show (QuotientGroup.mk (rt (u*v) a) : ↥A ⧸ K)
      = QuotientGroup.mk (rt u a) * QuotientGroup.mk (rt v a)
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, hKmem]
    have h1 : ((((rt (u * v) a)⁻¹ * (rt u a * rt v a) : ↥A)) : P) ^ 2 ∈ powSub A 4 := by
      rw [← Subgroup.coe_pow]
      have h2 : ((rt (u * v) a)⁻¹ * (rt u a * rt v a)) ^ 2
          = (del (u * v) a * (del u a * del v a)⁻¹)⁻¹ := by
        rw [mul_pow, inv_pow, mul_pow, rt_sq, rt_sq, rt_sq, mul_inv_rev, inv_inv]
        exact mul_comm _ _
      rw [h2, Subgroup.coe_inv]
      refine (powSub A 4).inv_mem ?_
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, del_coe] using
        delta_uv_mem_powSub_four h hA (u:P) (v:P) a
    exact hsqrt4 _ (A.mul_mem (A.inv_mem (rt (u*v) a).2) (A.mul_mem (rt u a).2 (rt v a).2)) h1
  have NB_idem : ∀ u : ↥C, (NB u).comp (NB u) = NB u := by
    intro u
    apply MonoidHom.ext
    intro x
    refine Quotient.inductionOn x (fun a => ?_)
    show nbf u (nbf u (QuotientGroup.mk a)) = nbf u (QuotientGroup.mk a)
    show (QuotientGroup.mk (rt u (rt u a)) : ↥A ⧸ K) = QuotientGroup.mk (rt u a)
    have h4 := hkey4 u a
    have h5 : (QuotientGroup.mk (rt u a) * QuotientGroup.mk (rt u (rt u a)) : ↥A ⧸ K) = 1 := by
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, hKmem, Subgroup.coe_mul]
      refine h4pow _ (A.mul_mem (rt u a).2 (rt u (rt u a)).2) ?_
      have h4' := congrArg (fun t : ↥A => (t : P)) h4
      simpa only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_one] using h4'
    have hW : (QuotientGroup.mk (rt u a) : ↥A ⧸ K) = (QuotientGroup.mk (rt u a))⁻¹ :=
      (inv_eq_of_mul_eq_one_right (hVexp _)).symm
    calc QuotientGroup.mk (rt u (rt u a))
        = (QuotientGroup.mk (rt u a))⁻¹ := eq_inv_of_mul_eq_one_right h5
      _ = QuotientGroup.mk (rt u a) := hW.symm
  -- the automorphism of `A/A²` induced by `ξ`
  let xA : ↥A ≃* ↥A :=
    { toFun := fun a => ⟨h.xi (a:P), by
        have hm := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom a.2
        rwa [hA.map_eq] at hm⟩
      invFun := fun a => ⟨(h.xi : MulAut P).symm (a:P), symm_mem_of_map_eq h.xi hA.map_eq a.2⟩
      left_inv := fun a => Subtype.ext (by simp)
      right_inv := fun a => Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have xA_coe : ∀ a : ↥A, ((xA a : ↥A) : P) = h.xi (a:P) := fun a => rfl
  have xA_symm_coe : ∀ a : ↥A, ((xA.symm a : ↥A) : P) = (h.xi : MulAut P).symm (a:P) :=
    fun a => rfl
  have xA_apply_symm : ∀ a : ↥A, xA (xA.symm a) = a := fun a => MulEquiv.apply_symm_apply xA a
  have hmapK : Subgroup.map (xA : ↥A →* ↥A) K = K := by
    ext x
    rw [Subgroup.mem_map, hKmem]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : (y : P) ∈ powSub A 2 := (hKmem y).mp hy
      show h.xi (y : P) ∈ powSub A 2
      have h2 := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom hy'
      rwa [map_powSub (h.xi : MulAut P) hA.map_eq 2] at h2
    · intro hx
      refine ⟨xA.symm x, (hKmem _).mpr ?_, xA_apply_symm x⟩
      show ((xA.symm x : ↥A) : P) ∈ powSub A 2
      rw [xA_symm_coe]
      exact symm_mem_of_map_eq h.xi (map_powSub (h.xi : MulAut P) hA.map_eq 2) hx
  have hmapKinv : Subgroup.map (xA.symm : ↥A →* ↥A) K = K := by
    ext x
    rw [Subgroup.mem_map, hKmem]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : (y : P) ∈ powSub A 2 := (hKmem y).mp hy
      show ((xA.symm y : ↥A) : P) ∈ powSub A 2
      rw [xA_symm_coe]
      exact symm_mem_of_map_eq h.xi (map_powSub (h.xi : MulAut P) hA.map_eq 2) hy'
    · intro hx
      refine ⟨xA x, (hKmem _).mpr ?_, MulEquiv.symm_apply_apply xA x⟩
      show ((xA x : ↥A) : P) ∈ powSub A 2
      rw [xA_coe]
      have h2 := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom hx
      rwa [map_powSub (h.xi : MulAut P) hA.map_eq 2] at h2
  have Tfun_wd : ∀ a b : ↥A, a⁻¹ * b ∈ K → (xA a)⁻¹ * xA b ∈ K := by
    intro a b hab
    have h1 : xA (a⁻¹ * b) ∈ K := by
      have hm := Subgroup.mem_map_of_mem (xA : ↥A →* ↥A) hab
      rwa [hmapK] at hm
    rw [← map_inv, ← map_mul]
    exact h1
  let Tfun : (↥A ⧸ K) → (↥A ⧸ K) := Quotient.map' xA (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    exact Tfun_wd a b hab)
  have Tfun_mk : ∀ a : ↥A, Tfun (QuotientGroup.mk a) = QuotientGroup.mk (xA a) := fun a => rfl
  have Tfun_mul : ∀ x y : (↥A ⧸ K), Tfun (x * y) = Tfun x * Tfun y := by
    intro x y
    refine Quotient.inductionOn x (fun a => ?_)
    refine Quotient.inductionOn y (fun b => ?_)
    rw [← QuotientGroup.mk_mul, Tfun_mk]
    show (QuotientGroup.mk (xA (a * b)) : ↥A ⧸ K)
      = QuotientGroup.mk (xA a) * QuotientGroup.mk (xA b)
    rw [← QuotientGroup.mk_mul]
    refine QuotientGroup.eq.mpr ?_
    simpa [map_mul] using K.one_mem
  let TqHom : (↥A ⧸ K) →* (↥A ⧸ K) := MonoidHom.mk' Tfun Tfun_mul
  have TqHom_mk : ∀ a : ↥A, TqHom (QuotientGroup.mk a) = QuotientGroup.mk (xA a) := fun a => rfl
  have TqHom_bij : Function.Bijective TqHom := by
    constructor
    · intro x y hxy
      revert hxy
      refine Quotient.inductionOn x (fun a => ?_)
      refine Quotient.inductionOn y (fun b => ?_)
      intro hxy
      have h1 : (xA a)⁻¹ * (xA b) ∈ K := by
        rw [← QuotientGroup.eq]; exact hxy
      have h2 : xA.symm ((xA a)⁻¹ * (xA b)) ∈ K := by
        have hm := Subgroup.mem_map_of_mem (xA.symm : ↥A →* ↥A) h1
        rwa [hmapKinv] at hm
      rw [map_mul, map_inv] at h2
      rw [QuotientGroup.eq]
      simpa using h2
    · intro y
      refine Quotient.inductionOn y (fun b => ?_)
      refine ⟨QuotientGroup.mk (xA.symm b), ?_⟩
      show QuotientGroup.mk (xA (xA.symm b)) = QuotientGroup.mk b
      rw [xA_apply_symm]
  let Tq : MulAut (↥A ⧸ K) := MulEquiv.ofBijective TqHom TqHom_bij
  have Tq_apply : ∀ a : ↥A, Tq (QuotientGroup.mk a) = QuotientGroup.mk (xA a) := fun a => rfl
  have Tq_pow_apply : ∀ (k : ℕ) (b : ↥A),
      (Tq ^ k) (QuotientGroup.mk b)
        = QuotientGroup.mk (⟨(h.xi ^ k) (b:P), apply_xi_pow_mem h hA.map_eq k b.2⟩ : ↥A) := by
    intro k b
    induction k with
    | zero =>
      show QuotientGroup.mk b = QuotientGroup.mk (⟨(h.xi ^ 0) (b:P), _⟩ : ↥A)
      rfl
    | succ k ih =>
      rw [pow_succ']
      show Tq ((Tq ^ k) (QuotientGroup.mk b)) = _
      rw [ih, Tq_apply]
      congr 1
      apply Subtype.ext
      show (h.xi : MulAut P) ((h.xi ^ k) (b:P)) = (h.xi ^ (k+1)) (b:P)
      rw [pow_succ', MulAut.mul_apply]
  have htrans : ∀ a b : (↥A ⧸ K), a ≠ 1 → b ≠ 1 → ∃ k, (Tq ^ k) a = b := by
    intro a b ha hb
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    have ha2 : (a' : P) ∉ powSub A 2 := by
      intro hc
      exact ha (by rw [QuotientGroup.eq_one_iff, hKmem]; exact hc)
    have hb2 : (b' : P) ∉ powSub A 2 := by
      intro hc
      exact hb (by rw [QuotientGroup.eq_one_iff, hKmem]; exact hc)
    obtain ⟨k, hk⟩ := xi_trans_quot_sq h hA a'.2 b'.2 ha2 hb2
    refine ⟨k, ?_⟩
    rw [Tq_pow_apply k a']
    rw [QuotientGroup.eq_iff_div_mem, hKmem]
    simpa [Subgroup.coe_div, div_eq_mul_inv] using hk
  haveI : Fintype ↥C := Fintype.ofFinite _
  have hpt : ∀ i j : ↥C, ∃ k, NB k = NB i * NB j := by
    intro i j
    refine ⟨i * j, ?_⟩
    ext x
    exact nbf_mul_u i j x
  let xC : ↥C ≃ ↥C :=
    { toFun := fun u => ⟨h.xi (u:P), by
        have hm := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom u.2
        rwa [hCinv] at hm⟩
      invFun := fun u => ⟨(h.xi : MulAut P).symm (u:P), symm_mem_of_map_eq h.xi hCinv u.2⟩
      left_inv := fun u => Subtype.ext (by simp)
      right_inv := fun u => Subtype.ext (by simp) }
  have xC_coe : ∀ u : ↥C, ((xC u : ↥C) : P) = h.xi (u:P) := fun u => rfl
  have hstab : ∃ τ : ↥C ≃ ↥C,
      ∀ i, Tq.toMonoidHom.comp ((NB i).comp Tq.symm.toMonoidHom) = NB (τ i) := by
    refine ⟨xC, ?_⟩
    intro i
    apply MonoidHom.ext
    intro x
    refine Quotient.inductionOn x (fun a => ?_)
    show Tq (NB i (Tq.symm (QuotientGroup.mk a))) = NB (xC i) (QuotientGroup.mk a)
    have hsym : Tq.symm (QuotientGroup.mk a) = QuotientGroup.mk (xA.symm a) := by
      apply Tq.injective
      rw [MulEquiv.apply_symm_apply, Tq_apply, xA_apply_symm]
    rw [hsym, NB_apply, nbf_mk, Tq_apply, NB_apply, nbf_mk]
    rw [QuotientGroup.eq, hKmem]
    have hisq : (rt (xC i) a) ^ 2 = (xA (rt i (xA.symm a))) ^ 2 := by
      rw [rt_sq (xC i) a,
        show (xA (rt i (xA.symm a))) ^ 2 = xA ((rt i (xA.symm a)) ^ 2) from
          (map_pow (xA : ↥A →* ↥A) _ 2).symm,
        rt_sq i (xA.symm a)]
      refine Subtype.ext ?_
      simp only [del_coe, xA_coe, xA_symm_coe, xC_coe]
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply]
    have hsq : ((rt (xC i) a)⁻¹ * xA (rt i (xA.symm a))) ^ 2 = 1 := by
      rw [mul_pow, inv_pow, hisq, inv_mul_cancel]
    have hfin : ((((xA (rt i (xA.symm a)))⁻¹ * rt (xC i) a : ↥A)) : P) ^ 2 ∈ powSub A 4 := by
      rw [← Subgroup.coe_pow]
      have h2 : ((xA (rt i (xA.symm a)))⁻¹ * rt (xC i) a : ↥A) ^ 2 = 1 := by
        have he : ((xA (rt i (xA.symm a)))⁻¹ * rt (xC i) a : ↥A)
            = ((rt (xC i) a)⁻¹ * xA (rt i (xA.symm a)))⁻¹ := by
          rw [mul_inv_rev, inv_inv]
        rw [he, inv_pow, hsq, inv_one]
      rw [h2]
      simpa using Subgroup.one_mem (powSub A 4)
    exact hsqrt4 (((xA (rt i (xA.symm a)))⁻¹ * rt (xC i) a : ↥A) : P)
      (A.mul_mem (A.inv_mem (xA (rt i (xA.symm a))).2) (rt (xC i) a).2) hfin
  have hscalar := scalar_endomorphism hVexp Tq htrans NB hpt NB_idem hstab

  refine ⟨NB, ?_, ?_, ?_, ?_⟩
  · intro u; exact NB_idem u
  · intro u v x
    rw [NB_apply, NB_apply, NB_apply]
    exact nbf_mul_u u v x
  · intro u
    rcases hscalar u with hz | hid
    · exact Or.inl hz
    · exact Or.inr hid
  · intro u
    constructor
    · intro h0 a ha
      have h1 : NB u (QuotientGroup.mk (⟨a, ha⟩ : ↥A)) = 1 := h0 _
      rw [NB_apply, nbf_mk, QuotientGroup.eq_one_iff, hKmem] at h1
      have h2 : ((rt u ⟨a, ha⟩ : ↥A) : P) ^ 2 ∈ powSub A 4 := by
        rw [← powSub_powSub hAb 2 2]
        exact pow_mem_powSub (A := powSub A 2) (n := 2) h1
      have h3 : ((del u ⟨a, ha⟩ : ↥A) : P) ∈ powSub A 4 := by
        have hh := congrArg (fun t : ↥A => (t : P)) (rt_sq u ⟨a, ha⟩)
        simp only [Subgroup.coe_pow] at hh
        rw [← hh]
        exact h2
      have hdu : (u : P)⁻¹ * a * (u : P) * a⁻¹ ∈ powSub A 4 := by
        rw [← del_coe u ⟨a, ha⟩]; exact h3
      have hconj : (u : P) * ((u : P)⁻¹ * a * (u : P) * a⁻¹) * (u : P)⁻¹ ∈ powSub A 4 :=
        (powSub_four_normal hAn).conj_mem _ hdu (u : P)
      have hid : a * (u : P) * a⁻¹ * (u : P)⁻¹
          = (u : P) * ((u : P)⁻¹ * a * (u : P) * a⁻¹) * (u : P)⁻¹ := by group
      rw [hid]; exact hconj
    · intro hdv x
      refine Quotient.inductionOn x (fun a => ?_)
      rw [NB_apply, nbf_mk, QuotientGroup.eq_one_iff, hKmem]
      apply hsqrt4 _ (rt u a).2
      have hda : (u : P)⁻¹ * (a : P) * (u : P) * (a : P)⁻¹ ∈ powSub A 4 := by
        have h1 := hdv (a : P) a.2
        have h2 : (u : P)⁻¹ * ((a : P) * (u : P) * (a : P)⁻¹ * (u : P)⁻¹) * (u : P)
            ∈ powSub A 4 := by
          simpa using (powSub_four_normal hAn).conj_mem _ h1 (u : P)⁻¹
        have hid : (u : P)⁻¹ * ((a : P) * (u : P) * (a : P)⁻¹ * (u : P)⁻¹) * (u : P)
            = (u : P)⁻¹ * (a : P) * (u : P) * (a : P)⁻¹ := by group
        rwa [hid] at h2
      have hh := congrArg (fun t : ↥A => (t : P)) (rt_sq u a)
      simp only [Subgroup.coe_pow] at hh
      rw [hh, del_coe]
      exact hda

/-! ## The main theorem -/

theorem higman9_derivation_kernel {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A) (hCn : C.Normal)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hC2 : Work.Higman.powSub C 2 ≤ A)
    {e : ℕ} (he1 : ∀ a ∈ A, a ^ 2 ^ e = 1) (he2 : ∃ a ∈ A, orderOf a = 2 ^ e)
    (hkey : ∀ x ∈ A, x ∈ Work.Higman.powSub A 2 ↔ x ^ 2 ^ (e - 1) = 1)
    (he : 3 ≤ e) :
    ∃ Z : Subgroup P, Z ≤ C ∧ A ≤ Z ∧ Z.Normal ∧
      Z.map (h.xi : MulAut P).toMonoidHom = Z ∧
      (∀ u ∈ C, u ∈ Z ↔ ∀ a ∈ A, a * u * a⁻¹ * u⁻¹ ∈ Work.Higman.powSub A 4) ∧
      (Z = C ∨ Subgroup.index (Z.subgroupOf C) = 2) := by
  classical
  have hAn : A.Normal := hA.normal
  have hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.abelian
  -- the candidate subgroup
  let Z : Subgroup P := derivKernel A hAn ⊓ C
  have hZle : Z ≤ C := inf_le_right
  have hAZ : A ≤ Z := by
    intro x hx
    rw [Subgroup.mem_inf]
    refine ⟨?_, hAC hx⟩
    intro a ha
    have hcomm : a * x = x * a := hAb a ha x hx
    have hone : a * x * a⁻¹ * x⁻¹ = 1 := by rw [hcomm]; group
    rw [hone]
    exact Subgroup.one_mem _
  have hZn : Z.Normal := Subgroup.Normal.mk (fun n hn g => by
    rw [Subgroup.mem_inf] at hn ⊢
    exact ⟨(derivKernel_normal A hAn).conj_mem n hn.1 g, hCn.conj_mem n hn.2 g⟩)
  have hZinv : Z.map (h.xi : MulAut P).toMonoidHom = Z := by
    have hWinv : (derivKernel A hAn).map (h.xi : MulAut P).toMonoidHom
        = derivKernel A hAn := by
      apply le_antisymm
      · rintro x ⟨y, hy, rfl⟩
        intro a ha
        have hxa : (h.xi : MulAut P).symm a ∈ A := symm_mem_of_map_eq h.xi hA.map_eq ha
        have h1 : (h.xi : MulAut P).symm a * y * ((h.xi : MulAut P).symm a)⁻¹ * y⁻¹
            ∈ powSub A 4 := hy _ hxa
        have h2 : (h.xi : MulAut P)
            ((h.xi : MulAut P).symm a * y * ((h.xi : MulAut P).symm a)⁻¹ * y⁻¹)
            ∈ powSub A 4 := by
          have hm := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom h1
          rwa [map_powSub (h.xi : MulAut P) hA.map_eq 4] at hm
        convert h2 using 2 <;> simp
      · intro x hx
        refine ⟨(h.xi : MulAut P).symm x, ?_, by simp⟩
        intro a ha
        have hAinv' : A.map ((h.xi : MulAut P).symm).toMonoidHom = A :=
          map_symm_eq_of_map_eq h.xi hA.map_eq
        have h1 : (h.xi : MulAut P) a ∈ A := by
          have hm := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom ha
          rwa [hA.map_eq] at hm
        have h2 : (h.xi : MulAut P) a * x * ((h.xi : MulAut P) a)⁻¹ * x⁻¹
            ∈ powSub A 4 := hx _ h1
        have h3 : (h.xi : MulAut P).symm
            ((h.xi : MulAut P) a * x * ((h.xi : MulAut P) a)⁻¹ * x⁻¹)
            ∈ powSub A 4 := by
          have hm := Subgroup.mem_map_of_mem ((h.xi : MulAut P).symm).toMonoidHom h2
          rwa [map_powSub ((h.xi : MulAut P).symm) hAinv' 4] at hm
        convert h3 using 2 <;> simp
    rw [Subgroup.map_inf _ _ _ (h.xi : MulAut P).injective, hWinv, hCinv]
  have hZchar : ∀ u ∈ C, (u ∈ Z ↔ derivZero A u) := by
    intro u hu
    show u ∈ derivKernel A hAn ⊓ C ↔ derivZero A u
    rw [Subgroup.mem_inf, and_iff_left hu]
    rfl
  refine ⟨Z, hZle, hAZ, hZn, hZinv, ?_, ?_⟩
  · intro u hu
    rw [hZchar u hu]
    rfl
  · by_cases hall : ∀ u ∈ C, derivZero A u
    · left
      apply le_antisymm hZle
      intro u hu
      rw [Subgroup.mem_inf]
      exact ⟨hall u hu, hu⟩
    · right
      push_neg at hall
      obtain ⟨u0, hu0C, hu0bad⟩ := hall
      obtain ⟨NB, hNBidem, hNBmul, hNBscalar, hNBchar⟩ :=
        derivFactor_exists hA hCn hCinv hAC hC2 he1 he2 hkey he
      -- `V = A / A ^ (2)` has exponent two
      have hVexp : ∀ x : (↥A ⧸ (powSub A 2).subgroupOf A), x * x = 1 := by
        intro x
        refine Quotient.inductionOn x (fun a => ?_)
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        have h : ((a : P)) ^ 2 ∈ powSub A 2 := pow_mem_powSub (A := A) (n := 2) a.2
        simpa [pow_two] using h
      -- `V` is non-trivial
      have hVnt : ∃ x : (↥A ⧸ (powSub A 2).subgroupOf A), x ≠ 1 := by
        obtain ⟨a, haA, haord⟩ := he2
        refine ⟨QuotientGroup.mk (⟨a, haA⟩ : ↥A), ?_⟩
        intro hc
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hc
        have h1 : a ^ 2 ^ (e - 1) = 1 := (hkey a haA).mp hc
        have hdvd : orderOf a ∣ 2 ^ (e - 1) := orderOf_dvd_iff_pow_eq_one.mpr h1
        rw [haord] at hdvd
        have hlt : 2 ^ (e - 1) < 2 ^ e := Nat.pow_lt_pow_right (by norm_num) (by omega)
        exact not_le_of_gt hlt (Nat.le_of_dvd (pow_pos (by norm_num) _) hdvd)
      have hnt : ∃ x : (↥A ⧸ (powSub A 2).subgroupOf A), (MonoidHom.id _) x ≠ 1 := by
        obtain ⟨x, hx⟩ := hVnt
        exact ⟨x, by simpa using hx⟩
      -- a "bad" element has `NB = id`
      have hid_of_bad : ∀ u : ↥C, ¬ derivZero A (u : P) → NB u = MonoidHom.id _ := by
        intro u hu
        rcases hNBscalar u with hz | hid
        · exact absurd ((hNBchar u).mp hz) hu
        · exact hid
      -- the truth table: `derivZero (u*v) ↔ (derivZero u ↔ derivZero v)`
      have hderiv_iff : ∀ u v : ↥C,
          derivZero A ((u * v : ↥C) : P)
            ↔ (derivZero A (u : P) ↔ derivZero A (v : P)) := by
        intro u v
        by_cases hu : derivZero A (u : P) <;> by_cases hv : derivZero A (v : P)
        · exact ⟨fun _ => ⟨fun _ => hv, fun _ => hu⟩,
            fun _ => derivZero_mul hAn hu hv⟩
        · have hbadv : ¬ derivZero A ((u * v : ↥C) : P) := by
            intro hcon
            have hz : ∀ x, NB (u * v) x = 1 := (hNBchar (u * v)).mpr hcon
            obtain ⟨x, hx⟩ := hnt
            have h1 : NB u x = 1 := (hNBchar u).mpr hu x
            have h2 : NB v x = x := by rw [hid_of_bad v hv]; rfl
            have h3 : NB (u * v) x = x := by rw [hNBmul u v x, h1, h2, one_mul]
            have hx1 : x = 1 := by rw [← h3]; exact hz x
            exact hx hx1
          exact ⟨fun h => absurd h hbadv, fun h => absurd (h.mp hu) hv⟩
        · have hbadv : ¬ derivZero A ((u * v : ↥C) : P) := by
            intro hcon
            have hz : ∀ x, NB (u * v) x = 1 := (hNBchar (u * v)).mpr hcon
            obtain ⟨x, hx⟩ := hnt
            have h1 : NB u x = x := by rw [hid_of_bad u hu]; rfl
            have h2 : NB v x = 1 := (hNBchar v).mpr hv x
            have h3 : NB (u * v) x = x := by rw [hNBmul u v x, h1, h2, mul_one]
            have hx1 : x = 1 := by rw [← h3]; exact hz x
            exact hx hx1
          exact ⟨fun h => absurd h hbadv, fun h => absurd (h.mpr hv) hu⟩
        · have hgood : derivZero A ((u * v : ↥C) : P) := by
            refine (hNBchar (u * v)).mp (fun x => ?_)
            have h1 : NB u x = x := by rw [hid_of_bad u hu]; rfl
            have h2 : NB v x = x := by rw [hid_of_bad v hv]; rfl
            rw [hNBmul u v x, h1, h2]
            exact hVexp x
          exact ⟨fun _ => ⟨fun h => absurd h hu, fun h => absurd h hv⟩, fun _ => hgood⟩
      -- the index is two
      have hxor : ∀ b : ↥C,
          Xor (b * ⟨u0, hu0C⟩ ∈ Z.subgroupOf C) (b ∈ Z.subgroupOf C) := by
        intro b
        have hb1 : (b * ⟨u0, hu0C⟩ ∈ Z.subgroupOf C) ↔ ¬ derivZero A (b : P) := by
          rw [Subgroup.mem_subgroupOf]
          rw [hZchar ((b * ⟨u0, hu0C⟩ : ↥C) : P) (C.mul_mem b.2 hu0C)]
          rw [hderiv_iff b ⟨u0, hu0C⟩]
          constructor
          · intro h hb; exact hu0bad (h.mp hb)
          · intro h; exact ⟨fun hb => absurd hb h, fun hu => absurd hu hu0bad⟩
        have hb2 : (b ∈ Z.subgroupOf C) ↔ derivZero A (b : P) := by
          rw [Subgroup.mem_subgroupOf]
          exact hZchar (b : P) b.2
        rw [hb1, hb2]
        tauto
      exact Subgroup.index_eq_two_iff.mpr ⟨⟨u0, hu0C⟩, hxor⟩

end Work.Higman

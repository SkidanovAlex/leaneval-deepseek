import Mathlib
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.higman_lemma2
import Submission.Work.Higman.higman_lemma3_base
import Submission.Work.Higman.higman_lemma8
import Submission.Work.Higman.delta_uv_mem_powSub_four
import Submission.Work.Higman.xi_trans_quot_sq
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.boolean_idempotent_family
import Submission.Work.Higman.higman_lemma3_last_step

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

/-- The conjugation defect `u⁻¹ * a * u * a⁻¹` (`= ⁅u⁻¹, a⁆`) is multiplicative in `a`. -/
theorem delta_mul (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A) (u : P)
    (a b : ↥A) :
    u⁻¹ * ((a : P) * (b : P)) * u * ((a : P) * (b : P))⁻¹
      = (u⁻¹ * (a : P) * u * (a : P)⁻¹) * (u⁻¹ * (b : P) * u * (b : P)⁻¹) := by
  have hc2 : u⁻¹ * (b : P) * u ∈ A := by simpa using hA.normal.conj_mem (b : P) b.2 u⁻¹
  have hcab : (u⁻¹ * (b : P) * u) * (b : P)⁻¹ ∈ A := A.mul_mem hc2 (A.inv_mem b.2)
  calc u⁻¹ * ((a : P) * (b : P)) * u * ((a : P) * (b : P))⁻¹
      = (u⁻¹ * (a : P) * u) * ((u⁻¹ * (b : P) * u) * (b : P)⁻¹ * (a : P)⁻¹) := by
        rw [mul_inv_rev]; group
    _ = (u⁻¹ * (a : P) * u) * ((a : P)⁻¹ * ((u⁻¹ * (b : P) * u) * (b : P)⁻¹)) := by
        rw [hA.abelian ((u⁻¹ * (b : P) * u) * (b : P)⁻¹) hcab ((a : P)⁻¹) (A.inv_mem a.2)]
    _ = (u⁻¹ * (a : P) * u * (a : P)⁻¹) * (u⁻¹ * (b : P) * u * (b : P)⁻¹) := by group

/-- The conjugation defect of the inverse is the inverse of the conjugation defect. -/
theorem delta_inv (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A) (u : P)
    (a : ↥A) :
    u⁻¹ * (a : P)⁻¹ * u * (a : P) = (u⁻¹ * (a : P) * u * (a : P)⁻¹)⁻¹ := by
  have h2 : u⁻¹ * (a : P)⁻¹ * u ∈ A := by
    simpa using hA.normal.conj_mem (a : P)⁻¹ (A.inv_mem a.2) u⁻¹
  have hcomm : (u⁻¹ * (a : P)⁻¹ * u) * (a : P) = (a : P) * (u⁻¹ * (a : P)⁻¹ * u) :=
    hA.abelian _ h2 _ a.2
  calc u⁻¹ * (a : P)⁻¹ * u * (a : P) = (u⁻¹ * (a : P)⁻¹ * u) * (a : P) := by group
    _ = (a : P) * (u⁻¹ * (a : P)⁻¹ * u) := hcomm
    _ = (u⁻¹ * (a : P) * u * (a : P)⁻¹)⁻¹ := by
        simp only [mul_inv_rev, inv_inv]
        group

/-- `δ_u(c) ∈ A⁴` for `c ∈ A²`. -/
theorem delta_mem_powSub_four (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    (u : P) {c : P} (hcA : c ∈ A) (hc : c ∈ powSub A 2) :
    u⁻¹ * c * u * c⁻¹ ∈ powSub A 4 := by
  obtain ⟨b, hbA, hb⟩ := (mem_powSub_iff hA.abelian).mp hc
  have hbmem : u⁻¹ * b * u * b⁻¹ ∈ powSub A 2 := by
    have hh := commutator_mem_powSub_two h hA u⁻¹ b hbA
    rwa [commutatorElement_def, inv_inv] at hh
  have h2 : u⁻¹ * (b * b) * u * (b * b)⁻¹
      = (u⁻¹ * b * u * b⁻¹) * (u⁻¹ * b * u * b⁻¹) :=
    delta_mul h hA u ⟨b, hbA⟩ ⟨b, hbA⟩
  have hpow : (u⁻¹ * b * u * b⁻¹) ^ 2 ∈ powSub (powSub A 2) 2 :=
    pow_mem_powSub (A := powSub A 2) (n := 2) hbmem
  have e4 : powSub (powSub A 2) 2 = powSub A 4 := by
    rw [powSub_powSub hA.abelian 2 2]
  rw [e4] at hpow
  rw [← hb, pow_two, h2, ← pow_two]
  exact hpow

/-- **Scalar step.**  A finite `T`-stable family of commuting idempotent endomorphisms of a
finite commutative group `V` of exponent two, closed under pointwise products, on which `T` acts
transitively on the non-identity elements, consists of scalars (`1` or `id`). -/
theorem scalar_endomorphism {V : Type} [CommGroup V] [Finite V]
    (hexp0 : ∀ v : V, v * v = 1)
    {ι : Type} [Fintype ι] (T : MulAut V)
    (htrans : ∀ x y : V, x ≠ 1 → y ≠ 1 → ∃ k : ℕ, (T ^ k) x = y)
    (f : ι → V →* V)
    (hpt : ∀ i j, ∃ k, f k = f i * f j)
    (hidem : ∀ i, (f i).comp (f i) = f i)
    (hinv : ∃ τ : ι ≃ ι, ∀ i, T.toMonoidHom.comp ((f i).comp T.symm.toMonoidHom) = f (τ i)) :
    ∀ i, (∀ x, f i x = 1) ∨ f i = MonoidHom.id V := by
  have hexp : ∀ v : V, v * v = 1 := hexp0
  have h2' : ∀ v : Additive V, (2 : ℕ) • v = 0 := by
    intro v
    rw [← ofMul_toMul v, ← ofMul_pow, ofMul_eq_zero, pow_two]
    exact hexp (Additive.toMul v)
  haveI hmod : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule h2'
  let σ : ι → Additive V →ₗ[ZMod 2] Additive V := fun i =>
    AddMonoidHom.toZModLinearMap 2
      { toFun := fun x => Additive.ofMul (f i (Additive.toMul x))
        map_zero' := by
          show Additive.ofMul (f i 1) = 0
          rw [map_one]
          rfl
        map_add' := fun x y => by
          show Additive.ofMul (f i (Additive.toMul (x + y))) =
            Additive.ofMul (f i (Additive.toMul x)) + Additive.ofMul (f i (Additive.toMul y))
          rw [show Additive.toMul (x + y) = Additive.toMul x * Additive.toMul y from rfl,
            map_mul]
          rfl }
  have hσidem : ∀ i, (σ i).comp (σ i) = σ i := by
    intro i
    ext x
    show Additive.ofMul (f i (f i (Additive.toMul x))) = Additive.ofMul (f i (Additive.toMul x))
    have h := congrArg (fun g : V →* V => g (Additive.toMul x)) (hidem i)
    rw [MonoidHom.comp_apply] at h
    rw [h]
  have hσadd : ∀ i j, ∃ k, σ k = σ i + σ j := by
    intro i j
    obtain ⟨k, hk⟩ := hpt i j
    refine ⟨k, ?_⟩
    ext x
    show Additive.ofMul (f k (Additive.toMul x)) =
      Additive.ofMul (f i (Additive.toMul x)) + Additive.ofMul (f j (Additive.toMul x))
    have h := congrArg (fun g : V →* V => g (Additive.toMul x)) hk
    rw [MonoidHom.mul_apply] at h
    rw [h]
    rfl
  let ξl : Additive V ≃ₗ[ZMod 2] Additive V :=
    LinearEquiv.ofBijective
      (AddMonoidHom.toZModLinearMap 2 (MulEquiv.toAdditive T).toAddMonoidHom)
      (MulEquiv.toAdditive T).bijective
  have hξapply : ∀ x : Additive V, ξl x = Additive.ofMul (T (Additive.toMul x)) := fun x => rfl
  have hξtrans : ∀ a b : Additive V, a ≠ 0 → b ≠ 0 → ∃ k : ℕ, (ξl ^ k) a = b := by
    intro a b ha hb
    have ha' : Additive.toMul a ≠ 1 := fun hc =>
      ha (by rw [← ofMul_toMul a, hc]; rfl)
    have hb' : Additive.toMul b ≠ 1 := fun hc =>
      hb (by rw [← ofMul_toMul b, hc]; rfl)
    obtain ⟨k, hk⟩ := htrans (Additive.toMul a) (Additive.toMul b) ha' hb'
    refine ⟨k, ?_⟩
    have h1 : ∀ n : ℕ, (ξl ^ n) a = Additive.ofMul ((T ^ n) (Additive.toMul a)) := by
      intro n
      induction n with
      | zero => rw [pow_zero, pow_zero]; rfl
      | succ n ih =>
        rw [pow_succ', pow_succ']
        show ξl ((ξl ^ n) a) = Additive.ofMul (T ((T ^ n) (Additive.toMul a)))
        rw [ih, hξapply, toMul_ofMul]
    rw [h1 k, hk, ofMul_toMul]
  have hσinv : ∃ τ : ι ≃ ι, ∀ i v, σ (τ i) (ξl v) = ξl (σ i v) := by
    obtain ⟨τ, hτ⟩ := hinv
    refine ⟨τ, ?_⟩
    intro i v
    show Additive.ofMul (f (τ i) (Additive.toMul (ξl v))) =
      Additive.ofMul (T (f i (Additive.toMul v)))
    rw [hξapply]
    show Additive.ofMul (f (τ i) (T (Additive.toMul v))) =
      Additive.ofMul (T (f i (Additive.toMul v)))
    have h := congrArg (fun g : V →* V => g (T (Additive.toMul v))) (hτ i)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at h
    rw [show (T.symm.toMonoidHom) (T (Additive.toMul v)) = Additive.toMul v from
      MulEquiv.symm_apply_apply T (Additive.toMul v)] at h
    show Additive.ofMul ((f (τ i)) (T (Additive.toMul v))) =
      Additive.ofMul ((MulEquiv.toMonoidHom T) ((f i) (Additive.toMul v)))
    rw [← h]
  have hmain := boolean_idempotent_family ξl hξtrans σ hσidem hσadd hσinv
  intro i
  rcases hmain i with h | h
  · left
    intro x
    have hx := congrArg (fun g : Additive V →ₗ[ZMod 2] Additive V => g (Additive.ofMul x)) h
    simp only [LinearMap.zero_apply] at hx
    have hx2 : Additive.ofMul (f i x) = 0 := hx
    exact ofMul_eq_zero.mp hx2
  · right
    ext x
    have hx := congrArg (fun g : Additive V →ₗ[ZMod 2] Additive V => g (Additive.ofMul x)) h
    simp only [LinearMap.id_apply] at hx
    have hx2 : Additive.ofMul (f i x) = Additive.ofMul x := hx
    exact (fun (hh : Additive.ofMul (f i x) = Additive.ofMul x) => by
      simpa using congrArg Additive.toMul hh) hx2


/-- **Higman 1963, Lemma 3.** Let `A` be a normal abelian `ξ`-subgroup of a Suzuki 2-group `P`
and `C > A` a normal `ξ`-subgroup covering `A` (`C/A` a minimal normal `ξ`-section). If
`Φ(C) = C²[C,C] = A²` (equivalently `powSub C 2 ⊔ ⁅C,C⁆ = powSub A 2`), then `A` has exponent
dividing `4`. -/
theorem clo_lemma3 {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hPhi : Work.Higman.powSub C 2 ⊔ ⁅C, C⁆ = Work.Higman.powSub A 2) :
    ∀ a ∈ A, a ^ 4 = 1 := by
  classical
  have hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.abelian
  rcases eq_or_ne A ⊥ with hbot | hAne
  · subst hbot
    intro a ha
    rw [Subgroup.mem_bot] at ha
    subst ha
    simp
  have hOm : omega1 P ≤ A := omega1_le_of_isXiAbelNormal_ne_bot h hA hAne
  by_contra hcon
  push_neg at hcon
  obtain ⟨a0, ha0A, ha0⟩ := hcon
  obtain ⟨D⟩ := exists_homocyclicData h hA
  have h3 : 3 ≤ D.e := by
    by_contra hlt
    push_neg at hlt
    refine ha0 ?_
    have hle : D.e ≤ 2 := by omega
    have hd : 2 ^ D.e ∣ 4 := by
      calc 2 ^ D.e ∣ 2 ^ 2 := Nat.pow_dvd_pow 2 hle
        _ = 4 := by norm_num
    obtain ⟨t, ht⟩ := hd
    rw [ht, pow_mul, D.hexp a0 ha0A, one_pow]
  have hC2 : powSub C 2 ≤ powSub A 2 := by rw [← hPhi]; exact le_sup_left
  have hsqrt4 : ∀ x ∈ A, x ^ 2 ∈ powSub A 4 → x ∈ powSub A 2 :=
    fun x hx hh => mem_powSub_two_of_sq_mem_powSub_four h hA D h3 hx hh
  have h4pow : ∀ x ∈ A, x ^ 4 = 1 → x ∈ powSub A 2 :=
    fun x hx hh => mem_powSub_two_of_pow_four_eq_one h hA D h3 hx hh
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
    exact powSub_le (A := A) (n := 2) (by norm_num) (hC2 h1)
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
  have hkey : ∀ (u : ↥C) (y : ↥A), (rt u y * rt u (rt u y)) ^ 4 = 1 := by
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
    have h4 := hkey u a
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
  have hker1 : ∀ u : ↥C, (∀ x : (↥A ⧸ K), NB u x = 1) → (u : P) ∈ A := by
    intro u hz
    by_contra huA
    have h4 : ∀ a ∈ A, ⁅(u:P)⁻¹, a⁆ ∈ powSub A 4 := by
      intro a ha
      have h1 : NB u (QuotientGroup.mk (⟨a, ha⟩ : ↥A)) = 1 := hz _
      rw [NB_apply, nbf_mk, QuotientGroup.eq_one_iff, hKmem] at h1
      have h3 : ((del u ⟨a, ha⟩ : ↥A) : P) ∈ powSub A 4 := by
        rw [← rt_sq u ⟨a, ha⟩, Subgroup.coe_pow, ← powSub_powSub hAb 2 2]
        exact pow_mem_powSub (A := powSub A 2) (n := 2) h1
      rw [commutatorElement_def, inv_inv]
      simpa [del_coe] using h3
    exact (higman_lemma2 h hA hOm hAne (by
        intro hinv
        exact huA (by simpa using A.inv_mem hinv)) ⟨by
        rw [inv_pow]
        exact (powSub A 2).inv_mem (hC2 (pow_mem_powSub (A := C) (n := 2) u.2)), h4⟩)
  have hker2 : ∀ u : ↥C, (u : P) ∈ A → (∀ x : (↥A ⧸ K), NB u x = 1) := by
    intro u hu x
    refine Quotient.inductionOn x (fun a => ?_)
    rw [NB_apply, nbf_mk, QuotientGroup.eq_one_iff, hKmem]
    have hdel : del u a = 1 := by
      refine Subtype.ext ?_
      simp only [del_coe, Subgroup.coe_one]
      rw [show (u:P)⁻¹ * (a:P) * (u:P) * (a:P)⁻¹
          = (u:P)⁻¹ * ((a:P) * (u:P)) * (a:P)⁻¹ from by group,
        show (a:P) * (u:P) = (u:P) * (a:P) from (hAb (u:P) hu (a:P) a.2).symm]
      group
    have h1 : (rt u a) ^ 2 = 1 := by rw [rt_sq, hdel]
    exact hsqrt4 _ (rt u a).2 (by rw [← Subgroup.coe_pow, h1]; exact Subgroup.one_mem _)
  obtain ⟨u0, hu0C, hu0A⟩ : ∃ u ∈ C, u ∉ A := by
    by_contra hc
    push_neg at hc
    exact hCA (le_antisymm hAC (fun x hx => hc x hx))
  have hid0 : NB ⟨u0, hu0C⟩ = MonoidHom.id (↥A ⧸ K) := by
    rcases hscalar ⟨u0, hu0C⟩ with hc | hc
    · exact absurd (hker1 ⟨u0, hu0C⟩ hc) hu0A
    · exact hc
  have hdich : ∀ u ∈ C, ∀ v ∈ C, u ∉ A → v ∉ A → u * v ∈ A := by
    intro u huC v hvC huA hvA
    have hu' : NB ⟨u, huC⟩ = MonoidHom.id (↥A ⧸ K) := by
      rcases hscalar ⟨u, huC⟩ with hc | hc
      · exact absurd (hker1 ⟨u, huC⟩ hc) huA
      · exact hc
    have hv' : NB ⟨v, hvC⟩ = MonoidHom.id (↥A ⧸ K) := by
      rcases hscalar ⟨v, hvC⟩ with hc | hc
      · exact absurd (hker1 ⟨v, hvC⟩ hc) hvA
      · exact hc
    have hprod : NB ⟨u * v, C.mul_mem huC hvC⟩ = NB ⟨u, huC⟩ * NB ⟨v, hvC⟩ := by
      ext x
      exact nbf_mul_u ⟨u, huC⟩ ⟨v, hvC⟩ x
    have hone : (NB ⟨u, huC⟩ * NB ⟨v, hvC⟩ : (↥A ⧸ K) →* (↥A ⧸ K)) = 1 := by
      rw [hu', hv']
      ext x
      exact hVexp x
    exact hker1 ⟨u * v, C.mul_mem huC hvC⟩ (by rw [hprod, hone]; intro x; rfl)
  have htriv0 : h.xi u0 * u0⁻¹ ∈ A := by
    have hu0sq : u0 * u0 ∈ A := by
      have h1 : (u0:P) * (u0:P) ∈ powSub C 2 := by
        rw [← pow_two]; exact pow_mem_powSub (A := C) (n := 2) hu0C
      exact powSub_le (A := A) (n := 2) (by norm_num) (hC2 h1)
    have hxC : h.xi u0 ∈ C := by
      have hm := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom hu0C
      rwa [hCinv] at hm
    have hne : h.xi u0 ∉ A := by
      intro hcon
      exact hu0A (by simpa using symm_mem_of_map_eq h.xi hA.map_eq hcon)
    have hΞ : h.xi u0 * u0 ∈ A := hdich (h.xi u0) hxC u0 hu0C hne hu0A
    rw [show u0⁻¹ = u0 * (u0 * u0)⁻¹ from by group, ← mul_assoc]
    exact A.mul_mem hΞ (A.inv_mem hu0sq)
  have hnu0 : ∀ a ∈ A, ∃ x ∈ A, x * x = (u0:P)⁻¹ * a * u0 * a⁻¹ ∧ x * a⁻¹ ∈ powSub A 2 := by
    intro a ha
    refine ⟨((rt ⟨u0, hu0C⟩ ⟨a, ha⟩ : ↥A) : P), (rt ⟨u0, hu0C⟩ ⟨a, ha⟩).2, ?_, ?_⟩
    · have hh := congrArg (fun t : ↥A => (t : P)) (rt_sq ⟨u0, hu0C⟩ ⟨a, ha⟩)
      simp only [Subgroup.coe_pow, del_coe] at hh
      rwa [pow_two] at hh
    · have h1 : NB ⟨u0, hu0C⟩ (QuotientGroup.mk (⟨a, ha⟩ : ↥A))
          = QuotientGroup.mk (⟨a, ha⟩ : ↥A) := by
        rw [hid0]; rfl
      rw [NB_apply, nbf_mk, QuotientGroup.eq] at h1
      have h3 : ((rt ⟨u0, hu0C⟩ ⟨a, ha⟩ : ↥A))⁻¹ * (⟨a, ha⟩ : ↥A) ∈ K := h1
      have h4 : ((rt ⟨u0, hu0C⟩ ⟨a, ha⟩ : ↥A)) * ((⟨a, ha⟩ : ↥A))⁻¹ ∈ K := by
        have heq : ((rt ⟨u0, hu0C⟩ ⟨a, ha⟩ : ↥A)) * ((⟨a, ha⟩ : ↥A))⁻¹
            = (((rt ⟨u0, hu0C⟩ ⟨a, ha⟩ : ↥A))⁻¹ * (⟨a, ha⟩ : ↥A))⁻¹ := by
          rw [mul_inv_rev, inv_inv]
          exact mul_comm _ _
        rw [heq]
        exact K.inv_mem h3
      rw [hKmem] at h4
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h4
  exact higman_lemma3_last_step h hA hOm hC2 hu0C hu0A htriv0 hnu0

end Work.Higman

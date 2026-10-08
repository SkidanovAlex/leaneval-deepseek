import Mathlib
import Submission.Work.Higman.clo_hard_defs
import Submission.Work.Higman.clo_sM_aux
import Submission.Work.Higman.h8_trivial_action_quot
import Submission.Work.Higman.CommAux.card_and_transitive_of_simple_mul
import Submission.Work.Higman.Fq_structure
import Submission.Work.Higman.bracket_expansion
import Submission.Work.Higman.squaring_layer
import Submission.Work.Higman.commutator_powSub_A_C
import Submission.Work.Higman.MSA.l8_exp_data
import Submission.Work.Higman.xi_trans_quot_sq
import Submission.Work.Higman.H8.cloXiQuot_irreducible
import Submission.Work.Higman.H8.bracket_radical

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped commutatorElement

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-! ## Auxiliary lemmas for the structural package of Higman's Lemma 8 -/

/-- **`ξ` acts regularly on `Ω₁(P) ∖ {1}`.**  Since `⟨ξ⟩` is abelian and `ξ` is transitive on the
involutions, an element `ξ ^ k` fixing one non-identity element of `Ω₁(P)` fixes all of them. -/
theorem cloXiOm_fixes_all (h : IsSuzuki2Grp P) {k : ℕ} {z : ↥(omega1 P)} (hz : z ≠ 1)
    (hfix : ((cloXiOm h) ^ k) z = z) : (cloXiOm h) ^ k = 1 := by
  refine MulEquiv.ext (fun w => ?_)
  rcases eq_or_ne w 1 with hw | hw
  · subst hw; rw [map_one, map_one]
  · obtain ⟨j, hj⟩ := cloXiOm_trans h hz hw
    calc ((cloXiOm h) ^ k) w = ((cloXiOm h) ^ k) (((cloXiOm h) ^ j) z) := by rw [hj]
      _ = ((cloXiOm h) ^ (k + j)) z := by rw [pow_add, MulAut.mul_apply]
      _ = ((cloXiOm h) ^ (j + k)) z := by rw [Nat.add_comm]
      _ = ((cloXiOm h) ^ j) (((cloXiOm h) ^ k) z) := by rw [pow_add, MulAut.mul_apply]
      _ = ((cloXiOm h) ^ j) z := by rw [hfix]
      _ = w := hj

/-- **The order of the automorphism induced by `ξ` on `Ω₁(P)`.**  By the regularity above, the
orbit of any non-identity element of `Ω₁(P)` has exactly `orderOf (cloXiOm h)` elements, and it is
the set of all non-identity elements; hence the order equals the number of involutions. -/
theorem cloXiOm_orderOf (h : IsSuzuki2Grp P) :
    orderOf (cloXiOm h) = (Invol P).ncard := by
  classical
  have hfin : IsOfFinOrder (cloXiOm h) := isOfFinOrder_of_finite _
  obtain ⟨x₀, y₀, hx₀, hy₀, hxy₀⟩ := h.manyInvol
  have hx₀sq : x₀ ^ 2 = 1 := by rw [← orderOf_dvd_iff_pow_eq_one, hx₀]
  let z : ↥(omega1 P) := ⟨x₀, (h.mem_omega1).mpr hx₀sq⟩
  have hz1 : z ≠ 1 := by
    intro hc
    have hx1 : x₀ = 1 := congrArg Subtype.val hc
    rw [hx1, orderOf_one] at hx₀
    exact absurd hx₀ (by norm_num)
  have hmaps : ∀ ψ : ↥(Subgroup.zpowers (cloXiOm h)),
      (((ψ : MulAut ↥(omega1 P)) z : ↥(omega1 P)) : P) ∈ Invol P := by
    intro ψ
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp
      ((IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf hfin).mp ψ.2)
    rw [mem_Invol]
    have hne : ((ψ : MulAut ↥(omega1 P)) z : ↥(omega1 P)) ≠ 1 := by
      rw [show (ψ : MulAut ↥(omega1 P)) = (cloXiOm h) ^ k from hk.symm]
      intro hc
      have h2 : ((cloXiOm h) ^ k) z = ((cloXiOm h) ^ k) 1 := by rw [hc, map_one]
      exact hz1 (((cloXiOm h) ^ k).injective h2)
    have hne' : (((ψ : MulAut ↥(omega1 P)) z : ↥(omega1 P)) : P) ≠ 1 :=
      fun hc => hne (Subtype.ext hc)
    exact orderOf_eq_two_of_mem_omega1 h ((ψ : MulAut ↥(omega1 P)) z).2 hne'
  let F : Subgroup.zpowers (cloXiOm h) → Invol P :=
    fun ψ => ⟨((ψ : MulAut ↥(omega1 P)) z : ↥(omega1 P)), hmaps ψ⟩
  have hFval : ∀ ψ : Subgroup.zpowers (cloXiOm h),
      ((F ψ : Invol P) : P) = ((ψ : MulAut ↥(omega1 P)) z : P) := fun _ => rfl
  have hinj : Function.Injective F := by
    intro ψ ψ' hEq
    have hval : ((ψ : MulAut ↥(omega1 P)) z) = ((ψ' : MulAut ↥(omega1 P)) z) := by
      apply Subtype.ext
      rw [← hFval ψ, ← hFval ψ', hEq]
    obtain ⟨χ, hχ⟩ : ∃ χ : Subgroup.zpowers (cloXiOm h),
        (χ : MulAut ↥(omega1 P))
          = (ψ' : MulAut ↥(omega1 P))⁻¹ * (ψ : MulAut ↥(omega1 P)) :=
      ⟨⟨(ψ' : MulAut ↥(omega1 P))⁻¹ * ψ,
        Subgroup.mul_mem _ (Subgroup.inv_mem _ ψ'.2) ψ.2⟩, rfl⟩
    obtain ⟨m, -, hm⟩ := Finset.mem_image.mp
      ((IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf hfin).mp χ.2)
    have hfix : ((cloXiOm h) ^ m) z = z := by
      rw [hm, hχ]
      show ((ψ' : MulAut ↥(omega1 P))⁻¹ * (ψ : MulAut ↥(omega1 P))) z = z
      rw [MulAut.mul_apply, hval]
      exact MulEquiv.symm_apply_apply (ψ' : MulAut ↥(omega1 P)) z
    have h1 : (cloXiOm h) ^ m = 1 := cloXiOm_fixes_all h hz1 hfix
    have h2 : (χ : MulAut ↥(omega1 P)) = 1 := by rw [← hm, h1]
    have h3 : (ψ' : MulAut ↥(omega1 P))⁻¹ * ψ = 1 := by rw [← hχ, h2]
    have h4 : (ψ : MulAut ↥(omega1 P)) = (ψ' : MulAut ↥(omega1 P)) := by
      calc (ψ : MulAut ↥(omega1 P))
          = (ψ' : MulAut ↥(omega1 P))
            * ((ψ' : MulAut ↥(omega1 P))⁻¹ * (ψ : MulAut ↥(omega1 P))) := by group
        _ = (ψ' : MulAut ↥(omega1 P)) * 1 := by rw [h3]
        _ = (ψ' : MulAut ↥(omega1 P)) := by rw [mul_one]
    exact Subtype.ext h4
  have hsurj : Function.Surjective F := by
    intro w
    obtain ⟨k, hk⟩ := h.trans x₀ (w : P) hx₀ w.2
    refine ⟨⟨(cloXiOm h) ^ k, Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k⟩, ?_⟩
    apply Subtype.ext
    show (((cloXiOm h) ^ k) z : P) = (w : P)
    rw [cloXiOm_pow_apply]
    rw [show (z : P) = x₀ from rfl, hk]
  have hcard : Nat.card ↥(Subgroup.zpowers (cloXiOm h)) = (Invol P).ncard := by
    rw [Nat.card_congr (Equiv.ofBijective F ⟨hinj, hsurj⟩), Nat.card_coe_set_eq]
  rwa [Nat.card_zpowers] at hcard

/-- **A power of `ξ` trivial on `Ω₁(P)` is trivial on `A / A²`.**  Under the data of Higman's
Lemma 8, `(ξ ^ k) a · a⁻¹ ∈ A ^ (2)` for every `a ∈ A`. -/
theorem xi_pow_triv_powSub_two (h : IsSuzuki2Grp P) {A C : Subgroup P} [hAn : A.Normal]
    (S : CloH8Data h A C) {k : ℕ} (hk : (cloXiOm h) ^ k = 1) :
    ∀ a ∈ A, (h.xi ^ k) a * a⁻¹ ∈ powSub A 2 := by
  intro a ha
  have hfix : ∀ zz : P, zz ∈ omega1 P → (h.xi ^ k) zz = zz := by
    intro zz hz
    have h1 : ((cloXiOm h) ^ k) ⟨zz, hz⟩ = ⟨zz, hz⟩ := by rw [hk]; rfl
    have h2 := congrArg Subtype.val h1
    rwa [cloXiOm_pow_apply] at h2
  have hxA : (h.xi ^ k) a ∈ A := apply_xi_pow_mem h S.hA.map_eq k ha
  have hmA : (h.xi ^ k) a * a⁻¹ ∈ A := A.mul_mem hxA (A.inv_mem ha)
  refine (S.hkey _ hmA).mpr ?_
  have hcomm : Commute ((h.xi ^ k) a) a⁻¹ :=
    (commute_iff_eq _ _).mpr (S.hA.abelian _ hxA _ (A.inv_mem ha))
  rw [hcomm.mul_pow, ← map_pow, inv_pow]
  have hk2 : 2 ^ (S.e - 1) * 2 = 2 ^ S.e := by
    rw [← pow_succ, Nat.sub_add_cancel S.he]
  have hmem : a ^ 2 ^ (S.e - 1) ∈ omega1 P := by
    rw [h.mem_omega1, ← pow_mul, hk2]
    exact S.he1 a ha
  rw [hfix _ hmem, mul_inv_cancel]

/-- **A power of `ξ` trivial on `Ω₁(P)` is trivial on `A² / A⁴`.**  Under the data of Higman's
Lemma 8, `(ξ ^ k) a · a⁻¹ ∈ A ^ (4)` for every `a ∈ A ^ (2)`. -/
theorem xi_pow_triv_powSub_four (h : IsSuzuki2Grp P) {A C : Subgroup P} [hAn : A.Normal]
    (S : CloH8Data h A C) {k : ℕ} (hk : (cloXiOm h) ^ k = 1) :
    ∀ a ∈ powSub A 2, (h.xi ^ k) a * a⁻¹ ∈ powSub A 4 := by
  intro a ha2
  have hfix : ∀ zz : P, zz ∈ omega1 P → (h.xi ^ k) zz = zz := by
    intro zz hz
    have h1 : ((cloXiOm h) ^ k) ⟨zz, hz⟩ = ⟨zz, hz⟩ := by rw [hk]; rfl
    have h2 := congrArg Subtype.val h1
    rwa [cloXiOm_pow_apply] at h2
  have hA2inv : (powSub A 2).map (h.xi : MulAut P).toMonoidHom = powSub A 2 :=
    map_powSub (h.xi : MulAut P) S.hA.map_eq 2
  have hxA : (h.xi ^ k) a ∈ powSub A 2 := apply_xi_pow_mem h hA2inv k ha2
  have hmA2 : (h.xi ^ k) a * a⁻¹ ∈ powSub A 2 :=
    (powSub A 2).mul_mem hxA ((powSub A 2).inv_mem ha2)
  refine (powSub_four_ker h S.hA S.he1 S.hkey hmA2).mpr ?_
  have hcomm : Commute ((h.xi ^ k) a) a⁻¹ :=
    (commute_iff_eq _ _).mpr (S.hA.abelian _ (powSub_le (by norm_num) hxA) _
      (A.inv_mem (powSub_le (by norm_num) ha2)))
  rw [hcomm.mul_pow, ← map_pow, inv_pow]
  have hk2 : 2 * 2 ^ (S.e - 2) = 2 ^ (S.e - 1) := by
    have he2 : 2 ≤ S.e := S.he2
    rw [← pow_succ']; congr 1; omega
  have hk3 : 2 ^ (S.e - 1) * 2 = 2 ^ S.e := by
    rw [← pow_succ, Nat.sub_add_cancel S.he]
  have hmem : a ^ 2 ^ (S.e - 2) ∈ omega1 P := by
    obtain ⟨dd, hdd, hdd2⟩ := (mem_powSub_iff S.hA.abelian).mp ha2
    rw [← hdd2, h.mem_omega1]
    rw [show (dd ^ 2) ^ 2 ^ (S.e - 2) = dd ^ 2 ^ (S.e - 1) from by rw [← pow_mul, hk2]]
    rw [← pow_mul, hk3]
    exact S.he1 dd hdd
  rw [hfix _ hmem, mul_inv_cancel]

/-- **The bracket computation.**  If a power of `ξ` is trivial on `Ω₁(P)`, then the element
`d = (ξ ^ k) u · u⁻¹` (for `u ∈ C`) commutes with every `a ∈ A` modulo `A ^ (4)`. -/
theorem xi_pow_k_bracket_mem_powSub_four (h : IsSuzuki2Grp P) {A C : Subgroup P} [hAn : A.Normal]
    (S : CloH8Data h A C) {k : ℕ} (hk : (cloXiOm h) ^ k = 1) {u : P} (hu : u ∈ C) :
    ∀ a ∈ A, ((h.xi ^ k) u * u⁻¹) * a * ((h.xi ^ k) u * u⁻¹)⁻¹ * a⁻¹ ∈ powSub A 4 := by
  intro a ha
  have hgen : ∀ a' ∈ A, ((h.xi ^ k) u * u⁻¹) * ((h.xi ^ k) a')
      * ((h.xi ^ k) u * u⁻¹)⁻¹ * ((h.xi ^ k) a')⁻¹ ∈ powSub A 4 := by
    intro a' ha'
    set d : P := (h.xi ^ k) u * u⁻¹ with hd
    set e : P := (h.xi ^ k) a' * a'⁻¹ with he
    have hdC : d ∈ C := C.mul_mem (apply_xi_pow_mem h S.hCinv k hu) (C.inv_mem hu)
    have heA2 : e ∈ powSub A 2 := xi_pow_triv_powSub_two h S hk a' ha'
    have heA : e ∈ A := powSub_le (by norm_num) heA2
    have hdu : (h.xi ^ k) u = d * u := by rw [hd]; group
    have hea : (h.xi ^ k) a' = e * a' := by rw [he]; group
    have hua2 : ⁅u, a'⁆ ∈ powSub A 2 := commutator_mem_powSub_two h S.hA u a' ha'
    have hIII : (h.xi ^ k) ⁅u, a'⁆ * ⁅u, a'⁆⁻¹ ∈ powSub A 4 :=
      xi_pow_triv_powSub_four h S hk ⁅u, a'⁆ hua2
    have hIV : (h.xi ^ k) ⁅u, a'⁆ = ⁅d * u, e * a'⁆ := by
      have hdu' : ((h.xi ^ k : MulAut P).toMonoidHom) u = d * u := hdu
      have hea' : ((h.xi ^ k : MulAut P).toMonoidHom) a' = e * a' := hea
      have h1 := map_commutatorElement ((h.xi ^ k : MulAut P)).toMonoidHom u a'
      rw [hdu', hea'] at h1
      exact h1
    have hZ1 : ⁅d * u, e * a'⁆ * ⁅u, a'⁆⁻¹ ∈ powSub A 4 := by rw [← hIV]; exact hIII
    have hI : ⁅d * u, e * a'⁆ * (⁅d, e * a'⁆ * ⁅u, e * a'⁆)⁻¹ ∈ powSub A 4 :=
      bracket_mul_left h S.hA S.hCn S.hCd S.hC2 hdC hu (A.mul_mem heA ha')
    have hII : ⁅u, e * a'⁆ * ⁅u, a'⁆⁻¹ ∈ powSub A 4 := by
      rw [bracket_mul_right h S.hA S.hCd hu heA ha']
      have hMA : ⁅u, e⁆ ∈ powSub A 4 := by
        have hstep := commutator_powSub_A_C h S.hA S.hCn S.hC2 S.hCd 1
        rw [show (2 : ℕ) ^ 1 = 2 from by norm_num,
          show (2 : ℕ) ^ (1 + 1) = 4 from by norm_num] at hstep
        rw [← hstep, Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator hu heA2
      rw [mul_assoc, mul_inv_cancel, mul_one]
      exact hMA
    have hkey : ⁅d, e * a'⁆ = (⁅d * u, e * a'⁆ * (⁅d, e * a'⁆ * ⁅u, e * a'⁆)⁻¹)⁻¹
        * (⁅d * u, e * a'⁆ * ⁅u, a'⁆⁻¹) * (⁅u, e * a'⁆ * ⁅u, a'⁆⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [hea]
    rw [show d * (e * a') * d⁻¹ * (e * a')⁻¹ = ⁅d, e * a'⁆ from
      (commutatorElement_def d (e * a')).symm, hkey]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ hI) hZ1) (Subgroup.inv_mem _ hII)
  have hinv : (h.xi ^ k : MulAut P).symm a ∈ A :=
    symm_mem_of_map_eq (h.xi ^ k) (map_xi_pow_eq h S.hA.map_eq k) ha
  have hkey := hgen ((h.xi ^ k : MulAut P).symm a) hinv
  rwa [MulEquiv.apply_symm_apply] at hkey

/-- **The radical of the bracket pairing is trivial, transported.**  If a power of `ξ` is trivial
on `Ω₁(P)` then `(ξ ^ k) u · u⁻¹ ∈ A` for every `u ∈ C`. -/
theorem xi_pow_k_mul_inv_mem_A (h : IsSuzuki2Grp P) {A C : Subgroup P} [hAn : A.Normal]
    (S : CloH8Data h A C) {k : ℕ} (hk : (cloXiOm h) ^ k = 1) {u : P} (hu : u ∈ C) :
    (h.xi ^ k) u * u⁻¹ ∈ A :=
  H8.bracket_radical h S (C.mul_mem (apply_xi_pow_mem h S.hCinv k hu) (C.inv_mem hu))
    (xi_pow_k_bracket_mem_powSub_four h S hk hu)

/-- `cloXiQuot` on the class of a representative, for powers. -/
theorem cloXiQuot_pow_mk (h : IsSuzuki2Grp P) {A C : Subgroup P} [hAn : A.Normal]
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) (k : ℕ) (u : ↥C) :
    ((cloXiQuot h hAinv hCinv) ^ k) (QuotientGroup.mk u)
      = QuotientGroup.mk ((cloXiC h hCinv ^ k) u) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, ih]
    rw [show (cloXiC h hCinv) ^ (k + 1) = cloXiC h hCinv * (cloXiC h hCinv) ^ k
      from pow_succ' _ _, MulAut.mul_apply]
    exact cloXiQuot_mk h hAinv hCinv (((cloXiC h hCinv) ^ k) u)

/-- **The order of the automorphism of `C/A` induced by `ξ`.** -/
theorem orderOf_cloXiQuot (h : IsSuzuki2Grp P) {A C : Subgroup P} [hAn : A.Normal]
    (S : CloH8Data h A C) :
    orderOf (cloXiQuot h S.hA.map_eq S.hCinv) = Nat.card ↥(omega1 P) - 1 := by
  set q : ℕ := Nat.card ↥(omega1 P) - 1 with hq
  have horder : orderOf (cloXiOm h) = q := by
    rw [cloXiOm_orderOf, hq, h.card_omega1, Nat.add_sub_cancel]
  have hfixq : (cloXiOm h) ^ q = 1 := by
    rw [← horder]; exact pow_orderOf_eq_one _
  have hdir1 : (cloXiQuot h S.hA.map_eq S.hCinv) ^ q = 1 := by
    refine MulEquiv.ext (fun x => ?_)
    show ((cloXiQuot h S.hA.map_eq S.hCinv) ^ q) x = x
    induction x using QuotientGroup.induction_on with
    | _ u =>
      rw [cloXiQuot_pow_mk h S.hA.map_eq S.hCinv q u]
      apply QuotientGroup.eq.mpr
      rw [Subgroup.mem_subgroupOf]
      have hval : (((cloXiC h S.hCinv ^ q) u : ↥C) : P) = (h.xi ^ q) u :=
        cloXiSub_pow_apply h S.hCinv q u
      have hdA : (h.xi ^ q) u * u⁻¹ ∈ A := xi_pow_k_mul_inv_mem_A h S hfixq u.2
      show ((((cloXiC h S.hCinv ^ q) u : ↥C) : P))⁻¹ * (u : P) ∈ A
      rw [hval]
      have hconj : ((h.xi ^ q) u)⁻¹ * (u : P)
          = (u : P)⁻¹ * ((h.xi ^ q) u * (u : P)⁻¹)⁻¹ * (u : P) := by group
      rw [hconj]
      simpa using S.hA.normal.conj_mem _ (A.inv_mem hdA) (u : P)⁻¹
  have hdvd1 : orderOf (cloXiQuot h S.hA.map_eq S.hCinv) ∣ q :=
    orderOf_dvd_iff_pow_eq_one.mpr hdir1
  have hdvd2 : q ∣ orderOf (cloXiQuot h S.hA.map_eq S.hCinv) := by
    rw [← horder, orderOf_dvd_iff_pow_eq_one]
    obtain ⟨y, hy⟩ := cloSM_exists_ne_one S
    have hpow : (cloXiQuot h S.hA.map_eq S.hCinv)
        ^ (orderOf (cloXiQuot h S.hA.map_eq S.hCinv)) = 1 := pow_orderOf_eq_one _
    have hfix : ((cloXiOm h) ^ (orderOf (cloXiQuot h S.hA.map_eq S.hCinv))) (cloSM S y)
        = cloSM S y := by
      rw [cloSM_xi_pow, hpow]; rfl
    exact cloXiOm_fixes_all h hy hfix
  exact Nat.dvd_antisymm hdvd1 hdvd2

/-- **Structural package for the hard case of Higman's Lemma 8.**  In the situation of
`CloH8Data` (Higman's Lemma 8 with `A ≠ ⊥` and `A² ≠ ⊥`), the layer modules `C/A` and `Ω₁(P)` have
the same order `2 ^ n` (`n ≥ 2`), `ξ` acts transitively on the non-identity elements of each, and
the `2 ^ e`-th power map `cloSM : C/A → Ω₁(P)` is anisotropic.

Route.  `ξ` is transitive on `Ω₁(P) ∖ {1}` (`cloXiOm_trans`) and `⟨ξ⟩` is abelian, so its action
is regular and `orderOf (cloXiOm h) = |Ω₁(P)| - 1`.  Then `ξ ^ (|Ω₁|-1)` is trivial on `A/A²`
(transport along the `ξ`-equivariant bijection `a ↦ a ^ 2 ^ (e-1) : A/A² → Ω₁`) and on `A²/A⁴`
(transport along squaring); the bracket pairing `⌊uA, aA²⌋ = ⁅u,a⁆ · A⁴` is well defined with
trivial radical (`hcover` plus `A² ≠ ⊥`), whence `ξ ^ (|Ω₁|-1)` is trivial on `C/A`; conversely a
power of `ξ` trivial on `C/A` is trivial on `Ω₁` (via the non-zero values of `cloSM` and
transitivity on `Ω₁`), so `orderOf (cloXiQuot …) = |Ω₁(P)| - 1`.  `C/A` is a simple `𝔽₂⟨ξ⟩`-module
(`hcover` plus the trivial action `⁅⊤,C⁆ ≤ A` of `h8_trivial_action_quot`, which makes every
subgroup between `A` and `C` normal in `P`), so `CommAux.card_and_transitive_of_simple_mul` gives
`|C/A| = 2 ^ n` and transitivity.  Anisotropy of `cloSM` follows from transitivity on `C/A`
together with `cloSM_exists_ne_one`. -/
theorem h8_struct {P : Type} [Group P] [Finite P] (h : IsSuzuki2Grp P) {A C : Subgroup P}
    [A.Normal] (S : CloH8Data h A C) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card ↥(omega1 P) = 2 ^ n ∧
      Nat.card (↥C ⧸ (A.subgroupOf C)) = 2 ^ n ∧
      (∀ a b : ↥C ⧸ (A.subgroupOf C), a ≠ 1 → b ≠ 1 →
        ∃ k : ℕ, ((cloXiQuot h S.hA.map_eq S.hCinv) ^ k) a = b) ∧
      (∀ a b : ↥(omega1 P), a ≠ 1 → b ≠ 1 → ∃ k : ℕ, ((cloXiOm h) ^ k) a = b) ∧
      (∀ x : ↥C ⧸ (A.subgroupOf C), cloSM S x = 1 → x = 1) := by
  classical
  obtain ⟨n, hn⟩ := h.exists_card_omega1_eq_two_pow
  have h4 : 4 ≤ Nat.card ↥(omega1 P) := h.omega1_card_ge_four
  have hn2 : 2 ≤ n := by
    by_contra hc
    push Not at hc
    have hle : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hn] at h4
    norm_num at hle
    omega
  have hord : orderOf (cloXiQuot h S.hA.map_eq S.hCinv) = 2 ^ n - 1 := by
    rw [orderOf_cloXiQuot h S, hn]
  have hV2 : ∀ v : ↥C ⧸ (A.subgroupOf C), v * v = 1 := fun v => cloQuot_sq_one S.hC2 v
  letI hQc : CommGroup (↥C ⧸ (A.subgroupOf C)) :=
    { (inferInstance : Group (↥C ⧸ (A.subgroupOf C))) with mul_comm := cloQuot_comm S.hCd }
  obtain ⟨hVcard, hVtrans⟩ :=
    CommAux.card_and_transitive_of_simple_mul hn2 hV2 (cloXiQuot h S.hA.map_eq S.hCinv)
      (H8.cloXiQuot_irreducible h S) hord
  refine ⟨n, hn2, hn, hVcard, hVtrans, fun a b ha hb => cloXiOm_trans h ha hb, ?_⟩
  intro x hx
  by_contra hx1
  obtain ⟨y, hy⟩ := cloSM_exists_ne_one S
  have hy1 : y ≠ 1 := fun hc => hy (by rw [hc, cloSM_one])
  obtain ⟨k, hk⟩ := hVtrans x y hx1 hy1
  have h2 : cloSM S y = 1 := by
    have h1 : cloSM S (((cloXiQuot h S.hA.map_eq S.hCinv) ^ k) x)
        = ((cloXiOm h) ^ k) (cloSM S x) := (cloSM_xi_pow S k x).symm
    rw [hk] at h1
    rw [hx, map_one] at h1
    exact h1
  exact hy h2

end Work.Higman

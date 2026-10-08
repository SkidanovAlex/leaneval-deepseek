import Mathlib
import Submission.Work.DSTR.invTrickAbelian
import Submission.Work.DSTR.invTrickPre
import Submission.Work.DSTR.invTrickCombine
import Submission.Work.DSTR.centralizer_map_eq_of_odd_card

/-!
# `Work.DSTR.invTrickSolvable`

The inversion trick for finite solvable groups of odd order: if `τ` is an involution of `F`
inverting `ξ`, if `ξ` has odd order coprime to `|F|`, and if every `τ`-fixed element is
`ξ`-fixed, then `ξ = 1`.

The proof is by strong induction on `|F|`, using `N = [F,F]`:
* the abelian case is `Work.DSTR.invTrickAbelian`;
* on the abelian quotient `F/[F,F]` the abelian case gives `ξ` trivial mod `[F,F]`
  (`Work.DSTR.invTrickAbelianQuot`), the fixed points of `τ` descending to the quotient;
* the induction hypothesis applies to the characteristic subgroup `[F,F]`;
* `Work.DSTR.invTrickCombine` assembles the two.
-/

namespace Work.DSTR

open Subgroup

/-- **Descent of fixed points to a coset.**  Let `N ◁ G` be a characteristic subgroup, `τ` an
involution of `G` whose order is coprime to `|G|`, and `ξ` an automorphism fixing every
`τ`-fixed element.  If `g` is fixed by `τ` modulo `N`, then it is fixed by `ξ` modulo `N`.

Elementary proof: the coset `gN` is `τ`-invariant and has odd cardinality (in the nontrivial
case `orderOf τ = 2`), so the involution `τ` fixes a point `c ∈ gN`; then `ξ c = c` and
`ξ g · g⁻¹ = ξ (g c⁻¹) · (c g⁻¹) ∈ N`. -/
theorem invTrickQuotFixedElem {G : Type*} [Group G] [Finite G] {N : Subgroup G} [N.Normal]
    [N.Characteristic] (τ ξ : MulAut G) (hτ2 : τ * τ = 1)
    (hcop : Nat.Coprime (orderOf τ) (Nat.card G))
    (hfix : ∀ x : G, τ x = x → ξ x = x) (g : G) (hg : τ g * g⁻¹ ∈ N) :
    ξ g * g⁻¹ ∈ N := by
  classical
  have hττ : ∀ x : G, τ (τ x) = x := by
    intro x
    have h := congrArg (fun f : MulAut G => f x) hτ2
    simpa [MulAut.mul_apply] using h
  have hmemτ : ∀ x : G, x ∈ N ↔ τ x ∈ N := by
    intro x
    have hmap : Subgroup.map τ.toMonoidHom N = N :=
      (Subgroup.characteristic_iff_map_eq.mp inferInstance) τ
    have hmap' : Subgroup.map (τ⁻¹).toMonoidHom N = N :=
      (Subgroup.characteristic_iff_map_eq.mp inferInstance) τ⁻¹
    constructor
    · intro hx
      have h1 : τ x ∈ Subgroup.map τ.toMonoidHom N := Subgroup.mem_map_of_mem τ.toMonoidHom hx
      rwa [hmap] at h1
    · intro hx
      have h1 : x ∈ Subgroup.map (τ⁻¹).toMonoidHom N := by
        have h2 : τ⁻¹ (τ x) ∈ Subgroup.map (τ⁻¹).toMonoidHom N :=
          Subgroup.mem_map_of_mem (τ⁻¹).toMonoidHom hx
        rwa [MulAut.inv_apply_self] at h2
      rwa [hmap'] at h1
  have hmemξ : ∀ x : G, x ∈ N ↔ ξ x ∈ N := by
    intro x
    have hmap : Subgroup.map ξ.toMonoidHom N = N :=
      (Subgroup.characteristic_iff_map_eq.mp inferInstance) ξ
    have hmap' : Subgroup.map (ξ⁻¹).toMonoidHom N = N :=
      (Subgroup.characteristic_iff_map_eq.mp inferInstance) ξ⁻¹
    constructor
    · intro hx
      have h1 : ξ x ∈ Subgroup.map ξ.toMonoidHom N := Subgroup.mem_map_of_mem ξ.toMonoidHom hx
      rwa [hmap] at h1
    · intro hx
      have h1 : x ∈ Subgroup.map (ξ⁻¹).toMonoidHom N := by
        have h2 : ξ⁻¹ (ξ x) ∈ Subgroup.map (ξ⁻¹).toMonoidHom N :=
          Subgroup.mem_map_of_mem (ξ⁻¹).toMonoidHom hx
        rwa [MulAut.inv_apply_self] at h2
      rwa [hmap'] at h1
  have hτdvd : orderOf τ ∣ 2 :=
    orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hτ2)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hτdvd with h1 | h2
  · -- `τ = 1`: then `hfix` makes `ξ` trivial
    have hτ1 : τ = 1 := orderOf_eq_one_iff.mp h1
    have hg1 : ξ g = g := by
      have h := hfix g (by rw [hτ1]; rfl)
      simpa using h
    rw [hg1, mul_inv_cancel]
    exact N.one_mem
  · -- `orderOf τ = 2`, so `|G|` (and `|N|`) is odd
    have hGodd : Odd (Nat.card G) := by
      rw [← Nat.coprime_two_left]
      rwa [h2] at hcop
    have hNOdd : Odd (Nat.card ↥N) := hGodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card N)
    let S : Set G := {x | x * g⁻¹ ∈ N}
    have hτS : ∀ x : G, x ∈ S → τ x ∈ S := by
      intro x hx
      have h1 : τ (x * g⁻¹) ∈ N := (hmemτ _).mp hx
      have heq : τ x * g⁻¹ = τ (x * g⁻¹) * (τ g * g⁻¹) := by
        rw [map_mul, map_inv]; group
      show τ x * g⁻¹ ∈ N
      rw [heq]
      exact N.mul_mem h1 hg
    have he : ↥N ≃ S :=
      { toFun := fun n => ⟨g * (n : G), by
          show g * (n : G) * g⁻¹ ∈ N
          exact (inferInstance : N.Normal).conj_mem (n : G) n.2 g⟩
        invFun := fun x => ⟨g⁻¹ * (x : G), by
          have heq : g⁻¹ * (x : G) = g⁻¹ * ((x : G) * g⁻¹) * (g⁻¹)⁻¹ := by group
          rw [heq]
          exact (inferInstance : N.Normal).conj_mem ((x : G) * g⁻¹) x.2 g⁻¹⟩
        left_inv := fun n => Subtype.ext (by simp)
        right_inv := fun x => Subtype.ext (by
          show g * (g⁻¹ * (x : G)) = (x : G)
          group) }
    letI : Fintype S := Fintype.ofFinite S
    have hcardS : ¬ 2 ∣ Fintype.card S := by
      have hmod : Nat.card ↥N % 2 = 1 := Nat.odd_iff.mp hNOdd
      have hcard : Fintype.card S = Nat.card ↥N := by
        have hc : Nat.card S = Nat.card ↥N := (Nat.card_congr he).symm
        rwa [Nat.card_eq_fintype_card] at hc
      rw [hcard, Nat.dvd_iff_mod_eq_zero]
      omega
    let σfun : S → S := fun x => ⟨τ (x : G), hτS (x : G) x.2⟩
    have hinv : Function.Involutive σfun := by
      intro x
      exact Subtype.ext (hττ (x : G))
    have hσ2 : (Function.Involutive.toPerm σfun hinv) ^ 2 = 1 := by
      refine Equiv.Perm.ext (fun x => ?_)
      simp only [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
      exact hinv x
    obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hcardS hσ2
    have hxval : τ (x : G) = (x : G) := by simpa using Subtype.ext_iff.mp hx
    have hxc : ξ (x : G) = (x : G) := hfix _ hxval
    have hgx : g * (x : G)⁻¹ ∈ N := by
      have h := N.inv_mem x.2
      simpa [mul_inv_rev, inv_inv] using h
    have hξgx : ξ (g * (x : G)⁻¹) ∈ N := (hmemξ _).mp hgx
    have heq : ξ g * g⁻¹ = ξ (g * (x : G)⁻¹) * ((x : G) * g⁻¹) := by
      rw [map_mul, map_inv, hxc]
      group
    rw [heq]
    exact N.mul_mem hξgx x.2

/-- Strong-induction engine for `invTrickSolvable`. -/
theorem invTrickSolvable_aux (n : ℕ) :
    ∀ {F : Type*} [Group F] [Finite F], Nat.card F = n → Group.IsSolvable F →
      Odd (Nat.card F) → ∀ {τ ξ : MulAut F}, τ * τ = 1 →
      Nat.Coprime (orderOf ξ) (Nat.card F) → Odd (orderOf ξ) →
      τ * ξ * τ⁻¹ = ξ⁻¹ → (∀ f : F, τ f = f → ξ f = f) → ξ = 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro F _ _ hFcard hsol hFodd τ ξ hτ2 hcop hξodd hconj hfix
    by_cases habel : ∀ a b : F, a * b = b * a
    · -- ### The abelian case
      letI : CommGroup F := { (inferInstance : Group F) with mul_comm := habel }
      exact invTrickAbelian hFodd hτ2 hcop hξodd hconj hfix
    · -- ### The non-abelian case
      have hNchar : (commutator F).Characteristic := Subgroup.commutator_characteristic ⊤ ⊤
      haveI : (commutator F).Characteristic := hNchar
      haveI : (commutator F).Normal := inferInstance
      -- `[F,F] ≠ ⊤` because `F` is solvable and non-abelian
      have hNtop : commutator F ≠ ⊤ := by
        intro htop
        obtain ⟨k, hk⟩ := (Group.isSolvable_def F).mp hsol
        have hder : ∀ m, derivedSeries F m = ⊤ := by
          intro m
          induction m with
          | zero => exact derivedSeries_zero F
          | succ m ihm => rw [derivedSeries_succ, ihm]; exact htop
        have htopbot : (⊤ : Subgroup F) = ⊥ := (hder k).symm.trans hk
        exact habel (fun a b => by
          have ha : a = 1 := Subgroup.mem_bot.mp (htopbot ▸ Subgroup.mem_top a)
          have hb : b = 1 := Subgroup.mem_bot.mp (htopbot ▸ Subgroup.mem_top b)
          rw [ha, hb])
      have hNcard_lt : Nat.card ↥(commutator F) < Nat.card F := by
        haveI : Fintype ↥(commutator F) := Fintype.ofFinite _
        haveI : Fintype F := Fintype.ofFinite _
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        refine Fintype.card_lt_of_injective_not_surjective
          (Subtype.val : ↥(commutator F) → F) Subtype.val_injective ?_
        intro hsurj
        apply hNtop
        rw [eq_top_iff]
        intro x _
        obtain ⟨y, hy⟩ := hsurj x
        rw [← hy]
        exact y.2
      -- ### The induction hypothesis on `[F,F]`
      have hτ2N : invTrickRestrictHom (commutator F) τ * invTrickRestrictHom (commutator F) τ
          = 1 := by
        have h := congrArg (invTrickRestrictHom (commutator F)) hτ2
        simpa using h
      have hξoddN : Odd (orderOf (invTrickRestrictHom (commutator F) ξ)) :=
        Odd.of_dvd_nat hξodd (orderOf_invTrickRestrictHom_dvd (commutator F) ξ)
      have hcopN : Nat.Coprime (orderOf (invTrickRestrictHom (commutator F) ξ))
          (Nat.card ↥(commutator F)) :=
        Nat.Coprime.coprime_dvd_left (orderOf_invTrickRestrictHom_dvd (commutator F) ξ)
          (hcop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card (commutator F)))
      have hconjN : invTrickRestrictHom (commutator F) τ * invTrickRestrictHom (commutator F) ξ
            * (invTrickRestrictHom (commutator F) τ)⁻¹
          = (invTrickRestrictHom (commutator F) ξ)⁻¹ := by
        have h := congrArg (invTrickRestrictHom (commutator F)) hconj
        simpa using h
      have hfixN : ∀ x : ↥(commutator F), invTrickRestrictHom (commutator F) τ x = x →
          invTrickRestrictHom (commutator F) ξ x = x := by
        intro x hx
        apply Subtype.ext
        rw [invTrickRestrictHom_apply_coe]
        refine hfix (x : F) ?_
        have h := congrArg Subtype.val hx
        rwa [invTrickRestrictHom_apply_coe] at h
      have hsolN : Group.IsSolvable ↥(commutator F) := inferInstance
      have hoddN : Odd (Nat.card ↥(commutator F)) :=
        hFodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card (commutator F))
      have hξN : invTrickRestrictHom (commutator F) ξ = 1 :=
        ih (Nat.card ↥(commutator F)) (by rw [← hFcard]; exact hNcard_lt) rfl hsolN hoddN
          hτ2N hcopN hξoddN hconjN hfixN
      -- ### The abelian quotient `F ⧸ [F,F]`
      have hcopτ : Nat.Coprime (orderOf τ) (Nat.card F) := by
        refine Nat.Coprime.coprime_dvd_left ?_ (Nat.coprime_two_left.mpr hFodd)
        exact orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hτ2)
      have hτmap : Subgroup.map (τ : F ≃* F) (commutator F) = commutator F :=
        (Subgroup.characteristic_iff_map_eq.mp hNchar) τ
      have hξmap : Subgroup.map (ξ : F ≃* F) (commutator F) = commutator F :=
        (Subgroup.characteristic_iff_map_eq.mp hNchar) ξ
      have hNoddq : Odd (Nat.card (F ⧸ (commutator F))) :=
        hFodd.of_dvd_nat
          ⟨Nat.card ↥(commutator F), Subgroup.card_eq_card_quotient_mul_card_subgroup _⟩
      have hqfix : ∀ q : F ⧸ (commutator F),
          invTrickQuotMulAut (commutator F) τ hτmap q = q →
          invTrickQuotMulAut (commutator F) ξ hξmap q = q := by
        intro q hq
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (commutator F) q
        rw [invTrickQuotMulAut_apply] at hq
        have hg : τ g * g⁻¹ ∈ commutator F := invTrickQuot_eq_iff.mp hq
        have hg' : ξ g * g⁻¹ ∈ commutator F :=
          invTrickQuotFixedElem τ ξ hτ2 hcopτ hfix g hg
        rw [invTrickQuotMulAut_apply]
        exact invTrickQuot_eq_iff.mpr hg'
      have hquot := invTrickAbelianQuot (N := commutator F) (le_refl _) hNoddq hτmap hξmap
        hτ2 hcop hξodd hconj hqfix
      have hmodN : ∀ x : F, ξ x * x⁻¹ ∈ commutator F := by
        intro x
        have h := congrArg (fun f : MulAut (F ⧸ (commutator F)) =>
          f (QuotientGroup.mk' (commutator F) x)) hquot
        simp only [MulAut.one_apply] at h
        rw [invTrickQuotMulAut_apply] at h
        exact invTrickQuot_eq_iff.mp h
      have hfixN' : ∀ y ∈ commutator F, ξ y = y := by
        intro y hy
        have h := congrArg (fun f : MulAut ↥(commutator F) => f ⟨y, hy⟩) hξN
        simp only [MulAut.one_apply] at h
        have h2 := congrArg Subtype.val h
        rw [invTrickRestrictHom_apply_coe] at h2
        simpa using h2
      exact invTrickCombine ξ hfixN' hmodN
        (hcop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card (commutator F)))

/-- **The inversion trick for finite solvable groups of odd order.** -/
theorem invTrickSolvable {F : Type*} [Group F] [Finite F] (hsol : Group.IsSolvable F)
    (hFodd : Odd (Nat.card F)) {τ ξ : MulAut F} (hτ2 : τ * τ = 1)
    (hcop : Nat.Coprime (orderOf ξ) (Nat.card F)) (hξodd : Odd (orderOf ξ))
    (hconj : τ * ξ * τ⁻¹ = ξ⁻¹) (hfix : ∀ f : F, τ f = f → ξ f = f) : ξ = 1 :=
  invTrickSolvable_aux (Nat.card F) rfl hsol hFodd hτ2 hcop hξodd hconj hfix

end Work.DSTR

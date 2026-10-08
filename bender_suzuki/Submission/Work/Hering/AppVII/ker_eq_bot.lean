import Mathlib
import Submission.Work.Hering.AppVII.Setup
import Submission.Work.Hering.AppVII.fixedPoints_quotient_of_solvable_coeff
import Submission.Work.NormalComplement.AppVII.AbelianKernelCase
import Submission.Work.Hering.AppVII.appVIIZ_quotient_eq
import Submission.Work.Hering.AppVII.card_map_quotient_eq_of_inf_eq_bot

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Appendix VII — faithfulness in the `Z = 1` case

In the strong-induction assembly of Peterfalvi's Appendix VII the counterexample is pushed
into the case where `appVIIZ A P Q K = ⊥`.  This file proves that then the action of `A`
on `K` is faithful (`ker = ⊥`), the hypothesis `hfaith` consumed by
`Work.Hering.AppVII.hcent_of_eq_bot` and by the reduction to the special configuration.

(The universes of the induction hypothesis are those of `A` and `K`: it is available in the
assembly as `ih : ∀ m < n, AppVIIStmt.{u, v} m`; this is what makes the application below to
the quotient `A ⧸ C` — at the same universes — typecheck.)
-/

set_option linter.style.haveILetI false

universe u v

namespace Work.Hering.AppVII

open scoped Pointwise

theorem ker_eq_bot {n : ℕ} (ih : ∀ m < n, AppVIIStmt.{u, v} m)
    {A : Type u} [Group A] [Finite A] (P Q : Subgroup A) (hQn : Q.Normal)
    (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = ⊤) (p : ℕ) (hp : p.Prime) (hcardP : Nat.card ↥P = p)
    (hpQ : ¬ p ∣ Nat.card ↥Q) {K : Type v} [Group K] [Finite K] [MulDistribMulAction A K]
    (hcop : Nat.Coprime (Nat.card K) (Nat.card A))
    (hodd : Odd (Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set A))))
    (hsize : Nat.card A * Nat.card K = n)
    (hZbot : appVIIZ A P Q K = ⊥) (hKne : Nontrivial K) :
    (MulDistribMulAction.toMulAut A K).ker = ⊥ := by
  classical
  set ψ : A →* MulAut K := MulDistribMulAction.toMulAut A K with hψdef
  set C : Subgroup A := ψ.ker with hCdef
  have hCn : C.Normal := MonoidHom.normal_ker ψ
  haveI : C.Normal := hCn
  by_contra hCne
  have hmemker : ∀ a : A, a ∈ C ↔ ∀ x : K, a • x = x := by
    intro a
    rw [hCdef, MonoidHom.mem_ker]
    constructor
    · intro h x
      have h' : (MulDistribMulAction.toMulAut A K a) x = x := by
        have := congrArg (fun f : MulAut K => f x) h
        rwa [hψdef] at this
      simpa using h'
    · intro h
      ext x
      rw [hψdef]
      simpa using h x
  have hPnotC : ¬ P ≤ C := by
    intro hPC
    have hFx : appVIIFx A P Q K ⟨1, Q.one_mem⟩ = ⊤ := by
      rw [eq_top_iff]
      intro k _ y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨y', hy'P, hy'y⟩ := hy
      have hyC : y ∈ C := by
        rw [← hy'y]
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          using hCn.conj_mem y' (hPC hy'P) (1 : A)
      exact (hmemker y).mp hyC k
    have htop : appVIIZ A P Q K = ⊤ :=
      top_le_iff.mp (hFx ▸ appVIIFx_le_appVIIZ A P Q K ⟨1, Q.one_mem⟩)
    rw [hZbot] at htop
    have hsub : Subsingleton K := by
      refine ⟨fun a b => ?_⟩
      have ha : a = 1 := by
        simpa using (show a ∈ (⊥ : Subgroup K) from by rw [htop]; trivial)
      have hb : b = 1 := by
        simpa using (show b ∈ (⊥ : Subgroup K) from by rw [htop]; trivial)
      rw [ha, hb]
    exact (not_subsingleton_iff_nontrivial.mpr hKne) hsub
  have hCP : C ⊓ P = ⊥ := by
    rcases (Nat.dvd_prime hp).mp
        (hcardP ▸ Subgroup.card_dvd_of_le (inf_le_right : C ⊓ P ≤ P)) with h1 | h1
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have h2 : C ⊓ P = P := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, hcardP])
      exact hPnotC (h2 ▸ inf_le_left)
  have hCQ : C ≤ Q := by
    intro a ha
    obtain ⟨p', hp'P, q, hqQ, hpq⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := P) (t := Q)).mp (hsup ▸ Subgroup.mem_top a)
    have ha1 : ψ a = 1 := MonoidHom.mem_ker.mp (by rwa [hCdef] at ha)
    have h1 : ψ p' * ψ q = 1 := by
      have h := congrArg ψ hpq
      rw [map_mul, ha1] at h
      exact h
    have h1' : ψ p' = (ψ q)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h2 : orderOf (ψ p') ∣ p := by
      have h4 : orderOf p' ∣ p := by
        have h5 : orderOf (⟨p', hp'P⟩ : ↥P) ∣ Nat.card ↥P := orderOf_dvd_natCard _
        have h6 : orderOf (⟨p', hp'P⟩ : ↥P) = orderOf p' := (Subgroup.orderOf_coe _).symm
        rw [h6, hcardP] at h5
        exact h5
      exact (orderOf_map_dvd ψ p').trans h4
    have h3 : orderOf (ψ p') ∣ Nat.card ↥Q := by
      rw [h1', orderOf_inv]
      have h5 : orderOf (⟨q, hqQ⟩ : ↥Q) ∣ Nat.card ↥Q := orderOf_dvd_natCard _
      have h6 : orderOf (⟨q, hqQ⟩ : ↥Q) = orderOf q := (Subgroup.orderOf_coe _).symm
      rw [h6] at h5
      exact (orderOf_map_dvd ψ q).trans h5
    have h4 : orderOf (ψ p') = 1 := by
      refine Nat.Coprime.eq_one_of_dvd ?_ h2
      exact (hp.coprime_iff_not_dvd.mpr fun hd => hpQ (hd.trans h3)).symm
    have h6 : ψ p' = 1 := orderOf_eq_one_iff.mp h4
    have h7 : p' ∈ C := by rw [hCdef]; exact MonoidHom.mem_ker.mpr h6
    have h8 : p' = 1 := by
      have : p' ∈ C ⊓ P := Subgroup.mem_inf.mpr ⟨h7, hp'P⟩
      rw [hCP, Subgroup.mem_bot] at this
      exact this
    rw [← hpq, h8, one_mul]
    exact hqQ
  have hCψ : C ≤ ψ.ker := hCdef.le
  let f : A →* A ⧸ C := QuotientGroup.mk' C
  let ψq : (A ⧸ C) →* MulAut K := QuotientGroup.lift C ψ hCψ
  have hψq : ∀ a : A, ψq (f a) = ψ a := fun a => QuotientGroup.lift_mk' C hCψ a
  letI : MulDistribMulAction (A ⧸ C) K := MulDistribMulAction.compHom K ψq
  have hsmulq : ∀ (x : A ⧸ C) (k : K), x • k = ψq x k := fun _ _ => rfl
  have hact : ∀ (a : A) (k : K), (QuotientGroup.mk' C a) • k = a • k := by
    intro a k
    rw [hsmulq, hψq a, hψdef]
    rfl
  let Pq : Subgroup (A ⧸ C) := P.map f
  let Qq : Subgroup (A ⧸ C) := Q.map f
  have hQqn : Qq.Normal := hQn.map f (QuotientGroup.mk'_surjective C)
  have hinfq : Pq ⊓ Qq = ⊥ := by
    refine le_antisymm (fun y hy => ?_) bot_le
    obtain ⟨hyP, hyQ⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨p', hp'P, rfl⟩ := Subgroup.mem_map.mp hyP
    obtain ⟨q, hqQ, hpq⟩ := Subgroup.mem_map.mp hyQ
    have hpq' : (q : A ⧸ C) = (p' : A ⧸ C) := hpq
    have h1 : q⁻¹ * p' ∈ C := QuotientGroup.eq.mp hpq'
    have h2 : q⁻¹ * p' ∈ Q := hCQ h1
    have h3 : p' = q * (q⁻¹ * p') := by group
    have h4 : p' ∈ Q := h3 ▸ Q.mul_mem hqQ h2
    have h5 : p' ∈ P ⊓ Q := Subgroup.mem_inf.mpr ⟨hp'P, h4⟩
    rw [hinf, Subgroup.mem_bot] at h5
    rw [h5]
    exact map_one _
  have hsupq : Pq ⊔ Qq = ⊤ := by
    have h1 : Subgroup.map f (P ⊔ Q) = Pq ⊔ Qq := Subgroup.map_sup P Q f
    rw [← h1, hsup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective C)]
  have hcardPq : Nat.card ↥Pq = p := by
    have h : Nat.card ↥(P.map (QuotientGroup.mk' C)) = Nat.card ↥P :=
      card_map_quotient_eq_of_inf_eq_bot C P (by rw [inf_comm]; exact hCP)
    simp only [Pq, f] at h ⊢
    rw [h, hcardP]
  have hpQq : ¬ p ∣ Nat.card ↥Qq := fun hd => hpQ (hd.trans (Subgroup.card_map_dvd Q f))
  have hsizeq : Nat.card (A ⧸ C) * Nat.card K < n := by
    rw [← hsize]
    refine Nat.mul_lt_mul_of_pos_right ?_ (Nat.card_pos (α := K))
    have h1 : Nat.card A = Nat.card (A ⧸ C) * Nat.card ↥C :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup C
    have h2 : 1 < Nat.card ↥C := by
      have hne : Nat.card ↥C ≠ 1 := fun h => hCne (Subgroup.card_eq_one.mp h)
      have hpos : 0 < Nat.card ↥C := Nat.card_pos
      omega
    calc Nat.card (A ⧸ C) < Nat.card (A ⧸ C) * Nat.card ↥C :=
          lt_mul_of_one_lt_right Nat.card_pos h2
      _ = Nat.card A := h1.symm
  have hoddq : Odd (Nat.card ↥(Qq ⊓ Subgroup.centralizer (Pq : Set (A ⧸ C)))) := by
    have h := Work.NormalComplement.AppVII.odd_centralizer_map_quotient P Q C hQn hCn
      hp hcardP hpQ hodd
    simp only [Pq, Qq, f] at h ⊢
    exact h
  have hcopq : Nat.Coprime (Nat.card K) (Nat.card (A ⧸ C)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_quotient_dvd_card C) hcop
  have hres : appVIIZ (A ⧸ C) Pq Qq K = ⊤ :=
    ih (Nat.card (A ⧸ C) * Nat.card K) hsizeq Pq Qq hQqn hinfq hsupq p hp
      hcardPq hpQq hcopq hoddq rfl
  have htrans : appVIIZ (A ⧸ C) Pq Qq K = appVIIZ A P Q K := by
    have h := appVIIZ_quotient_eq C P Q hact
    simpa only [Pq, Qq, f] using h
  rw [htrans, hZbot] at hres
  have hsub : Subsingleton K := by
    refine ⟨fun a b => ?_⟩
    have ha : a = 1 := by
      simpa using (show a ∈ (⊥ : Subgroup K) from by rw [hres]; trivial)
    have hb : b = 1 := by
      simpa using (show b ∈ (⊥ : Subgroup K) from by rw [hres]; trivial)
    rw [ha, hb]
  exact (not_subsingleton_iff_nontrivial.mpr hKne) hsub

end Work.Hering.AppVII

import Mathlib
import Submission.Work.NormalComplement.AppVIIBase
import Submission.Work.Coprime.fixedPoints_quotient

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement.AppVII

open scoped Pointwise commutatorElement
open FT

theorem odd_centralizer_map_quotient {A : Type*} [Group A] [Finite A] (P Q C : Subgroup A)
    (hQn : Q.Normal) (hCn : C.Normal) {p : ℕ} (hp : p.Prime)
    (hcardP : Nat.card ↥P = p) (hpQ : ¬ p ∣ Nat.card ↥Q)
    (hodd : Odd (Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set A)))) :
    Odd (Nat.card ↥((Subgroup.map (QuotientGroup.mk' C) Q) ⊓
      Subgroup.centralizer (Subgroup.map (QuotientGroup.mk' C) P : Set (A ⧸ C)))) := by
  classical
  set f : A →* A ⧸ C := QuotientGroup.mk' C with hf
  set D : Subgroup A := Q ⊓ Subgroup.centralizer (P : Set A) with hD
  have hoddD : Odd (Nat.card ↥D) := hodd
  -- the conjugation action of `P` on `Q`
  haveI hNrm : FT.Normalizes P Q := ⟨by
    rw [Subgroup.normalizer_eq_top]; exact le_top⟩
  have hconj : ∀ (a : ↥P) (x : ↥Q), ((a • x : ↥Q) : A) = (a : A) * (x : A) * (a : A)⁻¹ :=
    fun a x => FT.conj_smul_coe P Q a x
  have hcopPQ : (Nat.card ↥P).Coprime (Nat.card ↥Q) := by
    rw [hcardP]; exact hp.coprime_iff_not_dvd.mpr hpQ
  have hsolP : Group.IsSolvable ↥P := by
    haveI : Fact (Nat.card ↥P).Prime := ⟨hcardP ▸ hp⟩
    haveI : IsCyclic ↥P := isCyclic_of_prime_card rfl
    exact Group.isSolvable_of_comm (isMulCommutative_iff.mp inferInstance)
  haveI hNn : (C.subgroupOf Q).Normal := hCn.subgroupOf Q
  haveI hNi : FT.IsInvariant ↥P (C.subgroupOf Q) := by
    refine ⟨fun a => le_antisymm ?_ ?_⟩
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := (Subgroup.mem_smul_pointwise_iff_exists y a (C.subgroupOf Q)).mp hy
      rw [← hxy, Subgroup.mem_subgroupOf]
      rw [Subgroup.mem_subgroupOf] at hx
      convert hCn.conj_mem (x : A) hx (a : A) using 1
      exact hconj a x
    · intro y hy
      rw [Subgroup.mem_smul_pointwise_iff_exists]
      refine ⟨(a⁻¹) • y, ?_, smul_inv_smul a y⟩
      rw [Subgroup.mem_subgroupOf]
      rw [Subgroup.mem_subgroupOf] at hy
      convert hCn.conj_mem (y : A) hy (a : A)⁻¹ using 1
  have hgas := Work.Coprime.fixedPoints_quotient (↥P) hcopPQ (Or.inl hsolP) (C.subgroupOf Q)
  -- every element of the target lies in the image of `D`
  have hE : (Subgroup.map f Q) ⊓ Subgroup.centralizer (Subgroup.map f P : Set (A ⧸ C))
      ≤ Subgroup.map f D := by
    intro y hy
    obtain ⟨hyQ, hyC⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨q, hqQ, hqy⟩ := Subgroup.mem_map.mp hyQ
    have hcomm : ∀ r ∈ P, q * r * q⁻¹ * r⁻¹ ∈ C := by
      intro r hrP
      have h1 : f q * f r = f r * f q := by
        rw [hqy]
        exact (Subgroup.mem_centralizer_iff.mp hyC (f r)
          (Subgroup.mem_map.mpr ⟨r, hrP, rfl⟩)).symm
      have h3 : f (q * r * q⁻¹ * r⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
        group
      have h4 : (q * r * q⁻¹ * r⁻¹) ∈ f.ker := MonoidHom.mem_ker.mpr h3
      rwa [hf, QuotientGroup.ker_mk'] at h4
    have hfixed : (QuotientGroup.mk' (C.subgroupOf Q)) (⟨q, hqQ⟩ : ↥Q) ∈
        FT.fixedPoints ↥P (↥Q ⧸ (C.subgroupOf Q)) := by
      rw [FT.mem_fixedPoints]
      intro a
      rw [QuotientGroup.mk'_apply, FT.quotient_smul_mk]
      refine QuotientGroup.eq.mpr ?_
      rw [Subgroup.mem_subgroupOf]
      convert (hCn.conj_mem (q * (a : A) * q⁻¹ * (a : A)⁻¹) (hcomm (a : A) a.2) q⁻¹) using 1
      show (((a • (⟨q, hqQ⟩ : ↥Q))⁻¹ * (⟨q, hqQ⟩ : ↥Q) : ↥Q) : A)
          = q⁻¹ * (q * (a : A) * q⁻¹ * (a : A)⁻¹) * q⁻¹⁻¹
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hconj a (⟨q, hqQ⟩ : ↥Q)]
      group
    have hmem : (QuotientGroup.mk' (C.subgroupOf Q)) (⟨q, hqQ⟩ : ↥Q) ∈
        (FT.fixedPoints ↥P ↥Q).map (QuotientGroup.mk' (C.subgroupOf Q)) := by
      rw [hgas]; exact hfixed
    obtain ⟨q₀, hq₀fix, hq₀eq⟩ := Subgroup.mem_map.mp hmem
    have hq₀D : (q₀ : A) ∈ D := by
      have h1 : (q₀ : A) ∈ Subgroup.centralizer (P : Set A) := by
        have h2 := FT.map_fixedPoints_conjAction P Q ▸ Subgroup.mem_map.mpr ⟨q₀, hq₀fix, rfl⟩
        exact h2.1
      exact Subgroup.mem_inf.mpr ⟨q₀.2, h1⟩
    have hfeq : f (q₀ : A) = f q := by
      have h1 : ((q₀ : A)⁻¹ * q) ∈ C := by
        have h2 : ((q₀)⁻¹ * (⟨q, hqQ⟩ : ↥Q)) ∈ C.subgroupOf Q := by
          rw [← QuotientGroup.eq]; exact hq₀eq
        rw [Subgroup.mem_subgroupOf] at h2
        simpa using h2
      have h3 : ((q₀ : A) : A ⧸ C) = ((q : A) : A ⧸ C) := QuotientGroup.eq.mpr h1
      simpa only [hf, QuotientGroup.mk'_apply] using h3
    exact Subgroup.mem_map.mpr ⟨(q₀ : A), hq₀D, by rw [hfeq, hqy]⟩
  have h1 : Nat.card ↥((Subgroup.map f Q) ⊓
      Subgroup.centralizer (Subgroup.map f P : Set (A ⧸ C)))
      ∣ Nat.card ↥(Subgroup.map f D) := Subgroup.card_dvd_of_le hE
  have h2 : Nat.card ↥(Subgroup.map f D) ∣ Nat.card ↥D := Subgroup.card_map_dvd D f
  have hiff : ∀ n : ℕ, Odd n ↔ ¬ (2 : ℕ) ∣ n := fun n => Nat.odd_iff.trans Nat.two_dvd_ne_zero.symm
  rw [hiff] at hoddD ⊢
  exact fun h => hoddD (h.trans (h1.trans h2))

theorem AbelianKernelCase {n : ℕ} (hFT : Submission.Blueprint.FeitThompsonProp) (ih : ∀ m < n, AbstractAppVII m)
    {A : Type} [Group A] [Finite A] (P Q : Subgroup A) (hQn : Q.Normal)
    (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = ⊤) {p : ℕ} (hp : p.Prime)
    (hcardP : Nat.card ↥P = p) (hpQ : ¬ p ∣ Nat.card ↥Q)
    (hodd : Odd (Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set A))))
    {K : Type} [Group K] [Finite K] [MulDistribMulAction A K]
    (hcop : Nat.Coprime (Nat.card K) (Nat.card A))
    (hfix : ∀ k : K, (∀ a ∈ P, a • k = k) → k = 1)
    (hsize : Nat.card A * Nat.card K = n)
    (hker : (MulDistribMulAction.toMulAut A K).ker ≠ ⊥) :
    ∀ k : K, ∀ a ∈ ⁅P, Q⁆, a • k = k := by
  classical
  by_cases hsub : Subsingleton K
  · intro k a _
    exact Subsingleton.elim _ _
  haveI : Nontrivial K := not_subsingleton_iff_nontrivial.mp hsub
  set ψ : A →* MulAut K := MulDistribMulAction.toMulAut A K with hψ
  have hψsmul : ∀ (a : A) (k : K), ψ a k = a • k := by
    intro a k
    simp only [hψ, MulDistribMulAction.toMulAut_apply, MulDistribMulAction.toMulEquiv_apply]
  set C : Subgroup A := ψ.ker with hC
  have hCne : C ≠ ⊥ := hker
  have hCn : C.Normal := MonoidHom.normal_ker ψ
  -- `P ⊄ C`, since `P ≤ C` would make `P` act trivially and force `K = 1`
  have hPnotle : ¬ (P ≤ C) := by
    intro hle
    have htriv : ∀ k : K, k = 1 := by
      intro k
      refine hfix k fun a ha => ?_
      have h1 : ψ a = 1 := MonoidHom.mem_ker.mp (hle ha)
      have h2 : ψ a k = (1 : MulAut K) k := by rw [h1]
      rw [hψsmul] at h2
      simpa using h2
    exact hsub (Subsingleton.intro fun x y => by rw [htriv x, htriv y])
  have hCP : C ⊓ P = ⊥ := by
    rcases (Nat.dvd_prime hp).mp (hcardP ▸ Subgroup.card_dvd_of_le inf_le_right) with h1 | h1
    · exact Subgroup.card_eq_one.mp h1
    · have h2 : C ⊓ P = P :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, hcardP])
      exact absurd (h2 ▸ inf_le_left : P ≤ C) hPnotle
  -- `C ≤ Q`
  have hCQ : C ≤ Q := by
    intro a ha
    obtain ⟨p', hp'P, q, hqQ, hpq⟩ := (Subgroup.mem_sup_of_normal_right (s := P) (t := Q)).mp
      (hsup ▸ Subgroup.mem_top a)
    have ha1 : ψ a = 1 := MonoidHom.mem_ker.mp ha
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
    have h7 : p' ∈ C := MonoidHom.mem_ker.mpr h6
    have h8 : p' = 1 := by
      have : p' ∈ C ⊓ P := Subgroup.mem_inf.mpr ⟨h7, hp'P⟩
      rw [hCP, Subgroup.mem_bot] at this
      exact this
    rw [← hpq, h8, one_mul]
    exact hqQ
  -- the quotient group and the induced action
  have hCψ : C ≤ ψ.ker := hC.le
  let ψq : (A ⧸ C) →* MulAut K := QuotientGroup.lift C ψ hCψ
  have hψq : ∀ a : A, ψq (QuotientGroup.mk' C a) = ψ a := fun a =>
    QuotientGroup.lift_mk' C hCψ a
  letI : MulDistribMulAction (A ⧸ C) K := MulDistribMulAction.compHom K ψq
  have hsmulq : ∀ (x : A ⧸ C) (k : K), x • k = ψq x k := fun _ _ => rfl
  let f : A →* A ⧸ C := QuotientGroup.mk' C
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
    have hinj : ∀ x y : ↥P, f (x : A) = f (y : A) → x = y := by
      intro x y hxy
      have h1 : (x : A)⁻¹ * (y : A) ∈ C := by
        rw [← QuotientGroup.eq, ← QuotientGroup.mk'_apply, ← QuotientGroup.mk'_apply]
        exact hxy
      have h2 : (x : A)⁻¹ * (y : A) ∈ P := P.mul_mem (P.inv_mem x.2) y.2
      have h3 : (x : A)⁻¹ * (y : A) ∈ P ⊓ C := Subgroup.mem_inf.mpr ⟨h2, h1⟩
      rw [inf_comm, hCP, Subgroup.mem_bot] at h3
      exact Subtype.ext (inv_mul_eq_one.mp h3)
    let e : ↥P → ↥Pq := fun x =>
      ⟨f (x : A), Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩⟩
    have hbij : Function.Bijective e := by
      refine ⟨fun x y hxy => hinj x y (Subtype.ext_iff.mp hxy), fun y => ?_⟩
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    have hcard : Nat.card ↥Pq = Nat.card ↥P :=
      (Nat.card_congr (Equiv.ofBijective e hbij)).symm
    rw [hcard, hcardP]
  have hpQq : ¬ p ∣ Nat.card ↥Qq := fun hd => hpQ (hd.trans (Subgroup.card_map_dvd (H := Q) f))
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
  have hoddq : Odd (Nat.card ↥(Qq ⊓ Subgroup.centralizer (Pq : Set (A ⧸ C)))) :=
    odd_centralizer_map_quotient P Q C hQn hCn hp hcardP hpQ hodd
  have hcopq : Nat.Coprime (Nat.card K) (Nat.card (A ⧸ C)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_quotient_dvd_card C) hcop
  have hfixq : ∀ k : K, (∀ x ∈ Pq, x • k = k) → k = 1 := by
    intro k hk
    refine hfix k fun a ha => ?_
    have hmem : f a ∈ Pq := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    have h2 := hk _ hmem
    rw [hsmulq, hψq, hψsmul] at h2
    exact h2
  have ihres : ∀ k : K, ∀ a ∈ ⁅Pq, Qq⁆, a • k = k :=
    ih (Nat.card (A ⧸ C) * Nat.card K) hsizeq hFT (A ⧸ C) Pq Qq hQqn hinfq hsupq hp
      hcardPq hpQq hoddq K hcopq hfixq rfl
  intro k a ha
  have hmem : f a ∈ ⁅Pq, Qq⁆ := by
    have h1 : f a ∈ Subgroup.map f ⁅P, Q⁆ := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    rwa [Subgroup.map_commutator] at h1
  have h2 := ihres k (f a) hmem
  rw [hsmulq, hψq, hψsmul] at h2
  exact h2

end Work.NormalComplement.AppVII

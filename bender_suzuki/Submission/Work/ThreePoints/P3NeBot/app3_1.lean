import Mathlib
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Submission.Work.ThreePoints.P3Sub.Basic
import Submission.Work.ThreePoints.Basic
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.sec3_lemma2
import Submission.Work.ThreePoints.TwoPointTransitive
import Submission.Work.ThreePoints.Sec2b
import Submission.Work.ThreePoints.isStronglyEmbedded_map_quotient
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup
import Submission.Work.DoubleTransitivity.Action
import Submission.Work.DoubleTransitivity.Sec3.prop1
import Submission.Work.NormalComplement.appIII
import Submission.Work.Reductions.hasFourGroup_quotient

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints.P3NeBot

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-! ## Preliminary: the action of `F ⧸ K` on `F ⧸ H₀` for a normal `K ≤ H₀` -/

/-- A normal subgroup `K ≤ H₀` fixes every point of `F ⧸ H₀`. -/
theorem smul_eq_of_mem_of_le {F : Type} [Group F] {K H₀ : Subgroup F} [K.Normal] (hKH : K ≤ H₀)
    {k : F} (hk : k ∈ K) (c : F ⧸ H₀) : k • c = c := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
  rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
  have h1 : (k • y)⁻¹ * y = y⁻¹ * k⁻¹ * y := by rw [smul_eq_mul]; group
  rw [h1]
  refine hKH ?_
  simpa using Subgroup.Normal.conj_mem (inferInstance : K.Normal) (k⁻¹) (K.inv_mem hk) (y⁻¹)

/-- The induced `SMul` of `F ⧸ K` on `F ⧸ H₀` (`K ⊴ F`, `K ≤ H₀`). -/
def quotientSMul (F : Type) [Group F] (K H₀ : Subgroup F) [K.Normal] (hKH : K ≤ H₀) :
    SMul (F ⧸ K) (F ⧸ H₀) :=
  ⟨fun x c => Quotient.liftOn x (fun g => g • c) (fun a a' h => by
    have hk : a⁻¹ * a' ∈ K := QuotientGroup.leftRel_apply.mp h
    calc a • c = a • ((a⁻¹ * a') • c) := by rw [smul_eq_of_mem_of_le hKH hk c]
      _ = (a * (a⁻¹ * a')) • c := (mul_smul a (a⁻¹ * a') c).symm
      _ = a' • c := by rw [show a * (a⁻¹ * a') = a' from by group])⟩

theorem quotientSMul_mk' (F : Type) [Group F] (K H₀ : Subgroup F) [K.Normal] (hKH : K ≤ H₀)
    (g : F) (c : F ⧸ H₀) :
    (quotientSMul F K H₀ hKH).smul (QuotientGroup.mk' K g) c = g • c := by
  rw [QuotientGroup.mk'_apply]
  exact Quotient.liftOn_mk _ _ g

instance quotientMulAction (F : Type) [Group F] (K H₀ : Subgroup F) [K.Normal]
    [Fact (K ≤ H₀)] : MulAction (F ⧸ K) (F ⧸ H₀) where
  toSMul := quotientSMul F K H₀ (Fact.out : K ≤ H₀)
  one_smul c := by
    show (quotientSMul F K H₀ (Fact.out : K ≤ H₀)).smul (1 : F ⧸ K) c = c
    rw [show (1 : F ⧸ K) = QuotientGroup.mk' K 1 by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk_one]]
    rw [quotientSMul_mk']
    exact one_smul F c
  mul_smul x y c := by
    induction x using Quotient.inductionOn' with
    | h a =>
      induction y using Quotient.inductionOn' with
      | h b =>
        show (quotientSMul F K H₀ (Fact.out : K ≤ H₀)).smul
            ((QuotientGroup.mk' K a) * (QuotientGroup.mk' K b)) c
          = (quotientSMul F K H₀ (Fact.out : K ≤ H₀)).smul (QuotientGroup.mk' K a)
              ((quotientSMul F K H₀ (Fact.out : K ≤ H₀)).smul (QuotientGroup.mk' K b) c)
        rw [← map_mul, quotientSMul_mk', quotientSMul_mk', quotientSMul_mk', mul_smul]

/-- The induced action of `F ⧸ K` on `F ⧸ H₀`, in the form used by rewriting. -/
theorem quotient_smul_mk' {F : Type} [Group F] (K H₀ : Subgroup F) [K.Normal] [Fact (K ≤ H₀)]
    (g : F) (c : F ⧸ H₀) : (QuotientGroup.mk' K g) • c = g • c := by
  show (quotientSMul F K H₀ (Fact.out : K ≤ H₀)).smul (QuotientGroup.mk' K g) c = g • c
  exact quotientSMul_mk' F K H₀ (Fact.out : K ≤ H₀) g c

/-! ## Elementary group theory: involutions and odd-order quotients -/

/-- Two distinct involutions whose product has even order generate a four-group. -/
theorem hasFourGroup_of_two_involutions_even {G : Type} [Group G] [Finite G] {y z : G}
    (hy : orderOf y = 2) (hz : orderOf z = 2) (hne : y ≠ z) (hev : 2 ∣ orderOf (y * z)) :
    HasFourGroup G := by
  have hy2 : y * y = 1 := mul_self_eq_one_of_orderOf_eq_two hy
  have hz2 : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two hz
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hpos : 0 < orderOf (y * z) :=
    Nat.pos_of_ne_zero fun h0 =>
      Nat.card_pos.ne' (Nat.eq_zero_of_zero_dvd (h0 ▸ orderOf_dvd_natCard (y * z)))
  set n := orderOf (y * z) with hn
  have hn2 : 2 * (n / 2) = n := Nat.mul_div_cancel' hev
  have h2n : 2 ≤ n := by rw [hn]; exact Nat.le_of_dvd hpos hev
  have hpow : ((y * z) ^ (n / 2)) * ((y * z) ^ (n / 2)) = 1 := by
    rw [← pow_add, ← two_mul, hn2, hn, pow_orderOf_eq_one]
  have hcinv : ((y * z) ^ (n / 2))⁻¹ = (y * z) ^ (n / 2) :=
    inv_eq_of_mul_eq_one_right hpow
  have hc2 : orderOf ((y * z) ^ (n / 2)) = 2 := by
    refine orderOf_eq_two_of ?_ hpow
    intro h1
    have hdvd : n ∣ n / 2 := by
      rw [hn, orderOf_dvd_iff_pow_eq_one]
      exact h1
    exact absurd (Nat.le_of_dvd (Nat.div_pos h2n (by norm_num)) hdvd) (by omega)
  have hcy : (y * z) ^ (n / 2) ≠ y := by
    intro h1
    -- `(y * z) ^ (n / 2)` commutes with `y * z`
    have hccomm : (y * z) ^ (n / 2) * (y * z) = (y * z) * (y * z) ^ (n / 2) := by
      calc (y * z) ^ (n / 2) * (y * z) = (y * z) ^ (n / 2 + 1) := (pow_succ _ _).symm
        _ = (y * z) * (y * z) ^ (n / 2) := by rw [pow_succ']
    have hyw : y * (y * z) = (y * z) * y := by
      have h := hccomm
      rw [h1] at h
      exact h
    have hcomm : y * z = z * y := by
      refine mul_left_cancel (a := y) ?_
      calc y * (y * z) = (y * z) * y := hyw
        _ = y * (z * y) := by rw [mul_assoc]
    have hsqq : (y * z) * (y * z) = 1 := by
      calc (y * z) * (y * z) = y * (z * y) * z := by group
        _ = y * (y * z) * z := by rw [← hcomm]
        _ = 1 := by rw [← mul_assoc y y z, hy2, one_mul, hz2]
    have hdvd2 : n ∣ 2 := by
      rw [hn, orderOf_dvd_iff_pow_eq_one, pow_two]
      exact hsqq
    have hle : n ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
    have hn1 : n / 2 = 1 := by omega
    rw [hn1, pow_one] at h1
    have hz1 : z = 1 :=
      mul_left_cancel (show y * z = y * 1 from by rw [mul_one]; exact h1)
    rw [hz1] at hz
    simp at hz
  have hyc : y * (y * z) ^ (n / 2) = (y * z) ^ (n / 2) * y := by
    have hconj : y * (y * z) ^ (n / 2) * y⁻¹ = (y * z) ^ (n / 2) := by
      have h1 : (MulAut.conj y) (y * z) = (y * z)⁻¹ := by
        rw [MulAut.conj_apply]
        have h2 : (y * z)⁻¹ = z * y := by rw [mul_inv_rev, hzi, hyi]
        rw [h2]
        calc y * (y * z) * y⁻¹ = y * y * (z * y⁻¹) := by group
          _ = z * y⁻¹ := by rw [hy2, one_mul]
          _ = z * y := by rw [hyi]
      calc y * (y * z) ^ (n / 2) * y⁻¹
          = (MulAut.conj y) ((y * z) ^ (n / 2)) := by rw [MulAut.conj_apply]
        _ = ((MulAut.conj y) (y * z)) ^ (n / 2) := map_pow _ _ _
        _ = ((y * z)⁻¹) ^ (n / 2) := by rw [h1]
        _ = ((y * z) ^ (n / 2))⁻¹ := inv_pow _ _
        _ = (y * z) ^ (n / 2) := hcinv
    calc y * (y * z) ^ (n / 2) = y * (y * z) ^ (n / 2) * y⁻¹ * y := by group
      _ = (y * z) ^ (n / 2) * y := by rw [hconj]
  exact ⟨y, (y * z) ^ (n / 2), hy, hc2, (fun h => hcy h.symm), hyc⟩

/-- **An element of order `2` of `F ⧸ K`, with `K` of odd order, is the image of an involution.** -/
theorem exists_orderOf_eq_two_mk'_eq {F : Type} [Group F] [Finite F] (K : Subgroup F) [K.Normal]
    (hodd : Odd (Nat.card K)) {x : F} (hx : orderOf (QuotientGroup.mk' K x) = 2) :
    ∃ y : F, orderOf y = 2 ∧ QuotientGroup.mk' K y = QuotientGroup.mk' K x := by
  obtain ⟨m, hm⟩ := hodd
  have hx2K : x ^ 2 ∈ K := by
    have h : QuotientGroup.mk' K (x ^ 2) = 1 := by
      rw [map_pow]
      exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hx])
    exact (QuotientGroup.eq_one_iff (x ^ 2)).mp h
  have hx2 : (QuotientGroup.mk' K x) ^ 2 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (by rw [hx])
  have hmk : (QuotientGroup.mk' K x) ^ (Nat.card K) = QuotientGroup.mk' K x := by
    rw [hm, pow_add, pow_mul, hx2, one_pow, pow_one, one_mul]
  have hpow : (x ^ Nat.card K) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard K hx2K)
  have hne : x ^ Nat.card K ≠ 1 := by
    intro h1
    have h2 : (QuotientGroup.mk' K x) ^ (Nat.card K) = 1 := by
      rw [← map_pow, h1, map_one]
    rw [hmk] at h2
    rw [h2] at hx
    simp at hx
  exact ⟨x ^ Nat.card K, orderOf_eq_two_of hne (by rwa [pow_two] at hpow), by rw [map_pow, hmk]⟩

/-- **The 2-rank does not increase when passing to a quotient by an odd-order normal subgroup.** -/
theorem not_hasFourGroup_quotient {F : Type} [Group F] [Finite F] (K : Subgroup F) [K.Normal]
    (hodd : Odd (Nat.card K)) (hrank : ¬ HasFourGroup F) : ¬ HasFourGroup (F ⧸ K) := by
  intro h4
  obtain ⟨a, b, ha2, hb2, hab, hcomm⟩ := h4
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K a
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective K b
  obtain ⟨y, hy2, hyk⟩ := exists_orderOf_eq_two_mk'_eq K hodd ha2
  obtain ⟨z, hz2, hzk⟩ := exists_orderOf_eq_two_mk'_eq K hodd hb2
  have hyz : y ≠ z := fun h => hab (by rw [← hyk, h, hzk])
  have hx2 : QuotientGroup.mk' K x * QuotientGroup.mk' K x = 1 := by
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [ha2])
  have hw2 : QuotientGroup.mk' K w * QuotientGroup.mk' K w = 1 := by
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hb2])
  have hord2 : orderOf (QuotientGroup.mk' K (y * z)) = 2 := by
    rw [map_mul, hyk, hzk]
    refine orderOf_eq_two_of ?_ ?_
    · intro h1
      refine hab ?_
      have h2 : QuotientGroup.mk' K w = (QuotientGroup.mk' K x)⁻¹ :=
        ((mul_eq_one_iff_inv_eq).mp h1).symm
      rw [inv_eq_of_mul_eq_one_right hx2] at h2
      exact h2.symm
    · calc (QuotientGroup.mk' K x * QuotientGroup.mk' K w)
            * (QuotientGroup.mk' K x * QuotientGroup.mk' K w)
          = QuotientGroup.mk' K x * (QuotientGroup.mk' K w * QuotientGroup.mk' K x)
              * QuotientGroup.mk' K w := by group
        _ = QuotientGroup.mk' K x * (QuotientGroup.mk' K x * QuotientGroup.mk' K w)
              * QuotientGroup.mk' K w := by rw [← hcomm]
        _ = (QuotientGroup.mk' K x * QuotientGroup.mk' K x)
              * (QuotientGroup.mk' K w * QuotientGroup.mk' K w) := by group
        _ = 1 := by rw [hx2, hw2, mul_one]
  have h2dvd : 2 ∣ orderOf (y * z) := by
    rw [← hord2]
    exact orderOf_map_dvd (QuotientGroup.mk' K) (y * z)
  exact hrank (hasFourGroup_of_two_involutions_even hy2 hz2 hyz h2dvd)

/-! ## Peterfalvi I, Appendix III (1) (p. 206), abstract form

The source's Appendix III (1) says that in a finite group `F` of 2-rank `1` with a maximal
strongly embedded subgroup `H₀`, the two-point stabiliser `H₀ ⊓ H₀^t` of an involution
`t ∈ F ∖ H₀` fixes the (unique) fixed point of `t`.  The proof goes through Appendix III (2),
(3) for the quotient of `F` by the kernel `core_F(H₀)` of the action on `F ⧸ H₀` (the source's
"we may assume `F` acts faithfully"), for which `Work.NormalComplement.appIII` provides the
structure theorem from `BrauerSuzukiProp` and `FeitThompsonProp`. -/

/-- **Peterfalvi I, Appendix III (1)** (p. 206), abstract (coset space) form: `H₀ ≤ F` strongly
embedded and maximal, `¬ HasFourGroup F`, `t ∈ F ∖ H₀` an involution, and `b` the unique fixed
point of `t` in `F ⧸ H₀`; then `H₀ ⊓ H₀^t` fixes `b`. -/
theorem appIII_one_core {F : Type} [Group F] [Finite F] (H₀ : Subgroup F)
    (hSE : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H₀)
    (hmax : ∀ M : Subgroup F, H₀ ≤ M → M = H₀ ∨ M = ⊤)
    (hrank : ¬ Submission.Blueprint.HasFourGroup F)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (hFT : Submission.Blueprint.FeitThompsonProp)
    {t : F} (ht : orderOf t = 2) (htH : t ∉ H₀)
    {b : F ⧸ H₀} (hb : t • b = b) (hbuniq : ∀ c : F ⧸ H₀, t • c = c → c = b) :
    H₀ ⊓ Submission.Blueprint.conj t H₀ ≤ MulAction.stabilizer F b := by
  classical
  -- ## the kernel `K = core_F(H₀)` of the action on `F ⧸ H₀` is normal in `F`, lies in `H₀`,
  -- and has odd order
  set K : Subgroup F := H₀.normalCore with hK
  have hKH : K ≤ H₀ := Subgroup.normalCore_le H₀
  haveI hKn : K.Normal := Subgroup.normalCore_normal H₀
  haveI hKfact : Fact (K ≤ H₀) := ⟨hKH⟩
  have hKodd : Odd (Nat.card K) := by
    have hle : K ≤ H₀ ⊓ Submission.Blueprint.conj t H₀ := by
      refine le_inf hKH ?_
      intro k hk
      rw [Work.ThreePoints.mem_conj_iff]
      exact hKH (by simpa using Subgroup.Normal.conj_mem hKn k hk (t⁻¹))
    exact Odd.of_dvd_nat (IsStronglyEmbedded.odd_card_inf_conj hSE htH)
      (Subgroup.card_dvd_of_le hle)
  -- ## the induced action of `F ⧸ K` on `F ⧸ H₀` is transitive and faithful
  have htrans : MulAction.IsPretransitive (F ⧸ K) (F ⧸ H₀) := by
    refine ⟨fun c d => ?_⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective d
    refine ⟨QuotientGroup.mk' K (z * y⁻¹), ?_⟩
    show (quotientSMul F K H₀ hKH).smul (QuotientGroup.mk' K (z * y⁻¹)) (y : F ⧸ H₀)
        = (z : F ⧸ H₀)
    rw [quotientSMul_mk', MulAction.Quotient.smul_mk, smul_eq_mul]
    congr 1
    group
  have hfaith : ∀ g : F ⧸ K, (∀ c : F ⧸ H₀, g • c = c) → g = 1 := by
    intro g hg
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective K g
    have hmem : a⁻¹ ∈ K := by
      intro c
      have h1 := hg ((a⁻¹ * c⁻¹ : F) : F ⧸ H₀)
      rw [quotient_smul_mk', MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at h1
      have h2 : (a * (a⁻¹ * c⁻¹))⁻¹ * (a⁻¹ * c⁻¹) = c * a⁻¹ * c⁻¹ := by group
      rwa [h2] at h1
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff a).mpr (by simpa using K.inv_mem hmem)
  -- ## the point stabiliser of the base point is `H₀K/K`, and it is a coatom
  have hstab : MulAction.stabilizer (F ⧸ K) ((1 : F) : F ⧸ H₀)
      = H₀.map (QuotientGroup.mk' K) := by
    ext x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective K x
    rw [Subgroup.mem_map]
    constructor
    · intro h
      refine ⟨a, ?_, rfl⟩
      rw [MulAction.mem_stabilizer_iff] at h
      have h1 : ((a : F) : F ⧸ H₀) = ((1 : F) : F ⧸ H₀) := by
        have h2 := h
        rw [quotient_smul_mk' K H₀ a ((1 : F) : F ⧸ H₀), MulAction.Quotient.smul_mk,
          smul_eq_mul, mul_one] at h2
        exact h2
      rw [← Subgroup.inv_mem_iff]
      simpa using (QuotientGroup.eq.mp h1)
    · rintro ⟨b', hb', hba⟩
      rw [MulAction.mem_stabilizer_iff, ← hba, quotient_smul_mk' K H₀ b' ((1 : F) : F ⧸ H₀),
        MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
      exact QuotientGroup.eq.mpr (by simpa using H₀.inv_mem hb')
  have hcoatom : IsCoatom (MulAction.stabilizer (F ⧸ K) ((1 : F) : F ⧸ H₀)) := by
    rw [hstab, isCoatom_iff_ge_of_le]
    constructor
    · intro hcon
      have h1 : Subgroup.comap (QuotientGroup.mk' K) (H₀.map (QuotientGroup.mk' K)) = H₀ :=
        Subgroup.comap_map_eq_self (by rw [QuotientGroup.ker_mk']; exact hKH)
      rw [hcon, Subgroup.comap_top] at h1
      exact IsStronglyEmbedded.ne_top hSE h1.symm
    · intro b' hb' hle
      have hle' : H₀ ≤ Subgroup.comap (QuotientGroup.mk' K) b' := by
        intro y hy
        rw [Subgroup.mem_comap]
        exact hle (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
      rcases hmax (Subgroup.comap (QuotientGroup.mk' K) b') hle' with hcase | hcase
      · intro y hy
        obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective K y
        rw [← hz]
        refine Subgroup.mem_map.mpr ⟨z, ?_, rfl⟩
        have h3 : z ∈ Subgroup.comap (QuotientGroup.mk' K) b' := by
          rw [Subgroup.mem_comap, hz]
          exact hy
        rwa [hcase] at h3
      · exfalso
        apply hb'
        refine le_antisymm le_top (fun y _ => ?_)
        obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective K y
        have h3 : z ∈ Subgroup.comap (QuotientGroup.mk' K) b' := by
          rw [hcase]; exact Subgroup.mem_top z
        rw [Subgroup.mem_comap] at h3
        rwa [hz] at h3
  -- ## Appendix III (2)–(5) in the quotient
  have hSE' : LeanEval.GroupTheory.Defs.IsStronglyEmbedded (H₀.map (QuotientGroup.mk' K)) :=
    Work.ThreePoints.isStronglyEmbedded_map_quotient K hKodd hKH hSE
  have hrank' : ¬ Submission.Blueprint.HasFourGroup (F ⧸ K) :=
    not_hasFourGroup_quotient K hKodd hrank
  have ht' : orderOf (QuotientGroup.mk' K t) = 2 :=
    Work.Reductions.orderOf_mk'_eq_two K ht hKodd
  have htH' : QuotientGroup.mk' K t ∉ H₀.map (QuotientGroup.mk' K) := by
    intro hmem
    obtain ⟨h, hh, hmh⟩ := Subgroup.mem_map.mp hmem
    have h1 : h⁻¹ * t ∈ K := by
      rw [← QuotientGroup.ker_mk' K, MonoidHom.mem_ker, map_mul, map_inv, hmh, inv_mul_cancel]
    have h2 : t ∈ H₀ := by
      have h3 : t = h * (h⁻¹ * t) := by group
      rw [h3]
      exact H₀.mul_mem hh (hKH h1)
    exact htH h2
  obtain ⟨f, Q, hfp, hQn, hQne, hQab, hQexp, hQinf, hQsup, huniq, -, -, -⟩ :=
    Work.NormalComplement.appIII hBrSz hFT (F ⧸ K) (F ⧸ H₀) ((1 : F) : F ⧸ H₀)
      htrans hfaith hrank' (by rw [hstab]; exact hSE') hcoatom
  -- ## the point stabiliser in the quotient has a unique involution
  have hInvStab : (Submission.Blueprint.involutions
      ((MulAction.stabilizer (F ⧸ K) ((1 : F) : F ⧸ H₀)) : Set (F ⧸ K))).ncard = 1 := by
    obtain ⟨u, hu, huniq2⟩ := huniq
    rw [Set.ncard_eq_one]
    refine ⟨u, ?_⟩
    ext x
    rw [Work.ThreePoints.mem_involutions, Set.mem_singleton_iff]
    exact ⟨fun hx => huniq2 x hx, fun hx => by rw [hx]; exact hu⟩
  have hcardJ : (Submission.Blueprint.invertedBy
      (Submission.Blueprint.twoPoint (MulAction.stabilizer (F ⧸ K) ((1 : F) : F ⧸ H₀))
        (QuotientGroup.mk' K t)) (QuotientGroup.mk' K t)).ncard = 1 := by
    have h1 : (Work.ThmF.Kset (MulAction.stabilizer (F ⧸ K) ((1 : F) : F ⧸ H₀))
        (QuotientGroup.mk' K t)).ncard = 1 := by
      rw [Work.ThmF.Bender.cardKsetEqInv
        (H := MulAction.stabilizer (F ⧸ K) ((1 : F) : F ⧸ H₀))
        (by rw [hstab]; exact hSE') ht' (by rw [hstab]; exact htH')]
      exact hInvStab
    exact h1
  -- ## hence the two-point stabiliser centralises `t`
  have hcent : Submission.Blueprint.twoPoint (MulAction.stabilizer (F ⧸ K) ((1 : F) : F ⧸ H₀))
        (QuotientGroup.mk' K t)
      ≤ Subgroup.centralizer ({QuotientGroup.mk' K t} : Set (F ⧸ K)) := by
    set D := Submission.Blueprint.twoPoint (MulAction.stabilizer (F ⧸ K) ((1 : F) : F ⧸ H₀))
      (QuotientGroup.mk' K t) with hD
    have hoddD : Odd (Nat.card D) := by
      rw [hD, Submission.Blueprint.twoPoint]
      exact IsStronglyEmbedded.odd_card_inf_conj
        (H := MulAction.stabilizer (F ⧸ K) ((1 : F) : F ⧸ H₀))
        (by rw [hstab]; exact hSE') (by rw [hstab]; exact htH')
    have hcardD := Work.ThreePoints.card_eq_mul_ncard_invertedBy (X := D)
      (t := QuotientGroup.mk' K t) ht' hoddD
      (Work.ThreePoints.mem_normalizer_twoPoint _ ht')
    rw [hcardJ, mul_one] at hcardD
    have hthis : D ⊓ Subgroup.centralizer ({QuotientGroup.mk' K t} : Set (F ⧸ K)) = D := by
      refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
      exact le_of_eq hcardD
    exact inf_eq_left.mp hthis
  -- ## a point of `F ⧸ H₀` fixed by `t` is fixed by `H₀ ⊓ H₀^t`
  intro g hg
  rw [MulAction.mem_stabilizer_iff]
  have hgH : g ∈ H₀ := hg.1
  have hgD : g ∈ Submission.Blueprint.conj t H₀ := hg.2
  have hgmem : QuotientGroup.mk' K g ∈ Submission.Blueprint.twoPoint
      (MulAction.stabilizer (F ⧸ K) ((1 : F) : F ⧸ H₀)) (QuotientGroup.mk' K t) := by
    rw [Submission.Blueprint.twoPoint, Subgroup.mem_inf, hstab]
    refine ⟨Subgroup.mem_map.mpr ⟨g, hgH, rfl⟩, ?_⟩
    rw [Work.ThreePoints.mem_conj_iff, Subgroup.mem_map]
    exact ⟨t⁻¹ * g * t, Work.ThreePoints.mem_conj_iff.mp hgD, by rw [map_mul, map_mul, map_inv]⟩
  have hgcent : QuotientGroup.mk' K g
      ∈ Subgroup.centralizer ({QuotientGroup.mk' K t} : Set (F ⧸ K)) := hcent hgmem
  rw [Subgroup.mem_centralizer_singleton_iff] at hgcent
  have hgb : (QuotientGroup.mk' K g) • b = b := by
    apply hbuniq
    calc t • ((QuotientGroup.mk' K g) • b)
        = (QuotientGroup.mk' K t) • ((QuotientGroup.mk' K g) • b) := by
          rw [quotient_smul_mk' K H₀ t ((QuotientGroup.mk' K g) • b)]
      _ = ((QuotientGroup.mk' K t) * (QuotientGroup.mk' K g)) • b := (mul_smul _ _ b).symm
      _ = ((QuotientGroup.mk' K g) * (QuotientGroup.mk' K t)) • b := by rw [← hgcent]
      _ = (QuotientGroup.mk' K g) • ((QuotientGroup.mk' K t) • b) := mul_smul _ _ b
      _ = (QuotientGroup.mk' K g) • b := by
          rw [quotient_smul_mk' K H₀ t b, hb]
  rw [← quotient_smul_mk' K H₀ g b]
  exact hgb
/-! ## The lemma in the form used by Ch. II §4 Prop. 3(c) -/

/-- Peterfalvi I Appendix III (1) (p. 206) in the form used by Ch. II §4 Prop. 3(c): `F` has 2-rank 1, `F ⊓ H` is a strongly embedded maximal subgroup of `F`, `F` is 2-transitive on `Ω_X`, `t ∈ F ∖ H` is an involution and `ω` is its (unique) fixed point. Then `F ⊓ twoPoint H t ≤ Stab_G ω`, i.e. the two-point stabiliser `F ⊓ H ⊓ H^t` fixes the third point `ω`, which is the source's `H ∩ H^t = H ∩ H(t)`. `hBrSz` and `hFT` are the black boxes used for `F = O_{2'}(F)·C_F(u)` and the solvability of the odd-order group `O_{2'}(F)`. Auxiliary ingredients available: `Work.DoubleTransitivity.Sec3.prop1` (Ch. I §3 Prop. 1 with `hBrSz`), and Appendix III (2)-(5) may be taken from `Work.NormalComplement.AppIIIProp` if it becomes available. -/
theorem app3_1 {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    {X F : Subgroup G}
    (hFN : F ≤ Subgroup.normalizer (X : Set G))
    (h2t : Work.DoubleTransitivity.IsTwoTransitiveOnSub F (Submission.Blueprint.fixedPts H X))
    (hFSE : LeanEval.GroupTheory.Defs.IsStronglyEmbedded ((F ⊓ H).subgroupOf F))
    (hmax : ∀ M : Subgroup G, F ⊓ H ≤ M → M ≤ F → M = F ⊓ H ∨ M = F)
    (h2rank1 : ¬ Submission.Blueprint.HasFourGroup ↥F)
    {t : G} (ht : orderOf t = 2) (htF : t ∈ F) (htH : t ∉ H)
    {ω : G ⧸ H} (hω : t • ω = ω) :
    F ⊓ Submission.Blueprint.twoPoint H t ≤ MulAction.stabilizer G ω := by
  classical
  -- work inside the abstract group `↥F`, whose point stabiliser is `H₀ = (F ⊓ H).subgroupOf F`
  haveI : Finite ↥F := Subtype.finite
  have ht' : orderOf (⟨t, htF⟩ : ↥F) = 2 := by rw [← Subgroup.orderOf_coe]; exact ht
  have htH' : (⟨t, htF⟩ : ↥F) ∉ (F ⊓ H).subgroupOf F := by
    intro hmem
    exact htH (Subgroup.mem_subgroupOf.mp hmem).2
  -- `F ⊓ H` is a maximal subgroup of `↥F`
  have hmax' : ∀ M : Subgroup ↥F, (F ⊓ H).subgroupOf F ≤ M → M = (F ⊓ H).subgroupOf F ∨ M = ⊤ := by
    intro M hM
    have hle : F ⊓ H ≤ M.map (Subgroup.subtype F) := by
      intro x hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hx.1⟩, hM (by
        rw [Subgroup.mem_subgroupOf]; exact hx), rfl⟩
    rcases hmax (M.map (Subgroup.subtype F)) hle (Subgroup.map_subtype_le M) with hcase | hcase
    · left
      refine le_antisymm ?_ hM
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      have h1 : (x : G) ∈ M.map (Subgroup.subtype F) := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rwa [hcase] at h1
    · right
      refine le_antisymm le_top fun x _ => ?_
      have h1 : (x : G) ∈ M.map (Subgroup.subtype F) := by rw [hcase]; exact x.2
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h1
      rwa [Subtype.ext hyx] at hy
  -- the (unique) fixed point of `t` in `↥F ⧸ (F ⊓ H).subgroupOf F`
  obtain ⟨b, hb_eq⟩ := Set.ncard_eq_one.mp
    (Work.ThreePoints.ncard_fixedPts_zpowers hFSE ht')
  have hb : (⟨t, htF⟩ : ↥F) • b = b := by
    have h : b ∈ Submission.Blueprint.fixedPts ((F ⊓ H).subgroupOf F)
        (Subgroup.zpowers (⟨t, htF⟩ : ↥F)) := by rw [hb_eq]; exact rfl
    exact (Work.ThreePoints.mem_fixedPts.mp h) _ (Subgroup.mem_zpowers _)
  have hbuniq : ∀ c : ↥F ⧸ (F ⊓ H).subgroupOf F, (⟨t, htF⟩ : ↥F) • c = c → c = b := by
    intro c hc
    have h : c ∈ Submission.Blueprint.fixedPts ((F ⊓ H).subgroupOf F)
        (Subgroup.zpowers (⟨t, htF⟩ : ↥F)) := by
      rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer]
      exact Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff]; exact hc)
    rw [hb_eq] at h
    exact h
  -- Appendix III (1) in the group `↥F`
  have hcore := appIII_one_core (F := ↥F) ((F ⊓ H).subgroupOf F) hFSE hmax' h2rank1 hBrSz hFT
    ht' htH' hb hbuniq
  -- transfer the conclusion back to `G`
  intro g hg
  rw [MulAction.mem_stabilizer_iff]
  have hgF : g ∈ F := hg.1
  have hgtp : g ∈ Submission.Blueprint.twoPoint H t := hg.2
  have hg1 : (⟨g, hgF⟩ : ↥F) ∈ (F ⊓ H).subgroupOf F := by
    rw [Subgroup.mem_subgroupOf]
    exact ⟨hgF, (Work.ThreePoints.mem_twoPoint.mp hgtp).1⟩
  have hg2 : (⟨g, hgF⟩ : ↥F) ∈ Submission.Blueprint.conj (⟨t, htF⟩ : ↥F)
      ((F ⊓ H).subgroupOf F) := by
    rw [Work.ThreePoints.mem_conj_iff, Subgroup.mem_subgroupOf]
    refine ⟨?_, ?_⟩
    · have hcoe : (((⟨t, htF⟩ : ↥F)⁻¹ * ⟨g, hgF⟩ * ⟨t, htF⟩ : ↥F) : G) = t⁻¹ * g * t := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
      rw [hcoe]
      exact F.mul_mem (F.mul_mem (F.inv_mem htF) hgF) htF
    · have hcoe : (((⟨t, htF⟩ : ↥F)⁻¹ * ⟨g, hgF⟩ * ⟨t, htF⟩ : ↥F) : G) = t⁻¹ * g * t := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
      rw [hcoe]
      exact (Work.ThreePoints.mem_twoPoint.mp hgtp).2
  have hgmem : (⟨g, hgF⟩ : ↥F) ∈ (F ⊓ H).subgroupOf F ⊓ Submission.Blueprint.conj
      (⟨t, htF⟩ : ↥F) ((F ⊓ H).subgroupOf F) := ⟨hg1, hg2⟩
  have hgb : (⟨g, hgF⟩ : ↥F) • b = b := MulAction.mem_stabilizer_iff.mp (hcore hgmem)
  -- `b` corresponds to the coset `x H`, whose stabiliser in `G` is the point `ω`
  obtain ⟨x, hxb⟩ := QuotientGroup.mk_surjective b
  have hmem1 : ((⟨g, hgF⟩ : ↥F) * x)⁻¹ * x ∈ (F ⊓ H).subgroupOf F := by
    rw [← hxb, MulAction.Quotient.smul_mk, QuotientGroup.eq] at hgb
    exact hgb
  have hmem2 : ((⟨t, htF⟩ : ↥F) * x)⁻¹ * x ∈ (F ⊓ H).subgroupOf F := by
    have h := hb
    rw [← hxb, MulAction.Quotient.smul_mk, QuotientGroup.eq] at h
    exact h
  have hcoe1 : ((((⟨g, hgF⟩ : ↥F) * x)⁻¹ * x : ↥F) : G) = (x : G)⁻¹ * g⁻¹ * (x : G) := by
    have h1 : ((⟨g, hgF⟩ : ↥F) * x)⁻¹ * x = x⁻¹ * (⟨g, hgF⟩ : ↥F)⁻¹ * x := by group
    rw [h1]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
  have hcoe2 : ((((⟨t, htF⟩ : ↥F) * x)⁻¹ * x : ↥F) : G) = (x : G)⁻¹ * t * (x : G) := by
    have h1 : ((⟨t, htF⟩ : ↥F) * x)⁻¹ * x = x⁻¹ * (⟨t, htF⟩ : ↥F)⁻¹ * x := by group
    rw [h1]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
    rw [inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_orderOf_eq_two ht)]
  have hH1 : (x : G)⁻¹ * g * (x : G) ∈ H := by
    have h := (Subgroup.mem_subgroupOf.mp hmem1).2
    rw [hcoe1] at h
    rw [show (x : G)⁻¹ * g * (x : G) = ((x : G)⁻¹ * g⁻¹ * (x : G))⁻¹ from by group]
    exact H.inv_mem h
  have hH2 : (x : G)⁻¹ * t * (x : G) ∈ H := by
    have h := (Subgroup.mem_subgroupOf.mp hmem2).2
    rwa [hcoe2] at h
  have hfix : t • (((x : G)) : G ⧸ H) = (((x : G)) : G ⧸ H) := by
    rw [Work.ThreePoints.smul_mk, QuotientGroup.eq]
    rw [show (t * (x : G))⁻¹ * (x : G) = (x : G)⁻¹ * t * (x : G) from by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_orderOf_eq_two ht)]]
    exact hH2
  have hω' : ω = (((x : G)) : G ⧸ H) := by
    obtain ⟨y, hy⟩ := Set.ncard_eq_one.mp (Work.ThreePoints.ncard_fixedPts_zpowers hH ht)
    have h1 : (((x : G)) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H (Subgroup.zpowers t) := by
      rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer]
      exact Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff]; exact hfix)
    have h2 : ω ∈ Submission.Blueprint.fixedPts H (Subgroup.zpowers t) := by
      rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer]
      exact Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff]; exact hω)
    rw [hy, Set.mem_singleton_iff] at h1 h2
    exact h2.trans h1.symm
  rw [hω', Work.ThreePoints.smul_mk, QuotientGroup.eq]
  rw [show (g * (x : G))⁻¹ * (x : G) = ((x : G)⁻¹ * g * (x : G))⁻¹ from by group]
  exact H.inv_mem hH1

end Work.ThreePoints.P3NeBot

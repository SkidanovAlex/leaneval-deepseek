import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.FieldTheory.Finite.card_pow_fiber_eq_units_fiber

open scoped BigOperators
open Polynomial
open Classical

namespace Commons.NumberTheory.CharacterSum

lemma geomSum_rootOfUnity {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R] {z : R} {e : ℕ}
    (hz : z ^ e = 1) :
    ∑ j ∈ Finset.range e, z ^ j = if z = 1 then (e : R) else 0 := by
  rcases eq_or_ne z 1 with h | h
  · subst h; rw [if_pos rfl]; simp
  · rw [if_neg h]
    have hmul := geom_sum_mul z e
    rw [hz, sub_self] at hmul
    rcases mul_eq_zero.mp hmul with h0 | h1
    · exact h0
    · exact absurd (sub_eq_zero.mp h1) h

lemma orderOf_toUnitHom_apply_of_generator {F : Type*} [Field F] [Fintype F] (e : ℕ) (he : 0 < e)
    (χ : MulChar F ℂ) (hord : orderOf χ = e) {g : Fˣ}
    (hg : ∀ x : Fˣ, x ∈ Subgroup.zpowers g) :
    orderOf (χ.toUnitHom g) = e := by
  have he_ne : e ≠ 0 := he.ne'
  have hpow : χ ^ e = 1 := by rw [← hord]; exact pow_orderOf_eq_one χ
  refine (orderOf_eq_iff he).mpr ⟨?_, ?_⟩
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, MulChar.coe_toUnitHom]
    rw [← MulChar.pow_apply' χ he_ne (g : F), hpow]
    exact MulChar.one_apply_coe g
  · intro m hm hmp hcon
    have hχm : χ ^ m = 1 := by
      apply MulChar.ext
      intro u
      rw [MulChar.one_apply_coe, MulChar.pow_apply_coe]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg u)
      have huk : χ.toUnitHom u = (χ.toUnitHom g) ^ k := by
        rw [← hk, MonoidHom.map_zpow]
      have key : (((χ.toUnitHom g) ^ k) ^ m : ℂˣ) = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hcon, one_zpow]
      calc χ (↑u : F) ^ m
          = (((χ.toUnitHom u : ℂˣ)) : ℂ) ^ m := by rw [MulChar.coe_toUnitHom]
        _ = ((((χ.toUnitHom u) ^ m : ℂˣ)) : ℂ) := by rw [Units.val_pow_eq_pow_val]
        _ = (((((χ.toUnitHom g) ^ k) ^ m : ℂˣ)) : ℂ) := by rw [huk]
        _ = ((1 : ℂˣ) : ℂ) := by rw [key]
        _ = 1 := rfl
    have hdvd : orderOf χ ∣ m := orderOf_dvd_iff_pow_eq_one.mpr hχm
    rw [hord] at hdvd
    exact Nat.not_dvd_of_pos_of_lt hmp hm hdvd

lemma mem_range_powMonoidHom_iff_apply_eq_one {F : Type*} [Field F] [Fintype F]
    (e : ℕ) (he : 0 < e) (hdiv : e ∣ Fintype.card F - 1)
    (χ : MulChar F ℂ) (hord : orderOf χ = e) (u : Fˣ) :
    u ∈ (powMonoidHom (α := Fˣ) e).range ↔ χ (u : F) = 1 := by
  have he_ne : e ≠ 0 := he.ne'
  have hpow : χ ^ e = 1 := by rw [← hord]; exact pow_orderOf_eq_one χ
  have hn : Nat.card Fˣ = Fintype.card F - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units]
  have he_dvd : e ∣ Nat.card Fˣ := by rw [hn]; exact hdiv
  have hrange : Nat.card (powMonoidHom (α := Fˣ) e).range = Nat.card Fˣ / e := by
    rw [IsCyclic.card_powMonoidHom_range, Nat.gcd_eq_right he_dvd]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hχrange : Nat.card (χ.toUnitHom).range = e := by
    have hgen : Subgroup.zpowers g = ⊤ := le_top.antisymm (fun x _ => hg x)
    rw [MonoidHom.range_eq_map, ← hgen, MonoidHom.map_zpowers, Nat.card_zpowers]
    exact orderOf_toUnitHom_apply_of_generator e he χ hord hg
  have hker : Nat.card (χ.toUnitHom).ker = Nat.card Fˣ / e := by
    have h1 := Subgroup.card_mul_index (χ.toUnitHom).ker
    rw [Subgroup.index_ker, hχrange, mul_comm] at h1
    exact Nat.eq_div_of_mul_eq_right he_ne h1
  have hle : (powMonoidHom (α := Fˣ) e).range ≤ (χ.toUnitHom).ker := by
    intro u hu
    rw [MonoidHom.mem_range] at hu
    obtain ⟨v, hv⟩ := hu
    rw [powMonoidHom_apply] at hv
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [MulChar.coe_toUnitHom, Units.val_one]
    rw [← hv, Units.val_pow_eq_pow_val]
    rw [map_pow, ← MulChar.pow_apply' χ he_ne (v : F), hpow]
    exact MulChar.one_apply_coe v
  have heq : (powMonoidHom (α := Fˣ) e).range = (χ.toUnitHom).ker :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hker, hrange])
  rw [heq, MonoidHom.mem_ker]
  constructor
  · intro h; rw [← MulChar.coe_toUnitHom, h, Units.val_one]
  · intro h; apply Units.ext; rw [MulChar.coe_toUnitHom, h, Units.val_one]

lemma card_fiber_powMonoidHom {G : Type*} [CommGroup G] [Fintype G] (e : ℕ) (u : G) :
    Nat.card {v : G // v ^ e = u} =
      if u ∈ (powMonoidHom e : G →* G).range then Nat.card (powMonoidHom e : G →* G).ker else 0 := by
  by_cases hu : u ∈ (powMonoidHom e : G →* G).range
  · rw [if_pos hu]
    obtain ⟨v0, hv0⟩ := MonoidHom.mem_range.mp hu
    rw [powMonoidHom_apply] at hv0
    have hcard : Nat.card {v : G // v ^ e = u} = Nat.card (powMonoidHom e : G →* G).ker := by
      refine Nat.card_congr ?_
      refine
        { toFun := fun v => ⟨v0⁻¹ * v.1, ?_⟩
          invFun := fun w => ⟨v0 * w.1, ?_⟩
          left_inv := fun v => Subtype.ext (by group)
          right_inv := fun w => Subtype.ext (by group) }
      · rw [MonoidHom.mem_ker, powMonoidHom_apply, mul_pow, inv_pow, hv0, v.2, inv_mul_cancel]
      · have hw : w.1 ^ e = 1 := by
          have := MonoidHom.mem_ker.mp w.2
          rwa [powMonoidHom_apply] at this
        rw [mul_pow, hv0, hw, mul_one]
    rw [hcard]
  · rw [if_neg hu, Nat.card_eq_fintype_card]
    exact Fintype.card_eq_zero_iff.mpr
      ⟨fun v => hu (MonoidHom.mem_range.mpr ⟨v.1, by rw [powMonoidHom_apply]; exact v.2⟩)⟩

lemma point_count_of_mulchar {F : Type*} [Field F] [Fintype F] (e : ℕ) (he : 2 ≤ e)
    (hdiv : e ∣ Fintype.card F - 1) (χ : MulChar F ℂ) (hord : orderOf χ = e) (c : F) :
    (({y : F | y ^ e = c} : Set F).ncard : ℂ)
      = 1 + ∑ j ∈ Finset.Icc 1 (e - 1), (χ ^ j) c := by
  have he0 : 0 < e := by omega
  have he_ne : e ≠ 0 := he0.ne'
  have hpow : χ ^ e = 1 := by rw [← hord]; exact pow_orderOf_eq_one χ
  have hn : Nat.card Fˣ = Fintype.card F - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units]
  have he_dvd : e ∣ Nat.card Fˣ := by rw [hn]; exact hdiv
  have hker : Nat.card (powMonoidHom (α := Fˣ) e).ker = e := by
    rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right he_dvd]
  have hval : ∀ u : Fˣ, (Nat.card {v : Fˣ // v ^ e = u} : ℂ) = if χ (u : F) = 1 then (e : ℂ) else 0 := by
    intro u
    rw [card_fiber_powMonoidHom e u, hker]
    by_cases h : u ∈ (powMonoidHom (α := Fˣ) e).range
    · rw [if_pos h, if_pos ((mem_range_powMonoidHom_iff_apply_eq_one e he0 hdiv χ hord u).mp h)]
    · rw [if_neg h,
        if_neg (fun hh => h ((mem_range_powMonoidHom_iff_apply_eq_one e he0 hdiv χ hord u).mpr hh))]
      simp
  rcases eq_or_ne c 0 with hc | hc
  · subst hc
    have hset : ({y : F | y ^ e = (0 : F)} : Set F) = {0} := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      exact ⟨fun hy => (pow_eq_zero_iff he_ne).mp hy, fun hy => by rw [hy]; exact zero_pow he_ne⟩
    rw [hset, Set.ncard_singleton]
    have hsum : ∑ j ∈ Finset.Icc 1 (e - 1), (χ ^ j) (0 : F) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      exact MulChar.map_zero (χ ^ j)
    rw [hsum, add_zero]
    norm_num
  · have hc_ne : c ≠ 0 := hc
    have hL : (({y : F | y ^ e = c} : Set F).ncard : ℂ)
        = (Nat.card {v : Fˣ // v ^ e = Units.mk0 c hc_ne} : ℂ) := by
      change ((Nat.card {y : F // y ^ e = c} : ℕ) : ℂ) = _
      rw [Commons.FieldTheory.Finite.card_pow_fiber_eq_units_fiber c hc_ne e he0]
    have hR : (1 : ℂ) + ∑ j ∈ Finset.Icc 1 (e - 1), (χ ^ j) c
        = if χ c = 1 then (e : ℂ) else 0 := by
      have hins : Finset.range e = insert 0 (Finset.Icc 1 (e - 1)) := by
        ext j; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      have hnot : (0 : ℕ) ∉ Finset.Icc 1 (e - 1) := by simp only [Finset.mem_Icc]; omega
      have hzero : (χ ^ 0) c = 1 := by
        rw [pow_zero]; exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hc_ne)
      have hfirst : (1 : ℂ) + ∑ j ∈ Finset.Icc 1 (e - 1), (χ ^ j) c
          = ∑ j ∈ Finset.range e, (χ ^ j) c := by
        rw [hins, Finset.sum_insert hnot, hzero]
      rw [hfirst]
      have hsum_eq : ∑ j ∈ Finset.range e, (χ ^ j) c = ∑ j ∈ Finset.range e, (χ c) ^ j := by
        apply Finset.sum_congr rfl
        intro j _
        rcases eq_or_ne j 0 with hj0 | hj0
        · subst hj0; rw [pow_zero, pow_zero]
          exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hc_ne)
        · exact MulChar.pow_apply' χ hj0 c
      have hzc : (χ c) ^ e = 1 := by
        rw [← MulChar.pow_apply' χ he_ne c, hpow]
        exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hc_ne)
      rw [hsum_eq, geomSum_rootOfUnity hzc]
    rw [hL, hval (Units.mk0 c hc_ne), Units.val_mk0, hR]
/-- The number of `F`-points of the affine curve `y ^ e = f x` equals `#F + Σ_{j=1}^{e-1} S_j`,
where `S_j = Σ_x (χ ^ j) (f.eval x)` and `χ` is a multiplicative character of order `e`. -/
theorem superelliptic_point_card {F : Type*} [Field F] [Fintype F] (e : ℕ) (he : 2 ≤ e)
    (hdiv : e ∣ Fintype.card F - 1) (χ : MulChar F ℂ) (hord : orderOf χ = e)
    (f : Polynomial F) :
    (({p : F × F | p.2 ^ e = f.eval p.1} : Set (F × F)).ncard : ℂ)
      = (Fintype.card F : ℂ) + ∑ j ∈ Finset.Icc 1 (e - 1), ∑ x : F, (χ ^ j) (f.eval x) := by
  have h1 : ((({p : F × F | p.2 ^ e = f.eval p.1} : Set (F × F)).ncard : ℂ))
      = ∑ x : F, (Nat.card {y : F // y ^ e = f.eval x} : ℂ) := by
    change ((Nat.card {p : F × F // p.2 ^ e = f.eval p.1} : ℕ) : ℂ) = _
    rw [Nat.card_congr
      ({ toFun := fun p => ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
         invFun := fun q => ⟨(q.1, q.2.1), q.2.2⟩
         left_inv := fun p => by simp
         right_inv := fun q => by simp } :
        {p : F × F // p.2 ^ e = f.eval p.1} ≃
          (Σ x : F, {y : F // y ^ e = f.eval x}))]
    rw [Nat.card_sigma, Nat.cast_sum]
  have h2 : ∀ x : F, (Nat.card {y : F // y ^ e = f.eval x} : ℂ)
      = 1 + ∑ j ∈ Finset.Icc 1 (e - 1), (χ ^ j) (f.eval x) :=
    fun x => point_count_of_mulchar e he hdiv χ hord (f.eval x)
  rw [h1]
  calc ∑ x : F, (Nat.card {y : F // y ^ e = f.eval x} : ℂ)
      = ∑ x : F, (1 + ∑ j ∈ Finset.Icc 1 (e - 1), (χ ^ j) (f.eval x)) :=
        Finset.sum_congr rfl (fun x _ => h2 x)
    _ = (∑ _x : F, (1 : ℂ))
          + ∑ x : F, ∑ j ∈ Finset.Icc 1 (e - 1), (χ ^ j) (f.eval x) :=
        Finset.sum_add_distrib
    _ = (Fintype.card F : ℂ) + ∑ j ∈ Finset.Icc 1 (e - 1), ∑ x : F, (χ ^ j) (f.eval x) := by
        rw [Finset.sum_comm]
        congr 1
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

end Commons.NumberTheory.CharacterSum
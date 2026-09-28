import Mathlib
import Submission.Work.HP.NA.Setup

namespace Work.HP.NA

/-- Complement counting for `Nat.card` over a finite type. -/
theorem natCard_subtype_compl {α : Type*} [Finite α] (p : α → Prop) :
    Nat.card {x // ¬ p x} = Nat.card α - Nat.card {x // p x} := by
  haveI := Fintype.ofFinite α
  haveI : Fintype {x // p x} := Fintype.ofFinite _
  haveI : Fintype {x // ¬ p x} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_subtype_compl p

/-- The subtype of units of a monoid is equivalent to its unit group. -/
noncomputable def isUnit_subtype_equiv_units {α : Type*} [Monoid α] :
    {x : α // IsUnit x} ≃ αˣ where
  toFun x := x.2.unit
  invFun u := ⟨u, u.isUnit⟩
  left_inv x := Subtype.ext (IsUnit.unit_spec x.2)
  right_inv u := Units.ext (IsUnit.unit_spec u.isUnit)

/-- A vector over `ZMod (p^r)` generates the unit ideal iff one of its coordinates is a
unit, i.e. is not divisible by `p`. -/
theorem isPrimMod_iff_exists_isUnit (p r k : ℕ) (hp : p.Prime) (hr : 1 ≤ r)
    (c : Fin k → ZMod (p ^ r)) :
    IsPrimMod (p ^ r) c ↔ ∃ i, IsUnit (c i) := by
  have hne : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  have hexists : ∀ x : ZMod (p ^ r), ¬ IsUnit x →
      ∃ y : ZMod (p ^ r), x = (p : ZMod (p ^ r)) * y := by
    intro x hx
    have hnotdvd : p ∣ x.val := by
      by_contra h
      exact hx (by rw [← ZMod.natCast_zmod_val x]
                   exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp hr).mpr h)
    obtain ⟨m, hm⟩ := hnotdvd
    exact ⟨(m : ZMod (p ^ r)), by rw [← ZMod.natCast_zmod_val x, hm, Nat.cast_mul]⟩
  constructor
  · intro h
    rw [IsPrimMod] at h
    by_contra hcon
    rw [not_exists] at hcon
    have hsubset : Set.range c ⊆
        (Ideal.span ({(p : ZMod (p ^ r))} : Set (ZMod (p ^ r))) : Set _) := by
      rintro x ⟨i, rfl⟩
      obtain ⟨y, hy⟩ := hexists (c i) (hcon i)
      rw [hy]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
    have hle : Ideal.span (Set.range c) ≤
        Ideal.span ({(p : ZMod (p ^ r))} : Set (ZMod (p ^ r))) := Ideal.span_le.mpr hsubset
    have htop : Ideal.span ({(p : ZMod (p ^ r))} : Set (ZMod (p ^ r))) = ⊤ := by
      rw [h] at hle; exact top_le_iff.mp hle
    rw [Ideal.span_singleton_eq_top] at htop
    exact ZMod.prime_natCast_not_isUnit_pow hp (by omega) htop
  · rintro ⟨i, hi⟩
    have h1 : Ideal.span ({c i} : Set (ZMod (p ^ r))) = ⊤ := Ideal.span_singleton_eq_top.mpr hi
    have h2 : Ideal.span ({c i} : Set (ZMod (p ^ r))) ≤ Ideal.span (Set.range c) :=
      Ideal.span_le.mpr (by rintro x rfl; exact Ideal.subset_span (Set.mem_range_self i))
    rw [IsPrimMod]
    apply top_le_iff.mp
    calc ⊤ = Ideal.span ({c i} : Set (ZMod (p ^ r))) := h1.symm
      _ ≤ Ideal.span (Set.range c) := h2

/-- The number of non-units in `ZMod (p^r)` is `p^(r-1)`. -/
theorem card_not_isUnit_zmod_prime_pow (p r : ℕ) (hp : p.Prime) (hr : 1 ≤ r) :
    Nat.card {x : ZMod (p ^ r) // ¬ IsUnit x} = p ^ (r - 1) := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  haveI : Fintype (ZMod (p ^ r))ˣ := Fintype.ofFinite _
  have hunits : Nat.card {x : ZMod (p ^ r) // IsUnit x} = (p ^ r).totient := by
    rw [Nat.card_congr (isUnit_subtype_equiv_units (α := ZMod (p ^ r)))]
    rw [Nat.card_eq_fintype_card]
    exact ZMod.card_units_eq_totient _
  have htot : (p ^ r).totient = p ^ (r - 1) * (p - 1) := Nat.totient_prime_pow hp (by omega)
  have hcomp := natCard_subtype_compl (α := ZMod (p ^ r)) (fun x => IsUnit x)
  rw [hcomp, hunits, htot, Nat.card_zmod]
  have hpr : p ^ r = p ^ (r - 1) * p := by
    conv_lhs => rw [show r = (r - 1) + 1 by omega]
    rw [pow_succ]
  have hpp : p - (p - 1) = 1 := by have := hp.two_le; omega
  rw [hpr, ← Nat.mul_sub_left_distrib, hpp, mul_one]

theorem card_primMod (p r k : ℕ) (hp : p.Prime) (hr : 1 ≤ r) :
    Nat.card {c : Fin k → ZMod (p ^ r) // Work.HP.NA.IsPrimMod (p ^ r) c}
      = (p ^ r) ^ k - p ^ ((r - 1) * k) := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  have hiff : ∀ c : Fin k → ZMod (p ^ r), IsPrimMod (p ^ r) c ↔ ∃ i, IsUnit (c i) :=
    fun c => isPrimMod_iff_exists_isUnit p r k hp hr c
  have hnonunit := card_not_isUnit_zmod_prime_pow p r hp hr
  have e : {c : Fin k → ZMod (p ^ r) // ¬ IsPrimMod (p ^ r) c} ≃
      ((_ : Fin k) → {x : ZMod (p ^ r) // ¬ IsUnit x}) :=
    (Equiv.subtypeEquivRight (fun c => by rw [hiff c]; exact not_exists)).trans
      Equiv.subtypePiEquivPi
  have hnonprim : Nat.card {c : Fin k → ZMod (p ^ r) // ¬ IsPrimMod (p ^ r) c}
      = p ^ ((r - 1) * k) := by
    rw [Nat.card_congr e, Nat.card_fun, Nat.card_fin, hnonunit, ← pow_mul]
  have htotal : Nat.card (Fin k → ZMod (p ^ r)) = (p ^ r) ^ k := by
    rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  classical
  have hsum := Nat.card_congr
    (Equiv.sumCompl (fun c : Fin k → ZMod (p ^ r) => IsPrimMod (p ^ r) c))
  rw [Nat.card_sum] at hsum
  rw [hnonprim, htotal] at hsum
  omega

end Work.HP.NA

import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.GroupTheory.Cyclic.fiber_card_pow_eq_of_pow_eq_one

namespace Commons.NumberTheory.Stepanov

open Polynomial

/-- The number of elements of a subtype equals the sum of the indicator of its predicate. -/
private lemma natCard_subtype_eq_sum {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    Nat.card {a : α // p a} = ∑ a : α, (if p a then (1:ℕ) else 0) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]

/-- `Nat.card` of a subtype agrees with the `Set.ncard` of the corresponding set. -/
private lemma natCard_subtype_eq_ncard {α : Type*} (p : α → Prop) :
    Nat.card {a : α // p a} = ({a : α | p a} : Set α).ncard := rfl

/-- For a finite field `F` of cardinality `q`, an exponent `e` with `1 ≤ e` and `e ∣ q - 1`, and
an element `c : F`, the number of `e`-th roots of `c` in `F` is `e` if `c` is a nonzero `e`-th
power (equivalently `c ^ ((q - 1) / e) = 1`), and `0` otherwise; additionally `0` has the single
`e`-th root `0`.

This is the group-theoretic heart of the point count on the superelliptic curve `y ^ e = f x`:
on `Fˣ` the map `y ↦ y ^ e` is a surjection onto the subgroup of `e`-th powers with all fibers of
size `e`, and that subgroup is `{x : x ^ ((q - 1) / e) = 1}`. -/
lemma natCard_pow_eq (F : Type*) [Field F] [Fintype F] [DecidableEq F] (e : ℕ)
    (he : 1 ≤ e) (hdiv : e ∣ Fintype.card F - 1) (c : F) :
    Nat.card {y : F // y ^ e = c}
      = e * (if c ^ ((Fintype.card F - 1) / e) = 1 then 1 else 0)
        + (if c = 0 then 1 else 0) := by
  classical
  have he0 : e ≠ 0 := by omega
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hb : 1 ≤ (Fintype.card F - 1) / e := by
    rcases Nat.eq_zero_or_pos ((Fintype.card F - 1) / e) with h0 | hpos
    · have hmul := Nat.mul_div_cancel' hdiv
      rw [h0, mul_zero] at hmul
      omega
    · exact hpos
  rcases eq_or_ne c 0 with rfl | hc
  · -- `c = 0`: the only `e`-th root of `0` is `0`.
    have hpow0 : (0 : F) ^ ((Fintype.card F - 1) / e) = 0 := zero_pow (by omega)
    have hsum : Nat.card {y : F // y ^ e = 0} = ∑ y : F, (if y = 0 then (1:ℕ) else 0) := by
      rw [natCard_subtype_eq_sum]
      apply Finset.sum_congr rfl
      intro y _
      simp only [pow_eq_zero_iff he0]
    rw [hsum, hpow0]
    simp only [zero_ne_one, if_false, mul_zero, if_true]
    rw [Finset.sum_ite_eq']
    simp
  · -- `c ≠ 0`: work in the unit group, a finite cyclic group of order `q - 1 = e * ((q-1)/e)`.
    set m : Fˣ := Units.mk0 c hc with hm_def
    have hmc : (m : F) = c := by rw [hm_def, Units.val_mk0]
    have hval : ∀ y : F, y ^ e = c → y ≠ 0 := by
      intro y hy hy0
      rw [hy0, zero_pow he0] at hy
      exact hc hy.symm
    have hto : ∀ y : {y : F // y ^ e = c},
        (Units.mk0 y.1 (hval y.1 y.2)) ^ e = m := by
      intro y
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0, hmc]
      exact y.2
    have hinv : ∀ u : {u : Fˣ // u ^ e = m}, (u.1 : F) ^ e = c := by
      intro u
      have := congrArg (fun z : Fˣ => (z : F)) u.2
      simp only [Units.val_pow_eq_pow_val, hmc] at this
      exact this
    let φ : {y : F // y ^ e = c} ≃ {u : Fˣ // u ^ e = m} :=
      { toFun := fun y => ⟨Units.mk0 y.1 (hval y.1 y.2), hto y⟩
        invFun := fun u => ⟨(u.1 : F), hinv u⟩
        left_inv := by
          intro y; apply Subtype.ext; simp only [Units.val_mk0]
        right_inv := by
          intro u; apply Subtype.ext; apply Units.ext; simp only [Units.val_mk0] }
    have hcardG : Nat.card Fˣ = ((Fintype.card F - 1) / e) * e := by
      rw [Nat.card_eq_fintype_card, Fintype.card_units, Nat.div_mul_cancel hdiv]
    have hcond : (m ^ ((Fintype.card F - 1) / e) = 1) ↔
        (c ^ ((Fintype.card F - 1) / e) = 1) := by
      constructor
      · intro h
        have := congrArg (fun z : Fˣ => (z : F)) h
        simpa only [Units.val_pow_eq_pow_val, Units.val_one, hmc] using this
      · intro h
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_one, hmc]
        exact h
    rw [Nat.card_congr φ, if_neg hc]
    by_cases h : c ^ ((Fintype.card F - 1) / e) = 1
    · rw [if_pos h]
      rw [Commons.GroupTheory.Cyclic.fiber_card_pow_eq_of_pow_eq_one e
        ((Fintype.card F - 1) / e) he hcardG m (hcond.mpr h)]
      simp
    · rw [if_neg h]
      have hempty : IsEmpty {u : Fˣ // u ^ e = m} := ⟨fun u => by
        have h1 : m ^ ((Fintype.card F - 1) / e) = 1 := by
          have hek : e * ((Fintype.card F - 1) / e) = Fintype.card F - 1 :=
            Nat.mul_div_cancel' hdiv
          have hpc : u.1 ^ (Fintype.card F - 1) = 1 := by
            have h1u : u.1 ^ Nat.card Fˣ = 1 := pow_card_eq_one'
            rwa [Nat.card_eq_fintype_card, Fintype.card_units] at h1u
          rw [← u.2, ← pow_mul, hek]
          exact hpc
        exact h (hcond.mp h1)⟩
      rw [Nat.card_eq_zero.mpr (Or.inl hempty)]
      simp

/-- Splitting a subset of a product by its first coordinate. -/
private def equivPoints (F : Type*) [CommSemiring F] (e : ℕ) (f : Polynomial F) :
    {p : F × F // p.2 ^ e = f.eval p.1} ≃ Σ a : F, {y : F // y ^ e = f.eval a} :=
  { toFun := fun p => ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
    invFun := fun s => ⟨(s.1, s.2.1), s.2.2⟩
    left_inv := by intro p; cases p with | mk pv hp => cases pv with | mk a b => rfl
    right_inv := by intro s; cases s with | mk a y => cases y with | mk b hb => rfl }

/-- The number of `F`-points `(x,y)` of the superelliptic curve `y ^ e = f x` over a finite
field `F` (with `e ∣ #F - 1`) equals `e` times the number of `x` for which `f x` is a
nonzero `e`-th power (equivalently `(f x) ^ ((#F - 1)/e) = 1`), plus the number of roots of
`f` in `F`. -/
theorem ncard_points_superelliptic (F : Type*) [Field F] [Fintype F] (e : ℕ) (he : 1 ≤ e)
    (hdiv : e ∣ Fintype.card F - 1) (f : Polynomial F) :
    (({p : F × F | p.2 ^ e = f.eval p.1} : Set (F × F)).ncard)
      = e * ({a : F | f.eval a ^ ((Fintype.card F - 1) / e) = 1} : Set F).ncard
        + ({a : F | f.eval a = 0} : Set F).ncard := by
  classical
  -- Split the point set by first coordinate: the fibre over `a` has `Nat.card {y // y^e = f a}`
  -- points.
  have hstep1 : (({p : F × F | p.2 ^ e = f.eval p.1} : Set (F × F)).ncard)
      = ∑ a : F, Nat.card {y : F // y ^ e = f.eval a} := by
    rw [← Nat.card_coe_set_eq]
    show Nat.card {p : F × F // p.2 ^ e = f.eval p.1}
        = ∑ a : F, Nat.card {y : F // y ^ e = f.eval a}
    rw [Nat.card_congr (equivPoints F e f), Nat.card_sigma]
  -- Evaluate each fibre.
  have hstep2 : (∑ a : F, Nat.card {y : F // y ^ e = f.eval a})
      = ∑ a : F, (e * (if f.eval a ^ ((Fintype.card F - 1) / e) = 1 then 1 else 0)
          + (if f.eval a = 0 then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro a _
    exact natCard_pow_eq F e he hdiv (f.eval a)
  -- Rearrange the sum.
  have hstep3 : (∑ a : F, (e * (if f.eval a ^ ((Fintype.card F - 1) / e) = 1 then 1 else 0)
          + (if f.eval a = 0 then 1 else 0)))
      = e * Nat.card {a : F // f.eval a ^ ((Fintype.card F - 1) / e) = 1}
        + Nat.card {a : F // f.eval a = 0} := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 1
    · rw [natCard_subtype_eq_sum]
    · rw [natCard_subtype_eq_sum]
  -- Go back from subtypes to sets.
  have hstep4 : e * Nat.card {a : F // f.eval a ^ ((Fintype.card F - 1) / e) = 1}
        + Nat.card {a : F // f.eval a = 0}
      = e * ({a : F | f.eval a ^ ((Fintype.card F - 1) / e) = 1} : Set F).ncard
        + ({a : F | f.eval a = 0} : Set F).ncard := by
    rw [natCard_subtype_eq_ncard, natCard_subtype_eq_ncard]
  rw [hstep1, hstep2, hstep3, hstep4]

end Commons.NumberTheory.Stepanov
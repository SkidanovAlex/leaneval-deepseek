import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.FunLike.Fintype
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Submission.Commons.FieldTheory.Finite.sum_erase_zero_eq_units

open AddChar MulChar
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000

namespace Commons.FieldTheory.Finite

noncomputable instance instFintypeMulCharC (F : Type*) [Field F] [Fintype F] :
    Fintype (MulChar F ℂ) := Fintype.ofFinite _

/-! ### Character orthogonality for the annihilator of a subgroup -/

private lemma sum_eq_zero_of_monoidHom_ne_one {G : Type*} [CommGroup G] [Fintype G]
    (f : G → ℂ) (hmul : ∀ a b, f (a * b) = f a * f b) (_hone : f 1 = 1)
    (hne : ∃ a, f a ≠ 1) : ∑ g : G, f g = 0 := by
  obtain ⟨a, ha⟩ := hne
  have hkey : (∑ g : G, f g) = f a * ∑ g : G, f g := by
    calc (∑ g : G, f g) = ∑ g : G, f (a * g) := by
          rw [← Equiv.sum_comp (Equiv.mulLeft a) f]; simp [Equiv.coe_mulLeft]
      _ = f a * ∑ g : G, f g := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun g _ => hmul a g)
  have h2 : (f a - 1) * (∑ g : G, f g) = 0 := by
    have h3 : f a * (∑ g : G, f g) = ∑ g : G, f g := hkey.symm
    rw [sub_mul, one_mul, h3, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr ha)

theorem sum_annihilator_eq_of_mem {F : Type*} [Field F] [Fintype F] (H : Subgroup Fˣ)
    (y : Fˣ) (hy : y ∈ H) :
    (∑ χ : ↥((MulChar.subgroupOrderIsoSubgroupMulChar F ℂ H).ofDual),
        (χ : MulChar F ℂ) (y : F)) = (Nat.card (Fˣ ⧸ H) : ℂ) := by
  classical
  set X : Subgroup (MulChar F ℂ) := (MulChar.subgroupOrderIsoSubgroupMulChar F ℂ H).ofDual with hX
  have hcard : Nat.card ↥X = Nat.card (Fˣ ⧸ H) := by
    rw [hX]; exact MulChar.card_subgroupOrderIsoSubgroupMulChar
  have h1 : ∀ χ : ↥X, (χ : MulChar F ℂ) (y : F) = 1 := by
    intro χ
    have hχ : (χ : MulChar F ℂ) ∈
        OrderDual.ofDual ((MulChar.subgroupOrderIsoSubgroupMulChar F ℂ) H) := by
      rw [← hX]; exact χ.2
    exact (MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff (H := H)).1 hχ y hy
  rw [Finset.sum_congr rfl (fun χ _ => h1 χ), Finset.sum_const, Finset.card_univ]
  have hc : Fintype.card ↥X = Nat.card (Fˣ ⧸ H) := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  rw [hc, nsmul_eq_mul, mul_one]

theorem sum_annihilator_eq_of_not_mem {F : Type*} [Field F] [Fintype F] (H : Subgroup Fˣ)
    (y : Fˣ) (hy : y ∉ H) :
    (∑ χ : ↥((MulChar.subgroupOrderIsoSubgroupMulChar F ℂ H).ofDual),
        (χ : MulChar F ℂ) (y : F)) = 0 := by
  classical
  set X : Subgroup (MulChar F ℂ) := (MulChar.subgroupOrderIsoSubgroupMulChar F ℂ H).ofDual with hX
  have hsymm : (MulChar.subgroupOrderIsoSubgroupMulChar F ℂ).symm (OrderDual.toDual X) = H := by
    rw [hX, OrderDual.toDual_ofDual, OrderIso.symm_apply_apply]
  have hex : ∃ χ : ↥X, (χ : MulChar F ℂ) (y : F) ≠ 1 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    apply hy
    rw [← hsymm]
    rw [MulChar.mem_subgroupOrderIsoSubgroupMulChar_symm_iff]
    intro χ hχ
    exact hcon ⟨χ, hχ⟩
  refine sum_eq_zero_of_monoidHom_ne_one (fun χ : ↥X => (χ : MulChar F ℂ) (y : F)) ?_ ?_ hex
  · intro a b
    rw [Subgroup.coe_mul, MulChar.mul_apply]
  · rw [Subgroup.coe_one]
    exact MulChar.one_apply y.isUnit

/-! ### Gauss sums -/

theorem normSq_gaussSum_eq_card {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (hχ : χ ≠ 1) (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) :
    Complex.normSq (gaussSum χ ψ) = (Fintype.card F : ℝ) := by
  have h := gaussSum_mul_gaussSum_eq_card (R := F) (R' := ℂ) hχ
    (AddChar.IsPrimitive.of_ne_one hψ)
  rw [← star_gaussSum_eq χ ψ] at h
  have h2 : ((Complex.normSq (gaussSum χ ψ) : ℝ) : ℂ) = (Fintype.card F : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    rw [show (starRingEnd ℂ) (gaussSum χ ψ) = star (gaussSum χ ψ) from rfl, mul_comm, h]
  exact_mod_cast h2

theorem gaussSum_eq_sum_units {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    gaussSum χ ψ = ∑ y : Fˣ, (χ : MulChar F ℂ) (y : F) * ψ (y : F) := by
  classical
  rw [gaussSum]
  have h0 : χ (0 : F) * ψ (0 : F) = 0 := by
    rw [MulChar.map_nonunit χ (by simp), zero_mul]
  have hins : (Finset.univ : Finset F) = insert 0 (Finset.univ.erase 0) := by
    ext a; simp
  rw [hins, Finset.sum_insert (Finset.notMem_erase _ _), h0, zero_add]
  exact Commons.FieldTheory.Finite.sum_erase_zero_eq_units (fun a : F => χ a * ψ a)

/-! ### The period bound for a subgroup -/

theorem norm_sum_filter_le {F : Type*} [Field F] [Fintype F]
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (H : Subgroup Fˣ) [DecidablePred (· ∈ H)] :
    ‖∑ y : Fˣ, if y ∈ H then ψ (y : F) else 0‖ ≤ Real.sqrt (Fintype.card F) := by
  classical
  set X : Subgroup (MulChar F ℂ) := (MulChar.subgroupOrderIsoSubgroupMulChar F ℂ H).ofDual with hX
  have hcardX : Nat.card (Fˣ ⧸ H) = Nat.card ↥X := by
    rw [hX]; exact (MulChar.card_subgroupOrderIsoSubgroupMulChar).symm
  set S : ℂ := ∑ y : Fˣ, if y ∈ H then ψ (y : F) else 0 with hS
  have hkey : (Nat.card ↥X : ℂ) * S = ∑ χ : ↥X, gaussSum (χ : MulChar F ℂ) ψ := by
    rw [hS]
    have hx : ∀ y : Fˣ, (∑ χ : ↥X, (χ : MulChar F ℂ) (y : F)) =
        (Nat.card ↥X : ℂ) * (if y ∈ H then 1 else 0) := by
      intro y
      by_cases hy : y ∈ H
      · rw [sum_annihilator_eq_of_mem H y hy, if_pos hy, mul_one, hcardX]
      · rw [sum_annihilator_eq_of_not_mem H y hy, if_neg hy, mul_zero]
    calc (Nat.card ↥X : ℂ) * (∑ y : Fˣ, if y ∈ H then ψ (y : F) else 0)
        = ∑ y : Fˣ, (Nat.card ↥X : ℂ) * (if y ∈ H then ψ (y : F) else 0) := by
            rw [Finset.mul_sum]
      _ = ∑ y : Fˣ, (∑ χ : ↥X, (χ : MulChar F ℂ) (y : F)) * ψ (y : F) := by
            refine Finset.sum_congr rfl (fun y _ => ?_)
            rw [hx y]
            by_cases hy : y ∈ H <;> simp [hy]
      _ = ∑ y : Fˣ, ∑ χ : ↥X, (χ : MulChar F ℂ) (y : F) * ψ (y : F) := by
            refine Finset.sum_congr rfl (fun y _ => ?_)
            rw [Finset.sum_mul]
      _ = ∑ χ : ↥X, ∑ y : Fˣ, (χ : MulChar F ℂ) (y : F) * ψ (y : F) :=
            Finset.sum_comm (s := (Finset.univ : Finset Fˣ)) (t := (Finset.univ : Finset ↥X))
              (f := fun y χ => (χ : MulChar F ℂ) (y : F) * ψ (y : F))
      _ = ∑ χ : ↥X, gaussSum (χ : MulChar F ℂ) ψ := by
            refine Finset.sum_congr rfl (fun χ _ => ?_)
            rw [gaussSum_eq_sum_units]
  have hbnd : ∀ χ : ↥X, ‖gaussSum (χ : MulChar F ℂ) ψ‖ ≤ Real.sqrt (Fintype.card F) := by
    intro χ
    by_cases hχ : (χ : MulChar F ℂ) = 1
    · rw [hχ, gaussSum_one_left hψ, norm_neg, norm_one, Real.one_le_sqrt]
      exact_mod_cast Fintype.card_pos
    · have hn := normSq_gaussSum_eq_card (χ : MulChar F ℂ) hχ ψ hψ
      rw [Complex.normSq_eq_norm_sq] at hn
      rw [← Real.sqrt_sq (norm_nonneg (gaussSum (χ : MulChar F ℂ) ψ)), hn]
  have hXpos : 0 < (Nat.card ↥X : ℝ) := by
    have : 0 < Nat.card ↥X := Nat.card_pos
    exact_mod_cast this
  have h1 : (Nat.card ↥X : ℝ) * ‖S‖ ≤
      (Nat.card ↥X : ℝ) * Real.sqrt (Fintype.card F) := by
    calc (Nat.card ↥X : ℝ) * ‖S‖ = ‖(Nat.card ↥X : ℂ) * S‖ := by
            rw [norm_mul, norm_natCast]
      _ = ‖∑ χ : ↥X, gaussSum (χ : MulChar F ℂ) ψ‖ := by rw [hkey]
      _ ≤ ∑ χ : ↥X, ‖gaussSum (χ : MulChar F ℂ) ψ‖ := norm_sum_le _ _
      _ ≤ ∑ _χ : ↥X, Real.sqrt (Fintype.card F) := Finset.sum_le_sum (fun χ _ => hbnd χ)
      _ = (Nat.card ↥X : ℝ) * Real.sqrt (Fintype.card F) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            have hc : Fintype.card ↥X = Nat.card ↥X := (Nat.card_eq_fintype_card).symm
            rw [hc]
  exact le_of_mul_le_mul_left h1 hXpos

/-! ### Möbius inversion on a finite group -/

private lemma sum_moebius_divisors {R : Type*} [CommRing R] {n : ℕ} (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : R)) = if n = 1 then 1 else 0 := by
  have hf : ∀ m > 0, ∑ i ∈ m.divisors, (if i = 1 then (1:R) else 0) = (1:R) := by
    intro m hm
    have h1 : 1 ∈ m.divisors := Nat.mem_divisors.mpr ⟨one_dvd m, hm.ne'⟩
    rw [Finset.sum_ite_eq' _ 1, if_pos h1]
  have key := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := R)
      (f := fun i => if i = 1 then (1:R) else 0) (g := fun _ => (1:R))).mp hf n
      (Nat.pos_of_ne_zero hn)
  have hconv : (∑ x ∈ n.divisorsAntidiagonal,
        ((ArithmeticFunction.moebius x.1 : ℤ) : R) * (1:R))
      = ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : R) := by
    rw [Nat.sum_divisorsAntidiagonal
      (f := fun i _ => ((ArithmeticFunction.moebius i : ℤ) : R) * (1:R))]
    simp
  rw [← hconv]
  exact key

private lemma ite_orderOf_eq_sum_moebius {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {R : Type*} [CommRing R] (x : G) (e : ℕ) (hx : x ^ e = 1) :
    (if orderOf x = e then (1:R) else 0) =
      ∑ d ∈ e.divisors, ((ArithmeticFunction.moebius d : ℤ) : R) *
        (if x ^ (e / d) = 1 then (1:R) else 0) := by
  classical
  by_cases he : e = 0
  · subst he
    rw [Nat.divisors_zero, Finset.sum_empty]
    have : orderOf x ≠ 0 := (orderOf_pos x).ne'
    simp [this]
  · have hepos : 0 < e := Nat.pos_of_ne_zero he
    set m := orderOf x with hmdef
    have hm : m ∣ e := orderOf_dvd_iff_pow_eq_one.mpr hx
    have hmpos : 0 < m := orderOf_pos x
    have hk : e / m ≠ 0 := by
      rw [Nat.div_ne_zero_iff]; exact ⟨hmpos.ne', Nat.le_of_dvd hepos hm⟩
    have hstep : ∀ d ∈ e.divisors,
        ((ArithmeticFunction.moebius d : ℤ) : R) * (if x ^ (e / d) = 1 then (1:R) else 0)
          = if d ∣ e / m then ((ArithmeticFunction.moebius d : ℤ) : R) else 0 := by
      intro d hd
      have hde : d ∣ e := (Nat.mem_divisors.mp hd).1
      have hiff : (x ^ (e / d) = 1) ↔ d ∣ e / m := by
        rw [← orderOf_dvd_iff_pow_eq_one, ← hmdef]
        show m ∣ e / d ↔ d ∣ e / m
        rw [Nat.dvd_div_iff_mul_dvd hde, Nat.dvd_div_iff_mul_dvd hm]
        constructor <;> intro h <;> rwa [Nat.mul_comm] at h
      by_cases h : d ∣ e / m
      · rw [if_pos h, if_pos (hiff.mpr h), mul_one]
      · rw [if_neg h, if_neg (fun hc => h (hiff.mp hc)), mul_zero]
    rw [Finset.sum_congr rfl hstep, ← Finset.sum_filter]
    have hseteq : e.divisors.filter (fun d => d ∣ e / m) = (e / m).divisors := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hde, _⟩, hdk⟩
        exact ⟨hdk, hk⟩
      · rintro ⟨hdk, _⟩
        exact ⟨⟨hdk.trans (Nat.div_dvd_of_dvd hm), he⟩, hdk⟩
    rw [hseteq, sum_moebius_divisors hk]
    by_cases hme : m = e
    · rw [if_pos hme, if_pos (by rw [hme, Nat.div_self hepos])]
    · rw [if_neg hme, if_neg (fun h => hme (by
        have h2 := Nat.mul_div_cancel' hm
        rw [h, mul_one] at h2; exact h2))]

theorem sum_ite_orderOf_eq_sum_divisors_moebius {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] {R : Type*} [CommRing R] (f : G → R) (e : ℕ) (he : ∀ x : G, x ^ e = 1) :
    (∑ x : G, if orderOf x = e then f x else 0)
      = ∑ d ∈ e.divisors, ((ArithmeticFunction.moebius d : ℤ) : R) *
          ∑ x : G, if x ^ (e / d) = 1 then f x else 0 := by
  classical
  have h1 : (∑ x : G, if orderOf x = e then f x else 0)
      = ∑ x : G, ∑ d ∈ e.divisors, ((ArithmeticFunction.moebius d : ℤ) : R) *
            (if x ^ (e / d) = 1 then f x else 0) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have hpt := ite_orderOf_eq_sum_moebius (R := R) x e (he x)
    have hfx : (if orderOf x = e then f x else 0) =
        f x * (if orderOf x = e then (1:R) else 0) := by
      by_cases hp : orderOf x = e <;> simp [hp]
    rw [hfx, hpt, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    by_cases hd : x ^ (e / d) = 1
    · simp only [hd, ite_true, mul_one]; ring
    · simp only [hd, ite_false, mul_zero]
  have h2 : (∑ x : G, ∑ d ∈ e.divisors, ((ArithmeticFunction.moebius d : ℤ) : R) *
            (if x ^ (e / d) = 1 then f x else 0))
      = ∑ d ∈ e.divisors, ∑ x : G, ((ArithmeticFunction.moebius d : ℤ) : R) *
            (if x ^ (e / d) = 1 then f x else 0) :=
    Finset.sum_comm (s := (Finset.univ : Finset G)) (t := e.divisors)
      (f := fun x d => ((ArithmeticFunction.moebius d : ℤ) : R) *
        (if x ^ (e / d) = 1 then f x else 0))
  have h3 : (∑ d ∈ e.divisors, ∑ x : G, ((ArithmeticFunction.moebius d : ℤ) : R) *
            (if x ^ (e / d) = 1 then f x else 0))
      = ∑ d ∈ e.divisors, ((ArithmeticFunction.moebius d : ℤ) : R) *
            ∑ x : G, if x ^ (e / d) = 1 then f x else 0 := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Finset.mul_sum]
  rw [h1, h2, h3]

private lemma natCard_subtype_eq_sum_one {α : Type*} [Fintype α] (P : α → Prop)
    [DecidablePred P] :
    (Nat.card {x : α // P x} : ℂ) = ∑ x : α, if P x then (1:ℂ) else 0 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.card_filter]
  push_cast
  rw [Finset.sum_boole]

private lemma sqrt_le_natSqrt_add_one (q : ℕ) :
    Real.sqrt (q : ℝ) ≤ (Nat.sqrt q : ℝ) + 1 := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h2 : q < (Nat.sqrt q + 1) * (Nat.sqrt q + 1) := Nat.lt_succ_sqrt q
  have h3 : ((Nat.sqrt q : ℝ) + 1) ^ 2
      = ((Nat.sqrt q + 1 : ℕ) : ℝ) * ((Nat.sqrt q + 1 : ℕ) : ℝ) := by
    push_cast; ring
  rw [h3]
  exact_mod_cast le_of_lt h2

/-! ### The main theorem -/

theorem count_generators_trace_zero_le_char {F : Type*} [Field F] [Fintype F] (p : ℕ)
    [Fact (Nat.Prime p)] [Algebra (ZMod p) F] [CharP F p] :
    Nat.card {x : Fˣ // orderOf x = Fintype.card F - 1 ∧
      Algebra.trace (ZMod p) F (x : F) = 0}
      ≤ (Nat.totient (Fintype.card F - 1)
          + (p - 1) * (Nat.divisors (Fintype.card F - 1)).card
              * (Nat.sqrt (Fintype.card F) + 1)) / p := by
  classical
  have hp : p.Prime := Fact.out
  have hnzp : NeZero p := ⟨hp.ne_zero⟩
  have hcardU : Fintype.card Fˣ = Fintype.card F - 1 := by
    rw [← Nat.card_eq_fintype_card (α := Fˣ), Nat.card_units F,
      Nat.card_eq_fintype_card (α := F)]
  rw [← hcardU]
  set e : ℕ := Fintype.card Fˣ with he
  -- the additive character on `ZMod p`
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ p
  let ψ : AddChar (ZMod p) ℂ := AddChar.zmodChar p hζ.pow_eq_one
  have hψne : ψ ≠ 1 := by
    rw [AddChar.zmod_char_ne_one_iff]
    have h1 : ψ 1 = ζ := by
      show AddChar.zmodChar p hζ.pow_eq_one (1 : ZMod p) = ζ
      rw [show (1 : ZMod p) = ((1:ℕ) : ZMod p) from by simp, AddChar.zmodChar_apply']
      simp
    rw [h1]; exact hζ.ne_one hp.one_lt
  have hψprim : ψ.IsPrimitive := AddChar.IsPrimitive.of_ne_one hψne
  have hψb : ∀ b : ZMod p, b ≠ 0 → ψ b ≠ 1 := fun b hb h =>
    hb ((hψprim.zmod_char_eq_one_iff p b).mp h)
  -- the trace is nonzero
  have htr_exists : ∃ x : F, Algebra.trace (ZMod p) F x ≠ 0 := by
    have htr : Algebra.trace (ZMod p) F ≠ 0 := Algebra.trace_ne_zero (ZMod p) F
    by_contra h; push Not at h; exact htr (LinearMap.ext h)
  -- the additive characters `x ↦ ψ (a * Tr x)`
  let ψa : ZMod p → AddChar F ℂ := fun a =>
    { toFun := fun x => ψ (a * Algebra.trace (ZMod p) F x)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := by
        intro x y
        rw [map_add, mul_add, AddChar.map_add_eq_mul] }
  have hψa_val : ∀ (a : ZMod p) (x : F),
      ψa a x = ψ (a * Algebra.trace (ZMod p) F x) := fun a x => rfl
  have hψa0 : ψa 0 = 1 := by
    ext x
    rw [hψa_val, zero_mul, AddChar.map_zero_eq_one, AddChar.one_apply]
  have hψane : ∀ a : ZMod p, a ≠ 0 → ψa a ≠ 1 := by
    intro a ha h1
    obtain ⟨x, hx⟩ := htr_exists
    have hx1 : ψa a x = 1 := by rw [h1]; exact AddChar.one_apply x
    have hx1' : ψ (a * Algebra.trace (ZMod p) F x) = 1 := by
      simpa only [hψa_val] using hx1
    exact hψb (a * Algebra.trace (ZMod p) F x) (mul_ne_zero ha hx) hx1'
  -- the counting identity
  have h2 : ∀ x : Fˣ, (∑ a : ZMod p, ψa a (x : F)) =
      if Algebra.trace (ZMod p) F (x : F) = 0 then (p : ℂ) else 0 := by
    intro x
    have hs : (∑ a : ZMod p, ψ (a * Algebra.trace (ZMod p) F (x : F)))
        = (if Algebra.trace (ZMod p) F (x : F) = 0 then (p : ℂ) else 0) := by
      rw [AddChar.sum_mulShift (ψ := ψ) (Algebra.trace (ZMod p) F (x : F)) hψprim,
        ZMod.card p]
      split_ifs <;> simp
    simpa only [hψa_val] using hs
  have hTN : (((p * Nat.card {x : Fˣ // orderOf x = e ∧
        Algebra.trace (ZMod p) F (x : F) = 0}) : ℕ) : ℂ)
      = ∑ a : ZMod p, ∑ x : Fˣ, if orderOf x = e then ψa a (x : F) else 0 := by
    have hNsum : ((Nat.card {x : Fˣ // orderOf x = e ∧
          Algebra.trace (ZMod p) F (x : F) = 0}) : ℂ)
        = ∑ x : Fˣ, if (orderOf x = e ∧
            Algebra.trace (ZMod p) F (x : F) = 0) then (1 : ℂ) else 0 :=
      natCard_subtype_eq_sum_one _
    have hpoint : ∀ x : Fˣ, (if (orderOf x = e ∧
            Algebra.trace (ZMod p) F (x : F) = 0) then (p : ℂ) else 0)
        = ∑ a : ZMod p, if orderOf x = e then ψa a (x : F) else 0 := by
      intro x
      by_cases h1 : orderOf x = e
      · have hsum : (∑ a : ZMod p, if orderOf x = e then ψa a (x : F) else 0)
            = ∑ a : ZMod p, ψa a (x : F) := by
          refine Finset.sum_congr rfl (fun a _ => ?_); rw [if_pos h1]
        rw [hsum, h2 x]
        by_cases h3 : Algebra.trace (ZMod p) F (x : F) = 0
        · rw [if_pos ⟨h1, h3⟩, if_pos h3]
        · rw [if_neg (fun hc => h3 hc.2), if_neg h3]
      · rw [if_neg (fun hc => h1 hc.1)]
        rw [Finset.sum_eq_zero (fun a _ => by rw [if_neg h1])]
    calc (((p * Nat.card {x : Fˣ // orderOf x = e ∧
            Algebra.trace (ZMod p) F (x : F) = 0}) : ℕ) : ℂ)
        = (p : ℂ) * (Nat.card {x : Fˣ // orderOf x = e ∧
            Algebra.trace (ZMod p) F (x : F) = 0} : ℂ) := by push_cast; ring
      _ = (p : ℂ) * ∑ x : Fˣ, if (orderOf x = e ∧
            Algebra.trace (ZMod p) F (x : F) = 0) then (1 : ℂ) else 0 := by rw [hNsum]
      _ = ∑ x : Fˣ, (p : ℂ) * (if (orderOf x = e ∧
            Algebra.trace (ZMod p) F (x : F) = 0) then (1 : ℂ) else 0) := by
            rw [Finset.mul_sum]
      _ = ∑ x : Fˣ, (if (orderOf x = e ∧
            Algebra.trace (ZMod p) F (x : F) = 0) then (p : ℂ) else 0) := by
            refine Finset.sum_congr rfl (fun x _ => ?_)
            by_cases hh : (orderOf x = e ∧ Algebra.trace (ZMod p) F (x : F) = 0)
            <;> simp [hh]
      _ = ∑ x : Fˣ, ∑ a : ZMod p, if orderOf x = e then ψa a (x : F) else 0 := by
            refine Finset.sum_congr rfl (fun x _ => hpoint x)
      _ = ∑ a : ZMod p, ∑ x : Fˣ, if orderOf x = e then ψa a (x : F) else 0 :=
            Finset.sum_comm (s := (Finset.univ : Finset Fˣ))
              (t := (Finset.univ : Finset (ZMod p)))
              (f := fun x a => if orderOf x = e then ψa a (x : F) else 0)
  -- T_0
  have hcount : Nat.card {x : Fˣ // orderOf x = e} = Nat.totient e := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsCyclic.card_orderOf_eq_totient (d := e) (by rw [he])
  have hT0 : (∑ x : Fˣ, if orderOf x = e then ψa 0 (x : F) else 0)
      = (Nat.totient e : ℂ) := by
    have hz : ∀ x : Fˣ, ψa 0 (x : F) = 1 := fun x => by
      rw [hψa0]; exact AddChar.one_apply (x : F)
    rw [Finset.sum_congr rfl (fun x _ => by rw [hz x])]
    rw [← natCard_subtype_eq_sum_one (fun x : Fˣ => orderOf x = e), hcount]
  -- bound on each T_a
  have hTbound : ∀ a : ZMod p, a ≠ 0 →
      ‖∑ x : Fˣ, if orderOf x = e then ψa a (x : F) else 0‖
        ≤ ((Nat.divisors e).card : ℝ) * Real.sqrt (Fintype.card F) := by
    intro a ha
    rw [sum_ite_orderOf_eq_sum_divisors_moebius (R := ℂ) (f := fun x : Fˣ => ψa a (x : F)) e
      (fun x => by rw [he]; exact pow_card_eq_one)]
    have hinner : ∀ d ∈ e.divisors,
        ‖∑ x : Fˣ, if x ^ (e / d) = 1 then ψa a (x : F) else 0‖
          ≤ Real.sqrt (Fintype.card F) := by
      intro d _
      have hsub : (∑ x : Fˣ, if x ^ (e / d) = 1 then ψa a (x : F) else 0)
          = ∑ x : Fˣ, if x ∈ (powMonoidHom (e / d) : Fˣ →* Fˣ).ker then ψa a (x : F) else 0 := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        by_cases hx : x ^ (e / d) = 1
        · have hm : x ∈ (powMonoidHom (e / d) : Fˣ →* Fˣ).ker := by
            rw [MonoidHom.mem_ker, powMonoidHom_apply]; exact hx
          rw [if_pos hx, if_pos hm]
        · have hm : x ∉ (powMonoidHom (e / d) : Fˣ →* Fˣ).ker := by
            rw [MonoidHom.mem_ker, powMonoidHom_apply]; exact hx
          rw [if_neg hx, if_neg hm]
      rw [hsub]
      exact norm_sum_filter_le (ψa a) (hψane a ha) ((powMonoidHom (e / d) : Fˣ →* Fˣ).ker)
    calc ‖∑ d ∈ e.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
              (∑ x : Fˣ, if x ^ (e / d) = 1 then ψa a (x : F) else 0)‖
        ≤ ∑ d ∈ e.divisors, ‖((ArithmeticFunction.moebius d : ℤ) : ℂ) *
              (∑ x : Fˣ, if x ^ (e / d) = 1 then ψa a (x : F) else 0)‖ := norm_sum_le _ _
      _ ≤ ∑ _d ∈ e.divisors, (1 : ℝ) * Real.sqrt (Fintype.card F) := by
            refine Finset.sum_le_sum (fun d hd => ?_)
            rw [norm_mul]
            have hμ : ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ 1 := by
              rw [Complex.norm_intCast, ← Int.cast_abs]
              exact_mod_cast ArithmeticFunction.abs_moebius_le_one
            exact mul_le_mul hμ (hinner d hd) (norm_nonneg _) (by norm_num)
      _ = ((Nat.divisors e).card : ℝ) * Real.sqrt (Fintype.card F) := by
            rw [Finset.sum_const, nsmul_eq_mul, one_mul]
  -- sum the bounds
  have hsumSplit : ∑ a : ZMod p, ‖∑ x : Fˣ, if orderOf x = e then ψa a (x : F) else 0‖
      ≤ (Nat.totient e : ℝ) + ((p:ℝ) - 1) * ((Nat.divisors e).card : ℝ)
          * Real.sqrt (Fintype.card F) := by
    have hins : (Finset.univ : Finset (ZMod p)) = insert 0 (Finset.univ.erase 0) := by
      ext a; simp
    rw [hins, Finset.sum_insert (Finset.notMem_erase _ _)]
    have h0 : ‖∑ x : Fˣ, if orderOf x = e then ψa 0 (x : F) else 0‖ = (Nat.totient e : ℝ) := by
      rw [hT0]; exact Complex.norm_natCast _
    rw [h0]
    have hrest : ∑ a ∈ (Finset.univ.erase 0 : Finset (ZMod p)),
          ‖∑ x : Fˣ, if orderOf x = e then ψa a (x : F) else 0‖
        ≤ ((Finset.univ.erase 0 : Finset (ZMod p)).card : ℝ)
            * (((Nat.divisors e).card : ℝ) * Real.sqrt (Fintype.card F)) := by
      calc _ ≤ ∑ _a ∈ (Finset.univ.erase 0 : Finset (ZMod p)),
              (((Nat.divisors e).card : ℝ) * Real.sqrt (Fintype.card F)) :=
              Finset.sum_le_sum (fun a ha => hTbound a (Finset.mem_erase.mp ha).1)
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hc : ((Finset.univ.erase 0 : Finset (ZMod p)).card : ℝ) = (p : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p)), Finset.card_univ,
        ZMod.card p, Nat.cast_sub hp.one_le]
      simp
    rw [hc] at hrest
    calc (Nat.totient e : ℝ) + ∑ a ∈ (Finset.univ.erase 0 : Finset (ZMod p)),
            ‖∑ x : Fˣ, if orderOf x = e then ψa a (x : F) else 0‖
        ≤ (Nat.totient e : ℝ) + ((p : ℝ) - 1)
            * (((Nat.divisors e).card : ℝ) * Real.sqrt (Fintype.card F)) := by
            linarith
      _ = (Nat.totient e : ℝ) + ((p:ℝ) - 1) * ((Nat.divisors e).card : ℝ)
            * Real.sqrt (Fintype.card F) := by ring
  -- assemble
  have hnorm : (p * Nat.card {x : Fˣ // orderOf x = e ∧
        Algebra.trace (ZMod p) F (x : F) = 0} : ℝ)
      ≤ (Nat.totient e : ℝ) + ((p:ℝ) - 1) * ((Nat.divisors e).card : ℝ)
          * Real.sqrt (Fintype.card F) := by
    have h := norm_sum_le (Finset.univ : Finset (ZMod p))
      (fun a => ∑ x : Fˣ, if orderOf x = e then ψa a (x : F) else 0)
    rw [← hTN, Complex.norm_natCast, Nat.cast_mul] at h
    exact le_trans h hsumSplit
  have hAle : (Nat.totient e : ℝ) + ((p:ℝ) - 1) * ((Nat.divisors e).card : ℝ)
        * Real.sqrt (Fintype.card F)
      ≤ ((Nat.totient e + (p - 1) * (Nat.divisors e).card
            * (Nat.sqrt (Fintype.card F) + 1) : ℕ) : ℝ) := by
    have hsqrt := sqrt_le_natSqrt_add_one (Fintype.card F)
    have hp1 : (0:ℝ) ≤ (p:ℝ) - 1 := by
      have : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.one_le
      linarith
    have hτ : (0:ℝ) ≤ ((Nat.divisors e).card : ℝ) := by positivity
    have hcast : ((Nat.totient e + (p - 1) * (Nat.divisors e).card
          * (Nat.sqrt (Fintype.card F) + 1) : ℕ) : ℝ)
        = (Nat.totient e : ℝ) + ((p:ℝ) - 1) * ((Nat.divisors e).card : ℝ)
            * ((Nat.sqrt (Fintype.card F) : ℝ) + 1) := by
      push_cast [Nat.cast_sub hp.one_le]; ring
    rw [hcast]
    have hle : ((p:ℝ) - 1) * ((Nat.divisors e).card : ℝ) * Real.sqrt (Fintype.card F)
        ≤ ((p:ℝ) - 1) * ((Nat.divisors e).card : ℝ)
            * ((Nat.sqrt (Fintype.card F) : ℝ) + 1) := by
      gcongr
    linarith
  have hfinal : p * Nat.card {x : Fˣ // orderOf x = e ∧
        Algebra.trace (ZMod p) F (x : F) = 0}
      ≤ Nat.totient e + (p - 1) * (Nat.divisors e).card
          * (Nat.sqrt (Fintype.card F) + 1) := by
    exact_mod_cast le_trans hnorm hAle
  rw [Nat.le_div_iff_mul_le hp.pos, mul_comm]
  exact hfinal

end Commons.FieldTheory.Finite
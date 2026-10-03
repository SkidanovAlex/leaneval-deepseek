import Mathlib
import Submission.Work.FIArea2.congCount
import Submission.Work.FIArea2.congAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! ## Prime-power reduction identities for the quadratic-congruence count

These are reproductions of the reduction identities of
`Submission/Work/FIArea2/congRed.lean` (same statements, same proofs, in the same style), kept here
so that the development of `Work.FIArea1.card_sq_congr_l51` depends only on finished modules.  The
low-level `ZMod (p^e)`-machinery they use lives in `Submission/Work/FIArea2/congAux.lean`. -/

namespace Work.FIArea1

open Finset
open Work.FIArea2

attribute [local instance] Classical.propDecidable

theorem Ncount_pow_dvd_dvd {p e : ℕ} [NeZero (p ^ e)] [NeZero (p ^ (e - 1))]
    (hp : p.Prime) (he : 2 ≤ e) {a b : ℕ} (ha : p ∣ a) (hb : p ∣ b) :
    Ncount (p ^ e) a b = p ^ 2 * Ncount (p ^ (e - 1)) (a / p) (b / p) := by
  have hd : p ^ (e - 1) ∣ p ^ e := pow_dvd_pow p (by omega)
  have hlt : 1 < e := by omega
  have hiff : ∀ z : ZMod (p ^ e) × ZMod (p ^ e),
      ((a : ZMod (p ^ e)) * z.1 ^ 2 = (b : ZMod (p ^ e)) * z.2 ^ 2) ↔
      ((a / p : ZMod (p ^ (e - 1))) * (ZMod.castHom hd (ZMod (p ^ (e - 1))) z.1) ^ 2
        = (b / p : ZMod (p ^ (e - 1))) * (ZMod.castHom hd (ZMod (p ^ (e - 1))) z.2) ^ 2) := by
    intro z
    have ha' : (a : ZMod (p ^ e)) = (p : ZMod (p ^ e)) * ((a / p : ℕ) : ZMod (p ^ e)) := by
      conv_lhs => rw [← Nat.mul_div_cancel' ha]
      rw [Nat.cast_mul]
    have hb' : (b : ZMod (p ^ e)) = (p : ZMod (p ^ e)) * ((b / p : ℕ) : ZMod (p ^ e)) := by
      conv_lhs => rw [← Nat.mul_div_cancel' hb]
      rw [Nat.cast_mul]
    have hstep := castHom_eq_iff_pow_mul_eq (p := p) (e := e) (k := 1) hp hlt hd
      (C := ((a / p : ℕ) : ZMod (p ^ e)) * z.1 ^ 2)
      (D := ((b / p : ℕ) : ZMod (p ^ e)) * z.2 ^ 2)
    rw [pow_one] at hstep
    have hC : (p : ZMod (p ^ e)) * ((a / p : ℕ) : ZMod (p ^ e)) * z.1 ^ 2
        = (p : ZMod (p ^ e)) * (((a / p : ℕ) : ZMod (p ^ e)) * z.1 ^ 2) := by ring
    have hD : (p : ZMod (p ^ e)) * ((b / p : ℕ) : ZMod (p ^ e)) * z.2 ^ 2
        = (p : ZMod (p ^ e)) * (((b / p : ℕ) : ZMod (p ^ e)) * z.2 ^ 2) := by ring
    rw [ha', hb', hC, hD, ← hstep]
    rw [map_mul, map_mul, map_pow, map_pow, castHom_natCast hd (ZMod (p ^ (e - 1))),
      castHom_natCast hd (ZMod (p ^ (e - 1)))]
  have hfib : ∀ t : ZMod (p ^ (e - 1)) × ZMod (p ^ (e - 1)),
      (Finset.univ.filter (fun z : ZMod (p ^ e) × ZMod (p ^ e) =>
        (ZMod.castHom hd (ZMod (p ^ (e - 1))) z.1,
          ZMod.castHom hd (ZMod (p ^ (e - 1))) z.2) = t)).card = p ^ 2 := by
    intro t
    rw [card_fiber_prod (ZMod.castHom hd (ZMod (p ^ (e - 1))))
      (ZMod.castHom hd (ZMod (p ^ (e - 1)))) t,
      fiber_card_zmod_castHom hd t.1, fiber_card_zmod_castHom hd t.2,
      Nat.pow_div (by omega) hp.pos, show e - (e - 1) = 1 by omega, pow_one]
    ring
  rw [Ncount, Ncount]
  exact card_preimage_mul (fun z : ZMod (p ^ e) × ZMod (p ^ e) =>
      (ZMod.castHom hd (ZMod (p ^ (e - 1))) z.1, ZMod.castHom hd (ZMod (p ^ (e - 1))) z.2))
    _ _ (p ^ 2) (fun z hz => (hiff z).mp hz) (fun z hz => (hiff z).mpr hz)
    (fun t _ => hfib t)

/-- Reduction (ii): if `p ∣ a` but `p ∤ b` (`e ≥ 2`), every solution of `a γ₁² ≡ b γ₂² (mod p^e)`
has `p ∣ γ₂`, and the congruence is equivalent to `(a/p) γ₁² ≡ (p·b) γ₂'² (mod p^(e-1))`, each
reduced solution having `p` lifts. -/
theorem Ncount_pow_dvd_not_dvd {p e : ℕ} [NeZero (p ^ e)] [NeZero (p ^ (e - 1))]
    (hp : p.Prime) (he : 2 ≤ e) {a b : ℕ} (ha : p ∣ a) (hb : ¬ p ∣ b) :
    Ncount (p ^ e) a b = p * Ncount (p ^ (e - 1)) (a / p) (p * b) := by
  have hd : p ^ (e - 1) ∣ p ^ e := pow_dvd_pow p (by omega)
  have hlt : 1 < e := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  have hpa : p ∣ p ^ e := pow_dvd_pow_of_pos (show 0 < e by omega)
  -- every solution of the original congruence has `p ∣ γ₂`
  have hy : ∀ z : ZMod (p ^ e) × ZMod (p ^ e),
      ((a : ZMod (p ^ e)) * z.1 ^ 2 = (b : ZMod (p ^ e)) * z.2 ^ 2) → p ∣ z.2.val := by
    intro z hz
    by_contra hcontra
    have hbU : (b : ZMod p) ≠ 0 :=
      fun h => hb ((CharP.cast_eq_zero_iff (ZMod p) p b).mp h)
    have h1 := congrArg (ZMod.castHom hpa (ZMod p)) hz
    rw [map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast,
      (CharP.cast_eq_zero_iff (ZMod p) p a).mpr ha, zero_mul] at h1
    have h2 : (ZMod.castHom hpa (ZMod p)) z.2 = 0 := by
      rcases mul_eq_zero.mp h1.symm with h | h
      · exact absurd h hbU
      · rw [pow_two] at h
        exact mul_self_eq_zero.mp h
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, CharP.cast_eq_zero_iff (ZMod p) p] at h2
    exact absurd h2 hcontra
  -- step 1: reparametrise solutions by `(γ₁, γ₂/p)`
  have hcard1 : (Finset.univ.filter (fun z : ZMod (p ^ e) × ZMod (p ^ e) =>
        (a : ZMod (p ^ e)) * z.1 ^ 2 = (b : ZMod (p ^ e)) * z.2 ^ 2)).card
      = (Finset.univ.filter (fun z : ZMod (p ^ e) × ZMod (p ^ (e - 1)) =>
        (a : ZMod (p ^ e)) * z.1 ^ 2 = (b : ZMod (p ^ e)) * (plift p e z.2) ^ 2)).card := by
    have hinj : Function.Injective (fun z : ZMod (p ^ e) × ZMod (p ^ (e - 1)) =>
        (z.1, plift p e z.2)) := by
      intro u v huv
      rw [Prod.mk.injEq] at huv
      exact Prod.ext huv.1 (plift_injective hp (by omega) huv.2)
    have himg : ((Finset.univ.filter (fun z : ZMod (p ^ e) × ZMod (p ^ (e - 1)) =>
          (a : ZMod (p ^ e)) * z.1 ^ 2 = (b : ZMod (p ^ e)) * (plift p e z.2) ^ 2)).image
          (fun z => (z.1, plift p e z.2)))
        = (Finset.univ.filter (fun z : ZMod (p ^ e) × ZMod (p ^ e) =>
          (a : ZMod (p ^ e)) * z.1 ^ 2 = (b : ZMod (p ^ e)) * z.2 ^ 2)) := by
      ext w
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hw
        refine ⟨(w.1, ((w.2.val / p : ℕ) : ZMod (p ^ (e - 1)))), ?_, ?_⟩
        · rw [plift_div hp (by omega) w.2 (hy w hw)]
          exact hw
        · rw [plift_div hp (by omega) w.2 (hy w hw)]
    rw [← himg, Finset.card_image_of_injective _ hinj]
  -- step 2: the reduction `(γ₁, z) ↦ (γ₁ mod p^(e-1), z)`
  have hcard2 : (Finset.univ.filter (fun z : ZMod (p ^ e) × ZMod (p ^ (e - 1)) =>
        (a : ZMod (p ^ e)) * z.1 ^ 2 = (b : ZMod (p ^ e)) * (plift p e z.2) ^ 2)).card
      = p * (Finset.univ.filter (fun t : ZMod (p ^ (e - 1)) × ZMod (p ^ (e - 1)) =>
        (a / p : ZMod (p ^ (e - 1))) * t.1 ^ 2
          = ((p * b : ℕ) : ZMod (p ^ (e - 1))) * t.2 ^ 2)).card := by
    have hiff : ∀ z : ZMod (p ^ e) × ZMod (p ^ (e - 1)),
        ((a : ZMod (p ^ e)) * z.1 ^ 2 = (b : ZMod (p ^ e)) * (plift p e z.2) ^ 2) ↔
        ((a / p : ZMod (p ^ (e - 1))) * (ZMod.castHom hd (ZMod (p ^ (e - 1))) z.1) ^ 2
          = ((p * b : ℕ) : ZMod (p ^ (e - 1))) * z.2 ^ 2) := by
      intro z
      have ha' : (a : ZMod (p ^ e)) = (p : ZMod (p ^ e)) * ((a / p : ℕ) : ZMod (p ^ e)) := by
        conv_lhs => rw [← Nat.mul_div_cancel' ha]
        rw [Nat.cast_mul]
      have hzc : ZMod.castHom hd (ZMod (p ^ (e - 1))) ((z.2.val : ℕ) : ZMod (p ^ e)) = z.2 := by
        rw [castHom_natCast hd (ZMod (p ^ (e - 1))), ZMod.natCast_zmod_val z.2]
      have hstep := castHom_eq_iff_pow_mul_eq (p := p) (e := e) (k := 1) hp hlt hd
        (C := ((a / p : ℕ) : ZMod (p ^ e)) * z.1 ^ 2)
        (D := ((p * b : ℕ) : ZMod (p ^ e)) * ((z.2.val : ℕ) : ZMod (p ^ e)) ^ 2)
      rw [pow_one] at hstep
      have hC : (p : ZMod (p ^ e)) * ((a / p : ℕ) : ZMod (p ^ e)) * z.1 ^ 2
          = (p : ZMod (p ^ e)) * (((a / p : ℕ) : ZMod (p ^ e)) * z.1 ^ 2) := by ring
      have hD : (b : ZMod (p ^ e)) * ((p : ZMod (p ^ e)) * ((z.2.val : ℕ) : ZMod (p ^ e))) ^ 2
          = (p : ZMod (p ^ e)) * (((p * b : ℕ) : ZMod (p ^ e))
              * ((z.2.val : ℕ) : ZMod (p ^ e)) ^ 2) := by rw [Nat.cast_mul]; ring
      rw [ha', plift_eq_mul, hC, hD, ← hstep]
      rw [map_mul, map_mul, map_pow, map_pow, castHom_natCast hd (ZMod (p ^ (e - 1))),
        castHom_natCast hd (ZMod (p ^ (e - 1))), hzc]
    have hfib : ∀ t : ZMod (p ^ (e - 1)) × ZMod (p ^ (e - 1)),
        (Finset.univ.filter (fun z : ZMod (p ^ e) × ZMod (p ^ (e - 1)) =>
          (ZMod.castHom hd (ZMod (p ^ (e - 1))) z.1, z.2) = t)).card = p := by
      intro t
      have hset : (Finset.univ.filter (fun z : ZMod (p ^ e) × ZMod (p ^ (e - 1)) =>
            (ZMod.castHom hd (ZMod (p ^ (e - 1))) z.1, z.2) = t))
          = (Finset.univ.filter (fun x : ZMod (p ^ e) =>
              ZMod.castHom hd (ZMod (p ^ (e - 1))) x = t.1)) ×ˢ {t.2} := by
        ext z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
          Finset.mem_singleton, Prod.ext_iff]
      rw [hset, Finset.card_product, fiber_card_zmod_castHom hd t.1,
        Nat.pow_div (by omega) hp.pos, show e - (e - 1) = 1 by omega, pow_one]
      simp
    refine card_preimage_mul (fun z : ZMod (p ^ e) × ZMod (p ^ (e - 1)) =>
      (ZMod.castHom hd (ZMod (p ^ (e - 1))) z.1, z.2)) _ _ p
      (fun z hz => (hiff z).mp hz) (fun z hz => (hiff z).mpr hz) (fun t _ => hfib t)
  rw [Ncount, Ncount, hcard1, hcard2]

/-- `Ncount` is symmetric in its two coefficients. -/
theorem Ncount_swap (q : ℕ) [NeZero q] (a b : ℕ) : Ncount q a b = Ncount q b a := by
  rw [Ncount, Ncount,
    ← Fintype.card_subtype (fun z : ZMod q × ZMod q =>
      (a : ZMod q) * z.1 ^ 2 = (b : ZMod q) * z.2 ^ 2),
    ← Fintype.card_subtype (fun z : ZMod q × ZMod q =>
      (b : ZMod q) * z.1 ^ 2 = (a : ZMod q) * z.2 ^ 2)]
  refine Fintype.card_congr (Equiv.subtypeEquiv (Equiv.prodComm (ZMod q) (ZMod q)) ?_)
  intro z
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- Reduction (iii): the case `p ∤ a`, `p ∣ b` (`e ≥ 2`), obtained from (ii) by symmetry. -/
theorem Ncount_pow_not_dvd_dvd {p e : ℕ} [NeZero (p ^ e)] [NeZero (p ^ (e - 1))]
    (hp : p.Prime) (he : 2 ≤ e) {a b : ℕ} (ha : ¬ p ∣ a) (hb : p ∣ b) :
    Ncount (p ^ e) a b = p * Ncount (p ^ (e - 1)) (p * a) (b / p) := by
  rw [Ncount_swap (p ^ e) a b, Ncount_pow_dvd_not_dvd hp he hb ha,
    Ncount_swap (p ^ (e - 1)) (b / p) (p * a)]


/-- The number of units of `ZMod (p^e)` is `p^e - p^(e-1)`. -/
lemma card_units_zmod_prime_pow {p e : ℕ} [NeZero (p ^ e)] (hp : p.Prime) (he : 1 ≤ e) :
    (Finset.univ.filter (fun y : ZMod (p ^ e) => IsUnit y)).card = p ^ e - p ^ (e - 1) := by
  have he0 : 0 < e := he
  haveI : NeZero (p ^ (e - 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hnon : (Finset.univ.filter (fun y : ZMod (p ^ e) => ¬ IsUnit y)).card = p ^ (e - 1) := by
    have hbij : (Finset.univ.filter (fun y : ZMod (p ^ e) => ¬ IsUnit y))
        = (Finset.univ.image (plift p e)) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hy
        have hpv : p ∣ y.val := by
          rw [isUnit_iff_not_dvd_val hp he0] at hy
          exact not_not.mp hy
        exact ⟨((y.val / p : ℕ) : ZMod (p ^ (e - 1))), plift_div hp he y hpv⟩
      · rintro ⟨u, rfl⟩
        rw [isUnit_iff_not_dvd_val hp he0, plift_val hp he]
        exact not_not.mpr (dvd_mul_right p u.val)
    rw [hbij, Finset.card_image_of_injective _ (plift_injective hp he), Finset.card_univ, ZMod.card]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (ZMod (p ^ e)))) (p := fun y => IsUnit y)
  rw [Finset.card_univ, ZMod.card, hnon] at hsplit
  omega

/-- If `p ∤ b`, a solution of `a γ₁² = b γ₂²` with `p ∣ γ₁` also has `p ∣ γ₂`. -/
lemma dvd_val_of_dvd_val {p e : ℕ} [NeZero (p ^ e)] (hp : p.Prime) (he : 1 ≤ e)
    {a b : ℕ} (hb : ¬ p ∣ b) {x y : ZMod (p ^ e)}
    (h : (a : ZMod (p ^ e)) * x ^ 2 = (b : ZMod (p ^ e)) * y ^ 2) (hx : p ∣ x.val) :
    p ∣ y.val := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpa : p ∣ p ^ e := pow_dvd_pow_of_pos (show 0 < e by omega)
  by_contra hcon
  have hbU : (b : ZMod p) ≠ 0 := fun hh => hb ((CharP.cast_eq_zero_iff (ZMod p) p b).mp hh)
  have h1 := congrArg (ZMod.castHom hpa (ZMod p)) h
  rw [map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast] at h1
  have hx0 : (ZMod.castHom hpa (ZMod p)) x = 0 := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, CharP.cast_eq_zero_iff (ZMod p) p]
    exact hx
  rw [hx0, show (0 : ZMod p) ^ 2 = 0 by norm_num, mul_zero] at h1
  have hy0 : (ZMod.castHom hpa (ZMod p)) y = 0 := by
    rcases mul_eq_zero.mp h1.symm with hh | hh
    · exact absurd hh hbU
    · rw [pow_two] at hh
      exact mul_self_eq_zero.mp hh
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, CharP.cast_eq_zero_iff (ZMod p) p] at hy0
  exact hcon hy0

/-- Mirror of `dvd_val_of_dvd_val`: if `p ∤ a` and `p ∣ γ₂` then `p ∣ γ₁`. -/
lemma dvd_val_of_dvd_val' {p e : ℕ} [NeZero (p ^ e)] (hp : p.Prime) (he : 1 ≤ e)
    {a b : ℕ} (ha : ¬ p ∣ a) {x y : ZMod (p ^ e)}
    (h : (a : ZMod (p ^ e)) * x ^ 2 = (b : ZMod (p ^ e)) * y ^ 2) (hy : p ∣ y.val) :
    p ∣ x.val :=
  dvd_val_of_dvd_val (a := b) (b := a) hp he ha h.symm hy

/-- For `p ∤ a`, `p ∤ b`, the units among the two coordinates of a solution of `a γ₁² = b γ₂²`
coincide. -/
lemma isUnit_fst_iff_snd {p e : ℕ} [NeZero (p ^ e)] (hp : p.Prime) (he : 1 ≤ e)
    {a b : ℕ} (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) {x y : ZMod (p ^ e)}
    (h : (a : ZMod (p ^ e)) * x ^ 2 = (b : ZMod (p ^ e)) * y ^ 2) :
    IsUnit x ↔ IsUnit y := by
  have he0 : 0 < e := he
  constructor
  · intro hx
    by_contra hy
    have hpy : p ∣ y.val := by
      rw [isUnit_iff_not_dvd_val hp he0] at hy
      exact not_not.mp hy
    have hpx : p ∣ x.val := dvd_val_of_dvd_val' hp he ha h hpy
    rw [isUnit_iff_not_dvd_val hp he0] at hx
    exact hx hpx
  · intro hy
    by_contra hx
    have hpx : p ∣ x.val := by
      rw [isUnit_iff_not_dvd_val hp he0] at hx
      exact not_not.mp hx
    have hpy : p ∣ y.val := dvd_val_of_dvd_val hp he hb h hpx
    rw [isUnit_iff_not_dvd_val hp he0] at hy
    exact hy hpy

/-- The inverse of a unit of `ZMod n` is a unit (`ZMod` is not a `DivisionMonoid`, so this needs
its own proof). -/
lemma isUnit_inv_zmod {n : ℕ} {c : ZMod n} (hc : IsUnit c) : IsUnit c⁻¹ :=
  ⟨⟨c⁻¹, c, ZMod.inv_mul_of_unit c hc, ZMod.mul_inv_of_unit c hc⟩, rfl⟩

/-- `Ncount` at the modulus `1` (the trivial ring). -/
lemma Ncount_one (a b : ℕ) : Ncount 1 a b = 1 := by
  rw [Ncount]
  have h : (Finset.univ.filter (fun p : ZMod 1 × ZMod 1 =>
      (a : ZMod 1) * p.1 ^ 2 = (b : ZMod 1) * p.2 ^ 2)) = Finset.univ := by
    refine Finset.filter_true_of_mem (fun x _ => ?_)
    exact Subsingleton.elim _ _
  rw [h, Finset.card_univ, Fintype.card_prod]
  simp [ZMod.card]

/-- `Ncount` at any modulus equal to `1`. -/
lemma Ncount_of_eq_one {q : ℕ} (hq : q = 1) (a b : ℕ) [NeZero q] : Ncount q a b = 1 := by
  subst hq
  exact Ncount_one a b

/-- `IsUnit` of the coefficients when `p` does not divide them. -/
lemma isUnit_natCast_of_not_dvd {p e a : ℕ} [NeZero (p ^ e)] (hp : p.Prime) (he : 0 < e)
    (ha : ¬ p ∣ a) : IsUnit (a : ZMod (p ^ e)) := by
  rw [isUnit_iff_not_dvd_val hp he, ZMod.val_natCast, Nat.dvd_mod_iff (pow_dvd_pow_of_pos he)]
  exact ha

/-- Primitive solutions (`p ∤ γ₁`) of `a γ₁² = b γ₂²` with `p ∤ ab` number at most `c·φ(p^e)`,
where `c` bounds the number of square roots of `a⁻¹b`. -/
lemma card_primitive_le {p e : ℕ} [NeZero (p ^ e)] (hp : p.Prime) (he : 1 ≤ e)
    {a b : ℕ} (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) {c : ℕ}
    (hc : (Finset.univ.filter (fun w : ZMod (p ^ e) =>
        w ^ 2 = (a : ZMod (p ^ e))⁻¹ * (b : ZMod (p ^ e)))).card ≤ c) :
    (Finset.univ.filter (fun z : ZMod (p ^ e) × ZMod (p ^ e) =>
      (a : ZMod (p ^ e)) * z.1 ^ 2 = (b : ZMod (p ^ e)) * z.2 ^ 2 ∧ IsUnit z.1)).card
      ≤ c * (Finset.univ.filter (fun y : ZMod (p ^ e) => IsUnit y)).card := by
  have hUa : IsUnit (a : ZMod (p ^ e)) := isUnit_natCast_of_not_dvd hp (by omega) ha
  refine le_trans (Finset.card_le_card_of_injOn
    (fun z : ZMod (p ^ e) × ZMod (p ^ e) => (z.2, z.1 * z.2⁻¹))
    (t := (Finset.univ.filter (fun y : ZMod (p ^ e) => IsUnit y)) ×ˢ
      (Finset.univ.filter (fun w : ZMod (p ^ e) =>
        w ^ 2 = (a : ZMod (p ^ e))⁻¹ * (b : ZMod (p ^ e))))) ?_ ?_) ?_
  · -- the image lies in `units × {w : w² = a⁻¹b}`
    intro z hz
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product] at hz ⊢
    obtain ⟨hzP, hzu⟩ := hz
    have hzu2 : IsUnit z.2 := (isUnit_fst_iff_snd hp he ha hb hzP).mp hzu
    have hy2 : IsUnit (z.2 ^ 2) := hzu2.pow 2
    have hinv2 : (z.2⁻¹) ^ 2 = (z.2 ^ 2)⁻¹ := by
      have hgoal : (z.2 ^ 2) * (z.2⁻¹) ^ 2 = 1 := by
        rw [← mul_pow, ZMod.mul_inv_of_unit z.2 hzu2, one_pow]
      exact (ZMod.inv_eq_of_mul_eq_one _ _ _ hgoal).symm
    refine ⟨hzu2, ?_⟩
    have hx2 : z.1 ^ 2 = (a : ZMod (p ^ e))⁻¹ * ((b : ZMod (p ^ e)) * z.2 ^ 2) := by
      rw [← hzP, ← mul_assoc, ZMod.inv_mul_of_unit (a : ZMod (p ^ e)) hUa, one_mul]
    calc (z.1 * z.2⁻¹) ^ 2 = z.1 ^ 2 * (z.2 ^ 2)⁻¹ := by rw [mul_pow, hinv2]
      _ = ((a : ZMod (p ^ e))⁻¹ * ((b : ZMod (p ^ e)) * z.2 ^ 2)) * (z.2 ^ 2)⁻¹ := by rw [hx2]
      _ = (a : ZMod (p ^ e))⁻¹ * ((b : ZMod (p ^ e)) * ((z.2 ^ 2) * (z.2 ^ 2)⁻¹)) := by ring
      _ = (a : ZMod (p ^ e))⁻¹ * (b : ZMod (p ^ e)) := by
            rw [ZMod.mul_inv_of_unit (z.2 ^ 2) hy2, mul_one]
  · -- injectivity
    intro z1 hz1 z2 hz2 h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hz1 hz2
    rw [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hzu : IsUnit z1.2 := (isUnit_fst_iff_snd hp he ha hb hz1.1).mp hz1.2
    refine Prod.ext ?_ h1
    calc z1.1 = (z1.1 * z1.2⁻¹) * z1.2 := by
          rw [mul_assoc, ZMod.inv_mul_of_unit z1.2 hzu, mul_one]
      _ = (z2.1 * z2.2⁻¹) * z1.2 := by rw [h2]
      _ = (z2.1 * z2.2⁻¹) * z2.2 := by rw [h1]
      _ = z2.1 := by rw [mul_assoc, ZMod.inv_mul_of_unit z2.2 (h1 ▸ hzu), mul_one]
  · rw [Finset.card_product]
    calc (Finset.univ.filter (fun y : ZMod (p ^ e) => IsUnit y)).card *
          (Finset.univ.filter (fun w : ZMod (p ^ e) =>
            w ^ 2 = (a : ZMod (p ^ e))⁻¹ * (b : ZMod (p ^ e)))).card
        ≤ (Finset.univ.filter (fun y : ZMod (p ^ e) => IsUnit y)).card * c :=
          Nat.mul_le_mul_left _ hc
      _ = c * (Finset.univ.filter (fun y : ZMod (p ^ e) => IsUnit y)).card := by rw [mul_comm]

/-- Non-primitive solutions of `a γ₁² = b γ₂²` (`p ∤ ab`, `e > 2`): the solutions with `p ∣ γ₁`
number `p²·N(a,b; p^(e-2))`. -/
lemma card_not_unit_eq {p e : ℕ} [NeZero (p ^ e)] [NeZero (p ^ (e - 1))]
    [NeZero (p ^ (e - 2))] (hp : p.Prime) (he : 2 < e) {a b : ℕ}
    (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) :
    (Finset.univ.filter (fun z : ZMod (p ^ e) × ZMod (p ^ e) =>
      (a : ZMod (p ^ e)) * z.1 ^ 2 = (b : ZMod (p ^ e)) * z.2 ^ 2 ∧ ¬ IsUnit z.1)).card
      = p ^ 2 * Ncount (p ^ (e - 2)) a b := by
  have he1 : 1 ≤ e := by omega
  have he0 : 0 < e := by omega
  have hd2 : p ^ (e - 2) ∣ p ^ (e - 1) := pow_dvd_pow p (by omega)
  have hd3 : p ^ (e - 2) ∣ p ^ e := pow_dvd_pow p (by omega)
  have hiff : ∀ u v : ZMod (p ^ (e - 1)),
      ((a : ZMod (p ^ e)) * (plift p e u) ^ 2 = (b : ZMod (p ^ e)) * (plift p e v) ^ 2) ↔
      ((a : ZMod (p ^ (e - 2))) * (ZMod.castHom hd2 (ZMod (p ^ (e - 2))) u) ^ 2
        = (b : ZMod (p ^ (e - 2))) * (ZMod.castHom hd2 (ZMod (p ^ (e - 2))) v) ^ 2) := by
    intro u v
    have ha2 : (ZMod.castHom hd3 (ZMod (p ^ (e - 2)))) ((a : ℕ) : ZMod (p ^ e))
        = ((a : ℕ) : ZMod (p ^ (e - 2))) := castHom_natCast hd3 (ZMod (p ^ (e - 2))) a
    have hb2 : (ZMod.castHom hd3 (ZMod (p ^ (e - 2)))) ((b : ℕ) : ZMod (p ^ e))
        = ((b : ℕ) : ZMod (p ^ (e - 2))) := castHom_natCast hd3 (ZMod (p ^ (e - 2))) b
    have hu2 : (ZMod.castHom hd3 (ZMod (p ^ (e - 2)))) ((u.val : ℕ) : ZMod (p ^ e))
        = ZMod.castHom hd2 (ZMod (p ^ (e - 2))) u := by
      rw [castHom_natCast hd3 (ZMod (p ^ (e - 2))), ZMod.castHom_apply, ZMod.cast_eq_val]
    have hv2 : (ZMod.castHom hd3 (ZMod (p ^ (e - 2)))) ((v.val : ℕ) : ZMod (p ^ e))
        = ZMod.castHom hd2 (ZMod (p ^ (e - 2))) v := by
      rw [castHom_natCast hd3 (ZMod (p ^ (e - 2))), ZMod.castHom_apply, ZMod.cast_eq_val]
    have hstep := castHom_eq_iff_pow_mul_eq (p := p) (e := e) (k := 2) hp (by omega) hd3
      (C := (a : ZMod (p ^ e)) * ((u.val : ℕ) : ZMod (p ^ e)) ^ 2)
      (D := (b : ZMod (p ^ e)) * ((v.val : ℕ) : ZMod (p ^ e)) ^ 2)
    have hC : (a : ZMod (p ^ e)) * (plift p e u) ^ 2
        = (p : ZMod (p ^ e)) ^ 2 * ((a : ZMod (p ^ e)) * ((u.val : ℕ) : ZMod (p ^ e)) ^ 2) := by
      rw [plift_eq_mul]; ring
    have hD : (b : ZMod (p ^ e)) * (plift p e v) ^ 2
        = (p : ZMod (p ^ e)) ^ 2 * ((b : ZMod (p ^ e)) * ((v.val : ℕ) : ZMod (p ^ e)) ^ 2) := by
      rw [plift_eq_mul]; ring
    rw [hC, hD, ← hstep]
    rw [map_mul, map_mul, map_pow, map_pow, ha2, hb2, hu2, hv2]
  have hinj : Function.Injective (fun w : ZMod (p ^ (e - 1)) × ZMod (p ^ (e - 1)) =>
      (plift p e w.1, plift p e w.2)) := by
    intro u v huv
    rw [Prod.mk.injEq] at huv
    exact Prod.ext (plift_injective hp he1 huv.1) (plift_injective hp he1 huv.2)
  have hset : (Finset.univ.filter (fun z : ZMod (p ^ e) × ZMod (p ^ e) =>
        (a : ZMod (p ^ e)) * z.1 ^ 2 = (b : ZMod (p ^ e)) * z.2 ^ 2 ∧ ¬ IsUnit z.1))
      = ((Finset.univ.filter (fun w : ZMod (p ^ (e - 1)) × ZMod (p ^ (e - 1)) =>
          (a : ZMod (p ^ (e - 2))) * (ZMod.castHom hd2 (ZMod (p ^ (e - 2))) w.1) ^ 2
            = (b : ZMod (p ^ (e - 2))) * (ZMod.castHom hd2 (ZMod (p ^ (e - 2))) w.2) ^ 2)).image
          (fun w => (plift p e w.1, plift p e w.2))) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hz, hunit⟩
      have hzx : p ∣ z.1.val := by
        rw [isUnit_iff_not_dvd_val hp he0] at hunit
        exact not_not.mp hunit
      have hzy : p ∣ z.2.val := dvd_val_of_dvd_val hp he1 hb hz hzx
      refine ⟨(↑(z.1.val / p), ↑(z.2.val / p)), ?_, ?_⟩
      · have h1 := plift_div hp he1 z.1 hzx
        have h2 := plift_div hp he1 z.2 hzy
        rw [← h1, ← h2] at hz
        exact (hiff _ _).mp hz
      · exact Prod.ext (plift_div hp he1 z.1 hzx) (plift_div hp he1 z.2 hzy)
    · rintro ⟨w, hw, rfl⟩
      refine ⟨(hiff w.1 w.2).mpr hw, ?_⟩
      rw [isUnit_iff_not_dvd_val hp he0, plift_val hp he1]
      exact not_not.mpr (dvd_mul_right p w.1.val)
  rw [hset, Finset.card_image_of_injective _ hinj]
  have hfib : ∀ t : ZMod (p ^ (e - 2)) × ZMod (p ^ (e - 2)),
      (Finset.univ.filter (fun w : ZMod (p ^ (e - 1)) × ZMod (p ^ (e - 1)) =>
        (ZMod.castHom hd2 (ZMod (p ^ (e - 2))) w.1,
          ZMod.castHom hd2 (ZMod (p ^ (e - 2))) w.2) = t)).card = p ^ 2 := by
    intro t
    rw [card_fiber_prod (ZMod.castHom hd2 (ZMod (p ^ (e - 2))))
      (ZMod.castHom hd2 (ZMod (p ^ (e - 2)))) t,
      fiber_card_zmod_castHom hd2 t.1, fiber_card_zmod_castHom hd2 t.2,
      Nat.pow_div (by omega) hp.pos, show e - 1 - (e - 2) = 1 by omega, pow_one]
    ring
  rw [Ncount]
  exact card_preimage_mul (fun w : ZMod (p ^ (e - 1)) × ZMod (p ^ (e - 1)) =>
    (ZMod.castHom hd2 (ZMod (p ^ (e - 2))) w.1, ZMod.castHom hd2 (ZMod (p ^ (e - 2))) w.2))
    _ _ (p ^ 2) (fun w hw => hw) (fun w hw => hw) (fun t _ => hfib t)

/-- Reduction (iv): for `p ∤ ab` and `e ≥ 2`, the count is at most
`p²·N(a,b; p^(e-2)) + c·φ(p^e)`, with `c = 2` for odd `p` and `c = 4` for `p = 2`. -/
theorem Ncount_pow_not_dvd_not_dvd {p e : ℕ} [NeZero (p ^ e)] [NeZero (p ^ (e - 2))]
    (hp : p.Prime) (he : 2 ≤ e) {a b : ℕ} (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) :
    Ncount (p ^ e) a b ≤ p ^ 2 * Ncount (p ^ (e - 2)) a b
      + (if p = 2 then 4 else 2) * (p ^ e - p ^ (e - 1)) := by
  have he1 : 1 ≤ e := by omega
  have hUa : IsUnit (a : ZMod (p ^ e)) := isUnit_natCast_of_not_dvd hp (by omega) ha
  have hUb : IsUnit (b : ZMod (p ^ e)) := isUnit_natCast_of_not_dvd hp (by omega) hb
  have hc : (Finset.univ.filter (fun w : ZMod (p ^ e) =>
      w ^ 2 = (a : ZMod (p ^ e))⁻¹ * (b : ZMod (p ^ e)))).card ≤ (if p = 2 then 4 else 2) := by
    by_cases hp2 : p = 2
    · subst hp2
      rw [if_pos rfl]
      exact sq_root_card_le_four he1 _ (isUnit_inv_zmod hUa |>.mul hUb)
    · rw [if_neg hp2]
      haveI : NeZero p := ⟨hp.ne_zero⟩
      exact sq_root_card_le_two hp hp2 he1 _ (isUnit_inv_zmod hUa |>.mul hUb)
  have hprim := card_primitive_le hp he1 ha hb hc
  have hnon : (Finset.univ.filter (fun z : ZMod (p ^ e) × ZMod (p ^ e) =>
      (a : ZMod (p ^ e)) * z.1 ^ 2 = (b : ZMod (p ^ e)) * z.2 ^ 2 ∧ ¬ IsUnit z.1)).card
      ≤ p ^ 2 * Ncount (p ^ (e - 2)) a b := by
    rcases eq_or_lt_of_le he with he2 | he3
    · -- `e = 2`: the non-primitive solutions are among the `p²` pairs with both coordinates
      -- divisible by `p`
      subst he2
      have hsub : (Finset.univ.filter (fun z : ZMod (p ^ 2) × ZMod (p ^ 2) =>
            (a : ZMod (p ^ 2)) * z.1 ^ 2 = (b : ZMod (p ^ 2)) * z.2 ^ 2 ∧ ¬ IsUnit z.1))
          ⊆ (Finset.univ.filter (fun z : ZMod (p ^ 2) × ZMod (p ^ 2) =>
              ¬ IsUnit z.1 ∧ ¬ IsUnit z.2)) := by
        intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        refine ⟨hz.2, ?_⟩
        have hz1 : p ∣ z.1.val := by
          rw [isUnit_iff_not_dvd_val hp (by norm_num)] at hz
          exact not_not.mp hz.2
        have hz2 : p ∣ z.2.val := dvd_val_of_dvd_val hp (by norm_num) hb hz.1 hz1
        rw [isUnit_iff_not_dvd_val hp (by norm_num)]
        exact fun h => h hz2
      refine le_trans (Finset.card_le_card hsub) ?_
      have hprod : (Finset.univ.filter (fun z : ZMod (p ^ 2) × ZMod (p ^ 2) =>
            ¬ IsUnit z.1 ∧ ¬ IsUnit z.2))
          = (Finset.univ.filter (fun x : ZMod (p ^ 2) => ¬ IsUnit x)) ×ˢ
            (Finset.univ.filter (fun x : ZMod (p ^ 2) => ¬ IsUnit x)) := by
        ext z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
      rw [hprod, Finset.card_product]
      have hunits := card_units_zmod_prime_pow (p := p) (e := 2) hp (by norm_num)
      have hnu : (Finset.univ.filter (fun x : ZMod (p ^ 2) => ¬ IsUnit x)).card = p := by
        have hsplit := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (ZMod (p ^ 2)))) (p := fun x => IsUnit x)
        rw [Finset.card_univ, ZMod.card] at hsplit
        have hle : p ≤ p ^ 2 := by nlinarith [hp.two_le]
        have h2 : p ^ 2 - p ^ (2 - 1) = p ^ 2 - p := by norm_num
        rw [h2] at hunits
        omega
      have hN : Ncount (p ^ (2 - 2)) a b = 1 := Ncount_of_eq_one (by norm_num) a b
      rw [hnu, hN]
      exact le_of_eq (by ring)
    · haveI : NeZero (p ^ (e - 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
      rw [Ncount]
      exact le_of_eq (card_not_unit_eq hp he3 ha hb)
  have hunits := card_units_zmod_prime_pow hp he1
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ.filter (fun z : ZMod (p ^ e) × ZMod (p ^ e) =>
      (a : ZMod (p ^ e)) * z.1 ^ 2 = (b : ZMod (p ^ e)) * z.2 ^ 2))) (p := fun z => IsUnit z.1)
  simp only [Finset.filter_filter] at hsplit
  rw [Ncount, ← hsplit]
  have h1 : (Finset.univ.filter (fun z : ZMod (p ^ e) × ZMod (p ^ e) =>
        (a : ZMod (p ^ e)) * z.1 ^ 2 = (b : ZMod (p ^ e)) * z.2 ^ 2 ∧ IsUnit z.1)).card
      ≤ (if p = 2 then 4 else 2) * (p ^ e - p ^ (e - 1)) := by
    rw [← hunits]
    exact hprim
  calc (Finset.univ.filter (fun z : ZMod (p ^ e) × ZMod (p ^ e) =>
        (a : ZMod (p ^ e)) * z.1 ^ 2 = (b : ZMod (p ^ e)) * z.2 ^ 2 ∧ IsUnit z.1)).card
      + (Finset.univ.filter (fun z : ZMod (p ^ e) × ZMod (p ^ e) =>
        (a : ZMod (p ^ e)) * z.1 ^ 2 = (b : ZMod (p ^ e)) * z.2 ^ 2 ∧ ¬ IsUnit z.1)).card
      ≤ (if p = 2 then 4 else 2) * (p ^ e - p ^ (e - 1)) + p ^ 2 * Ncount (p ^ (e - 2)) a b :=
        add_le_add h1 hnon
    _ = p ^ 2 * Ncount (p ^ (e - 2)) a b + (if p = 2 then 4 else 2) * (p ^ e - p ^ (e - 1)) := by
        ring



end Work.FIArea1

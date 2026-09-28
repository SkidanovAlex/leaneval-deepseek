import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.NA.Setup
import Submission.Work.HP.NA.SmoothDefs
import Submission.Work.HP.NA.Smooth.card_ker_of_surj
import Submission.Work.HP.NA.card_smooth_cond
import Submission.Work.HP.NA.succ_le_NN
import Submission.Work.HP.NA.sum_sigQ_eq

noncomputable section
open Finset
set_option autoImplicit false

namespace Work.HP
namespace NA

theorem map_fev_dfev (d n : ℕ) {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (a : Mon d n → A) (x : Fin (n + 1) → A) :
    (φ (fev d n a x) = fev d n (fun m => φ (a m)) (fun i => φ (x i))) ∧
    (∀ j : Fin (n + 1), φ (dfev d n a x j)
        = dfev d n (fun m => φ (a m)) (fun i => φ (x i)) j) := by
  constructor
  · unfold fev
    rw [map_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    simp only [map_mul, map_prod, map_pow, veronese]
  · intro j
    unfold dfev
    rw [map_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    simp only [map_mul, map_natCast, map_prod, map_pow]

lemma sum_shift_exp (d n : ℕ) (m : Mon d n) (j : Fin (n + 1)) (hj : (m.1 j : ℕ) ≠ 0) :
    ∑ i, (if i = j then (m.1 i : ℕ) - 1 else (m.1 i : ℕ)) = d - 1 := by
  have h : ∑ i, ((if i = j then (m.1 i : ℕ) - 1 else (m.1 i : ℕ)) + (if i = j then 1 else 0))
      = ∑ i, (m.1 i : ℕ) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i = j
    · subst hi; simp; omega
    · simp [hi]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', m.2] at h
  simp at h
  omega

theorem fev_dfev_smul (d n : ℕ) {R : Type*} [CommRing R] (a : Mon d n → R) (c : R)
    (x : Fin (n + 1) → R) :
    (fev d n a (c • x) = c ^ d * fev d n a x) ∧
    (∀ j : Fin (n + 1), dfev d n a (c • x) j = c ^ (d - 1) * dfev d n a x j) := by
  have hver : ∀ m : Mon d n, veronese d n (c • x) m = c ^ d * veronese d n x m := by
    intro m
    have h1 : (∏ i, (c • x) i ^ (m.1 i : ℕ)) = ∏ i, (c ^ (m.1 i : ℕ) * x i ^ (m.1 i : ℕ)) := by
      apply Finset.prod_congr rfl; intro i _
      rw [Pi.smul_apply, smul_eq_mul, mul_pow]
    show (∏ i, (c • x) i ^ (m.1 i : ℕ)) = c ^ d * ∏ i, x i ^ (m.1 i : ℕ)
    rw [h1, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, m.2]
  constructor
  · unfold fev
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro m _
    rw [hver m]; ring
  · intro j
    unfold dfev
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro m _
    set ee : Fin (n + 1) → ℕ := fun i => if i = j then (m.1 i : ℕ) - 1 else (m.1 i : ℕ) with hee
    have hprod : (∏ i, (c • x) i ^ (ee i)) = c ^ (∑ i, ee i) * ∏ i, x i ^ (ee i) := by
      have h1 : (∏ i, (c • x) i ^ (ee i)) = ∏ i, (c ^ (ee i) * x i ^ (ee i)) := by
        apply Finset.prod_congr rfl; intro i _
        rw [Pi.smul_apply, smul_eq_mul, mul_pow]
      rw [h1, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    by_cases hmj : (m.1 j : ℕ) = 0
    · rw [show ((m.1 j : ℕ) : R) = 0 from by rw [hmj]; simp]
      ring
    · have hsum : ∑ i, ee i = d - 1 := by
        rw [hee]; exact sum_shift_exp d n m j hmj
      rw [hprod, hsum]; ring

def redHom (p e r : ℕ) (her : e ≤ r) : ZMod (p ^ r) →+* ZMod (p ^ e) :=
  ZMod.castHom (Nat.pow_dvd_pow p her) (ZMod (p ^ e))

lemma redHom_val (p e r : ℕ) (her : e ≤ r) [NeZero (p ^ r)] (x : ZMod (p ^ r)) :
    redHom p e r her x = ((x.val : ℕ) : ZMod (p ^ e)) := by
  rw [redHom, ZMod.castHom_apply, ZMod.cast_eq_val]

lemma redHom_natCast (p e r : ℕ) (her : e ≤ r) (k : ℕ) :
    redHom p e r her ((k : ℕ) : ZMod (p ^ r)) = ((k : ℕ) : ZMod (p ^ e)) := by
  rw [redHom, ZMod.castHom_apply]
  exact ZMod.cast_natCast (Nat.pow_dvd_pow p her) k

lemma redHom_eq_zero_of_vpDvd (p e r : ℕ) (her : e ≤ r) {y : ZMod (p ^ r)}
    (h : vpDvd p r e y) : redHom p e r her y = 0 := by
  obtain ⟨c, rfl⟩ := h
  rw [map_mul, ← Nat.cast_pow, redHom_natCast, ZMod.natCast_self, zero_mul]

lemma isPrimMod_map_redHom {p e r N : ℕ} (hp : p.Prime) (he : 1 ≤ e) (her : e ≤ r)
    (x : Fin N → ZMod (p ^ r)) (hx : IsPrimMod (p ^ r) x) :
    IsPrimMod (p ^ e) (fun i => redHom p e r her (x i)) := by
  obtain ⟨i, hi⟩ := (isPrimMod_iff_exists_isUnit p r N hp (le_trans he her) x).mp hx
  exact (isPrimMod_iff_exists_isUnit p e N hp he _).mpr ⟨i, hi.map (redHom p e r her)⟩

def wcond (d n p e : ℕ) (b : Mon d n → ZMod (p ^ e)) (y : Fin (n + 1) → ZMod (p ^ e)) : Prop :=
  IsPrimGen (p ^ e) y ∧ fev d n b y = 0 ∧ ∀ j, dfev d n b y j = 0

def Wset (d n p e : ℕ) [NeZero (p ^ e)] (b : Mon d n → ZMod (p ^ e)) :
    Finset (Fin (n + 1) → ZMod (p ^ e)) := by
  classical
  exact Finset.univ.filter (wcond d n p e b)

def Tset (d n p e : ℕ) [NeZero (p ^ e)] : Finset (Mon d n → ZMod (p ^ e)) := by
  classical
  exact Finset.univ.filter (fun b => (Wset d n p e b).Nonempty)

def Ucard (d n p e : ℕ) (y : Fin (n + 1) → ZMod (p ^ e)) : ℕ :=
  Nat.card {b : Mon d n → ZMod (p ^ e) // wcond d n p e b y}

lemma natCard_eq_filter_card {α : Type*} [Fintype α] (q : α → Prop) [DecidablePred q] :
    Nat.card {x : α // q x} = (Finset.univ.filter q).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

lemma totient_eq (p e : ℕ) (hp : p.Prime) (he : 1 ≤ e) :
    (p ^ e).totient = p ^ (e - 1) * (p - 1) :=
  Nat.totient_prime_pow hp (by omega)

lemma totient_le_Wset_card (d n p e : ℕ) [NeZero (p ^ e)] (hp : p.Prime) (he : 1 ≤ e)
    (b : Mon d n → ZMod (p ^ e)) (hb : (Wset d n p e b).Nonempty) :
    (p ^ e).totient ≤ (Wset d n p e b).card := by
  classical
  obtain ⟨y, hy⟩ := hb
  rw [Wset, Finset.mem_filter] at hy
  obtain ⟨-, hy⟩ := hy
  rw [wcond] at hy
  obtain ⟨i0, hi0⟩ := (isPrimGen_iff_exists_isUnit hp he y).mp hy.1
  have horbit : ∀ u : (ZMod (p ^ e))ˣ, (fun i => (u : ZMod (p ^ e)) * y i) ∈ Wset d n p e b := by
    intro u
    have hsym : (fun i => (u : ZMod (p ^ e)) * y i) = (u : ZMod (p ^ e)) • y := by
      funext i; rw [Pi.smul_apply, smul_eq_mul]
    have h1 : IsPrimGen (p ^ e) (fun i => (u : ZMod (p ^ e)) * y i) := by
      apply isPrimGen_of_isUnit (i := i0)
      exact IsUnit.mul u.isUnit hi0
    rw [Wset, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [wcond]
    refine ⟨h1, ?_, ?_⟩
    · rw [hsym, (fev_dfev_smul d n b (u : ZMod (p ^ e)) y).1, hy.2.1, mul_zero]
    · intro j
      rw [hsym, (fev_dfev_smul d n b (u : ZMod (p ^ e)) y).2 j, hy.2.2 j, mul_zero]
  have hinj : Function.Injective (fun u : (ZMod (p ^ e))ˣ =>
      (⟨fun i => (u : ZMod (p ^ e)) * y i, horbit u⟩ : {y' // y' ∈ Wset d n p e b})) := by
    intro u v huv
    have h1 : (u : ZMod (p ^ e)) * y i0 = (v : ZMod (p ^ e)) * y i0 :=
      congrArg (fun z : {y' // y' ∈ Wset d n p e b} => z.1 i0) huv
    exact Units.ext (hi0.mul_right_cancel h1)
  have hcard := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_subtype, Finset.filter_mem_eq_inter, Finset.univ_inter,
      ZMod.card_units_eq_totient] at hcard
  exact hcard

lemma Ucard_le (d n p e : ℕ) [NeZero (p ^ e)] (hp : p.Prime) (he : 1 ≤ e)
    (y : Fin (n + 1) → ZMod (p ^ e)) :
    Ucard d n p e y ≤ (p ^ e) ^ (NN d n - (n + 1)) := by
  classical
  rw [Ucard, natCard_eq_filter_card]
  by_cases hy : IsPrimGen (p ^ e) y
  · obtain ⟨j0, hj0⟩ := (isPrimGen_iff_exists_isUnit hp he y).mp hy
    have hsub : Finset.univ.filter (fun b => wcond d n p e b y) ⊆
        Finset.univ.filter (fun b => fev d n b y = 0 ∧ ∀ i, i ≠ j0 → dfev d n b y i = 0) := by
      intro b hb
      rw [Finset.mem_filter] at hb ⊢
      rw [wcond] at hb
      exact ⟨Finset.mem_univ _, hb.2.2.1, fun i _ => hb.2.2.2 i⟩
    calc (Finset.univ.filter (fun b => wcond d n p e b y)).card
        ≤ (Finset.univ.filter (fun b => fev d n b y = 0 ∧
            ∀ i, i ≠ j0 → dfev d n b y i = 0)).card := Finset.card_le_card hsub
      _ = Nat.card {b : Mon d n → ZMod (p ^ e) //
            fev d n b y = 0 ∧ ∀ i, i ≠ j0 → dfev d n b y i = 0} :=
          (natCard_eq_filter_card _).symm
      _ = (p ^ e) ^ (NN d n - (n + 1)) := card_smooth_cond d n p e hp y j0 hj0
  · have hempty : Finset.univ.filter (fun b => wcond d n p e b y) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro b _ hb
      rw [wcond] at hb
      exact hy hb.1
    rw [hempty]
    simp

theorem card_Rset_le (d n p r e : ℕ) (hd : 1 ≤ d) (hp : p.Prime) (hr : 1 ≤ r) (he : 1 ≤ e)
    (her : e ≤ r) :
    Nat.card {a : Work.HP.Mon d n → ZMod (p ^ r) // Work.HP.NA.Rset d n p r e a}
      ≤ 2 * p ^ (r * Work.HP.NN d n - e) := by
  classical
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  have hNle : n + 1 ≤ NN d n := succ_le_NN d n hd
  have hNpos : 1 ≤ NN d n := by omega
  have hreve : e ≤ r * NN d n := by
    calc e ≤ r := her
      _ = r * 1 := (mul_one r).symm
      _ ≤ r * NN d n := Nat.mul_le_mul_left r hNpos
  have hNcard : Nat.card (Mon d n) = NN d n := by
    rw [Nat.card_eq_fintype_card]
  have hdiv : ∀ x : ZMod (p ^ r), x.val / p ^ e < p ^ (r - e) := by
    intro x
    have hpr : p ^ r = p ^ e * p ^ (r - e) := by rw [← pow_add, Nat.add_sub_of_le her]
    have hlt : x.val < p ^ e * p ^ (r - e) := by rw [← hpr]; exact x.val_lt
    exact Nat.div_lt_of_lt_mul hlt
  have hval_eq : ∀ x x' : ZMod (p ^ r),
      ((x.val : ℕ) : ZMod (p ^ e)) = ((x'.val : ℕ) : ZMod (p ^ e)) →
        x.val / p ^ e = x'.val / p ^ e → x = x' := by
    intro x x' h1 h2
    apply ZMod.val_injective
    have e1 : x.val % p ^ e = x'.val % p ^ e := by
      have := congrArg ZMod.val h1
      rwa [ZMod.val_natCast, ZMod.val_natCast] at this
    calc x.val = p ^ e * (x.val / p ^ e) + x.val % p ^ e := (Nat.div_add_mod _ _).symm
      _ = p ^ e * (x'.val / p ^ e) + x'.val % p ^ e := by rw [h2, e1]
      _ = x'.val := Nat.div_add_mod _ _
  have hmem : ∀ a : Mon d n → ZMod (p ^ r), Rset d n p r e a →
      (Wset d n p e (fun m => redHom p e r her (a m))).Nonempty := by
    intro a ha
    obtain ⟨-, x, hxprim, hfx, hgrad, -⟩ := ha
    refine ⟨fun i => redHom p e r her (x i), ?_⟩
    rw [Wset, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [wcond]
    refine ⟨?_, ?_, ?_⟩
    · exact isPrimMod_map_redHom hp he her x hxprim
    · have h := (map_fev_dfev d n (redHom p e r her) a x).1
      rw [← h, hfx, map_zero]
    · intro j
      have h := (map_fev_dfev d n (redHom p e r her) a x).2 j
      rw [← h]
      exact redHom_eq_zero_of_vpDvd p e r her (hgrad j)
  let Φ : {a : Mon d n → ZMod (p ^ r) // Rset d n p r e a} →
      {b : Mon d n → ZMod (p ^ e) // b ∈ Tset d n p e} × (Mon d n → Fin (p ^ (r - e))) :=
    fun a => (⟨fun m => redHom p e r her (a.1 m), by
        rw [Tset, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hmem a.1 a.2⟩⟩,
      fun m => ⟨(a.1 m).val / p ^ e, hdiv (a.1 m)⟩)
  have hΦ : Function.Injective Φ := by
    intro a a' h
    have h1 : (fun m => redHom p e r her (a.1 m)) = (fun m => redHom p e r her (a'.1 m)) := by
      have := congrArg (fun z => z.1.1) h
      dsimp only [Φ] at this
      exact this
    have h2 : ∀ m, (a.1 m).val / p ^ e = (a'.1 m).val / p ^ e := by
      intro m
      have := congrArg (fun z => (z.2 m : Fin (p ^ (r - e))).val) h
      dsimp only [Φ] at this
      exact this
    refine Subtype.ext (funext fun m => ?_)
    refine hval_eq _ _ ?_ (h2 m)
    have hh : redHom p e r her (a.1 m) = redHom p e r her (a'.1 m) := congrFun h1 m
    rwa [redHom_val, redHom_val] at hh
  have hcard1 := Nat.card_le_card_of_injective Φ hΦ
  simp only [Nat.card_prod, Nat.card_fun, Nat.card_fin] at hcard1
  have hTc : Nat.card {b : Mon d n → ZMod (p ^ e) // b ∈ Tset d n p e}
      = (Tset d n p e).card := by
    rw [natCard_eq_filter_card, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [hTc, hNcard] at hcard1
  have hsum3 : ∑ b : Mon d n → ZMod (p ^ e), (Wset d n p e b).card
      ≤ (p ^ e) ^ (n + 1) * (p ^ e) ^ (NN d n - (n + 1)) := by
    have h1 : (∑ b : Mon d n → ZMod (p ^ e), (Wset d n p e b).card)
        = ∑ y : Fin (n + 1) → ZMod (p ^ e), Ucard d n p e y := by
      calc ∑ b : Mon d n → ZMod (p ^ e), (Wset d n p e b).card
          = ∑ b, ∑ y, (if wcond d n p e b y then 1 else 0) := by
            apply Finset.sum_congr rfl; intro b _
            rw [Wset, Finset.card_filter]
        _ = ∑ y, ∑ b, (if wcond d n p e b y then 1 else 0) := Finset.sum_comm
        _ = ∑ y, Ucard d n p e y := by
            apply Finset.sum_congr rfl; intro y _
            rw [Ucard, natCard_eq_filter_card, Finset.card_filter]
    rw [h1]
    calc ∑ y : Fin (n + 1) → ZMod (p ^ e), Ucard d n p e y
        ≤ ∑ _y : Fin (n + 1) → ZMod (p ^ e), (p ^ e) ^ (NN d n - (n + 1)) :=
          Finset.sum_le_sum (fun y _ => Ucard_le d n p e hp he y)
      _ = Fintype.card (Fin (n + 1) → ZMod (p ^ e)) * (p ^ e) ^ (NN d n - (n + 1)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; simp
      _ = (p ^ e) ^ (n + 1) * (p ^ e) ^ (NN d n - (n + 1)) := by
          rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]
  have hsum2 : (Tset d n p e).card * (p ^ e).totient
      ≤ ∑ b : Mon d n → ZMod (p ^ e), (Wset d n p e b).card := by
    have hle1 : (Tset d n p e).card * (p ^ e).totient
        = ∑ b ∈ Tset d n p e, (p ^ e).totient := by
      rw [Finset.sum_const, nsmul_eq_mul]; simp
    have hle2 : ∑ b ∈ Tset d n p e, (p ^ e).totient
        ≤ ∑ b ∈ Tset d n p e, (Wset d n p e b).card := by
      apply Finset.sum_le_sum
      intro b hb
      rw [Tset, Finset.mem_filter] at hb
      exact totient_le_Wset_card d n p e hp he b hb.2
    have hle3 : ∑ b ∈ Tset d n p e, (Wset d n p e b).card
        ≤ ∑ b : Mon d n → ZMod (p ^ e), (Wset d n p e b).card := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro b _ _; exact Nat.zero_le _
    calc (Tset d n p e).card * (p ^ e).totient
        = ∑ b ∈ Tset d n p e, (p ^ e).totient := hle1
      _ ≤ ∑ b ∈ Tset d n p e, (Wset d n p e b).card := hle2
      _ ≤ ∑ b : Mon d n → ZMod (p ^ e), (Wset d n p e b).card := hle3
  have hmain : Nat.card {a : Mon d n → ZMod (p ^ r) // Rset d n p r e a} * (p ^ e).totient
      ≤ p ^ (r * NN d n) := by
    calc Nat.card {a : Mon d n → ZMod (p ^ r) // Rset d n p r e a} * (p ^ e).totient
        ≤ ((Tset d n p e).card * (p ^ (r - e)) ^ NN d n) * (p ^ e).totient :=
          Nat.mul_le_mul_right _ hcard1
      _ = ((Tset d n p e).card * (p ^ e).totient) * (p ^ (r - e)) ^ NN d n := by ring
      _ ≤ ((p ^ e) ^ (n + 1) * (p ^ e) ^ (NN d n - (n + 1))) * (p ^ (r - e)) ^ NN d n :=
          Nat.mul_le_mul_right _ (le_trans hsum2 hsum3)
      _ = p ^ (r * NN d n) := by
          rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← mul_add, Nat.add_sub_of_le hNle,
              ← pow_add, ← add_mul, Nat.add_sub_of_le her]
  have hple : p ≤ 2 * (p - 1) := by have := hp.two_le; omega
  have hpe_le : p ^ e ≤ 2 * (p ^ (e - 1) * (p - 1)) := by
    have h1 : p ^ e = p * p ^ (e - 1) := by rw [← pow_succ', Nat.sub_add_cancel he]
    rw [h1]
    calc p * p ^ (e - 1) ≤ (2 * (p - 1)) * p ^ (e - 1) := Nat.mul_le_mul_right _ hple
      _ = 2 * (p ^ (e - 1) * (p - 1)) := by ring
  have hgoal : Nat.card {a : Mon d n → ZMod (p ^ r) // Rset d n p r e a}
      ≤ 2 * p ^ (r * NN d n - e) := by
    have hmul : Nat.card {a : Mon d n → ZMod (p ^ r) // Rset d n p r e a} * p ^ e
        ≤ 2 * p ^ (r * NN d n) := by
      calc Nat.card {a : Mon d n → ZMod (p ^ r) // Rset d n p r e a} * p ^ e
          ≤ Nat.card {a : Mon d n → ZMod (p ^ r) // Rset d n p r e a}
              * (2 * (p ^ (e - 1) * (p - 1))) := Nat.mul_le_mul_left _ hpe_le
        _ = 2 * (Nat.card {a : Mon d n → ZMod (p ^ r) // Rset d n p r e a} * (p ^ e).totient) := by
            rw [totient_eq p e hp he]; ring
        _ ≤ 2 * p ^ (r * NN d n) := Nat.mul_le_mul_left 2 hmain
    have hpowe : p ^ (r * NN d n) = p ^ e * p ^ (r * NN d n - e) := by
      rw [← pow_add, Nat.add_sub_of_le hreve]
    have hmul' : Nat.card {a : Mon d n → ZMod (p ^ r) // Rset d n p r e a} * p ^ e
        ≤ (2 * p ^ (r * NN d n - e)) * p ^ e := by
      rw [hpowe] at hmul
      calc Nat.card {a : Mon d n → ZMod (p ^ r) // Rset d n p r e a} * p ^ e
          ≤ 2 * (p ^ e * p ^ (r * NN d n - e)) := hmul
        _ = (2 * p ^ (r * NN d n - e)) * p ^ e := by ring
    have hmul'' : p ^ e * Nat.card {a : Mon d n → ZMod (p ^ r) // Rset d n p r e a}
        ≤ p ^ e * (2 * p ^ (r * NN d n - e)) := by
      calc p ^ e * Nat.card {a : Mon d n → ZMod (p ^ r) // Rset d n p r e a}
          = Nat.card {a : Mon d n → ZMod (p ^ r) // Rset d n p r e a} * p ^ e := by ring
        _ ≤ (2 * p ^ (r * NN d n - e)) * p ^ e := hmul'
        _ = p ^ e * (2 * p ^ (r * NN d n - e)) := by ring
    exact Nat.le_of_mul_le_mul_left hmul'' (pow_pos hp.pos e)
  exact hgoal

end NA
end Work.HP

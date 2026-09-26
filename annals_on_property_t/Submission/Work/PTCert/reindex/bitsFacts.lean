import Mathlib
import Submission.Work.PTCert.reindex.Defs
import Submission.Work.PTCert.digitArith
import Submission.Work.PTCert.codeFactsAux.digitsRecon
import Submission.Work.PTCert.digits.sum_mul_pow_div_mod
import Submission.Work.PTCert.digits.sum_mul_pow_lt_pow

namespace Work.PTCert.reindex

open Submission.PTCert

/-! ## Bits of a `ZMod 2`-vector, and its code -/

/-- The `j`-th bit of a `ZMod 2`-vector as `0`/`1` (bits outside `Fin 5` vanish). -/
private def bitOf (a : Fin 5 → ZMod 2) (j : ℕ) : ℕ :=
  if h : j < 5 then (if a ⟨j, h⟩ = 1 then 1 else 0) else 0

private lemma bitOf_lt_two (a : Fin 5 → ZMod 2) (j : ℕ) : bitOf a j < 2 := by
  unfold bitOf
  split_ifs <;> omega

private lemma bitOf_eq (a : Fin 5 → ZMod 2) (i : Fin 5) :
    bitOf a i.val = (if a i = 1 then 1 else 0) := by
  rw [bitOf, dif_pos i.isLt]

private lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have h2 : x.val < 2 := ZMod.val_lt x
  rcases (show x.val = 0 ∨ x.val = 1 by omega) with h | h
  · exact Or.inl (ZMod.val_injective 2 (by rw [h, ZMod.val_zero]))
  · exact Or.inr (ZMod.val_injective 2 (by rw [h, ZMod.val_one 2]))

private lemma natCast_ite_eq_self (x : ZMod 2) :
    (((if x = 1 then 1 else 0 : ℕ)) : ZMod 2) = x := by
  by_cases h : x = 1
  · rw [if_pos h, h]; norm_num
  · rw [if_neg h]
    rcases zmod2_eq_zero_or_one x with h0 | h1
    · rw [h0]; norm_num
    · exact absurd h1 h

private lemma natCast_two_eq_one_iff {n : ℕ} (hn : n < 2) : ((n : ℕ) : ZMod 2) = 1 ↔ n = 1 := by
  constructor
  · intro h
    have h1 : ((n : ℕ) : ZMod 2).val = 1 := by rw [h, ZMod.val_one 2]
    rw [ZMod.val_natCast] at h1
    omega
  · intro h; rw [h]; norm_num

/-- The binary digit `sbit sc j` is `0` or `1`. -/
private lemma sbit_lt_two (sc j : ℕ) : Submission.PTCert.sbit sc j < 2 := by
  rw [Work.PTCert.sbit_eq_div]
  exact Nat.mod_lt _ (by norm_num)

/-- The code `encV a` is the positional sum of the bits of `a`. -/
private lemma encV_eq_range (a : Fin 5 → ZMod 2) :
    encV a = ∑ j ∈ Finset.range 5, bitOf a j * 2 ^ j := by
  have h1 : encV a = ∑ i : Fin 5, bitOf a i.val * 2 ^ i.val := by
    rw [Work.PTCert.encV, Submission.PTCert.scOf]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [bitOf_eq a i]
    simp only [Submission.PTCert.zBool, decide_eq_true_eq]
  rw [h1, Fin.sum_univ_eq_sum_range (fun j => bitOf a j * 2 ^ j) 5]

private lemma encV_lt (a : Fin 5 → ZMod 2) : encV a < 32 := by
  rw [encV_eq_range, show (32 : ℕ) = 2 ^ 5 from by norm_num]
  exact Work.PTCert.digits.sum_mul_pow_lt_pow (b := 2) (by norm_num) (bitOf a) 5
    (fun j _ => bitOf_lt_two a j)

/-- The bits of the code `encV a` are the bits of `a`. -/
private lemma zOfSc_encV (a : Fin 5 → ZMod 2) : Submission.PTCert.zOfSc (m := 5) (encV a) = a := by
  funext i
  show (((Submission.PTCert.sbit (encV a) i.val : ℕ)) : ZMod 2) = a i
  have h := Work.PTCert.digits.sum_mul_pow_div_mod (b := 2) (d := bitOf a) (n := 5) (i := i.val)
    (by norm_num) (fun j _ => bitOf_lt_two a j) i.isLt
  rw [← encV_eq_range] at h
  rw [Work.PTCert.sbit_eq_div, h, bitOf_eq a i]
  exact natCast_ite_eq_self (a i)

/-- `encV` inverts `zOfSc` on codes `< 32`: digit reconstruction in base `2`. -/
private lemma encV_zOfSc (sc : ℕ) (hsc : sc < 32) : encV (Submission.PTCert.zOfSc (m := 5) sc) = sc := by
  have hrec := Work.PTCert.selfDigits (b := 2) (by norm_num) sc 5 (by simpa using hsc)
  have key : encV (Submission.PTCert.zOfSc (m := 5) sc) =
      ∑ j ∈ Finset.range 5, Submission.PTCert.sbit sc j * 2 ^ j := by
    rw [encV_eq_range]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj5 : j < 5 := Finset.mem_range.mp hj
    have hb : bitOf (Submission.PTCert.zOfSc (m := 5) sc) j = Submission.PTCert.sbit sc j := by
      have hiff : (Submission.PTCert.zOfSc (m := 5) sc ⟨j, hj5⟩ = 1) ↔
          Submission.PTCert.sbit sc j = 1 := natCast_two_eq_one_iff (sbit_lt_two sc j)
      rw [bitOf, dif_pos hj5]
      by_cases h1 : Submission.PTCert.sbit sc j = 1
      · rw [if_pos (hiff.mpr h1), h1]
      · have h0 : Submission.PTCert.sbit sc j = 0 := by
          have := sbit_lt_two sc j; omega
        rw [if_neg (fun hh => h1 (hiff.mp hh)), h0]
    rw [hb]
  rw [key]
  calc ∑ j ∈ Finset.range 5, Submission.PTCert.sbit sc j * 2 ^ j
      = ∑ j ∈ Finset.range 5, (sc / 2 ^ j % 2) * 2 ^ j :=
        Finset.sum_congr rfl (fun j _ => by rw [Work.PTCert.sbit_eq_div])
    _ = sc := hrec.symm

/-- Code arithmetic for the `reindexEntryRow` reindexing: `scOf`/`sbit` digits, the inverse
`encV` of `zOfSc` on codes `< 32`, bounds, `bxor` as vector addition, `permCode` as a bit
permutation, and the reindexing of `∑ sc < 32` along `phiC q c0`.-/
theorem bitsFacts :
    (∀ s : Fin 5 → Bool, Submission.PTCert.scOf s < 32) ∧
    (∀ (s : Fin 5 → Bool) (i : ℕ) (hi : i < 5),
        Submission.PTCert.sbit (Submission.PTCert.scOf s) i = (if s ⟨i, hi⟩ then 1 else 0)) ∧
    (∀ v : Fin 5 → ZMod 2, Submission.PTCert.zOfSc (m := 5) (Work.PTCert.encV v) = v) ∧
    (∀ v : Fin 5 → ZMod 2, Work.PTCert.encV v < 32) ∧
    (∀ sc : ℕ, sc < 32 → Work.PTCert.encV (Submission.PTCert.zOfSc (m := 5) sc) = sc) ∧
    (∀ a b : ℕ, a < 32 → b < 32 →
        Submission.PTCert.zOfSc (m := 5) a = Submission.PTCert.zOfSc (m := 5) b → a = b) ∧
    (∀ a b : ℕ, Submission.PTCert.zOfSc (m := 5) (Work.PTCert.bxor a b) =
        Submission.PTCert.zOfSc (m := 5) a + Submission.PTCert.zOfSc (m := 5) b) ∧
    (∀ (q : Equiv.Perm (Fin 5)) (sc : ℕ),
        Submission.PTCert.zOfSc (m := 5) (Work.PTCert.permCode q sc) =
          fun i => Submission.PTCert.zOfSc (m := 5) sc (q i)) ∧
    (∀ (q : Equiv.Perm (Fin 5)) (sc : ℕ), Work.PTCert.permCode q sc < 32) ∧
    (∀ (q : Equiv.Perm (Fin 5)) (c0 sc : ℕ), Work.PTCert.phiC q c0 sc < 32) ∧
    (∀ (q : Equiv.Perm (Fin 5)) (c0 sc : ℕ),
        Submission.PTCert.zOfSc (m := 5) (Work.PTCert.phiC q c0 sc) =
          (fun i => Submission.PTCert.zOfSc (m := 5) sc (q i)) +
            Submission.PTCert.zOfSc (m := 5) c0) ∧
    (∀ (q : Equiv.Perm (Fin 5)) (c0 : ℕ), c0 < 32 →
        ∀ a b : ℕ, a < 32 → b < 32 → Work.PTCert.phiC q c0 a = Work.PTCert.phiC q c0 b → a = b) ∧
    (∀ (q : Equiv.Perm (Fin 5)) (c0 : ℕ), c0 < 32 → ∀ {M : Type} [AddCommMonoid M] (F : ℕ → M),
        (∑ sc ∈ Finset.range 32, F (Work.PTCert.phiC q c0 sc)) =
          ∑ sc ∈ Finset.range 32, F sc) := by
  -- the `scOf`/`sbit` digits of a sign vector
  have hscOf_lt : ∀ s : Fin 5 → Bool, Submission.PTCert.scOf s < 32 := by
    intro s
    simpa [Submission.PTCert.scOf] using (Work.PTCert.digitArith 5 (by norm_num)).2.2 s
  have hsbit_scOf : ∀ (s : Fin 5 → Bool) (i : ℕ) (hi : i < 5),
      Submission.PTCert.sbit (Submission.PTCert.scOf s) i = (if s ⟨i, hi⟩ then 1 else 0) := by
    intro s i hi
    simpa [Submission.PTCert.scOf] using (Work.PTCert.digitArith 5 (by norm_num)).2.1 s ⟨i, hi⟩
  -- `encV` is the inverse of `zOfSc` on codes `< 32`
  have hcode_pos : ∀ a b : ℕ, a < 32 → b < 32 →
      Submission.PTCert.zOfSc (m := 5) a = Submission.PTCert.zOfSc (m := 5) b → a = b := by
    intro a b ha hb h
    rw [← encV_zOfSc a ha, ← encV_zOfSc b hb, h]
  -- `bxor` is addition of the coded vectors
  have hbxor : ∀ a b : ℕ, Submission.PTCert.zOfSc (m := 5) (Work.PTCert.bxor a b) =
      Submission.PTCert.zOfSc (m := 5) a + Submission.PTCert.zOfSc (m := 5) b := by
    intro a b
    rw [Work.PTCert.bxor]
    exact zOfSc_encV _
  -- `permCode` permutes the bits
  have hpermCode : ∀ (q : Equiv.Perm (Fin 5)) (sc : ℕ),
      Submission.PTCert.zOfSc (m := 5) (Work.PTCert.permCode q sc) =
        fun i => Submission.PTCert.zOfSc (m := 5) sc (q i) := by
    intro q sc
    rw [Work.PTCert.permCode]
    exact zOfSc_encV _
  have hphiC : ∀ (q : Equiv.Perm (Fin 5)) (c0 sc : ℕ),
      Submission.PTCert.zOfSc (m := 5) (Work.PTCert.phiC q c0 sc) =
        (fun i => Submission.PTCert.zOfSc (m := 5) sc (q i)) +
          Submission.PTCert.zOfSc (m := 5) c0 := by
    intro q c0 sc
    rw [Work.PTCert.phiC, hbxor, hpermCode]
  have hphiC_inj : ∀ (q : Equiv.Perm (Fin 5)) (c0 : ℕ), c0 < 32 →
      ∀ a b : ℕ, a < 32 → b < 32 → Work.PTCert.phiC q c0 a = Work.PTCert.phiC q c0 b → a = b := by
    intro q c0 hc0 a b ha hb h
    have h1 := hphiC q c0 a
    have h2 := hphiC q c0 b
    rw [h] at h1
    have h3 : (fun i => Submission.PTCert.zOfSc (m := 5) a (q i)) =
        fun i => Submission.PTCert.zOfSc (m := 5) b (q i) := add_right_cancel (h1.symm.trans h2)
    have h4 : Submission.PTCert.zOfSc (m := 5) a = Submission.PTCert.zOfSc (m := 5) b := by
      funext i
      obtain ⟨j, hj⟩ := q.surjective i
      have := congrFun h3 j
      rwa [hj] at this
    exact hcode_pos a b ha hb h4
  refine ⟨hscOf_lt, hsbit_scOf, ?_, ?_, ?_, hcode_pos, hbxor, hpermCode, ?_, ?_, hphiC,
    hphiC_inj, ?_⟩
  · intro v; exact zOfSc_encV v
  · intro v; exact encV_lt v
  · intro sc hsc; exact encV_zOfSc sc hsc
  · intro q sc; rw [Work.PTCert.permCode]; exact encV_lt _
  · intro q c0 sc; rw [Work.PTCert.phiC, Work.PTCert.bxor]; exact encV_lt _
  · intro q c0 hc0 M _ F
    have hlt : ∀ sc : ℕ, Work.PTCert.phiC q c0 sc < 32 := fun sc => by
      rw [Work.PTCert.phiC, Work.PTCert.bxor]; exact encV_lt _
    have hinj : Set.InjOn (Work.PTCert.phiC q c0) (↑(Finset.range 32) : Set ℕ) :=
      fun a ha b hb h => hphiC_inj q c0 hc0 a b (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) h
    have hEq : (Finset.range 32).image (Work.PTCert.phiC q c0) = Finset.range 32 := by
      refine Finset.eq_of_subset_of_card_le
        (Finset.image_subset_iff.mpr (fun a _ => Finset.mem_range.mpr (hlt a))) ?_
      rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    calc (∑ sc ∈ Finset.range 32, F (Work.PTCert.phiC q c0 sc))
        = ∑ x ∈ (Finset.range 32).image (Work.PTCert.phiC q c0), F x :=
          (Finset.sum_image hinj).symm
      _ = ∑ x ∈ Finset.range 32, F x := by rw [hEq]

end Work.PTCert.reindex

import Mathlib
import Submission.Work.Resample.buKit
import Submission.Work.Resample.buWdSize
import Submission.Work.IntLib.encodeNatBridge

/-!
# Entry sizes of the `B̃` table word (`buL7`–`buL10`)

`buL7 … buL10` are the four list-valued entries of the static table `buTabList p α s t` of the
one-dimensional `B̃` word (`Work.Resample.buKit`).  This module bounds the encoding length
`HvdH.vsz` of each of them by `(t+1) * (p+1)^20`, using

* `vsz (ofList vs) = (vs.map vsz).sum + vs.length + 1` (so a list of `n` values of size `≤ B`
  has size `≤ (n+1)*(B+1)`),
* the element bounds `isz (egLam s t i) ≤ p+3`, `isz (egKeyS s t i) ≤ p+2`, and
  `isz (buWd …) ≤ buSZ p` / `isz (buWt …) ≤ buSZ p` (`Work.Resample.buWdSize`),
* `length (egHs m) = 2*m` and `|h| ≤ m` for `h ∈ egHs m`,
* `buSZ p + p + 7 ≤ (p+1)^18 ≤ (p+1)^20` for `p ≥ 100`.

The hypothesis `hθ` of the statement is not used: the factor `(t+1)` alone absorbs the length
`s < t+1` of the inner weight columns.

All arithmetic is delegated to small standalone lemmas with a clean context, so that the big
list terms of the main statement never enter a decision procedure.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH

/-! ## Sizes of `Val` encodings -/

theorem vsz_cons_loc (a b : Val) : vsz (Val.cons a b) = vsz a + vsz b + 1 := by
  simp [vsz, Val.enc, Nat.add_assoc]

theorem vsz_int_loc (z : ℤ) : vsz (Val.int z) = isz z := by
  show (Val.int z).enc.length = isz z
  rw [Work.IntLib.vsz_int]

theorem vsz_ofList_loc : ∀ (vs : List Val), vsz (ofList vs) = (vs.map vsz).sum + vs.length + 1 := by
  intro vs
  induction vs with
  | nil => simp [ofList, vsz, Val.enc]
  | cons a t ih =>
    rw [show ofList (a :: t) = Val.cons a (ofList t) from rfl, vsz_cons_loc, ih]
    simp [List.sum_cons, List.length_cons]
    ring

/-- The induction step of `vsz_ofList_le_loc`, isolated. -/
theorem ofList_le_step (x n S B : ℕ) (ha : x ≤ B) (ih : S + n + 1 ≤ (n + 1) * (B + 1)) :
    x + S + (n + 1) + 1 ≤ (n + 1 + 1) * (B + 1) := by
  nlinarith

theorem vsz_ofList_le_loc {vs : List Val} {B : ℕ} (h : ∀ x ∈ vs, vsz x ≤ B) :
    vsz (ofList vs) ≤ (vs.length + 1) * (B + 1) := by
  rw [vsz_ofList_loc]
  induction vs with
  | nil => simp
  | cons a t ih =>
    have ha : vsz a ≤ B := h a (by simp)
    have ht : ∀ y ∈ t, vsz y ≤ B := fun y hy => h y (by simp [hy])
    have iht := ih ht
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    exact ofList_le_step (vsz a) t.length (List.map vsz t).sum B ha iht

/-- `vsz (zl l) = Σ isz + length + 1`. -/
theorem vsz_zl (l : List ℤ) : vsz (zl l) = (l.map isz).sum + l.length + 1 := by
  show vsz (HvdH.ofList (l.map Val.int)) = _
  rw [vsz_ofList_loc]
  have h1 : (l.map Val.int).map vsz = l.map isz := by
    rw [List.map_map]
    exact List.map_congr_left (fun z _ => vsz_int_loc z)
  have h2 : (l.map Val.int).length = l.length := List.length_map _
  rw [h1, h2]

/-- A bound for the size of a list of naturals with a uniform bound on each term. -/
theorem list_sum_le_length_mul : ∀ (l : List ℕ) (B : ℕ), (∀ x ∈ l, x ≤ B) → l.sum ≤ l.length * B := by
  intro l
  induction l with
  | nil => intro B _; simp
  | cons a t ih =>
    intro B h
    have ha : a ≤ B := h a (by simp)
    have ht : ∀ x ∈ t, x ≤ B := fun x hx => h x (by simp [hx])
    have iht := ih B ht
    rw [List.length_cons, List.sum_cons]
    nlinarith

/-- `isz z ≤ B + 2` when `|z| < 2^B`. -/
theorem isz_le_of_lt (z : ℤ) (B : ℕ) (h : z.natAbs < 2 ^ B) : isz z ≤ B + 2 := by
  have h1 : z.natAbs.size ≤ B := Nat.size_le.mpr h
  simp only [isz]
  omega

/-- `isz n ≤ B + 2` for a natural `n < 2^B`. -/
private theorem isz_natCast_le (n : ℕ) (B : ℕ) (h : n < 2 ^ B) : isz ((n : ℤ)) ≤ B + 2 := by
  rw [isz, Int.natAbs_natCast]
  have h1 : n.size ≤ B := Nat.size_le.mpr h
  omega

/-- `isz n ≤ p + 3` for a natural `n < 2^(p+1)`. -/
theorem isz_natCast_le_p3 (n p : ℕ) (h : n < 2 ^ (p + 1)) : isz ((n : ℤ)) ≤ p + 3 := by
  have h3 := isz_natCast_le n (p + 1) h
  omega

/-- `isz z ≤ p + 3` for `|z| ≤ A ≤ p + 1`. -/
private theorem isz_le_of_natAbs_le (z : ℤ) (A p : ℕ) (h : z.natAbs ≤ A) (hA : A ≤ p + 1) :
    isz z ≤ p + 3 := by
  have h2 : z.natAbs < 2 ^ (p + 1) := by
    have := Nat.lt_two_pow_self (n := p + 1)
    omega
  have h3 := isz_le_of_lt z (p + 1) h2
  omega

/-! ## The kept shifts `egHs m` -/

theorem egHs_length (m : ℕ) : (egHs m).length = 2 * m := by
  simp only [egHs, List.length_append, List.length_map, List.length_range]
  omega

theorem egHs_natAbs_le (m : ℕ) {h : ℤ} (hh : h ∈ egHs m) : h.natAbs ≤ m := by
  unfold egHs at hh
  rw [List.mem_append] at hh
  rcases hh with hh | hh
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hh
    rw [List.mem_range] at hi
    have h1 : -(m : ℤ) ≤ (i : ℤ) - (m : ℤ) := by omega
    have h2 : (i : ℤ) - (m : ℤ) ≤ (m : ℤ) := by omega
    have h3 : |(i : ℤ) - (m : ℤ)| ≤ (m : ℤ) := abs_le.mpr ⟨h1, h2⟩
    rw [Int.abs_eq_natAbs] at h3
    exact_mod_cast h3
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hh
    rw [List.mem_range] at hi
    have he : ((i : ℤ) + 1) = ((i + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [he, Int.natAbs_natCast]
    omega

/-! ## Index-map bounds -/

theorem egLam_le_sadd (s t i : ℕ) (hi : i < t) : egLam s t i ≤ s + t := by
  unfold egLam
  split
  · rename_i hmem
    exact le_trans (le_of_lt (Classical.choose hmem).isLt) (Nat.le_add_right s t)
  · omega

theorem egKeyS_lt (s t i : ℕ) (hs : 0 < s) : egKeyS s t i < s := by
  unfold egKeyS
  exact Nat.mod_lt _ hs

/-- `egLam s t i < 2^(p+1)` for `i < t < 2^p`, `s < 2^p`. -/
theorem egLam_lt_pow (s t p i : ℕ) (hi : i < t) (hsp : s < 2 ^ p) (htp : t < 2 ^ p) :
    egLam s t i < 2 ^ (p + 1) := by
  have h1 : egLam s t i ≤ s + t := egLam_le_sadd s t i hi
  have hss : s ≤ 2 ^ p - 1 := by omega
  have htt : t ≤ 2 ^ p - 1 := by omega
  have hpow : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [pow_succ]; ring
  omega

/-- `egKeyS s t i < 2^p` for `0 < s < 2^p`. -/
theorem egKeyS_lt_pow (s t p i : ℕ) (hs : 0 < s) (hsp : s < 2 ^ p) : egKeyS s t i < 2 ^ p :=
  lt_trans (egKeyS_lt s t i hs) hsp

/-! ## The arithmetic bounds in `p` -/

theorem buSZ_quartic (p : ℕ) (hp : 100 ≤ p) : buSZ p + p + 7 ≤ 300 * (p + 1) ^ 2 := by
  show 80 * (p * p) + 6000 * p + 100000 + p + 7 ≤ 300 * (p + 1) ^ 2
  nlinarith

theorem pow300_le (p : ℕ) (hp : 100 ≤ p) : (300 : ℕ) ≤ (p + 1) ^ 16 := by
  have h101 : (101 : ℕ) ≤ p + 1 := by omega
  have h : (101 : ℕ) ^ 16 ≤ (p + 1) ^ 16 := Nat.pow_le_pow_left h101 16
  have h300 : (300 : ℕ) ≤ 101 ^ 16 := by norm_num
  omega

theorem buSZ_p7_le_pow18 (p : ℕ) (hp : 100 ≤ p) : buSZ p + p + 7 ≤ (p + 1) ^ 18 := by
  have h1 : buSZ p + p + 7 ≤ 300 * (p + 1) ^ 2 := buSZ_quartic p hp
  have h2 : (300 : ℕ) ≤ (p + 1) ^ 16 := pow300_le p hp
  have h3 : 300 * (p + 1) ^ 2 ≤ (p + 1) ^ 18 := by
    calc 300 * (p + 1) ^ 2 ≤ (p + 1) ^ 16 * (p + 1) ^ 2 := Nat.mul_le_mul_right _ h2
      _ = (p + 1) ^ 18 := by rw [← pow_add]
  omega

theorem buSZ_1_le_pow20 (p : ℕ) (hp : 100 ≤ p) : buSZ p + 1 ≤ (p + 1) ^ 20 := by
  have h1 := buSZ_p7_le_pow18 p hp
  have h2 : (p + 1) ^ 18 ≤ (p + 1) ^ 20 :=
    Nat.pow_le_pow_right (by omega) (by norm_num)
  omega

theorem p4_le_pow20 (p : ℕ) (hp : 100 ≤ p) : p + 4 ≤ (p + 1) ^ 20 := by
  have h1 : p + 4 ≤ (p + 1) ^ 2 := by nlinarith
  have h2 : (p + 1) ^ 2 ≤ (p + 1) ^ 20 :=
    Nat.pow_le_pow_right (by omega) (by norm_num)
  omega

theorem two_mul_add_le_sq (p : ℕ) (hp : 100 ≤ p) : 2 * p + 3 ≤ (p + 1) ^ 2 := by nlinarith

/-! ## Small arithmetic steps of the main proof (clean contexts) -/

theorem arith7 (S t p : ℕ) (h : S ≤ t * (p + 3)) : S + t + 1 ≤ (t + 1) * (p + 4) := by nlinarith

theorem arith8 (S s p : ℕ) (h : S ≤ s * (p + 2)) : S + s + 1 ≤ (s + 1) * (p + 3) := by nlinarith

theorem arith9 (S s A : ℕ) (h : S ≤ s * A) : S + s + 1 ≤ (s + 1) * (A + 1) := by nlinarith

theorem arithElem (a b s A p : ℕ) (h1 : a ≤ p + 3) (h2 : b ≤ s * A + s + 1) :
    a + b + 1 ≤ p + s * A + s + 5 := by omega

theorem arithE1 (m p : ℕ) (hm : m ≤ p + 1) (hp : 100 ≤ p) : 2 * m + 1 ≤ (p + 1) ^ 2 := by
  have := two_mul_add_le_sq p hp
  omega

theorem arithE2 (s t p A : ℕ) (hst : s ≤ t) : p + s * A + s + 6 ≤ (t + 1) * (A + p + 7) := by
  nlinarith

/-! ## The main statement -/

theorem buEntrySizes (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
    (htp : t < 2 ^ p) (hαp : α ^ 2 < p)
    (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1) :
    HvdH.vsz (Work.Resample.buL7 p α s t) ≤ (t + 1) * (p + 1) ^ 20 ∧
    HvdH.vsz (Work.Resample.buL8 p α s t) ≤ (t + 1) * (p + 1) ^ 20 ∧
    HvdH.vsz (Work.Resample.buL9 p α s t) ≤ (t + 1) * (p + 1) ^ 20 ∧
    HvdH.vsz (Work.Resample.buL10 p α s t) ≤ (t + 1) * (p + 1) ^ 20 := by
  have hs0 : 0 < s := by omega
  have hαp2 : α ^ 2 ≤ p := by omega
  have hαle : α ≤ 2 ^ p := by
    have h1 : α ≤ α ^ 2 := Nat.le_self_pow (by omega : (2 : ℕ) ≠ 0) α
    have h2 : α < p := lt_of_le_of_lt h1 hαp
    exact le_trans (le_of_lt h2) (le_of_lt (Nat.lt_two_pow_self))
  have hsp : s < 2 ^ p := lt_trans hst htp
  -- `buL7`
  have h7 : vsz (buL7 p α s t) ≤ (t + 1) * (p + 1) ^ 20 := by
    have hb : ∀ x ∈ (List.ofFn (fun i : Fin t => (egLam s t (i : ℕ) : ℤ))).map isz,
        x ≤ p + 3 := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hz
      rw [← hi]
      exact isz_natCast_le_p3 (egLam s t (i : ℕ)) p (egLam_lt_pow s t p (i : ℕ) i.isLt hsp htp)
    have hsum := list_sum_le_length_mul
      ((List.ofFn (fun i : Fin t => (egLam s t (i : ℕ) : ℤ))).map isz) (p + 3) hb
    rw [List.length_map, List.length_ofFn] at hsum
    have hmain : vsz (buL7 p α s t)
        = (List.map isz (List.ofFn (fun i : Fin t => (egLam s t (i : ℕ) : ℤ)))).sum + t + 1 := by
      unfold buL7
      rw [vsz_zl, List.length_ofFn]
    rw [hmain]
    refine le_trans (arith7 _ _ _ hsum) ?_
    exact Nat.mul_le_mul_left _ (p4_le_pow20 p hp)
  -- `buL8`
  have h8 : vsz (buL8 p α s t) ≤ (t + 1) * (p + 1) ^ 20 := by
    have hb : ∀ x ∈ (List.ofFn (fun i : Fin s => (egKeyS s t (i : ℕ) : ℤ))).map isz,
        x ≤ p + 2 := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hz
      rw [← hi]
      exact isz_natCast_le (egKeyS s t (i : ℕ)) p (egKeyS_lt_pow s t p (i : ℕ) hs0 hsp)
    have hsum := list_sum_le_length_mul
      ((List.ofFn (fun i : Fin s => (egKeyS s t (i : ℕ) : ℤ))).map isz) (p + 2) hb
    rw [List.length_map, List.length_ofFn] at hsum
    have hmain : vsz (buL8 p α s t)
        = (List.map isz (List.ofFn (fun i : Fin s => (egKeyS s t (i : ℕ) : ℤ)))).sum + s + 1 := by
      unfold buL8
      rw [vsz_zl, List.length_ofFn]
    rw [hmain]
    have hfin2 : (s + 1) * (p + 3) ≤ (t + 1) * (p + 3) := Nat.mul_le_mul_right _ (by omega)
    have hfin3 : (t + 1) * (p + 3) ≤ (t + 1) * (p + 1) ^ 20 :=
      Nat.mul_le_mul_left _ (le_trans (by omega : p + 3 ≤ p + 4) (p4_le_pow20 p hp))
    exact le_trans (arith8 _ _ _ hsum) (le_trans hfin2 hfin3)
  -- `buL9`
  have h9 : vsz (buL9 p α s t) ≤ (t + 1) * (p + 1) ^ 20 := by
    have hb : ∀ x ∈ (List.ofFn (fun i : Fin s => buWd p α s t (i : ℤ))).map isz,
        x ≤ buSZ p := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hz
      rw [← hi]
      exact (buWdSize p α s t (i : ℤ) hαp2 hs0 hsp hp).2
    have hsum := list_sum_le_length_mul
      ((List.ofFn (fun i : Fin s => buWd p α s t (i : ℤ))).map isz) (buSZ p) hb
    rw [List.length_map, List.length_ofFn] at hsum
    have hmain : vsz (buL9 p α s t)
        = (List.map isz (List.ofFn (fun i : Fin s => buWd p α s t (i : ℤ)))).sum + s + 1 := by
      unfold buL9
      rw [vsz_zl, List.length_ofFn]
    rw [hmain]
    have hfin2 : (s + 1) * (buSZ p + 1) ≤ (t + 1) * (buSZ p + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have hfin3 : (t + 1) * (buSZ p + 1) ≤ (t + 1) * (p + 1) ^ 20 :=
      Nat.mul_le_mul_left _ (buSZ_1_le_pow20 p hp)
    exact le_trans (arith9 _ _ _ hsum) (le_trans hfin2 hfin3)
  -- `buL10`
  have hCol : ∀ h : ℤ, h ∈ egHs (egM p α) → vsz (buCol p α s t h) ≤ s * buSZ p + s + 1 := by
    intro h hh
    have hmem : h.natAbs ≤ egM p α := egHs_natAbs_le (egM p α) hh
    have hwt : ∀ ℓ : ℤ, isz (buWt p α s t ℓ h) ≤ buSZ p :=
      fun ℓ => isz_buWt_le p α s t ℓ h hαp2 hαle hs0 hmem hsp htp hp
    have hb : ∀ x ∈ (List.ofFn (fun ℓ : Fin s => buWt p α s t (ℓ : ℤ) h)).map isz,
        x ≤ buSZ p := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hz
      rw [← hi]
      exact hwt (i : ℤ)
    have hsum := list_sum_le_length_mul
      ((List.ofFn (fun ℓ : Fin s => buWt p α s t (ℓ : ℤ) h)).map isz) (buSZ p) hb
    rw [List.length_map, List.length_ofFn] at hsum
    have hmain : vsz (buCol p α s t h)
        = (List.map isz (List.ofFn (fun ℓ : Fin s => buWt p α s t (ℓ : ℤ) h))).sum + s + 1 := by
      unfold buCol
      rw [vsz_zl, List.length_ofFn]
    rw [hmain]
    exact Nat.add_le_add_right (Nat.add_le_add_right hsum s) 1
  have h10 : vsz (buL10 p α s t) ≤ (t + 1) * (p + 1) ^ 20 := by
    have hB : ∀ v ∈ (egHs (egM p α)).map (fun h => Val.cons (.int h) (buCol p α s t h)),
        vsz v ≤ p + s * buSZ p + s + 5 := by
      intro v hv
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hv
      have h1 : isz h ≤ p + 3 :=
        isz_le_of_natAbs_le h (egM p α) p (egHs_natAbs_le (egM p α) hh) (egM_le p α)
      have h2 := hCol h hh
      rw [vsz_cons_loc, vsz_int_loc]
      exact arithElem _ _ _ _ _ h1 h2
    have hlen : ((egHs (egM p α)).map (fun h => Val.cons (.int h) (buCol p α s t h))).length
        = 2 * egM p α := by
      rw [List.length_map, egHs_length]
    have h0 := vsz_ofList_le_loc hB
    rw [hlen] at h0
    have harg : (p + s * buSZ p + s + 5) + 1 = p + s * buSZ p + s + 6 := by ring
    rw [harg] at h0
    refine le_trans h0 ?_
    have e1 : 2 * egM p α + 1 ≤ (p + 1) ^ 2 := arithE1 (egM p α) p (egM_le p α) hp
    have e2 : p + s * buSZ p + s + 6 ≤ (t + 1) * (buSZ p + p + 7) :=
      arithE2 s t p (buSZ p) (le_of_lt hst)
    have hpw : (p + 1) ^ 2 * (p + 1) ^ 18 = (p + 1) ^ 20 := by rw [← pow_add]
    calc (2 * egM p α + 1) * (p + s * buSZ p + s + 6)
        ≤ (p + 1) ^ 2 * ((t + 1) * (buSZ p + p + 7)) := Nat.mul_le_mul e1 e2
      _ = (p + 1) ^ 2 * (t + 1) * (buSZ p + p + 7) := by ring
      _ ≤ (p + 1) ^ 2 * (t + 1) * (p + 1) ^ 18 :=
            Nat.mul_le_mul_left _ (buSZ_p7_le_pow18 p hp)
      _ = (t + 1) * ((p + 1) ^ 2 * (p + 1) ^ 18) := by ring
      _ = (t + 1) * (p + 1) ^ 20 := by rw [hpw]
  exact ⟨h7, h8, h9, h10⟩

end Work.Resample

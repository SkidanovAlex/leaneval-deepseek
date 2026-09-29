import Mathlib
import Submission.Work.Main.word.toCfxElem

/-!
# `Work.Resample.buQWelemKit`: toolkit for the per-element `B̃` words

The three per-element words needed by `Work.Resample.buQWelemWord` all act on a *fixed window* of
at most 6 values sitting on top of the value stack and leave everything below untouched; this is
exactly the `Pipe` interface of `Submission/Work/Main/word/toCfxElem.lean`, which is imported here
(`Work.Main.word.Pipe`, `Pipe.comp`, `Pipe.le`, `Pipe.rw`, `Pipe.appendTail`, `Pipe.pick`,
`Pipe.roll`, `Pipe.binOp`, `Pipe.consV`, `szl`, `vsz_int`, `vsz_cons`, `isz_le_of_natAbs_le`, …).

This file adds:

* `Pipe` adapters for the remaining library words (`unconsV`, `drop`) and "tail" versions acting on
  the top of a longer window: `bu_unconsV`, `bu_unconsTail`, `bu_consTail`, `bu_drop`,
  `bu_dropTail`, `bu_binOpTail`;
* uniform cost bounds for `roll`/`pick` (`bu_rollK`, `bu_pickK`): on a window of at most 5 values
  each of size `≤ 3P+4`, any roll/pick costs at most `120·K·(P+1)`;
* numeric cost lemmas `bu_const_bound` (constant costs `K`), `bu_add_bound` (costs
  `K·(isz a + isz b)` of `IntLib.add`, `IntLib.shrT`), `bu_mul_bound` (cost `K·isz a·isz b` of
  `IntLib.mulS` with one factor of size `≤ 3`), `bu_drop_bound`;
* size lemmas `vsz_int_le`, `vsz_cfxVal_le`, `natAbs_lt_two_pow_of_isz_le`, `isz_add_le`,
  `isz_mul_pm_le`, `isz_tdiv_le`, `isz_pm_one`;
* `szlTake_le`: encoding size of the first `m` entries of a window.

## How the three words are built (identical pattern)

Every word is a chain of library words on a fixed window; each step is a `Pipe` statement with cost
`coef · (P+1)`, composed with `Pipe.comp`; the total is rewritten with `ring`.  All windows are
lists of `Val`s of the form `Val.int z` or `Val.cons (Val.int x) (Val.int y)`; given the hypotheses
`isz a.1 ≤ P`, … every entry has `vsz ≤ 3P+4`.  The three chains are (writing `aᵢ` for `Val.int a.1`,
`A = cons (int a₁) (int a₂)` etc.):

* **`Work.Resample.buQWelemAdd`** (`cfxVal a :: cfxVal b ↦ cfxVal (a+b)`):
  ```
  [A,B] →ᵘⁿᶜ [a₁,a₂,B] →ʳᵒˡˡ² [B,a₁,a₂] →ᵘⁿᶜ [b₁,b₂,a₁,a₂] →ʳᵒˡˡ² [a₁,b₁,b₂,a₂]
        →ʳᵒˡˡ² [b₂,a₁,b₁,a₂] →ʳᵒˡˡ³ [a₂,b₂,a₁,b₁] →ᵃᵈᵈ [a₂+b₂,a₁,b₁] →ʳᵒˡˡ² [b₁,a₂+b₂,a₁]
        →ʳᵒˡˡ² [a₁,b₁,a₂+b₂] →ᵃᵈᵈ [a₁+b₁,a₂+b₂] →ᶜᵒⁿˢ [cfxVal (a+b)]
  ```
  cost `≤ (720·KR + 4·Kad + Kcs + 2·Ku)·(P+1)`.
* **`Work.Resample.buQWelemShr`** (`cfxVal a :: int pp ↦ cfxVal (tdiv aᵢ 2^pp)`):
  ```
  [A, pp] →ᵘⁿᶜ [a₁,a₂,pp] →ᵖⁱᶜᵏ² [pp,a₁,a₂,pp] →ʳᵒˡˡ² [a₂,pp,a₁,pp] →ˢʰʳᵀ [t₂,a₁,pp]
          →ʳᵒˡˡ² [pp,t₂,a₁] →ʳᵒˡˡ² [a₁,pp,t₂] →ˢʰʳᵀ [t₁,t₂] →ᶜᵒⁿˢ [cfxVal (t₁,t₂)]
  ```
  where `tᵢ = Val.int (Int.tdiv aᵢ ((2:ℤ)^((pp:ℤ).toNat)))`; rewrite `(pp:ℤ).toNat = pp` only at the
  end (`Int.toNat_natCast`).  `IntLib.shrT` needs `0 ≤ (pp:ℤ)` (`Int.natCast_nonneg`).
* **`Work.Resample.buQWelemLin`** (`cfxVal a :: cfxVal b :: int σ ↦ cfxVal (a + σ b)`, `σ = ±1`):
  ```
  [A,B,σ] →ᵘⁿᶜ [a₁,a₂,B,σ] →ʳᵒˡˡ² [B,a₁,a₂,σ] →ᵘⁿᶜ [b₁,b₂,a₁,a₂,σ] →ᵖⁱᶜᵏ⁴ [σ,b₁,b₂,a₁,a₂,σ]
          →ʳᵒˡˡ¹ [b₁,σ,b₂,a₁,a₂,σ] →ᵐᵘˡˢ [b₁σ,b₂,a₁,a₂,σ] →ᵖⁱᶜᵏ⁴ [σ,b₁σ,b₂,a₁,a₂,σ]
          →ʳᵒˡˡ² [b₂,σ,b₁σ,a₁,a₂,σ] →ᵐᵘˡˢ [b₂σ,b₁σ,a₁,a₂,σ] →ʳᵒˡˡ³ [a₂,b₂σ,b₁σ,a₁,σ]
          →ᵃᵈᵈ [a₂+b₂σ,b₁σ,a₁,σ] →ʳᵒˡˡ² [a₁,a₂+b₂σ,b₁σ,σ] →ᵃᵈᵈ [a₁+b₁σ,a₂+b₂σ,σ]
          →ʳᵒˡˡ² [σ,a₁+b₁σ,a₂+b₂σ] →ᵈʳᵒᵖ [a₁+b₁σ,a₂+b₂σ] →ᶜᵒⁿˢ [cfxVal (a₁+σb₁, a₂+σb₂)]
  ```
  (`IntLib.mulS` computes `b*σ`; use `Int.mul_comm` for the final `σ*b`.)

In all three, the `have hM : ∀ v ∈ <window>, vsz v ≤ 3*P+4` obligations are discharged by
`intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with
rfl | rfl | … <;> [exact …; …]` using the size lemmas below, and the cost of `Pipe.roll`/`Pipe.pick`
is handled by `bu_rollK`/`bu_pickK`.  The final `WordR` is obtained from the chain by
`intro vs ⟨rest, hvs⟩ s R hR; obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := hchain rest vs hvs s R hR;
exact ⟨out, s', n, ⟨rest, hvs, hout⟩, hev, hn, hstk, hoth⟩`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH
open Work.Main.word

local infixr:68 " ;;; " => HvdH.Cmd.seq

/-! ## Size and cost arithmetic -/

theorem vsz_int_le {z : ℤ} {M : ℕ} (h : isz z ≤ M) : vsz (Val.int z) ≤ M := by
  rw [vsz_int]; exact h

theorem vsz_cfxVal_le {P : ℕ} {x y : ℤ} (hx : isz x ≤ P) (hy : isz y ≤ P) :
    vsz (Val.cons (Val.int x) (Val.int y)) ≤ 3 * P + 4 := by
  rw [vsz_cons, vsz_int, vsz_int]; omega

theorem natAbs_lt_two_pow_of_isz_le {z : ℤ} {P : ℕ} (h : isz z ≤ P) : z.natAbs < 2 ^ P := by
  have h1 : z.natAbs.size ≤ P - 2 := by simp only [isz] at h; omega
  have h2 : z.natAbs < 2 ^ (P - 2) := Nat.size_le.mp h1
  exact lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le P 2))

theorem isz_add_le {P : ℕ} {x y : ℤ} (hx : isz x ≤ P) (hy : isz y ≤ P) :
    isz (x + y) ≤ 3 * P + 4 := by
  have h1 : x.natAbs < 2 ^ P := natAbs_lt_two_pow_of_isz_le hx
  have h2 : y.natAbs < 2 ^ P := natAbs_lt_two_pow_of_isz_le hy
  have h3 : (x + y).natAbs ≤ x.natAbs + y.natAbs := Int.natAbs_add_le _ _
  have h4 : (x + y).natAbs < 2 ^ (P + 1) := by
    have h5 : x.natAbs + y.natAbs ≤ 2 ^ P * 2 - 2 := by omega
    calc (x + y).natAbs ≤ x.natAbs + y.natAbs := h3
      _ ≤ 2 ^ P * 2 - 2 := h5
      _ < 2 ^ P * 2 := by omega
      _ = 2 ^ (P + 1) := by rw [pow_succ]
  have h6 : (x + y).natAbs.size ≤ P + 1 := Nat.size_le.mpr h4
  simp only [isz]; omega

theorem isz_pm_one {σ : ℤ} (h : σ = 1 ∨ σ = -1) : isz σ ≤ 3 := by
  rcases h with rfl | rfl
  · exact isz_le_of_natAbs_le (p := 0) (by norm_num)
  · exact isz_le_of_natAbs_le (p := 0) (by norm_num)

theorem isz_mul_pm_le {P : ℕ} {x σ : ℤ} (hx : isz x ≤ P) (hσ : σ = 1 ∨ σ = -1) :
    isz (x * σ) ≤ 3 * P + 4 := by
  have h : isz (x * σ) ≤ isz x := by
    rcases hσ with rfl | rfl
    · rw [mul_one]
    · rw [mul_neg_one]; simp only [isz, Int.natAbs_neg]
      omega
  omega

theorem isz_tdiv_le {P : ℕ} {x : ℤ} (hx : isz x ≤ P) (k : ℕ) :
    isz (Int.tdiv x ((2 : ℤ) ^ k)) ≤ 3 * P + 4 := by
  have h1 : (Int.tdiv x ((2 : ℤ) ^ k)).natAbs ≤ x.natAbs := by
    rw [Int.natAbs_tdiv]; exact Nat.div_le_self _ _
  have h2 : x.natAbs < 2 ^ P := natAbs_lt_two_pow_of_isz_le hx
  have h3 : (Int.tdiv x ((2 : ℤ) ^ k)).natAbs < 2 ^ P := lt_of_le_of_lt h1 h2
  have h4 : (Int.tdiv x ((2 : ℤ) ^ k)).natAbs.size ≤ P := Nat.size_le.mpr h3
  simp only [isz]; omega

theorem sum_le_length_mul {l : List ℕ} {M : ℕ} (h : ∀ x ∈ l, x ≤ M) :
    l.sum ≤ l.length * M := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have h1 : a ≤ M := h a (by simp)
    have h2 : t.sum ≤ t.length * M := ih (fun x hx => h x (by simp [hx]))
    simp only [List.sum_cons, List.length_cons, add_mul, one_mul]
    omega

theorem szlTake_le (A : List Val) (m M : ℕ) (h : ∀ v ∈ A, vsz v ≤ M) :
    szl (A.take m) ≤ m * M := by
  have h1 : szl (A.take m) ≤ (A.take m).length * M := by
    have := sum_le_length_mul (l := (A.take m).map vsz) (M := M) (fun x hx => by
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
      exact h v (List.mem_of_mem_take hv))
    simpa [szl, List.length_map] using this
  calc szl (A.take m) ≤ (A.take m).length * M := h1
    _ ≤ m * M := Nat.mul_le_mul_right M (by rw [List.length_take]; exact Nat.min_le_left _ _)

theorem bu_const_bound (K P : ℕ) : K ≤ K * (P + 1) :=
  Nat.le_mul_of_pos_right K (Nat.succ_pos P)

theorem bu_add_bound {K P u v : ℕ} (hu : u ≤ P) (hv : v ≤ P) :
    K * (u + v) ≤ 2 * K * (P + 1) := by
  have h : u + v ≤ 2 * (P + 1) := by omega
  calc K * (u + v) ≤ K * (2 * (P + 1)) := Nat.mul_le_mul_left K h
    _ = 2 * K * (P + 1) := by ring

theorem bu_mul_bound {K P u v : ℕ} (hu : u ≤ P) (hv : v ≤ 3) :
    K * u * v ≤ 3 * K * (P + 1) := by
  have h : u * v ≤ 3 * (P + 1) := by
    have h1 : u * v ≤ P * 3 := Nat.mul_le_mul hu hv
    omega
  calc K * u * v = K * (u * v) := by ring
    _ ≤ K * (3 * (P + 1)) := Nat.mul_le_mul_left K h
    _ = 3 * K * (P + 1) := by ring

theorem bu_drop_bound {K P v : ℕ} (hv : v ≤ P + 1) : K * (v + 1) ≤ 2 * K * (P + 1) := by
  have h : v + 1 ≤ 2 * (P + 1) := by omega
  calc K * (v + 1) ≤ K * (2 * (P + 1)) := Nat.mul_le_mul_left K h
    _ = 2 * K * (P + 1) := by ring

/-! ## `Pipe` adapters -/

/-- `KernelLib.unconsV` as a `Pipe` on a one-value window. -/
theorem bu_unconsV {prog : Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ m : Cmd, WordR m prog
      (fun vs => ∃ a b rest, vs = .cons a b :: rest)
      (fun vs out => ∃ a b rest, vs = .cons a b :: rest ∧ out = a :: b :: rest)
      (fun _ => K)) (a b : Val) :
    Pipe main prog [Val.cons a b] [a, b] K := by
  intro rest vs hvs s R hR
  have hv2 : vs = Val.cons a b :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', b', rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs ⟨a, b, rest, hv2⟩ s R hR
  have h1 := List.cons.inj (hvs'.symm.trans hv2)
  have h2 := Val.cons.inj h1.1
  refine ⟨out, s', n, ?_, hev, hn, hstk, hoth⟩
  rw [hout, h2.1, h2.2, h1.2]
  rfl

/-- `KernelLib.unconsV` at the top of a longer window. -/
theorem bu_unconsTail {prog : Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ m : Cmd, WordR m prog
      (fun vs => ∃ a b rest, vs = .cons a b :: rest)
      (fun vs out => ∃ a b rest, vs = .cons a b :: rest ∧ out = a :: b :: rest)
      (fun _ => K)) (a b : Val) (T : List Val) :
    Pipe main prog (Val.cons a b :: T) (a :: b :: T) K :=
  Pipe.appendTail T (bu_unconsV main h a b)

/-- `KernelLib.consV` at the top of a longer window. -/
theorem bu_consTail {consP : Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ m : Cmd, WordR m consP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest) (fun _ => K))
    (a b : Val) (T : List Val) :
    Pipe main consP (a :: b :: T) (Val.cons a b :: T) K :=
  Pipe.appendTail T (Pipe.consV main h a b)

/-- `KernelLib.drop` as a `Pipe` on a one-value window. -/
theorem bu_drop {prog : Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ m : Cmd, WordR m prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1))) (a : Val) :
    Pipe main prog [a] [] (K * (vsz a + 1)) := by
  intro rest vs hvs s R hR
  have hv2 : vs = a :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨v, rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs (by rw [hv2]; simp) s R hR
  have h1 := List.cons.inj (hvs'.symm.trans hv2)
  have hv : v = a := h1.1
  refine ⟨out, s', n, ?_, hev, ?_, hstk, hoth⟩
  · rw [hout, h1.2]; rfl
  · rw [hv2] at hn
    simpa only [List.headD_cons] using hn

/-- `KernelLib.drop` at the top of a longer window. -/
theorem bu_dropTail {prog : Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ m : Cmd, WordR m prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1))) (a : Val) (T : List Val) :
    Pipe main prog (a :: T) T (K * (vsz a + 1)) :=
  Pipe.appendTail T (bu_drop main h a)

/-- A `BinOp` acting on the top two values of a longer window. -/
theorem bu_binOpTail {prog : Cmd} {Pr : ℤ → ℤ → Prop} {f : ℤ → ℤ → ℤ} {C : ℤ → ℤ → ℕ}
    (main : Cmd) (h : BinOp main prog Pr f C) {a b : ℤ} (hab : Pr a b) {c : ℕ}
    (hc : C a b ≤ c) (T : List Val) :
    Pipe main prog (Val.int a :: Val.int b :: T) (Val.int (f a b) :: T) c :=
  Pipe.appendTail T (Pipe.le (Pipe.binOp h hab) hc)

/-- `KernelLib.roll` on a window of at most 5 values of size `≤ 3P+4`: cost `≤ 120·K·(P+1)`. -/
theorem bu_rollK {rollP : ℕ → Cmd} {KR : ℕ} (main : Cmd)
    (h : ∀ (m : Cmd) (k : ℕ), WordR m (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => KR * (k + 1) * (szl (vs.take (k + 1)) + 1)))
    {A : List Val} {k P : ℕ} (hk : k < A.length) (hk5 : k + 1 ≤ 5)
    (hM : ∀ v ∈ A, vsz v ≤ 3 * P + 4) :
    Pipe main (rollP k) A (A.getD k .nil :: A.eraseIdx k) (120 * KR * (P + 1)) := by
  refine Pipe.le (Pipe.roll main h hk) ?_
  have hS : szl (A.take (k + 1)) ≤ 15 * P + 20 := by
    calc szl (A.take (k + 1)) ≤ (k + 1) * (3 * P + 4) := szlTake_le A (k + 1) (3 * P + 4) hM
      _ ≤ 5 * (3 * P + 4) := Nat.mul_le_mul_right _ hk5
      _ = 15 * P + 20 := by ring
  have hS1 : szl (A.take (k + 1)) + 1 ≤ 21 * (P + 1) := by omega
  have h2 : KR * (k + 1) * (szl (A.take (k + 1)) + 1) ≤ KR * 5 * (21 * (P + 1)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left KR hk5) hS1
  calc KR * (k + 1) * (szl (A.take (k + 1)) + 1) ≤ KR * 5 * (21 * (P + 1)) := h2
    _ = 105 * KR * (P + 1) := by ring
    _ ≤ 120 * KR * (P + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right KR (by norm_num))

/-- `KernelLib.pick` on a window of at most 5 values of size `≤ 3P+4`: cost `≤ 120·K·(P+1)`. -/
theorem bu_pickK {pickP : ℕ → Cmd} {KP : ℕ} (main : Cmd)
    (h : ∀ (m : Cmd) (k : ℕ), WordR m (pickP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => KP * (k + 1) * (szl (vs.take (k + 1)) + 1)))
    {A : List Val} {k P : ℕ} (hk : k < A.length) (hk5 : k + 1 ≤ 5)
    (hM : ∀ v ∈ A, vsz v ≤ 3 * P + 4) :
    Pipe main (pickP k) A (A.getD k .nil :: A) (120 * KP * (P + 1)) := by
  refine Pipe.le (Pipe.pick main h hk) ?_
  have hS : szl (A.take (k + 1)) ≤ 15 * P + 20 := by
    calc szl (A.take (k + 1)) ≤ (k + 1) * (3 * P + 4) := szlTake_le A (k + 1) (3 * P + 4) hM
      _ ≤ 5 * (3 * P + 4) := Nat.mul_le_mul_right _ hk5
      _ = 15 * P + 20 := by ring
  have hS1 : szl (A.take (k + 1)) + 1 ≤ 21 * (P + 1) := by omega
  have h2 : KP * (k + 1) * (szl (A.take (k + 1)) + 1) ≤ KP * 5 * (21 * (P + 1)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left KP hk5) hS1
  calc KP * (k + 1) * (szl (A.take (k + 1)) + 1) ≤ KP * 5 * (21 * (P + 1)) := h2
    _ = 105 * KP * (P + 1) := by ring
    _ ≤ 120 * KP * (P + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right KP (by norm_num))

end Work.Resample

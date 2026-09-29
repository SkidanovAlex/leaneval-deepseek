import Mathlib
import Submission.Work.Fx.ExpDefs
import Submission.Work.Fx.ExpPre
import Submission.Work.Fx.expPreludeList
import Submission.Work.Fx.expPreludeSizes

/-!
# `Work.Fx.expPrelude`: the prelude of the fixed-point complex exponential

`prog` turns the input `int p :: int X :: int Y :: rest` into the seed state of the Horner fold

`[ofList (replicate (wcnt p) (int 1)), Pow, 0, wcnt p, X·2^{d0 p}, Y·2^{d0 p}, Pow, d0 p] ++ rest`

where `Pow = 2^{wprec p}`.  The word is the composition of three pieces:

* `Work.Fx.expPreludeArrange` — the seven-value parameter window (`Qre = Pow`, `Qim = 0`,
  `dd = wcnt p`, `Zs = X·2^{d0 p}`, `Zt = Y·2^{d0 p}`, `Pow`, `d0 p`);
* `expPreludeSetup` (below) — copy `dd` to the top and insert the `nil` list seed just below it;
* `Work.Fx.expPreludeList` — build `ofList (replicate (wcnt p) (int 1))`.

Cost: the first word contributes `KA (p+1)^KA`, the setup moves contribute `O(S)` with
`S = 40 (p+1)` a bound on every window value, and the list loop contributes `O((wcnt p + 1)^KL)`
with `wcnt p = 8 (p+1)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 20000000

namespace Work.Fx

open HvdH
open Work.Fx.ExpAsm

/-! ## List size bookkeeping -/

theorem getD_mem_of_lt {l : List Val} {k : ℕ} (h : k < l.length) : l.getD k .nil ∈ l := by
  induction l generalizing k with
  | nil => simp at h
  | cons a t ih =>
    cases k with
    | zero => simp
    | succ j => exact List.mem_cons_of_mem a (ih (by simpa using h))

/-! ## The parameter window of the fold state -/

/-- The seven-value window `Qre, Qim, dd, Zs, Zt, Pow, d0` produced by the prelude. -/
def preA (p : ℕ) (X Y : ℤ) : List Val :=
  [Val.int ((2 : ℤ) ^ wprec p), Val.int 0, Val.int ((wcnt p : ℕ) : ℤ),
   Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p),
   Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ)]

@[simp] theorem preA_length (p : ℕ) (X Y : ℤ) : (preA p X Y).length = 7 := rfl

theorem preA_getD_two (p : ℕ) (X Y : ℤ) :
    (preA p X Y).getD 2 .nil = Val.int ((wcnt p : ℕ) : ℤ) := rfl

theorem isz_zero_x1 : isz (0 : ℤ) = 2 := by simp [isz]

/-- Every value of the window has encoding size at most `40 (p+1)`. -/
theorem preA_sizes (p : ℕ) (X Y : ℤ) (hp : 100 ≤ p)
    (h : (X : ℝ) ^ 2 + (Y : ℝ) ^ 2 ≤ (32 * 2 ^ p) ^ 2) :
    ∀ v ∈ preA p X Y, vsz v ≤ 40 * (p + 1) := by
  have hX : (X : ℝ) ^ 2 ≤ (32 * 2 ^ p) ^ 2 := by nlinarith [sq_nonneg (Y : ℝ)]
  have hY : (Y : ℝ) ^ 2 ≤ (32 * 2 ^ p) ^ 2 := by nlinarith [sq_nonneg (X : ℝ)]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := expPreludeSizes p hp X Y hX hY
  intro v hv
  simp only [preA, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [vsz_int]; exact h5
  · rw [vsz_int, isz_zero_x1]; omega
  · rw [vsz_int]; exact h8
  · rw [vsz_int]; exact h3
  · rw [vsz_int]; exact h4
  · rw [vsz_int]; exact h5
  · rw [vsz_int]; exact h6

/-! ## A consequence rule for `WordR` -/

/-- The `conseq` field of `KernelLib`, with the parameters inferred. -/
theorem wordR_conseq (hK : HvdH.KernelLib) {main p : HvdH.Cmd} {P P' : List Val → Prop}
    {Q Q' : List Val → List Val → Prop} {C C' : List Val → ℕ} (h : HvdH.WordR main p P Q C)
    (hP : ∀ vs, P' vs → P vs) (hQ : ∀ vs out, P' vs → Q vs out → Q' vs out)
    (hC : ∀ vs, P' vs → C vs ≤ C' vs) : HvdH.WordR main p P' Q' C' :=
  hK.conseq main p P P' Q Q' C C' h hP hQ hC

/-- Window relabelling for a `WordR` spec: the same word, with the window replaced along
equalities of lists. -/
theorem w_conv (hk : HvdH.KernelLib) {main p : HvdH.Cmd} {A B A' B' : List Val} {c : ℕ}
    (h : HvdH.WordR main p (fun vs => vs = A) (fun _ out => out = B) (fun _ => c))
    (hA : A' = A) (hB : B = B') :
    HvdH.WordR main p (fun vs => vs = A') (fun _ out => out = B') (fun _ => c) := by
  refine wordR_conseq hk h ?_ ?_ ?_
  · intro vs hvs; rw [hvs, hA]
  · intro vs out hvs hq; rw [hq, hB]
  · intro vs hvs; exact le_rfl

/-- Budget check for one word: a product `x * y` with `x ≤ 1000 KT` and `y ≤ 100 (S+1)` fits the
step budget `100000 KT (S+1)`. -/
theorem le_CB {x y KT S : ℕ} (h1 : x ≤ 1000 * KT) (h2 : y ≤ 100 * (S + 1)) :
    x * y ≤ 100000 * KT * (S + 1) := by
  calc x * y ≤ (1000 * KT) * (100 * (S + 1)) := Nat.mul_le_mul h1 h2
    _ = 100000 * KT * (S + 1) := by ring


/-! ## The setup moves around the list loop -/

/-- Copy `dd = A.getD 2` to the top of the window, push the `nil` list seed below it and swap the
two back: from `A ++ rest` to `dd :: nil :: A ++ rest`, at cost `O(S)`. -/
theorem expPreludeSetup (hk : HvdH.KernelLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (A rest : List HvdH.Val) (S : ℕ),
      3 ≤ A.length → (∀ v ∈ A, vsz v ≤ S) →
      HvdH.WordR main prog (fun vs => vs = A ++ rest)
        (fun _ out => out = (A.getD 2 .nil :: HvdH.Val.nil :: A) ++ rest)
        (fun _ => K * (S + 1)) := by
  obtain ⟨pickP, Kpick, hpick⟩ := hk.pick
  obtain ⟨pushP, Kpush, hpush⟩ := hk.pushVal
  obtain ⟨swapP, Kswap, hswap⟩ := hk.swap
  refine ⟨Cmd.seq (pickP 2) (Cmd.seq (pushP Val.nil) swapP),
    30 * (Kpick + Kpush + Kswap + 1), ?_⟩
  intro main A rest S hlen hsz
  have hmem : A.getD 2 .nil ∈ A := getD_mem_of_lt (by omega)
  have hget : (A ++ rest).getD 2 .nil = A.getD 2 .nil := getD_append_of_lt (by omega)
  have hlenAR : 2 < (A ++ rest).length := by simp [List.length_append]; omega
  have hsum : (((A ++ rest).take (2 + 1)).map vsz).sum ≤ 3 * S := by
    rw [List.take_append_of_le_length (by omega : 3 ≤ A.length)]
    exact sum_take_le hsz 2
  have s1 : HvdH.WordR main (pickP 2) (fun vs => vs = A ++ rest)
      (fun _ out => out = A.getD 2 .nil :: (A ++ rest))
      (fun _ => 10 * (Kpick + Kpush + Kswap + 1) * (S + 1)) := by
    refine w_pick (hpick main) 2 (A ++ rest) (A.getD 2 .nil) hget hlenAR ?_
    have h1 : (((A ++ rest).take (2 + 1)).map vsz).sum + 1 ≤ 3 * (S + 1) := by omega
    calc Kpick * (2 + 1) * ((((A ++ rest).take (2 + 1)).map vsz).sum + 1)
        ≤ Kpick * (2 + 1) * (3 * (S + 1)) := Nat.mul_le_mul_left _ h1
      _ = 9 * Kpick * (S + 1) := by ring
      _ ≤ 10 * (Kpick + Kpush + Kswap + 1) * (S + 1) := Nat.mul_le_mul_right _ (by omega)
  have s2 : HvdH.WordR main (pushP Val.nil) (fun vs => vs = A.getD 2 .nil :: (A ++ rest))
      (fun _ out => out = Val.nil :: (A.getD 2 .nil :: (A ++ rest)))
      (fun _ => 10 * (Kpick + Kpush + Kswap + 1) * (S + 1)) := by
    refine w_pushVal (hpush main Val.nil) (A.getD 2 .nil :: (A ++ rest)) ?_
    rw [vsz_nil]
    calc Kpush * (1 + 1) = 2 * Kpush := by ring
      _ ≤ 2 * (Kpick + Kpush + Kswap + 1) := by omega
      _ = 2 * (Kpick + Kpush + Kswap + 1) * 1 := by ring
      _ ≤ 2 * (Kpick + Kpush + Kswap + 1) * (S + 1) :=
          Nat.mul_le_mul_left _ (by omega : 1 ≤ S + 1)
      _ ≤ 10 * (Kpick + Kpush + Kswap + 1) * (S + 1) := Nat.mul_le_mul_right _ (by omega)
  have s3 : HvdH.WordR main swapP (fun vs => vs = Val.nil :: (A.getD 2 .nil :: (A ++ rest)))
      (fun _ out => out = A.getD 2 .nil :: (Val.nil :: (A ++ rest)))
      (fun _ => 10 * (Kpick + Kpush + Kswap + 1) * (S + 1)) := by
    refine w_swap (hswap main) Val.nil (A.getD 2 .nil) (A ++ rest) ?_
    have h1 : vsz (A.getD 2 .nil) ≤ S := hsz _ hmem
    rw [vsz_nil]
    calc Kswap * (1 + vsz (A.getD 2 .nil) + 1)
        ≤ Kswap * (1 + S + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = Kswap * (S + 2) := by ring
      _ ≤ Kswap * (2 * (S + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * Kswap * (S + 1) := by ring
      _ ≤ 10 * (Kpick + Kpush + Kswap + 1) * (S + 1) := Nat.mul_le_mul_right _ (by omega)
  have hchain := w_seq2 s1 (w_seq2 s2 s3)
  refine wordR_conseq hk hchain (fun vs h => h) (fun vs out h hq => hq) ?_
  intro vs hvs
  exact le_of_eq (by ring)

/-! ## The parameter window -/

/-- All the size facts (in bits) needed by the stages of the prelude window construction. -/
theorem prelude_isz_facts (p : ℕ) (X Y : ℤ) (hp : 100 ≤ p)
    (hR : (X : ℝ) ^ 2 + (Y : ℝ) ^ 2 ≤ (32 * 2 ^ p) ^ 2) :
    HvdH.isz X ≤ 40 * (p + 1) ∧ HvdH.isz Y ≤ 40 * (p + 1) ∧
    HvdH.isz (X * (2 : ℤ) ^ d0 p) ≤ 40 * (p + 1) ∧
    HvdH.isz (Y * (2 : ℤ) ^ d0 p) ≤ 40 * (p + 1) ∧
    HvdH.isz ((2 : ℤ) ^ wprec p) ≤ 40 * (p + 1) ∧
    HvdH.isz ((d0 p : ℕ) : ℤ) ≤ d0 p + 2 ∧
    HvdH.isz ((wprec p : ℕ) : ℤ) ≤ wprec p + 2 ∧
    HvdH.isz ((wcnt p : ℕ) : ℤ) ≤ 40 * (p + 1) ∧
    HvdH.isz (p : ℤ) ≤ p + 2 ∧
    HvdH.isz (3 : ℤ) = 4 ∧ HvdH.isz (70 : ℤ) = 9 ∧ HvdH.isz (8 : ℤ) = 6 ∧
    HvdH.isz (1 : ℤ) = 3 ∧ HvdH.isz (0 : ℤ) = 2 ∧
    HvdH.isz (p : ℤ) ≤ p + 2 ∧
    HvdH.isz ((p.size : ℕ) : ℤ) ≤ p + 2 ∧
    HvdH.isz ((d0 p : ℕ) : ℤ) ≤ d0 p + 2 ∧
    HvdH.isz ((wprec p : ℕ) : ℤ) ≤ wprec p + 2 ∧
    HvdH.isz (3 * ((p.size : ℕ) : ℤ)) ≤ p + 6 ∧
    HvdH.isz (70 + 3 * ((p.size : ℕ) : ℤ)) ≤ p + 10 ∧
    HvdH.isz (((d0 p : ℕ) : ℤ) + (p : ℤ)) ≤ 40 * (p + 1) ∧
    HvdH.isz ((1 : ℤ) + (p : ℤ)) ≤ p + 3 ∧
    HvdH.isz (8 * ((1 : ℤ) + (p : ℤ))) ≤ p + 9 ∧
    wprec p ≤ 5 * (p + 1) ∧ d0 p ≤ 4 * (p + 1) ∧ p.size ≤ p := by
  have hX2 : (X : ℝ) ^ 2 ≤ (32 * 2 ^ p) ^ 2 := by nlinarith [sq_nonneg (Y : ℝ)]
  have hY2 : (Y : ℝ) ^ 2 ≤ (32 * 2 ^ p) ^ 2 := by nlinarith [sq_nonneg (X : ℝ)]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := expPreludeSizes p hp X Y hX2 hY2
  have hpsle : p.size ≤ p := Nat.size_le.mpr (Nat.lt_two_pow_self (n := p))
  have hd0le : d0 p ≤ 4 * (p + 1) := by simp only [d0]; omega
  have hwple : wprec p ≤ 5 * (p + 1) := by simp only [wprec]; omega
  have h_isz3 : HvdH.isz (3 : ℤ) = 4 := by decide
  have h_isz70 : HvdH.isz (70 : ℤ) = 9 := by decide
  have h_isz8 : HvdH.isz (8 : ℤ) = 6 := by decide
  have h_isz1 : HvdH.isz (1 : ℤ) = 3 := by decide
  have h_isz0 : HvdH.isz (0 : ℤ) = 2 := by decide
  have hnatp : Int.natAbs (p : ℤ) = p := Int.natAbs_natCast p
  have hnatps : Int.natAbs ((p.size : ℕ) : ℤ) = p.size := Int.natAbs_natCast p.size
  have hnatd0 : Int.natAbs ((d0 p : ℕ) : ℤ) = d0 p := Int.natAbs_natCast (d0 p)
  have hnatwp : Int.natAbs ((wprec p : ℕ) : ℤ) = wprec p := Int.natAbs_natCast (wprec p)
  have hiszp : HvdH.isz (p : ℤ) ≤ p + 2 := by
    have h := Nat.size_le.mpr (Nat.lt_two_pow_self (n := p))
    simp only [HvdH.isz, hnatp]
    omega
  have hiszps : HvdH.isz ((p.size : ℕ) : ℤ) ≤ p + 2 := by
    have h := Nat.size_le.mpr (Nat.lt_two_pow_self (n := p.size))
    simp only [HvdH.isz, hnatps]
    omega
  have hiszd0 : HvdH.isz ((d0 p : ℕ) : ℤ) ≤ d0 p + 2 := by
    have h := Nat.size_le.mpr (Nat.lt_two_pow_self (n := d0 p))
    simp only [HvdH.isz, hnatd0]
    omega
  have hiszwp : HvdH.isz ((wprec p : ℕ) : ℤ) ≤ wprec p + 2 := by
    have h := Nat.size_le.mpr (Nat.lt_two_pow_self (n := wprec p))
    simp only [HvdH.isz, hnatwp]
    omega
  have hiszt3 : HvdH.isz (3 * ((p.size : ℕ) : ℤ)) ≤ p + 6 := by
    have h := Work.Fx.isz_mul_le (3 : ℤ) ((p.size : ℕ) : ℤ)
    omega
  have hiszt70 : HvdH.isz (70 + 3 * ((p.size : ℕ) : ℤ)) ≤ p + 10 := by
    have h := Work.Fx.isz_add_le (70 : ℤ) (3 * ((p.size : ℕ) : ℤ))
    have hmax : max (HvdH.isz (70 : ℤ)) (HvdH.isz (3 * ((p.size : ℕ) : ℤ))) ≤ p + 9 :=
      max_le (by omega) (by omega)
    omega
  have hisztwp : HvdH.isz (((d0 p : ℕ) : ℤ) + (p : ℤ)) ≤ 40 * (p + 1) := by
    have h := Work.Fx.isz_add_le ((d0 p : ℕ) : ℤ) (p : ℤ)
    have hmax : max (HvdH.isz ((d0 p : ℕ) : ℤ)) (HvdH.isz (p : ℤ)) ≤ 5 * (p + 1) :=
      max_le (by omega) (by omega)
    omega
  have hiszp1 : HvdH.isz ((1 : ℤ) + (p : ℤ)) ≤ p + 3 := by
    have h := Work.Fx.isz_add_le (1 : ℤ) (p : ℤ)
    have hmax : max (HvdH.isz (1 : ℤ)) (HvdH.isz (p : ℤ)) ≤ p + 2 :=
      max_le (by omega) (by omega)
    omega
  have hisztwc : HvdH.isz (8 * ((1 : ℤ) + (p : ℤ))) ≤ p + 9 := by
    have h := Work.Fx.isz_mul_le (8 : ℤ) ((1 : ℤ) + (p : ℤ))
    omega
  exact ⟨h1, h2, h3, h4, h5, hiszd0, hiszwp, h8, hiszp, h_isz3, h_isz70, h_isz8, h_isz1,
    h_isz0, hiszp, hiszps, hiszd0, hiszwp, hiszt3, hiszt70, hisztwp, hiszp1, hisztwc,
    hwple, hd0le, hpsle⟩

/-- Cost bound for one stage: `n ≤ 12` steps of budget `100000 KT (40(p+1)+1)`. -/
theorem stage_cost_le {n KT p K : ℕ} (hn : n ≤ 12) (hK : 49200000 * KT + 20 ≤ K) :
    n * (100000 * KT * (40 * (p + 1) + 1)) ≤ K * (p + 1) ^ K := by
  have h1 : 100000 * KT * (40 * (p + 1) + 1) ≤ 4100000 * KT * (p + 1) := by
    calc 100000 * KT * (40 * (p + 1) + 1) ≤ 100000 * KT * (41 * (p + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 4100000 * KT * (p + 1) := by ring
  have h2 : n * (100000 * KT * (40 * (p + 1) + 1)) ≤ 49200000 * KT * (p + 1) := by
    calc n * (100000 * KT * (40 * (p + 1) + 1)) ≤ n * (4100000 * KT * (p + 1)) :=
          Nat.mul_le_mul_left _ h1
      _ ≤ 12 * (4100000 * KT * (p + 1)) := Nat.mul_le_mul_right _ hn
      _ = 49200000 * KT * (p + 1) := by ring
  have h3 : 49200000 * KT * (p + 1) ≤ (49200000 * KT + 20) * (p + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have h4 : (49200000 * KT + 20) * (p + 1) ≤ K * (p + 1) ^ K := by
    have hpow : (p + 1) ^ 1 ≤ (p + 1) ^ K :=
      Nat.pow_le_pow_right (by omega : 0 < p + 1) (by omega)
    calc (49200000 * KT + 20) * (p + 1) = (49200000 * KT + 20) * (p + 1) ^ 1 := by rw [pow_one]
      _ ≤ K * (p + 1) ^ K := Nat.mul_le_mul hK hpow
  exact le_trans (le_trans h2 h3) h4

/-- Combine the four stage cost bounds into one. -/
theorem cost_combine (p K1 K2 K3 K4 : ℕ) (hp : 1 ≤ p) :
    K1 * (p + 1) ^ K1 + K2 * (p + 1) ^ K2 + K3 * (p + 1) ^ K3 + K4 * (p + 1) ^ K4
      ≤ (2 * (K1 + K2 + K3 + K4) + 8) * (p + 1) ^ (2 * (K1 + K2 + K3 + K4) + 8) := by
  have hp2 : 2 ≤ p + 1 := by omega
  have hle : ∀ K : ℕ, K ≤ (p + 1) ^ K := by
    intro K
    have h1 : K ≤ 2 ^ K := le_of_lt (Nat.lt_two_pow_self (n := K))
    exact le_trans h1 (Nat.pow_le_pow_left hp2 K)
  have hmain : ∀ K : ℕ, K ≤ K1 + K2 + K3 + K4 →
      K * (p + 1) ^ K ≤ (p + 1) ^ (2 * (K1 + K2 + K3 + K4) + 8) := by
    intro K hK
    calc K * (p + 1) ^ K = (p + 1) ^ K * K := by ring
      _ ≤ (p + 1) ^ K * (p + 1) ^ K := Nat.mul_le_mul_left _ (hle K)
      _ = (p + 1) ^ (K + K) := by rw [pow_add]
      _ ≤ (p + 1) ^ (2 * (K1 + K2 + K3 + K4) + 8) :=
          Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : 4 * (p + 1) ^ (2 * (K1 + K2 + K3 + K4) + 8)
      ≤ (2 * (K1 + K2 + K3 + K4) + 8) * (p + 1) ^ (2 * (K1 + K2 + K3 + K4) + 8) :=
    Nat.mul_le_mul_right _ (by omega)
  calc K1 * (p + 1) ^ K1 + K2 * (p + 1) ^ K2 + K3 * (p + 1) ^ K3 + K4 * (p + 1) ^ K4
      ≤ 4 * (p + 1) ^ (2 * (K1 + K2 + K3 + K4) + 8) := by
        have hs : K1 ≤ K1 + K2 + K3 + K4 := by omega
        have ht : K2 ≤ K1 + K2 + K3 + K4 := by omega
        have hu : K3 ≤ K1 + K2 + K3 + K4 := by omega
        have hv : K4 ≤ K1 + K2 + K3 + K4 := by omega
        linarith [hmain K1 hs, hmain K2 ht, hmain K3 hu, hmain K4 hv]
    _ ≤ _ := h4

/-- The size of the first `k+1` values of a window is at most `(k+1) * S`. -/
theorem map_sum_take_le {A rest : List Val} {k S : ℕ} (hk : k + 1 ≤ A.length)
    (h : ∀ v ∈ A, vsz v ≤ S) :
    ((((A ++ rest)).take (k + 1)).map vsz).sum ≤ (k + 1) * S := by
  rw [List.take_append_of_le_length hk]
  exact Work.Fx.ExpAsm.sum_take_le h k
theorem expPreludeStage1 (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ) (X Y : ℤ) (rest : List HvdH.Val),
      100 ≤ p → ((X : ℝ) ^ 2 + (Y : ℝ) ^ 2 ≤ (32 * 2 ^ p) ^ 2) →
      HvdH.WordR main prog
        (fun vs => vs = [Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ out => out = [Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest)
        (fun _ => K * (p + 1) ^ K) := by
  obtain ⟨pickP, Kpick, hpick⟩ := hk.pick
  obtain ⟨rollP, Kroll, hroll⟩ := hk.roll
  obtain ⟨swapP, Kswap, hswap⟩ := hk.swap
  obtain ⟨dropP, Kdrop, hdrop⟩ := hk.drop
  obtain ⟨pushP, Kpush, hpush⟩ := hk.pushVal
  obtain ⟨sizeP, Ksize, hsize⟩ := hi.size
  obtain ⟨mulsP, Kmuls, hmuls⟩ := hi.mulS
  obtain ⟨addP, Kadd, hadd⟩ := hi.add
  obtain ⟨shlP, Kshl, hshl⟩ := hi.shl
  obtain ⟨pow2P, Kpow2, hpow2⟩ := hi.pow2
  set KT : ℕ := Kpick + Kroll + Kswap + Kdrop + Kpush + Ksize + Kmuls + Kadd + Kshl + Kpow2 + 1
    with hKT
  have hKpick : Kpick ≤ KT := by rw [hKT]; omega
  have hKroll : Kroll ≤ KT := by rw [hKT]; omega
  have hKswap : Kswap ≤ KT := by rw [hKT]; omega
  have hKdrop : Kdrop ≤ KT := by rw [hKT]; omega
  have hKpush : Kpush ≤ KT := by rw [hKT]; omega
  have hKsize : Ksize ≤ KT := by rw [hKT]; omega
  have hKmuls : Kmuls ≤ KT := by rw [hKT]; omega
  have hKadd : Kadd ≤ KT := by rw [hKT]; omega
  have hKshl : Kshl ≤ KT := by rw [hKT]; omega
  have hKpow2 : Kpow2 ≤ KT := by rw [hKT]; omega
  refine ⟨List.foldl (fun a b => Cmd.seq a b) (pickP 0) [sizeP, pushP (Val.int (3 : ℤ)), mulsP, pushP (Val.int (70 : ℤ)), addP, pickP 1, pickP 1, addP, pow2P], 100000000 * KT + 20, ?_⟩
  intro main p X Y rest hp hR
  obtain ⟨hXb, hYb, hXsb, hYtb, hPowb, hDb, hWpb, hWcb, hpb, h_isz3, h_isz70, h_isz8,
    h_isz1, h_isz0, h_iszp, h_iszps, h_iszd0, h_iszwp, h_iszt3, h_iszt70, h_isztwp, h_iszp1,
    h_isztwc, hwple, hd0le, hpsle⟩ := prelude_isz_facts p X Y hp hR
  have s1 : HvdH.WordR main (pickP 0) (fun vs => vs = [Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ out => out = Val.int (p : ℤ) :: [Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_pick (hpick main) 0 ([Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (Val.int (p : ℤ)) rfl (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) ?_
    refine le_CB (x := Kpick * (0 + 1)) (y := (((([Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest).take (0 + 1)).map vsz).sum + 1))
      (by calc Kpick * (0 + 1) ≤ KT * 10 := Nat.mul_le_mul hKpick (by omega)
        _ ≤ 1000 * KT := by omega)
      (by have hb := map_sum_take_le (A := [Val.int (p : ℤ), Val.int X, Val.int Y]) (rest := rest) (k := 0) (S := 40 * (p + 1))
            (by simp only [List.length_cons, List.length_nil]; omega)
            (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl; all_goals (simp only [vsz_int]; omega))
          omega)
  have e1 := s1
  have s2 : HvdH.WordR main sizeP (fun vs => vs = Val.int (p : ℤ) :: [Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ out => out = Val.int ((p.size : ℕ) : ℤ) :: [Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_unOp (hsize main) (a := (p : ℤ)) (rest := [Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) trivial ?_
    refine le_CB (x := Ksize) (y := HvdH.isz (p : ℤ)) (by omega) (by omega)
  have e2 := w_seq2 e1 s2
  have s3 : HvdH.WordR main (pushP (Val.int (3 : ℤ))) (fun vs => vs = Val.int ((p.size : ℕ) : ℤ) :: [Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ out => out = Val.int (3 : ℤ) :: [Val.int ((p.size : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_pushVal (hpush main (Val.int (3 : ℤ))) (Val.int ((p.size : ℕ) : ℤ) :: [Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) ?_
    refine le_CB (x := Kpush) (y := vsz (Val.int (3 : ℤ)) + 1) (by omega) (by simp only [vsz_int]; omega)
  have e3 := w_seq2 e2 s3
  have s4 : HvdH.WordR main mulsP (fun vs => vs = Val.int (3 : ℤ) :: [Val.int ((p.size : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ out => out = Val.int (3 * ((p.size : ℕ) : ℤ)) :: [Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_binOp (hmuls main) (a := (3 : ℤ)) (b := ((p.size : ℕ) : ℤ)) (rest := [Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) trivial ?_
    refine le_CB (x := Kmuls * HvdH.isz (3 : ℤ)) (y := HvdH.isz ((p.size : ℕ) : ℤ))
      (by rw [h_isz3]; omega) (by omega)
  have e4 := w_seq2 e3 s4
  have s5 : HvdH.WordR main (pushP (Val.int (70 : ℤ))) (fun vs => vs = Val.int (3 * ((p.size : ℕ) : ℤ)) :: [Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ out => out = Val.int (70 : ℤ) :: [Val.int (3 * ((p.size : ℕ) : ℤ)), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_pushVal (hpush main (Val.int (70 : ℤ))) (Val.int (3 * ((p.size : ℕ) : ℤ)) :: [Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) ?_
    refine le_CB (x := Kpush) (y := vsz (Val.int (70 : ℤ)) + 1) (by omega) (by simp only [vsz_int]; omega)
  have e5 := w_seq2 e4 s5
  have s6 : HvdH.WordR main addP (fun vs => vs = Val.int (70 : ℤ) :: [Val.int (3 * ((p.size : ℕ) : ℤ)), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ out => out = Val.int (70 + 3 * ((p.size : ℕ) : ℤ)) :: [Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_binOp (hadd main) (a := (70 : ℤ)) (b := (3 * ((p.size : ℕ) : ℤ))) (rest := [Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) trivial ?_
    refine le_CB (x := Kadd) (y := HvdH.isz (70 : ℤ) + HvdH.isz (3 * ((p.size : ℕ) : ℤ))) (by omega) (by omega)
  have e6 := w_seq2 e5 s6
  have e7 := w_conv hk e6 rfl (by rw [show Val.int (70 + 3 * ((p.size : ℕ) : ℤ)) = Val.int ((d0 p : ℕ) : ℤ) by congr 1; simp only [d0]; push_cast; ring])
  have s8 : HvdH.WordR main (pickP 1) (fun vs => vs = [Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ out => out = Val.int (p : ℤ) :: [Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_pick (hpick main) 1 ([Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (Val.int (p : ℤ)) rfl (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) ?_
    refine le_CB (x := Kpick * (1 + 1)) (y := (((([Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest).take (1 + 1)).map vsz).sum + 1))
      (by calc Kpick * (1 + 1) ≤ KT * 10 := Nat.mul_le_mul hKpick (by omega)
        _ ≤ 1000 * KT := by omega)
      (by have hb := map_sum_take_le (A := [Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y]) (rest := rest) (k := 1) (S := 40 * (p + 1))
            (by simp only [List.length_cons, List.length_nil]; omega)
            (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl; all_goals (simp only [vsz_int]; omega))
          omega)
  have e8 := w_seq2 e7 s8
  have s9 : HvdH.WordR main (pickP 1) (fun vs => vs = [Val.int (p : ℤ), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ out => out = Val.int ((d0 p : ℕ) : ℤ) :: [Val.int (p : ℤ), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_pick (hpick main) 1 ([Val.int (p : ℤ), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (Val.int ((d0 p : ℕ) : ℤ)) rfl (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) ?_
    refine le_CB (x := Kpick * (1 + 1)) (y := (((([Val.int (p : ℤ), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest).take (1 + 1)).map vsz).sum + 1))
      (by calc Kpick * (1 + 1) ≤ KT * 10 := Nat.mul_le_mul hKpick (by omega)
        _ ≤ 1000 * KT := by omega)
      (by have hb := map_sum_take_le (A := [Val.int (p : ℤ), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y]) (rest := rest) (k := 1) (S := 40 * (p + 1))
            (by simp only [List.length_cons, List.length_nil]; omega)
            (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl | rfl; all_goals (simp only [vsz_int]; omega))
          omega)
  have e9 := w_seq2 e8 s9
  have s10 : HvdH.WordR main addP (fun vs => vs = Val.int ((d0 p : ℕ) : ℤ) :: [Val.int (p : ℤ), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ out => out = Val.int (((d0 p : ℕ) : ℤ) + (p : ℤ)) :: [Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_binOp (hadd main) (a := ((d0 p : ℕ) : ℤ)) (b := (p : ℤ)) (rest := [Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) trivial ?_
    refine le_CB (x := Kadd) (y := HvdH.isz ((d0 p : ℕ) : ℤ) + HvdH.isz (p : ℤ)) (by omega) (by omega)
  have e10 := w_seq2 e9 s10
  have e11 := w_conv hk e10 rfl (by rw [show Val.int (((d0 p : ℕ) : ℤ) + (p : ℤ)) = Val.int ((wprec p : ℕ) : ℤ) by congr 1; rw [wprec_eq, Nat.cast_add]; ring])
  have s12 : HvdH.WordR main pow2P (fun vs => vs = Val.int ((wprec p : ℕ) : ℤ) :: [Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ out => out = Val.int ((2 : ℤ) ^ wprec p) :: [Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_unOp (hpow2 main) (a := ((wprec p : ℕ) : ℤ)) (rest := [Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (by omega) ?_
    rw [Int.toNat_natCast]
    refine le_CB (x := Kpow2) (y := wprec p + HvdH.isz ((wprec p : ℕ) : ℤ)) (by omega) (by omega)
  have e12 := w_seq2 e11 s12
  refine wordR_conseq hk e12 (fun vs h => h) (fun vs out hvs hq => hq) ?_
  intro vs hvs
  refine le_trans (by omega) (stage_cost_le (n := 10) (KT := KT) (K := 100000000 * KT + 20) (by omega) (by omega))

theorem expPreludeStage2 (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ) (X Y : ℤ) (rest : List HvdH.Val),
      100 ≤ p → ((X : ℝ) ^ 2 + (Y : ℝ) ^ 2 ≤ (32 * 2 ^ p) ^ 2) →
      HvdH.WordR main prog
        (fun vs => vs = [Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ out => out = [Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest)
        (fun _ => K * (p + 1) ^ K) := by
  obtain ⟨pickP, Kpick, hpick⟩ := hk.pick
  obtain ⟨rollP, Kroll, hroll⟩ := hk.roll
  obtain ⟨swapP, Kswap, hswap⟩ := hk.swap
  obtain ⟨dropP, Kdrop, hdrop⟩ := hk.drop
  obtain ⟨pushP, Kpush, hpush⟩ := hk.pushVal
  obtain ⟨sizeP, Ksize, hsize⟩ := hi.size
  obtain ⟨mulsP, Kmuls, hmuls⟩ := hi.mulS
  obtain ⟨addP, Kadd, hadd⟩ := hi.add
  obtain ⟨shlP, Kshl, hshl⟩ := hi.shl
  obtain ⟨pow2P, Kpow2, hpow2⟩ := hi.pow2
  set KT : ℕ := Kpick + Kroll + Kswap + Kdrop + Kpush + Ksize + Kmuls + Kadd + Kshl + Kpow2 + 1
    with hKT
  have hKpick : Kpick ≤ KT := by rw [hKT]; omega
  have hKroll : Kroll ≤ KT := by rw [hKT]; omega
  have hKswap : Kswap ≤ KT := by rw [hKT]; omega
  have hKdrop : Kdrop ≤ KT := by rw [hKT]; omega
  have hKpush : Kpush ≤ KT := by rw [hKT]; omega
  have hKsize : Ksize ≤ KT := by rw [hKT]; omega
  have hKmuls : Kmuls ≤ KT := by rw [hKT]; omega
  have hKadd : Kadd ≤ KT := by rw [hKT]; omega
  have hKshl : Kshl ≤ KT := by rw [hKT]; omega
  have hKpow2 : Kpow2 ≤ KT := by rw [hKT]; omega
  refine ⟨List.foldl (fun a b => Cmd.seq a b) (pickP 4) [pickP 2, swapP, shlP, pickP 4, pickP 3, swapP, shlP], 100000000 * KT + 20, ?_⟩
  intro main p X Y rest hp hR
  obtain ⟨hXb, hYb, hXsb, hYtb, hPowb, hDb, hWpb, hWcb, hpb, h_isz3, h_isz70, h_isz8,
    h_isz1, h_isz0, h_iszp, h_iszps, h_iszd0, h_iszwp, h_iszt3, h_iszt70, h_isztwp, h_iszp1,
    h_isztwc, hwple, hd0le, hpsle⟩ := prelude_isz_facts p X Y hp hR
  have s1 : HvdH.WordR main (pickP 4) (fun vs => vs = [Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ out => out = Val.int Y :: [Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_pick (hpick main) 4 ([Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (Val.int Y) rfl (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) ?_
    refine le_CB (x := Kpick * (4 + 1)) (y := (((([Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest).take (4 + 1)).map vsz).sum + 1))
      (by calc Kpick * (4 + 1) ≤ KT * 10 := Nat.mul_le_mul hKpick (by omega)
        _ ≤ 1000 * KT := by omega)
      (by have hb := map_sum_take_le (A := [Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y]) (rest := rest) (k := 4) (S := 40 * (p + 1))
            (by simp only [List.length_cons, List.length_nil]; omega)
            (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl | rfl; all_goals (simp only [vsz_int]; omega))
          omega)
  have e1 := s1
  have s2 : HvdH.WordR main (pickP 2) (fun vs => vs = [Val.int Y, Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ out => out = Val.int ((d0 p : ℕ) : ℤ) :: [Val.int Y, Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_pick (hpick main) 2 ([Val.int Y, Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (Val.int ((d0 p : ℕ) : ℤ)) rfl (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) ?_
    refine le_CB (x := Kpick * (2 + 1)) (y := (((([Val.int Y, Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest).take (2 + 1)).map vsz).sum + 1))
      (by calc Kpick * (2 + 1) ≤ KT * 10 := Nat.mul_le_mul hKpick (by omega)
        _ ≤ 1000 * KT := by omega)
      (by have hb := map_sum_take_le (A := [Val.int Y, Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y]) (rest := rest) (k := 2) (S := 40 * (p + 1))
            (by simp only [List.length_cons, List.length_nil]; omega)
            (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl | rfl | rfl; all_goals (simp only [vsz_int]; omega))
          omega)
  have e2 := w_seq2 e1 s2
  have s3 : HvdH.WordR main swapP (fun vs => vs = Val.int ((d0 p : ℕ) : ℤ) :: [Val.int Y, Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ out => out = Val.int Y :: [Val.int ((d0 p : ℕ) : ℤ), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_swap (hswap main) (Val.int ((d0 p : ℕ) : ℤ)) (Val.int Y) ([Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) ?_
    refine le_CB (x := Kswap) (y := vsz (Val.int ((d0 p : ℕ) : ℤ)) + vsz (Val.int Y) + 1) (by omega) (by simp only [vsz_int]; omega)
  have e3 := w_seq2 e2 s3
  have s4 : HvdH.WordR main shlP (fun vs => vs = Val.int Y :: [Val.int ((d0 p : ℕ) : ℤ), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ out => out = Val.int (Y * (2 : ℤ) ^ d0 p) :: [Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_binOp (hshl main) (a := Y) (b := ((d0 p : ℕ) : ℤ)) (rest := [Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (by omega) ?_
    rw [Int.toNat_natCast]
    refine le_CB (x := Kshl) (y := HvdH.isz Y + d0 p + HvdH.isz ((d0 p : ℕ) : ℤ)) (by omega) (by omega)
  have e4 := w_seq2 e3 s4
  have s5 : HvdH.WordR main (pickP 4) (fun vs => vs = [Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ out => out = Val.int X :: [Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_pick (hpick main) 4 ([Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (Val.int X) rfl (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) ?_
    refine le_CB (x := Kpick * (4 + 1)) (y := (((([Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest).take (4 + 1)).map vsz).sum + 1))
      (by calc Kpick * (4 + 1) ≤ KT * 10 := Nat.mul_le_mul hKpick (by omega)
        _ ≤ 1000 * KT := by omega)
      (by have hb := map_sum_take_le (A := [Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y]) (rest := rest) (k := 4) (S := 40 * (p + 1))
            (by simp only [List.length_cons, List.length_nil]; omega)
            (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl | rfl | rfl; all_goals (simp only [vsz_int]; omega))
          omega)
  have e5 := w_seq2 e4 s5
  have s6 : HvdH.WordR main (pickP 3) (fun vs => vs = [Val.int X, Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ out => out = Val.int ((d0 p : ℕ) : ℤ) :: [Val.int X, Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_pick (hpick main) 3 ([Val.int X, Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (Val.int ((d0 p : ℕ) : ℤ)) rfl (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) ?_
    refine le_CB (x := Kpick * (3 + 1)) (y := (((([Val.int X, Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest).take (3 + 1)).map vsz).sum + 1))
      (by calc Kpick * (3 + 1) ≤ KT * 10 := Nat.mul_le_mul hKpick (by omega)
        _ ≤ 1000 * KT := by omega)
      (by have hb := map_sum_take_le (A := [Val.int X, Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y]) (rest := rest) (k := 3) (S := 40 * (p + 1))
            (by simp only [List.length_cons, List.length_nil]; omega)
            (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl; all_goals (simp only [vsz_int]; omega))
          omega)
  have e6 := w_seq2 e5 s6
  have s7 : HvdH.WordR main swapP (fun vs => vs = Val.int ((d0 p : ℕ) : ℤ) :: [Val.int X, Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ out => out = Val.int X :: [Val.int ((d0 p : ℕ) : ℤ), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_swap (hswap main) (Val.int ((d0 p : ℕ) : ℤ)) (Val.int X) ([Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) ?_
    refine le_CB (x := Kswap) (y := vsz (Val.int ((d0 p : ℕ) : ℤ)) + vsz (Val.int X) + 1) (by omega) (by simp only [vsz_int]; omega)
  have e7 := w_seq2 e6 s7
  have s8 : HvdH.WordR main shlP (fun vs => vs = Val.int X :: [Val.int ((d0 p : ℕ) : ℤ), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ out => out = Val.int (X * (2 : ℤ) ^ d0 p) :: [Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_binOp (hshl main) (a := X) (b := ((d0 p : ℕ) : ℤ)) (rest := [Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (by omega) ?_
    rw [Int.toNat_natCast]
    refine le_CB (x := Kshl) (y := HvdH.isz X + d0 p + HvdH.isz ((d0 p : ℕ) : ℤ)) (by omega) (by omega)
  have e8 := w_seq2 e7 s8
  refine wordR_conseq hk e8 (fun vs h => h) (fun vs out hvs hq => hq) ?_
  intro vs hvs
  refine le_trans (by omega) (stage_cost_le (n := 8) (KT := KT) (K := 100000000 * KT + 20) (by omega) (by omega))

theorem expPreludeStage3 (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ) (X Y : ℤ) (rest : List HvdH.Val),
      100 ≤ p → ((X : ℝ) ^ 2 + (Y : ℝ) ^ 2 ≤ (32 * 2 ^ p) ^ 2) →
      HvdH.WordR main prog
        (fun vs => vs = [Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ out => out = [Val.int ((2 : ℤ) ^ wprec p), Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest)
        (fun _ => K * (p + 1) ^ K) := by
  obtain ⟨pickP, Kpick, hpick⟩ := hk.pick
  obtain ⟨rollP, Kroll, hroll⟩ := hk.roll
  obtain ⟨swapP, Kswap, hswap⟩ := hk.swap
  obtain ⟨dropP, Kdrop, hdrop⟩ := hk.drop
  obtain ⟨pushP, Kpush, hpush⟩ := hk.pushVal
  obtain ⟨sizeP, Ksize, hsize⟩ := hi.size
  obtain ⟨mulsP, Kmuls, hmuls⟩ := hi.mulS
  obtain ⟨addP, Kadd, hadd⟩ := hi.add
  obtain ⟨shlP, Kshl, hshl⟩ := hi.shl
  obtain ⟨pow2P, Kpow2, hpow2⟩ := hi.pow2
  set KT : ℕ := Kpick + Kroll + Kswap + Kdrop + Kpush + Ksize + Kmuls + Kadd + Kshl + Kpow2 + 1
    with hKT
  have hKpick : Kpick ≤ KT := by rw [hKT]; omega
  have hKroll : Kroll ≤ KT := by rw [hKT]; omega
  have hKswap : Kswap ≤ KT := by rw [hKT]; omega
  have hKdrop : Kdrop ≤ KT := by rw [hKT]; omega
  have hKpush : Kpush ≤ KT := by rw [hKT]; omega
  have hKsize : Ksize ≤ KT := by rw [hKT]; omega
  have hKmuls : Kmuls ≤ KT := by rw [hKT]; omega
  have hKadd : Kadd ≤ KT := by rw [hKT]; omega
  have hKshl : Kshl ≤ KT := by rw [hKT]; omega
  have hKpow2 : Kpow2 ≤ KT := by rw [hKT]; omega
  refine ⟨List.foldl (fun a b => Cmd.seq a b) (pickP 4) [pushP (Val.int (1 : ℤ)), addP, pushP (Val.int (8 : ℤ)), mulsP, pushP (Val.int (0 : ℤ)), pickP 4], 100000000 * KT + 20, ?_⟩
  intro main p X Y rest hp hR
  obtain ⟨hXb, hYb, hXsb, hYtb, hPowb, hDb, hWpb, hWcb, hpb, h_isz3, h_isz70, h_isz8,
    h_isz1, h_isz0, h_iszp, h_iszps, h_iszd0, h_iszwp, h_iszt3, h_iszt70, h_isztwp, h_iszp1,
    h_isztwc, hwple, hd0le, hpsle⟩ := prelude_isz_facts p X Y hp hR
  have s1 : HvdH.WordR main (pickP 4) (fun vs => vs = [Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ out => out = Val.int (p : ℤ) :: [Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_pick (hpick main) 4 ([Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (Val.int (p : ℤ)) rfl (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) ?_
    refine le_CB (x := Kpick * (4 + 1)) (y := (((([Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest).take (4 + 1)).map vsz).sum + 1))
      (by calc Kpick * (4 + 1) ≤ KT * 10 := Nat.mul_le_mul hKpick (by omega)
        _ ≤ 1000 * KT := by omega)
      (by have hb := map_sum_take_le (A := [Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y]) (rest := rest) (k := 4) (S := 40 * (p + 1))
            (by simp only [List.length_cons, List.length_nil]; omega)
            (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl; all_goals (simp only [vsz_int]; omega))
          omega)
  have e1 := s1
  have s2 : HvdH.WordR main (pushP (Val.int (1 : ℤ))) (fun vs => vs = Val.int (p : ℤ) :: [Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ out => out = Val.int (1 : ℤ) :: [Val.int (p : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_pushVal (hpush main (Val.int (1 : ℤ))) (Val.int (p : ℤ) :: [Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) ?_
    refine le_CB (x := Kpush) (y := vsz (Val.int (1 : ℤ)) + 1) (by omega) (by simp only [vsz_int]; omega)
  have e2 := w_seq2 e1 s2
  have s3 : HvdH.WordR main addP (fun vs => vs = Val.int (1 : ℤ) :: [Val.int (p : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ out => out = Val.int ((1 : ℤ) + (p : ℤ)) :: [Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_binOp (hadd main) (a := (1 : ℤ)) (b := (p : ℤ)) (rest := [Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) trivial ?_
    refine le_CB (x := Kadd) (y := HvdH.isz (1 : ℤ) + HvdH.isz (p : ℤ)) (by omega) (by omega)
  have e3 := w_seq2 e2 s3
  have s4 : HvdH.WordR main (pushP (Val.int (8 : ℤ))) (fun vs => vs = Val.int ((1 : ℤ) + (p : ℤ)) :: [Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ out => out = Val.int (8 : ℤ) :: [Val.int ((1 : ℤ) + (p : ℤ)), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_pushVal (hpush main (Val.int (8 : ℤ))) (Val.int ((1 : ℤ) + (p : ℤ)) :: [Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) ?_
    refine le_CB (x := Kpush) (y := vsz (Val.int (8 : ℤ)) + 1) (by omega) (by simp only [vsz_int]; omega)
  have e4 := w_seq2 e3 s4
  have s5 : HvdH.WordR main mulsP (fun vs => vs = Val.int (8 : ℤ) :: [Val.int ((1 : ℤ) + (p : ℤ)), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ out => out = Val.int (8 * ((1 : ℤ) + (p : ℤ))) :: [Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_binOp (hmuls main) (a := (8 : ℤ)) (b := ((1 : ℤ) + (p : ℤ))) (rest := [Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) trivial ?_
    refine le_CB (x := Kmuls * HvdH.isz (8 : ℤ)) (y := HvdH.isz ((1 : ℤ) + (p : ℤ)))
      (by rw [h_isz8]; omega) (by omega)
  have e5 := w_seq2 e4 s5
  have e6 := w_conv hk e5 rfl (by rw [show Val.int (8 * ((1 : ℤ) + (p : ℤ))) = Val.int ((wcnt p : ℕ) : ℤ) by congr 1; rw [wcnt]; push_cast; ring])
  have s7 : HvdH.WordR main (pushP (Val.int (0 : ℤ))) (fun vs => vs = Val.int ((wcnt p : ℕ) : ℤ) :: [Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ out => out = Val.int (0 : ℤ) :: [Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_pushVal (hpush main (Val.int (0 : ℤ))) (Val.int ((wcnt p : ℕ) : ℤ) :: [Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) ?_
    refine le_CB (x := Kpush) (y := vsz (Val.int (0 : ℤ)) + 1) (by omega) (by simp only [vsz_int]; omega)
  have e7 := w_seq2 e6 s7
  have s8 : HvdH.WordR main (pickP 4) (fun vs => vs = [Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ out => out = Val.int ((2 : ℤ) ^ wprec p) :: [Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_pick (hpick main) 4 ([Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (Val.int ((2 : ℤ) ^ wprec p)) rfl (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) ?_
    refine le_CB (x := Kpick * (4 + 1)) (y := (((([Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest).take (4 + 1)).map vsz).sum + 1))
      (by calc Kpick * (4 + 1) ≤ KT * 10 := Nat.mul_le_mul hKpick (by omega)
        _ ≤ 1000 * KT := by omega)
      (by have hb := map_sum_take_le (A := [Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y]) (rest := rest) (k := 4) (S := 40 * (p + 1))
            (by simp only [List.length_cons, List.length_nil]; omega)
            (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl; all_goals (simp only [vsz_int]; omega))
          omega)
  have e8 := w_seq2 e7 s8
  refine wordR_conseq hk e8 (fun vs h => h) (fun vs out hvs hq => hq) ?_
  intro vs hvs
  refine le_trans (by omega) (stage_cost_le (n := 7) (KT := KT) (K := 100000000 * KT + 20) (by omega) (by omega))

theorem expPreludeStage4 (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ) (X Y : ℤ) (rest : List HvdH.Val),
      100 ≤ p → ((X : ℝ) ^ 2 + (Y : ℝ) ^ 2 ≤ (32 * 2 ^ p) ^ 2) →
      HvdH.WordR main prog
        (fun vs => vs = [Val.int ((2 : ℤ) ^ wprec p), Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ out => out = preA p X Y ++ rest)
        (fun _ => K * (p + 1) ^ K) := by
  obtain ⟨pickP, Kpick, hpick⟩ := hk.pick
  obtain ⟨rollP, Kroll, hroll⟩ := hk.roll
  obtain ⟨swapP, Kswap, hswap⟩ := hk.swap
  obtain ⟨dropP, Kdrop, hdrop⟩ := hk.drop
  obtain ⟨pushP, Kpush, hpush⟩ := hk.pushVal
  obtain ⟨sizeP, Ksize, hsize⟩ := hi.size
  obtain ⟨mulsP, Kmuls, hmuls⟩ := hi.mulS
  obtain ⟨addP, Kadd, hadd⟩ := hi.add
  obtain ⟨shlP, Kshl, hshl⟩ := hi.shl
  obtain ⟨pow2P, Kpow2, hpow2⟩ := hi.pow2
  set KT : ℕ := Kpick + Kroll + Kswap + Kdrop + Kpush + Ksize + Kmuls + Kadd + Kshl + Kpow2 + 1
    with hKT
  have hKpick : Kpick ≤ KT := by rw [hKT]; omega
  have hKroll : Kroll ≤ KT := by rw [hKT]; omega
  have hKswap : Kswap ≤ KT := by rw [hKT]; omega
  have hKdrop : Kdrop ≤ KT := by rw [hKT]; omega
  have hKpush : Kpush ≤ KT := by rw [hKT]; omega
  have hKsize : Ksize ≤ KT := by rw [hKT]; omega
  have hKmuls : Kmuls ≤ KT := by rw [hKT]; omega
  have hKadd : Kadd ≤ KT := by rw [hKT]; omega
  have hKshl : Kshl ≤ KT := by rw [hKT]; omega
  have hKpow2 : Kpow2 ≤ KT := by rw [hKT]; omega
  refine ⟨List.foldl (fun a b => Cmd.seq a b) (rollP 9) [dropP, rollP 8, dropP, rollP 7, dropP], 100000000 * KT + 20, ?_⟩
  intro main p X Y rest hp hR
  obtain ⟨hXb, hYb, hXsb, hYtb, hPowb, hDb, hWpb, hWcb, hpb, h_isz3, h_isz70, h_isz8,
    h_isz1, h_isz0, h_iszp, h_iszps, h_iszd0, h_iszwp, h_iszt3, h_iszt70, h_isztwp, h_iszp1,
    h_isztwc, hwple, hd0le, hpsle⟩ := prelude_isz_facts p X Y hp hR
  have s1 : HvdH.WordR main (rollP 9) (fun vs => vs = [Val.int ((2 : ℤ) ^ wprec p), Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (fun _ out => out = Val.int Y :: [Val.int ((2 : ℤ) ^ wprec p), Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_roll (hroll main) 9 ([Val.int ((2 : ℤ) ^ wprec p), Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) (Val.int Y) rfl (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) ?_
    refine le_CB (x := Kroll * (9 + 1)) (y := (((([Val.int ((2 : ℤ) ^ wprec p), Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest).take (9 + 1)).map vsz).sum + 1))
      (by calc Kroll * (9 + 1) ≤ KT * 10 := Nat.mul_le_mul hKroll (by omega)
        _ ≤ 1000 * KT := by omega)
      (by have hb := map_sum_take_le (A := [Val.int ((2 : ℤ) ^ wprec p), Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X, Val.int Y]) (rest := rest) (k := 9) (S := 40 * (p + 1))
            (by simp only [List.length_cons, List.length_nil]; omega)
            (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl; all_goals (simp only [vsz_int]; omega))
          omega)
  have e1 := s1
  have s2 : HvdH.WordR main dropP (fun vs => vs = Val.int Y :: [Val.int ((2 : ℤ) ^ wprec p), Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X] ++ rest) (fun _ out => out = [Val.int ((2 : ℤ) ^ wprec p), Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_drop (hdrop main) (Val.int Y) ([Val.int ((2 : ℤ) ^ wprec p), Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X] ++ rest) ?_
    refine le_CB (x := Kdrop) (y := vsz (Val.int Y) + 1) (by omega) (by simp only [vsz_int]; omega)
  have e2 := w_seq2 e1 s2
  have s3 : HvdH.WordR main (rollP 8) (fun vs => vs = [Val.int ((2 : ℤ) ^ wprec p), Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X] ++ rest) (fun _ out => out = Val.int X :: [Val.int ((2 : ℤ) ^ wprec p), Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ)] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_roll (hroll main) 8 ([Val.int ((2 : ℤ) ^ wprec p), Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X] ++ rest) (Val.int X) rfl (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) ?_
    refine le_CB (x := Kroll * (8 + 1)) (y := (((([Val.int ((2 : ℤ) ^ wprec p), Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X] ++ rest).take (8 + 1)).map vsz).sum + 1))
      (by calc Kroll * (8 + 1) ≤ KT * 10 := Nat.mul_le_mul hKroll (by omega)
        _ ≤ 1000 * KT := by omega)
      (by have hb := map_sum_take_le (A := [Val.int ((2 : ℤ) ^ wprec p), Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ), Val.int X]) (rest := rest) (k := 8) (S := 40 * (p + 1))
            (by simp only [List.length_cons, List.length_nil]; omega)
            (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl; all_goals (simp only [vsz_int]; omega))
          omega)
  have e3 := w_seq2 e2 s3
  have s4 : HvdH.WordR main dropP (fun vs => vs = Val.int X :: [Val.int ((2 : ℤ) ^ wprec p), Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ)] ++ rest) (fun _ out => out = [Val.int ((2 : ℤ) ^ wprec p), Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ)] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_drop (hdrop main) (Val.int X) ([Val.int ((2 : ℤ) ^ wprec p), Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ)] ++ rest) ?_
    refine le_CB (x := Kdrop) (y := vsz (Val.int X) + 1) (by omega) (by simp only [vsz_int]; omega)
  have e4 := w_seq2 e3 s4
  have s5 : HvdH.WordR main (rollP 7) (fun vs => vs = [Val.int ((2 : ℤ) ^ wprec p), Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ)] ++ rest) (fun _ out => out = Val.int (p : ℤ) :: [Val.int ((2 : ℤ) ^ wprec p), Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ)] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_roll (hroll main) 7 ([Val.int ((2 : ℤ) ^ wprec p), Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ)] ++ rest) (Val.int (p : ℤ)) rfl (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) ?_
    refine le_CB (x := Kroll * (7 + 1)) (y := (((([Val.int ((2 : ℤ) ^ wprec p), Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ)] ++ rest).take (7 + 1)).map vsz).sum + 1))
      (by calc Kroll * (7 + 1) ≤ KT * 10 := Nat.mul_le_mul hKroll (by omega)
        _ ≤ 1000 * KT := by omega)
      (by have hb := map_sum_take_le (A := [Val.int ((2 : ℤ) ^ wprec p), Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ), Val.int (p : ℤ)]) (rest := rest) (k := 7) (S := 40 * (p + 1))
            (by simp only [List.length_cons, List.length_nil]; omega)
            (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl; all_goals (simp only [vsz_int]; omega))
          omega)
  have e5 := w_seq2 e4 s5
  have s6 : HvdH.WordR main dropP (fun vs => vs = Val.int (p : ℤ) :: [Val.int ((2 : ℤ) ^ wprec p), Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ)] ++ rest) (fun _ out => out = [Val.int ((2 : ℤ) ^ wprec p), Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ)] ++ rest) (fun _ => 100000 * KT * (40 * (p + 1) + 1)) := by
    refine w_drop (hdrop main) (Val.int (p : ℤ)) ([Val.int ((2 : ℤ) ^ wprec p), Val.int (0 : ℤ), Val.int ((wcnt p : ℕ) : ℤ), Val.int (X * (2 : ℤ) ^ d0 p), Val.int (Y * (2 : ℤ) ^ d0 p), Val.int ((2 : ℤ) ^ wprec p), Val.int ((d0 p : ℕ) : ℤ)] ++ rest) ?_
    refine le_CB (x := Kdrop) (y := vsz (Val.int (p : ℤ)) + 1) (by omega) (by simp only [vsz_int]; omega)
  have e6 := w_seq2 e5 s6
  refine wordR_conseq hk e6 (fun vs h => h) (fun vs out hvs hq => hq) ?_
  intro vs hvs
  refine le_trans (by omega) (stage_cost_le (n := 6) (KT := KT) (K := 100000000 * KT + 20) (by omega) (by omega))

theorem expPreludeArrangeWord (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ) (X Y : ℤ) (rest : List HvdH.Val),
      100 ≤ p → ((X : ℝ) ^ 2 + (Y : ℝ) ^ 2 ≤ (32 * 2 ^ p) ^ 2) →
      HvdH.WordR main prog
        (fun vs => vs = [HvdH.Val.int (p : ℤ), HvdH.Val.int X, HvdH.Val.int Y] ++ rest)
        (fun _ out => out = preA p X Y ++ rest)
        (fun _ => K * (p + 1) ^ K) := by
  obtain ⟨pA, KA, hA⟩ := expPreludeStage1 hk hi
  obtain ⟨pB, KB, hB⟩ := expPreludeStage2 hk hi
  obtain ⟨pC, KC, hC⟩ := expPreludeStage3 hk hi
  obtain ⟨pD, KD, hD⟩ := expPreludeStage4 hk hi
  refine ⟨Cmd.seq (Cmd.seq (Cmd.seq pA pB) pC) pD, 2 * (KA + KB + KC + KD) + 8, ?_⟩
  intro main p X Y rest hp hR
  have e1 := hA main p X Y rest hp hR
  have e2 := hB main p X Y rest hp hR
  have e3 := hC main p X Y rest hp hR
  have e4 := hD main p X Y rest hp hR
  have f2 := w_seq2 e1 e2
  have f3 := w_seq2 f2 e3
  have f4 := w_seq2 f3 e4
  refine wordR_conseq hk f4 (fun vs h => h) (fun vs out hvs hq => hq) ?_
  intro vs hvs
  exact cost_combine p KA KB KC KD (by omega)

/-! ## The final cost bound -/

/-- The three pieces of the prelude cost add up to a single `K (p+1)^K`. -/
theorem prelude_cost_bound (p KA KS KL : ℕ) (hp : 100 ≤ p) :
    (KA * (p + 1) ^ KA + KS * (40 * (p + 1) + 1)) + KL * (wcnt p + 1) ^ KL
      ≤ (KA + KS + KL * 9 ^ KL + 6) * (p + 1) ^ (KA + KS + KL * 9 ^ KL + 6) := by
  set KF : ℕ := KA + KS + KL * 9 ^ KL + 6 with hKF
  have h1 : KA ≤ KF := by rw [hKF]; omega
  have h9p : 1 ≤ 9 ^ KL := Nat.one_le_pow KL 9 (by norm_num)
  have hKL9 : KL ≤ KL * 9 ^ KL := by
    calc KL = KL * 1 := (Nat.mul_one KL).symm
      _ ≤ KL * 9 ^ KL := Nat.mul_le_mul_left _ h9p
  have h3 : KL ≤ KF := by rw [hKF]; omega
  have h4 : 2 ≤ KF := by rw [hKF]; omega
  have h5 : KA + KS + KL * 9 ^ KL ≤ KF := by rw [hKF]; omega
  have hp1 : 1 ≤ p + 1 := by omega
  have hc1 : KA * (p + 1) ^ KA ≤ KA * (p + 1) ^ KF :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hp1 h1)
  have hc2 : KS * (40 * (p + 1) + 1) ≤ KS * (p + 1) ^ KF := by
    refine Nat.mul_le_mul_left _ ?_
    have h41 : 40 * (p + 1) + 1 ≤ 41 * (p + 1) := by omega
    have hmul : 41 * (p + 1) ≤ (p + 1) * (p + 1) := Nat.mul_le_mul_right _ (by omega)
    have hsq : (p + 1) * (p + 1) = (p + 1) ^ 2 := by ring
    exact le_trans (le_trans (le_trans h41 hmul) (le_of_eq hsq)) (Nat.pow_le_pow_right hp1 h4)
  have hc3 : KL * (wcnt p + 1) ^ KL ≤ KL * 9 ^ KL * (p + 1) ^ KF := by
    have hw : wcnt p + 1 ≤ 9 * (p + 1) := by simp only [wcnt]; omega
    have h9 : (wcnt p + 1) ^ KL ≤ (9 * (p + 1)) ^ KL := Nat.pow_le_pow_left hw KL
    have hm : (9 * (p + 1)) ^ KL = 9 ^ KL * (p + 1) ^ KL := Nat.mul_pow 9 (p + 1) KL
    calc KL * (wcnt p + 1) ^ KL ≤ KL * (9 * (p + 1)) ^ KL := Nat.mul_le_mul_left _ h9
      _ = KL * (9 ^ KL * (p + 1) ^ KL) := by rw [hm]
      _ = KL * 9 ^ KL * (p + 1) ^ KL := by ring
      _ ≤ KL * 9 ^ KL * (p + 1) ^ KF :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hp1 h3)
  calc (KA * (p + 1) ^ KA + KS * (40 * (p + 1) + 1)) + KL * (wcnt p + 1) ^ KL
      ≤ (KA * (p + 1) ^ KF + KS * (p + 1) ^ KF) + KL * 9 ^ KL * (p + 1) ^ KF :=
        add_le_add (add_le_add hc1 hc2) hc3
    _ = (KA + KS + KL * 9 ^ KL) * (p + 1) ^ KF := by ring
    _ ≤ KF * (p + 1) ^ KF := Nat.mul_le_mul_right _ h5
    _ = (KA + KS + KL * 9 ^ KL + 6) * (p + 1) ^ (KA + KS + KL * 9 ^ KL + 6) := by rw [hKF]

/-! ## The prelude -/

/-- Assembly: arrange window, setup moves, list loop. -/
theorem expPrelude_main (hk : HvdH.KernelLib) (hi : HvdH.IntLib)
    (hArr : ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ) (X Y : ℤ)
      (rest : List HvdH.Val),
      100 ≤ p → ((X : ℝ) ^ 2 + (Y : ℝ) ^ 2 ≤ (32 * 2 ^ p) ^ 2) →
      HvdH.WordR main prog
        (fun vs => vs = [HvdH.Val.int (p : ℤ), HvdH.Val.int X, HvdH.Val.int Y] ++ rest)
        (fun _ out => out = preA p X Y ++ rest) (fun _ => K * (p + 1) ^ K)) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ) (X Y : ℤ) (rest : List HvdH.Val),
      100 ≤ p → ((X : ℝ) ^ 2 + (Y : ℝ) ^ 2 ≤ (32 * 2 ^ p) ^ 2) →
      HvdH.WordR main prog
        (fun vs => vs = [HvdH.Val.int (p : ℤ), HvdH.Val.int X, HvdH.Val.int Y] ++ rest)
        (fun _ out => out = HvdH.ofList (List.replicate (wcnt p) (HvdH.Val.int 1)) ::
          HvdH.Val.int ((2 : ℤ) ^ wprec p) :: HvdH.Val.int 0 :: HvdH.Val.int (wcnt p) ::
          HvdH.Val.int (X * (2 : ℤ) ^ d0 p) :: HvdH.Val.int (Y * (2 : ℤ) ^ d0 p) ::
          HvdH.Val.int ((2 : ℤ) ^ wprec p) :: HvdH.Val.int (d0 p) :: rest)
        (fun _ => K * (p + 1) ^ K) := by
  obtain ⟨progA, KA, hA⟩ := hArr
  obtain ⟨progS, KS, hS⟩ := expPreludeSetup hk
  obtain ⟨progL, KL, hL⟩ := expPreludeList hk hi
  refine ⟨Cmd.seq (Cmd.seq progA progS) progL, KA + KS + KL * 9 ^ KL + 6, ?_⟩
  intro main p X Y rest hp hR
  have h1 := hA main p X Y rest hp hR
  have h2 := hS main (preA p X Y) rest (40 * (p + 1)) (by rw [preA_length]; norm_num)
    (preA_sizes p X Y hp hR)
  have h3 := hL main (wcnt p) (preA p X Y ++ rest)
  have h12 := w_seq2 h1 h2
  have h123 := w_seq2 h12 h3
  refine wordR_conseq hk h123 (fun vs h => h) (fun vs out h hq => hq) ?_
  intro vs hvs
  exact prelude_cost_bound p KA KS KL hp

theorem expPrelude (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ) (X Y : ℤ) (rest : List HvdH.Val),
      100 ≤ p → ((X : ℝ) ^ 2 + (Y : ℝ) ^ 2 ≤ (32 * 2 ^ p) ^ 2) →
      HvdH.WordR main prog
        (fun vs => vs = [HvdH.Val.int (p : ℤ), HvdH.Val.int X, HvdH.Val.int Y] ++ rest)
        (fun _ out => out = HvdH.ofList (List.replicate (wcnt p) (HvdH.Val.int 1)) ::
          HvdH.Val.int ((2 : ℤ) ^ wprec p) :: HvdH.Val.int 0 :: HvdH.Val.int (wcnt p) ::
          HvdH.Val.int (X * (2 : ℤ) ^ d0 p) :: HvdH.Val.int (Y * (2 : ℤ) ^ d0 p) ::
          HvdH.Val.int ((2 : ℤ) ^ wprec p) :: HvdH.Val.int (d0 p) :: rest)
        (fun _ => K * (p + 1) ^ K) :=
  expPrelude_main hk hi (expPreludeArrangeWord hk hi)

end Work.Fx

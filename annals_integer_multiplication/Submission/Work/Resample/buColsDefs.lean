import Mathlib
import Submission.Work.Resample.buKit
import Submission.Work.Resample.buQWhs

/-!
# `Work.Resample.buColsDefs`: the cost/size constants of the `buL10` column word

`Work.Resample.buColsWord` builds a word turning the parameter block `buCB p α s t` into
`buL10 p α s t :: buCB p α s t`, the list of the `2·egM p α` weight columns of the static table of
the one-dimensional `B̃` resampling.  The word is

* `buHsWord` (the shift list `zl (egHs (egM p α))`), then
* `KernelLib.mapList` with the per-column word `buColWord`,

so its cost is bounded by `Clabel + (2·egM p α)·(c + Kml·(L+1)) + Kml`.  This module fixes the
numbers appearing in that bookkeeping (`buLin`, `buLout`, `buColK`, `buColsK`) together with the
arithmetic helpers the two word-level proofs need.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-! ## The constants -/

/-- Uniform `vsz`-bound on the labels of one column, `cons (int ℓ) (int h)` (`ℓ < s`,
`|h| ≤ egM p α`), and on the produced weight values. -/
def buLin (p : ℕ) : ℕ := 2 * buSZ p + 4

/-- Uniform `vsz`-bound on a labelled column `cons (int h) (buCol p α s t h)`. -/
def buLout (p s : ℕ) : ℕ := (s + 1) * (buSZ p + 1) + buSZ p + 1

/-- The program constant of the per-column word. -/
def buColK (Kuc Kw Kml Krep Ken KP : ℕ) : ℕ :=
  1000 * (Kuc + Kw + Kml + Krep + Ken + KP + 2)

/-- The program constant of `Work.Resample.buColsWord`. -/
def buColsK (Kl Kc Kml Ke KAR Kuc Kcs : ℕ) : ℕ :=
  1000 * (Kl + Kc + Kml + Ke + KAR + Kuc + Kcs + 2)

/-- The program constant of `Work.Resample.buHsWord`. -/
def buHsK (KAR Kuc Kp Ksw Kdr Kpu Kad Kml Kr Ke : ℕ) : ℕ :=
  1000 * (KAR + Kuc + Kp + Ksw + Kdr + Kpu + Kad + Kml + Kr + Ke + 2)

/-- The program constant of the index-to-shift arithmetic word. -/
def buArithK (Kp Ksw Kpu Klt Ksu Kad : ℕ) : ℕ :=
  10000 * (Kp + Ksw + Kpu + Klt + Ksu + Kad + 2)

/-- The shift produced from the index `i < 2·egM p α`: `i - m + 1 - [i < m]`. -/
def buHidx (p α : ℕ) (i : ℤ) : ℤ :=
  (1 - (if i < (egM p α : ℤ) then 1 else 0)) + (i - (egM p α : ℤ))

/-! ## Elementary size facts -/

/-- `buSZ p + 1 ≤ (p+1)^4` for `p ≥ 100`. -/
theorem buSZ_add_one_le_four (p : ℕ) (hp : 100 ≤ p) : buSZ p + 1 ≤ (p + 1) ^ 4 := by
  have h100 : 100 * p ≤ p * p := Nat.mul_le_mul_right p hp
  have hsq : 10000 * (p * p) ≤ p ^ 4 := by
    have h := Nat.pow_le_pow_left h100 2
    nlinarith [h]
  have hlin : 6000 * p + 100001 ≤ 9920 * (p * p) := by nlinarith [h100, hp]
  have hexp : (p + 1) ^ 4 = p ^ 4 + 4 * p ^ 3 + 6 * (p * p) + 4 * p + 1 := by ring
  simp only [buSZ]
  nlinarith [hsq, hlin, hexp]

/-- `X ≤ (s+1)·X`. -/
theorem le_mul_succ (s X : ℕ) : X ≤ (s + 1) * X := by
  calc X = 1 * X := (one_mul X).symm
    _ ≤ (s + 1) * X := Nat.mul_le_mul_right X (by omega)

/-- `isz z ≤ buSZ p` for `|z| ≤ 2^p`. -/
theorem isz_le_buSZ_two_pow {z : ℤ} {p : ℕ} (hp : 100 ≤ p) (h : z.natAbs ≤ 2 ^ p) :
    isz z ≤ buSZ p :=
  isz_le_buSZ_of (p := p) (A := p) (by simp only [buSZ]; omega) h

/-- `isz n ≤ buSZ p` for `n < 2^p`. -/
theorem isz_nat_le_buSZ_two_pow {p n : ℕ} (hp : 100 ≤ p) (h : n < 2 ^ p) :
    isz ((n : ℤ)) ≤ buSZ p := by
  refine isz_le_buSZ_two_pow hp ?_
  rw [Int.natAbs_natCast]
  exact le_of_lt h

/-- `vsz (ofList l) ≤ (l.length + 1)(B+1)` when every entry has `vsz ≤ B`. -/
theorem buCol_vsz_ofList_le {l : List Val} {B : ℕ} (h : ∀ x ∈ l, vsz x ≤ B) :
    vsz (ofList l) ≤ (l.length + 1) * (B + 1) := by
  induction l with
  | nil => simp [ofList, vsz, Val.enc]
  | cons x t ih =>
    have hx : vsz x ≤ B := h x (by simp)
    have ht : ∀ y ∈ t, vsz y ≤ B := fun y hy => h y (by simp [hy])
    have ih' := ih ht
    have hcons : vsz (ofList (x :: t)) = vsz x + vsz (ofList t) + 1 := by
      show vsz (Val.cons x (ofList t)) = vsz x + vsz (ofList t) + 1
      simp [vsz, Val.enc]
    rw [hcons, List.length_cons]
    nlinarith [ih']

/-- `(List.range n).map g = List.ofFn g`. -/
theorem buCol_range_map_ofFn (n : ℕ) (g : ℕ → Val) :
    (List.range n).map g = List.ofFn (fun i : Fin n => g i) := by
  apply List.ext_getElem
  · simp
  · intro i _ _
    rw [List.getElem_map, List.getElem_range, List.getElem_ofFn]

/-- `vsz` of the parameter block. -/
theorem vsz_buCB_le {p α s t : ℕ} (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
    (htp : t < 2 ^ p) (hαp : α ^ 2 < p) {v : Val} (hv : v ∈ buCB p α s t) :
    vsz v ≤ buSZ p := by
  have hp1 : 1 ≤ p := by omega
  have hs0 : 0 < s := by omega
  have hsp : s < 2 ^ p := by omega
  have hα2p : α < 2 ^ p := by
    have h1 : α ≤ α * α := by nlinarith [hα]
    have h2 : α * α < 2 ^ p := by
      have h3 : α ^ 2 < 2 ^ p := lt_of_lt_of_le hαp (le_of_lt (Nat.lt_two_pow_self (n := p)))
      simpa [pow_two] using h3
    omega
  have hszp : isz ((p : ℤ)) ≤ buSZ p :=
    isz_nat_le_buSZ_two_pow hp (Nat.lt_two_pow_self (n := p))
  have hszα : isz ((α : ℤ)) ≤ buSZ p := isz_nat_le_buSZ_two_pow hp hα2p
  have hszs : isz ((s : ℤ)) ≤ buSZ p := isz_nat_le_buSZ_two_pow hp hsp
  have hszt : isz ((t : ℤ)) ≤ buSZ p := isz_nat_le_buSZ_two_pow hp htp
  have hszm : isz (((egM p α : ℕ) : ℤ)) ≤ buSZ p := isz_egM_le p α
  have hszn : isz (((egN p α s t : ℕ) : ℤ)) ≤ buSZ p := isz_egN_le p α s t hs0 hsp hp1
  have hszπ : isz (auPi p) ≤ buSZ p := isz_auPi_le_buSZ p
  simp only [buCB, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [Work.Fx.vsz_int] using hszp
  · simpa only [Work.Fx.vsz_int] using hszα
  · simpa only [Work.Fx.vsz_int] using hszs
  · simpa only [Work.Fx.vsz_int] using hszt
  · simpa only [Work.Fx.vsz_int] using hszm
  · simpa only [Work.Fx.vsz_int] using hszn
  · simpa only [Work.Fx.vsz_int] using hszπ

/-! ## Arithmetic helpers for the cost bookkeeping -/

/-- A numeral bound: `C ≤ (p+1)^d` for `p ≥ 100` whenever `C ≤ 101^d`. -/
theorem buCol_num_le {p C d : ℕ} (hp : 100 ≤ p) (h : C ≤ 101 ^ d) : C ≤ (p + 1) ^ d :=
  le_trans h (Nat.pow_le_pow_left (by omega : 101 ≤ p + 1) d)

/-- The two forms of `buHidx`. -/
theorem buHidx_eq (p α : ℕ) (i : ℤ) :
    buHidx p α i = i - (egM p α : ℤ) + 1 - (if i < (egM p α : ℤ) then 1 else 0) := by
  unfold buHidx
  by_cases h : i < (egM p α : ℤ)
  · rw [if_pos h]; ring
  · rw [if_neg h]; ring


/-- `C ≤ b^C` for `b ≥ 2`. -/
theorem le_pow_self (b C : ℕ) (hb : 2 ≤ b) : C ≤ b ^ C :=
  le_trans (le_of_lt (Nat.lt_two_pow_self (n := C))) (Nat.pow_le_pow_left hb C)

/-- `C · b^n ≤ b^(C+n)` for `b ≥ 2`. -/
theorem const_mul_pow_le_pow {C b n : ℕ} (hb : 2 ≤ b) : C * b ^ n ≤ b ^ (C + n) := by
  calc C * b ^ n ≤ b ^ C * b ^ n := Nat.mul_le_mul_right _ (le_pow_self b C hb)
    _ = b ^ (C + n) := by rw [← pow_add]

/-- `C · b^m ≤ b^e` when `C ≤ 2^c` and `c + m ≤ e`. -/
theorem buCol_mul_pow_le {C b c m e : ℕ} (hb : 2 ≤ b) (hC : C ≤ 2 ^ c) (h : c + m ≤ e) :
    C * b ^ m ≤ b ^ e := by
  calc C * b ^ m ≤ 2 ^ c * b ^ m := Nat.mul_le_mul_right _ hC
    _ ≤ b ^ c * b ^ m := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hb c)
    _ = b ^ (c + m) := by rw [← pow_add]
    _ ≤ b ^ e := Nat.pow_le_pow_right (by omega) h

/-- A polynomial-in-`p` bound: `D ≤ M(p+1)^2 ≤ (p+1)^50` for `M ≤ 2000000` (in particular
`D ≤ (p+1)^50`). -/
theorem buCol_poly_le2 {p D : ℕ} (hp : 100 ≤ p) (h : D ≤ 2000000 * (p + 1) ^ 2) :
    D ≤ (p + 1) ^ 50 := by
  have hM : (2000000 : ℕ) ≤ (p + 1) ^ 48 :=
    buCol_num_le hp (by norm_num)
  calc D ≤ 2000000 * (p + 1) ^ 2 := h
    _ ≤ (p + 1) ^ 48 * (p + 1) ^ 2 := Nat.mul_le_mul_right _ hM
    _ = (p + 1) ^ 50 := by rw [← pow_add]

/-- The per-step cost bound `Kc · D ≤ 8(s+1)(p+1)^Λ` for `D ≤ (s+1)(p+1)^50` and `Kc + 51 ≤ Λ`. -/
theorem buCol_step_le {p s Kc D Λ : ℕ} (hp : 100 ≤ p)
    (hD : D ≤ (s + 1) * (p + 1) ^ 50) (hK : Kc + 51 ≤ Λ) :
    Kc * D ≤ 8 * (s + 1) * (p + 1) ^ Λ := by
  have hb : 2 ≤ p + 1 := by omega
  have hKc : Kc ≤ (p + 1) ^ Kc :=
    le_trans (le_of_lt (Nat.lt_two_pow_self (n := Kc))) (Nat.pow_le_pow_left hb Kc)
  have h1 : (s + 1) * (p + 1) ^ (Kc + 50) ≤ (s + 1) * (p + 1) ^ (Λ - 1) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have h2 : (s + 1) * (p + 1) ^ (Λ - 1) ≤ (s + 1) * (p + 1) ^ Λ :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  calc Kc * D ≤ (p + 1) ^ Kc * D := Nat.mul_le_mul_right _ hKc
    _ ≤ (p + 1) ^ Kc * ((s + 1) * (p + 1) ^ 50) := Nat.mul_le_mul_left _ hD
    _ = (s + 1) * (p + 1) ^ (Kc + 50) := by rw [pow_add]; ring
    _ ≤ (s + 1) * (p + 1) ^ (Λ - 1) := h1
    _ ≤ (s + 1) * (p + 1) ^ Λ := h2
    _ ≤ 8 * (s + 1) * (p + 1) ^ Λ := by
        calc (s + 1) * (p + 1) ^ Λ = 1 * ((s + 1) * (p + 1) ^ Λ) := (Nat.one_mul _).symm
          _ ≤ 8 * ((s + 1) * (p + 1) ^ Λ) := Nat.mul_le_mul_right _ (by norm_num)
          _ = 8 * (s + 1) * (p + 1) ^ Λ := by ring


/-- The `vsz`-bound `buLout p s` of a labelled column, in the form needed by the cost arithmetic. -/
theorem buLout_succ_le (p s : ℕ) (hp : 100 ≤ p) (hs : 2 ≤ s) (N : ℕ) (hN : 4 ≤ N) :
    buLout p s + 1 ≤ 2 * ((s + 1) * (p + 1) ^ N) := by
  have hB : buSZ p + 1 ≤ (p + 1) ^ N :=
    le_trans (buSZ_add_one_le_four p hp) (Nat.pow_le_pow_right (by norm_num) hN)
  have h3 : buSZ p + 2 ≤ 3 * (buSZ p + 1) := by omega
  have h3' : 3 * (buSZ p + 1) ≤ (s + 1) * (buSZ p + 1) := Nat.mul_le_mul_right _ (by omega)
  have hB2 : buSZ p + 2 ≤ (s + 1) * (buSZ p + 1) := le_trans h3 h3'
  have hstep : buLout p s + 1 ≤ 2 * ((s + 1) * (buSZ p + 1)) := by
    simp only [buLout]
    omega
  calc buLout p s + 1 ≤ 2 * ((s + 1) * (buSZ p + 1)) := hstep
    _ ≤ 2 * ((s + 1) * (p + 1) ^ N) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left (s + 1) hB)

/-- `X ≤ M·(s+1)·(buSZ p + 1)` with `M ≤ 101^46` gives `X ≤ (s+1)(p+1)^50`. -/
theorem buCol_le_pow50 {p s M X : ℕ} (hp : 100 ≤ p) (h : X ≤ M * ((s + 1) * (buSZ p + 1)))
    (hM : M ≤ 101 ^ 46) : X ≤ (s + 1) * (p + 1) ^ 50 := by
  have hB : buSZ p + 1 ≤ (p + 1) ^ 4 := buSZ_add_one_le_four p hp
  have hM' : M ≤ (p + 1) ^ 46 := buCol_num_le hp hM
  calc X ≤ M * ((s + 1) * (buSZ p + 1)) := h
    _ ≤ M * ((s + 1) * (p + 1) ^ 4) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hB)
    _ ≤ (p + 1) ^ 46 * ((s + 1) * (p + 1) ^ 4) := Nat.mul_le_mul_right _ hM'
    _ = (s + 1) * ((p + 1) ^ 46 * (p + 1) ^ 4) := by ring
    _ = (s + 1) * (p + 1) ^ 50 := by rw [← pow_add]

/-- `Nat.size` is monotone. -/
theorem size_mono {a b : ℕ} (h : a ≤ b) : a.size ≤ b.size := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · rw [Nat.le_zero.mp (le_trans h (le_of_eq hb)), hb, Nat.size_zero]
  · exact Nat.size_le.mpr (lt_of_le_of_lt h (Nat.lt_size_self b))

/-- `(a+b).size ≤ a.size + b.size + 1`. -/
theorem size_add_le (a b : ℕ) : (a + b).size ≤ a.size + b.size + 1 := by
  have h1 : a < 2 ^ a.size := Nat.lt_size_self a
  have h2 : b < 2 ^ b.size := Nat.lt_size_self b
  have h3 : a + b < 2 ^ a.size + 2 ^ b.size := Nat.add_lt_add h1 h2
  have h4 : 2 ^ a.size + 2 ^ b.size ≤ 2 ^ (a.size + b.size + 1) := by
    have h5 : a.size ≤ a.size + b.size := Nat.le_add_right _ _
    have h6 : b.size ≤ a.size + b.size := Nat.le_add_left _ _
    calc 2 ^ a.size + 2 ^ b.size ≤ 2 ^ (a.size + b.size) + 2 ^ (a.size + b.size) :=
          Nat.add_le_add (Nat.pow_le_pow_right (by norm_num) h5) (Nat.pow_le_pow_right (by norm_num) h6)
      _ = 2 ^ (a.size + b.size + 1) := by rw [pow_succ]; ring
  exact Nat.size_le.mpr (lt_of_lt_of_le h3 h4)

/-- `isz (a-b) ≤ isz a + isz b`. -/
theorem isz_sub_le (a b : ℤ) : isz (a - b) ≤ isz a + isz b := by
  have h1 : (a - b).natAbs ≤ a.natAbs + b.natAbs := Int.natAbs_sub_le _ _
  have h2 : (a - b).natAbs.size ≤ a.natAbs.size + b.natAbs.size + 1 :=
    le_trans (size_mono h1) (size_add_le a.natAbs b.natAbs)
  simp only [isz]
  omega

/-- `isz (a+b) ≤ isz a + isz b`. -/
theorem isz_add_le_coord (a b : ℤ) : isz (a + b) ≤ isz a + isz b := by
  have h1 : (a + b).natAbs ≤ a.natAbs + b.natAbs := Int.natAbs_add_le _ _
  have h2 : (a + b).natAbs.size ≤ a.natAbs.size + b.natAbs.size + 1 :=
    le_trans (size_mono h1) (size_add_le a.natAbs b.natAbs)
  simp only [isz]
  omega

/-- `isz` of the `0/1` flag of `IL.lt`. -/
theorem isz_ltFlag_le (a b : ℤ) : isz (if a < b then (1:ℤ) else 0) ≤ 3 := by
  split
  · decide
  · decide

/-- A list of values of size `≤ N` has `szl` at most `length * N`. -/
theorem sum_map_vsz_le (l : List Val) : ∀ (N : ℕ), (∀ v ∈ l, vsz v ≤ N) →
    (l.map vsz).sum ≤ l.length * N := by
  induction l with
  | nil => intro N _; simp
  | cons a t ih =>
    intro N h
    have ha : vsz a ≤ N := h a (by simp)
    have ht : ∀ v ∈ t, vsz v ≤ N := fun v hv => h v (by simp [hv])
    have ih' := ih N ht
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [Nat.succ_mul]
    omega

theorem szl_le_length_mul' {l : List Val} {N : ℕ} (h : ∀ v ∈ l, vsz v ≤ N) :
    Work.Fx.szl l ≤ l.length * N := by
  have hh := sum_map_vsz_le l N h
  simpa only [Work.Fx.szl, List.length_map] using hh

/-- `vsz` of a list of integers. -/
theorem vsz_zl_le {l : List ℤ} {B : ℕ} (h : ∀ z ∈ l, isz z ≤ B) :
    vsz (zl l) ≤ (l.length + 1) * (B + 1) := by
  have h2 : ∀ x ∈ l.map Val.int, vsz x ≤ B := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    rw [Work.Fx.vsz_int]
    exact h z hz
  have h1 := buCol_vsz_ofList_le (l := l.map Val.int) (B := B) h2
  rw [List.length_map] at h1
  show vsz (ofList (List.map Val.int l)) ≤ (l.length + 1) * (B + 1)
  exact h1


/-- Three-factor product bound. -/
theorem mul_le_mul3 {a b c a' b' c' : ℕ} (h1 : a ≤ a') (h2 : b ≤ b') (h3 : c ≤ c') :
    a * b * c ≤ a' * b' * c' := by
  calc a * b * c = (a * b) * c := rfl
    _ ≤ (a' * b') * c' := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    _ = a' * b' * c' := by ring

/-- Four-factor product bound. -/
theorem mul_le_mul4 {a b c d a' b' c' d' : ℕ} (h1 : a ≤ a') (h2 : b ≤ b') (h3 : c ≤ c')
    (h4 : d ≤ d') : a * b * c * d ≤ a' * b' * c' * d' := by
  calc a * b * c * d = (a * b) * (c * d) := by ring
    _ ≤ (a' * b') * (c' * d') := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) (Nat.mul_le_mul h3 h4)
    _ = a' * b' * c' * d' := by ring

/-- `(p+1)^KK` is below `(m+1)(s+1)(p+1)^KK`. -/
theorem pow_le_prod (m s p KK : ℕ) :
    (p + 1) ^ KK ≤ (m + 1) * (s + 1) * (p + 1) ^ KK := by
  calc (p + 1) ^ KK ≤ (m + 1) * (p + 1) ^ KK := le_mul_succ m ((p + 1) ^ KK)
    _ ≤ (m + 1) * ((s + 1) * (p + 1) ^ KK) :=
        Nat.mul_le_mul_left _ (le_mul_succ s ((p + 1) ^ KK))
    _ = (m + 1) * (s + 1) * (p + 1) ^ KK := by ring

/-- `(m+1)(p+1)^KK` is below `(m+1)(s+1)(p+1)^KK`. -/
theorem prod_le_prod (m s p KK : ℕ) :
    (m + 1) * (p + 1) ^ KK ≤ (m + 1) * (s + 1) * (p + 1) ^ KK := by
  calc (m + 1) * (p + 1) ^ KK ≤ (m + 1) * ((s + 1) * (p + 1) ^ KK) :=
        Nat.mul_le_mul_left _ (le_mul_succ s ((p + 1) ^ KK))
    _ = (m + 1) * (s + 1) * (p + 1) ^ KK := by ring

/-- `(m+1)(s+1)(p+1)^KK` is positive. -/
theorem prod_pos (m s p KK : ℕ) : 0 < (m + 1) * (s + 1) * (p + 1) ^ KK := by
  have h1 : 0 < m + 1 := by omega
  have h2 : 0 < s + 1 := by omega
  have h3 : 0 < (p + 1) ^ KK := pow_pos (by omega) KK
  positivity


/-- Composition of two `WordR`s with exact pre/post windows. -/
theorem buCol_comp {main p q : Cmd} {A B D : List Val} {c1 c2 : ℕ}
    (h1 : WordR main p (fun vs => vs = A) (fun _ out => out = B) (fun _ => c1))
    (h2 : WordR main q (fun vs => vs = B) (fun _ out => out = D) (fun _ => c2)) :
    WordR main (.seq p q) (fun vs => vs = A) (fun _ out => out = D) (fun _ => c1 + c2) := by
  intro vs hvs s R hR
  obtain ⟨mid, s', n1, hmid, hev1, hn1, hstk1, hoth1⟩ := h1 vs hvs s R hR
  obtain ⟨out, s'', n2, hout, hev2, hn2, hstk2, hoth2⟩ := h2 mid hmid s' R hstk1
  exact ⟨out, s'', n1 + n2, hout, Eval.seq hev1 hev2, Nat.add_le_add hn1 hn2, hstk2,
    fun k hk => by rw [hoth2 k hk, hoth1 k hk]⟩


/-! ## Power bookkeeping and `2·egM` size bounds (for `Work.Resample.buHsWord`) -/

/-- `X * Y ≤ b^(d+e)` when `X ≤ b^d` and `Y ≤ b^e`. -/
theorem mul_le_pow_add {b X Y d e : ℕ} (h1 : X ≤ b ^ d) (h2 : Y ≤ b ^ e) :
    X * Y ≤ b ^ (d + e) := by
  calc X * Y ≤ b ^ d * b ^ e := Nat.mul_le_mul h1 h2
    _ = b ^ (d + e) := by rw [← pow_add]

/-- `X * Y * Z ≤ b^(d+e+f)`. -/
theorem mul3_le_pow_add {b X Y Z d e f : ℕ} (h1 : X ≤ b ^ d) (h2 : Y ≤ b ^ e)
    (h3 : Z ≤ b ^ f) : X * Y * Z ≤ b ^ (d + e + f) := by
  calc X * Y * Z ≤ (b ^ d * b ^ e) * b ^ f := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    _ = b ^ (d + e + f) := by rw [← pow_add, ← pow_add]

/-- `X + Y ≤ b^(d+2)` when `X ≤ b^d`, `Y ≤ b^d` and `2 ≤ b`. -/
theorem add_le_pow {b X Y d : ℕ} (hb : 2 ≤ b) (h1 : X ≤ b ^ d) (h2 : Y ≤ b ^ d) :
    X + Y ≤ b ^ (d + 2) := by
  have h2b : (2 : ℕ) ≤ b ^ 2 := by
    calc (2 : ℕ) ≤ b := hb
      _ = b ^ 1 := (pow_one b).symm
      _ ≤ b ^ 2 := Nat.pow_le_pow_right (by omega) (by omega)
  calc X + Y ≤ b ^ d + b ^ d := Nat.add_le_add h1 h2
    _ = 2 * b ^ d := by ring
    _ ≤ b ^ 2 * b ^ d := Nat.mul_le_mul_right _ h2b
    _ = b ^ (d + 2) := by rw [← pow_add, Nat.add_comm]

/-- `4^p = 2^(2p)`. -/
theorem four_pow_eq (p : ℕ) : 4 ^ p = 2 ^ (2 * p) := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]

/-- `2(p+1) ≤ 4^p` for `p ≥ 1`. -/
theorem two_mul_succ_le_four_pow {p : ℕ} (hp : 1 ≤ p) : 2 * (p + 1) ≤ 4 ^ p := by
  rw [four_pow_eq]
  have h1 : p + 1 ≤ 2 ^ p := by have := Nat.lt_two_pow_self (n := p); omega
  have h2 : 2 * (p + 1) ≤ (p + 1) * (p + 1) := by nlinarith
  have h3 : (p + 1) * (p + 1) ≤ 2 ^ p * 2 ^ p := Nat.mul_le_mul h1 h1
  have h4 : 2 ^ p * 2 ^ p = 2 ^ (2 * p) := by rw [← pow_add]; congr 1; ring
  linarith [h2, h3, h4]

/-- `2·egM p α ≤ 4^p` for `p ≥ 1`. -/
theorem two_egM_le_four_pow {p : ℕ} (α : ℕ) (hp : 1 ≤ p) : 2 * egM p α ≤ 4 ^ p :=
  le_trans (Nat.mul_le_mul_left 2 (egM_le p α)) (two_mul_succ_le_four_pow hp)

/-- `isz n ≤ buSZ p` when `n ≤ 4^p`. -/
theorem isz_nat_le_buSZ_four_pow {p n : ℕ} (hp : 100 ≤ p) (h : n ≤ 4 ^ p) :
    isz ((n : ℤ)) ≤ buSZ p :=
  isz_le_buSZ_of (p := p) (A := 2 * p) (by simp only [buSZ]; omega) (by
    rw [Int.natAbs_natCast, ← four_pow_eq]
    exact h)

/-- `isz (2·egM p α) ≤ buSZ p`. -/
theorem isz_two_egM_le (p α : ℕ) (hp : 100 ≤ p) : isz ((2 * egM p α : ℕ) : ℤ) ≤ buSZ p :=
  isz_nat_le_buSZ_four_pow hp (two_egM_le_four_pow α (by omega))

/-- `(2·egM p α).size ≤ 2p + 1` for `p ≥ 1`. -/
theorem size_two_egM_le (p α : ℕ) (hp : 1 ≤ p) : (2 * egM p α).size ≤ 2 * p + 1 := by
  have h1 : 2 * egM p α ≤ 4 ^ p := two_egM_le_four_pow α hp
  rw [four_pow_eq] at h1
  have h2 : 2 ^ (2 * p) < 2 ^ (2 * p + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  exact Nat.size_le.mpr (lt_of_le_of_lt h1 h2)

/-- `|(1 - [i<m]) + (i - m)| ≤ m` for `0 ≤ i < 2m`. -/
theorem natAbs_buHidx_le (p α : ℕ) {i : ℤ} (h0 : 0 ≤ i) (h2 : i < 2 * (egM p α : ℤ)) :
    (buHidx p α i).natAbs ≤ egM p α := by
  have hm : (0 : ℤ) ≤ (egM p α : ℤ) := by positivity
  have h1 : -(egM p α : ℤ) ≤ buHidx p α i := by
    unfold buHidx
    by_cases hc : i < (egM p α : ℤ)
    · rw [if_pos hc]; omega
    · rw [if_neg hc]; omega
  have h3 : buHidx p α i ≤ (egM p α : ℤ) := by
    unfold buHidx
    by_cases hc : i < (egM p α : ℤ)
    · rw [if_pos hc]; omega
    · rw [if_neg hc]; omega
  have h := natAbs_le_of (buHidx p α i) (egM p α : ℤ) hm h1 h3
  rwa [Int.natAbs_natCast] at h

/-- `isz (buHidx p α i) ≤ buSZ p` for `0 ≤ i < 2·egM p α`. -/
theorem isz_buHidx_le (p α : ℕ) (hp : 100 ≤ p) {i : ℤ} (h0 : 0 ≤ i)
    (h2 : i < 2 * (egM p α : ℤ)) : isz (buHidx p α i) ≤ buSZ p :=
  isz_le_buSZ_two_pow hp (le_trans (natAbs_buHidx_le p α h0 h2)
    (le_trans (egM_le p α) (by have h := Nat.lt_two_pow_self (n := p); omega)))


/-- `X + Y ≤ (s+1)·b^(d+2)` when `X ≤ (s+1)·b^d` and `Y ≤ (s+1)·b^d`. -/
theorem add_le_mul_pow {b X Y s d : ℕ} (hb : 2 ≤ b) (h1 : X ≤ (s + 1) * b ^ d)
    (h2 : Y ≤ (s + 1) * b ^ d) : X + Y ≤ (s + 1) * b ^ (d + 2) := by
  have hb2 : (2 : ℕ) ≤ b ^ 2 := by
    calc (2 : ℕ) ≤ b := hb
      _ = b ^ 1 := (pow_one b).symm
      _ ≤ b ^ 2 := Nat.pow_le_pow_right (by omega) (by omega)
  calc X + Y ≤ (s + 1) * b ^ d + (s + 1) * b ^ d := Nat.add_le_add h1 h2
    _ = 2 * ((s + 1) * b ^ d) := by ring
    _ ≤ b ^ 2 * ((s + 1) * b ^ d) := Nat.mul_le_mul_right _ hb2
    _ = (s + 1) * (b ^ 2 * b ^ d) := by ring
    _ = (s + 1) * (b ^ d * b ^ 2) := by ring
    _ = (s + 1) * b ^ (d + 2) := by rw [← pow_add]


end Work.Resample

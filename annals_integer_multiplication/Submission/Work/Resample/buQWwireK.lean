import Mathlib
import Submission.Work.Resample.buQWdefs
import Submission.Work.Resample.buQWtabS
import Submission.Work.Resample.buQWnloop
import Submission.Work.Resample.auCWFinal
import Submission.Work.Resample.buScInV
import Submission.Work.Resample.buSelLInV
import Submission.Work.Resample.buQWsel
import Submission.Work.Resample.buQWstepKit
import Submission.Work.Resample.buScSizeKit
import Submission.Work.Resample.buR1_vsz_buColsT
import Submission.Work.Resample.buCostK

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.Resample

open HvdH

/-! ## small helpers (copied locally so that this module has no extra dependencies) -/

theorem ofList_injK : ∀ {l l' : List Val}, ofList l = ofList l' → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [ofList] at h
  | _ :: _, [], h => by simp [ofList] at h
  | a :: t, a' :: t', h => by
      have h' : a = a' ∧ ofList t = ofList t' := by
        simpa [ofList, Val.cons.injEq] using h
      rw [h'.1, ofList_injK h'.2]

theorem cfxVal_injK {a b : ℤ × ℤ} (h : cfxVal a = cfxVal b) : a = b := by
  have h' : a.1 = b.1 ∧ a.2 = b.2 := by
    simpa [cfxVal, Val.cons.injEq, Val.int.injEq] using h
  exact Prod.ext h'.1 h'.2

theorem map_cfxVal_injK : ∀ (u u' : List (ℤ × ℤ)), u.map cfxVal = u'.map cfxVal → u = u'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: t, b :: t', h => by
      have h' : cfxVal a = cfxVal b ∧ t.map cfxVal = t'.map cfxVal := by
        simpa using h
      rw [cfxVal_injK h'.1, map_cfxVal_injK t t' h'.2]

theorem cvecVal_injK {u u' : List (ℤ × ℤ)} (h : cvecVal u = cvecVal u') : u = u' :=
  map_cfxVal_injK u u' (ofList_injK h)

theorem isz_natK (n : ℕ) : isz (n : ℤ) = n.size + 2 := by
  simp [isz, Int.natAbs_natCast]

theorem vsz_intNatK (n : ℕ) : vsz (Val.int (n : ℤ)) = n.size + 2 := by
  rw [Work.Fx.vsz_int, isz_natK]

theorem one_le_buSBK (p α t : ℕ) : 1 ≤ buSB p α t := by
  rw [buSB]
  have h : 0 < 1000000 * (t + 1) * (p + 4) * (Nat.sqrt p + 1) * (α + 1) := by positivity
  omega

/-- The program `[p₁, …, pₙ]` sequenced in order, with a trailing `skip`. -/
def buChainProgK (ps : List Cmd) : Cmd := ps.foldr Cmd.seq .skip

theorem buChainProgK_cons (p : Cmd) (ps : List Cmd) :
    buChainProgK (p :: ps) = .seq p (buChainProgK ps) := rfl

theorem Pipe.skipKK (KL : HvdH.KernelLib) {main : Cmd} {A : List Val} :
    Pipe main .skip A A 1 := by
  intro rest
  refine KL.conseq main .skip
    (fun _ => True) (fun vs => vs = A ++ rest) (fun vs out => out = vs)
    (fun _ out => out = A ++ rest)
    (fun _ => 1) (fun _ => 1) (KL.skip main) ?_ ?_ ?_
  · intro vs _
    trivial
  · intro vs out hvs hq
    rw [hq, hvs]
  · intro vs _
    exact le_rfl

/-! ## 1. Absorption of the elementary bounds into `buSB` -/

/-- `100 (t+1)(p+1) ≤ buSB p α t`. -/
theorem buTabSzKK_absorb (p α t : ℕ) :
    100 * (t + 1) * (p + 1) ≤ buSB p α t := by
  have h2 : 0 < Nat.sqrt p + 1 := by omega
  have h3 : 0 < α + 1 := by omega
  calc 100 * (t + 1) * (p + 1) ≤ 100 * (t + 1) * (p + 4) :=
        Nat.mul_le_mul_left _ (by omega : p + 1 ≤ p + 4)
    _ ≤ 100 * (t + 1) * (p + 4) * (Nat.sqrt p + 1) := Nat.le_mul_of_pos_right _ h2
    _ ≤ 100 * (t + 1) * (p + 4) * (Nat.sqrt p + 1) * (α + 1) := Nat.le_mul_of_pos_right _ h3
    _ ≤ 1000000 * (t + 1) * (p + 4) * (Nat.sqrt p + 1) * (α + 1) := by
        rw [show 100 * (t + 1) * (p + 4) * (Nat.sqrt p + 1) * (α + 1)
              = 100 * ((t + 1) * (p + 4) * (Nat.sqrt p + 1) * (α + 1)) from by ring,
            show 1000000 * (t + 1) * (p + 4) * (Nat.sqrt p + 1) * (α + 1)
              = 1000000 * ((t + 1) * (p + 4) * (Nat.sqrt p + 1) * (α + 1)) from by ring]
        exact Nat.mul_le_mul_right _ (by norm_num : 100 ≤ 1000000)
    _ = buSB p α t := rfl

/-- `buSB` also absorbs the larger window bound `400 (egM p α + 1)(t+1)(p+1)`. -/
theorem buTabSzKK_absorb_alpha (p α t : ℕ) (hα : 2 ≤ α) :
    400 * (egM p α + 1) * (t + 1) * (p + 1) ≤ buSB p α t := by
  have h4 : 4 * (egM p α + 1) ≤ Nat.sqrt p + 8 := by
    have hdiv : Nat.sqrt p / (2 * α) ≤ Nat.sqrt p / 4 :=
      Nat.div_le_div_left (show 4 ≤ 2 * α by omega) (by norm_num)
    have hmul : 4 * (Nat.sqrt p / 4) ≤ Nat.sqrt p := Nat.mul_div_le (Nat.sqrt p) 4
    simp only [egM]
    omega
  have h9 : Nat.sqrt p + 8 ≤ 8 * (Nat.sqrt p + 1) := by omega
  have h2 : 0 < α + 1 := by omega
  calc 400 * (egM p α + 1) * (t + 1) * (p + 1)
      = 100 * (4 * (egM p α + 1)) * (t + 1) * (p + 1) := by ring
    _ ≤ 100 * (Nat.sqrt p + 8) * (t + 1) * (p + 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h4))
    _ ≤ 100 * (8 * (Nat.sqrt p + 1)) * (t + 1) * (p + 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h9))
    _ = 800 * (Nat.sqrt p + 1) * (t + 1) * (p + 1) := by ring
    _ ≤ 800 * (Nat.sqrt p + 1) * (t + 1) * (p + 4) :=
        Nat.mul_le_mul_left _ (by omega : p + 1 ≤ p + 4)
    _ ≤ 800 * (Nat.sqrt p + 1) * (t + 1) * (p + 4) * (α + 1) := Nat.le_mul_of_pos_right _ h2
    _ ≤ 1000000 * (t + 1) * (p + 4) * (Nat.sqrt p + 1) * (α + 1) := by
        rw [show 800 * (Nat.sqrt p + 1) * (t + 1) * (p + 4) * (α + 1)
              = 800 * ((Nat.sqrt p + 1) * (t + 1) * (p + 4) * (α + 1)) from by ring,
            show 1000000 * (t + 1) * (p + 4) * (Nat.sqrt p + 1) * (α + 1)
              = 1000000 * ((Nat.sqrt p + 1) * (t + 1) * (p + 4) * (α + 1)) from by ring]
        exact Nat.mul_le_mul_right _ (by norm_num : 800 ≤ 1000000)
    _ = buSB p α t := rfl

/-- `(s+1)(3p+13) ≤ 100 (t+1)(p+1)` for `s ≤ t`: the common shape of the list bounds. -/
theorem buTabSzKK_absorb_scale (s t p : ℕ) (h : s ≤ t) :
    (s + 1) * (3 * p + 13) ≤ 100 * (t + 1) * (p + 1) := by
  have hsle : s + 1 ≤ t + 1 := by omega
  calc (s + 1) * (3 * p + 13) ≤ (t + 1) * (3 * p + 13) := Nat.mul_le_mul_right _ hsle
    _ ≤ (t + 1) * (16 * (p + 1)) := Nat.mul_le_mul_left _ (by omega)
    _ = 16 * (t + 1) * (p + 1) := by ring
    _ ≤ 100 * (t + 1) * (p + 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num : 16 ≤ 100))

/-- `4 p + 2 ≤ 100 (t+1)(p+1)`. -/
theorem buTabSzKK_scale_pt (p t : ℕ) : 4 * p + 2 ≤ 100 * (t + 1) * (p + 1) := by
  have h1 : (1 : ℕ) ≤ t + 1 := by omega
  calc 4 * p + 2 ≤ 100 * (p + 1) := by omega
    _ = 100 * 1 * (p + 1) := by ring
    _ ≤ 100 * (t + 1) * (p + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)

/-! ## 2. The scalar entries -/

/-- A natural below `2^(p+1)` gives a `Val.int` of size `≤ 100 (t+1)(p+1)`. -/
theorem buTabSzKK_intNat_le (n p t : ℕ) (h : n < 2 ^ (p + 1)) :
    vsz (Val.int (n : ℤ)) ≤ 100 * (t + 1) * (p + 1) := by
  rw [vsz_intNatK]
  have h1 : n.size ≤ p + 1 := Nat.size_le.mpr h
  have h2 : n.size + 2 ≤ 100 * (p + 1) := by omega
  have h4 : (1 : ℕ) ≤ t + 1 := by omega
  have h3 : 100 * (p + 1) ≤ 100 * (t + 1) * (p + 1) := by
    calc 100 * (p + 1) = 100 * 1 * (p + 1) := by ring
      _ ≤ 100 * (t + 1) * (p + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h4)
  exact le_trans h2 h3

/-- `n ≤ p+1` implies `n < 2^(p+1)`. -/
theorem buTabSzKK_lt_succ {n p : ℕ} (h : n ≤ p + 1) : n < 2 ^ (p + 1) :=
  lt_of_le_of_lt h (Nat.lt_two_pow_self (n := p + 1))

/-- `n < 2^p` implies `n < 2^(p+1)`. -/
theorem buTabSzKK_lt_of_lt {n p : ℕ} (h : n < 2 ^ p) : n < 2 ^ (p + 1) :=
  lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ p))

/-- The generic scalar entry bound. -/
theorem buTabSzKK_scalar (n p α t : ℕ) (h : n < 2 ^ (p + 1)) :
    vsz (Val.int (n : ℤ)) ≤ buSB p α t :=
  le_trans (buTabSzKK_intNat_le n p t h) (buTabSzKK_absorb p α t)

/-! ## 3. The four list-valued entries -/

theorem buTabSzKK_keysT (p α s t : ℕ) (hst : s < t) (htp : t < 2 ^ p) :
    vsz (buKeysT s t) ≤ buSB p α t := by
  have h1 := vsz_buKeysT_le (s := s) (t := t) (p := p) hst htp
  have h2 : buSL p + 1 = 3 * p + 13 := by simp only [buSL]
  rw [h2] at h1
  exact le_trans (le_trans h1 (buTabSzKK_absorb_scale t t p le_rfl)) (buTabSzKK_absorb p α t)

theorem buTabSzKK_keysS (p α s t : ℕ) (hst : s < t) (htp : t < 2 ^ p) :
    vsz (buKeysS s t) ≤ buSB p α t := by
  have h1 := buScVsz_buKeysS p s t hst htp
  have h2 : buScB p + 1 = 3 * p + 13 := by simp only [buScB]
  rw [h2] at h1
  exact le_trans (le_trans h1 (buTabSzKK_absorb_scale s t p (le_of_lt hst))) (buTabSzKK_absorb p α t)

theorem buTabSzKK_wdL (p α s t : ℕ) (hst : s < t)
    (hwd : ∀ ℓ : ℤ, 8 * (buWd p α s t ℓ).natAbs ≤ 3 * 2 ^ p) :
    vsz (buWdL p α s t) ≤ buSB p α t := by
  have h1 := buScVsz_buWdL p α s t hwd
  have h2 : buScB p + 1 = 3 * p + 13 := by simp only [buScB]
  rw [h2] at h1
  exact le_trans (le_trans h1 (buTabSzKK_absorb_scale s t p (le_of_lt hst))) (buTabSzKK_absorb p α t)

theorem buTabSzKK_colsT (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hp : 100 ≤ p) (hα : 2 ≤ α)
    (hrow : ∀ ℓ : ℤ, ∑ h ∈ egHset (egM p α),
      |(buWt p α s t ℓ h : ℝ)| ≤ (2 : ℝ) ^ p / 2 + 8 * (egM p α : ℝ)) :
    vsz (buColsT p α s t) ≤ buSB p α t := by
  have hwt : ∀ (ℓ h : ℤ), h ∈ egHset (egM p α) → isz (buWt p α s t ℓ h) ≤ p + 3 :=
    fun ℓ h hh => buQT_buWt_isz_le p α s t hα hp hrow ℓ h hh
  have h1 := (buR1_vsz_buColsT p α s t hs hp hwt).2
  have hsle : s + 1 ≤ t + 1 := by omega
  have h2 : 20 * (egM p α + 1) * (s + 1) * (p + 1)
      ≤ 400 * (egM p α + 1) * (t + 1) * (p + 1) := by
    calc 20 * (egM p α + 1) * (s + 1) * (p + 1)
        = 20 * ((egM p α + 1) * (s + 1) * (p + 1)) := by ring
      _ ≤ 400 * ((egM p α + 1) * (s + 1) * (p + 1)) :=
            Nat.mul_le_mul_right _ (by norm_num : 20 ≤ 400)
      _ ≤ 400 * ((egM p α + 1) * (t + 1) * (p + 1)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hsle))
      _ = 400 * (egM p α + 1) * (t + 1) * (p + 1) := by ring
  exact le_trans (le_trans h1 h2) (buTabSzKK_absorb_alpha p α t hα)

theorem buTabSzKK_signsT (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
    (hαp : α ^ 2 < p)
    (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1) :
    vsz (buSignsT p α s t) ≤ buSB p α t := by
  have heN : egN p α s t ≤ p := by
    have h1 := buQWnloop_egN_le p α s t hs hst hα hp hθ
    have h2 : α ^ 2 + 1 ≤ p := by omega
    omega
  have hmain : vsz (buSignsT p α s t) ≤ 100 * (t + 1) * (p + 1) := by
    unfold buSignsT
    rw [buQT_vsz_zl]
    have hsum : (((List.range (egN p α s t - 1)).map
        (fun j => (-1 : ℤ) ^ (j + 1))).map isz).sum ≤ (egN p α s t - 1) * 3 := by
      have hlen : (((List.range (egN p α s t - 1)).map
          (fun j => (-1 : ℤ) ^ (j + 1))).map isz).length = egN p α s t - 1 := by simp
      have h := buQT_sum_le_length_mul
        (l := ((List.range (egN p α s t - 1)).map (fun j => (-1 : ℤ) ^ (j + 1))).map isz)
        (M := 3) (fun x hx => by
          obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
          obtain ⟨j, -, rfl⟩ := List.mem_map.mp hz
          have hp1 : ((-1 : ℤ) ^ (j + 1)).natAbs = 1 := by
            rcases Nat.even_or_odd (j + 1) with h | h
            · rw [Even.neg_one_pow h]; rfl
            · rw [Odd.neg_one_pow h]; rfl
          rw [HvdH.isz, hp1]
          norm_num)
      rwa [hlen] at h
    rw [List.length_map, List.length_range]
    have hbig : 4 * p + 2 ≤ 100 * (t + 1) * (p + 1) := buTabSzKK_scale_pt p t
    omega
  exact le_trans hmain (buTabSzKK_absorb p α t)

/-! ## 4. The target -/

/-- **Size of every entry of the static table `buTabList p α s t` of the `B̃` wire.**

`buTabList p α s t hs hcop = [int p, int α, int s, int t, int egM, int egN, buKeysT,
buKeysS, buWdL, buColsT, buSignsT]` (`Work.Resample.buTabList_eq`, `rfl`; the body of `buTabList`
does not depend on the two proof arguments), and each of the eleven entries is separately bounded
by `buSB p α t`: the six `Val.int` entries through `Work.Resample.vsz_intNatK` and
`n < 2^(p+1)` (the round count `egN p α s t` is `≤ α²+1 ≤ p` by `Work.Resample.buQWnloop_egN_le`),
the list-valued entries through `Work.Resample.vsz_buKeysT_le`, `Work.Resample.buScVsz_buKeysS`,
`Work.Resample.buScVsz_buWdL`, `Work.Resample.buR1_vsz_buColsT` (with the row-sum bound
`hrow` and `Work.Resample.buQT_buWt_isz_le`) and the `±1`-sign list `buSignsT`.  The elementary
estimates absorb into `buSB p α t = 10^6 (t+1)(p+4)(√p+1)(α+1)`. -/
theorem buTabSzKK (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t)
    (htp : t < 2 ^ p) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
    (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1)
    (hrow : ∀ ℓ : ℤ, ∑ h ∈ Work.Resample.egHset (Work.Resample.egM p α),
      |(Work.Resample.buWt p α s t ℓ h : ℝ)| ≤ (2 : ℝ) ^ p / 2 + 8 * (Work.Resample.egM p α : ℝ))
    (hwd : ∀ ℓ : ℤ, 8 * (Work.Resample.buWd p α s t ℓ).natAbs ≤ 3 * 2 ^ p) :
    ∀ v ∈ Work.Resample.buTabList p α s t (by omega) hcop.symm,
      HvdH.vsz v ≤ Work.Resample.buSB p α t := by
  have hαle : α ≤ p := by
    have h1 : α ≤ α ^ 2 := by
      calc α = α * 1 := by ring
        _ ≤ α * α := Nat.mul_le_mul_left α (by omega)
        _ = α ^ 2 := by ring
    exact le_trans h1 (le_of_lt hαp)
  have heN : egN p α s t ≤ p := by
    have h1 := buQWnloop_egN_le p α s t hs hst hα hp hθ
    have h2 : α ^ 2 + 1 ≤ p := by omega
    omega
  have heM : egM p α ≤ p + 1 := buR1_egM_le p α
  have hkT := buTabSzKK_keysT p α s t hst htp
  have hkS := buTabSzKK_keysS p α s t hst htp
  have hwL := buTabSzKK_wdL p α s t hst hwd
  have hcol := buTabSzKK_colsT p α s t hs hst hp hα hrow
  have hsign := buTabSzKK_signsT p α s t hs hst hα hp hαp hθ
  intro v hv
  rw [buTabList_eq p α s t (by omega) hcop.symm] at hv
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact buTabSzKK_scalar p p α t (buTabSzKK_lt_succ (Nat.le_succ p))
  · exact buTabSzKK_scalar α p α t (buTabSzKK_lt_succ (le_trans hαle (Nat.le_succ p)))
  · exact buTabSzKK_scalar s p α t (buTabSzKK_lt_of_lt (lt_trans hst htp))
  · exact buTabSzKK_scalar t p α t (buTabSzKK_lt_of_lt htp)
  · exact buTabSzKK_scalar (egM p α) p α t (buTabSzKK_lt_succ heM)
  · exact buTabSzKK_scalar (egN p α s t) p α t (buTabSzKK_lt_succ (le_trans heN (Nat.le_succ p)))
  · exact hkT
  · exact hkS
  · exact hwL
  · exact hcol
  · exact hsign


/-! ## the static table as an explicit list -/

/-- The eleven entries of the static table of the `B̃` wire, as an explicit list. -/
noncomputable def buTK (p α s t : ℕ) : List Val :=
  [Val.int (p : ℤ), Val.int (α : ℤ), Val.int (s : ℤ), Val.int (t : ℤ),
   Val.int ((egM p α : ℕ) : ℤ), Val.int ((egN p α s t : ℕ) : ℤ),
   buKeysT s t, buKeysS s t, buWdL p α s t, buColsT p α s t, buSignsT p α s t]

theorem buTabList_eq_buTK (p α s t : ℕ) (hs : 0 < s) (hcop : Nat.Coprime t s) :
    buTabList p α s t hs hcop = buTK p α s t := rfl

theorem mem_buTK_int_p (p α s t : ℕ) : Val.int (p : ℤ) ∈ buTK p α s t := by
  unfold buTK; simp
theorem mem_buTK_int_s (p α s t : ℕ) : Val.int (s : ℤ) ∈ buTK p α s t := by
  unfold buTK; simp
theorem mem_buTK_keysT (p α s t : ℕ) : buKeysT s t ∈ buTK p α s t := by
  unfold buTK; simp
theorem mem_buTK_keysS (p α s t : ℕ) : buKeysS s t ∈ buTK p α s t := by
  unfold buTK; simp
theorem mem_buTK_wdL (p α s t : ℕ) : buWdL p α s t ∈ buTK p α s t := by
  unfold buTK; simp
theorem mem_buTK_colsT (p α s t : ℕ) : buColsT p α s t ∈ buTK p α s t := by
  unfold buTK; simp
theorem mem_buTK_signsT (p α s t : ℕ) : buSignsT p α s t ∈ buTK p α s t := by
  unfold buTK; simp

/-! ## list-size helpers -/

theorem vsz_all_cons {SEL : ℕ} {a : Val} {A : List Val} (ha : vsz a ≤ SEL)
    (hA : ∀ v ∈ A, vsz v ≤ SEL) : ∀ v ∈ a :: A, vsz v ≤ SEL := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact ha
  · exact hA v hv

theorem le_mul_of_one_le (a b : ℕ) (h : 1 ≤ b) : a ≤ a * b := by
  calc a = a * 1 := (Nat.mul_one a).symm
    _ ≤ a * b := Nat.mul_le_mul_left a h

/-- Every work vector of the `B̃` wire has encoding size at most `buSB p α t`. -/
theorem buVecSz (p α t B : ℕ) {v : List (ℤ × ℤ)} (hvt : v.length ≤ t) (hB : B ≤ 2 ^ (p + 1))
    (hv : buInV B v) : vsz (cvecVal v) ≤ buSB p α t := by
  have h1 : buInV (2 ^ (p + 1)) v := fun z hz => buIn_mono hB (hv z hz)
  have h2 := vsz_cvecVal_le (p := p + 1) h1
  rw [buSB]
  have h3 : buSL (p + 1) + 1 ≤ 1000000 * (p + 4) := by simp only [buSL]; omega
  have h4 : v.length + 1 ≤ t + 1 := by omega
  calc vsz (cvecVal v) ≤ (v.length + 1) * (buSL (p + 1) + 1) := h2
    _ ≤ (t + 1) * (buSL (p + 1) + 1) := Nat.mul_le_mul_right _ h4
    _ ≤ (t + 1) * (1000000 * (p + 4)) := Nat.mul_le_mul_left _ h3
    _ = 1000000 * (t + 1) * (p + 4) := by ring
    _ ≤ 1000000 * (t + 1) * (p + 4) * (Nat.sqrt p + 1) := le_mul_of_one_le _ _ (by omega)
    _ ≤ 1000000 * (t + 1) * (p + 4) * (Nat.sqrt p + 1) * (α + 1) :=
        le_mul_of_one_le _ _ (by omega)

/-! ## `Pipe` cost helpers -/

theorem szl_take_le_n {A : List Val} {SEL : ℕ} (h : ∀ v ∈ A, vsz v ≤ SEL) (k : ℕ) :
    Work.Fx.szl (A.take (k + 1)) ≤ (k + 1) * SEL := by
  have h1 : Work.Fx.szl (A.take (k + 1)) ≤ (A.take (k + 1)).length * SEL :=
    szl_le_len_mul (fun v hv => h v (List.mem_of_mem_take hv))
  have h2 : (A.take (k + 1)).length ≤ k + 1 := by rw [List.length_take]; omega
  exact le_trans h1 (Nat.mul_le_mul_right _ h2)

theorem le_step_mover20 {K KS SEL : ℕ} (hK : K ≤ KS) (k : ℕ) (hk : k ≤ 19) {A : List Val}
    (hsz : Work.Fx.szl (A.take (k + 1)) ≤ (k + 1) * SEL) (hSEL : 1 ≤ SEL) :
    K * (k + 1) * (Work.Fx.szl (A.take (k + 1)) + 1) ≤ 1000 * KS * SEL := by
  have h1 : K * (k + 1) ≤ KS * 20 := Nat.mul_le_mul hK (by omega)
  have h2 : Work.Fx.szl (A.take (k + 1)) + 1 ≤ 20 * SEL + 1 := by
    have hk20 : k + 1 ≤ 20 := by omega
    have := Nat.mul_le_mul_right SEL hk20
    omega
  have h3 : KS * 20 * (20 * SEL + 1) ≤ 1000 * KS * SEL := by
    have h4 : 20 * (20 * SEL + 1) ≤ 1000 * SEL := by nlinarith [hSEL]
    calc KS * 20 * (20 * SEL + 1) = KS * (20 * (20 * SEL + 1)) := by ring
      _ ≤ KS * (1000 * SEL) := Nat.mul_le_mul_left KS h4
      _ = 1000 * KS * SEL := by ring
  calc K * (k + 1) * (Work.Fx.szl (A.take (k + 1)) + 1) ≤ (KS * 20) * (20 * SEL + 1) :=
        Nat.mul_le_mul h1 h2
    _ = KS * 20 * (20 * SEL + 1) := by ring
    _ ≤ 1000 * KS * SEL := h3

theorem Pipe.pickK {prog : ℕ → Cmd} {K KS SEL : ℕ} (main : Cmd)
    (h : ∀ (m : Cmd) (k : ℕ), WordR m (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {A : List Val} {k : ℕ} (hK : K ≤ KS) (hk : k ≤ 19) (hkA : k < A.length)
    (hsz : ∀ v ∈ A, vsz v ≤ SEL) (hSEL : 1 ≤ SEL) :
    Pipe main (prog k) A (A.getD k .nil :: A) (1000 * KS * SEL) :=
  Pipe.le (Pipe.pick main h hkA) (le_step_mover20 hK k hk (szl_take_le_n hsz k) hSEL)

theorem Pipe.rollK {prog : ℕ → Cmd} {K KS SEL : ℕ} (main : Cmd)
    (h : ∀ (m : Cmd) (k : ℕ), WordR m (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {A : List Val} {k : ℕ} (hK : K ≤ KS) (hk : k ≤ 19) (hkA : k < A.length)
    (hsz : ∀ v ∈ A, vsz v ≤ SEL) (hSEL : 1 ≤ SEL) :
    Pipe main (prog k) A (A.getD k .nil :: A.eraseIdx k) (1000 * KS * SEL) :=
  Pipe.le (Pipe.roll main h hkA) (le_step_mover20 hK k hk (szl_take_le_n hsz k) hSEL)

theorem Pipe.dropK {prog : Cmd} {K KS SEL : ℕ} (main : Cmd)
    (h : ∀ (m : Cmd), WordR m prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1)))
    (a : Val) (hK : K ≤ KS) (ha : vsz a ≤ SEL) (hSEL : 1 ≤ SEL) :
    Pipe main prog [a] [] (1000 * KS * SEL) := by
  refine Pipe.le (Pipe.drop main h a) ?_
  have h1 : K * (vsz a + 1) ≤ KS * (SEL + 1) := Nat.mul_le_mul hK (by omega)
  have h2 : SEL + 1 ≤ 1000 * SEL := by omega
  calc K * (vsz a + 1) ≤ KS * (SEL + 1) := h1
    _ ≤ KS * (1000 * SEL) := Nat.mul_le_mul_left KS h2
    _ = 1000 * KS * SEL := by ring

/-! ## injectivity of the windows -/

theorem shape1_inj {s t : ℕ} {u u' : List (ℤ × ℤ)} {r r' : List Val}
    (h : cvecVal u :: buKeysT s t :: Val.int (s : ℤ) :: r
       = cvecVal u' :: buKeysT s t :: Val.int (s : ℤ) :: r') : u = u' ∧ r = r' := by
  have h1 : cvecVal u = cvecVal u' := (List.cons.inj h).1
  have h2 : buKeysT s t :: Val.int (s : ℤ) :: r = buKeysT s t :: Val.int (s : ℤ) :: r' :=
    (List.cons.inj h).2
  have h3 : Val.int (s : ℤ) :: r = Val.int (s : ℤ) :: r' := (List.cons.inj h2).2
  exact ⟨cvecVal_injK h1, (List.cons.inj h3).2⟩

theorem shape2_inj {p α s t : ℕ} {v v' : List (ℤ × ℤ)} {r r' : List Val}
    (h : buSignsT p α s t :: cvecVal v :: cvecVal v :: buColsT p α s t :: Val.int (s : ℤ)
          :: Val.int (p : ℤ) :: r
       = buSignsT p α s t :: cvecVal v' :: cvecVal v' :: buColsT p α s t :: Val.int (s : ℤ)
          :: Val.int (p : ℤ) :: r') : v = v' ∧ r = r' := by
  have h1 : cvecVal v :: cvecVal v :: buColsT p α s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: r
      = cvecVal v' :: cvecVal v' :: buColsT p α s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: r' :=
    (List.cons.inj h).2
  have h2 : cvecVal v = cvecVal v' := (List.cons.inj h1).1
  have h3 : cvecVal v :: buColsT p α s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: r
      = cvecVal v' :: buColsT p α s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: r' :=
    (List.cons.inj h1).2
  have h4 : buColsT p α s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: r
      = buColsT p α s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: r' := (List.cons.inj h3).2
  have h5 : Val.int (s : ℤ) :: Val.int (p : ℤ) :: r = Val.int (s : ℤ) :: Val.int (p : ℤ) :: r' :=
    (List.cons.inj h4).2
  have h6 : Val.int (p : ℤ) :: r = Val.int (p : ℤ) :: r' := (List.cons.inj h5).2
  exact ⟨cvecVal_injK h2, (List.cons.inj h6).2⟩

theorem shape3_inj {p α s t : ℕ} {u u' : List (ℤ × ℤ)} {r r' : List Val}
    (h : cvecVal u :: buWdL p α s t :: buKeysS s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: r
       = cvecVal u' :: buWdL p α s t :: buKeysS s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: r') :
    u = u' ∧ r = r' := by
  have h1 : cvecVal u = cvecVal u' := (List.cons.inj h).1
  have h2 : buWdL p α s t :: buKeysS s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: r
      = buWdL p α s t :: buKeysS s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: r' :=
    (List.cons.inj h).2
  have h3 : buKeysS s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: r
      = buKeysS s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: r' := (List.cons.inj h2).2
  have h4 : Val.int (s : ℤ) :: Val.int (p : ℤ) :: r = Val.int (s : ℤ) :: Val.int (p : ℤ) :: r' :=
    (List.cons.inj h3).2
  have h5 : Val.int (p : ℤ) :: r = Val.int (p : ℤ) :: r' := (List.cons.inj h4).2
  exact ⟨cvecVal_injK h1, (List.cons.inj h5).2⟩

/-! ## proof irrelevance of `buPermL`'s proof arguments, and the `buPhiL` bridge -/

theorem egGam_congr (s t : ℕ) (h1 h1' : 0 < s) (h2 h2' : Nat.Coprime t s) (j : Fin s) :
    egGam s t h1 h2 j = egGam s t h1' h2' j := by
  unfold egGam
  exact congrArg Classical.choose (Subsingleton.elim _ _)

theorem buPermL_congr (s t : ℕ) (h1 h1' : 0 < s) (h2 h2' : Nat.Coprime t s) (d : List (ℤ × ℤ)) :
    buPermL s t h1 h2 d = buPermL s t h1' h2' d :=
  congrArg (fun (g : Fin s → ℕ) => List.ofFn (fun j : Fin s => d.getD (g j) (0, 0)))
    (funext (fun j => congrArg Fin.val (egGam_congr s t h1 h1' h2 h2' j)))

theorem buPhiL_eq_permL (p α s t : ℕ) (h1 : 0 < s) (h2 : Nat.Coprime t s) (u : List (ℤ × ℤ)) :
    buPhiL p α s t h1 h2 u
      = buPermL s t h1 h2 (buDscL (buWd p α s t) p s
          (buJsumL (buWt p α s t) p s (egM p α) (egN p α s t) (buSelL s t u))) := rfl

/-! ## extracting the postcondition of a `WordR` -/

theorem WordR.post_exists {main p : Cmd} {Pre : List Val → Prop}
    {Post : List Val → List Val → Prop} {C : List Val → ℕ} (h : WordR main p Pre Post C)
    {vs : List Val} (hv : Pre vs) : ∃ out, Post vs out := by
  obtain ⟨out, s', n, hp, hev, hn, hstk, hoth⟩ :=
    h vs hv ⟨fun _ => Glyph.eos, fun k => if k = 0 then encs vs ++ ([] : List Glyph) else []⟩ []
      (by simp)
  exact ⟨out, hp⟩

/-! ## converting the three stage words into `Pipe`s -/

theorem Pipe.selStage {main selW : Cmd} {Ksel : ℕ} (p α s t : ℕ)
    (hsel : WordR main selW
      (fun vs => ∃ (u : List (ℤ × ℤ)) (rest : List Val),
        vs = cvecVal u :: buKeysT s t :: Val.int (s : ℤ) :: rest ∧ u.length = t ∧ buInV (2 ^ p) u)
      (fun vs out => ∃ (u : List (ℤ × ℤ)) (rest : List Val) (v : List (ℤ × ℤ)),
        vs = cvecVal u :: buKeysT s t :: Val.int (s : ℤ) :: rest ∧ out = cvecVal v :: rest ∧
        v = buSelL s t u ∧ v.length = s ∧ buInV (2 ^ (p - 1) + 2) v)
      (fun _ => Ksel * (t + 1) * (p + 1) * (p + 1)))
    {u₀ : List (ℤ × ℤ)} (hu₀ : u₀.length = t) (hv₀ : buInV (2 ^ p) u₀) :
    Pipe main selW (cvecVal u₀ :: buKeysT s t :: Val.int (s : ℤ) :: ([] : List Val))
      [cvecVal (buSelL s t u₀)] (Ksel * (t + 1) * (p + 1) * (p + 1)) := by
  intro rest vs hvs s' R hR
  obtain ⟨out, s'', n, ⟨u, rst, v, hvs', hout, hv, hvlen, hvV⟩, hev, hn, hstk, hoth⟩ :=
    hsel vs ⟨u₀, rest, hvs, hu₀, hv₀⟩ s' R hR
  obtain ⟨hu, hr⟩ := shape1_inj (hvs'.symm.trans hvs)
  try simp only [List.nil_append] at hout hr
  rw [hr] at hout
  rw [hu] at hv
  refine ⟨out, s'', n, ?_, hev, hn, hstk, hoth⟩
  simp only [List.cons_append, List.nil_append, hout, hv]
  try rfl

theorem Pipe.rndStage {main rndW : Cmd} {Krnd : ℕ} {Cm : ℕ → ℕ} (p α s t : ℕ)
    (hrnd : WordR main rndW
      (fun vs => ∃ (v : List (ℤ × ℤ)) (rest : List Val),
        vs = buSignsT p α s t :: cvecVal v :: cvecVal v :: buColsT p α s t :: Val.int (s : ℤ)
          :: Val.int (p : ℤ) :: rest ∧ v.length = s ∧ buInV (2 ^ (p - 1) + 2) v)
      (fun vs out => ∃ (v : List (ℤ × ℤ)) (rest : List Val) (u : List (ℤ × ℤ)),
        vs = buSignsT p α s t :: cvecVal v :: cvecVal v :: buColsT p α s t :: Val.int (s : ℤ)
          :: Val.int (p : ℤ) :: rest ∧ out = cvecVal u :: rest ∧
        u = buJsumL (buWt p α s t) p s (egM p α) (egN p α s t) v ∧ u.length = s ∧
        buInV (2 ^ (p + 1)) u)
      (fun _ => Krnd * (egN p α s t + 1) * (egM p α + 1) * (s + 1) * (Cm (Krnd * p) + p + 1)))
    {v₀ : List (ℤ × ℤ)} (hv₀ : v₀.length = s) (hVv₀ : buInV (2 ^ (p - 1) + 2) v₀) :
    Pipe main rndW (buSignsT p α s t :: cvecVal v₀ :: cvecVal v₀ :: buColsT p α s t
        :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: ([] : List Val))
      [cvecVal (buJsumL (buWt p α s t) p s (egM p α) (egN p α s t) v₀)]
      (Krnd * (egN p α s t + 1) * (egM p α + 1) * (s + 1) * (Cm (Krnd * p) + p + 1)) := by
  intro rest vs hvs s' R hR
  obtain ⟨out, s'', n, ⟨v, rst, u, hvs', hout, hu, hulen, huV⟩, hev, hn, hstk, hoth⟩ :=
    hrnd vs ⟨v₀, rest, hvs, hv₀, hVv₀⟩ s' R hR
  obtain ⟨hv, hr⟩ := shape2_inj (hvs'.symm.trans hvs)
  try simp only [List.nil_append] at hout hr
  rw [hr] at hout
  rw [hv] at hu
  refine ⟨out, s'', n, ?_, hev, hn, hstk, hoth⟩
  simp only [List.cons_append, List.nil_append, hout, hu]
  try rfl

theorem Pipe.sclStage {main sclW : Cmd} {Kscl : ℕ} {Cm : ℕ → ℕ} (p α s t : ℕ)
    (hcop : Nat.Coprime t s)
    (hscl : ∀ (h1 : 0 < s), WordR main sclW
      (fun vs => ∃ (u : List (ℤ × ℤ)) (rest : List Val),
        vs = cvecVal u :: buWdL p α s t :: buKeysS s t :: Val.int (s : ℤ) :: Val.int (p : ℤ)
          :: rest ∧ u.length = s ∧ buInV (2 ^ (p + 1)) u)
      (fun vs out => ∃ (u : List (ℤ × ℤ)) (rest : List Val) (w : List (ℤ × ℤ)),
        vs = cvecVal u :: buWdL p α s t :: buKeysS s t :: Val.int (s : ℤ) :: Val.int (p : ℤ)
          :: rest ∧ out = cvecVal w :: rest ∧
        w = buPermL s t h1 hcop (buDscL (buWd p α s t) p s u) ∧ w.length = s ∧ buInV (2 ^ p) w)
      (fun _ => Kscl * (s + 1) * (p + 1) * (p + 1) + Kscl * (s + 1) * (Cm (Kscl * p) + p + 1)))
    {u₀ : List (ℤ × ℤ)} (hu₀ : u₀.length = s) (hv₀ : buInV (2 ^ (p + 1)) u₀) (h1 : 0 < s) :
    Pipe main sclW (cvecVal u₀ :: buWdL p α s t :: buKeysS s t :: Val.int (s : ℤ)
        :: Val.int (p : ℤ) :: ([] : List Val))
      [cvecVal (buPermL s t h1 hcop (buDscL (buWd p α s t) p s u₀))]
      (Kscl * (s + 1) * (p + 1) * (p + 1) + Kscl * (s + 1) * (Cm (Kscl * p) + p + 1)) := by
  intro rest vs hvs s' R hR
  obtain ⟨out, s'', n, ⟨u, rst, w, hvs', hout, hw, hwl, hwV⟩, hev, hn, hstk, hoth⟩ :=
    hscl h1 vs ⟨u₀, rest, hvs, hu₀, hv₀⟩ s' R hR
  obtain ⟨hu, hr⟩ := shape3_inj (hvs'.symm.trans hvs)
  try simp only [List.nil_append] at hout hr
  rw [hr] at hout
  rw [hu] at hw
  refine ⟨out, s'', n, ?_, hev, hn, hstk, hoth⟩
  simp only [List.cons_append, List.nil_append, hout, hw]
  try rfl
  try exact congrArg (fun d => cvecVal d :: rest) (buPermL_congr s t _ _ hcop hcop _)

theorem buQWwireK (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib) (FL : HvdH.FxLib)
    (selW rndW sclW : HvdH.Cmd) (Ksel Krnd Kscl : ℕ)
    (hsel : ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t) (htp : t < 2 ^ p)
      (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm → Ksel * p < N →
      HvdH.WordR main selW
        (fun vs => ∃ (u : List (ℤ × ℤ)) (rest : List HvdH.Val),
          vs = HvdH.cvecVal u :: Work.Resample.buKeysT s t :: HvdH.Val.int (s : ℤ) :: rest ∧
          u.length = t ∧ Work.Resample.buInV (2 ^ p) u)
        (fun vs out => ∃ (u : List (ℤ × ℤ)) (rest : List HvdH.Val) (v : List (ℤ × ℤ)),
          vs = HvdH.cvecVal u :: Work.Resample.buKeysT s t :: HvdH.Val.int (s : ℤ) :: rest ∧
          out = HvdH.cvecVal v :: rest ∧ v = Work.Resample.buSelL s t u ∧ v.length = s ∧
          Work.Resample.buInV (2 ^ (p - 1) + 2) v)
        (fun _ => Ksel * (t + 1) * (p + 1) * (p + 1)))
    (hrnd : ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
      (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1)
      (hrow : ∀ ℓ : ℤ, ∑ h ∈ Work.Resample.egHset (Work.Resample.egM p α),
        |(Work.Resample.buWt p α s t ℓ h : ℝ)| ≤ (2 : ℝ) ^ p / 2 + 8 * (Work.Resample.egM p α : ℝ))
      (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm → Krnd * p < N →
      HvdH.WordR main rndW
        (fun vs => ∃ (v : List (ℤ × ℤ)) (rest : List HvdH.Val),
          vs = Work.Resample.buSignsT p α s t :: HvdH.cvecVal v :: HvdH.cvecVal v ::
            Work.Resample.buColsT p α s t :: HvdH.Val.int (s : ℤ) :: HvdH.Val.int (p : ℤ) :: rest ∧
          v.length = s ∧ Work.Resample.buInV (2 ^ (p - 1) + 2) v)
        (fun vs out => ∃ (v : List (ℤ × ℤ)) (rest : List HvdH.Val) (u : List (ℤ × ℤ)),
          vs = Work.Resample.buSignsT p α s t :: HvdH.cvecVal v :: HvdH.cvecVal v ::
            Work.Resample.buColsT p α s t :: HvdH.Val.int (s : ℤ) :: HvdH.Val.int (p : ℤ) :: rest ∧
          out = HvdH.cvecVal u :: rest ∧
          u = Work.Resample.buJsumL (Work.Resample.buWt p α s t) p s (Work.Resample.egM p α)
            (Work.Resample.egN p α s t) v ∧
          u.length = s ∧ Work.Resample.buInV (2 ^ (p + 1)) u)
        (fun _ => Krnd * (Work.Resample.egN p α s t + 1) * (Work.Resample.egM p α + 1) * (s + 1) *
            (Cm (Krnd * p) + p + 1)))
    (hscl : ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t) (htp : t < 2 ^ p)
      (hα : 2 ≤ α)
      (hwd : ∀ ℓ : ℤ, 8 * (Work.Resample.buWd p α s t ℓ).natAbs ≤ 3 * 2 ^ p)
      (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm → Kscl * p < N →
      HvdH.WordR main sclW
        (fun vs => ∃ (u : List (ℤ × ℤ)) (rest : List HvdH.Val),
          vs = HvdH.cvecVal u :: Work.Resample.buWdL p α s t :: Work.Resample.buKeysS s t ::
            HvdH.Val.int (s : ℤ) :: HvdH.Val.int (p : ℤ) :: rest ∧
          u.length = s ∧ Work.Resample.buInV (2 ^ (p + 1)) u)
        (fun vs out => ∃ (u : List (ℤ × ℤ)) (rest : List HvdH.Val) (w : List (ℤ × ℤ)),
          vs = HvdH.cvecVal u :: Work.Resample.buWdL p α s t :: Work.Resample.buKeysS s t ::
            HvdH.Val.int (s : ℤ) :: HvdH.Val.int (p : ℤ) :: rest ∧
          out = HvdH.cvecVal w :: rest ∧
          w = Work.Resample.buPermL s t (by omega) hcop.symm
                (Work.Resample.buDscL (Work.Resample.buWd p α s t) p s u) ∧
          w.length = s ∧ Work.Resample.buInV (2 ^ p) w)
        (fun _ => Kscl * (s + 1) * (p + 1) * (p + 1) + Kscl * (s + 1) * (Cm (Kscl * p) + p + 1))) :
    ∃ (q : HvdH.Cmd) (Kw : ℕ),
    ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t) (htp : t < 2 ^ p)
      (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
      (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1)
      (hrow : ∀ ℓ : ℤ, ∑ h ∈ Work.Resample.egHset (Work.Resample.egM p α),
        |(Work.Resample.buWt p α s t ℓ h : ℝ)| ≤ (2 : ℝ) ^ p / 2 + 8 * (Work.Resample.egM p α : ℝ))
      (hwd : ∀ ℓ : ℤ, 8 * (Work.Resample.buWd p α s t ℓ).natAbs ≤ 3 * 2 ^ p)
      (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm → Kw * p < N →
    HvdH.WordR main q
      (fun vs => ∃ (u : List (ℤ × ℤ)) (rest : List HvdH.Val),
        vs = HvdH.ofList (u.map HvdH.cfxVal) ::
          Work.Resample.buTabList p α s t (by omega) hcop.symm ++ rest ∧
        u.length = t ∧ Work.Resample.buInV (2 ^ p) u)
      (fun vs out => ∃ (u : List (ℤ × ℤ)) (rest : List HvdH.Val) (w : List (ℤ × ℤ)),
        vs = HvdH.ofList (u.map HvdH.cfxVal) ::
          Work.Resample.buTabList p α s t (by omega) hcop.symm ++ rest ∧
        out = HvdH.cvecVal w :: Work.Resample.buTabList p α s t (by omega) hcop.symm ++ rest ∧
        w = Work.Resample.buPhiL p α s t (by omega) hcop.symm u ∧
        w.length = s ∧ Work.Resample.buInV (2 ^ p) w)
      (fun _ => Work.Resample.egCostShape Kw p α t Cm) := by
  obtain ⟨pickP, KP, hpick⟩ := KL.pick
  obtain ⟨rollP, KR, hroll⟩ := KL.roll
  obtain ⟨dropP, KD, hdrop⟩ := KL.drop
  let KW : ℕ := 4 * 10 ^ 10 * (KP + KR + KD + 1) + 16 * Krnd + Ksel + 2 * Kscl + 2
  refine ⟨buChainProgK [pickP 3, pickP 8, pickP 2, selW, pickP 2, pickP 5, pickP 13, pickP 3, pickP 4, pickP 17, rndW, pickP 3, pickP 6, pickP 12, pickP 14, pickP 4, sclW, rollP 3, dropP, rollP 2, dropP, rollP 1, dropP], KW, ?_⟩
  intro p α s t hs hst hcop htp hα hp hαp hθ hrow hwd main N Cm hcm hmul hN
  intro vs hpre
  obtain ⟨u, rest, hvs, hulen, huV⟩ := hpre
  intro st0 RR hR
  have h0s : 0 < s := by omega
  let Wc : ℕ := 1000 * (KP + KR + KD + 1) * buSB p α t
  let Ssel : ℕ := Ksel * (t + 1) * (p + 1) * (p + 1)
  let Srnd : ℕ := Krnd * (egN p α s t + 1) * (egM p α + 1) * (s + 1) * (Cm (Krnd * p) + p + 1)
  let Sscl : ℕ := Kscl * (s + 1) * (p + 1) * (p + 1) + Kscl * (s + 1) * (Cm (Kscl * p) + p + 1)
  let CSUM : ℕ := Wc + (Wc + (Wc + (Ssel + (Wc + (Wc + (Wc + (Wc + (Wc + (Wc + (Srnd + (Wc + (Wc + (Wc + (Wc + (Wc + (Sscl + (Wc + (Wc + (Wc + (Wc + (Wc + (Wc + (1)))))))))))))))))))))))
  let V : Val := cvecVal u
  let V1 : Val := cvecVal (buSelL s t u)
  let Jv : List (ℤ × ℤ) := buJsumL (buWt p α s t) p s (egM p α) (egN p α s t) (buSelL s t u)
  let U : Val := cvecVal Jv
  let Wv : List (ℤ × ℤ) := buPermL s t h0s hcop.symm (buDscL (buWd p α s t) p s Jv)
  let W : Val := cvecVal Wv
  have hNKsel : Ksel * p < N :=
    lt_of_le_of_lt (Nat.mul_le_mul_right p (by omega : Ksel ≤ KW)) hN
  have hNKrnd : Krnd * p < N :=
    lt_of_le_of_lt (Nat.mul_le_mul_right p (by omega : Krnd ≤ KW)) hN
  have hNKscl : Kscl * p < N :=
    lt_of_le_of_lt (Nat.mul_le_mul_right p (by omega : Kscl ≤ KW)) hN
  have hTsz : ∀ v ∈ buTK p α s t, vsz v ≤ buSB p α t := by
    intro v hv
    exact buTabSzKK p α s t hs hst hcop htp hα hp hαp hθ hrow hwd v
      (by rw [buTabList_eq_buTK]; exact hv)
  have hTab_p : vsz (Val.int (p : ℤ)) ≤ buSB p α t := hTsz _ (mem_buTK_int_p p α s t)
  have hTab_s : vsz (Val.int (s : ℤ)) ≤ buSB p α t := hTsz _ (mem_buTK_int_s p α s t)
  have hTab_KT : vsz (buKeysT s t) ≤ buSB p α t := hTsz _ (mem_buTK_keysT p α s t)
  have hTab_KS : vsz (buKeysS s t) ≤ buSB p α t := hTsz _ (mem_buTK_keysS p α s t)
  have hTab_WD : vsz (buWdL p α s t) ≤ buSB p α t := hTsz _ (mem_buTK_wdL p α s t)
  have hTab_CO : vsz (buColsT p α s t) ≤ buSB p α t := hTsz _ (mem_buTK_colsT p α s t)
  have hTab_SG : vsz (buSignsT p α s t) ≤ buSB p α t := hTsz _ (mem_buTK_signsT p α s t)
  have hselLen : (buSelL s t u).length = s := by simp [buSelL]
  have hselInV : buInV (2 ^ (p - 1) + 2) (buSelL s t u) := buSelLInV p s t u hulen huV
  have hrndW := hrnd p α s t hs hst hα hp hαp hθ hrow main N Cm hcm hmul hNKrnd
  obtain ⟨outR, ⟨vR, rstR, uR, hvsR, houtR, huR, huRlen, huRV⟩⟩ :=
    WordR.post_exists hrndW
      (vs := buSignsT p α s t :: cvecVal (buSelL s t u) :: cvecVal (buSelL s t u)
        :: buColsT p α s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: ([] : List Val))
      ⟨buSelL s t u, [], rfl, hselLen, hselInV⟩
  have hvR : vR = buSelL s t u := (shape2_inj hvsR.symm).1
  have huR2 : uR = Jv := by rw [huR, hvR]
  have hUlen : Jv.length = s := by rw [← huR2]; exact huRlen
  have hUV : buInV (2 ^ (p + 1)) Jv := by rw [← huR2]; exact huRV
  have hWlen : Wv.length = s := by simp [Wv, buPermL]
  have hWV : buInV (2 ^ p) Wv := by
    have hDsc : buInV (2 ^ p) (buDscL (buWd p α s t) p s Jv) :=
      buDscL_inV p s (buWd p α s t) Jv hwd hUV
    exact buPermL_inV p s t h0s hcop.symm _ hDsc
  have hVsz : vsz V ≤ buSB p α t :=
    buVecSz p α t (2 ^ p) (le_of_eq hulen) (Nat.pow_le_pow_right (by norm_num) (by omega)) huV
  have hV1sz : vsz V1 ≤ buSB p α t :=
    buVecSz p α t (2 ^ (p - 1) + 2) (by rw [hselLen]; omega)
      (by have h2 : 2 ≤ 2 ^ (p - 1) := by
            calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
              _ ≤ 2 ^ (p - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h4 : 2 ^ (p - 1) + 2 ≤ 2 ^ (p - 1) * 2 := by
            have h6 : 2 ^ (p - 1) * 2 = 2 ^ (p - 1) + 2 ^ (p - 1) := by ring
            rw [h6]; omega
          have h5 : 2 ^ (p - 1) * 2 = 2 ^ p := by
            rw [← pow_succ]
            congr 1
            omega
          calc 2 ^ (p - 1) + 2 ≤ 2 ^ (p - 1) * 2 := h4
            _ = 2 ^ p := h5
            _ ≤ 2 ^ (p + 1) := Nat.pow_le_pow_right (by norm_num) (by omega))
      hselInV
  have hUsz : vsz U ≤ buSB p α t :=
    buVecSz p α t (2 ^ (p + 1)) (by rw [hUlen]; omega) le_rfl hUV
  have hWsz : vsz W ≤ buSB p α t :=
    buVecSz p α t (2 ^ p) (by rw [hWlen]; omega)
      (Nat.pow_le_pow_right (by norm_num) (by omega)) hWV
  have hsclGen : ∀ (h1 : 0 < s), WordR main sclW
      (fun vs => ∃ (u : List (ℤ × ℤ)) (rest : List Val),
        vs = cvecVal u :: buWdL p α s t :: buKeysS s t :: Val.int (s : ℤ) :: Val.int (p : ℤ)
          :: rest ∧ u.length = s ∧ buInV (2 ^ (p + 1)) u)
      (fun vs out => ∃ (u : List (ℤ × ℤ)) (rest : List Val) (w : List (ℤ × ℤ)),
        vs = cvecVal u :: buWdL p α s t :: buKeysS s t :: Val.int (s : ℤ) :: Val.int (p : ℤ)
          :: rest ∧ out = cvecVal w :: rest ∧
        w = buPermL s t h1 hcop.symm (buDscL (buWd p α s t) p s u) ∧ w.length = s ∧
        buInV (2 ^ p) w)
      (fun _ => Kscl * (s + 1) * (p + 1) * (p + 1) + Kscl * (s + 1) * (Cm (Kscl * p) + p + 1)) := by
    intro h1
    refine KL.conseq main sclW _ _ _ _ _ _
      (hscl p α s t hs hst hcop htp hα hwd main N Cm hcm hmul hNKscl)
      (fun vs hv => hv) ?_ (fun vs hv => le_rfl)
    intro vs out hv hpost
    obtain ⟨u₂, r₂, w₂, hvs₂, hout₂, hw₂, hwl₂, hwV₂⟩ := hpost
    exact ⟨u₂, r₂, w₂, hvs₂, hout₂,
      hw₂.trans (buPermL_congr s t _ h1 hcop.symm hcop.symm _), hwl₂, hwV₂⟩
  have hsz0 : ∀ v ∈ V :: buTK p α s t, vsz v ≤ buSB p α t := vsz_all_cons hVsz (hTsz)
  have hsz1 : ∀ v ∈ Val.int (s : ℤ) :: V :: buTK p α s t, vsz v ≤ buSB p α t := vsz_all_cons hTab_s (vsz_all_cons hVsz (hTsz))
  have hsz2 : ∀ v ∈ buKeysT s t :: Val.int (s : ℤ) :: V :: buTK p α s t, vsz v ≤ buSB p α t := vsz_all_cons hTab_KT (vsz_all_cons hTab_s (vsz_all_cons hVsz (hTsz)))
  have hsz3 : ∀ v ∈ V :: buKeysT s t :: Val.int (s : ℤ) :: V :: buTK p α s t, vsz v ≤ buSB p α t := vsz_all_cons hVsz (vsz_all_cons hTab_KT (vsz_all_cons hTab_s (vsz_all_cons hVsz (hTsz))))
  have hsz4 : ∀ v ∈ V1 :: V :: buTK p α s t, vsz v ≤ buSB p α t := vsz_all_cons hV1sz (vsz_all_cons hVsz (hTsz))
  have hsz5 : ∀ v ∈ Val.int (p : ℤ) :: V1 :: V :: buTK p α s t, vsz v ≤ buSB p α t := vsz_all_cons hTab_p (vsz_all_cons hV1sz (vsz_all_cons hVsz (hTsz)))
  have hsz6 : ∀ v ∈ Val.int (s : ℤ) :: Val.int (p : ℤ) :: V1 :: V :: buTK p α s t, vsz v ≤ buSB p α t := vsz_all_cons hTab_s (vsz_all_cons hTab_p (vsz_all_cons hV1sz (vsz_all_cons hVsz (hTsz))))
  have hsz7 : ∀ v ∈ buColsT p α s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: V1 :: V :: buTK p α s t, vsz v ≤ buSB p α t := vsz_all_cons hTab_CO (vsz_all_cons hTab_s (vsz_all_cons hTab_p (vsz_all_cons hV1sz (vsz_all_cons hVsz (hTsz)))))
  have hsz8 : ∀ v ∈ V1 :: buColsT p α s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: V1 :: V :: buTK p α s t, vsz v ≤ buSB p α t := vsz_all_cons hV1sz (vsz_all_cons hTab_CO (vsz_all_cons hTab_s (vsz_all_cons hTab_p (vsz_all_cons hV1sz (vsz_all_cons hVsz (hTsz))))))
  have hsz9 : ∀ v ∈ V1 :: V1 :: buColsT p α s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: V1 :: V :: buTK p α s t, vsz v ≤ buSB p α t := vsz_all_cons hV1sz (vsz_all_cons hV1sz (vsz_all_cons hTab_CO (vsz_all_cons hTab_s (vsz_all_cons hTab_p (vsz_all_cons hV1sz (vsz_all_cons hVsz (hTsz)))))))
  have hsz10 : ∀ v ∈ buSignsT p α s t :: V1 :: V1 :: buColsT p α s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: V1 :: V :: buTK p α s t, vsz v ≤ buSB p α t := vsz_all_cons hTab_SG (vsz_all_cons hV1sz (vsz_all_cons hV1sz (vsz_all_cons hTab_CO (vsz_all_cons hTab_s (vsz_all_cons hTab_p (vsz_all_cons hV1sz (vsz_all_cons hVsz (hTsz))))))))
  have hsz11 : ∀ v ∈ U :: V1 :: V :: buTK p α s t, vsz v ≤ buSB p α t := vsz_all_cons hUsz (vsz_all_cons hV1sz (vsz_all_cons hVsz (hTsz)))
  have hsz12 : ∀ v ∈ Val.int (p : ℤ) :: U :: V1 :: V :: buTK p α s t, vsz v ≤ buSB p α t := vsz_all_cons hTab_p (vsz_all_cons hUsz (vsz_all_cons hV1sz (vsz_all_cons hVsz (hTsz))))
  have hsz13 : ∀ v ∈ Val.int (s : ℤ) :: Val.int (p : ℤ) :: U :: V1 :: V :: buTK p α s t, vsz v ≤ buSB p α t := vsz_all_cons hTab_s (vsz_all_cons hTab_p (vsz_all_cons hUsz (vsz_all_cons hV1sz (vsz_all_cons hVsz (hTsz)))))
  have hsz14 : ∀ v ∈ buKeysS s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: U :: V1 :: V :: buTK p α s t, vsz v ≤ buSB p α t := vsz_all_cons hTab_KS (vsz_all_cons hTab_s (vsz_all_cons hTab_p (vsz_all_cons hUsz (vsz_all_cons hV1sz (vsz_all_cons hVsz (hTsz))))))
  have hsz15 : ∀ v ∈ buWdL p α s t :: buKeysS s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: U :: V1 :: V :: buTK p α s t, vsz v ≤ buSB p α t := vsz_all_cons hTab_WD (vsz_all_cons hTab_KS (vsz_all_cons hTab_s (vsz_all_cons hTab_p (vsz_all_cons hUsz (vsz_all_cons hV1sz (vsz_all_cons hVsz (hTsz)))))))
  have hsz16 : ∀ v ∈ U :: buWdL p α s t :: buKeysS s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: U :: V1 :: V :: buTK p α s t, vsz v ≤ buSB p α t := vsz_all_cons hUsz (vsz_all_cons hTab_WD (vsz_all_cons hTab_KS (vsz_all_cons hTab_s (vsz_all_cons hTab_p (vsz_all_cons hUsz (vsz_all_cons hV1sz (vsz_all_cons hVsz (hTsz))))))))
  have hsz17 : ∀ v ∈ W :: U :: V1 :: V :: buTK p α s t, vsz v ≤ buSB p α t := vsz_all_cons hWsz (vsz_all_cons hUsz (vsz_all_cons hV1sz (vsz_all_cons hVsz (hTsz))))
  have hsz18 : ∀ v ∈ V :: W :: U :: V1 :: buTK p α s t, vsz v ≤ buSB p α t := vsz_all_cons hVsz (vsz_all_cons hWsz (vsz_all_cons hUsz (vsz_all_cons hV1sz (hTsz))))
  have hsz19 : ∀ v ∈ W :: U :: V1 :: buTK p α s t, vsz v ≤ buSB p α t := vsz_all_cons hWsz (vsz_all_cons hUsz (vsz_all_cons hV1sz (hTsz)))
  have hsz20 : ∀ v ∈ V1 :: W :: U :: buTK p α s t, vsz v ≤ buSB p α t := vsz_all_cons hV1sz (vsz_all_cons hWsz (vsz_all_cons hUsz (hTsz)))
  have hsz21 : ∀ v ∈ W :: U :: buTK p α s t, vsz v ≤ buSB p α t := vsz_all_cons hWsz (vsz_all_cons hUsz (hTsz))
  have hsz22 : ∀ v ∈ U :: W :: buTK p α s t, vsz v ≤ buSB p α t := vsz_all_cons hUsz (vsz_all_cons hWsz (hTsz))
  have hsz23 : ∀ v ∈ W :: buTK p α s t, vsz v ≤ buSB p α t := vsz_all_cons hWsz (hTsz)
  have hstep0 : Pipe main (pickP 3) (V :: buTK p α s t) (Val.int (s : ℤ) :: V :: buTK p α s t) (Wc) := by
    refine Pipe.rw (Pipe.pickK (K := KP) (KS := KP + KR + KD + 1) (SEL := buSB p α t) main hpick
      (by omega) (by omega) ?_ ?_ (one_le_buSBK p α t)) ?_
    · simp only [buTK, List.length_cons, List.length_nil]; omega
    · exact hsz0
    · simp only [buTK, List.getD_cons_zero, List.getD_cons_succ]
  have hstep1 : Pipe main (pickP 8) (Val.int (s : ℤ) :: V :: buTK p α s t) (buKeysT s t :: Val.int (s : ℤ) :: V :: buTK p α s t) (Wc) := by
    refine Pipe.rw (Pipe.pickK (K := KP) (KS := KP + KR + KD + 1) (SEL := buSB p α t) main hpick
      (by omega) (by omega) ?_ ?_ (one_le_buSBK p α t)) ?_
    · simp only [buTK, List.length_cons, List.length_nil]; omega
    · exact hsz1
    · simp only [buTK, List.getD_cons_zero, List.getD_cons_succ]
  have hstep2 : Pipe main (pickP 2) (buKeysT s t :: Val.int (s : ℤ) :: V :: buTK p α s t) (V :: buKeysT s t :: Val.int (s : ℤ) :: V :: buTK p α s t) (Wc) := by
    refine Pipe.rw (Pipe.pickK (K := KP) (KS := KP + KR + KD + 1) (SEL := buSB p α t) main hpick
      (by omega) (by omega) ?_ ?_ (one_le_buSBK p α t)) ?_
    · simp only [buTK, List.length_cons, List.length_nil]; omega
    · exact hsz2
    · simp only [buTK, List.getD_cons_zero, List.getD_cons_succ]
  have hstep3 : Pipe main (selW) (V :: buKeysT s t :: Val.int (s : ℤ) :: V :: buTK p α s t) (V1 :: V :: buTK p α s t) (Ssel) := by
    exact Pipe.appendTail (V :: buTK p α s t) (Pipe.selStage p α s t
      (hsel p α s t hs hst hcop htp main N Cm hcm hmul hNKsel) (u₀ := u) hulen huV)
  have hstep4 : Pipe main (pickP 2) (V1 :: V :: buTK p α s t) (Val.int (p : ℤ) :: V1 :: V :: buTK p α s t) (Wc) := by
    refine Pipe.rw (Pipe.pickK (K := KP) (KS := KP + KR + KD + 1) (SEL := buSB p α t) main hpick
      (by omega) (by omega) ?_ ?_ (one_le_buSBK p α t)) ?_
    · simp only [buTK, List.length_cons, List.length_nil]; omega
    · exact hsz4
    · simp only [buTK, List.getD_cons_zero, List.getD_cons_succ]
  have hstep5 : Pipe main (pickP 5) (Val.int (p : ℤ) :: V1 :: V :: buTK p α s t) (Val.int (s : ℤ) :: Val.int (p : ℤ) :: V1 :: V :: buTK p α s t) (Wc) := by
    refine Pipe.rw (Pipe.pickK (K := KP) (KS := KP + KR + KD + 1) (SEL := buSB p α t) main hpick
      (by omega) (by omega) ?_ ?_ (one_le_buSBK p α t)) ?_
    · simp only [buTK, List.length_cons, List.length_nil]; omega
    · exact hsz5
    · simp only [buTK, List.getD_cons_zero, List.getD_cons_succ]
  have hstep6 : Pipe main (pickP 13) (Val.int (s : ℤ) :: Val.int (p : ℤ) :: V1 :: V :: buTK p α s t) (buColsT p α s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: V1 :: V :: buTK p α s t) (Wc) := by
    refine Pipe.rw (Pipe.pickK (K := KP) (KS := KP + KR + KD + 1) (SEL := buSB p α t) main hpick
      (by omega) (by omega) ?_ ?_ (one_le_buSBK p α t)) ?_
    · simp only [buTK, List.length_cons, List.length_nil]; omega
    · exact hsz6
    · simp only [buTK, List.getD_cons_zero, List.getD_cons_succ]
  have hstep7 : Pipe main (pickP 3) (buColsT p α s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: V1 :: V :: buTK p α s t) (V1 :: buColsT p α s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: V1 :: V :: buTK p α s t) (Wc) := by
    refine Pipe.rw (Pipe.pickK (K := KP) (KS := KP + KR + KD + 1) (SEL := buSB p α t) main hpick
      (by omega) (by omega) ?_ ?_ (one_le_buSBK p α t)) ?_
    · simp only [buTK, List.length_cons, List.length_nil]; omega
    · exact hsz7
    · simp only [buTK, List.getD_cons_zero, List.getD_cons_succ]
  have hstep8 : Pipe main (pickP 4) (V1 :: buColsT p α s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: V1 :: V :: buTK p α s t) (V1 :: V1 :: buColsT p α s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: V1 :: V :: buTK p α s t) (Wc) := by
    refine Pipe.rw (Pipe.pickK (K := KP) (KS := KP + KR + KD + 1) (SEL := buSB p α t) main hpick
      (by omega) (by omega) ?_ ?_ (one_le_buSBK p α t)) ?_
    · simp only [buTK, List.length_cons, List.length_nil]; omega
    · exact hsz8
    · simp only [buTK, List.getD_cons_zero, List.getD_cons_succ]
  have hstep9 : Pipe main (pickP 17) (V1 :: V1 :: buColsT p α s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: V1 :: V :: buTK p α s t) (buSignsT p α s t :: V1 :: V1 :: buColsT p α s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: V1 :: V :: buTK p α s t) (Wc) := by
    refine Pipe.rw (Pipe.pickK (K := KP) (KS := KP + KR + KD + 1) (SEL := buSB p α t) main hpick
      (by omega) (by omega) ?_ ?_ (one_le_buSBK p α t)) ?_
    · simp only [buTK, List.length_cons, List.length_nil]; omega
    · exact hsz9
    · simp only [buTK, List.getD_cons_zero, List.getD_cons_succ]
  have hstep10 : Pipe main (rndW) (buSignsT p α s t :: V1 :: V1 :: buColsT p α s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: V1 :: V :: buTK p α s t) (U :: V1 :: V :: buTK p α s t) (Srnd) := by
    exact Pipe.appendTail (V1 :: V :: buTK p α s t) (Pipe.rndStage p α s t
      (hrnd p α s t hs hst hα hp hαp hθ hrow main N Cm hcm hmul hNKrnd)
      (v₀ := buSelL s t u) hselLen hselInV)
  have hstep11 : Pipe main (pickP 3) (U :: V1 :: V :: buTK p α s t) (Val.int (p : ℤ) :: U :: V1 :: V :: buTK p α s t) (Wc) := by
    refine Pipe.rw (Pipe.pickK (K := KP) (KS := KP + KR + KD + 1) (SEL := buSB p α t) main hpick
      (by omega) (by omega) ?_ ?_ (one_le_buSBK p α t)) ?_
    · simp only [buTK, List.length_cons, List.length_nil]; omega
    · exact hsz11
    · simp only [buTK, List.getD_cons_zero, List.getD_cons_succ]
  have hstep12 : Pipe main (pickP 6) (Val.int (p : ℤ) :: U :: V1 :: V :: buTK p α s t) (Val.int (s : ℤ) :: Val.int (p : ℤ) :: U :: V1 :: V :: buTK p α s t) (Wc) := by
    refine Pipe.rw (Pipe.pickK (K := KP) (KS := KP + KR + KD + 1) (SEL := buSB p α t) main hpick
      (by omega) (by omega) ?_ ?_ (one_le_buSBK p α t)) ?_
    · simp only [buTK, List.length_cons, List.length_nil]; omega
    · exact hsz12
    · simp only [buTK, List.getD_cons_zero, List.getD_cons_succ]
  have hstep13 : Pipe main (pickP 12) (Val.int (s : ℤ) :: Val.int (p : ℤ) :: U :: V1 :: V :: buTK p α s t) (buKeysS s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: U :: V1 :: V :: buTK p α s t) (Wc) := by
    refine Pipe.rw (Pipe.pickK (K := KP) (KS := KP + KR + KD + 1) (SEL := buSB p α t) main hpick
      (by omega) (by omega) ?_ ?_ (one_le_buSBK p α t)) ?_
    · simp only [buTK, List.length_cons, List.length_nil]; omega
    · exact hsz13
    · simp only [buTK, List.getD_cons_zero, List.getD_cons_succ]
  have hstep14 : Pipe main (pickP 14) (buKeysS s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: U :: V1 :: V :: buTK p α s t) (buWdL p α s t :: buKeysS s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: U :: V1 :: V :: buTK p α s t) (Wc) := by
    refine Pipe.rw (Pipe.pickK (K := KP) (KS := KP + KR + KD + 1) (SEL := buSB p α t) main hpick
      (by omega) (by omega) ?_ ?_ (one_le_buSBK p α t)) ?_
    · simp only [buTK, List.length_cons, List.length_nil]; omega
    · exact hsz14
    · simp only [buTK, List.getD_cons_zero, List.getD_cons_succ]
  have hstep15 : Pipe main (pickP 4) (buWdL p α s t :: buKeysS s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: U :: V1 :: V :: buTK p α s t) (U :: buWdL p α s t :: buKeysS s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: U :: V1 :: V :: buTK p α s t) (Wc) := by
    refine Pipe.rw (Pipe.pickK (K := KP) (KS := KP + KR + KD + 1) (SEL := buSB p α t) main hpick
      (by omega) (by omega) ?_ ?_ (one_le_buSBK p α t)) ?_
    · simp only [buTK, List.length_cons, List.length_nil]; omega
    · exact hsz15
    · simp only [buTK, List.getD_cons_zero, List.getD_cons_succ]
  have hstep16 : Pipe main (sclW) (U :: buWdL p α s t :: buKeysS s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: U :: V1 :: V :: buTK p α s t) (W :: U :: V1 :: V :: buTK p α s t) (Sscl) := by
    exact Pipe.appendTail (U :: V1 :: V :: buTK p α s t) (Pipe.sclStage p α s t hcop.symm
      (fun h1 => hsclGen h1) (u₀ := Jv) hUlen hUV h0s)
  have hstep17 : Pipe main (rollP 3) (W :: U :: V1 :: V :: buTK p α s t) (V :: W :: U :: V1 :: buTK p α s t) (Wc) := by
    refine Pipe.rw (Pipe.rollK (K := KR) (KS := KP + KR + KD + 1) (SEL := buSB p α t) main hroll
      (by omega) (by omega) ?_ ?_ (one_le_buSBK p α t)) ?_
    · simp only [buTK, List.length_cons, List.length_nil]; omega
    · exact hsz17
    · simp only [buTK, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero,
        List.eraseIdx_cons_succ]
  have hstep18 : Pipe main (dropP) (V :: W :: U :: V1 :: buTK p α s t) (W :: U :: V1 :: buTK p α s t) (Wc) := by
    exact Pipe.appendTail (W :: U :: V1 :: buTK p α s t) (Pipe.dropK (K := KD) (KS := KP + KR + KD + 1)
      (SEL := buSB p α t) main hdrop V (by omega) hVsz (one_le_buSBK p α t))
  have hstep19 : Pipe main (rollP 2) (W :: U :: V1 :: buTK p α s t) (V1 :: W :: U :: buTK p α s t) (Wc) := by
    refine Pipe.rw (Pipe.rollK (K := KR) (KS := KP + KR + KD + 1) (SEL := buSB p α t) main hroll
      (by omega) (by omega) ?_ ?_ (one_le_buSBK p α t)) ?_
    · simp only [buTK, List.length_cons, List.length_nil]; omega
    · exact hsz19
    · simp only [buTK, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero,
        List.eraseIdx_cons_succ]
  have hstep20 : Pipe main (dropP) (V1 :: W :: U :: buTK p α s t) (W :: U :: buTK p α s t) (Wc) := by
    exact Pipe.appendTail (W :: U :: buTK p α s t) (Pipe.dropK (K := KD) (KS := KP + KR + KD + 1)
      (SEL := buSB p α t) main hdrop V1 (by omega) hV1sz (one_le_buSBK p α t))
  have hstep21 : Pipe main (rollP 1) (W :: U :: buTK p α s t) (U :: W :: buTK p α s t) (Wc) := by
    refine Pipe.rw (Pipe.rollK (K := KR) (KS := KP + KR + KD + 1) (SEL := buSB p α t) main hroll
      (by omega) (by omega) ?_ ?_ (one_le_buSBK p α t)) ?_
    · simp only [buTK, List.length_cons, List.length_nil]; omega
    · exact hsz21
    · simp only [buTK, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero,
        List.eraseIdx_cons_succ]
  have hstep22 : Pipe main (dropP) (U :: W :: buTK p α s t) (W :: buTK p α s t) (Wc) := by
    exact Pipe.appendTail (W :: buTK p α s t) (Pipe.dropK (K := KD) (KS := KP + KR + KD + 1)
      (SEL := buSB p α t) main hdrop U (by omega) hUsz (one_le_buSBK p α t))
  have hchain : Pipe main (buChainProgK [pickP 3, pickP 8, pickP 2, selW, pickP 2, pickP 5, pickP 13, pickP 3, pickP 4, pickP 17, rndW, pickP 3, pickP 6, pickP 12, pickP 14, pickP 4, sclW, rollP 3, dropP, rollP 2, dropP, rollP 1, dropP]) (V :: buTK p α s t) (W :: buTK p α s t) CSUM :=
    Pipe.comp hstep0 (Pipe.comp hstep1 (Pipe.comp hstep2 (Pipe.comp hstep3 (Pipe.comp hstep4 (Pipe.comp hstep5 (Pipe.comp hstep6 (Pipe.comp hstep7 (Pipe.comp hstep8 (Pipe.comp hstep9 (Pipe.comp hstep10 (Pipe.comp hstep11 (Pipe.comp hstep12 (Pipe.comp hstep13 (Pipe.comp hstep14 (Pipe.comp hstep15 (Pipe.comp hstep16 (Pipe.comp hstep17 (Pipe.comp hstep18 (Pipe.comp hstep19 (Pipe.comp hstep20 (Pipe.comp hstep21 (Pipe.comp hstep22 (Pipe.skipKK KL)))))))))))))))))))))))
  have hpreW : vs = (V :: buTK p α s t) ++ rest := by
    have h := hvs
    rw [buTabList_eq_buTK] at h
    exact h
  have hstepPipe := hchain rest vs hpreW st0 RR hR
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := hstepPipe
  have hcost : CSUM ≤ egCostShape KW p α t Cm := by
    have h1 : CSUM = 20 * Wc + 1 + Ssel + Srnd + Sscl := by
      dsimp only [CSUM, Wc, Ssel, Srnd, Sscl]
      ring
    rw [h1]
    exact buCostK Ksel Krnd Kscl (KP + KR + KD + 1) KW p α s t Cm hs hst hα hp hαp
      hθ hcm le_rfl
  refine ⟨out, s', n, ⟨u, rest, Wv, hvs, ?_, ?_, ?_, ?_⟩, hev, le_trans hn hcost, hstk, hoth⟩
  · rw [hout, ← buTabList_eq_buTK]
    try rfl
  · rw [buPhiL_eq_permL]
    try exact buPermL_congr s t _ _ hcop.symm hcop.symm _
  · exact hWlen
  · exact hWV

end Work.Resample

import Mathlib
import Submission.Work.Resample.buKit

/-!
# Kit for `Work.Resample.buWdElem`

Bookkeeping for the tail `[α,s,t,m,n,π]` of the canonical block (`buTail`), uniform size bounds,
two cost absorbers (`buSZ_add8_le`, `buStepCost`, `buCostFinal`) and the `Pipe` adapters that
assemble the diagonal-weight word from its phases (`spec_to_pipe` converts a `Work.Fx.Spec` into a
`Pipe`; `pipe_to_wordR` is the final conversion back to `WordR`; `buHeadBracket` removes the `ℓ`
entry and duplicates the `p` entry, which is what the Horner call of `buWdElem` needs).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH
open Work.Fx

/-! ## The tail of the canonical block -/

/-- The last six entries `[α,s,t,m,n,π]` of the canonical block `buCB p α s t = [p] ++ buTail`. -/
def buTail (p α s t : ℕ) : List Val :=
  [.int (α : ℤ), .int (s : ℤ), .int (t : ℤ), .int ((egM p α : ℕ) : ℤ),
   .int ((egN p α s t : ℕ) : ℤ), .int (auPi p)]

theorem buCB_eq_cons (p α s t : ℕ) : buCB p α s t = .int (p : ℤ) :: buTail p α s t := rfl

theorem buCB_eq_append (p α s t : ℕ) : buCB p α s t = [.int (p : ℤ)] ++ buTail p α s t := rfl

theorem buTail_length (p α s t : ℕ) : (buTail p α s t).length = 6 := rfl

/-! ## Uniform size bounds -/

theorem isz_p_le_buSZ (p : ℕ) : isz ((p : ℤ)) ≤ buSZ p := by
  refine isz_le_buSZ_of (A := p) (by simp only [buSZ]; omega) ?_
  rw [Int.natAbs_natCast]
  exact le_of_lt (Nat.lt_two_pow_self)

theorem isz_natCast_le_buSZ_lt {p n : ℕ} (h : n < 2 ^ p) : isz ((n : ℤ)) ≤ buSZ p := by
  refine isz_le_buSZ_of (A := p) (by simp only [buSZ]; omega) ?_
  rw [Int.natAbs_natCast]
  exact le_of_lt h

theorem isz_le_buSZ_of_nonneg_lt {p : ℕ} {ℓ : ℤ} {s : ℕ} (h0 : 0 ≤ ℓ) (hs : ℓ < (s : ℤ))
    (hsp : s < 2 ^ p) : isz ℓ ≤ buSZ p := by
  refine isz_le_buSZ_of (A := p) (by simp only [buSZ]; omega) ?_
  refine le_trans (natAbs_le_of ℓ (s : ℤ) (by positivity) (by omega) (by omega)) ?_
  exact le_of_lt hsp

theorem buTail_szl_le (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
    (htp : t < 2 ^ p) (hαp : α ^ 2 < p) : szl (buTail p α s t) ≤ 6 * buSZ p := by
  have hsp : s < 2 ^ p := by omega
  have hα2 : α ^ 2 < p := hαp
  have hαp' : α < p := by nlinarith
  have hαpow : α < 2 ^ p := lt_of_lt_of_le hαp' (le_of_lt (Nat.lt_two_pow_self))
  have h1 : isz ((α : ℤ)) ≤ buSZ p := isz_natCast_le_buSZ_lt hαpow
  have h2 : isz ((s : ℤ)) ≤ buSZ p := isz_natCast_le_buSZ_lt hsp
  have h3 : isz ((t : ℤ)) ≤ buSZ p := isz_natCast_le_buSZ_lt htp
  have h4 : isz ((egM p α : ℕ) : ℤ) ≤ buSZ p := isz_egM_le p α
  have h5 : isz ((egN p α s t : ℕ) : ℤ) ≤ buSZ p := isz_egN_le p α s t (by omega) hsp (by omega)
  have h6 : isz (auPi p) ≤ buSZ p := isz_auPi_le_buSZ p
  simp only [buTail, szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [vsz_int]
  omega

/-! ## Cost absorbers -/

/-- `buSZ p + 8 ≤ (p+1)^8` for `p ≥ 100`. -/
theorem buSZ_add8_le (p : ℕ) (hp : 100 ≤ p) : buSZ p + 8 ≤ (p + 1) ^ 8 := by
  have h : buSZ p + 8 = 80 * p ^ 2 + 6000 * p + 100008 := by simp only [buSZ]; ring
  rw [h, show (p + 1) ^ 8 = (p + 1) ^ 2 * (p + 1) ^ 6 from by ring]
  have h6 : (101 : ℕ) ^ 6 ≤ (p + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have hnum : (101 : ℕ) ^ 6 = 1061520150601 := by norm_num
  have hq : 80 * p ^ 2 + 6000 * p + 100008 ≤ p ^ 2 * (101 : ℕ) ^ 6 := by
    rw [hnum]
    nlinarith [hp]
  have hp2 : p ^ 2 ≤ (p + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  exact le_trans hq (Nat.mul_le_mul hp2 h6)

/-- A chain of at most `256` steps, each costing at most `KS * (buSZ p + 8)^2`. -/
theorem buStepCost {KS p n : ℕ} (hp : 100 ≤ p) (hn : n ≤ 256) :
    n * (KS * (buSZ p + 8) ^ 2) ≤ (256 * KS + 256) * (p + 1) ^ (256 * KS + 256) := by
  have hB1 : 1 ≤ p + 1 := by omega
  have h1 : buSZ p + 8 ≤ (p + 1) ^ 8 := buSZ_add8_le p hp
  have h2 : (buSZ p + 8) ^ 2 ≤ (p + 1) ^ 16 := by
    calc (buSZ p + 8) ^ 2 ≤ ((p + 1) ^ 8) ^ 2 := Nat.pow_le_pow_left h1 2
      _ = (p + 1) ^ 16 := by rw [← pow_mul]
  calc n * (KS * (buSZ p + 8) ^ 2) ≤ 256 * (KS * (p + 1) ^ 16) :=
        Nat.mul_le_mul hn (Nat.mul_le_mul_left KS h2)
    _ = 256 * KS * (p + 1) ^ 16 := by ring
    _ ≤ (256 * KS + 256) * (p + 1) ^ (256 * KS + 256) :=
        Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hB1 (by omega))

/-- The final cost of `buWdElem`: two phase costs `Kz * (p+1)^Kz`, `Kt * (p+1)^Kt`, the Horner cost
`Kh * (p+1)^Kh` and one uniform-cost step (`C` times `2·buSZ p + 1`), absorbed into a single
`K * (p+1)^K`. -/
theorem buCostFinal {Kz Kh Kt C p : ℕ} (hp : 100 ≤ p) :
    Kz * (p + 1) ^ Kz + C * (2 * buSZ p + 1) + Kh * (p + 1) ^ Kh + Kt * (p + 1) ^ Kt
      ≤ 2 ^ (Kz + Kh + Kt + C + 102) * (p + 1) ^ (2 ^ (Kz + Kh + Kt + C + 102)) := by
  set R : ℕ := Kz + Kh + Kt + C with hR
  set B : ℕ := p + 1 with hB
  set M : ℕ := 2 ^ (R + 102) with hM
  have hB1 : 1 ≤ B := by rw [hB]; omega
  have hN : R + 100 ≤ 2 ^ (R + 100) := le_of_lt (Nat.lt_two_pow_self)
  have hNM : 2 ^ (R + 100) ≤ M := by
    rw [hM]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h16M : 16 ≤ M := by
    rw [hM]
    calc (16 : ℕ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (R + 102) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsz : 2 * buSZ p + 1 ≤ B ^ M := by
    have h1 : buSZ p + 8 ≤ B ^ 8 := by rw [hB]; exact buSZ_add8_le p hp
    have h2 : 2 * buSZ p + 1 ≤ (buSZ p + 8) ^ 2 := by
      have h3 := buSZ_ge p
      nlinarith
    have h4 : (buSZ p + 8) ^ 2 ≤ (B ^ 8) ^ 2 := Nat.pow_le_pow_left h1 2
    have h5 : (B ^ 8) ^ 2 = B ^ 16 := by rw [← pow_mul]
    calc 2 * buSZ p + 1 ≤ (buSZ p + 8) ^ 2 := h2
      _ ≤ (B ^ 8) ^ 2 := h4
      _ = B ^ 16 := h5
      _ ≤ B ^ M := Nat.pow_le_pow_right hB1 h16M
  have hkey : ∀ K : ℕ, K ≤ R + 100 → K * B ^ K ≤ 2 ^ (R + 100) * B ^ M := by
    intro K hK
    have hKN : K ≤ 2 ^ (R + 100) := le_trans hK hN
    have hKM : K ≤ M := le_trans hKN hNM
    exact Nat.mul_le_mul hKN (Nat.pow_le_pow_right hB1 hKM)
  have hC' : C * (2 * buSZ p + 1) ≤ 2 ^ (R + 100) * B ^ M :=
    Nat.mul_le_mul (le_trans (by omega) hN) hsz
  have hfour : ∀ a b c d X : ℕ, a ≤ X → b ≤ X → c ≤ X → d ≤ X → a + (b + (c + d)) ≤ 4 * X := by
    intro a b c d X ha hb hc hd
    omega
  have hsum := hfour _ _ _ _ _ (hkey Kz (by omega)) hC' (hkey Kh (by omega)) (hkey Kt (by omega))
  have hgoal : Kz * (p + 1) ^ Kz + C * (2 * buSZ p + 1) + Kh * (p + 1) ^ Kh
      + Kt * (p + 1) ^ Kt
      = Kz * B ^ Kz + (C * (2 * buSZ p + 1) + (Kh * B ^ Kh + Kt * B ^ Kt)) := by
    rw [hB]; ring
  rw [hgoal]
  refine le_trans hsum (le_of_eq ?_)
  rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← mul_assoc, ← pow_add,
    show 2 + (R + 100) = R + 102 from by omega]

/-! ## Adapters -/

/-- A `Spec` on the exact window `A → B` is a `Pipe`. -/
theorem spec_to_pipe {main prog : Cmd} {n : ℕ} {A B : List Val} {C : List Val → ℕ}
    (h : Spec main prog n (fun t => t = A) (fun _ o => o = B) C) (hA : A.length = n) :
    Pipe main prog A B (C A) := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', k, hpost, hev, hk, hstk, hoth⟩ := h A rest hA rfl vs hvs s R hR
  obtain ⟨o, hout, ho⟩ := hpost
  exact ⟨out, s', k, by rw [hout, ho], hev, hk, hstk, hoth⟩

/-- A `Pipe` is a `WordR` with the (redundant) conjunctive postcondition. -/
theorem pipe_to_wordR {main prog : Cmd} {A B : List Val} {c : ℕ} (rest : List Val)
    (h : Pipe main prog A B c) :
    WordR main prog (fun vs => vs = A ++ rest) (fun vs out => vs = A ++ rest ∧ out = B ++ rest)
      (fun _ => c) := by
  intro vs hvs s R hR
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h rest vs hvs s R hR
  exact ⟨out, s', n, ⟨hvs, hout⟩, hev, hn, hstk, hoth⟩

/-- The head-bracketing step: from `[Zb, ℓ, p] ++ V` remove the `ℓ` entry and duplicate the `p`
entry, giving `[Zb, p, p] ++ V`.  (`pick 2`, `swap`, `roll 2`, `drop`.) -/
theorem buHeadBracket (KL : HvdH.KernelLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (Zb ℓ p : HvdH.Val) (V : List HvdH.Val),
      Pipe main prog (Zb :: ℓ :: p :: V) (Zb :: p :: p :: V)
        (K * (vsz Zb + vsz ℓ + vsz p + 1)) := by
  obtain ⟨pickProg, Kpk, hpick⟩ := KL.pick
  obtain ⟨swapProg, Ks, hswap⟩ := KL.swap
  obtain ⟨rollProg, Kr, hroll⟩ := KL.roll
  obtain ⟨dropProg, Kd, hdrop⟩ := KL.drop
  refine ⟨.seq (pickProg 2) (.seq swapProg (.seq (rollProg 2) dropProg)),
    3 * Kpk + Ks + 3 * Kr + Kd, ?_⟩
  intro main Zb ℓ p V
  -- step 1: copy `p` (position 2) to the top
  have s1 : Pipe main (pickProg 2) (Zb :: ℓ :: p :: V) (p :: Zb :: ℓ :: p :: V)
      (Kpk * 3 * (vsz Zb + vsz ℓ + vsz p + 1)) := by
    have h := Pipe.pickAt (prog := pickProg) (K := Kpk) main hpick
      (A := [Zb, ℓ, p] ++ V) (k := 2) (v := p) (by simp) (by simp)
    refine Pipe.le h ?_
    have hsz : szl (([Zb, ℓ, p] ++ V).take (2 + 1)) = vsz Zb + vsz ℓ + vsz p := by
      rw [show ([Zb, ℓ, p] ++ V).take 3 = [Zb, ℓ, p] from by simp, szl]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega
    rw [hsz]
  -- step 2: swap to bring `Zb` back on top
  have s2 : Pipe main swapProg (p :: Zb :: ℓ :: p :: V) (Zb :: p :: ℓ :: p :: V)
      (Ks * (vsz Zb + vsz ℓ + vsz p + 1)) := by
    have h := Pipe.appendTail ([ℓ, p] ++ V) (Pipe.swap main hswap p Zb)
    refine Pipe.le h ?_
    exact Nat.mul_le_mul_left _ (by omega)
  -- step 3: roll `ℓ` (position 2) to the top
  have s3 : Pipe main (rollProg 2) (Zb :: p :: ℓ :: p :: V) (ℓ :: Zb :: p :: p :: V)
      (Kr * 3 * (vsz Zb + vsz ℓ + vsz p + 1)) := by
    have h := Pipe.roll (prog := rollProg) (K := Kr) main hroll
      (A := [Zb, p, ℓ, p] ++ V) (k := 2) (by simp)
    refine Pipe.le (Pipe.rw h ?_) ?_
    · rw [show ([Zb, p, ℓ, p] ++ V).getD 2 .nil = ℓ from by simp,
        show ([Zb, p, ℓ, p] ++ V).eraseIdx 2 = [Zb, p, p] ++ V from by simp]
      rfl
    · have hsz : szl (([Zb, p, ℓ, p] ++ V).take (2 + 1)) = vsz Zb + vsz ℓ + vsz p := by
        rw [show ([Zb, p, ℓ, p] ++ V).take 3 = [Zb, p, ℓ] from by simp, szl]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        omega
      rw [hsz]
  -- step 4: drop the `ℓ` now on top
  have s4 : Pipe main dropProg (ℓ :: Zb :: p :: p :: V) (Zb :: p :: p :: V)
      (Kd * (vsz Zb + vsz ℓ + vsz p + 1)) := by
    have h := Pipe.appendTail ([Zb, p, p] ++ V) (Pipe.drop main hdrop ℓ)
    refine Pipe.le h ?_
    exact Nat.mul_le_mul_left _ (by omega)
  refine Pipe.le (Pipe.comp s1 (Pipe.comp s2 (Pipe.comp s3 s4))) ?_
  exact le_of_eq (by ring)

end Work.Resample

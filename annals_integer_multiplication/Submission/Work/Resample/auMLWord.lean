import Mathlib
import Submission.Work.Resample.auKit

/-!
# `auM`/`auL` from `p` and `α`: the window parameters of the Gaussian resampling word

`auMLWord` builds the word that computes the window half-width `auM p α = (⌈√p⌉)·α` and the
window length `auL p α = 2·auM p α + 1` from the two integer values `p`, `α` on top of the value
stack.  The program is the chain

`(√p + 1) · α`  (integer sqrt, push 1, add, schoolbook multiply), then `2·(that) + 1`
(duplicate, push 2, multiply, push 1, add) and finally a swap, so that the two results appear in
the order `auM`, `auL`.  The cost is the sum of the library costs of these eight words, each of
which is bounded by the uniform per-step bound `auSB p Kl` of `auKit`; the total is at most
`10 · auSB p Kl ≤ K · (p+1)^K` for `K = 1960·Kl + 4`, where `Kl` is the sum of the constants of
the six library words used.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH

/-- `isz` of a natural-cast integer is at most the number plus two. -/
lemma isz_cast_le_add_two (n : ℕ) : isz ((n : ℤ)) ≤ n + 2 := by
  simp only [isz, Int.natAbs_natCast]
  have := Nat.size_le.mpr (Nat.lt_two_pow_self (n := n))
  omega

theorem auMLWord (hk : HvdH.KernelLib) (hi : HvdH.IntLib) : ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (p α : ℕ), 100 ≤ p → α ^ 2 < p →
    Work.Resample.Pipe main prog [HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ)]
      [HvdH.Val.int ((Work.Resample.auM p α : ℕ) : ℤ), HvdH.Val.int ((Work.Resample.auL p α : ℕ) : ℤ)]
      (K * (p + 1) ^ K) := by
  obtain ⟨sqProg, Ks, hSq⟩ := hi.sqrt
  obtain ⟨addProg, Ka, hAdd⟩ := hi.add
  obtain ⟨mulProg, Km, hMul⟩ := hi.mulS
  obtain ⟨dupProg, Kd, hDup⟩ := hk.dup
  obtain ⟨swpProg, Kw, hSwp⟩ := hk.swap
  obtain ⟨pushProg, Kp, hPush⟩ := hk.pushVal
  let Kl : ℕ := Ks + Ka + Km + Kd + Kw + Kp
  let K : ℕ := 1960 * Kl + 4
  let P : Cmd := .seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq sqProg (pushProg (.int 1)))
    addProg) mulProg) dupProg) (pushProg (.int 2))) mulProg) (pushProg (.int 1))) addProg) swpProg
  refine ⟨P, K, ?_⟩
  intro main p α hp hαp
  let X : ℤ := (1 + (Nat.sqrt p : ℤ)) * (α : ℤ)
  have hp0 : (0:ℤ) ≤ (p:ℤ) := Int.natCast_nonneg p
  have s1 : Pipe main sqProg [Val.int (p:ℤ)] [Val.int ((Nat.sqrt p : ℕ) : ℤ)]
      (Ks * isz (p:ℤ)^2) := by
    have h := Pipe.unOp (hSq main) hp0
    simpa using h
  have s1x : Pipe main sqProg [Val.int (p:ℤ), Val.int (α:ℤ)]
      [Val.int ((Nat.sqrt p : ℕ) : ℤ), Val.int (α:ℤ)] (Ks * isz (p:ℤ)^2) :=
    Pipe.appendTail [Val.int (α:ℤ)] s1
  have s2 : Pipe main (pushProg (.int 1))
      [Val.int ((Nat.sqrt p : ℕ) : ℤ), Val.int (α:ℤ)]
      (Val.int (1:ℤ) :: [Val.int ((Nat.sqrt p : ℕ) : ℤ), Val.int (α:ℤ)])
      (Kp * (vsz (Val.int (1:ℤ)) + 1)) :=
    Pipe.pushOnAny (T := [Val.int ((Nat.sqrt p : ℕ) : ℤ), Val.int (α:ℤ)]) (hPush main (.int 1))
  have s3 : Pipe main addProg
      (Val.int (1:ℤ) :: [Val.int ((Nat.sqrt p : ℕ) : ℤ), Val.int (α:ℤ)])
      [Val.int (1 + (Nat.sqrt p : ℤ)), Val.int (α:ℤ)]
      (Ka * (isz (1:ℤ) + isz ((Nat.sqrt p : ℕ) : ℤ))) :=
    Pipe.appendTail [Val.int (α:ℤ)]
      (Pipe.binOp (hAdd main) (a := (1:ℤ)) (b := ((Nat.sqrt p : ℕ) : ℤ)) trivial)
  have s4 : Pipe main mulProg
      [Val.int (1 + (Nat.sqrt p : ℤ)), Val.int (α:ℤ)] [Val.int X]
      (Km * isz (1 + (Nat.sqrt p : ℤ)) * isz (α:ℤ)) :=
    Pipe.binOp (hMul main) (a := 1 + (Nat.sqrt p : ℤ)) (b := (α:ℤ)) trivial
  have s5 : Pipe main dupProg [Val.int X] [Val.int X, Val.int X]
      (Kd * (vsz (Val.int X) + 1)) :=
    Pipe.dup main hDup (Val.int X)
  have s6 : Pipe main (pushProg (.int 2)) [Val.int X, Val.int X]
      (Val.int (2:ℤ) :: [Val.int X, Val.int X])
      (Kp * (vsz (Val.int (2:ℤ)) + 1)) :=
    Pipe.pushOnAny (T := [Val.int X, Val.int X]) (hPush main (.int 2))
  have s7 : Pipe main mulProg
      (Val.int (2:ℤ) :: [Val.int X, Val.int X]) [Val.int (2*X), Val.int X]
      (Km * isz (2:ℤ) * isz X) :=
    Pipe.appendTail [Val.int X]
      (Pipe.binOp (hMul main) (a := (2:ℤ)) (b := X) trivial)
  have s8 : Pipe main (pushProg (.int 1)) [Val.int (2*X), Val.int X]
      (Val.int (1:ℤ) :: [Val.int (2*X), Val.int X])
      (Kp * (vsz (Val.int (1:ℤ)) + 1)) :=
    Pipe.pushOnAny (T := [Val.int (2*X), Val.int X]) (hPush main (.int 1))
  have s9 : Pipe main addProg
      (Val.int (1:ℤ) :: [Val.int (2*X), Val.int X]) [Val.int (1 + 2*X), Val.int X]
      (Ka * (isz (1:ℤ) + isz (2*X))) :=
    Pipe.appendTail [Val.int X]
      (Pipe.binOp (hAdd main) (a := (1:ℤ)) (b := 2*X) trivial)
  have s10 : Pipe main swpProg [Val.int (1 + 2*X), Val.int X] [Val.int X, Val.int (1 + 2*X)]
      (Kw * (vsz (Val.int (1 + 2*X)) + vsz (Val.int X) + 1)) :=
    Pipe.swap main hSwp (Val.int (1 + 2*X)) (Val.int X)
  have hchain : Pipe main P [Val.int (p:ℤ), Val.int (α:ℤ)] [Val.int X, Val.int (1 + 2*X)] _ :=
    Pipe.comp (Pipe.comp (Pipe.comp (Pipe.comp (Pipe.comp (Pipe.comp (Pipe.comp (Pipe.comp (Pipe.comp
      s1x s2) s3) s4) s5) s6) s7) s8) s9) s10
  have hW : [Val.int X, Val.int (1 + 2 * X)] =
      [Val.int ((auM p α : ℕ) : ℤ), Val.int ((auL p α : ℕ) : ℤ)] := by
    have h1 : X = ((auM p α : ℕ) : ℤ) := by simp only [X, auM]; push_cast; ring
    have h2 : (1 + 2 * X) = ((auL p α : ℕ) : ℤ) := by rw [h1]; simp only [auL]; push_cast; ring
    rw [h2, h1]
  refine Pipe.le (Pipe.rw hchain hW) ?_
  -- size bounds for the intermediate values
  have hαle : α ≤ Nat.sqrt p := by
    rw [Nat.le_sqrt]
    calc α * α = α ^ 2 := by ring
      _ ≤ p := le_of_lt hαp
  have hsle : Nat.sqrt p ≤ p := Nat.sqrt_le_self p
  have hss : Nat.sqrt p * Nat.sqrt p ≤ p := Nat.sqrt_le p
  have hXval : X = (((Nat.sqrt p + 1) * α : ℕ) : ℤ) := by simp only [X]; push_cast; ring
  have hXn : X.natAbs = (Nat.sqrt p + 1) * α := by rw [hXval, Int.natAbs_natCast]
  have hXnle : X.natAbs ≤ 2 * p := by
    rw [hXn]
    nlinarith [hαle, hsle, hss]
  have hszp : isz (p:ℤ) ≤ auSZ p :=
    le_trans (isz_cast_le_add_two p) (by simp only [auSZ]; omega)
  have hszs : isz ((Nat.sqrt p : ℕ) : ℤ) ≤ auSZ p :=
    le_trans (isz_cast_le_add_two (Nat.sqrt p)) (by simp only [auSZ]; omega)
  have hsza : isz (α:ℤ) ≤ auSZ p :=
    le_trans (isz_cast_le_add_two α) (by simp only [auSZ]; omega)
  have hsz1 : isz (1:ℤ) ≤ auSZ p :=
    le_trans (isz_cast_le_add_two 1) (by simp only [auSZ]; omega)
  have hsz2 : isz (2:ℤ) ≤ auSZ p :=
    le_trans (isz_cast_le_add_two 2) (by simp only [auSZ]; omega)
  have hszS1 : isz (1 + (Nat.sqrt p : ℤ)) ≤ auSZ p := by
    have he : (1 + (Nat.sqrt p : ℤ)) = (((1 + Nat.sqrt p) : ℕ) : ℤ) := by push_cast; ring
    rw [he]
    exact le_trans (isz_cast_le_add_two (1 + Nat.sqrt p)) (by simp only [auSZ]; omega)
  have hszX : isz X ≤ auSZ p := by
    rw [hXval]
    refine le_trans (isz_cast_le_add_two ((Nat.sqrt p + 1) * α)) ?_
    simp only [auSZ]; omega
  have hsz2X : isz (2*X) ≤ auSZ p := by
    have h2Xval : (2*X : ℤ) = ((2 * ((Nat.sqrt p + 1) * α) : ℕ) : ℤ) := by
      simp only [X]; push_cast; ring
    rw [h2Xval]
    refine le_trans (isz_cast_le_add_two (2 * ((Nat.sqrt p + 1) * α))) ?_
    simp only [auSZ]; omega
  have hszY : isz (1 + 2*X) ≤ auSZ p := by
    have hYval : (1 + 2*X : ℤ) = ((1 + 2 * ((Nat.sqrt p + 1) * α) : ℕ) : ℤ) := by
      simp only [X]; push_cast; ring
    rw [hYval]
    refine le_trans (isz_cast_le_add_two (1 + 2 * ((Nat.sqrt p + 1) * α))) ?_
    simp only [auSZ]; omega
  -- each of the ten library words costs at most the uniform step bound `auSB p Kl`
  have hKs : Ks ≤ Kl := by simp only [Kl]; omega
  have hKa : Ka ≤ Kl := by simp only [Kl]; omega
  have hKm : Km ≤ Kl := by simp only [Kl]; omega
  have hKd : Kd ≤ Kl := by simp only [Kl]; omega
  have hKw : Kw ≤ Kl := by simp only [Kl]; omega
  have hKp : Kp ≤ Kl := by simp only [Kl]; omega
  have e1 : Ks * isz (p:ℤ)^2 ≤ auSB p Kl := au_le_sq hKs hszp
  have e2 : Kp * (vsz (Val.int (1:ℤ)) + 1) ≤ auSB p Kl := by
    rw [Work.Fx.vsz_int]; exact au_le_one hKp hsz1
  have e3 : Ka * (isz (1:ℤ) + isz ((Nat.sqrt p : ℕ) : ℤ)) ≤ auSB p Kl :=
    au_le_two hKa hsz1 hszs
  have e4 : Km * isz (1 + (Nat.sqrt p : ℤ)) * isz (α:ℤ) ≤ auSB p Kl := by
    have hle' : isz (1 + (Nat.sqrt p : ℤ)) * isz (α:ℤ) ≤ auSZ p * auSZ p :=
      Nat.mul_le_mul hszS1 hsza
    have hle : isz (1 + (Nat.sqrt p : ℤ)) * isz (α:ℤ) ≤ (auSZ p)^2 := by
      rw [pow_two]; exact hle'
    calc Km * isz (1 + (Nat.sqrt p : ℤ)) * isz (α:ℤ)
        = Km * (isz (1 + (Nat.sqrt p : ℤ)) * isz (α:ℤ)) := by ring
      _ ≤ Km * (auSZ p)^2 := Nat.mul_le_mul_left Km hle
      _ ≤ auSB p Kl := au_le_sq hKm (le_refl (auSZ p))
  have e5 : Kd * (vsz (Val.int X) + 1) ≤ auSB p Kl := by
    rw [Work.Fx.vsz_int]; exact au_le_one hKd hszX
  have e6 : Kp * (vsz (Val.int (2:ℤ)) + 1) ≤ auSB p Kl := by
    rw [Work.Fx.vsz_int]; exact au_le_one hKp hsz2
  have e7 : Km * isz (2:ℤ) * isz X ≤ auSB p Kl := by
    have hle' : isz (2:ℤ) * isz X ≤ auSZ p * auSZ p := Nat.mul_le_mul hsz2 hszX
    have hle : isz (2:ℤ) * isz X ≤ (auSZ p)^2 := by rw [pow_two]; exact hle'
    calc Km * isz (2:ℤ) * isz X = Km * (isz (2:ℤ) * isz X) := by ring
      _ ≤ Km * (auSZ p)^2 := Nat.mul_le_mul_left Km hle
      _ ≤ auSB p Kl := au_le_sq hKm (le_refl (auSZ p))
  have e9 : Ka * (isz (1:ℤ) + isz (2*X)) ≤ auSB p Kl := au_le_two hKa hsz1 hsz2X
  have e10 : Kw * (vsz (Val.int (1 + 2*X)) + vsz (Val.int X) + 1) ≤ auSB p Kl := by
    rw [Work.Fx.vsz_int, Work.Fx.vsz_int]
    exact au_le_three hKw hszY hszX (by simp only [auSZ]; omega)
  -- total cost bound
  have h2 : 10 * auSB p Kl ≤ K * (p + 1) ^ K := by
    have hAU : auSZ p + 8 ≤ 14 * (p + 1) := by simp only [auSZ]; omega
    have hKge : 4 ≤ K := by simp only [K]; omega
    rw [auSB]
    calc 10 * (Kl * (auSZ p + 8) ^ 2) = 10 * Kl * (auSZ p + 8)^2 := by ring
      _ ≤ 10 * Kl * (14 * (p+1))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hAU 2)
      _ = 1960 * Kl * (p+1)^2 := by ring
      _ ≤ (1960 * Kl + 4) * (p+1)^4 := by
          apply Nat.mul_le_mul
          · omega
          · exact Nat.pow_le_pow_right (by omega) (by omega : 2 ≤ 4)
      _ ≤ (1960 * Kl + 4) * (p+1)^K := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hKge)
      _ = K * (p+1)^K := by simp only [K]
  omega

end Work.Resample

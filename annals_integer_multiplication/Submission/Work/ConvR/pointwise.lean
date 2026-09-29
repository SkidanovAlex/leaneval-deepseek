import Mathlib
import Submission.Work.ConvR.basic
import Submission.Work.ConvR.pwdefs
import Submission.Work.ConvR.reorderArr
import Submission.Work.ConvR.dropUnder
import Submission.Work.ConvR.arrSzLe
import Submission.Work.ConvR.pwCost
import Submission.Work.Kernel.Raw

/-!
# ConvR: the pointwise-product step of Proposition 3.4

`Work.ConvR.pointwise` maps the Kronecker word of Lemma 2.5 (`Work.ConvR.KroneckerSpec`) over the
`M` coefficient-vector pairs of two arrays `As`, `Bs ∈ (C̃◦^r)^M`, producing `Zs ∈ (C̃◦^r)^M` with

  `2^p * ‖Zs[i][j] - (1/r) * (As[i] * Bs[i])[j]‖ < 2`   for all `i < M`, `j < r`,

at cost `4 * M * Cm (3*r*p) + K * (M*r+1) * p^2 + K`.

The program first rotates `p, r` below the two arrays (`reorderArr`), then runs
`KernelLib.zipWith` over the two arrays with the wrapped Kronecker word `pwElem` (`pick 2; pick 4;
swap; Kronecker`), and finally drops the two saved integers (`dropUnder`).

-/

set_option autoImplicit false

namespace Work.ConvR

open HvdH
open Work.Kernel

/-! ## size helpers -/

theorem vsz_ofList_le {zs : List Val} {L : ℕ} (h : ∀ z ∈ zs, vsz z ≤ L) :
    vsz (ofList zs) ≤ zs.length * L + zs.length + 1 := by
  rw [vsz_ofList]
  have hs : (zs.map vsz).sum ≤ zs.length * L := by
    have := List.sum_le_sum (fun z hz => h z hz)
    rwa [sum_map_const] at this
  omega

theorem isz_natCast_le_self (n : ℕ) : isz (n : ℤ) ≤ n + 3 := by
  have h : n.size ≤ n + 1 :=
    Nat.size_le.mpr (Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ n)))
  simp only [isz, Int.natAbs_natCast]
  omega

theorem isz_natCast_le_of_lt {r p : ℕ} (hr : 2 ≤ r) (h : r < 2 ^ (p - 1)) :
    isz (r : ℤ) ≤ p + 1 := by
  have h2 : (2:ℕ) ≤ 2 ^ (p - 1) := le_trans hr h.le
  have hp1 : 1 ≤ p := by
    by_contra hc
    have hp0 : p = 0 := by omega
    subst hp0
    simp at h2
  have hrs : r.size ≤ p - 1 := Nat.size_le.mpr h
  simp only [isz, Int.natAbs_natCast]
  omega

/-! ## extraction -/

theorem extractAux {p M r : ℕ} {As Bs : List (List (ℤ × ℤ))} {zs : List Val}
    (hA : As.length = M) (hB : Bs.length = M) (hlen : zs.length = M)
    (hQ : ∀ i < M, PWq p r ((As.map cvecVal).getD i .nil) ((Bs.map cvecVal).getD i .nil) (zs.getD i .nil)) :
    ∃ Zs : List (List (ℤ × ℤ)), ofList zs = rarrVal Zs ∧ InDiscArr p M r Zs ∧
      ∀ (i : Fin M) (j : Fin r), (2 : ℝ) ^ p *
        ‖fxC p ((Zs.getD i []).getD j (0, 0)) -
          ((r : ℂ))⁻¹ * negaMul r (fxArr p M r As i) (fxArr p M r Bs i) j‖ < 2 := by
  classical
  let W : Fin M → List (ℤ × ℤ) := fun i => (hQ i i.isLt).choose
  have hWz : ∀ i : Fin M, zs.getD (i:ℕ) .nil = cvecVal (W i) := by
    intro i; exact PWq.eq (hQ i i.isLt)
  have hWspec : ∀ i : Fin M, ∃ u v, (As.map cvecVal).getD (i:ℕ) .nil = cvecVal u ∧
      (Bs.map cvecVal).getD (i:ℕ) .nil = cvecVal v ∧ InDiscVec p r (W i) ∧
      ∀ j : Fin r, (2:ℝ)^p * ‖fxC p ((W i).getD j (0,0)) -
        ((r:ℂ))⁻¹ * negaMul r (fxVec p r u) (fxVec p r v) j‖ < 2 := by
    intro i; exact PWq.spec (hQ i i.isLt)
  refine ⟨List.ofFn W, ?_, ?_, ?_⟩
  · have hrw : rarrVal (List.ofFn W) = ofList (List.ofFn (fun i : Fin M => cvecVal (W i))) := by
      rw [rarrVal, List.map_ofFn]
      congr 1
    rw [hrw]
    congr 1
    apply List.ext_getElem
    · simp [List.length_ofFn, hlen]
    · intro i h1 h2
      have h3 : i < M := by simpa [List.length_ofFn] using h2
      rw [List.getElem_ofFn]
      show zs[i] = cvecVal (W ⟨i, h3⟩)
      rw [← hWz ⟨i, h3⟩, List.getD_eq_getElem _ _ h1]
  · constructor
    · simp [List.length_ofFn, hlen]
    · intro w hw
      rw [List.mem_ofFn] at hw
      obtain ⟨i, rfl⟩ := hw
      obtain ⟨u, v, -, -, hInD, -⟩ := hWspec i
      exact hInD
  · intro i j
    obtain ⟨u, v, hu, hv, hInD, herr⟩ := hWspec i
    have hZsi : (List.ofFn W).getD (i:ℕ) [] = W i := by
      rw [List.getD_eq_getElem _ _ (by simp [List.length_ofFn]), List.getElem_ofFn]
    rw [hZsi]
    have hu' : u = As.getD (i:ℕ) [] := by
      have h1 : (As.map cvecVal).getD (i:ℕ) .nil = cvecVal (As.getD (i:ℕ) []) :=
        cvecVal_getD (by rw [hA]; exact i.isLt)
      rw [hu] at h1
      exact cvecVal_injective h1
    have hv' : v = Bs.getD (i:ℕ) [] := by
      have h1 : (Bs.map cvecVal).getD (i:ℕ) .nil = cvecVal (Bs.getD (i:ℕ) []) :=
        cvecVal_getD (by rw [hB]; exact i.isLt)
      rw [hv] at h1
      exact cvecVal_injective h1
    rw [hu', hv'] at herr
    have e1 : fxVec p r (As.getD (i:ℕ) []) = fxArr p M r As i := rfl
    have e2 : fxVec p r (Bs.getD (i:ℕ) []) = fxArr p M r Bs i := rfl
    rw [e1, e2] at herr
    exact herr j

theorem le_mul_X (a r : ℕ) : a ≤ (r+1)*a := by
  calc a = a*1 := (Nat.mul_one a).symm
    _ ≤ a*(r+1) := Nat.mul_le_mul_left a (by omega)
    _ = (r+1)*a := by ring

theorem cvecSzBound (r p : ℕ) : cvecSz p r ≤ 12 * ((r+1)*(p+1)^2) := by
  have hrp : r * p ≤ (r + 1) * (p + 1) ^ 2 := by
    calc r * p ≤ (r + 1) * p := Nat.mul_le_mul_right p (Nat.le_succ r)
      _ ≤ (r + 1) * (p + 1) := Nat.mul_le_mul_left (r + 1) (Nat.le_succ p)
      _ ≤ (r + 1) * (p + 1) * (p + 1) :=
          Nat.le_mul_of_pos_right ((r + 1) * (p + 1)) (Nat.succ_pos p)
      _ = (r + 1) * (p + 1) ^ 2 := by ring
  have hr : r ≤ (r + 1) * (p + 1) ^ 2 := by
    calc r = r * 1 := (Nat.mul_one r).symm
      _ ≤ r * (p + 1) ^ 2 := Nat.mul_le_mul_left r (Nat.one_le_pow 2 (p+1) (Nat.succ_pos p))
      _ ≤ (r + 1) * (p + 1) ^ 2 := Nat.mul_le_mul_right _ (Nat.le_succ r)
  have h1 : 1 ≤ (r + 1) * (p + 1) ^ 2 :=
    le_trans (Nat.one_le_pow 2 (p+1) (Nat.succ_pos p)) (le_mul_X ((p+1)^2) r)
  have hc : cvecSz p r = 2 * (r * p) + 9 * r + 1 := by simp only [cvecSz, cfxSz]; ring
  set X := (r + 1) * (p + 1) ^ 2 with hX
  have hc' : cvecSz p r ≤ 12 * X := by
    rw [hc]
    have hrpX : r * p ≤ X := by rw [hX]; exact hrp
    have hrX : r ≤ X := by rw [hX]; exact hr
    have h1X : 1 ≤ X := by rw [hX]; exact h1
    have h2 := Nat.mul_le_mul_left 2 hrpX
    have h9 := Nat.mul_le_mul_left 9 hrX
    omega
  rw [hX] at hc'
  exact hc'

theorem pwCostElem (PK SK KronK r p vszx vszy iszp iszr : ℕ) (hr : 1 ≤ r) (hp : 1 ≤ p)
    (hx : vszx ≤ 12 * ((r+1)*(p+1)^2)) (hy : vszy ≤ 12 * ((r+1)*(p+1)^2))
    (hpz : iszp ≤ 4 * ((r+1)*(p+1)^2)) (hrz : iszr ≤ 2 * ((r+1)*(p+1)^2)) :
    PK * 3 * (vszx + vszy + iszp + 1) + PK * 5 * (iszp + vszx + vszy + iszp + iszr + 1)
      + SK * (iszr + iszp + 1) + KronK * ((r+1)*(p+1)^2)
    ≤ (KronK + 280 * PK + 7 * SK + 1) * (r + 1) * (p + 1) ^ 2 := by
  set X := (r+1)*(p+1)^2 with hX
  have hx' : vszx ≤ 12 * X := by rw [hX]; exact hx
  have hy' : vszy ≤ 12 * X := by rw [hX]; exact hy
  have hpz' : iszp ≤ 4 * X := by rw [hX]; exact hpz
  have hrz' : iszr ≤ 2 * X := by rw [hX]; exact hrz
  have hX1 : 1 ≤ X := by rw [hX]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h1 : vszx + vszy + iszp + 1 ≤ 29 * X := by linarith
  have h2 : iszp + vszx + vszy + iszp + iszr + 1 ≤ 35 * X := by linarith
  have h3 : iszr + iszp + 1 ≤ 7 * X := by linarith
  have e1 : PK * 3 * (vszx + vszy + iszp + 1) ≤ PK * 3 * (29 * X) :=
    Nat.mul_le_mul_left (PK * 3) h1
  have e2 : PK * 5 * (iszp + vszx + vszy + iszp + iszr + 1) ≤ PK * 5 * (35 * X) :=
    Nat.mul_le_mul_left (PK * 5) h2
  have e3 : SK * (iszr + iszp + 1) ≤ SK * (7 * X) := Nat.mul_le_mul_left SK h3
  have hsum : PK * 3 * (vszx + vszy + iszp + 1) + PK * 5 * (iszp + vszx + vszy + iszp + iszr + 1)
      + SK * (iszr + iszp + 1) + KronK * X
      ≤ PK * 3 * (29 * X) + PK * 5 * (35 * X) + SK * (7 * X) + KronK * X :=
    add_le_add (add_le_add (add_le_add e1 e2) e3) le_rfl
  refine le_trans hsum ?_
  have heq : PK * 3 * (29 * X) + PK * 5 * (35 * X) + SK * (7 * X) + KronK * X
      = (KronK + 262 * PK + 7 * SK) * X := by ring
  rw [heq]
  have hgoal : (KronK + 280 * PK + 7 * SK + 1) * (r + 1) * (p + 1) ^ 2
      = (KronK + 280 * PK + 7 * SK + 1) * X := by rw [hX]; ring
  rw [hgoal]
  exact Nat.mul_le_mul_right X (by omega)

theorem WordC.pickEq (hK : KernelLib) {main : Cmd} {pickP : ℕ → Cmd} {PK : ℕ}
    (hpick : ∀ (main : Cmd) (k : ℕ), WordR main (pickP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => PK * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {L L' : List Val} {k C : ℕ} (hk : k < L.length)
    (hL' : L.getD k .nil :: L = L')
    (hC : PK * (k + 1) * (((L.take (k + 1)).map vsz).sum + 1) ≤ C) :
    WordC main (pickP k) (fun vs => vs = L) (fun _ out => out = L') C := by
  refine hK.conseq main (pickP k) (fun vs => k < vs.length) (fun vs => vs = L)
    (fun vs out => out = vs.getD k .nil :: vs) (fun _ out => out = L')
    (fun vs => PK * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)) (fun _ => C)
    (hpick main k) ?_ ?_ ?_
  · intro vs hvs; rw [hvs]; exact hk
  · intro vs out hvs hQ; rw [hvs] at hQ; rw [hQ, hL']
  · intro vs hvs; rw [hvs]; exact hC

theorem pwElemLocal (hK : KernelLib) (hkr : KroneckerSpec) :
    ∃ (q : Cmd) (K : ℕ), ∀ (main : Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm →
      MulBelow main N Cm → ∀ (p r : ℕ), 2 ≤ r → IsPow2 r → r < 2 ^ (p - 1) → 3 * r * p < N →
      ∀ (x y : Val) (rest : List Val), PWp p r x y →
        WordC main q (fun vs => vs = x :: y :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest)
          (fun _ out => ∃ z, out = z :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest ∧ PWq p r x y z ∧ vsz z ≤ cvecSz p r)
          (4 * Cm (3*r*p) + K * (r+1) * (p+1)^2) := by
  obtain ⟨kronP, KronK, hkron⟩ := hkr
  obtain ⟨pickP, PK, hpick⟩ := hK.pick
  obtain ⟨swapP, SK, hswap⟩ := hK.swap
  refine ⟨.seq (.seq (.seq (pickP 2) (pickP 4)) swapP) kronP, KronK + 280 * PK + 7 * SK + 1, ?_⟩
  intro main N Cm hmon hmul p r hr hpow hlt hN x y rest hxy
  obtain ⟨u, v, hxu, hyv, hdu, hdv⟩ := hxy
  have hxy : PWp p r x y := ⟨u, v, hxu, hyv, hdu, hdv⟩
  have hr1 : 1 ≤ r := by omega
  have hp1 : 1 ≤ p := by
    have h2 : (2:ℕ) ≤ 2 ^ (p - 1) := le_trans hr hlt.le
    by_contra hc
    have hp0 : p = 0 := by omega
    subst hp0
    simp at h2
  have hxX : vsz x ≤ 12 * ((r+1)*(p+1)^2) := le_trans (PWp.vsz_le hxy).1 (cvecSzBound r p)
  have hyX : vsz y ≤ 12 * ((r+1)*(p+1)^2) := le_trans (PWp.vsz_le hxy).2 (cvecSzBound r p)
  have hpzX : isz (p:ℤ) ≤ 4 * ((r+1)*(p+1)^2) := by
    have h1 : (p+1)^2 ≤ (r+1)*(p+1)^2 := le_mul_X ((p+1)^2) r
    calc isz (p:ℤ) ≤ p + 3 := isz_natCast_le_self p
      _ ≤ 4 * (p+1)^2 := by nlinarith
      _ ≤ 4 * ((r+1)*(p+1)^2) := Nat.mul_le_mul_left 4 h1
  have hrzX : isz (r:ℤ) ≤ 2 * ((r+1)*(p+1)^2) := by
    have h1 : (p+1) ≤ (r+1)*(p+1)^2 := by
      have h2 : p+1 ≤ (p+1)^2 := by simpa [pow_two] using Nat.le_mul_self (p+1)
      exact le_trans h2 (le_mul_X ((p+1)^2) r)
    calc isz (r:ℤ) ≤ p + 1 := isz_natCast_le_of_lt hr hlt
      _ ≤ (r+1)*(p+1)^2 := h1
      _ ≤ 2 * ((r+1)*(p+1)^2) := by
          calc (r+1)*(p+1)^2 = ((r+1)*(p+1)^2) * 1 := (Nat.mul_one _).symm
            _ ≤ ((r+1)*(p+1)^2) * 2 := Nat.mul_le_mul_left _ (by norm_num)
            _ = 2 * ((r+1)*(p+1)^2) := by ring
  have step1 : WordR main (pickP 2)
      (fun vs => vs = x :: y :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest)
      (fun _ out => out = Val.int (p:ℤ) :: x :: y :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest)
      (fun _ => PK * 3 * (vsz x + vsz y + isz (p:ℤ) + 1)) := by
    refine WordC.pickEq hK hpick (k := 2)
      (L := x :: y :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest)
      (L' := Val.int (p:ℤ) :: x :: y :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest)
      (C := PK * 3 * (vsz x + vsz y + isz (p:ℤ) + 1)) ?_ ?_ ?_
    · simp
    · simp
    · have hsum : (((x :: y :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest).take 3).map vsz).sum + 1
          = vsz x + vsz y + isz (p:ℤ) + 1 := by simp [vsz_int] <;> ring
      calc PK * (2 + 1) * ((((x :: y :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest).take 3).map vsz).sum + 1)
          = PK * (2 + 1) * (vsz x + vsz y + isz (p:ℤ) + 1) := by rw [hsum]
        _ ≤ PK * 3 * (vsz x + vsz y + isz (p:ℤ) + 1) := Nat.mul_le_mul_right _ (le_refl _)
  have step2 : WordR main (pickP 4)
      (fun vs => vs = Val.int (p:ℤ) :: x :: y :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest)
      (fun _ out => out = Val.int (r:ℤ) :: Val.int (p:ℤ) :: x :: y :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest)
      (fun _ => PK * 5 * (isz (p:ℤ) + vsz x + vsz y + isz (p:ℤ) + isz (r:ℤ) + 1)) := by
    refine WordC.pickEq hK hpick (k := 4)
      (L := Val.int (p:ℤ) :: x :: y :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest)
      (L' := Val.int (r:ℤ) :: Val.int (p:ℤ) :: x :: y :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest)
      (C := PK * 5 * (isz (p:ℤ) + vsz x + vsz y + isz (p:ℤ) + isz (r:ℤ) + 1)) ?_ ?_ ?_
    · simp
    · simp
    · have hsum : (((Val.int (p:ℤ) :: x :: y :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest).take 5).map vsz).sum + 1
          = isz (p:ℤ) + vsz x + vsz y + isz (p:ℤ) + isz (r:ℤ) + 1 := by simp [vsz_int] <;> ring
      calc PK * (4 + 1) * ((((Val.int (p:ℤ) :: x :: y :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest).take 5).map vsz).sum + 1)
          = PK * (4 + 1) * (isz (p:ℤ) + vsz x + vsz y + isz (p:ℤ) + isz (r:ℤ) + 1) := by rw [hsum]
        _ ≤ PK * 5 * (isz (p:ℤ) + vsz x + vsz y + isz (p:ℤ) + isz (r:ℤ) + 1) := Nat.mul_le_mul_right _ (le_refl _)
  have step3 : WordR main swapP
      (fun vs => vs = Val.int (r:ℤ) :: Val.int (p:ℤ) :: x :: y :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest)
      (fun _ out => out = Val.int (p:ℤ) :: Val.int (r:ℤ) :: x :: y :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest)
      (fun _ => SK * (isz (r:ℤ) + isz (p:ℤ) + 1)) := by
    refine hK.conseq main swapP (fun vs => 2 ≤ vs.length)
      (fun vs => vs = Val.int (r:ℤ) :: Val.int (p:ℤ) :: x :: y :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest)
      (fun vs out => ∃ a b rest', vs = a :: b :: rest' ∧ out = b :: a :: rest')
      (fun _ out => out = Val.int (p:ℤ) :: Val.int (r:ℤ) :: x :: y :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest)
      (fun vs => SK * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1))
      (fun _ => SK * (isz (r:ℤ) + isz (p:ℤ) + 1))
      (hswap main) ?_ ?_ ?_
    · intro vs hvs; rw [hvs]; simp
    · intro vs out hvs hQ
      rw [hvs] at hQ
      obtain ⟨a, b, rest', hv, hout⟩ := hQ
      rw [hout]
      have hh : Val.int (r:ℤ) :: Val.int (p:ℤ) :: x :: y :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest
          = a :: b :: rest' := hv
      injection hh with h1 h2
      injection h2 with h3 h4
      rw [← h1, ← h3, ← h4]
    · intro vs hvs
      rw [hvs]
      have hsum : vsz ((Val.int (r:ℤ) :: Val.int (p:ℤ) :: x :: y :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest).getD 0 .nil)
          + vsz ((Val.int (r:ℤ) :: Val.int (p:ℤ) :: x :: y :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest).getD 1 .nil)
          + 1 = isz (r:ℤ) + isz (p:ℤ) + 1 := by simp [vsz_int] <;> ring
      calc SK * (vsz ((Val.int (r:ℤ) :: Val.int (p:ℤ) :: x :: y :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest).getD 0 .nil)
              + vsz ((Val.int (r:ℤ) :: Val.int (p:ℤ) :: x :: y :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest).getD 1 .nil) + 1)
          = SK * (isz (r:ℤ) + isz (p:ℤ) + 1) := by rw [hsum]
        _ ≤ SK * (isz (r:ℤ) + isz (p:ℤ) + 1) := le_refl _
  have step4 : WordR main kronP
      (fun vs => vs = Val.int (p:ℤ) :: Val.int (r:ℤ) :: x :: y :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest)
      (fun _ out => ∃ w : List (ℤ × ℤ), out = cvecVal w :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest ∧
        InDiscVec p r w ∧
        ∀ j : Fin r, (2:ℝ)^p * ‖fxC p (w.getD j (0,0)) - ((r:ℂ))⁻¹ * negaMul r (fxVec p r u) (fxVec p r v) j‖ < 2)
      (fun _ => 4 * Cm (3*r*p) + KronK * (r+1) * (p+1)^2) := by
    refine hK.conseq main kronP
      (fun vs => ∃ u' v' rest2, vs = Val.int (p:ℤ) :: Val.int (r:ℤ) :: cvecVal u' :: cvecVal v' :: rest2 ∧
        InDiscVec p r u' ∧ InDiscVec p r v')
      (fun vs => vs = Val.int (p:ℤ) :: Val.int (r:ℤ) :: x :: y :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest)
      (fun vs out => ∃ u' v' w rest2, vs = Val.int (p:ℤ) :: Val.int (r:ℤ) :: cvecVal u' :: cvecVal v' :: rest2 ∧
        out = cvecVal w :: rest2 ∧ InDiscVec p r w ∧
        ∀ j : Fin r, (2:ℝ)^p * ‖fxC p (w.getD j (0,0)) - ((r:ℂ))⁻¹ * negaMul r (fxVec p r u') (fxVec p r v') j‖ < 2)
      (fun _ out => ∃ w, out = cvecVal w :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest ∧ InDiscVec p r w ∧
        ∀ j : Fin r, (2:ℝ)^p * ‖fxC p (w.getD j (0,0)) - ((r:ℂ))⁻¹ * negaMul r (fxVec p r u) (fxVec p r v) j‖ < 2)
      (fun _ => 4 * Cm (3*r*p) + KronK * (r+1) * (p+1)^2)
      (fun _ => 4 * Cm (3*r*p) + KronK * (r+1) * (p+1)^2)
      (hkron main N Cm hmon hmul p r hr hpow hlt hN) ?_ ?_ ?_
    · intro vs hvs
      refine ⟨u, v, Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest, ?_, hdu, hdv⟩
      rw [hvs, hxu, hyv]
    · intro vs out hvs hQ
      obtain ⟨u', v', w, rest2, hvs', hout, hdw, herr⟩ := hQ
      have hh : Val.int (p:ℤ) :: Val.int (r:ℤ) :: cvecVal u' :: cvecVal v' :: rest2
          = Val.int (p:ℤ) :: Val.int (r:ℤ) :: x :: y :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest := by
        rw [← hvs', hvs]
      injection hh with _ h1
      injection h1 with _ h2
      injection h2 with hx' h3
      injection h3 with hy' h4
      have hu' : u' = u := cvecVal_injective (hx'.trans hxu)
      have hv' : v' = v := cvecVal_injective (hy'.trans hyv)
      refine ⟨w, ?_, hdw, ?_⟩
      · rw [hout, h4]
      · rw [hu', hv'] at herr; exact herr
    · intro vs hvs; exact le_rfl
  intro vs hvs s R0 hR0
  obtain ⟨m1, s1, n1, hQ1, he1, hn1, hstk1, hoth1⟩ := step1 vs hvs s R0 hR0
  obtain ⟨m2, s2, n2, hQ2, he2, hn2, hstk2, hoth2⟩ := step2 m1 hQ1 s1 R0 hstk1
  obtain ⟨m3, s3, n3, hQ3, he3, hn3, hstk3, hoth3⟩ := step3 m2 hQ2 s2 R0 hstk2
  obtain ⟨m4, s4, n4, hQ4, he4, hn4, hstk4, hoth4⟩ := step4 m3 hQ3 s3 R0 hstk3
  obtain ⟨w, hout4, hdw, herr4⟩ := hQ4
  have htot : n1 + n2 + n3 + n4 ≤ 4 * Cm (3 * r * p) + (KronK + 280 * PK + 7 * SK + 1) * (r + 1) * (p + 1) ^ 2 := by
    have hb := pwCostElem PK SK KronK r p (vsz x) (vsz y) (isz (p:ℤ)) (isz (r:ℤ)) hr1 hp1 hxX hyX hpzX hrzX
    have hsum : n1 + n2 + n3 + n4 ≤
        PK * 3 * (vsz x + vsz y + isz (p:ℤ) + 1)
          + PK * 5 * (isz (p:ℤ) + vsz x + vsz y + isz (p:ℤ) + isz (r:ℤ) + 1)
          + SK * (isz (r:ℤ) + isz (p:ℤ) + 1)
          + (4 * Cm (3*r*p) + KronK * (r+1) * (p+1)^2) :=
      add_le_add (add_le_add (add_le_add hn1 hn2) hn3) hn4
    calc n1 + n2 + n3 + n4
        ≤ PK * 3 * (vsz x + vsz y + isz (p:ℤ) + 1)
          + PK * 5 * (isz (p:ℤ) + vsz x + vsz y + isz (p:ℤ) + isz (r:ℤ) + 1)
          + SK * (isz (r:ℤ) + isz (p:ℤ) + 1)
          + (4 * Cm (3*r*p) + KronK * (r+1) * (p+1)^2) := hsum
      _ = 4 * Cm (3*r*p) + (PK * 3 * (vsz x + vsz y + isz (p:ℤ) + 1)
          + PK * 5 * (isz (p:ℤ) + vsz x + vsz y + isz (p:ℤ) + isz (r:ℤ) + 1)
          + SK * (isz (r:ℤ) + isz (p:ℤ) + 1) + KronK * ((r+1)*(p+1)^2)) := by ring
      _ ≤ 4 * Cm (3*r*p) + (KronK + 280 * PK + 7 * SK + 1) * (r + 1) * (p + 1) ^ 2 :=
          Nat.add_le_add_left hb _
  refine ⟨m4, s4, n1 + n2 + n3 + n4, ⟨cvecVal w, ?_, ?_, ?_⟩,
    Eval.seq (Eval.seq (Eval.seq he1 he2) he3) he4, htot, hstk4, ?_⟩
  · rw [hout4]
  · exact ⟨w, u, v, rfl, hxu, hyv, hdw, herr4⟩
  · exact vsz_cvecVal_le hdw
  · intro k hk; rw [hoth4 k hk, hoth3 k hk, hoth2 k hk, hoth1 k hk]

theorem pointwise (hK : HvdH.KernelLib) (hI : HvdH.IntLib) (hL : HvdH.LayoutLib) (hF : HvdH.FxLib)
    (hkr : Work.ConvR.KroneckerSpec) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm →
      HvdH.MulBelow main N Cm → ∀ (p r M : ℕ), 2 ≤ r → HvdH.IsPow2 r → r < 2 ^ (p - 1) → 3 * r * p < N →
      ∀ (As Bs : List (List (ℤ × ℤ))) (rest : List HvdH.Val),
        HvdH.InDiscArr p M r As → HvdH.InDiscArr p M r Bs →
        HvdH.WordR main prog
          (fun vs => vs = HvdH.Val.int (p : ℤ) :: HvdH.Val.int (r : ℤ) ::
            HvdH.rarrVal As :: HvdH.rarrVal Bs :: rest)
          (fun _ out => ∃ Zs : List (List (ℤ × ℤ)), out = HvdH.rarrVal Zs :: rest ∧
            HvdH.InDiscArr p M r Zs ∧ ∀ (i : Fin M) (j : Fin r), (2 : ℝ) ^ p *
              ‖HvdH.fxC p ((Zs.getD i []).getD j (0, 0)) - ((r : ℂ))⁻¹ *
                HvdH.negaMul r (HvdH.fxArr p M r As i) (HvdH.fxArr p M r Bs i) j‖ < 2)
          (fun _ => 4 * M * Cm (3 * r * p) + K * (M * r + 1) * p ^ 2 + K) := by
  classical
  obtain ⟨q, Kq, hq⟩ := pwElemLocal hK hkr
  obtain ⟨reoP, K3, hreo⟩ := reorderArr hK
  obtain ⟨drpP, K4, hdrp⟩ := dropUnder hK
  obtain ⟨combq, kK, hzw⟩ := hK.zipWith
  refine ⟨(reoP ;; combq q) ;; drpP, 8 * Kq + 13 * kK + 33 * K3 + 20 * K4 + kK + 1, ?_⟩
  intro main N Cm hmon hmul p r M hr hpow hlt hN As Bs rest hAs hBs
  have hp1 : 1 ≤ p := by
    have h2 : (2:ℕ) ≤ 2 ^ (p - 1) := le_trans hr hlt.le
    by_contra hc
    have hp0 : p = 0 := by omega
    subst hp0
    simp at h2
  set xs : List Val := As.map cvecVal with hxs
  set ys : List Val := Bs.map cvecVal with hys
  have hxslen : xs.length = M := by rw [hxs, List.length_map, hAs.1]
  have hyslen : ys.length = M := by rw [hys, List.length_map, hBs.1]
  have hqzy : ∀ x y, PWp p r x y →
      WordR main q (fun vs => vs = x :: y :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest)
        (fun _ out => ∃ z, out = z :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest ∧
          PWq p r x y z ∧ vsz z ≤ cvecSz p r)
        (fun _ => 4*Cm (3*r*p) + Kq*(r+1)*(p+1)^2) := by
    intro x y hxy
    exact hq main N Cm hmon hmul p r hr hpow hlt hN x y rest hxy
  have hxA : xs.length = As.length := by rw [hxs, List.length_map]
  have hyB : ys.length = Bs.length := by rw [hys, List.length_map]
  have hPmem : ∀ i < xs.length, PWp p r (xs.getD i .nil) (ys.getD i .nil) := by
    intro i hi
    refine ⟨As.getD i [], Bs.getD i [], ?_, ?_, ?_, ?_⟩
    · rw [hxs]; exact cvecVal_getD (by omega)
    · rw [hys]; exact cvecVal_getD (by omega)
    · have hi' : i < As.length := by omega
      rw [List.getD_eq_getElem _ _ hi']
      exact hAs.2 _ (List.getElem_mem hi')
    · have hi' : i < Bs.length := by omega
      rw [List.getD_eq_getElem _ _ hi']
      exact hBs.2 _ (List.getElem_mem hi')
  have hLmem : ∀ x ∈ xs ++ ys, vsz x ≤ cvecSz p r := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨w, hw, rfl⟩ := mem_map_cvecVal (by rwa [hxs] at hx)
      exact vsz_cvecVal_le (hAs.2 w hw)
    · obtain ⟨w, hw, rfl⟩ := mem_map_cvecVal (by rwa [hys] at hx)
      exact vsz_cvecVal_le (hBs.2 w hw)
  have hzip := hzw main q (Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest) (PWp p r) (PWq p r)
      (4*Cm (3*r*p) + Kq*(r+1)*(p+1)^2) (cvecSz p r) hqzy xs ys
      (by rw [hxslen, hyslen]) hPmem hLmem
  intro vs hvs s R hR
  obtain ⟨mid1, s1, n1, hQ1, he1, hn1, hstk1, hoth1⟩ := hreo main p r As Bs rest vs hvs s R hR
  have hmid1 : mid1 = ofList xs :: ofList ys :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: rest := by
    rw [hQ1, hxs, hys]; rfl
  obtain ⟨mid2, s2, n2, hQ2, he2, hn2, hstk2, hoth2⟩ := hzip mid1 hmid1 s1 R hstk1
  obtain ⟨zs, hout2, hlen2, hQz⟩ := hQ2
  obtain ⟨out, s3, n3, hQ3, he3, hn3, hstk3, hoth3⟩ :=
      hdrp main (ofList zs) (Val.int (p:ℤ)) (Val.int (r:ℤ)) rest mid2 hout2 s2 R hstk2
  have hlenzM : zs.length = M := by rw [hlen2, hxslen]
  have hQz' : ∀ i < M, PWq p r ((As.map cvecVal).getD i .nil) ((Bs.map cvecVal).getD i .nil) (zs.getD i .nil) := by
    intro i hi
    have hi' : i < xs.length := by rw [hxslen]; exact hi
    have hh := hQz i hi'
    rwa [hxs, hys] at hh
  obtain ⟨Zs, hZsEq, hZsDisc, hZsErr⟩ :=
      extractAux (p:=p) (M:=M) (r:=r) (As:=As) (Bs:=Bs) (zs:=zs) hAs.1 hBs.1 hlenzM hQz'
  -- cost ingredients
  have harrA : vsz (rarrVal As) ≤ arrSz p M r := vsz_rarrVal_le hAs
  have harrB : vsz (rarrVal Bs) ≤ arrSz p M r := vsz_rarrVal_le hBs
  have hzsz : ∀ z ∈ zs, vsz z ≤ cvecSz p r := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
    have hi' : i < xs.length := by omega
    have hpq := hQz i hi'
    have h1 : zs[i] = cvecVal hpq.choose := (List.getD_eq_getElem _ _ hi).symm.trans (PWq.eq hpq)
    rw [h1]
    obtain ⟨u, v, -, -, hC, -⟩ := PWq.spec hpq
    exact vsz_cvecVal_le hC
  have harrZ : vsz (ofList zs) ≤ arrSz p M r := by
    have := vsz_ofList_le hzsz
    simpa [arrSz, hlenzM] using this
  have hiszp : isz (p:ℤ) ≤ p + 3 := isz_natCast_le_self p
  have hiszr : isz (r:ℤ) ≤ p + 1 := isz_natCast_le_of_lt hr hlt
  have harr13 : arrSz p M r ≤ 13*(M*r+1)*p^2 := arrSzLe M r p (by omega) hp1
  have hn1' : n1 ≤ K3 * (vsz (rarrVal As) + vsz (rarrVal Bs) + isz (p:ℤ) + isz (r:ℤ) + 1) := hn1
  have hcv1 : cvecSz p r + 1 = 2*r*p + 9*r + 2 := by simp only [cvecSz, cfxSz]; ring
  have hn2'' : n2 ≤ M * (4*Cm (3*r*p) + Kq*(r+1)*(p+1)^2 + kK*(2*r*p + 9*r + 2)) + kK := by
    rw [hxslen, hcv1] at hn2
    calc n2 ≤ M * ((4*Cm (3*r*p) + Kq*(r+1)*(p+1)^2) + kK*(2*r*p + 9*r + 2)) + kK := hn2
      _ = M * (4*Cm (3*r*p) + Kq*(r+1)*(p+1)^2 + kK*(2*r*p + 9*r + 2)) + kK := by ring
  have hn3' : n3 ≤ K4 * (vsz (ofList zs) + isz (p:ℤ) + isz (r:ℤ) + 1) := by
    have hh := hn3
    rw [vsz_int, vsz_int] at hh
    exact hh
  have hmain := pwCost Kq kK K3 K4 M r p (Cm (3*r*p)) (by omega) hp1
      (vsz (rarrVal As)) (vsz (rarrVal Bs)) (vsz (ofList zs)) (isz (p:ℤ)) (isz (r:ℤ))
      (le_trans harrA harr13) (le_trans harrB harr13) (le_trans harrZ harr13) hiszp hiszr
  have hsum : n1 + n2 + n3 ≤
      K3 * (vsz (rarrVal As) + vsz (rarrVal Bs) + isz (p:ℤ) + isz (r:ℤ) + 1)
        + (M * (4*Cm (3*r*p) + Kq*(r+1)*(p+1)^2 + kK*(2*r*p + 9*r + 2)) + kK)
        + K4 * (vsz (ofList zs) + isz (p:ℤ) + isz (r:ℤ) + 1) :=
    add_le_add (add_le_add hn1' hn2'') hn3'
  refine ⟨out, s3, n1 + n2 + n3, ⟨Zs, ?_, hZsDisc, hZsErr⟩,
    Eval.seq (Eval.seq he1 he2) he3, le_trans hsum hmain, ?_, ?_⟩
  · rw [hQ3, hZsEq]
  · exact hstk3
  · intro k hk; rw [hoth3 k hk, hoth2 k hk, hoth1 k hk]

end Work.ConvR

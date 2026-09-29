import Mathlib
import Submission.Work.Transform.Defs
import Submission.Work.ConvR.basic
import Submission.Work.ConvR.permTop
import Submission.Work.Kernel.Raw
import Submission.Work.Transform.phiAux
import Submission.Work.Transform.phiZipDefs
import Submission.Work.Transform.phiDrop
import Submission.Work.Transform.extractCvec

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Transform

open HvdH

/-! ## The prologue: the parameter goes below the two vectors

`Kernel.zipWith` reads the two vectors as the two topmost values of the value stack and passes
everything below them (`rest`) unchanged to the element word; the element word
(`Work.Transform.cfxMulWord`) needs the precision parameter `int p` at the *front* of that `rest`.
So the first thing the `mulWord` program does is the cyclic rotation
`int p :: X :: Y :: R ↦ X :: Y :: int p :: R` of the three topmost values, which is the
permutation `[1,2,0]` of `Work.ConvR.permTop`. -/

theorem mulWord_rollPro (hK : KernelLib) :
    ∃ (prog : Cmd) (K : ℕ),
    ∀ (main : Cmd) (p : ℕ) (X Y : Val) (R : List Val),
      WordR main prog
        (fun vs => vs = Val.int (p : ℤ) :: X :: Y :: R)
        (fun _ out => out = X :: Y :: Val.int (p : ℤ) :: R)
        (fun _ => K * (vsz X + vsz Y + isz (p : ℤ) + 1) + K) := by
  obtain ⟨permP, K0, hperm⟩ := Work.ConvR.permTop hK
  refine ⟨permP [1, 2, 0], 16 * K0, ?_⟩
  intro main p X Y R
  have hperm3 : ([1, 2, 0] : List ℕ).Perm (List.range 3) := by decide
  refine Work.Kernel.WordR_conseq
    (hperm main 3 [1, 2, 0] [Val.int (p : ℤ), X, Y] R (by simp) (by simp) hperm3) ?_ ?_ ?_
  · intro vs hvs
    simpa using hvs
  · intro vs out hvs hout
    rw [hout]
    simp
  · intro vs hvs
    have hsum : (([Val.int (p : ℤ), X, Y] : List Val).map vsz).sum
        = isz (p : ℤ) + vsz X + vsz Y := by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int]
      ring
    rw [hsum]
    have hcomm : isz (p : ℤ) + vsz X + vsz Y + 1 = vsz X + vsz Y + isz (p : ℤ) + 1 := by ring
    rw [hcomm]
    have h16 : K0 * (3 + 1) * (3 + 1) * (vsz X + vsz Y + isz (p : ℤ) + 1)
        = 16 * K0 * (vsz X + vsz Y + isz (p : ℤ) + 1) := by ring
    rw [h16]
    exact Nat.le_add_right _ _

/-! ## The pointwise product (`KernelLib.zipWith` with `cfxMulWord`)

This is `Work.Transform.phiPairWord` with the hypothesis `2 ≤ n` dropped, and with the product
written in the order `x * y`; the length-`0` and length-`1` cases are handled by the same proof
(the empty zip costs only the constant `K₄` of `KernelLib.zipWith`). -/

/-- Per-element input condition of the pointwise product: both values are `cfxVal`s of `C̃◦`. -/
private def MzP (p : ℕ) (x y : Val) : Prop :=
  ∃ u v : ℤ × ℤ, x = cfxVal u ∧ y = cfxVal v ∧ inDisc p u ∧ inDisc p v

/-- Per-element output condition: `z = cfxVal w` with `w ∈ C̃◦` and `2^p‖w̃ - ũ·ṽ‖ < 2`
(`w` first so that `Classical.choose` returns it). -/
private def MzQ (p : ℕ) (x y z : Val) : Prop :=
  ∃ w u v : ℤ × ℤ, z = cfxVal w ∧ x = cfxVal u ∧ y = cfxVal v ∧ inDisc p w ∧
    (2 : ℝ) ^ p * ‖fxC p w - fxC p u * fxC p v‖ < 2

private theorem mulWord_zipP (Kl : KernelLib) (Fl : FxLib) :
    ∃ (prog : Cmd) (K : ℕ),
    ∀ (main : Cmd) (p N : ℕ) (x y : List (ℤ × ℤ)) (R : List Val),
      x.length = N → y.length = N → InDiscVec p N x → InDiscVec p N y → 100 ≤ p →
      WordR main prog
        (fun vs => vs = cvecVal x :: cvecVal y :: Val.int (p : ℤ) :: R)
        (fun _ out => ∃ c : List (ℤ × ℤ), out = cvecVal c :: Val.int (p : ℤ) :: R ∧
          c.length = N ∧ InDiscVec p N c ∧
          ∀ i < N, (2 : ℝ) ^ p * ‖fxC p (c.getD i (0, 0))
            - fxC p (x.getD i (0, 0)) * fxC p (y.getD i (0, 0))‖ < 2)
        (fun _ => K * (N * p ^ 2 + p + 1) + K) := by
  obtain ⟨mulP, K₂, hmul⟩ := cfxMulWord Kl Fl
  obtain ⟨zwP, K₄, hzip⟩ := Kl.zipWith
  refine ⟨zwP mulP, 10000 * (K₂ + K₄ + 1), ?_⟩
  intro main p N x y R hxlen hylen hdx hdy hp
  set xs : List Val := x.map cfxVal with hxs
  set ys : List Val := y.map cfxVal with hys
  have hxslen : xs.length = N := by rw [hxs, List.length_map, hxlen]
  have hyslen : ys.length = N := by rw [hys, List.length_map, hylen]
  -- the per-element word: `cfxMulWord` with the precision parameter below the two values
  have hqzy : ∀ a b, MzP p a b → WordR main mulP
      (fun vs => vs = a :: b :: Val.int (p : ℤ) :: R)
      (fun _ out => ∃ z, out = z :: Val.int (p : ℤ) :: R ∧ MzQ p a b z ∧
        vsz z ≤ Work.ConvR.cfxSz p)
      (fun _ => K₂ * (p + 1) ^ 2) := by
    intro a b hab
    obtain ⟨u, v, rfl, rfl, hu, hv⟩ := hab
    refine Work.Kernel.WordR_conseq (p := mulP)
      (P' := fun vs => vs = cfxVal u :: cfxVal v :: Val.int (p : ℤ) :: R)
      (Q' := fun _ out => ∃ z, out = z :: Val.int (p : ℤ) :: R ∧
        MzQ p (cfxVal u) (cfxVal v) z ∧ vsz z ≤ Work.ConvR.cfxSz p)
      (hmul main p u v R hu hv hp) (fun vs hvs => hvs) ?_ (fun vs hvs => le_rfl)
    intro vs out hvs hout
    obtain ⟨w, hout', hd, herr⟩ := hout
    refine ⟨cfxVal w, hout', ⟨w, u, v, rfl, rfl, rfl, hd, ?_⟩,
      Work.ConvR.vsz_cfxVal_le hd⟩
    simpa only [mul_comm (fxC p u) (fxC p v)] using herr
  have hPmem : ∀ i < xs.length, MzP p (xs.getD i Val.nil) (ys.getD i Val.nil) := by
    intro i hi
    have hiN : i < N := by rw [hxslen] at hi; exact hi
    have hix : i < x.length := by rw [hxlen]; exact hiN
    have hiy : i < y.length := by rw [hylen]; exact hiN
    exact ⟨x.getD i (0, 0), y.getD i (0, 0),
      by rw [hxs]; exact cfxVal_getD (l := x) (i := i) hix,
      by rw [hys]; exact cfxVal_getD (l := y) (i := i) hiy,
      inDiscVec_getD hdx i hiN, inDiscVec_getD hdy i hiN⟩
  have hLmem : ∀ z ∈ xs ++ ys, vsz z ≤ Work.ConvR.cfxSz p := by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · rw [hxs] at hz
      obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
      exact Work.ConvR.vsz_cfxVal_le (hdx.2 z' hz')
    · rw [hys] at hz
      obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
      exact Work.ConvR.vsz_cfxVal_le (hdy.2 z' hz')
  have hzipInst := hzip main mulP (Val.int (p : ℤ) :: R) (MzP p) (MzQ p)
      (K₂ * (p + 1) ^ 2) (Work.ConvR.cfxSz p) hqzy xs ys (by rw [hxslen, hyslen]) hPmem hLmem
  intro vs hvs s Rg hstk
  obtain ⟨mid, s', n, hQ, he, hn, hstk', hoth'⟩ := hzipInst vs hvs s Rg hstk
  obtain ⟨zs, hout, hzlen, hQz⟩ := hQ
  have hzlenN : zs.length = N := by rw [hzlen, hxslen]
  -- read the products back as a list of pairs
  let Q : ℕ → ℤ × ℤ → Prop := fun i w => inDisc p w ∧ (2 : ℝ) ^ p * ‖fxC p w
        - fxC p (x.getD i (0, 0)) * fxC p (y.getD i (0, 0))‖ < 2
  have hex : ∀ i < N, ∃ w : ℤ × ℤ, zs.getD i Val.nil = cfxVal w ∧ Q i w := by
    intro i hi
    have hi' : i < xs.length := by rw [hxslen]; exact hi
    obtain ⟨w, u, v, hzw, hxu, hyv, hd, herr⟩ := hQz i hi'
    have hix : i < x.length := by rw [hxlen]; exact hi
    have hiy : i < y.length := by rw [hylen]; exact hi
    have hxg := cfxVal_getD (l := x) (i := i) hix
    have hyg := cfxVal_getD (l := y) (i := i) hiy
    have hu : u = x.getD i (0, 0) := cfxVal_injective (by rw [← hxu, hxg])
    have hv : v = y.getD i (0, 0) := cfxVal_injective (by rw [← hyv, hyg])
    exact ⟨w, hzw, hd, by rw [hu, hv] at herr; exact herr⟩
  obtain ⟨c, hcEq, hclen, hcQ⟩ := extractCvec (N := N) (Q := Q) hzlenN hex
  have hdisc : InDiscVec p N c := by
    refine ⟨hclen, ?_⟩
    intro z hz
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
    have hi' : i < N := by rw [← hclen]; exact hi
    rw [← List.getD_eq_getElem (l := c) (d := ((0, 0) : ℤ × ℤ)) hi]
    exact (hcQ i hi').1
  have herrQ : ∀ i < N, (2 : ℝ) ^ p * ‖fxC p (c.getD i (0, 0))
      - fxC p (x.getD i (0, 0)) * fxC p (y.getD i (0, 0))‖ < 2 :=
    fun i hi => (hcQ i hi).2
  have hcost : n ≤ 10000 * (K₂ + K₄ + 1) * (N * p ^ 2 + p + 1) + 10000 * (K₂ + K₄ + 1) := by
    refine le_trans hn ?_
    show xs.length * (K₂ * (p + 1) ^ 2 + K₄ * (Work.ConvR.cfxSz p + 1)) + K₄
      ≤ 10000 * (K₂ + K₄ + 1) * (N * p ^ 2 + p + 1) + 10000 * (K₂ + K₄ + 1)
    rw [hxslen]
    unfold Work.ConvR.cfxSz
    have h1 : (p + 1) ^ 2 ≤ 4 * p ^ 2 := by nlinarith
    have h2 : 2 * p + 8 + 1 ≤ 4 * p ^ 2 := by nlinarith
    have e : N * (K₂ * (p + 1) ^ 2 + K₄ * (2 * p + 8 + 1)) + K₄
        = N * (K₂ * (p + 1) ^ 2) + N * (K₄ * (2 * p + 8 + 1)) + K₄ := by ring
    rw [e]
    have i1 : N * (K₂ * (p + 1) ^ 2) ≤ N * (K₂ * (4 * p ^ 2)) :=
      Nat.mul_le_mul_left N (Nat.mul_le_mul_left K₂ h1)
    have i2 : N * (K₄ * (2 * p + 8 + 1)) ≤ N * (K₄ * (4 * p ^ 2)) :=
      Nat.mul_le_mul_left N (Nat.mul_le_mul_left K₄ h2)
    have e3 : 10000 * (K₂ + K₄ + 1) * (N * p ^ 2 + p + 1) + 10000 * (K₂ + K₄ + 1)
        = 10000 * (K₂ * (N * p ^ 2)) + 10000 * (K₄ * (N * p ^ 2)) + 10000 * (N * p ^ 2)
          + 10000 * (K₂ * p) + 10000 * (K₄ * p) + 10000 * p + 20000 * K₂ + 20000 * K₄
          + 20000 := by ring
    calc N * (K₂ * (p + 1) ^ 2) + N * (K₄ * (2 * p + 8 + 1)) + K₄
        ≤ N * (K₂ * (4 * p ^ 2)) + N * (K₄ * (4 * p ^ 2)) + K₄ := by omega
      _ = 4 * (K₂ * (N * p ^ 2)) + 4 * (K₄ * (N * p ^ 2)) + K₄ := by ring
      _ ≤ 10000 * (K₂ + K₄ + 1) * (N * p ^ 2 + p + 1) + 10000 * (K₂ + K₄ + 1) := by
          rw [e3]; omega
  exact ⟨mid, s', n, ⟨c, by rw [hout, hcEq], hclen, hdisc, herrQ⟩, he, hcost, hstk', hoth'⟩

/-! ## Cost arithmetic of the three phases -/

/-- Combining the cost bounds of the prologue, the zip and the epilogue: with
`sX, sY, sZ ≤ 200 (n p² + 1)` (the `C̃◦`-size bound of `Work.Transform.vsz_cvecVal_le`) and
`isp ≤ p + 2` (`Work.Transform.isz_le`), the sum is within the stated shape with one uniform
constant `4000 (KA + KB + KC + 1)`. -/
theorem mulWord_costBound (KA KB KC n p sX sY sZ isp : ℕ)
    (hX : sX ≤ 200 * (n * p ^ 2 + 1)) (hY : sY ≤ 200 * (n * p ^ 2 + 1))
    (hZ : sZ ≤ 200 * (n * p ^ 2 + 1)) (hzp : isp ≤ p + 2) :
    KA * (sX + sY + isp + 1) + KA + (KB * (n * p ^ 2 + p + 1) + KB)
      + (KC * (sZ + isp + 1) + KC)
      ≤ 2000 * (KA + KB + KC + 1) * (n * p ^ 2 + p + 1) + 2000 * (KA + KB + KC + 1) := by
  have hA : KA * (sX + sY + isp + 1)
      ≤ KA * (1000 * (n * p ^ 2 + p + 1)) :=
    Nat.mul_le_mul_left KA (by omega)
  have hB : KB * (n * p ^ 2 + p + 1) ≤ KB * (1000 * (n * p ^ 2 + p + 1)) :=
    Nat.mul_le_mul_left KB (by omega)
  have hC : KC * (sZ + isp + 1) ≤ KC * (1000 * (n * p ^ 2 + p + 1)) :=
    Nat.mul_le_mul_left KC (by omega)
  have hKA : KA ≤ 1000 * (KA + KB + KC + 1) := by omega
  have hKB : KB ≤ 1000 * (KA + KB + KC + 1) := by omega
  have hKC : KC ≤ 1000 * (KA + KB + KC + 1) := by omega
  nlinarith [hA, hB, hC, hKA, hKB, hKC, Nat.zero_le KA, Nat.zero_le KB, Nat.zero_le KC,
    Nat.zero_le (n * p ^ 2 + p + 1)]

/-! ## The pointwise fixed-point complex product -/

/-- Pointwise fixed-point complex product of two length-`n` vectors, both in `C̃◦ⁿ`:
`Kernel.zipWith` with the `FxLib.mulS` word (`2^p`-scaled error `< 2` per coordinate).
Consumes `int p` and the two vectors, pushes the product.  The `+ p + 1` in the cost bound is
needed: even at `n = 0` the program must delete the `int p` on the stack
(see `Submission/Work/Transform/mulWord_refute.lean` for a refutation of the bound
`K * (n * p^2) + K`). -/
theorem mulWord : HvdH.KernelLib → HvdH.IntLib → HvdH.FxLib → ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (p n : ℕ) (x y : List (ℤ × ℤ)) (R : List HvdH.Val),
      x.length = n → y.length = n → HvdH.InDiscVec p n x → HvdH.InDiscVec p n y → 100 ≤ p →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.Val.int p :: HvdH.cvecVal x :: HvdH.cvecVal y :: R)
        (fun vs out => ∃ z : List (ℤ × ℤ), out = HvdH.cvecVal z :: R ∧ z.length = n ∧
          HvdH.InDiscVec p n z ∧
          ∀ i < n, (2 : ℝ) ^ p * ‖HvdH.fxC p (z.getD i (0, 0))
            - HvdH.fxC p (x.getD i (0, 0)) * HvdH.fxC p (y.getD i (0, 0))‖ < 2)
        (fun _ => K * (n * p ^ 2 + p + 1) + K) := by
  intro Kl Il Fl
  obtain ⟨proA, KA, hA⟩ := mulWord_rollPro Kl
  obtain ⟨proB, KB, hB⟩ := mulWord_zipP Kl Fl
  obtain ⟨proC, KC, hC⟩ := dropParamWord Kl
  refine ⟨Cmd.seq (Cmd.seq proA proB) proC, 2000 * (KA + KB + KC + 1), ?_⟩
  intro main p n x y R hxlen hylen hdx hdy hp
  have hszX : vsz (cvecVal x) ≤ 200 * (n * p ^ 2 + 1) := vsz_cvecVal_le hdx hp
  have hszY : vsz (cvecVal y) ≤ 200 * (n * p ^ 2 + 1) := vsz_cvecVal_le hdy hp
  have hiszp : isz (p : ℤ) ≤ p + 2 := by simpa using isz_le (p : ℤ)
  intro vs hvs s Rg hRg
  obtain ⟨mid1, s1, n1, hpost1, hev1, hn1, hstk1, hoth1⟩ :=
    hA main p (cvecVal x) (cvecVal y) R vs hvs s Rg hRg
  obtain ⟨mid2, s2, n2, hpost2, hev2, hn2, hstk2, hoth2⟩ :=
    hB main p n x y R hxlen hylen hdx hdy hp mid1 (by rw [hpost1]) s1 Rg hstk1
  obtain ⟨z, hpost2', hzlen, hdz, herr⟩ := hpost2
  obtain ⟨out, s3, n3, hpost3, hev3, hn3, hstk3, hoth3⟩ :=
    hC main p (cvecVal z) R mid2 (by rw [hpost2']) s2 Rg hstk2
  have hszZ : vsz (cvecVal z) ≤ 200 * (n * p ^ 2 + 1) := vsz_cvecVal_le hdz hp
  have hn3' : n3 ≤ KC * (vsz (cvecVal z) + isz (p : ℤ) + 1) + KC := by
    refine le_trans hn3 ?_
    rw [hpost2']
    simp only [List.getD_cons_zero, List.getD_cons_succ, vsz_int]
    exact Nat.le_add_right _ _
  refine ⟨out, s3, n1 + n2 + n3, ⟨z, hpost3, hzlen, hdz, herr⟩,
    Eval.seq (Eval.seq hev1 hev2) hev3, ?_, hstk3, ?_⟩
  · refine le_trans (add_le_add (add_le_add hn1 hn2) hn3') ?_
    exact mulWord_costBound KA KB KC n p _ _ _ _ hszX hszY hszZ hiszp
  · intro k hk
    rw [hoth3 k hk, hoth2 k hk, hoth1 k hk]

end Work.Transform

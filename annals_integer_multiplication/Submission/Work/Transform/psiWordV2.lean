import Mathlib
import Submission.Work.Transform.Defs
import Submission.Work.Transform.phiAux
import Submission.Work.Transform.flattenIdx
import Submission.Work.Transform.inDiscFlatten
import Submission.Work.ConvR.basic
import Submission.Work.Transform.psiShuffleWord
import Submission.Work.Transform.extractCvec

/-!
# `psiWordV2`: the inverse transform `Ũ = T̃⁻¹` of paper Prop 3.5 as a flat-vector word

The program is the composition of three words:

* `Work.Transform.psiShuffleWord` — `rarrVal w :: int p :: cvecVal zt :: int r :: R` becomes
  `cvecVal w.flatten :: cvecVal zt :: int p :: R` (`roll 3; drop; roll 2; roll 1; flatten`),
* `cvecMulWord` (below) — the pointwise fixed-point product of two `C̃◦`-vectors
  (`KernelLib.zipWith` over the two vectors with the element word `Work.Transform.cfxMulWord`),
* `KernelLib.swap` — puts `int p` back on top of the product.

In `cvecMulWord`, `KernelLib.zipWith` produces a list of values `zs` of length `M*r` whose entries
are `cfxVal`-encodings of the products (through the per-element predicate `VecQ`); that list is
turned into a genuine list of pairs by `Work.Transform.extractCvec`, and the index alignment of
`w.flatten` with the `M × r`-matrix `w` is `Work.Transform.flattenIdx`.
-/

set_option autoImplicit false

namespace Work.Transform

open HvdH

/-! ## Per-element predicates for the pointwise product

`VecP p x y` is the input condition of the element word (`x`, `y` are the `cfxVal`-encodings of two
points of `C̃◦`); `VecQ p x y z` is its output condition: `z` is a `cfxVal`, and the `2^p`-scaled
error against `fxC p y * fxC p x` is `< 2`.  (`cfxMulWord` multiplies the second value by the
first, which is the order appearing in `VecQ` and in the statement of `psiWordV2`.) -/

private def VecP (p : ℕ) (x y : Val) : Prop :=
  ∃ u v : ℤ × ℤ, x = cfxVal u ∧ y = cfxVal v ∧ inDisc p u ∧ inDisc p v

private def VecQ (p : ℕ) (x y z : Val) : Prop :=
  ∃ w u v : ℤ × ℤ, z = cfxVal w ∧ x = cfxVal u ∧ y = cfxVal v ∧ inDisc p w ∧
    (2 : ℝ) ^ p * ‖fxC p w - fxC p v * fxC p u‖ < 2

/-! ## Elementary helpers -/

/-- `getD` of a `cfxVal`-mapped list, below its length. -/
private theorem getD_map_cfxVal (x : List (ℤ × ℤ)) {i : ℕ} (hi : i < x.length) :
    (x.map cfxVal).getD i Val.nil = cfxVal (x.getD i (0, 0)) := by
  have h2 : i < (x.map cfxVal).length := by simpa using hi
  calc (x.map cfxVal).getD i Val.nil = (x.map cfxVal)[i] := List.getD_eq_getElem _ _ h2
    _ = (x.map cfxVal).getD i (cfxVal (0, 0)) := (List.getD_eq_getElem _ _ h2).symm
    _ = cfxVal (x.getD i (0, 0)) :=
        List.getD_map (l := x) (d := ((0, 0) : ℤ × ℤ)) (n := i) cfxVal

private theorem isz_natCast_le' (p : ℕ) : isz ((p : ℤ)) ≤ p + 2 := by
  simpa using isz_le ((p : ℤ))

/-- The arithmetic combining the costs of the three phases into the stated bound
`K * ((M*r)*p^2 + p + r + 1) + K`. -/
private theorem costArith (K₁ K₂ K₃ T p r : ℕ) (hp : 100 ≤ p) :
    (K₁ * (T * p ^ 2 + p + r + 1) + K₁) +
      ((K₂ * (T * p ^ 2 + p + 1) + K₂) + K₃ * (200 * (T * p ^ 2 + 1) + (p + 2) + 1))
      ≤ 100000 * (K₁ + K₂ + K₃ + 1) * (T * p ^ 2 + p + r + 1) +
        100000 * (K₁ + K₂ + K₃ + 1) := by
  set A : ℕ := T * p ^ 2 + p + r + 1 with hA
  have hApos : 0 < A := by omega
  have hK1 : K₁ ≤ K₁ * A := Nat.le_mul_of_pos_right K₁ hApos
  have hB : T * p ^ 2 + p + 1 ≤ A := by omega
  have hK2 : K₂ * (T * p ^ 2 + p + 1) ≤ K₂ * A := Nat.mul_le_mul_left K₂ hB
  have hK2' : K₂ ≤ K₂ * A := Nat.le_mul_of_pos_right K₂ hApos
  have hC : 200 * (T * p ^ 2 + 1) + (p + 2) + 1 ≤ 404 * A := by
    have h200 : 200 * (T * p ^ 2 + 1) ≤ 200 * A := Nat.mul_le_mul_left 200 (by omega)
    have hpd : p + 3 ≤ 204 * A := by
      have hle : p ≤ A := by omega
      calc p + 3 ≤ 204 * p := by omega
        _ ≤ 204 * A := Nat.mul_le_mul_left 204 hle
    omega
  have hK3 : K₃ * (200 * (T * p ^ 2 + 1) + (p + 2) + 1) ≤ K₃ * (404 * A) :=
    Nat.mul_le_mul_left K₃ hC
  have hfirst : (K₁ * A + K₁) + ((K₂ * (T * p ^ 2 + p + 1) + K₂) +
      K₃ * (200 * (T * p ^ 2 + 1) + (p + 2) + 1)) ≤ (2 * K₁ + 2 * K₂ + 404 * K₃) * A := by
    have e : (2 * K₁ + 2 * K₂ + 404 * K₃) * A = (K₁ * A + K₁ * A) +
        ((K₂ * A + K₂ * A) + K₃ * (404 * A)) := by ring
    rw [e]
    exact Nat.add_le_add (Nat.add_le_add_left hK1 (K₁ * A))
      (Nat.add_le_add (Nat.add_le_add hK2 hK2') hK3)
  refine le_trans hfirst ?_
  have e2 : (2 * K₁ + 2 * K₂ + 404 * K₃) * A = 2 * K₁ * A + 2 * K₂ * A + 404 * K₃ * A := by
    ring
  rw [e2]
  have i1 : 2 * K₁ * A ≤ 100000 * K₁ * A := Nat.mul_le_mul_right A (by omega)
  have i2 : 2 * K₂ * A ≤ 100000 * K₂ * A := Nat.mul_le_mul_right A (by omega)
  have i3 : 404 * K₃ * A ≤ 100000 * K₃ * A := Nat.mul_le_mul_right A (by omega)
  have i4 : 100000 * K₁ * A + 100000 * K₂ * A + 100000 * K₃ * A ≤
      100000 * (K₁ + K₂ + K₃ + 1) * A := by
    have e3 : 100000 * (K₁ + K₂ + K₃ + 1) * A =
        100000 * K₁ * A + 100000 * K₂ * A + 100000 * K₃ * A + 100000 * A := by ring
    rw [e3]; omega
  omega

/-! ## The pointwise product word
`cvecVal x :: cvecVal y :: int p :: R ↦ cvecVal c :: int p :: R` -/

private theorem cvecMulWord (Kl : HvdH.KernelLib) (Fl : HvdH.FxLib) :
    ∃ (prog : Cmd) (K : ℕ),
    ∀ (main : Cmd) (p N : ℕ) (x y : List (ℤ × ℤ)) (R : List Val),
      x.length = N → y.length = N → InDiscVec p N x → InDiscVec p N y → 100 ≤ p →
      WordR main prog
        (fun vs => vs = cvecVal x :: cvecVal y :: Val.int p :: R)
        (fun _ out => ∃ c : List (ℤ × ℤ), out = cvecVal c :: Val.int p :: R ∧
          c.length = N ∧ InDiscVec p N c ∧
          ∀ i < N, (2 : ℝ) ^ p * ‖fxC p (c.getD i (0, 0))
            - fxC p (y.getD i (0, 0)) * fxC p (x.getD i (0, 0))‖ < 2)
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
  have hqzy : ∀ a b, VecP p a b → WordR main mulP
      (fun vs => vs = a :: b :: Val.int (p : ℤ) :: R)
      (fun _ out => ∃ z, out = z :: Val.int (p : ℤ) :: R ∧ VecQ p a b z ∧
        vsz z ≤ Work.ConvR.cfxSz p)
      (fun _ => K₂ * (p + 1) ^ 2) := by
    intro a b hab
    obtain ⟨u, v, rfl, rfl, hu, hv⟩ := hab
    refine Work.Kernel.WordR_conseq (p := mulP) (P' := fun vs => vs = cfxVal u :: cfxVal v ::
        Val.int (p : ℤ) :: R) (Q' := fun _ out => ∃ z, out = z :: Val.int (p : ℤ) :: R ∧
        VecQ p (cfxVal u) (cfxVal v) z ∧ vsz z ≤ Work.ConvR.cfxSz p)
      (hmul main p u v R hu hv hp) (fun vs hvs => hvs) ?_ (fun vs hvs => le_rfl)
    intro vs out hvs hout
    obtain ⟨w, hout', hd, herr⟩ := hout
    exact ⟨cfxVal w, hout', ⟨w, u, v, rfl, rfl, rfl, hd, herr⟩, Work.ConvR.vsz_cfxVal_le hd⟩
  have hPmem : ∀ i < xs.length, VecP p (xs.getD i Val.nil) (ys.getD i Val.nil) := by
    intro i hi
    have hiN : i < N := by rw [hxslen] at hi; exact hi
    have hix : i < x.length := by rw [hxlen]; exact hiN
    have hiy : i < y.length := by rw [hylen]; exact hiN
    exact ⟨x.getD i (0, 0), y.getD i (0, 0), by rw [hxs]; exact getD_map_cfxVal x hix,
      by rw [hys]; exact getD_map_cfxVal y hiy,
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
  have hzipInst := hzip main mulP (Val.int (p : ℤ) :: R) (VecP p) (VecQ p)
      (K₂ * (p + 1) ^ 2) (Work.ConvR.cfxSz p) hqzy xs ys (by rw [hxslen, hyslen]) hPmem hLmem
  intro vs hvs s Rg hstk
  obtain ⟨mid, s', n, hQ, he, hn, hstk', hoth'⟩ := hzipInst vs hvs s Rg hstk
  obtain ⟨zs, hout, hzlen, hQz⟩ := hQ
  have hzlenN : zs.length = N := by rw [hzlen, hxslen]
  -- read the products back as a list of pairs
  let Q : ℕ → ℤ × ℤ → Prop := fun i w => inDisc p w ∧ (2 : ℝ) ^ p * ‖fxC p w
        - fxC p (y.getD i (0, 0)) * fxC p (x.getD i (0, 0))‖ < 2
  have hex : ∀ i < N, ∃ w : ℤ × ℤ, zs.getD i Val.nil = cfxVal w ∧ Q i w := by
    intro i hi
    have hi' : i < xs.length := by rw [hxslen]; exact hi
    obtain ⟨w, u, v, hzw, hxu, hyv, hd, herr⟩ := hQz i hi'
    have hix : i < x.length := by rw [hxlen]; exact hi
    have hiy : i < y.length := by rw [hylen]; exact hi
    have hxg := getD_map_cfxVal x hix
    have hyg := getD_map_cfxVal y hiy
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
      - fxC p (y.getD i (0, 0)) * fxC p (x.getD i (0, 0))‖ < 2 :=
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

/-- The inverse map `Ũ = T̃⁻¹` of Prop 3.5 as an array word: flatten the `R`-array
`w : List (List (ℤ × ℤ))` (an `M × r` matrix of fixed-point pairs, each row in `C̃◦`) to a vector
of length `M*r` and multiply pointwise by the stretched table `zt` (length `M*r`, in `C̃◦`,
meant to be `i ↦ ζ^{-(i mod r)}`), with `2^p`-scaled error `< 2` per coordinate.  Intended
implementation: `LayoutLib.flatten` then `Kernel.zipWith` + `FxLib.mulS`.  `int p` is kept on top
of the result (the following word needs it).  The `+ p + r + 1` in the cost bound is needed: even
at `M = 0` the program must delete the `int r` and `int p` on the stack
(cf. `Submission/Work/Transform/mulWord_refute.lean`). -/
theorem psiWordV2 : HvdH.KernelLib → HvdH.IntLib → HvdH.LayoutLib → HvdH.FxLib →
    ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (p r M : ℕ) (w : List (List (ℤ × ℤ))) (zt : List (ℤ × ℤ))
      (R : List HvdH.Val),
      w.length = M → (∀ a < M, (w.getD a []).length = r) → zt.length = M * r →
      HvdH.InDiscArr p M r w → HvdH.InDiscVec p (M * r) zt → 100 ≤ p → 2 ≤ r →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.rarrVal w :: HvdH.Val.int p :: HvdH.cvecVal zt ::
          HvdH.Val.int r :: R)
        (fun vs out => ∃ c : List (ℤ × ℤ), out = HvdH.Val.int p :: HvdH.cvecVal c :: R ∧
          c.length = M * r ∧ HvdH.InDiscVec p (M * r) c ∧
          ∀ i < M * r, (2 : ℝ) ^ p * ‖HvdH.fxC p (c.getD i (0, 0))
            - HvdH.fxC p (zt.getD i (0, 0)) * HvdH.fxC p ((w.getD (i / r) []).getD (i % r) (0, 0))‖ < 2)
        (fun _ => K * ((M * r) * p ^ 2 + p + r + 1) + K) := by
  intro Kl Il La Fl
  obtain ⟨shufP, K₁, hshuf⟩ := psiShuffleWord Kl La
  obtain ⟨mulP, K₂, hmul⟩ := cvecMulWord Kl Fl
  obtain ⟨swP, K₃, hswap⟩ := Kl.swap
  refine ⟨HvdH.Cmd.seq shufP (HvdH.Cmd.seq mulP swP), 100000 * (K₁ + K₂ + K₃ + 1), ?_⟩
  intro main p r M w zt R hwlen hrow hzt hda hdz hp hr
  have hfl := flattenIdx (0, 0) w M r hwlen hrow
  intro vs hvs s Rg hstk
  -- phase 1: shuffle (flatten the array, erase `int r`, put the table under the vector)
  obtain ⟨mid₁, s₁, n₁, hQ₁, he₁, hn₁, hstk₁, hoth₁⟩ :=
    hshuf main p r M w zt R hwlen hrow hzt hda hdz hp hr vs hvs s Rg hstk
  -- phase 2: pointwise product
  obtain ⟨mid₂, s₂, n₂, hQ₂, he₂, hn₂, hstk₂, hoth₂⟩ :=
    hmul main p (M * r) w.flatten zt R hfl.1 hzt (inDiscFlatten hda) hdz hp
      mid₁ (by rw [hQ₁]) s₁ Rg hstk₁
  obtain ⟨c, hout₂, hclen, hdc, herr₂⟩ := hQ₂
  -- phase 3: bring `int p` back on top
  have h2le : 2 ≤ mid₂.length := by rw [hout₂]; simp
  obtain ⟨out₃, s₃, n₃, hpost₃, he₃, hn₃, hstk₃, hoth₃⟩ := hswap main mid₂ h2le s₂ Rg hstk₂
  obtain ⟨a, b, rest, hmid₂', hout₃'⟩ := hpost₃
  have hcons : a :: b :: rest = cvecVal c :: Val.int (p : ℤ) :: R := hmid₂'.symm.trans hout₂
  have ha : a = cvecVal c := (List.cons.inj hcons).1
  have hcons2 : b :: rest = Val.int (p : ℤ) :: R := (List.cons.inj hcons).2
  have hb : b = Val.int (p : ℤ) := (List.cons.inj hcons2).1
  have hrest : rest = R := (List.cons.inj hcons2).2
  have hout₃'' : out₃ = Val.int (p : ℤ) :: cvecVal c :: R := by rw [hout₃', hb, ha, hrest]
  have herr : ∀ i < M * r, (2 : ℝ) ^ p * ‖fxC p (c.getD i (0, 0))
      - fxC p (zt.getD i (0, 0)) * fxC p ((w.getD (i / r) []).getD (i % r) (0, 0))‖ < 2 := by
    intro i hi
    have h := herr₂ i hi
    rwa [hfl.2 i hi] at h
  refine ⟨out₃, s₃, n₁ + (n₂ + n₃), ⟨c, hout₃'', hclen, hdc, herr⟩,
    Eval.seq he₁ (Eval.seq he₂ he₃), ?_, hstk₃, ?_⟩
  · have hvsz : vsz (cvecVal c) ≤ 200 * ((M * r) * p ^ 2 + 1) := vsz_cvecVal_le hdc hp
    have hisz : isz ((p : ℤ)) ≤ p + 2 := isz_natCast_le' p
    have hn₃' : n₃ ≤ K₃ * (200 * ((M * r) * p ^ 2 + 1) + (p + 2) + 1) := by
      refine le_trans hn₃ ?_
      simp only [hout₂, List.getD_cons_zero, List.getD_cons_succ, vsz_int]
      apply Nat.mul_le_mul_left
      omega
    have hn₁r : n₁ ≤ K₁ * ((M * r) * p ^ 2 + p + r + 1) + K₁ := hn₁
    have hn₂r : n₂ ≤ K₂ * ((M * r) * p ^ 2 + p + 1) + K₂ := hn₂
    have hcost := costArith K₁ K₂ K₃ (M * r) p r hp
    show n₁ + (n₂ + n₃) ≤ 100000 * (K₁ + K₂ + K₃ + 1) * ((M * r) * p ^ 2 + p + r + 1) +
        100000 * (K₁ + K₂ + K₃ + 1)
    omega
  · intro k hk
    rw [hoth₃ k hk, hoth₂ k hk, hoth₁ k hk]

end Work.Transform

import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs

/-!
# SynFFT: encoding sizes of the array / list values (`Work.SynFFT.ArrSizeProp`)

`ArrSizeProp` (`Submission/Work/SynFFT/kit2.lean`) collects the three elementary size bounds the
axis loop of the synthetic FFT needs:

* an in-disc coefficient vector (`r` pairs in the disc of radius `1`, at precision `p ≥ 1`) is
  encoded in at most `r (2p+6) + 1` glyphs;
* a list of `M` such vectors in at most `M (r (2p+6) + 2) + 1` glyphs;
* a list of `ts.length` naturals below `2^p` in at most `ts.length (p + 3) + 1` glyphs.

The bounds are *tight*: for `w = [(2^(p-1), 2^(p-1))]` (`p ≥ 1`) the first is an equality, and for
`ts = [2^p - 1]` the third is an equality.  The only estimate with real content is therefore the
per-coordinate bit count `size x + size y ≤ 2p` for `x² + y² ≤ 4^p`, proven as
`size_add_size_le` below; the naive bound derived from `|x|, |y| ≤ 2^p` alone is `2p + 2` and
would miss the last four glyphs.

The counting lemmas (`vsz_ofList`, `sum_le_of_forall`, `natAbs_le_two_pow`, …) are taken from the
`Work.SynFFT.MrgKit` kit, where they are already proven.
-/

namespace Work.SynFFT

open HvdH

/-! ## The tight per-coordinate bit count -/

/-- If `x² + y² ≤ 4^p` with `p ≥ 1`, then the two integers have at most `2p` bits altogether.
Indeed, either both are `< 2^p` (so `size ≤ p` each), or one of them equals `±2^p`, in which case
the other one vanishes. -/
lemma size_add_size_le (p : ℕ) (hp : 0 < p) (a b : ℤ) (h : a ^ 2 + b ^ 2 ≤ 4 ^ p) :
    a.natAbs.size + b.natAbs.size ≤ 2 * p := by
  have ha : a.natAbs ≤ 2 ^ p := MrgKit.natAbs_le_two_pow p (a, b) h
  have hb : b.natAbs ≤ 2 ^ p :=
    MrgKit.natAbs_le_two_pow p (b, a) (by show b ^ 2 + a ^ 2 ≤ 4 ^ p; nlinarith [h])
  have hZ : (4 : ℤ) ^ p = ((2 : ℤ) ^ p) ^ 2 := by
    rw [show (4:ℤ) = 2^2 by norm_num, ← pow_mul, mul_comm 2 p, pow_mul]
  -- a coordinate at the maximal modulus `2^p` forces the other one to vanish
  have key : ∀ x y : ℤ, x.natAbs ≤ 2 ^ p → 2 ^ p ≤ x.natAbs → x ^ 2 + y ^ 2 ≤ 4 ^ p → y = 0 := by
    intro x y hx1 hx2 hxy
    have heq : x.natAbs = 2 ^ p := le_antisymm hx1 hx2
    have hxsq : x ^ 2 = ((2 : ℤ) ^ p) ^ 2 := by
      rw [← Int.natAbs_sq x, heq, Nat.cast_pow, Nat.cast_ofNat]
    have h1 : x ^ 2 + y ^ 2 ≤ ((2 : ℤ) ^ p) ^ 2 := by rw [← hZ]; exact hxy
    have h2 : y ^ 2 ≤ 0 := by nlinarith [h1, hxsq]
    nlinarith [sq_nonneg y, h2]
  by_cases ha' : a.natAbs.size ≤ p
  · by_cases hb' : b.natAbs.size ≤ p
    · omega
    · have hb2 : 2 ^ p ≤ b.natAbs := (Nat.lt_size).mp (by omega)
      have ha0 : a = 0 := key b a hb hb2 (by show b ^ 2 + a ^ 2 ≤ 4 ^ p; nlinarith [h])
      have hb3 : b.natAbs.size ≤ p + 1 := by
        have := Nat.size_le_size hb; rwa [Nat.size_pow] at this
      rw [ha0] at ha' ⊢
      simp only [Int.natAbs_zero, Nat.size_zero, Nat.zero_add] at ha' ⊢
      omega
  · have ha2 : 2 ^ p ≤ a.natAbs := (Nat.lt_size).mp (by omega)
    have hb0 : b = 0 := key a b ha ha2 h
    have ha3 : a.natAbs.size ≤ p + 1 := by
      have := Nat.size_le_size ha; rwa [Nat.size_pow] at this
    rw [hb0]
    simp only [Int.natAbs_zero, Nat.size_zero, Nat.add_zero]
    omega

/-- One fixed-point complex number in the disc of radius `1` at precision `p ≥ 1` costs at most
`2p + 5` glyphs: `vsz (cfxVal z) = isz z.1 + isz z.2 + 1` and the two coordinates have `≤ 2p`
bits in total (`size_add_size_le`). -/
lemma vsz_cfxVal_le_tight (p : ℕ) (hp : 0 < p) (z : ℤ × ℤ) (h : inDisc p z) :
    vsz (cfxVal z) ≤ 2 * p + 5 := by
  rw [MrgKit.vsz_cfxVal']
  have := size_add_size_le p hp z.1 z.2 h
  simp only [isz]
  omega

/-! ## The three bounds -/

/-- Encoding size of an in-disc coefficient vector. -/
lemma vsz_cvecVal_tight (p r : ℕ) (hp : 0 < p) (w : List (ℤ × ℤ)) (hw : InDiscVec p r w) :
    vsz (cvecVal w) ≤ r * (2 * p + 6) + 1 := by
  obtain ⟨hlen, hd⟩ := hw
  have h1 : vsz (cvecVal w) = w.length + (w.map fun z => vsz (cfxVal z)).sum + 1 := by
    rw [cvecVal, MrgKit.vsz_ofList, List.length_map, List.map_map]; rfl
  have h2 : (w.map fun z => vsz (cfxVal z)).sum ≤ w.length * (2 * p + 5) :=
    MrgKit.sum_le_of_forall _ w (2 * p + 5)
      (fun z hz => vsz_cfxVal_le_tight p hp z (hd z hz))
  rw [h1, hlen] at *
  nlinarith [h2]

/-- Encoding size of an array of `M` in-disc coefficient vectors. -/
lemma vsz_rarrVal_tight (p r M : ℕ) (hp : 0 < p) (ws : List (List (ℤ × ℤ)))
    (hw : InDiscArr p M r ws) : vsz (rarrVal ws) ≤ M * (r * (2 * p + 6) + 2) + 1 := by
  obtain ⟨hlen, hd⟩ := hw
  subst hlen
  have h1 : vsz (rarrVal ws) = ws.length + (ws.map fun w => vsz (cvecVal w)).sum + 1 := by
    rw [rarrVal, MrgKit.vsz_ofList, List.length_map, List.map_map]; rfl
  have h2 : (ws.map fun w => vsz (cvecVal w)).sum ≤ ws.length * (r * (2 * p + 6) + 1) :=
    MrgKit.sum_le_of_forall _ ws (r * (2 * p + 6) + 1)
      (fun w hw' => vsz_cvecVal_tight p r hp w (hd w hw'))
  rw [h1]
  have h3 : ws.length * (r * (2 * p + 6) + 2) + 1 =
      ws.length * (r * (2 * p + 6) + 1) + ws.length + 1 := by ring
  rw [h3]
  omega

/-- Encoding size of a list of naturals below `2^p`.  (No bound on `p` is needed: for `p = 0`
every `t ∈ ts` is `0` and the estimate stays true.) -/
lemma vsz_intList_le (ts : List ℕ) (p : ℕ) (h : ∀ t ∈ ts, t < 2 ^ p) :
    vsz (intList ts) ≤ ts.length * (p + 3) + 1 := by
  induction ts with
  | nil => simp [intList, ofList, vsz, Val.enc]
  | cons x t ih =>
    have hx : x < 2 ^ p := h x (by simp)
    have ht : ∀ y ∈ t, y < 2 ^ p := fun y hy => h y (by simp [hy])
    have ih' := ih ht
    have hstep : intList (x :: t) = Val.cons (Val.int (x : ℤ)) (intList t) := rfl
    rw [hstep, MrgKit.vsz_cons', MrgKit.vsz_int']
    have hxsz : x.size ≤ p := by rw [Nat.size_le]; exact hx
    have hx2 : isz (↑x : ℤ) = x.size + 2 := by simp [isz]
    rw [hx2]
    simp only [List.length_cons]
    nlinarith [ih', hxsz]

theorem arrSize : Work.SynFFT.ArrSizeProp :=
  ⟨vsz_cvecVal_tight, vsz_rarrVal_tight, vsz_intList_le⟩

end Work.SynFFT

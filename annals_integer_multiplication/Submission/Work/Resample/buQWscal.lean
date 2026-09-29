import Mathlib
import Submission.Work.Resample.buQWscalDefs
import Submission.Work.Resample.auPreKit
import Submission.Work.Resample.buScInV
import Submission.Work.Resample.buScRecsFacts
import Submission.Work.Resample.buScKeysFacts
import Submission.Work.Resample.buScSorted
import Submission.Work.Resample.buScOut
import Submission.Work.Resample.buScZipEq
import Submission.Work.Resample.buZipWithFun
import Submission.Work.Resample.buScElemWord
import Submission.Work.Resample.buScStripWord
import Submission.Work.Resample.buScArith
import Submission.Work.Resample.buScElemBracket
import Submission.Work.Resample.buScSizes

/-!
# `Work.Resample.buQWscal`: the scaling stage `D̃'` and the final permutation `P̃_sᵀ`

The stage reads the vector `u` (length `s`, in the disc of radius `2^{p+1}`) together with the
diagonal weights `buWdL` (entry 9 of `buTabList`), the key list `buKeysS` (entry 8) and the
parameters `s`, `p`, and produces `buPermL s t _ hcop.symm (buDscL (buWd p α s t) p s u)`.

The word is: `zipWith` of `buWdL` with the vector (element word: multiply by the weight and
truncate-divide by `2^p`), then the label/sort/take/strip permutation driven by the keys
`i ↦ (t·i) mod s`, which is the same move as in the selection stage `buQWsel`.

## Proof shape

`buQWscal` is assembled from the library words (`KernelLib.pick/roll/drop/consV/zipWith/mapList`,
`LayoutLib.take/sortByKey`, `IntLib.pow2`) and the element words `buScElemWord` (scaling) and
`buScStripWord` (dropping the key).  The programme is

`G₁ ; zip elP ; roll 2 ; zip consV ; sortByKey ; roll 1 ; drop ; roll 1 ; take s ; mapList stP ;
 roll 1 ; drop`

where `G₁ = pick 4 ; pow2 ; roll 1 ; roll 2` brings `int (2^p)` into place and puts the weight list
on top of the vector.  Each stage is a `WSw`/`Pipe` triple; the composition is right-nested to match
the programme, and every stage cost is normalised to `buScQ S s p = 400·S·(s+1)·(buScB p+1)·(p+1)`
with `S` the sum of the library constants.  The whole chain then costs at most `14·buScQ`, which is
absorbed by `Kc = 2^(2 ^ S + 80)` as proved in `buScArith`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample
open HvdH

/-! ## plumbing -/

theorem buScWord_le (KL : KernelLib) {main p : Cmd} {P : List Val → Prop}
    {Q : List Val → List Val → Prop} {C C' : List Val → ℕ} (h : WordR main p P Q C)
    (hCC : ∀ vs, P vs → C vs ≤ C' vs) : WordR main p P Q C' :=
  KL.conseq main p P P Q Q C C' h (fun vs hvs => hvs) (fun vs out _ hout => hout) hCC

theorem buScWord_post (KL : KernelLib) {main p : Cmd} {P : List Val → Prop}
    {Q Q' : List Val → List Val → Prop} {C : List Val → ℕ} (h : WordR main p P Q C)
    (hQ : ∀ vs out, P vs → Q vs out → Q' vs out) : WordR main p P Q' C :=
  KL.conseq main p P P Q Q' C C h (fun vs hvs => hvs) hQ (fun vs _ => le_rfl)

/-- an element word acting on the *fixed front* `x :: y :: T` and preserving the tail `T`. -/
theorem Pipe.ofElem {main q : Cmd} {x y z : Val} {T : List Val} {c : ℕ}
    (h : ∀ T' : List Val, WordR main q (fun vs => vs = x :: y :: T')
      (fun _ out => out = z :: T') (fun _ => c)) :
    Pipe main q (x :: y :: T) (z :: T) c := by
  intro rest vs hvs s R hR
  have hv : vs = x :: y :: (T ++ rest) := by rw [hvs]; simp [List.cons_append]
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h (T ++ rest) vs hv s R hR
  exact ⟨out, s', n, by rw [hout]; simp [List.cons_append], hev, hn, hstk, hoth⟩

/-- the `consV` element word. -/
theorem Pipe.consElem {prog : Cmd} {K : ℕ} (main : Cmd)
    (h : WordR main prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest) (fun _ => K))
    (x y : Val) (T : List Val) :
    Pipe main prog (x :: y :: T) (Val.cons x y :: T) K := by
  intro rest vs hvs s R hR
  have hv : vs = x :: y :: (T ++ rest) := by rw [hvs]; simp [List.cons_append]
  obtain ⟨out, s', n, ⟨a, b, r, hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h vs (by rw [hv]; simp) s R hR
  obtain ⟨h1, h2, h3⟩ := Work.Fx.cons_inj3 (hvs'.symm.trans hv)
  refine ⟨out, s', n, ?_, hev, hn, hstk, hoth⟩
  rw [hout, h1, h2, h3]
  simp [List.cons_append]

/-- `LL.take` as a fixed-window word. -/
theorem Pipe.takeOf {prog : Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ (m : Cmd) (k : ℕ) (xs : List Val), WordR m prog
      (fun vs => ∃ rest, vs = .int (k : ℤ) :: ofList xs :: rest)
      (fun vs out => ∃ rest, vs = .int (k : ℤ) :: ofList xs :: rest ∧ out = ofList (xs.take k) :: rest)
      (fun _ => K * (vsz (ofList xs) + isz (k : ℤ) + 1)))
    {k : ℕ} {xs : List Val} :
    Pipe main prog [.int (k : ℤ), ofList xs] [ofList (xs.take k)]
      (K * (vsz (ofList xs) + isz (k : ℤ) + 1)) := by
  intro rest vs hvs s R hR
  have hv : vs = .int (k : ℤ) :: ofList xs :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨r', hvs', hout⟩, hev, hn, hstk, hoth⟩ := h main k xs vs ⟨rest, hv⟩ s R hR
  have hr : r' = rest := (List.cons.inj (List.cons.inj (hvs'.symm.trans hv)).2).2
  refine ⟨out, s', n, ?_, hev, hn, hstk, hoth⟩
  rw [hout, hr]
  rfl

theorem nat_le_mul_succ (m p : ℕ) : m ≤ m * (p + 1) := Nat.le_mul_of_pos_right m (by omega)

theorem mul_le_mul_right'' {a b c : ℕ} (h : a ≤ b) : a * c ≤ b * c := Nat.mul_le_mul_right c h

theorem le_buScV_succ (s p : ℕ) : buScB p + 1 ≤ (s + 1) * (buScB p + 1) := by
  calc buScB p + 1 = 1 * (buScB p + 1) := by ring
    _ ≤ (s + 1) * (buScB p + 1) := mul_le_mul_right'' (by omega)

theorem one_le_Vp (s p : ℕ) : 1 ≤ ((s + 1) * (buScB p + 1)) * (p + 1) :=
  Nat.succ_le_of_lt (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))

theorem mul_le_mul_left'' {a b c : ℕ} (h : a ≤ b) : c * a ≤ c * b := Nat.mul_le_mul_left c h


/-- the `zipWith` stage in fixed-window form, with a fixed tail `T` under the two lists. -/
theorem Pipe.zipFun {comb : Cmd → Cmd} {Kz : ℕ}
    (hZ : ∀ (main q : Cmd) (T : List Val) (P : Val → Val → Prop) (F : Val → Val → Val)
        (c L : ℕ),
      (∀ x y, P x y → WordR main q (fun vs => vs = x :: y :: T)
        (fun _ out => out = F x y :: T) (fun _ => c)) →
      (∀ x y, P x y → vsz (F x y) ≤ L) →
      ∀ xs ys : List Val, xs.length = ys.length →
        (∀ i < xs.length, P (xs.getD i Val.nil) (ys.getD i Val.nil)) →
        (∀ x ∈ xs ++ ys, vsz x ≤ L) →
        WordR main (comb q) (fun vs => vs = ofList xs :: ofList ys :: T)
          (fun _ out => out = ofList (List.zipWith F xs ys) :: T)
          (fun _ => xs.length * (c + Kz * (L + 1)) + Kz))
    (KL : KernelLib) {main q : Cmd} {T : List Val} {P : Val → Val → Prop} {F : Val → Val → Val}
    {c L : ℕ}
    (hper : ∀ x y, P x y → Pipe main q (x :: y :: T) (F x y :: T) c)
    (hF : ∀ x y, P x y → vsz (F x y) ≤ L)
    (xs ys : List Val) (hlen : xs.length = ys.length)
    (hP : ∀ i < xs.length, P (xs.getD i Val.nil) (ys.getD i Val.nil))
    (hL : ∀ x ∈ xs ++ ys, vsz x ≤ L) :
    Pipe main (comb q) (ofList xs :: ofList ys :: T) (ofList (List.zipWith F xs ys) :: T)
      (xs.length * (c + Kz * (L + 1)) + Kz) := by
  intro rest
  have hper' : ∀ x y, P x y → WordR main q (fun vs => vs = x :: y :: (T ++ rest))
      (fun _ out => out = F x y :: (T ++ rest)) (fun _ => c) := by
    intro x y hxy
    have h := hper x y hxy rest
    simpa [List.cons_append] using h
  have hmain := hZ main q (T ++ rest) P F c L hper' hF xs ys hlen hP hL
  refine buScWord_le KL (KL.conseq main (comb q)
    (fun vs => vs = ofList xs :: ofList ys :: (T ++ rest))
    (fun vs => vs = (ofList xs :: ofList ys :: T) ++ rest)
    (fun _ out => out = ofList (List.zipWith F xs ys) :: (T ++ rest))
    (fun _ out => out = (ofList (List.zipWith F xs ys) :: T) ++ rest)
    (fun _ => xs.length * (c + Kz * (L + 1)) + Kz)
    (fun _ => xs.length * (c + Kz * (L + 1)) + Kz)
    hmain (fun vs hvs => by simpa [List.cons_append] using hvs)
    (fun vs out hvs hout => by simpa [List.cons_append] using hout)
    (fun vs _ => le_rfl)) (fun vs _ => le_rfl)

/-- the `sortByKey` stage in fixed-window form (existential output). -/
theorem WSw.sortOf {prog : Cmd} {K : ℕ} (KL : KernelLib) (main : Cmd)
    (h : ∀ (m : Cmd) (xs : List Val),
      (∀ x ∈ xs, ∃ (k : ℕ) (v : Val), x = .cons (.int (k : ℤ)) v) → (xs.map pairKey).Nodup →
      WordR m prog (fun vs => ∃ rest, vs = ofList xs :: rest)
        (fun vs out => ∃ rest ys, vs = ofList xs :: rest ∧ out = ofList ys :: rest ∧ ys.Perm xs ∧
          ys.Pairwise fun a b => pairKey a < pairKey b)
        (fun _ => K * (vsz (ofList xs) + 1) * (xs.length.size + 1)))
    (xs : List Val) (hshape : ∀ x ∈ xs, ∃ (k : ℕ) (v : Val), x = .cons (.int (k : ℤ)) v)
    (hnd : (xs.map pairKey).Nodup) (T : List Val) :
    WSw main prog (ofList xs :: T)
      (fun Bv => ∃ ys, ys.Perm xs ∧ ys.Pairwise (fun a b => pairKey a < pairKey b) ∧
        Bv = ofList ys :: T)
      (K * (vsz (ofList xs) + 1) * (xs.length.size + 1)) := by
  intro rest vs hvs s R hR
  have hv : vs = ofList xs :: (T ++ rest) := by rw [hvs]; simp [List.cons_append]
  obtain ⟨out, s', n, ⟨r', ys, hvs', hout, hperm, hsort⟩, hev, hn, hstk, hoth⟩ :=
    h main xs hshape hnd vs ⟨T ++ rest, hv⟩ s R hR
  have hr : r' = T ++ rest := (List.cons.inj (hvs'.symm.trans hv)).2
  refine ⟨(ofList ys :: T) ++ rest, s', n, ⟨ofList ys :: T, ⟨ys, hperm, hsort, rfl⟩, rfl⟩,
    hev, hn, ?_, hoth⟩
  rw [hstk, hout, hr]
  simp [List.cons_append]

/-! ## cost and size helpers -/

theorem le_V_of_le_buScB {s p a : ℕ} (h : a ≤ buScB p) : a ≤ (s + 1) * (buScB p + 1) := by
  have h1 : 1 ≤ s + 1 := by omega
  calc a ≤ buScB p := h
    _ ≤ buScB p + 1 := by omega
    _ = 1 * (buScB p + 1) := by ring_nf
    _ ≤ (s + 1) * (buScB p + 1) := mul_le_mul_right'' h1

theorem one_le_sq (p : ℕ) : 1 ≤ (p + 1) * (p + 1) := Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))

/-- the cost shape of the two `zipWith` stages. -/
theorem one_le_Bp (p : ℕ) : 1 ≤ (buScB p + 1) * (p + 1) :=
  Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))

theorem buScQ_zip {S s p c Kz : ℕ} (hc : c ≤ 324 * S * (p + 1) * (p + 1)) (hKz : Kz ≤ S) :
    s * (c + Kz * (buScB p + 1)) + Kz
      ≤ 400 * S * (((s + 1) * (buScB p + 1)) * (p + 1)) := by
  have hB1 : p + 1 ≤ buScB p + 1 := by simp only [buScB]; omega
  have hbr : c + Kz * (buScB p + 1) ≤ 325 * (S * ((buScB p + 1) * (p + 1))) := by
    have hc1 : c ≤ 324 * (S * ((buScB p + 1) * (p + 1))) := by
      have hm : (p + 1) * (p + 1) ≤ (buScB p + 1) * (p + 1) :=
        Nat.mul_le_mul hB1 (le_refl (p + 1))
      calc c ≤ 324 * S * (p + 1) * (p + 1) := hc
        _ = 324 * (S * ((p + 1) * (p + 1))) := by ring
        _ ≤ 324 * (S * ((buScB p + 1) * (p + 1))) :=
            Nat.mul_le_mul_left 324 (Nat.mul_le_mul_left S hm)
    have hb : Kz * (buScB p + 1) ≤ S * ((buScB p + 1) * (p + 1)) := by
      calc Kz * (buScB p + 1) ≤ S * (buScB p + 1) := Nat.mul_le_mul_right (buScB p + 1) hKz
        _ ≤ S * ((buScB p + 1) * (p + 1)) :=
            Nat.mul_le_mul_left S (Nat.le_mul_of_pos_right (buScB p + 1) (by omega))
    calc c + Kz * (buScB p + 1)
        ≤ 324 * (S * ((buScB p + 1) * (p + 1))) + S * ((buScB p + 1) * (p + 1)) :=
          add_le_add hc1 hb
      _ ≤ 325 * (S * ((buScB p + 1) * (p + 1))) := by
          have he : 324 * (S * ((buScB p + 1) * (p + 1))) + S * ((buScB p + 1) * (p + 1))
              = 325 * (S * ((buScB p + 1) * (p + 1))) := by ring_nf
          exact le_of_eq he
  have hkx : Kz ≤ 325 * (S * ((buScB p + 1) * (p + 1))) := by
    have h2 : S ≤ S * ((buScB p + 1) * (p + 1)) := by
      calc S = S * 1 := (Nat.mul_one S).symm
        _ ≤ S * ((buScB p + 1) * (p + 1)) := Nat.mul_le_mul_left S (one_le_Bp p)
    have h3 : S * ((buScB p + 1) * (p + 1)) ≤ 325 * (S * ((buScB p + 1) * (p + 1))) := by
      calc S * ((buScB p + 1) * (p + 1)) = 1 * (S * ((buScB p + 1) * (p + 1))) := by ring
        _ ≤ 325 * (S * ((buScB p + 1) * (p + 1))) :=
            Nat.mul_le_mul_right (S * ((buScB p + 1) * (p + 1))) (by omega : 1 ≤ 325)
    exact le_trans (le_trans hKz h2) h3
  calc s * (c + Kz * (buScB p + 1)) + Kz
      ≤ s * (325 * (S * ((buScB p + 1) * (p + 1))))
          + 325 * (S * ((buScB p + 1) * (p + 1))) :=
        add_le_add (Nat.mul_le_mul_left s hbr) hkx
    _ = 325 * S * (s + 1) * (buScB p + 1) * (p + 1) := by ring
    _ ≤ 400 * S * (((s + 1) * (buScB p + 1)) * (p + 1)) := by
        calc 325 * S * (s + 1) * (buScB p + 1) * (p + 1)
            = 325 * (S * (s + 1) * ((buScB p + 1) * (p + 1))) := by ring
          _ ≤ 400 * (S * (s + 1) * ((buScB p + 1) * (p + 1))) :=
                Nat.mul_le_mul_right (S * (s + 1) * ((buScB p + 1) * (p + 1))) (by omega : 325 ≤ 400)
          _ = 400 * S * (((s + 1) * (buScB p + 1)) * (p + 1)) := by ring

/-- the cost shape of the `mapList` stage. -/
theorem buScQ_mapList {S s p K1 K2 : ℕ} (h1 : K1 ≤ S) (h2 : K2 ≤ S) :
    s * (K1 * buScB p + K2 * (buScB p + 1)) + K2
      ≤ 400 * S * (((s + 1) * (buScB p + 1)) * (p + 1)) := by
  have hBp : buScB p ≤ buScB p + 1 := by omega
  have hS1 : S ≤ S * (buScB p + 1) := by
    calc S = S * 1 := (Nat.mul_one S).symm
      _ ≤ S * (buScB p + 1) := Nat.mul_le_mul_left S (by omega)
  have hsum : K1 * buScB p + K2 * (buScB p + 1) ≤ 2 * (S * (buScB p + 1)) := by
    have h1' : K1 * buScB p ≤ S * (buScB p + 1) :=
      le_trans (Nat.mul_le_mul_right (buScB p) h1) (Nat.mul_le_mul_left S hBp)
    have h2' : K2 * (buScB p + 1) ≤ S * (buScB p + 1) := Nat.mul_le_mul_right (buScB p + 1) h2
    calc K1 * buScB p + K2 * (buScB p + 1) ≤ S * (buScB p + 1) + S * (buScB p + 1) :=
          add_le_add h1' h2'
      _ = 2 * (S * (buScB p + 1)) := by ring
  have hz : K2 ≤ 2 * (S * (buScB p + 1)) := by
    have h3 : S * (buScB p + 1) ≤ 2 * (S * (buScB p + 1)) := by
      calc S * (buScB p + 1) = 1 * (S * (buScB p + 1)) := by ring
        _ ≤ 2 * (S * (buScB p + 1)) :=
            Nat.mul_le_mul_right (S * (buScB p + 1)) (by omega : 1 ≤ 2)
    exact le_trans (le_trans h2 hS1) h3
  calc s * (K1 * buScB p + K2 * (buScB p + 1)) + K2
      ≤ s * (2 * (S * (buScB p + 1))) + 2 * (S * (buScB p + 1)) :=
        add_le_add (Nat.mul_le_mul_left s hsum) hz
    _ = 2 * S * (s + 1) * (buScB p + 1) := by ring
    _ ≤ 400 * S * (((s + 1) * (buScB p + 1)) * (p + 1)) := by
        calc 2 * S * (s + 1) * (buScB p + 1)
            = 2 * (S * (s + 1) * (buScB p + 1)) := by ring
          _ ≤ (400 * (p + 1)) * (S * (s + 1) * (buScB p + 1)) :=
                Nat.mul_le_mul_right (S * (s + 1) * (buScB p + 1)) (by omega : 2 ≤ 400 * (p + 1))
          _ = 400 * S * (((s + 1) * (buScB p + 1)) * (p + 1)) := by ring

theorem szl5 (a b c d e : Val) :
    Work.Fx.szl [a, b, c, d, e] = vsz a + vsz b + vsz c + vsz d + vsz e := by
  simp [Work.Fx.szl, Nat.add_assoc]

theorem szl2 (a b : Val) : Work.Fx.szl [a, b] = vsz a + vsz b := by
  simp [Work.Fx.szl]

theorem szl3 (a b c : Val) : Work.Fx.szl [a, b, c] = vsz a + vsz b + vsz c := by
  simp [Work.Fx.szl, Nat.add_assoc]

theorem szl4 (a b c d : Val) : Work.Fx.szl [a, b, c, d] = vsz a + vsz b + vsz c + vsz d := by
  simp [Work.Fx.szl, Nat.add_assoc]

theorem szl1 (a : Val) : Work.Fx.szl [a] = vsz a := by simp [Work.Fx.szl]

/-- size of one element produced by the scaling element word. -/
theorem isz_tdiv_mul_le {p : ℕ} {W a : ℤ} (hW : 8 * W.natAbs ≤ 3 * 2 ^ p)
    (ha : a.natAbs ≤ 2 ^ (p + 1)) : isz (Int.tdiv (W * a) ((2 : ℤ) ^ p)) ≤ p + 2 := by
  have hlt : (W * a).natAbs < 2 ^ (2 * p) := by
    have h8 : 8 * (W * a).natAbs < 8 * 2 ^ (2 * p) := by
      rw [Int.natAbs_mul]
      calc 8 * (W.natAbs * a.natAbs) = (8 * W.natAbs) * a.natAbs := by ring_nf
        _ ≤ (3 * 2 ^ p) * 2 ^ (p + 1) := Nat.mul_le_mul hW ha
        _ = 3 * 2 ^ (2 * p + 1) := by
            rw [mul_assoc, ← pow_add, show p + (p + 1) = 2 * p + 1 by omega]
        _ < 8 * 2 ^ (2 * p) := by
            have hpos : 0 < 2 ^ (2 * p) := by positivity
            rw [show (2:ℕ) ^ (2 * p + 1) = 2 ^ (2 * p) * 2 by rw [pow_succ]]
            nlinarith
    exact Nat.lt_of_mul_lt_mul_left h8
  have hlt2 : (W * a).natAbs < 2 ^ p * 2 ^ p := by
    rw [show (2:ℕ) ^ (2 * p) = 2 ^ p * 2 ^ p by rw [← pow_add]; congr 1; omega] at hlt
    exact hlt
  have hdiv : (W * a).natAbs / 2 ^ p < 2 ^ p := Nat.div_lt_of_lt_mul hlt2
  have h2p : (Int.tdiv (W * a) ((2 : ℤ) ^ p)).natAbs = (W * a).natAbs / 2 ^ p := by
    rw [Int.natAbs_tdiv, Int.natAbs_pow]
    norm_num
    rfl
  have hmain : (Int.tdiv (W * a) ((2 : ℤ) ^ p)).natAbs < 2 ^ p := by
    rw [h2p]; exact hdiv
  exact Work.Fx.isz_le_of_natAbs_lt hmain

theorem vsz_buScProd_le {p : ℕ} {W a b : ℤ} (hW : 8 * W.natAbs ≤ 3 * 2 ^ p)
    (ha : a.natAbs ≤ 2 ^ (p + 1)) (hb : b.natAbs ≤ 2 ^ (p + 1)) :
    vsz (buScProd ((2 : ℤ) ^ p) (.int W) (.cons (.int a) (.int b))) ≤ buScB p := by
  rw [buScProd_apply, Work.Fx.vsz_cons, Work.Fx.vsz_int, Work.Fx.vsz_int]
  have h1 := isz_tdiv_mul_le hW ha
  have h2 := isz_tdiv_mul_le hW hb
  simp only [buScB] at *
  omega

/-- an element word acting on `x :: y :: D :: T` and preserving the tail `D :: T`. -/
theorem Pipe.ofElemD {main q : Cmd} {x y z D : Val} {T : List Val} {c : ℕ}
    (h : ∀ T' : List Val, WordR main q (fun vs => vs = x :: y :: D :: T')
      (fun _ out => out = z :: D :: T') (fun _ => c)) :
    Pipe main q (x :: y :: D :: T) (z :: D :: T) c := by
  intro rest vs hvs s R hR
  have hv : vs = x :: y :: D :: (T ++ rest) := by rw [hvs]; simp [List.cons_append]
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h (T ++ rest) vs hv s R hR
  exact ⟨out, s', n, by rw [hout]; simp [List.cons_append], hev, hn, hstk, hoth⟩

/-- a unary element word acting on `x :: T`. -/
theorem Pipe.ofUn {main q : Cmd} {x z : Val} {c : ℕ}
    (h : ∀ T' : List Val, WordR main q (fun vs => vs = x :: T') (fun _ out => out = z :: T')
      (fun _ => c)) :
    Pipe main q [x] [z] c := by
  intro rest vs hvs s R hR
  have hv : vs = x :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h rest vs hv s R hR
  exact ⟨out, s', n, hout, hev, hn, hstk, hoth⟩

/-- cost bound with the `(p+1)` slack. -/
theorem mul_le_buScQ {S s p c K : ℕ} (hK : c * K ≤ 400 * S) :
    c * K * ((s + 1) * (buScB p + 1)) * (p + 1)
      ≤ 400 * S * (((s + 1) * (buScB p + 1)) * (p + 1)) := by
  have h := Nat.mul_le_mul_right (((s + 1) * (buScB p + 1)) * (p + 1)) hK
  calc c * K * ((s + 1) * (buScB p + 1)) * (p + 1)
      = (c * K) * (((s + 1) * (buScB p + 1)) * (p + 1)) := by ring_nf
    _ ≤ (400 * S) * (((s + 1) * (buScB p + 1)) * (p + 1)) := h
    _ = 400 * S * (((s + 1) * (buScB p + 1)) * (p + 1)) := by ring_nf

/-- cost bound without the `(p+1)` slack. -/
theorem mul_le_buScQ' {S s p c K : ℕ} (hK : c * K ≤ 400 * S) :
    c * K * ((s + 1) * (buScB p + 1))
      ≤ 400 * S * (((s + 1) * (buScB p + 1)) * (p + 1)) := by
  have h1 : c * K ≤ 400 * S * (p + 1) :=
    le_trans hK (nat_le_mul_succ (400 * S) p)
  have h := Nat.mul_le_mul_right ((s + 1) * (buScB p + 1)) h1
  calc c * K * ((s + 1) * (buScB p + 1)) = (c * K) * ((s + 1) * (buScB p + 1)) := by ring_nf
    _ ≤ (400 * S * (p + 1)) * ((s + 1) * (buScB p + 1)) := h
    _ = 400 * S * (((s + 1) * (buScB p + 1)) * (p + 1)) := by ring_nf

/-- **the scaling stage `D̃'` + final permutation**, proved by assembling the library words. -/
theorem buQWscal (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib) (FL : HvdH.FxLib) :
    ∃ (q : HvdH.Cmd) (Kc : ℕ),
    ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t) (htp : t < 2 ^ p)
      (hα : 2 ≤ α)
      (hwd : ∀ ℓ : ℤ, 8 * (Work.Resample.buWd p α s t ℓ).natAbs ≤ 3 * 2 ^ p)
      (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm → Kc * p < N →
    HvdH.WordR main q
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
      (fun _ => Kc * (s + 1) * (p + 1) * (p + 1) + Kc * (s + 1) * (Cm (Kc * p) + p + 1)) := by
  obtain ⟨zipC, Kz, hzipF⟩ := buZipWithFun KL
  obtain ⟨combML, Kml, hML⟩ := KL.mapList
  obtain ⟨pkP, Kpk, hpk⟩ := KL.pick
  obtain ⟨rlP, Krl, hrl⟩ := KL.roll
  obtain ⟨drP, Kdr, hdr⟩ := KL.drop
  obtain ⟨cVP, Kv, hcV⟩ := KL.consV
  obtain ⟨tkP, Ktk, htk⟩ := LL.take
  obtain ⟨srtP, Ksrt, hsrt⟩ := LL.sortByKey
  obtain ⟨pwP, Kpw, hpw⟩ := IL.pow2
  obtain ⟨elP, Kel, hel⟩ := buScElemWord KL IL
  obtain ⟨stP, Kst, hstW⟩ := buScStripWord KL
  let S : ℕ := Kpk + Krl + Kdr + Kv + Ktk + Ksrt + Kpw + Kz + Kml + Kel + Kst + 50
  have hKpkS : Kpk ≤ S := by omega
  have hKrlS : Krl ≤ S := by omega
  have hKdrS : Kdr ≤ S := by omega
  have hKvS : Kv ≤ S := by omega
  have hKtkS : Ktk ≤ S := by omega
  have hKsrtS : Ksrt ≤ S := by omega
  have hKpwS : Kpw ≤ S := by omega
  have hKzS : Kz ≤ S := by omega
  have hKmlS : Kml ≤ S := by omega
  have hKelS : Kel ≤ S := by omega
  have hKstS : Kst ≤ S := by omega
  have hS1 : 1 ≤ S := by omega
  refine ⟨.seq (.seq (pkP 4) (.seq pwP (.seq (rlP 1) (rlP 2))))
      (.seq (zipC elP) (.seq (rlP 2) (.seq (zipC cVP) (.seq srtP
        (.seq (rlP 1) (.seq drP (.seq (rlP 1) (.seq tkP (.seq (combML stP)
          (.seq (rlP 1) drP)))))))))), 2 ^ (2 ^ S + 80), ?_⟩
  intro p α s t hs hst hcop htp hα hwd main N Cm hmon hmul hN
  intro vs hPre s0 R hR
  obtain ⟨u, rest, hvs, hulen, hV⟩ := hPre
  subst hvs
  let iP : Val := Val.int (p : ℤ)
  let iS : Val := Val.int (s : ℤ)
  let iD : Val := Val.int ((2 : ℤ) ^ p)
  let WdL : Val := buWdL p α s t
  let KeysS : Val := buKeysS s t
  let d : List (ℤ × ℤ) := buDscL (buWd p α s t) p s u
  let recs : List Val := buScRecs s t d
  let cu : ℕ := 324 * Kel * (p + 1) * (p + 1)
  let WdList : List Val := (List.ofFn (fun i : Fin s => buWd p α s t (i : ℤ))).map Val.int
  let uList : List Val := u.map cfxVal
  have hVpos : 1 ≤ (s + 1) * (buScB p + 1) :=
    Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
  have hdlen : d.length = s := by
    show (buDscL (buWd p α s t) p s u).length = s
    simp [buDscL, hulen]
  have hrep : buInV (2 ^ p) (List.replicate s (0, 0)) := by
    intro z hz
    simp only [List.mem_replicate] at hz
    obtain ⟨-, rfl⟩ := hz
    show (0 : ℤ) ^ 2 + (0 : ℤ) ^ 2 ≤ (((2 ^ p : ℕ)) : ℤ) ^ 2
    nlinarith [sq_nonneg (((2 ^ p : ℕ)) : ℤ)]
  have hVd : buInV (2 ^ p) d :=
    (buScInV p s t hs hcop (buWd p α s t) u (List.replicate s (0, 0)) hulen hwd hV
      (by simp) hrep).1
  have hrecslen : recs.length = s := by
    show (buScRecs s t d).length = s
    rw [(buScRecsFacts s t d hdlen).2.2.2]
  obtain ⟨hsu1, hsu2, hsu3, hsu4, hsu5, hsu6, hsu7, hsu8, hsu9, hsu10, hsu11, hsu12⟩ :=
    buScSizes p α s t hs hst hcop htp hwd u hulen hV d hdlen hVd recs (List.Perm.refl recs)
  have hlt2p : ∀ {W : ℤ}, 8 * W.natAbs ≤ 3 * 2 ^ p → W.natAbs < 2 ^ p := by
    intro W hW
    have h8 : 8 * W.natAbs < 8 * 2 ^ p := by
      calc 8 * W.natAbs ≤ 3 * 2 ^ p := hW
        _ < 8 * 2 ^ p := by
            have hpos : 0 < 2 ^ p := by positivity
            nlinarith
    exact Nat.lt_of_mul_lt_mul_left h8
  have hwdsz : ∀ ℓ : ℤ, isz (buWd p α s t ℓ) ≤ buScB p := by
    intro ℓ
    have h1 : isz (buWd p α s t ℓ) ≤ p + 2 := Work.Fx.isz_le_of_natAbs_lt (hlt2p (hwd ℓ))
    simp only [buScB] at *
    omega
  have hcfxsz : ∀ z : ℤ × ℤ, buIn (2 ^ (p + 1)) z → vsz (cfxVal z) ≤ buScB p := by
    intro z hz
    obtain ⟨h1, h2⟩ := buIn_coord hz
    have e1 : isz z.1 ≤ p + 4 := by
      refine Work.Fx.isz_le_of_natAbs_lt (n := p + 2) ?_
      calc z.1.natAbs ≤ 2 ^ (p + 1) := h1
        _ < 2 ^ (p + 2) := Nat.pow_lt_pow_succ (by norm_num)
    have e2 : isz z.2 ≤ p + 4 := by
      refine Work.Fx.isz_le_of_natAbs_lt (n := p + 2) ?_
      calc z.2.natAbs ≤ 2 ^ (p + 1) := h2
        _ < 2 ^ (p + 2) := Nat.pow_lt_pow_succ (by norm_num)
    rw [Work.Fx.vsz_cfxVal]
    simp only [buScB] at *
    omega
  have hcfxszp : ∀ z : ℤ × ℤ, buIn (2 ^ p) z → vsz (cfxVal z) ≤ buScB p := by
    intro z hz
    obtain ⟨h1, h2⟩ := buIn_coord hz
    have e1 : isz z.1 ≤ p + 3 := by
      refine Work.Fx.isz_le_of_natAbs_lt ?_
      calc z.1.natAbs ≤ 2 ^ p := h1
        _ < 2 ^ (p + 1) := Nat.pow_lt_pow_succ (by norm_num)
    have e2 : isz z.2 ≤ p + 3 := by
      refine Work.Fx.isz_le_of_natAbs_lt ?_
      calc z.2.natAbs ≤ 2 ^ p := h2
        _ < 2 ^ (p + 1) := Nat.pow_lt_pow_succ (by norm_num)
    rw [Work.Fx.vsz_cfxVal]
    simp only [buScB] at *
    omega
  have hVs : s ≤ 2 ^ p := by omega
  have hkeysz : ∀ i : ℕ, isz (((egKeyS s t i : ℕ) : ℤ)) ≤ buScB p := by
    intro i
    have h1 : ((egKeyS s t i : ℕ) : ℤ).natAbs < 2 ^ (p + 1) := by
      rw [Int.natAbs_natCast]
      calc egKeyS s t i < s := Nat.mod_lt _ (by omega)
        _ < t := hst
        _ < 2 ^ p := htp
        _ < 2 ^ (p + 1) := Nat.pow_lt_pow_succ (by norm_num)
    have h2 := Work.Fx.isz_le_of_natAbs_lt (n := p + 1) h1
    simp only [buScB] at *
    omega
  have hA1 : WSw main (pkP 4) [cvecVal u, WdL, KeysS, iS, iP]
      (fun B => B = [iP, cvecVal u, WdL, KeysS, iS, iP]) (30 * Kpk * ((s + 1) * (buScB p + 1))) := by
    refine WSw.cost KL (WSw.ofPipe KL (Pipe.pick (main := main) (prog := pkP) (K := Kpk) hpk
      (A := [cvecVal u, WdL, KeysS, iS, iP]) (k := 4) (by simp))) ?_
    have hsz : Work.Fx.szl (([cvecVal u, WdL, KeysS, iS, iP] : List Val).take (4 + 1)) ≤ 5 * ((s + 1) * (buScB p + 1)) := by
      rw [show ([cvecVal u, WdL, KeysS, iS, iP] : List Val).take (4 + 1)
          = [cvecVal u, WdL, KeysS, iS, iP] from rfl, szl5]
      have h4 : vsz iS ≤ ((s + 1) * (buScB p + 1)) := by
        rw [show iS = Val.int (s : ℤ) from rfl, Work.Fx.vsz_int]
        exact le_V_of_le_buScB hsu8
      have h5 : vsz iP ≤ ((s + 1) * (buScB p + 1)) := by
        rw [show iP = Val.int (p : ℤ) from rfl, Work.Fx.vsz_int]
        exact le_V_of_le_buScB hsu9
      have h6 : vsz WdL ≤ ((s + 1) * (buScB p + 1)) := hsu2
      have h7 : vsz KeysS ≤ ((s + 1) * (buScB p + 1)) := hsu3
      omega
    calc Kpk * (4 + 1) * (Work.Fx.szl
            (([cvecVal u, WdL, KeysS, iS, iP] : List Val).take (4 + 1)) + 1)
        ≤ Kpk * 5 * (5 * ((s + 1) * (buScB p + 1)) + 1) :=
          mul_le_mul_left'' (Nat.add_le_add_right hsz 1)
      _ ≤ 30 * Kpk * ((s + 1) * (buScB p + 1)) := by
          have h6 : 5 * ((s + 1) * (buScB p + 1)) + 1 ≤ 6 * ((s + 1) * (buScB p + 1)) := by omega
          calc Kpk * 5 * (5 * ((s + 1) * (buScB p + 1)) + 1) ≤ Kpk * 5 * (6 * ((s + 1) * (buScB p + 1))) :=
                mul_le_mul_left'' h6
            _ = 30 * Kpk * ((s + 1) * (buScB p + 1)) := by ring_nf
  have hA2 : WSw main pwP [iP, cvecVal u, WdL, KeysS, iS, iP]
      (fun B => B = [iD, cvecVal u, WdL, KeysS, iS, iP]) (2 * Kpw * ((s + 1) * (buScB p + 1)) * (p + 1)) := by
    have hpipe : Pipe main pwP [iP, cvecVal u, WdL, KeysS, iS, iP]
        [iD, cvecVal u, WdL, KeysS, iS, iP] (Kpw * (p + isz ((p : ℤ)))) := by
      have h0 := Pipe.appendTail [cvecVal u, WdL, KeysS, iS, iP]
        (Pipe.unOp (main := main) (h := hpw main) (a := (p : ℤ)) (by positivity))
      simpa [iP, iD, Int.toNat_natCast] using h0
    refine WSw.cost KL (WSw.ofPipe KL hpipe) ?_
    have h1 : p + isz ((p : ℤ)) ≤ 2 * (((s + 1) * (buScB p + 1)) * (p + 1)) := by
      have hisz : isz ((p : ℤ)) ≤ p + 2 := by
        have hna : ((p : ℤ)).natAbs = p := Int.natAbs_natCast p
        simp only [isz, hna]
        have := Nat.size_le.mpr (Nat.lt_two_pow_self (n := p))
        omega
      have h2 : 2 * (p + 1) ≤ 2 * (((s + 1) * (buScB p + 1)) * (p + 1)) :=
        Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_left _ (by omega))
      omega
    calc Kpw * (p + isz ((p : ℤ))) ≤ Kpw * (2 * (((s + 1) * (buScB p + 1)) * (p + 1))) := mul_le_mul_left'' h1
      _ = 2 * Kpw * ((s + 1) * (buScB p + 1)) * (p + 1) := by ring_nf
  have hA3 : WSw main (rlP 1) [iD, cvecVal u, WdL, KeysS, iS, iP]
      (fun B => B = [cvecVal u, iD, WdL, KeysS, iS, iP]) (6 * Krl * ((s + 1) * (buScB p + 1))) := by
    refine WSw.cost KL (WSw.ofPipe KL (Pipe.roll (main := main) (prog := rlP) (K := Krl) hrl
      (A := [iD, cvecVal u, WdL, KeysS, iS, iP]) (k := 1) (by simp))) ?_
    have hsz : Work.Fx.szl (([iD, cvecVal u, WdL, KeysS, iS, iP] : List Val).take (1 + 1)) ≤ 2 * ((s + 1) * (buScB p + 1)) := by
      rw [show ([iD, cvecVal u, WdL, KeysS, iS, iP] : List Val).take (1 + 1) = [iD, cvecVal u]
        from rfl, szl2]
      have h4 : vsz iD ≤ ((s + 1) * (buScB p + 1)) := by
        rw [show iD = Val.int ((2 : ℤ) ^ p) from rfl, Work.Fx.vsz_int]
        exact le_V_of_le_buScB hsu7
      omega
    calc Krl * (1 + 1) * (Work.Fx.szl
            (([iD, cvecVal u, WdL, KeysS, iS, iP] : List Val).take (1 + 1)) + 1)
        ≤ Krl * 2 * (2 * ((s + 1) * (buScB p + 1)) + 1) :=
          mul_le_mul_left'' (Nat.add_le_add_right hsz 1)
      _ ≤ 6 * Krl * ((s + 1) * (buScB p + 1)) := by
          have h6 : 2 * ((s + 1) * (buScB p + 1)) + 1 ≤ 3 * ((s + 1) * (buScB p + 1)) := by omega
          calc Krl * 2 * (2 * ((s + 1) * (buScB p + 1)) + 1) ≤ Krl * 2 * (3 * ((s + 1) * (buScB p + 1))) :=
                mul_le_mul_left'' h6
            _ = 6 * Krl * ((s + 1) * (buScB p + 1)) := by ring_nf
  have hA4 : WSw main (rlP 2) [cvecVal u, iD, WdL, KeysS, iS, iP]
      (fun B => B = [WdL, cvecVal u, iD, KeysS, iS, iP]) (12 * Krl * ((s + 1) * (buScB p + 1))) := by
    refine WSw.cost KL (WSw.ofPipe KL (Pipe.roll (main := main) (prog := rlP) (K := Krl) hrl
      (A := [cvecVal u, iD, WdL, KeysS, iS, iP]) (k := 2) (by simp))) ?_
    have hsz : Work.Fx.szl (([cvecVal u, iD, WdL, KeysS, iS, iP] : List Val).take (2 + 1)) ≤ 3 * ((s + 1) * (buScB p + 1)) := by
      rw [show ([cvecVal u, iD, WdL, KeysS, iS, iP] : List Val).take (2 + 1)
          = [cvecVal u, iD, WdL] from rfl, szl3]
      have h5 : vsz iD ≤ ((s + 1) * (buScB p + 1)) := by
        rw [show iD = Val.int ((2 : ℤ) ^ p) from rfl, Work.Fx.vsz_int]
        exact le_V_of_le_buScB hsu7
      have h6 : vsz WdL ≤ ((s + 1) * (buScB p + 1)) := hsu2
      omega
    calc Krl * (2 + 1) * (Work.Fx.szl
            (([cvecVal u, iD, WdL, KeysS, iS, iP] : List Val).take (2 + 1)) + 1)
        ≤ Krl * 3 * (3 * ((s + 1) * (buScB p + 1)) + 1) :=
          mul_le_mul_left'' (Nat.add_le_add_right hsz 1)
      _ ≤ 12 * Krl * ((s + 1) * (buScB p + 1)) := by
          have h6 : 3 * ((s + 1) * (buScB p + 1)) + 1 ≤ 4 * ((s + 1) * (buScB p + 1)) := by omega
          calc Krl * 3 * (3 * ((s + 1) * (buScB p + 1)) + 1) ≤ Krl * 3 * (4 * ((s + 1) * (buScB p + 1))) :=
                mul_le_mul_left'' h6
            _ = 12 * Krl * ((s + 1) * (buScB p + 1)) := by ring_nf
  have hG1 : WSw main (.seq (pkP 4) (.seq pwP (.seq (rlP 1) (rlP 2))))
      [cvecVal u, WdL, KeysS, iS, iP] (fun B => B = [WdL, cvecVal u, iD, KeysS, iS, iP])
      (buScQ S s p) := by
    refine WSw.cost KL (WSw.comp KL hA1 (fun Bv hBv => by
      rw [hBv]
      exact WSw.comp KL hA2 (fun Bv hBv => by
        rw [hBv]
        exact WSw.comp KL hA3 (fun Bv hBv => by rw [hBv]; exact hA4)))) ?_
    have h9 : 30 * Kpk + 2 * Kpw * (p + 1) + 18 * Krl ≤ 400 * S * (p + 1) := by
      have h1 : Kpk ≤ S * (p + 1) := le_trans hKpkS (nat_le_mul_succ S p)
      have h3 : Krl ≤ S * (p + 1) := le_trans hKrlS (nat_le_mul_succ S p)
      nlinarith [h1, hKpwS, h3]
    have heq : 30 * Kpk * ((s + 1) * (buScB p + 1))
          + (2 * Kpw * ((s + 1) * (buScB p + 1)) * (p + 1)
            + (6 * Krl * ((s + 1) * (buScB p + 1)) + 12 * Krl * ((s + 1) * (buScB p + 1))))
        = (30 * Kpk + 2 * Kpw * (p + 1) + 18 * Krl) * ((s + 1) * (buScB p + 1)) := by ring_nf
    rw [heq]
    calc (30 * Kpk + 2 * Kpw * (p + 1) + 18 * Krl) * ((s + 1) * (buScB p + 1))
        ≤ (400 * S * (p + 1)) * ((s + 1) * (buScB p + 1)) := mul_le_mul_right'' h9
      _ = 400 * S * (((s + 1) * (buScB p + 1)) * (p + 1)) := by ring_nf
  -- generic getD facts for the two zipped lists
  have hWdGet : ∀ i < s, WdList.getD i Val.nil = Val.int (buWd p α s t (i : ℤ)) := by
    intro i hi
    show (((List.ofFn (fun i : Fin s => buWd p α s t (i : ℤ))).map Val.int)).getD i Val.nil
      = Val.int (buWd p α s t (i : ℤ))
    rw [List.getD_eq_getElem _ _ (by simpa [List.length_map, List.length_ofFn] using hi),
      List.getElem_map, List.getElem_ofFn]
  have huGet : ∀ i < s, uList.getD i Val.nil = cfxVal (u.getD i (0, 0)) := by
    intro i hi
    have hiu : i < u.length := by omega
    show (u.map cfxVal).getD i Val.nil = cfxVal (u.getD i (0, 0))
    rw [List.getD_eq_getElem _ _ (by simpa using hiu), List.getElem_map,
      ← List.getD_eq_getElem u (0, 0) hiu]
  -- ================ stage B : the scaling zipWith ================
  have hB : Pipe main (zipC elP) [WdL, cvecVal u, iD, KeysS, iS, iP] [cvecVal d, iD, KeysS, iS, iP]
      (s * (cu + Kz * (buScB p + 1)) + Kz) := by
    have hlen : WdList.length = uList.length := by
      simp [WdList, uList, List.length_map, List.length_ofFn, hulen]
    have hper : ∀ x y, (fun x y => ∃ (i : ℕ) (a b : ℤ), i < s ∧
        x = Val.int (buWd p α s t (i : ℤ)) ∧ a.natAbs ≤ 2 ^ (p + 1) ∧ b.natAbs ≤ 2 ^ (p + 1) ∧
        y = Val.cons (Val.int a) (Val.int b)) x y →
        Pipe main elP (x :: y :: [iD, KeysS, iS, iP])
          (buScProd ((2 : ℤ) ^ p) x y :: [iD, KeysS, iS, iP]) cu := by
      intro x y hxy
      obtain ⟨i, a, b, hi, hx, ha, hb, hy⟩ := hxy
      subst hx
      subst hy
      refine Pipe.ofElemD (x := Val.int (buWd p α s t (i : ℤ)))
        (y := Val.cons (Val.int a) (Val.int b))
        (z := buScProd ((2 : ℤ) ^ p) (Val.int (buWd p α s t (i : ℤ)))
          (Val.cons (Val.int a) (Val.int b)))
        (D := iD) (T := [KeysS, iS, iP]) (fun T' => ?_)
      have h1 := hel main (buWd p α s t (i : ℤ)) a b ((2 : ℤ) ^ p) T' (by positivity)
      have hzeq : buScProd ((2 : ℤ) ^ p) (Val.int (buWd p α s t (i : ℤ)))
            (Val.cons (Val.int a) (Val.int b))
          = Val.cons (Val.int (Int.tdiv (buWd p α s t (i : ℤ) * a) ((2 : ℤ) ^ p)))
              (Val.int (Int.tdiv (buWd p α s t (i : ℤ) * b) ((2 : ℤ) ^ p))) :=
        buScProd_apply _ _ _ _
      refine buScWord_le KL (buScWord_post KL h1 ?_) ?_
      · intro vs out _ hout
        rw [hout, hzeq]
      · intro vs _
        have hbr := buScElemBracket p (buWd p α s t (i : ℤ)) a b (hwd (i : ℤ)) ha hb
        calc Kel * (isz (buWd p α s t (i : ℤ)) + isz a + isz b + isz ((2 : ℤ) ^ p) + 1) *
              (isz (buWd p α s t (i : ℤ)) + isz a + isz b + isz ((2 : ℤ) ^ p) + 1)
            = Kel * ((isz (buWd p α s t (i : ℤ)) + isz a + isz b + isz ((2 : ℤ) ^ p) + 1) *
              (isz (buWd p α s t (i : ℤ)) + isz a + isz b + isz ((2 : ℤ) ^ p) + 1)) := by ring_nf
          _ ≤ Kel * ((18 * (p + 1)) * (18 * (p + 1))) :=
              mul_le_mul_left'' (Nat.mul_le_mul hbr hbr)
          _ = cu := by simp only [cu]; ring_nf
    have hF : ∀ x y, (fun x y => ∃ (i : ℕ) (a b : ℤ), i < s ∧
        x = Val.int (buWd p α s t (i : ℤ)) ∧ a.natAbs ≤ 2 ^ (p + 1) ∧ b.natAbs ≤ 2 ^ (p + 1) ∧
        y = Val.cons (Val.int a) (Val.int b)) x y → vsz (buScProd ((2 : ℤ) ^ p) x y) ≤ buScB p := by
      intro x y hxy
      obtain ⟨i, a, b, hi, hx, ha, hb, hy⟩ := hxy
      subst hx
      subst hy
      exact vsz_buScProd_le (hwd (i : ℤ)) ha hb
    have hP : ∀ i < WdList.length, (fun x y => ∃ (i : ℕ) (a b : ℤ), i < s ∧
        x = Val.int (buWd p α s t (i : ℤ)) ∧ a.natAbs ≤ 2 ^ (p + 1) ∧ b.natAbs ≤ 2 ^ (p + 1) ∧
        y = Val.cons (Val.int a) (Val.int b)) (WdList.getD i Val.nil) (uList.getD i Val.nil) := by
      intro i hi
      have his : i < s := by simpa [WdList, List.length_map, List.length_ofFn] using hi
      have hiu : i < u.length := by omega
      have hzu : u.getD i (0, 0) ∈ u := by
        rw [List.getD_eq_getElem u (0, 0) hiu]
        exact List.getElem_mem hiu
      have hzc := buIn_coord (hV _ hzu)
      exact ⟨i, (u.getD i (0, 0)).1, (u.getD i (0, 0)).2, his, hWdGet i his, hzc.1, hzc.2,
        huGet i his⟩
    have hL : ∀ x ∈ WdList ++ uList, vsz x ≤ buScB p := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · have hx' : x ∈ (List.ofFn (fun i : Fin s => buWd p α s t (i : ℤ))).map Val.int := hx
        obtain ⟨k, hk, hkx⟩ := List.mem_map.mp hx'
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hk
        rw [← hkx, Work.Fx.vsz_int]
        exact hwdsz (j : ℤ)
      · have hx' : x ∈ u.map cfxVal := hx
        obtain ⟨z, hz, hzx⟩ := List.mem_map.mp hx'
        rw [← hzx]
        exact hcfxsz z (hV z hz)
    have hzip := Pipe.zipFun (comb := zipC) (Kz := Kz) hzipF KL
      (T := [iD, KeysS, iS, iP]) hper hF WdList uList hlen hP hL
    have hWd : ofList WdList = WdL := rfl
    have hUl : ofList uList = cvecVal u := rfl
    have hZipEq : List.zipWith (buScProd ((2 : ℤ) ^ p)) WdList uList = d.map cfxVal :=
      buScZipEq (buWd p α s t) p s u
    have hlen' : WdList.length = s := by simp [WdList, List.length_map, List.length_ofFn]
    rw [hWd, hUl, hZipEq, hlen'] at hzip
    exact hzip
  have hBw : Pipe main (zipC elP) [WdL, cvecVal u, iD, KeysS, iS, iP] [cvecVal d, iD, KeysS, iS, iP]
      (buScQ S s p) := by
    refine Pipe.le hB ?_
    show s * (cu + Kz * (buScB p + 1)) + Kz
      ≤ 400 * S * (((s + 1) * (buScB p + 1)) * (p + 1))
    refine buScQ_zip (S := S) (s := s) (p := p) (c := cu) (Kz := Kz) ?_ hKzS
    show 324 * Kel * (p + 1) * (p + 1) ≤ 324 * S * (p + 1) * (p + 1)
    exact mul_le_mul_right'' (mul_le_mul_right'' (mul_le_mul_left'' hKelS))
  -- ================ stage C : bring the key list on top ================
  have hC : WSw main (rlP 2) [cvecVal d, iD, KeysS, iS, iP]
      (fun B => B = [KeysS, cvecVal d, iD, iS, iP]) (12 * Krl * ((s + 1) * (buScB p + 1))) := by
    refine WSw.cost KL (WSw.ofPipe KL (Pipe.roll (main := main) (prog := rlP) (K := Krl) hrl
      (A := [cvecVal d, iD, KeysS, iS, iP]) (k := 2) (by simp))) ?_
    have hsz : Work.Fx.szl (([cvecVal d, iD, KeysS, iS, iP] : List Val).take (2 + 1)) ≤ 3 * ((s + 1) * (buScB p + 1)) := by
      rw [show ([cvecVal d, iD, KeysS, iS, iP] : List Val).take (2 + 1) = [cvecVal d, iD, KeysS]
        from rfl, szl3]
      have h5 : vsz iD ≤ ((s + 1) * (buScB p + 1)) := by
        rw [show iD = Val.int ((2 : ℤ) ^ p) from rfl, Work.Fx.vsz_int]
        exact le_V_of_le_buScB hsu7
      have h6 : vsz KeysS ≤ ((s + 1) * (buScB p + 1)) := hsu3
      omega
    calc Krl * (2 + 1) * (Work.Fx.szl
            (([cvecVal d, iD, KeysS, iS, iP] : List Val).take (2 + 1)) + 1)
        ≤ Krl * 3 * (3 * ((s + 1) * (buScB p + 1)) + 1) :=
          mul_le_mul_left'' (Nat.add_le_add_right hsz 1)
      _ ≤ 12 * Krl * ((s + 1) * (buScB p + 1)) := by
          have h6 : 3 * ((s + 1) * (buScB p + 1)) + 1 ≤ 4 * ((s + 1) * (buScB p + 1)) := by omega
          calc Krl * 3 * (3 * ((s + 1) * (buScB p + 1)) + 1) ≤ Krl * 3 * (4 * ((s + 1) * (buScB p + 1))) :=
                mul_le_mul_left'' h6
            _ = 12 * Krl * ((s + 1) * (buScB p + 1)) := by ring_nf
  -- ================ stage D : label the entries with their keys ================
  have hD : Pipe main (zipC cVP) [KeysS, cvecVal d, iD, iS, iP] [ofList recs, iD, iS, iP]
      (s * (Kv + Kz * (buScB p + 1)) + Kz) := by
    have hlen : (buScKeys s t).length = (d.map cfxVal).length := by
      simp [buScKeys, List.length_map, List.length_ofFn, hdlen]
    have hper : ∀ x y, (fun x y => ∃ (k : ℤ) (z : ℤ × ℤ), x = Val.int k ∧ k.natAbs ≤ 2 ^ p ∧
        y = cfxVal z ∧ buIn (2 ^ p) z) x y →
        Pipe main cVP (x :: y :: [iD, iS, iP]) (Val.cons x y :: [iD, iS, iP]) Kv := by
      intro x y hxy
      exact Pipe.consElem main (hcV main) x y [iD, iS, iP]
    have hF : ∀ x y, (fun x y => ∃ (k : ℤ) (z : ℤ × ℤ), x = Val.int k ∧ k.natAbs ≤ 2 ^ p ∧
        y = cfxVal z ∧ buIn (2 ^ p) z) x y → vsz (Val.cons x y) ≤ buScB p := by
      intro x y hxy
      obtain ⟨k, z, hx, hk, hy, hz⟩ := hxy
      subst hx
      subst hy
      rw [Work.Fx.vsz_cons, Work.Fx.vsz_int]
      have hk' : isz k ≤ p + 3 := by
        refine Work.Fx.isz_le_of_natAbs_lt ?_
        calc k.natAbs ≤ 2 ^ p := hk
          _ < 2 ^ (p + 1) := Nat.pow_lt_pow_succ (by norm_num)
      have hz' : vsz (cfxVal z) ≤ 2 * p + 7 := by
        obtain ⟨h1, h2⟩ := buIn_coord hz
        have e1 : isz z.1 ≤ p + 3 := by
          refine Work.Fx.isz_le_of_natAbs_lt ?_
          calc z.1.natAbs ≤ 2 ^ p := h1
            _ < 2 ^ (p + 1) := Nat.pow_lt_pow_succ (by norm_num)
        have e2 : isz z.2 ≤ p + 3 := by
          refine Work.Fx.isz_le_of_natAbs_lt ?_
          calc z.2.natAbs ≤ 2 ^ p := h2
            _ < 2 ^ (p + 1) := Nat.pow_lt_pow_succ (by norm_num)
        rw [Work.Fx.vsz_cfxVal]
        omega
      simp only [buScB] at *
      omega
    have hkeyGet : ∀ i < s, (buScKeys s t).getD i Val.nil = Val.int (((egKeyS s t i : ℕ) : ℤ)) := by
      intro i hi
      show (((List.ofFn (fun i : Fin s => ((egKeyS s t i : ℕ) : ℤ))).map Val.int)).getD i Val.nil
        = Val.int (((egKeyS s t i : ℕ) : ℤ))
      rw [List.getD_eq_getElem _ _ (by simpa [buScKeys, List.length_map, List.length_ofFn] using hi),
        List.getElem_map, List.getElem_ofFn]
    have hdGet : ∀ i < s, (d.map cfxVal).getD i Val.nil = cfxVal (d.getD i (0, 0)) := by
      intro i hi
      have hid : i < d.length := by omega
      show (d.map cfxVal).getD i Val.nil = cfxVal (d.getD i (0, 0))
      rw [List.getD_eq_getElem _ _ (by simpa using hid), List.getElem_map,
        ← List.getD_eq_getElem d (0, 0) hid]
    have hP : ∀ i < (buScKeys s t).length, (fun x y => ∃ (k : ℤ) (z : ℤ × ℤ), x = Val.int k ∧
        k.natAbs ≤ 2 ^ p ∧ y = cfxVal z ∧ buIn (2 ^ p) z)
        ((buScKeys s t).getD i Val.nil) ((d.map cfxVal).getD i Val.nil) := by
      intro i hi
      have his : i < s := by simpa [buScKeys, List.length_map, List.length_ofFn] using hi
      have hid : i < d.length := by omega
      refine ⟨(((egKeyS s t i : ℕ) : ℤ)), d.getD i (0, 0), hkeyGet i his, ?_, hdGet i his, ?_⟩
      · rw [Int.natAbs_natCast]
        exact le_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by omega)) hVs)
      · refine hVd _ ?_
        rw [List.getD_eq_getElem d (0, 0) hid]
        exact List.getElem_mem hid
    have hL : ∀ x ∈ buScKeys s t ++ d.map cfxVal, vsz x ≤ buScB p := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨k, hk, hkx⟩ := List.mem_map.mp hx
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hk
        rw [← hkx, Work.Fx.vsz_int]
        exact hkeysz j
      · obtain ⟨z, hz, hzx⟩ := List.mem_map.mp hx
        rw [← hzx]
        exact hcfxszp z (hVd z hz)
    have hzip := Pipe.zipFun (comb := zipC) (Kz := Kz) hzipF KL (T := [iD, iS, iP])
      (P := fun x y => ∃ (k : ℤ) (z : ℤ × ℤ), x = Val.int k ∧ k.natAbs ≤ 2 ^ p ∧
        y = cfxVal z ∧ buIn (2 ^ p) z)
      (F := Val.cons) (c := Kv) (L := buScB p)
      hper hF (buScKeys s t) (d.map cfxVal) hlen hP hL
    have hKs : ofList (buScKeys s t) = KeysS := by
      rw [show KeysS = buKeysS s t from rfl, buKeysS_eq]
    have hUl : ofList (d.map cfxVal) = cvecVal d := rfl
    have hRecs : ofList (List.zipWith Val.cons (buScKeys s t) (d.map cfxVal)) = ofList recs := by
      rw [show recs = buScRecs s t d from rfl, show buScRecs s t d
        = List.zipWith Val.cons (buScKeys s t) (d.map cfxVal) from rfl]
    have hlen' : (buScKeys s t).length = s := buScKeys_length s t
    rw [hKs, hUl, hRecs, hlen'] at hzip
    exact hzip
  have hDw : Pipe main (zipC cVP) [KeysS, cvecVal d, iD, iS, iP] [ofList recs, iD, iS, iP]
      (buScQ S s p) := by
    refine Pipe.le hD ?_
    show s * (Kv + Kz * (buScB p + 1)) + Kz
      ≤ 400 * S * (((s + 1) * (buScB p + 1)) * (p + 1))
    refine buScQ_zip (S := S) (s := s) (p := p) (c := Kv) (Kz := Kz) ?_ hKzS
    have h1 : Kv ≤ S := hKvS
    have h2 : S ≤ 324 * S * (p + 1) * (p + 1) := by
      calc S = S * 1 := (Nat.mul_one S).symm
        _ ≤ S * ((p + 1) * (p + 1)) := mul_le_mul_left'' (one_le_sq p)
        _ = 1 * (S * ((p + 1) * (p + 1))) := by ring
        _ ≤ 324 * (S * ((p + 1) * (p + 1))) := mul_le_mul_right'' (by norm_num : 1 ≤ 324)
        _ = 324 * S * (p + 1) * (p + 1) := by ring_nf
    exact le_trans h1 h2
  -- ================ stage E : sort by key ================
  have hE : WSw main srtP [ofList recs, iD, iS, iP]
      (fun Bv => ∃ (ys : List Val), ys.Perm recs ∧ ys.Pairwise (fun a b => pairKey a < pairKey b) ∧
        Bv = ofList ys :: [iD, iS, iP]) (buScQ S s p) := by
    refine WSw.cost KL (WSw.sortOf KL main hsrt recs ?hshape ?hnd [iD, iS, iP]) ?_
    · intro x hx
      have hx' : x ∈ buScRecs s t d := by rwa [show recs = buScRecs s t d from rfl] at hx
      obtain ⟨k, v, hv⟩ := (buScKeysFacts s t hs hcop d).2.2 x hx'
      exact ⟨k, v, hv⟩
    · rw [show recs = buScRecs s t d from rfl, (buScRecsFacts s t d hdlen).2.2.1]
      exact (buScKeysFacts s t hs hcop d).1
    · have h2 : (recs.length).size ≤ p := by
        rw [hrecslen]
        exact Nat.size_le.mpr (lt_trans hst htp)
      calc Ksrt * (vsz (ofList recs) + 1) * (recs.length.size + 1)
          ≤ Ksrt * (((s + 1) * (buScB p + 1)) + 1) * (p + 1) :=
            Nat.mul_le_mul (mul_le_mul_left'' (Nat.add_le_add_right hsu5 1))
              (Nat.add_le_add_right h2 1)
        _ ≤ Ksrt * (2 * ((s + 1) * (buScB p + 1))) * (p + 1) :=
            mul_le_mul_right'' (mul_le_mul_left'' (by omega))
        _ = 2 * Ksrt * ((s + 1) * (buScB p + 1)) * (p + 1) := by ring_nf
        _ ≤ buScQ S s p := by
            show 2 * Ksrt * ((s + 1) * (buScB p + 1)) * (p + 1) ≤ 400 * S * (((s + 1) * (buScB p + 1)) * (p + 1))
            exact mul_le_buScQ (S := S) (s := s) (p := p) (c := 2) (K := Ksrt) (by omega)
  -- ================ the tail : roll, drop, take, strip, drop ================
  have hPost : ∀ ys : List Val, ys.Perm recs → ys.Pairwise (fun a b => pairKey a < pairKey b) →
      WSw main (.seq (rlP 1) (.seq drP (.seq (rlP 1) (.seq tkP (.seq (combML stP)
        (.seq (rlP 1) drP))))))
        [ofList ys, iD, iS, iP] (fun Bv => Bv = [ofList ((ys.take s).map buScStrip)])
        (7 * buScQ S s p) := by
    intro ys hperm hsort
    have hylen : ys.length = s := by rw [List.Perm.length_eq hperm, hrecslen]
    obtain ⟨-, -, -, -, -, hsu6', -, -, -, hsu10', hsu11', -⟩ :=
      buScSizes p α s t hs hst hcop htp hwd u hulen hV d hdlen hVd ys hperm
    have hiDsz : vsz iD ≤ ((s + 1) * (buScB p + 1)) := by
      rw [show iD = Val.int ((2 : ℤ) ^ p) from rfl, Work.Fx.vsz_int]
      exact le_V_of_le_buScB hsu7
    have hiPsz : vsz iP ≤ ((s + 1) * (buScB p + 1)) := by
      rw [show iP = Val.int (p : ℤ) from rfl, Work.Fx.vsz_int]
      exact le_V_of_le_buScB hsu9
    have hWpos : 1 ≤ ((s + 1) * (buScB p + 1)) * (p + 1) := Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
    have houtsz : vsz (ofList ((ys.take s).map buScStrip)) ≤ ((s + 1) * (buScB p + 1)) := by
      have h := Work.Resample.vsz_ofList_le (l := (ys.take s).map buScStrip) (B := buScB p)
        (fun x hx => by
          obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hx
          rw [← hyx]
          exact hsu11' y hy)
      have hlen : ((ys.take s).map buScStrip).length = s := by
        rw [List.length_map, List.length_take, hylen, min_self]
      rwa [hlen] at h
    have hF : WSw main (rlP 1) [ofList ys, iD, iS, iP] (fun B => B = [iD, ofList ys, iS, iP])
        (buScQ S s p) := by
      refine WSw.cost KL (WSw.ofPipe KL (Pipe.roll (main := main) (prog := rlP) (K := Krl) hrl
        (A := [ofList ys, iD, iS, iP]) (k := 1) (by simp))) ?_
      have hsz : Work.Fx.szl (([ofList ys, iD, iS, iP] : List Val).take (1 + 1)) ≤ 2 * ((s + 1) * (buScB p + 1)) := by
        rw [show ([ofList ys, iD, iS, iP] : List Val).take (1 + 1) = [ofList ys, iD] from rfl, szl2]
        omega
      calc Krl * (1 + 1) * (Work.Fx.szl (([ofList ys, iD, iS, iP] : List Val).take (1 + 1)) + 1)
          ≤ Krl * 2 * (2 * ((s + 1) * (buScB p + 1)) + 1) :=
            mul_le_mul_left'' (Nat.add_le_add_right hsz 1)
        _ ≤ 6 * Krl * ((s + 1) * (buScB p + 1)) := by
            have h6 : 2 * ((s + 1) * (buScB p + 1)) + 1 ≤ 3 * ((s + 1) * (buScB p + 1)) := by omega
            calc Krl * 2 * (2 * ((s + 1) * (buScB p + 1)) + 1) ≤ Krl * 2 * (3 * ((s + 1) * (buScB p + 1))) :=
                  mul_le_mul_left'' h6
              _ = 6 * Krl * ((s + 1) * (buScB p + 1)) := by ring_nf
        _ ≤ buScQ S s p := by
            show 6 * Krl * ((s + 1) * (buScB p + 1)) ≤ 400 * S * (((s + 1) * (buScB p + 1)) * (p + 1))
            exact mul_le_buScQ' (S := S) (s := s) (p := p) (c := 6) (K := Krl) (by omega)
    have hG : WSw main drP [iD, ofList ys, iS, iP] (fun B => B = [ofList ys, iS, iP])
        (buScQ S s p) := by
      refine WSw.cost KL (WSw.ofPipe KL (Pipe.appendTail [ofList ys, iS, iP]
        (Pipe.drop (main := main) (prog := drP) (K := Kdr) hdr iD))) ?_
      calc Kdr * (vsz iD + 1) ≤ Kdr * (((s + 1) * (buScB p + 1)) + 1) := mul_le_mul_left'' (Nat.add_le_add_right hiDsz 1)
        _ ≤ 2 * Kdr * ((s + 1) * (buScB p + 1)) := by
            have h6 : ((s + 1) * (buScB p + 1)) + 1 ≤ 2 * ((s + 1) * (buScB p + 1)) := by omega
            calc Kdr * (((s + 1) * (buScB p + 1)) + 1) ≤ Kdr * (2 * ((s + 1) * (buScB p + 1))) := mul_le_mul_left'' h6
              _ = 2 * Kdr * ((s + 1) * (buScB p + 1)) := by ring_nf
        _ ≤ buScQ S s p := by
            show 2 * Kdr * ((s + 1) * (buScB p + 1)) ≤ 400 * S * (((s + 1) * (buScB p + 1)) * (p + 1))
            exact mul_le_buScQ' (S := S) (s := s) (p := p) (c := 2) (K := Kdr) (by omega)
    have hH : WSw main (rlP 1) [ofList ys, iS, iP] (fun B => B = [iS, ofList ys, iP])
        (buScQ S s p) := by
      refine WSw.cost KL (WSw.ofPipe KL (Pipe.roll (main := main) (prog := rlP) (K := Krl) hrl
        (A := [ofList ys, iS, iP]) (k := 1) (by simp))) ?_
      have hsz : Work.Fx.szl (([ofList ys, iS, iP] : List Val).take (1 + 1)) ≤ 2 * ((s + 1) * (buScB p + 1)) := by
        rw [show ([ofList ys, iS, iP] : List Val).take (1 + 1) = [ofList ys, iS] from rfl, szl2]
        have hisz : vsz iS ≤ ((s + 1) * (buScB p + 1)) := by
          rw [show iS = Val.int (s : ℤ) from rfl, Work.Fx.vsz_int]
          exact le_V_of_le_buScB hsu8
        omega
      calc Krl * (1 + 1) * (Work.Fx.szl (([ofList ys, iS, iP] : List Val).take (1 + 1)) + 1)
          ≤ Krl * 2 * (2 * ((s + 1) * (buScB p + 1)) + 1) :=
            mul_le_mul_left'' (Nat.add_le_add_right hsz 1)
        _ ≤ 6 * Krl * ((s + 1) * (buScB p + 1)) := by
            have h6 : 2 * ((s + 1) * (buScB p + 1)) + 1 ≤ 3 * ((s + 1) * (buScB p + 1)) := by omega
            calc Krl * 2 * (2 * ((s + 1) * (buScB p + 1)) + 1) ≤ Krl * 2 * (3 * ((s + 1) * (buScB p + 1))) :=
                  mul_le_mul_left'' h6
              _ = 6 * Krl * ((s + 1) * (buScB p + 1)) := by ring_nf
        _ ≤ buScQ S s p := by
            show 6 * Krl * ((s + 1) * (buScB p + 1)) ≤ 400 * S * (((s + 1) * (buScB p + 1)) * (p + 1))
            exact mul_le_buScQ' (S := S) (s := s) (p := p) (c := 6) (K := Krl) (by omega)
    have hI : WSw main tkP [iS, ofList ys, iP] (fun B => B = [ofList (ys.take s), iP])
        (buScQ S s p) := by
      refine WSw.cost KL (WSw.ofPipe KL (Pipe.appendTail [iP]
        (Pipe.takeOf (main := main) (prog := tkP) (K := Ktk) htk (k := s) (xs := ys)))) ?_
      calc Ktk * (vsz (ofList ys) + isz ((s : ℤ)) + 1)
          ≤ Ktk * (((s + 1) * (buScB p + 1)) + ((s + 1) * (buScB p + 1)) + 1) := by
            refine mul_le_mul_left'' ?_
            have : isz ((s : ℤ)) ≤ ((s + 1) * (buScB p + 1)) := le_V_of_le_buScB hsu8
            omega
        _ ≤ 3 * Ktk * ((s + 1) * (buScB p + 1)) := by
            have h6 : 2 * ((s + 1) * (buScB p + 1)) + 1 ≤ 3 * ((s + 1) * (buScB p + 1)) := by omega
            calc Ktk * (((s + 1) * (buScB p + 1)) + ((s + 1) * (buScB p + 1)) + 1) = Ktk * (2 * ((s + 1) * (buScB p + 1)) + 1) := by ring_nf
              _ ≤ Ktk * (3 * ((s + 1) * (buScB p + 1))) := mul_le_mul_left'' h6
              _ = 3 * Ktk * ((s + 1) * (buScB p + 1)) := by ring_nf
        _ ≤ buScQ S s p := by
            show 3 * Ktk * ((s + 1) * (buScB p + 1)) ≤ 400 * S * (((s + 1) * (buScB p + 1)) * (p + 1))
            exact mul_le_buScQ' (S := S) (s := s) (p := p) (c := 3) (K := Ktk) (by omega)
    have hJ : WSw main (combML stP) [ofList (ys.take s), iP]
        (fun B => B = [ofList ((ys.take s).map buScStrip), iP]) (buScQ S s p) := by
      have hstP : ∀ x ∈ ys.take s, Pipe main stP [x] [buScStrip x] (Kst * buScB p) := by
        intro x hx
        have hxrec : x ∈ recs := (hperm.mem_iff).mp (List.mem_of_mem_take hx)
        have hxshape : ∃ (k : ℤ) (z : ℤ × ℤ), x = Val.cons (Val.int k) (cfxVal z) := by
          obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hxrec
          refine ⟨(((egKeyS s t i : ℕ) : ℤ)), d.getD i (0, 0), ?_⟩
          have h1 : recs.getD i Val.nil = Val.cons (Val.int (((egKeyS s t i : ℕ) : ℤ)))
              (cfxVal (d.getD i (0, 0))) :=
            (buScRecsFacts s t d hdlen).2.1 i (by rwa [hrecslen] at hi)
          rw [← hix, ← List.getD_eq_getElem recs Val.nil hi, h1]
        obtain ⟨k, z, rfl⟩ := hxshape
        have hxsz : vsz (Val.cons (Val.int k) (cfxVal z)) ≤ buScB p := hsu10' _ hxrec
        have hc : Kst * (isz k + isz z.1 + isz z.2 + 2) ≤ Kst * buScB p := by
          refine mul_le_mul_left'' ?_
          rw [Work.Fx.vsz_cons, Work.Fx.vsz_cfxVal, Work.Fx.vsz_int] at hxsz
          omega
        have hW : ∀ T' : List Val, WordR main stP (fun vs => vs = Val.cons (Val.int k)
              (cfxVal z) :: T') (fun _ out => out = buScStrip (Val.cons (Val.int k) (cfxVal z)) :: T')
            (fun _ => Kst * buScB p) := by
          intro T'
          have h1 := hstW main k z.1 z.2 T'
          refine buScWord_le KL (buScWord_post KL h1 ?_) ?_
          · intro vs out _ hout
            rw [hout]
            rfl
          · intro vs _
            exact hc
        exact Pipe.ofUn hW
      have hx2 : ∀ x ∈ ys.take s, vsz x ≤ buScB p := fun x hx =>
        hsu10' x ((hperm.mem_iff).mp (List.mem_of_mem_take hx))
      have hML2 := Pipe.mapListFun (comb := combML) (Kml := Kml) hML (main := main) (q := stP)
        (rest := [iP]) (xs := ys.take s) (F := buScStrip) (c := Kst * buScB p) (L := buScB p)
        hstP hx2 hsu11'
      refine WSw.cost KL (WSw.ofPipe KL hML2) ?_
      have hlen : (ys.take s).length = s := by rw [List.length_take, hylen, min_self]
      rw [hlen]
      exact buScQ_mapList (S := S) (s := s) (p := p) (K1 := Kst) (K2 := Kml) hKstS hKmlS
    have hK : WSw main (rlP 1) [ofList ((ys.take s).map buScStrip), iP]
        (fun B => B = [iP, ofList ((ys.take s).map buScStrip)]) (buScQ S s p) := by
      refine WSw.cost KL (WSw.ofPipe KL (Pipe.roll (main := main) (prog := rlP) (K := Krl) hrl
        (A := [ofList ((ys.take s).map buScStrip), iP]) (k := 1) (by simp))) ?_
      have hsz : Work.Fx.szl (([ofList ((ys.take s).map buScStrip), iP] : List Val).take (1 + 1))
          ≤ 2 * ((s + 1) * (buScB p + 1)) := by
        rw [show ([ofList ((ys.take s).map buScStrip), iP] : List Val).take (1 + 1)
          = [ofList ((ys.take s).map buScStrip), iP] from rfl, szl2]
        omega
      calc Krl * (1 + 1) * (Work.Fx.szl
              (([ofList ((ys.take s).map buScStrip), iP] : List Val).take (1 + 1)) + 1)
          ≤ Krl * 2 * (2 * ((s + 1) * (buScB p + 1)) + 1) :=
            mul_le_mul_left'' (Nat.add_le_add_right hsz 1)
        _ ≤ 6 * Krl * ((s + 1) * (buScB p + 1)) := by
            have h6 : 2 * ((s + 1) * (buScB p + 1)) + 1 ≤ 3 * ((s + 1) * (buScB p + 1)) := by omega
            calc Krl * 2 * (2 * ((s + 1) * (buScB p + 1)) + 1) ≤ Krl * 2 * (3 * ((s + 1) * (buScB p + 1))) :=
                  mul_le_mul_left'' h6
              _ = 6 * Krl * ((s + 1) * (buScB p + 1)) := by ring_nf
        _ ≤ buScQ S s p := by
            show 6 * Krl * ((s + 1) * (buScB p + 1)) ≤ 400 * S * (((s + 1) * (buScB p + 1)) * (p + 1))
            exact mul_le_buScQ' (S := S) (s := s) (p := p) (c := 6) (K := Krl) (by omega)
    have hL : WSw main drP [iP, ofList ((ys.take s).map buScStrip)]
        (fun B => B = [ofList ((ys.take s).map buScStrip)]) (buScQ S s p) := by
      refine WSw.cost KL (WSw.ofPipe KL (Pipe.appendTail [ofList ((ys.take s).map buScStrip)]
        (Pipe.drop (main := main) (prog := drP) (K := Kdr) hdr iP))) ?_
      calc Kdr * (vsz iP + 1) ≤ Kdr * (((s + 1) * (buScB p + 1)) + 1) := mul_le_mul_left'' (Nat.add_le_add_right hiPsz 1)
        _ ≤ 2 * Kdr * ((s + 1) * (buScB p + 1)) := by
            have h6 : ((s + 1) * (buScB p + 1)) + 1 ≤ 2 * ((s + 1) * (buScB p + 1)) := by omega
            calc Kdr * (((s + 1) * (buScB p + 1)) + 1) ≤ Kdr * (2 * ((s + 1) * (buScB p + 1))) := mul_le_mul_left'' h6
              _ = 2 * Kdr * ((s + 1) * (buScB p + 1)) := by ring_nf
        _ ≤ buScQ S s p := by
            show 2 * Kdr * ((s + 1) * (buScB p + 1)) ≤ 400 * S * (((s + 1) * (buScB p + 1)) * (p + 1))
            exact mul_le_buScQ' (S := S) (s := s) (p := p) (c := 2) (K := Kdr) (by omega)
    refine WSw.cost KL (WSw.comp KL hF (fun B hB => by
      rw [hB]
      exact WSw.comp KL hG (fun B hB => by
        rw [hB]
        exact WSw.comp KL hH (fun B hB => by
          rw [hB]
          exact WSw.comp KL hI (fun B hB => by
            rw [hB]
            exact WSw.comp KL hJ (fun B hB => by
              rw [hB]
              exact WSw.comp KL hK (fun B hB => by rw [hB]; exact hL))))))) ?_
    have he : buScQ S s p + (buScQ S s p + (buScQ S s p + (buScQ S s p + (buScQ S s p
      + (buScQ S s p + buScQ S s p))))) = 7 * buScQ S s p := by ring_nf
    rw [he]
  -- ================ assembly ================
  have hSortTail : ∀ B5 : List Val,
      (fun Bv => ∃ (ys : List Val), ys.Perm recs ∧ ys.Pairwise (fun a b => pairKey a < pairKey b) ∧
        Bv = ofList ys :: [iD, iS, iP]) B5 →
      WSw main (.seq (rlP 1) (.seq drP (.seq (rlP 1) (.seq tkP (.seq (combML stP)
        (.seq (rlP 1) drP)))))) B5
        (fun Bv => ∃ (ys : List Val), ys.Perm recs ∧ ys.Pairwise (fun a b => pairKey a < pairKey b) ∧
          Bv = [ofList ((ys.take s).map buScStrip)]) (7 * buScQ S s p) := by
    intro B5 hB5
    obtain ⟨ys, hperm, hsort, rfl⟩ := hB5
    exact WSw.mono KL (hPost ys hperm hsort) (fun Bv hBv => ⟨ys, hperm, hsort, hBv⟩)
  have hTail : WSw main (.seq srtP (.seq (rlP 1) (.seq drP (.seq (rlP 1) (.seq tkP
      (.seq (combML stP) (.seq (rlP 1) drP)))))))
      [ofList recs, iD, iS, iP]
      (fun Bv => ∃ (ys : List Val), ys.Perm recs ∧ ys.Pairwise (fun a b => pairKey a < pairKey b) ∧
        Bv = [ofList ((ys.take s).map buScStrip)]) (8 * buScQ S s p) := by
    refine WSw.cost KL (WSw.comp KL hE hSortTail) ?_
    have he : buScQ S s p + 7 * buScQ S s p = 8 * buScQ S s p := by ring_nf
    rw [he]
  have hCw : WSw main (rlP 2) [cvecVal d, iD, KeysS, iS, iP]
      (fun B => B = [KeysS, cvecVal d, iD, iS, iP]) (buScQ S s p) := by
    refine WSw.cost KL hC ?_
    show 12 * Krl * ((s + 1) * (buScB p + 1))
      ≤ 400 * S * (((s + 1) * (buScB p + 1)) * (p + 1))
    exact mul_le_buScQ' (S := S) (s := s) (p := p) (c := 12) (K := Krl) (by omega)
  have hL1 : WSw main (.seq (zipC cVP) (.seq srtP (.seq (rlP 1) (.seq drP (.seq (rlP 1) (.seq tkP (.seq (combML stP) (.seq (rlP 1) drP))))))))
      [KeysS, cvecVal d, iD, iS, iP] (fun Bv => ∃ (ys : List Val), ys.Perm recs ∧ ys.Pairwise (fun a b => pairKey a < pairKey b) ∧
        Bv = [ofList ((ys.take s).map buScStrip)])
      (buScQ S s p + 8 * buScQ S s p) := by
    refine WSw.comp KL (WSw.ofPipe KL hDw) (fun B4 hB4 => ?_)
    rw [hB4]
    exact hTail
  have hL2 : WSw main (.seq (rlP 2) (.seq (zipC cVP) (.seq srtP (.seq (rlP 1) (.seq drP (.seq (rlP 1) (.seq tkP (.seq (combML stP) (.seq (rlP 1) drP)))))))))
      [cvecVal d, iD, KeysS, iS, iP] (fun Bv => ∃ (ys : List Val), ys.Perm recs ∧ ys.Pairwise (fun a b => pairKey a < pairKey b) ∧
        Bv = [ofList ((ys.take s).map buScStrip)])
      (buScQ S s p + (buScQ S s p + 8 * buScQ S s p)) := by
    refine WSw.comp KL hCw (fun B3 hB3 => ?_)
    rw [hB3]
    exact hL1
  have hL3 : WSw main (.seq (zipC elP) (.seq (rlP 2) (.seq (zipC cVP) (.seq srtP (.seq (rlP 1) (.seq drP (.seq (rlP 1) (.seq tkP (.seq (combML stP) (.seq (rlP 1) drP))))))))))
      [WdL, cvecVal u, iD, KeysS, iS, iP] (fun Bv => ∃ (ys : List Val), ys.Perm recs ∧ ys.Pairwise (fun a b => pairKey a < pairKey b) ∧
        Bv = [ofList ((ys.take s).map buScStrip)])
      (buScQ S s p + (buScQ S s p + (buScQ S s p + 8 * buScQ S s p))) := by
    refine WSw.comp KL (WSw.ofPipe KL hBw) (fun B2 hB2 => ?_)
    rw [hB2]
    exact hL2
  have hL4 : WSw main (.seq (.seq (pkP 4) (.seq pwP (.seq (rlP 1) (rlP 2))))
      (.seq (zipC elP) (.seq (rlP 2) (.seq (zipC cVP) (.seq srtP (.seq (rlP 1) (.seq drP (.seq (rlP 1) (.seq tkP (.seq (combML stP) (.seq (rlP 1) drP)))))))))))
      [cvecVal u, WdL, KeysS, iS, iP] (fun Bv => ∃ (ys : List Val), ys.Perm recs ∧ ys.Pairwise (fun a b => pairKey a < pairKey b) ∧
        Bv = [ofList ((ys.take s).map buScStrip)])
      (buScQ S s p + (buScQ S s p + (buScQ S s p + (buScQ S s p + 8 * buScQ S s p)))) := by
    refine WSw.comp KL hG1 (fun B1 hB1 => ?_)
    rw [hB1]
    exact hL3
  have hChain : WSw main (.seq (.seq (pkP 4) (.seq pwP (.seq (rlP 1) (rlP 2))))
      (.seq (zipC elP) (.seq (rlP 2) (.seq (zipC cVP) (.seq srtP (.seq (rlP 1) (.seq drP (.seq (rlP 1) (.seq tkP (.seq (combML stP) (.seq (rlP 1) drP)))))))))))
      [cvecVal u, WdL, KeysS, iS, iP] (fun Bv => ∃ (ys : List Val), ys.Perm recs ∧ ys.Pairwise (fun a b => pairKey a < pairKey b) ∧
        Bv = [ofList ((ys.take s).map buScStrip)])
      (12 * buScQ S s p) := by
    refine WSw.cost KL hL4 ?_
    have he : buScQ S s p + (buScQ S s p + (buScQ S s p + (buScQ S s p + 8 * buScQ S s p)))
        = 12 * buScQ S s p := by ring_nf
    rw [he]
  obtain ⟨out, s', n, ⟨Bv, ⟨ys, hperm, hsort, hBv⟩, hout⟩, hev, hn, hstk, hoth⟩ :=
    hChain rest (cvecVal u :: WdL :: KeysS :: iS :: iP :: rest) rfl s0 R hR
  have hylen : ys.length = s := by rw [List.Perm.length_eq hperm, hrecslen]
  have hget := buScSorted s t hs hst hcop d hdlen ys hperm hsort
  have houtmap := buScOut s t hs hst hcop d hdlen ys hylen hget
  refine ⟨out, s', n, ?_, hev, ?_, ?_, hoth⟩
  · refine ⟨u, rest, buPermL s t (by omega) hcop.symm d, rfl, ?_, rfl, List.length_ofFn, ?_⟩
    · rw [hout, hBv, houtmap]
      rfl
    · exact (buScInV p s t hs hcop (buWd p α s t) u d hulen hwd hV hdlen hVd).2
  · refine le_trans hn ?_
    have h1 := buScArith.1 (X := buScQ S s p) le_rfl
    have h2 := buScArith.2 (S := S) (s := s) (p := p) hS1
    have h5 : 12 * buScQ S s p ≤ 12 * (2 ^ 20 * S * (s + 1) * (p + 1) * (p + 1)) :=
      Nat.mul_le_mul_left 12 h1
    have h6 : 12 * (2 ^ 20 * S * (s + 1) * (p + 1) * (p + 1))
        ≤ 14 * (2 ^ 20 * S * (s + 1) * (p + 1) * (p + 1)) :=
      mul_le_mul_right'' (by norm_num)
    exact le_trans h5 (le_trans h6 (le_trans h2 (Nat.le_add_right _ _)))
  · exact hstk




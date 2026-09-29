import Mathlib
import Submission.Work.Transform.conjKit
import Submission.Work.Transform.phiAux
import Submission.Work.ConvR.extractScaleVec

/-!
# The row- and vector-conjugation words

Assembly of `Work.Transform.conjVecWord`: conjugating a whole vector of fixed-point complex
coefficients (negating every imaginary part) in time `O(n p²)`.

Two layers, mirroring `Work.ConvR.scaleRowWord`:

* `conjRowWord_of` (from the per-coefficient word `Work.Transform.conjElemWord`, whose statement is
  the `Prop` `Work.Transform.ConjElemSpec`) runs the `KernelLib.mapList` loop with the
  per-coefficient conjugating word on the list `u.map cfxVal` that encodes `cvecVal u`, and reads
  the result back with `Work.ConvR.exists_map_cfxVal_of_forall₂`;
* `conjVecWord_of` prepends a single `KernelLib.roll 1`, which moves the parameter `int p` from
  above the vector to below it: `int p :: cvecVal a :: R ↦ cvecVal (a.map conjPair) :: int p :: R`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Transform

open HvdH

local infixr:68 " ;;; " => HvdH.Cmd.seq

/-! ## `WordR` plumbing -/

/-- The consequence (monotonicity) rule for `WordR`. -/
theorem conjConseq {main p : Cmd} {P P' : List Val → Prop} {Q Q' : List Val → List Val → Prop}
    {C C' : List Val → ℕ} (h : WordR main p P Q C) (hP : ∀ vs, P' vs → P vs)
    (hQ : ∀ vs out, P' vs → Q vs out → Q' vs out) (hC : ∀ vs, P' vs → C vs ≤ C' vs) :
    WordR main p P' Q' C' := by
  intro vs hP' s R hR
  obtain ⟨out, s', n, hQh, he, hn, hstk, hoth⟩ := h vs (hP vs hP') s R hR
  exact ⟨out, s', n, hQ vs out hP' hQh, he, le_trans hn (hC vs hP'), hstk, hoth⟩

/-- Sequential composition of two constant-cost `WordR`s whose intermediate value stack is fixed. -/
theorem conjSeqFix {main p q : Cmd} {A B : List Val} {Q : List Val → Prop} {c1 c2 : ℕ}
    (h1 : WordR main p (fun vs => vs = A) (fun _ out => out = B) (fun _ => c1))
    (h2 : WordR main q (fun vs => vs = B) (fun _ out => Q out) (fun _ => c2)) :
    WordR main (.seq p q) (fun vs => vs = A) (fun _ out => Q out) (fun _ => c1 + c2) := by
  intro vs hvs s T hT
  rw [hvs] at hT
  obtain ⟨mid, s₂, n₁, hQ, he₁, hn₁, hstk₁, hoth₁⟩ := h1 A rfl s T hT
  rw [hQ] at hstk₁
  obtain ⟨out, s₃, n₂, hQ', he₂, hn₂, hstk₂, hoth₂⟩ := h2 B rfl s₂ T hstk₁
  exact ⟨out, s₃, n₁ + n₂, hQ', Eval.seq he₁ he₂, Nat.add_le_add hn₁ hn₂, hstk₂,
    fun k hk => by rw [hoth₂ k hk, hoth₁ k hk]⟩

/-- Two lists of equal length whose `getD`s (with a common default) agree are equal. -/
theorem eq_of_getD_eq' {α : Type} [Inhabited α] {l l' : List α} (d : α)
    (hlen : l.length = l'.length) (h : ∀ i < l.length, l.getD i d = l'.getD i d) : l = l' := by
  apply List.ext_getElem hlen
  intro n h1 h2
  rw [← List.getD_eq_getElem (l := l) (d := d) h1,
    ← List.getD_eq_getElem (l := l') (d := d) h2]
  exact h n h1

/-! ## The row-conjugation word -/

/-- Conjugate a whole disc vector: `cvecVal u :: int p :: rest ↦ cvecVal (u.map conjPair) :: int p :: rest`,
in cost `K (r+1)(p+1)² + K`, given the per-coefficient word `ConjElemSpec`. -/
theorem conjRowWord_of (hKer : HvdH.KernelLib) (hElem : ConjElemSpec) :
    ∃ (prog : HvdH.Cmd) (K : ℕ),
      ∀ (main : HvdH.Cmd) (p r : ℕ) (u : List (ℤ × ℤ)) (rest : List HvdH.Val),
        HvdH.InDiscVec p r u →
        HvdH.WordR main prog
          (fun vs => vs = HvdH.cvecVal u :: HvdH.Val.int (p : ℤ) :: rest)
          (fun _ out => out = HvdH.cvecVal (u.map conjPair) :: HvdH.Val.int (p : ℤ) :: rest)
          (fun _ => K * (r + 1) * (p + 1) ^ 2 + K) := by
  obtain ⟨celP, Kc, hcel⟩ := hElem
  obtain ⟨mapP, Km, hmap⟩ := hKer.mapList
  refine ⟨mapP celP, Kc + 10 * Km, ?_⟩
  intro main p r u rest hu
  have hlen : (u.map HvdH.cfxVal).length = r := by rw [List.length_map, hu.1]
  -- every element of the encoded row is a disc coefficient of encoding size `≤ 2p + 8`
  have hxs : ∀ x ∈ u.map HvdH.cfxVal,
      (∃ z : ℤ × ℤ, x = HvdH.cfxVal z ∧ HvdH.inDisc p z) ∧ HvdH.vsz x ≤ 2 * p + 8 := by
    intro x hx
    obtain ⟨z, hzx, rfl⟩ := List.mem_map.mp hx
    exact ⟨⟨z, rfl, hu.2 z hzx⟩, vsz_cfxVal_le (hu.2 z hzx)⟩
  -- the per-element word: conjugate one coefficient
  have hper : ∀ x, (∃ z : ℤ × ℤ, x = HvdH.cfxVal z ∧ HvdH.inDisc p z) →
      HvdH.WordR main celP (fun vs => vs = x :: HvdH.Val.int (p : ℤ) :: rest)
        (fun _ out => ∃ y, out = y :: HvdH.Val.int (p : ℤ) :: rest ∧
          (∃ z w : ℤ × ℤ, x = HvdH.cfxVal z ∧ y = HvdH.cfxVal w ∧ w = conjPair z) ∧
          HvdH.vsz y ≤ 2 * p + 8)
        (fun _ => Kc * (p + 1)) := by
    rintro x ⟨z, rfl, hz⟩
    refine conjConseq (hcel main p z (HvdH.Val.int (p : ℤ) :: rest) hz) (fun _ h => h) ?_
      (fun _ _ => le_rfl)
    rintro vs out hvs hout
    exact ⟨HvdH.cfxVal (conjPair z), by rw [hout]; rfl,
      ⟨z, conjPair z, rfl, rfl, rfl⟩,
      by rw [conjPair_apply]; exact vsz_cfxVal_le (inDisc_conjPair hz)⟩
  have hmain := hmap main celP (HvdH.Val.int (p : ℤ) :: rest)
      (fun x => ∃ z : ℤ × ℤ, x = HvdH.cfxVal z ∧ HvdH.inDisc p z)
      (fun x y => ∃ z w : ℤ × ℤ, x = HvdH.cfxVal z ∧ y = HvdH.cfxVal w ∧ w = conjPair z)
      (Kc * (p + 1)) (2 * p + 8) hper (u.map HvdH.cfxVal) hxs
  refine conjConseq hmain (fun _ h => h) ?_ ?_
  · rintro vs out hvs ⟨ys, hout, hF2⟩
    obtain ⟨v, hys, hvlen, hP⟩ :=
      Work.ConvR.exists_map_cfxVal_of_forall₂ u (R := fun z w => w = conjPair z) hF2
    have hv : v = u.map conjPair := by
      refine eq_of_getD_eq' ((0 : ℤ), (0 : ℤ)) (by rw [hvlen, List.length_map]) ?_
      intro i hi
      rw [hvlen] at hi
      rw [getD_map_conjPair u i, hP i hi]
      rfl
    rw [hout, hys, hv]
    rfl
  · intro vs hvs
    rw [hlen]
    have h9 : (2 * p + 8) + 1 ≤ 9 * (p + 1) := by omega
    have h0 : Kc * (p + 1) + Km * ((2 * p + 8) + 1) ≤ (Kc + 9 * Km) * (p + 1) := by
      have h := Nat.mul_le_mul_left Km h9
      calc Kc * (p + 1) + Km * ((2 * p + 8) + 1) ≤ Kc * (p + 1) + Km * (9 * (p + 1)) :=
            Nat.add_le_add_left h _
        _ = (Kc + 9 * Km) * (p + 1) := by ring
    have hp1 : (p + 1) ≤ (p + 1) ^ 2 := by
      calc (p + 1) = (p + 1) * 1 := by rw [Nat.mul_one]
        _ ≤ (p + 1) * (p + 1) := Nat.mul_le_mul_left _ (by omega)
        _ = (p + 1) ^ 2 := by ring
    have h1 : r * ((Kc + 9 * Km) * (p + 1)) ≤ (Kc + 9 * Km) * ((r + 1) * (p + 1) ^ 2) := by
      have hh : r * (p + 1) ≤ (r + 1) * (p + 1) ^ 2 := by
        have hr : r * (p + 1) ≤ (r + 1) * (p + 1) := Nat.mul_le_mul_right _ (by omega)
        exact le_trans hr (Nat.mul_le_mul_left _ hp1)
      calc r * ((Kc + 9 * Km) * (p + 1)) = (Kc + 9 * Km) * (r * (p + 1)) := by ring
        _ ≤ (Kc + 9 * Km) * ((r + 1) * (p + 1) ^ 2) := Nat.mul_le_mul_left _ hh
    have h2 : (Kc + 9 * Km) * ((r + 1) * (p + 1) ^ 2) + Km ≤
        (Kc + 10 * Km) * ((r + 1) * (p + 1) ^ 2) + (Kc + 10 * Km) := by
      have h3 : (Kc + 9 * Km) * ((r + 1) * (p + 1) ^ 2) ≤
          (Kc + 10 * Km) * ((r + 1) * (p + 1) ^ 2) := Nat.mul_le_mul_right _ (by omega)
      exact Nat.add_le_add h3 (by omega)
    calc r * (Kc * (p + 1) + Km * ((2 * p + 8) + 1)) + Km
        ≤ r * ((Kc + 9 * Km) * (p + 1)) + Km := Nat.add_le_add_right (Nat.mul_le_mul_left r h0) _
      _ ≤ (Kc + 9 * Km) * ((r + 1) * (p + 1) ^ 2) + Km := Nat.add_le_add_right h1 _
      _ ≤ (Kc + 10 * Km) * ((r + 1) * (p + 1) ^ 2) + (Kc + 10 * Km) := h2
      _ = (Kc + 10 * Km) * (r + 1) * (p + 1) ^ 2 + (Kc + 10 * Km) := by ring

/-! ## The vector-conjugation word -/

/-- Conjugate a vector of disc coefficients, with the precision `p` sitting *above* the vector:
`int p :: cvecVal a :: R ↦ cvecVal (a.map conjPair) :: int p :: R` (the parameter ends up below
the vector again), in cost `K (n p²) + K`. -/
theorem conjVecWord_of (hKer : HvdH.KernelLib) (hInt : HvdH.IntLib) (hElem : ConjElemSpec) :
    ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (p n : ℕ) (a : List (ℤ × ℤ)) (R : List HvdH.Val),
      100 ≤ p → 1 ≤ n → a.length = n → HvdH.InDiscVec p n a →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.Val.int p :: HvdH.cvecVal a :: R)
        (fun vs out => vs = HvdH.Val.int p :: HvdH.cvecVal a :: R ∧
          ∃ (ab : List (ℤ × ℤ)),
            out = HvdH.cvecVal ab :: HvdH.Val.int p :: R ∧
            ab.length = n ∧ HvdH.InDiscVec p n ab ∧
            ∀ i < n, ab.getD i (0, 0) = ((a.getD i (0, 0)).1, -(a.getD i (0, 0)).2))
        (fun _ => K * (n * p ^ 2) + K) := by
  obtain ⟨rowP, Krw, hrow⟩ := conjRowWord_of hKer hElem
  obtain ⟨rollP, Kr, hroll⟩ := hKer.roll
  refine ⟨rollP 1 ;;; rowP, 402 * Kr + 8 * Krw, ?_⟩
  intro main p n a R hp hn hlen hdisc
  -- size of the two values that `roll 1` has to move
  have hisz : HvdH.isz (p : ℤ) ≤ p + 2 := by
    have h : p.size ≤ p := nat_size_le_self p
    show (p : ℤ).natAbs.size + 2 ≤ p + 2
    rw [Int.natAbs_natCast]
    omega
  have hvec : HvdH.vsz (HvdH.cvecVal a) ≤ 200 * (n * p ^ 2 + 1) := vsz_cvecVal_le hdisc hp
  have hpn : p + 3 ≤ n * p ^ 2 + 1 := by
    have h1 : p + 3 ≤ p ^ 2 + 1 := by
      have hp2 : p + 2 ≤ p * p := by
        calc p + 2 ≤ 2 * p := by omega
          _ ≤ p * p := Nat.mul_le_mul_right p (by omega)
      have hsq : p * p = p ^ 2 := by ring
      omega
    have h3 : p ^ 2 + 1 ≤ n * p ^ 2 + 1 := by
      have h4 : p ^ 2 * 1 ≤ p ^ 2 * n := Nat.mul_le_mul_left _ hn
      simpa [Nat.mul_comm] using h4
    exact le_trans h1 h3
  have hsz : HvdH.isz (p : ℤ) + HvdH.vsz (HvdH.cvecVal a) + 1 ≤ 201 * (n * p ^ 2 + 1) := by
    have hthis : HvdH.isz (p : ℤ) + HvdH.vsz (HvdH.cvecVal a) + 1
        ≤ (p + 2) + 200 * (n * p ^ 2 + 1) + 1 :=
      Nat.add_le_add (Nat.add_le_add hisz hvec) le_rfl
    have h2 : (p + 2) + 200 * (n * p ^ 2 + 1) + 1 ≤ 201 * (n * p ^ 2 + 1) := by
      have hr : (p + 2) + 200 * (n * p ^ 2 + 1) + 1 = 200 * (n * p ^ 2 + 1) + (p + 3) := by
        ring
      rw [hr, show 201 * (n * p ^ 2 + 1) = 200 * (n * p ^ 2 + 1) + (n * p ^ 2 + 1) from by ring]
      exact Nat.add_le_add_left hpn _
    exact le_trans hthis h2
  -- step 1: `roll 1` moves `int p` below the vector
  have hroll1 : HvdH.WordR main (rollP 1)
      (fun vs => vs = HvdH.Val.int (p : ℤ) :: HvdH.cvecVal a :: R)
      (fun _ out => out = HvdH.cvecVal a :: HvdH.Val.int (p : ℤ) :: R)
      (fun _ => Kr * 2 * (201 * (n * p ^ 2 + 1))) := by
    refine conjConseq (hroll main 1) (fun vs hvs => by rw [hvs]; simp) ?_ ?_
    · rintro vs out hvs hout
      rw [hvs] at hout
      rw [hout]
      simp
    · intro vs hvs
      rw [hvs]
      simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, vsz_int, Nat.add_zero]
      have hmul : Kr * (1 + 1) * (HvdH.isz (p : ℤ) + HvdH.vsz (HvdH.cvecVal a) + 1)
          = Kr * 2 * (HvdH.isz (p : ℤ) + HvdH.vsz (HvdH.cvecVal a) + 1) := by ring
      rw [hmul]
      exact Nat.mul_le_mul_left _ hsz
  -- step 2: conjugate every coefficient of the vector
  have hrow1 : HvdH.WordR main rowP
      (fun vs => vs = HvdH.cvecVal a :: HvdH.Val.int (p : ℤ) :: R)
      (fun _ out => out = HvdH.cvecVal (a.map conjPair) :: HvdH.Val.int (p : ℤ) :: R)
      (fun _ => Krw * (a.length + 1) * (p + 1) ^ 2 + Krw) :=
    hrow main p a.length a R ⟨rfl, hdisc.2⟩
  refine conjConseq (conjSeqFix hroll1 hrow1) (fun _ h => h) ?_ ?_
  · rintro vs out hvs hout
    exact ⟨hvs, a.map conjPair, hout, by rw [List.length_map, hlen],
      inDiscVec_map_conjPair hdisc, fun i _ => getD_map_conjPair a i⟩
  · intro vs hvs
    rw [hlen]
    -- cost: `roll` is `O((n p² + 1)(p+1))`, the row word `O((n+1)(p+1)²)`
    have hp1 : (p + 1) ^ 2 ≤ 4 * p ^ 2 := by
      calc (p + 1) ^ 2 = (p + 1) * (p + 1) := by ring
        _ ≤ (2 * p) * (2 * p) := Nat.mul_le_mul (by omega) (by omega)
        _ = 4 * p ^ 2 := by ring
    have hA : Kr * 2 * (201 * (n * p ^ 2 + 1)) = 402 * Kr * (n * p ^ 2) + 402 * Kr := by ring
    have hB : Krw * (n + 1) * (p + 1) ^ 2 + Krw ≤ 8 * Krw * (n * p ^ 2) + 8 * Krw := by
      have h1 : Krw * (n + 1) * (p + 1) ^ 2 ≤ Krw * (2 * n) * (4 * p ^ 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left Krw (by omega)) hp1
      have h2 : Krw * (2 * n) * (4 * p ^ 2) = 8 * Krw * (n * p ^ 2) := by ring
      rw [h2] at h1
      exact Nat.add_le_add h1 (by omega)
    rw [hA]
    have hsum : (402 * Kr * (n * p ^ 2) + 402 * Kr)
        + (Krw * (n + 1) * (p + 1) ^ 2 + Krw)
        ≤ (402 * Kr * (n * p ^ 2) + 402 * Kr) + (8 * Krw * (n * p ^ 2) + 8 * Krw) :=
      Nat.add_le_add_left hB _
    have he : (402 * Kr * (n * p ^ 2) + 402 * Kr) + (8 * Krw * (n * p ^ 2) + 8 * Krw)
        = (402 * Kr + 8 * Krw) * (n * p ^ 2) + (402 * Kr + 8 * Krw) := by ring
    rwa [he] at hsum

end Work.Transform

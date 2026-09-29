import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Assembly.Base
import Submission.Work.Assembly.Defs
import Submission.Work.Kernel.Raw
import Submission.Work.Main.defs
import Submission.Work.Assembly.cost_lemmas

/-!
# Assembly (area Assembly)

`HvdH.AssemblyProp = KernelLib → IntLib → MainStepProp → RecursionProp → MulProgramC`.

The program built here is

`main := peek 0 r; ite r Glyph.pos core (parse; core; emit)`

where `core := ovh; ifZero (step) (mulS)`, `ovh` computes `n = max (size x) (size y)`,
pushes `n₀` below it and tests `n < n₀`.  Correctness and the `O(n log n)` cost follow by
strong induction on the operand sizes (`RecursionProp` closes the arithmetic).

The cost bounds of the individual pieces are `overCost`/`dispCost` (`Assembly/Defs.lean`); the
overhead chain `ovh` is the delegated lemma `Assembly/ovh_cost`.
-/

namespace Work.Assembly

open HvdH

/-! ## Local helper facts (encodings and sizes) -/

/-- A one-element value stack. -/
theorem encs_singleton (v : Val) : encs [v] = v.enc := by
  rw [Work.Kernel.encs_cons, Work.Kernel.encs_nil, List.append_nil]

/-- `eos`/`inp` glyphs are never `pos`. -/
theorem inpGlyph_headD_ne_pos (w : List (Option Bool × Option Bool)) :
    ((w.map inpGlyph).headD Glyph.eos) ≠ Glyph.pos := by
  cases w with
  | nil => decide
  | cons a t => obtain ⟨a, b⟩ := a; simp [HvdH.inpGlyph]

/-- `zipWithAll` has the length of the longer argument. -/
theorem length_zipWithAll {α β γ : Type*} (f : Option α → Option β → γ) :
    ∀ (l₁ : List α) (l₂ : List β), (List.zipWithAll f l₁ l₂).length = max l₁.length l₂.length
  | [], [] => rfl
  | [], _ :: _ => by simp
  | _ :: _, [] => by simp
  | _ :: as, _ :: bs => by
      rw [List.zipWithAll_cons_cons, List.length_cons, length_zipWithAll f as bs, List.length_cons,
        List.length_cons, max_add_add_right]

/-- The input length is the size of the larger operand. -/
theorem encProd_length (x y : ℕ) :
    (IntegerMultiplication.encodeProd Computability.encodeNat Computability.encodeNat (x, y)).length
      = max x.size y.size := by
  rw [IntegerMultiplication.encodeProd, length_zipWithAll]
  simp [Work.Main.encodeNat_length]

theorem size_mul_le (x y : ℕ) : (x * y).size ≤ x.size + y.size := by
  rw [Nat.size_le, Nat.pow_add]
  rcases Nat.eq_zero_or_pos y with hy | hy
  · subst hy; simp
  · exact Nat.mul_lt_mul_of_lt_of_le (Nat.lt_size_self x) (Nat.le_of_lt (Nat.lt_size_self y))
      (by positivity)

theorem isz_natCast (m : ℕ) : isz (m : ℤ) = m.size + 2 := by
  simp [HvdH.isz, Int.natAbs_natCast]

theorem mulSize_int_int (x y : ℕ) (rest : List Val) :
    mulSize (.int (x : ℤ) :: .int (y : ℤ) :: rest) = max x.size y.size := by
  simp [HvdH.mulSize, Int.natAbs_natCast]

theorem binCost_mul (K x y : ℕ) (rest : List Val) :
    binCost (fun a b => K * isz a * isz b) (.int (x : ℤ) :: .int (y : ℤ) :: rest)
      = K * (x.size + 2) * (y.size + 2) := by
  simp [HvdH.binCost, isz_natCast]

/-- The `ifZero` flag contributes `4 Kiz` in the base case (`n < n₀`). -/
theorem br_cost_small (Kiz Kms n₀ x y : ℕ) (h : max x.size y.size < n₀) :
    Kiz * (isz (zOf n₀ (max x.size y.size)) + 1) +
        max 0 (Kms * (max x.size y.size + 2) * (max x.size y.size + 2))
      = 4 * Kiz + Kms * (max x.size y.size + 2) * (max x.size y.size + 2) := by
  have h1 : isz (zOf n₀ (max x.size y.size)) = 3 := by
    rw [zOf_of_lt h]; norm_num [HvdH.isz]
  rw [h1, Nat.max_eq_right (Nat.zero_le _)]
  ring

/-- The `ifZero` flag contributes `3 Kiz` in the recursive case (`n₀ ≤ n`). -/
theorem br_cost_big (Kiz Km C n₀ x y : ℕ) (h : ¬ max x.size y.size < n₀) :
    Kiz * (isz (zOf n₀ (max x.size y.size)) + 1) +
        max (mainCost Km (CmOf C) (max x.size y.size)) 0
      = 3 * Kiz + mainCost Km (CmOf C) (max x.size y.size) := by
  have hn : n₀ ≤ max x.size y.size := by omega
  have h1 : isz (zOf n₀ (max x.size y.size)) = 2 := by
    rw [zOf_of_le hn]; norm_num [HvdH.isz]
  rw [h1, Nat.max_eq_left (Nat.zero_le _)]
  ring


/-- `vsz` of an integer value built from a natural number. -/
theorem vsz_int_natCast (m : ℕ) : vsz (.int (m : ℤ)) = m.size + 2 := by
  rw [Work.Main.vsz_int, isz_natCast]

/-- Specialise a `WordR` to a concrete input list and a constant cost. -/
theorem wrd_concrete {main p : Cmd} {P : List Val → Prop} {Q : List Val → List Val → Prop}
    {C : List Val → ℕ} {A B : List Val} {c : ℕ}
    (h : WordR main p P Q C) (hA : P A) (hB : ∀ out, Q A out → out = B) (hc : C A ≤ c) :
    WordR main p (fun vs => vs = A) (fun _ out => out = B) (fun _ => c) := by
  intro vs hvs s R hs
  subst vs
  obtain ⟨out, s', n, hPost, hev, hn, hstk, hfr⟩ := h A hA s R hs
  exact ⟨out, s', n, hB out hPost, hev, le_trans hn hc, hstk, hfr⟩

/-- Chain two stage words with exact input / intermediate / output lists. -/
theorem wrd_chain {main : Cmd} {p q : Cmd} {A mid B : List Val} {c1 c2 : ℕ}
    (hp : WordR main p (fun vs => vs = A) (fun _ out => out = mid) (fun _ => c1))
    (hq : WordR main q (fun vs => vs = mid) (fun _ out => out = B) (fun _ => c2)) :
    WordR main (p.seq q) (fun vs => vs = A) (fun _ out => out = B) (fun _ => c1 + c2) := by
  have h := Work.Kernel.WordR_seq hp hq (fun vs mid' _ h2 => ⟨h2, le_rfl⟩)
  refine Work.Kernel.WordR_conseq h (fun vs hvs => hvs) ?_ (fun vs _ => le_rfl)
  intro vs out _ hh
  obtain ⟨m, hm, hB⟩ := hh
  exact hB

/-- The cost arithmetic of the overhead word (one inequality summing the eight stage costs). -/
theorem ovh_arith_aux {Kp Ksz Kmx Kpv Ksw Klt S n₀ x y : ℕ}
    (hS : 1000 * (Kp + Ksz + Kmx + Kpv + Ksw + Klt + 1) ≤ S) :
    Kp * 2 * (x.size + y.size + 5) + Ksz * (y.size + 2) + Kp * 2 * (y.size.size + x.size + 5)
      + Ksz * (x.size + 2) + Kmx * (x.size.size + y.size.size + 4) + Kpv * (n₀.size + 3)
      + Ksw * (n₀.size + (max x.size y.size).size + 5)
      + Klt * ((max x.size y.size).size + n₀.size + 4)
    ≤ S * (max x.size y.size + 1) + S * (n₀.size + 1) := by
  have ha : x.size ≤ max x.size y.size := le_max_left _ _
  have hb : y.size ≤ max x.size y.size := le_max_right _ _
  have has : x.size.size ≤ max x.size y.size :=
    le_trans (Nat.size_le.mpr (Nat.lt_two_pow_self (n := x.size))) ha
  have hbs : y.size.size ≤ max x.size y.size :=
    le_trans (Nat.size_le.mpr (Nat.lt_two_pow_self (n := y.size))) hb
  have hms : (max x.size y.size).size ≤ max x.size y.size :=
    Nat.size_le.mpr (Nat.lt_two_pow_self (n := max x.size y.size))
  nlinarith [ha, hb, has, hbs, hms, hS]

/-! ## Programs -/

/-- The dispatcher overhead: `n = max (size x) (size y)`, push `n₀`, test `n < n₀`. -/
def ovhProg (pickP : ℕ → Cmd) (szP mxP swP ltP : Cmd) (pushP : Val → Cmd) (n₀ : ℕ) : Cmd :=
  .seq (.seq (.seq (.seq (.seq (.seq (.seq (pickP 1) szP) (pickP 1)) szP) mxP)
    (pushP (.int (n₀ : ℤ)))) swP) ltP

/-- The dispatcher: overhead followed by the `ifZero` branch. -/
def dispProg (ovh br : Cmd) : Cmd := .seq ovh br

/-- The whole program: dispatch on `pos` (recursive call) versus raw input. -/
def mainProg (disp parseP emitP : Cmd) (r : Reg) : Cmd :=
  .seq (.peek 0 r) (.ite r Glyph.pos disp (.seq (.seq parseP disp) emitP))

/-- The top-level multiplication program and the induction establishing its cost. -/
theorem assembly : HvdH.AssemblyProp := by
  intro hK hI hM hR
  obtain ⟨pickP, Kp, hpick⟩ := hK.pick
  obtain ⟨swP, Ksw, hsw⟩ := hK.swap
  obtain ⟨pushP, Kpv, hpush⟩ := hK.pushVal
  obtain ⟨izComb, Kiz, hiz⟩ := hK.ifZero
  obtain ⟨szP, Ksz, hsz⟩ := hI.size
  obtain ⟨mxP, Kmx, hmx⟩ := hI.max
  obtain ⟨ltP, Klt, hlt⟩ := hI.lt
  obtain ⟨msP, Kms, hms⟩ := hI.mulS
  obtain ⟨parP, Kpar, hpar⟩ := hI.parse
  obtain ⟨emiP, Kem, hemi⟩ := hI.emit
  obtain ⟨stepP, Km, n₁, hstep⟩ := hM
  obtain ⟨n₀, C, hn₁n₀, hrec⟩ := hR Km n₁ (Kbw Kp Ksz Kmx Kpv Ksw Klt Kiz Kms)
  have hbig : ∀ n : ℕ, n₀ ≤ n →
      mainCost Km (CmOf C) n + Kbw Kp Ksz Kmx Kpv Ksw Klt Kiz Kms * (n + 1) ≤ CmOf C n :=
    fun n hn => (hrec n).1 hn
  have hsmall : ∀ n : ℕ, n < n₀ →
      Kbw Kp Ksz Kmx Kpv Ksw Klt Kiz Kms * ((n + 1) ^ 2 + n₀.size) ≤ CmOf C n :=
    fun n hn => (hrec n).2 hn
  -- the constant dominating the library constants of the dispatcher
  have hSrel : 1000 * (Kp + Ksz + Kmx + Kpv + Ksw + Klt + 1) ≤
      Sw Kp Ksz Kmx Kpv Ksw Klt Kiz Kms := by simp only [Sw]; omega
  have hKbbig : 2 * Sw Kp Ksz Kmx Kpv Ksw Klt Kiz Kms + 3 * Kiz + 3 ≤
      Kbw Kp Ksz Kmx Kpv Ksw Klt Kiz Kms := by simp only [Kbw, Sw]; omega
  have hKbsmall : 2 * Sw Kp Ksz Kmx Kpv Ksw Klt Kiz Kms + 4 * Kiz + 4 * Kms + 3 ≤
      Kbw Kp Ksz Kmx Kpv Ksw Klt Kiz Kms := by simp only [Kbw, Sw]; omega
  let S : ℕ := Sw Kp Ksz Kmx Kpv Ksw Klt Kiz Kms
  have hCmmono : Monotone (CmOf C) := cost_lemmas.1 C
  -- the programs
  let OVH : Cmd := ovhProg pickP szP mxP swP ltP pushP n₀
  let BR : Cmd := izComb stepP msP
  let DISP : Cmd := dispProg OVH BR
  let MAIN : Cmd := mainProg DISP parP emiP 0
  -- the dispatcher's `WordR`
  have hdisp : ∀ (x y : ℕ) (rest₀ : List Val) (N : ℕ), MulBelow MAIN N (CmOf C) →
      max x.size y.size ≤ N → WordR MAIN DISP
        (fun vs => vs = .int (x : ℤ) :: .int (y : ℤ) :: rest₀)
        (fun _ out => out = .int (x * y : ℕ) :: rest₀)
        (fun _ => dispCost S Kiz Kms Km C n₀ x y) := by
    intro x y rest₀ N hMul hN
    -- the eight overhead stages, as concrete stack-to-stack words
    let A0 : List Val := .int (x : ℤ) :: .int (y : ℤ) :: rest₀
    let A1 : List Val := .int (y : ℤ) :: A0
    let A2 : List Val := .int ((y.size : ℕ) : ℤ) :: .int (x : ℤ) :: .int (y : ℤ) :: rest₀
    let A3 : List Val := .int (x : ℤ) :: A2
    let A4 : List Val := .int ((x.size : ℕ) : ℤ) :: A2
    let A5 : List Val := .int (((max x.size y.size : ℕ)) : ℤ) :: .int (x : ℤ) :: .int (y : ℤ) :: rest₀
    let A6 : List Val := .int ((n₀ : ℕ) : ℤ) :: A5
    let A7 : List Val := .int (((max x.size y.size : ℕ)) : ℤ) :: .int ((n₀ : ℕ) : ℤ) ::
      .int (x : ℤ) :: .int (y : ℤ) :: rest₀
    let A8 : List Val := .int (zOf n₀ (max x.size y.size)) :: .int (x : ℤ) :: .int (y : ℤ) :: rest₀
    have hovh : WordR MAIN (ovhProg pickP szP mxP swP ltP pushP n₀)
        (fun vs => vs = A0) (fun _ out => out = A8) (fun _ => overCost S n₀ x y) := by
      have h1 : WordR MAIN (pickP 1) (fun vs => vs = A0) (fun _ out => out = A1)
          (fun _ => Kp * 2 * (x.size + y.size + 5)) := by
        refine wrd_concrete (hpick MAIN 1) ?_ ?_ ?_
        · simp only [A0, List.length_cons]; omega
        · intro out hout
          rw [hout]
          simp only [A0, List.getD_cons_succ, List.getD_cons_zero]
          rfl
        · simp only [A0, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, Nat.add_zero, vsz_int_natCast]
          have h : x.size + 2 + (y.size + 2) + 1 ≤ x.size + y.size + 5 := by omega
          exact Nat.mul_le_mul_left (Kp * 2) h
      have h2 : WordR MAIN szP (fun vs => vs = A1) (fun _ out => out = A2)
          (fun _ => Ksz * (y.size + 2)) := by
        refine wrd_concrete (hsz MAIN) ?_ ?_ ?_
        · exact ⟨(y : ℤ), A0, rfl, trivial⟩
        · intro out hout
          obtain ⟨a, rest, ha, hb⟩ := hout
          dsimp only [A1] at ha
          simp only [List.cons.injEq, Val.int.injEq] at ha
          obtain ⟨rfl, rfl⟩ := ha
          rw [hb]
          simp only [Int.natAbs_natCast]
          rfl
        · simp only [A1, HvdH.unCost, isz_natCast, Int.natAbs_natCast, HvdH.isz]
          exact le_rfl
      have h3 : WordR MAIN (pickP 1) (fun vs => vs = A2) (fun _ out => out = A3)
          (fun _ => Kp * 2 * (y.size.size + x.size + 5)) := by
        refine wrd_concrete (hpick MAIN 1) ?_ ?_ ?_
        · simp only [A2, List.length_cons]; omega
        · intro out hout
          rw [hout]
          simp only [A2, List.getD_cons_succ, List.getD_cons_zero]
          rfl
        · simp only [A2, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, Nat.add_zero, vsz_int_natCast]
          have h : y.size.size + 2 + (x.size + 2) + 1 ≤ y.size.size + x.size + 5 := by omega
          exact Nat.mul_le_mul_left (Kp * 2) h
      have h4 : WordR MAIN szP (fun vs => vs = A3) (fun _ out => out = A4)
          (fun _ => Ksz * (x.size + 2)) := by
        refine wrd_concrete (hsz MAIN) ?_ ?_ ?_
        · exact ⟨(x : ℤ), A2, rfl, trivial⟩
        · intro out hout
          obtain ⟨a, rest, ha, hb⟩ := hout
          dsimp only [A3] at ha
          simp only [List.cons.injEq, Val.int.injEq] at ha
          obtain ⟨rfl, rfl⟩ := ha
          rw [hb]
          simp only [Int.natAbs_natCast]
          rfl
        · simp only [A3, HvdH.unCost, isz_natCast, Int.natAbs_natCast, HvdH.isz]
          exact le_rfl
      have h5 : WordR MAIN mxP (fun vs => vs = A4) (fun _ out => out = A5)
          (fun _ => Kmx * (x.size.size + y.size.size + 4)) := by
        refine wrd_concrete (hmx MAIN) ?_ ?_ ?_
        · exact ⟨((x.size : ℕ) : ℤ), ((y.size : ℕ) : ℤ),
            Val.int (x : ℤ) :: Val.int (y : ℤ) :: rest₀, rfl, trivial⟩
        · intro out hout
          obtain ⟨a, b, rest, ha, hb⟩ := hout
          dsimp only [A4, A2] at ha
          simp only [List.cons.injEq, Val.int.injEq] at ha
          obtain ⟨rfl, rfl, rfl⟩ := ha
          rw [hb, ← Nat.cast_max]
        · simp only [A4, HvdH.binCost, isz_natCast, Int.natAbs_natCast, HvdH.isz]
          have h : x.size.size + 2 + (y.size.size + 2) ≤ x.size.size + y.size.size + 4 := by omega
          exact Nat.mul_le_mul_left Kmx h
      have h6 : WordR MAIN (pushP (.int (n₀ : ℤ))) (fun vs => vs = A5) (fun _ out => out = A6)
          (fun _ => Kpv * (n₀.size + 3)) := by
        refine wrd_concrete (hpush MAIN (Val.int (n₀ : ℤ))) trivial ?_ ?_
        · intro out hout
          rw [hout]
        · simp only [A5, vsz_int_natCast]
          have h : n₀.size + 2 + 1 ≤ n₀.size + 3 := by omega
          exact Nat.mul_le_mul_left Kpv h
      have h7 : WordR MAIN swP (fun vs => vs = A6) (fun _ out => out = A7)
          (fun _ => Ksw * (n₀.size + (max x.size y.size).size + 5)) := by
        refine wrd_concrete (hsw MAIN) ?_ ?_ ?_
        · simp only [A6, A5, List.length_cons]; omega
        · intro out hout
          obtain ⟨a, b, rest, ha, hb⟩ := hout
          dsimp only [A6, A5] at ha
          simp only [List.cons.injEq] at ha
          obtain ⟨rfl, rfl, rfl⟩ := ha
          rw [hb]
        · simp only [A6, A5, List.getD_cons_succ, List.getD_cons_zero, vsz_int_natCast]
          have h : n₀.size + 2 + ((max x.size y.size).size + 2) + 1 ≤
              n₀.size + (max x.size y.size).size + 5 := by omega
          exact Nat.mul_le_mul_left Ksw h
      have h8 : WordR MAIN ltP (fun vs => vs = A7) (fun _ out => out = A8)
          (fun _ => Klt * ((max x.size y.size).size + n₀.size + 4)) := by
        refine wrd_concrete (hlt MAIN) ?_ ?_ ?_
        · exact ⟨((max x.size y.size : ℕ) : ℤ), ((n₀ : ℕ) : ℤ),
            .int (x : ℤ) :: .int (y : ℤ) :: rest₀, rfl, trivial⟩
        · intro out hout
          obtain ⟨a, b, rest, ha, hb⟩ := hout
          dsimp only [A7] at ha
          simp only [List.cons.injEq, Val.int.injEq] at ha
          obtain ⟨rfl, rfl, rfl⟩ := ha
          rw [hb]
          simp only [ite_int_lt_eq_zOf]
          rfl
        · simp only [A7, HvdH.binCost, isz_natCast, Int.natAbs_natCast, HvdH.isz]
          have h : (max x.size y.size).size + 2 + (n₀.size + 2) ≤
              (max x.size y.size).size + n₀.size + 4 := by omega
          exact Nat.mul_le_mul_left Klt h
      have h18 := wrd_chain (wrd_chain (wrd_chain (wrd_chain (wrd_chain (wrd_chain (wrd_chain
        h1 h2) h3) h4) h5) h6) h7) h8
      refine Work.Kernel.WordR_conseq h18 (fun vs hvs => hvs) (fun vs out _ h => h)
        (fun vs _ => ?_)
      simpa only [overCost] using ovh_arith_aux (S := S) (Kp := Kp) (Ksz := Ksz) (Kmx := Kmx)
        (Kpv := Kpv) (Ksw := Ksw) (Klt := Klt) (n₀ := n₀) hSrel
    -- the branch
    have hbr : WordR MAIN (izComb stepP msP)
        (fun vs => vs = .int (zOf n₀ (max x.size y.size)) ::
          .int (x : ℤ) :: .int (y : ℤ) :: rest₀)
        (fun _ out => out = .int (x * y : ℕ) :: rest₀)
        (fun _ => if max x.size y.size < n₀ then
            4 * Kiz + Kms * (max x.size y.size + 2) * (max x.size y.size + 2)
          else 3 * Kiz + mainCost Km (CmOf C) (max x.size y.size)) := by
      by_cases hlt : max x.size y.size < n₀
      · -- schoolbook branch: the step word is not needed
        have hz : zOf n₀ (max x.size y.size) = 1 := zOf_of_lt hlt
        have hstepW : (zOf n₀ (max x.size y.size) = 0 → WordR MAIN stepP
            (fun vs => vs = .int (x : ℤ) :: .int (y : ℤ) :: rest₀)
            (fun _ out => out = .int (x * y : ℕ) :: rest₀) (fun _ => 0)) :=
          fun hc => absurd hc (by rw [hz]; exact one_ne_zero)
        have hmsW : (zOf n₀ (max x.size y.size) ≠ 0 → WordR MAIN msP
            (fun vs => vs = .int (x : ℤ) :: .int (y : ℤ) :: rest₀)
            (fun _ out => out = .int (x * y : ℕ) :: rest₀)
            (fun _ => Kms * (max x.size y.size + 2) * (max x.size y.size + 2))) := by
          intro _
          refine Work.Kernel.WordR_conseq (hms MAIN) ?_ ?_ ?_
          · intro vs hvs
            exact ⟨(x : ℤ), (y : ℤ), rest₀, hvs, trivial⟩
          · intro vs out hvs hout
            obtain ⟨a, b, rest, ha, hb⟩ := hout
            rw [hvs] at ha
            simp only [List.cons.injEq, Val.int.injEq, and_true, true_and] at ha
            obtain ⟨rfl, rfl, rfl⟩ := ha
            rw [hb, Nat.cast_mul]
          · intro vs hvs
            rw [hvs, binCost_mul]
            exact Nat.mul_le_mul (Nat.mul_le_mul_left Kms (Nat.add_le_add_right (le_max_left _ _) 2))
              (Nat.add_le_add_right (le_max_right _ _) 2)
        refine Work.Kernel.WordR_conseq (hiz MAIN stepP msP (zOf n₀ (max x.size y.size))
          (.int (x : ℤ) :: .int (y : ℤ) :: rest₀)
          (fun out => out = .int (x * y : ℕ) :: rest₀)
          (fun out => out = .int (x * y : ℕ) :: rest₀)
          0 (Kms * (max x.size y.size + 2) * (max x.size y.size + 2)) hstepW hmsW)
          (fun vs hvs => hvs) ?_ ?_
        · intro vs out _ hc
          by_cases hz0 : zOf n₀ (max x.size y.size) = 0
          · exact hc.1 hz0
          · exact hc.2 hz0
        · intro vs _
          rw [br_cost_small Kiz Kms n₀ x y hlt]
          exact le_of_eq (by rw [if_pos hlt])
      · -- recursive branch: the step word
        have hz : zOf n₀ (max x.size y.size) = 0 := zOf_of_le (by omega)
        have hstepW : (zOf n₀ (max x.size y.size) = 0 → WordR MAIN stepP
            (fun vs => vs = .int (x : ℤ) :: .int (y : ℤ) :: rest₀)
            (fun _ out => out = .int (x * y : ℕ) :: rest₀)
            (fun _ => mainCost Km (CmOf C) (max x.size y.size))) := by
          intro _
          refine Work.Kernel.WordR_conseq (hstep MAIN N (CmOf C) hCmmono hMul) ?_ ?_ ?_
          · intro vs hvs
            exact ⟨x, y, rest₀, hvs, le_trans hn₁n₀ (by omega), hN⟩
          · intro vs out hvs hout
            obtain ⟨a, b, rest, ha, hb⟩ := hout
            have ha' : (↑a : ℤ) = ↑x ∧ (↑b : ℤ) = ↑y ∧ rest = rest₀ := by
              rw [hvs] at ha
              simpa only [List.cons.injEq, Val.int.injEq] using ha.symm
            obtain ⟨ha1, ha2, ha3⟩ := ha'
            have h1 : a = x := by omega
            have h2 : b = y := by omega
            rw [h1, h2, ha3] at hb
            exact hb
          · intro vs hvs
            rw [hvs, mulSize_int_int]
        have hmsW : (zOf n₀ (max x.size y.size) ≠ 0 → WordR MAIN msP
            (fun vs => vs = .int (x : ℤ) :: .int (y : ℤ) :: rest₀)
            (fun _ out => out = .int (x * y : ℕ) :: rest₀) (fun _ => 0)) :=
          fun hc => (hc hz).elim
        refine Work.Kernel.WordR_conseq (hiz MAIN stepP msP (zOf n₀ (max x.size y.size))
          (.int (x : ℤ) :: .int (y : ℤ) :: rest₀)
          (fun out => out = .int (x * y : ℕ) :: rest₀)
          (fun out => out = .int (x * y : ℕ) :: rest₀)
          (mainCost Km (CmOf C) (max x.size y.size)) 0 hstepW hmsW)
          (fun vs hvs => hvs) ?_ ?_
        · intro vs out _ hc
          by_cases hz0 : zOf n₀ (max x.size y.size) = 0
          · exact hc.1 hz0
          · exact hc.2 hz0
        · intro vs _
          rw [br_cost_big Kiz Km C n₀ x y hlt]
          exact le_of_eq (by rw [if_neg hlt])
    -- assemble the dispatcher
    have hseq : WordR MAIN (dispProg OVH BR)
        (fun vs => vs = .int (x : ℤ) :: .int (y : ℤ) :: rest₀)
        (fun _ out => ∃ mid, mid = .int (zOf n₀ (max x.size y.size)) ::
            .int (x : ℤ) :: .int (y : ℤ) :: rest₀ ∧ out = .int (x * y : ℕ) :: rest₀)
        (fun _ => overCost S n₀ x y +
          (if max x.size y.size < n₀ then
            4 * Kiz + Kms * (max x.size y.size + 2) * (max x.size y.size + 2)
          else 3 * Kiz + mainCost Km (CmOf C) (max x.size y.size))) := by
      rw [dispProg]
      exact Work.Kernel.WordR_seq hovh hbr (fun vs mid h1 h2 => ⟨h2, le_rfl⟩)
    refine Work.Kernel.WordR_conseq hseq (fun vs hvs => hvs) ?_ ?_
    · intro vs out _ h
      obtain ⟨mid, hmid, ho⟩ := h
      exact ho
    · intro vs _
      exact le_of_eq (by simp only [dispCost])
  -- the induction on the operand sizes
  have hind : ∀ N : ℕ, MulBelow MAIN N (CmOf C) := by
    intro N
    induction N with
    | zero =>
      intro vs hpre
      obtain ⟨x, y, rest, -, hx, -⟩ := hpre
      exact absurd hx (by omega)
    | succ N ih =>
      intro vs hpre s R hs
      obtain ⟨x, y, rest, rfl, hx, hy⟩ := hpre
      have hN : max x.size y.size ≤ N := by omega
      have hpeek : Eval MAIN (.peek 0 0) s (State.tPeek s 0 0) 1 := Work.Kernel.eval_peek MAIN 0 0 s
      have hhead : (s.stk 0).headD Glyph.eos = Glyph.pos := by
        rw [hs, Work.Kernel.encs_cons, HvdH.Val.enc]
        simp
      have hreg : (State.tPeek s 0 0).reg 0 = Glyph.pos := by
        simp only [State.tPeek, State.updReg_apply, Function.update_self]
        exact hhead
      obtain ⟨out, s₂, n₂, hpost, he₂, hn₂, hstk₂, hfr₂⟩ :=
        hdisp x y rest N ih hN (.int (x : ℤ) :: .int (y : ℤ) :: rest) rfl
          (State.tPeek s 0 0) R (by simpa only [State.tPeek, State.updReg_stk] using hs)
      dsimp only at hn₂
      refine ⟨out, s₂, 1 + (n₂ + 1) + 1, ⟨x, y, rest, rfl, hpost⟩, ?_, ?_, hstk₂, hfr₂⟩
      · exact Eval.self (Eval.seq hpeek (Work.Kernel.eval_iteT hreg he₂))
      · dsimp only
        rw [mulSize_int_int]
        by_cases hlt : max x.size y.size < n₀
        · have hb := cost_lemmas.2.2.1 (S := S) (Kiz := Kiz) (Kms := Kms)
            (Km := Km) (C := C) (n₀ := n₀) (x := x) (y := y)
            (Kb := Kbw Kp Ksz Kmx Kpv Ksw Klt Kiz Kms) hKbsmall hlt
            (hsmall (max x.size y.size) hlt)
          omega
        · have hb := cost_lemmas.2.1 (S := S) (Kiz := Kiz) (Kms := Kms)
            (Km := Km) (C := C) (n₀ := n₀) (x := x) (y := y)
            (Kb := Kbw Kp Ksz Kmx Kpv Ksw Klt Kiz Kms) hKbbig (by omega)
            (hbig (max x.size y.size) (by omega))
          omega
  -- top level
  refine ⟨MAIN, C + Kpar + 2 * Kem + 2, fun x y => ?_⟩
  let w : List InSym := IntegerMultiplication.encodeProd Computability.encodeNat Computability.encodeNat (x, y)
  let L : ℕ := w.length
  have hLmax : L = max x.size y.size := by
    dsimp only [L, w]; exact encProd_length x y
  let s₀ : State := initState w
  have hs₀' : s₀.stk 0 = w.map inpGlyph := by simp [s₀, HvdH.initState]
  have hs₀'' : ∀ k : Stk, k ≠ 0 → s₀.stk k = [] := by
    intro k hk; simp [s₀, HvdH.initState, hk]
  have hpeek := Work.Kernel.eval_peek MAIN 0 0 s₀
  have hne : (State.tPeek s₀ 0 0).reg 0 ≠ Glyph.pos := by
    have h := inpGlyph_headD_ne_pos w
    simpa [State.tPeek, State.updReg, hs₀'] using h
  obtain ⟨s₁, n₁c, he₁, hn₁c, hstk₁, hfr₁⟩ :=
    hpar MAIN x y (State.tPeek s₀ 0 0) (by simpa only [State.tPeek, State.updReg_stk] using hs₀')
  obtain ⟨out, s₂, n₂, hpost₂, he₂, hn₂, hstk₂, hfr₂⟩ :=
    hdisp x y [] L (hind L) (le_of_eq hLmax.symm)
      (.int (x : ℤ) :: .int (y : ℤ) :: []) rfl s₁ [] (by rw [hstk₁, List.append_nil])
  dsimp only at hn₂
  have hstk₀₂ : s₂.stk 0 = (Val.int (x * y : ℕ)).enc := by
    rw [hstk₂, hpost₂, encs_singleton, List.append_nil]
  have hstk₁₂ : s₂.stk 1 = [] := by
    rw [hfr₂ 1 (by decide), hfr₁ 1 (by decide)]
    simpa only [State.tPeek, State.updReg_stk] using hs₀'' 1 (by decide)
  obtain ⟨s₃, n₃, he₃, hn₃, hstk₀₃, hstk₁₃, hfr₃⟩ := hemi MAIN (x * y) s₂ hstk₀₂ hstk₁₂
  have hn₁c' : n₁c ≤ Kpar * (L + 1) := hn₁c
  refine ⟨s₃, 1 + (n₁c + n₂ + n₃ + 1), ?_, ?_, ?_⟩
  · refine Eval.seq hpeek (Work.Kernel.eval_iteF hne ?_)
    exact Work.Kernel.eval_seq (Work.Kernel.eval_seq he₁ he₂) he₃
  · have hn₃' : n₃ ≤ Kem * (2 * L + 1) := by
      refine le_trans hn₃ (Nat.mul_le_mul_left Kem ?_)
      have h1 : (x * y).size ≤ x.size + y.size := size_mul_le x y
      have h2 : x.size ≤ L := by rw [hLmax]; exact le_max_left _ _
      have h3 : y.size ≤ L := by rw [hLmax]; exact le_max_right _ _
      omega
    have hCmEq : CmOf C (max x.size y.size) = C * (L * L.size + 1) := by
      rw [← hLmax]; rfl
    have hn₂L : n₂ ≤ C * (L * L.size + 1) := by
      by_cases hlt : max x.size y.size < n₀
      · have hb := cost_lemmas.2.2.1 (S := S) (Kiz := Kiz) (Kms := Kms) (Km := Km) (C := C)
          (n₀ := n₀) (x := x) (y := y) (Kb := Kbw Kp Ksz Kmx Kpv Ksw Klt Kiz Kms)
          hKbsmall hlt (hsmall (max x.size y.size) hlt)
        rw [hCmEq] at hb
        omega
      · have hb := cost_lemmas.2.1 (S := S) (Kiz := Kiz) (Kms := Kms) (Km := Km) (C := C)
          (n₀ := n₀) (x := x) (y := y) (Kb := Kbw Kp Ksz Kmx Kpv Ksw Klt Kiz Kms)
          hKbbig (by omega) (hbig (max x.size y.size) (by omega))
        rw [hCmEq] at hb
        omega
    have htop := cost_lemmas.2.2.2 (C := C) (Kp := Kpar) (Ke := Kem) (L := L) (M := n₂) hn₂L
    dsimp only [L, w] at *
    omega
  · intro k
    by_cases hk1 : k = 1
    · rw [hk1]; simp only [if_pos rfl]; exact hstk₁₃
    · rw [if_neg hk1]
      by_cases hk0 : k = 0
      · rw [hk0]; exact hstk₀₃
      · rw [hfr₃ k hk0 hk1, hfr₂ k hk0, hfr₁ k hk0]
        simpa only [State.tPeek, State.updReg_stk] using hs₀'' k hk0

end Work.Assembly

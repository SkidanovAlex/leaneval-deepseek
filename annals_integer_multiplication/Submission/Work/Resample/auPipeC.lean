import Mathlib
import Submission.Work.Resample.auKit2

/-!
# The cleanup word of the weight computation

`[0, Qv, Z, E, E2] ↦ [Qv / E2]` by five rounds of "roll the `k`-th value to the top, use it or
drop it".  Stated parametrically in the four primitive words (`roll`, `drop`, `swap`, `tdiv`) so
that the caller supplies its own witnesses and constants.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Work.Resample
open HvdH Work.Fx

theorem auPipeC (rollP : ℕ → Cmd) (Kroll : ℕ) (dropP : Cmd) (Kdrop : ℕ)
    (swapP : Cmd) (Kswap : ℕ) (tdivP : Cmd) (Ktdiv : ℕ)
    (hRoll : ∀ (m : Cmd) (k : ℕ), WordR m (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Kroll * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (hDrop : ∀ m : Cmd, WordR m dropP (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => Kdrop * (vsz (vs.headD .nil) + 1)))
    (hSwap : ∀ m : Cmd, WordR m swapP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => Kswap * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (hTdiv : ∀ m : Cmd, BinOp m tdivP (fun _ b => b ≠ 0) Int.tdiv
      (fun a b => Ktdiv * isz a * isz b)) :
    ∀ (main : Cmd) (KS : ℕ) (p : ℕ) (Qv Z E E2 : ℤ) (rest : List Val),
      Kroll ≤ KS → Kdrop ≤ KS → Kswap ≤ KS → Ktdiv ≤ KS →
      isz Qv ≤ auSZ p → isz Z ≤ auSZ p → isz E ≤ auSZ p → isz E2 ≤ auSZ p → E2 ≠ 0 →
      WordR main (.seq (rollP 1) (.seq (rollP 4) (.seq swapP (.seq tdivP (.seq (rollP 3)
        (.seq dropP (.seq (rollP 2) (.seq dropP (.seq (rollP 1) dropP)))))))))
        (fun vs => vs = [.int (0 : ℤ), .int Qv, .int Z, .int E, .int E2] ++ rest)
        (fun _ out => out = [.int (Int.tdiv Qv E2)] ++ rest)
        (fun _ => 10 * auSB p KS) := by
  intro main KS p Qv Z E E2 rest hKroll hKdrop hKswap hKtdiv hszQv hsz_Z hsz_E hsz_E2 hE2ne
  have hvszQv : vsz (Val.int Qv) ≤ auSZ p := by rw [vsz_int]; exact hszQv
  have hvsz_Z : vsz (Val.int Z) ≤ auSZ p := by rw [vsz_int]; exact hsz_Z
  have hvsz_E : vsz (Val.int E) ≤ auSZ p := by rw [vsz_int]; exact hsz_E
  have hvsz_E2 : vsz (Val.int E2) ≤ auSZ p := by rw [vsz_int]; exact hsz_E2
  have hvsz0 : vsz (Val.int (0 : ℤ)) ≤ auSZ p := by
    rw [vsz_int]
    exact le_trans (by decide : isz (0 : ℤ) ≤ 5) (by simp only [auSZ]; omega)
  have hone : 1 ≤ auSZ p := by simp only [auSZ]; omega
  have hszR : isz (Int.tdiv Qv E2) ≤ auSZ p := le_trans (isz_tdiv_le Qv E2) hszQv
  have hvszR : vsz (Val.int (Int.tdiv Qv E2)) ≤ auSZ p := by rw [vsz_int]; exact hszR
  have hsum10 : auSB p KS + (auSB p KS + (auSB p KS + (auSB p KS + (auSB p KS
      + (auSB p KS + (auSB p KS + (auSB p KS + (auSB p KS + auSB p KS))))))))
      ≤ 10 * auSB p KS := by omega
  have c1 : Pipe main (rollP 1) [.int (0 : ℤ), .int Qv, .int Z, .int E, .int E2]
      [.int Qv, .int (0 : ℤ), .int Z, .int E, .int E2] (auSB p KS) :=
    Pipe.le (Pipe.rw (Pipe.roll main hRoll
      (A := [.int (0 : ℤ), .int Qv, .int Z, .int E, .int E2]) (k := 1) (by simp)) (by simp))
      (au_le_roll hKroll (by simp) (by simp)
        (by intro v hv
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
            rcases hv with rfl | rfl | rfl | rfl | rfl
            · exact hvsz0
            · exact hvszQv
            · exact hvsz_Z
            · exact hvsz_E
            · exact hvsz_E2))
  have c2 : Pipe main (rollP 4) [.int Qv, .int (0 : ℤ), .int Z, .int E, .int E2]
      [.int E2, .int Qv, .int (0 : ℤ), .int Z, .int E] (auSB p KS) :=
    Pipe.le (Pipe.rw (Pipe.roll main hRoll
      (A := [.int Qv, .int (0 : ℤ), .int Z, .int E, .int E2]) (k := 4) (by simp)) (by simp))
      (au_le_roll hKroll (by simp) (by simp)
        (by intro v hv
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
            rcases hv with rfl | rfl | rfl | rfl | rfl
            · exact hvszQv
            · exact hvsz0
            · exact hvsz_Z
            · exact hvsz_E
            · exact hvsz_E2))
  have c3 : Pipe main swapP [.int E2, .int Qv, .int (0 : ℤ), .int Z, .int E]
      [.int Qv, .int E2, .int (0 : ℤ), .int Z, .int E] (auSB p KS) :=
    Pipe.le (Pipe.appendTail [.int (0 : ℤ), .int Z, .int E]
      (Pipe.swap main hSwap (Val.int E2) (Val.int Qv)))
      (au_le_three hKswap hvsz_E2 hvszQv hone)
  have c4 : Pipe main tdivP [.int Qv, .int E2, .int (0 : ℤ), .int Z, .int E]
      [.int (Int.tdiv Qv E2), .int (0 : ℤ), .int Z, .int E] (auSB p KS) :=
    Pipe.le (Pipe.appendTail [.int (0 : ℤ), .int Z, .int E]
      (Pipe.binOp (hTdiv main) (a := Qv) (b := E2) hE2ne))
      (au_le_mul hKtdiv hszQv hsz_E2)
  have c5 : Pipe main (rollP 3) [.int (Int.tdiv Qv E2), .int (0 : ℤ), .int Z, .int E]
      [.int E, .int (Int.tdiv Qv E2), .int (0 : ℤ), .int Z] (auSB p KS) :=
    Pipe.le (Pipe.rw (Pipe.roll main hRoll
      (A := [.int (Int.tdiv Qv E2), .int (0 : ℤ), .int Z, .int E]) (k := 3) (by simp))
      (by simp))
      (au_le_roll hKroll (by simp) (by simp)
        (by intro v hv
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
            rcases hv with rfl | rfl | rfl | rfl
            · exact hvszR
            · exact hvsz0
            · exact hvsz_Z
            · exact hvsz_E))
  have c6 : Pipe main dropP [.int E, .int (Int.tdiv Qv E2), .int (0 : ℤ), .int Z]
      [.int (Int.tdiv Qv E2), .int (0 : ℤ), .int Z] (auSB p KS) :=
    Pipe.le (Pipe.appendTail [.int (Int.tdiv Qv E2), .int (0 : ℤ), .int Z]
      (Pipe.drop main hDrop (Val.int E))) (au_le_one hKdrop hvsz_E)
  have c7 : Pipe main (rollP 2) [.int (Int.tdiv Qv E2), .int (0 : ℤ), .int Z]
      [.int Z, .int (Int.tdiv Qv E2), .int (0 : ℤ)] (auSB p KS) :=
    Pipe.le (Pipe.rw (Pipe.roll main hRoll
      (A := [.int (Int.tdiv Qv E2), .int (0 : ℤ), .int Z]) (k := 2) (by simp)) (by simp))
      (au_le_roll hKroll (by simp) (by simp)
        (by intro v hv
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
            rcases hv with rfl | rfl | rfl
            · exact hvszR
            · exact hvsz0
            · exact hvsz_Z))
  have c8 : Pipe main dropP [.int Z, .int (Int.tdiv Qv E2), .int (0 : ℤ)]
      [.int (Int.tdiv Qv E2), .int (0 : ℤ)] (auSB p KS) :=
    Pipe.le (Pipe.appendTail [.int (Int.tdiv Qv E2), .int (0 : ℤ)]
      (Pipe.drop main hDrop (Val.int Z))) (au_le_one hKdrop hvsz_Z)
  have c9 : Pipe main (rollP 1) [.int (Int.tdiv Qv E2), .int (0 : ℤ)]
      [.int (0 : ℤ), .int (Int.tdiv Qv E2)] (auSB p KS) :=
    Pipe.le (Pipe.rw (Pipe.roll main hRoll
      (A := [.int (Int.tdiv Qv E2), .int (0 : ℤ)]) (k := 1) (by simp)) (by simp))
      (au_le_roll hKroll (by simp) (by simp)
        (by intro v hv
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
            rcases hv with rfl | rfl
            · exact hvszR
            · exact hvsz0))
  have c10 : Pipe main dropP [.int (0 : ℤ), .int (Int.tdiv Qv E2)]
      [.int (Int.tdiv Qv E2)] (auSB p KS) :=
    Pipe.le (Pipe.appendTail [.int (Int.tdiv Qv E2)]
      (Pipe.drop main hDrop (Val.int (0 : ℤ)))) (au_le_one hKdrop hvsz0)
  exact (Pipe.le (Pipe.comp c1 (Pipe.comp c2 (Pipe.comp c3 (Pipe.comp c4 (Pipe.comp c5
    (Pipe.comp c6 (Pipe.comp c7 (Pipe.comp c8 (Pipe.comp c9 c10))))))))) hsum10) rest

end Work.Resample

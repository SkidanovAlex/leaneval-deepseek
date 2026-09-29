import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.IntLib.encodeNatBridge

set_option maxHeartbeats 4000000

open HvdH

namespace Work.Resample

namespace BuSign

def Wr (main prog : Cmd) (A B : List Val) (c : ℕ) : Prop :=
  ∀ rest : List Val, WordR main prog (fun vs => vs = A ++ rest) (fun _ out => out = B ++ rest)
    (fun _ => c)

theorem Wr.comp (KL : KernelLib) {main p q : Cmd} {A B C : List Val} {c d : ℕ}
    (h1 : Wr main p A B c) (h2 : Wr main q B C d) : Wr main (.seq p q) A C (c + d) := by
  intro rest
  have hseq := KL.seq main p q
    (fun vs : List Val => vs = A ++ rest)
    (fun _ out : List Val => out = B ++ rest)
    (fun _ : List Val => c)
    (fun vs : List Val => vs = B ++ rest)
    (fun _ out : List Val => out = C ++ rest)
    (fun _ : List Val => d)
    (fun _ : List Val => d)
    (h1 rest) (h2 rest)
    (fun vs mid _ hmid => ⟨hmid, le_rfl⟩)
  refine KL.conseq main (.seq p q)
    (fun vs : List Val => vs = A ++ rest)
    (fun vs : List Val => vs = A ++ rest)
    (fun _ out : List Val => ∃ mid, mid = B ++ rest ∧ out = C ++ rest)
    (fun _ out : List Val => out = C ++ rest)
    (fun _ : List Val => c + d) (fun _ : List Val => c + d)
    hseq (fun vs hvs => hvs) ?_ (fun vs hvs => le_rfl)
  intro vs out hvs h
  obtain ⟨mid, _, ho⟩ := h
  exact ho

theorem Wr.mono (KL : KernelLib) {main p : Cmd} {A B : List Val} {c c' : ℕ}
    (h : Wr main p A B c) (hcc : c ≤ c') : Wr main p A B c' := by
  intro rest
  exact KL.conseq main p
    (fun vs : List Val => vs = A ++ rest) (fun vs : List Val => vs = A ++ rest)
    (fun _ out : List Val => out = B ++ rest) (fun _ out : List Val => out = B ++ rest)
    (fun _ : List Val => c) (fun _ : List Val => c')
    (h rest) (fun vs hvs => hvs) (fun _ _ _ ho => ho) (fun _ _ => hcc)

theorem Wr.ofPush (KL : KernelLib) {main prog : Cmd} {v : Val} {c : ℕ} {A : List Val}
    (h : WordR main prog (fun _ => True) (fun vs out => out = v :: vs) (fun _ => c)) :
    Wr main prog A (v :: A) c := by
  intro rest
  refine KL.conseq main prog
    (fun _ => True)
    (fun vs : List Val => vs = A ++ rest)
    (fun vs out => out = v :: vs)
    (fun _ out => out = (v :: A) ++ rest)
    (fun _ : List Val => c) (fun _ : List Val => c)
    h (fun vs _ => trivial) ?_ (fun vs _ => le_rfl)
  intro vs out hvs ho
  rw [ho, hvs]
  simp

theorem Wr.ofUncons (KL : KernelLib) {main prog : Cmd} {K : ℕ} (a b : Val) {A : List Val}
    (h : WordR main prog (fun vs => ∃ a b r, vs = .cons a b :: r)
      (fun vs out => ∃ a b r, vs = .cons a b :: r ∧ out = a :: b :: r) (fun _ => K)) :
    Wr main prog (.cons a b :: A) (a :: b :: A) K := by
  intro rest
  refine KL.conseq main prog
    (fun vs => ∃ a' b' r, vs = .cons a' b' :: r)
    (fun vs : List Val => vs = (.cons a b :: A) ++ rest)
    (fun vs out => ∃ a' b' r, vs = .cons a' b' :: r ∧ out = a' :: b' :: r)
    (fun _ out => out = (a :: b :: A) ++ rest)
    (fun _ : List Val => K) (fun _ : List Val => K)
    h ?_ ?_ (fun vs _ => le_rfl)
  · intro vs hvs
    exact ⟨a, b, A ++ rest, by rw [hvs]; rfl⟩
  · intro vs out hvs ho
    obtain ⟨a', b', r, hvs', ho'⟩ := ho
    rw [hvs] at hvs'
    simp only [List.cons_append, List.cons.injEq, Val.cons.injEq] at hvs'
    obtain ⟨⟨h1, h2⟩, h3⟩ := hvs'
    subst h1; subst h2; subst h3
    rw [ho']
    simp

theorem Wr.ofDrop (KL : KernelLib) {main prog : Cmd} {K : ℕ} {v : Val} {A : List Val}
    (h : WordR main prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v r, vs = v :: r ∧ out = r)
      (fun vs => K * (vsz (vs.headD .nil) + 1))) :
    Wr main prog (v :: A) A (K * (vsz v + 1)) := by
  intro rest
  refine KL.conseq main prog
    (fun vs => vs ≠ [])
    (fun vs : List Val => vs = (v :: A) ++ rest)
    (fun vs out => ∃ v' r, vs = v' :: r ∧ out = r)
    (fun _ out => out = A ++ rest)
    (fun vs => K * (vsz (vs.headD .nil) + 1))
    (fun _ : List Val => K * (vsz v + 1))
    h ?_ ?_ ?_
  · intro vs hvs
    rw [hvs]; simp
  · intro vs out hvs ho
    obtain ⟨v', r, hvs', ho'⟩ := ho
    rw [hvs] at hvs'
    simp only [List.cons_append, List.cons.injEq] at hvs'
    obtain ⟨h1, h2⟩ := hvs'
    subst h1; subst h2
    rw [ho']
  · intro vs hvs
    rw [hvs]; simp

theorem Wr.ofSwap (KL : KernelLib) {main prog : Cmd} {K : ℕ} (a b : Val) {A : List Val}
    (h : WordR main prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b r, vs = a :: b :: r ∧ out = b :: a :: r)
      (fun vs => K * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1))) :
    Wr main prog (a :: b :: A) (b :: a :: A) (K * (vsz a + vsz b + 1)) := by
  intro rest
  refine KL.conseq main prog
    (fun vs => 2 ≤ vs.length)
    (fun vs : List Val => vs = (a :: b :: A) ++ rest)
    (fun vs out => ∃ a' b' r, vs = a' :: b' :: r ∧ out = b' :: a' :: r)
    (fun _ out => out = (b :: a :: A) ++ rest)
    (fun vs => K * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1))
    (fun _ : List Val => K * (vsz a + vsz b + 1))
    h ?_ ?_ ?_
  · intro vs hvs
    rw [hvs]; simp
  · intro vs out hvs ho
    obtain ⟨a', b', r, hvs', ho'⟩ := ho
    rw [hvs] at hvs'
    simp only [List.cons_append, List.cons.injEq] at hvs'
    obtain ⟨h1, h2, h3⟩ := hvs'
    subst h1; subst h2; subst h3
    rw [ho']
    simp
  · intro vs hvs
    rw [hvs]; simp

theorem Wr.ofBinOp (KL : KernelLib) {main prog : Cmd} {P : ℤ → ℤ → Prop} {f : ℤ → ℤ → ℤ}
    {C : ℤ → ℤ → ℕ} (h : BinOp main prog P f C) (a b : ℤ) (hb : P a b) :
    Wr main prog ([.int a, .int b]) ([.int (f a b)]) (C a b) := by
  intro rest
  unfold BinOp at h
  refine KL.conseq main prog
    (fun vs => ∃ a' b' r, vs = .int a' :: .int b' :: r ∧ P a' b')
    (fun vs : List Val => vs = [.int a, .int b] ++ rest)
    (fun vs out => ∃ a' b' r, vs = .int a' :: .int b' :: r ∧ out = .int (f a' b') :: r)
    (fun _ out => out = [.int (f a b)] ++ rest)
    (binCost C) (fun _ : List Val => C a b)
    h ?_ ?_ ?_
  · intro vs hvs
    exact ⟨a, b, rest, by rw [hvs]; rfl, hb⟩
  · intro vs out hvs ho
    obtain ⟨a', b', r, hvs', ho'⟩ := ho
    rw [hvs] at hvs'
    simp only [List.cons_append, List.nil_append, List.cons.injEq, Val.int.injEq] at hvs'
    obtain ⟨h1, h2, h3⟩ := hvs'
    subst h1; subst h2; subst h3
    rw [ho']
    simp
  · intro vs hvs
    rw [hvs]
    rfl

/-- One step's cost against the uniform budget. -/
theorem step_le {Kc p c m : ℕ} (hc : c ≤ Kc) (hm : m ≤ 12 * (p + 1)) :
    c * m ≤ 12 * (Kc * (p + 1)) := by
  calc c * m ≤ Kc * m := Nat.mul_le_mul_right m hc
    _ ≤ Kc * (12 * (p + 1)) := Nat.mul_le_mul_left Kc hm
    _ = 12 * (Kc * (p + 1)) := by ring

theorem vsz_int_eq (z : ℤ) : vsz (Val.int z) = isz z := Work.IntLib.vsz_int z

theorem tmod_two_eq (i : ℕ) : Int.tmod (i : ℤ) 2 = ((i % 2 : ℕ) : ℤ) := by
  rw [Int.tmod_eq_emod]; simp

theorem natAbs_tmod_two (i : ℕ) : (Int.tmod (i : ℤ) 2).natAbs ≤ 1 := by
  rw [tmod_two_eq, Int.natAbs_natCast]
  exact Nat.le_of_lt_succ (Nat.mod_lt i (by norm_num))

theorem isz_tmod_two (i : ℕ) : isz (Int.tmod (i : ℤ) 2) ≤ 3 := by
  have h := natAbs_tmod_two i
  have hs : (Int.tmod (i : ℤ) 2).natAbs.size ≤ 1 := Nat.size_le.mpr (by omega)
  simp only [HvdH.isz]; omega

theorem natAbs_two_mul_tmod_two (i : ℕ) : (2 * Int.tmod (i : ℤ) 2).natAbs ≤ 2 := by
  rw [tmod_two_eq]
  have h : (2 : ℤ) * ((i % 2 : ℕ) : ℤ) = (((2 * (i % 2) : ℕ)) : ℤ) := by push_cast; ring
  rw [h, Int.natAbs_natCast]
  have := Nat.mod_lt i (by norm_num : 0 < 2)
  omega

theorem isz_two_mul_tmod_two (i : ℕ) : isz (2 * Int.tmod (i : ℤ) 2) ≤ 4 := by
  have h := natAbs_two_mul_tmod_two i
  have hs : (2 * Int.tmod (i : ℤ) 2).natAbs.size ≤ 2 := Nat.size_le.mpr (by omega)
  simp only [HvdH.isz]; omega

end BuSign

open Work.Resample.BuSign

theorem buSignElem (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ) (hp : 1 ≤ p) (i : ℕ)
      (hi : i < 2 ^ (2 * p)),
      ∀ rest : List HvdH.Val, HvdH.WordR main prog
        (fun vs => vs = [HvdH.Val.cons (HvdH.Val.int (i : ℤ)) HvdH.Val.nil] ++ rest)
        (fun vs out => vs = [HvdH.Val.cons (HvdH.Val.int (i : ℤ)) HvdH.Val.nil] ++ rest ∧
          out = [HvdH.Val.int (1 - 2 * ((i % 2 : ℕ) : ℤ))] ++ rest)
        (fun _ => K * (p + 1) ^ K) := by
  obtain ⟨uProg, uK, uSpec⟩ := KL.unconsV
  obtain ⟨sProg, sK, sSpec⟩ := KL.swap
  obtain ⟨dProg, dK, dSpec⟩ := KL.drop
  obtain ⟨pvProg, pvK, pvSpec⟩ := KL.pushVal
  obtain ⟨tmProg, tmK, tmSpec⟩ := IL.tmod
  obtain ⟨msProg, msK, msSpec⟩ := IL.mulS
  obtain ⟨sbProg, sbK, sbSpec⟩ := IL.sub
  set Kc : ℕ := uK + sK + dK + pvK + tmK + msK + sbK + 1 with hKc
  set Kbig : ℕ := 120 * Kc + 2 with hKbig
  let pv2 : Cmd := pvProg (.int 2)
  let pv1 : Cmd := pvProg (.int 1)
  let prg : Cmd := .seq uProg (.seq sProg (.seq dProg (.seq pv2 (.seq sProg (.seq tmProg
    (.seq pv2 (.seq msProg (.seq pv1 sbProg))))))))
  refine ⟨prg, Kbig, ?_⟩
  intro main p hp i hi rest
  set X : ℕ := Kc * (p + 1) with hX
  have huK : uK ≤ Kc := by rw [hKc]; omega
  have hsK : sK ≤ Kc := by rw [hKc]; omega
  have hdK : dK ≤ Kc := by rw [hKc]; omega
  have hpvK : pvK ≤ Kc := by rw [hKc]; omega
  have htmK : tmK ≤ Kc := by rw [hKc]; omega
  have hmsK : msK ≤ Kc := by rw [hKc]; omega
  have hsbK : sbK ≤ Kc := by rw [hKc]; omega
  have hIszI : isz ((i : ℤ)) ≤ 2 * p + 2 := by
    have h1 : i.size ≤ 2 * p := Nat.size_le.mpr hi
    simp only [HvdH.isz, Int.natAbs_natCast]
    omega
  have hVszI : vsz (HvdH.Val.int (i : ℤ)) = isz (i : ℤ) := vsz_int_eq _
  have hVsz2 : vsz (HvdH.Val.int 2) = 4 := by rw [vsz_int_eq]; decide
  have hVsz1 : vsz (HvdH.Val.int 1) = 3 := by rw [vsz_int_eq]; decide
  have hVszNil : vsz (HvdH.Val.nil) = 1 := rfl
  have hIsz2 : isz (2 : ℤ) = 4 := by decide
  have hIsz1 : isz (1 : ℤ) = 3 := by decide
  have hIszTm : isz (Int.tmod (i : ℤ) 2) ≤ 3 := isz_tmod_two i
  have hIsz2Tm : isz (2 * Int.tmod (i : ℤ) 2) ≤ 4 := isz_two_mul_tmod_two i
  have hXK : 120 * X ≤ Kbig * (p + 1) ^ Kbig := by
    have hp1 : 1 ≤ p + 1 := by omega
    have hK1 : 1 ≤ Kbig := by rw [hKbig]; omega
    have hpow : p + 1 ≤ (p + 1) ^ Kbig := by
      have h1 : (p + 1) ^ 1 ≤ (p + 1) ^ Kbig := Nat.pow_le_pow_right (by omega) hK1
      simpa using h1
    have hKle : 120 * Kc ≤ Kbig := by rw [hKbig]; omega
    calc 120 * X = 120 * (Kc * (p + 1)) := by rw [hX]
      _ = 120 * Kc * (p + 1) := by ring
      _ ≤ Kbig * (p + 1) := Nat.mul_le_mul_right (p + 1) hKle
      _ ≤ Kbig * (p + 1) ^ Kbig := Nat.mul_le_mul_left Kbig hpow
  have hU : Wr main uProg [HvdH.Val.cons (HvdH.Val.int (i : ℤ)) HvdH.Val.nil]
      [HvdH.Val.int (i : ℤ), HvdH.Val.nil] (12 * X) :=
    Wr.mono (KL := KL)
      (Wr.ofUncons (KL := KL) (HvdH.Val.int (i : ℤ)) HvdH.Val.nil (A := []) (uSpec main))
      (by
        have h := step_le (Kc := Kc) (p := p) (c := uK) (m := 1) huK (by omega)
        simpa using h)
  have hSw1 : Wr main sProg [HvdH.Val.int (i : ℤ), HvdH.Val.nil]
      [HvdH.Val.nil, HvdH.Val.int (i : ℤ)] (12 * X) :=
    Wr.mono (KL := KL)
      (Wr.ofSwap (KL := KL) (HvdH.Val.int (i : ℤ)) HvdH.Val.nil (A := []) (sSpec main))
      (step_le (Kc := Kc) (p := p) (c := sK)
        (m := vsz (HvdH.Val.int (i : ℤ)) + vsz (HvdH.Val.nil) + 1) hsK
        (by rw [hVszI, hVszNil]; omega))
  have hDp : Wr main dProg [HvdH.Val.nil, HvdH.Val.int (i : ℤ)] [HvdH.Val.int (i : ℤ)]
      (12 * X) :=
    Wr.mono (KL := KL)
      (Wr.ofDrop (KL := KL) (v := HvdH.Val.nil) (A := [HvdH.Val.int (i : ℤ)]) (dSpec main))
      (step_le (Kc := Kc) (p := p) (c := dK) (m := vsz (HvdH.Val.nil) + 1) hdK
        (by rw [hVszNil]; omega))
  have hP2a : Wr main pv2 [HvdH.Val.int (i : ℤ)]
      [HvdH.Val.int 2, HvdH.Val.int (i : ℤ)] (12 * X) :=
    Wr.mono (KL := KL)
      (Wr.ofPush (KL := KL) (A := [HvdH.Val.int (i : ℤ)]) (pvSpec main (.int 2)))
      (step_le (Kc := Kc) (p := p) (c := pvK) (m := vsz (HvdH.Val.int 2) + 1) hpvK
        (by rw [hVsz2]; omega))
  have hSw2 : Wr main sProg [HvdH.Val.int 2, HvdH.Val.int (i : ℤ)]
      [HvdH.Val.int (i : ℤ), HvdH.Val.int 2] (12 * X) :=
    Wr.mono (KL := KL)
      (Wr.ofSwap (KL := KL) (HvdH.Val.int 2) (HvdH.Val.int (i : ℤ)) (A := []) (sSpec main))
      (step_le (Kc := Kc) (p := p) (c := sK)
        (m := vsz (HvdH.Val.int 2) + vsz (HvdH.Val.int (i : ℤ)) + 1) hsK
        (by rw [hVsz2, hVszI]; omega))
  have hTM : Wr main tmProg [HvdH.Val.int (i : ℤ), HvdH.Val.int 2]
      [HvdH.Val.int (Int.tmod (i : ℤ) 2)] (12 * X) :=
    Wr.mono (KL := KL)
      (Wr.ofBinOp (KL := KL) (tmSpec main) (i : ℤ) 2 (by norm_num))
      (by
        have h := step_le (Kc := Kc) (p := p) (c := tmK) (m := isz (i : ℤ) * isz (2 : ℤ)) htmK
          (by rw [hIsz2]; omega)
        simpa only [Nat.mul_assoc] using h)
  have hP2b : Wr main pv2 [HvdH.Val.int (Int.tmod (i : ℤ) 2)]
      [HvdH.Val.int 2, HvdH.Val.int (Int.tmod (i : ℤ) 2)] (12 * X) :=
    Wr.mono (KL := KL)
      (Wr.ofPush (KL := KL) (A := [HvdH.Val.int (Int.tmod (i : ℤ) 2)]) (pvSpec main (.int 2)))
      (step_le (Kc := Kc) (p := p) (c := pvK) (m := vsz (HvdH.Val.int 2) + 1) hpvK
        (by rw [hVsz2]; omega))
  have hMS : Wr main msProg [HvdH.Val.int 2, HvdH.Val.int (Int.tmod (i : ℤ) 2)]
      [HvdH.Val.int (2 * Int.tmod (i : ℤ) 2)] (12 * X) :=
    Wr.mono (KL := KL)
      (Wr.ofBinOp (KL := KL) (msSpec main) (2 : ℤ) (Int.tmod (i : ℤ) 2) (by trivial))
      (by
        have h := step_le (Kc := Kc) (p := p) (c := msK)
          (m := isz (2 : ℤ) * isz (Int.tmod (i : ℤ) 2)) hmsK (by rw [hIsz2]; omega)
        simpa only [Nat.mul_assoc] using h)
  have hP1 : Wr main pv1 [HvdH.Val.int (2 * Int.tmod (i : ℤ) 2)]
      [HvdH.Val.int 1, HvdH.Val.int (2 * Int.tmod (i : ℤ) 2)] (12 * X) :=
    Wr.mono (KL := KL)
      (Wr.ofPush (KL := KL) (A := [HvdH.Val.int (2 * Int.tmod (i : ℤ) 2)]) (pvSpec main (.int 1)))
      (step_le (Kc := Kc) (p := p) (c := pvK) (m := vsz (HvdH.Val.int 1) + 1) hpvK
        (by rw [hVsz1]; omega))
  have hSB : Wr main sbProg [HvdH.Val.int 1, HvdH.Val.int (2 * Int.tmod (i : ℤ) 2)]
      [HvdH.Val.int (1 - 2 * Int.tmod (i : ℤ) 2)] (12 * X) :=
    Wr.mono (KL := KL)
      (Wr.ofBinOp (KL := KL) (sbSpec main) (1 : ℤ) (2 * Int.tmod (i : ℤ) 2) (by trivial))
      (step_le (Kc := Kc) (p := p) (c := sbK)
        (m := isz (1 : ℤ) + isz (2 * Int.tmod (i : ℤ) 2)) hsbK
        (by rw [hIsz1]; omega))
  have hAll := Wr.comp KL hU (Wr.comp KL hSw1 (Wr.comp KL hDp (Wr.comp KL hP2a
    (Wr.comp KL hSw2 (Wr.comp KL hTM (Wr.comp KL hP2b (Wr.comp KL hMS
      (Wr.comp KL hP1 hSB))))))))
  refine KL.conseq main prg
    (fun vs => vs = [HvdH.Val.cons (HvdH.Val.int (i : ℤ)) HvdH.Val.nil] ++ rest)
    (fun vs => vs = [HvdH.Val.cons (HvdH.Val.int (i : ℤ)) HvdH.Val.nil] ++ rest)
    (fun _ out => out = [HvdH.Val.int (1 - 2 * Int.tmod (i : ℤ) 2)] ++ rest)
    (fun vs out => vs = [HvdH.Val.cons (HvdH.Val.int (i : ℤ)) HvdH.Val.nil] ++ rest ∧
      out = [HvdH.Val.int (1 - 2 * ((i % 2 : ℕ) : ℤ))] ++ rest)
    _ _ (hAll rest) ?_ ?_ ?_
  · intro vs hvs
    exact hvs
  · intro vs out hvs ho
    exact ⟨hvs, by rw [ho, tmod_two_eq i]⟩
  · intro vs _
    omega

end Work.Resample

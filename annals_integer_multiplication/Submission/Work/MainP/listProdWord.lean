import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.ConvR.basic
import Submission.Work.Transform.arrangeDefs

/-!
# `Work.MainP.listProdWord`: the product of a list of natural numbers

`intList ss :: rest ↦ int (∏ ss) :: rest`, computed by pushing a unit, swapping it below the list
and running `KernelLib.foldList` with `IntLib.mulS`.  The program does not depend on `ss`; this is
what allows Proposition 5.3 to obtain the scaling factor `S = ∏ sᵢ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.MainP

open HvdH

private theorem isz_nat_le (n : ℕ) : HvdH.isz ((n : ℕ) : ℤ) ≤ n + 2 := by
  rw [HvdH.isz, Int.natAbs_natCast]
  have h : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  omega

/-- `Σ (t.size + 3)` over a list of naturals below `2^p`. -/
private theorem mapSum_le : ∀ (l : List ℕ) (p : ℕ), (∀ t ∈ l, t < 2 ^ p) →
    (l.map fun t => t.size + 3).sum ≤ l.length * (p + 3) := by
  intro l p hl
  induction l with
  | nil => simp
  | cons t ts ih =>
    have ht : t < 2 ^ p := hl t (by simp)
    have hts : ∀ x ∈ ts, x < 2 ^ p := fun x hx => hl x (by simp [hx])
    have h1 : t.size ≤ p := Nat.size_le.mpr ht
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h2 := ih hts
    calc t.size + 3 + (List.map (fun t => t.size + 3) ts).sum
        ≤ (p + 3) + ts.length * (p + 3) := by omega
      _ = (ts.length + 1) * (p + 3) := by ring

/-- The list coercion `List ℕ → List ℤ` is `List.map (↑·)` (propositionally: it is defined via
`List.flatMap`). -/
private theorem coe_list_nat_int (l : List ℕ) :
    ((l : List ℤ)) = l.map (fun t : ℕ => (t : ℤ)) := by
  show List.flatMap (fun a : ℕ => [((a : ℕ) : ℤ)]) l = List.map (fun t : ℕ => (t : ℤ)) l
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.flatMap_cons, ih]; rfl

/-- `HvdH.intList` agrees with the explicit `ℕ`-map form used by `listProdWord` (the two are equal
but not definitionally equal: `intList`'s definition coerces the list to `List ℤ`). -/
theorem intList_eq_map (l : List ℕ) :
    HvdH.intList l = HvdH.ofList (l.map (fun t : ℕ => HvdH.Val.int (t : ℤ))) := by
  rw [show HvdH.intList l = HvdH.ofList ((l : List ℤ).map (fun n : ℤ => HvdH.Val.int n)) from rfl,
      coe_list_nat_int l, List.map_map]
  rfl

/-- Encoding size of the value list used by the pipeline for `intList l`, when all entries are
`< 2^p`.  (Stated for the explicit `ℕ`-map rather than `intList`: `intList`'s definition coerces
the list to `List ℤ`, so the two forms are equal but not definitionally equal.) -/
private theorem vsz_intList_le' (l : List ℕ) (p : ℕ) (hl : ∀ t ∈ l, t < 2 ^ p) :
    HvdH.vsz (HvdH.ofList (l.map (fun t : ℕ => HvdH.Val.int (t : ℤ)))) ≤ (l.length + 1) * (p + 4) := by
  have hsum : ((l.map (fun t : ℕ => HvdH.Val.int (t : ℤ))).map HvdH.vsz).sum ≤ l.length * (p + 3) := by
    calc ((l.map (fun t : ℕ => HvdH.Val.int (t : ℤ))).map HvdH.vsz).sum
        = (l.map (HvdH.vsz ∘ fun t : ℕ => HvdH.Val.int (t : ℤ))).sum := by rw [List.map_map]
      _ ≤ (l.map (fun t : ℕ => t.size + 3)).sum := by
          refine List.sum_le_sum (fun t ht => ?_)
          simp only [Function.comp_apply]
          rw [Work.ConvR.vsz_int, HvdH.isz, Int.natAbs_natCast]
          omega
      _ ≤ l.length * (p + 3) := mapSum_le l p hl
  rw [Work.ConvR.vsz_ofList, List.length_map]
  have h3 : l.length * (p + 3) + l.length + 1 ≤ (l.length + 1) * (p + 4) := by
    have e : (l.length + 1) * (p + 4) = l.length * (p + 3) + l.length + (p + 4) := by ring
    rw [e]
    omega
  omega

private theorem costBound3 (Kpv Kr Kfold Kmul ss_len p : ℕ) :
    Kpv * (p + 4) ^ 2 + Kr * (2 * ((ss_len + 2) * (p + 4) + 1))
        + (ss_len * (Kmul * (p + 3) ^ 2 + Kfold * (p + 4)) + Kfold)
      ≤ 12 * (Kpv + Kr + 2 * Kfold + Kmul + 1) * (ss_len + 1) * (p + 4) ^ 2
        + 12 * (Kpv + Kr + 2 * Kfold + Kmul + 1) := by
  set Q : ℕ := Kpv + Kr + 2 * Kfold + Kmul + 1 with hQ
  set B : ℕ := (ss_len + 2) * (p + 4) ^ 2 with hB
  have hp4sq : p + 4 ≤ (p + 4) ^ 2 := by rw [pow_two]; exact Nat.le_mul_self _
  have hpp : (p + 3) ^ 2 ≤ (p + 4) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hQ1 : Kpv ≤ Q := by omega
  have hQ2 : Kr ≤ Q := by omega
  have hQ3 : Kfold ≤ Q := by omega
  have hQ6 : Kmul + Kfold ≤ Q := by omega
  have hone : 1 ≤ (p + 4) ^ 2 := by
    calc (1 : ℕ) ≤ p + 4 := by omega
      _ ≤ (p + 4) * (p + 4) := Nat.le_mul_self _
      _ = (p + 4) ^ 2 := by ring_nf
  have hBle : (ss_len + 2) * (p + 4) ≤ B := by
    rw [hB]; exact Nat.mul_le_mul_left _ hp4sq
  have ha : Kpv * (p + 4) ^ 2 ≤ Q * (B + 1) := by
    have h1 : Kpv * (p + 4) ^ 2 ≤ Q * (p + 4) ^ 2 := Nat.mul_le_mul_right _ hQ1
    have h2 : Q * (p + 4) ^ 2 ≤ Q * B := by
      refine Nat.mul_le_mul_left _ ?_
      calc (p + 4) ^ 2 = 1 * (p + 4) ^ 2 := by ring
        _ ≤ (ss_len + 2) * (p + 4) ^ 2 := Nat.mul_le_mul_right _ (by omega)
    have h3 : Q * B ≤ Q * (B + 1) := Nat.mul_le_mul_left _ (Nat.le_add_right B 1)
    exact le_trans h1 (le_trans h2 h3)
  have hb : Kr * (2 * ((ss_len + 2) * (p + 4) + 1)) ≤ 2 * (Q * (B + 1)) := by
    have h1 : (ss_len + 2) * (p + 4) + 1 ≤ B + 1 := by have := hBle; omega
    calc Kr * (2 * ((ss_len + 2) * (p + 4) + 1))
        = 2 * (Kr * ((ss_len + 2) * (p + 4) + 1)) := by ring
      _ ≤ 2 * (Q * (B + 1)) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul hQ2 h1)
  have hc : ss_len * (Kmul * (p + 3) ^ 2 + Kfold * (p + 4)) + Kfold ≤ Q * (B + 1) := by
    have h3 : Kmul * (p + 4) ^ 2 + Kfold * (p + 4) ^ 2 ≤ Q * (p + 4) ^ 2 := by
      rw [← add_mul]
      exact Nat.mul_le_mul_right _ hQ6
    have e1 : ss_len * (Kmul * (p + 3) ^ 2 + Kfold * (p + 4)) ≤ ss_len * (Q * (p + 4) ^ 2) := by
      refine Nat.mul_le_mul_left _ ?_
      exact le_trans (Nat.add_le_add (Nat.mul_le_mul_left _ hpp)
        (Nat.mul_le_mul_left _ hp4sq)) h3
    have e2 : Kfold ≤ Q * (p + 4) ^ 2 := by
      calc Kfold ≤ Q := hQ3
        _ = Q * 1 := by ring
        _ ≤ Q * (p + 4) ^ 2 := Nat.mul_le_mul_left _ hone
    have e3 : ss_len * (Q * (p + 4) ^ 2) + Q * (p + 4) ^ 2
        = (ss_len + 1) * (Q * (p + 4) ^ 2) := by ring_nf
    have e4 : (ss_len + 1) * (Q * (p + 4) ^ 2) ≤ (ss_len + 2) * (Q * (p + 4) ^ 2) :=
      Nat.mul_le_mul_right _ (by omega)
    have e5 : (ss_len + 2) * (Q * (p + 4) ^ 2) = Q * B := by rw [hB]; ring_nf
    have e6 : Q * B ≤ Q * (B + 1) := Nat.mul_le_mul_left _ (Nat.le_add_right B 1)
    calc ss_len * (Kmul * (p + 3) ^ 2 + Kfold * (p + 4)) + Kfold
        ≤ ss_len * (Q * (p + 4) ^ 2) + Q * (p + 4) ^ 2 := Nat.add_le_add e1 e2
      _ = (ss_len + 1) * (Q * (p + 4) ^ 2) := e3
      _ ≤ (ss_len + 2) * (Q * (p + 4) ^ 2) := e4
      _ = Q * B := e5
      _ ≤ Q * (B + 1) := e6
  have hBle2 : B ≤ 2 * (ss_len + 1) * (p + 4) ^ 2 := by
    rw [hB]
    calc (ss_len + 2) * (p + 4) ^ 2 ≤ (2 * (ss_len + 1)) * (p + 4) ^ 2 :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 2 * (ss_len + 1) * (p + 4) ^ 2 := by ring_nf
  have hsum : Kpv * (p + 4) ^ 2 + Kr * (2 * ((ss_len + 2) * (p + 4) + 1))
        + (ss_len * (Kmul * (p + 3) ^ 2 + Kfold * (p + 4)) + Kfold)
      ≤ 12 * Q * (ss_len + 1) * (p + 4) ^ 2 + 12 * Q := by
    nlinarith [ha, hb, hc, hBle2, Nat.zero_le Q, Nat.zero_le B,
      Nat.zero_le ((p + 4) ^ 2), Nat.zero_le (ss_len + 1)]
  exact hsum

/-- The product of a list of naturals, as a value word. -/
theorem listProdWord (hK : HvdH.KernelLib) (hI : HvdH.IntLib) :
    ∃ (q : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (ss : List ℕ) (rest : List HvdH.Val) (p : ℕ),
      (∀ t ∈ ss, t < 2 ^ p) → (∀ t ∈ ss, 1 ≤ t) → ss.prod < 2 ^ p →
      HvdH.WordR main q (fun vs => vs = HvdH.ofList (ss.map (fun t : ℕ => HvdH.Val.int (t : ℤ))) :: rest)
        (fun _ out => out = HvdH.Val.int ((ss.prod : ℕ) : ℤ) :: rest)
        (fun _ => K * (ss.length + 1) * (p + 4) ^ 2 + K) := by
  obtain ⟨pushP, Kpv, hpush⟩ := hK.pushVal
  obtain ⟨rollP, Kr, hroll⟩ := hK.roll
  obtain ⟨foldC, Kfold, hfold⟩ := hK.foldList
  obtain ⟨mulP, Kmul, hmul⟩ := hI.mulS
  refine ⟨HvdH.Cmd.seq (HvdH.Cmd.seq (pushP (HvdH.Val.int (1 : ℤ))) (rollP 1)) (foldC mulP),
    12 * (Kpv + Kr + 2 * Kfold + Kmul + 1), ?_⟩
  intro main ss rest p hlt hp1 hsp
  have hisz : ∀ t ∈ ss, HvdH.isz ((t : ℤ)) ≤ p + 3 := by
    intro t ht
    refine Work.ConvR.isz_le_of_natAbs_le ?_
    rw [Int.natAbs_natCast]
    exact le_of_lt (hlt t ht)
  have hPle : ∀ i, i ≤ ss.length → (ss.take i).prod ≤ ss.prod := by
    intro i _
    have h := List.prod_take_mul_prod_drop ss i
    have h1 : 1 ≤ (ss.drop i).prod :=
      List.one_le_prod (fun a ha => hp1 a (List.mem_of_mem_drop ha))
    calc (ss.take i).prod ≤ (ss.take i).prod * (ss.drop i).prod := Nat.le_mul_of_pos_right _ h1
      _ = ss.prod := h
  have hPlt : ∀ i, i ≤ ss.length → (ss.take i).prod < 2 ^ p := fun i hi =>
    lt_of_le_of_lt (hPle i hi) hsp
  -- stage 1: push the unit
  have s1 : Work.ConvR.WordC main (pushP (HvdH.Val.int (1 : ℤ)))
      (fun vs => vs = HvdH.ofList (ss.map (fun t : ℕ => HvdH.Val.int (t : ℤ))) :: rest)
      (fun _ out => out = HvdH.Val.int (1 : ℤ) :: HvdH.ofList (ss.map (fun t : ℕ => HvdH.Val.int (t : ℤ))) :: rest)
      (Kpv * (p + 4) ^ 2) := by
    refine hK.conseq main (pushP (HvdH.Val.int (1 : ℤ))) (fun _ => True)
      (fun vs => vs = HvdH.ofList (ss.map (fun t : ℕ => HvdH.Val.int (t : ℤ))) :: rest)
      (fun vs out => out = HvdH.Val.int (1 : ℤ) :: vs)
      (fun _ out => out = HvdH.Val.int (1 : ℤ) :: HvdH.ofList (ss.map (fun t : ℕ => HvdH.Val.int (t : ℤ))) :: rest)
      (fun _ => Kpv * (HvdH.vsz (HvdH.Val.int (1 : ℤ)) + 1)) (fun _ => Kpv * (p + 4) ^ 2)
      (hpush main (HvdH.Val.int (1 : ℤ))) (fun vs _ => trivial) ?_ ?_
    · intro vs out hvs hout
      rw [hvs] at hout
      exact hout
    · intro vs _
      have hv : HvdH.vsz (HvdH.Val.int (1 : ℤ)) + 1 ≤ (p + 4) ^ 2 := by
        have h1 : HvdH.vsz (HvdH.Val.int (1 : ℤ)) ≤ 3 := by
          rw [Work.ConvR.vsz_int]
          have h := isz_nat_le 1
          omega
        have h4 : 4 ≤ (p + 4) ^ 2 := by
          calc (4 : ℕ) ≤ p + 4 := by omega
            _ ≤ (p + 4) * (p + 4) := Nat.le_mul_self _
            _ = (p + 4) ^ 2 := by ring_nf
        omega
      exact Nat.mul_le_mul_left _ hv
  -- stage 2: swap the unit below the list
  have s2 : Work.ConvR.WordC main (rollP 1)
      (fun vs => vs = HvdH.Val.int (1 : ℤ) :: HvdH.ofList (ss.map (fun t : ℕ => HvdH.Val.int (t : ℤ))) :: rest)
      (fun _ out => out = HvdH.ofList (ss.map (fun t : ℕ => HvdH.Val.int (t : ℤ))) :: HvdH.Val.int (1 : ℤ) :: rest)
      (Kr * (2 * ((ss.length + 2) * (p + 4) + 1))) := by
    refine hK.conseq main (rollP 1) (fun vs => 1 < vs.length)
      (fun vs => vs = HvdH.Val.int (1 : ℤ) :: HvdH.ofList (ss.map (fun t : ℕ => HvdH.Val.int (t : ℤ))) :: rest)
      (fun vs out => out = vs.getD 1 .nil :: vs.eraseIdx 1)
      (fun _ out => out = HvdH.ofList (ss.map (fun t : ℕ => HvdH.Val.int (t : ℤ))) :: HvdH.Val.int (1 : ℤ) :: rest)
      (fun vs => Kr * (1 + 1) * (((vs.take 2).map HvdH.vsz).sum + 1))
      (fun _ => Kr * (2 * ((ss.length + 2) * (p + 4) + 1)))
      (hroll main 1) ?_ ?_ ?_
    · intro vs hvs; rw [hvs]; simp
    · intro vs out hvs hout
      rw [hvs] at hout
      rw [hout]
      rfl
    · intro vs hvs
      rw [hvs]
      have h1 : HvdH.vsz (HvdH.Val.int (1 : ℤ)) ≤ p + 4 := by
        have h : HvdH.vsz (HvdH.Val.int (1 : ℤ)) ≤ 3 := by
          rw [Work.ConvR.vsz_int]
          have h := isz_nat_le 1
          omega
        omega
      have h2 : HvdH.vsz (HvdH.ofList (ss.map (fun t : ℕ => HvdH.Val.int (t : ℤ)))) ≤ (ss.length + 1) * (p + 4) :=
        vsz_intList_le' ss p hlt
      have htake : ((List.take 2 (HvdH.Val.int (1 : ℤ) :: HvdH.ofList (ss.map (fun t : ℕ => HvdH.Val.int (t : ℤ))) :: rest)).map
            HvdH.vsz).sum = HvdH.vsz (HvdH.Val.int (1 : ℤ)) + HvdH.vsz (HvdH.ofList (ss.map (fun t : ℕ => HvdH.Val.int (t : ℤ)))) := by
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        ring_nf
      rw [htake]
      have hstep : HvdH.vsz (HvdH.Val.int (1 : ℤ)) + HvdH.vsz (HvdH.ofList (ss.map (fun t : ℕ => HvdH.Val.int (t : ℤ)))) + 1
          ≤ (ss.length + 2) * (p + 4) + 1 := by
        have e : (ss.length + 2) * (p + 4) = (p + 4) + (ss.length + 1) * (p + 4) := by ring
        rw [e]; omega
      calc Kr * 2 * (HvdH.vsz (HvdH.Val.int (1 : ℤ)) + HvdH.vsz (HvdH.ofList (ss.map (fun t : ℕ => HvdH.Val.int (t : ℤ)))) + 1)
          = Kr * (2 * (HvdH.vsz (HvdH.Val.int (1 : ℤ)) + HvdH.vsz (HvdH.ofList (ss.map (fun t : ℕ => HvdH.Val.int (t : ℤ)))) + 1)) := by ring
        _ ≤ Kr * (2 * ((ss.length + 2) * (p + 4) + 1)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 hstep)
  -- stage 3: the fold
  have s3 : Work.ConvR.WordC main (foldC mulP)
      (fun vs => vs = HvdH.ofList (ss.map (fun t : ℕ => HvdH.Val.int (t : ℤ))) :: HvdH.Val.int (1 : ℤ) :: rest)
      (fun _ out => out = HvdH.Val.int ((ss.prod : ℕ) : ℤ) :: rest)
      (ss.length * (Kmul * (p + 3) ^ 2 + Kfold * (p + 4)) + Kfold) := by
    have hstep : ∀ (i : ℕ) (acc : List HvdH.Val),
        i < (ss.map (fun t : ℕ => HvdH.Val.int (t : ℤ))).length →
        acc = HvdH.Val.int (((ss.take i).prod : ℕ) : ℤ) :: rest →
        HvdH.WordR main mulP
          (fun vs => vs = (ss.map (fun t : ℕ => HvdH.Val.int (t : ℤ))).getD i .nil :: acc)
          (fun _ out => out = HvdH.Val.int (((ss.take (i + 1)).prod : ℕ) : ℤ) :: rest)
          (fun _ => Kmul * (p + 3) ^ 2) := by
      intro i acc hi hacc
      have hi' : i < ss.length := by rw [List.length_map] at hi; exact hi
      have hget : (ss.map (fun t : ℕ => HvdH.Val.int (t : ℤ))).getD i HvdH.Val.nil
          = HvdH.Val.int ((ss.getD i 0 : ℕ) : ℤ) := by
        rw [Work.Transform.getD_default (ss.map (fun t : ℕ => HvdH.Val.int (t : ℤ)))
              (by rw [List.length_map]; exact hi') HvdH.Val.nil (HvdH.Val.int ((0 : ℕ) : ℤ))]
        exact List.getD_map ss (0 : ℕ) (fun t : ℕ => HvdH.Val.int (t : ℤ))
      refine hK.conseq main mulP
        (fun vs => ∃ (a b : ℤ) (r : List HvdH.Val), vs = .int a :: .int b :: r ∧ True)
        (fun vs => vs = (ss.map (fun t : ℕ => HvdH.Val.int (t : ℤ))).getD i .nil :: acc)
        (fun vs out => ∃ (a b : ℤ) (r : List HvdH.Val),
          vs = .int a :: .int b :: r ∧ out = .int (a * b) :: r)
        (fun _ out => out = HvdH.Val.int (((ss.take (i + 1)).prod : ℕ) : ℤ) :: rest)
        (HvdH.binCost (fun a b => Kmul * HvdH.isz a * HvdH.isz b))
        (fun _ => Kmul * (p + 3) ^ 2) (hmul main) ?_ ?_ ?_
      · intro vs hvs
        exact ⟨((ss.getD i 0 : ℕ) : ℤ), (((ss.take i).prod : ℕ) : ℤ), rest,
          by rw [hvs, hget, hacc], trivial⟩
      · intro vs out hvs hq
        rw [hvs] at hq
        obtain ⟨a, b, r, hvs', hout⟩ := hq
        have heq : HvdH.Val.int ((ss.getD i 0 : ℕ) : ℤ) ::
              HvdH.Val.int (((ss.take i).prod : ℕ) : ℤ) :: rest
            = HvdH.Val.int a :: HvdH.Val.int b :: r := by rw [← hget, ← hacc]; exact hvs'
        have ha : a = ((ss.getD i 0 : ℕ) : ℤ) := by
          have h : HvdH.Val.int ((ss.getD i 0 : ℕ) : ℤ) = HvdH.Val.int a :=
            congrArg (fun (l : List HvdH.Val) => l.getD 0 .nil) heq
          rw [HvdH.Val.int.injEq] at h
          exact h.symm
        have hb : b = (((ss.take i).prod : ℕ) : ℤ) := by
          have h : HvdH.Val.int (((ss.take i).prod : ℕ) : ℤ) = HvdH.Val.int b :=
            congrArg (fun (l : List HvdH.Val) => l.getD 1 .nil) heq
          rw [HvdH.Val.int.injEq] at h
          exact h.symm
        have hr : r = rest :=
          (congrArg (fun (l : List HvdH.Val) => l.drop 2) heq).symm
        rw [hout, hr]
        have hP : ((ss.take (i + 1)).prod : ℕ) = ss.getD i 0 * (ss.take i).prod := by
          have hp := List.prod_take_succ ss i hi'
          rw [← List.getD_eq_getElem ss 0 hi'] at hp
          rw [hp]; ring
        have hcast2 : (((ss.take (i + 1)).prod : ℕ) : ℤ)
            = (((ss.getD i 0 : ℕ)) : ℤ) * ((((ss.take i).prod : ℕ)) : ℤ) := by
          rw [hP]; push_cast; ring
        rw [hcast2, ← ha, ← hb]
      · intro vs hvs
        rw [hvs, hget, hacc]
        have hb1 : HvdH.isz (((ss.getD i 0 : ℕ)) : ℤ) ≤ p + 3 := by
          refine Work.ConvR.isz_le_of_natAbs_le ?_
          rw [Int.natAbs_natCast]
          exact le_of_lt (hlt _ (by
            rw [List.getD_eq_getElem _ _ hi']
            exact List.getElem_mem hi'))
        have hb2 : HvdH.isz ((((ss.take i).prod : ℕ)) : ℤ) ≤ p + 3 := by
          refine Work.ConvR.isz_le_of_natAbs_le ?_
          rw [Int.natAbs_natCast]
          exact le_of_lt (hPlt i (le_of_lt hi'))
        show Kmul * HvdH.isz (((ss.getD i 0 : ℕ)) : ℤ) * HvdH.isz ((((ss.take i).prod : ℕ)) : ℤ)
            ≤ Kmul * (p + 3) ^ 2
        calc Kmul * HvdH.isz (((ss.getD i 0 : ℕ)) : ℤ) * HvdH.isz ((((ss.take i).prod : ℕ)) : ℤ)
            ≤ Kmul * (p + 3) * (p + 3) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hb1) hb2
          _ = Kmul * (p + 3) ^ 2 := by ring
    have hsz : ∀ x ∈ (ss.map (fun t : ℕ => HvdH.Val.int (t : ℤ))), HvdH.vsz x ≤ p + 3 := by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      rw [Work.ConvR.vsz_int]
      exact hisz t ht
    have hf := hfold main mulP (ss.map (fun t : ℕ => HvdH.Val.int (t : ℤ)))
      (fun i acc => acc = HvdH.Val.int (((ss.take i).prod : ℕ) : ℤ) :: rest)
      (Kmul * (p + 3) ^ 2) (p + 3) hsz hstep
    refine hK.conseq main (foldC mulP) _ _ _ _ _ _ hf ?_ ?_ ?_
    · intro vs hvs
      refine ⟨HvdH.Val.int (1 : ℤ) :: rest, ?_, ?_⟩
      · rw [hvs]
      · have h0 : ((ss.take 0).prod : ℕ) = 1 := by simp
        rw [h0]
        rfl
    · intro vs out hvs hq
      rw [List.length_map] at hq
      rw [hq]
      congr 2
      rw [List.take_length]
    · intro vs _
      show (ss.map (fun t : ℕ => HvdH.Val.int (t : ℤ))).length *
          (Kmul * (p + 3) ^ 2 + Kfold * ((p + 3) + 1)) + Kfold
          ≤ ss.length * (Kmul * (p + 3) ^ 2 + Kfold * (p + 4)) + Kfold
      rw [List.length_map]
  -- compose
  have h12 := Work.ConvR.WordC.seq hK s1 s2 (fun vs mid hvs hq => hq)
  have hall := Work.ConvR.WordC.seq hK h12 s3 (fun vs mid hvs hq => hq.elim (fun m2 hm => hm.2))
  refine Work.ConvR.WordC.conseq hK hall (fun vs hvs => hvs) ?_ ?_
  · rintro vs out hvs ⟨mid, hm, ho⟩
    exact ho
  · exact costBound3 Kpv Kr Kfold Kmul ss.length p

end Work.MainP

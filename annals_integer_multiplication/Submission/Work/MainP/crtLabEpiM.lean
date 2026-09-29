import Mathlib
import Submission.Work.MainP.crtLabDefs
import Submission.Work.MainP.crtLabEpi
import Submission.Work.MainP.crtLabSum
import Submission.Work.MainP.crtMath
import Submission.Work.Kernel.Raw
import Submission.Work.Layout.Base
import Submission.Work.MainP.epiLabelList
import Submission.Work.MainP.epiXhBound
import Submission.Work.MainP.epiBodyWord
import Submission.Work.MainP.epiCostArith

/-!
# `crtLabEpiM`: extracting the CRT labels from the accumulator

`Work.MainP.crtLabWord` assembles the word computing `intList (sigmaList ss)` from `int S :: intList ss`
out of three phases; the last one is the *epilogue* formalised here: the accumulator
`acc ss S` (a nested value whose head is the pair `(vlab ss (S-1), Est ss S)` and whose tail is the
history `Xh ss S`) has to be turned into `intList (sigmaList ss)`.

## The algorithm

Recall (`Submission/Work/MainP/crtLabDefs.lean`)

* `prp v E = cons (int v) (ofList E)` — a pair `(label, state)`,
* `Xh ss i` — the history after `i` steps: `prp (vlab ss (i-2)) (Est ss (i-1)) :: … :: [prp (vlab ss 0) (Est ss 0)]`,
* `acc ss i = cons (prp (vlab ss (i-1)) (Est ss i)) (ofList (Xh ss i))`, so that
  `acc ss i = ofList (prp (vlab ss (i-1)) (Est ss i) :: Xh ss i)`.

Hence `acc ss S = ofList xs` with `xs = p₀ :: Xh ss S`, and the list of *keys* of `xs` is

  `[vlab ss (S-1), vlab ss (S-2), …, vlab ss 0, vlab ss 0]`

(the last `vlab ss 0` comes from the truncated subtraction `S-2-(S-1) = 0` in `Xh`).  The epilogue

1. maps `fun p => int (pairKey p)` over the list `xs` (`KernelLib.mapList` with the body
   `unconsV ;; swap ;; drop`, i.e. split the pair, push the payload below the key and drop it);
2. reverses the resulting list (`LayoutLib.reverse`), giving
   `[vlab 0, vlab 0, vlab 1, …, vlab (S-1)]`;
3. drops one entry (`pushVal (int 1) ;; LayoutLib.drop 1`) to get `(List.range S).map (vlab ss ·)`,
   which is `intList (sigmaList ss)`.

Step 1 is where the cost lives: the list has `S+1` entries of size `O((ss.length+1)(S.size+2))`, so
the extraction costs `O(S · (ss.length+1) · (S.size+2))`; the reversal and the drop cost
`O((S+1)(S.size+2) + …)`, and everything fits the target bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.MainP

open HvdH

/-! ## Auxiliary statements (delegated separately; replaced by imports on completion) -/

theorem epiCostArithX (Ku Ks Kd Km Kr Kp Kdl S d sz : ℕ) (hS : 1 ≤ S) :
    (S + 1) * ((Ku + Ks * ((3*d+4)*(sz+2) + 4*d + 6) + Kd * (((3*d+4)*(sz+2) + 4*d + 6) + 1))
        + Km * (((3*d+4)*(sz+2) + 4*d + 6) + 1)) + Km
      + Kr * (((S+1)*(sz+2) + (S+1) + 1) + 1)
      + Kp * 4 + Kdl * (((S+1)*(sz+2) + (S+1) + 1) + 4)
      ≤ 1000 * (Ku + Ks + Kd + Km + Kr + Kp + Kdl + 1) * (S * (d + 1) * (sz + 2) + 1) :=
  epiCostArith Ku Ks Kd Km Kr Kp Kdl S d sz hS

/-! ## Plumbing -/

/-- Re-bind a `WordR` whose pre/post are existential in the ambient tail to a fixed tail. -/
theorem epiWrdFix {main p : Cmd} {L0 L1 : List Val} {C0 c : ℕ}
    (h : WordR main p (fun vs => ∃ r, vs = L0 ++ r)
      (fun vs out => ∃ r, vs = L0 ++ r ∧ out = L1 ++ r) (fun _ => C0))
    (hc : C0 ≤ c) :
    ∀ rest, WordR main p (fun vs => vs = L0 ++ rest) (fun _ out => out = L1 ++ rest)
      (fun _ => c) := by
  intro rest
  refine Work.Kernel.WordR_conseq h (fun vs hvs => ⟨rest, hvs⟩) ?_ (fun vs _ => hc)
  intro vs out hvs hq
  obtain ⟨r, h1, h2⟩ := hq
  rw [hvs] at h1
  have h3 : r = rest := (List.append_cancel_left h1).symm
  subst h3
  exact h2

/-- Compose two steps whose intermediate stack is *exactly* `M`. -/
theorem epiSeq (hK : KernelLib) {main : Cmd} {p q : Cmd} {L M N : List Val} {c c' : ℕ}
    (hp : WordR main p (fun vs => vs = L) (fun _ out => out = M) (fun _ => c))
    (hq : WordR main q (fun vs => vs = M) (fun _ out => out = N) (fun _ => c')) :
    WordR main (.seq p q) (fun vs => vs = L) (fun _ out => out = N) (fun _ => c + c') := by
  have h := hK.seq main p q (fun vs => vs = L) (fun _ out => out = M) (fun _ => c)
    (fun vs => vs = M) (fun _ out => out = N) (fun _ => c') (fun _ => c') hp hq
    (fun vs mid _ hM => ⟨hM, le_refl _⟩)
  refine hK.conseq main (.seq p q) (fun vs => vs = L) (fun vs => vs = L)
    (fun vs out => ∃ mid, mid = M ∧ out = N) (fun _ out => out = N)
    (fun _ => c + c') (fun _ => c + c') h (fun _ hh => hh) ?_ (fun _ _ => le_rfl)
  intro vs out _ hq'
  obtain ⟨mid, -, hout⟩ := hq'
  exact hout

/-- Turn a `WordR` with structural pre/post into one with exact states. -/
theorem epiLift (hK : KernelLib) {main : Cmd} {p : Cmd} {P : List Val → Prop}
    {Q : List Val → List Val → Prop} {C : List Val → ℕ} (h : WordR main p P Q C)
    {L M : List Val} {c : ℕ} (hP : P L) (hQ : ∀ out, Q L out → out = M) (hC : C L ≤ c) :
    WordR main p (fun vs => vs = L) (fun _ out => out = M) (fun _ => c) := by
  refine hK.conseq main p P (fun vs => vs = L) Q (fun _ out => out = M) C (fun _ => c) h ?_ ?_ ?_
  · intro vs hvs; rw [hvs]; exact hP
  · intro vs out hvs hq; rw [hvs] at hq; exact hQ out hq
  · intro vs hvs; rw [hvs]; exact hC

/-- A `Forall₂` with a functional relation is the pointwise map. -/
theorem epiForall₂ {xs ys : List Val} {f : Val → Val} {L : ℕ}
    (h : List.Forall₂ (fun x y => y = f x ∧ vsz y ≤ L) xs ys) : ys = xs.map f := by
  induction h with
  | nil => rfl
  | cons hx _ ih =>
      obtain ⟨hx1, -⟩ := hx
      rw [hx1, ih, List.map_cons]

/-! ## The epilogue word -/

theorem crtLabEpiM (hK : HvdH.KernelLib) (hL : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (ss : List ℕ) (S : ℕ) (rest : List HvdH.Val),
    (∀ s ∈ ss, 1 ≤ s) → S = ss.prod →
    HvdH.WordR main prog
      (fun vs => vs = Work.MainP.acc ss S :: rest)
      (fun vs out => vs = Work.MainP.acc ss S :: rest ∧
        out = HvdH.intList (Work.MainP.sigmaList ss) :: rest)
      (fun _ => K * (S * (ss.length + 1) * (S.size + 2) + 1)) := by
  obtain ⟨up, Ku, hU⟩ := hK.unconsV
  obtain ⟨sw, Ks, hSw⟩ := hK.swap
  obtain ⟨dp, Kd, hDp⟩ := hK.drop
  obtain ⟨ml, Km, hMl⟩ := hK.mapList
  obtain ⟨rv, Kr, hRv⟩ := hL.reverse
  obtain ⟨pv, Kp, hPv⟩ := hK.pushVal
  obtain ⟨dl, Kdl, hDl⟩ := hL.drop
  refine ⟨(ml (up.seq (sw.seq dp))).seq (rv.seq ((pv (.int 1)).seq dl)),
    1000 * (Ku + Ks + Kd + Km + Kr + Kp + Kdl + 1), ?_⟩
  intro main ss S rest hpos hS
  have hS1 : 1 ≤ S := by rw [hS]; exact List.one_le_prod (fun x hx => hpos x hx)
  set L : ℕ := (3 * ss.length + 4) * (S.size + 2) + 4 * ss.length + 6 with hLdef
  set cB : ℕ := Ku + Ks * L + Kd * (L + 1) with hcBdef
  set Vl : ℕ := (S + 1) * (S.size + 2) + (S + 1) + 1 with hVldef
  set p0 : Val := prp (vlab ss (S - 1)) (Est ss S) with hp0def
  set xs : List Val := p0 :: Xh ss S with hxsdef
  set fv : ℕ → Val := fun j => Val.int (vlab ss j) with hfvdef
  set Yv : ℕ → List Val := fun i => (Xh ss i).map (fun x => Val.int (pairKey x)) with hYvdef
  set lv : List Val := xs.map (fun x => Val.int (pairKey x)) with hlvdef
  -- the accumulator is the `ofList` of the list `xs`
  have hacc : ofList xs = acc ss S := rfl
  -- lengths
  have Xh_len : ∀ i : ℕ, (Xh ss i).length = i := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [Xh_succ, List.length_cons, ih]
  have hxslen : xs.length = S + 1 := by
    rw [hxsdef, List.length_cons, Xh_len]
  -- element bounds for the map
  have hmem : ∀ x ∈ xs, (∃ (v : ℤ) (E : List Val), x = prp v E ∧ vsz (Val.int v) ≤ S.size + 2) ∧
      vsz x ≤ L := by
    intro x hx
    have hx' : x ∈ prp (vlab ss (S - 1)) (Est ss S) :: Xh ss S := by
      rw [hxsdef, hp0def] at hx
      exact hx
    obtain ⟨h1, h2⟩ := epiXhBound ss S hpos hS x hx'
    exact ⟨h1, by rw [hLdef]; exact h2⟩
  -- sizes of the label list
  have hlv_size : ∀ y ∈ lv, vsz y ≤ S.size + 2 := by
    intro y hy
    rw [hlvdef] at hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    obtain ⟨⟨v, E, hxeq, hvsz⟩, -⟩ := hmem x hx
    rw [hxeq]
    simpa only [pairKey_prp] using hvsz
  have hsum : ((lv.map vsz).sum) ≤ lv.length * (S.size + 2) := by
    have h := List.sum_le_sum (l := lv) (f := fun y : Val => vsz y)
      (g := fun _ : Val => S.size + 2) (fun i hi => hlv_size i hi)
    rw [List.map_const', List.sum_const_nat] at h
    exact h
  have hVlb : vsz (ofList lv) ≤ Vl := by
    have h2 : lv.length = S + 1 := by rw [hlvdef, List.length_map, hxslen]
    have hsum' : ((lv.map vsz).sum) ≤ (S + 1) * (S.size + 2) := by
      simpa [h2] using hsum
    rw [vsz_ofList, hVldef, h2]
    omega
  -- the body of the `mapList`
  have hbody : ∀ x : Val, (∃ (v : ℤ) (E : List Val), x = prp v E ∧ vsz x ≤ L) →
      WordR main (up.seq (sw.seq dp)) (fun vs => vs = x :: rest)
        (fun _ out => ∃ y, out = y :: rest ∧ (y = Val.int (pairKey x) ∧ vsz y ≤ L) ∧ vsz y ≤ L)
        (fun _ => cB) := by
    intro x hx
    obtain ⟨v, E, rfl, hsz⟩ := hx
    have hb := epiBodyWord hK (hU main) (hSw main) (hDp main) rest v E hsz
    refine hK.conseq main (up.seq (sw.seq dp))
      (fun vs => vs = prp v E :: rest) (fun vs => vs = prp v E :: rest)
      (fun _ out => ∃ y, out = y :: rest ∧ y = Val.int v ∧ vsz y ≤ L)
      (fun _ out => ∃ y, out = y :: rest ∧ (y = Val.int (pairKey (prp v E)) ∧ vsz y ≤ L)
        ∧ vsz y ≤ L)
      (fun _ => Ku + Ks * L + Kd * (L + 1)) (fun _ => cB) hb
      (fun vs hvs => hvs) ?_ ?_
    · intro vs out hvs hq
      obtain ⟨y, hout, hy, hyL⟩ := hq
      subst hy
      exact ⟨Val.int v, hout, ⟨⟨by rw [pairKey_prp], hyL⟩, hyL⟩⟩
    · intro vs hvs
      rw [hcBdef]
  have hPx : ∀ x ∈ xs, (∃ (v : ℤ) (E : List Val), x = prp v E ∧ vsz x ≤ L) ∧ vsz x ≤ L := by
    intro x hx
    obtain ⟨h1, h2⟩ := hmem x hx
    obtain ⟨v, E, hxeq, -⟩ := h1
    exact ⟨⟨v, E, hxeq, h2⟩, h2⟩
  have hmap := hMl main (up.seq (sw.seq dp)) rest
    (fun x : Val => ∃ (v : ℤ) (E : List Val), x = prp v E ∧ vsz x ≤ L)
    (fun x y : Val => y = Val.int (pairKey x) ∧ vsz y ≤ L) cB L hbody xs hPx
  -- phase 1: extract the keys
  have hmapX : WordR main (ml (up.seq (sw.seq dp))) (fun vs => vs = ofList xs :: rest)
      (fun _ out => out = ofList lv :: rest)
      (fun _ => xs.length * (cB + Km * (L + 1)) + Km) := by
    refine hK.conseq main (ml (up.seq (sw.seq dp))) _ _ _ _ _ _ hmap (fun vs h => h)
      ?_ (fun _ _ => le_rfl)
    intro vs out hvs hq
    obtain ⟨ys, hout, hf2⟩ := hq
    rw [hout, epiForall₂ (f := fun x : Val => Val.int (pairKey x)) hf2, hlvdef]
  have h1 : WordR main (ml (up.seq (sw.seq dp))) (fun vs => vs = acc ss S :: rest)
      (fun _ out => out = ofList lv :: rest)
      (fun _ => (S + 1) * (cB + Km * (L + 1)) + Km) := by
    refine hK.conseq main (ml (up.seq (sw.seq dp)))
      (fun vs => vs = acc ss S :: rest) (fun vs => vs = ofList xs :: rest)
      (fun _ out => out = ofList lv :: rest) (fun _ out => out = ofList lv :: rest)
      (fun _ => xs.length * (cB + Km * (L + 1)) + Km)
      (fun _ => (S + 1) * (cB + Km * (L + 1)) + Km) hmapX ?_ (fun _ _ _ h => h) ?_
    · intro vs hvs
      rw [hvs, ← hacc]
    · intro vs _
      rw [hxslen]
  -- phase 2: reverse
  have h2 : ∀ rest' : List Val, WordR main rv (fun vs => vs = ofList lv :: rest')
      (fun _ out => out = ofList lv.reverse :: rest') (fun _ => Kr * (Vl + 1)) := by
    intro rest'
    refine epiWrdFix (L0 := [ofList lv]) (L1 := [ofList lv.reverse]) (hRv main lv) ?_ rest'
    exact Nat.mul_le_mul_left Kr (Nat.add_le_add_right hVlb 1)
  -- phase 3: push `int 1`
  have h3 : WordR main (pv (.int 1)) (fun vs => vs = ofList lv.reverse :: rest)
      (fun _ out => out = .int 1 :: ofList lv.reverse :: rest) (fun _ => Kp * 4) := by
    refine epiLift hK (hPv main (.int 1)) trivial (fun out hout => hout) ?_
    have h1 : vsz (Val.int (1 : ℤ)) + 1 = 4 := by
      have hcast : (1 : ℤ) = ((1 : ℕ) : ℤ) := rfl
      rw [hcast, vsz_intNat, iszN, Nat.size_one]
    exact Nat.mul_le_mul_left Kp (le_of_eq h1)
  -- phase 4: drop the leading entry
  have h4 : WordR main dl (fun vs => vs = .int 1 :: ofList lv.reverse :: rest)
      (fun _ out => out = ofList (lv.reverse.drop 1) :: rest) (fun _ => Kdl * (Vl + 4)) := by
    refine epiWrdFix (L0 := [.int 1, ofList lv.reverse]) (L1 := [ofList (lv.reverse.drop 1)])
      (hDl main 1 lv.reverse) ?_ rest
    have hrevsz : vsz (ofList lv.reverse) = vsz (ofList lv) := by
      rw [vsz_ofList, vsz_ofList, List.length_reverse, List.map_reverse, List.sum_reverse]
    have hisz : isz ((1 : ℕ) : ℤ) = 3 := by rw [isz_natCast, iszN, Nat.size_one]
    rw [hrevsz, hisz]
    exact Nat.mul_le_mul_left Kdl (by omega)
  -- the chain
  have h34 := epiSeq hK h3 h4
  have h234 := epiSeq hK (h2 rest) h34
  have h1234 := epiSeq hK h1 h234
  -- the final list identity
  have hlv_eq : lv = fv (S - 1) :: Yv S := by
    rw [hlvdef, hxsdef, List.map_cons, hp0def, hYvdef, hfvdef]
    simp only [pairKey_prp]
  have hYv0 : Yv 0 = [] := by
    simp only [hYvdef, Xh_zero, List.map_nil]
  have hYv : ∀ i : ℕ, Yv (i + 1) = fv (i - 1) :: Yv i := by
    intro i
    simp only [hYvdef, hfvdef]
    rw [Xh_succ, List.map_cons]
    simp only [pairKey_prp]
  have hfin : ofList ((List.range S).map fv) = intList (sigmaList ss) := by
    have hsig : sigmaList ss = (List.range S).map (crtIdx ss) := by
      rw [sigmaList, ← hS]
    have hlab : labVals (sigmaList ss) = (List.range S).map fv := by
      rw [labVals, hsig, List.map_map]
      apply List.map_congr_left
      intro j _
      simp only [Function.comp_apply, hfvdef, vlab]
    rw [← hlab, ← intList_eq_ofList]
  have hpost_eq : ofList (lv.reverse.drop 1) = intList (sigmaList ss) := by
    rw [hlv_eq, epiLabelList fv Yv hYv0 hYv S hS1, hfin]
  -- the cost
  have hcost : ((S + 1) * (cB + Km * (L + 1)) + Km)
      + (Kr * (Vl + 1) + (Kp * 4 + Kdl * (Vl + 4)))
      ≤ 1000 * (Ku + Ks + Kd + Km + Kr + Kp + Kdl + 1)
          * (S * (ss.length + 1) * (S.size + 2) + 1) := by
    have heq : ((S + 1) * (cB + Km * (L + 1)) + Km) + (Kr * (Vl + 1) + (Kp * 4 + Kdl * (Vl + 4)))
        = (S + 1) * (cB + Km * (L + 1)) + Km + Kr * (Vl + 1) + Kp * 4 + Kdl * (Vl + 4) := by
      ring
    rw [heq]
    have h := epiCostArithX Ku Ks Kd Km Kr Kp Kdl S ss.length S.size hS1
    rw [hcBdef, hLdef, hVldef]
    exact h
  refine hK.conseq main ((ml (up.seq (sw.seq dp))).seq (rv.seq ((pv (.int 1)).seq dl)))
    (fun vs => vs = acc ss S :: rest) (fun vs => vs = acc ss S :: rest)
    (fun _ out => out = ofList (lv.reverse.drop 1) :: rest)
    (fun vs out => vs = acc ss S :: rest ∧ out = intList (sigmaList ss) :: rest)
    (fun _ => ((S + 1) * (cB + Km * (L + 1)) + Km) + (Kr * (Vl + 1) + (Kp * 4 + Kdl * (Vl + 4))))
    (fun _ => 1000 * (Ku + Ks + Kd + Km + Kr + Kp + Kdl + 1)
      * (S * (ss.length + 1) * (S.size + 2) + 1))
    h1234 (fun vs hvs => hvs) ?_ (fun _ _ => hcost)
  intro vs out hvs hq
  exact ⟨hvs, by rw [hq, hpost_eq]⟩

end Work.MainP

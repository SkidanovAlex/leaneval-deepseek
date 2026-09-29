import Mathlib
import Submission.Work.MainP.crtLabDefs
import Submission.Work.MainP.crtLabUpd
import Submission.Work.MainP.crtLabSum
import Submission.Work.MainP.crtLabSetupAux
import Submission.Work.Kernel.Raw
import Submission.Work.Layout.mvVal_ev_full

/-!
# `crtLabLoop`: the main loop of the CRT label word

`Work.MainP.acc ss i = cons (prp (vlab ss (i-1)) (Est ss i)) (ofList (Xh ss i))` is the CRT
label state after `i` odometer steps (`Submission/Work/MainP/crtLabDefs.lean`).  This file proves
`Work.MainP.crtLabLoop`: from the driver list `drv S` (with `S = ss.prod`) on top of `acc ss 0`,
the word runs the odometer step `S` times and leaves `acc ss S`.

The loop is `KernelLib.foldList` over the driver list `drv S` (a list of `S` values, all `nil`):
its per-element body drops one `nil` and applies the one-step odometer word
`Work.MainP.crtLabStepW`, which turns `acc ss i` into `acc ss (i+1)`.  The per-round cost is bounded
by a constant multiple of `(ss.length + 1) * (S.size + 2)`, so the total is
`O (S * (ss.length + 1) * (S.size + 2))`, as required.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.MainP

open HvdH

/-! ## Bounds on the entries of the runtime state -/

/-- Every entry of `Est ss i` has nonnegative first component. -/
theorem entryC_nonneg {ss : List ℕ} {i : ℕ} {e : HvdH.Val} (he : e ∈ Est ss i) :
    0 ≤ entryC e := by
  obtain ⟨sp, -, rfl⟩ := List.mem_map.mp (mem_Est.mp he)
  exact Int.natCast_nonneg _

/-- Every entry of `Est ss i` has first component at most `S = ss.prod`. -/
theorem entryC_le_prod {ss : List ℕ} {S : ℕ} (hS : S = ss.prod) (hpos : ∀ s ∈ ss, 1 ≤ s)
    {i : ℕ} {e : HvdH.Val} (he : e ∈ Est ss i) : entryC e ≤ (S : ℤ) := by
  obtain ⟨sp, hsp, rfl⟩ := List.mem_map.mp (mem_Est.mp he)
  have h1 : 1 ≤ sp.1 := crtTab_1le_fst hpos hsp
  have hmod : i % sp.1 ≤ sp.1 := le_of_lt (Nat.mod_lt i (lt_of_lt_of_le Nat.zero_lt_one h1))
  have hmul : (i % sp.1) * sp.2 ≤ sp.1 * sp.2 := Nat.mul_le_mul_right _ hmod
  have hle : sp.1 * sp.2 ≤ ss.prod := crtTab_mul_le hpos hsp
  have hcast : (((i % sp.1) * sp.2 : ℕ) : ℤ) ≤ (S : ℤ) := by
    rw [hS]; exact_mod_cast le_trans hmul hle
  simpa only [entryC_triple] using hcast

/-- The label of any time fits in `S` (so its `isz` is `S.size + 2`). -/
theorem isz_vlab_le {ss : List ℕ} {S : ℕ} (hS : S = ss.prod) (hpos : ∀ s ∈ ss, 1 ≤ s) (i : ℕ) :
    HvdH.isz (vlab ss i) ≤ S.size + 2 := by
  have hlt : crtIdx ss i < ss.prod :=
    crtIdx_lt (fun s hs => lt_of_lt_of_le Nat.zero_lt_one (hpos s hs)) i
  rw [vlab, isz_natCast, iszN]
  exact Nat.add_le_add_right (Nat.size_le_size (by rw [hS]; exact le_of_lt hlt)) 2

/-- `ss.prod ≥ 1` when all elements are `≥ 1`. -/
theorem one_le_prod {ss : List ℕ} (hpos : ∀ s ∈ ss, 1 ≤ s) : 1 ≤ ss.prod :=
  List.one_le_prod (fun a ha => hpos a ha)

/-! ## The per-round cost bound -/

/-- The cost of one odometer step, bounded by a constant multiple of
`(ss.length + 1) * (S.size + 2)`. -/
theorem stepCost_bound {ss : List ℕ} {S : ℕ} (hS : S = ss.prod) (hpos : ∀ s ∈ ss, 1 ≤ s)
    (K : ℕ) (i : ℕ) :
    K * (((Est ss i).length + 1) * (S.size + (3 * (S.size + 2) + 3) + 1)
        + HvdH.vsz (HvdH.ofList (Est ss i)) + HvdH.isz (vlab ss (i - 1)) + 1)
      ≤ K * (11 * (ss.length + 1) * (S.size + 2) + (S.size + 2) + 2) := by
  obtain ⟨-, -, -, -, -, hvszE⟩ := crtLabSum (ss := ss) (S := S) hS hpos i
  have hiszv : HvdH.isz (vlab ss (i - 1)) ≤ S.size + 2 := isz_vlab_le hS hpos (i - 1)
  have hlen : (Est ss i).length = ss.length := Est_length ss i
  have hS1 : 1 ≤ S := by rw [hS]; exact one_le_prod hpos
  have hsz1 : 1 ≤ S.size := Nat.size_le_size hS1
  have hsz2 : 2 ≤ S.size + 2 := by omega
  have hkey : (ss.length + 1) * (S.size + (3 * (S.size + 2) + 3) + 1)
      + HvdH.vsz (HvdH.ofList (Est ss i)) + HvdH.isz (vlab ss (i - 1)) + 1
      ≤ 11 * (ss.length + 1) * (S.size + 2) + (S.size + 2) + 2 := by
    nlinarith [hvszE, hiszv, Nat.zero_le (ss.length + 1), Nat.zero_le (S.size + 2)]
  exact Nat.mul_le_mul_left K (by rw [hlen]; exact hkey)

/-! ## The one-step specification, as a hypothesis -/

/-- The statement of `Work.MainP.crtLabStepW`: one odometer step of the CRT label loop. -/
abbrev StepSpec : Prop :=
  ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : HvdH.Val) (X : List HvdH.Val)
      (v : ℤ) (E : List HvdH.Val) (L B : ℕ) (rest : List HvdH.Val),
    p = Work.MainP.prp v E →
    (∀ e ∈ E, ∃ (c P Q : ℤ), e = Work.MainP.triple c P Q) →
    (∀ e ∈ E, HvdH.vsz e ≤ L) →
    (∀ e ∈ E, 0 ≤ Work.MainP.entryC e) →
    (∀ e ∈ E, Work.MainP.entryC e ≤ (B : ℤ)) →
    ((E.map Work.MainP.entryC).sum ≤ (B : ℤ)) →
    HvdH.WordR main prog
      (fun vs => vs = HvdH.ofList (p :: X) :: rest)
      (fun vs out => vs = HvdH.ofList (p :: X) :: rest ∧
        out = HvdH.ofList (Work.MainP.prp ((E.map Work.MainP.entryC).sum)
              ((E.map Work.MainP.entryUpd).reverse) :: p :: X) :: rest)
      (fun _ => K * ((E.length + 1) * (B.size + L + 1) + HvdH.vsz (HvdH.ofList E) + HvdH.isz v + 1))

/-! ## The scratch-stack excursion used by the odometer step -/

/-- Move the top value `a` aside (to stack `7`, via the `Work.Layout` value mover), merge the next
two values with `KernelLib.consV`, move `a` back and `consV` again.  The cost is `O (vsz a)`: the
values `c`, `d` are only ever merged at the top, so the bound does not involve their sizes. -/
theorem shiftOut_word (hK : HvdH.KernelLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (a c d : HvdH.Val) (rest : List HvdH.Val),
      HvdH.WordR main prog (fun vs => vs = a :: c :: d :: rest)
        (fun _ out => out = HvdH.Val.cons a (HvdH.Val.cons c d) :: rest)
        (fun _ => K * (HvdH.vsz a + 1)) := by
  obtain ⟨consP, Kc, hconsV⟩ := hK.consV
  refine ⟨.seq (Work.Layout.mvVal 0 7 3 4) (.seq consP (.seq (Work.Layout.mvVal 7 0 3 4) consP)),
    32 + 2 * Kc, ?_⟩
  intro main a c d rest vs hvs s R hR
  subst hvs
  obtain ⟨s₁, N₁, hev₁, hn₁, hst₁0, hst₁7, hst₁3, hst₁4, hoth₁⟩ :=
    Work.Layout.mvVal_ev_full (main := main) (a := 0) (b := 7) (c := 3) (d := 4)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s.reg) (X := s.stk) (v := a) (A := HvdH.encs (c :: d :: rest) ++ R)
      (B := s.stk 7) (by rw [hR, Work.Kernel.encs_cons, List.append_assoc]) rfl
  obtain ⟨n₁, hev₁, hn₁'⟩ := hev₁
  obtain ⟨out₂, s₂, n₂, hpost₂, hev₂, hn₂, hstk₂, hoth₂⟩ :=
    hconsV main (c :: d :: rest) (by simp) s₁ R hst₁0
  obtain ⟨a₂, b₂, r₂, hvs₂, hout₂⟩ := hpost₂
  have hvs₂' : c = a₂ ∧ d :: rest = b₂ :: r₂ := by simpa using hvs₂
  obtain ⟨rfl, hvs₂'⟩ := hvs₂'
  have hvs₂'' : d = b₂ ∧ rest = r₂ := by simpa using hvs₂'
  obtain ⟨rfl, rfl⟩ := hvs₂''
  obtain ⟨s₃, N₃, hev₃, hn₃, hst₃7, hst₃0, hst₃3, hst₃4, hoth₃⟩ :=
    Work.Layout.mvVal_ev_full (main := main) (a := 7) (b := 0) (c := 3) (d := 4)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s₂.reg) (X := s₂.stk) (v := a) (A := s.stk 7)
      (B := HvdH.encs (HvdH.Val.cons c d :: rest) ++ R)
      (by rw [hoth₂ 7 (by decide), hst₁7]) (by rw [hstk₂, hout₂])
  obtain ⟨n₃, hev₃, hn₃'⟩ := hev₃
  obtain ⟨out₄, s₄, n₄, hpost₄, hev₄, hn₄, hstk₄, hoth₄⟩ :=
    hconsV main (a :: HvdH.Val.cons c d :: rest) (by simp) s₃ R
      (by rw [hst₃0]; simp only [Work.Kernel.encs_cons, List.append_assoc])
  obtain ⟨a₄, b₄, r₄, hvs₄, hout₄⟩ := hpost₄
  have hvs₄' : a = a₄ ∧ HvdH.Val.cons c d :: rest = b₄ :: r₄ := by simpa using hvs₄
  obtain ⟨rfl, hvs₄'⟩ := hvs₄'
  have hvs₄'' : HvdH.Val.cons c d = b₄ ∧ rest = r₄ := by simpa using hvs₄'
  obtain ⟨rfl, rfl⟩ := hvs₄''
  refine ⟨out₄, s₄, n₁ + (n₂ + (n₃ + n₄)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hout₄]
  · exact Eval.seq hev₁ (Eval.seq hev₂ (Eval.seq hev₃ hev₄))
  · have hv1 : 1 ≤ HvdH.vsz a + 1 := by omega
    have hk1 : Kc ≤ Kc * (HvdH.vsz a + 1) := by
      simpa using Nat.mul_le_mul_left Kc hv1
    have hk2 : 2 * Kc ≤ 2 * (Kc * (HvdH.vsz a + 1)) := by nlinarith [hk1]
    have h13 : n₁ + n₃ ≤ 32 * (HvdH.vsz a + 1) := by nlinarith [hn₁', hn₃', one_le_vsz a]
    nlinarith [h13, hn₂, hn₄, hk2]
  · rw [hstk₄, hout₄]
  · intro k hk
    by_cases h7 : k = 7
    · subst h7; rw [hoth₄ 7 hk, hst₃7]
    · by_cases h3 : k = 3
      · subst h3; rw [hoth₄ 3 hk, hst₃3, hoth₂ 3 (by decide), hst₁3]
      · by_cases h4 : k = 4
        · subst h4; rw [hoth₄ 4 hk, hst₃4, hoth₂ 4 (by decide), hst₁4]
        · rw [hoth₄ k hk, hoth₃ k h7 hk h3 h4, hoth₂ k hk, hoth₁ k hk h7 h3 h4]


/-! ## Arithmetic of `isz` -/

/-- `size` is subadditive. -/
theorem size_add_le (m n : ℕ) : (m + n).size ≤ m.size + n.size := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  have hm1 : 1 ≤ m := by omega
  have hn1 : 1 ≤ n := by omega
  have hmn : 2 ^ m.size + 2 ^ n.size ≤ 2 ^ m.size * 2 ^ n.size := by
    refine add_le_mul ?_ ?_
    · have h1 : 1 ≤ m.size := Nat.size_pos.mpr hm1
      have h2 : 2 ^ 1 ≤ 2 ^ m.size := Nat.pow_le_pow_right (by norm_num : 0 < 2) h1
      simpa using h2
    · have h1 : 1 ≤ n.size := Nat.size_pos.mpr hn1
      have h2 : 2 ^ 1 ≤ 2 ^ n.size := Nat.pow_le_pow_right (by norm_num : 0 < 2) h1
      simpa using h2
  have hlt : m + n < 2 ^ m.size * 2 ^ n.size :=
    lt_of_lt_of_le (Nat.add_lt_add (Nat.lt_size_self m) (Nat.lt_size_self n)) hmn
  rw [← Nat.pow_add] at hlt
  exact Nat.size_le.mpr hlt

/-- `isz` is subadditive. -/
theorem isz_add_le (a b : ℤ) : isz (a + b) ≤ isz a + isz b := by
  have h : (a + b).natAbs ≤ a.natAbs + b.natAbs := Int.natAbs_add_le a b
  have h1 : (a + b).natAbs.size ≤ (a.natAbs + b.natAbs).size := Nat.size_le_size h
  have h2 : (a.natAbs + b.natAbs).size ≤ a.natAbs.size + b.natAbs.size := size_add_le _ _
  simp only [isz]
  omega

/-- `isz` is at least `2`. -/
theorem two_le_isz (z : ℤ) : 2 ≤ isz z := by
  simp only [isz]
  omega

/-- The size of the 2-element prefix, as a sum. -/
theorem take2_sum (a b : Val) (tl : List Val) :
    (((a :: b :: tl).take (1 + 1)).map vsz).sum + 1 = vsz a + vsz b + 1 := by
  simp [List.take_succ_cons]

/-- The size of the 3-element prefix, as a sum. -/
theorem take3_sum (a b c : Val) (tl : List Val) :
    (((a :: b :: c :: tl).take (2 + 1)).map vsz).sum + 1 = vsz a + vsz b + vsz c + 1 := by
  simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  ring

/-- Cost of `pick 1` on a two-element prefix. -/
theorem pick2_cost (K0 : ℕ) (a b : Val) (tl : List Val) :
    K0 * (1 + 1) * ((((a :: b :: tl).take (1 + 1)).map vsz).sum + 1)
      ≤ (2 * K0) * (vsz a + vsz b + 1) := by
  rw [take2_sum]; nlinarith

/-- Cost of `roll 1` on a two-element prefix. -/
theorem roll2_cost (K0 : ℕ) (a b : Val) (tl : List Val) :
    K0 * (1 + 1) * ((((a :: b :: tl).take (1 + 1)).map vsz).sum + 1)
      ≤ (2 * K0) * (vsz a + vsz b + 1) := by
  rw [take2_sum]; nlinarith

/-- Cost of `roll 2` on a three-element prefix. -/
theorem roll3_cost (K0 : ℕ) (a b c : Val) (tl : List Val) :
    K0 * (2 + 1) * ((((a :: b :: c :: tl).take (2 + 1)).map vsz).sum + 1)
      ≤ (3 * K0) * (vsz a + vsz b + vsz c + 1) := by
  rw [take3_sum]; nlinarith

/-! ## Exact-stack steps for the library fields -/

/-- `KernelLib.unconsV` as an exact-stack step. -/
theorem step_unconsV {main up : Cmd} {K0 : ℕ}
    (h : WordR main up (fun vs => ∃ a b rest, vs = Val.cons a b :: rest)
      (fun vs out => ∃ a b rest, vs = Val.cons a b :: rest ∧ out = a :: b :: rest)
      (fun _ => K0))
    (a b : Val) (tl : List Val) (c : ℕ) (hc : K0 ≤ c) :
    WordR main up (fun vs => vs = Val.cons a b :: tl) (fun _ out => out = a :: b :: tl)
      (fun _ => c) := by
  refine wordR_lift h ⟨a, b, tl, rfl⟩ ?_ hc
  intro out hq
  obtain ⟨a', b', rest, hv, hout⟩ := hq
  simp only [List.cons.injEq] at hv
  obtain ⟨hv1, hv2⟩ := hv
  simp only [Val.cons.injEq] at hv1
  obtain ⟨rfl, rfl⟩ := hv1
  subst hv2
  exact hout

/-- `KernelLib.dup` as an exact-stack step. -/
theorem step_dup {main up : Cmd} {K0 : ℕ}
    (h : WordR main up (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
      (fun vs => K0 * (vsz (vs.headD .nil) + 1)))
    (a : Val) (tl : List Val) (c : ℕ) (hc : K0 * (vsz a + 1) ≤ c) :
    WordR main up (fun vs => vs = a :: tl) (fun _ out => out = a :: a :: tl) (fun _ => c) := by
  refine wordR_lift h (by intro hh; cases hh) ?_ ?_
  · intro out hq
    obtain ⟨v, rest, hv, hout⟩ := hq
    simp only [List.cons.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    exact hout
  · simpa using hc

/-- `KernelLib.pick` as an exact-stack step (copy the `k`-th value to the top). -/
theorem step_pick {main : Cmd} {prog : ℕ → Cmd} {K0 : ℕ}
    (h : ∀ k : ℕ, WordR main (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => K0 * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (k : ℕ) (L : List Val) (hk : k < L.length) (c : ℕ)
    (hc : K0 * (k + 1) * (((L.take (k + 1)).map vsz).sum + 1) ≤ c) :
    WordR main (prog k) (fun vs => vs = L) (fun _ out => out = L.getD k .nil :: L)
      (fun _ => c) :=
  wordR_lift (h k) hk (fun _ hq => hq) hc

/-- `KernelLib.pushVal` as an exact-stack step. -/
theorem step_pushVal' {main : Cmd} {prog : Val → Cmd} {K0 : ℕ}
    (h : ∀ v : Val, WordR main (prog v) (fun _ => True) (fun vs out => out = v :: vs)
      (fun _ => K0 * (vsz v + 1)))
    (v : Val) (L : List Val) (c : ℕ) (hc : K0 * (vsz v + 1) ≤ c) :
    WordR main (prog v) (fun vs => vs = L) (fun _ out => out = v :: L) (fun _ => c) :=
  wordR_lift (h v) trivial (fun _ hq => hq) hc

/-- `IntLib.add` as an exact-stack step. -/
theorem step_add {main p : Cmd} {K0 : ℕ}
    (h : BinOp main p (fun _ _ => True) (· + ·) (fun a b => K0 * (isz a + isz b)))
    (a b : ℤ) (tl : List Val) (c : ℕ) (hc : K0 * (isz a + isz b) ≤ c) :
    WordR main p (fun vs => vs = Val.int a :: Val.int b :: tl)
      (fun _ out => out = Val.int (a + b) :: tl) (fun _ => c) := by
  refine wordR_lift h ⟨a, b, tl, rfl, trivial⟩ ?_ ?_
  · intro out hq
    obtain ⟨a', b', rest, hv, hout⟩ := hq
    simp only [List.cons.injEq, Val.int.injEq] at hv
    obtain ⟨rfl, rfl, rfl⟩ := hv
    exact hout
  · simpa [BinOp, binCost] using hc

/-- `IntLib.eq` as an exact-stack step. -/
theorem step_eq {main p : Cmd} {K0 : ℕ}
    (h : BinOp main p (fun _ _ => True) (fun a b => if a = b then 1 else 0)
      (fun a b => K0 * (isz a + isz b)))
    (a b : ℤ) (tl : List Val) (c : ℕ) (hc : K0 * (isz a + isz b) ≤ c) :
    WordR main p (fun vs => vs = Val.int a :: Val.int b :: tl)
      (fun _ out => out = Val.int (if a = b then 1 else 0) :: tl) (fun _ => c) := by
  refine wordR_lift h ⟨a, b, tl, rfl, trivial⟩ ?_ ?_
  · intro out hq
    obtain ⟨a', b', rest, hv, hout⟩ := hq
    simp only [List.cons.injEq, Val.int.injEq] at hv
    obtain ⟨rfl, rfl, rfl⟩ := hv
    exact hout
  · simpa [BinOp, binCost] using hc

/-! ## The per-entry programs of the odometer step -/

/-- The program of the sum pass (one entry). -/
def sumProgBody (unP ro1P drP adP : Cmd) : Cmd := .seq unP (.seq ro1P (.seq drP adP))

/-- One entry of the sum pass: `triple c P Q :: int s :: tl ↦ int (c + s) :: tl`. -/
theorem sumProg_spec (hK : HvdH.KernelLib) (hI : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (c P Q s : ℤ) (tl : List HvdH.Val),
      HvdH.WordR main prog (fun vs => vs = triple c P Q :: Val.int s :: tl)
        (fun _ out => out = Val.int (c + s) :: tl)
        (fun _ => K * (isz c + isz P + isz Q + isz s + 1)) := by
  obtain ⟨unP, Ku, hun⟩ := hK.unconsV
  obtain ⟨roP, Kr, hro⟩ := hK.roll
  obtain ⟨drP, Kd, hdr⟩ := hK.drop
  obtain ⟨adP, Ka, had⟩ := hI.add
  refine ⟨sumProgBody unP (roP 1) drP adP, Ku + (6 * Kr + (2 * Kd + Ka)), ?_⟩
  intro main c P Q s tl
  set tc : ℕ := isz c + isz P + isz Q + isz s + 1 with htc'
  have htc1 : 1 ≤ tc := by omega
  have h1 : WordR main unP (fun vs => vs = triple c P Q :: Val.int s :: tl)
      (fun _ out => out = Val.int c :: Val.cons (Val.int P) (Val.int Q) :: Val.int s :: tl)
      (fun _ => Ku * tc) := by
    refine step_unconsV (h := hun main) (Val.int c) (Val.cons (Val.int P) (Val.int Q))
      (Val.int s :: tl) (Ku * tc) ?_
    exact le_trans (le_of_eq (Nat.mul_one Ku).symm) (Nat.mul_le_mul_left Ku htc1)
  have h2 : WordR main (roP 1)
      (fun vs => vs = Val.int c :: Val.cons (Val.int P) (Val.int Q) :: Val.int s :: tl)
      (fun _ out => out = Val.cons (Val.int P) (Val.int Q) :: Val.int c :: Val.int s :: tl)
      (fun _ => 6 * Kr * tc) := by
    refine step_roll (h := hro main) 1
      (Val.int c :: Val.cons (Val.int P) (Val.int Q) :: Val.int s :: tl) (by simp)
      (6 * Kr * tc) ?_
    refine le_trans (roll2_cost Kr (Val.int c) (Val.cons (Val.int P) (Val.int Q))
      (Val.int s :: tl)) ?_
    have hST : vsz (Val.int c) + vsz (Val.cons (Val.int P) (Val.int Q)) + 1 ≤ 3 * tc := by
      rw [htc']
      simp only [vsz_int, vsz_cons]
      omega
    calc (2 * Kr) * (vsz (Val.int c) + vsz (Val.cons (Val.int P) (Val.int Q)) + 1)
        ≤ (2 * Kr) * (3 * tc) := Nat.mul_le_mul_left _ hST
      _ = 6 * Kr * tc := by ring
  have h3 : WordR main drP
      (fun vs => vs = Val.cons (Val.int P) (Val.int Q) :: Val.int c :: Val.int s :: tl)
      (fun _ out => out = Val.int c :: Val.int s :: tl) (fun _ => 2 * Kd * tc) := by
    refine step_drop (h := hdr main) (Val.cons (Val.int P) (Val.int Q))
      (Val.int c :: Val.int s :: tl) (2 * Kd * tc) ?_
    have hST : vsz (Val.cons (Val.int P) (Val.int Q)) + 1 ≤ 2 * tc := by
      rw [htc']
      simp only [vsz_cons, vsz_int]
      omega
    calc Kd * (vsz (Val.cons (Val.int P) (Val.int Q)) + 1) ≤ Kd * (2 * tc) :=
          Nat.mul_le_mul_left Kd hST
      _ = 2 * Kd * tc := by ring
  have h4 : WordR main adP (fun vs => vs = Val.int c :: Val.int s :: tl)
      (fun _ out => out = Val.int (c + s) :: tl) (fun _ => Ka * tc) := by
    refine step_add (h := had main) c s tl (Ka * tc) ?_
    refine Nat.mul_le_mul_left Ka ?_
    rw [htc']
    omega
  have hchain := wordR_seqC hK h1 (wordR_seqC hK h2 (wordR_seqC hK h3 h4))
  refine hK.conseq (main := main) (p := sumProgBody unP (roP 1) drP adP)
    (P := fun vs => vs = triple c P Q :: Val.int s :: tl)
    (P' := fun vs => vs = triple c P Q :: Val.int s :: tl)
    (Q := fun _ out => out = Val.int (c + s) :: tl)
    (Q' := fun _ out => out = Val.int (c + s) :: tl)
    (C := fun _ => Ku * tc + (6 * Kr * tc + (2 * Kd * tc + (Ka * tc))))
    (C' := fun _ => (Ku + (6 * Kr + (2 * Kd + Ka))) * tc)
    hchain (fun _ h => h) (fun _ _ _ h => h) (fun _ _ => le_of_eq (by ring))

/-- The program of the rebuild pass (one entry). -/
def updProgBody (unP pk1P ro2P adP dpP eqP ifP cnP : Cmd) : Cmd :=
  .seq unP (.seq pk1P (.seq unP (.seq ro2P (.seq adP (.seq dpP
    (.seq ro2P (.seq eqP (.seq ifP cnP))))))))

/-- One entry of the rebuild pass: `triple c P Q` is updated in place (`c ↦ c + P`, wrapping to
`0` at `Q`), i.e. replaced by `entryUpd (triple c P Q)`. -/
theorem updProg_spec (hK : HvdH.KernelLib) (hI : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (c P Q : ℤ) (tl : List HvdH.Val),
      HvdH.WordR main prog (fun vs => vs = triple c P Q :: tl)
        (fun _ out => out = triple (if c + P = Q then 0 else c + P) P Q :: tl)
        (fun _ => K * (isz c + isz P + isz Q + 1)) := by
  obtain ⟨unP, Ku, hun⟩ := hK.unconsV
  obtain ⟨pkP, Kp, hpk⟩ := hK.pick
  obtain ⟨roP, Kr, hro⟩ := hK.roll
  obtain ⟨dpP, Kdp, hdp⟩ := hK.dup
  obtain ⟨cnP, Kn, hcn⟩ := hK.consV
  obtain ⟨drP, Kd, hdr⟩ := hK.drop
  obtain ⟨pvP, Kpv, hpv⟩ := hK.pushVal
  obtain ⟨adP, Ka, had⟩ := hI.add
  obtain ⟨eqP, Ke, heq⟩ := hI.eq
  obtain ⟨ifP, Kiz, hif⟩ := hK.ifZero
  refine ⟨updProgBody unP (pkP 1) (roP 2) adP dpP eqP
    (ifP .skip (.seq drP (pvP (Val.int 0)))) cnP, Ku + (6 * Kp + (Ku + (3 * Kr + (Ka + (Kdp + (8 * Kr + (Ke + ((4 * Kiz + Kd + 3 * Kpv + 1) + Kn)))))))), ?_⟩
  intro main c P Q tl
  set tc : ℕ := isz c + isz P + isz Q + 1 with ht'
  have htc1 : 1 ≤ tc := by omega
  have hX : isz (c + P) ≤ isz c + isz P := isz_add_le c P
  have h1 : WordR main unP (fun vs => vs = triple c P Q :: tl)
      (fun _ out => out = Val.int c :: Val.cons (Val.int P) (Val.int Q) :: tl)
      (fun _ => Ku * tc) := by
    refine step_unconsV (h := hun main) (Val.int c) (Val.cons (Val.int P) (Val.int Q)) tl
      (Ku * tc) ?_
    exact le_trans (le_of_eq (Nat.mul_one Ku).symm) (Nat.mul_le_mul_left Ku htc1)
  have h2 : WordR main (pkP 1)
      (fun vs => vs = Val.int c :: Val.cons (Val.int P) (Val.int Q) :: tl)
      (fun _ out => out = Val.cons (Val.int P) (Val.int Q)
        :: Val.int c :: Val.cons (Val.int P) (Val.int Q) :: tl)
      (fun _ => 6 * Kp * tc) := by
    refine step_pick (h := hpk main) 1 (Val.int c :: Val.cons (Val.int P) (Val.int Q) :: tl)
      (by simp) (6 * Kp * tc) ?_
    refine le_trans (pick2_cost Kp (Val.int c) (Val.cons (Val.int P) (Val.int Q)) tl) ?_
    have hST : vsz (Val.int c) + vsz (Val.cons (Val.int P) (Val.int Q)) + 1 ≤ 3 * tc := by
      rw [ht']
      simp only [vsz_int, vsz_cons]
      omega
    calc (2 * Kp) * (vsz (Val.int c) + vsz (Val.cons (Val.int P) (Val.int Q)) + 1)
        ≤ (2 * Kp) * (3 * tc) := Nat.mul_le_mul_left _ hST
      _ = 6 * Kp * tc := by ring
  have h3 : WordR main unP
      (fun vs => vs = Val.cons (Val.int P) (Val.int Q)
        :: Val.int c :: Val.cons (Val.int P) (Val.int Q) :: tl)
      (fun _ out => out = Val.int P :: Val.int Q :: Val.int c
        :: Val.cons (Val.int P) (Val.int Q) :: tl) (fun _ => Ku * tc) := by
    refine step_unconsV (h := hun main) (Val.int P) (Val.int Q)
      (Val.int c :: Val.cons (Val.int P) (Val.int Q) :: tl) (Ku * tc) ?_
    exact le_trans (le_of_eq (Nat.mul_one Ku).symm) (Nat.mul_le_mul_left Ku htc1)
  have h4 : WordR main (roP 2)
      (fun vs => vs = Val.int P :: Val.int Q :: Val.int c
        :: Val.cons (Val.int P) (Val.int Q) :: tl)
      (fun _ out => out = Val.int c :: Val.int P :: Val.int Q
        :: Val.cons (Val.int P) (Val.int Q) :: tl) (fun _ => 3 * Kr * tc) := by
    refine step_roll (h := hro main) 2 (Val.int P :: Val.int Q :: Val.int c
      :: Val.cons (Val.int P) (Val.int Q) :: tl) (by simp) (3 * Kr * tc) ?_
    refine le_trans (roll3_cost Kr (Val.int P) (Val.int Q) (Val.int c)
      (Val.cons (Val.int P) (Val.int Q) :: tl)) ?_
    have hST : vsz (Val.int P) + vsz (Val.int Q) + vsz (Val.int c) + 1 ≤ tc := by
      rw [ht']
      simp only [vsz_int, vsz_cons]
      omega
    calc (3 * Kr) * (vsz (Val.int P) + vsz (Val.int Q) + vsz (Val.int c) + 1)
        ≤ (3 * Kr) * tc := Nat.mul_le_mul_left _ hST
      _ = 3 * Kr * tc := by ring
  have h5 : WordR main adP
      (fun vs => vs = Val.int c :: Val.int P :: Val.int Q
        :: Val.cons (Val.int P) (Val.int Q) :: tl)
      (fun _ out => out = Val.int (c + P) :: Val.int Q
        :: Val.cons (Val.int P) (Val.int Q) :: tl) (fun _ => Ka * tc) := by
    refine step_add (h := had main) c P (Val.int Q :: Val.cons (Val.int P) (Val.int Q) :: tl)
      (Ka * tc) ?_
    refine Nat.mul_le_mul_left Ka ?_
    rw [ht']
    omega
  have h6 : WordR main dpP
      (fun vs => vs = Val.int (c + P) :: Val.int Q :: Val.cons (Val.int P) (Val.int Q) :: tl)
      (fun _ out => out = Val.int (c + P) :: Val.int (c + P) :: Val.int Q
        :: Val.cons (Val.int P) (Val.int Q) :: tl) (fun _ => Kdp * tc) := by
    refine step_dup (h := hdp main) (Val.int (c + P))
      (Val.int Q :: Val.cons (Val.int P) (Val.int Q) :: tl) (Kdp * tc) ?_
    refine Nat.mul_le_mul_left Kdp ?_
    rw [ht']
    simp only [vsz_int]
    omega
  have h7 : WordR main (roP 2)
      (fun vs => vs = Val.int (c + P) :: Val.int (c + P) :: Val.int Q
        :: Val.cons (Val.int P) (Val.int Q) :: tl)
      (fun _ out => out = Val.int Q :: Val.int (c + P) :: Val.int (c + P)
        :: Val.cons (Val.int P) (Val.int Q) :: tl) (fun _ => 8 * Kr * tc) := by
    refine step_roll (h := hro main) 2 (Val.int (c + P) :: Val.int (c + P) :: Val.int Q
      :: Val.cons (Val.int P) (Val.int Q) :: tl) (by simp) (8 * Kr * tc) ?_
    refine le_trans (roll3_cost Kr (Val.int (c + P)) (Val.int (c + P)) (Val.int Q)
      (Val.cons (Val.int P) (Val.int Q) :: tl)) ?_
    have hST : vsz (Val.int (c + P)) + vsz (Val.int (c + P)) + vsz (Val.int Q) + 1 ≤ 2 * tc := by
      rw [ht']
      simp only [vsz_int]
      omega
    calc (3 * Kr) * (vsz (Val.int (c + P)) + vsz (Val.int (c + P)) + vsz (Val.int Q) + 1)
        ≤ (3 * Kr) * (2 * tc) := Nat.mul_le_mul_left _ hST
      _ = 6 * (Kr * tc) := by ring
      _ ≤ 8 * (Kr * tc) := Nat.mul_le_mul_right (Kr * tc) (by omega)
      _ = 8 * Kr * tc := by ring
  have h8 : WordR main eqP
      (fun vs => vs = Val.int Q :: Val.int (c + P) :: Val.int (c + P)
        :: Val.cons (Val.int P) (Val.int Q) :: tl)
      (fun _ out => out = Val.int (if Q = c + P then 1 else 0) :: Val.int (c + P)
        :: Val.cons (Val.int P) (Val.int Q) :: tl) (fun _ => Ke * tc) := by
    refine step_eq (h := heq main) Q (c + P)
      (Val.int (c + P) :: Val.cons (Val.int P) (Val.int Q) :: tl) (Ke * tc) ?_
    refine Nat.mul_le_mul_left Ke ?_
    rw [ht']
    omega
  have hbr : WordR main (.seq drP (pvP (Val.int 0)))
      (fun vs => vs = Val.int (c + P) :: Val.cons (Val.int P) (Val.int Q) :: tl)
      (fun _ out => out = Val.int 0 :: Val.cons (Val.int P) (Val.int Q) :: tl)
      (fun _ => Kd * (isz (c + P) + 1) + 3 * Kpv) := by
    refine wordR_seqC hK (step_drop (h := hdr main) (Val.int (c + P))
      (Val.cons (Val.int P) (Val.int Q) :: tl) (Kd * (isz (c + P) + 1)) (by rw [vsz_int]))
      (step_pushVal' (h := hpv main) (Val.int 0) (Val.cons (Val.int P) (Val.int Q) :: tl)
        (3 * Kpv) ?_)
    simp only [vsz_int, HvdH.isz, Int.natAbs_zero, Nat.size_zero]
    rw [Nat.mul_comm Kpv 3]
  have hskip : WordR main .skip
      (fun vs => vs = Val.int (c + P) :: Val.cons (Val.int P) (Val.int Q) :: tl)
      (fun _ out => out = Val.int (c + P) :: Val.cons (Val.int P) (Val.int Q) :: tl)
      (fun _ => 1) :=
    wordR_lift (hK.skip main) trivial (fun _ hq => hq) le_rfl
  have h9 := hif main .skip (.seq drP (pvP (Val.int 0)))
    (if Q = c + P then 1 else 0) (Val.int (c + P) :: Val.cons (Val.int P) (Val.int Q) :: tl)
    (fun out => out = Val.int (c + P) :: Val.cons (Val.int P) (Val.int Q) :: tl)
    (fun out => out = Val.int 0 :: Val.cons (Val.int P) (Val.int Q) :: tl)
    1 (Kd * (isz (c + P) + 1) + 3 * Kpv)
    (fun _ => hskip) (fun _ => hbr)
  have h9' : WordR main (ifP .skip (.seq drP (pvP (Val.int 0))))
      (fun vs => vs = Val.int (if Q = c + P then 1 else 0) :: Val.int (c + P)
        :: Val.cons (Val.int P) (Val.int Q) :: tl)
      (fun _ out => out = Val.int (if c + P = Q then 0 else c + P)
        :: Val.cons (Val.int P) (Val.int Q) :: tl)
      (fun _ => (4 * Kiz + Kd + 3 * Kpv + 1) * tc) := by
    refine hK.conseq (main := main) (p := ifP .skip (.seq drP (pvP (Val.int 0))))
      (P := fun vs => vs = Val.int (if Q = c + P then 1 else 0) :: Val.int (c + P)
        :: Val.cons (Val.int P) (Val.int Q) :: tl)
      (P' := fun vs => vs = Val.int (if Q = c + P then 1 else 0) :: Val.int (c + P)
        :: Val.cons (Val.int P) (Val.int Q) :: tl)
      (Q := fun _ out => ((if Q = c + P then (1 : ℤ) else 0) = 0 →
          out = Val.int (c + P) :: Val.cons (Val.int P) (Val.int Q) :: tl) ∧
        ((if Q = c + P then (1 : ℤ) else 0) ≠ 0 →
          out = Val.int 0 :: Val.cons (Val.int P) (Val.int Q) :: tl))
      (Q' := fun _ out => out = Val.int (if c + P = Q then 0 else c + P)
        :: Val.cons (Val.int P) (Val.int Q) :: tl)
      (C := fun _ => Kiz * (isz (if Q = c + P then 1 else 0) + 1)
        + max 1 (Kd * (isz (c + P) + 1) + 3 * Kpv))
      (C' := fun _ => (4 * Kiz + Kd + 3 * Kpv + 1) * tc)
      h9 (fun _ h => h) (fun _ out _ hpost => by
        by_cases hq : c + P = Q
        · have hf : (if Q = c + P then (1 : ℤ) else 0) ≠ 0 := by
            rw [if_pos (by omega : Q = c + P)]
            norm_num
          rw [hpost.2 hf, if_pos hq]
        · have hf : (if Q = c + P then (1 : ℤ) else 0) = 0 := by
            rw [if_neg (by omega : ¬ Q = c + P)]
          rw [hpost.1 hf, if_neg hq])
      (fun _ _ => ?_)
    · have hf : isz (if Q = c + P then (1 : ℤ) else 0) ≤ 3 := by
        by_cases hq : Q = c + P
        · rw [if_pos hq]; simp only [isz]; norm_num
        · rw [if_neg hq]; simp only [isz]; norm_num
      have e1 : Kiz * (isz (if Q = c + P then (1 : ℤ) else 0) + 1) ≤ 4 * Kiz * tc := by
        have h4 : isz (if Q = c + P then (1 : ℤ) else 0) + 1 ≤ 4 * tc := by
          rw [ht']
          omega
        calc Kiz * (isz (if Q = c + P then (1 : ℤ) else 0) + 1) ≤ Kiz * (4 * tc) :=
              Nat.mul_le_mul_left Kiz h4
          _ = 4 * Kiz * tc := by ring
      have e2 : max 1 (Kd * (isz (c + P) + 1) + 3 * Kpv) ≤ Kd * tc + 3 * Kpv * tc + tc := by
        rw [max_le_iff]
        constructor
        · calc (1 : ℕ) = 1 * 1 := by ring
            _ ≤ 1 * tc := Nat.mul_le_mul_left 1 htc1
            _ ≤ Kd * tc + 3 * Kpv * tc + tc := by omega
        · have hd : Kd * (isz (c + P) + 1) ≤ Kd * tc := by
            refine Nat.mul_le_mul_left Kd ?_
            rw [ht']
            -- (no simplification needed)
            omega
          have hp : 3 * Kpv ≤ 3 * Kpv * tc :=
            le_trans (le_of_eq (Nat.mul_one (3 * Kpv)).symm) (Nat.mul_le_mul_left (3 * Kpv) htc1)
          calc Kd * (isz (c + P) + 1) + 3 * Kpv ≤ Kd * tc + 3 * Kpv * tc := Nat.add_le_add hd hp
            _ ≤ Kd * tc + 3 * Kpv * tc + tc := Nat.le_add_right _ _
      calc Kiz * (isz (if Q = c + P then (1 : ℤ) else 0) + 1)
            + max 1 (Kd * (isz (c + P) + 1) + 3 * Kpv)
          ≤ 4 * Kiz * tc + (Kd * tc + 3 * Kpv * tc + tc) := Nat.add_le_add e1 e2
        _ = (4 * Kiz + Kd + 3 * Kpv + 1) * tc := by ring
  have h10 : WordR main cnP
      (fun vs => vs = Val.int (if c + P = Q then 0 else c + P)
        :: Val.cons (Val.int P) (Val.int Q) :: tl)
      (fun _ out => out = triple (if c + P = Q then 0 else c + P) P Q :: tl)
      (fun _ => Kn * tc) := by
    refine step_consV (h := hcn main) (Val.int (if c + P = Q then 0 else c + P))
      (Val.cons (Val.int P) (Val.int Q)) tl (Kn * tc) ?_
    simpa using Nat.mul_le_mul_left Kn htc1
  have hchain := wordR_seqC hK h1 (wordR_seqC hK h2 (wordR_seqC hK h3 (wordR_seqC hK h4
    (wordR_seqC hK h5 (wordR_seqC hK h6 (wordR_seqC hK h7 (wordR_seqC hK h8
      (wordR_seqC hK h9' h10))))))))
  refine hK.conseq (main := main)
    (p := updProgBody unP (pkP 1) (roP 2) adP dpP eqP
      (ifP .skip (.seq drP (pvP (Val.int 0)))) cnP)
    (P := fun vs => vs = triple c P Q :: tl) (P' := fun vs => vs = triple c P Q :: tl)
    (Q := fun _ out => out = triple (if c + P = Q then 0 else c + P) P Q :: tl)
    (Q' := fun _ out => out = triple (if c + P = Q then 0 else c + P) P Q :: tl)
    (C := fun _ => Ku * tc + (6 * Kp * tc + (Ku * tc + (3 * Kr * tc + (Ka * tc + (Kdp * tc + (8 * Kr * tc + (Ke * tc + ((4 * Kiz + Kd + 3 * Kpv + 1) * tc + (Kn * tc))))))))))
    (C' := fun _ => (Ku + (6 * Kp + (Ku + (3 * Kr + (Ka + (Kdp + (8 * Kr + (Ke + ((4 * Kiz + Kd + 3 * Kpv + 1) + Kn))))))))) * tc)
    hchain (fun _ h => h) (fun _ _ _ h => h) (fun _ _ => le_of_eq (by ring))

/-! ## The odometer step -/

/-- Splitting the last element off a `take`. -/
theorem take_succ_eq {α : Type} (l : List α) {i : ℕ} (h : i < l.length) :
    l.take (i + 1) = l.take i ++ [l[i]] :=
  List.take_succ_eq_append_getElem h

/-- An updated entry is at most twice as big as the original. -/
theorem vsz_entryUpd_le (c P Q : ℤ) :
    vsz (entryUpd (triple c P Q)) ≤ 2 * vsz (triple c P Q) + 2 := by
  rw [entryUpd_triple, vsz_triple, vsz_triple]
  by_cases h : c + P = Q
  · rw [if_pos h]
    have h0 : isz (0 : ℤ) = 2 := by simp only [isz, Int.natAbs_zero, Nat.size_zero]
    rw [h0]
    omega
  · rw [if_neg h]
    have h1 : isz (c + P) ≤ isz c + isz P := isz_add_le c P
    omega

/-! ### Elementary list bounds -/

/-- A mapped list's sum is at most `length * bound`. -/
theorem sum_map_le_mul {α : Type} (l : List α) (g : α → ℕ) (b : ℕ)
    (h : ∀ x ∈ l, g x ≤ b) : (l.map g).sum ≤ l.length * b := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hx : g x ≤ b := h x (by simp)
    have hl : (l.map g).sum ≤ l.length * b := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

/-- A `take`-sum is at most the full sum, when all the entries are nonnegative. -/
theorem sum_take_le_map {α : Type} (l : List α) (f : α → ℤ) (hf : ∀ x ∈ l, 0 ≤ f x) (i : ℕ) :
    ((l.take i).map f).sum ≤ (l.map f).sum :=
  List.Sublist.sum_le_sum ((List.take_sublist i l).map f) (fun y hy => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact hf x hx)

/-- The `vsz` of a reversed mapped list. -/
theorem vsz_ofList_reverse_map_le {E : List Val} {f : Val → Val} {L' : ℕ}
    (h : ∀ e ∈ E, vsz (f e) ≤ L') :
    vsz (ofList ((E.map f).reverse)) ≤ (E.length + 1) * (L' + 1) := by
  rw [vsz_ofList, List.length_reverse, List.length_map]
  have hsum : (((E.map f).reverse).map vsz).sum ≤ E.length * L' := by
    rw [List.map_reverse, List.sum_reverse, List.map_map]
    exact sum_map_le_mul E (fun e => vsz (f e)) L' h
  have h1 : (((E.map f).reverse).map vsz).sum + E.length + 1
      ≤ E.length * L' + E.length + 1 :=
    Nat.add_le_add_right (Nat.add_le_add_right hsum E.length) 1
  refine le_trans h1 ?_
  have h3 : E.length * L' + E.length + 1 ≤ E.length * L' + E.length + (L' + 1) :=
    Nat.add_le_add_left (by omega) _
  calc E.length * L' + E.length + 1
      ≤ E.length * L' + E.length + (L' + 1) := h3
    _ = (E.length + 1) * (L' + 1) := by ring

/-- `take`-ing the whole length is the identity. -/
theorem take_length_rev_map {α β : Type} (E : List α) (f : α → β) :
    ((E.map f).take E.length).reverse = (E.map f).reverse := by
  induction E with
  | nil => simp
  | cons a E ih =>
    rw [List.map_cons, List.length_cons, List.take_succ_cons, List.reverse_cons, List.reverse_cons,
      ih]

/-! ### The cost denominator of one step -/

/-- The denominator `N` of the cost of one odometer step. -/
def blkN (E : List Val) (B L : ℕ) (v : ℤ) : ℕ :=
  (E.length + 1) * (B.size + L + 1) + vsz (ofList E) + isz v + 1

/-- The length of a list is at most the sum of the `vsz` of its entries. -/
theorem length_le_sum_vsz (E : List Val) : E.length ≤ (E.map vsz).sum := by
  induction E with
  | nil => simp
  | cons e E ih =>
    have h1 : 1 ≤ vsz e := one_le_vsz e
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    calc E.length + 1 ≤ (E.map vsz).sum + 1 := Nat.add_le_add_right ih 1
      _ = 1 + (E.map vsz).sum := by ring
      _ ≤ vsz e + (E.map vsz).sum := Nat.add_le_add_right h1 _

theorem one_le_blkN (E : List Val) (B L : ℕ) (v : ℤ) : 1 ≤ blkN E B L v := by
  change 1 ≤ (E.length + 1) * (B.size + L + 1) + vsz (ofList E) + isz v + 1
  omega

theorem two_le_blkN (E : List Val) (B L : ℕ) (v : ℤ) : 2 ≤ blkN E B L v := by
  change 2 ≤ (E.length + 1) * (B.size + L + 1) + vsz (ofList E) + isz v + 1
  have h1 : 1 ≤ vsz (ofList E) := one_le_vsz _
  have h2 : 2 ≤ isz v := two_le_isz v
  omega

theorem le_blkN_A (E : List Val) (B L : ℕ) (v : ℤ) :
    (E.length + 1) * (B.size + L + 1) ≤ blkN E B L v := by
  change (E.length + 1) * (B.size + L + 1)
    ≤ (E.length + 1) * (B.size + L + 1) + vsz (ofList E) + isz v + 1
  omega

theorem vsz_ofList_le_blkN (E : List Val) (B L : ℕ) (v : ℤ) :
    vsz (ofList E) ≤ blkN E B L v := by
  change vsz (ofList E) ≤ (E.length + 1) * (B.size + L + 1) + vsz (ofList E) + isz v + 1
  omega

theorem isz_le_blkN (E : List Val) (B L : ℕ) (v : ℤ) : isz v ≤ blkN E B L v := by
  change isz v ≤ (E.length + 1) * (B.size + L + 1) + vsz (ofList E) + isz v + 1
  omega

theorem le_blkN_L (E : List Val) (B L : ℕ) (v : ℤ) : L ≤ blkN E B L v := by
  change L ≤ (E.length + 1) * (B.size + L + 1) + vsz (ofList E) + isz v + 1
  have h : L ≤ (E.length + 1) * (B.size + L + 1) := by
    calc L = 1 * L := by ring
      _ ≤ (E.length + 1) * (B.size + L + 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem le_blkN_Bsize (E : List Val) (B L : ℕ) (v : ℤ) : B.size ≤ blkN E B L v := by
  change B.size ≤ (E.length + 1) * (B.size + L + 1) + vsz (ofList E) + isz v + 1
  have h : B.size ≤ (E.length + 1) * (B.size + L + 1) := by
    calc B.size = 1 * B.size := by ring
      _ ≤ (E.length + 1) * (B.size + L + 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem le_blkN_Elength (E : List Val) (B L : ℕ) (v : ℤ) : E.length ≤ blkN E B L v := by
  change E.length ≤ (E.length + 1) * (B.size + L + 1) + vsz (ofList E) + isz v + 1
  rw [vsz_ofList]
  have hlv : E.length ≤ (E.map vsz).sum := length_le_sum_vsz E
  omega

theorem le_blkN_E1L (E : List Val) (B L : ℕ) (v : ℤ) :
    (E.length + 1) * (L + 1) ≤ blkN E B L v := by
  change (E.length + 1) * (L + 1)
    ≤ (E.length + 1) * (B.size + L + 1) + vsz (ofList E) + isz v + 1
  have h : (E.length + 1) * (L + 1) ≤ (E.length + 1) * (B.size + L + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

theorem le_blkN_EL (E : List Val) (B L : ℕ) (v : ℤ) : E.length * (L + 1) ≤ blkN E B L v :=
  le_trans (Nat.mul_le_mul_right _ (by omega)) (le_blkN_E1L E B L v)

theorem vsz_prp_le_blkN (E : List Val) (B L : ℕ) (v : ℤ) :
    vsz (prp v E) ≤ 2 * blkN E B L v := by
  change vsz (prp v E) ≤ 2 * ((E.length + 1) * (B.size + L + 1) + vsz (ofList E) + isz v + 1)
  rw [prp, vsz_cons, vsz_int, vsz_ofList]
  omega

theorem vsz_ofList_reverse_map_le_blkN {E : List Val} {f : Val → Val} (B L : ℕ) (v : ℤ)
    (h : ∀ e ∈ E, vsz (f e) ≤ 2 * L + 2) :
    vsz (ofList ((E.map f).reverse)) ≤ 3 * blkN E B L v := by
  refine le_trans (vsz_ofList_reverse_map_le (E := E) (f := f) (L' := 2 * L + 2) h) ?_
  have h1 : (E.length + 1) * (2 * L + 2 + 1)
      = 2 * ((E.length + 1) * (L + 1)) + (E.length + 1) := by ring
  have h2 : 2 * ((E.length + 1) * (L + 1)) ≤ 2 * blkN E B L v :=
    Nat.mul_le_mul_left 2 (le_blkN_E1L E B L v)
  have h3 : E.length + 1 ≤ blkN E B L v := by
    calc E.length + 1 = (E.length + 1) * 1 := by ring
      _ ≤ (E.length + 1) * (L + 1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ blkN E B L v := le_blkN_E1L E B L v
  calc (E.length + 1) * (2 * L + 2 + 1)
      = 2 * ((E.length + 1) * (L + 1)) + (E.length + 1) := h1
    _ ≤ 2 * blkN E B L v + blkN E B L v := Nat.add_le_add h2 h3
    _ = 3 * blkN E B L v := by ring

theorem isz_sum_entryC_le_blkN {E : List Val} {B : ℕ} (L : ℕ) (v : ℤ)
    (h0 : ∀ e ∈ E, 0 ≤ entryC e) (hBsum : (E.map entryC).sum ≤ (B : ℤ)) :
    isz (E.map entryC).sum ≤ 3 * blkN E B L v := by
  set s : ℤ := (E.map entryC).sum with hs
  have h0s : 0 ≤ s := by
    rw [hs]
    exact List.sum_nonneg (fun x hx => by
      obtain ⟨e, he, hfe⟩ := List.mem_map.mp hx
      rw [← hfe]
      exact h0 e he)
  have hsum_le : s ≤ (B : ℤ) := by rw [hs]; exact hBsum
  have hnat : s.natAbs ≤ B := by
    have hcast : ((s.natAbs : ℕ) : ℤ) ≤ (B : ℤ) := by
      rw [Int.natAbs_of_nonneg h0s]
      exact hsum_le
    exact_mod_cast hcast
  have hsize : s.natAbs.size ≤ B.size := Nat.size_le_size hnat
  have hB : B.size ≤ blkN E B L v := le_blkN_Bsize E B L v
  have h2 : 2 ≤ blkN E B L v := two_le_blkN E B L v
  simp only [isz]
  omega

theorem vsz_prp_sum_le_blkN {E : List Val} {B L : ℕ} (v : ℤ)
    (h0 : ∀ e ∈ E, 0 ≤ entryC e) (hBsum : (E.map entryC).sum ≤ (B : ℤ))
    (hLp : ∀ e ∈ E, vsz (entryUpd e) ≤ 2 * L + 2) :
    vsz (prp ((E.map entryC).sum) ((E.map entryUpd).reverse)) ≤ 8 * blkN E B L v := by
  have h1 : isz (E.map entryC).sum ≤ 3 * blkN E B L v := isz_sum_entryC_le_blkN L v h0 hBsum
  have h2 : vsz (ofList ((E.map entryUpd).reverse)) ≤ 3 * blkN E B L v :=
    vsz_ofList_reverse_map_le_blkN B L v hLp
  have h3 : 1 ≤ blkN E B L v := one_le_blkN E B L v
  rw [prp, vsz_cons, vsz_int]
  omega

/-- The odometer step (`StepSpec` of `crtLabLoop_of`). -/
theorem crtLabStepV (hK : HvdH.KernelLib) (hI : HvdH.IntLib) : StepSpec := by
  obtain ⟨unP, Ku, hun⟩ := hK.unconsV
  obtain ⟨dpP, Kdp, hdp⟩ := hK.dup
  obtain ⟨drP, Kd, hdr⟩ := hK.drop
  obtain ⟨pvP, Kpv, hpv⟩ := hK.pushVal
  obtain ⟨roP, Kr, hro⟩ := hK.roll
  obtain ⟨cnP, Kn, hcn⟩ := hK.consV
  obtain ⟨swP, Ks, hsw⟩ := hK.swap
  obtain ⟨sumP, Ksm, hsumP⟩ := sumProg_spec hK hI
  obtain ⟨updP, Kup, hupdP⟩ := updProg_spec hK hI
  obtain ⟨shiftP, Ksh, hshift⟩ := shiftOut_word hK
  obtain ⟨comb, Kf, hfold⟩ := hK.foldList
  let KK : ℕ := 2 * Ku + 4 * Kdp + 2 * Ku + 4 * Kd + 4 * Kdp + 4 * Kpv + 6 * Kr
    + (3 * Ksm + 2 * Kf) + 3 * Kpv + 24 * Kr + (Kup + Kn + 2 * Kf) + 8 * Ks + 2 * Kn + 12 * Ksh
  refine ⟨.seq unP (.seq dpP (.seq unP (.seq drP (.seq dpP (.seq (pvP (Val.int 0))
    (.seq (roP 1) (.seq (comb sumP) (.seq (pvP Val.nil) (.seq (roP 2)
      (.seq (comb (.seq updP cnP)) (.seq swP (.seq cnP shiftP)))))))))))), KK, ?_⟩
  intro main p X v E L B rest hp htri hL h0 hB hBsum
  set N : ℕ := blkN E B L v with hN
  have hN1 : 1 ≤ N := by rw [hN]; exact one_le_blkN E B L v
  have hN2 : 2 ≤ N := by rw [hN]; exact two_le_blkN E B L v
  have hNV : vsz (ofList E) ≤ N := by rw [hN]; exact vsz_ofList_le_blkN E B L v
  have hNA : isz v ≤ N := by rw [hN]; exact isz_le_blkN E B L v
  have hNL : L ≤ N := by rw [hN]; exact le_blkN_L E B L v
  have hNSz : B.size ≤ N := by rw [hN]; exact le_blkN_Bsize E B L v
  have hND : E.length ≤ N := by rw [hN]; exact le_blkN_Elength E B L v
  have hNA1 : (E.length + 1) * (B.size + L + 1) ≤ N := by rw [hN]; exact le_blkN_A E B L v
  have hNE1L : (E.length + 1) * (L + 1) ≤ N := by rw [hN]; exact le_blkN_E1L E B L v
  have hNEL : E.length * (L + 1) ≤ N := by rw [hN]; exact le_blkN_EL E B L v
  have hvz0 : vsz (Val.int 0) = 2 := by
    rw [vsz_int]
    simp only [isz, Int.natAbs_zero, Nat.size_zero]
  have hvnil : vsz (Val.nil : Val) = 1 := rfl
  have hLp : ∀ e ∈ E, vsz (entryUpd e) ≤ 2 * L + 2 := by
    intro e he
    obtain ⟨c, P, Q, rfl⟩ := htri e he
    refine le_trans (vsz_entryUpd_le c P Q) ?_
    have h2 := hL (triple c P Q) he
    omega
  have hVp : vsz p ≤ 2 * N := by
    rw [hp, hN]
    exact vsz_prp_le_blkN E B L v
  have hVE' : vsz (ofList ((E.map entryUpd).reverse)) ≤ 3 * N := by
    rw [hN]
    exact vsz_ofList_reverse_map_le_blkN B L v hLp
  have hNsig : isz (E.map entryC).sum ≤ 3 * N := by
    rw [hN]
    exact isz_sum_entryC_le_blkN L v h0 hBsum
  have hVprp : vsz (prp ((E.map entryC).sum) ((E.map entryUpd).reverse)) ≤ 8 * N := by
    rw [hN]
    exact vsz_prp_sum_le_blkN v h0 hBsum hLp
  set cSum : ℕ := Ksm * (L + B.size + 3) with hcSum
  set cReb : ℕ := Kup * (L + 1) + Kn with hcReb
  -- phase 1: split the input value `p` into `int v` and `ofList E`
  have h1 : WordR main unP (fun vs => vs = ofList (p :: X) :: rest)
      (fun _ out => out = p :: ofList X :: rest) (fun _ => 2 * Ku * N) := by
    refine step_unconsV (h := hun main) p (ofList X) rest (2 * Ku * N) ?_
    calc Ku ≤ Ku * N := le_trans (le_of_eq (Nat.mul_one Ku).symm) (Nat.mul_le_mul_left Ku hN1)
      _ ≤ 2 * Ku * N := Nat.mul_le_mul_right N (by omega)
  -- phase 2: duplicate the pair
  have h2 : WordR main dpP (fun vs => vs = p :: ofList X :: rest)
      (fun _ out => out = p :: p :: ofList X :: rest) (fun _ => 4 * Kdp * N) := by
    refine step_dup (h := hdp main) p (ofList X :: rest) (4 * Kdp * N) ?_
    calc Kdp * (vsz p + 1) ≤ Kdp * (4 * N) := Nat.mul_le_mul_left Kdp (by omega)
      _ = 4 * Kdp * N := by ring
  -- phase 3: uncons the copy
  have h3 : WordR main unP (fun vs => vs = p :: p :: ofList X :: rest)
      (fun _ out => out = Val.int v :: ofList E :: p :: ofList X :: rest)
      (fun _ => 2 * Ku * N) := by
    have h0' : WordR main unP (fun vs => vs = prp v E :: p :: ofList X :: rest)
        (fun _ out => out = Val.int v :: ofList E :: p :: ofList X :: rest)
        (fun _ => 2 * Ku * N) := by
      refine step_unconsV (h := hun main) (Val.int v) (ofList E) (p :: ofList X :: rest)
        (2 * Ku * N) ?_
      calc Ku ≤ Ku * N := le_trans (le_of_eq (Nat.mul_one Ku).symm) (Nat.mul_le_mul_left Ku hN1)
        _ ≤ 2 * Ku * N := Nat.mul_le_mul_right N (by omega)
    refine hK.conseq (main := main) (p := unP)
      (P := fun vs => vs = prp v E :: p :: ofList X :: rest)
      (P' := fun vs => vs = p :: p :: ofList X :: rest)
      (Q := fun _ out => out = Val.int v :: ofList E :: p :: ofList X :: rest)
      (Q' := fun _ out => out = Val.int v :: ofList E :: p :: ofList X :: rest)
      (C := fun _ => 2 * Ku * N) (C' := fun _ => 2 * Ku * N)
      h0' (fun vs hvs => hvs.trans (by rw [hp])) (fun _ _ _ h => h) (fun _ _ => le_rfl)
  -- phase 4: drop the label `int v`
  have h4 : WordR main drP (fun vs => vs = Val.int v :: ofList E :: p :: ofList X :: rest)
      (fun _ out => out = ofList E :: p :: ofList X :: rest) (fun _ => 4 * Kd * N) := by
    refine step_drop (h := hdr main) (Val.int v) (ofList E :: p :: ofList X :: rest)
      (4 * Kd * N) ?_
    calc Kd * (vsz (Val.int v) + 1) = Kd * (isz v + 1) := by rw [vsz_int]
      _ ≤ Kd * (4 * N) := Nat.mul_le_mul_left Kd (by omega)
      _ = 4 * Kd * N := by ring
  -- phase 5: duplicate the entry list
  have h5 : WordR main dpP (fun vs => vs = ofList E :: p :: ofList X :: rest)
      (fun _ out => out = ofList E :: ofList E :: p :: ofList X :: rest)
      (fun _ => 4 * Kdp * N) := by
    refine step_dup (h := hdp main) (ofList E) (p :: ofList X :: rest) (4 * Kdp * N) ?_
    calc Kdp * (vsz (ofList E) + 1) ≤ Kdp * (4 * N) := Nat.mul_le_mul_left Kdp (by omega)
      _ = 4 * Kdp * N := by ring
  -- phase 6: push the initial partial sum `int 0`
  have h6 : WordR main (pvP (Val.int 0))
      (fun vs => vs = ofList E :: ofList E :: p :: ofList X :: rest)
      (fun _ out => out = Val.int 0 :: ofList E :: ofList E :: p :: ofList X :: rest)
      (fun _ => 4 * Kpv * N) := by
    refine step_pushVal' (h := hpv main) (Val.int 0)
      (ofList E :: ofList E :: p :: ofList X :: rest) (4 * Kpv * N) ?_
    calc Kpv * (vsz (Val.int 0) + 1) ≤ Kpv * 3 := Nat.mul_le_mul_left Kpv (by omega)
      _ ≤ Kpv * (4 * N) := Nat.mul_le_mul_left Kpv (by omega)
      _ = 4 * Kpv * N := by ring
  -- phase 7: roll the entry list above the partial sum
  have h7 : WordR main (roP 1)
      (fun vs => vs = Val.int 0 :: ofList E :: ofList E :: p :: ofList X :: rest)
      (fun _ out => out = ofList E :: Val.int 0 :: ofList E :: p :: ofList X :: rest)
      (fun _ => 6 * Kr * N) := by
    refine step_roll (h := hro main) 1
      (Val.int 0 :: ofList E :: ofList E :: p :: ofList X :: rest) (by simp) (6 * Kr * N) ?_
    calc Kr * (1 + 1) * (((List.take (1 + 1)
          (Val.int 0 :: ofList E :: ofList E :: p :: ofList X :: rest)).map vsz).sum + 1)
        = Kr * (1 + 1) * (vsz (Val.int 0) + vsz (ofList E) + 1) := by
          rw [take2_sum (Val.int 0) (ofList E) (ofList E :: p :: ofList X :: rest)]
      _ ≤ Kr * (1 + 1) * (3 * N) := Nat.mul_le_mul_left _ (by omega)
      _ = 6 * Kr * N := by ring
  -- phase 8: the sum pass
  have h8 : WordR main (comb sumP)
      (fun vs => vs = ofList E :: Val.int 0 :: ofList E :: p :: ofList X :: rest)
      (fun _ out => out = Val.int (E.map entryC).sum :: ofList E :: p :: ofList X :: rest)
      (fun _ => (3 * Ksm + 2 * Kf) * N) := by
    have hbody : ∀ i (accs : List Val), i < E.length →
        (∃ s : ℤ, accs = Val.int s :: ofList E :: p :: ofList X :: rest ∧
          s = (((E.take i).map entryC).reverse).sum) →
        WordR main sumP (fun vs => vs = E.getD i .nil :: accs)
          (fun _ out => ∃ s : ℤ, out = Val.int s :: ofList E :: p :: ofList X :: rest ∧
            s = (((E.take (i + 1)).map entryC).reverse).sum) (fun _ => cSum) := by
      intro i accs hi hI
      obtain ⟨s, haccs, hs⟩ := hI
      subst haccs
      have he : E.getD i .nil ∈ E := by
        rw [List.getD_eq_getElem _ _ hi]
        exact List.getElem_mem hi
      obtain ⟨c, P, Q, hPQ⟩ := htri (E.getD i .nil) he
      rw [hPQ] at he
      have hsum1 : (((E.take (i + 1)).map entryC).reverse).sum
          = c + (((E.take i).map entryC).reverse).sum := by
        have htake : (E.take (i + 1)).map entryC
            = (E.take i).map entryC ++ [entryC (E.getD i .nil)] := by
          rw [List.getD_eq_getElem _ _ hi, take_succ_eq E hi, List.map_append, List.map_cons,
            List.map_nil]
        have hA : (((E.take (i + 1)).map entryC).reverse).sum
            = entryC (E.getD i .nil) + (((E.take i).map entryC).reverse).sum := by
          rw [htake, List.reverse_append, List.reverse_singleton, List.singleton_append,
            List.sum_cons]
        have hB : entryC (E.getD i .nil) = c := by rw [hPQ]; rfl
        rw [hA, hB]
      refine hK.conseq (main := main) (p := sumP)
        (P := fun vs => vs = triple c P Q :: Val.int s :: ofList E :: p :: ofList X :: rest)
        (P' := fun vs => vs = E.getD i .nil :: Val.int s :: ofList E :: p :: ofList X :: rest)
        (Q := fun _ out => out = Val.int (c + s) :: ofList E :: p :: ofList X :: rest)
        (Q' := fun _ out => ∃ s' : ℤ, out = Val.int s' :: ofList E :: p :: ofList X :: rest ∧
          s' = (((E.take (i + 1)).map entryC).reverse).sum)
        (C := fun _ => Ksm * (isz c + isz P + isz Q + isz s + 1))
        (C' := fun _ => cSum)
        (hsumP main c P Q s (ofList E :: p :: ofList X :: rest))
        (fun vs hvs => hvs.trans (by rw [hPQ]))
        (fun _ out _ hout => ⟨c + s, by rw [hout], by rw [hsum1, hs]⟩)
        (fun _ _ => ?_)
      · have hsz : isz c + isz P + isz Q + 1 ≤ L := by
          have h1 : vsz (triple c P Q) = isz c + isz P + isz Q + 2 := vsz_triple c P Q
          have h2 := hL (triple c P Q) he
          rw [h1] at h2
          omega
        have hBs : isz s ≤ B.size + 2 := by
          have hsum_le : s ≤ (B : ℤ) := by
            rw [hs, List.sum_reverse]
            exact le_trans (sum_take_le_map E entryC h0 i) hBsum
          have h0s : 0 ≤ s := by
            rw [hs, List.sum_reverse]
            exact List.sum_nonneg (fun x hx => by
              obtain ⟨e, he', hfe⟩ := List.mem_map.mp hx
              rw [← hfe]
              exact h0 e (List.mem_of_mem_take he'))
          have hnat : s.natAbs ≤ B := by
            have hcast : ((s.natAbs : ℕ) : ℤ) ≤ (B : ℤ) := by
              rw [Int.natAbs_of_nonneg h0s]
              exact hsum_le
            exact_mod_cast hcast
          have hsize : s.natAbs.size ≤ B.size := Nat.size_le_size hnat
          simp only [isz]
          omega
        rw [hcSum]
        refine Nat.mul_le_mul_left Ksm ?_
        omega
    have hfold8 := hfold main sumP E (fun i accs => ∃ s : ℤ,
        accs = Val.int s :: ofList E :: p :: ofList X :: rest ∧
        s = (((E.take i).map entryC).reverse).sum) cSum L hL hbody
    have hcost : E.length * (cSum + Kf * (L + 1)) + Kf ≤ (3 * Ksm + 2 * Kf) * N := by
      have h1 : E.length * cSum ≤ 3 * Ksm * N := by
        have h3 : E.length * (L + B.size + 3) ≤ 3 * N := by
          have hfac : L + B.size + 3 ≤ 3 * (B.size + L + 1) := by omega
          calc E.length * (L + B.size + 3) ≤ (E.length + 1) * (L + B.size + 3) :=
                Nat.mul_le_mul_right _ (by omega)
            _ ≤ (E.length + 1) * (3 * (B.size + L + 1)) := Nat.mul_le_mul_left _ hfac
            _ = 3 * ((E.length + 1) * (B.size + L + 1)) := by ring
            _ ≤ 3 * N := Nat.mul_le_mul_left 3 hNA1
        calc E.length * cSum = Ksm * (E.length * (L + B.size + 3)) := by rw [hcSum]; ring
          _ ≤ Ksm * (3 * N) := Nat.mul_le_mul_left Ksm h3
          _ = 3 * Ksm * N := by ring
      have h2 : E.length * (Kf * (L + 1)) ≤ Kf * N := by
        calc E.length * (Kf * (L + 1)) = Kf * (E.length * (L + 1)) := by ring
          _ ≤ Kf * N := Nat.mul_le_mul_left Kf hNEL
      have h3 : Kf ≤ Kf * N :=
        le_trans (le_of_eq (Nat.mul_one Kf).symm) (Nat.mul_le_mul_left Kf hN1)
      calc E.length * (cSum + Kf * (L + 1)) + Kf
          = E.length * cSum + (E.length * (Kf * (L + 1)) + Kf) := by ring
        _ ≤ 3 * Ksm * N + (Kf * N + Kf * N) := Nat.add_le_add h1 (Nat.add_le_add h2 h3)
        _ = (3 * Ksm + 2 * Kf) * N := by ring
    refine hK.conseq (main := main) (p := comb sumP)
      (P := fun vs => ∃ acc, vs = ofList E :: acc ∧ ∃ s : ℤ,
        acc = Val.int s :: ofList E :: p :: ofList X :: rest ∧
        s = (((E.take 0).map entryC).reverse).sum)
      (P' := fun vs => vs = ofList E :: Val.int 0 :: ofList E :: p :: ofList X :: rest)
      (Q := fun _ out => ∃ s : ℤ, out = Val.int s :: ofList E :: p :: ofList X :: rest ∧
        s = (((E.take E.length).map entryC).reverse).sum)
      (Q' := fun _ out => out = Val.int (E.map entryC).sum :: ofList E :: p :: ofList X :: rest)
      (C := fun _ => E.length * (cSum + Kf * (L + 1)) + Kf)
      (C' := fun _ => (3 * Ksm + 2 * Kf) * N)
      hfold8
      (fun vs hvs => ⟨Val.int 0 :: ofList E :: p :: ofList X :: rest, by rw [hvs], 0, rfl,
        by simp⟩)
      (fun _ out _ hout => by
        obtain ⟨s, hout, hs⟩ := hout
        rw [hout, hs, List.take_length, List.sum_reverse])
      (fun _ _ => hcost)
  -- phase 9: push `nil` (the seed of the rebuilt list)
  have h9 : WordR main (pvP Val.nil)
      (fun vs => vs = Val.int (E.map entryC).sum :: ofList E :: p :: ofList X :: rest)
      (fun _ out => out = Val.nil :: Val.int (E.map entryC).sum :: ofList E :: p
        :: ofList X :: rest) (fun _ => 3 * Kpv * N) := by
    refine step_pushVal' (h := hpv main) Val.nil
      (Val.int (E.map entryC).sum :: ofList E :: p :: ofList X :: rest) (3 * Kpv * N) ?_
    calc Kpv * (vsz Val.nil + 1) ≤ Kpv * 2 := Nat.mul_le_mul_left Kpv (by omega)
      _ ≤ Kpv * (3 * N) := Nat.mul_le_mul_left Kpv (by omega)
      _ = 3 * Kpv * N := by ring
  -- phase 10: roll the entry list above the rebuilt list seed
  have h10 : WordR main (roP 2)
      (fun vs => vs = Val.nil :: Val.int (E.map entryC).sum :: ofList E :: p
        :: ofList X :: rest)
      (fun _ out => out = ofList E :: Val.nil :: Val.int (E.map entryC).sum :: p
        :: ofList X :: rest) (fun _ => 24 * Kr * N) := by
    refine step_roll (h := hro main) 2
      (Val.nil :: Val.int (E.map entryC).sum :: ofList E :: p :: ofList X :: rest) (by simp)
      (24 * Kr * N) ?_
    calc Kr * (2 + 1) * (((List.take (2 + 1)
          (Val.nil :: Val.int (E.map entryC).sum :: ofList E :: p :: ofList X :: rest)).map vsz).sum
          + 1)
        = Kr * (2 + 1) * (vsz Val.nil + vsz (Val.int (E.map entryC).sum)
            + vsz (ofList E) + 1) := by
          rw [take3_sum Val.nil (Val.int (E.map entryC).sum) (ofList E)
            (p :: ofList X :: rest)]
      _ ≤ Kr * (2 + 1) * (6 * N) := by
          refine Nat.mul_le_mul_left _ ?_
          rw [vsz_int]
          omega
      _ = 18 * Kr * N := by ring
      _ ≤ 24 * Kr * N := Nat.mul_le_mul_right N (by omega)
  -- phase 11: the rebuild pass
  have h11 : WordR main (comb (.seq updP cnP))
      (fun vs => vs = ofList E :: Val.nil :: Val.int (E.map entryC).sum :: p
        :: ofList X :: rest)
      (fun _ out => out = ofList ((E.map entryUpd).reverse) :: Val.int (E.map entryC).sum
        :: p :: ofList X :: rest)
      (fun _ => (Kup + Kn + 2 * Kf) * N) := by
    have hbody : ∀ i (accs : List Val), i < E.length →
        (∃ revs : List Val, accs = ofList revs :: Val.int (E.map entryC).sum :: p
          :: ofList X :: rest ∧ revs = ((E.map entryUpd).take i).reverse) →
        WordR main (.seq updP cnP) (fun vs => vs = E.getD i .nil :: accs)
          (fun _ out => ∃ revs : List Val, out = ofList revs
            :: Val.int (E.map entryC).sum :: p :: ofList X :: rest ∧
            revs = ((E.map entryUpd).take (i + 1)).reverse) (fun _ => cReb) := by
      intro i accs hi hI
      obtain ⟨revs, haccs, hrevs⟩ := hI
      subst haccs
      have he : E.getD i .nil ∈ E := by
        rw [List.getD_eq_getElem _ _ hi]
        exact List.getElem_mem hi
      obtain ⟨c, P, Q, hPQ⟩ := htri (E.getD i .nil) he
      rw [hPQ] at he
      have hrev2 : ((E.map entryUpd).take (i + 1)).reverse
          = entryUpd (E.getD i .nil) :: ((E.map entryUpd).take i).reverse := by
        rw [List.getD_eq_getElem _ _ hi, ← List.map_take, take_succ_eq E hi, List.map_append,
          List.map_cons, List.map_nil, List.reverse_append, List.reverse_singleton,
          List.singleton_append]
        congr 1
        rw [List.map_take]
      have hstep : WordR main updP
          (fun vs => vs = E.getD i .nil :: ofList revs :: Val.int (E.map entryC).sum
            :: p :: ofList X :: rest)
          (fun _ out => out = entryUpd (E.getD i .nil) :: ofList revs
            :: Val.int (E.map entryC).sum :: p :: ofList X :: rest)
          (fun _ => Kup * (L + 1)) := by
        have h0' := hupdP main c P Q (ofList revs :: Val.int (E.map entryC).sum :: p
          :: ofList X :: rest)
        refine hK.conseq (main := main) (p := updP)
          (P := fun vs => vs = triple c P Q :: ofList revs :: Val.int (E.map entryC).sum
            :: p :: ofList X :: rest)
          (P' := fun vs => vs = E.getD i .nil :: ofList revs :: Val.int (E.map entryC).sum
            :: p :: ofList X :: rest)
          (Q := fun _ out => out = triple (if c + P = Q then 0 else c + P) P Q
            :: ofList revs :: Val.int (E.map entryC).sum :: p :: ofList X :: rest)
          (Q' := fun _ out => out = entryUpd (E.getD i .nil) :: ofList revs
            :: Val.int (E.map entryC).sum :: p :: ofList X :: rest)
          (C := fun _ => Kup * (isz c + isz P + isz Q + 1))
          (C' := fun _ => Kup * (L + 1))
          h0' (fun vs hvs => hvs.trans (by rw [hPQ])) (fun _ out _ hout => by
            rw [hout, hPQ, ← entryUpd_triple]) (fun _ _ => ?_)
        · have hsz : isz c + isz P + isz Q + 1 ≤ L + 1 := by
            have h1 : vsz (triple c P Q) = isz c + isz P + isz Q + 2 := vsz_triple c P Q
            have h2 := hL (triple c P Q) he
            rw [h1] at h2
            omega
          exact Nat.mul_le_mul_left Kup hsz
      have hstep2 : WordR main cnP
          (fun vs => vs = entryUpd (E.getD i .nil) :: ofList revs
            :: Val.int (E.map entryC).sum :: p :: ofList X :: rest)
          (fun _ out => out = ofList (entryUpd (E.getD i .nil) :: revs)
            :: Val.int (E.map entryC).sum :: p :: ofList X :: rest) (fun _ => Kn) := by
        have h0' := step_consV (h := hcn main) (entryUpd (E.getD i .nil)) (ofList revs)
          (Val.int (E.map entryC).sum :: p :: ofList X :: rest) Kn le_rfl
        refine hK.conseq (main := main) (p := cnP)
          (P := fun vs => vs = entryUpd (E.getD i .nil) :: ofList revs
            :: Val.int (E.map entryC).sum :: p :: ofList X :: rest)
          (P' := fun vs => vs = entryUpd (E.getD i .nil) :: ofList revs
            :: Val.int (E.map entryC).sum :: p :: ofList X :: rest)
          (Q := fun _ out => out = Val.cons (entryUpd (E.getD i .nil)) (ofList revs)
            :: Val.int (E.map entryC).sum :: p :: ofList X :: rest)
          (Q' := fun _ out => out = ofList (entryUpd (E.getD i .nil) :: revs)
            :: Val.int (E.map entryC).sum :: p :: ofList X :: rest)
          (C := fun _ => Kn) (C' := fun _ => Kn)
          h0' (fun _ h => h) (fun _ out _ hout => by rw [hout]; rfl) (fun _ _ => le_rfl)
      have hchain2 := wordR_seqC hK hstep hstep2
      refine hK.conseq (main := main) (p := .seq updP cnP)
        (P := fun vs => vs = E.getD i .nil :: ofList revs :: Val.int (E.map entryC).sum
          :: p :: ofList X :: rest)
        (P' := fun vs => vs = E.getD i .nil :: ofList revs :: Val.int (E.map entryC).sum
          :: p :: ofList X :: rest)
        (Q := fun _ out => out = ofList (entryUpd (E.getD i .nil) :: revs)
          :: Val.int (E.map entryC).sum :: p :: ofList X :: rest)
        (Q' := fun _ out => ∃ revs' : List Val, out = ofList revs'
          :: Val.int (E.map entryC).sum :: p :: ofList X :: rest ∧
          revs' = ((E.map entryUpd).take (i + 1)).reverse)
        (C := fun _ => Kup * (L + 1) + Kn) (C' := fun _ => cReb)
        hchain2 (fun _ h => h)
        (fun _ out _ hout => ⟨entryUpd (E.getD i .nil) :: revs, by rw [hout],
          by rw [hrev2, hrevs]⟩)
        (fun _ _ => by rw [hcReb])
    have hfold11 := hfold main (.seq updP cnP) E (fun i accs => ∃ revs : List Val,
        accs = ofList revs :: Val.int (E.map entryC).sum :: p :: ofList X :: rest ∧
        revs = ((E.map entryUpd).take i).reverse) cReb L hL hbody
    have hcost : E.length * (cReb + Kf * (L + 1)) + Kf ≤ (Kup + Kn + 2 * Kf) * N := by
      have h1 : E.length * cReb ≤ (Kup + Kn) * N := by
        have hsplit : E.length * cReb = E.length * (Kup * (L + 1)) + E.length * Kn := by
          rw [hcReb]; ring
        rw [hsplit]
        have ha : E.length * (Kup * (L + 1)) = Kup * (E.length * (L + 1)) := by ring
        rw [ha]
        have hb : Kup * (E.length * (L + 1)) ≤ Kup * N := Nat.mul_le_mul_left Kup hNEL
        have hc : E.length * Kn ≤ Kn * N := by
          calc E.length * Kn = Kn * E.length := by ring
            _ ≤ Kn * N := Nat.mul_le_mul_left Kn hND
        calc Kup * (E.length * (L + 1)) + E.length * Kn ≤ Kup * N + Kn * N :=
              Nat.add_le_add hb hc
          _ = (Kup + Kn) * N := by ring
      have h2 : E.length * (Kf * (L + 1)) ≤ Kf * N := by
        calc E.length * (Kf * (L + 1)) = Kf * (E.length * (L + 1)) := by ring
          _ ≤ Kf * N := Nat.mul_le_mul_left Kf hNEL
      have h3 : Kf ≤ Kf * N :=
        le_trans (le_of_eq (Nat.mul_one Kf).symm) (Nat.mul_le_mul_left Kf hN1)
      calc E.length * (cReb + Kf * (L + 1)) + Kf
          = E.length * cReb + (E.length * (Kf * (L + 1)) + Kf) := by ring
        _ ≤ (Kup + Kn) * N + (Kf * N + Kf * N) := Nat.add_le_add h1 (Nat.add_le_add h2 h3)
        _ = (Kup + Kn + 2 * Kf) * N := by ring
    refine hK.conseq (main := main) (p := comb (.seq updP cnP))
      (P := fun vs => ∃ acc, vs = ofList E :: acc ∧ ∃ revs : List Val,
        acc = ofList revs :: Val.int (E.map entryC).sum :: p :: ofList X :: rest ∧
        revs = ((E.map entryUpd).take 0).reverse)
      (P' := fun vs => vs = ofList E :: Val.nil :: Val.int (E.map entryC).sum :: p
        :: ofList X :: rest)
      (Q := fun _ out => ∃ revs : List Val, out = ofList revs
        :: Val.int (E.map entryC).sum :: p :: ofList X :: rest ∧
        revs = ((E.map entryUpd).take E.length).reverse)
      (Q' := fun _ out => out = ofList ((E.map entryUpd).reverse)
        :: Val.int (E.map entryC).sum :: p :: ofList X :: rest)
      (C := fun _ => E.length * (cReb + Kf * (L + 1)) + Kf)
      (C' := fun _ => (Kup + Kn + 2 * Kf) * N)
      hfold11
      (fun vs hvs => ⟨Val.nil :: Val.int (E.map entryC).sum :: p :: ofList X :: rest,
        hvs.trans rfl, [], rfl, by simp⟩)
      (fun _ out _ hout => by
        obtain ⟨revs, hout, hrevs⟩ := hout
        rw [hout, hrevs, take_length_rev_map E entryUpd])
      (fun _ _ => hcost)
  -- phase 12: swap the partial sum and the rebuilt list
  have h12 : WordR main swP
      (fun vs => vs = ofList ((E.map entryUpd).reverse) :: Val.int (E.map entryC).sum
        :: p :: ofList X :: rest)
      (fun _ out => out = Val.int (E.map entryC).sum :: ofList ((E.map entryUpd).reverse)
        :: p :: ofList X :: rest) (fun _ => 8 * Ks * N) := by
    refine step_swap (h := hsw main) (ofList ((E.map entryUpd).reverse))
      (Val.int (E.map entryC).sum) (p :: ofList X :: rest) (8 * Ks * N) ?_
    calc Ks * (vsz (ofList ((E.map entryUpd).reverse))
          + vsz (Val.int (E.map entryC).sum) + 1)
        ≤ Ks * (8 * N) := by
          refine Nat.mul_le_mul_left Ks ?_
          rw [vsz_int]
          omega
      _ = 8 * Ks * N := by ring
  -- phase 13: build the new pair `(label, state)`
  have h13 : WordR main cnP
      (fun vs => vs = Val.int (E.map entryC).sum :: ofList ((E.map entryUpd).reverse)
        :: p :: ofList X :: rest)
      (fun _ out => out = prp ((E.map entryC).sum) ((E.map entryUpd).reverse)
        :: p :: ofList X :: rest) (fun _ => 2 * Kn * N) := by
    have h0' : WordR main cnP
        (fun vs => vs = Val.int (E.map entryC).sum :: ofList ((E.map entryUpd).reverse)
          :: p :: ofList X :: rest)
        (fun _ out => out = Val.cons (Val.int (E.map entryC).sum)
          (ofList ((E.map entryUpd).reverse)) :: p :: ofList X :: rest) (fun _ => Kn * N) :=
      step_consV (h := hcn main) (Val.int (E.map entryC).sum)
        (ofList ((E.map entryUpd).reverse)) (p :: ofList X :: rest) (Kn * N)
        (le_trans (le_of_eq (Nat.mul_one Kn).symm) (Nat.mul_le_mul_left Kn hN1))
    refine hK.conseq (main := main) (p := cnP)
      (P := fun vs => vs = Val.int (E.map entryC).sum :: ofList ((E.map entryUpd).reverse)
        :: p :: ofList X :: rest)
      (P' := fun vs => vs = Val.int (E.map entryC).sum :: ofList ((E.map entryUpd).reverse)
        :: p :: ofList X :: rest)
      (Q := fun _ out => out = Val.cons (Val.int (E.map entryC).sum)
        (ofList ((E.map entryUpd).reverse)) :: p :: ofList X :: rest)
      (Q' := fun _ out => out = prp ((E.map entryC).sum) ((E.map entryUpd).reverse)
        :: p :: ofList X :: rest)
      (C := fun _ => Kn * N) (C' := fun _ => 2 * Kn * N)
      h0' (fun _ h => h) (fun _ out _ hout => by rw [hout]; rfl) (fun _ _ => by
        have h4 : Kn * N ≤ 2 * (Kn * N) := Nat.le_mul_of_pos_left _ (by norm_num)
        nlinarith [h4, Nat.zero_le (Kn * N)])
  -- phase 14: cons the new pair onto the history
  have h14 : WordR main shiftP
      (fun vs => vs = prp ((E.map entryC).sum) ((E.map entryUpd).reverse)
        :: p :: ofList X :: rest)
      (fun _ out => out = Val.cons (prp ((E.map entryC).sum) ((E.map entryUpd).reverse))
        (Val.cons p (ofList X)) :: rest) (fun _ => 12 * Ksh * N) := by
    refine hK.conseq (main := main) (p := shiftP)
      (P := fun vs => vs = prp ((E.map entryC).sum) ((E.map entryUpd).reverse)
        :: p :: ofList X :: rest)
      (P' := fun vs => vs = prp ((E.map entryC).sum) ((E.map entryUpd).reverse)
        :: p :: ofList X :: rest)
      (Q := fun _ out => out = Val.cons (prp ((E.map entryC).sum) ((E.map entryUpd).reverse))
        (Val.cons p (ofList X)) :: rest)
      (Q' := fun _ out => out = Val.cons (prp ((E.map entryC).sum) ((E.map entryUpd).reverse))
        (Val.cons p (ofList X)) :: rest)
      (C := fun _ => Ksh * (vsz (prp ((E.map entryC).sum) ((E.map entryUpd).reverse)) + 1))
      (C' := fun _ => 12 * Ksh * N)
      (hshift main (prp ((E.map entryC).sum) ((E.map entryUpd).reverse)) p (ofList X) rest)
      (fun _ h => h) (fun _ out _ hout => hout) (fun _ _ => by
        calc Ksh * (vsz (prp ((E.map entryC).sum) ((E.map entryUpd).reverse)) + 1)
            ≤ Ksh * (12 * N) := by
              refine Nat.mul_le_mul_left Ksh ?_
              omega
          _ = 12 * Ksh * N := by ring)
  -- assemble the chain
  have hchain := wordR_seqC hK h1 (wordR_seqC hK h2 (wordR_seqC hK h3 (wordR_seqC hK h4 
    (wordR_seqC hK h5 (wordR_seqC hK h6 (wordR_seqC hK h7 
    (wordR_seqC hK h8 (wordR_seqC hK h9 (wordR_seqC hK h10 
    (wordR_seqC hK h11 (wordR_seqC hK h12 (wordR_seqC hK h13 
    h14))))))))))))
  refine hK.conseq (main := main)
    (p := .seq unP (.seq dpP (.seq unP (.seq drP (.seq dpP (.seq (pvP (Val.int 0))
      (.seq (roP 1) (.seq (comb sumP) (.seq (pvP Val.nil) (.seq (roP 2)
        (.seq (comb (.seq updP cnP)) (.seq swP (.seq cnP shiftP)))))))))))))
    (P := fun vs => vs = ofList (p :: X) :: rest)
    (P' := fun vs => vs = ofList (p :: X) :: rest)
    (Q := fun _ out => out = Val.cons (prp ((E.map entryC).sum) ((E.map entryUpd).reverse))
      (Val.cons p (ofList X)) :: rest)
    (Q' := fun vs out => vs = ofList (p :: X) :: rest ∧
      out = ofList (prp ((E.map entryC).sum) ((E.map entryUpd).reverse) :: p :: X) :: rest)
    (C := fun _ => 2 * Ku * N + (4 * Kdp * N + (2 * Ku * N + (4 * Kd * N + (4 * Kdp * N
      + (4 * Kpv * N + (6 * Kr * N + ((3 * Ksm + 2 * Kf) * N + (3 * Kpv * N + (24 * Kr * N
      + ((Kup + Kn + 2 * Kf) * N + (8 * Ks * N + (2 * Kn * N + 12 * Ksh * N)))))))))))))
    (C' := fun _ => KK * N)
    hchain (fun _ h => h)
    (fun vs out hvs hout => ⟨hvs, by rw [hout]; rfl⟩)
    (fun _ _ => by
      refine le_of_eq ?_
      rw [show KK = 2 * Ku + 4 * Kdp + 2 * Ku + 4 * Kd + 4 * Kdp + 4 * Kpv + 6 * Kr
        + (3 * Ksm + 2 * Kf) + 3 * Kpv + 24 * Kr + (Kup + Kn + 2 * Kf) + 8 * Ks + 2 * Kn
        + 12 * Ksh from rfl]
      ring)

/-! ## The cost arithmetic of the loop -/

/-- The total cost of the loop fits the advertised bound (in the "atomised" form used by the
main proof: `e = d * sz`, `t = sz` with `t ≤ e`). -/
theorem loopCost_bound_atoms (Kstep Kdrop Kf S e t : ℕ) (he : 1 ≤ e) (h2 : t ≤ e) :
    S * (2 * Kdrop + Kstep * (11 * e + t + 2) + Kf * 2) + Kf
      ≤ (20 * Kstep + 4 * Kdrop + 4 * Kf + 4) * (S * e + 1) := by
  have h2e : 2 ≤ 4 * e := by omega
  have hBe : 11 * e + t + 2 ≤ 20 * e := by omega
  have hA : S * (2 * Kdrop) ≤ 4 * Kdrop * (S * e) := by
    have h := Nat.mul_le_mul_left (S * Kdrop) h2e
    calc S * (2 * Kdrop) = (S * Kdrop) * 2 := by ring
      _ ≤ (S * Kdrop) * (4 * e) := h
      _ = 4 * Kdrop * (S * e) := by ring
  have hB : S * (Kstep * (11 * e + t + 2)) ≤ 20 * Kstep * (S * e) := by
    have h := Nat.mul_le_mul_left (S * Kstep) hBe
    calc S * (Kstep * (11 * e + t + 2)) = (S * Kstep) * (11 * e + t + 2) := by ring
      _ ≤ (S * Kstep) * (20 * e) := h
      _ = 20 * Kstep * (S * e) := by ring
  have hC : S * (Kf * 2) ≤ 4 * Kf * (S * e) := by
    have h := Nat.mul_le_mul_left (S * Kf) h2e
    calc S * (Kf * 2) = (S * Kf) * 2 := by ring
      _ ≤ (S * Kf) * (4 * e) := h
      _ = 4 * Kf * (S * e) := by ring
  nlinarith [hA, hB, hC, Nat.zero_le (S * e), Nat.zero_le Kstep, Nat.zero_le Kdrop,
    Nat.zero_le Kf]

/-- The total cost of the loop fits the advertised bound. -/
theorem loopCost_bound (Kstep Kdrop Kf S d sz : ℕ) (hd : 1 ≤ d) (hs : 2 ≤ sz) :
    S * (2 * Kdrop + Kstep * (11 * d * sz + sz + 2) + Kf * 2) + Kf
      ≤ (20 * Kstep + 4 * Kdrop + 4 * Kf + 4) * (S * d * sz + 1) := by
  have hdsz : 0 < d * sz := Nat.mul_pos (by omega) (by omega)
  have h1 : 1 ≤ d * sz := by omega
  have hszle : sz ≤ d * sz := by simpa using Nat.mul_le_mul_right sz hd
  simpa only [Nat.mul_assoc] using
    loopCost_bound_atoms Kstep Kdrop Kf S (d * sz) sz h1 hszle

/-! ## The loop -/

theorem crtLabLoop_of (hK : HvdH.KernelLib) (_hI : HvdH.IntLib) (hstep : StepSpec) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (ss : List ℕ) (S : ℕ) (rest : List HvdH.Val),
    (∀ s ∈ ss, 1 ≤ s) → S = ss.prod →
    HvdH.WordR main prog
      (fun vs => vs = HvdH.ofList (Work.MainP.drv S) :: Work.MainP.acc ss 0 :: rest)
      (fun vs out => vs = HvdH.ofList (Work.MainP.drv S) :: Work.MainP.acc ss 0 :: rest ∧
        out = Work.MainP.acc ss S :: rest)
      (fun _ => K * (S * (ss.length + 1) * (S.size + 2) + 1)) := by
  obtain ⟨stepP, Kstep, hstepSpec⟩ := hstep
  obtain ⟨dropP, Kdrop, hdrop⟩ := hK.drop
  obtain ⟨comb, Kf, hfold⟩ := hK.foldList
  refine ⟨comb (.seq dropP stepP), 20 * Kstep + 4 * Kdrop + 4 * Kf + 4, ?_⟩
  intro main ss S rest hpos hS
  -- the per-round cost bound
  have hbodyV : ∀ i (accs : List HvdH.Val), i < (drv S).length → accs = acc ss i :: rest →
      HvdH.WordR main (.seq dropP stepP) (fun vs => vs = (drv S).getD i .nil :: accs)
        (fun _ out => out = acc ss (i + 1) :: rest) (fun _ => 2 * Kdrop +
          Kstep * (11 * (ss.length + 1) * (S.size + 2) + (S.size + 2) + 2)) := by
    intro i accs hi haccs
    subst haccs
    -- the `drop` of the driver element
    have hdr : HvdH.WordR main dropP (fun vs => vs = .nil :: acc ss i :: rest)
        (fun _ out => out = acc ss i :: rest) (fun _ => 2 * Kdrop) := by
      refine step_drop (h := hdrop main) (a := .nil) (tl := acc ss i :: rest) (c := 2 * Kdrop) ?_
      simp only [HvdH.vsz, HvdH.Val.enc, List.length_cons, List.length_nil]
      omega
    -- the odometer step
    have hsum := crtLabSum (ss := ss) (S := S) hS hpos i
    have hupd := crtLabUpd ss hpos
    have hst0 := hstepSpec main (prp (vlab ss (i - 1)) (Est ss i)) (Xh ss i) (vlab ss (i - 1))
      (Est ss i) (3 * (S.size + 2) + 3) S rest rfl
      (fun e he => by
        obtain ⟨s, P, heq⟩ := hsum.2.2.2.1 e he
        exact ⟨(((i % s) * P : ℕ) : ℤ), (P : ℤ), ((s * P : ℕ) : ℤ), heq⟩)
      (fun e he => hsum.2.2.2.2.1 e he) (fun e he => entryC_nonneg he)
      (fun e he => entryC_le_prod hS hpos he)
      (by rw [hsum.1]; exact hsum.2.2.1)
    have hst : HvdH.WordR main stepP (fun vs => vs = acc ss i :: rest)
        (fun _ out => out = acc ss (i + 1) :: rest)
        (fun _ => Kstep * (((Est ss i).length + 1) * (S.size + (3 * (S.size + 2) + 3) + 1)
          + HvdH.vsz (HvdH.ofList (Est ss i)) + HvdH.isz (vlab ss (i - 1)) + 1)) := by
      refine hK.conseq (main := main) (p := stepP)
        (P := fun vs => vs = HvdH.ofList (prp (vlab ss (i - 1)) (Est ss i) :: Xh ss i) :: rest)
        (P' := fun vs => vs = acc ss i :: rest)
        (Q := fun vs out => vs = HvdH.ofList (prp (vlab ss (i - 1)) (Est ss i) :: Xh ss i) :: rest ∧
          out = HvdH.ofList (prp ((Est ss i).map entryC).sum
            (((Est ss i).map entryUpd).reverse) :: prp (vlab ss (i - 1)) (Est ss i) :: Xh ss i) :: rest)
        (Q' := fun _ out => out = acc ss (i + 1) :: rest)
        (C := fun _ => Kstep * (((Est ss i).length + 1) * (S.size + (3 * (S.size + 2) + 3) + 1)
          + HvdH.vsz (HvdH.ofList (Est ss i)) + HvdH.isz (vlab ss (i - 1)) + 1))
        (C' := fun _ => Kstep * (((Est ss i).length + 1) * (S.size + (3 * (S.size + 2) + 3) + 1)
          + HvdH.vsz (HvdH.ofList (Est ss i)) + HvdH.isz (vlab ss (i - 1)) + 1))
        hst0 (fun vs hvs => by rw [hvs]; rfl) (fun vs out hvs hpost => by
          obtain ⟨-, hout⟩ := hpost
          rw [hout, hsum.1, ← hupd.2 i, acc_succ]
          rfl)
        (fun _ _ => le_rfl)
    have hseq := wordR_seqC hK hdr hst
    refine hK.conseq (main := main) (p := .seq dropP stepP)
      (P := fun vs => vs = .nil :: acc ss i :: rest)
      (P' := fun vs => vs = (drv S).getD i .nil :: acc ss i :: rest)
      (Q := fun _ out => out = acc ss (i + 1) :: rest)
      (Q' := fun _ out => out = acc ss (i + 1) :: rest)
      (C := fun _ => 2 * Kdrop + Kstep * (((Est ss i).length + 1) * (S.size + (3 * (S.size + 2) + 3) + 1)
          + HvdH.vsz (HvdH.ofList (Est ss i)) + HvdH.isz (vlab ss (i - 1)) + 1))
      (C' := fun _ => 2 * Kdrop +
          Kstep * (11 * (ss.length + 1) * (S.size + 2) + (S.size + 2) + 2))
      hseq (fun vs hvs => by rw [hvs, drv_getD]) (fun _ _ _ h => h) (fun _ _ => by
        have hb := stepCost_bound (ss := ss) (S := S) hS hpos Kstep i
        omega)
  -- the fold over the driver list
  have hdrv : (drv S).length = S := drv_length S
  have hfoldV := hfold main (.seq dropP stepP) (drv S) (fun i accs => accs = acc ss i :: rest)
    (2 * Kdrop + Kstep * (11 * (ss.length + 1) * (S.size + 2) + (S.size + 2) + 2)) 1
    (fun x hx => drv_vsz S x hx) hbodyV
  rw [hdrv] at hfoldV
  refine hK.conseq (main := main) (p := comb (.seq dropP stepP))
    (P := fun vs => ∃ accs, vs = HvdH.ofList (drv S) :: accs ∧ accs = acc ss 0 :: rest)
    (P' := fun vs => vs = HvdH.ofList (drv S) :: acc ss 0 :: rest)
    (Q := fun _ out => out = acc ss S :: rest)
    (Q' := fun vs out => vs = HvdH.ofList (drv S) :: acc ss 0 :: rest ∧ out = acc ss S :: rest)
    (C := fun _ => S * ((2 * Kdrop +
        Kstep * (11 * (ss.length + 1) * (S.size + 2) + (S.size + 2) + 2)) + Kf * (1 + 1)) + Kf)
    (C' := fun _ => (20 * Kstep + 4 * Kdrop + 4 * Kf + 4) *
        (S * (ss.length + 1) * (S.size + 2) + 1))
    hfoldV
    (fun vs hvs => ⟨acc ss 0 :: rest, by rw [hvs], rfl⟩)
    (fun vs out hvs hout => ⟨hvs, hout⟩)
    (fun _ _ => loopCost_bound Kstep Kdrop Kf S (ss.length + 1) (S.size + 2) (by omega) (by omega))

/-! ## The target theorem -/

/-- **The CRT label loop**: from the driver list `drv S` on top of `acc ss 0`, run the odometer
`S = ss.prod` times and leave `acc ss S`. -/
theorem crtLabLoop (hK : HvdH.KernelLib) (hI : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (ss : List ℕ) (S : ℕ) (rest : List HvdH.Val),
    (∀ s ∈ ss, 1 ≤ s) → S = ss.prod →
    HvdH.WordR main prog
      (fun vs => vs = HvdH.ofList (Work.MainP.drv S) :: Work.MainP.acc ss 0 :: rest)
      (fun vs out => vs = HvdH.ofList (Work.MainP.drv S) :: Work.MainP.acc ss 0 :: rest ∧
        out = Work.MainP.acc ss S :: rest)
      (fun _ => K * (S * (ss.length + 1) * (S.size + 2) + 1)) :=
  crtLabLoop_of hK hI (crtLabStepV hK hI)

end Work.MainP

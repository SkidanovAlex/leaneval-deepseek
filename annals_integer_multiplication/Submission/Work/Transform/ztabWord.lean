import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Transform.Defs
import Submission.Work.ConvR.basic
import Submission.Work.Fx.FxCommon
import Submission.Work.Transform.ztabStretch
import Submission.Work.Transform.ztabCost
import Submission.Work.Transform.ztabStar
import Submission.Work.Transform.ztabProdFacts
import Submission.Work.Transform.conjVecWord
import Submission.Work.Kernel.Raw
import Submission.Work.Transform.ztabCostExtra
import Submission.Work.Transform.ztabCis
import Submission.Work.Transform.ztabProd

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Work.Transform

open HvdH


/-- The invariant of the length-`r` `ζ`-table: in the disc with error `< 2` for `ζ^c`. -/
def ZPB (p r : ℕ) (bs : List (ℤ × ℤ)) : Prop :=
  InDiscVec p r bs ∧
    ∀ c < r, (2 : ℝ) ^ p * ‖fxC p (bs.getD c (0, 0)) - zeta r c‖ < 2

/-- The invariant after the stretch by `k`: the stretched table and the underlying `ζ`-table. -/
def ZPT (p r k : ℕ) (bs bs' : List (ℤ × ℤ)) : Prop :=
  ZPB p r bs ∧ bs'.length = k * r ∧
    ∀ i < k * r, bs'.getD i (0, 0) = bs.getD (i % r) (0, 0)

/-- The invariant after conjugation. -/
def ZPC (p r k : ℕ) (bs bs' bs'' : List (ℤ × ℤ)) : Prop :=
  ZPT p r k bs bs' ∧ bs''.length = bs'.length ∧
    ∀ i < bs'.length, bs''.getD i (0, 0) = ((bs'.getD i (0, 0)).1, -(bs'.getD i (0, 0)).2)

/-! ## Two chaining helpers -/

/-- Compose a word with an existential post with a word running for every witness. -/
theorem WordR_existsSeq {main p q : Cmd} {α : Type*} {A : List Val} {St : α → List Val}
    {P : α → Prop} {Q : α → List Val → Prop} {c B : ℕ}
    (h1 : WordR main p (fun vs => vs = A) (fun _ out => ∃ m, out = St m ∧ P m) (fun _ => c))
    (h2 : ∀ m, P m → WordR main q (fun vs => vs = St m) (fun _ out => Q m out) (fun _ => B)) :
    WordR main (.seq p q) (fun vs => vs = A) (fun _ out => ∃ m, P m ∧ Q m out)
      (fun _ => c + B) := by
  intro vs hv s R0 hs
  obtain ⟨o, s1, n1, ⟨m, hm, hP⟩, hev1, hc1, hstk1, hoth1⟩ := h1 vs hv s R0 hs
  obtain ⟨o2, s2, n2, hQ, hev2, hc2, hstk2, hoth2⟩ := h2 m hP o hm s1 R0 hstk1
  have hc1' : n1 ≤ c := hc1
  have hc2' : n2 ≤ B := hc2
  refine ⟨o2, s2, n1 + n2, ⟨m, hP, hQ⟩, Eval.seq hev1 hev2, ?_, hstk2, ?_⟩
  · show n1 + n2 ≤ c + B
    omega
  · intro k hk; rw [hoth2 k hk, hoth1 k hk]

/-- Compose two words with exact (deterministic) pre/post on the value stack. -/
theorem WordR_seqDet {main p q : Cmd} {A Bst Dst : List Val} {c d : ℕ}
    (h1 : WordR main p (fun vs => vs = A) (fun _ out => out = Bst) (fun _ => c))
    (h2 : WordR main q (fun vs => vs = Bst) (fun _ out => out = Dst) (fun _ => d)) :
    WordR main (.seq p q) (fun vs => vs = A) (fun _ out => out = Dst) (fun _ => c + d) := by
  intro vs hv s R0 hs
  obtain ⟨o, s1, n1, ho, hev1, hc1, hstk1, hoth1⟩ := h1 vs hv s R0 hs
  obtain ⟨o2, s2, n2, ho2, hev2, hc2, hstk2, hoth2⟩ := h2 o ho s1 R0 hstk1
  have hc1' : n1 ≤ c := hc1
  have hc2' : n2 ≤ d := hc2
  refine ⟨o2, s2, n1 + n2, ho2, Eval.seq hev1 hev2, ?_, hstk2, ?_⟩
  · show n1 + n2 ≤ c + d
    omega
  · intro k hk; rw [hoth2 k hk, hoth1 k hk]

/-- `l.getD i d ∈ l` for an in-range index. -/
theorem getD_mem' {α : Type*} (l : List α) (i : ℕ) (d : α) (h : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem _

/-- Compose an exact-post word with a word whose post carries a witness. -/
theorem WordR_seqCont {main p q : Cmd} {A Bst : List Val} {α : Type*}
    {P : α → Prop} {Q : α → List Val → Prop} {c Bc : ℕ}
    (h1 : WordR main p (fun vs => vs = A) (fun _ out => out = Bst) (fun _ => c))
    (h2 : WordR main q (fun vs => vs = Bst) (fun _ out => ∃ m, P m ∧ Q m out) (fun _ => Bc)) :
    WordR main (.seq p q) (fun vs => vs = A) (fun _ out => ∃ m, P m ∧ Q m out)
      (fun _ => c + Bc) := by
  intro vs hv s R0 hs
  obtain ⟨o, s1, n1, ho, hev1, hc1, hstk1, hoth1⟩ := h1 vs hv s R0 hs
  obtain ⟨o2, s2, n2, hQ, hev2, hc2, hstk2, hoth2⟩ := h2 o ho s1 R0 hstk1
  have hc1' : n1 ≤ c := hc1
  have hc2' : n2 ≤ Bc := hc2
  refine ⟨o2, s2, n1 + n2, hQ, Eval.seq hev1 hev2, ?_, hstk2, ?_⟩
  · show n1 + n2 ≤ c + Bc
    omega
  · intro k hk; rw [hoth2 k hk, hoth1 k hk]

/-- The constant absorbing the eight matched stages of `ztabWord`. -/
def ZKb1 (Kcis Kpick Kprod Kdrop Kst Kswap Kfdiv Kconj : ℕ) : ℕ :=
  1000 * (Kcis + Kpick + Kprod + Kdrop + Kst + Kswap + Kfdiv + Kconj + 100) + 1000

/-- The constant absorbing the `dup` and the two `roll 2` stages. -/
def ZKb2 (Kdup Kroll : ℕ) : ℕ := 1000 * (Kdup + Kroll + 100) + 1000

/-- The constant absorbing the extra `swap` stage. -/
def ZKb3 (Kswap : ℕ) : ℕ := 1000 * (Kswap + 100) + 1000

/-- The final constant of `ztabWord`. -/
def ZKK (Kcis Kpick Kprod Kdrop Kst Kswap Kfdiv Kconj Kdup Kroll : ℕ) : ℕ :=
  ZKb1 Kcis Kpick Kprod Kdrop Kst Kswap Kfdiv Kconj + ZKb2 Kdup Kroll + ZKb3 Kswap + 100

/-- The `ζ` tables of Prop 3.5: from `int p :: int r` (with `intList ts'`, `intList ts` and the
input vector `cvecVal zs` below) compute the "stretched" tables `i ↦ ζ^{i mod r}` and
`i ↦ ζ^{-(i mod r)}` (`ζ = e^{πi/r}`), of length `T = zs.length`, each entry a fixed-point complex
number with `2^p`-scaled error `< 2`.  Intended implementation: the length-`r` table
`c ↦ cis c (2r)` (using `FxLib.cis`: `e^{2πi c/(2r)} = ζ^c`), then replicate the whole length-`r`
table `T/r` times (`LayoutLib.replicate` + `Kernel.mapList` + `flatten`); the inverse table is the
conjugate (`y ↦ -y`), which is exactly `ζ^{-c}` since `‖ζ‖ = 1`.
The cost bound pays `vsz (intList ts') + vsz (intList ts)`: the length `T` must be read from the
values *below* `intList ts'` on the stack, so every run must traverse them
(cf. `Submission/Work/Transform/mulWord_refute.lean` for the analogous degeneracy argument).
The hypothesis `r < 2^(p-1)` (satisfied in Theorem 3.1) keeps `isz r = O(p)`, so the `r` calls of
`cis` fit the budget. -/
theorem ztabWord : HvdH.KernelLib → HvdH.IntLib → HvdH.LayoutLib → HvdH.FxLib →
    ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (p r : ℕ) (ts' ts : List ℕ) (zs : List (ℤ × ℤ)) (R : List HvdH.Val),
      100 ≤ p → 2 ≤ r → r < 2 ^ (p - 1) → zs.length = ts.prod → (∀ t ∈ ts, 0 < t) →
      HvdH.lmax ts = r →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.Val.int p :: HvdH.Val.int r :: HvdH.intList ts' ::
          HvdH.intList ts :: HvdH.cvecVal zs :: R)
        (fun vs out => ∃ (zst zstie : List (ℤ × ℤ)),
          out = HvdH.cvecVal zst :: HvdH.cvecVal zstie :: HvdH.Val.int p :: HvdH.Val.int r ::
            HvdH.intList ts' :: HvdH.intList ts :: HvdH.cvecVal zs :: R ∧
          zst.length = zs.length ∧ zstie.length = zs.length ∧
          HvdH.InDiscVec p zs.length zst ∧ HvdH.InDiscVec p zs.length zstie ∧
          (∀ i < zs.length, (2 : ℝ) ^ p * ‖HvdH.fxC p (zst.getD i (0, 0)) -
            Work.Transform.zeta r (i % r)‖ < 2) ∧
          (∀ i < zs.length, (2 : ℝ) ^ p * ‖HvdH.fxC p (zstie.getD i (0, 0)) -
            Work.Transform.zetaInv r (i % r)‖ < 2))
        (fun _ => K * (zs.length * p ^ 2 + r * (p + 1) ^ K + HvdH.vsz (HvdH.intList ts') +
          HvdH.vsz (HvdH.intList ts) + 1) + K) := by
  intro hKL hIL hLL hFx
  obtain ⟨cisP, Kcis, hcis⟩ := ztabCis hKL hIL hLL hFx
  obtain ⟨prodP, Kprod, hprod⟩ := ztabProd hKL hIL
  obtain ⟨stretchP, Kst, hstretch⟩ := ztabStretch hKL hLL
  obtain ⟨conjP, Kconj, hconj⟩ := conjVecWord hKL hIL
  obtain ⟨pickP, Kpick, hpick⟩ := hKL.pick
  obtain ⟨swapP, Kswap, hswap⟩ := hKL.swap
  obtain ⟨dropP, Kdrop, hdrop⟩ := hKL.drop
  obtain ⟨dupP, Kdup, hdup⟩ := hKL.dup
  obtain ⟨rollP, Kroll, hroll⟩ := hKL.roll
  obtain ⟨fdivP, Kfdiv, hfdiv⟩ := hIL.fdiv
  obtain ⟨hstarZeta, hstarFxC, hstarNorm⟩ := ztabStar
  obtain ⟨hF1, hF2, hF3, hF4, hF5, hF6, hF7, hF8, hF9, hF10⟩ := ztabProdFacts
  refine ⟨Cmd.seq cisP (Cmd.seq
      (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (pickP 4) prodP) (pickP 4)) swapP) fdivP)
        swapP) dropP)
      (Cmd.seq stretchP (Cmd.seq (Cmd.seq dupP (rollP 2)) (Cmd.seq conjP (rollP 2))))),
    1000 * (Kcis + Kpick + Kprod + Kdrop + Kst + Kswap + Kfdiv + Kconj + 100) + 1000 +
      (1000 * (Kdup + Kroll + 100) + 1000) + (1000 * (Kswap + 100) + 1000) + 100, ?_⟩
  intro main p r ts' ts zs R hp hr hrlt hzlen hpos hlmax
  -- basic facts
  have hTz : ts.prod = zs.length := hzlen.symm
  have hrt : r ∈ ts := hF1 ts r hlmax (by omega)
  have hleprod : r ≤ ts.prod := hF3 ts r hlmax hpos
  have hkr : ts.prod / r * r = ts.prod := hF4 ts r hlmax (by omega) hpos
  have hk1 : 1 ≤ ts.prod / r := by
    rw [Nat.le_div_iff_mul_le (by omega : 0 < r)]
    simpa using hleprod
  have hrltp : r < 2 ^ p := by
    have h2 : 2 ^ (p - 1) ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have htlt : ∀ t ∈ ts, t < 2 ^ p := by
    intro t ht
    have h1 := hF9 ts t ht
    rw [hlmax] at h1
    omega
  have hiszp : isz ((p : ℕ) : ℤ) ≤ p + 2 := hF8 p p (Nat.lt_two_pow_self (n := p))
  have hiszr : isz ((r : ℕ) : ℤ) ≤ p + 2 := hF8 r p hrltp
  have hdiv : Int.fdiv ((ts.prod : ℕ) : ℤ) ((r : ℕ) : ℤ) = ((ts.prod / r : ℕ) : ℤ) :=
    hF7 ts.prod r (by omega)
  -- size bounds of the components
  have hvszPp : vsz (Val.int (p : ℤ)) ≤ p + 2 := by rw [Work.ConvR.vsz_int]; exact hiszp
  have hvszRr : vsz (Val.int (r : ℤ)) ≤ p + 2 := by rw [Work.ConvR.vsz_int]; exact hiszr
  have hvszTv : vsz (Val.int ((ts.prod : ℕ) : ℤ)) ≤ ts.prod + 2 := by
    rw [Work.ConvR.vsz_int]; exact hF6 ts.prod
  have hvszKv : vsz (Val.int (((ts.prod / r : ℕ)) : ℤ)) ≤ ts.prod / r + 2 := by
    rw [Work.ConvR.vsz_int]; exact hF6 (ts.prod / r)
  have hBs : ∀ bs, ZPB p r bs → vsz (cvecVal bs) ≤ Work.ConvR.cvecSz p r := fun bs h => Work.ConvR.vsz_cvecVal_le h.1
  -- the ζ-table itself
  have h1 : WordR main cisP
      (fun vs => vs = Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
      (fun _ out => ∃ bs, out = cvecVal bs :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R ∧ ZPB p r bs)
      (fun _ => Kcis * (r * (p + 1) ^ Kcis + 1)) := by
    refine Work.Kernel.WordR_conseq (hcis main p r (intList ts' :: intList ts :: cvecVal zs :: R) hp hr hrlt) ?_ ?_ ?_
    · intro vs hv; rw [hv]
    · intro vs out hv hpost
      obtain ⟨bs, hout, hlen, hdisc, herr⟩ := hpost
      exact ⟨bs, hout, hdisc, herr⟩
    · intro vs _; rfl
  -- stage 2: `pick 4` (copy `intList ts` for the product word)
  have step2 : ∀ bs, ZPB p r bs → WordR main (pickP 4)
      (fun vs => vs = cvecVal bs :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
      (fun _ out => out = intList ts :: cvecVal bs :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
      (fun _ => Kpick * 5 * (Work.ConvR.cvecSz p r + 2 * (p + 2) + vsz (intList ts) + vsz (intList ts') + 1)) := by
    intro bs hPB
    intro vs hv s Rg hg
    obtain ⟨o, s', n, hpost, hev, hcost, hstk, hoth⟩ :=
      hpick main 4 vs (by rw [hv]; simp only [List.length_cons]; omega) s Rg hg
    have hle : ((vsz (cvecVal bs) + vsz (Val.int (p : ℤ)) + vsz (Val.int (r : ℤ)) + vsz (intList ts') + vsz (intList ts)) + 1)
        ≤ Work.ConvR.cvecSz p r + 2 * (p + 2) + vsz (intList ts) + vsz (intList ts') + 1 := by
      have hb := hBs bs hPB
      omega
    have hcost' : n ≤ Kpick * 5 * (Work.ConvR.cvecSz p r + 2 * (p + 2) + vsz (intList ts) + vsz (intList ts') + 1) := by
      have hsum' : (((vs.take (4 + 1)).map vsz).sum + 1)
          ≤ Work.ConvR.cvecSz p r + 2 * (p + 2) + vsz (intList ts) + vsz (intList ts') + 1 := by
        rw [hv]
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil]
        have hb := hBs bs hPB
        omega
      have hbound : Kpick * (4 + 1) * (((vs.take (4 + 1)).map vsz).sum + 1)
          ≤ Kpick * 5 * (Work.ConvR.cvecSz p r + 2 * (p + 2) + vsz (intList ts) + vsz (intList ts') + 1) := by
        have h5 : Kpick * (4 + 1) = Kpick * 5 := by norm_num
        rw [h5]
        exact Nat.mul_le_mul_left _ hsum'
      exact le_trans hcost hbound
    refine ⟨o, s', n, ?_, hev, hcost', hstk, hoth⟩
    · rw [hpost, hv]; rfl
  -- stage 3: the product of the dimensions
  have step3 : ∀ bs, ZPB p r bs → WordR main prodP
      (fun vs => vs = intList ts :: cvecVal bs :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
      (fun _ out => out = Val.int ((ts.prod : ℕ) : ℤ) :: intList ts :: cvecVal bs :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
      (fun _ => Kprod * (vsz (intList ts) + ts.prod * p ^ 2 + 1)) := by
    intro bs hPB
    refine Work.Kernel.WordR_conseq
      (hprod main p ts (cvecVal bs :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
        hp hpos htlt) ?_ ?_ ?_
    · intro vs hv; rw [hv]
    · intro vs out hv hpost; rw [hpost]
    · intro vs _; exact le_rfl
  -- stage 4: `pick 4` (copy `int r` for the division)
  have step4 : ∀ bs, ZPB p r bs → WordR main (pickP 4)
      (fun vs => vs = Val.int ((ts.prod : ℕ) : ℤ) :: intList ts :: cvecVal bs :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
      (fun _ out => out = Val.int (r : ℤ) :: Val.int ((ts.prod : ℕ) : ℤ) :: intList ts :: cvecVal bs :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
      (fun _ => Kpick * 5 * ((ts.prod + 2) + vsz (intList ts) + Work.ConvR.cvecSz p r + 2 * (p + 2) + 1)) := by
    intro bs hPB
    intro vs hv s Rg hg
    obtain ⟨o, s', n, hpost, hev, hcost, hstk, hoth⟩ :=
      hpick main 4 vs (by rw [hv]; simp only [List.length_cons]; omega) s Rg hg
    have hle : ((vsz (Val.int ((ts.prod : ℕ) : ℤ)) + vsz (intList ts) + vsz (cvecVal bs) + vsz (Val.int (p : ℤ)) + vsz (Val.int (r : ℤ))) + 1)
        ≤ (ts.prod + 2) + vsz (intList ts) + Work.ConvR.cvecSz p r + 2 * (p + 2) + 1 := by
      have hb := hBs bs hPB
      omega
    have hcost' : n ≤ Kpick * 5 * ((ts.prod + 2) + vsz (intList ts) + Work.ConvR.cvecSz p r + 2 * (p + 2) + 1) := by
      have hsum' : (((vs.take (4 + 1)).map vsz).sum + 1)
          ≤ (ts.prod + 2) + vsz (intList ts) + Work.ConvR.cvecSz p r + 2 * (p + 2) + 1 := by
        rw [hv]
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil]
        have hb := hBs bs hPB
        omega
      have hbound : Kpick * (4 + 1) * (((vs.take (4 + 1)).map vsz).sum + 1)
          ≤ Kpick * 5 * ((ts.prod + 2) + vsz (intList ts) + Work.ConvR.cvecSz p r + 2 * (p + 2) + 1) := by
        have h5 : Kpick * (4 + 1) = Kpick * 5 := by norm_num
        rw [h5]
        exact Nat.mul_le_mul_left _ hsum'
      exact le_trans hcost hbound
    refine ⟨o, s', n, ?_, hev, hcost', hstk, hoth⟩
    · rw [hpost, hv]; rfl
  -- a generic `swap` step
  have swapStep : ∀ (a b : Val) (tl : List Val) (ca cb : ℕ), vsz a ≤ ca → vsz b ≤ cb →
      WordR main swapP (fun vs => vs = a :: b :: tl) (fun _ out => out = b :: a :: tl)
        (fun _ => Kswap * (ca + cb + 1)) := by
    intro a b tl ca cb ha hb
    intro vs hv s Rg hg
    obtain ⟨o, s', n, hpost, hev, hcost, hstk, hoth⟩ :=
      hswap main vs (by rw [hv]; simp only [List.length_cons]; omega) s Rg hg
    obtain ⟨a', b', rest, hvs, hout⟩ := hpost
    obtain ⟨ha', hb', hr⟩ := Work.Fx.cons_inj3 (hv.symm.trans hvs)
    have hcost' : n ≤ Kswap * (ca + cb + 1) := by
      have h1 : vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1 ≤ ca + cb + 1 := by
        rw [hv]; simp only [List.getD_cons_zero, List.getD_cons_succ]; omega
      calc n ≤ Kswap * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1) := hcost
        _ ≤ Kswap * (ca + cb + 1) := Nat.mul_le_mul_left _ h1
    refine ⟨o, s', n, ?_, hev, hcost', hstk, hoth⟩
    · rw [hout, ← hb', ← ha', hr]
  -- stage 5: swap `int r` and the product
  have step5 : ∀ bs, ZPB p r bs → WordR main swapP
      (fun vs => vs = Val.int (r : ℤ) :: Val.int ((ts.prod : ℕ) : ℤ) :: intList ts :: cvecVal bs :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
      (fun _ out => out = Val.int ((ts.prod : ℕ) : ℤ) :: Val.int (r : ℤ) :: intList ts :: cvecVal bs :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
      (fun _ => Kswap * ((ts.prod + 2) + (p + 3) + 1)) := by
    intro bs hPB
    refine Work.Kernel.WordR_conseq
      (swapStep (Val.int (r : ℤ)) (Val.int ((ts.prod : ℕ) : ℤ))
        (intList ts :: cvecVal bs :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
        (p + 2) (ts.prod + 2) hvszRr hvszTv) ?_ ?_ ?_
    · intro vs hv; rw [hv]
    · intro vs out hv hpost; rw [hpost]
    · intro vs _; exact Nat.mul_le_mul_left _ (by omega)
  -- stage 6: divide by `r`
  have step6 : ∀ bs, ZPB p r bs → WordR main fdivP
      (fun vs => vs = Val.int ((ts.prod : ℕ) : ℤ) :: Val.int (r : ℤ) :: intList ts :: cvecVal bs :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
      (fun _ out => out = Val.int (((ts.prod / r : ℕ)) : ℤ) :: intList ts :: cvecVal bs :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
      (fun _ => Kfdiv * (ts.prod + 2) * (p + 3)) := by
    intro bs hPB
    refine Work.Kernel.WordR_conseq (hfdiv main) ?_ ?_ ?_
    · intro vs hv
      refine ⟨((ts.prod : ℕ) : ℤ), ((r : ℕ) : ℤ),
        intList ts :: cvecVal bs :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R,
        ?_, ?_⟩
      · rw [hv]
      · omega
    · intro vs out hv hpost
      obtain ⟨a, b, rest, hvs, hout⟩ := hpost
      obtain ⟨ha, hb, hr⟩ := Work.Fx.cons_inj3 (hv.symm.trans hvs)
      have ha' : a = ((ts.prod : ℕ) : ℤ) := (Val.int.inj ha).symm
      have hb' : b = ((r : ℕ) : ℤ) := (Val.int.inj hb).symm
      rw [hout, ha', hb', ← hr, hdiv]
    · intro vs hv
      rw [hv]
      show Kfdiv * isz ((ts.prod : ℕ) : ℤ) * isz ((r : ℕ) : ℤ) ≤ Kfdiv * (ts.prod + 2) * (p + 3)
      calc Kfdiv * isz ((ts.prod : ℕ) : ℤ) * isz ((r : ℕ) : ℤ)
          ≤ Kfdiv * (ts.prod + 2) * (p + 2) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left Kfdiv (hF6 ts.prod)) hiszr
        _ ≤ Kfdiv * (ts.prod + 2) * (p + 3) :=
            Nat.mul_le_mul_left _ (by omega)
  -- stage 7: swap the copy of `intList ts` above the quotient
  have step7 : ∀ bs, ZPB p r bs → WordR main swapP
      (fun vs => vs = Val.int (((ts.prod / r : ℕ)) : ℤ) :: intList ts :: cvecVal bs :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
      (fun _ out => out = intList ts :: Val.int (((ts.prod / r : ℕ)) : ℤ) :: cvecVal bs :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
      (fun _ => Kswap * ((ts.prod / r + 2) + vsz (intList ts) + 1)) := by
    intro bs hPB
    refine Work.Kernel.WordR_conseq
      (swapStep (Val.int (((ts.prod / r : ℕ)) : ℤ)) (intList ts)
        (cvecVal bs :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
        (ts.prod / r + 2) (vsz (intList ts)) hvszKv le_rfl) ?_ ?_ ?_
    · intro vs hv; rw [hv]
    · intro vs out hv hpost; rw [hpost]
    · intro vs _; exact le_rfl
  -- stage 8: drop the copy of `intList ts`
  have step8 : ∀ bs, ZPB p r bs → WordR main dropP
      (fun vs => vs = intList ts :: Val.int (((ts.prod / r : ℕ)) : ℤ) :: cvecVal bs :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
      (fun _ out => out = Val.int (((ts.prod / r : ℕ)) : ℤ) :: cvecVal bs :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
      (fun _ => Kdrop * (vsz (intList ts) + 1)) := by
    intro bs hPB
    intro vs hv s Rg hg
    obtain ⟨o, s', n, hpost, hev, hcost, hstk, hoth⟩ :=
      hdrop main vs (by rw [hv]; exact List.cons_ne_nil _ _) s Rg hg
    obtain ⟨v, rest, hvs, hout⟩ := hpost
    obtain ⟨ha, hr⟩ := List.cons.inj (hv.symm.trans hvs)
    have hcost' : n ≤ Kdrop * (vsz (intList ts) + 1) := by
      have h1 : vsz (vs.headD .nil) + 1 ≤ vsz (intList ts) + 1 := by
        rw [hv]; simp only [List.headD_cons]; omega
      calc n ≤ Kdrop * (vsz (vs.headD .nil) + 1) := hcost
        _ ≤ Kdrop * (vsz (intList ts) + 1) := Nat.mul_le_mul_left _ h1
    refine ⟨o, s', n, ?_, hev, hcost', hstk, hoth⟩
    · rw [hout, hr]
  -- stage 9: the stretch
  have stretchStep9 : ∀ bs, ZPB p r bs → WordR main stretchP
      (fun vs => vs = Val.int (((ts.prod / r : ℕ)) : ℤ) :: cvecVal bs :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
      (fun _ out => ∃ bs', out = cvecVal bs' :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R ∧
        (bs'.length = (ts.prod / r) * r ∧ ∀ i < (ts.prod / r) * r, bs'.getD i (0, 0) = bs.getD (i % r) (0, 0)))
      (fun _ => Kst * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 1) + 1)) := by
    intro bs hPB
    have hblen : bs.length = r := hPB.1.1
    refine Work.Kernel.WordR_conseq
      (hstretch main (ts.prod / r) bs (Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R) hk1) ?_ ?_ ?_
    · intro vs hv; rw [hv]
    · intro vs out hv hpost
      obtain ⟨bs', hout, hlen, hpt⟩ := hpost
      refine ⟨bs', hout, ?_, ?_⟩
      · rw [hlen, hblen]
      · intro i hi
        have hi' : i < (ts.prod / r) * bs.length := by rw [hblen]; exact hi
        have h := hpt i hi'
        rw [hblen] at h
        exact h
    · intro vs _
      have hb := hBs bs hPB
      exact Nat.mul_le_mul_left Kst
        (Nat.add_le_add_right (Nat.mul_le_mul_left (ts.prod / r) (by omega)) 1)
  -- size bound for a stretched table that is in the disc
  have hszDisc : ∀ v : List (ℤ × ℤ), InDiscVec p ((ts.prod / r) * r) v →
      vsz (cvecVal v) ≤ (ts.prod / r) * (Work.ConvR.cvecSz p r + 2) := by
    intro v hv
    have h1 : vsz (cvecVal v) ≤ Work.ConvR.cvecSz p ((ts.prod / r) * r) := Work.ConvR.vsz_cvecVal_le hv
    have h2 : Work.ConvR.cvecSz p ((ts.prod / r) * r) ≤ (ts.prod / r) * (Work.ConvR.cvecSz p r + 2) := by
      have e1 : Work.ConvR.cvecSz p ((ts.prod / r) * r)
          = (ts.prod / r) * r * (2 * p + 8) + (ts.prod / r) * r + 1 := rfl
      have e2 : (ts.prod / r) * (Work.ConvR.cvecSz p r + 2)
          = (ts.prod / r) * (r * (2 * p + 8) + r + 3) := rfl
      rw [e1, e2]
      have e3 : (ts.prod / r) * r * (2 * p + 8) = (ts.prod / r) * (r * (2 * p + 8)) := by ring
      have h3 : (ts.prod / r) * (r * (2 * p + 8) + r + 3)
          = (ts.prod / r) * (r * (2 * p + 8)) + (ts.prod / r) * (r + 3) := by ring
      rw [e3, h3]
      have h4 : (ts.prod / r) * (r + 3) = (ts.prod / r) * r + 3 * (ts.prod / r) := by ring
      rw [h4]
      omega
    omega
  -- stage 10: duplicate the stretched table
  have step10 : ∀ bs', InDiscVec p ((ts.prod / r) * r) bs' →
      WordR main dupP
        (fun vs => vs = cvecVal bs' :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
        (fun _ out => out = cvecVal bs' :: cvecVal bs' :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
        (fun _ => Kdup * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 2) + 1)) := by
    intro bs' hD
    intro vs hv s Rg hg
    obtain ⟨o, s', n, hpost, hev, hcost, hstk, hoth⟩ :=
      hdup main vs (by rw [hv]; exact List.cons_ne_nil _ _) s Rg hg
    obtain ⟨v, rest, hvs, hout⟩ := hpost
    obtain ⟨ha, hr⟩ := List.cons.inj (hv.symm.trans hvs)
    have hb := hszDisc bs' hD
    have hcost' : n ≤ Kdup * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 2) + 1) := by
      have h1 : vsz (vs.headD .nil) + 1 ≤ (ts.prod / r) * (Work.ConvR.cvecSz p r + 2) + 1 := by
        rw [hv]; simp only [List.headD_cons]; omega
      calc n ≤ Kdup * (vsz (vs.headD .nil) + 1) := hcost
        _ ≤ Kdup * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 2) + 1) := Nat.mul_le_mul_left _ h1
    refine ⟨o, s', n, ?_, hev, hcost', hstk, hoth⟩
    · rw [hout, ← ha, hr]
  -- stage 11: roll `int p` above the two copies
  have step11 : ∀ bs', InDiscVec p ((ts.prod / r) * r) bs' →
      WordR main (rollP 2)
        (fun vs => vs = cvecVal bs' :: cvecVal bs' :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
        (fun _ out => out = Val.int (p : ℤ) :: cvecVal bs' :: cvecVal bs' :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
        (fun _ => 3 * Kroll * (2 * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 2)) + (p + 2) + 1)) := by
    intro bs' hD
    intro vs hv s Rg hg
    obtain ⟨o, s', n, hpost, hev, hcost, hstk, hoth⟩ :=
      hroll main 2 vs (by rw [hv]; simp only [List.length_cons]; omega) s Rg hg
    have hb := hszDisc bs' hD
    have hcost' : n ≤ 3 * Kroll * (2 * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 2)) + (p + 2) + 1) := by
      have hsum' : (((vs.take (2 + 1)).map vsz).sum + 1)
          ≤ 2 * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 2)) + (p + 2) + 1 := by
        rw [hv]
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil]
        nlinarith [hb, hvszPp]
      have hbound : Kroll * (2 + 1) * (((vs.take (2 + 1)).map vsz).sum + 1)
          ≤ 3 * Kroll * (2 * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 2)) + (p + 2) + 1) := by
        have h3 : Kroll * (2 + 1) = 3 * Kroll := by ring
        rw [h3]
        exact Nat.mul_le_mul_left _ hsum'
      exact le_trans hcost hbound
    refine ⟨o, s', n, ?_, hev, hcost', hstk, hoth⟩
    · rw [hpost, hv]; rfl
  -- stage 12: conjugate the top copy
  have step12 : ∀ bs', InDiscVec p ((ts.prod / r) * r) bs' →
      WordR main conjP
        (fun vs => vs = Val.int (p : ℤ) :: cvecVal bs' :: cvecVal bs' :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
        (fun _ out => ∃ bs'', out = cvecVal bs'' :: Val.int (p : ℤ) :: cvecVal bs' :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R ∧
          (bs''.length = bs'.length ∧ InDiscVec p bs'.length bs'' ∧
            ∀ i < bs'.length, bs''.getD i (0, 0) = ((bs'.getD i (0, 0)).1, -(bs'.getD i (0, 0)).2)))
        (fun _ => Kconj * (ts.prod * p ^ 2) + Kconj) := by
    intro bs' hD
    refine Work.Kernel.WordR_conseq
      (hconj main p bs'.length bs' (cvecVal bs' :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
        hp (by rw [hD.1]; have h1 : 0 < (ts.prod / r) * r := Nat.mul_pos (by omega) (by omega); omega)
        rfl (by rw [hD.1]; exact hD)) ?_ ?_ ?_
    · intro vs hv; rw [hv]
    · intro vs out hv hpost
      obtain ⟨-, bs'', hout, hlen', hdisc', hpt'⟩ := hpost
      exact ⟨bs'', hout, hlen', hdisc', hpt'⟩
    · intro vs _
      have hlenT : bs'.length = ts.prod := by rw [hD.1, hkr]
      rw [hlenT]
  -- stage 13: roll the forward table above the conjugate
  have step13 : ∀ bs' bs'', vsz (cvecVal bs') ≤ (ts.prod / r) * (Work.ConvR.cvecSz p r + 2) →
      vsz (cvecVal bs'') ≤ (ts.prod / r) * (Work.ConvR.cvecSz p r + 2) →
      WordR main (rollP 2)
        (fun vs => vs = cvecVal bs'' :: Val.int (p : ℤ) :: cvecVal bs' :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
        (fun _ out => out = cvecVal bs' :: cvecVal bs'' :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
        (fun _ => 3 * Kroll * (2 * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 2)) + (p + 2) + 1)) := by
    intro bs' bs'' hb' hb''
    intro vs hv s Rg hg
    obtain ⟨o, s', n, hpost, hev, hcost, hstk, hoth⟩ :=
      hroll main 2 vs (by rw [hv]; simp only [List.length_cons]; omega) s Rg hg
    have hcost' : n ≤ 3 * Kroll * (2 * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 2)) + (p + 2) + 1) := by
      have hsum' : (((vs.take (2 + 1)).map vsz).sum + 1)
          ≤ 2 * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 2)) + (p + 2) + 1 := by
        rw [hv]
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil]
        nlinarith [hb', hb'', hvszPp]
      have hbound : Kroll * (2 + 1) * (((vs.take (2 + 1)).map vsz).sum + 1)
          ≤ 3 * Kroll * (2 * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 2)) + (p + 2) + 1) := by
        have h3 : Kroll * (2 + 1) = 3 * Kroll := by ring
        rw [h3]
        exact Nat.mul_le_mul_left _ hsum'
      exact le_trans hcost hbound
    refine ⟨o, s', n, ?_, hev, hcost', hstk, hoth⟩
    · rw [hpost, hv]; rfl
  -- the in-disc property of the stretched table
  have hstretchDisc : ∀ bs, ZPB p r bs → ∀ bs' : List (ℤ × ℤ),
      bs'.length = (ts.prod / r) * r →
      (∀ i < (ts.prod / r) * r, bs'.getD i (0, 0) = bs.getD (i % r) (0, 0)) →
      InDiscVec p ((ts.prod / r) * r) bs' := by
    intro bs hPB bs' hlen hpt
    refine ⟨hlen, ?_⟩
    intro z hz
    obtain ⟨i, hi, hzi⟩ := List.mem_iff_getElem.mp hz
    have hik : i < (ts.prod / r) * r := by rw [← hlen]; exact hi
    have h1 : bs'.getD i (0, 0) = bs.getD (i % r) (0, 0) := hpt i hik
    have h2 : z = bs.getD (i % r) (0, 0) := by
      rw [← hzi, ← List.getD_eq_getElem _ _ hi]
      exact h1
    rw [h2]
    exact hPB.1.2 _ (getD_mem' _ _ _ (by rw [hPB.1.1]; exact Nat.mod_lt _ (by omega)))
  -- the chain
  have h28 : ∀ bs, ZPB p r bs → WordR main (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (pickP 4) prodP) (pickP 4)) swapP) fdivP) swapP) dropP)
      (fun vs => vs = cvecVal bs :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R) (fun _ out => out = Val.int (((ts.prod / r : ℕ)) : ℤ) :: cvecVal bs :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
      (fun _ => ((((((Kpick * 5 * (Work.ConvR.cvecSz p r + 2 * (p + 2) + vsz (intList ts) + vsz (intList ts') + 1) + Kprod * (vsz (intList ts) + ts.prod * p ^ 2 + 1)) + Kpick * 5 * ((ts.prod + 2) + vsz (intList ts) + Work.ConvR.cvecSz p r + 2 * (p + 2) + 1)) + Kswap * ((ts.prod + 2) + (p + 3) + 1)) + Kfdiv * (ts.prod + 2) * (p + 3)) + Kswap * ((ts.prod / r + 2) + vsz (intList ts) + 1)) + Kdrop * (vsz (intList ts) + 1))) := by
    intro bs hPB
    exact WordR_seqDet
      (WordR_seqDet
        (WordR_seqDet
          (WordR_seqDet
            (WordR_seqDet
              (WordR_seqDet (step2 bs hPB) (step3 bs hPB)) (step4 bs hPB))
            (step5 bs hPB)) (step6 bs hPB)) (step7 bs hPB)) (step8 bs hPB)
  have h913 : ∀ bs, ZPB p r bs → WordR main (Cmd.seq stretchP (Cmd.seq (Cmd.seq dupP (rollP 2)) (Cmd.seq conjP (rollP 2))))
      (fun vs => vs = Val.int (((ts.prod / r : ℕ)) : ℤ) :: cvecVal bs :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
      (fun _ out => ∃ bs', (bs'.length = (ts.prod / r) * r ∧ ∀ i < (ts.prod / r) * r, bs'.getD i (0, 0) = bs.getD (i % r) (0, 0)) ∧ (∃ bs'', (bs''.length = bs'.length ∧ InDiscVec p bs'.length bs'' ∧ ∀ i < bs'.length, bs''.getD i (0, 0) = ((bs'.getD i (0, 0)).1, -(bs'.getD i (0, 0)).2)) ∧ out = cvecVal bs' :: cvecVal bs'' :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R))
      (fun _ => Kst * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 1) + 1) + ((Kdup * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 2) + 1) + 3 * Kroll * (2 * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 2)) + (p + 2) + 1)) + (Kconj * (ts.prod * p ^ 2) + Kconj + 3 * Kroll * (2 * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 2)) + (p + 2) + 1)))) := by
    intro bs hPB
    have hblen : bs.length = r := hPB.1.1
    have h9 : WordR main stretchP
        (fun vs => vs = Val.int (((ts.prod / r : ℕ)) : ℤ) :: cvecVal bs :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
        (fun _ out => ∃ bs', out = cvecVal bs' :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R ∧ (bs'.length = (ts.prod / r) * r ∧ ∀ i < (ts.prod / r) * r, bs'.getD i (0, 0) = bs.getD (i % r) (0, 0)))
        (fun _ => Kst * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 1) + 1)) := by
      refine Work.Kernel.WordR_conseq (hstretch main (ts.prod / r) bs (Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R) hk1) ?_ ?_ ?_
      · intro vs hv; rw [hv]
      · intro vs out hv hpost
        obtain ⟨bs', hout, hlen, hpt⟩ := hpost
        refine ⟨bs', hout, ?_, ?_⟩
        · rw [hlen, hblen]
        · intro i hi
          have hi' : i < (ts.prod / r) * bs.length := by rw [hblen]; exact hi
          have h := hpt i hi'
          rw [hblen] at h
          exact h
      · intro vs _
        have hb := hBs bs hPB
        show Kst * ((ts.prod / r) * (vsz (cvecVal bs) + 1) + 1)
            ≤ Kst * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 1) + 1)
        apply Nat.mul_le_mul_left
        apply Nat.add_le_add_right
        apply Nat.mul_le_mul_left
        omega
    have h2 : ∀ (bs' : List (ℤ × ℤ)) (hPT' : bs'.length = (ts.prod / r) * r ∧ ∀ i < (ts.prod / r) * r, bs'.getD i (0, 0) = bs.getD (i % r) (0, 0)),
        WordR main (Cmd.seq (Cmd.seq dupP (rollP 2)) (Cmd.seq conjP (rollP 2)))
          (fun vs => vs = cvecVal bs' :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
          (fun _ out => ∃ bs'', (bs''.length = bs'.length ∧ InDiscVec p bs'.length bs'' ∧ ∀ i < bs'.length, bs''.getD i (0, 0) = ((bs'.getD i (0, 0)).1, -(bs'.getD i (0, 0)).2)) ∧ out = cvecVal bs' :: cvecVal bs'' :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
          (fun _ => ((Kdup * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 2) + 1) + 3 * Kroll * (2 * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 2)) + (p + 2) + 1)) + (Kconj * (ts.prod * p ^ 2) + Kconj + 3 * Kroll * (2 * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 2)) + (p + 2) + 1)))) := by
      intro bs' hPT'
      have hd' : InDiscVec p ((ts.prod / r) * r) bs' := hstretchDisc bs hPB bs' hPT'.1 hPT'.2
      have h1011 : WordR main (Cmd.seq dupP (rollP 2)) (fun vs => vs = cvecVal bs' :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R) (fun _ out => out = Val.int (p : ℤ) :: cvecVal bs' :: cvecVal bs' :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R) (fun _ => Kdup * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 2) + 1) + 3 * Kroll * (2 * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 2)) + (p + 2) + 1)) := by
        exact WordR_seqDet (step10 bs' hd') (step11 bs' hd')
      have h1213 : WordR main (Cmd.seq conjP (rollP 2)) (fun vs => vs = Val.int (p : ℤ) :: cvecVal bs' :: cvecVal bs' :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R) (fun _ out => ∃ bs'', (bs''.length = bs'.length ∧ InDiscVec p bs'.length bs'' ∧ ∀ i < bs'.length, bs''.getD i (0, 0) = ((bs'.getD i (0, 0)).1, -(bs'.getD i (0, 0)).2)) ∧ out = cvecVal bs' :: cvecVal bs'' :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R) (fun _ => Kconj * (ts.prod * p ^ 2) + Kconj + 3 * Kroll * (2 * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 2)) + (p + 2) + 1)) := by
        exact WordR_existsSeq (step12 bs' hd') (fun bs'' hPT'' => step13 bs' bs''
          (hszDisc bs' hd') (hszDisc bs'' (by have hh := hPT''.2.1; rw [hPT'.1] at hh; exact hh)))
      exact WordR_seqCont h1011 h1213
    exact WordR_existsSeq h9 h2
  have hchain : WordR main (Cmd.seq cisP (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (pickP 4) prodP) (pickP 4)) swapP) fdivP) swapP) dropP) (Cmd.seq stretchP (Cmd.seq (Cmd.seq dupP (rollP 2)) (Cmd.seq conjP (rollP 2))))))
      (fun vs => vs = Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)
      (fun _ out => ∃ bs, ZPB p r bs ∧ (∃ bs', (bs'.length = (ts.prod / r) * r ∧ ∀ i < (ts.prod / r) * r, bs'.getD i (0, 0) = bs.getD (i % r) (0, 0)) ∧ (∃ bs'', (bs''.length = bs'.length ∧ InDiscVec p bs'.length bs'' ∧ ∀ i < bs'.length, bs''.getD i (0, 0) = ((bs'.getD i (0, 0)).1, -(bs'.getD i (0, 0)).2)) ∧ out = cvecVal bs' :: cvecVal bs'' :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: intList ts' :: intList ts :: cvecVal zs :: R)))
      (fun _ => Kcis * (r * (p + 1) ^ Kcis + 1) + (((((((Kpick * 5 * (Work.ConvR.cvecSz p r + 2 * (p + 2) + vsz (intList ts) + vsz (intList ts') + 1) + Kprod * (vsz (intList ts) + ts.prod * p ^ 2 + 1)) + Kpick * 5 * ((ts.prod + 2) + vsz (intList ts) + Work.ConvR.cvecSz p r + 2 * (p + 2) + 1)) + Kswap * ((ts.prod + 2) + (p + 3) + 1)) + Kfdiv * (ts.prod + 2) * (p + 3)) + Kswap * ((ts.prod / r + 2) + vsz (intList ts) + 1)) + Kdrop * (vsz (intList ts) + 1)) + (Kst * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 1) + 1) + ((Kdup * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 2) + 1) + 3 * Kroll * (2 * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 2)) + (p + 2) + 1)) + (Kconj * (ts.prod * p ^ 2) + Kconj + 3 * Kroll * (2 * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 2)) + (p + 2) + 1)))))) := by
    refine WordR_existsSeq h1 ?_
    intro bs hPB
    exact WordR_seqCont (h28 bs hPB) (h913 bs hPB)

  refine Work.Kernel.WordR_conseq hchain (fun vs hv => hv) ?_ ?_
  · intro vs out hv hpost
    obtain ⟨bs, hPB, bs', hPT', bs'', hPT'', hout⟩ := hpost
    have hD' : InDiscVec p ((ts.prod / r) * r) bs' := hstretchDisc bs hPB bs' hPT'.1 hPT'.2
    refine ⟨bs', bs'', hout, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hPT'.1, hkr, hTz]
    · rw [hPT''.1, hPT'.1, hkr, hTz]
    · refine ⟨?_, ?_⟩
      · rw [hPT'.1, hkr, hTz]
      · intro z hz
        obtain ⟨i, hi, hzi⟩ := List.mem_iff_getElem.mp hz
        have hik : i < (ts.prod / r) * r := by rw [← hPT'.1]; exact hi
        have h1 : bs'.getD i (0, 0) = bs.getD (i % r) (0, 0) := hPT'.2 i hik
        have h2 : z = bs.getD (i % r) (0, 0) := by
          rw [← hzi, ← List.getD_eq_getElem _ _ hi]
          exact h1
        rw [h2]
        exact hPB.1.2 _ (getD_mem' _ _ _ (by rw [hPB.1.1]; exact Nat.mod_lt _ (by omega)))
    · refine ⟨?_, ?_⟩
      · rw [hPT''.1, hPT'.1, hkr, hTz]
      · intro z hz
        obtain ⟨i, hi, hzi⟩ := List.mem_iff_getElem.mp hz
        have hi' : i < bs'.length := by omega
        have h3 : inDisc p (bs'.getD i (0, 0)) := hD'.2 _ (getD_mem' _ _ _ hi')
        have h1 : bs''.getD i (0, 0) = ((bs'.getD i (0, 0)).1, -(bs'.getD i (0, 0)).2) :=
          hPT''.2.2 i hi'
        have h2 : z = ((bs'.getD i (0, 0)).1, -(bs'.getD i (0, 0)).2) := by
          rw [← hzi, ← List.getD_eq_getElem _ _ hi]
          exact h1
        rw [h2]
        simp only [HvdH.inDisc] at h3 ⊢
        have h4 : (-(bs'.getD i (0, 0)).2) ^ 2 = (bs'.getD i (0, 0)).2 ^ 2 := by ring
        rw [h4]
        exact h3
    · intro i hi
      have hik : i < (ts.prod / r) * r := by omega
      rw [hPT'.2 i hik]
      exact hPB.2 (i % r) (Nat.mod_lt _ (by omega))
    · intro i hi
      have hi' : i < bs'.length := by omega
      have hik : i < (ts.prod / r) * r := by omega
      have h1 : bs''.getD i (0, 0) = ((bs'.getD i (0, 0)).1, -(bs'.getD i (0, 0)).2) :=
        hPT''.2.2 i hi'
      rw [h1, hstarFxC, hPT'.2 i hik, ← hstarZeta, hstarNorm]
      exact hPB.2 (i % r) (Nat.mod_lt _ (by omega))
  · intro vs hv
    have hb1 := ztabCost p r (ts.prod) (ts.prod / r) (vsz (intList ts)) (vsz (intList ts')) (Work.ConvR.cvecSz p r)
      Kcis Kpick Kprod Kdrop Kst Kswap Kfdiv Kconj (ZKb1 Kcis Kpick Kprod Kdrop Kst Kswap Kfdiv Kconj) hp hr hk1 hkr rfl rfl
    have hb2 := ztabCostExtra p r (ts.prod) (ts.prod / r) (Work.ConvR.cvecSz p r) Kdup Kroll
      (ZKb2 Kdup Kroll) hp hr hk1 hkr rfl rfl
    have hb3 : Kswap * ((ts.prod / r + 2) + vsz (intList ts) + 1)
        ≤ ZKb3 Kswap * (ts.prod * p ^ 2 + vsz (intList ts) + 1) + ZKb3 Kswap := by
      rw [ZKb3]
      have h1 : ts.prod / r ≤ ts.prod := Nat.div_le_self _ _
      have h2 : ts.prod ≤ ts.prod * p ^ 2 := by
        calc ts.prod = ts.prod * 1 := by ring
          _ ≤ ts.prod * p ^ 2 := Nat.mul_le_mul_left _ (by nlinarith)
      have h4 : Kswap * ((ts.prod / r + 2) + vsz (intList ts) + 1) ≤ Kswap * (ts.prod + vsz (intList ts) + 3) := by
        apply Nat.mul_le_mul_left; omega
      have h5 : Kswap * (ts.prod + vsz (intList ts) + 3)
          ≤ Kswap * (ts.prod * p ^ 2 + vsz (intList ts) + 1) + 2 * Kswap := by
        have e : Kswap * (ts.prod * p ^ 2 + vsz (intList ts) + 1) + 2 * Kswap
            = Kswap * (ts.prod * p ^ 2 + vsz (intList ts) + 3) := by ring
        rw [e]
        exact Nat.mul_le_mul_left _ (by omega)
      have h6 : Kswap * (ts.prod * p ^ 2 + vsz (intList ts) + 1) + 2 * Kswap
          ≤ (1000 * (Kswap + 100) + 1000) * (ts.prod * p ^ 2 + vsz (intList ts) + 1)
            + (1000 * (Kswap + 100) + 1000) := by
        have h7 : Kswap * (ts.prod * p ^ 2 + vsz (intList ts) + 1)
            ≤ (1000 * (Kswap + 100) + 1000) * (ts.prod * p ^ 2 + vsz (intList ts) + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        have h8 : 2 * Kswap ≤ 1000 * (Kswap + 100) + 1000 := by omega
        linarith
      linarith
    have hK1 : (ZKb1 Kcis Kpick Kprod Kdrop Kst Kswap Kfdiv Kconj) ≤ (ZKK Kcis Kpick Kprod Kdrop Kst Kswap Kfdiv Kconj Kdup Kroll) := by rw [ZKK]; omega
    have hK2 : (ZKb2 Kdup Kroll) ≤ (ZKK Kcis Kpick Kprod Kdrop Kst Kswap Kfdiv Kconj Kdup Kroll) := by rw [ZKK]; omega
    have hK3 : (ZKb3 Kswap) ≤ (ZKK Kcis Kpick Kprod Kdrop Kst Kswap Kfdiv Kconj Kdup Kroll) := by rw [ZKK]; omega
    have hconv : Kcis * (r * (p + 1) ^ Kcis + 1)
      + Kpick * 5 * (Work.ConvR.cvecSz p r + 2 * (p + 2) + vsz (intList ts) + vsz (intList ts') + 1)
      + Kprod * (vsz (intList ts) + ts.prod * p ^ 2 + 1)
      + (Kpick * 5 * ((ts.prod + 2) + vsz (intList ts) + Work.ConvR.cvecSz p r + 2 * (p + 2) + 1)
          + Kswap * ((ts.prod + 2) + (p + 3) + 1)
          + Kfdiv * (ts.prod + 2) * (p + 3))
      + Kdrop * (vsz (intList ts) + 1)
      + Kst * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 1) + 1)
      + Kswap * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 2) + (p + 2) + 1)
      + (Kconj * (ts.prod * p ^ 2) + Kconj)
          + (Kdup * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 2) + 1)
      + 3 * Kroll * (2 * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 2)) + (p + 2) + 1)
      + 3 * Kroll * (2 * ((ts.prod / r) * (Work.ConvR.cvecSz p r + 2)) + (p + 2) + 1)
          + Kswap * ((ts.prod / r + 2) + vsz (intList ts) + 1))
        ≤ (ZKK Kcis Kpick Kprod Kdrop Kst Kswap Kfdiv Kconj Kdup Kroll) * (zs.length * p ^ 2 + r * (p + 1) ^ (ZKK Kcis Kpick Kprod Kdrop Kst Kswap Kfdiv Kconj Kdup Kroll) + vsz (intList ts') + vsz (intList ts) + 1) + (ZKK Kcis Kpick Kprod Kdrop Kst Kswap Kfdiv Kconj Kdup Kroll) := by
      set B : ℕ := zs.length * p ^ 2 + r * (p + 1) ^ (ZKK Kcis Kpick Kprod Kdrop Kst Kswap Kfdiv Kconj Kdup Kroll)
        + vsz (intList ts') + vsz (intList ts) + 1 with hB
      have hp1 : r * (p + 1) ^ (ZKb1 Kcis Kpick Kprod Kdrop Kst Kswap Kfdiv Kconj)
          ≤ r * (p + 1) ^ (ZKK Kcis Kpick Kprod Kdrop Kst Kswap Kfdiv Kconj Kdup Kroll) :=
        Nat.mul_le_mul_left r (Nat.pow_le_pow_right (by omega) hK1)
      have hp2 : r * (p + 1) ^ (ZKb2 Kdup Kroll)
          ≤ r * (p + 1) ^ (ZKK Kcis Kpick Kprod Kdrop Kst Kswap Kfdiv Kconj Kdup Kroll) :=
        Nat.mul_le_mul_left r (Nat.pow_le_pow_right (by omega) hK2)
      have m1 : (ZKb1 Kcis Kpick Kprod Kdrop Kst Kswap Kfdiv Kconj)
            * (ts.prod * p ^ 2 + r * (p + 1) ^ (ZKb1 Kcis Kpick Kprod Kdrop Kst Kswap Kfdiv Kconj)
              + vsz (intList ts') + vsz (intList ts) + 1) + (ZKb1 Kcis Kpick Kprod Kdrop Kst Kswap Kfdiv Kconj)
          ≤ (ZKb1 Kcis Kpick Kprod Kdrop Kst Kswap Kfdiv Kconj) * B + (ZKb1 Kcis Kpick Kprod Kdrop Kst Kswap Kfdiv Kconj) := by
        rw [hB, hTz]
        exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
      have m2 : (ZKb2 Kdup Kroll) * (ts.prod * p ^ 2 + r * (p + 1) ^ (ZKb2 Kdup Kroll) + 1)
            + (ZKb2 Kdup Kroll) ≤ (ZKb2 Kdup Kroll) * B + (ZKb2 Kdup Kroll) := by
        rw [hB, hTz]
        exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
      have m3 : (ZKb3 Kswap) * (ts.prod * p ^ 2 + vsz (intList ts) + 1) + (ZKb3 Kswap)
          ≤ (ZKb3 Kswap) * B + (ZKb3 Kswap) := by
        rw [hB, hTz]
        exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
      have hZ : (ZKb1 Kcis Kpick Kprod Kdrop Kst Kswap Kfdiv Kconj) + (ZKb2 Kdup Kroll) + (ZKb3 Kswap)
          ≤ (ZKK Kcis Kpick Kprod Kdrop Kst Kswap Kfdiv Kconj Kdup Kroll) := by rw [ZKK]; omega
      have hZB : ((ZKb1 Kcis Kpick Kprod Kdrop Kst Kswap Kfdiv Kconj) + (ZKb2 Kdup Kroll) + (ZKb3 Kswap)) * B
          ≤ (ZKK Kcis Kpick Kprod Kdrop Kst Kswap Kfdiv Kconj Kdup Kroll) * B := Nat.mul_le_mul_right B hZ
      nlinarith [hb1, hb2, hb3, m1, m2, m3, hZB]
    refine le_trans ?_ hconv
    omega


end Work.Transform

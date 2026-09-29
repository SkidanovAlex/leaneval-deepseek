import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs
import Submission.Work.SynFFT.mrgPassDefs
import Submission.Work.SynFFT.mrgPassListKit
import Submission.Work.SynFFT.mrgPassCostLe
import Submission.Work.SynFFT.mrgBlocksApprox

/-!
# SynFFT: `HasMrgPass` — the interleave pass on the whole slice

`HasMrgPass` (kit2) asks for a word which, given the `t` coefficient vectors of a slice
(`2 * s ∣ t`), applies the *interleave* of scale `s` to every block of `2 * s` consecutive
vectors, at cost `O(t (r+1) (p+1))`.

The word is
`chunksOf (2s) ; mapList (block word HasMrgBlk) ; flatten`, with the scalar `2s` computed by
`pushVal 1 ; pick ; shl`.  The block word is applied with error `0` against the *exact* vector
function of the block (`vecFun`), so that the interleave — a pure permutation of the two halves
of the block — adds no error at all; the outer error `e` is then exactly the input error.

One subtlety of the statement: the cost `K t (r+1)(p+1) + K` must hold for *every* instance,
including the degenerate `t = 0` with an arbitrarily large `s` (the hypotheses `0 < s`,
`2s ∣ t`, `ws = []` are consistent).  On this input the required output *is* the input, so the
word branches on the top value being `nil` (`ifNil`): the `chunksOf` bound loses a factor
`isz (2s)`, which is unbounded in `s` when `t = 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.SynFFT

open HvdH

local infixr:68 " ;;; " => HvdH.Cmd.seq

/-! ## Composing `WordR` triples -/

theorem WordR_seq_fixed {main p q : Cmd} {A B : List Val} {R : List Val → Prop} {c1 c2 : ℕ}
    (h1 : WordR main p (fun vs => vs = A) (fun _ out => out = B) (fun _ => c1))
    (h2 : WordR main q (fun vs => vs = B) (fun _ out => R out) (fun _ => c2)) :
    WordR main (p ;;; q) (fun vs => vs = A) (fun _ out => R out) (fun _ => c1 + c2) := by
  intro vs hvs st Rg hR
  rw [hvs] at hR
  obtain ⟨mid, st2, n1, hmid, he1, hn1, hstk, hoth⟩ := h1 A rfl st Rg hR
  rw [hmid] at hstk
  obtain ⟨out, st3, n2, hP, he2, hn2, hstk2, hoth2⟩ := h2 B rfl st2 Rg hstk
  exact ⟨out, st3, n1 + n2, hP, Eval.seq he1 he2, Nat.add_le_add hn1 hn2, hstk2,
    fun k hk => by rw [hoth2 k hk, hoth k hk]⟩

theorem WordR_seq_Q {main p q : Cmd} {A : List Val} {Q : List Val → Prop} {R : List Val → Prop}
    {c1 c2 : ℕ}
    (h1 : WordR main p (fun vs => vs = A) (fun _ out => Q out) (fun _ => c1))
    (h2 : ∀ B, Q B → WordR main q (fun vs => vs = B) (fun _ out => R out) (fun _ => c2)) :
    WordR main (p ;;; q) (fun vs => vs = A) (fun _ out => R out) (fun _ => c1 + c2) := by
  intro vs hvs st Rg hR
  rw [hvs] at hR
  obtain ⟨mid, st2, n1, hmid, he1, hn1, hstk, hoth⟩ := h1 A rfl st Rg hR
  obtain ⟨out, st3, n2, hP, he2, hn2, hstk2, hoth2⟩ := h2 mid hmid mid rfl st2 Rg hstk
  exact ⟨out, st3, n1 + n2, hP, Eval.seq he1 he2, Nat.add_le_add hn1 hn2, hstk2,
    fun k hk => by rw [hoth2 k hk, hoth k hk]⟩

/-! ## Small list helpers -/

theorem blkVec_length (s : ℕ) (ws : List (List (ℤ × ℤ))) (b : ℕ)
    (h : (b + 1) * (2 * s) ≤ ws.length) : (blkVec s ws b).length = 2 * s := by
  have h' : b * (2 * s) + 2 * s ≤ ws.length := by
    have : (b + 1) * (2 * s) = b * (2 * s) + 2 * s := by ring
    omega
  rw [blkVec, List.length_take, List.length_drop]
  omega

theorem mem_blkVec {w : List (ℤ × ℤ)} {s b : ℕ} {ws : List (List (ℤ × ℤ))}
    (h : w ∈ blkVec s ws b) : w ∈ ws :=
  (List.drop_sublist (b * (2 * s)) ws).subset
    ((List.take_sublist (2 * s) (ws.drop (b * (2 * s)))).subset h)

theorem eq_of_getD_nil {l₁ l₂ : List Val} (h : l₁.length = l₂.length)
    (h' : ∀ i < l₁.length, l₁.getD i .nil = l₂.getD i .nil) : l₁ = l₂ := by
  apply List.ext_getElem h
  intro i h1 h2
  have := h' i h1
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

theorem mem_le_of_getD_le {l : List Val} {f : Val → ℕ} {B : ℕ}
    (h : ∀ i < l.length, f (l.getD i .nil) ≤ B) : ∀ x ∈ l, f x ≤ B := by
  intro x hx
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
  subst hi
  have := h i i.isLt
  simpa [List.getD_eq_getElem _ _ i.isLt] using this

/-- `Kiz + (K₁ * X + K₁) ≤ (K₁ + Kiz + 2 Kpv + 4) * X + (K₁ + Kiz + 2 Kpv + 4)` for `X ≥ 1`. -/
theorem ifNil_cost (Kiz K₁ Kpv t r p : ℕ) (ht : 0 < t) :
    Kiz + (K₁ * t * (r + 1) * (p + 1) + K₁) ≤
      (K₁ + Kiz + 2 * Kpv + 4) * t * (r + 1) * (p + 1) + (K₁ + Kiz + 2 * Kpv + 4) := by
  have hX : 1 ≤ t * (r + 1) * (p + 1) :=
    Nat.succ_le_of_lt (Nat.mul_pos (Nat.mul_pos ht (Nat.succ_pos r)) (Nat.succ_pos p))
  nlinarith [hX]

theorem hasMrgPass (hk : Work.SynFFT.KLib) (hi : HvdH.IntLib) (hl : HvdH.LayoutLib) (hf : HvdH.FxLib) (hm : Work.SynFFT.HasMrgBlk) : Work.SynFFT.HasMrgPass := by
  classical
  obtain ⟨blk, Kb, hblk⟩ := hm
  obtain ⟨mlC, Kml, hml⟩ := hk.mapList
  obtain ⟨pvP, Kpv, hpv⟩ := hk.pushVal
  obtain ⟨drP, Kdr, hdr⟩ := hk.drop
  obtain ⟨pkP, Kpk, hpk⟩ := hk.pick
  obtain ⟨izC, Kiz, hiz⟩ := hk.ifNil
  obtain ⟨chP, Kch, hch⟩ := hl.chunksOf
  obtain ⟨flP, Kfl, hfl⟩ := hl.flatten
  obtain ⟨shlP, Kshl, hshl0⟩ := hi.shl
  obtain ⟨hkit1, hkit2, hkit3, hkit4, hkit5, hkit6, hkit7, hkit8, hkit9, hkit10, hkit11, hkit12⟩ :=
    mrgPassListKit
  obtain ⟨K₁, hK₁⟩ := mrgPassCostLe Kpv Kpk Kshl Kch Kdr Kb Kml Kfl
  let body : Cmd := Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq
    (pvP (Val.int 1)) (pkP 2)) shlP) chP) (mlC blk)) flP
  refine ⟨izC (pvP Val.nil) body, K₁ + Kiz + 2 * Kpv + 4, ?_⟩
  intro main p r t s ws u e rest hs hdiv hlen hinD happ
  let v : Val := ofList (cvecs ws)
  let rest6 : List Val := Val.int (s : ℤ) :: Val.int (r : ℤ) :: Val.int (p : ℤ) :: rest
  let Vsz : ℕ := vsz (ofList (cvecs ws))
  let Lb : ℕ := 2 * s * (13 * (r + 1) * (p + 1) + 1) + 1
  let cblk : ℕ := Kb * s * (r + 1) * (p + 1) + Kb
  let Q : List Val → Prop := fun out => ∃ ws' : List (List (ℤ × ℤ)),
      out = ofList (cvecs ws') :: Val.int (s : ℤ) :: Val.int (r : ℤ) :: Val.int (p : ℤ) :: rest ∧
      ws'.length = t ∧ (∀ w ∈ ws', InDiscVec p r w) ∧ ApproxSL p r t ws' (mrgN r s u) e
  change WordR main (izC (pvP Val.nil) body) (fun vs => vs = v :: rest6)
    (fun _ out => Q out)
    (fun _ => (K₁ + Kiz + 2 * Kpv + 4) * t * (r + 1) * (p + 1) + (K₁ + Kiz + 2 * Kpv + 4))
  by_cases hnil : v = Val.nil
  · -- ===== degenerate case: the input list is empty (t = 0)
    have hh1 : ofList (cvecs ws) = ofList ([] : List Val) := by
      show v = Val.nil
      exact hnil
    have hws : ws = [] := by
      have h2 : cvecs ws = ([] : List Val) := hkit3 _ _ hh1
      simpa [cvecs] using h2
    have ht0 : t = 0 := by rw [← hlen, hws]; rfl
    have hq1 : v = Val.nil → WordR main (pvP Val.nil) (fun vs => vs = rest6)
        (fun _ out => Q out) (fun _ => Kpv * (vsz Val.nil + 1)) := by
      intro hv
      refine MrgKit.WordR_weaken
        (MrgKit.pushStep (hpv main) Val.nil rest6 (Kpv * (vsz Val.nil + 1)) le_rfl)
        (fun vs hvs => hvs) ?_ (fun vs _ => le_rfl)
      intro vs out hvs hout
      rw [hout]
      dsimp only [Q]
      refine ⟨[], ?_, ?_, ?_, ?_⟩
      · rfl
      · show ([] : List (List (ℤ × ℤ))).length = t
        rw [ht0]; rfl
      · intro w hw; simp at hw
      · refine ⟨?_, ?_⟩
        · show ([] : List (List (ℤ × ℤ))).length = t
          rw [ht0]; rfl
        · intro q hq c
          omega
    have hq2 : v ≠ Val.nil → WordR main body (fun vs => vs = v :: rest6)
        (fun _ out => Q out) (fun _ => 0) := fun hne => absurd hnil hne
    have hif := hiz main (pvP Val.nil) body v rest6 Q Q (Kpv * (vsz Val.nil + 1)) 0 hq1 hq2
    refine MrgKit.WordR_weaken hif (fun vs hvs => hvs) ?_ ?_
    · intro vs out hvs hq
      exact hq.1 hnil
    · intro vs _
      rw [ht0, max_eq_left (Nat.zero_le _)]
      simp only [Nat.mul_zero, Nat.zero_mul]
      have hvv : vsz Val.nil = 1 := rfl
      rw [hvv]
      omega
  · -- ===== main case
    have ht : 0 < t := by
      by_contra h
      have h0 : t = 0 := Nat.eq_zero_of_not_pos h
      have hws : ws = [] := by
        have h1 : ws.length = 0 := by rw [hlen, h0]
        exact List.eq_nil_of_length_eq_zero h1
      exact hnil (by show ofList (cvecs ws) = Val.nil; rw [hws]; rfl)
    have hLb1 : Lb + 1 = 2 * s * (13 * (r + 1) * (p + 1) + 1) + 2 := by
      dsimp only [Lb]; try ring
    have hVle : Vsz ≤ t * (13 * (r + 1) * (p + 1) + 1) + 1 := by
      dsimp only [Vsz]; exact hkit12 p r t ws hlen hinD
    let D1 : ℕ := Kpv * (isz (1 : ℤ) + 1)
    let D2 : ℕ := Kpk * 3 * (isz (1 : ℤ) + Vsz + isz (s : ℤ) + 1)
    let D3 : ℕ := Kshl * (isz (s : ℤ) + 1 + isz (1 : ℤ))
    let D4 : ℕ := Kch * (Vsz + (t / (2 * s) + 1) * isz ((2 * s : ℕ) : ℤ) + 1)
    let D5 : ℕ := Kdr * (isz ((2 * s : ℕ) : ℤ) + 1)
    let D6 : ℕ := (t / (2 * s)) * (cblk + Kml * (2 * s * (13 * (r + 1) * (p + 1) + 1) + 2)) + Kml
    let D7 : ℕ := Kfl * ((t / (2 * s)) * (2 * s * (13 * (r + 1) * (p + 1) + 1) + 2) + 2)
    have hbody : WordR main body (fun vs => vs = v :: rest6) (fun _ out => Q out)
        (fun _ => K₁ * t * (r + 1) * (p + 1) + K₁) := by
      have hstep1 : WordR main (pvP (Val.int 1)) (fun vs => vs = v :: rest6)
          (fun _ out => out = Val.int 1 :: v :: rest6) (fun _ => D1) := by
        dsimp only [D1]
        exact MrgKit.pushStep (hpv main) (Val.int 1) (v :: rest6) _
          (by rw [MrgKit.vsz_int'])
      have hstep2 : WordR main (pkP 2) (fun vs => vs = Val.int 1 :: v :: rest6)
          (fun _ out => out = Val.int (s : ℤ) :: Val.int 1 :: v :: rest6) (fun _ => D2) := by
        dsimp only [D2]
        refine MrgKit.WordR_weaken
          (MrgKit.pickStep (hpk main) 2 (Val.int 1 :: v :: rest6) (by dsimp only [rest6]; simp) _
            (by
              dsimp only [Vsz, v]
              rw [show Kpk * (2 + 1) = Kpk * 3 from by ring]
              simp only [rest6, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
                List.sum_cons, List.sum_nil, MrgKit.vsz_int']
              apply Nat.mul_le_mul_left
              omega))
          (fun vs hvs => hvs) ?_ (fun vs _ => le_rfl)
        intro vs out hvs hq
        rw [hq]
        simp only [rest6, List.getD_cons_succ, List.getD_cons_zero]
      have hstep3 : WordR main shlP (fun vs => vs = Val.int (s : ℤ) :: Val.int 1 :: v :: rest6)
          (fun _ out => out = Val.int ((2 * s : ℕ) : ℤ) :: v :: rest6) (fun _ => D3) := by
        dsimp only [D3]
        have h := hshl0 main
        unfold BinOp at h
        refine MrgKit.WordR_weaken h ?_ ?_ ?_
        · intro vs hvs
          rw [hvs]
          exact ⟨s, 1, v :: rest6, rfl, by norm_num⟩
        · intro vs out hvs hq
          rw [hvs] at hq
          obtain ⟨a, b, rr, heq, hout⟩ := hq
          simp only [List.cons.injEq, Val.int.injEq] at heq
          obtain ⟨rfl, rfl, rfl⟩ := heq
          rw [hout]
          have hii : (Val.int ((s : ℤ) * 2 ^ ((1 : ℤ).toNat)) : Val) =
              Val.int ((2 * s : ℕ) : ℤ) := by
            rw [Val.int.injEq]
            push_cast
            ring
          rw [hii]
        · intro vs hvs
          rw [hvs]
          show Kshl * (isz (s : ℤ) + (1 : ℤ).toNat + isz (1 : ℤ)) ≤
            Kshl * (isz (s : ℤ) + 1 + isz (1 : ℤ))
          norm_num
      have hstep4 : WordR main chP (fun vs => vs = Val.int ((2 * s : ℕ) : ℤ) :: v :: rest6)
          (fun _ out => out = ofList (chunkVals_xmrgPassDefs s ws) :: rest6) (fun _ => D4) := by
        dsimp only [D4]
        have hchunk : (List.range ((cvecs ws).length / (2 * s))).map
            (fun i => ofList (((cvecs ws).drop (i * (2 * s))).take (2 * s))) = chunkVals_xmrgPassDefs s ws := by
          have hcl : (cvecs ws).length = t := by dsimp only [cvecs]; rw [List.length_map, hlen]
          have hfun : (fun i => ofList (((cvecs ws).drop (i * (2 * s))).take (2 * s))) =
              (fun b => ofList (cvecs (blkVec s ws b))) := by
            funext i
            simp only [blkVec]
            rw [← cvecs_drop, ← cvecs_take]
          rw [hcl, hfun]
          simp only [chunkVals_xmrgPassDefs, hlen]
        have h := hch main (2 * s) (cvecs ws) (by omega)
          (by dsimp only [cvecs]; rw [List.length_map, hlen]; exact hdiv)
        refine MrgKit.WordR_weaken h ?_ ?_ ?_
        · intro vs hvs
          exact ⟨rest6, by rw [hvs]; try rfl⟩
        · intro vs out hvs hq
          obtain ⟨rr, heq, hout⟩ := hq
          have hrr : rr = rest6 := by
            have h0 : Val.int ((2 * s : ℕ) : ℤ) :: v :: rest6 =
                Val.int ((2 * s : ℕ) : ℤ) :: ofList (cvecs ws) :: rr := by
              rw [hvs] at heq
              exact heq
            have h1 : v :: rest6 = ofList (cvecs ws) :: rr := ((List.cons.injEq _ _ _ _).mp h0).2
            exact ((List.cons.injEq _ _ _ _).mp h1.symm).2
          subst hrr
          rw [hout, hchunk]
        · intro vs _
          rw [show vsz (ofList (cvecs ws)) = Vsz from rfl,
            show (cvecs ws).length = t from by dsimp only [cvecs]; rw [List.length_map, hlen]]
      have hcB : chunkVals_xmrgPassDefs s ws =
          (List.range (t / (2 * s))).map (fun b => ofList (cvecs (blkVec s ws b))) := by
        simp only [chunkVals_xmrgPassDefs, hlen]
      have hclen : (chunkVals_xmrgPassDefs s ws).length = t / (2 * s) := by
        rw [hcB, List.length_map, List.length_range]
      have hstep6 : WordR main (mlC blk) (fun vs => vs = ofList (chunkVals_xmrgPassDefs s ws) :: rest6)
          (fun _ out => ∃ ys, out = ofList ys :: rest6 ∧
            List.Forall₂ (blkRel p r s) (chunkVals_xmrgPassDefs s ws) ys) (fun _ => D6) := by
        dsimp only [D6]
        have hxs : ∀ x ∈ chunkVals_xmrgPassDefs s ws, blkPre p r s x ∧ vsz x ≤ Lb := by
          intro x hx
          rw [hcB] at hx
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
          have hbB : b < t / (2 * s) := List.mem_range.mp hb
          have hb2 : (b + 1) * (2 * s) ≤ t := by
            have h1 : b + 1 ≤ t / (2 * s) := by omega
            calc (b + 1) * (2 * s) ≤ (t / (2 * s)) * (2 * s) := Nat.mul_le_mul_right _ h1
              _ = t := Nat.div_mul_cancel hdiv
          have hbl : (blkVec s ws b).length = 2 * s := blkVec_length s ws b (by rw [hlen]; exact hb2)
          have hdisc : ∀ w ∈ blkVec s ws b, InDiscVec p r w := fun w hw => hinD w (mem_blkVec hw)
          exact ⟨⟨blkVec s ws b, rfl, hbl, hdisc⟩, by
            dsimp only [Lb]; exact hkit11 p r s (blkVec s ws b) hbl hdisc⟩
        have hq' : ∀ x, blkPre p r s x → WordR main blk (fun vs => vs = x :: rest6)
            (fun _ out => ∃ y, out = y :: rest6 ∧ blkRel p r s x y ∧ vsz y ≤ Lb)
            (fun _ => cblk) := by
          intro x hx
          dsimp only [blkPre] at hx
          obtain ⟨vv, rfl, hvlen, hvinD⟩ := hx
          have happ0 : ApproxSL p r (2 * s) vv (vecFun p r vv) 0 := by
            refine ⟨hvlen, ?_⟩
            intro q hq c
            simp only [vecFun]
            simp
          have hblk' := hblk main p r s vv (vecFun p r vv) 0 rest hs hvlen hvinD happ0
          refine MrgKit.WordR_weaken hblk' ?_ ?_ ?_
          · intro vs hvs
            rw [hvs]
          · intro vs out hvs hq
            obtain ⟨ws', hout, hlen', hdisc', hap'⟩ := hq
            exact ⟨ofList (cvecs ws'), by rw [hout], ⟨vv, ws', rfl, rfl, hvlen, hlen', hdisc', hap'⟩,
              by dsimp only [Lb]; exact hkit11 p r s ws' hlen' hdisc'⟩
          · intro vs _
            exact le_rfl
        have hml' := hml main blk rest6 (blkPre p r s) (blkRel p r s) cblk Lb hq'
          (chunkVals_xmrgPassDefs s ws) hxs
        refine MrgKit.WordR_weaken hml' (fun vs hvs => hvs) (fun vs out hvs hq => hq) ?_
        intro vs _
        rw [hclen, hLb1]
      have hstep7 : ∀ Bv, (∃ ys, Bv = ofList ys :: rest6 ∧
            List.Forall₂ (blkRel p r s) (chunkVals_xmrgPassDefs s ws) ys) →
          WordR main flP (fun vs => vs = Bv) (fun _ out => Q out) (fun _ => D7) := by
        intro Bv hBv
        obtain ⟨ys, hBv', hF2⟩ := hBv
        have hyslen : ys.length = t / (2 * s) := by rw [← hF2.length_eq, hclen]
        have hVex : ∀ b < t / (2 * s), ∃ v' : List (List (ℤ × ℤ)),
            ys.getD b .nil = ofList (cvecs v') ∧ v'.length = 2 * s ∧
            (∀ w ∈ v', InDiscVec p r w) ∧
            ApproxSL p r (2 * s) v' (mrgN r s (vecFun p r (blkVec s ws b))) 0 := by
          intro b hb
          have hbcl : b < (chunkVals_xmrgPassDefs s ws).length := by rw [hclen]; exact hb
          have hQ := hkit6 (blkRel p r s) (chunkVals_xmrgPassDefs s ws) ys hF2.length_eq hF2 Val.nil Val.nil b hbcl
          rw [hcB] at hQ
          rw [hkit2 (fun b => ofList (cvecs (blkVec s ws b))) Val.nil (t / (2 * s)) b hb] at hQ
          dsimp only [blkRel] at hQ
          obtain ⟨v₁, v', hx, hy, -, hv'len, hv'disc, hv'ap⟩ := hQ
          have hv₁ : blkVec s ws b = v₁ := hkit4 _ _ (hkit3 _ _ hx)
          exact ⟨v', hy, hv'len, hv'disc, by rwa [← hv₁] at hv'ap⟩
        let Vf : ℕ → List (List (ℤ × ℤ)) := fun b => extractV p r s ws ys b
        have hVs : ∀ b < t / (2 * s), ys.getD b .nil = ofList (cvecs (Vf b)) ∧
            (Vf b).length = 2 * s ∧ (∀ w ∈ Vf b, InDiscVec p r w) ∧
            ApproxSL p r (2 * s) (Vf b) (mrgN r s (vecFun p r (blkVec s ws b))) 0 :=
          fun b hb => by dsimp only [Vf]; exact extractV_spec p r s ws ys b (hVex b hb)
        let xss : List (List Val) := (List.range (t / (2 * s))).map (fun b => cvecs (Vf b))
        have hxsslen : xss.length = ys.length := by
          dsimp only [xss]; rw [List.length_map, List.length_range, hyslen]
        have hxss : xss.map ofList = ys := by
          refine eq_of_getD_nil (by rw [List.length_map]; exact hxsslen) ?_
          intro i hi
          have hi' : i < t / (2 * s) := by
            simp only [xss, List.length_map, List.length_range] at hi
            exact hi
          have h1 : xss.getD i [] = cvecs (Vf i) := by
            dsimp only [xss]
            exact getD_map_range' (fun b => cvecs (Vf b)) [] hi'
          have h2 : (xss.map ofList).getD i .nil = ofList (xss.getD i []) := by
            rw [show (Val.nil : Val) = ofList ([] : List Val) from rfl, List.getD_map]
          rw [h2, h1]
          exact ((hVs i hi').1).symm
        have hysle : ∀ y ∈ ys, vsz y ≤ Lb := by
          refine mem_le_of_getD_le ?_
          intro i hi
          have hi' : i < t / (2 * s) := by rw [← hyslen]; exact hi
          rw [(hVs i hi').1]
          dsimp only [Lb]
          exact hkit11 p r s (Vf i) (hVs i hi').2.1 (hVs i hi').2.2.1
        dsimp only [D7]
        have hfl' := hfl main xss
        refine MrgKit.WordR_weaken hfl' ?_ ?_ ?_
        · intro vs hvs
          exact ⟨rest6, by rw [hvs, hBv', hxss]; try rfl⟩
        · intro vs out hvs hq
          obtain ⟨rr, heq, hout⟩ := hq
          have hrr : rr = rest6 := by
            have h1 : ofList (xss.map ofList) :: rr = ofList ys :: rest6 := by
              rw [hvs, hBv'] at heq
              exact heq.symm
            rw [hxss] at h1
            exact ((List.cons.injEq _ _ _ _).mp h1).2
          subst hrr
          dsimp only [Q]
          have hcvec : xss.flatten = cvecs (((List.range (t / (2 * s))).map Vf).flatten) := by
            dsimp only [xss, cvecs]
            rw [List.map_flatten, List.map_map]
            rfl
          refine ⟨((List.range (t / (2 * s))).map Vf).flatten, ?_, ?_, ?_, ?_⟩
          · rw [hout, hcvec]
          · refine (hkit10 (t / (2 * s)) s Vf ?_).trans (Nat.div_mul_cancel hdiv)
            intro b hb
            exact (hVs b hb).2.1
          · intro w hw
            obtain ⟨b, hb, hwb⟩ := hkit9 (t / (2 * s)) Vf w hw
            exact (hVs b hb).2.2.1 w hwb
          · exact mrgBlocksApprox p r t s ws u e Vf hs hdiv hlen happ
              (fun b hb => (hVs b hb).2.1) (fun b hb => (hVs b hb).2.2.2)
        · intro vs _
          rw [hxss]
          have h2 : vsz (ofList ys) + 1 ≤
              (t / (2 * s)) * (2 * s * (13 * (r + 1) * (p + 1) + 1) + 2) + 2 := by
            have h3 : vsz (ofList ys) + 1 ≤ ys.length * (Lb + 1) + 2 := by
              have := MrgKit.vsz_ofList_le_of_bound ys Lb ys.length hysle le_rfl
              omega
            rw [hyslen, hLb1] at h3
            exact h3
          exact Nat.mul_le_mul_left _ h2
      have h12 : WordR main (pvP (Val.int 1) ;;; pkP 2) (fun vs => vs = v :: rest6)
          (fun _ out => out = Val.int (s : ℤ) :: Val.int 1 :: v :: rest6) (fun _ => D1 + D2) :=
        WordR_seq_fixed hstep1 hstep2
      have h123 : WordR main ((pvP (Val.int 1) ;;; pkP 2) ;;; shlP) (fun vs => vs = v :: rest6)
          (fun _ out => out = Val.int ((2 * s : ℕ) : ℤ) :: v :: rest6) (fun _ => D1 + D2 + D3) :=
        WordR_seq_fixed h12 hstep3
      have h1234 : WordR main (((pvP (Val.int 1) ;;; pkP 2) ;;; shlP) ;;; chP)
          (fun vs => vs = v :: rest6) (fun _ out => out = ofList (chunkVals_xmrgPassDefs s ws) :: rest6)
          (fun _ => D1 + D2 + D3 + D4) := WordR_seq_fixed h123 hstep4
      have h12345 : WordR main ((((pvP (Val.int 1) ;;; pkP 2) ;;; shlP) ;;; chP) ;;; mlC blk)
          (fun vs => vs = v :: rest6)
          (fun _ out => ∃ ys, out = ofList ys :: rest6 ∧
            List.Forall₂ (blkRel p r s) (chunkVals_xmrgPassDefs s ws) ys)
          (fun _ => D1 + D2 + D3 + D4 + D6) := WordR_seq_fixed h1234 hstep6
      have h123456 : WordR main body (fun vs => vs = v :: rest6) (fun _ out => Q out)
          (fun _ => D1 + D2 + D3 + D4 + D6 + D7) := by
        dsimp only [body]
        exact WordR_seq_Q h12345 hstep7
      refine MrgKit.WordR_weaken h123456 (fun vs hvs => hvs) (fun vs out hvs hq => hq) ?_
      intro vs _
      have hcost : D1 + D2 + D3 + D4 + D6 + D7 ≤ K₁ * t * (r + 1) * (p + 1) + K₁ := by
        have hcl := hK₁ Vsz t s r p hs ht hdiv hVle
        dsimp only [D1, D2, D3, D4, D6, D7, cblk] at hcl ⊢
        omega
      exact hcost
    have hq1 : v = Val.nil → WordR main (pvP Val.nil) (fun vs => vs = rest6)
        (fun _ out => Q out) (fun _ => 0) := fun hv => absurd hv hnil
    have hq2 : v ≠ Val.nil → WordR main body (fun vs => vs = v :: rest6)
        (fun _ out => Q out) (fun _ => K₁ * t * (r + 1) * (p + 1) + K₁) := fun _ => hbody
    have hif := hiz main (pvP Val.nil) body v rest6 Q Q 0 (K₁ * t * (r + 1) * (p + 1) + K₁) hq1 hq2
    refine MrgKit.WordR_weaken hif (fun vs hvs => hvs) ?_ ?_
    · intro vs out hvs hq
      exact hq.2 hnil
    · intro vs _
      rw [max_eq_right (Nat.zero_le _)]
      exact ifNil_cost Kiz K₁ Kpv t r p ht

end Work.SynFFT

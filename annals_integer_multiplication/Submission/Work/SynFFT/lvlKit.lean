import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs
import Submission.Work.SynFFT.lvlAllGetD

/-!
# `Work.SynFFT.lvlKit`: vocabulary and pure list/size facts for `HasLvlPass`

`HasLvlPass` (`Submission/Work/SynFFT/kit2.lean`) asks for a word that, given the `t` coefficient
vectors of one slice, applies the level-`m` butterfly pass block by block.  The natural program is
`chunksOf m ; (pair each chunk with the parameter value) ; fold (block word) ; reverse ; flatten`.

This file fixes the vocabulary used by the assembled proof and collects the pure list and size
facts it needs:

* `cws m ws b` — the `m` coefficient vectors of the `b`-th block of `ws`;
* `blkV m ws b` — its value (`ofList (cvecs ·)`);
* `blkArr u m b` — the block `b` of an array `u`, as an array (so that `lvlN`'s block-locality
  `lvlNBlock` applies);
* `prepV` — the value `ofList [int m, int sh, int sgn, int r, int p]` carrying the five scalar
  parameters into every element of the fold.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.SynFFT

open HvdH

/-- The `b`-th block (`m` consecutive coefficient vectors) of `ws`. -/
def cws (m : ℕ) (ws : List (List (ℤ × ℤ))) (b : ℕ) : List (List (ℤ × ℤ)) :=
  (ws.drop (b * m)).take m

/-- The value of the `b`-th block: the list of its `m` coefficient vectors. -/
def blkV (m : ℕ) (ws : List (List (ℤ × ℤ))) (b : ℕ) : Val := ofList (cvecs (cws m ws b))

/-- Block `b` of an array `u`, as an array. -/
noncomputable def blkArr (r : ℕ) (u : Arr r) (m b : ℕ) : Arr r := fun j c => u (b * m + j) c

/-- The value `ofList [int m, int sh, int sgn, int r, int p]`: the five scalar parameters, carried
as one value inside every element of the fold. -/
def prepV (m sh : ℕ) (sgn : ℤ) (r p : ℕ) : Val :=
  ofList [Val.int (m : ℤ), Val.int (sh : ℤ), Val.int sgn, Val.int (r : ℤ), Val.int (p : ℤ)]

/-! ## Reading blocks -/

/-- Reading a block at an offset `< m` reads `ws` at the corresponding flat position. -/
theorem cws_getD (m : ℕ) (ws : List (List (ℤ × ℤ))) (b j : ℕ) (hj : j < m) :
    (cws m ws b).getD j [] = ws.getD (b * m + j) [] := by
  rw [cws]
  by_cases h : b * m + j < ws.length
  · have h1 : j < ((ws.drop (b * m)).take m).length := by
      simp only [List.length_take, List.length_drop]; omega
    rw [List.getD_eq_getElem _ _ h1, List.getElem_take, List.getElem_drop,
      List.getD_eq_getElem _ _ h]
  · have h1 : ((ws.drop (b * m)).take m).length ≤ j := by
      simp only [List.length_take, List.length_drop]; omega
    rw [List.getD_eq_default _ _ h1, List.getD_eq_default _ _ (by omega)]

theorem cws_length_le (m : ℕ) (ws : List (List (ℤ × ℤ))) (b : ℕ) : (cws m ws b).length ≤ m := by
  rw [cws, List.length_take]; exact min_le_left _ _

theorem cws_length (m : ℕ) (ws : List (List (ℤ × ℤ))) {b : ℕ} (hb : (b + 1) * m ≤ ws.length) :
    (cws m ws b).length = m := by
  have hbm : (b + 1) * m = b * m + m := Nat.succ_mul b m
  rw [hbm] at hb
  rw [cws, List.length_take, List.length_drop, Nat.min_eq_left]
  omega

/-! ## Size bound for the value of a block -/

/-- The value of a block is at most `15 (m+1)(r+1)(p+1)` glyphs long. -/
theorem vsz_blkV_le (p r m : ℕ) (ws : List (List (ℤ × ℤ))) (b : ℕ)
    (hlen : (cws m ws b).length = m) (h : ∀ w ∈ cws m ws b, InDiscVec p r w) :
    vsz (blkV m ws b) ≤ 15 * (m + 1) * (r + 1) * (p + 1) := by
  have h1 : vsz (blkV m ws b)
      = (cws m ws b).length + ((cws m ws b).map (fun w => vsz (cvecVal w))).sum + 1 := by
    rw [blkV, cvecs, MrgKit.vsz_ofList, List.length_map, List.map_map]
    rfl
  have h2 : ∀ w ∈ cws m ws b, vsz (cvecVal w) ≤ 13 * (r + 1) * (p + 1) :=
    fun w hw => MrgKit.vsz_cvecVal_le p r w (h w hw).1 (h w hw).2
  have h3 : ((cws m ws b).map (fun w => vsz (cvecVal w))).sum
      ≤ (cws m ws b).length * (13 * (r + 1) * (p + 1)) :=
    MrgKit.sum_le_of_forall _ _ _ h2
  have hA : 0 < (r + 1) * (p + 1) := by positivity
  rw [h1, hlen] at *
  nlinarith [hA]

/-- A block of an approximation approximates the corresponding block of the array. -/
theorem approxSL_block (p r t m : ℕ) (u : Arr r) (ws : List (List (ℤ × ℤ))) (e : ℝ) (b : ℕ)
    (hb : (b + 1) * m ≤ t) (h : ApproxSL p r t ws u e) :
    ApproxSL p r m (cws m ws b) (blkArr r u m b) e := by
  have ht : ws.length = t := h.1
  have hbm : (b + 1) * m = b * m + m := Nat.succ_mul b m
  refine ⟨cws_length m ws (by rw [ht]; exact hb), ?_⟩
  intro q hq c
  have hq' : b * m + q < t := by rw [← ht, hbm] at hb; omega
  have h2 := h.2 (b * m + q) hq' c
  rw [cws_getD m ws b q hq]
  exact h2

/-! ## Reading the accumulated output list -/

/-- Reading the reversed list at `b` reads the original at its mirror index. -/
theorem rev_getD {W : List (List (List (ℤ × ℤ)))} (b : ℕ) (hb : b < W.length) :
    (W.reverse).getD b [] = W.getD (W.length - 1 - b) [] := by
  have h1 : b < (W.reverse).length := by rw [List.length_reverse]; exact hb
  rw [List.getD_eq_getElem _ _ h1, List.getElem_reverse h1,
    List.getD_eq_getElem _ _ (by omega)]

/-- Reading the flattened accumulated list at flat index `b*m + j` (with `j < m`) reads the
corresponding block at `j`. -/
theorem flatten_getD {m : ℕ} {W : List (List (List (ℤ × ℤ)))}
    (hW : ∀ w ∈ W, w.length = m) (b j : ℕ) (hj : j < m) :
    (W.reverse).flatten.getD (b * m + j) [] = ((W.reverse).getD b []).getD j [] :=
  getD_flatten_eq (n := m) W.reverse [] (fun l hl => hW l (List.mem_reverse.mp hl)) b j hj

/-- Block-locality of `lvlN`: the level-`m` pass at a flat position only looks at the position's
own block. -/
theorem lvlNBlock (r m : ℕ) (sgn : ℤ) (a : Arr r) (hm : 0 < m) (b j : ℕ) (hj : j < m) :
    lvlN r m sgn a (b * m + j) = lvlN r m sgn (fun j' => a (b * m + j')) j := by
  funext c
  have hmod : (b * m + j) % m = j := by
    rw [Nat.add_comm (b * m) j, Nat.mul_comm b m, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hj]
  simp only [lvlN, hmod, Nat.mod_eq_of_lt hj]
  rcases lt_or_ge j (m / 2) with h | h
  · rw [if_pos h, if_pos h]
    rw [show b * m + j + m / 2 = b * m + (j + m / 2) by omega]
  · rw [if_neg (by omega), if_neg (by omega)]
    rw [show b * m + j - m / 2 = b * m + (j - m / 2) by omega]

/-! ## WordR step lemmas (the `MrgKit` pattern) for the four library words used -/

/-- Concrete form of `LayoutLib.chunksOf`. -/
theorem chunksOfStep {main : Cmd} {csP : Cmd} {Kcs : ℕ}
    (h : ∀ (m : ℕ) (xs : List Val), 1 ≤ m → m ∣ xs.length → WordR main csP
      (fun vs => ∃ rest, vs = .int (m : ℤ) :: ofList xs :: rest)
      (fun vs out => ∃ rest, vs = .int (m : ℤ) :: ofList xs :: rest ∧
        out = ofList ((List.range (xs.length / m)).map fun i => ofList ((xs.drop (i * m)).take m)) :: rest)
      (fun _ => Kcs * (vsz (ofList xs) + (xs.length / m + 1) * isz (m : ℤ) + 1)))
    (m : ℕ) (xs : List Val) (hm : 1 ≤ m) (hd : m ∣ xs.length) (t : List Val) (D : ℕ)
    (hD : Kcs * (vsz (ofList xs) + (xs.length / m + 1) * isz (m : ℤ) + 1) ≤ D) :
    WordR main csP (fun vs => vs = .int (m : ℤ) :: ofList xs :: t)
      (fun _ out => out = ofList ((List.range (xs.length / m)).map fun i =>
        ofList ((xs.drop (i * m)).take m)) :: t)
      (fun _ => D) := by
  refine MrgKit.WordR_conseqC (h m xs hm hd) ⟨t, rfl⟩ ?_ hD
  intro out hout
  obtain ⟨r, hr1, hr2⟩ := hout
  simp only [List.cons.injEq] at hr1
  obtain ⟨-, -, rfl⟩ := hr1
  exact hr2

/-- Concrete form of the `foldList` combinator of `KLib`. -/
theorem foldStep {main : Cmd} {foldP : Cmd → Cmd} {Kfl : ℕ}
    (h : ∀ (q : Cmd) (xs : List Val) (I : ℕ → List Val → Prop) (c L : ℕ),
      (∀ x ∈ xs, vsz x ≤ L) →
      (∀ i acc, i < xs.length → I i acc → WordR main q
        (fun vs => vs = xs.getD i .nil :: acc)
        (fun _ out => I (i + 1) out) (fun _ => c)) →
      WordR main (foldP q) (fun vs => ∃ acc, vs = ofList xs :: acc ∧ I 0 acc)
        (fun _ out => I xs.length out) (fun _ => xs.length * (c + Kfl * (L + 1)) + Kfl))
    (q : Cmd) (xs : List Val) (I : ℕ → List Val → Prop) (c L : ℕ)
    (hL : ∀ x ∈ xs, vsz x ≤ L)
    (hq : ∀ i acc, i < xs.length → I i acc → WordR main q
      (fun vs => vs = xs.getD i .nil :: acc)
      (fun _ out => I (i + 1) out) (fun _ => c))
    (D : ℕ) (hD : xs.length * (c + Kfl * (L + 1)) + Kfl ≤ D) :
    WordR main (foldP q) (fun vs => ∃ acc, vs = ofList xs :: acc ∧ I 0 acc)
      (fun _ out => I xs.length out) (fun _ => D) :=
  MrgKit.WordR_weaken (h q xs I c L hL hq) (fun _ hvs => hvs)
    (fun _ _ _ hQ => hQ) (fun _ _ => hD)

/-- Concrete form of `LayoutLib.reverse`. -/
theorem reverseStep {main : Cmd} {revP : Cmd} {Krev : ℕ}
    (h : ∀ (xs : List Val), WordR main revP
      (fun vs => ∃ rest, vs = ofList xs :: rest)
      (fun vs out => ∃ rest, vs = ofList xs :: rest ∧ out = ofList xs.reverse :: rest)
      (fun _ => Krev * (vsz (ofList xs) + 1)))
    (xs : List Val) (t : List Val) (D : ℕ) (hD : Krev * (vsz (ofList xs) + 1) ≤ D) :
    WordR main revP (fun vs => vs = ofList xs :: t) (fun _ out => out = ofList xs.reverse :: t)
      (fun _ => D) := by
  refine MrgKit.WordR_conseqC (h xs) ⟨t, rfl⟩ ?_ hD
  intro out hout
  obtain ⟨r, hr1, hr2⟩ := hout
  simp only [List.cons.injEq] at hr1
  obtain ⟨-, rfl⟩ := hr1
  exact hr2

/-- Concrete form of `LayoutLib.flatten`. -/
theorem flattenStep {main : Cmd} {fltP : Cmd} {Kflt : ℕ}
    (h : ∀ (xss : List (List Val)), WordR main fltP
      (fun vs => ∃ rest, vs = ofList (xss.map ofList) :: rest)
      (fun vs out => ∃ rest, vs = ofList (xss.map ofList) :: rest ∧
        out = ofList xss.flatten :: rest)
      (fun _ => Kflt * (vsz (ofList (xss.map ofList)) + 1)))
    (xss : List (List Val)) (t : List Val) (D : ℕ)
    (hD : Kflt * (vsz (ofList (xss.map ofList)) + 1) ≤ D) :
    WordR main fltP (fun vs => vs = ofList (xss.map ofList) :: t)
      (fun _ out => out = ofList xss.flatten :: t) (fun _ => D) := by
  refine MrgKit.WordR_conseqC (h xss) ⟨t, rfl⟩ ?_ hD
  intro out hout
  obtain ⟨r, hr1, hr2⟩ := hout
  simp only [List.cons.injEq] at hr1
  obtain ⟨-, rfl⟩ := hr1
  exact hr2

/-- The total number of coefficient vectors in a list of blocks of length `m`. -/
theorem sum_map_length_eq (W : List (List (List (ℤ × ℤ)))) (m : ℕ)
    (hw : ∀ w ∈ W, w.length = m) : (W.map List.length).sum = W.length * m := by
  induction W with
  | nil => simp
  | cons a l ih =>
    have ha : a.length = m := hw a (by simp)
    have hl : ∀ w ∈ l, w.length = m := fun w hw' => hw w (by simp [hw'])
    simp only [List.map_cons, List.sum_cons, List.length_cons, ha, ih hl, Nat.succ_mul]
    omega

/-! ## The final `ApproxSL` assembly -/

/-- The per-block bounds on the accumulated output list give the `ApproxSL` of the flattened,
put-back-in-order list against `lvlN r m sgn u`. -/
theorem approxSLOfBlocks {p r t m n : ℕ} {u : Arr r} {e : ℝ} (sgn : ℤ)
    {W : List (List (List (ℤ × ℤ)))}
    (hm : 0 < m) (ht : n * m = t) (hW : W.length = n) (hw : ∀ w ∈ W, w.length = m)
    (hblock : ∀ b < n, ApproxSL p r m (W.getD (n - 1 - b) [])
      (lvlN r m sgn (blkArr r u m b)) (e + 1)) :
    ApproxSL p r t ((W.reverse).flatten) (lvlN r m sgn u) (e + 1) := by
  constructor
  · rw [List.length_flatten, List.map_reverse, List.sum_reverse]
    rw [sum_map_length_eq W m hw, hW, ht]
  · intro q hq c
    obtain ⟨b, j, hb, hj, rfl⟩ : ∃ b j, b < n ∧ j < m ∧ q = b * m + j :=
      ⟨q / m, q % m,
        by rw [← ht] at hq; exact (Nat.div_lt_iff_lt_mul hm).mpr hq,
        Nat.mod_lt q hm,
        by rw [mul_comm]; exact (Nat.div_add_mod q m).symm⟩
    have hb' : b < W.length := by rw [hW]; exact hb
    have hrev : (W.getD (n - 1 - b) []) = (W.reverse).getD b [] := by
      have h := (rev_getD b hb').symm
      rwa [hW] at h
    have hfl := flatten_getD hw b j hj
    have hlv : (lvlN r m sgn (blkArr r u m b)) j c = (lvlN r m sgn u) (b * m + j) c := by
      have harr : blkArr r u m b = (fun j' => u (b * m + j')) := rfl
      rw [harr, lvlNBlock r m sgn u hm b j hj]
    have hbnd := (hblock b hb).2 j hj c
    rw [hrev, hlv] at hbnd
    rw [hfl]
    exact hbnd

end Work.SynFFT

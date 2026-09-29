import Mathlib
import Submission.Work.SynFFT.mrgBlkDefs
import Submission.Work.SynFFT.hasSplitWord

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Work.SynFFT
open HvdH

local infixr:68 " ;;; " => HvdH.Cmd.seq

/-! ## A. Elementary list / `getD` facts -/

lemma getD_take_of_lt {α : Type} (l : List α) (d : α) {s i : ℕ} (h : i < s) :
    (l.take s).getD i d = l.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h, ← List.getD_eq_getElem?_getD]

lemma getD_drop_lt {α : Type} (l : List α) (d : α) (s i : ℕ) :
    (l.drop s).getD i d = l.getD (i + s) d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm, ← List.getD_eq_getElem?_getD]

lemma getD_cvecs_xmrgBlkHelper {ws : List (List (ℤ × ℤ))} {i : ℕ} (h : i < ws.length) :
    (cvecs ws).getD i .nil = cvecVal (ws.getD i []) := by
  have h' : i < (cvecs ws).length := by simpa [cvecs] using h
  have h1 : (cvecs ws).getD i .nil = (cvecs ws).getD i (cvecVal []) := by
    rw [List.getD_eq_getElem (cvecs ws) .nil h', List.getD_eq_getElem (cvecs ws) (cvecVal []) h']
  dsimp only [cvecs] at h1 ⊢
  rw [h1, List.getD_map]

lemma getD_mem {α : Type} (l : List α) (d : α) {i : ℕ} (h : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem l d h]
  exact List.getElem_mem h

lemma ofList_pair (a b : Val) : ofList [a, b] = Val.cons a (Val.cons b .nil) := rfl

lemma ofList_congr : ∀ (xs ys : List Val), xs.length = ys.length →
    (∀ i, i < xs.length → xs.getD i .nil = ys.getD i .nil) → ofList xs = ofList ys
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: as, b :: bs, h, hg => by
      have ha : a = b := by
        have h0 := hg 0 (by simp)
        simpa using h0
      rw [ha]
      have hlen : as.length = bs.length := by simpa using h
      have hg' : ∀ i, i < as.length → as.getD i .nil = bs.getD i .nil := by
        intro i hi
        have h1 := hg (i + 1) (by simpa using Nat.succ_lt_succ hi)
        simpa using h1
      show Val.cons b (ofList as) = Val.cons b (ofList bs)
      rw [ofList_congr as bs hlen hg']

lemma getD_flatten {α : Type} (d : α) {m : ℕ} (hm : 0 < m) :
    ∀ (xss : List (List α)), (∀ x ∈ xss, x.length = m) → ∀ q, q < m * xss.length →
      xss.flatten.getD q d = (xss.getD (q / m) []).getD (q % m) d := by
  intro xss
  induction xss with
  | nil => intro _ q hq; simp at hq
  | cons x xs ih =>
    intro hlen q hq
    have hx : x.length = m := hlen x (by simp)
    have hxs : ∀ y ∈ xs, y.length = m := fun y hy => hlen y (by simp [hy])
    rw [List.flatten_cons]
    rcases Nat.lt_or_ge q m with hqm | hqm
    · have hqx : q < x.length := by rw [hx]; exact hqm
      rw [List.getD_append x xs.flatten d q hqx]
      have hdiv : q / m = 0 := Nat.div_eq_of_lt hqm
      have hmod : q % m = q := Nat.mod_eq_of_lt hqm
      rw [hdiv, hmod]
      simp
    · have hqx : x.length ≤ q := by rw [hx]; exact hqm
      rw [List.getD_append_right x xs.flatten d q hqx, hx]
      have hj : q - m < m * xs.length := by
        have h2 : q < m * (xs.length + 1) := by simpa using hq
        rw [Nat.mul_add, Nat.mul_one] at h2
        omega
      rw [ih hxs (q - m) hj]
      have hqeq : q = (q - m) + m * 1 := by omega
      have hdiv : q / m = (q - m) / m + 1 := by
        conv_lhs => rw [hqeq]
        rw [Nat.add_mul_div_left (q - m) 1 hm]
      have hmod : q % m = (q - m) % m := by
        conv_lhs => rw [hqeq]
        rw [Nat.add_mul_mod_self_left (q - m) m 1]
      rw [hdiv, hmod]
      simp

lemma vsz_ofList_pair (a b : Val) : vsz (ofList [a, b]) = vsz a + vsz b + 3 := by
  have h : vsz (.nil : Val) = 1 := rfl
  rw [ofList_pair, MrgKit.vsz_cons', MrgKit.vsz_cons', h]
  ring

lemma mrgIdx_lt {s q : ℕ} (hq : q < 2 * s) : q / 2 + (q % 2) * s < 2 * s := by
  have hq2 : q / 2 < s := by
    have h1 := Nat.div_add_mod q 2
    omega
  have h2 : q % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rcases Nat.eq_zero_or_pos (q % 2) with h0 | h0
  · rw [h0]; omega
  · have h1 : q % 2 = 1 := by omega
    rw [h1]; omega

/-! ## `mrgBlkL` facts -/

lemma mrgBlkL_length (s : ℕ) (ws : List (List (ℤ × ℤ))) : (mrgBlkL s ws).length = 2 * s := by
  rw [mrgBlkL, List.length_flatten]
  have h1 : List.map List.length
      (List.map (fun i => [ws.getD i [], ws.getD (i + s) []]) (List.range s)) =
      List.replicate s 2 := by
    rw [List.map_map]
    have h2 : (List.length ∘ fun i : ℕ => [ws.getD i [], ws.getD (i + s) []]) = fun _ => 2 := by
      funext i; simp
    rw [h2, show (fun _ : ℕ => 2) = Function.const ℕ 2 from rfl, List.map_const, List.length_range]
  rw [h1, List.sum_replicate, smul_eq_mul]
  ring

lemma mrgBlkL_getD {s : ℕ} {ws : List (List (ℤ × ℤ))} (hlen : ws.length = 2 * s)
    {q : ℕ} (hq : q < 2 * s) :
    (mrgBlkL s ws).getD q [] = ws.getD (q / 2 + (q % 2) * s) [] := by
  have hlen_pairs : ((List.range s).map (fun i => [ws.getD i [], ws.getD (i + s) []])).length = s := by
    simp
  have hpair_len : ∀ x ∈ (List.range s).map (fun i => [ws.getD i [], ws.getD (i + s) []]),
      x.length = 2 := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    simp
  have hq' : q < 2 * ((List.range s).map (fun i => [ws.getD i [], ws.getD (i + s) []])).length := by
    rw [hlen_pairs]; exact hq
  rw [mrgBlkL,
    getD_flatten (α := List (ℤ × ℤ)) ([] : List (ℤ × ℤ)) (m := 2) (by norm_num) _ hpair_len q hq']
  have hq2 : q / 2 < s := by omega
  have hq2' : q / 2 < ((List.range s).map
      (fun i => [ws.getD i [], ws.getD (i + s) []])).length := by rw [hlen_pairs]; exact hq2
  have hpair : ((List.range s).map (fun i => [ws.getD i [], ws.getD (i + s) []])).getD (q / 2) []
      = [ws.getD (q / 2) [], ws.getD (q / 2 + s) []] := by
    rw [List.getD_eq_getElem _ [] hq2']
    rw [List.getElem_map (f := fun i => [ws.getD i [], ws.getD (i + s) []]) (h := hq2')]
    rw [List.getElem_range (by simpa using hq2)]
  rw [hpair]
  have hmod : q % 2 = 0 ∨ q % 2 = 1 := by omega
  rcases hmod with h0 | h1
  · rw [h0]; simp
  · rw [h1]; simp [Nat.add_comm]

lemma mrgBlkL_mem {s : ℕ} {ws : List (List (ℤ × ℤ))} (hlen : ws.length = 2 * s) :
    ∀ w ∈ mrgBlkL s ws, w ∈ ws := by
  intro w hw
  obtain ⟨q, hq, rfl⟩ := List.mem_iff_getElem.mp hw
  have hq' : q < 2 * s := by rwa [mrgBlkL_length] at hq
  rw [← List.getD_eq_getElem (mrgBlkL s ws) [] hq, mrgBlkL_getD hlen hq']
  exact getD_mem ws [] (by rw [hlen]; exact mrgIdx_lt hq')

theorem mrgBlk_facts (p r s : ℕ) (ws : List (List (ℤ × ℤ))) (u : Arr r) (e : ℝ)
    (hs : 0 < s) (hlen : ws.length = 2 * s)
    (hdisc : ∀ w ∈ ws, InDiscVec p r w) (happ : ApproxSL p r (2 * s) ws u e) :
    (mrgBlkL s ws).length = 2 * s ∧ (∀ w ∈ mrgBlkL s ws, InDiscVec p r w) ∧
      ApproxSL p r (2 * s) (mrgBlkL s ws) (mrgN r s u) e := by
  refine ⟨mrgBlkL_length s ws, fun w hw => hdisc w (mrgBlkL_mem hlen w hw),
    mrgBlkL_length s ws, ?_⟩
  intro q hq c
  obtain ⟨-, happ'⟩ := happ
  have hq2 : q / 2 < s := by
    have h1 := Nat.div_add_mod q 2
    omega
  have hidx : q / 2 + (q % 2) * s < 2 * s := mrgIdx_lt hq
  have hval := happ' (q / 2 + (q % 2) * s) hidx c
  have hget : (mrgBlkL s ws).getD q [] = ws.getD (q / 2 + (q % 2) * s) [] :=
    mrgBlkL_getD hlen hq
  have hmrg : mrgN r s u q c = u (q / 2 + (q % 2) * s) c := by
    have h1 : q / (2 * s) = 0 := Nat.div_eq_of_lt hq
    have h2 : q / 2 % s = q / 2 := Nat.mod_eq_of_lt hq2
    simp only [mrgN]
    rw [h1, h2]
    simp
  rw [hget, hmrg]
  exact hval

lemma vsz_ofList_cvecs_le_xmrgBlkHelper {p r N : ℕ} (ws : List (List (ℤ × ℤ))) (hN : ws.length = N)
    (hd : ∀ w ∈ ws, InDiscVec p r w) :
    vsz (ofList (cvecs ws)) ≤ N * (13 * (r + 1) * (p + 1) + 1) + 1 := by
  rw [MrgKit.vsz_ofList]
  have hlen : (cvecs ws).length = N := by
    rw [show (cvecs ws).length = ws.length from by simp [cvecs], hN]
  have hsum : ((cvecs ws).map vsz).sum ≤ N * (13 * (r + 1) * (p + 1)) := by
    refine le_trans (MrgKit.sum_le_of_forall vsz (cvecs ws) (13 * (r + 1) * (p + 1)) ?_) ?_
    · intro v hv
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
      exact MrgKit.vsz_cvecVal_le p r w (hd w hw).1 (hd w hw).2
    · rw [hlen]
  rw [hlen]
  nlinarith [hsum]

/-! ### A calculus of multiples of `s * (r+1) * (p+1)` -/

lemma one_le_sX {s r p : ℕ} (hs : 0 < s) : 1 ≤ s * (r + 1) * (p + 1) :=
  Nat.one_le_iff_ne_zero.mpr (by positivity)

lemma add_le_mul {a b A B U : ℕ} (ha : a ≤ A * U) (hb : b ≤ B * U) : a + b ≤ (A + B) * U := by
  have h := Nat.add_le_add ha hb
  rwa [← Nat.add_mul] at h

lemma le_mul_const {a U A B : ℕ} (h : a ≤ A * U) (hAB : A ≤ B) : a ≤ B * U :=
  le_trans h (Nat.mul_le_mul_right U hAB)

lemma three_le {a b c U A B C : ℕ} (ha : a ≤ A * U) (hb : b ≤ B * U) (hc : c ≤ C * U) :
    (a + b) + c ≤ ((A + B) + C) * U := by
  have h1 := Nat.add_le_add (Nat.add_le_add ha hb) hc
  calc (a + b) + c ≤ (A * U + B * U) + C * U := h1
    _ = ((A + B) + C) * U := by ring

lemma two_le {a b U A B : ℕ} (ha : a ≤ A * U) (hb : b ≤ B * U) : a + b ≤ (A + B) * U := by
  have h1 := Nat.add_le_add ha hb
  calc a + b ≤ A * U + B * U := h1
    _ = (A + B) * U := by ring

/-- Conversion of the size bounds into the shape `40 * (s*(r+1)*(p+1))`. -/
lemma poly_le40 {v s r p N : ℕ} (hs : 0 < s) (hNs : N ≤ 2 * s)
    (h : (v : ℤ) ≤ (N : ℤ) * (13 * ((r + 1 : ℕ) * (p + 1)) + 1) + 1) :
    v ≤ 40 * (s * (r + 1) * (p + 1)) := by
  have hX : 1 ≤ (r + 1) * (p + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hXZ : (1 : ℤ) ≤ ((r + 1 : ℕ) * (p + 1)) := by exact_mod_cast hX
  have hsZ : (1 : ℤ) ≤ (s : ℤ) := by exact_mod_cast hs
  have hNZ : (N : ℤ) ≤ 2 * (s : ℤ) := by exact_mod_cast hNs
  have key : (v : ℤ) ≤ 40 * ((s : ℤ) * ((r + 1 : ℕ) * (p + 1))) := by
    nlinarith [h, hXZ, hsZ, hNZ]
  have hcast : ((40 * (s * (r + 1) * (p + 1)) : ℕ) : ℤ)
      = 40 * ((s : ℤ) * ((r + 1 : ℕ) * (p + 1))) := by push_cast; ring
  rw [← hcast] at key
  exact_mod_cast key

lemma vsz_cvecs_le40 {p r s : ℕ} (hs : 0 < s) {ws : List (List (ℤ × ℤ))}
    (hlen : ws.length ≤ 2 * s) (hd : ∀ w ∈ ws, InDiscVec p r w) :
    vsz (ofList (cvecs ws)) ≤ 40 * (s * (r + 1) * (p + 1)) := by
  refine poly_le40 hs hlen ?_
  have h := vsz_ofList_cvecs_le_xmrgBlkHelper ws rfl hd
  have h2 : ((ws.length * (13 * (r + 1) * (p + 1) + 1) + 1 : ℕ) : ℤ)
      = (ws.length : ℤ) * (13 * ((r + 1 : ℕ) * (p + 1)) + 1) + 1 := by push_cast; ring
  rw [← h2]
  exact_mod_cast h

lemma isz_le40 {r p s : ℕ} (hs : 0 < s) : isz (s : ℤ) ≤ 40 * (s * (r + 1) * (p + 1)) := by
  rw [isz, Int.natAbs_natCast]
  have h1 : s.size ≤ s := (Nat.size_le).mpr Nat.lt_two_pow_self
  have hX : 1 ≤ (r + 1) * (p + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h2 : s + 2 ≤ 3 * s := by omega
  have h3 : s * 1 ≤ s * ((r + 1) * (p + 1)) := Nat.mul_le_mul_left s hX
  have h4 : s ≤ s * (r + 1) * (p + 1) := by
    have : s * ((r + 1) * (p + 1)) = s * (r + 1) * (p + 1) := by ring
    linarith
  calc s.size + 2 ≤ s + 2 := by omega
    _ ≤ 3 * s := h2
    _ ≤ 3 * (s * (r + 1) * (p + 1)) := Nat.mul_le_mul_left 3 h4
    _ ≤ 40 * (s * (r + 1) * (p + 1)) := Nat.mul_le_mul_right _ (by norm_num)

lemma one_le40 {r p s : ℕ} (hs : 0 < s) : 1 ≤ 40 * (s * (r + 1) * (p + 1)) := by
  have h := one_le_sX (r := r) (p := p) hs
  calc (1 : ℕ) ≤ s * (r + 1) * (p + 1) := h
    _ ≤ 40 * (s * (r + 1) * (p + 1)) := by
        have h3 : (1 : ℕ) * (s * (r + 1) * (p + 1)) ≤ 40 * (s * (r + 1) * (p + 1)) :=
          Nat.mul_le_mul_right _ (by norm_num)
        simpa using h3

/-! ## B. `WordR` adapters -/

theorem binOpStep {main prog : Cmd} {P : ℤ → ℤ → Prop} {f : ℤ → ℤ → ℤ} {Kf : ℤ → ℤ → ℕ}
    (h : BinOp main prog P f Kf) (a b : ℤ) (t : List Val) (hP : P a b) (D : ℕ)
    (hD : Kf a b ≤ D) :
    WordR main prog (fun vs => vs = .int a :: .int b :: t) (fun _ out => out = .int (f a b) :: t)
      (fun _ => D) := by
  refine MrgKit.WordR_conseqC h ⟨a, b, t, rfl, hP⟩ ?_ ?_
  · intro out hout
    obtain ⟨a', b', t', h1, hout'⟩ := hout
    simp only [List.cons.injEq, Val.int.injEq] at h1
    obtain ⟨rfl, rfl, rfl⟩ := h1
    exact hout'
  · show binCost Kf (.int a :: .int b :: t) ≤ D
    simpa [binCost] using hD

theorem zipStep_xmrgBlkHelper {main : Cmd} {zipP : Cmd → Cmd} {Kzw : ℕ}
    (h : ∀ (q : Cmd) (rest : List Val) (P : Val → Val → Prop) (Q : Val → Val → Val → Prop)
      (c L : ℕ),
      (∀ x y, P x y → WordR main q (fun vs => vs = x :: y :: rest)
        (fun _ out => ∃ z, out = z :: rest ∧ Q x y z ∧ vsz z ≤ L) (fun _ => c)) →
      ∀ xs ys : List Val, xs.length = ys.length →
      (∀ i < xs.length, P (xs.getD i .nil) (ys.getD i .nil)) → (∀ x ∈ xs ++ ys, vsz x ≤ L) →
      WordR main (zipP q) (fun vs => vs = ofList xs :: ofList ys :: rest)
        (fun _ out => ∃ zs, out = ofList zs :: rest ∧ zs.length = xs.length ∧
          ∀ i < xs.length, Q (xs.getD i .nil) (ys.getD i .nil) (zs.getD i .nil))
        (fun _ => xs.length * (c + Kzw * (L + 1)) + Kzw))
    (q : Cmd) (rest : List Val) (P : Val → Val → Prop) (Q : Val → Val → Val → Prop) (c L : ℕ)
    (hq : ∀ x y, P x y → WordR main q (fun vs => vs = x :: y :: rest)
        (fun _ out => ∃ z, out = z :: rest ∧ Q x y z ∧ vsz z ≤ L) (fun _ => c))
    (xs ys : List Val) (hlen : xs.length = ys.length)
    (hP : ∀ i < xs.length, P (xs.getD i .nil) (ys.getD i .nil))
    (hL : ∀ x ∈ xs ++ ys, vsz x ≤ L)
    (B : Val) (hB : ∀ zs, zs.length = xs.length →
      (∀ i < xs.length, Q (xs.getD i .nil) (ys.getD i .nil) (zs.getD i .nil)) → ofList zs = B)
    (D : ℕ) (hD : xs.length * (c + Kzw * (L + 1)) + Kzw ≤ D) :
    WordR main (zipP q) (fun vs => vs = ofList xs :: ofList ys :: rest)
      (fun _ out => out = B :: rest) (fun _ => D) := by
  have hspec := h q rest P Q c L hq xs ys hlen hP hL
  refine MrgKit.WordR_weaken hspec (fun vs hvs => hvs) ?_ (fun vs _ => hD)
  intro vs out hvs hQ
  obtain ⟨zs, hout, hlen', hget⟩ := hQ
  rw [hout, hB zs hlen' hget]

theorem flattenStep_xmrgBlkHelper {main : Cmd} {flatP : Cmd} {Kfl : ℕ}
    (h : ∀ (xss : List (List Val)), WordR main flatP
      (fun vs => ∃ rest, vs = ofList (xss.map ofList) :: rest)
      (fun vs out => ∃ rest, vs = ofList (xss.map ofList) :: rest ∧ out = ofList xss.flatten :: rest)
      (fun _ => Kfl * (vsz (ofList (xss.map ofList)) + 1)))
    (xss : List (List Val)) (rest : List Val) (D : ℕ)
    (hD : Kfl * (vsz (ofList (xss.map ofList)) + 1) ≤ D) :
    WordR main flatP (fun vs => vs = ofList (xss.map ofList) :: rest)
      (fun _ out => out = ofList xss.flatten :: rest) (fun _ => D) := by
  refine MrgKit.WordR_conseqC (h xss) ⟨rest, rfl⟩ ?_ hD
  intro out hout
  obtain ⟨r, h1, h2⟩ := hout
  have hr : r = rest := (List.cons.inj h1).2.symm
  simpa [hr] using h2

theorem lengthStep {main : Cmd} {lenP : Cmd} {Kl : ℕ}
    (h : ∀ (xs : List Val), WordR main lenP (fun vs => ∃ rest, vs = ofList xs :: rest)
      (fun vs out => ∃ rest, vs = ofList xs :: rest ∧
        out = .int (xs.length : ℤ) :: ofList xs :: rest)
      (fun _ => Kl * (vsz (ofList xs) + 1)))
    (xs : List Val) (rest : List Val) (D : ℕ) (hD : Kl * (vsz (ofList xs) + 1) ≤ D) :
    WordR main lenP (fun vs => vs = ofList xs :: rest)
      (fun _ out => out = .int (xs.length : ℤ) :: ofList xs :: rest) (fun _ => D) := by
  refine MrgKit.WordR_conseqC (h xs) ⟨rest, rfl⟩ ?_ hD
  intro out hout
  obtain ⟨r, h1, h2⟩ := hout
  have hr : r = rest := (List.cons.inj h1).2.symm
  simpa [hr] using h2

/-! ## C. The split phase -/

theorem mrgBlk_splitW (hk : KLib) (hl : LayoutLib) :
    ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (s : ℕ) (ws : List (List (ℤ × ℤ))) (r p : ℕ)
      (rest : List Val),
      0 < s → ws.length = 2 * s → (∀ w ∈ ws, InDiscVec p r w) →
      WordR main prog
        (fun vs => vs = ofList (cvecs ws) :: .int (s : ℤ) :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
        (fun vs out => out = ofList (cvecs (ws.drop s)) :: ofList (cvecs (ws.take s)) ::
          .int (r : ℤ) :: .int (p : ℤ) :: rest)
        (fun _ => K * s * (r + 1) * (p + 1) + K) := by
  obtain ⟨splitP, Ksp, hsplit⟩ := hasSplitWord hk hl
  obtain ⟨swapP, Ksw, hswap⟩ := hk.swap
  obtain ⟨rollP, Kr, hroll⟩ := hk.roll
  obtain ⟨kdrP, Kdr, hkdr⟩ := hk.drop
  refine ⟨((splitP ;;; swapP) ;;; rollP 2) ;;; kdrP,
    10000 * (1000 * (Ksp + Ksw + Kr + Kdr + 1)), ?_⟩
  intro main s ws r p rest hs hlen hdisc
  set Kx : ℕ := 1000 * (Ksp + Ksw + Kr + Kdr + 1) with hKx
  set U : ℕ := s * (r + 1) * (p + 1) with hU
  set Cs : ℕ := 2000 * Kx * U with hCs
  have hKsp : Ksp ≤ Kx := by rw [hKx]; omega
  have hKsw : Ksw ≤ Kx := by rw [hKx]; omega
  have hKr : Kr ≤ Kx := by rw [hKx]; omega
  have hKdr : Kdr ≤ Kx := by rw [hKx]; omega
  have hbW : vsz (ofList (cvecs ws)) ≤ 40 * U := by
    rw [hU]; exact vsz_cvecs_le40 hs (le_of_eq hlen) hdisc
  have hbT : vsz (ofList ((cvecs ws).take s)) ≤ 40 * U := by
    rw [hU, ← cvecs_take s ws]
    exact vsz_cvecs_le40 hs (by rw [List.length_take]; omega)
      (fun w hw => hdisc w (List.mem_of_mem_take hw))
  have hbD : vsz (ofList ((cvecs ws).drop s)) ≤ 40 * U := by
    rw [hU, ← cvecs_drop s ws]
    exact vsz_cvecs_le40 hs (by rw [List.length_drop]; omega)
      (fun w hw => hdisc w (List.mem_of_mem_drop hw))
  have hbS : isz (s : ℤ) ≤ 40 * U := by rw [hU]; exact isz_le40 hs
  have hone : 1 ≤ 40 * U := by rw [hU]; exact one_le40 hs
  have hcost : ∀ c z : ℕ, c ≤ Kx → z ≤ 2000 * U → c * z ≤ Cs := by
    intro c z hc hz
    rw [hCs]
    calc c * z ≤ Kx * (2000 * U) := Nat.mul_le_mul hc hz
      _ = 2000 * Kx * U := by ring
  -- step 1: split
  have e1 : WordR main splitP
      (fun vs => vs = ofList (cvecs ws) :: .int (s : ℤ) :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = ofList ((cvecs ws).take s) :: ofList ((cvecs ws).drop s) ::
        .int (s : ℤ) :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ => Cs) := by
    have h := hsplit main s (cvecs ws) (.int (r : ℤ) :: .int (p : ℤ) :: rest)
    refine MrgKit.WordR_weaken h (fun vs hvs => hvs) (fun vs out _ hq => hq) (fun vs _ => ?_)
    exact hcost Ksp ((vsz (ofList (cvecs ws)) + isz (s : ℤ)) + 1) hKsp
      (le_mul_const (three_le hbW hbS hone) (by norm_num))
  -- step 2: swap
  have e2 : WordR main swapP
      (fun vs => vs = ofList ((cvecs ws).take s) :: ofList ((cvecs ws).drop s) ::
        .int (s : ℤ) :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = ofList ((cvecs ws).drop s) :: ofList ((cvecs ws).take s) ::
        .int (s : ℤ) :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ => Cs) := by
    refine MrgKit.swapStep (hswap main)
      (ofList ((cvecs ws).take s) :: ofList ((cvecs ws).drop s) :: .int (s : ℤ) ::
        .int (r : ℤ) :: .int (p : ℤ) :: rest) (by simp) Cs ?_
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    exact hcost Ksw _ hKsw (le_mul_const (three_le hbT hbD hone) (by norm_num))
  -- step 3: roll 2
  have e3 : WordR main (rollP 2)
      (fun vs => vs = ofList ((cvecs ws).drop s) :: ofList ((cvecs ws).take s) ::
        .int (s : ℤ) :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = .int (s : ℤ) :: ofList ((cvecs ws).drop s) :: ofList ((cvecs ws).take s) ::
        .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ => Cs) := by
    refine MrgKit.rollStep (fun k => hroll main k) 2
      (ofList ((cvecs ws).drop s) :: ofList ((cvecs ws).take s) :: .int (s : ℤ) ::
        .int (r : ℤ) :: .int (p : ℤ) :: rest) (by simp) Cs ?_
    have hsum : (((ofList ((cvecs ws).drop s) :: ofList ((cvecs ws).take s) :: .int (s : ℤ) ::
        .int (r : ℤ) :: .int (p : ℤ) :: rest : List Val).take 3).map vsz).sum
        = (vsz (ofList ((cvecs ws).drop s)) + vsz (ofList ((cvecs ws).take s))) + isz (s : ℤ) := by
      simp [MrgKit.vsz_int']
      ring
    rw [hsum]
    have h4 : ((vsz (ofList ((cvecs ws).drop s)) + vsz (ofList ((cvecs ws).take s))) + isz (s : ℤ)) + 1
        ≤ (((40 + 40) + 40) + 40) * U := two_le (three_le hbD hbT hbS) hone
    have hz : 3 * (((vsz (ofList ((cvecs ws).drop s)) + vsz (ofList ((cvecs ws).take s)))
        + isz (s : ℤ)) + 1) ≤ 2000 * U := by
      calc 3 * (((vsz (ofList ((cvecs ws).drop s)) + vsz (ofList ((cvecs ws).take s)))
            + isz (s : ℤ)) + 1)
          ≤ 3 * ((((40 + 40) + 40) + 40) * U) := Nat.mul_le_mul_left 3 h4
        _ ≤ 2000 * U := by
            have h5 : (3 * (((40 + 40) + 40) + 40)) * U ≤ 2000 * U :=
              Nat.mul_le_mul_right U (by norm_num)
            have h6 : 3 * ((((40 + 40) + 40) + 40) * U)
                = (3 * (((40 + 40) + 40) + 40)) * U := by ring
            rw [h6]
            exact h5
    have hz' := hcost Kr (3 * (((vsz (ofList ((cvecs ws).drop s))
      + vsz (ofList ((cvecs ws).take s))) + isz (s : ℤ)) + 1)) hKr hz
    simpa [Nat.mul_assoc] using hz'
  -- step 4: drop the integer s
  have e4 : WordR main kdrP
      (fun vs => vs = .int (s : ℤ) :: ofList ((cvecs ws).drop s) :: ofList ((cvecs ws).take s) ::
        .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = ofList ((cvecs ws).drop s) :: ofList ((cvecs ws).take s) ::
        .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ => Cs) := by
    refine MrgKit.kdropStep (hkdr main)
      (.int (s : ℤ) :: ofList ((cvecs ws).drop s) :: ofList ((cvecs ws).take s) ::
        .int (r : ℤ) :: .int (p : ℤ) :: rest) (by simp) Cs ?_
    simp only [List.headD_cons, MrgKit.vsz_int']
    exact hcost Kdr (isz (s : ℤ) + 1) hKdr
      (le_mul_const (two_le hbS hone) (by norm_num))
  -- assembly
  have e12 := MrgKit.WordR_seqC e1 e2
  have e123 := MrgKit.WordR_seqC e12 e3
  have e1234 := MrgKit.WordR_seqC e123 e4
  refine MrgKit.WordR_weaken e1234 (fun vs hvs => hvs) (fun vs out _ hq => ?_) (fun vs _ => ?_)
  · rw [hq, cvecs_take, cvecs_drop]
  · have h4 : Cs + Cs + Cs + Cs ≤ 10000 * (1000 * (Ksp + Ksw + Kr + Kdr + 1)) * U := by
      rw [hCs, hKx]
      nlinarith [one_le_sX (r := r) (p := p) hs]
    have hfin : 10000 * (1000 * (Ksp + Ksw + Kr + Kdr + 1)) * U
        ≤ 10000 * (1000 * (Ksp + Ksw + Kr + Kdr + 1)) * s * (r + 1) * (p + 1)
          + 10000 * (1000 * (Ksp + Ksw + Kr + Kdr + 1)) := by
      have hEq : 10000 * (1000 * (Ksp + Ksw + Kr + Kdr + 1)) * U
          = 10000 * (1000 * (Ksp + Ksw + Kr + Kdr + 1)) * s * (r + 1) * (p + 1) := by
        rw [hU]; ring
      rw [hEq]
      exact Nat.le_add_right _ _
    exact le_trans h4 hfin

end Work.SynFFT

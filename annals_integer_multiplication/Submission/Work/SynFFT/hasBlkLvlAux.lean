import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs
import Submission.Work.SynFFT.blkLvlDefs
import Submission.Work.SynFFT.lvlAllGetD

/-!
# `Work.SynFFT.hasBlkLvlAux`: shared plumbing for the block level pass

Auxiliary material for `Submission/Work/SynFFT/hasBlkLvl.lean`:

* `zipStep`: the concretisation of `KLib.zipWith` with a constant cost (mirror of `MrgKit.mapStep`);
* elementary list-index and size lemmas;
* the two parameter-moving steps of the assembly (`blkRollShift`, `blkFixParams`);
* the per-pair predicates (`InVec`, `ApproxVec`, `PackProps`, `PackP`, `PairP`, `PairQ`) and
  `pairWordBlk`, the word that computes the two butterfly outputs of one pair and bunches them
  into a `cons` value.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Work.SynFFT

open HvdH

local infixl:68 " ;;; " => HvdH.Cmd.seq

/-! ## `zipWith` with a constant cost -/

theorem zipStep {main : Cmd} {zipP : Cmd → Cmd} {Kz : ℕ}
    (h : ∀ (q : Cmd) (rest : List Val) (P : Val → Val → Prop) (Q : Val → Val → Val → Prop)
        (c L : ℕ),
      (∀ x y, P x y → WordR main q (fun vs => vs = x :: y :: rest)
        (fun _ out => ∃ z, out = z :: rest ∧ Q x y z ∧ vsz z ≤ L) (fun _ => c)) →
      ∀ xs ys : List Val, xs.length = ys.length →
      (∀ i < xs.length, P (xs.getD i .nil) (ys.getD i .nil)) → (∀ x ∈ xs ++ ys, vsz x ≤ L) →
      WordR main (zipP q) (fun vs => vs = ofList xs :: ofList ys :: rest)
        (fun _ out => ∃ zs, out = ofList zs :: rest ∧ zs.length = xs.length ∧
          ∀ i < xs.length, Q (xs.getD i .nil) (ys.getD i .nil) (zs.getD i .nil))
        (fun _ => xs.length * (c + Kz * (L + 1)) + Kz))
    (q : Cmd) (rest : List Val) (P : Val → Val → Prop) (Q : Val → Val → Val → Prop) (c L : ℕ)
    (hq : ∀ x y, P x y → WordR main q (fun vs => vs = x :: y :: rest)
        (fun _ out => ∃ z, out = z :: rest ∧ Q x y z ∧ vsz z ≤ L) (fun _ => c))
    (xs ys : List Val) (hlen : xs.length = ys.length)
    (hP : ∀ i < xs.length, P (xs.getD i .nil) (ys.getD i .nil))
    (hL : ∀ x ∈ xs ++ ys, vsz x ≤ L) (B : List Val)
    (hB : ∀ zs, zs.length = xs.length →
      (∀ i < xs.length, Q (xs.getD i .nil) (ys.getD i .nil) (zs.getD i .nil)) → B = zs)
    (D : ℕ) (hD : xs.length * (c + Kz * (L + 1)) + Kz ≤ D) :
    WordR main (zipP q) (fun vs => vs = ofList xs :: ofList ys :: rest)
      (fun _ out => out = ofList B :: rest) (fun _ => D) := by
  refine MrgKit.WordR_weaken (h q rest P Q c L hq xs ys hlen hP hL) (fun vs hvs => hvs) ?_
    (fun vs _ => hD)
  intro vs out _ hout
  obtain ⟨zs, hout', hlen', hQ⟩ := hout
  rw [hout', hB zs hlen' hQ]

/-! ## List index and size lemmas -/

/-- The sum of the sizes of the first `3` values of a `cons`-chain. -/
theorem sum_take3_cons (x1 x2 x3 : Val) (t : List Val) :
    (((x1 :: x2 :: x3 :: t).take 3).map vsz).sum = vsz x1 + (vsz x2 + vsz x3) := by
  simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]

/-- The sum of the sizes of the first `5` values of a `cons`-chain. -/
theorem sum_take5_cons (x1 x2 x3 x4 x5 : Val) (t : List Val) :
    (((x1 :: x2 :: x3 :: x4 :: x5 :: t).take 5).map vsz).sum
      = vsz x1 + (vsz x2 + (vsz x3 + (vsz x4 + vsz x5))) := by
  simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]

/-- The sum of the sizes of the first `6` values of a `cons`-chain. -/
theorem sum_take6_cons (x1 x2 x3 x4 x5 x6 : Val) (t : List Val) :
    (((x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: t).take 6).map vsz).sum
      = vsz x1 + (vsz x2 + (vsz x3 + (vsz x4 + (vsz x5 + vsz x6)))) := by
  simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]

/-- `Kr * k * (s + 1) ≤ Kr * 6 * (S + 1)` when `k ≤ 6` and `s ≤ S`. -/
theorem cost_le_of_sum_le (Kr k s S : ℕ) (hk : k ≤ 6) (h : s ≤ S) :
    Kr * k * (s + 1) ≤ Kr * 6 * (S + 1) := by
  have h1 : s + 1 ≤ S + 1 := by omega
  have h2 : k * (s + 1) ≤ 6 * (S + 1) := Nat.mul_le_mul hk h1
  calc Kr * k * (s + 1) = Kr * (k * (s + 1)) := by ring
    _ ≤ Kr * (6 * (S + 1)) := Nat.mul_le_mul_left Kr h2
    _ = Kr * 6 * (S + 1) := by ring

/-- Reading the `drop` of a list. -/
theorem getD_drop' {α : Type} (l : List α) (d : α) : ∀ (n i : ℕ),
    (l.drop n).getD i d = l.getD (n + i) d
  | 0, i => by simp
  | n + 1, i => by
    cases l with
    | nil => simp
    | cons a t =>
      rw [List.drop_succ_cons]
      cases i with
      | zero =>
        rw [show n + 1 + 0 = n + 1 from by omega, List.getD_cons_succ, getD_drop' t d n 0]
        exact congrArg (fun k => t.getD k d) (by omega)
      | succ i =>
        rw [show n + 1 + (i + 1) = (n + 1 + i) + 1 from by omega, List.getD_cons_succ,
          getD_drop' t d n (i + 1)]
        exact congrArg (fun k => t.getD k d) (by omega)

/-- Reading the `take` of a list. -/
theorem getD_take' {α : Type} (l : List α) (d : α) : ∀ (n i : ℕ), i < n →
    (l.take n).getD i d = l.getD i d
  | 0, i, h => by omega
  | n + 1, i, h => by
    cases l with
    | nil => simp
    | cons a t =>
      rw [List.take_succ_cons]
      cases i with
      | zero => simp
      | succ i =>
        rw [List.getD_cons_succ]
        exact getD_take' t d n i (by omega)

/-- Composition of two `WordR` steps, the first with an arbitrary postcondition: this is
`KLib.seq` packaged with constant costs. -/
theorem composeEx {main : Cmd} {p q : Cmd} {P0 : List Val → Prop}
    {Q1 : List Val → List Val → Prop} {P2 : List Val → Prop} {Q2 : List Val → List Val → Prop}
    {c1 c2 : ℕ}
    (h1 : WordR main p P0 Q1 (fun _ => c1)) (h2 : WordR main q P2 Q2 (fun _ => c2))
    (h : ∀ vs mid, P0 vs → Q1 vs mid → P2 mid) :
    WordR main (p ;;; q) P0 (fun vs out => ∃ mid, Q1 vs mid ∧ Q2 mid out) (fun _ => c1 + c2) := by
  intro vs hvs s R hR
  obtain ⟨mid, s2, n1, hQ1, hev1, hn1, hstk1, hoth1⟩ := h1 vs hvs s R hR
  obtain ⟨out, s3, n2, hQ2, hev2, hn2, hstk2, hoth2⟩ := h2 mid (h vs mid hvs hQ1) s2 R hstk1
  have hn1' : n1 ≤ c1 := hn1
  have hn2' : n2 ≤ c2 := hn2
  have hc : n1 + n2 ≤ c1 + c2 := by omega
  exact ⟨out, s3, n1 + n2, ⟨mid, hQ1, hQ2⟩, Eval.seq hev1 hev2, hc, hstk2,
    fun k hk => by rw [hoth2 k hk, hoth1 k hk]⟩

/-- Reading a `cvecVal`-list. -/
theorem getD_cvecs_xhasBlkLvlAux (ws : List (List (ℤ × ℤ))) (i : ℕ) :
    (cvecs ws).getD i .nil = cvecVal (ws.getD i []) := by
  have h := List.getD_map (l := ws) (d := ([] : List (ℤ × ℤ))) (n := i) cvecVal
  have hnil : cvecVal ([] : List (ℤ × ℤ)) = Val.nil := rfl
  rw [hnil] at h
  exact h

/-- Size of the encoding of a list of `R`-elements. -/
theorem vsz_ofList_cvecs_le (p r m : ℕ) (ws : List (List (ℤ × ℤ)))
    (hws : ws.length = m) (h : ∀ w ∈ ws, InDiscVec p r w) :
    vsz (ofList (cvecs ws)) ≤ m * (13 * (r + 1) * (p + 1) + 1) + 1 := by
  refine MrgKit.vsz_ofList_le_of_bound (cvecs ws) (13 * (r + 1) * (p + 1)) m ?_ ?_
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    exact MrgKit.vsz_cvecVal_le p r w (h w hw).1 (h w hw).2
  · simp only [cvecs, List.length_map]
    omega

/-- Size of a tagged element `cons (int i) (cvecVal w)`. -/
theorem vsz_lab_le (p r i : ℕ) (w : List (ℤ × ℤ))
    (hw : w.length = r) (hin : ∀ z ∈ w, inDisc p z) :
    vsz (Val.cons (.int (i : ℤ)) (cvecVal w)) ≤ 13 * (r + 1) * (p + 1) + isz (i : ℤ) + 1 := by
  rw [MrgKit.vsz_cons', MrgKit.vsz_int']
  have := MrgKit.vsz_cvecVal_le p r w hw hin
  omega

/-- `isz` of a small natural. -/
theorem isz_lt_two_r_le (i r : ℕ) (hi : i < 2 * r) : isz (i : ℤ) ≤ 4 * (r + 1) := by
  have h1 : ((i : ℤ)).natAbs = i := by simp
  have h2 : i.size ≤ r.size + 1 := by
    have h3 : (2 * r).size ≤ r.size + 1 := by
      refine (Nat.size_le).mpr ?_
      rw [pow_succ]
      nlinarith [Nat.lt_size_self r]
    exact le_trans (Nat.size_le_size (le_of_lt hi)) h3
  have h4 : r.size ≤ r := (Nat.size_le).mpr Nat.lt_two_pow_self
  simp only [isz, h1]
  omega

/-- Size of a bunched pair of `R`-elements. -/
theorem vsz_pack_le (p r : ℕ) (lo hi : List (ℤ × ℤ))
    (hlo : lo.length = r) (hhi : hi.length = r)
    (hloi : ∀ z ∈ lo, inDisc p z) (hhii : ∀ z ∈ hi, inDisc p z) :
    vsz (Val.cons (cvecVal lo) (cvecVal hi)) ≤ 2 * (13 * (r + 1) * (p + 1)) + 1 := by
  rw [MrgKit.vsz_cons']
  have h1 := MrgKit.vsz_cvecVal_le p r lo hlo hloi
  have h2 := MrgKit.vsz_cvecVal_le p r hi hhi hhii
  omega

/-! ## Two parameter-moving steps -/

/-- Moving `mv` (the second value of the parameter block) to the *end* of the block:
`A :: mv :: sh :: sgn :: r :: p :: t  ↦  A :: sh :: sgn :: r :: p :: mv :: t`. -/
theorem blkRollShift {main : Cmd} {rollP : ℕ → Cmd} {Kr : ℕ}
    (hroll : ∀ k, WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Kr * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (A shv gnv rv pv mv : Val) (t : List Val) (S D : ℕ)
    (hS : vsz A + vsz mv + vsz shv + vsz gnv + vsz rv + vsz pv ≤ S)
    (hD : 5 * (Kr * 6 * (S + 1)) ≤ D) :
    WordR main (rollP 5 ;;; rollP 5 ;;; rollP 5 ;;; rollP 5 ;;; rollP 4)
      (fun vs => vs = A :: mv :: shv :: gnv :: rv :: pv :: t)
      (fun _ out => out = A :: shv :: gnv :: rv :: pv :: mv :: t) (fun _ => D) := by
  set Ds : ℕ := Kr * 6 * (S + 1) with hDs
  have hmain : ∀ (L M : List Val), 6 ≤ L.length →
      (L.getD 5 .nil :: L.eraseIdx 5) = M → ((L.take 6).map vsz).sum ≤ S →
      WordR main (rollP 5) (fun vs => vs = L) (fun _ out => out = M) (fun _ => Ds) := by
    intro L M hlen hM hsum
    have hcost : Kr * (5 + 1) * (((L.take (5 + 1)).map vsz).sum + 1) ≤ Ds := by
      rw [hDs]
      exact cost_le_of_sum_le Kr 6 ((L.take 6).map vsz).sum S le_rfl hsum
    refine MrgKit.WordR_weaken
      (MrgKit.rollStep hroll 5 L (by omega) Ds hcost)
      (fun _ h => h) (fun _ _ _ hout => ?_) (fun _ _ => le_rfl)
    rw [hout]
    exact hM
  have s1 := hmain (A :: mv :: shv :: gnv :: rv :: pv :: t)
    (pv :: A :: mv :: shv :: gnv :: rv :: t) (by simp) (by simp)
    (by rw [sum_take6_cons]; omega)
  have s2 := hmain (pv :: A :: mv :: shv :: gnv :: rv :: t)
    (rv :: pv :: A :: mv :: shv :: gnv :: t) (by simp) (by simp)
    (by rw [sum_take6_cons]; omega)
  have s3 := hmain (rv :: pv :: A :: mv :: shv :: gnv :: t)
    (gnv :: rv :: pv :: A :: mv :: shv :: t) (by simp) (by simp)
    (by rw [sum_take6_cons]; omega)
  have s4 := hmain (gnv :: rv :: pv :: A :: mv :: shv :: t)
    (shv :: gnv :: rv :: pv :: A :: mv :: t) (by simp) (by simp)
    (by rw [sum_take6_cons]; omega)
  have s5 : WordR main (rollP 4)
      (fun vs => vs = shv :: gnv :: rv :: pv :: A :: mv :: t)
      (fun _ out => out = A :: shv :: gnv :: rv :: pv :: mv :: t) (fun _ => Ds) := by
    have hcost : Kr * (4 + 1)
        * ((((shv :: gnv :: rv :: pv :: A :: mv :: t).take (4 + 1)).map vsz).sum + 1) ≤ Ds := by
      rw [hDs]
      have hsum : (((shv :: gnv :: rv :: pv :: A :: mv :: t).take (4 + 1)).map vsz).sum ≤ S := by
        rw [sum_take5_cons]
        omega
      exact cost_le_of_sum_le Kr 5 _ S (by norm_num) hsum
    refine MrgKit.WordR_weaken
      (MrgKit.rollStep hroll 4 (shv :: gnv :: rv :: pv :: A :: mv :: t) (by simp) Ds hcost)
      (fun _ h => h) (fun _ _ _ hout => ?_) (fun _ _ => le_rfl)
    rw [hout]
    simp
  have c1 := MrgKit.WordR_seqC s1 s2
  have c2 := MrgKit.WordR_seqC c1 s3
  have c3 := MrgKit.WordR_seqC c2 s4
  have c4 := MrgKit.WordR_seqC c3 s5
  refine MrgKit.WordR_weaken c4 (fun _ h => h) (fun _ _ _ hout => hout) ?_
  intro vs _
  have h5 : Ds + Ds + Ds + Ds + Ds = 5 * Ds := by ring
  rw [h5, hDs]
  exact hD

/-- After the `zipWith` pass the parameter block is `sh :: sgn :: r :: p :: mv`; this step brings
`mv` back to the front: `Z :: sh :: sgn :: r :: p :: mv :: t ↦ Z :: mv :: sh :: sgn :: r :: p :: t`. -/
theorem blkFixParams {main : Cmd} {rollP : ℕ → Cmd} {swapP : Cmd} {Kr Ksw : ℕ}
    (hroll : ∀ k, WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Kr * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (hswap : WordR main swapP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => Ksw * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (Z shv gnv rv pv mv : Val) (t : List Val) (S D : ℕ)
    (hS : vsz Z + vsz shv + vsz gnv + vsz rv + vsz pv + vsz mv ≤ S)
    (hD : Kr * 6 * (S + 1) + Ksw * (S + 1) ≤ D) :
    WordR main (rollP 5 ;;; swapP)
      (fun vs => vs = Z :: shv :: gnv :: rv :: pv :: mv :: t)
      (fun _ out => out = Z :: mv :: shv :: gnv :: rv :: pv :: t) (fun _ => D) := by
  have s1 : WordR main (rollP 5)
      (fun vs => vs = Z :: shv :: gnv :: rv :: pv :: mv :: t)
      (fun _ out => out = mv :: Z :: shv :: gnv :: rv :: pv :: t)
      (fun _ => Kr * 6 * (S + 1)) := by
    have hcost : Kr * (5 + 1)
        * ((((Z :: shv :: gnv :: rv :: pv :: mv :: t).take (5 + 1)).map vsz).sum + 1)
        ≤ Kr * 6 * (S + 1) := by
      have hsum : (((Z :: shv :: gnv :: rv :: pv :: mv :: t).take (5 + 1)).map vsz).sum
          ≤ S := by
        rw [sum_take6_cons]
        omega
      exact cost_le_of_sum_le Kr 6 _ S le_rfl hsum
    refine MrgKit.WordR_weaken
      (MrgKit.rollStep hroll 5 (Z :: shv :: gnv :: rv :: pv :: mv :: t) (by simp)
        (Kr * 6 * (S + 1)) hcost)
      (fun _ h => h) (fun _ _ _ hout => ?_) (fun _ _ => le_rfl)
    rw [hout]
    simp
  have s2 : WordR main swapP
      (fun vs => vs = mv :: Z :: shv :: gnv :: rv :: pv :: t)
      (fun _ out => out = Z :: mv :: shv :: gnv :: rv :: pv :: t)
      (fun _ => Ksw * (S + 1)) := by
    have hcost : Ksw * (vsz (((mv :: Z :: shv :: gnv :: rv :: pv :: t).getD 0 .nil))
        + vsz (((mv :: Z :: shv :: gnv :: rv :: pv :: t).getD 1 .nil)) + 1)
        ≤ Ksw * (S + 1) := by
      have e0 : ((mv :: Z :: shv :: gnv :: rv :: pv :: t).getD 0 .nil) = mv := rfl
      have e1 : ((mv :: Z :: shv :: gnv :: rv :: pv :: t).getD 1 .nil) = Z := rfl
      rw [e0, e1]
      exact Nat.mul_le_mul_left Ksw (by omega)
    refine MrgKit.WordR_weaken
      (MrgKit.swapStep hswap (mv :: Z :: shv :: gnv :: rv :: pv :: t) (by simp)
        (Ksw * (S + 1)) hcost)
      (fun _ h => h) (fun _ _ _ hout => ?_) (fun _ _ => le_rfl)
    rw [hout]
    simp
  have c := MrgKit.WordR_seqC s1 s2
  refine MrgKit.WordR_weaken c (fun _ h => h) (fun _ _ _ hout => hout) ?_
  intro vs _
  exact hD

/-! ## The per-pair predicates and the per-pair word -/

/-- A coefficient vector in the disc and of the right length. -/
def InVec (p r : ℕ) (w : List (ℤ × ℤ)) : Prop :=
  w.length = r ∧ ∀ z ∈ w, inDisc p z

/-- `InVec` of an element of an `InDiscVec`-list, read with `getD`. -/
theorem inVec_getD {p r : ℕ} {ws : List (List (ℤ × ℤ))}
    (hind : ∀ w ∈ ws, InDiscVec p r w) {i : ℕ} (hi : i < ws.length) :
    InVec p r (ws.getD i []) := by
  have hmem : ws.getD i [] ∈ ws := by
    rw [List.getD_eq_getElem ws ([] : List (ℤ × ℤ)) hi]
    exact List.mem_iff_getElem.mpr ⟨i, hi, rfl⟩
  exact hind _ hmem

/-- Pointwise approximation of `v` by `w` at the `2^p` scale. -/
def ApproxVec (p r : ℕ) (w : List (ℤ × ℤ)) (v : Fin r → ℂ) (e : ℝ) : Prop :=
  ∀ c : Fin r, (2 : ℝ) ^ p * ‖fxC p (w.getD (c : ℕ) (0, 0)) - v c‖ ≤ e

/-- The properties of the two outputs of the butterfly at pair index `i`. -/
def PackProps (p r m sh : ℕ) (sgn : ℤ) (u : Arr r) (e : ℝ) (i : ℕ)
    (lo hi : List (ℤ × ℤ)) : Prop :=
  InVec p r lo ∧ InVec p r hi ∧
  ApproxVec p r lo (fun c => (u i c + u (i + m / 2) c) / 2) (e + 1) ∧
  ApproxVec p r hi (fun c => yMul r (sgn * (((i * 2 ^ sh : ℕ)) : ℤ))
    (fun c' => (u i c' - u (i + m / 2) c') / 2) c) (e + 1)

/-- The bunched outputs of one butterfly pair. -/
def PackP (p r m sh : ℕ) (sgn : ℤ) (u : Arr r) (e : ℝ) (i : ℕ) (z : Val) : Prop :=
  ∃ lo hi : List (ℤ × ℤ), z = Val.cons (cvecVal lo) (cvecVal hi) ∧
    PackProps p r m sh sgn u e i lo hi

/-- The input of one butterfly pair: a left vector tagged with its index `i` and a right vector,
both approximating the array `u` at positions `i` and `i + m/2`. -/
def PairP (p r m sh : ℕ) (u : Arr r) (e : ℝ) (x y : Val) : Prop :=
  ∃ (i : ℕ) (l rw : List (ℤ × ℤ)),
    i < m - m / 2 ∧ x = Val.cons (.int (i : ℤ)) (cvecVal l) ∧ y = cvecVal rw ∧
    InVec p r l ∧ InVec p r rw ∧ ApproxVec p r l (fun c => u i c) e ∧
    ApproxVec p r rw (fun c => u (i + m / 2) c) e

/-- Input and bunched output of one butterfly pair. -/
def PairQ (p r m sh : ℕ) (sgn : ℤ) (u : Arr r) (e : ℝ) (x y z : Val) : Prop :=
  ∃ (i : ℕ) (l rw : List (ℤ × ℤ)),
    i < m - m / 2 ∧ x = Val.cons (.int (i : ℤ)) (cvecVal l) ∧ y = cvecVal rw ∧
    InVec p r l ∧ InVec p r rw ∧ ApproxVec p r l (fun c => u i c) e ∧
    ApproxVec p r rw (fun c => u (i + m / 2) c) e ∧
    PackP p r m sh sgn u e i z

/-- **The per-pair word of the block level pass.**  `cons (int i) (cvecVal l) :: cvecVal rw`
(unpack the tag, rotate, run `HasPair`, drop the tag, re-pack) becomes `cons (cvecVal lo) (cvecVal hi)`
with the two butterfly outputs of pair `i`. -/
theorem pairWordBlk (hk : Work.SynFFT.KLib) (hp : Work.SynFFT.HasPair) :
    ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p r m sh : ℕ) (sgn : ℤ) (u : Arr r) (e : ℝ)
      (rest : List Val) (x y : Val),
      2 ≤ m → m * 2 ^ sh = 2 * r → 2 * r < 2 ^ p → (sgn = 1 ∨ sgn = -1) →
      PairP p r m sh u e x y →
      WordR main prog
        (fun vs => vs = x :: y :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) ::
          .int (p : ℤ) :: rest)
        (fun _ out => ∃ z : Val,
          out = z :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest ∧
          PairQ p r m sh sgn u e x y z ∧ vsz z ≤ 2 * (13 * (r + 1) * (p + 1)) + 1)
        (fun _ => K * (r + 1) * (p + 1) + K) := by
  obtain ⟨uncP, Kuc, hunc⟩ := hk.unconsV
  obtain ⟨rollP, Kr, hroll⟩ := hk.roll
  obtain ⟨pairP, Kpi, hpair⟩ := hp
  obtain ⟨kdrP, Kdr, hkdr⟩ := hk.drop
  obtain ⟨consP, Kcv, hcons⟩ := hk.consV
  set Ksum : ℕ := Kuc + Kr + Kpi + Kdr + Kcv + 1 with hKsum
  refine ⟨uncP ;;; rollP 2 ;;; rollP 2 ;;; pairP ;;; rollP 2 ;;; kdrP ;;; consP,
    3000 * Ksum, ?_⟩
  intro main p r m sh sgn u e rest x y h2 hmul hp2 hsgn hxy
  obtain ⟨i, l, rw, hiP, rfl, rfl, hl, hrw, hlapp, hrwapp⟩ := hxy
  set Tail : List Val := .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest
    with hTail
  have h2sh : 1 ≤ 2 ^ sh := Nat.one_le_two_pow
  have hm_le : m ≤ 2 * r := by
    calc m = m * 1 := by ring
      _ ≤ m * 2 ^ sh := Nat.mul_le_mul_left m h2sh
      _ = 2 * r := hmul
  have hr1 : 1 ≤ r := by
    have h1 : 2 ≤ 2 * r := by
      calc (2 : ℕ) = 2 * 1 := by ring
        _ ≤ m * 2 ^ sh := Nat.mul_le_mul h2 h2sh
        _ = 2 * r := hmul
    omega
  have hpow : 2 ^ sh ≤ 2 * r := by
    calc 2 ^ sh = 1 * 2 ^ sh := by ring
      _ ≤ m * 2 ^ sh := Nat.mul_le_mul_right (2 ^ sh) (by omega)
      _ = 2 * r := hmul
  have hi2r : i < 2 * r := by
    have h1 : i < m := lt_of_lt_of_le hiP (Nat.sub_le m (m / 2))
    omega
  have hisz : isz (i : ℤ) ≤ 4 * (r + 1) * (p + 1) := by
    have h1 := isz_lt_two_r_le i r hi2r
    have hp1 : 1 ≤ p + 1 := by omega
    calc isz (i : ℤ) ≤ 4 * (r + 1) := h1
      _ ≤ 4 * (r + 1) * (p + 1) := by
          have h3 := Nat.mul_le_mul_left (4 * (r + 1)) hp1
          rw [mul_one] at h3
          exact h3
  have hvl : vsz (cvecVal l) ≤ 13 * (r + 1) * (p + 1) := MrgKit.vsz_cvecVal_le p r l hl.1 hl.2
  have hvr : vsz (cvecVal rw) ≤ 13 * (r + 1) * (p + 1) :=
    MrgKit.vsz_cvecVal_le p r rw hrw.1 hrw.2
  have hjr : i * 2 ^ sh < r := by
    have hpos : 0 < 2 ^ sh := by positivity
    have h2i : 2 * i < m := by
      have := Nat.lt_of_lt_of_le hiP (Nat.sub_le m (m / 2))
      omega
    have h4 : 2 * (i * 2 ^ sh) < 2 * r := by
      rw [← hmul]
      calc 2 * (i * 2 ^ sh) = (2 * i) * 2 ^ sh := by ring
        _ < m * 2 ^ sh := Nat.mul_lt_mul_of_pos_right h2i hpos
    omega
  have hR1 : 1 ≤ r + 1 := by omega
  have hP1 : 1 ≤ p + 1 := by omega
  set D : ℕ := 300 * Ksum * (r + 1) * (p + 1) + 300 * Ksum with hDdef
  have hkey : ∀ (a b : ℕ), a ≤ 300 * Ksum → b ≤ 300 * Ksum →
      a * (r + 1) * (p + 1) + b ≤ D := by
    intro a b ha hb
    rw [hDdef]
    have h1 : a * (r + 1) * (p + 1) ≤ 300 * Ksum * (r + 1) * (p + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ha)
    omega
  have hbig : 270 * Kr + Kpi + 4 * Kdr ≤ 300 * Ksum := by rw [hKsum]; omega
  -- step 1: unpack the tagged pair
  have s1 : WordR main uncP
      (fun vs => vs = (Val.cons (.int (i : ℤ)) (cvecVal l)) :: cvecVal rw :: Tail)
      (fun _ out => out = .int (i : ℤ) :: cvecVal l :: cvecVal rw :: Tail) (fun _ => D) := by
    refine MrgKit.uncStep (hunc main) (.int (i : ℤ)) (cvecVal l) (cvecVal rw :: Tail) D ?_
    simpa using hkey 0 Kuc (by omega) (by omega)
  -- step 2: rotate (`int i :: l :: rw` ↦ `rw :: int i :: l`)
  have s2 : WordR main (rollP 2)
      (fun vs => vs = .int (i : ℤ) :: cvecVal l :: cvecVal rw :: Tail)
      (fun _ out => out = cvecVal rw :: .int (i : ℤ) :: cvecVal l :: Tail) (fun _ => D) := by
    refine MrgKit.rollStep (hroll main) 2 (.int (i : ℤ) :: cvecVal l :: cvecVal rw :: Tail)
      (by simp) D ?_
    rw [sum_take3_cons, MrgKit.vsz_int']
    have hmid : Kr * 3 * (isz (i : ℤ) + (vsz (cvecVal l) + vsz (cvecVal rw)) + 1)
        ≤ (90 * Kr) * (r + 1) * (p + 1) + 3 * Kr := by
      nlinarith [hisz, hvl, hvr]
    exact le_trans hmid (hkey (90 * Kr) (3 * Kr) (by omega) (by omega))
  -- step 3: rotate (`rw :: int i :: l` ↦ `l :: rw :: int i`)
  have s3 : WordR main (rollP 2)
      (fun vs => vs = cvecVal rw :: .int (i : ℤ) :: cvecVal l :: Tail)
      (fun _ out => out = cvecVal l :: cvecVal rw :: .int (i : ℤ) :: Tail) (fun _ => D) := by
    refine MrgKit.rollStep (hroll main) 2 (cvecVal rw :: .int (i : ℤ) :: cvecVal l :: Tail)
      (by simp) D ?_
    rw [sum_take3_cons, MrgKit.vsz_int']
    have hmid : Kr * 3 * (vsz (cvecVal rw) + (isz (i : ℤ) + vsz (cvecVal l)) + 1)
        ≤ (90 * Kr) * (r + 1) * (p + 1) + 3 * Kr := by
      nlinarith [hisz, hvl, hvr]
    exact le_trans hmid (hkey (90 * Kr) (3 * Kr) (by omega) (by omega))
  -- step 4: the butterfly
  have s4 : WordR main pairP
      (fun vs => vs = cvecVal l :: cvecVal rw :: .int (i : ℤ) :: Tail)
      (fun _ out => ∃ (lo hi : List (ℤ × ℤ)),
        out = cvecVal lo :: cvecVal hi :: .int (i : ℤ) :: Tail ∧
        PackProps p r m sh sgn u e i lo hi) (fun _ => D) := by
    have hpair' := hpair main p r i sh sgn l rw rest (fun c => u i c)
      (fun c => u (i + m / 2) c) e hr1 hsgn hjr hpow hp2 hl.1 hrw.1 hl.2 hrw.2 hlapp hrwapp
    refine MrgKit.WordR_weaken hpair' (fun _ h => h) ?_ (fun _ _ => ?_)
    · intro vs out _ hout
      obtain ⟨v1, v2, hout', hv1, hv2, hi1, hi2, ha1, ha2⟩ := hout
      exact ⟨v1, v2, hout', ⟨⟨hv1, hi1⟩, ⟨hv2, hi2⟩, ha1, ha2⟩⟩
    · exact hkey Kpi Kpi (by omega) (by omega)
  -- step 5: bring the tag back on top
  have s5c : ∀ (lo hi : List (ℤ × ℤ)),
      vsz (cvecVal lo) ≤ 13 * (r + 1) * (p + 1) → vsz (cvecVal hi) ≤ 13 * (r + 1) * (p + 1) →
      WordR main (rollP 2)
        (fun vs => vs = cvecVal lo :: cvecVal hi :: .int (i : ℤ) :: Tail)
        (fun _ out => out = .int (i : ℤ) :: cvecVal lo :: cvecVal hi :: Tail) (fun _ => D) := by
    intro lo hi hlos hhis
    refine MrgKit.rollStep (hroll main) 2 (cvecVal lo :: cvecVal hi :: .int (i : ℤ) :: Tail)
      (by simp) D ?_
    rw [sum_take3_cons, MrgKit.vsz_int']
    have hmid : Kr * 3 * (vsz (cvecVal lo) + (vsz (cvecVal hi) + isz (i : ℤ)) + 1)
        ≤ (90 * Kr) * (r + 1) * (p + 1) + 3 * Kr := by
      nlinarith [hisz, hlos, hhis]
    exact le_trans hmid (hkey (90 * Kr) (3 * Kr) (by omega) (by omega))
  have s5 : WordR main (rollP 2)
      (fun vs => ∃ (lo hi : List (ℤ × ℤ)),
        vs = cvecVal lo :: cvecVal hi :: .int (i : ℤ) :: Tail ∧
        PackProps p r m sh sgn u e i lo hi)
      (fun _ out => ∃ (lo hi : List (ℤ × ℤ)),
        out = .int (i : ℤ) :: cvecVal lo :: cvecVal hi :: Tail ∧
        PackProps p r m sh sgn u e i lo hi) (fun _ => D) := by
    intro vs hvs s R hR
    obtain ⟨lo, hi, hvs', hprops⟩ := hvs
    have hlos := MrgKit.vsz_cvecVal_le p r lo hprops.1.1 hprops.1.2
    have hhis := MrgKit.vsz_cvecVal_le p r hi hprops.2.1.1 hprops.2.1.2
    obtain ⟨out, s', n, hpost, hev, hn, hstk, hoth⟩ := s5c lo hi hlos hhis vs hvs' s R hR
    exact ⟨out, s', n, ⟨lo, hi, hpost, hprops⟩, hev, hn, hstk, hoth⟩
  -- step 6: drop the tag
  have s6c : ∀ (lo hi : List (ℤ × ℤ)),
      WordR main kdrP
        (fun vs => vs = .int (i : ℤ) :: cvecVal lo :: cvecVal hi :: Tail)
        (fun _ out => out = cvecVal lo :: cvecVal hi :: Tail) (fun _ => D) := by
    intro lo hi
    refine MrgKit.kdropStep (hkdr main) (.int (i : ℤ) :: cvecVal lo :: cvecVal hi :: Tail)
      (by simp) D ?_
    have hsum : vsz ((.int (i : ℤ) :: cvecVal lo :: cvecVal hi :: Tail).headD .nil) = isz (i : ℤ) :=
      MrgKit.vsz_int' (i : ℤ)
    rw [hsum]
    have hmid : Kdr * (isz (i : ℤ) + 1) ≤ (4 * Kdr) * (r + 1) * (p + 1) + Kdr := by
      nlinarith [hisz]
    exact le_trans hmid (hkey (4 * Kdr) Kdr (by omega) (by omega))
  have s6 : WordR main kdrP
      (fun vs => ∃ (lo hi : List (ℤ × ℤ)),
        vs = .int (i : ℤ) :: cvecVal lo :: cvecVal hi :: Tail ∧
        PackProps p r m sh sgn u e i lo hi)
      (fun _ out => ∃ (lo hi : List (ℤ × ℤ)),
        out = cvecVal lo :: cvecVal hi :: Tail ∧
        PackProps p r m sh sgn u e i lo hi) (fun _ => D) := by
    intro vs hvs s R hR
    obtain ⟨lo, hi, hvs', hprops⟩ := hvs
    obtain ⟨out, s', n, hpost, hev, hn, hstk, hoth⟩ := s6c lo hi vs hvs' s R hR
    exact ⟨out, s', n, ⟨lo, hi, hpost, hprops⟩, hev, hn, hstk, hoth⟩
  -- step 7: re-pack
  have s7c : ∀ (lo hi : List (ℤ × ℤ)),
      WordR main consP
        (fun vs => vs = cvecVal lo :: cvecVal hi :: Tail)
        (fun _ out => out = Val.cons (cvecVal lo) (cvecVal hi) :: Tail) (fun _ => D) := by
    intro lo hi
    refine MrgKit.consStep (hcons main) (cvecVal lo) (cvecVal hi) Tail D ?_
    simpa using hkey 0 Kcv (by omega) (by omega)
  have s7 : WordR main consP
      (fun vs => ∃ (lo hi : List (ℤ × ℤ)),
        vs = cvecVal lo :: cvecVal hi :: Tail ∧
        PackProps p r m sh sgn u e i lo hi)
      (fun _ out => ∃ z : Val, out = z :: Tail ∧ PairQ p r m sh sgn u e
        (.cons (.int (i : ℤ)) (cvecVal l)) (cvecVal rw) z ∧
        vsz z ≤ 2 * (13 * (r + 1) * (p + 1)) + 1) (fun _ => D) := by
    intro vs hvs s R hR
    obtain ⟨lo, hi, hvs', hprops⟩ := hvs
    obtain ⟨out, s', n, hpost, hev, hn, hstk, hoth⟩ := s7c lo hi vs hvs' s R hR
    refine ⟨out, s', n, ⟨.cons (cvecVal lo) (cvecVal hi), hpost,
      ⟨i, l, rw, hiP, rfl, rfl, hl, hrw, hlapp, hrwapp, lo, hi, rfl, hprops⟩,
      vsz_pack_le p r lo hi hprops.1.1 hprops.2.1.1 hprops.1.2 hprops.2.1.2⟩,
      hev, hn, hstk, hoth⟩
  have c1 := composeEx s1 s2 (fun vs mid _ h2 => h2)
  have c2 := composeEx c1 s3 (fun vs mid _ h2 => by
    obtain ⟨m1, hinner, hlast⟩ := h2
    exact hlast)
  have c3 := composeEx c2 s4 (fun vs mid _ h2 => by
    obtain ⟨m1, hinner, hlast⟩ := h2
    exact hlast)
  have c4 := composeEx c3 s5 (fun vs mid _ h2 => by
    obtain ⟨m1, hinner, lo, hi, hout, hprops⟩ := h2
    exact ⟨lo, hi, hout, hprops⟩)
  have c5 := composeEx c4 s6 (fun vs mid _ h2 => by
    obtain ⟨m1, hinner, lo, hi, hout, hprops⟩ := h2
    exact ⟨lo, hi, hout, hprops⟩)
  have c6 := composeEx c5 s7 (fun vs mid _ h2 => by
    obtain ⟨m1, hinner, lo, hi, hout, hprops⟩ := h2
    exact ⟨lo, hi, hout, hprops⟩)
  refine MrgKit.WordR_weaken c6 (fun _ h => h) ?_ ?_
  · intro vs out _ hout
    obtain ⟨m1, hinner, z, hz, hpair, hvsz⟩ := hout
    exact ⟨z, hz, hpair, hvsz⟩
  · intro vs _
    rw [hDdef]
    nlinarith [Nat.zero_le Ksum, Nat.zero_le r, Nat.zero_le p]

/-! ## The `zipWith` pass of the block level pass -/

/-- Approximation of a `cvecVal`-list by `u` (the `ApproxSL` hypothesis, in `List` form). -/
theorem approxSL_iff (p r m : ℕ) (ws : List (List (ℤ × ℤ))) (u : Arr r) (e : ℝ) :
    ApproxSL p r m ws u e ↔
      ws.length = m ∧ ∀ q, q < m → ApproxVec p r (ws.getD q []) (fun c => u q c) e :=
  Iff.rfl

/-- **The `zipWith` pass of the block level pass.**  Zipping the tagged first half with the second
half by `pairWordBlk` bunches the two butterfly outputs of every pair into one value. -/
theorem blkLvlZip (hk : Work.SynFFT.KLib) (hp : Work.SynFFT.HasPair) :
    ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p r m sh : ℕ) (sgn : ℤ)
      (ws : List (List (ℤ × ℤ))) (u : Arr r) (e : ℝ) (rest : List Val) (L R : List Val),
      2 ≤ m → m * 2 ^ sh = 2 * r → (sgn = 1 ∨ sgn = -1) → 2 * r < 2 ^ p → ws.length = m →
      (∀ w ∈ ws, InDiscVec p r w) → ApproxSL p r m ws u e →
      L = (List.range (m - m / 2)).map
        (fun i : ℕ => Val.cons (.int (i : ℤ)) ((cvecs ws).getD i .nil)) →
      R = cvecs (ws.drop (m / 2)) →
      WordR main prog
        (fun vs => vs = ofList L :: ofList R :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) ::
          .int (p : ℤ) :: .int (m : ℤ) :: rest)
        (fun _ out => ∃ zs : List Val,
          out = ofList zs :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) ::
            .int (p : ℤ) :: .int (m : ℤ) :: rest ∧
          zs.length = m - m / 2 ∧
          ∀ i < m - m / 2, PackP p r m sh sgn u e i (zs.getD i .nil))
        (fun _ => K * (m + 1) * (((r + 1) * (p + 1)) + 1) + K) := by
  obtain ⟨zipP, Kz, hzip⟩ := hk.zipWith
  obtain ⟨pwP, Kpw, hpw⟩ := pairWordBlk hk hp
  refine ⟨zipP pwP, Kpw + 29 * Kz + 1, ?_⟩
  intro main p r m sh sgn ws u e rest L R h2 hmul hsgn hp2 hws hind happ hLeq hReq
  have hP1 : 1 ≤ p + 1 := by omega
  have hr1 : 1 ≤ r := by
    have h3 : 1 ≤ 2 ^ sh := Nat.one_le_two_pow
    have h1 : 2 ≤ 2 * r := by
      calc (2 : ℕ) = 2 * 1 := by ring
        _ ≤ m * 2 ^ sh := Nat.mul_le_mul h2 h3
        _ = 2 * r := hmul
    omega
  have hA2 : 2 ≤ (r + 1) * (p + 1) := by
    calc (2 : ℕ) = 2 * 1 := by ring
      _ ≤ (r + 1) * (p + 1) := Nat.mul_le_mul (by omega) hP1
  have hmP : m - m / 2 ≤ m := Nat.sub_le _ _
  have hm_le : m ≤ 2 * r := by
    have h3 : 1 ≤ 2 ^ sh := Nat.one_le_two_pow
    calc m = m * 1 := by ring
      _ ≤ m * 2 ^ sh := Nat.mul_le_mul_left m h3
      _ = 2 * r := hmul
  have hLlen : L.length = m - m / 2 := by rw [hLeq]; simp
  have hRlen : R.length = m - m / 2 := by
    rw [hReq]
    show (cvecs (ws.drop (m / 2))).length = m - m / 2
    rw [cvecs, List.length_map, List.length_drop, hws]
  have hlen : L.length = R.length := by rw [hLlen, hRlen]
  have hisz : ∀ i : ℕ, i < m - m / 2 → isz (i : ℤ) ≤ 4 * (r + 1) * (p + 1) := by
    intro i hiP
    have him : i < 2 * r := lt_of_lt_of_le (lt_of_lt_of_le hiP hmP) hm_le
    have h1 := isz_lt_two_r_le i r him
    calc isz (i : ℤ) ≤ 4 * (r + 1) := h1
      _ ≤ 4 * (r + 1) * (p + 1) := by
          have h3 := Nat.mul_le_mul_left (4 * (r + 1)) hP1
          rw [mul_one] at h3
          exact h3
  -- the per-index input predicate
  have hPidx : ∀ i < L.length, PairP p r m sh u e (L.getD i .nil) (R.getD i .nil) := by
    intro i hi
    have hiP : i < m - m / 2 := by rw [hLlen] at hi; exact hi
    have him : i < m := lt_of_lt_of_le hiP hmP
    have hsplit : m - m / 2 + m / 2 = m := Nat.sub_add_cancel (Nat.div_le_self m 2)
    have his : i + m / 2 < m := by omega
    have hLget : L.getD i .nil
        = Val.cons (.int (i : ℤ)) (cvecVal (ws.getD i [])) := by
      rw [hLeq,
        getD_map_range (fun i : ℕ => Val.cons (.int (i : ℤ)) ((cvecs ws).getD i .nil)) Val.nil hiP,
        getD_cvecs_xhasBlkLvlAux]
    have hRget : R.getD i .nil = cvecVal (ws.getD (i + m / 2) []) := by
      rw [hReq, getD_cvecs_xhasBlkLvlAux, getD_drop', show m / 2 + i = i + m / 2 from by omega]
    have hin1 : InVec p r (ws.getD i []) := inVec_getD hind (by rw [hws]; exact him)
    have hin2 : InVec p r (ws.getD (i + m / 2) []) :=
      inVec_getD hind (by rw [hws]; exact his)
    exact ⟨i, ws.getD i [], ws.getD (i + m / 2) [], hiP, hLget, hRget, hin1, hin2,
      happ.2 i him, happ.2 (i + m / 2) his⟩
  -- the element size bound
  have hLb' : ∀ x ∈ L ++ R, vsz x ≤ 2 * (13 * (r + 1) * (p + 1)) + 1 := by
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (by rw [hLeq] at hx; exact hx)
      have hiP : i < m - m / 2 := by simpa using hi
      have hmem : ws.getD i [] ∈ ws := by
        rw [List.getD_eq_getElem ws ([] : List (ℤ × ℤ))
          (by rw [hws]; exact lt_of_lt_of_le hiP hmP)]
        exact List.mem_iff_getElem.mpr ⟨i, by rw [hws]; exact lt_of_lt_of_le hiP hmP, rfl⟩
      have hin : InVec p r (ws.getD i []) := hind _ hmem
      have h1 := vsz_lab_le p r i (ws.getD i []) hin.1 hin.2
      have h2 := hisz i hiP
      rw [getD_cvecs_xhasBlkLvlAux]
      nlinarith [h1, h2]
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp (by rw [hReq] at hx; exact hx)
      have hmem : w ∈ ws := List.mem_of_mem_drop hw
      have hin : InVec p r w := hind _ hmem
      have h1 := MrgKit.vsz_cvecVal_le p r w hin.1 hin.2
      nlinarith [h1]
  -- the inner word
  have hq : ∀ x y, PairP p r m sh u e x y →
      WordR main pwP (fun vs => vs = x :: y :: (.int (sh : ℤ) :: .int sgn :: .int (r : ℤ) ::
        .int (p : ℤ) :: .int (m : ℤ) :: rest))
        (fun _ out => ∃ z, out = z :: (.int (sh : ℤ) :: .int sgn :: .int (r : ℤ) ::
          .int (p : ℤ) :: .int (m : ℤ) :: rest) ∧ PairQ p r m sh sgn u e x y z ∧
          vsz z ≤ 2 * (13 * (r + 1) * (p + 1)) + 1)
        (fun _ => Kpw * (r + 1) * (p + 1) + Kpw) := by
    intro x y hxy
    exact hpw main p r m sh sgn u e (.int (m : ℤ) :: rest) x y h2 hmul hp2 hsgn hxy
  have hmain := hzip main pwP (.int (sh : ℤ) :: .int sgn :: .int (r : ℤ) ::
      .int (p : ℤ) :: .int (m : ℤ) :: rest) (PairP p r m sh u e) (PairQ p r m sh sgn u e)
    (Kpw * (r + 1) * (p + 1) + Kpw) (2 * (13 * (r + 1) * (p + 1)) + 1) hq L R hlen hPidx hLb'
  refine MrgKit.WordR_weaken hmain (fun _ h => h) ?_ ?_
  · intro vs out _ hout
    obtain ⟨zs, hout', hlen', hQ⟩ := hout
    refine ⟨zs, hout', by rw [hlen', hLlen], ?_⟩
    intro i hi
    have hLget : L.getD i .nil
        = Val.cons (.int (i : ℤ)) (cvecVal (ws.getD i [])) := by
      rw [hLeq,
        getD_map_range (fun i : ℕ => Val.cons (.int (i : ℤ)) ((cvecs ws).getD i .nil)) Val.nil hi,
        getD_cvecs_xhasBlkLvlAux]
    obtain ⟨m1, l1, rw1, hiP1, hxl, hyr, hin1, hin2, happ1, happ2, lo, hiv, hz, hprops⟩ :=
      hQ i (by rw [hLlen]; exact hi)
    have hzi : m1 = i := by
      have h1 : Val.cons (.int (m1 : ℤ)) (cvecVal l1) = Val.cons (.int (i : ℤ)) (cvecVal (ws.getD i [])) := by
        rw [← hxl, hLget]
      injection h1 with h2 _
      have h3 : ((m1 : ℤ)) = ((i : ℤ)) := by injection h2
      exact_mod_cast h3
    rw [hzi] at hprops
    exact ⟨lo, hiv, hz, hprops⟩
  · intro vs _
    have hE : Kpw * (r + 1) * (p + 1) + Kpw + Kz * (2 * (13 * (r + 1) * (p + 1)) + 1 + 1)
        ≤ (Kpw + 28 * Kz) * (((r + 1) * (p + 1)) + 1) := by
      have h26 : Kz * (2 * (13 * (r + 1) * (p + 1)) + 1 + 1)
          ≤ Kz * (28 * ((r + 1) * (p + 1)) + 28) := by
        refine Nat.mul_le_mul_left Kz ?_
        nlinarith [Nat.zero_le ((r + 1) * (p + 1))]
      have h2 : Kpw * (r + 1) * (p + 1) + Kpw = Kpw * (((r + 1) * (p + 1)) + 1) := by ring
      have h3' : Kpw * (((r + 1) * (p + 1)) + 1)
            + Kz * (2 * (13 * (r + 1) * (p + 1)) + 1 + 1)
          ≤ (Kpw + 28 * Kz) * (((r + 1) * (p + 1)) + 1) := by
        rw [show (Kpw + 28 * Kz) * (((r + 1) * (p + 1)) + 1)
            = Kpw * (((r + 1) * (p + 1)) + 1) + Kz * (28 * ((r + 1) * (p + 1)) + 28) from by ring]
        exact Nat.add_le_add_left h26 _
      rw [h2]
      exact h3'
    have hLm : L.length ≤ m + 1 := by rw [hLlen]; omega
    have h3 : L.length * (Kpw * (r + 1) * (p + 1) + Kpw
          + Kz * (2 * (13 * (r + 1) * (p + 1)) + 1 + 1))
        ≤ ((Kpw + 28 * Kz) * (m + 1)) * (((r + 1) * (p + 1)) + 1) := by
      calc L.length * (Kpw * (r + 1) * (p + 1) + Kpw
            + Kz * (2 * (13 * (r + 1) * (p + 1)) + 1 + 1))
          ≤ (m + 1) * ((Kpw + 28 * Kz) * (((r + 1) * (p + 1)) + 1)) :=
            Nat.mul_le_mul hLm hE
        _ = ((Kpw + 28 * Kz) * (m + 1)) * (((r + 1) * (p + 1)) + 1) := by ring
    have h4 : ((Kpw + 28 * Kz) * (m + 1)) * (((r + 1) * (p + 1)) + 1)
        ≤ ((Kpw + 29 * Kz + 1) * (m + 1)) * (((r + 1) * (p + 1)) + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right (m + 1) (by omega))
    have h5 : Kz ≤ Kpw + 29 * Kz + 1 := by omega
    exact Nat.add_le_add (le_trans h3 h4) h5


end Work.SynFFT

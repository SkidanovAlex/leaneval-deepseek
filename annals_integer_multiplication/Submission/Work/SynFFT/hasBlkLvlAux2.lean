import Mathlib
import Submission.Work.SynFFT.hasBlkLvlAux

/-!
# `Work.SynFFT.hasBlkLvlAux2`: assembly of the block level pass

The three list-level pieces of the block level pass are stated as `Prop`s
(`PrefixStmt`, `SuffixStmt`, `ReadStmt`) so that the assembly `hasBlkLvl_aux` can be stated and
proved independently of the modules that prove them.  `Submission/Work/SynFFT/hasBlkLvl.lean`
instantiates them with the proved pieces.

The pipeline (one level pass on a block of `m` coefficient vectors):

1. `blkRollShift`: move the integer `m` to the end of the parameter block;
2. `PrefixStmt` (prefix): split the block into the tagged first `m - m/2` elements and the last
   `m/2` ones and tag the first list with the indices;
3. `blkLvlZip`: zip the two halves with `pairWordBlk`, bunching both butterfly outputs per pair;
4. `blkFixParams`: bring `m` back in front of the parameter block;
5. `SuffixStmt` (suffix): extract the two components of each bunched value, keep the first `m/2`
   "sum" outputs, and append the "difference" outputs;
6. `ReadStmt` (maths): read the resulting list as `lvlN r m sgn u` with error `e+1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Work.SynFFT

open HvdH

local infixl:68 " ;;; " => HvdH.Cmd.seq

/-- Interface of the prefix piece of the block level pass. -/
def PrefixStmt : Prop :=
  ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p r m sh : ℕ) (sgn : ℤ)
      (ws : List (List (ℤ × ℤ))) (rest : List Val),
      2 ≤ m → m * 2 ^ sh = 2 * r → 2 * r < 2 ^ p → ws.length = m →
      (∀ w ∈ ws, InDiscVec p r w) →
      WordR main prog
        (fun vs => vs = ofList (cvecs ws) :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) ::
          .int (p : ℤ) :: .int (m : ℤ) :: rest)
        (fun vs out => ∃ (L R : List Val),
          out = ofList L :: ofList R :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) ::
            .int (p : ℤ) :: .int (m : ℤ) :: rest ∧
          R = cvecs (ws.drop (m / 2)) ∧
          L = (List.range (m - m / 2)).map
            (fun i : ℕ => Val.cons (.int (i : ℤ)) ((cvecs ws).getD i .nil)))
        (fun _ => K * (m * (r + 1) * (p + 1) + 1) + K)

/-- Interface of the suffix piece of the block level pass. -/
def SuffixStmt : Prop :=
  ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (m Lb : ℕ) (Z rest : List Val),
      2 ≤ m → Z.length = m - m / 2 → (∀ v ∈ Z, vsz v ≤ Lb) →
      (∀ v ∈ Z, ∃ a b : Val, v = .cons a b) →
      WordR main prog
        (fun vs => vs = ofList Z :: .int (m : ℤ) :: rest)
        (fun vs out => ∃ (Y : List Val),
          out = ofList Y :: .int (m : ℤ) :: rest ∧
          Y = (Z.map vfst).take (m / 2) ++ Z.map vsnd)
        (fun _ => K * (m * (Lb + 1) + 1) + K)

/-- Interface of the maths piece of the block level pass. -/
def ReadStmt : Prop :=
  ∀ (p r m sh : ℕ) (sgn : ℤ) (u : Arr r) (e : ℝ)
    (lowsVecs highsVecs : List (List (ℤ × ℤ))),
    (2 ≤ m) → (m * 2 ^ sh = 2 * r) → (2 * r < 2 ^ p) →
    (lowsVecs.length = m - m / 2) → (highsVecs.length = m - m / 2) →
    (∀ i, i < m - m / 2 → ∀ c : Fin r,
      (2 : ℝ) ^ p * ‖fxC p ((lowsVecs.getD i []).getD (c : ℕ) (0, 0)) -
        (u i c + u (i + m / 2) c) / 2‖ ≤ e + 1) →
    (∀ i, i < m - m / 2 → ∀ c : Fin r,
      (2 : ℝ) ^ p * ‖fxC p ((highsVecs.getD i []).getD (c : ℕ) (0, 0)) -
        yMul r (sgn * (((i * 2 ^ sh : ℕ)) : ℤ)) (fun c' => (u i c' - u (i + m / 2) c') / 2) c‖ ≤ e + 1) →
    ApproxSL p r m (lowsVecs.take (m / 2) ++ highsVecs) (lvlN r m sgn u) (e + 1)

/-! ## Arithmetic helpers -/

/-- Right-multiplication is monotone. -/
theorem mrm (a b c : ℕ) (h : a ≤ b) : a * c ≤ b * c := Nat.mul_le_mul h (le_refl c)

/-- `C₁ * M + C₂ ≤ C * M + C` when both constants are at most `C`. -/
theorem mul_add_bound (C1 C2 C M : ℕ) (h1 : C1 ≤ C) (h2 : C2 ≤ C) : C1 * M + C2 ≤ C * M + C :=
  Nat.add_le_add (Nat.mul_le_mul h1 (le_refl M)) h2

/-- An element bound times a bound on the list length. -/
theorem vsz_ofList_le (xs : List Val) (B N : ℕ) (h : ∀ v ∈ xs, vsz v ≤ B) (hN : xs.length ≤ N) :
    vsz (ofList xs) ≤ N * (B + 1) + 1 :=
  MrgKit.vsz_ofList_le_of_bound xs B N h hN

/-- Bound of an `isz` for a value of size at most `2r`. -/
theorem isz_le_two_r (x r : ℕ) (h : x ≤ 2 * r) : isz (x : ℤ) ≤ 4 * (r + 1) := by
  have h2 : (2 * r).size ≤ r.size + 1 := by
    refine (Nat.size_le).mpr ?_
    rw [pow_succ]
    nlinarith [Nat.lt_size_self r]
  have h1 : x.size ≤ r.size + 1 := le_trans (Nat.size_le_size h) h2
  have h3 : r.size ≤ r := (Nat.size_le).mpr Nat.lt_two_pow_self
  have h4 : isz (x : ℤ) = x.size + 2 := rfl
  omega

/-- Bound of an `isz` for an arbitrary natural. -/
theorem isz_le_self (x : ℕ) : isz (x : ℤ) ≤ 3 * (x + 1) := by
  have h : x.size ≤ x := (Nat.size_le).mpr Nat.lt_two_pow_self
  have h4 : isz (x : ℤ) = x.size + 2 := rfl
  omega

/-! ## The assembly -/

/-- **The block level pass**, assembled from the pieces. -/
theorem hasBlkLvl_aux (hk : Work.SynFFT.KLib) (hi : HvdH.IntLib) (hl : HvdH.LayoutLib)
    (hf : HvdH.FxLib) (hp : Work.SynFFT.HasPair)
    (hpre : PrefixStmt) (hsuf : SuffixStmt) (hread : ReadStmt) : Work.SynFFT.HasBlkLvl := by
  obtain ⟨preP, Kpre, hpre'⟩ := hpre
  obtain ⟨sufP, Ksuf, hsuf'⟩ := hsuf
  obtain ⟨zipP, Kzip, hzip'⟩ := blkLvlZip hk hp
  obtain ⟨rollP, Kr, hroll⟩ := hk.roll
  obtain ⟨swapP, Ksw, hswap⟩ := hk.swap
  set S : ℕ := Kpre + Kzip + Ksuf + Ksw + Kr + 1 with hS
  set BIG : ℕ := 1000000 * S with hBIG
  refine ⟨((rollP 5 ;;; rollP 5 ;;; rollP 5 ;;; rollP 5 ;;; rollP 4) ;;; preP ;;; zipP)
      ;;; ((rollP 5 ;;; swapP) ;;; sufP), 10 * BIG + 1, ?_⟩
  intro main p r m sh sgn ws u e rest h2 hmul hsgn hp2 hws hind happ
  set A : ℕ := (r + 1) * (p + 1) with hA
  have hA1 : 1 ≤ A := by
    rw [hA]
    simpa using Nat.mul_le_mul (show 1 ≤ r + 1 by omega) (show 1 ≤ p + 1 by omega)
  have hrp : r + 1 ≤ A := by
    rw [hA]
    simpa using Nat.mul_le_mul_left (r + 1) (show 1 ≤ p + 1 by omega)
  have hpp : p + 1 ≤ A := by
    rw [hA]
    simpa using mrm (p + 1) (r + 1) (p + 1) (show 1 ≤ r + 1 by omega)
  have hkr : Kr ≤ S := by rw [hS]; omega
  have hkpre : Kpre ≤ S := by rw [hS]; omega
  have hkzip : Kzip ≤ S := by rw [hS]; omega
  have hksuf : Ksuf ≤ S := by rw [hS]; omega
  have hksw : Ksw ≤ S := by rw [hS]; omega
  have hSB : S ≤ BIG := by
    rw [hBIG]; exact le_mul_of_one_le_left (Nat.zero_le S) (by norm_num)
  have hkrB : Kr ≤ BIG := le_trans hkr hSB
  have hkpreB : Kpre ≤ BIG := le_trans hkpre hSB
  have hkzipB : Kzip ≤ BIG := le_trans hkzip hSB
  have hksufB : Ksuf ≤ BIG := le_trans hksuf hSB
  have hkswB : Ksw ≤ BIG := le_trans hksw hSB
  have hmA : 1 ≤ m * A := by
    simpa using Nat.mul_le_mul (show 1 ≤ m by omega) hA1
  -- sizes of the parameters
  have hmm : m ≤ 2 * r := by
    have h3 : 1 ≤ 2 ^ sh := Nat.one_le_two_pow
    calc m = m * 1 := by ring
      _ ≤ m * 2 ^ sh := Nat.mul_le_mul_left m h3
      _ = 2 * r := hmul
  have hiszm : isz (m : ℤ) ≤ 4 * A := by
    have h1 := isz_le_two_r m r hmm
    have h2 : 4 * (r + 1) ≤ 4 * A := Nat.mul_le_mul_left 4 hrp
    linarith
  have hiszsh : isz (sh : ℤ) ≤ 4 * A := by
    have h2shr : 2 ^ sh ≤ 2 * r := by
      calc 2 ^ sh = 1 * 2 ^ sh := by ring
        _ ≤ m * 2 ^ sh := Nat.mul_le_mul (show 1 ≤ m by omega) (le_refl _)
        _ = 2 * r := hmul
    have hlt : sh ≤ 2 * r := le_of_lt (lt_of_lt_of_le Nat.lt_two_pow_self h2shr)
    have h1 := isz_le_two_r sh r hlt
    have h2 : 4 * (r + 1) ≤ 4 * A := Nat.mul_le_mul_left 4 hrp
    linarith
  have hiszr : isz (r : ℤ) ≤ 4 * A := by
    have h1 : isz (r : ℤ) ≤ 3 * (r + 1) := isz_le_self r
    have h2 : 3 * (r + 1) ≤ 4 * A := by nlinarith [hrp]
    linarith
  have hiszp : isz (p : ℤ) ≤ 4 * A := by
    have h1 : isz (p : ℤ) ≤ 3 * (p + 1) := isz_le_self p
    have h2 : 3 * (p + 1) ≤ 4 * A := by nlinarith [hpp]
    linarith
  have hiszsgn : isz sgn ≤ 4 * A := by
    have h1 : isz sgn ≤ 3 := by rcases hsgn with h | h <;> (rw [h]; decide)
    have h2 : (3 : ℕ) ≤ 4 * A := by nlinarith [hA1]
    linarith
  have hVszA : vsz (ofList (cvecs ws)) ≤ 100 * (m * A) + 100 := by
    have h1 := vsz_ofList_cvecs_le p r m ws hws hind
    have h2 : 13 * (r + 1) * (p + 1) = 13 * A := by rw [hA]; ring
    nlinarith [h1, h2, hmA, hA1, Nat.zero_le m]
  -- ===== step 1: move `m` to the end of the parameter block =====
  set S1 : ℕ := vsz (ofList (cvecs ws)) + vsz (Val.int (m : ℤ)) + vsz (Val.int (sh : ℤ))
      + vsz (Val.int sgn) + vsz (Val.int (r : ℤ)) + vsz (Val.int (p : ℤ)) with hS1
  have hS1le : S1 + 1 ≤ 200 * (m * A) + 200 := by
    have h5 : vsz (Val.int (m : ℤ)) = isz (m : ℤ) := MrgKit.vsz_int' _
    have h6 : vsz (Val.int (sh : ℤ)) = isz (sh : ℤ) := MrgKit.vsz_int' _
    have h7 : vsz (Val.int sgn) = isz sgn := MrgKit.vsz_int' _
    have h8 : vsz (Val.int (r : ℤ)) = isz (r : ℤ) := MrgKit.vsz_int' _
    have h9 : vsz (Val.int (p : ℤ)) = isz (p : ℤ) := MrgKit.vsz_int' _
    rw [hS1, h5, h6, h7, h8, h9]
    nlinarith [hVszA, hiszm, hiszsh, hiszsgn, hiszr, hiszp, hmA, hA1, Nat.zero_le m]
  have hD1le : 5 * (Kr * 6 * (S1 + 1)) ≤ BIG * (m * A) + BIG := by
    have e1 : 5 * (Kr * 6 * (S1 + 1)) = 30 * Kr * (S1 + 1) := by ring
    have h2 : 30 * Kr * (S1 + 1) ≤ 30 * Kr * (200 * (m * A) + 200) :=
      Nat.mul_le_mul_left (30 * Kr) hS1le
    have e2 : 30 * Kr * (200 * (m * A) + 200) = 6000 * Kr * (m * A) + 6000 * Kr := by ring
    have h3 : 6000 * Kr ≤ BIG := by rw [hBIG, hS]; nlinarith
    calc 5 * (Kr * 6 * (S1 + 1)) = 30 * Kr * (S1 + 1) := e1
      _ ≤ 30 * Kr * (200 * (m * A) + 200) := h2
      _ = 6000 * Kr * (m * A) + 6000 * Kr := e2
      _ ≤ BIG * (m * A) + BIG := mul_add_bound _ _ BIG (m * A) h3 h3
  have step1 : WordR main (rollP 5 ;;; rollP 5 ;;; rollP 5 ;;; rollP 5 ;;; rollP 4)
      (fun vs => vs = ofList (cvecs ws) :: Val.int (m : ℤ) :: Val.int (sh : ℤ) ::
        Val.int sgn :: Val.int (r : ℤ) :: Val.int (p : ℤ) :: rest)
      (fun _ out => out = ofList (cvecs ws) :: Val.int (sh : ℤ) :: Val.int sgn ::
        Val.int (r : ℤ) :: Val.int (p : ℤ) :: Val.int (m : ℤ) :: rest)
      (fun _ => 5 * (Kr * 6 * (S1 + 1))) :=
    blkRollShift (main := main) (hroll main) (ofList (cvecs ws)) (Val.int (sh : ℤ)) (Val.int sgn)
      (Val.int (r : ℤ)) (Val.int (p : ℤ)) (Val.int (m : ℤ)) rest S1 (5 * (Kr * 6 * (S1 + 1)))
      (le_refl S1) (le_refl _)
  -- ===== step 2: the prefix =====
  have step2 := hpre' main p r m sh sgn ws rest h2 hmul hp2 hws hind
  have hD2le : Kpre * (m * (r + 1) * (p + 1) + 1) + Kpre ≤ BIG * (m * A) + BIG := by
    have e1 : Kpre * (m * (r + 1) * (p + 1) + 1) + Kpre = Kpre * (m * A) + 2 * Kpre := by
      rw [hA]; ring
    rw [e1]
    have h2 : 2 * Kpre ≤ BIG := by rw [hBIG, hS]; nlinarith
    exact mul_add_bound _ _ BIG (m * A) hkpreB h2
  have c12 := composeEx (MrgKit.WordR_weaken step1 (fun _ h => h) (fun _ _ _ h => h)
      (fun _ _ => hD1le)) step2 (fun vs mid _ h2' => h2')
  -- ===== step 3: the zip pass (repackaged with an existential precondition) =====
  have step3 : WordR main zipP
      (fun vs => ∃ (L R : List Val),
        vs = ofList L :: ofList R :: Val.int (sh : ℤ) :: Val.int sgn ::
          Val.int (r : ℤ) :: Val.int (p : ℤ) :: Val.int (m : ℤ) :: rest ∧
        R = cvecs (ws.drop (m / 2)) ∧
        L = (List.range (m - m / 2)).map
            (fun i : ℕ => Val.cons (.int (i : ℤ)) ((cvecs ws).getD i .nil)))
      (fun _ out => ∃ zs : List Val,
        out = ofList zs :: Val.int (sh : ℤ) :: Val.int sgn ::
          Val.int (r : ℤ) :: Val.int (p : ℤ) :: Val.int (m : ℤ) :: rest ∧
        zs.length = m - m / 2 ∧
        ∀ i < m - m / 2, PackP p r m sh sgn u e i (zs.getD i .nil))
      (fun _ => Kzip * (m + 1) * (A + 1) + Kzip) := by
    intro vs hvs s R0 hR0
    obtain ⟨L, R, hvs', hReq, hLeq⟩ := hvs
    have h := hzip' main p r m sh sgn ws u e rest L R h2 hmul hsgn hp2 hws hind happ hLeq hReq
    have h' : Kzip * (m + 1) * (((r + 1) * (p + 1)) + 1) + Kzip
        = Kzip * (m + 1) * (A + 1) + Kzip := by rw [hA]
    rw [h'] at h
    exact h vs hvs' s R0 hR0
  have hD3le : Kzip * (m + 1) * (A + 1) + Kzip ≤ BIG * (m * A) + BIG := by
    have h4 : (m + 1) * (A + 1) ≤ 4 * (m * A) := by nlinarith [hA1, Nat.zero_le m]
    have e1 : Kzip * (m + 1) * (A + 1) = Kzip * ((m + 1) * (A + 1)) := by ring
    have h5 : Kzip * ((m + 1) * (A + 1)) ≤ Kzip * (4 * (m * A)) := Nat.mul_le_mul_left _ h4
    have e2 : Kzip * (4 * (m * A)) = 4 * Kzip * (m * A) := by ring
    have h6 : 4 * Kzip ≤ BIG := by rw [hBIG, hS]; nlinarith
    calc Kzip * (m + 1) * (A + 1) + Kzip = Kzip * ((m + 1) * (A + 1)) + Kzip := by rw [e1]
      _ ≤ Kzip * (4 * (m * A)) + Kzip := Nat.add_le_add h5 (le_refl _)
      _ = 4 * Kzip * (m * A) + Kzip := by rw [e2]
      _ ≤ BIG * (m * A) + BIG := mul_add_bound _ _ BIG (m * A) h6 hkzipB
  have c123 := composeEx c12 step3 (fun vs mid _ h2' => by
    obtain ⟨m1, hA1', hB1'⟩ := h2'
    obtain ⟨L, R, hout, hReq, hLeq⟩ := hB1'
    exact ⟨L, R, hout, hReq, hLeq⟩)
  -- ===== steps 4 and 5, parameterised by the list `zs` =====
  have step45 : WordR main ((rollP 5 ;;; swapP) ;;; sufP)
      (fun vs => ∃ zs : List Val,
        vs = ofList zs :: Val.int (sh : ℤ) :: Val.int sgn ::
          Val.int (r : ℤ) :: Val.int (p : ℤ) :: Val.int (m : ℤ) :: rest ∧
        zs.length = m - m / 2 ∧
        ∀ i < m - m / 2, PackP p r m sh sgn u e i (zs.getD i .nil))
      (fun vs out => ∃ zs : List Val,
        vs = ofList zs :: Val.int (sh : ℤ) :: Val.int sgn ::
          Val.int (r : ℤ) :: Val.int (p : ℤ) :: Val.int (m : ℤ) :: rest ∧
        zs.length = m - m / 2 ∧
        (∀ i < m - m / 2, PackP p r m sh sgn u e i (zs.getD i .nil)) ∧
        ∃ Y : List Val, out = ofList Y :: Val.int (m : ℤ) :: Val.int (sh : ℤ) ::
          Val.int sgn :: Val.int (r : ℤ) :: Val.int (p : ℤ) :: rest ∧
        Y = (zs.map vfst).take (m / 2) ++ zs.map vsnd)
      (fun _ => (BIG * (m * A) + BIG) + (BIG * (m * A) + BIG)) := by
    intro vs hvs s R0 hR0
    obtain ⟨zs, hvs', hzslen, hzpack⟩ := hvs
    set Lb : ℕ := 2 * (13 * (r + 1) * (p + 1)) + 1 with hLb
    have hLbA : Lb ≤ 27 * A + 1 := by
      rw [hLb]
      have h2 : 26 * (r + 1) * (p + 1) = 26 * A := by rw [hA]; ring
      have e : 2 * (13 * (r + 1) * (p + 1)) + 1 = 26 * (r + 1) * (p + 1) + 1 := by ring
      rw [e]
      omega
    have hLb30 : Lb + 1 ≤ 30 * A := by
      have h2 : 28 ≤ 30 * A := by nlinarith [hA1]
      linarith [hLbA, h2]
    have hzsz : ∀ v ∈ zs, vsz v ≤ Lb := by
      intro v hv
      obtain ⟨i, hi, hvi⟩ := List.mem_iff_getElem.mp hv
      have hiP : i < m - m / 2 := by rw [hzslen] at hi; exact hi
      obtain ⟨hz1, hzprops⟩ := Classical.choose_spec (Classical.choose_spec (hzpack i hiP))
      have hgi : zs.getD i .nil = zs[i] := List.getD_eq_getElem zs .nil hi
      have hz1' : zs[i] = Val.cons (cvecVal (Classical.choose (hzpack i hiP)))
          (cvecVal (Classical.choose (Classical.choose_spec (hzpack i hiP)))) := by
        rw [← hgi]; exact hz1
      rw [← hvi, hz1', hLb]
      exact vsz_pack_le p r _ _ hzprops.1.1 hzprops.2.1.1 hzprops.1.2 hzprops.2.1.2
    have hzcons : ∀ v ∈ zs, ∃ a b : Val, v = Val.cons a b := by
      intro v hv
      obtain ⟨i, hi, hvi⟩ := List.mem_iff_getElem.mp hv
      have hiP : i < m - m / 2 := by rw [hzslen] at hi; exact hi
      obtain ⟨hz1, _⟩ := Classical.choose_spec (Classical.choose_spec (hzpack i hiP))
      have hgi : zs.getD i .nil = zs[i] := List.getD_eq_getElem zs .nil hi
      have hvv : v = Val.cons (cvecVal (Classical.choose (hzpack i hiP)))
          (cvecVal (Classical.choose (Classical.choose_spec (hzpack i hiP)))) := by
        rw [← hvi, ← hgi]
        exact hz1
      exact ⟨cvecVal (Classical.choose (hzpack i hiP)),
        cvecVal (Classical.choose (Classical.choose_spec (hzpack i hiP))), hvv⟩
    have hvszzs : vsz (ofList zs) ≤ (m + 1) * (Lb + 1) + 1 :=
      vsz_ofList_le zs Lb (m + 1) hzsz (by rw [hzslen]; omega)
    have hzslb : vsz (ofList zs) ≤ 100 * (m * A) + 100 := by
      have h1 : (m + 1) * (Lb + 1) + 1 ≤ 100 * (m * A) + 100 := by
        have h2 : Lb + 1 ≤ 30 * A := hLb30
        nlinarith [h2, hmA, hA1, Nat.zero_le m]
      linarith [hvszzs, h1]
    set S4 : ℕ := vsz (ofList zs) + vsz (Val.int (sh : ℤ)) + vsz (Val.int sgn)
        + vsz (Val.int (r : ℤ)) + vsz (Val.int (p : ℤ)) + vsz (Val.int (m : ℤ)) with hS4
    have hS4le : S4 + 1 ≤ 200 * (m * A) + 200 := by
      have h5 : vsz (Val.int (m : ℤ)) = isz (m : ℤ) := MrgKit.vsz_int' _
      have h6 : vsz (Val.int (sh : ℤ)) = isz (sh : ℤ) := MrgKit.vsz_int' _
      have h7 : vsz (Val.int sgn) = isz sgn := MrgKit.vsz_int' _
      have h8 : vsz (Val.int (r : ℤ)) = isz (r : ℤ) := MrgKit.vsz_int' _
      have h9 : vsz (Val.int (p : ℤ)) = isz (p : ℤ) := MrgKit.vsz_int' _
      rw [hS4, h5, h6, h7, h8, h9]
      nlinarith [hzslb, hiszm, hiszsh, hiszsgn, hiszr, hiszp, hmA, hA1, Nat.zero_le m]
    have hD4le : Kr * 6 * (S4 + 1) + Ksw * (S4 + 1) ≤ BIG * (m * A) + BIG := by
      have e1 : Kr * 6 * (S4 + 1) + Ksw * (S4 + 1) = (6 * Kr + Ksw) * (S4 + 1) := by ring
      rw [e1]
      have h2 : (6 * Kr + Ksw) * (S4 + 1) ≤ (6 * Kr + Ksw) * (200 * (m * A) + 200) :=
        Nat.mul_le_mul_left _ hS4le
      have e2 : (6 * Kr + Ksw) * (200 * (m * A) + 200)
          = 200 * (6 * Kr + Ksw) * (m * A) + 200 * (6 * Kr + Ksw) := by ring
      have h3 : 200 * (6 * Kr + Ksw) ≤ BIG := by rw [hBIG, hS]; nlinarith
      exact le_trans (le_trans h2 (le_of_eq e2)) (mul_add_bound _ _ BIG (m * A) h3 h3)
    have step4 := blkFixParams (main := main) (hroll main) (hswap main) (ofList zs)
      (Val.int (sh : ℤ)) (Val.int sgn) (Val.int (r : ℤ)) (Val.int (p : ℤ)) (Val.int (m : ℤ))
      rest S4 (Kr * 6 * (S4 + 1) + Ksw * (S4 + 1)) (le_refl S4) (le_refl _)
    have step5 := hsuf' main m Lb zs (Val.int (sh : ℤ) :: Val.int sgn :: Val.int (r : ℤ) ::
      Val.int (p : ℤ) :: rest) h2 (by rw [hzslen]) hzsz hzcons
    have hD5le : Ksuf * (m * (Lb + 1) + 1) + Ksuf ≤ BIG * (m * A) + BIG := by
      have h5 : m * (Lb + 1) + 1 ≤ 60 * (m * A) := by
        have h6 : Lb + 1 ≤ 30 * A := hLb30
        have h7 : m * (Lb + 1) ≤ m * (30 * A) := Nat.mul_le_mul_left m h6
        nlinarith [h7, hmA, Nat.zero_le m]
      have h7' : Ksuf * (m * (Lb + 1) + 1) ≤ Ksuf * (60 * (m * A)) := Nat.mul_le_mul_left _ h5
      have e1 : Ksuf * (60 * (m * A)) = 60 * Ksuf * (m * A) := by ring
      have h8 : 60 * Ksuf ≤ BIG := by rw [hBIG, hS]; nlinarith
      calc Ksuf * (m * (Lb + 1) + 1) + Ksuf ≤ Ksuf * (60 * (m * A)) + Ksuf :=
            Nat.add_le_add h7' (le_refl _)
        _ = 60 * Ksuf * (m * A) + Ksuf := by rw [e1]
        _ ≤ BIG * (m * A) + BIG := mul_add_bound _ _ BIG (m * A) h8 hksufB
    have hcomb : Kr * 6 * (S4 + 1) + Ksw * (S4 + 1) + (Ksuf * (m * (Lb + 1) + 1) + Ksuf)
        ≤ (BIG * (m * A) + BIG) + (BIG * (m * A) + BIG) :=
      Nat.add_le_add hD4le hD5le
    have c45 := composeEx step4 step5 (fun vs mid _ h2' => h2')
    obtain ⟨out, s', n, hpost, hev, hn, hstk, hoth⟩ := c45 vs hvs' s R0 hR0
    refine ⟨out, s', n, ⟨zs, hvs', hzslen, hzpack, ?_⟩, hev, ?_, hstk, hoth⟩
    · obtain ⟨m1, hm1, Y, hY, hYeq⟩ := hpost
      exact ⟨Y, hY, hYeq⟩
    · exact le_trans hn hcomb
  have c12345 := composeEx c123 step45
    (fun vs mid _ h2' => by
      obtain ⟨m1, hA1', hB1'⟩ := h2'
      obtain ⟨zs, hout, hzslen, hzpack⟩ := hB1'
      exact ⟨zs, hout, hzslen, hzpack⟩)
  -- ===== the final postcondition =====
  refine MrgKit.WordR_weaken c12345 (fun _ h => h) ?_ ?_
  · intro vs out _ hout
    obtain ⟨m1, hA1', hB1'⟩ := hout
    obtain ⟨zs, hout', hzslen, hzpack, hYpart⟩ := hB1'
    obtain ⟨Y, hY, hYeq⟩ := hYpart
    set loV : ℕ → List (ℤ × ℤ) :=
      fun i => if h : i < m - m / 2 then Classical.choose (hzpack i h) else [] with hloV
    set hiV : ℕ → List (ℤ × ℤ) :=
      fun i => if h : i < m - m / 2 then
        Classical.choose (Classical.choose_spec (hzpack i h)) else [] with hhiV
    have hpack : ∀ i (h : i < m - m / 2),
        zs.getD i .nil = Val.cons (cvecVal (loV i)) (cvecVal (hiV i)) ∧
        PackProps p r m sh sgn u e i (loV i) (hiV i) := by
      intro i h
      have h1 : loV i = Classical.choose (hzpack i h) := dif_pos h
      have h2 : hiV i = Classical.choose (Classical.choose_spec (hzpack i h)) := dif_pos h
      rw [h1, h2]
      exact Classical.choose_spec (Classical.choose_spec (hzpack i h))
    set lowsV : List (List (ℤ × ℤ)) := (List.range (m - m / 2)).map loV with hlowsV
    set highsV : List (List (ℤ × ℤ)) := (List.range (m - m / 2)).map hiV with hhighsV
    set ws' : List (List (ℤ × ℤ)) := lowsV.take (m / 2) ++ highsV with hws'
    have hZeq : zs = (List.range (m - m / 2)).map
        (fun i => Val.cons (cvecVal (loV i)) (cvecVal (hiV i))) := by
      apply List.ext_getElem
      · rw [hzslen]; simp
      · intro i h1 h2
        have h1' : i < m - m / 2 := by rw [hzslen] at h1; exact h1
        have hg : zs.getD i .nil = zs[i] := List.getD_eq_getElem zs .nil h1
        simp only [List.getElem_map, List.getElem_range]
        rw [← hg]
        exact (hpack i h1').1
    have hmapfst : zs.map vfst = lowsV.map cvecVal := by
      rw [hZeq, hlowsV]
      simp only [List.map_map]
      congr 1
    have hmapsnd : zs.map vsnd = highsV.map cvecVal := by
      rw [hZeq, hhighsV]
      simp only [List.map_map]
      congr 1
    have hY' : Y = cvecs ws' := by
      rw [hYeq, hmapfst, hmapsnd, hws']
      simp only [cvecs]
      rw [← List.map_take, ← List.map_append]
    refine ⟨ws', ?_, ?_, ?_, ?_⟩
    · rw [hY, hY']
    · have h1 : lowsV.length = m - m / 2 := by rw [hlowsV]; simp
      have h2' : highsV.length = m - m / 2 := by rw [hhighsV]; simp
      have hdiv : m / 2 ≤ m := Nat.div_le_self m 2
      have h3 : (lowsV.take (m / 2)).length = m / 2 := by
        rw [List.length_take, h1]
        omega
      rw [hws', List.length_append, h3, h2']
      omega
    · intro w hw
      rw [hws', List.mem_append] at hw
      rcases hw with hw | hw
      · have hw' : w ∈ lowsV := List.mem_of_mem_take hw
        rw [hlowsV] at hw'
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw'
        have hiP : i < m - m / 2 := by simpa using hi
        exact (hpack i hiP).2.1
      · rw [hhighsV] at hw
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
        exact (hpack i (by simpa using hi)).2.2.1
    · refine hread p r m sh sgn u e lowsV highsV h2 hmul hp2 ?_ ?_ ?_ ?_
      · rw [hlowsV]; simp
      · rw [hhighsV]; simp
      · intro i hi c
        have h1 := (hpack i hi).2
        have h2' : lowsV.getD i [] = loV i := by
          rw [hlowsV]
          exact getD_map_range loV ([] : List (ℤ × ℤ)) hi
        rw [h2']
        exact h1.2.2.1 c
      · intro i hi c
        have h1 := (hpack i hi).2
        have h2' : highsV.getD i [] = hiV i := by
          rw [hhighsV]
          exact getD_map_range hiV ([] : List (ℤ × ℤ)) hi
        rw [h2']
        exact h1.2.2.2 c
  · intro vs _
    have hAm : (10 * BIG + 1) * m * (r + 1) * (p + 1) + (10 * BIG + 1)
        = (10 * BIG + 1) * (m * A) + (10 * BIG + 1) := by rw [hA]; ring
    rw [hAm]
    have h4b : 5 * (BIG * (m * A) + BIG) ≤ (10 * BIG + 1) * (m * A) + (10 * BIG + 1) := by
      nlinarith [hmA]
    linarith [hD1le, hD2le, hD3le, h4b]

end Work.SynFFT

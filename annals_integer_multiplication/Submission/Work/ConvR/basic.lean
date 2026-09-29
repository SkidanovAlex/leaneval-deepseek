import Mathlib
import Submission.HvdH.Interfaces

/-!
# ConvR: shared vocabulary for the convolution over `ℝ = ℂ[y]/(y^r+1)`

(paper Lemma 2.5 and Proposition 3.4)

This file is owned by the ConvR area.  It holds definitions and small helper lemmas that the
other ConvR files (`kronecker`, `pointwise`, `scaleArr`, …) import; the heavy statements live
in those sibling files.

Main contents:

* `WordC`: a `WordR` whose cost is a constant (independent of the value stack).  All the
  "big" library words used by the ConvR pipeline have such costs, which makes the composition
  arithmetic closed-form.
* size bounds for the encoded values manipulated by the pipeline
  (`vsz (.int z) = isz z`, `vsz (ofList xs)`, `vsz (cvecVal u) ≤ cvecSz p r`,
  `vsz (rarrVal A) ≤ arrSz p M r`, …).
-/

set_option autoImplicit false

namespace Work.ConvR

open HvdH

/-! ## Constant-cost words -/

/-- `WordR` with the cost function specialised to a constant. -/
def WordC (main p : Cmd) (P : List Val → Prop) (Q : List Val → List Val → Prop) (C : ℕ) : Prop :=
  WordR main p P Q (fun _ => C)

theorem WordC.ofWordR {main p : Cmd} {P : List Val → Prop} {Q : List Val → List Val → Prop}
    {C : ℕ} (h : WordR main p P Q (fun _ => C)) : WordC main p P Q C := h

theorem WordC.toWordR {main p : Cmd} {P : List Val → Prop} {Q : List Val → List Val → Prop}
    {C : ℕ} (h : WordC main p P Q C) : WordR main p P Q (fun _ => C) := h

/-- Sequential composition of constant-cost words. -/
theorem WordC.seq (hK : KernelLib) {main p q : Cmd} {P P' : List Val → Prop}
    {Q Q' : List Val → List Val → Prop} {C C' : ℕ}
    (h1 : WordC main p P Q C) (h2 : WordC main q P' Q' C')
    (h : ∀ vs mid, P vs → Q vs mid → P' mid) :
    WordC main (.seq p q) P (fun vs out => ∃ mid, Q vs mid ∧ Q' mid out) (C + C') :=
  hK.seq main p q P Q (fun _ => C) P' Q' (fun _ => C') (fun _ => C') h1 h2
    (fun _ _ _ hq => ⟨h _ _ ‹_› hq, le_rfl⟩)

/-- Consequence rule for constant-cost words. -/
theorem WordC.conseq (hK : KernelLib) {main p : Cmd} {P P' : List Val → Prop}
    {Q Q' : List Val → List Val → Prop} {C C' : ℕ}
    (h1 : WordC main p P Q C) (hP : ∀ vs, P' vs → P vs)
    (hQ : ∀ vs out, P' vs → Q vs out → Q' vs out) (hC : C ≤ C') :
    WordC main p P' Q' C' :=
  hK.conseq main p P P' Q Q' (fun _ => C) (fun _ => C') h1 hP hQ (fun _ _ => hC)

/-! ## Sizes of encoded values -/

theorem encodePosNum_length (q : PosNum) : (Computability.encodePosNum q).length = q.natSize := by
  induction q with
  | one => rfl
  | bit0 q ih => simp [Computability.encodePosNum, PosNum.natSize, ih]
  | bit1 q ih => simp [Computability.encodePosNum, PosNum.natSize, ih]

theorem encodeNum_length (x : Num) : (Computability.encodeNum x).length = x.natSize := by
  cases x with
  | zero => rfl
  | pos q => exact encodePosNum_length q

theorem castNum_ofNat'_nat (n : ℕ) : ((Num.ofNat' n : Num) : ℕ) = n := by simp

theorem encodeNat_length (n : ℕ) : (Computability.encodeNat n).length = n.size := by
  change (Computability.encodeNum (Num.ofNat' n)).length = n.size
  rw [encodeNum_length, Num.natSize_to_nat, castNum_ofNat'_nat]

/-- The encoding size of an integer value is `isz`. -/
theorem vsz_int (z : ℤ) : vsz (.int z) = isz z := by
  simp only [vsz, Val.enc, List.length_cons, List.length_append, List.length_nil,
    List.length_map, encodeNat_length, isz]

theorem vsz_cons (a b : Val) : vsz (.cons a b) = vsz a + vsz b + 1 := by
  simp only [vsz, Val.enc, List.length_cons, List.length_append]

/-- Encoding size of a `cons`-chain. -/
theorem vsz_ofList (xs : List Val) : vsz (ofList xs) = (xs.map vsz).sum + xs.length + 1 := by
  induction xs with
  | nil => simp [ofList, vsz, Val.enc]
  | cons x xs ih =>
    have e : ofList (x :: xs) = .cons x (ofList xs) := rfl
    rw [e, vsz_cons, ih]
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

theorem isz_le_of_natAbs_le {z : ℤ} {p : ℕ} (h : z.natAbs ≤ 2 ^ p) : isz z ≤ p + 3 := by
  have h1 : z.natAbs.size ≤ p + 1 := by
    rw [Nat.size_le]
    exact lt_of_le_of_lt h (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self p))
  simp only [isz]
  omega

theorem natAbs_fst_le_of_inDisc {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) : z.1.natAbs ≤ 2 ^ p := by
  simp only [inDisc] at h
  have h2 : z.1 ^ 2 ≤ (4 : ℤ) ^ p := by nlinarith [sq_nonneg z.2]
  have h3 : ((z.1.natAbs : ℤ)) ^ 2 ≤ (((2 ^ p : ℕ) : ℤ)) ^ 2 := by
    have e : ((z.1.natAbs : ℤ)) ^ 2 = z.1 ^ 2 := by
      rw [← Int.natCast_pow, ← Int.natAbs_pow, Int.natAbs_of_nonneg (sq_nonneg z.1)]
    have e2 : (((2 ^ p : ℕ) : ℤ)) ^ 2 = (4 : ℤ) ^ p := by
      have h1 : (((2 ^ p : ℕ) : ℤ)) = (2 : ℤ) ^ p := Int.natCast_pow 2 p
      rw [h1, ← pow_mul, mul_comm, pow_mul, show (4 : ℤ) = (2 : ℤ) ^ 2 by norm_num]
    rw [e, e2]
    exact h2
  exact (Nat.pow_le_pow_iff_left (show (2 : ℕ) ≠ 0 by norm_num)).mp (by exact_mod_cast h3)

theorem natAbs_snd_le_of_inDisc {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) : z.2.natAbs ≤ 2 ^ p := by
  have h' : inDisc p (z.2, z.1) := by
    simp only [inDisc] at h ⊢; linarith
  exact natAbs_fst_le_of_inDisc h'

/-- Uniform bound on the encoding size of a fixed-point complex number in the disc. -/
def cfxSz (p : ℕ) : ℕ := 2 * p + 8

/-- Uniform bound on the encoding size of a coefficient vector of length `r` in the disc. -/
def cvecSz (p r : ℕ) : ℕ := r * cfxSz p + r + 1

/-- Uniform bound on the encoding size of an array of `M` coefficient vectors in the disc. -/
def arrSz (p M r : ℕ) : ℕ := M * cvecSz p r + M + 1

theorem vsz_cfxVal_le {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) : vsz (cfxVal z) ≤ cfxSz p := by
  have h1 : z.1.natAbs ≤ 2 ^ p := natAbs_fst_le_of_inDisc h
  have h2 : z.2.natAbs ≤ 2 ^ p := natAbs_snd_le_of_inDisc h
  have i1 : isz z.1 ≤ p + 3 := isz_le_of_natAbs_le h1
  have i2 : isz z.2 ≤ p + 3 := isz_le_of_natAbs_le h2
  rw [show cfxVal z = Val.cons (.int z.1) (.int z.2) from rfl, vsz_cons, vsz_int, vsz_int, cfxSz]
  omega

theorem sum_map_const {α : Type*} (l : List α) (c : ℕ) :
    (l.map (fun _ => c)).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Nat.succ_mul, Nat.add_comm]

theorem vsz_cvecVal_le {p r : ℕ} {u : List (ℤ × ℤ)} (h : InDiscVec p r u) :
    vsz (cvecVal u) ≤ cvecSz p r := by
  have hlen : u.length = r := h.1
  have hsum : ((u.map cfxVal).map vsz).sum ≤ u.length * cfxSz p := by
    calc ((u.map cfxVal).map vsz).sum
        = (u.map (fun z => vsz (cfxVal z))).sum := by rw [List.map_map, Function.comp_def]
      _ ≤ (u.map (fun _ => cfxSz p)).sum :=
          List.sum_le_sum (fun z hz => vsz_cfxVal_le (h.2 z hz))
      _ = u.length * cfxSz p := sum_map_const u (cfxSz p)
  have e : vsz (cvecVal u) = ((u.map cfxVal).map vsz).sum + u.length + 1 := by
    rw [show cvecVal u = ofList (u.map cfxVal) from rfl, vsz_ofList, List.length_map]
  rw [hlen] at hsum
  rw [e, hlen, cvecSz]
  omega

theorem vsz_rarrVal_le {p M r : ℕ} {A : List (List (ℤ × ℤ))} (h : InDiscArr p M r A) :
    vsz (rarrVal A) ≤ arrSz p M r := by
  have hlen : A.length = M := h.1
  have hsum : ((A.map cvecVal).map vsz).sum ≤ A.length * cvecSz p r := by
    calc ((A.map cvecVal).map vsz).sum
        = (A.map (fun u => vsz (cvecVal u))).sum := by rw [List.map_map, Function.comp_def]
      _ ≤ (A.map (fun _ => cvecSz p r)).sum :=
          List.sum_le_sum (fun u hu => vsz_cvecVal_le (h.2 u hu))
      _ = A.length * cvecSz p r := sum_map_const A (cvecSz p r)
  have e : vsz (rarrVal A) = ((A.map cvecVal).map vsz).sum + A.length + 1 := by
    rw [show rarrVal A = ofList (A.map cvecVal) from rfl, vsz_ofList, List.length_map]
  rw [hlen] at hsum
  rw [e, hlen, arrSz]
  omega

/-- Size of a list of natural numbers encoded as values. -/
theorem vsz_intList_le (ts : List ℕ) :
    vsz (intList ts) ≤ (ts.map fun t => t.size + 3).sum + ts.length + 2 := by
  induction ts with
  | nil => simp [intList, ofList, vsz, Val.enc]
  | cons t ts ih =>
    have e : vsz (intList (t :: ts)) = vsz (.int (t : ℤ)) + vsz (intList ts) + 1 := by
      rw [show intList (t :: ts) = Val.cons (.int (t : ℤ)) (intList ts) from rfl, vsz_cons]
    have i1 : isz (t : ℤ) ≤ t.size + 3 :=
      isz_le_of_natAbs_le (by rw [Int.natAbs_natCast]; exact le_of_lt (Nat.lt_size_self t))
    rw [e, vsz_int]
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega


/-! ## Specification of the Kronecker word (paper Lemma 2.5)

This is the `Prop` proved in `Submission/Work/ConvR/kronecker.lean` and used by
`Submission/Work/ConvR/pointwise.lean`. -/

/-- Paper Lemma 2.5, as a `WordR` statement: given `p`, `r` and two coefficient vectors
`u, v ∈ R̃◦` (`R = ℂ[y]/(y^r+1)`), compute `w̃ ∈ R̃◦` with `2^p‖w̃ - uv/r‖_∞ < 2`, using four
multiplications by `self` of integers of size `≤ 3rp`. -/
def KroneckerSpec : Prop :=
  ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → MulBelow main N Cm →
    ∀ (p r : ℕ), 2 ≤ r → IsPow2 r → r < 2 ^ (p - 1) → 3 * r * p < N →
    WordR main prog
      (fun vs => ∃ (u v : List (ℤ × ℤ)) (rest : List Val),
        vs = .int (p : ℤ) :: .int (r : ℤ) :: cvecVal u :: cvecVal v :: rest ∧
          InDiscVec p r u ∧ InDiscVec p r v)
      (fun vs out => ∃ (u v w : List (ℤ × ℤ)) (rest : List Val),
        vs = .int (p : ℤ) :: .int (r : ℤ) :: cvecVal u :: cvecVal v :: rest ∧
          out = cvecVal w :: rest ∧ InDiscVec p r w ∧
          ∀ j : Fin r, (2 : ℝ) ^ p * ‖fxC p (w.getD j (0, 0)) -
            ((r : ℂ))⁻¹ * negaMul r (fxVec p r u) (fxVec p r v) j‖ < 2)
      (fun _ => 4 * Cm (3 * r * p) + K * (r + 1) * (p + 1) ^ 2)

/-! ## Coercions of the disc condition -/

theorem InDiscVec.getD {p r : ℕ} {u : List (ℤ × ℤ)} (h : InDiscVec p r u) (j : Fin r) :
    inDisc p (u.getD j (0, 0)) := by
  have hj : (j : ℕ) < u.length := by rw [h.1]; exact j.isLt
  rw [List.getD_eq_getElem _ _ hj]
  exact h.2 _ (List.getElem_mem hj)

theorem InDiscArr.getD {p M r : ℕ} {A : List (List (ℤ × ℤ))} (h : InDiscArr p M r A)
    (i : Fin M) (j : Fin r) : inDisc p ((A.getD i []).getD j (0, 0)) := by
  have hi : (i : ℕ) < A.length := by rw [h.1]; exact i.isLt
  rw [List.getD_eq_getElem _ _ hi]
  exact InDiscVec.getD (h.2 _ (List.getElem_mem hi)) j

/-- Each fixed-point number in the disc has modulus `≤ 1`. -/
theorem norm_fxC_le_one {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) : ‖fxC p z‖ ≤ 1 := by
  simp only [inDisc] at h
  have h1 : Complex.normSq ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I) =
      (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 := by
    simp [Complex.normSq_apply]; ring
  have h2 : Complex.normSq ((2 : ℂ) ^ p) = (4 : ℝ) ^ p := by
    rw [map_pow]
    have hh : Complex.normSq (2 : ℂ) = 4 := by norm_num
    rw [hh]
  have hsq : ‖fxC p z‖ ^ 2 = ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) / (4 : ℝ) ^ p := by
    rw [Complex.sq_norm,
      show fxC p z = ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I) * ((2 : ℂ) ^ p)⁻¹ from by
        rw [fxC]; ring,
      map_mul, map_inv₀, h1, h2]
    ring
  have hle : ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) ≤ (4 : ℝ) ^ p := by
    have h2' : ((z.1 ^ 2 + z.2 ^ 2 : ℤ) : ℝ) ≤ ((4 : ℤ) ^ p : ℝ) := by exact_mod_cast h
    push_cast at h2' ⊢
    linarith
  have hs : ‖fxC p z‖ ^ 2 ≤ 1 := by
    rw [hsq, div_le_one (by positivity)]
    exact hle
  nlinarith [norm_nonneg (fxC p z), hs]

end Work.ConvR

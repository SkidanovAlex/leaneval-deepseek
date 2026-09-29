import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.ConvR.basic
import Submission.Work.ConvR.permTop
import Submission.Work.ConvR.norms
import Submission.Work.ConvR.setupPhase
import Submission.Work.ConvR.convIdentity
import Submission.Work.ConvR.pointwise
import Submission.Work.ConvR.scaleArr
import Submission.Work.ConvR.listProdB
import Submission.Work.KronP.kronecker

/-! Guidance from the project lead (the requester):

AREA OWNER: ConvR (paper Lemma 2.5 + Prop 3.4, REFS/nlogn.txt lines 693–730 and 1016–1067).

This file assembles `HvdH.ConvRProp` from the delegated pieces:
* the Kronecker word (paper Lemma 2.5),
* the pointwise loop over the `M` components,
* the array scaling by `M`,
* the list product `M = ∏ tᵢ`,
* the set-up/duplication phase of the pipeline,
* the norm/linearity facts and the convolution identity `convR = M · G*((1/r)(Gu)(Gv))`.

The pipeline (paper proof of Proposition 3.4): from
`[int p, int r, intList ts, rarrVal us, rarrVal ws] ++ rest`
  1. duplicate `(p, r, ts)` (set-up phase),
  2. `G̃u`, `G̃v` via `SynFFTProp` with `sgn = -1`,
  3. pointwise `z = (1/r)·u·v` in `R = ℂ[y]/(y^r+1)`,
  4. `G̃*` via `SynFFTProp` with `sgn = 1`,
  5. `M = ∏ tᵢ` and scaling by `M`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

open HvdH

namespace Work.ConvR

/-! ## size arithmetic for the assembly -/

theorem size_le_self {n : ℕ} (h : 1 ≤ n) : n.size ≤ n := by
  rw [Nat.size_le]
  exact Nat.lt_two_pow_self

theorem isz_nat (n : ℕ) : isz (n : ℤ) = n.size + 2 := by simp [isz]

theorem isz_nat_le {n p : ℕ} (h : n < 2 ^ p) : isz (n : ℤ) ≤ p + 2 := by
  rw [isz_nat]
  have := Nat.size_le.mpr h
  omega

theorem convR_arrSz_le {p M r : ℕ} (hM : 1 ≤ M) (hr : 1 ≤ r) (hp : 1 ≤ p) :
    arrSz p M r + 1 ≤ 26 * (M * r * p) := by
  have hpos : 0 < M * r := Nat.mul_pos (by omega) (by omega)
  have e : arrSz p M r + 1 = M * r * (2 * p + 8) + M * r + M + M + 2 := by
    rw [arrSz, cvecSz, cfxSz]; ring
  rw [e]
  nlinarith [hM, hr, hp, hpos]


/-- Sup-norm bound from coordinatewise bounds. -/
theorem norm_le_of_coord {ι : Type} [Fintype ι] {f : ι → ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, ‖f i‖ ≤ c) : ‖f‖ ≤ c :=
  have h2 : @norm (ι → ℂ) Pi.seminormedAddGroup.toNorm f ≤ c :=
    (pi_norm_le_iff_of_nonneg hc).mpr h
  h2

/-- The array `fxArr p M r A` has sup norm `≤ 1` when all its coordinates are in the disc. -/
theorem norm_fxArr_le {M r p : ℕ} {A : List (List (ℤ × ℤ))}
    (h : ∀ (i : Fin M) (j : Fin r), inDisc p ((A.getD i []).getD j (0, 0))) :
    ‖fxArr p M r A‖ ≤ 1 := by
  have h2 : @norm (Fin M → Fin r → ℂ) Pi.seminormedAddGroup.toNorm (fxArr p M r A) ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun i =>
      (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun j => norm_fxC_le_one (h i j)))
  exact h2

theorem vsz_intList_le' {ts : List ℕ} {p : ℕ} (hlen : ts.length = D - 1)
    (h : ∀ t ∈ ts, t < 2 ^ p) : vsz (intList ts) + 1 ≤ 2000 * (p + 4) := by
  have h1 : vsz (intList ts) ≤ (ts.map fun t => t.size + 3).sum + ts.length + 2 :=
    vsz_intList_le ts
  have h2 : (ts.map fun t => t.size + 3).sum ≤ ts.length * (p + 3) := by
    calc (ts.map fun t => t.size + 3).sum ≤ (ts.map fun _ => p + 3).sum :=
          List.sum_le_sum (fun t ht => by
            have := Nat.size_le.mpr (h t ht)
            omega)
      _ = ts.length * (p + 3) := by simp [sum_map_const]
  have hD : D - 1 = 1728 := by decide
  rw [hD] at hlen
  nlinarith [hlen, h1, h2, Nat.zero_le p]



/-- `WordC.conseq` with a state-dependent cost comparison. -/
theorem WordC.conseq' (hK : KernelLib) {main p : Cmd} {P P' : List Val → Prop}
    {Q Q' : List Val → List Val → Prop} {C : List Val → ℕ} {C' : ℕ}
    (h1 : WordR main p P Q C) (hP : ∀ vs, P' vs → P vs)
    (hQ : ∀ vs out, P' vs → Q vs out → Q' vs out) (hC : ∀ vs, P' vs → C vs ≤ C') :
    WordC main p P' Q' C' :=
  hK.conseq main p P P' Q Q' C (fun _ => C') h1 hP hQ hC

/-! ## injectivity of the array encodings -/

theorem ofList_inj {xs ys : List Val} (h : ofList xs = ofList ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => simp [ofList] at h
  | cons x xs ih =>
    cases ys with
    | nil => simp [ofList] at h
    | cons y ys =>
      rw [show ofList (x :: xs) = Val.cons x (ofList xs) from rfl] at h
      rw [show ofList (y :: ys) = Val.cons y (ofList ys) from rfl] at h
      simp only [Val.cons.injEq] at h
      rw [ih h.2, h.1]

theorem cfxVal_inj {z z' : ℤ × ℤ} (h : cfxVal z = cfxVal z') : z = z' := by
  simp only [cfxVal, Val.cons.injEq, Val.int.injEq] at h
  exact Prod.ext h.1 h.2

theorem map_cfxVal_inj {u v : List (ℤ × ℤ)} (h : u.map cfxVal = v.map cfxVal) : u = v := by
  induction u generalizing v with
  | nil => cases v <;> simp_all
  | cons a u ih =>
    cases v with
    | nil => simp at h
    | cons b v =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [ih h.2, cfxVal_inj h.1]

theorem convR_cvecVal_inj {u v : List (ℤ × ℤ)} (h : cvecVal u = cvecVal v) : u = v :=
  map_cfxVal_inj (ofList_inj h)

theorem map_cvecVal_inj {A B : List (List (ℤ × ℤ))} (h : A.map cvecVal = B.map cvecVal) :
    A = B := by
  induction A generalizing B with
  | nil => cases B <;> simp_all
  | cons a A ih =>
    cases B with
    | nil => simp at h
    | cons b B =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [ih h.2, convR_cvecVal_inj h.1]

theorem rarrVal_inj {A B : List (List (ℤ × ℤ))} (h : rarrVal A = rarrVal B) : A = B :=
  map_cvecVal_inj (ofList_inj h)


/-- The permutations used by the ConvR pipeline. -/
def sg1 : List ℕ := [1, 2, 3, 0, 4]
def sg2 : List ℕ := [2, 3, 4, 0, 5, 1]
def sg3 : List ℕ := [2, 3, 1, 0]
def sg4 : List ℕ := [3, 4, 2, 0, 1, 5]
def sg5 : List ℕ := [1, 0]
def sg6 : List ℕ := [2, 0, 1]

theorem sg1perm : sg1.Perm (List.range 5) := by decide
theorem sg2perm : sg2.Perm (List.range 6) := by decide
theorem sg3perm : sg3.Perm (List.range 4) := by decide
theorem sg4perm : sg4.Perm (List.range 6) := by decide
theorem sg5perm : sg5.Perm (List.range 2) := by decide
theorem sg6perm : sg6.Perm (List.range 3) := by decide

/-! ## The assembly -/

/-- The final error analysis of the ConvR pipeline (paper Prop 3.4): the two forward transforms
(`< log₂T` each), the pointwise product (bilinear amplification), the inverse transform and the
scaling by `M` give the claimed `3T log₂T + 2T + 3` error bound, `T = M r`. -/
theorem convRErr {p r : ℕ} {ts : List ℕ} {usz wsz : List (List (ℤ × ℤ))}
    (Gu Gv Z W0 Zout : List (List (ℤ × ℤ))) (w0 : Fin ts.prod → Fin r → ℂ)
    (hMpos : 0 < ts.prod) (hr2 : 2 ≤ r)
    (hNegN : ∀ (r : ℕ) (a b : Fin r → ℂ), ‖negaMul r a b‖ ≤ r * ‖a‖ * ‖b‖)
    (hNegSubL : ∀ (r : ℕ) (a a' b : Fin r → ℂ),
      negaMul r (a - a') b = negaMul r a b - negaMul r a' b)
    (hNegSubR : ∀ (r : ℕ) (a b b' : Fin r → ℂ),
      negaMul r a (b - b') = negaMul r a b - negaMul r a b')
    (hSynN : ∀ (r : ℕ) (ts : List ℕ) (sgn : ℤ) (u : Fin ts.prod → Fin r → ℂ),
      0 < ts.prod → ‖synDFT r ts sgn u‖ ≤ ‖u‖)
    (hSynSub : ∀ (r : ℕ) (ts : List ℕ) (sgn : ℤ) (u v : Fin ts.prod → Fin r → ℂ),
      synDFT r ts sgn (u - v) = synDFT r ts sgn u - synDFT r ts sgn v)
    (hdu : InDiscArr p ts.prod r usz) (hdw : InDiscArr p ts.prod r wsz)
    (hGu : ApproxR p Gu (synDFT r ts (-1) (fxArr p ts.prod r usz))
      (Nat.log 2 (ts.prod * r) : ℝ))
    (hGv : ApproxR p Gv (synDFT r ts (-1) (fxArr p ts.prod r wsz))
      (Nat.log 2 (ts.prod * r) : ℝ))
    (hZ : ∀ (i : Fin ts.prod) (j : Fin r),
      (2 : ℝ) ^ p * ‖fxC p ((Z.getD i []).getD j (0, 0)) - ((r : ℂ))⁻¹ *
        negaMul r (fxArr p ts.prod r Gu i) (fxArr p ts.prod r Gv i) j‖ < 2)
    (hW0 : ApproxR p W0 (synDFT r ts 1 (fxArr p ts.prod r Z))
      (Nat.log 2 (ts.prod * r) : ℝ))
    (hw0 : w0 = synDFT r ts 1 (fun k c' => ((r : ℂ))⁻¹ *
      negaMul r (synDFT r ts (-1) (fxArr p ts.prod r usz) k)
        (synDFT r ts (-1) (fxArr p ts.prod r wsz) k) c'))
    (hconv : convR r ts (fxArr p ts.prod r usz) (fxArr p ts.prod r wsz) =
      fun j c => (ts.prod : ℂ) * w0 j c)
    (hZout : ∀ (i : Fin ts.prod) (j : Fin r),
      (2 : ℝ) ^ p * ‖fxC p ((Zout.getD i []).getD j (0, 0)) - (ts.prod : ℂ) * w0 i j‖ <
        2 * (ts.prod : ℝ) * ((2 : ℝ) ^ p *
          ‖fxC p ((W0.getD i []).getD j (0, 0)) - w0 i j‖) + 3)
    (i : Fin ts.prod) (j : Fin r) :
    (2 : ℝ) ^ p * ‖fxC p ((Zout.getD i []).getD j (0, 0)) -
        convR r ts (fxArr p ts.prod r usz) (fxArr p ts.prod r wsz) i j‖ <
      ((3 * (ts.prod * r) * Nat.log 2 (ts.prod * r) + 2 * (ts.prod * r) + 3 : ℕ) : ℝ) := by
  have hLnn : (0 : ℝ) ≤ (Nat.log 2 (ts.prod * r) : ℝ) := Nat.cast_nonneg _
  have h2p : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
  have hMnn : (0 : ℝ) < (ts.prod : ℝ) := by exact_mod_cast hMpos
  set L : ℝ := (Nat.log 2 (ts.prod * r) : ℝ) with hLdef
  set A0 : Fin ts.prod → Fin r → ℂ := synDFT r ts (-1) (fxArr p ts.prod r usz) with hA0
  set B0 : Fin ts.prod → Fin r → ℂ := synDFT r ts (-1) (fxArr p ts.prod r wsz) with hB0
  set zz : Fin ts.prod → Fin r → ℂ :=
    fun k c' => ((r : ℂ))⁻¹ * negaMul r (A0 k) (B0 k) c' with hzz
  have hLnn' : (0 : ℝ) ≤ L := hLnn
  have hLdiv : (0 : ℝ) ≤ L / 2 ^ p := div_nonneg hLnn' (le_of_lt h2p)
  have hw0' : w0 = synDFT r ts 1 zz := by rw [hw0, hzz, hA0, hB0]
  have hGu' : ApproxR p Gu A0 L := hGu
  have hGv' : ApproxR p Gv B0 L := hGv
  have hW0' : ApproxR p W0 (synDFT r ts 1 (fxArr p ts.prod r Z)) L := hW0
  have hA0n : ‖A0‖ ≤ 1 := by
    rw [hA0]
    exact le_trans (hSynN r ts (-1) _ hMpos) (norm_fxArr_le (fun i j => InDiscArr.getD hdu i j))
  have hB0n : ‖B0‖ ≤ 1 := by
    rw [hB0]
    exact le_trans (hSynN r ts (-1) _ hMpos) (norm_fxArr_le (fun i j => InDiscArr.getD hdw i j))
  have hGun : ‖fxArr p ts.prod r Gu‖ ≤ 1 :=
    norm_fxArr_le (fun i j => InDiscArr.getD hGu'.1 i j)
  have hGvn : ‖fxArr p ts.prod r Gv‖ ≤ 1 :=
    norm_fxArr_le (fun i j => InDiscArr.getD hGv'.1 i j)
  have hdurow : ∀ i : Fin ts.prod, ‖fxArr p ts.prod r Gu i - A0 i‖ ≤ L / 2 ^ p := by
    intro i
    refine (pi_norm_le_iff_of_nonneg hLdiv).mpr (fun j => ?_)
    rw [Pi.sub_apply]
    refine le_of_lt ((lt_div_iff₀ h2p).mpr (by
      have h := hGu'.2 i j
      rwa [mul_comm] at h))
  have hdvrow : ∀ i : Fin ts.prod, ‖fxArr p ts.prod r Gv i - B0 i‖ ≤ L / 2 ^ p := by
    intro i
    refine (pi_norm_le_iff_of_nonneg hLdiv).mpr (fun j => ?_)
    rw [Pi.sub_apply]
    refine le_of_lt ((lt_div_iff₀ h2p).mpr (by
      have h := hGv'.2 i j
      rwa [mul_comm] at h))
  have hbil : ∀ (i : Fin ts.prod) (j : Fin r),
      (2 : ℝ) ^ p * ‖((r : ℂ))⁻¹ * negaMul r (fxArr p ts.prod r Gu i)
          (fxArr p ts.prod r Gv i) j - zz i j‖ ≤ 2 * L := by
    intro i j
    have hvn : ‖fxArr p ts.prod r Gv i‖ ≤ 1 :=
      le_trans (norm_le_pi_norm (fxArr p ts.prod r Gv) i) hGvn
    have han : ‖A0 i‖ ≤ 1 := le_trans (norm_le_pi_norm A0 i) hA0n
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := by positivity
    have hkey : negaMul r (fxArr p ts.prod r Gu i) (fxArr p ts.prod r Gv i) -
          negaMul r (A0 i) (B0 i) =
        negaMul r (fxArr p ts.prod r Gu i - A0 i) (fxArr p ts.prod r Gv i) +
          negaMul r (A0 i) (fxArr p ts.prod r Gv i - B0 i) := by
      rw [hNegSubL r _ (A0 i) _, hNegSubR r (A0 i) _ (B0 i)]
      abel
    have hnorm : ‖negaMul r (fxArr p ts.prod r Gu i) (fxArr p ts.prod r Gv i) -
        negaMul r (A0 i) (B0 i)‖ ≤ 2 * r * (L / 2 ^ p) := by
      rw [hkey]
      refine le_trans (norm_add_le _ _) ?_
      have h1 : ‖negaMul r (fxArr p ts.prod r Gu i - A0 i) (fxArr p ts.prod r Gv i)‖ ≤
          r * (L / 2 ^ p) := by
        refine le_trans (hNegN r _ _) ?_
        calc (r : ℝ) * ‖fxArr p ts.prod r Gu i - A0 i‖ * ‖fxArr p ts.prod r Gv i‖
            ≤ ((r : ℝ) * (L / 2 ^ p)) * 1 :=
              mul_le_mul (mul_le_mul_of_nonneg_left (hdurow i) hr0) hvn
                (norm_nonneg _) (mul_nonneg hr0 hLdiv)
          _ = (r : ℝ) * (L / 2 ^ p) := by ring
      have h2 : ‖negaMul r (A0 i) (fxArr p ts.prod r Gv i - B0 i)‖ ≤ r * (L / 2 ^ p) := by
        refine le_trans (hNegN r _ _) ?_
        calc (r : ℝ) * ‖A0 i‖ * ‖fxArr p ts.prod r Gv i - B0 i‖
            ≤ ((r : ℝ) * 1) * (L / 2 ^ p) :=
              mul_le_mul (mul_le_mul_of_nonneg_left han hr0) (hdvrow i)
                (norm_nonneg _) (mul_nonneg hr0 zero_le_one)
          _ = (r : ℝ) * (L / 2 ^ p) := by ring
      linarith
    have hdiff : ((r : ℂ))⁻¹ * negaMul r (fxArr p ts.prod r Gu i)
          (fxArr p ts.prod r Gv i) j - zz i j =
        ((r : ℂ))⁻¹ * ((negaMul r (fxArr p ts.prod r Gu i) (fxArr p ts.prod r Gv i) -
          negaMul r (A0 i) (B0 i)) j) := by
      rw [hzz]
      simp only [Pi.sub_apply]
      ring
    rw [hdiff, norm_mul, norm_inv, Complex.norm_natCast]
    calc (2 : ℝ) ^ p * (((r : ℝ))⁻¹ *
          ‖(negaMul r (fxArr p ts.prod r Gu i) (fxArr p ts.prod r Gv i) -
            negaMul r (A0 i) (B0 i)) j‖)
        ≤ (2 : ℝ) ^ p * (((r : ℝ))⁻¹ * (2 * r * (L / 2 ^ p))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
            (le_of_lt h2p)
          exact le_trans (norm_le_pi_norm _ j) hnorm
      _ = 2 * L := by
          have hrne : ((r : ℝ)) ≠ 0 := by positivity
          field_simp
  have hstep2 : ∀ (i : Fin ts.prod) (j : Fin r),
      (2 : ℝ) ^ p * ‖fxC p ((Z.getD i []).getD j (0, 0)) - zz i j‖ < 2 + 2 * L := by
    intro i j
    have h1 := hZ i j
    have h2 := hbil i j
    have e : fxC p ((Z.getD i []).getD j (0, 0)) - zz i j =
        (fxC p ((Z.getD i []).getD j (0, 0)) - ((r : ℂ))⁻¹ * negaMul r
          (fxArr p ts.prod r Gu i) (fxArr p ts.prod r Gv i) j) +
        (((r : ℂ))⁻¹ * negaMul r (fxArr p ts.prod r Gu i) (fxArr p ts.prod r Gv i) j -
          zz i j) := by abel
    calc (2 : ℝ) ^ p * ‖fxC p ((Z.getD i []).getD j (0, 0)) - zz i j‖
        = (2 : ℝ) ^ p * ‖(fxC p ((Z.getD i []).getD j (0, 0)) - ((r : ℂ))⁻¹ * negaMul r
            (fxArr p ts.prod r Gu i) (fxArr p ts.prod r Gv i) j) +
          (((r : ℂ))⁻¹ * negaMul r (fxArr p ts.prod r Gu i) (fxArr p ts.prod r Gv i) j -
            zz i j)‖ := by rw [e]
      _ ≤ (2 : ℝ) ^ p * (‖fxC p ((Z.getD i []).getD j (0, 0)) - ((r : ℂ))⁻¹ * negaMul r
            (fxArr p ts.prod r Gu i) (fxArr p ts.prod r Gv i) j‖ +
          ‖((r : ℂ))⁻¹ * negaMul r (fxArr p ts.prod r Gu i) (fxArr p ts.prod r Gv i) j -
            zz i j‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (le_of_lt h2p)
      _ = (2 : ℝ) ^ p * ‖fxC p ((Z.getD i []).getD j (0, 0)) - ((r : ℂ))⁻¹ * negaMul r
            (fxArr p ts.prod r Gu i) (fxArr p ts.prod r Gv i) j‖ +
          (2 : ℝ) ^ p * ‖((r : ℂ))⁻¹ * negaMul r (fxArr p ts.prod r Gu i)
            (fxArr p ts.prod r Gv i) j - zz i j‖ := by ring
      _ < 2 + 2 * L := by linarith
  have hSbound : (2 : ℝ) ^ p * ‖fxArr p ts.prod r Z - zz‖ ≤ 2 + 2 * L := by
    have hc : (0 : ℝ) ≤ (2 + 2 * L) / 2 ^ p := div_nonneg (by linarith) (le_of_lt h2p)
    have h1 : ‖fxArr p ts.prod r Z - zz‖ ≤ (2 + 2 * L) / 2 ^ p := by
      refine (pi_norm_le_iff_of_nonneg hc).mpr (fun i => ?_)
      refine (pi_norm_le_iff_of_nonneg hc).mpr (fun j => ?_)
      rw [Pi.sub_apply]
      refine le_of_lt ((lt_div_iff₀ h2p).mpr (by
        have h := hstep2 i j
        rwa [mul_comm] at h))
    calc (2 : ℝ) ^ p * ‖fxArr p ts.prod r Z - zz‖ ≤ (2 : ℝ) ^ p * ((2 + 2 * L) / 2 ^ p) :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt h2p)
      _ = 2 + 2 * L := by field_simp
  have hstep3 : ∀ (i : Fin ts.prod) (j : Fin r),
      (2 : ℝ) ^ p * ‖fxC p ((W0.getD i []).getD j (0, 0)) - w0 i j‖ < 3 * L + 2 := by
    intro i j
    have h1 := hW0'.2 i j
    have e : synDFT r ts 1 (fxArr p ts.prod r Z) - w0 =
        synDFT r ts 1 (fxArr p ts.prod r Z - zz) := by
      rw [hw0', ← hSynSub r ts 1 (fxArr p ts.prod r Z) zz]
    have h2 : (2 : ℝ) ^ p * ‖synDFT r ts 1 (fxArr p ts.prod r Z) i j - w0 i j‖ ≤ 2 + 2 * L :=
      calc (2 : ℝ) ^ p * ‖synDFT r ts 1 (fxArr p ts.prod r Z) i j - w0 i j‖
          = (2 : ℝ) ^ p * ‖(synDFT r ts 1 (fxArr p ts.prod r Z) - w0) i j‖ := by
            simp only [Pi.sub_apply]
        _ = (2 : ℝ) ^ p * ‖synDFT r ts 1 (fxArr p ts.prod r Z - zz) i j‖ := by rw [e]
        _ ≤ (2 : ℝ) ^ p * ‖synDFT r ts 1 (fxArr p ts.prod r Z - zz)‖ :=
            mul_le_mul_of_nonneg_left
              (le_trans (norm_le_pi_norm (synDFT r ts 1 (fxArr p ts.prod r Z - zz) i) j)
                (norm_le_pi_norm (synDFT r ts 1 (fxArr p ts.prod r Z - zz)) i))
              (le_of_lt h2p)
        _ ≤ (2 : ℝ) ^ p * ‖fxArr p ts.prod r Z - zz‖ :=
            mul_le_mul_of_nonneg_left (hSynN r ts 1 _ hMpos) (le_of_lt h2p)
        _ ≤ 2 + 2 * L := hSbound
    have e2 : fxC p ((W0.getD i []).getD j (0, 0)) - w0 i j =
        (fxC p ((W0.getD i []).getD j (0, 0)) - synDFT r ts 1 (fxArr p ts.prod r Z) i j) +
        (synDFT r ts 1 (fxArr p ts.prod r Z) i j - w0 i j) := by abel
    calc (2 : ℝ) ^ p * ‖fxC p ((W0.getD i []).getD j (0, 0)) - w0 i j‖
        = (2 : ℝ) ^ p * ‖(fxC p ((W0.getD i []).getD j (0, 0)) -
            synDFT r ts 1 (fxArr p ts.prod r Z) i j) +
          (synDFT r ts 1 (fxArr p ts.prod r Z) i j - w0 i j)‖ := by rw [e2]
      _ ≤ (2 : ℝ) ^ p * (‖fxC p ((W0.getD i []).getD j (0, 0)) -
            synDFT r ts 1 (fxArr p ts.prod r Z) i j‖ +
          ‖synDFT r ts 1 (fxArr p ts.prod r Z) i j - w0 i j‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (le_of_lt h2p)
      _ = (2 : ℝ) ^ p * ‖fxC p ((W0.getD i []).getD j (0, 0)) -
            synDFT r ts 1 (fxArr p ts.prod r Z) i j‖ +
          (2 : ℝ) ^ p * ‖synDFT r ts 1 (fxArr p ts.prod r Z) i j - w0 i j‖ := by ring
      _ < L + (2 + 2 * L) := by linarith
      _ = 3 * L + 2 := by ring
  calc (2 : ℝ) ^ p * ‖fxC p ((Zout.getD i []).getD j (0, 0)) -
        convR r ts (fxArr p ts.prod r usz) (fxArr p ts.prod r wsz) i j‖
      = (2 : ℝ) ^ p * ‖fxC p ((Zout.getD i []).getD j (0, 0)) - (ts.prod : ℂ) * w0 i j‖ := by
        rw [hconv]
    _ < 2 * (ts.prod : ℝ) * ((2 : ℝ) ^ p *
          ‖fxC p ((W0.getD i []).getD j (0, 0)) - w0 i j‖) + 3 := hZout i j
    _ < 2 * (ts.prod : ℝ) * (3 * L + 2) + 3 := by
        have := hstep3 i j
        nlinarith
    _ = 6 * ts.prod * L + 4 * ts.prod + 3 := by ring
    _ ≤ 3 * (ts.prod * r) * L + 2 * (ts.prod * r) + 3 := by
        have hr2' : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
        have hML : (0 : ℝ) ≤ 3 * (ts.prod : ℝ) * L := mul_nonneg (by positivity) hLnn'
        have hM0 : (0 : ℝ) ≤ 2 * (ts.prod : ℝ) := by positivity
        have h1 : 6 * (ts.prod : ℝ) * L ≤ 3 * ((ts.prod : ℝ) * r) * L := by
          rw [show (6 : ℝ) * ts.prod * L = (3 * ts.prod * L) * 2 by ring,
              show 3 * (ts.prod * r) * L = (3 * ts.prod * L) * r by ring]
          exact mul_le_mul_of_nonneg_left hr2' hML
        have h2 : 4 * (ts.prod : ℝ) ≤ 2 * ((ts.prod : ℝ) * r) := by
          rw [show (4 : ℝ) * ts.prod = (2 * ts.prod) * 2 by ring,
              show 2 * ((ts.prod : ℝ) * r) = (2 * ts.prod) * r by ring]
          exact mul_le_mul_of_nonneg_left hr2' hM0
        linarith
    _ = ((3 * (ts.prod * r) * Nat.log 2 (ts.prod * r) + 2 * (ts.prod * r) + 3 : ℕ) : ℝ) := by
        rw [hLdef]
        push_cast
        ring

/-- Numeric core of the ConvR cost bound. -/
theorem convR_cost_arith {Ksum M r p : ℕ} (h1 : 1 ≤ Ksum) (h4 : Ksum ≤ Ksum ^ 4) :
    21 * (10 ^ 12 * Ksum * (M * r * p ^ 2 + 1)) ≤
      100 * (10 ^ 12 * Ksum ^ 4 + 10 ^ 12) * (M * r) * p ^ 2 +
        100 * (10 ^ 12 * Ksum ^ 4 + 10 ^ 12) := by
  nlinarith [h1, h4, Nat.zero_le (M * r * p ^ 2)]

/-- The ConvR pipeline, assembled from the delegated words.  All the specs of the delegated
pieces are hypotheses here; `Work.ConvR.convR` fills them in from the corresponding modules. -/
theorem convR_of_children (hK : KernelLib) (hI : IntLib) (hL : LayoutLib) (hF : FxLib)
    (hSyn : SynFFTProp)
    (hPermTopSpec : ∃ (prog : List ℕ → Cmd) (K : ℕ), ∀ (main : Cmd) (n : ℕ) (σ : List ℕ)
      (head tail : List Val),
      head.length = n → σ.length = n → σ.Perm (List.range n) →
      WordR main (prog σ) (fun vs => vs = head ++ tail)
        (fun _ out => out = σ.map (fun i => head.getD i .nil) ++ tail)
        (fun _ => K * (n + 1) * (n + 1) * (((head.map vsz).sum) + 1)))
    (hKronecker : KroneckerSpec)
    (hPointwise : ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm →
      MulBelow main N Cm → ∀ (p r M : ℕ), 2 ≤ r → IsPow2 r → r < 2 ^ (p - 1) → 3 * r * p < N →
      ∀ (As Bs : List (List (ℤ × ℤ))) (rest : List Val),
        InDiscArr p M r As → InDiscArr p M r Bs →
        WordR main prog
          (fun vs => vs = .int (p : ℤ) :: .int (r : ℤ) :: rarrVal As :: rarrVal Bs :: rest)
          (fun _ out => ∃ Zs : List (List (ℤ × ℤ)), out = rarrVal Zs :: rest ∧
            InDiscArr p M r Zs ∧ ∀ (i : Fin M) (j : Fin r), (2 : ℝ) ^ p *
              ‖fxC p ((Zs.getD i []).getD j (0, 0)) - ((r : ℂ))⁻¹ *
                negaMul r (fxArr p M r As i) (fxArr p M r Bs i) j‖ < 2)
          (fun _ => 4 * M * Cm (3 * r * p) + K * (M * r + 1) * p ^ 2 + K))
    (hScale : ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p c M r : ℕ), 1 ≤ c → c ≤ 2 ^ p →
      ∀ (As : List (List (ℤ × ℤ))) (a : Fin M → Fin r → ℂ) (rest : List Val),
        InDiscArr p M r As → (∀ (i : Fin M) (j : Fin r), (c : ℝ) * ‖a i j‖ ≤ 1) →
        WordR main prog
          (fun vs => vs = .int (p : ℤ) :: .int (c : ℤ) :: rarrVal As :: rest)
          (fun _ out => ∃ Bs, out = rarrVal Bs :: rest ∧ InDiscArr p M r Bs ∧
            ∀ (i : Fin M) (j : Fin r), (2 : ℝ) ^ p *
                ‖fxC p ((Bs.getD i []).getD j (0, 0)) - (c : ℂ) * a i j‖ <
              2 * c * ((2 : ℝ) ^ p * ‖fxC p ((As.getD i []).getD j (0, 0)) - a i j‖) + 3)
          (fun _ => K * (M * r + 1) * (p + 1) ^ 2 + K))
    (hListProd : ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (ts : List ℕ) (rest : List Val),
      WordR main prog (fun vs => vs = intList ts :: rest)
        (fun _ out => out = .int ((ts.prod : ℕ) : ℤ) :: rest)
        (fun vs => K * ((vsz (vs.headD .nil)) + 1) ^ 2))
    (hSetup : ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p r : ℕ) (ts : List ℕ)
      (us ws : List (List (ℤ × ℤ))) (rest : List Val),
      WordR main prog
        (fun vs => vs = [.int (p : ℤ), .int (r : ℤ), intList ts, rarrVal us, rarrVal ws] ++ rest)
        (fun _ out => out = [.int (p : ℤ), .int (r : ℤ), intList ts, rarrVal us,
            .int (p : ℤ), .int (r : ℤ), intList ts, rarrVal ws,
            .int (p : ℤ), .int (r : ℤ), intList ts,
            .int (p : ℤ), .int (r : ℤ), intList ts,
            .int (p : ℤ)] ++ rest)
        (fun vs => K * (vsz (rarrVal ws) + vsz (rarrVal us) + vsz (intList ts) +
          isz (r : ℤ) + p + 2)))
    (hNorms :
      (∀ (r : ℕ) (e : ℤ) (a : Fin r → ℂ), ‖yMul r e a‖ ≤ ‖a‖) ∧
      (∀ (r : ℕ) (e : ℤ) (a b : Fin r → ℂ), yMul r e (a - b) = yMul r e a - yMul r e b) ∧
      (∀ (r : ℕ) (a b : Fin r → ℂ), ‖negaMul r a b‖ ≤ r * ‖a‖ * ‖b‖) ∧
      (∀ (r : ℕ) (a a' b : Fin r → ℂ),
        negaMul r (a - a') b = negaMul r a b - negaMul r a' b) ∧
      (∀ (r : ℕ) (a b b' : Fin r → ℂ),
        negaMul r a (b - b') = negaMul r a b - negaMul r a b') ∧
      (∀ (r : ℕ) (ts : List ℕ) (sgn : ℤ) (u : Fin ts.prod → Fin r → ℂ),
        0 < ts.prod → ‖synDFT r ts sgn u‖ ≤ ‖u‖) ∧
      (∀ (r : ℕ) (ts : List ℕ) (sgn : ℤ) (u v : Fin ts.prod → Fin r → ℂ),
        synDFT r ts sgn (u - v) = synDFT r ts sgn u - synDFT r ts sgn v) ∧
      (∀ (r : ℕ) (ts : List ℕ) (u v : Fin ts.prod → Fin r → ℂ),
        0 < ts.prod → 0 < r → ‖convR r ts u v‖ ≤ ‖u‖ * ‖v‖))
    (hConvId : ∀ (r : ℕ) (ts : List ℕ), IsPow2 r → (∀ t ∈ ts, t ∣ 2 * r) →
      ∀ u v : Fin ts.prod → Fin r → ℂ,
        convR r ts u v = fun j c => (ts.prod : ℂ) *
          synDFT r ts 1 (fun k c' => ((r : ℂ))⁻¹ *
            negaMul r (synDFT r ts (-1) u k) (synDFT r ts (-1) v k) c') j c) :
    ConvRProp := by
  classical
  obtain ⟨permProg, Kpm, hPerm⟩ := hPermTopSpec
  obtain ⟨pushValProg, Kpv, hPush⟩ := hK.pushVal
  obtain ⟨synProg, Ksyn, hSynW⟩ := hSyn
  obtain ⟨pwProg, Kpw, hPw⟩ := hPointwise
  obtain ⟨scProg, Ksc, hSc⟩ := hScale
  obtain ⟨lpProg, Klp, hLp⟩ := hListProd
  obtain ⟨setupProg, Kset, hSetupW⟩ := hSetup
  obtain ⟨hYMle, hYMsub, hNegN, hNegSubL, hNegSubR, hSynN, hSynSub, hConvN⟩ := hNorms
  -- the program
  let Ksum : ℕ := Kpm + Kpv + Ksyn + Kpw + Ksc + Klp + Kset + 1
  let AA : ℕ := 10 ^ 12 * Ksum ^ 4 + 10 ^ 12
  let KF : ℕ := 100 * AA
  let Nv : Val := .int (-1)
  let Ov : Val := .int 1
  let prg : Cmd :=
    .seq setupProg <|
      .seq (.seq (pushValProg Nv) (.seq (permProg sg1) synProg)) <|
        .seq (.seq (pushValProg Nv) (.seq (permProg sg2) synProg)) <|
          .seq (.seq (permProg sg3) pwProg) <|
            .seq (.seq (pushValProg Ov) (.seq (permProg sg4) synProg)) <|
              .seq (.seq (permProg sg5) lpProg) (.seq (permProg sg6) scProg)
  refine ⟨prg, KF, ?_⟩
  intro main N Cm hmon hmb p r ts hp hN
  have hpSyn : SynParams p r ts := hp
  obtain ⟨hlen, hrpow, hts, hTp, hp100⟩ := hp
  -- basic numeric facts
  have hDlen : ts.length = 1728 := by rw [hlen]; decide
  have ht2 : ∀ t ∈ ts, 2 ≤ t := by
    intro t ht
    obtain ⟨k, hk, rfl⟩ := (hts t ht).1
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hr2 : 2 ≤ r := by
    obtain ⟨k, hk, rfl⟩ := hrpow
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hM1 : 1 ≤ ts.prod := by
    apply List.one_le_prod
    intro t ht
    have := ht2 t ht
    omega
  have hM2 : 2 ≤ ts.prod := by
    cases ts with
    | nil => simp at hDlen
    | cons t ts' =>
      have ht := ht2 t (by simp)
      have h1 : 1 ≤ ts'.prod := by
        apply List.one_le_prod
        intro x hx
        have := ht2 x (by simp [hx])
        omega
      have he : (t :: ts').prod = t * ts'.prod := List.prod_cons
      rw [he]
      nlinarith
  have hp1 : 1 ≤ p := by omega
  have h2r : 2 * r < 2 ^ p := by
    calc 2 * r ≤ ts.prod * r := by nlinarith [hM2]
      _ < 2 ^ p := hTp
  have hrlt : r < 2 ^ (p - 1) := by
    have e : 2 ^ p = 2 * 2 ^ (p - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  have hlog : Nat.log 2 (ts.prod * r) ≤ p := by
    have h1 : ts.prod * r ≠ 0 := by
      have := Nat.mul_pos (by omega : 0 < ts.prod) (by omega : 0 < r)
      omega
    have := (Nat.log_lt_iff_lt_pow (by norm_num) h1).mpr hTp
    omega
  let SA : ℕ := 2000 * (p + 4)
  let SA2 : ℕ := 27 * (ts.prod * r * p)
  let L : ℝ := (Nat.log 2 (ts.prod * r) : ℝ)
  have hMr1 : 1 ≤ ts.prod * r := by nlinarith [hM1, hr2]
  have hMrp1 : 1 ≤ ts.prod * r * p := by nlinarith [hMr1, hp1]
  have hSA1 : 1 ≤ SA := by simp only [SA]; omega
  have hSA2 : 1 ≤ SA2 := by simp only [SA2]; nlinarith [hMrp1]
  have hKs1 : 1 ≤ Ksum := by simp only [Ksum]; omega
  have hKs7 : Kpm ≤ Ksum ∧ Kpv ≤ Ksum ∧ Ksyn ≤ Ksum ∧ Kpw ≤ Ksum ∧ Ksc ≤ Ksum ∧
      Klp ≤ Ksum ∧ Kset ≤ Ksum := by
    simp only [Ksum]; omega
  have hKs4 : Ksum ≤ Ksum ^ 4 := by
    calc Ksum = Ksum ^ 1 := (pow_one Ksum).symm
      _ ≤ Ksum ^ 4 := Nat.pow_le_pow_right hKs1 (by norm_num)
  have hAAge : 1 ≤ AA := by simp only [AA]; nlinarith
  have hAAle : ∀ k : ℕ, k ≤ Ksum → k ≤ AA := by
    intro k hk
    have hkk : k ≤ Ksum ^ 4 := le_trans hk hKs4
    simp only [AA]
    nlinarith
  -- size bounds for the small values
  have hPsz : vsz (Val.int (p : ℤ)) + 1 ≤ SA := by
    have h1 : isz (p : ℤ) = p.size + 2 := isz_nat p
    have h2 : p.size ≤ p := size_le_self hp1
    simp only [vsz_int, SA]
    omega
  have hrltp : r < 2 ^ p :=
    lt_of_lt_of_le hrlt (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hQsz : vsz (Val.int (r : ℤ)) + 1 ≤ SA := by
    have h2 : isz (r : ℤ) ≤ p + 2 := isz_nat_le hrltp
    simp only [vsz_int, SA]
    omega
  have hTsz : vsz (intList ts) + 1 ≤ SA := by
    have h2 : ∀ t ∈ ts, t < 2 ^ p := by
      intro t ht
      have h3 : t ∣ 2 * r := (hts t ht).2
      have h4 : 0 < t := by
        obtain ⟨k, hk, rfl⟩ := (hts t ht).1
        positivity
      have h5 : t ≤ 2 * r := Nat.le_of_dvd (by omega : 0 < 2 * r) h3
      omega
    have h1 := vsz_intList_le' hlen h2
    simp only [SA]
    omega
  have hNsz : vsz (Val.int (-1)) + 1 ≤ SA := by
    have : isz (-1 : ℤ) = 3 := by decide
    simp only [vsz_int, this, SA]
    omega
  have hOsz : vsz (Val.int 1) + 1 ≤ SA := by
    have : isz (1 : ℤ) = 3 := by decide
    simp only [vsz_int, this, SA]
    omega
  have hMsz : vsz (Val.int ((ts.prod : ℕ) : ℤ)) + 1 ≤ SA := by
    have h2 : isz (((ts.prod : ℕ) : ℤ)) ≤ p + 2 := by
      apply isz_nat_le
      calc ts.prod ≤ ts.prod * r := Nat.le_mul_of_pos_right _ (by omega)
        _ < 2 ^ p := hTp
    simp only [vsz_int, SA]
    omega
  -- size bound for array values
  have hArrsz : ∀ (A : List (List (ℤ × ℤ))), InDiscArr p (ts.prod) r A →
      vsz (rarrVal A) + 1 ≤ SA2 := by
    intro A hA
    have h1 := vsz_rarrVal_le hA
    have h2 : arrSz p (ts.prod) r + 1 ≤ 26 * (ts.prod * r * p) := convR_arrSz_le hM1 (by omega) hp1
    simp only [SA2]
    omega

  -- ==================== the pipeline ====================
  intro vs hv s R hs
  obtain ⟨us, ws, rest, hvs, hdu, hdw⟩ := hv
  subst hvs
  set Pv : Val := .int (p : ℤ) with hPv
  set Qv : Val := .int (r : ℤ) with hQv
  set Tv : Val := intList ts with hTv
  set Uv : Val := rarrVal us with hUv
  set Wv : Val := rarrVal ws with hWv
  set Nv : Val := .int (-1) with hNv
  set Ov : Val := .int 1 with hOv
  set X1a : List Val := [Pv, Qv, Tv, Wv, Pv, Qv, Tv, Pv, Qv, Tv, Pv] with hX1a
  set X1 : List Val := [Pv, Qv, Tv, Uv, Pv, Qv, Tv, Wv, Pv, Qv, Tv, Pv, Qv, Tv, Pv] with hX1
  set X2a : List Val := [Pv, Qv, Tv, Pv, Qv, Tv, Pv] with hX2a
  set X3a : List Val := [Tv, Pv, Qv, Tv, Pv] with hX3a
  set X4a : List Val := [Pv] with hX4a
  -- size bound for arrays
  have hAsz : ∀ (A : List (List (ℤ × ℤ))), InDiscArr p (ts.prod) r A →
      vsz (rarrVal A) + 1 ≤ SA2 := hArrsz
  -- the mathematical target values
  set a' : Fin (ts.prod) → Fin r → ℂ := synDFT r ts (-1) (fxArr p (ts.prod) r us) with ha'
  set b' : Fin (ts.prod) → Fin r → ℂ := synDFT r ts (-1) (fxArr p (ts.prod) r ws) with hb'
  set zz : Fin (ts.prod) → Fin r → ℂ :=
    fun k c' => ((r : ℂ))⁻¹ * negaMul r (a' k) (b' k) c' with hzz
  set w0 : Fin (ts.prod) → Fin r → ℂ := synDFT r ts 1 zz with hw0
  have hMpos : 0 < ts.prod := by omega
  have hTpos : 0 < ts.prod * r := by positivity
  -- the convolution identity
  have hconv : convR r ts (fxArr p (ts.prod) r us) (fxArr p (ts.prod) r ws) =
      fun j c => (ts.prod : ℂ) * w0 j c := by
    simpa only [hw0, hzz, ha', hb'] using
      hConvId r ts hrpow (fun t ht => (hts t ht).2) (fxArr p (ts.prod) r us)
        (fxArr p (ts.prod) r ws)
  -- norms of the target values
  have hdu' : ‖fxArr p (ts.prod) r us‖ ≤ 1 :=
    norm_fxArr_le (fun i j => InDiscArr.getD hdu i j)
  have hdw' : ‖fxArr p (ts.prod) r ws‖ ≤ 1 :=
    norm_fxArr_le (fun i j => InDiscArr.getD hdw i j)
  have ha'n : ‖a'‖ ≤ 1 := by
    rw [ha']
    exact le_trans (hSynN r ts (-1) _ hMpos) hdu'
  have hb'n : ‖b'‖ ≤ 1 := by
    rw [hb']
    exact le_trans (hSynN r ts (-1) _ hMpos) hdw'
  -- the scale hypothesis on w0
  have hw0bound : ∀ (i : Fin (ts.prod)) (j : Fin r), ((ts.prod : ℝ)) * ‖w0 i j‖ ≤ 1 := by
    intro i j
    have h1 : (ts.prod : ℂ) * w0 i j = convR r ts (fxArr p (ts.prod) r us)
        (fxArr p (ts.prod) r ws) i j := by
      rw [hconv]
    have h2 : ‖(ts.prod : ℂ) * w0 i j‖ = (ts.prod : ℝ) * ‖w0 i j‖ := by
      rw [norm_mul, Complex.norm_natCast]
    have h3 : ‖convR r ts (fxArr p (ts.prod) r us) (fxArr p (ts.prod) r ws) i j‖ ≤ 1 := by
      refine le_trans (norm_le_pi_norm (convR r ts (fxArr p (ts.prod) r us)
        (fxArr p (ts.prod) r ws) i) j) ?_
      refine le_trans (norm_le_pi_norm (convR r ts (fxArr p (ts.prod) r us)
        (fxArr p (ts.prod) r ws)) i) ?_
      refine le_trans (hConvN r ts _ _ (by positivity) (by omega)) ?_
      exact mul_le_one₀ hdu' (norm_nonneg _) hdw'
    rw [← h2, h1]
    exact h3

  -- ==================== cost constants ====================
  set Csyn : ℕ := Ksyn * (ts.prod * r) * p * (Nat.log 2 (ts.prod * r) + 1) + Ksyn with hCsyn
  set Cpw : ℕ := 4 * (ts.prod) * Cm (3 * r * p) + Kpw * (ts.prod * r + 1) * p ^ 2 + Kpw with hCpw
  set Csc : ℕ := Ksc * (ts.prod * r + 1) * (p + 1) ^ 2 + Ksc with hCsc
  set Csh : ℕ := 1000000 * Kpm * (SA + SA2 + 1) with hCsh
  set Cst : ℕ := Kset * (4 * SA2 + 4 * SA) with hCst
  set Clp : ℕ := Klp * SA ^ 2 with hClp
  -- size bounds for the abbreviations
  have hPsz' : vsz Pv + 1 ≤ SA := by rw [hPv]; exact hPsz
  have hQsz' : vsz Qv + 1 ≤ SA := by rw [hQv]; exact hQsz
  have hTsz' : vsz Tv + 1 ≤ SA := by rw [hTv]; exact hTsz
  have hNsz' : vsz Nv + 1 ≤ SA := by rw [hNv]; exact hNsz
  have hOsz' : vsz Ov + 1 ≤ SA := by rw [hOv]; exact hOsz
  have hUsz' : vsz Uv + 1 ≤ SA2 := by rw [hUv]; exact hArrsz us hdu
  have hWsz' : vsz Wv + 1 ≤ SA2 := by rw [hWv]; exact hArrsz ws hdw
  -- ==================== helpers ====================
  have shufStep : ∀ (σ : List ℕ) (X Y tl : List Val) (B : ℕ), σ.Perm (List.range X.length) →
      σ.map (fun i => X.getD i Val.nil) = Y →
      Kpm * (X.length + 1) * (X.length + 1) * ((X.map vsz).sum + 1) ≤ B →
      WordC main (permProg σ) (fun S => S = X ++ tl) (fun _ out => out = Y ++ tl) B := by
    intro σ X Y tl B hper heq hcost
    refine WordC.conseq hK (hPerm main X.length σ X tl rfl (by simpa using hper.length_eq) hper)
      (fun _ h => h) (fun _ _ _ h => by rw [h, heq]) hcost
  have cshBound : ∀ (X : List Val), X.length ≤ 16 → (X.map vsz).sum ≤ 16 * SA + 16 * SA2 →
      Kpm * (X.length + 1) * (X.length + 1) * ((X.map vsz).sum + 1) ≤ Csh := by
    intro X hlen hsum
    have hl17 : X.length + 1 ≤ 17 := by omega
    have h1 : (X.length + 1) * (X.length + 1) ≤ 289 := by
      have := Nat.mul_le_mul hl17 hl17
      simpa using this
    have h2 : (X.map vsz).sum + 1 ≤ 16 * SA + 16 * SA2 + 1 := by omega
    have h3 : Kpm * (X.length + 1) * (X.length + 1) ≤ Kpm * 289 := by
      calc Kpm * (X.length + 1) * (X.length + 1)
          = Kpm * ((X.length + 1) * (X.length + 1)) := by ring
        _ ≤ Kpm * 289 := Nat.mul_le_mul_left Kpm h1
    calc Kpm * (X.length + 1) * (X.length + 1) * ((X.map vsz).sum + 1)
        = (Kpm * (X.length + 1) * (X.length + 1)) * ((X.map vsz).sum + 1) := by ring
      _ ≤ (Kpm * 289) * (16 * SA + 16 * SA2 + 1) := Nat.mul_le_mul h3 h2
      _ ≤ Csh := by
          rw [hCsh]
          have h4 : 289 * (16 * SA + 16 * SA2 + 1) ≤ 1000000 * (SA + SA2 + 1) := by
            have e2 : 4624 * (SA + SA2 + 1) = 4624 * SA + 4624 * SA2 + 4624 := by ring
            have h5 : 289 * (16 * SA + 16 * SA2 + 1) ≤ 4624 * (SA + SA2 + 1) := by
              rw [e2]
              omega
            have h6 : 4624 * (SA + SA2 + 1) ≤ 1000000 * (SA + SA2 + 1) :=
              Nat.mul_le_mul_right _ (by norm_num)
            exact le_trans h5 h6
          calc (Kpm * 289) * (16 * SA + 16 * SA2 + 1)
              = Kpm * (289 * (16 * SA + 16 * SA2 + 1)) := by ring
            _ ≤ Kpm * (1000000 * (SA + SA2 + 1)) := Nat.mul_le_mul_left Kpm h4
            _ = 1000000 * Kpm * (SA + SA2 + 1) := by ring
  have mem16 : ∀ (Y : List Val), Y.length ≤ 16 → (∀ v ∈ Y, vsz v ≤ SA ∨ vsz v ≤ SA2) →
      (Y.map vsz).sum ≤ 16 * SA + 16 * SA2 := by
    intro Y hlen hm
    have h1 : (Y.map vsz).sum ≤ Y.length * (SA + SA2) := by
      calc (Y.map vsz).sum ≤ (Y.map fun _ => SA + SA2).sum :=
            List.sum_le_sum (fun v hv => by rcases hm v hv with h | h <;> omega)
        _ = Y.length * (SA + SA2) := sum_map_const Y _
    calc (Y.map vsz).sum ≤ Y.length * (SA + SA2) := h1
      _ ≤ 16 * (SA + SA2) := Nat.mul_le_mul_right _ hlen
      _ = 16 * SA + 16 * SA2 := by ring
  have pushStep : ∀ (v : Val) (X tl : List Val), vsz v + 1 ≤ SA →
      WordC main (pushValProg v) (fun S => S = X ++ tl)
        (fun S out => S = X ++ tl ∧ out = v :: X ++ tl) (Kpv * SA) := by
    intro v X tl hv
    have h1 : WordR main (pushValProg v) (fun S => S = X ++ tl) (fun S out => S = X ++ tl ∧ out = v :: X ++ tl) (fun _ => Kpv * SA) := by
      refine WordC.conseq' hK (hPush main v) (fun S _ => trivial)
        (fun S out hS hout => ⟨hS, by rw [hout]; exact congrArg (fun l => v :: l) hS⟩)
        (fun vs _ => Nat.mul_le_mul_left Kpv hv)
    exact Work.ConvR.WordC.ofWordR h1
  have synCall : ∀ (sgn : ℤ) (hsgn : sgn = 1 ∨ sgn = -1) (A : List (List (ℤ × ℤ)))
      (tl : List Val), InDiscArr p (ts.prod) r A →
      WordC main synProg (fun S => S = Pv :: Qv :: Tv :: .int sgn :: rarrVal A :: tl)
        (fun _ out => ∃ Zs, out = rarrVal Zs :: tl ∧
          ApproxR p Zs (synDFT r ts sgn (fxArr p (ts.prod) r A)) L) Csyn := by
    intro sgn hsgn A tl hA
    refine WordC.conseq hK (hSynW main p r ts sgn hpSyn hsgn) (fun S hS => ?_)
      (fun S out hS hout => ?_) ?_
    · exact ⟨A, tl, hS, hA⟩
    · obtain ⟨u0, r0, G, hpre, hout', happ⟩ := hout
      rw [hS] at hpre
      simp only [hPv, hQv, hTv] at hpre
      simp only [List.cons.injEq, true_and] at hpre
      have hr : r0 = tl := hpre.2.symm
      have hu : u0 = A := rarrVal_inj hpre.1.symm
      rw [hu] at happ
      exact ⟨G, by simp only [hout', hr], happ⟩
    · exact le_rfl
  have existsPre : ∀ {α : Type} {P : α → List Val → Prop} {Q : α → List Val → List Val → Prop}
      {C : ℕ} {w : Cmd}, (∀ a, WordC main w (P a) (Q a) C) →
      WordC main w (fun S => ∃ a, P a S) (fun S out => ∃ a, P a S ∧ Q a S out) C := by
    intro α P Q C w h vs hpre s R hs
    obtain ⟨a, ha⟩ := hpre
    obtain ⟨out, s', n, hQ, hev, hn, hstk, hfr⟩ := h a vs ha s R hs
    exact ⟨out, s', n, ⟨a, ha, hQ⟩, hev, hn, hstk, hfr⟩
  -- ==================== stage 0: the set-up ====================
  have st0 : WordC main setupProg (fun S => S = [Pv, Qv, Tv, Uv, Wv] ++ rest)
      (fun _ out => out = X1 ++ rest) Cst := by
    refine WordC.conseq hK (hSetupW main p r ts us ws rest) (fun S hS => ?_)
      (fun S out hS hout => ?_) ?_
    · simpa only [hPv, hQv, hTv, hUv, hWv] using hS
    · rw [hout]
    · rw [hCst]
      have h1 : vsz (rarrVal us) + 1 ≤ SA2 := hArrsz us hdu
      have h2 : vsz (rarrVal ws) + 1 ≤ SA2 := hArrsz ws hdw
      have h3 : vsz (intList ts) + 1 ≤ SA := hTsz
      have h4 : isz (r : ℤ) = vsz (Val.int (r : ℤ)) := (vsz_int _).symm
      have h5 : vsz (Val.int (r : ℤ)) + 1 ≤ SA := hQsz
      have h6 : p ≤ SA := by simp only [SA]; omega
      apply Nat.mul_le_mul_left
      rw [h4]
      omega

  -- ==================== stage 1: G̃u ====================
  have st1 : WordC main (.seq (pushValProg Nv) (.seq (permProg sg1) synProg))
      (fun S => S = X1 ++ rest)
      (fun _ out => ∃ Gu, out = rarrVal Gu :: X1a ++ rest ∧ ApproxR p Gu a' L)
      (Kpv * SA + (Csh + Csyn)) := by
    have hpush : WordC main (pushValProg Nv) (fun S => S = X1 ++ rest)
        (fun S out => S = X1 ++ rest ∧ out = Nv :: X1 ++ rest) (Kpv * SA) :=
      pushStep Nv X1 rest hNsz'
    have hsh : WordC main (permProg sg1) (fun S => S = Nv :: X1 ++ rest)
        (fun S out => S = Nv :: X1 ++ rest ∧
          out = [Pv, Qv, Tv, Nv, Uv] ++ X1a ++ rest) Csh := by
      refine WordC.conseq' hK
        (hPerm main 5 sg1 [Nv, Pv, Qv, Tv, Uv] (X1a ++ rest) rfl (by decide) sg1perm)
        (fun S hS => ?_) (fun S out hS hout => ?_) (fun vs hvs => ?_)
      · simp only [hS, hX1, hX1a, List.cons_append, List.nil_append]
      · exact ⟨hS, by rw [hout]; rfl⟩
      · exact cshBound [Nv, Pv, Qv, Tv, Uv] (by simp)
          (mem16 [Nv, Pv, Qv, Tv, Uv] (by simp) (by
            intro v hv
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
            rcases hv with rfl | rfl | rfl | rfl | rfl
            · exact Or.inl (by have := hNsz'; omega)
            · exact Or.inl (by have := hPsz'; omega)
            · exact Or.inl (by have := hQsz'; omega)
            · exact Or.inl (by have := hTsz'; omega)
            · exact Or.inr (by have := hUsz'; omega)))
    have hsyn : WordC main synProg (fun S => S = [Pv, Qv, Tv, Nv, Uv] ++ X1a ++ rest)
        (fun S out => S = [Pv, Qv, Tv, Nv, Uv] ++ X1a ++ rest ∧
          ∃ Gu, out = rarrVal Gu :: X1a ++ rest ∧ ApproxR p Gu a' L) Csyn := by
      refine WordC.conseq hK (synCall (-1) (Or.inr rfl) us (X1a ++ rest) hdu)
        (fun S hS => ?_) (fun S out hS hout => ?_) le_rfl
      · subst hS; rfl
      · obtain ⟨Zs, hZ', hApp⟩ := hout
        exact ⟨hS, Zs, hZ', hApp⟩
    refine WordC.conseq hK (WordC.seq hK hpush (WordC.seq hK hsh hsyn ?_) ?_)
      (fun _ hS => hS) (fun _ out _ hout => ?_) le_rfl
    · intro vs mid h1 h2; exact h2.2
    · intro vs mid h1 h2; exact h2.2
    · obtain ⟨m1, ⟨h1a, h1b⟩, m2, ⟨h2a, h2b⟩, h2c, Gu, hGu, ⟨hJ1, hJ2⟩⟩ := hout
      exact ⟨Gu, hGu, hJ1, hJ2⟩
  -- ==================== stage 2: G̃w ====================
  have st2 : WordC main (.seq (pushValProg Nv) (.seq (permProg sg2) synProg))
      (fun S => ∃ Gu, S = rarrVal Gu :: X1a ++ rest ∧ ApproxR p Gu a' L)
      (fun _ out => ∃ Gu Gv, out = rarrVal Gv :: rarrVal Gu :: X2a ++ rest ∧
        ApproxR p Gu a' L ∧ ApproxR p Gv b' L)
      (Kpv * SA + (Csh + Csyn)) := by
    intro vs hv s R hs
    obtain ⟨Gu, hS, ⟨hA1, hA2⟩⟩ := hv
    have hinner : ∀ (Gu : List (List (ℤ × ℤ))), InDiscArr p (ts.prod) r Gu →
        WordC main (.seq (pushValProg Nv) (.seq (permProg sg2) synProg))
        (fun S => S = rarrVal Gu :: X1a ++ rest)
        (fun _ out => ∃ Gv, out = rarrVal Gv :: rarrVal Gu :: X2a ++ rest ∧ ApproxR p Gv b' L)
        (Kpv * SA + (Csh + Csyn)) := by
      intro Gu hGuI
      have hpush : WordC main (pushValProg Nv) (fun S => S = rarrVal Gu :: X1a ++ rest)
          (fun S out => S = rarrVal Gu :: X1a ++ rest ∧
            out = Nv :: rarrVal Gu :: X1a ++ rest) (Kpv * SA) :=
        pushStep Nv [rarrVal Gu] (X1a ++ rest) hNsz'
      have hsh : WordC main (permProg sg2)
          (fun S => S = Nv :: rarrVal Gu :: X1a ++ rest)
          (fun S out => S = Nv :: rarrVal Gu :: X1a ++ rest ∧
            out = [Pv, Qv, Tv, Nv, Wv] ++ rarrVal Gu :: X2a ++ rest) Csh := by
        refine WordC.conseq' hK
          (hPerm main 6 sg2 [Nv, rarrVal Gu, Pv, Qv, Tv, Wv] (X2a ++ rest) rfl (by decide)
            sg2perm)
          (fun S hS => ?_) (fun S out hS hout => ?_) (fun vs hvs => ?_)
        · rw [hS]
          simp only [hX1a, hX2a, List.cons_append, List.nil_append]
        · exact ⟨hS, by rw [hout]; rfl⟩
        · exact cshBound [Nv, rarrVal Gu, Pv, Qv, Tv, Wv] (by simp)
            (mem16 [Nv, rarrVal Gu, Pv, Qv, Tv, Wv] (by simp) (by
              intro v hv
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
              rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
              · exact Or.inl (by have := hNsz'; omega)
              · exact Or.inr (by have := hArrsz Gu hGuI; omega)
              · exact Or.inl (by have := hPsz'; omega)
              · exact Or.inl (by have := hQsz'; omega)
              · exact Or.inl (by have := hTsz'; omega)
              · exact Or.inr (by have := hWsz'; omega)))
      have hsyn : WordC main synProg
          (fun S => S = Pv :: Qv :: Tv :: Nv :: Wv :: (rarrVal Gu :: X2a ++ rest))
          (fun S out => S = Pv :: Qv :: Tv :: Nv :: Wv :: (rarrVal Gu :: X2a ++ rest) ∧
            (∃ Gv, out = rarrVal Gv :: rarrVal Gu :: X2a ++ rest ∧ ApproxR p Gv b' L)) Csyn := by
        refine WordC.conseq hK (synCall (-1) (Or.inr rfl) ws (rarrVal Gu :: X2a ++ rest) hdw)
          (fun S hS => ?_) (fun S out hS hout => ?_) le_rfl
        · simp only [hS, hNv, hWv, List.cons_append]
        · exact ⟨hS, hout⟩
      refine WordC.conseq hK (WordC.seq hK hpush (WordC.seq hK hsh hsyn ?_) ?_)
        (fun _ hS => hS) (fun _ out _ hout => ?_) le_rfl
      · intro vs mid h1 h2; exact h2.2
      · intro vs mid h1 h2; exact h2.2
      · obtain ⟨m1, ⟨h1a, ⟨h1b1, h1b2⟩, h1c⟩, m2, ⟨h2a, ⟨h2b1, h2b2⟩, h2c⟩,
          ⟨h3a, Gv, hGv, hJ1, hJ2⟩⟩ := hout
        exact ⟨Gv, hGv, hJ1, hJ2⟩
    obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ := hinner Gu hA1 vs hS s R hs
    obtain ⟨Gv, h1, h2a, h2b⟩ := hpost
    exact ⟨out, s', n, ⟨Gu, Gv, h1, ⟨hA1, hA2⟩, h2a, h2b⟩, hev, hn, hstk, hfr⟩
  -- ==================== stage 3: the pointwise product (1/r) u v ====================
  have st3 : WordC main (.seq (permProg sg3) pwProg)
      (fun S => ∃ Gu Gv, S = rarrVal Gv :: rarrVal Gu :: X2a ++ rest ∧
        ApproxR p Gu a' L ∧ ApproxR p Gv b' L)
      (fun _ out => ∃ Gu Gv Z, out = rarrVal Z :: X3a ++ rest ∧
        ApproxR p Gu a' L ∧ ApproxR p Gv b' L ∧ InDiscArr p (ts.prod) r Z ∧
        ∀ (i : Fin (ts.prod)) (j : Fin r), (2 : ℝ) ^ p *
          ‖fxC p ((Z.getD i []).getD j (0, 0)) - ((r : ℂ))⁻¹ *
            negaMul r (fxArr p (ts.prod) r Gu i) (fxArr p (ts.prod) r Gv i) j‖ < 2)
      (Csh + Cpw) := by
    intro vs hv s R hs
    obtain ⟨Gu, Gv, hS, ⟨hA1, hA2⟩, ⟨hB1, hB2⟩⟩ := hv
    have hsh : WordC main (permProg sg3)
        (fun S => S = [rarrVal Gv, rarrVal Gu, Pv, Qv] ++ X3a ++ rest)
        (fun _ out => out = [Pv, Qv, rarrVal Gu, rarrVal Gv] ++ X3a ++ rest) Csh :=
      shufStep sg3 [rarrVal Gv, rarrVal Gu, Pv, Qv] [Pv, Qv, rarrVal Gu, rarrVal Gv]
        (X3a ++ rest) Csh sg3perm rfl
        (cshBound [rarrVal Gv, rarrVal Gu, Pv, Qv] (by simp)
          (mem16 [rarrVal Gv, rarrVal Gu, Pv, Qv] (by simp) (by
            intro v hv'
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv'
            rcases hv' with rfl | rfl | rfl | rfl
            · exact Or.inr (by have := hArrsz Gv hB1; omega)
            · exact Or.inr (by have := hArrsz Gu hA1; omega)
            · exact Or.inl (by have := hPsz'; omega)
            · exact Or.inl (by have := hQsz'; omega))))
    have hpw : WordC main pwProg
        (fun S => S = Pv :: Qv :: rarrVal Gu :: rarrVal Gv :: (X3a ++ rest))
        (fun _ out => ∃ Z, out = rarrVal Z :: (X3a ++ rest) ∧ InDiscArr p (ts.prod) r Z ∧
          ∀ (i : Fin (ts.prod)) (j : Fin r), (2 : ℝ) ^ p *
            ‖fxC p ((Z.getD i []).getD j (0, 0)) - ((r : ℂ))⁻¹ *
              negaMul r (fxArr p (ts.prod) r Gu i) (fxArr p (ts.prod) r Gv i) j‖ < 2) Cpw := by
      refine WordC.conseq hK
        (hPw main N Cm hmon hmb p r (ts.prod) hr2 hrpow hrlt hN Gu Gv (X3a ++ rest) hA1 hB1)
        (fun S hS => ?_) (fun _ _ _ hout => hout) le_rfl
      rw [hS]
    have hinner : WordC main (.seq (permProg sg3) pwProg)
        (fun S => S = rarrVal Gv :: rarrVal Gu :: X2a ++ rest)
        (fun _ out => ∃ Z, out = rarrVal Z :: X3a ++ rest ∧ InDiscArr p (ts.prod) r Z ∧
          ∀ (i : Fin (ts.prod)) (j : Fin r), (2 : ℝ) ^ p *
            ‖fxC p ((Z.getD i []).getD j (0, 0)) - ((r : ℂ))⁻¹ *
              negaMul r (fxArr p (ts.prod) r Gu i) (fxArr p (ts.prod) r Gv i) j‖ < 2)
        (Csh + Cpw) := by
      refine WordC.conseq hK (WordC.seq hK hsh hpw ?_) (fun S hS => ?_)
        (fun _ out _ hout => ?_) le_rfl
      · intro vs mid h1 h2
        exact h2
      · simp only [hS, hX2a, hX3a, List.cons_append, List.nil_append]
      · obtain ⟨mid, hmid, Z, hZout, hZdisc, hZp⟩ := hout
        exact ⟨Z, hZout, hZdisc, hZp⟩
    obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ := hinner vs hS s R hs
    obtain ⟨Z, h1, h2, h3⟩ := hpost
    exact ⟨out, s', n, ⟨Gu, Gv, Z, h1, ⟨hA1, hA2⟩, ⟨hB1, hB2⟩, h2, h3⟩, hev, hn, hstk, hfr⟩
  -- ==================== stage 4: G̃* ====================
  have st4 : WordC main (.seq (pushValProg Ov) (.seq (permProg sg4) synProg))
      (fun S => ∃ Gu Gv Z, S = rarrVal Z :: X3a ++ rest ∧ ApproxR p Gu a' L ∧
        ApproxR p Gv b' L ∧ InDiscArr p (ts.prod) r Z ∧
        ∀ (i : Fin (ts.prod)) (j : Fin r), (2 : ℝ) ^ p *
          ‖fxC p ((Z.getD i []).getD j (0, 0)) - ((r : ℂ))⁻¹ *
            negaMul r (fxArr p (ts.prod) r Gu i) (fxArr p (ts.prod) r Gv i) j‖ < 2)
      (fun _ out => ∃ Gu Gv Z W0, out = rarrVal W0 :: Tv :: X4a ++ rest ∧
        ApproxR p Gu a' L ∧ ApproxR p Gv b' L ∧ InDiscArr p (ts.prod) r Z ∧
        (∀ (i : Fin (ts.prod)) (j : Fin r), (2 : ℝ) ^ p *
          ‖fxC p ((Z.getD i []).getD j (0, 0)) - ((r : ℂ))⁻¹ *
            negaMul r (fxArr p (ts.prod) r Gu i) (fxArr p (ts.prod) r Gv i) j‖ < 2) ∧
        ApproxR p W0 (synDFT r ts 1 (fxArr p (ts.prod) r Z)) L)
      (Kpv * SA + (Csh + Csyn)) := by
    intro vs hv s R hs
    obtain ⟨Gu, Gv, Z, hS, ⟨hA1, hA2⟩, ⟨hB1, hB2⟩, hZ, hpwf⟩ := hv
    have hpush : WordC main (pushValProg Ov) (fun S => S = rarrVal Z :: X3a ++ rest)
        (fun S out => S = rarrVal Z :: X3a ++ rest ∧
          out = Ov :: rarrVal Z :: X3a ++ rest) (Kpv * SA) :=
      pushStep Ov [rarrVal Z] (X3a ++ rest) hOsz'
    have hsh : WordC main (permProg sg4) (fun S => S = Ov :: rarrVal Z :: X3a ++ rest)
        (fun S out => S = Ov :: rarrVal Z :: X3a ++ rest ∧
          out = [Pv, Qv, Tv, Ov, rarrVal Z, Tv] ++ X4a ++ rest) Csh := by
      refine WordC.conseq' hK
        (hPerm main 6 sg4 [Ov, rarrVal Z, Tv, Pv, Qv, Tv] (X4a ++ rest) rfl (by decide)
          sg4perm)
        (fun S hS => ?_) (fun S out hS hout => ?_) (fun vs hvs => ?_)
      · rw [hS]
        simp only [hX3a, hX4a, List.cons_append, List.nil_append]
      · exact ⟨hS, by rw [hout]; rfl⟩
      · exact cshBound [Ov, rarrVal Z, Tv, Pv, Qv, Tv] (by simp)
          (mem16 [Ov, rarrVal Z, Tv, Pv, Qv, Tv] (by simp) (by
            intro v hv
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
            rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
            · exact Or.inl (by have := hOsz'; omega)
            · exact Or.inr (by have := hArrsz Z hZ; omega)
            · exact Or.inl (by have := hTsz'; omega)
            · exact Or.inl (by have := hPsz'; omega)
            · exact Or.inl (by have := hQsz'; omega)
            · exact Or.inl (by have := hTsz'; omega)))
    have hsyn : WordC main synProg
        (fun S => S = Pv :: Qv :: Tv :: Ov :: rarrVal Z :: (Tv :: X4a ++ rest))
        (fun S out => S = Pv :: Qv :: Tv :: Ov :: rarrVal Z :: (Tv :: X4a ++ rest) ∧
          ∃ W0, out = rarrVal W0 :: (Tv :: X4a ++ rest) ∧
            ApproxR p W0 (synDFT r ts 1 (fxArr p (ts.prod) r Z)) L) Csyn := by
      refine WordC.conseq hK (synCall 1 (Or.inl rfl) Z (Tv :: X4a ++ rest) hZ)
        (fun S hS => ?_) (fun S out hS hout => ?_) le_rfl
      · rw [hS]
      · exact ⟨hS, hout⟩
    have hinner : WordC main (.seq (pushValProg Ov) (.seq (permProg sg4) synProg))
        (fun S => S = rarrVal Z :: X3a ++ rest)
        (fun _ out => ∃ W0, out = rarrVal W0 :: Tv :: X4a ++ rest ∧
          ApproxR p W0 (synDFT r ts 1 (fxArr p (ts.prod) r Z)) L)
        (Kpv * SA + (Csh + Csyn)) := by
      refine WordC.conseq hK (WordC.seq hK hpush (WordC.seq hK hsh hsyn ?_) ?_)
        (fun _ hS => hS) (fun _ out _ hout => ?_) le_rfl
      · intro vs mid h1 h2; exact h2.2
      · intro vs mid h1 h2; exact h2.2
      · obtain ⟨m1, ⟨h1a, h1b⟩, m2, ⟨h2a, h2b⟩, ⟨h3a, W0, hW0, hJ1, hJ2⟩⟩ := hout
        exact ⟨W0, hW0, hJ1, hJ2⟩
    obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ := hinner vs hS s R hs
    obtain ⟨W0, h1, h2a, h2b⟩ := hpost
    exact ⟨out, s', n,
      ⟨Gu, Gv, Z, W0, h1, ⟨hA1, hA2⟩, ⟨hB1, hB2⟩, hZ, hpwf, h2a, h2b⟩, hev, hn, hstk, hfr⟩
  -- ==================== stage 5: M = ∏ tᵢ ====================
  have st5 : WordC main (.seq (permProg sg5) lpProg)
      (fun S => ∃ Gu Gv Z W0, S = rarrVal W0 :: Tv :: X4a ++ rest ∧ ApproxR p Gu a' L ∧
        ApproxR p Gv b' L ∧ InDiscArr p (ts.prod) r Z ∧
        (∀ (i : Fin (ts.prod)) (j : Fin r), (2 : ℝ) ^ p *
          ‖fxC p ((Z.getD i []).getD j (0, 0)) - ((r : ℂ))⁻¹ *
            negaMul r (fxArr p (ts.prod) r Gu i) (fxArr p (ts.prod) r Gv i) j‖ < 2) ∧
        ApproxR p W0 (synDFT r ts 1 (fxArr p (ts.prod) r Z)) L)
      (fun _ out => ∃ Gu Gv Z W0, out = .int ((ts.prod : ℕ) : ℤ) :: rarrVal W0 :: X4a ++ rest ∧
        ApproxR p Gu a' L ∧ ApproxR p Gv b' L ∧ InDiscArr p (ts.prod) r Z ∧
        (∀ (i : Fin (ts.prod)) (j : Fin r), (2 : ℝ) ^ p *
          ‖fxC p ((Z.getD i []).getD j (0, 0)) - ((r : ℂ))⁻¹ *
            negaMul r (fxArr p (ts.prod) r Gu i) (fxArr p (ts.prod) r Gv i) j‖ < 2) ∧
        ApproxR p W0 (synDFT r ts 1 (fxArr p (ts.prod) r Z)) L)
      (Csh + Clp) := by
    intro vs hv s R hs
    obtain ⟨Gu, Gv, Z, W0, hS, ⟨hA1, hA2⟩, ⟨hB1, hB2⟩, hZ, hpwf, hW0⟩ := hv
    have hsh : WordC main (permProg sg5) (fun S => S = rarrVal W0 :: Tv :: X4a ++ rest)
        (fun _ out => out = [Tv, rarrVal W0] ++ X4a ++ rest) Csh :=
      shufStep sg5 [rarrVal W0, Tv] [Tv, rarrVal W0] (X4a ++ rest) Csh sg5perm rfl
        (cshBound [rarrVal W0, Tv] (by simp)
          (mem16 [rarrVal W0, Tv] (by simp) (by
            intro v hv'
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv'
            rcases hv' with rfl | rfl
            · exact Or.inr (by have := hArrsz W0 hW0.1; omega)
            · exact Or.inl (by have := hTsz'; omega))))
    have hlp : WordC main lpProg (fun S => S = Tv :: rarrVal W0 :: X4a ++ rest)
        (fun _ out => out = .int ((ts.prod : ℕ) : ℤ) :: rarrVal W0 :: X4a ++ rest) Clp := by
      refine hK.conseq main lpProg
        (fun vs => vs = Tv :: rarrVal W0 :: X4a ++ rest)
        (fun vs => vs = Tv :: rarrVal W0 :: X4a ++ rest)
        (fun _ out => out = .int ((ts.prod : ℕ) : ℤ) :: rarrVal W0 :: X4a ++ rest)
        (fun _ out => out = .int ((ts.prod : ℕ) : ℤ) :: rarrVal W0 :: X4a ++ rest)
        (fun vs => Klp * ((vsz (vs.headD Val.nil)) + 1) ^ 2)
        (fun _ => Clp)
        (hLp main ts (rarrVal W0 :: X4a ++ rest))
        (fun vs h => h) (fun vs out h1 h2 => h2) (fun vs h => ?_)
      rw [hClp, h]
      have hh : (Tv :: rarrVal W0 :: X4a ++ rest).headD Val.nil = Tv := rfl
      rw [hh]
      exact Nat.mul_le_mul_left Klp (Nat.pow_le_pow_left hTsz' 2)
    have hinner : WordC main (.seq (permProg sg5) lpProg)
        (fun S => S = rarrVal W0 :: Tv :: X4a ++ rest)
        (fun _ out => out = .int ((ts.prod : ℕ) : ℤ) :: rarrVal W0 :: X4a ++ rest)
        (Csh + Clp) := by
      refine WordC.conseq hK (WordC.seq hK hsh hlp ?_) (fun S hS => hS)
        (fun _ out _ hout => ?_) le_rfl
      · intro vs mid h1 h2
        exact h2
      · obtain ⟨mid, hmid, hout⟩ := hout
        exact hout
    obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ := hinner vs hS s R hs
    exact ⟨out, s', n, ⟨Gu, Gv, Z, W0, hpost, ⟨hA1, hA2⟩, ⟨hB1, hB2⟩, hZ, hpwf, hW0⟩,
      hev, hn, hstk, hfr⟩
  -- ==================== stage 6: scaling by M ====================
  have st6 : WordC main (.seq (permProg sg6) scProg)
      (fun S => ∃ Gu Gv Z W0, S = .int ((ts.prod : ℕ) : ℤ) :: rarrVal W0 :: X4a ++ rest ∧
        ApproxR p Gu a' L ∧ ApproxR p Gv b' L ∧ InDiscArr p (ts.prod) r Z ∧
        (∀ (i : Fin (ts.prod)) (j : Fin r), (2 : ℝ) ^ p *
          ‖fxC p ((Z.getD i []).getD j (0, 0)) - ((r : ℂ))⁻¹ *
            negaMul r (fxArr p (ts.prod) r Gu i) (fxArr p (ts.prod) r Gv i) j‖ < 2) ∧
        ApproxR p W0 (synDFT r ts 1 (fxArr p (ts.prod) r Z)) L)
      (fun _ out => ∃ Gu Gv Z W0 Zout, out = rarrVal Zout :: rest ∧ ApproxR p Gu a' L ∧
        ApproxR p Gv b' L ∧ InDiscArr p (ts.prod) r Z ∧
        (∀ (i : Fin (ts.prod)) (j : Fin r), (2 : ℝ) ^ p *
          ‖fxC p ((Z.getD i []).getD j (0, 0)) - ((r : ℂ))⁻¹ *
            negaMul r (fxArr p (ts.prod) r Gu i) (fxArr p (ts.prod) r Gv i) j‖ < 2) ∧
        ApproxR p W0 (synDFT r ts 1 (fxArr p (ts.prod) r Z)) L ∧
        InDiscArr p (ts.prod) r Zout ∧
        ∀ (i : Fin (ts.prod)) (j : Fin r), (2 : ℝ) ^ p *
          ‖fxC p ((Zout.getD i []).getD j (0, 0)) - ((ts.prod : ℂ)) * w0 i j‖ <
          2 * (ts.prod : ℝ) * ((2 : ℝ) ^ p *
            ‖fxC p ((W0.getD i []).getD j (0, 0)) - w0 i j‖) + 3)
      (Csh + Csc) := by
    intro vs hv s R hs
    obtain ⟨Gu, Gv, Z, W0, hS, ⟨hA1, hA2⟩, ⟨hB1, hB2⟩, hZ, hpwf, hW0⟩ := hv
    have hsh : WordC main (permProg sg6)
        (fun S => S = .int ((ts.prod : ℕ) : ℤ) :: rarrVal W0 :: X4a ++ rest)
        (fun _ out => out = [Pv, .int ((ts.prod : ℕ) : ℤ), rarrVal W0] ++ rest) Csh :=
      shufStep sg6 [.int ((ts.prod : ℕ) : ℤ), rarrVal W0, Pv]
        [Pv, .int ((ts.prod : ℕ) : ℤ), rarrVal W0] rest Csh sg6perm rfl
        (cshBound [.int ((ts.prod : ℕ) : ℤ), rarrVal W0, Pv] (by simp)
          (mem16 [.int ((ts.prod : ℕ) : ℤ), rarrVal W0, Pv] (by simp) (by
            intro v hv'
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv'
            rcases hv' with rfl | rfl | rfl
            · exact Or.inl (by have := hMsz; omega)
            · exact Or.inr (by have := hArrsz W0 hW0.1; omega)
            · exact Or.inl (by have := hPsz'; omega))))
    have hsc : WordC main scProg
        (fun S => S = Pv :: .int ((ts.prod : ℕ) : ℤ) :: rarrVal W0 :: rest)
        (fun _ out => ∃ Zout, out = rarrVal Zout :: rest ∧ InDiscArr p (ts.prod) r Zout ∧
          ∀ (i : Fin (ts.prod)) (j : Fin r), (2 : ℝ) ^ p *
            ‖fxC p ((Zout.getD i []).getD j (0, 0)) - ((ts.prod : ℂ)) * w0 i j‖ <
            2 * (ts.prod : ℝ) * ((2 : ℝ) ^ p *
              ‖fxC p ((W0.getD i []).getD j (0, 0)) - w0 i j‖) + 3) Csc := by
      refine WordC.conseq hK
        (hSc main p (ts.prod) (ts.prod) r hM1
          (by have h1 : ts.prod ≤ ts.prod * r :=
                Nat.le_mul_of_pos_right (ts.prod) (by omega : 0 < r)
              omega) W0 w0 rest hW0.1 hw0bound)
        (fun S hS => ?_) (fun _ _ _ hout => hout) le_rfl
      rw [hS]
    have hinner : WordC main (.seq (permProg sg6) scProg)
        (fun S => S = .int ((ts.prod : ℕ) : ℤ) :: rarrVal W0 :: X4a ++ rest)
        (fun _ out => ∃ Zout, out = rarrVal Zout :: rest ∧ InDiscArr p (ts.prod) r Zout ∧
          ∀ (i : Fin (ts.prod)) (j : Fin r), (2 : ℝ) ^ p *
            ‖fxC p ((Zout.getD i []).getD j (0, 0)) - ((ts.prod : ℂ)) * w0 i j‖ <
            2 * (ts.prod : ℝ) * ((2 : ℝ) ^ p *
              ‖fxC p ((W0.getD i []).getD j (0, 0)) - w0 i j‖) + 3) (Csh + Csc) := by
      refine WordC.conseq hK (WordC.seq hK hsh hsc ?_) (fun S hS => hS)
        (fun _ out _ hout => ?_) le_rfl
      · intro vs mid h1 h2
        exact h2
      · obtain ⟨mid, hmid, Zout, hout, hdisc, hsc⟩ := hout
        exact ⟨Zout, hout, hdisc, hsc⟩
    obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ := hinner vs hS s R hs
    obtain ⟨Zout, h1, h2, h3⟩ := hpost
    exact ⟨out, s', n,
      ⟨Gu, Gv, Z, W0, Zout, h1, ⟨hA1, hA2⟩, ⟨hB1, hB2⟩, hZ, hpwf, hW0, h2, h3⟩,
      hev, hn, hstk, hfr⟩
  -- ==================== the chain ====================
  have hchain0 :=
    WordC.seq hK st0 (WordC.seq hK st1 (WordC.seq hK st2 (WordC.seq hK st3
      (WordC.seq hK st4 (WordC.seq hK st5 st6 (fun _ _ _ h => h)) (fun _ _ _ h => h))
      (fun _ _ _ h => h)) (fun _ _ _ h => h)) (fun _ _ _ h => h)) (fun _ _ _ h => h)
  have hchain : WordC main prg (fun S => S = [Pv, Qv, Tv, Uv, Wv] ++ rest)
      (fun _ out => ∃ Gu Gv Z W0 Zout, out = rarrVal Zout :: rest ∧ ApproxR p Gu a' L ∧
        ApproxR p Gv b' L ∧ InDiscArr p (ts.prod) r Z ∧
        (∀ (i : Fin (ts.prod)) (j : Fin r), (2 : ℝ) ^ p *
          ‖fxC p ((Z.getD i []).getD j (0, 0)) - ((r : ℂ))⁻¹ *
            negaMul r (fxArr p (ts.prod) r Gu i) (fxArr p (ts.prod) r Gv i) j‖ < 2) ∧
        ApproxR p W0 (synDFT r ts 1 (fxArr p (ts.prod) r Z)) L ∧
        InDiscArr p (ts.prod) r Zout ∧
        ∀ (i : Fin (ts.prod)) (j : Fin r), (2 : ℝ) ^ p *
          ‖fxC p ((Zout.getD i []).getD j (0, 0)) - ((ts.prod : ℂ)) * w0 i j‖ <
          2 * (ts.prod : ℝ) * ((2 : ℝ) ^ p *
            ‖fxC p ((W0.getD i []).getD j (0, 0)) - w0 i j‖) + 3)
      (Cst + ((Kpv * SA + (Csh + Csyn)) + ((Kpv * SA + (Csh + Csyn)) +
        ((Csh + Cpw) + ((Kpv * SA + (Csh + Csyn)) + ((Csh + Clp) + (Csh + Csc))))))) := by
    refine WordC.conseq hK hchain0 (fun _ hS => hS) (fun _ out _ hout => ?_) le_rfl
    obtain ⟨m1, h1, hr1⟩ := hout
    obtain ⟨m2, h2, hr2⟩ := hr1
    obtain ⟨m3, h3, hr3⟩ := hr2
    obtain ⟨m4, h4, hr4⟩ := hr3
    obtain ⟨m5, h5, hr5⟩ := hr4
    obtain ⟨m6, h6, h7⟩ := hr5
    exact h7
  -- ==================== final conversion, error analysis, cost ====================
  have hfinal : WordC main prg (fun S => S = [Pv, Qv, Tv, Uv, Wv] ++ rest)
      (fun vs out => ∃ us' ws' rest' zs,
        vs = .int (p : ℤ) :: .int (r : ℤ) :: intList ts :: rarrVal us' :: rarrVal ws' :: rest' ∧
        out = rarrVal zs :: rest' ∧
        ApproxR p zs (convR r ts (fxArr p (ts.prod) r us') (fxArr p (ts.prod) r ws'))
          (3 * (ts.prod * r) * Nat.log 2 (ts.prod * r) + 2 * (ts.prod * r) + 3 : ℕ))
      (4 * (ts.prod) * Cm (3 * r * p) + KF * (ts.prod * r) * p ^ 2 + KF) := by
    refine WordC.conseq hK hchain (fun _ hS => hS) (fun S out hS hout => ?_) ?_
    · obtain ⟨Gu, Gv, Z, W0, Zout, h1, ⟨hA1, hA2⟩, ⟨hB1, hB2⟩, hZ, hpwf, ⟨hW01, hW02⟩,
        hZdisc, hZsc⟩ := hout
      exact ⟨us, ws, rest, Zout, hS, h1, hZdisc,
        fun i j => convRErr Gu Gv Z W0 Zout w0 hMpos hr2 hNegN hNegSubL hNegSubR hSynN
          hSynSub hdu hdw ⟨hA1, hA2⟩ ⟨hB1, hB2⟩ hpwf ⟨hW01, hW02⟩ hw0 hconv hZsc i j⟩
    · -- cost
      obtain ⟨hKsKpm, hKsKpv, hKsKsyn, hKsKpw, hKsKsc, hKsKlp, hKsKset⟩ := hKs7
      let U : ℕ := ts.prod * r * p ^ 2 + 1
      let V : ℕ := 10 ^ 12 * Ksum * U
      have hUdef : U = ts.prod * r * p ^ 2 + 1 := rfl
      have hVdef : V = 10 ^ 12 * Ksum * U := rfl
      have hU1 : 1 ≤ U := by rw [hUdef]; omega
      have pow_two' : ∀ n : ℕ, n * n = n ^ 2 := fun n => (pow_two n).symm
      have hp2 : p ≤ p ^ 2 := by
        calc p = p * 1 := (Nat.mul_one p).symm
          _ ≤ p * p := Nat.mul_le_mul_left p hp1
          _ = p ^ 2 := (pow_two p).symm
      have hMrp2U : ts.prod * r * p ^ 2 ≤ U := by rw [hUdef]; omega
      have hp2U : p ^ 2 ≤ U := by
        rw [hUdef]
        calc p ^ 2 = 1 * p ^ 2 := (Nat.one_mul _).symm
          _ ≤ (ts.prod * r) * p ^ 2 := Nat.mul_le_mul hMr1 (le_refl (p ^ 2))
          _ ≤ ts.prod * r * p ^ 2 + 1 := Nat.le_succ _
      have hpU : p ≤ U := by
        calc p ≤ p ^ 2 := hp2
          _ ≤ ts.prod * r * p ^ 2 := by
              calc p ^ 2 = 1 * p ^ 2 := (Nat.one_mul _).symm
                _ ≤ (ts.prod * r) * p ^ 2 := Nat.mul_le_mul hMr1 (le_refl (p ^ 2))
          _ ≤ U := hMrp2U
      have hMrpU : ts.prod * r * p ≤ U := by
        rw [hUdef]
        calc ts.prod * r * p ≤ ts.prod * r * p ^ 2 := Nat.mul_le_mul_left _ hp2
          _ ≤ ts.prod * r * p ^ 2 + 1 := Nat.le_succ _
      have hSAU : SA ≤ 10 ^ 4 * U := by
        have h1 : SA = 2000 * (p + 4) := rfl
        rw [h1]
        calc 2000 * (p + 4) ≤ 10 ^ 4 * p := by omega
          _ ≤ 10 ^ 4 * U := Nat.mul_le_mul_left _ hpU
      have hSA2U : SA2 ≤ 27 * U := by
        have h1 : SA2 = 27 * (ts.prod * r * p) := rfl
        rw [h1]
        exact Nat.mul_le_mul_left _ hMrpU
      have hSAp : SA ≤ 10 ^ 4 * p := by
        have h1 : SA = 2000 * (p + 4) := rfl
        rw [h1]; omega
      have hp21 : 1 ≤ p ^ 2 := by
        calc (1 : ℕ) = 1 ^ 2 := rfl
          _ ≤ p ^ 2 := Nat.pow_le_pow_left hp1 2
      have hlog2 : Nat.log 2 (ts.prod * r) + 1 ≤ 2 * p := by omega
      have h1011 : (1 : ℕ) ≤ 10 ^ 11 * U := by
        calc (1 : ℕ) ≤ U := hU1
          _ = 1 * U := (Nat.one_mul U).symm
          _ ≤ 10 ^ 11 * U := Nat.mul_le_mul_right U (by norm_num)
      have absorb : ∀ (K X : ℕ), K ≤ Ksum → X ≤ 10 ^ 11 * U → K * X ≤ V := by
        intro K X hK hX
        calc K * X ≤ Ksum * (10 ^ 11 * U) := Nat.mul_le_mul hK hX
          _ = 10 ^ 11 * Ksum * U := by ring
          _ ≤ 10 ^ 12 * Ksum * U :=
              Nat.mul_le_mul_right U (Nat.mul_le_mul_right Ksum (by norm_num))
          _ = V := hVdef.symm
      have hCstB : Kset * (4 * SA2 + 4 * SA) ≤ V := by
        refine absorb Kset (4 * SA2 + 4 * SA) hKsKset ?_
        have e1 : SA = 2000 * (p + 4) := rfl
        have e2 : SA2 = 27 * (ts.prod * r * p) := rfl
        rw [e1, e2]
        calc 4 * (27 * (ts.prod * r * p)) + 4 * (2000 * (p + 4))
            ≤ 108 * U + 40000 * U := by
              have ha : 4 * (27 * (ts.prod * r * p)) ≤ 108 * U := by
                calc 4 * (27 * (ts.prod * r * p)) = 108 * (ts.prod * r * p) := by ring
                  _ ≤ 108 * U := Nat.mul_le_mul_left _ hMrpU
              have hb : 4 * (2000 * (p + 4)) ≤ 40000 * U := by
                calc 4 * (2000 * (p + 4)) = 8000 * (p + 4) := by ring
                  _ ≤ 8000 * (5 * U) := Nat.mul_le_mul_left _ (by omega)
                  _ = 40000 * U := by ring
              exact Nat.add_le_add ha hb
          _ ≤ 10 ^ 11 * U := by
              calc 108 * U + 40000 * U = (108 + 40000) * U := (Nat.add_mul 108 40000 U).symm
                _ ≤ 10 ^ 11 * U := Nat.mul_le_mul_right U (by norm_num)
      have hKpvB : Kpv * SA ≤ V :=
        absorb Kpv SA hKsKpv (le_trans hSAU (Nat.mul_le_mul_right U (by norm_num)))
      have hCshB : 1000000 * Kpm * (SA + SA2 + 1) ≤ V := by
        rw [show 1000000 * Kpm * (SA + SA2 + 1) = Kpm * (1000000 * (SA + SA2 + 1))
          by ring]
        refine absorb Kpm (1000000 * (SA + SA2 + 1)) hKsKpm ?_
        have h4 : SA + SA2 + 1 ≤ 10028 * U := by
          calc SA + SA2 + 1 ≤ 10 ^ 4 * U + 27 * U + 1 :=
                Nat.add_le_add (Nat.add_le_add hSAU hSA2U) (le_refl 1)
            _ ≤ 10 ^ 4 * U + 27 * U + U := Nat.add_le_add (le_refl _) hU1
            _ = 10028 * U := by ring
        calc 1000000 * (SA + SA2 + 1) ≤ 1000000 * (10028 * U) := Nat.mul_le_mul_left _ h4
          _ = 10028000000 * U := by ring
          _ ≤ 10 ^ 11 * U := Nat.mul_le_mul_right U (by norm_num)
      have hCsyn1B : Ksyn * (ts.prod * r) * p * (Nat.log 2 (ts.prod * r) + 1) ≤ V := by
        rw [show Ksyn * (ts.prod * r) * p * (Nat.log 2 (ts.prod * r) + 1) =
          Ksyn * ((ts.prod * r) * p * (Nat.log 2 (ts.prod * r) + 1)) by ring]
        refine absorb Ksyn ((ts.prod * r) * p * (Nat.log 2 (ts.prod * r) + 1)) hKsKsyn ?_
        calc (ts.prod * r) * p * (Nat.log 2 (ts.prod * r) + 1)
            ≤ (ts.prod * r) * p * (2 * p) := Nat.mul_le_mul_left _ hlog2
          _ = 2 * (ts.prod * r * p ^ 2) := by ring
          _ ≤ 2 * U := Nat.mul_le_mul_left _ hMrp2U
          _ ≤ 10 ^ 11 * U := Nat.mul_le_mul_right U (by norm_num)
      have hCsyn2B : Ksyn ≤ V := by
        have h := absorb Ksyn 1 hKsKsyn h1011
        simpa using h
      have hClpB : Klp * SA ^ 2 ≤ V := by
        refine absorb Klp (SA ^ 2) hKsKlp ?_
        calc SA ^ 2 ≤ (10 ^ 4 * p) ^ 2 := Nat.pow_le_pow_left hSAp 2
          _ = 10 ^ 8 * p ^ 2 := by ring
          _ ≤ 10 ^ 8 * U := Nat.mul_le_mul_left _ hp2U
          _ ≤ 10 ^ 11 * U := Nat.mul_le_mul_right U (by norm_num)
      have hCsc1B : Ksc * (ts.prod * r + 1) * (p + 1) ^ 2 ≤ V := by
        rw [show Ksc * (ts.prod * r + 1) * (p + 1) ^ 2 =
          Ksc * ((ts.prod * r + 1) * (p + 1) ^ 2) by ring]
        refine absorb Ksc ((ts.prod * r + 1) * (p + 1) ^ 2) hKsKsc ?_
        have h2 : ts.prod * r + 1 ≤ 2 * (ts.prod * r) := by omega
        have h3 : (p + 1) ^ 2 ≤ 4 * p ^ 2 := by
          have h4 : p + 1 ≤ 2 * p := by omega
          calc (p + 1) ^ 2 ≤ (2 * p) ^ 2 := Nat.pow_le_pow_left h4 2
            _ = 4 * p ^ 2 := by ring
        calc (ts.prod * r + 1) * (p + 1) ^ 2
            ≤ (2 * (ts.prod * r)) * (4 * p ^ 2) := Nat.mul_le_mul h2 h3
          _ = 8 * (ts.prod * r * p ^ 2) := by ring
          _ ≤ 8 * U := Nat.mul_le_mul_left _ hMrp2U
          _ ≤ 10 ^ 11 * U := Nat.mul_le_mul_right U (by norm_num)
      have hCsc2B : Ksc ≤ V := by
        have h := absorb Ksc 1 hKsKsc h1011
        simpa using h
      have hCpw1B : Kpw * (ts.prod * r + 1) * p ^ 2 ≤ V := by
        rw [show Kpw * (ts.prod * r + 1) * p ^ 2 =
          Kpw * ((ts.prod * r + 1) * p ^ 2) by ring]
        refine absorb Kpw ((ts.prod * r + 1) * p ^ 2) hKsKpw ?_
        have h2 : ts.prod * r + 1 ≤ 2 * (ts.prod * r) := by omega
        calc (ts.prod * r + 1) * p ^ 2 ≤ (2 * (ts.prod * r)) * p ^ 2 :=
              Nat.mul_le_mul_right _ h2
          _ = 2 * (ts.prod * r * p ^ 2) := by ring
          _ ≤ 2 * U := Nat.mul_le_mul_left _ hMrp2U
          _ ≤ 10 ^ 11 * U := Nat.mul_le_mul_right U (by norm_num)
      have hCpw2B : Kpw ≤ V := by
        have h := absorb Kpw 1 hKsKpw h1011
        simpa using h
      have harith : 21 * V ≤ KF * (ts.prod * r) * p ^ 2 + KF := by
        have h1 : V = 10 ^ 12 * Ksum * (ts.prod * r * p ^ 2 + 1) := by rw [hVdef, hUdef]
        have hAA : AA = 10 ^ 12 * Ksum ^ 4 + 10 ^ 12 := rfl
        have hKF : KF = 100 * AA := rfl
        rw [h1, hKF, hAA]
        exact convR_cost_arith hKs1 hKs4
      rw [hCst, hCsh, hCsyn, hCpw, hClp, hCsc]
      linarith only [hCstB, hKpvB, hCshB, hCsyn1B, hCsyn2B, hClpB, hCsc1B, hCsc2B,
        hCpw1B, hCpw2B, harith]
  exact hfinal _ rfl s R hs
/-- Paper Lem. 2.5 and Proposition 3.4: convolution over C[y]/(y^r+1). -/
theorem convR : HvdH.KernelLib → HvdH.IntLib → HvdH.LayoutLib → HvdH.FxLib → HvdH.SynFFTProp →
    HvdH.ConvRProp := by
  intro hK hI hL hF hSyn
  exact convR_of_children hK hI hL hF hSyn (permTop hK) (Work.KronP.kronecker hK hI hL hF)
    (pointwise hK hI hL hF (Work.KronP.kronecker hK hI hL hF)) (scaleArr hK hI hL hF)
    (listProdB hK hI hL) (setupPhase hK) (norms hK)
    (fun r ts hr ht => convIdentity (r := r) (ts := ts) hr ht)

end Work.ConvR

import Mathlib
import Submission.Work.Cert.Spec

/-! # Soundness of the integer theta-sum certificate: definitions and rounding layer

This file fixes the real-analytic vocabulary for `Work.Cert.theta_encl` (`ThetaEncl`).

* `((S : ℝ))` is the certificate scale `S = 2^40·10^8` seen as a real number.
* `tri k = k(k+1)/2` is the `k`-th triangular number; `thetaA q = Σ q^{tri n}`.
* For integer mantissas `x y`, `cx x y` (from `Spec.lean`) is `(x + y·i)/((S : ℝ))`, and `md`, `mu`, `dvu`
  (from `Defs.lean`) are the floored/ceiled products and quotients.

The arithmetic core below records that the integer operations move the real value by at most one ulp:

* `thmd_le`, `thmd_gt` : `md a b / ((S : ℝ)) ∈ (a·b/SR² - 1/((S : ℝ)), a·b/((S : ℝ))]`
* `thmu_ge`, `thmu_lt` : `mu a b / ((S : ℝ)) ∈ [a·b/SR², a·b/SR² + 1/((S : ℝ)))`
* `thdvu_ge`, `thdvu_lt` : `dvu a b / ((S : ℝ)) ∈ [a/b, a/b + 1/((S : ℝ)))` for `b > 0`
* `cx_mul_le` : `cx (cmr a b c d) (cmi a b c d)` is `(cx a b)·(cx c d)` up to `3/((S : ℝ))`
* `md_S`, `md_self_S`, `mu_S` : multiplication by `S` is exact (used for the first loop step)
-/

/-! NOTE (agent H25 / area ANum, namespace hygiene).  The rounding layer below duplicates names
(`S_pos`, `S_ne`, `md_le`, `md_gt`, `mu_ge`, `mu_lt`, `dvu_ge`, `dvu_lt`, `cx_re`, `cx_im`) that are
also defined in `Submission/Work/Cert/LeafAux.lean` (and `S_pos` in `Cert/rot_aux.lean`).  Two
modules defining the same constant cannot be imported together, which made the final assembly of
`Work.Cert.leaf_sound` (LeafAux) with `Work.Cert.theta_encl` (this file) impossible.  The names in
THIS file (and in its users: `aInv_base`, `aInv_step`, `aLoop_aux`, `bLoop_inv`, `binv_base1`,
`bstep_Br_le`, `bstep_num`, `bstep_por_le`, `bstep_psr_le`, `cx_mul_le`, `dA_step`, `theta_encl`,
`theta_keep`) have therefore been renamed with the prefix `th`; nothing else changed (the statements
are identical, only the names carry `th`).  `rot_aux.lean`'s `S_pos` was renamed `rotS_pos`.
Backups of the pre-rename files: `ScratchH25/pre_rename/`; the script is `ScratchH25/rename.sh`. -/

namespace Work.Cert

open Complex Finset

noncomputable section

/-! ## Scale and index notation -/

lemma thS_pos : (0 : ℝ) < (S : ℝ) := by
  have h : (0 : ℤ) < S := by norm_num [S]
  exact_mod_cast h

lemma thS_ne : (S : ℝ) ≠ 0 := ne_of_gt thS_pos

lemma S_ge_one : (1 : ℝ) ≤ (S : ℝ) := by
  have h : (1 : ℤ) ≤ S := by norm_num [S]
  exact_mod_cast h

/-- The `k`-th triangular number `k(k+1)/2`. -/
def tri (k : ℕ) : ℕ := k * (k + 1) / 2

@[simp] lemma tri_zero : tri 0 = 0 := rfl
@[simp] lemma tri_one : tri 1 = 1 := rfl

lemma tri_succ (k : ℕ) : tri (k + 1) = tri k + (k + 1) := by
  have h : (k + 1) * ((k + 1) + 1) = k * (k + 1) + (k + 1) * 2 := by ring
  unfold tri
  rw [h, Nat.add_mul_div_right _ _ (by norm_num : 0 < 2)]

lemma tri_pos {k : ℕ} (hk : 1 ≤ k) : 1 ≤ tri k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [show 1 + j = j + 1 by omega, tri_succ]
  omega

/-- `tri` grows at least like the identity (used for the geometric tails). -/
lemma le_tri (k : ℕ) : k ≤ tri k := by
  induction k with
  | zero => simp
  | succ k ih => rw [tri_succ]; omega

/-- Mantissa `m` seen as a real number `m/((S : ℝ))`. -/
noncomputable def mub (m : ℤ) : ℝ := (m : ℝ) / ((S : ℝ))

/-- The centre `(qr + i·qi)/((S : ℝ))` of the theta-sum disc. -/
noncomputable def qc (qr qi : ℤ) : ℂ := cx qr qi

/-! ## Rounding arithmetic (one ulp) -/

lemma thmd_le (a b : ℤ) : ((md a b : ℤ) : ℝ) / ((S : ℝ)) ≤ ((a : ℝ) / ((S : ℝ))) * ((b : ℝ) / ((S : ℝ))) := by
  have hS : (0 : ℤ) < S := by norm_num [S]
  have hSp : (0 : ℝ) < ((S : ℝ)) := thS_pos
  have h : md a b * S ≤ a * b := Int.ediv_mul_le (a * b) (ne_of_gt hS)
  have hR : ((md a b : ℤ) : ℝ) * ((S : ℝ)) ≤ (a : ℝ) * (b : ℝ) := by
    exact_mod_cast h
  rw [div_le_iff₀ hSp,
    show ((a : ℝ) / ((S : ℝ))) * ((b : ℝ) / ((S : ℝ))) * ((S : ℝ)) = (a : ℝ) * (b : ℝ) / ((S : ℝ)) by field_simp,
    le_div_iff₀ hSp]
  exact hR

lemma thmd_gt (a b : ℤ) : ((a : ℝ) / ((S : ℝ))) * ((b : ℝ) / ((S : ℝ))) - 1 / ((S : ℝ)) < ((md a b : ℤ) : ℝ) / ((S : ℝ)) := by
  have hS : (0 : ℤ) < S := by norm_num [S]
  have hSp : (0 : ℝ) < ((S : ℝ)) := thS_pos
  have h : a * b < (md a b + 1) * S := Int.lt_ediv_add_one_mul_self (a * b) hS
  have hR : (a : ℝ) * (b : ℝ) < (((md a b : ℤ) : ℝ) + 1) * ((S : ℝ)) := by
    exact_mod_cast h
  rw [lt_div_iff₀ hSp,
    show (((a : ℝ) / ((S : ℝ))) * ((b : ℝ) / ((S : ℝ))) - 1 / ((S : ℝ))) * ((S : ℝ)) = ((a : ℝ) * (b : ℝ) - ((S : ℝ))) / ((S : ℝ)) by
      field_simp,
    div_lt_iff₀ hSp]
  linarith

lemma thmu_ge (a b : ℤ) : ((a : ℝ) / ((S : ℝ))) * ((b : ℝ) / ((S : ℝ))) ≤ ((mu a b : ℤ) : ℝ) / ((S : ℝ)) := by
  have hS : (0 : ℤ) < S := by norm_num [S]
  have hSp : (0 : ℝ) < ((S : ℝ)) := thS_pos
  have h : (-(a * b)) / S * S ≤ -(a * b) := Int.ediv_mul_le _ (ne_of_gt hS)
  have hR : (a : ℝ) * (b : ℝ) ≤ ((mu a b : ℤ) : ℝ) * ((S : ℝ)) := by
    have h2 : (a * b : ℤ) ≤ -((-(a * b)) / S) * S := by linarith
    have h3 := (Int.cast_le (R := ℝ)).mpr h2
    push_cast at h3
    rw [show ((mu a b : ℤ) : ℝ) = -(((-(a * b)) / S : ℤ) : ℝ) from by
      have e : mu a b = -((-(a * b)) / S) := rfl
      rw [e]; push_cast; ring]
    linarith [h3]
  rw [le_div_iff₀ hSp,
    show ((a : ℝ) / ((S : ℝ))) * ((b : ℝ) / ((S : ℝ))) * ((S : ℝ)) = (a : ℝ) * (b : ℝ) / ((S : ℝ)) by field_simp,
    div_le_iff₀ hSp]
  exact hR

lemma thmu_lt (a b : ℤ) : ((mu a b : ℤ) : ℝ) / ((S : ℝ)) < ((a : ℝ) / ((S : ℝ))) * ((b : ℝ) / ((S : ℝ))) + 1 / ((S : ℝ)) := by
  have hS : (0 : ℤ) < S := by norm_num [S]
  have hSp : (0 : ℝ) < ((S : ℝ)) := thS_pos
  have h : -(a * b) < ((-(a * b)) / S + 1) * S := Int.lt_ediv_add_one_mul_self _ hS
  have hR : ((mu a b : ℤ) : ℝ) * ((S : ℝ)) < (a : ℝ) * (b : ℝ) + ((S : ℝ)) := by
    have h2 : -((-(a * b)) / S + 1) * S < (a * b : ℤ) := by linarith
    have h3 := (Int.cast_lt (R := ℝ)).mpr h2
    push_cast at h3
    rw [show ((mu a b : ℤ) : ℝ) = -(((-(a * b)) / S : ℤ) : ℝ) from by
      have e : mu a b = -((-(a * b)) / S) := rfl
      rw [e]; push_cast; ring]
    linarith [h3]
  rw [div_lt_iff₀ hSp,
    show (((a : ℝ) / ((S : ℝ))) * ((b : ℝ) / ((S : ℝ))) + 1 / ((S : ℝ))) * ((S : ℝ)) = ((a : ℝ) * (b : ℝ) + ((S : ℝ))) / ((S : ℝ)) by
      field_simp,
    lt_div_iff₀ hSp]
  linarith

lemma dvu_mul_le (a b : ℤ) (hb : 0 < b) : (a * S : ℤ) ≤ dvu a b * b := by
  have h : (-(a * S)) / b * b ≤ -(a * S) := Int.ediv_mul_le _ (ne_of_gt hb)
  have h2 : (a * S : ℤ) ≤ -((-(a * S)) / b) * b := by linarith
  have e : dvu a b = -((-(a * S)) / b) := rfl
  rw [e]; exact h2

lemma dvu_lt_mul (a b : ℤ) (hb : 0 < b) : (dvu a b - 1) * b < a * S := by
  have h : -(a * S) < ((-(a * S)) / b + 1) * b := Int.lt_ediv_add_one_mul_self _ hb
  have h2 : (-((-(a * S)) / b) - 1) * b < (a * S : ℤ) := by linarith
  have e : dvu a b = -((-(a * S)) / b) := rfl
  rw [e]; exact h2

lemma thdvu_ge (a b : ℤ) (hb : 0 < b) : (a : ℝ) / (b : ℝ) ≤ ((dvu a b : ℤ) : ℝ) / ((S : ℝ)) := by
  have hSp : (0 : ℝ) < ((S : ℝ)) := thS_pos
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hR : (a : ℝ) * ((S : ℝ)) ≤ ((dvu a b : ℤ) : ℝ) * (b : ℝ) := by
    have h := dvu_mul_le a b hb
    exact_mod_cast h
  rw [le_div_iff₀ hSp,
    show (a : ℝ) / (b : ℝ) * ((S : ℝ)) = (a : ℝ) * ((S : ℝ)) / (b : ℝ) by field_simp,
    div_le_iff₀ hbR]
  exact hR

lemma thdvu_lt (a b : ℤ) (hb : 0 < b) : ((dvu a b : ℤ) : ℝ) / ((S : ℝ)) < (a : ℝ) / (b : ℝ) + 1 / ((S : ℝ)) := by
  have hSp : (0 : ℝ) < ((S : ℝ)) := thS_pos
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hR : (((dvu a b : ℤ) : ℝ) - 1) * (b : ℝ) < (a : ℝ) * ((S : ℝ)) := by
    have h := dvu_lt_mul a b hb
    exact_mod_cast h
  have key : ((dvu a b : ℤ) : ℝ) < (a : ℝ) * ((S : ℝ)) / (b : ℝ) + 1 := by
    have h1 : ((dvu a b : ℤ) : ℝ) - 1 < (a : ℝ) * ((S : ℝ)) / (b : ℝ) := by
      rw [lt_div_iff₀ hbR]; linarith
    linarith
  rw [div_lt_iff₀ hSp,
    show ((a : ℝ) / (b : ℝ) + 1 / ((S : ℝ))) * ((S : ℝ)) = (a : ℝ) * ((S : ℝ)) / (b : ℝ) + 1 by field_simp]
  exact key

/-! ## The complex layer: the mantissa pair `(x,y)` represents `(x + y·i)/((S : ℝ))` -/

lemma thcx_re (x y : ℤ) : (cx x y).re = (x : ℝ) / ((S : ℝ)) := by simp [cx]

lemma thcx_im (x y : ℤ) : (cx x y).im = (y : ℝ) / ((S : ℝ)) := by simp [cx]

/-- Addition of mantissa pairs is exact. -/
lemma cx_add (a b c d : ℤ) : cx (a + c) (b + d) = cx a b + cx c d := by
  simp only [cx]; push_cast; ring

/-- Scaled (division-free) form of the one-ulp product bound: `md x c` differs from
`x·c/S` by less than `1`. -/
lemma md_err' (x c : ℤ) :
    |((md x c : ℤ) : ℝ) - (x : ℝ) * (c : ℝ) / ((S : ℝ))| < 1 := by
  have hS : (0 : ℤ) < S := by norm_num [S]
  have h1 : md x c * S ≤ x * c := Int.ediv_mul_le _ (ne_of_gt hS)
  have h2 : x * c < (md x c + 1) * S := Int.lt_ediv_add_one_mul_self _ hS
  have h1R : ((md x c : ℤ) : ℝ) * ((S : ℝ)) ≤ (x : ℝ) * (c : ℝ) := by exact_mod_cast h1
  have h2R : (x : ℝ) * (c : ℝ) < (((md x c : ℤ) : ℝ) + 1) * ((S : ℝ)) := by exact_mod_cast h2
  have h3 : ((md x c : ℤ) : ℝ) ≤ (x : ℝ) * (c : ℝ) / ((S : ℝ)) := by
    rw [le_div_iff₀ thS_pos]; linarith
  have h4 : (x : ℝ) * (c : ℝ) / ((S : ℝ)) - 1 < ((md x c : ℤ) : ℝ) := by
    rw [sub_lt_iff_lt_add, div_lt_iff₀ thS_pos]; linarith
  rw [abs_lt]; exact ⟨by linarith, by linarith⟩

lemma normSq_cx (x y : ℤ) : Complex.normSq (cx x y) = ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) / ((S : ℝ)) ^ 2 := by
  simp only [cx, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im]
  field_simp
  ring

/-- The norm of a mantissa pair. -/
lemma norm_cx_le {x y : ℤ} {r : ℝ} (h : (x : ℝ) ^ 2 + (y : ℝ) ^ 2 ≤ r ^ 2) (hr : 0 ≤ r) :
    ‖cx x y‖ ≤ r / ((S : ℝ)) := by
  have h1 : Complex.normSq (cx x y) ≤ (r / ((S : ℝ))) ^ 2 := by
    rw [normSq_cx, div_pow, div_le_div_iff₀ (sq_pos_of_pos thS_pos) (sq_pos_of_pos thS_pos)]
    nlinarith [h]
  have h2 : ‖cx x y‖ ^ 2 ≤ (r / ((S : ℝ))) ^ 2 := by rw [Complex.sq_norm]; exact h1
  have h3 : |‖cx x y‖| ≤ |r / ((S : ℝ))| := sq_le_sq.mp h2
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (div_nonneg hr (le_of_lt thS_pos))] at h3

/-! ## Exactness of the scale -/

lemma md_S (x : ℤ) : md S x = x := by
  have hS : (0 : ℤ) < S := by norm_num [S]
  have e : md S x = (S * x) / S := rfl
  rw [e, mul_comm, Int.mul_ediv_cancel x (ne_of_gt hS)]

lemma md_self_S (x : ℤ) : md x S = x := by
  have hS : (0 : ℤ) < S := by norm_num [S]
  have e : md x S = (x * S) / S := rfl
  rw [e, Int.mul_ediv_cancel x (ne_of_gt hS)]

lemma mu_S (x : ℤ) : mu S x = x := by
  have hS : (0 : ℤ) < S := by norm_num [S]
  have e : mu S x = -((-(S * x)) / S) := rfl
  rw [e, show (-(S * x) : ℤ) = (-x) * S by ring, Int.mul_ediv_cancel (-x) (ne_of_gt hS)]
  ring


/-! ## Budgets, partial sums and the loop invariants

The two accumulator loops `aLoop` (triangular exponents, `thetaA`) and `bLoop` (squares, `thetaB`)
are certified by the following invariants.  In both, `k` counts *completed* steps, so at a state
satisfying the invariant with index `k` the `(k+1)`-st step is `aStep qr qi rq m (k+1)` /
`bStep q2r q2i rq m (k+1)`.

The bounds are (in mantissa units, i.e. multiplied by `S`):

* pn-error `≤ 8` (`A`), pT-error `≤ 8·tri k` (`A`), por-error `≤ 16`, psr-error `≤ 8k²` (`B`);
* `mn ≥ μ^k`, `mT ≥ μ^{tri k}` (`μ = m/S` upper bound on `|q|` and on the centre) — these give the
  MVT credits and the tail credits;
* `dA ≥ Bd k + BdM k` (`dB ≥ Bd2 k + BdM2 k`), the sum of the per-step rounding allowances
  `8·tri(k+1)+1` (resp. `16(k+1)²+1`) and of the per-step mean-value terms
  `tri(k+1)·μ^{tri(k+1)-1}·rq` (resp. `2(k+1)²·μ^{(k+1)²-1}·rq`);
* the accumulated enclosure error of the partial sum `≤ Bd k/S` (resp. `Bd2 k/S`).

Proof plan for the step `k → k+1` (`k ≥ 1`): combine `hcxmul` with the product/MVT bounds; the
crucial arithmetic inputs are `μ ≤ 79/100`, `rq ≥ 0`, and that the integer roundings `md`, `mu`,
`dvu` only ever *help* (`mu a b ≥ a·b/S`, `dvu a b ≥ a·S/b`, `mu a b + 1 > a·b/S`).
The base case is the explicitly computed state after the *first* step, where `md S x = x` and
`mu S x = x` are exact: there `pn = z`, `pT = z^{tri 1}`, `mn = m+1`, `mT = m+2`,
`dA = mu (1 · dvu (m+2) m) rq + 9`, and similarly for `B`. -/

/-- Rounding allowance accumulated by the `A` loop after `k` steps. -/
noncomputable def Bd (k : ℕ) : ℝ := ∑ j ∈ Finset.range k, ((((8 * tri (j + 1) + 1 : ℕ)) : ℝ))

/-- Mean-value budget accumulated by the `A` loop after `k` steps. -/
noncomputable def BdM (m rq : ℤ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, ((tri (j + 1) : ℝ) * (mub m) ^ (tri (j + 1) - 1) * (rq : ℝ))

/-- Rounding allowance accumulated by the `B` loop after `k` steps. -/
noncomputable def Bd2 (k : ℕ) : ℝ := ∑ j ∈ Finset.range k, ((((16 * (j + 1) ^ 2 + 1 : ℕ)) : ℝ))

/-- Mean-value budget accumulated by the `B` loop after `k` steps. -/
noncomputable def BdM2 (m rq : ℤ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, (2 * (((j + 1) ^ 2 : ℕ) : ℝ) * (mub m) ^ ((j + 1) ^ 2 - 1) * (rq : ℝ))

/-- `k`-th partial sum `Σ_{j<k} q^{tri j}` of `thetaA`. -/
noncomputable def Asum (q : ℂ) (k : ℕ) : ℂ := ∑ j ∈ Finset.range k, q ^ tri j

/-- `k`-th partial sum `1 + Σ_{j<k} 2(-1)^{j+1} q^{(j+1)²}` of `thetaB`. -/
noncomputable def Bsum (q : ℂ) (k : ℕ) : ℂ :=
  1 + ∑ j ∈ Finset.range k, (2 * (-1 : ℂ) ^ (j + 1) * q ^ ((j + 1) ^ 2))

/-- Invariant of the `A` accumulator loop after `k` completed steps (see the module docstring).

The `pn` and `pT` error constants are the *reachable* ones: the `pn` error recurs as
`e(k+1) ≤ μ·e(k) + 3/S` with `μ ≤ 79/100`, so its limit is `3/(1-μ) ≤ 14.29` ulps (bound `16`); the
`pT` error then satisfies `f(k+1) ≤ μ·f(k) + 16/S + 3/S`, whence the linear bound
`20·(k-1)` ulps, which stays inside the per-step budget `8·tri k + 1`. -/
def AInv (qr qi rq m : ℤ) (k : ℕ) (s : TS) : Prop :=
  ‖cx s.pnr s.pni - (qc qr qi) ^ k‖ ≤ 16 / ((S : ℝ)) ∧
  ‖cx s.pTr s.pTi - (qc qr qi) ^ tri k‖ ≤ (20 * ((k - 1 : ℕ) : ℝ)) / ((S : ℝ)) ∧
  s.T = (tri k : ℤ) ∧
  (mub m) ^ k ≤ (s.mn : ℝ) / ((S : ℝ)) ∧
  (mub m) ^ (tri k) ≤ (s.mT : ℝ) / ((S : ℝ)) ∧
  Bd k + BdM m rq k ≤ (s.dA : ℝ) ∧
  ‖cx s.Ar s.Ai - Asum (qc qr qi) (k + 1)‖ ≤ (Bd k) / ((S : ℝ))

/-- Invariant of the `B` accumulator loop after `k` completed steps (see the module docstring). -/
def BInv (qr qi rq m : ℤ) (k : ℕ) (s : BS) : Prop :=
  ‖cx s.por s.poi - (qc qr qi) ^ (2 * k + 1)‖ ≤ 16 / ((S : ℝ)) ∧
  ‖cx s.psr s.psi - (qc qr qi) ^ (k * k)‖ ≤ (8 * ((k * k : ℕ) : ℝ)) / ((S : ℝ)) ∧
  (mub m) ^ (k * k) ≤ (s.ms : ℝ) / ((S : ℝ)) ∧
  (mub m) ^ (2 * k + 1) ≤ (s.mo : ℝ) / ((S : ℝ)) ∧
  Bd2 k + BdM2 m rq k ≤ (s.dB : ℝ) ∧
  ‖cx s.Br s.Bi - Bsum (qc qr qi) k‖ ≤ (Bd2 k) / ((S : ℝ))

end

end Work.Cert

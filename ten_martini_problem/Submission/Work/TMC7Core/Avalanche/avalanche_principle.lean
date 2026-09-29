import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Cocycle.frob_mul_le
import Submission.Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one
import Submission.Work.TMC7Core.Avalanche.rift_def
import Submission.Work.TMC7Core.Avalanche.dframe
import Submission.Work.TMC7Core.Avalanche.svd_ge_one
import Submission.Work.TMC7Core.Avalanche.frob_unitary
import Submission.Work.TMC7Core.Avalanche.frob_Dm_mul_Dm
import Submission.Work.TMC7Core.Avalanche.lambda_pair_bound
import Submission.Work.TMC7Core.Avalanche.core_est

/-!
# TMC7Core: the avalanche principle (Goldstein–Schlag / Bourgain–Jitomirskaya)

This file formalises the *avalanche principle* for finite products of `2×2` complex
matrices of determinant one, in the form used by Bourgain–Jitomirskaya (*J. Stat. Phys.*
108 (2002), Lemma 5) and by the Ten Martini proof (component `C7`).

## Notation

For a sequence `A : ℕ → Matrix (Fin 2) (Fin 2) ℂ` we write

* `P k = matProd A k = A (k-1) ⋯ A 0` (so `P 0 = 1`),
* `b j  = log ‖A j‖_F`,
* `c j  = log ‖A (j+1) * A j‖_F`,
* `d j  = b (j+1) + b j - c j`               (the *pair defect*, `≥ 0`),
* `dl j = log (‖A j‖_F * ‖P j‖_F / ‖P (j+1)‖_F)` (the *partial-product defect*, `≥ 0`).

The quantity estimated by the theorem is (compare `sum_dl` below)

  `L + Σ_{j=1}^{n-2} b j - Σ_{j=0}^{n-2} c j = Σ_{k=1}^{n-1} (d (k-1) - dl k)`.

The mathematical content is that each *partial-product defect* `dl k` is essentially the
corresponding *pair defect* `d (k-1)`: the long partial product `P k` "looks like" the
single matrix `A (k-1)` as seen from `A k`.  This is the avalanche principle.

## Strategy

`frob` is the Frobenius norm (`= ‖·‖_HS`), and for `det = 1` matrices the singular values
are `σ` and `σ⁻¹` (`σ = ‖·‖_op`), so `frob M ^ 2 = σ ^ 2 + σ ^ (-2)`.  The proof proceeds
through the following layers (see `ROUTE_LEAD.md`, component `C7`, item "AP"):

1. elementary single-matrix estimates (this file, `*_le` lemmas),
2. the telescoping identity `sum_dl` (this file),
3. a uniform per-term bound `|d (k-1) - dl k| ≤ C / μ` (this file, `perTerm_le`),
4. assembly (`avalanche_principle`).

-/

open Matrix
open scoped Matrix.Norms.Frobenius

noncomputable section

namespace Work.TMC7Core.Avalanche

/-! ## 1. Notation -/

/-- `b j = log ‖A j‖_F`. -/
def bOf (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (j : ℕ) : ℝ := Real.log (frob (A j))

/-- `c j = log ‖A (j+1) * A j‖_F`. -/
def cOf (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (j : ℕ) : ℝ :=
  Real.log (frob (A (j + 1) * A j))

/-- The pair defect `d j = log (‖A (j+1)‖_F ‖A j‖_F / ‖A (j+1) * A j‖_F) ≥ 0`. -/
def dOf (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (j : ℕ) : ℝ :=
  Real.log (frob (A (j + 1)) * frob (A j) / frob (A (j + 1) * A j))

/-- The partial-product defect `dl j = log (‖A j‖_F ‖P j‖_F / ‖P (j+1)‖_F) ≥ 0`. -/
def dlOf (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (j : ℕ) : ℝ :=
  Real.log (frob (A j) * frob (matProd A j) / frob (matProd A (j + 1)))

/-! ## 2. Positivity -/

lemma frob_matProd_pos (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hdet : ∀ j, (A j).det = 1) (j : ℕ) :
    0 < frob (matProd A j) :=
  lt_of_lt_of_le (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
    (Cocycle.frob_sqrt_two_le_of_det_one (det_matProd A hdet j))

lemma frobA_pos (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hdet : ∀ j, (A j).det = 1) (j : ℕ) :
    0 < frob (A j) :=
  lt_of_lt_of_le (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
    (Cocycle.frob_sqrt_two_le_of_det_one (hdet j))

lemma log_frob_matProd_zero (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) :
    Real.log (frob (matProd A 0)) = Real.log (Real.sqrt 2) := by
  rw [matProd_zero, frob_one]

/-! ## 3. The telescoping identity -/

/-- Telescoping identity: `∑_{j<n} dl j = ∑_{j<n} b j - log ‖P n‖_F + log √2`. -/
lemma sum_dl (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hdet : ∀ j, (A j).det = 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, dlOf A j
      = (∑ j ∈ Finset.range n, bOf A j) - Real.log (frob (matProd A n))
        + Real.log (Real.sqrt 2) := by
  induction n with
  | zero => simp [dlOf, bOf, log_frob_matProd_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    unfold dlOf bOf
    have hPn : 0 < frob (matProd A n) := frob_matProd_pos A hdet n
    have hPn1 : 0 < frob (matProd A (n + 1)) := frob_matProd_pos A hdet (n + 1)
    have hA : 0 < frob (A n) := frobA_pos A hdet n
    have hps : matProd A (n + 1) = A n * matProd A n := matProd_succ A n
    rw [hps] at hPn1 ⊢
    rw [Real.log_div (by positivity) hPn1.ne', Real.log_mul hA.ne' hPn.ne']
    ring

/-- `dl 0 = log √2`. -/
lemma dlOf_zero (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hdet : ∀ j, (A j).det = 1) :
    dlOf A 0 = Real.log (Real.sqrt 2) := by
  unfold dlOf
  have h0 : frob (matProd A 0) = Real.sqrt 2 := by rw [matProd_zero, frob_one]
  have h1 : frob (matProd A 1) = frob (A 0) := by rw [matProd_succ, matProd_zero, mul_one]
  rw [h0, h1]
  have hA : frob (A 0) ≠ 0 := (frobA_pos A hdet 0).ne'
  field_simp

/-! ## 4. The assembly identity

The target of `avalanche_principle` is

  `target = L + Σ_{j=1}^{n-2} b j - Σ_{j=0}^{n-2} c j`,

and the per-term defects `d (k-1) - dl k` telescope to it.  This section proves the exact
identity (proved below as `assembly`).  Hence the theorem reduces to bounding each
`|d (k-1) - dl k|`. -/

lemma frob_pos_det_one_ap {M : Matrix (Fin 2) (Fin 2) ℂ} (h : M.det = 1) : 0 < frob M :=
  lt_of_lt_of_le (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
    (Cocycle.frob_sqrt_two_le_of_det_one h)

lemma frob_prod_pos (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hdet : ∀ j, (A j).det = 1) (j : ℕ) :
    0 < frob (A (j + 1) * A j) :=
  frob_pos_det_one_ap (by rw [Matrix.det_mul, hdet (j + 1), hdet j, one_mul])

/-- `d j = b (j+1) + b j - c j`. -/
lemma dOf_eq (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hdet : ∀ j, (A j).det = 1) (j : ℕ) :
    dOf A j = bOf A (j + 1) + bOf A j - cOf A j := by
  unfold dOf bOf cOf
  rw [Real.log_div (ne_of_gt (mul_pos (frobA_pos A hdet (j + 1)) (frobA_pos A hdet j)))
        (ne_of_gt (frob_prod_pos A hdet j)),
      Real.log_mul (frobA_pos A hdet (j + 1)).ne' (frobA_pos A hdet j).ne']

/-- `dl (j+1) = b (j+1) + log ‖P (j+1)‖_F - log ‖P (j+2)‖_F`. -/
lemma dlOf_eq (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hdet : ∀ j, (A j).det = 1) (j : ℕ) :
    dlOf A (j + 1) = bOf A (j + 1) + Real.log (frob (matProd A (j + 1)))
      - Real.log (frob (matProd A (j + 2))) := by
  unfold dlOf bOf
  rw [show matProd A (j + 2) = A (j + 1) * matProd A (j + 1) from matProd_succ A (j + 1),
    Real.log_div (ne_of_gt (mul_pos (frobA_pos A hdet (j + 1)) (frob_matProd_pos A hdet (j + 1))))
      (ne_of_gt (frob_pos_det_one_ap (by
        rw [Matrix.det_mul, hdet (j + 1), det_matProd A hdet (j + 1), one_mul]))),
    Real.log_mul (frobA_pos A hdet (j + 1)).ne' (frob_matProd_pos A hdet (j + 1)).ne']

/-- The one-step identity behind the induction. -/
lemma step (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hdet : ∀ j, (A j).det = 1) (m : ℕ) :
    (Real.log (frob (matProd A (m + 3))) - Real.log (frob (matProd A (m + 2))))
      + bOf A (m + 1) - cOf A (m + 1) = dOf A (m + 1) - dlOf A (m + 2) := by
  rw [dOf_eq A hdet (m + 1), dlOf_eq A hdet (m + 1)]
  ring

lemma assembly_base (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hdet : ∀ j, (A j).det = 1) :
    Real.log (frob (matProd A 2)) + (∑ j ∈ Finset.Icc 1 0, bOf A j)
      - (∑ j ∈ Finset.range 1, cOf A j)
    = ∑ k ∈ Finset.Icc 1 1, (dOf A (k - 1) - dlOf A k) := by
  rw [Finset.Icc_eq_empty (by norm_num : ¬ (1 : ℕ) ≤ 0), Finset.sum_empty, Finset.sum_range_one,
    Finset.Icc_self, Finset.sum_singleton]
  have h1 : matProd A (1 : ℕ) = A 0 := by rw [matProd_succ, matProd_zero, mul_one]
  have h2 : matProd A (2 : ℕ) = A 1 * A 0 := by rw [matProd_succ, h1]
  unfold dOf dlOf cOf
  simp only [show (1 : ℕ) - 1 = 0 from rfl, show (0 : ℕ) + 1 = 1 from rfl,
    show (1 : ℕ) + 1 = 2 from rfl]
  rw [h1, h2]
  ring_nf

/-- Assembly, in the form `n = m + 2`. -/
lemma assembly_aux (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hdet : ∀ j, (A j).det = 1) (m : ℕ) :
    Real.log (frob (matProd A (m + 2))) + (∑ j ∈ Finset.Icc 1 m, bOf A j)
      - (∑ j ∈ Finset.range (m + 1), cOf A j)
    = ∑ k ∈ Finset.Icc 1 (m + 1), (dOf A (k - 1) - dlOf A k) := by
  induction m with
  | zero => exact assembly_base A hdet
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (show (1 : ℕ) ≤ m + 1 by omega),
        Finset.sum_range_succ,
        Finset.sum_Icc_succ_top (show (1 : ℕ) ≤ m + 2 by omega),
        ← ih]
    simp only [show m + 1 + 2 = m + 3 from by omega, show m + 1 + 1 = m + 2 from by omega,
      show m + 1 + 1 - 1 = m + 1 from by omega]
    linarith [step A hdet m]

/-- **Assembly identity.**  The target expression equals the sum of the per-term defects
`d (k-1) - dl k`. -/
lemma assembly (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) (hn : 2 ≤ n)
    (hdet : ∀ j, (A j).det = 1) :
    Real.log (frob (matProd A n)) + (∑ j ∈ Finset.Icc 1 (n - 2), bOf A j)
      - (∑ j ∈ Finset.range (n - 1), cOf A j)
    = ∑ k ∈ Finset.Icc 1 (n - 1), (dOf A (k - 1) - dlOf A k) := by
  have h := assembly_aux A hdet (n - 2)
  simpa only [show (n - 2) + 2 = n from by omega,
    show (n - 2) + 2 - 2 = n - 2 from by omega,
    show (n - 2) + 2 - 1 = n - 1 from by omega,
    show (n - 2) + 1 = n - 1 from by omega] using h


/-! ## 4b. The rift form of `dOf` and `dlOf`

`dOf A j = log(‖A (j+1)‖ ‖A j‖/‖A (j+1) A j‖) = - log R(A (j+1), A j)` and
`dlOf A j = - log R(A j, P j)`. Hence `dOf A (k-1) - dlOf A k` is exactly the difference of the
logarithms of the two rifts that the avalanche step controls. -/

/-- `P 1 = A 0`. -/
lemma matProd_one_of (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) : matProd A 1 = A 0 := by
  rw [matProd_succ, matProd_zero, mul_one]

lemma dOf_add_log_rift (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (j : ℕ) :
    dOf A j + Real.log (rift (A (j+1)) (A j)) = 0 := by
  have h : rift (A (j+1)) (A j)
      = (frob (A (j+1)) * frob (A j) / frob (A (j+1) * A j))⁻¹ := by
    unfold rift; rw [inv_div]
  simp only [dOf]
  rw [h, Real.log_inv]
  ring

lemma dOf_eq_neg_log_rift (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (j : ℕ) :
    dOf A j = -Real.log (rift (A (j+1)) (A j)) := by
  have := dOf_add_log_rift A j
  linarith

lemma dlOf_add_log_rift (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (j : ℕ) :
    dlOf A j + Real.log (rift (A j) (matProd A j)) = 0 := by
  have h : rift (A j) (matProd A j)
      = (frob (A j) * frob (matProd A j) / frob (matProd A (j+1)))⁻¹ := by
    unfold rift; rw [matProd_succ, inv_div]
  simp only [dlOf]
  rw [h, Real.log_inv]
  ring

lemma dlOf_eq_neg_log_rift (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (j : ℕ) :
    dlOf A j = -Real.log (rift (A j) (matProd A j)) := by
  have := dlOf_add_log_rift A j
  linarith

/-- The pairing identity: the per-term defect is the log-difference of the two rifts. -/
lemma dOf_sub_dlOf_eq (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) (hk : 1 ≤ k) :
    dOf A (k-1) - dlOf A k
      = Real.log (rift (A k) (matProd A k)) - Real.log (rift (A k) (A (k-1))) := by
  rw [dOf_eq_neg_log_rift A (k-1), dlOf_eq_neg_log_rift A k,
    show k - 1 + 1 = k from by omega]
  ring

/-- The pair condition in rift form: `R(A (j+1), A j) > 1/√μ`. -/
lemma one_div_sqrt_le_rift_of_pair (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (μ : ℝ) (j : ℕ)
    (hμ1 : 1 ≤ μ) (hdet : ∀ i, (A i).det = 1)
    (hpair : Real.log (frob (A (j+1))) + Real.log (frob (A j))
      - Real.log (frob (A (j+1) * A j)) < Real.log μ / 2) :
    1 / Real.sqrt μ ≤ rift (A (j+1)) (A j) := by
  have hμpos : 0 < μ := lt_of_lt_of_le (by norm_num) hμ1
  have hs : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμpos
  have hlt : Real.log (rift (A (j+1)) (A j)) > Real.log (1 / Real.sqrt μ) := by
    have key : Real.log (rift (A (j+1)) (A j))
        = -(Real.log (frob (A (j+1))) + Real.log (frob (A j))
            - Real.log (frob (A (j+1) * A j))) := by
      have h : rift (A (j+1)) (A j)
          = (frob (A (j+1)) * frob (A j) / frob (A (j+1) * A j))⁻¹ := by
        unfold rift; rw [inv_div]
      rw [h, Real.log_inv]
      have hmul : Real.log (frob (A (j+1)) * frob (A j) / frob (A (j+1) * A j))
          = Real.log (frob (A (j+1))) + Real.log (frob (A j))
            - Real.log (frob (A (j+1) * A j)) := by
        have hp1 : 0 < frob (A (j+1)) := frob_pos_det_one_ap (hdet (j+1))
        have hp2 : 0 < frob (A j) := frob_pos_det_one_ap (hdet j)
        have hp3 : 0 < frob (A (j+1) * A j) :=
          frob_pos_det_one_ap (by rw [Matrix.det_mul, hdet (j+1), hdet j, one_mul])
        rw [Real.log_div (ne_of_gt (mul_pos hp1 hp2)) (ne_of_gt hp3),
          Real.log_mul hp1.ne' hp2.ne']
      rw [hmul]
    rw [key, Real.log_div one_ne_zero (ne_of_gt hs), Real.log_one, Real.log_sqrt (le_of_lt hμpos)]
    linarith
  calc 1 / Real.sqrt μ = Real.exp (Real.log (1 / Real.sqrt μ)) :=
        (Real.exp_log (by positivity)).symm
    _ ≤ Real.exp (Real.log (rift (A (j+1)) (A j))) := Real.exp_le_exp.mpr (le_of_lt hlt)
    _ = rift (A (j+1)) (A j) := Real.exp_log (by
        unfold rift
        exact div_pos (frob_pos_det_one_ap (by rw [Matrix.det_mul, hdet (j+1), hdet j, one_mul]))
          (mul_pos (frob_pos_det_one_ap (hdet (j+1))) (frob_pos_det_one_ap (hdet j))))

/-! ## 5. The `SVD` normal form of the chain, and the core estimate

Each `A j` of determinant one is `U j · Dm (σ j) · V jᴴ` (`svd_ge_one`).  With
`W j = (V (j+1))ᴴ · U j` and `Nmat`/`Gmat` from `dframe`, the whole target expression is
`log ‖N (n-1)‖_F - Σ_{j<n} log (σ j) - Σ_{j<n-1} log ‖W j 0 0‖` up to the error terms of the
passage between `frob (A j)` and `σ j` and between `frob (A (j+1) * A j)` and `σ (j+1) σ j ‖W j 0 0‖`.
`avalanche_core` is the analytic heart: the log-additive estimate for `Nmat`. -/

/-- The sorted SVD data `M = U · Dm a · Vᴴ` of a determinant-one `2×2` matrix. -/
structure SvdData (M : Matrix (Fin 2) (Fin 2) ℂ) where
  /-- left unitary factor -/
  U : Matrix (Fin 2) (Fin 2) ℂ
  /-- right unitary factor -/
  V : Matrix (Fin 2) (Fin 2) ℂ
  /-- the larger singular value -/
  a : ℝ
  hU1 : U.conjTranspose * U = 1
  hU2 : U * U.conjTranspose = 1
  hV1 : V.conjTranspose * V = 1
  hV2 : V * V.conjTranspose = 1
  ha : 1 ≤ a
  hM : M = U * Dm a * V.conjTranspose

theorem svdData_exists (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det = 1) : Nonempty (SvdData M) := by
  obtain ⟨U, V, a, hU1, hU2, hV1, hV2, ha, hUV⟩ := svd_ge_one M hM
  exact ⟨⟨U, V, a, hU1, hU2, hV1, hV2, ha, hUV⟩⟩

/-- The SVD data of `A j`, chosen once and for all. -/
noncomputable def svdData (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hdet : ∀ j, (A j).det = 1) (j : ℕ) :
    SvdData (A j) := Classical.choice (svdData_exists (A j) (hdet j))

/-- `σ j`: the larger singular value of `A j`. -/
noncomputable def svdSigma (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hdet : ∀ j, (A j).det = 1)
    (j : ℕ) : ℝ := (svdData A hdet j).a

/-- `W j = (V (j+1))ᴴ · U j`, the unitary linking two consecutive singular frames. -/
noncomputable def svdW (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hdet : ∀ j, (A j).det = 1)
    (j : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (svdData A hdet (j + 1)).V.conjTranspose * (svdData A hdet j).U

/-- `λ j = ‖W j 0 0‖`, the alignment of consecutive singular frames. -/
noncomputable def svdLam (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hdet : ∀ j, (A j).det = 1)
    (j : ℕ) : ℝ := ‖svdW A hdet j 0 0‖

theorem A_eq_svd (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hdet : ∀ j, (A j).det = 1) (j : ℕ) :
    A j = (svdData A hdet j).U * Dm (svdSigma A hdet j) * (svdData A hdet j).V.conjTranspose :=
  (svdData A hdet j).hM

/-- **The chain is a product of `Dm`'s and unitary `W`'s**: `A (n-1)⋯A 0 = U (n-1) · N (n-1) · V 0ᴴ`. -/
theorem matProd_eq_svd (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hdet : ∀ j, (A j).det = 1) :
    ∀ k : ℕ, matProd A (k + 1) =
      (svdData A hdet k).U * Nmat (svdSigma A hdet) (svdW A hdet) k
        * (svdData A hdet 0).V.conjTranspose := by
  intro k
  induction k with
  | zero =>
    rw [show (0 : ℕ) + 1 = 1 from rfl, show matProd A 1 = A 0 from by
        rw [matProd_succ, matProd_zero, mul_one]]
    exact (svdData A hdet 0).hM
  | succ k ih =>
    rw [show k + 1 + 1 = (k + 1) + 1 from rfl, matProd_succ]
    rw [ih]
    simp only [A_eq_svd A hdet (k + 1), Nmat_succ, svdW, svdSigma]
    noncomm_ring

/-! ## 6. The analytic core -/

/-! ## 6c. Frobenius norms in the SVD normal form -/

lemma frob_conjTranspose (M : Matrix (Fin 2) (Fin 2) ℂ) :
    frob M.conjTranspose = frob M := by
  simp only [frob, Matrix.conjTranspose_apply, Complex.norm_conj, norm_star, Fin.sum_univ_two]
  ring_nf

lemma frob_mul_conjTranspose (M W : Matrix (Fin 2) (Fin 2) ℂ) (hW : W.conjTranspose * W = 1) :
    frob (M * W.conjTranspose) = frob M := by
  rw [← frob_conjTranspose (M * W.conjTranspose), Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  rw [frob_unitary W M.conjTranspose hW, frob_conjTranspose M]

lemma frob_sandwich (U M V : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U.conjTranspose * U = 1) (hV : V.conjTranspose * V = 1) :
    frob (U * M * V.conjTranspose) = frob M := by
  rw [mul_assoc, frob_unitary U (M * V.conjTranspose) hU, frob_mul_conjTranspose M V hV]

lemma frob_Dm (s : ℝ) : frob (Dm s) = Real.sqrt (s ^ 2 + (s ^ 2)⁻¹) := by
  have h0 : ‖(Dm s) 0 0‖ ^ 2 = s ^ 2 := by
    simp [Dm, Matrix.diagonal, Complex.sq_norm]
  have h1 : ‖(Dm s) 0 1‖ ^ 2 = 0 := by
    simp [Dm, Matrix.diagonal]
  have h2 : ‖(Dm s) 1 0‖ ^ 2 = 0 := by
    simp [Dm, Matrix.diagonal]
  have h3 : ‖(Dm s) 1 1‖ ^ 2 = (s ^ 2)⁻¹ := by
    simp [Dm, Matrix.diagonal, Complex.sq_norm, inv_pow]
  simp only [frob, h0, h1, h2, h3]
  ring_nf

/-- **The avalanche core estimate in the SVD normal form.**  For a chain of diagonal scalings
`Dm (s j)` (with `s j ^ 2 ≥ μ ^ 2 - 1`) and unitaries `W j` whose leading entries satisfy
`λ j ^ 2 ≥ 1/μ - 2/(μ^2-1)^2`, the Frobenius norm of the truncated product `N (n-1)` is
log-additive up to `450 n/μ`.  This is the whole analytic content of the avalanche principle;
it is proved by an induction on the length of the chain (see the `core_*` lemmas below). -/
theorem avalanche_core (s : ℕ → ℝ) (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) (μ : ℝ)
    (hn : 2 ≤ n) (hμn : (n : ℝ) < μ) (hμ : 3 < μ)
    (hσ : ∀ j, j < n → 1 ≤ s j)
    (hσμ : ∀ j, j + 1 < n → μ ^ 2 - 1 ≤ (s j) ^ 2 ∧ μ ^ 2 - 1 ≤ (s (j + 1)) ^ 2)
    (hW : ∀ j, j + 1 < n → (W j).conjTranspose * W j = 1 ∧ W j * (W j).conjTranspose = 1)
    (hlam : ∀ j, j + 1 < n → 1 / μ - 2 / (μ ^ 2 - 1) ^ 2 ≤ ‖W j 0 0‖ ^ 2) :
    |Real.log (frob (Nmat s W (n - 1)))
        - (∑ j ∈ Finset.range n, Real.log (s j))
        - (∑ j ∈ Finset.range (n - 1), Real.log ‖W j 0 0‖)| ≤ 450 * (n : ℝ) / μ :=
  core_est s W n μ hn hμn hμ hσ hσμ hW hlam

/-! ## 5. The per-term estimate and the theorem

The target statement is reduced to `avalanche_core` by rewriting each `A j` in its SVD normal
form.  The conversion errors are of order `n/μ³` and are absorbed by the constant `1000`. -/

/-! ## 6d. The SVD normal form of the target expression -/

section Assembly

variable (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hdet : ∀ j, (A j).det = 1)

lemma frob_A_eq (j : ℕ) :
    frob (A j) = Real.sqrt ((svdSigma A hdet j) ^ 2 + ((svdSigma A hdet j) ^ 2)⁻¹) := by
  rw [A_eq_svd A hdet j,
    frob_sandwich _ _ _ (svdData A hdet j).hU1 (svdData A hdet j).hV1]
  exact frob_Dm _

lemma frob_pair_eq (j : ℕ) :
    frob (A (j + 1) * A j)
      = frob (Dm (svdSigma A hdet (j + 1)) * svdW A hdet j * Dm (svdSigma A hdet j)) := by
  have key : (svdData A hdet (j + 1)).U * Dm (svdData A hdet (j + 1)).a
        * (svdData A hdet (j + 1)).V.conjTranspose
      * ((svdData A hdet j).U * Dm (svdData A hdet j).a * (svdData A hdet j).V.conjTranspose)
      = (svdData A hdet (j + 1)).U
        * (Dm (svdData A hdet (j + 1)).a
            * ((svdData A hdet (j + 1)).V.conjTranspose * (svdData A hdet j).U)
            * Dm (svdData A hdet j).a)
        * (svdData A hdet j).V.conjTranspose := by noncomm_ring
  rw [A_eq_svd A hdet (j + 1), A_eq_svd A hdet j]
  simp only [svdSigma]
  rw [key, frob_sandwich _ _ _ (svdData A hdet (j + 1)).hU1 (svdData A hdet j).hV1]
  rfl

lemma one_le_svdSigma (j : ℕ) : 1 ≤ svdSigma A hdet j := (svdData A hdet j).ha

/-- The scalings are at least `√(μ²-1)` when every `A j` has Frobenius norm `≥ μ`. -/
lemma sq_svdSigma_ge (μ : ℝ) (hμ1 : 1 ≤ μ) (hnorm : ∀ j, μ ≤ frob (A j)) (j : ℕ) :
    μ ^ 2 - 1 ≤ (svdSigma A hdet j) ^ 2 := by
  have h1 : 1 ≤ svdSigma A hdet j := one_le_svdSigma A hdet j
  have h2 : μ ≤ frob (A j) := hnorm j
  rw [frob_A_eq A hdet j] at h2
  set x := (svdSigma A hdet j) ^ 2 with hx
  have hx1 : 1 ≤ x := by rw [hx]; nlinarith
  have hx2 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hsq : Real.sqrt (x + x⁻¹) ^ 2 = x + x⁻¹ := Real.sq_sqrt (by positivity)
  have h3 : μ ^ 2 ≤ x + x⁻¹ := by
    nlinarith [Real.sqrt_nonneg (x + x⁻¹), h2, hsq, hμ1]
  have h4 : x⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hx2]; exact hx1
  rw [hx]
  linarith

/-- The unitarity of the SVD frames. -/
lemma svdW_unitary (j : ℕ) :
    (svdW A hdet j).conjTranspose * svdW A hdet j = 1
      ∧ svdW A hdet j * (svdW A hdet j).conjTranspose = 1 := by
  have hV1 := (svdData A hdet (j + 1)).hV1
  have hV2 := (svdData A hdet (j + 1)).hV2
  have hU1 := (svdData A hdet j).hU1
  have hU2 := (svdData A hdet j).hU2
  constructor
  · calc (svdW A hdet j).conjTranspose * svdW A hdet j
        = (svdData A hdet j).U.conjTranspose
            * ((svdData A hdet (j + 1)).V * (svdData A hdet (j + 1)).V.conjTranspose)
            * (svdData A hdet j).U := by
          rw [svdW, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
          noncomm_ring
      _ = (svdData A hdet j).U.conjTranspose * 1 * (svdData A hdet j).U := by rw [hV2]
      _ = 1 := by rw [mul_one, hU1]
  · calc svdW A hdet j * (svdW A hdet j).conjTranspose
        = (svdData A hdet (j + 1)).V.conjTranspose
            * ((svdData A hdet j).U * (svdData A hdet j).U.conjTranspose)
            * (svdData A hdet (j + 1)).V := by
          rw [svdW, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
          noncomm_ring
      _ = (svdData A hdet (j + 1)).V.conjTranspose * 1 * (svdData A hdet (j + 1)).V := by rw [hU2]
      _ = 1 := by rw [mul_one, hV1]

/-- **The pair hypothesis in the SVD normal form**: the leading entry of `W j` is at least
`1/μ` in modulus squared, up to the explicit correction `2/(μ²-1)²`. -/
lemma lam_sq_ge (n : ℕ) (μ : ℝ) (hμ2 : 2 ≤ μ)
    (hnorm : ∀ j, μ ≤ frob (A j))
    (hpair : ∀ j, j + 1 < n → Real.log (frob (A (j + 1))) + Real.log (frob (A j))
        - Real.log (frob (A (j + 1) * A j)) < Real.log μ / 2)
    (j : ℕ) (hj : j + 1 < n) :
    1 / μ - 2 / (μ ^ 2 - 1) ^ 2 ≤ (svdLam A hdet j) ^ 2 := by
  have hμpos : 0 < μ := lt_of_lt_of_le (by norm_num) hμ2
  have hμ1 : 1 ≤ μ := by linarith
  have hla : 0 < frob (A (j + 1)) := frob_pos_det_one_ap (hdet (j + 1))
  have hlb : 0 < frob (A j) := frob_pos_det_one_ap (hdet j)
  have hlc : 0 < frob (A (j + 1) * A j) :=
    frob_pos_det_one_ap (by rw [Matrix.det_mul, hdet (j + 1), hdet j, one_mul])
  have hp := hpair j hj
  have hlog : Real.log (frob (A (j + 1)) * frob (A j) / frob (A (j + 1) * A j))
      = Real.log (frob (A (j + 1))) + Real.log (frob (A j))
        - Real.log (frob (A (j + 1) * A j)) := by
    rw [Real.log_div (by positivity) (ne_of_gt hlc),
      Real.log_mul (ne_of_gt hla) (ne_of_gt hlb)]
  have hlogsqrt : Real.log (Real.sqrt μ) = Real.log μ / 2 := Real.log_sqrt (le_of_lt hμpos)
  have hlt : frob (A (j + 1)) * frob (A j) / frob (A (j + 1) * A j) < Real.sqrt μ := by
    rw [← hlogsqrt, ← hlog] at hp
    exact (Real.log_lt_log_iff (by positivity) (Real.sqrt_pos.mpr hμpos)).mp hp
  have hsq : frob (A (j + 1)) ^ 2 * frob (A j) ^ 2
      < μ * frob (A (j + 1) * A j) ^ 2 := by
    have h1 : frob (A (j + 1)) * frob (A j)
        < Real.sqrt μ * frob (A (j + 1) * A j) := by
      rw [div_lt_iff₀ hlc] at hlt
      linarith [hlt]
    have h2 : (frob (A (j + 1)) * frob (A j)) ^ 2
        < (Real.sqrt μ * frob (A (j + 1) * A j)) ^ 2 := by
      have := mul_self_lt_mul_self
        (show (0 : ℝ) ≤ frob (A (j + 1)) * frob (A j) from by positivity) h1
      simpa [pow_two] using this
    have h3 : (Real.sqrt μ * frob (A (j + 1) * A j)) ^ 2
        = μ * frob (A (j + 1) * A j) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hμpos)]
    rw [mul_pow, h3] at h2
    exact h2
  have ha2 : frob (A (j + 1)) ^ 2
      = (svdSigma A hdet (j + 1)) ^ 2 + ((svdSigma A hdet (j + 1)) ^ 2)⁻¹ := by
    rw [frob_A_eq A hdet (j + 1), Real.sq_sqrt (by positivity)]
  have hb2 : frob (A j) ^ 2
      = (svdSigma A hdet j) ^ 2 + ((svdSigma A hdet j) ^ 2)⁻¹ := by
    rw [frob_A_eq A hdet j, Real.sq_sqrt (by positivity)]
  have hprod : ((svdSigma A hdet (j + 1)) ^ 2 + ((svdSigma A hdet (j + 1)) ^ 2)⁻¹)
      * ((svdSigma A hdet j) ^ 2 + ((svdSigma A hdet j) ^ 2)⁻¹)
      < μ * frob (Dm (svdSigma A hdet (j + 1)) * svdW A hdet j * Dm (svdSigma A hdet j)) ^ 2 := by
    rw [ha2, hb2, frob_pair_eq A hdet j] at hsq
    exact hsq
  have hW := svdW_unitary A hdet j
  have hres := lambda_pair_bound (svdSigma A hdet j) (svdSigma A hdet (j + 1)) μ
    (svdW A hdet j) hW.1 hW.2 (sq_svdSigma_ge A hdet μ hμ1 hnorm j)
    (sq_svdSigma_ge A hdet μ hμ1 hnorm (j + 1)) hμ2 (by rw [mul_comm]; exact hprod)
  simpa only [svdLam] using le_of_lt hres

end Assembly

/-- The relative defect of the pair `A (j+1) · A j` against the product of the two singular
values and the frame alignment. -/
noncomputable def delta (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hdet : ∀ j, (A j).det = 1) (j : ℕ) : ℝ :=
  frob (A (j + 1) * A j) ^ 2
    / ((svdSigma A hdet (j + 1)) ^ 2 * (svdSigma A hdet j) ^ 2 * (svdLam A hdet j) ^ 2) - 1

lemma norm_entry_le_one (W : Matrix (Fin 2) (Fin 2) ℂ) (hW : W.conjTranspose * W = 1) :
    ‖W 0 0‖ ≤ 1 := by
  have hE : frob (W * !![(1 : ℂ), 0; 0, 0]) = frob (!![(1 : ℂ), 0; 0, 0]) :=
    frob_unitary W _ hW
  have h2 : frob (!![(1 : ℂ), 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ^ 2 = 1 := by
    rw [frob_sq]
    norm_num [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
  have h3 : frob (W * !![(1 : ℂ), 0; 0, 0]) ^ 2 = ‖W 0 0‖ ^ 2 + ‖W 1 0‖ ^ 2 := by
    rw [frob_sq, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    norm_num [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hE, h2] at h3
  nlinarith [sq_nonneg ‖W 1 0‖]

/-- The logarithmic correction between `frob (A j)` and the corresponding singular value. -/
noncomputable def slog (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hdet : ∀ j, (A j).det = 1)
    (j : ℕ) : ℝ :=
  Real.log (frob (A j)) - Real.log (svdSigma A hdet j)

/-- The logarithmic correction between `frob (A (j+1) · A j)` and
`σ (j+1) σ j λ j`. -/
noncomputable def dlog (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hdet : ∀ j, (A j).det = 1)
    (j : ℕ) : ℝ :=
  Real.log (frob (A (j + 1) * A j))
    - (Real.log (svdSigma A hdet (j + 1)) + Real.log (svdSigma A hdet j)
      + Real.log (svdLam A hdet j))

lemma log_frob_A_eq (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hdet : ∀ j, (A j).det = 1) (j : ℕ) :
    Real.log (frob (A j)) = Real.log (svdSigma A hdet j) + slog A hdet j := by
  unfold slog; ring

lemma log_frob_pair_eq (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hdet : ∀ j, (A j).det = 1) (j : ℕ) :
    Real.log (frob (A (j + 1) * A j))
      = Real.log (svdSigma A hdet (j + 1)) + Real.log (svdSigma A hdet j)
        + Real.log (svdLam A hdet j) + dlog A hdet j := by
  unfold dlog; ring

/-- The telescoping identity for the three sums occurring in the SVD bookkeeping. -/
lemma telescoping_id (f : ℕ → ℝ) (k : ℕ) :
    (∑ j ∈ Finset.Icc 1 k, f j) - (∑ j ∈ Finset.range (k + 1), f (j + 1))
      - (∑ j ∈ Finset.range (k + 1), f j) + (∑ j ∈ Finset.range (k + 2), f j) = 0 := by
  have himg : Finset.Icc 1 k = (Finset.range k).image (· + 1) := by
    ext p
    simp only [Finset.mem_Icc, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨p - 1, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  have h1 := Finset.sum_range_succ' f k
  have h2 := Finset.sum_range_succ' (fun j => f (j + 1)) k
  have h3 := Finset.sum_range_succ (fun j => f (j + 1)) k
  have h4 := Finset.sum_range_succ f (k + 1)
  rw [himg, Finset.sum_image (fun a _ b _ h => Nat.add_right_cancel h)]
  linarith

/-- The single-matrix correction is between `0` and `1/(2(μ²-1)²)`. -/
lemma slog_bounds (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hdet : ∀ j, (A j).det = 1) (j : ℕ)
    (μ : ℝ) (hμ : 3 ≤ μ) (hS : μ ^ 2 - 1 ≤ (svdSigma A hdet j) ^ 2) :
    0 ≤ slog A hdet j ∧ slog A hdet j ≤ 1 / (2 * (μ ^ 2 - 1) ^ 2) := by
  have hσ : 0 < svdSigma A hdet j := lt_of_lt_of_le zero_lt_one (one_le_svdSigma A hdet j)
  have hpos : 0 < μ ^ 2 - 1 := by nlinarith
  have hpos4 : 0 < 1 + ((svdSigma A hdet j) ^ 4)⁻¹ :=
    lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right (by positivity))
  have hkey : slog A hdet j = Real.log (1 + ((svdSigma A hdet j) ^ 4)⁻¹) / 2 := by
    unfold slog
    rw [frob_A_eq A hdet j]
    have h1 : Real.sqrt ((svdSigma A hdet j) ^ 2 + ((svdSigma A hdet j) ^ 2)⁻¹)
        = svdSigma A hdet j * Real.sqrt (1 + ((svdSigma A hdet j) ^ 4)⁻¹) := by
      rw [show (svdSigma A hdet j) ^ 2 + ((svdSigma A hdet j) ^ 2)⁻¹
          = (svdSigma A hdet j) ^ 2 * (1 + ((svdSigma A hdet j) ^ 4)⁻¹) from by
        field_simp,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (le_of_lt hσ)]
    rw [h1, Real.log_mul (ne_of_gt hσ)
      (ne_of_gt (Real.sqrt_pos.mpr hpos4)), Real.log_sqrt (le_of_lt hpos4)]
    ring
  rw [hkey]
  have hlog0 : 0 ≤ Real.log (1 + ((svdSigma A hdet j) ^ 4)⁻¹) :=
    Real.log_nonneg (le_add_of_nonneg_right (by positivity))
  have hlog1 : Real.log (1 + ((svdSigma A hdet j) ^ 4)⁻¹) ≤ ((svdSigma A hdet j) ^ 4)⁻¹ := by
    linarith [Real.log_le_sub_one_of_pos hpos4]
  have h5 : ((svdSigma A hdet j) ^ 4)⁻¹ ≤ 1 / (μ ^ 2 - 1) ^ 2 := by
    have h6 : (μ ^ 2 - 1) ^ 2 ≤ (svdSigma A hdet j) ^ 4 := by
      have h7 := pow_le_pow_left₀ (le_of_lt hpos) hS 2
      rw [show ((svdSigma A hdet j) ^ 2) ^ 2 = (svdSigma A hdet j) ^ 4 from by ring] at h7
      exact h7
    rw [inv_eq_one_div]
    exact (one_div_le_one_div (by positivity) (by positivity)).mpr h6
  constructor
  · linarith
  · have h6 : 1 / (μ ^ 2 - 1) ^ 2 / 2 = ((μ ^ 2 - 1) ^ 2)⁻¹ / 2 := by rw [inv_eq_one_div]
    have h7 : (1 : ℝ) / (2 * (μ ^ 2 - 1) ^ 2) = ((μ ^ 2 - 1) ^ 2)⁻¹ / 2 := by
      field_simp [hpos.ne']
    rw [h7]
    linarith

/-- The elementary numeric corner bound behind `dlog_bounds`. -/
theorem dlog_ratio_bound_aux (s s' l μ : ℝ) (hμ : 3 ≤ μ)
    (hs : μ ^ 2 - 1 ≤ s) (hs' : μ ^ 2 - 1 ≤ s') (hl : 1 / (2 * μ) ≤ l)
    (hs0 : 0 < s) (hs0' : 0 < s') (hl0 : 0 < l) :
    ((1 - l) * (s' * s⁻¹ + s'⁻¹ * s) + l * (s⁻¹ * s'⁻¹)) / (s' * s * l) ≤ 6 / μ ^ 3 := by
  have hμpos : 0 < μ := by linarith
  have hw : 0 < μ ^ 2 - 1 := by nlinarith
  have h2μ : (0 : ℝ) < 2 * μ := by positivity
  set W : ℝ := (μ ^ 2 - 1) ^ 2 with hW
  have hWpos : 0 < W := by rw [hW]; positivity
  have hl_inv : l⁻¹ ≤ 2 * μ := by
    have h1 : 1 ≤ l * (2 * μ) := (div_le_iff₀ h2μ).mp hl
    rw [← one_div, div_le_iff₀ hl0]
    linarith
  have hs_inv : (s⁻¹) ^ 2 ≤ W⁻¹ := by
    have h1 : s⁻¹ ≤ (μ ^ 2 - 1)⁻¹ := by rw [inv_le_inv₀ hs0 hw]; linarith
    have h2 : 0 ≤ s⁻¹ := le_of_lt (inv_pos.mpr hs0)
    have h3 := pow_le_pow_left₀ h2 h1 2
    rw [hW]
    simpa [inv_pow] using h3
  have hs'_inv : (s'⁻¹) ^ 2 ≤ W⁻¹ := by
    have h1 : s'⁻¹ ≤ (μ ^ 2 - 1)⁻¹ := by rw [inv_le_inv₀ hs0' hw]; linarith
    have h2 : 0 ≤ s'⁻¹ := le_of_lt (inv_pos.mpr hs0')
    have h3 := pow_le_pow_left₀ h2 h1 2
    rw [hW]
    simpa [inv_pow] using h3
  have hkey : ((1 - l) * (s' * s⁻¹ + s'⁻¹ * s) + l * (s⁻¹ * s'⁻¹)) / (s' * s * l)
      = (l⁻¹ - 1) * ((s⁻¹) ^ 2 + (s'⁻¹) ^ 2) + (s⁻¹) ^ 2 * (s'⁻¹) ^ 2 := by
    field_simp
  rw [hkey]
  have hstep1 : (l⁻¹ - 1) * ((s⁻¹) ^ 2 + (s'⁻¹) ^ 2) ≤ 2 * μ * (2 * W⁻¹) := by
    have h1 : l⁻¹ - 1 ≤ 2 * μ := by linarith
    have h3 : 0 ≤ (s⁻¹) ^ 2 + (s'⁻¹) ^ 2 := by positivity
    calc (l⁻¹ - 1) * ((s⁻¹) ^ 2 + (s'⁻¹) ^ 2)
        ≤ (2 * μ) * ((s⁻¹) ^ 2 + (s'⁻¹) ^ 2) := mul_le_mul_of_nonneg_right h1 h3
      _ ≤ (2 * μ) * (2 * W⁻¹) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [hs_inv, hs'_inv]
  have hstep2 : (s⁻¹) ^ 2 * (s'⁻¹) ^ 2 ≤ W⁻¹ * W⁻¹ :=
    mul_le_mul hs_inv hs'_inv (by positivity) (by positivity)
  have hnum : 2 * μ * (2 * W⁻¹) + W⁻¹ * W⁻¹ ≤ 6 / μ ^ 3 := by
    have h81 : 64 * μ ^ 4 ≤ 81 * W := by
      rw [hW]
      have h1 : 8 * μ ^ 2 ≤ 9 * (μ ^ 2 - 1) := by nlinarith
      have h2 : 0 ≤ 8 * μ ^ 2 := by positivity
      have h3 := mul_self_le_mul_self h2 h1
      nlinarith [h3]
    have hA : 64 * μ ^ 4 * W ≤ 81 * W ^ 2 := by
      have h := mul_le_mul_of_nonneg_right h81 hWpos.le
      nlinarith [h]
    have hB : 16 * μ ^ 3 ≤ 15 * W ^ 2 := by
      have h1 : 8 * μ ^ 2 ≤ 9 * (μ ^ 2 - 1) := by nlinarith
      have h2 : 0 ≤ 8 * μ ^ 2 := by positivity
      have h3 : (8 * μ ^ 2) ^ 4 ≤ (9 * (μ ^ 2 - 1)) ^ 4 := pow_le_pow_left₀ h2 h1 4
      have hμ5 : 243 ≤ μ ^ 5 := by nlinarith
      nlinarith [h3, hμ5, hμpos, hW, hWpos]
    have key : (4 * μ * W + 1) * μ ^ 3 ≤ 6 * W ^ 2 := by nlinarith [hA, hB]
    have hM : 2 * μ * (2 * W⁻¹) + W⁻¹ * W⁻¹ = (4 * μ * W + 1) / (W * W) := by
      field_simp
      ring
    rw [hM, le_div_iff₀ (by positivity : (0 : ℝ) < μ ^ 3)]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < W * W)]
    nlinarith [key]
  linarith [hstep1, hstep2, hnum]

/-- The pair correction is between `0` and `3/μ³`. -/
lemma dlog_bounds (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hdet : ∀ j, (A j).det = 1) (j : ℕ)
    (μ : ℝ) (hμ : 3 ≤ μ) (hlam : 1 / (2 * μ) ≤ (svdLam A hdet j) ^ 2)
    (hS : μ ^ 2 - 1 ≤ (svdSigma A hdet j) ^ 2)
    (hS' : μ ^ 2 - 1 ≤ (svdSigma A hdet (j + 1)) ^ 2) :
    0 ≤ dlog A hdet j ∧ dlog A hdet j ≤ 3 / μ ^ 3 := by
  have hμpos : 0 < μ := by linarith
  have ha0 : 0 < svdSigma A hdet (j + 1) :=
    lt_of_lt_of_le zero_lt_one (one_le_svdSigma A hdet (j + 1))
  have hb0 : 0 < svdSigma A hdet j :=
    lt_of_lt_of_le zero_lt_one (one_le_svdSigma A hdet j)
  have hl2pos : 0 < (svdLam A hdet j) ^ 2 :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / (2 * μ)) hlam
  have hl0 : 0 < svdLam A hdet j := by
    have hnn : 0 ≤ svdLam A hdet j := norm_nonneg _
    nlinarith [sq_nonneg (svdLam A hdet j)]
  have hWu := svdW_unitary A hdet j
  have hl1 : (svdLam A hdet j) ^ 2 ≤ 1 := by
    have h := norm_entry_le_one (svdW A hdet j) hWu.1
    have h2 : ‖svdW A hdet j 0 0‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg (svdW A hdet j 0 0)]
    simpa only [svdLam] using h2
  set D : ℝ := (svdSigma A hdet (j + 1)) ^ 2 * (svdSigma A hdet j) ^ 2
    * (svdLam A hdet j) ^ 2 with hD
  set E : ℝ := (1 - (svdLam A hdet j) ^ 2)
        * ((svdSigma A hdet (j + 1)) ^ 2 * ((svdSigma A hdet j) ^ 2)⁻¹
           + ((svdSigma A hdet (j + 1)) ^ 2)⁻¹ * (svdSigma A hdet j) ^ 2)
      + (svdLam A hdet j) ^ 2
        * (((svdSigma A hdet j) ^ 2)⁻¹ * ((svdSigma A hdet (j + 1)) ^ 2)⁻¹) with hEdef
  have hDpos : 0 < D := by
    rw [hD]; exact mul_pos (mul_pos (pow_pos ha0 2) (pow_pos hb0 2)) (pow_pos hl0 2)
  have hE0 : 0 ≤ E := by
    rw [hEdef]
    have h1 : 0 ≤ 1 - (svdLam A hdet j) ^ 2 := by linarith
    have h2 : 0 ≤ (svdSigma A hdet (j + 1)) ^ 2 * ((svdSigma A hdet j) ^ 2)⁻¹
        + ((svdSigma A hdet (j + 1)) ^ 2)⁻¹ * (svdSigma A hdet j) ^ 2 := by positivity
    have h3 : 0 ≤ (svdLam A hdet j) ^ 2
        * (((svdSigma A hdet j) ^ 2)⁻¹ * ((svdSigma A hdet (j + 1)) ^ 2)⁻¹) := by positivity
    exact add_nonneg (mul_nonneg h1 h2) h3
  have hFSde : frob (A (j + 1) * A j) ^ 2 = D + E := by
    rw [frob_pair_eq A hdet j,
      frob_Dm_mul_Dm (svdSigma A hdet j) (svdSigma A hdet (j + 1)) (svdW A hdet j) hWu.1 hWu.2,
      hD, hEdef]
    simp only [svdLam]
    ring
  have hFSp : 0 < frob (A (j + 1) * A j) := frob_prod_pos A hdet j
  have hsiglam : 0 < svdSigma A hdet (j + 1) * svdSigma A hdet j * svdLam A hdet j := by positivity
  have hlog0 : dlog A hdet j
      = (1 / 2) * Real.log (frob (A (j + 1) * A j) ^ 2 / D) := by
    have hsum : Real.log (svdSigma A hdet (j + 1)) + Real.log (svdSigma A hdet j)
          + Real.log (svdLam A hdet j)
        = Real.log (svdSigma A hdet (j + 1) * svdSigma A hdet j * svdLam A hdet j) := by
      rw [Real.log_mul (mul_ne_zero ha0.ne' hb0.ne') hl0.ne', Real.log_mul ha0.ne' hb0.ne']
    have harg : frob (A (j + 1) * A j) ^ 2 / D
        = (frob (A (j + 1) * A j)
            / (svdSigma A hdet (j + 1) * svdSigma A hdet j * svdLam A hdet j)) ^ 2 := by
      rw [hD, div_pow, mul_pow, mul_pow]
    unfold dlog
    rw [hsum, ← Real.log_div hFSp.ne' hsiglam.ne', harg, Real.log_pow]
    push_cast
    ring
  have hlog : dlog A hdet j = (1 / 2) * Real.log (1 + E / D) := by
    have h3 : (D + E) / D = 1 + E / D := by rw [add_div, div_self hDpos.ne']
    rw [hlog0, hFSde, h3]
  have hEbound : E / D ≤ 6 / μ ^ 3 := by
    have h := dlog_ratio_bound_aux ((svdSigma A hdet j) ^ 2) ((svdSigma A hdet (j + 1)) ^ 2)
      ((svdLam A hdet j) ^ 2) μ hμ hS hS' hlam (pow_pos hb0 2) (pow_pos ha0 2) hl2pos
    rw [hEdef, hD]
    exact h
  have hEDnn : 0 ≤ E / D := div_nonneg hE0 hDpos.le
  constructor
  · rw [hlog]
    have h1 : 1 ≤ 1 + E / D := by linarith
    have h2 := Real.log_nonneg h1
    linarith
  · rw [hlog]
    have h2 : 0 < 1 + E / D := by linarith
    have hlogle : Real.log (1 + E / D) ≤ E / D := by
      have h3 := Real.log_le_sub_one_of_pos h2
      linarith
    have hhalf : (1 / 2) * (E / D) ≤ 3 / μ ^ 3 := by
      have h4 := mul_le_mul_of_nonneg_left hEbound (by norm_num : (0 : ℝ) ≤ 1 / 2)
      have h5 : (1 / 2 : ℝ) * (6 / μ ^ 3) = 3 / μ ^ 3 := by ring
      linarith
    linarith

/-- Elementary numeric bound used in the bookkeeping. -/
lemma le_two_sq (μ : ℝ) (hμ : 2 ≤ μ) : μ ≤ 2 * (μ ^ 2 - 1) ^ 2 := by
  have h1 : μ ≤ μ ^ 2 - 1 := by nlinarith [hμ, sq_nonneg (μ - 2)]
  have h2 : 1 ≤ μ ^ 2 - 1 := by linarith
  have h3 : μ ≤ (μ ^ 2 - 1) ^ 2 := by
    calc μ ≤ μ ^ 2 - 1 := h1
      _ = (μ ^ 2 - 1) * 1 := by ring
      _ ≤ (μ ^ 2 - 1) * (μ ^ 2 - 1) := mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = (μ ^ 2 - 1) ^ 2 := by ring
  linarith

/-- The pair hypothesis gives `λ j² ≥ 1/(2μ)`. -/
lemma half_mu_le_lam (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hdet : ∀ j, (A j).det = 1)
    (n : ℕ) (μ : ℝ) (hμ2 : 2 ≤ μ) (hμ3 : 3 ≤ μ) (hnorm : ∀ j, μ ≤ frob (A j))
    (hpair : ∀ j : ℕ, j + 1 < n → Real.log (frob (A (j + 1))) + Real.log (frob (A j))
        - Real.log (frob (A (j + 1) * A j)) < Real.log μ / 2)
    (j : ℕ) (hj : j + 1 < n) :
    1 / (2 * μ) ≤ (svdLam A hdet j) ^ 2 := by
  have h := lam_sq_ge A hdet n μ hμ2 hnorm hpair j hj
  have hμpos : 0 < μ := by linarith
  have h2 : 0 < μ ^ 2 - 1 := by nlinarith
  have hbase : 1 / (2 * μ) ≤ 1 / μ - 2 / (μ ^ 2 - 1) ^ 2 := by
    have h9 : 9 * μ ^ 2 ≤ μ ^ 4 := by
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg μ) (by linarith : (0:ℝ) ≤ μ - 3))
        (by linarith : (0:ℝ) ≤ μ + 3)]
    have h4 : 4 * μ ≤ (μ ^ 2 - 1) ^ 2 := by nlinarith [h9, hμ3, sq_nonneg μ]
    have hμne : μ ≠ 0 := ne_of_gt hμpos
    have h2ne : (μ ^ 2 - 1) ^ 2 ≠ 0 := by positivity
    field_simp
    nlinarith [h4]
  linarith

/-- **Avalanche principle** (Bourgain--Jitomirskaya, Lemma 5; Goldstein--Schlag Prop. 2.2).
For a chain of determinant-one `2×2` matrices all of Frobenius norm `≥ μ > n` whose
consecutive pair defects are `< (log μ)/2`, the defect of the full product equals the sum of
the pair defects, up to `O(n/μ)`. -/
theorem avalanche_principle (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) (μ : ℝ) (hn : 2 ≤ n) (hμ : (n : ℝ) < μ) (hμ1 : 1 ≤ μ) (hdet : ∀ j, (A j).det = 1) (hnorm : ∀ j, μ ≤ frob (A j)) (hpair : ∀ j : ℕ, j + 1 < n → Real.log (frob (A (j + 1))) + Real.log (frob (A j)) - Real.log (frob (A (j + 1) * A j)) < Real.log μ / 2) : |Real.log (frob (matProd A n)) + (∑ j ∈ Finset.Icc 1 (n - 2), Real.log (frob (A j))) - (∑ j ∈ Finset.range (n - 1), Real.log (frob (A (j + 1) * A j)))| ≤ 1000 * (n : ℝ) / μ := by
  by_cases hn2 : n = 2
  · subst hn2
    have hP : matProd A 2 = A 1 * A 0 := by rw [matProd_succ, matProd_succ, matProd_zero, mul_one]
    have hI : Finset.Icc 1 (2 - 2) = (∅ : Finset ℕ) := by decide
    have hR : Finset.range (2 - 1) = ({0} : Finset ℕ) := by decide
    rw [hP, hI, hR, Finset.sum_empty, Finset.sum_singleton]
    simp only [Nat.zero_add, add_zero]
    rw [sub_self, abs_zero]
    have : (0 : ℝ) ≤ 1000 * (2 : ℝ) / μ := by positivity
    linarith
  · have hn3 : 3 ≤ n := by omega
    have hμ2 : 2 ≤ μ := by
      have h2n : (2 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 2 < n)
      linarith
    have hμ3 : 3 < μ := by
      have h3n : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
      linarith
    have hμpos : 0 < μ := by linarith
    -- the core estimate
    have hcore := avalanche_core (svdSigma A hdet) (svdW A hdet) n μ hn hμ hμ3
      (fun j _ => one_le_svdSigma A hdet j)
      (fun j _ => ⟨sq_svdSigma_ge A hdet μ hμ1 hnorm j,
        sq_svdSigma_ge A hdet μ hμ1 hnorm (j + 1)⟩)
      (fun j _ => svdW_unitary A hdet j)
      (fun j hj => by
        have h := lam_sq_ge A hdet n μ hμ2 hnorm hpair j hj
        simpa only [svdLam] using h)
    -- the SVD rewriting of the three blocks
    have hfP : Real.log (frob (matProd A n))
        = Real.log (frob (Nmat (svdSigma A hdet) (svdW A hdet) (n - 1))) := by
      have hP := matProd_eq_svd A hdet (n - 1)
      rw [show n - 1 + 1 = n from by omega] at hP
      rw [hP, frob_sandwich _ _ _ (svdData A hdet (n - 1)).hU1 (svdData A hdet 0).hV1]
    have hIcc : (∑ j ∈ Finset.Icc 1 (n - 2), Real.log (frob (A j)))
        = (∑ j ∈ Finset.Icc 1 (n - 2), Real.log (svdSigma A hdet j))
          + (∑ j ∈ Finset.Icc 1 (n - 2), slog A hdet j) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => log_frob_A_eq A hdet j)
    have hRng : (∑ j ∈ Finset.range (n - 1), Real.log (frob (A (j + 1) * A j)))
        = (∑ j ∈ Finset.range (n - 1), (Real.log (svdSigma A hdet (j + 1))
            + Real.log (svdSigma A hdet j) + Real.log (svdLam A hdet j)))
          + (∑ j ∈ Finset.range (n - 1), dlog A hdet j) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => log_frob_pair_eq A hdet j)
    -- the telescoping
    have hsplit : Real.log (frob (matProd A n))
          + (∑ j ∈ Finset.Icc 1 (n - 2), Real.log (frob (A j)))
          - (∑ j ∈ Finset.range (n - 1), Real.log (frob (A (j + 1) * A j)))
        = (Real.log (frob (Nmat (svdSigma A hdet) (svdW A hdet) (n - 1)))
            - (∑ j ∈ Finset.range n, Real.log (svdSigma A hdet j))
            - (∑ j ∈ Finset.range (n - 1), Real.log (svdLam A hdet j)))
          + (∑ j ∈ Finset.Icc 1 (n - 2), slog A hdet j)
          - (∑ j ∈ Finset.range (n - 1), dlog A hdet j) := by
      rw [hfP, hIcc, hRng, Finset.sum_add_distrib, Finset.sum_add_distrib]
      have hid := telescoping_id (fun j => Real.log (svdSigma A hdet j)) (n - 2)
      rw [show n - 2 + 1 = n - 1 from by omega,
        show n - 2 + 2 = n from by omega] at hid
      linarith
    -- the two corrections
    have hslog0 : 0 ≤ (∑ j ∈ Finset.Icc 1 (n - 2), slog A hdet j) :=
      Finset.sum_nonneg (fun j _ =>
        (slog_bounds A hdet j μ (by linarith) (sq_svdSigma_ge A hdet μ hμ1 hnorm j)).1)
    have hslog1 : (∑ j ∈ Finset.Icc 1 (n - 2), slog A hdet j)
        ≤ (n : ℝ) * (1 / μ) := by
      have h1 : (∑ j ∈ Finset.Icc 1 (n - 2), slog A hdet j)
          ≤ (∑ _j ∈ Finset.Icc 1 (n - 2), (1 / μ)) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        refine le_trans (slog_bounds A hdet j μ (by linarith)
          (sq_svdSigma_ge A hdet μ hμ1 hnorm j)).2 ?_
        have hpos2 : (0 : ℝ) < 2 * (μ ^ 2 - 1) ^ 2 := by
          have h1 : 1 < μ ^ 2 := by nlinarith
          positivity
        rw [div_le_div_iff₀ hpos2 hμpos]
        nlinarith [le_two_sq μ (by linarith)]
      calc (∑ j ∈ Finset.Icc 1 (n - 2), slog A hdet j) ≤ (∑ _j ∈ Finset.Icc 1 (n - 2), (1 / μ)) := h1
        _ = ((Finset.Icc 1 (n - 2)).card : ℝ) * (1 / μ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (n : ℝ) * (1 / μ) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have : (Finset.Icc 1 (n - 2)).card ≤ n := by
              rw [Nat.card_Icc]; omega
            exact_mod_cast this
    have hdlog0 : 0 ≤ (∑ j ∈ Finset.range (n - 1), dlog A hdet j) :=
      Finset.sum_nonneg (fun j hj =>
        (dlog_bounds A hdet j μ (by linarith)
          (half_mu_le_lam A hdet n μ hμ2 (by linarith) hnorm hpair j (by
            have hlt := Finset.mem_range.mp hj
            omega))
          (sq_svdSigma_ge A hdet μ hμ1 hnorm j)
          (sq_svdSigma_ge A hdet μ hμ1 hnorm (j + 1))).1)
    have hdlog1 : (∑ j ∈ Finset.range (n - 1), dlog A hdet j) ≤ (n : ℝ) * (1 / μ) := by
      have h1 : (∑ j ∈ Finset.range (n - 1), dlog A hdet j)
          ≤ (∑ _j ∈ Finset.range (n - 1), (1 / μ)) := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        have hj' : j + 1 < n := by
          have hlt := Finset.mem_range.mp hj
          omega
        have hlam2 : 1 / (2 * μ) ≤ (svdLam A hdet j) ^ 2 :=
          half_mu_le_lam A hdet n μ hμ2 (by linarith) hnorm hpair j hj'
        refine le_trans (dlog_bounds A hdet j μ (by linarith) hlam2
          (sq_svdSigma_ge A hdet μ hμ1 hnorm j)
          (sq_svdSigma_ge A hdet μ hμ1 hnorm (j + 1))).2 ?_
        rw [div_le_div_iff₀ (by positivity) hμpos]
        nlinarith [hμ3, sq_nonneg μ]
      calc (∑ j ∈ Finset.range (n - 1), dlog A hdet j) ≤ (∑ _j ∈ Finset.range (n - 1), (1 / μ)) := h1
        _ = ((Finset.range (n - 1)).card : ℝ) * (1 / μ) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (n : ℝ) * (1 / μ) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have : (Finset.range (n - 1)).card ≤ n := by
              rw [Finset.card_range]; omega
            exact_mod_cast this
    -- conclusion
    set Lcore := Real.log (frob (Nmat (svdSigma A hdet) (svdW A hdet) (n - 1)))
      - (∑ j ∈ Finset.range n, Real.log (svdSigma A hdet j))
      - (∑ j ∈ Finset.range (n - 1), Real.log (svdLam A hdet j)) with hLcore
    rw [hsplit]
    have htri : |Lcore + (∑ j ∈ Finset.Icc 1 (n - 2), slog A hdet j)
        - (∑ j ∈ Finset.range (n - 1), dlog A hdet j)|
        ≤ (450 * (n : ℝ) / μ) + (n : ℝ) * (1 / μ) + (n : ℝ) * (1 / μ) := by
      rw [abs_sub_le_iff]
      have h3 : |Lcore| ≤ 450 * (n : ℝ) / μ := hcore
      have h4 : Lcore ≤ 450 * (n : ℝ) / μ := le_trans (le_abs_self Lcore) h3
      have h5 : -Lcore ≤ 450 * (n : ℝ) / μ := by
        have := neg_le_abs Lcore
        linarith
      constructor <;> linarith
    calc |Lcore + (∑ j ∈ Finset.Icc 1 (n - 2), slog A hdet j)
          - (∑ j ∈ Finset.range (n - 1), dlog A hdet j)|
        ≤ (450 * (n : ℝ) / μ) + (n : ℝ) * (1 / μ) + (n : ℝ) * (1 / μ) := htri
      _ ≤ 1000 * (n : ℝ) / μ := by
          have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          have hμne : μ ≠ 0 := ne_of_gt hμpos
          have heq : (450 * (n : ℝ) / μ) + (n : ℝ) * (1 / μ) + (n : ℝ) * (1 / μ)
              = 452 * (n : ℝ) / μ := by
            field_simp
            ring
          rw [heq, div_le_div_iff₀ hμpos hμpos]
          nlinarith [hn0]
end Work.TMC7Core.Avalanche

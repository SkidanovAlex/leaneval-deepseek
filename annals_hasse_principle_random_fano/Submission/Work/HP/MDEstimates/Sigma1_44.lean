import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDCommon
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.six_le_NN
import Submission.Work.HP.MDEstimates.pairS0_asymptotic
import Submission.Work.HP.MDEstimates.mu_sum_bound

/-!
# `Sigma1_44` — the `(4,4)` case of the `Σ^{(1)}` estimate

Browning--Le Boudec--Sawin, *The Hasse principle for random Fano hypersurfaces* (Annals 2023),
Lemma D44: the "small-`μ`" half `Σ^{(1)}` of the second moment of `N_V(B)` for the quartic
threefold case `(d,n) = (4,4)`.

The proof of the general estimate `Sigma1_estimate` (in `Submission/Work/HP/MDEstimates/
Sigma1_estimate.lean`) never uses its hypothesis `(d,n) ≠ (4,4)`: the two analytic inputs,
`pairS0_asymptotic` and `mu_sum_bound`, are both available at `(4,4)`.  This file therefore
repeats that assembly without the `(4,4)` exclusion (as a `private` auxiliary, so that it can
coexist with the sibling file), and specialises.

The two analytic inputs are imported:

* `pairS0_asymptotic` : the per-pair primitive lattice count `pairS0 d n A p` for `p ∈ Ω(B)`,
  `μ ≤ A`, is `8 ι A^{N-2}/det Γ_p` up to a relative error `O(μ/A)` (Le Boudec's Lemma 3);
* `mu_sum_bound` : `Σ_{Ω(B)} μ(x,y)/det Γ_{x,y} ≤ K A^{3/4} E_{d,n}(B)`.

The remaining bookkeeping splits `Σ^{(1)}` into its main part and an error, bounds the two
pieces by `K₂·mainTerm/A^{1/4}` and `(K₁K₂/(8ι))·mainTerm/A^{1/4}`, and concludes.
-/

open MvPolynomial Finset MeasureTheory
open scoped BigOperators

namespace Work.HP.MDEstimates
open Work.HP

/-! ## Elementary positivity -/

/-- The volume of the unit ball in `ℝ^R` is positive for `R ≥ 1`. -/
private lemma ballVol_pos (R : ℕ) (hR : 1 ≤ R) : 0 < ballVol R := by
  haveI : Nonempty (Fin R) := ⟨⟨0, by omega⟩⟩
  have hg : 0 < Real.sqrt Real.pi ^ R / Real.Gamma ((R : ℝ) / 2 + 1) := by
    have h1 : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have h2 : 0 < Real.Gamma ((R : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
    positivity
  have h := EuclideanSpace.volume_closedBall (Fin R) (0 : EuclideanSpace ℝ (Fin R)) 1
  simp only [Fintype.card_fin] at h
  have h2 : ballVol R = Real.sqrt Real.pi ^ R / Real.Gamma ((R : ℝ) / 2 + 1) := by
    unfold ballVol
    rw [h, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1), one_pow,
      ENNReal.toReal_ofReal (le_of_lt hg)]
    ring
  rw [h2]; exact hg

/-- The tail of the `ζ`-series is positive. -/
private lemma zeta_tail_pos (m : ℕ) (hm : 1 < m) : 0 < ∑' k : ℕ, (1:ℝ) / ((k : ℝ) + 1) ^ m := by
  have hsum : Summable (fun k : ℕ => (1:ℝ) / ((k : ℝ) + 1) ^ m) := by
    have hf : Summable (fun j : ℕ => (1:ℝ) / (j : ℝ) ^ m) := Real.summable_one_div_nat_pow.mpr hm
    have := (summable_nat_add_iff (f := fun j : ℕ => (1:ℝ) / (j : ℝ) ^ m) 1).mpr hf
    simpa [Nat.cast_add, Nat.cast_one] using this
  exact Summable.tsum_pos hsum (fun i => by positivity) 0 (by norm_num)

/-- `ι_{d,n} = V_{N-2}/(8 ζ(N-2)) > 0` for `2 ≤ d ≤ n`. -/
private lemma iotaDN_pos (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) : 0 < iotaDN d n := by
  have h6 := Work.HP.six_le_NN d n hd hdn
  have hN : 1 ≤ NN d n - 2 := by omega
  have hm : 1 < NN d n - 2 := by omega
  unfold iotaDN
  have := ballVol_pos (NN d n - 2) hN
  have := zeta_tail_pos (NN d n - 2) hm
  positivity

private lemma dmin_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ) (S : Set (ι → ℤ)) :
    0 ≤ dmin r S := by
  rw [dmin]
  refine Real.sInf_nonneg ?_
  rintro D ⟨L, -, -, rfl⟩
  exact detL_nonneg L

/-- The threshold `μ(x,y)` of the paper is nonnegative. -/
private lemma muXY_nonneg (n : ℕ) (x y : Fin (n + 1) → ℤ) : 0 ≤ muXY n x y := by
  rw [muXY]
  have h2 : 0 ≤ max (dmin 2 {x, y} / dmin 3 {x, y}) (eNorm x * eNorm y / dmin 2 {x, y} ^ 2) := by
    rw [le_max_iff]; left
    exact div_nonneg (dmin_nonneg 2 _) (dmin_nonneg 3 _)
  positivity

/-! ## The summands `1/det Γ` and `μ/det Γ` -/

/-- The summand `1/det(Γ_{x,y})` of `E_{d,n}(B)`. -/
private noncomputable def invDetGam (d n : ℕ) (p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) : ℝ :=
  1 / detL (Gam d n p.1 p.2)

/-- The summand `μ(x,y)/det(Γ_{x,y})`. -/
private noncomputable def muGam (d n : ℕ) (p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) : ℝ :=
  muXY n p.1 p.2 / detL (Gam d n p.1 p.2)

private lemma invDetGam_nonneg (d n : ℕ) (p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) :
    0 ≤ invDetGam d n p := div_nonneg zero_le_one (detL_nonneg _)

private lemma muGam_nonneg (d n : ℕ) (p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) :
    0 ≤ muGam d n p := div_nonneg (muXY_nonneg n p.1 p.2) (detL_nonneg _)

/-- The arithmetic identity at the heart of the final comparison:
`A^{1/4}` times the coefficient produced by the error term equals
`(K₁K₂/(8ι))·(2ι A^k E)`, using `A^{1/4}A^{3/4} = A` and `(1/A)A = 1`. -/
private lemma arith_quarter (A i K₁ K₂ EE : ℝ) (k : ℕ) (hA : A ≠ 0)
    (h1 : A^((1:ℝ)/4) * A^((3:ℝ)/4) = A) (hi : i ≠ 0) :
    ((1/4) * (K₁ * A^k * (1/A) * (K₂ * A^((3:ℝ)/4) * EE))) * A^((1:ℝ)/4)
      = (K₁*K₂/(8*i)) * (2*i*A^k*EE) := by
  have h2 : A^((3:ℝ)/4) * A^((1:ℝ)/4) = A := by rw [mul_comm, h1]
  have h3 : (1/A) * A = 1 := by field_simp
  have h4 : K₁*K₂/(8*i) * (2*i) = K₁*K₂/4 := by field_simp; ring
  have e1 : (1/4) * (K₁ * A^k * (1/A) * (K₂ * A^((3:ℝ)/4) * EE)) * A^((1:ℝ)/4)
      = K₁*K₂*EE*A^k*((1/A)*(A^((3:ℝ)/4)*A^((1:ℝ)/4)))*(1/4) := by ring
  have e2 : K₁*K₂*EE*A^k*((1/A)*(A^((3:ℝ)/4)*A^((1:ℝ)/4)))*(1/4)
      = K₁*K₂*EE*A^k*(1/4) := by rw [h2, h3]; ring
  have e3 : (K₁*K₂/(8*i)) * (2*i*A^k*EE) = K₁*K₂*EE*A^k*(1/4) := by
    calc (K₁*K₂/(8*i)) * (2*i*A^k*EE)
        = (K₁*K₂/(8*i)*(2*i))*A^k*EE := by ring
      _ = (K₁*K₂/4)*A^k*EE := by rw [h4]
      _ = K₁*K₂*EE*A^k*(1/4) := by ring
  rw [e1, e3, e2]

set_option maxHeartbeats 4000000 in
private theorem Sigma1_44_gen (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (h22 : (d, n) ≠ (2, 2))
    (h33 : (d, n) ≠ (3, 3)) :
    ∃ K B₀ : ℝ, ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      |Sigma1 d n A B - mainTerm d n A B| ≤ K * mainTerm d n A B / A ^ ((1 : ℝ) / 4) := by
  obtain ⟨K₁, B₁, hK₁, hB₁, hL1⟩ := pairS0_asymptotic d n hd hdn h22
  obtain ⟨K₂, B₂, hK₂, hL2⟩ := mu_sum_bound d n hd hdn h22 h33
  have hι : 0 < iotaDN d n := iotaDN_pos d n hd hdn
  refine ⟨K₂ + K₁ * K₂ / (8 * iotaDN d n), max 4 (max B₁ B₂), ?_⟩
  intro A B hB hA1 hA2
  have hB4 : (4 : ℝ) ≤ B := le_trans (le_max_left _ _) hB
  have hB1 : B₁ ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hB
  have hB2 : B₂ ≤ B := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hB
  have hBpos : 0 < B := by linarith
  have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
  have hApos : 0 < A := lt_of_lt_of_le (div_pos hBpos hlogB) hA1
  have hA0 : 0 ≤ A := le_of_lt hApos
  have hAne : A ≠ 0 := ne_of_gt hApos
  have hqpos : 0 < A ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hApos _
  have hquarter : A ^ ((1 : ℝ) / 4) * A ^ ((3 : ℝ) / 4) = A := by
    rw [← Real.rpow_add hApos]; norm_num
  have hinvA : (1 / A) * A = 1 := by field_simp
  obtain ⟨-, -, hΩfin⟩ := Work.HP.MDBasic.finite_sets d n A B (fun _ => True)
  set F : Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) := hΩfin.toFinset with hFdef
  have hFcoe : (F : Set _) = Omega d n B := by rw [hFdef]; exact hΩfin.coe_toFinset
  set Gs := ∑ p ∈ F.filter (fun p => muXY n p.1 p.2 ≤ A), invDetGam d n p with hGs
  set Gt := ∑ p ∈ F.filter (fun p => ¬ (muXY n p.1 p.2 ≤ A)), invDetGam d n p with hGt
  set Ms := ∑ p ∈ F.filter (fun p => muXY n p.1 p.2 ≤ A), muGam d n p with hMs
  set Mt := ∑ p ∈ F.filter (fun p => ¬ (muXY n p.1 p.2 ≤ A)), muGam d n p with hMt
  set Mtot := ∑ p ∈ F, muGam d n p with hMtot
  set Err := ∑ p ∈ F.filter (fun p => muXY n p.1 p.2 ≤ A),
      (pairS0 d n A p - 8 * iotaDN d n * A ^ (NN d n - 2) * invDetGam d n p) with hErr
  have hEE : EE d n B = ∑ p ∈ F, invDetGam d n p := by
    have h0 : Omega d n B = (↑F : Set _) := hFcoe.symm
    rw [show EE d n B = ∑ᶠ p ∈ Omega d n B, invDetGam d n p from rfl,
        finsum_mem_congr h0 (fun p _ => rfl), finsum_mem_coe_finset]
  have hmt : mainTerm d n A B = 2 * iotaDN d n * A ^ (NN d n - 2) * (∑ p ∈ F, invDetGam d n p) := by
    rw [show mainTerm d n A B
          = 2 * iotaDN d n * A ^ (NN d n - 2) * (∑ᶠ p ∈ Omega d n B, invDetGam d n p) from rfl,
        finsum_mem_congr hFcoe.symm (fun p _ => rfl), finsum_mem_coe_finset]
  have hsplit : (∑ p ∈ F, invDetGam d n p)
      = (∑ p ∈ F.filter (fun p => muXY n p.1 p.2 ≤ A), invDetGam d n p)
        + (∑ p ∈ F.filter (fun p => ¬ (muXY n p.1 p.2 ≤ A)), invDetGam d n p) := by
    rw [← Finset.sum_filter_add_sum_filter_not F (fun p => muXY n p.1 p.2 ≤ A)
      (fun p => invDetGam d n p)]
  have hS1 : Sigma1 d n A B
      = (1/4) * (∑ p ∈ F.filter (fun p => muXY n p.1 p.2 ≤ A), pairS0 d n A p) := by
    have hset : {p ∈ Omega d n B | muXY n p.1 p.2 ≤ A}
        = ↑(F.filter (fun p => muXY n p.1 p.2 ≤ A)) := by
      rw [hFdef]
      ext p
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, hΩfin.mem_toFinset]
    rw [show Sigma1 d n A B
          = (1/4) * ∑ᶠ p ∈ {p ∈ Omega d n B | muXY n p.1 p.2 ≤ A}, pairS0 d n A p from rfl,
        finsum_mem_congr hset (fun p _ => rfl), finsum_mem_coe_finset]
  -- per-element bound (Le Boudec's Lemma 3, dominated form)
  have hpe : ∀ p ∈ F.filter (fun p => muXY n p.1 p.2 ≤ A),
      |pairS0 d n A p - 8 * iotaDN d n * A ^ (NN d n - 2) * invDetGam d n p|
        ≤ K₁ * (A ^ (NN d n - 2) * invDetGam d n p) * (muXY n p.1 p.2 / A) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hpΩ : p ∈ Omega d n B := by rw [← hFcoe]; exact hp.1
    have h := hL1 A B hB1 hA1 hA2 p hpΩ hp.2
    have h1 : 8 * iotaDN d n * A ^ (NN d n - 2) / detL (Gam d n p.1 p.2)
        = 8 * iotaDN d n * A ^ (NN d n - 2) * invDetGam d n p := by
      rw [invDetGam, div_eq_mul_one_div]
    have h2 : K₁ * (A ^ (NN d n - 2) / detL (Gam d n p.1 p.2)) * (muXY n p.1 p.2 / A)
        = K₁ * (A ^ (NN d n - 2) * invDetGam d n p) * (muXY n p.1 p.2 / A) := by
      rw [invDetGam, div_eq_mul_one_div]
    rwa [h1, h2] at h
  -- the summed error term
  have hErr_bound : |Err| ≤ K₁ * A ^ (NN d n - 2) * (1 / A) * Ms := by
    rw [hErr, hMs]
    calc |∑ p ∈ F.filter (fun p => muXY n p.1 p.2 ≤ A),
            (pairS0 d n A p - 8 * iotaDN d n * A ^ (NN d n - 2) * invDetGam d n p)|
        ≤ ∑ p ∈ F.filter (fun p => muXY n p.1 p.2 ≤ A),
            |pairS0 d n A p - 8 * iotaDN d n * A ^ (NN d n - 2) * invDetGam d n p| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ F.filter (fun p => muXY n p.1 p.2 ≤ A),
            K₁ * (A ^ (NN d n - 2) * invDetGam d n p) * (muXY n p.1 p.2 / A) :=
          Finset.sum_le_sum hpe
      _ = K₁ * A ^ (NN d n - 2) * (1 / A)
            * (∑ p ∈ F.filter (fun p => muXY n p.1 p.2 ≤ A), muGam d n p) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          rw [muGam, invDetGam, div_eq_mul_one_div]
          ring
  -- the `μ`-sum bound of the paper, in finite-set form
  have hL2' : Mtot ≤ K₂ * A ^ ((3:ℝ)/4) * EE d n B := by
    have h := hL2 A B hB2 hA1 hA2
    have h0 : Omega d n B = (↑F : Set _) := hFcoe.symm
    rw [show (∑ᶠ p ∈ Omega d n B, muXY n p.1 p.2 / detL (Gam d n p.1 p.2))
          = ∑ᶠ p ∈ Omega d n B, muGam d n p from rfl,
        finsum_mem_congr h0 (fun p _ => rfl), finsum_mem_coe_finset] at h
    rw [hMtot]; exact h
  have hMs_le : Ms ≤ K₂ * A ^ ((3:ℝ)/4) * EE d n B := by
    rw [hMs, hMtot] at *
    exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (fun p hp => by rw [Finset.mem_filter] at hp; exact hp.1)
      (fun p _ _ => muGam_nonneg d n p)) hL2'
  -- the tail of the `1/det Γ` sum
  have hGt_le_Mt : Gt ≤ (1/A) * Mt := by
    rw [hGt, hMt, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    rw [Finset.mem_filter] at hp
    have hAμ : A ≤ muXY n p.1 p.2 := le_of_lt (lt_of_not_ge hp.2)
    have h1 : (1:ℝ) ≤ (1/A) * muXY n p.1 p.2 := by
      rw [show (1/A) * muXY n p.1 p.2 = muXY n p.1 p.2 / A from by ring, le_div_iff₀ hApos]
      simpa using hAμ
    have hg := invDetGam_nonneg d n p
    have hm : muGam d n p = muXY n p.1 p.2 * invDetGam d n p := by
      rw [muGam, invDetGam, div_eq_mul_one_div]
    rw [hm]
    calc invDetGam d n p = 1 * invDetGam d n p := by ring
      _ ≤ ((1/A) * muXY n p.1 p.2) * invDetGam d n p := mul_le_mul_of_nonneg_right h1 hg
      _ = (1/A) * (muXY n p.1 p.2 * invDetGam d n p) := by ring
  have hGt_bound : Gt ≤ (1/A) * (K₂ * A ^ ((3:ℝ)/4) * EE d n B) := by
    calc Gt ≤ (1/A) * Mt := hGt_le_Mt
      _ ≤ (1/A) * (K₂ * A ^ ((3:ℝ)/4) * EE d n B) := by
          apply mul_le_mul_of_nonneg_left
          · rw [hMt, hMtot] at *
            exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg
              (fun p hp => by rw [Finset.mem_filter] at hp; exact hp.1)
              (fun p _ _ => muGam_nonneg d n p)) hL2'
          · positivity
  -- the two sum identities
  have hS1sum : (∑ p ∈ F.filter (fun p => muXY n p.1 p.2 ≤ A), pairS0 d n A p)
      = 8 * iotaDN d n * A ^ (NN d n - 2) * Gs + Err := by
    have h1 : (∑ p ∈ F.filter (fun p => muXY n p.1 p.2 ≤ A), pairS0 d n A p)
        = (∑ p ∈ F.filter (fun p => muXY n p.1 p.2 ≤ A),
              (8 * iotaDN d n * A ^ (NN d n - 2)) * invDetGam d n p)
          + (∑ p ∈ F.filter (fun p => muXY n p.1 p.2 ≤ A),
              (pairS0 d n A p - (8 * iotaDN d n * A ^ (NN d n - 2)) * invDetGam d n p)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp; ring
    rw [h1, hGs, hErr, Finset.mul_sum]
  have hmt2 : mainTerm d n A B = 2 * iotaDN d n * A ^ (NN d n - 2) * (Gs + Gt) := by
    rw [hmt, hsplit, ← hGs, ← hGt]
  -- the absolute-value decomposition
  have habs : |Sigma1 d n A B - mainTerm d n A B|
      ≤ 2 * iotaDN d n * A ^ (NN d n - 2) * Gt + (1/4) * |Err| := by
    have hEq : Sigma1 d n A B - mainTerm d n A B
        = (1/4) * Err - 2 * iotaDN d n * A ^ (NN d n - 2) * Gt := by
      rw [hS1, hS1sum, hmt2]
      ring
    rw [hEq]
    have h1 : |(1/4) * Err - 2 * iotaDN d n * A ^ (NN d n - 2) * Gt|
        ≤ |(1/4) * Err| + |2 * iotaDN d n * A ^ (NN d n - 2) * Gt| := by
      rw [sub_eq_add_neg]
      calc |(1/4) * Err + -(2 * iotaDN d n * A ^ (NN d n - 2) * Gt)|
          ≤ |(1/4) * Err| + |-(2 * iotaDN d n * A ^ (NN d n - 2) * Gt)| := abs_add_le _ _
        _ = |(1/4) * Err| + |2 * iotaDN d n * A ^ (NN d n - 2) * Gt| := by rw [abs_neg]
    have hA1 : |(1/4) * Err| = (1/4) * |Err| := by
      rw [abs_mul]; congr 1; exact abs_of_nonneg (by norm_num)
    have hA2 : |2 * iotaDN d n * A ^ (NN d n - 2) * Gt| = 2 * iotaDN d n * A ^ (NN d n - 2) * Gt := by
      rw [abs_of_nonneg]
      have : 0 ≤ Gt := by rw [hGt]; exact Finset.sum_nonneg (fun p _ => invDetGam_nonneg d n p)
      positivity
    calc |(1/4) * Err - 2 * iotaDN d n * A ^ (NN d n - 2) * Gt|
        ≤ |(1/4) * Err| + |2 * iotaDN d n * A ^ (NN d n - 2) * Gt| := h1
      _ = (1/4) * |Err| + 2 * iotaDN d n * A ^ (NN d n - 2) * Gt := by rw [hA1, hA2]
      _ = 2 * iotaDN d n * A ^ (NN d n - 2) * Gt + (1/4) * |Err| := by ring
  -- the two halves
  have termB : (2 * iotaDN d n * A ^ (NN d n - 2) * Gt) * A ^ ((1:ℝ)/4)
      ≤ K₂ * mainTerm d n A B := by
    have hstep2 : (2 * iotaDN d n * A ^ (NN d n - 2) * Gt) * A ^ ((1:ℝ)/4)
        ≤ (2 * iotaDN d n * A ^ (NN d n - 2)
            * ((1/A) * (K₂ * A ^ ((3:ℝ)/4) * EE d n B))) * A ^ ((1:ℝ)/4) := by
      have hc : 0 ≤ 2 * iotaDN d n * A ^ (NN d n - 2) := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hGt_bound hc) (le_of_lt hqpos)
    have heq : (2 * iotaDN d n * A ^ (NN d n - 2)
            * ((1/A) * (K₂ * A ^ ((3:ℝ)/4) * EE d n B))) * A ^ ((1:ℝ)/4)
        = K₂ * mainTerm d n A B := by
      rw [show mainTerm d n A B = 2 * iotaDN d n * A ^ (NN d n - 2) * EE d n B from rfl]
      have h2 : A ^ ((3:ℝ)/4) * A ^ ((1:ℝ)/4) = A := by rw [mul_comm, hquarter]
      have h3 : (1/A) * A = 1 := hinvA
      have e1 : (2 * iotaDN d n * A ^ (NN d n - 2)
            * ((1/A) * (K₂ * A ^ ((3:ℝ)/4) * EE d n B))) * A ^ ((1:ℝ)/4)
          = 2 * iotaDN d n * A ^ (NN d n - 2) * K₂ * EE d n B
              * ((1/A) * (A ^ ((3:ℝ)/4) * A ^ ((1:ℝ)/4))) := by ring
      rw [e1, h2, h3]; ring
    linarith [hstep2, heq]
  have termA : ((1/4) * |Err|) * A ^ ((1:ℝ)/4)
      ≤ (K₁ * K₂ / (8 * iotaDN d n)) * mainTerm d n A B := by
    have hstep : (1/4) * |Err| ≤ (1/4) * (K₁ * A ^ (NN d n - 2) * (1/A) * Ms) :=
      mul_le_mul_of_nonneg_left hErr_bound (by norm_num)
    have hstep2 : (1/4) * (K₁ * A ^ (NN d n - 2) * (1/A) * Ms)
        ≤ (1/4) * (K₁ * A ^ (NN d n - 2) * (1/A) * (K₂ * A ^ ((3:ℝ)/4) * EE d n B)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply mul_le_mul_of_nonneg_left hMs_le (by positivity)
    have hstep3 : ((1/4) * |Err|) * A ^ ((1:ℝ)/4)
        ≤ ((1/4) * (K₁ * A ^ (NN d n - 2) * (1/A)
            * (K₂ * A ^ ((3:ℝ)/4) * EE d n B))) * A ^ ((1:ℝ)/4) :=
      mul_le_mul_of_nonneg_right (le_trans hstep hstep2) (le_of_lt hqpos)
    rw [show mainTerm d n A B = 2 * iotaDN d n * A ^ (NN d n - 2) * EE d n B from rfl]
    exact le_trans hstep3 (le_of_eq (arith_quarter A (iotaDN d n) K₁ K₂ (EE d n B)
      (NN d n - 2) hAne hquarter (ne_of_gt hι)))
  -- conclusion
  rw [le_div_iff₀ hqpos]
  calc |Sigma1 d n A B - mainTerm d n A B| * A ^ ((1:ℝ)/4)
      ≤ (2 * iotaDN d n * A ^ (NN d n - 2) * Gt + (1/4) * |Err|) * A ^ ((1:ℝ)/4) :=
        mul_le_mul_of_nonneg_right habs (le_of_lt hqpos)
    _ = (2 * iotaDN d n * A ^ (NN d n - 2) * Gt) * A ^ ((1:ℝ)/4)
        + ((1/4) * |Err|) * A ^ ((1:ℝ)/4) := by ring
    _ ≤ K₂ * mainTerm d n A B + (K₁ * K₂ / (8 * iotaDN d n)) * mainTerm d n A B :=
        add_le_add termB termA
    _ = (K₂ + K₁ * K₂ / (8 * iotaDN d n)) * mainTerm d n A B := by ring

/-- The `(4,4)` case of the `Σ^{(1)}` estimate (BBS Lemma D44, small-`μ` half). -/
theorem Sigma1_44 :
    ∃ K B₀ : ℝ, ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      |Sigma1 4 4 A B - mainTerm 4 4 A B| ≤ K * mainTerm 4 4 A B / A ^ ((1 : ℝ) / 4) :=
  Sigma1_44_gen 4 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Work.HP.MDEstimates

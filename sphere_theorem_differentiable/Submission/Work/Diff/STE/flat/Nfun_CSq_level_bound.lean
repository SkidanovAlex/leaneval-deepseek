import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.level_defs
import Submission.Work.Diff.STE.flat.CSq_comp_xperiodic_le
import Submission.Work.Diff.STE.CSq_le_ENormSq_seriesFun
import Submission.Work.Diff.STE.flat.nonlin_coeff_bound
import Submission.Work.Diff.STE.flat.det_cutoff
import Submission.Work.Diff.STE.flat.cutoff_mul_contDiff
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The level-`k` `CSq` bound for the value-and-first-jet nonlinearity

This file proves `Work.Diff.STE.flat.Nfun_CSq_level_bound`: for a smooth nonlinearity `Nfun`
depending only on the point `x` and the value-and-first-jet `(A, L)` of the unknown (smooth on the
nondegenerate locus `{det (reMat A) ≠ 0}`, `1`-periodic in `x`), and data `c` supported in the
Fourier box `box n N` whose level-`k` full energy is bounded by `B²` and whose series is uniformly
`lam`-elliptic, the `k`-th weighted `ℓ²` norm of the Fourier coefficients of each matrix entry of
`x ↦ Nfun (x, jetP c x)` is bounded by a constant times `1 + ENormSqFull (k+1) (seriesFunM c)`,
the constant being independent of `N` and `c`.

## Proof

The nonlinearity sees the first jet, hence loses exactly one derivative: the estimate needs the
level `k - 2` data bound of the Moser composition estimate (`CSq_comp_xperiodic_le`, applied with
`ρ = k - 2`, `s = k`; the hypothesis `n + 4 < 2 k` is exactly `n < 2 ρ`), while the level-`k`
coefficient norm of the data is controlled by `ENormSqFull (k+1)` (one level above, to pay for the
extra derivative).

* The value and the first jet of `seriesFunM c` are packed into one vector of
  `Fintype.card (JetIx n)` complex numbers (`unpackJ`/`jetDataJ`), reusing the index set `JetIx n`
  of the two-jet data of `nonlin_coeff_bound`; the `.sec` slots carry a redundant copy of the
  first-derivative blocks, which only changes constants.
* The nonlinearity is multiplied by a smooth cut-off equal to `1` on the set of jets bounded by
  `KA` and `lam/2`-elliptic and supported in `{det ≠ 0}` (`det_cutoff`, with the second block
  evaluated at `0`); the product is *globally* smooth (`cutoff_mul_contDiff_jet1`), so the Moser
  composition estimate applies.
* The cut-off equals `1` on the graph of the jet because ellipticity and the energy bound give a
  uniform sup bound for the value and the first jet (`jetP_sup_le_uniform`, from
  `norm_seriesFun_le` + `CSq_le_ENormSq_seriesFun`).
* The data bounds are `CSq_jetDataJ_le`: the level-`q` coefficient norm of the packed data is
  controlled by `ENormSqFull L` whenever `q + 1 ≤ L`.
-/

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat
open Filter
open scoped Topology

noncomputable section

/-! ## Packing the value and the first jet -/

/-- The coefficient family of the value-and-first-jet data of `seriesFunM c`, indexed by `JetIx n`:
the value, the first jet, and a (redundant) copy of the first jet in the `.sec` slots. -/
def jetDataJV {n : ℕ} (c : (Fin n → ℤ) → MatC n) (k : Fin n → ℤ) : JetIx n → ℂ
  | .val i j => c k i j
  | .lin a i j => Work.Diff.STE.dmul a (fun m => c m i j) k
  | .sec a _b i j => Work.Diff.STE.dmul a (fun m => c m i j) k

/-- The packed value-and-first-jet data of `c`, as a family with values in
`Fin (Fintype.card (JetIx n)) → ℂ` (the shape required by the Moser composition estimate). -/
def jetDataJ {n : ℕ} (c : (Fin n → ℤ) → MatC n) :
    (Fin n → ℤ) → (Fin (Fintype.card (JetIx n)) → ℂ) :=
  fun k p => jetDataJV c k ((jetIdxEquiv n).symm p)

/-- Unpacking a vector indexed by `JetIx n` into a value matrix and a first jet (the inverse of
`jetDataJ` on the data of a series). -/
def unpackJ {n : ℕ} (z : Fin (Fintype.card (JetIx n)) → ℂ) : MatC n × (Fin n → MatC n) :=
  ((fun i j => z (jetIdxEquiv n (.val i j))), fun a i j => z (jetIdxEquiv n (.lin a i j)))

lemma jetDataJ_apply {n : ℕ} (c : (Fin n → ℤ) → MatC n) (k : Fin n → ℤ) (w : JetIx n) :
    jetDataJ c k (jetIdxEquiv n w) = jetDataJV c k w := by
  simp only [jetDataJ, Equiv.symm_apply_apply]

/-- **The packed data vector is the value and the first jet of the series.** -/
lemma unpackJ_jetDataJ {n N : ℕ} (c : (Fin n → ℤ) → MatC n)
    (hc : ∀ k' : Fin n → ℤ, k' ∉ box n N → c k' = 0) (x : Fin n → ℝ) :
    unpackJ (fun p => Work.Diff.STE.seriesFun (fun k => jetDataJ c k p) x) = jetP c x := by
  refine Prod.ext ?_ ?_
  · funext i j
    simp only [unpackJ, jetDataJ, jetDataJV, jetP_fst, jetIdxEquiv, Equiv.symm_apply_apply,
      seriesFunM_apply]
  · funext a i j
    simp only [unpackJ, jetDataJ, jetDataJV, jetP_snd, jetIdxEquiv, Equiv.symm_apply_apply,
      seriesFunM_apply]
    exact (Work.Diff.STE.pd_seriesFun a (fun m => c m i j)
      (fun M => summable_moment_box c hc i j M) x).symm

/-- The unpacking map is smooth (it is linear). -/
lemma contDiff_unpackJ {n : ℕ} : ContDiff ℝ (⊤ : ℕ∞) (unpackJ (n := n)) := by
  unfold unpackJ
  refine ContDiff.prodMk ?_ ?_
  · refine contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => ?_
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (Fintype.card (JetIx n)) => ℂ)
      (jetIdxEquiv n (.val i j))).contDiff
  · refine contDiff_pi.mpr fun a => contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => ?_
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (Fintype.card (JetIx n)) => ℂ)
      (jetIdxEquiv n (.lin a i j))).contDiff

/-- The packed data family has finite moments as soon as `c` is box-supported. -/
lemma summable_moment_jetDataJ {n N : ℕ} (c : (Fin n → ℤ) → MatC n)
    (hc : ∀ k' : Fin n → ℤ, k' ∉ box n N → c k' = 0) :
    ∀ M : ℕ, Summable (fun k : Fin n → ℤ =>
      (Work.Diff.STE.wt k) ^ M * ‖jetDataJ c k‖) := by
  intro M
  have hmom : ∀ (i j : Fin n) (M' : ℕ),
      Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ M' * ‖c k i j‖) :=
    fun i j M' => summable_moment_box c hc i j M'
  have hcomp : ∀ w : JetIx n,
      Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ M * ‖jetDataJV c k w‖) := by
    intro w
    cases w with
    | val i j => exact hmom i j M
    | lin a i j => exact summable_dmul_moments a _ (hmom i j) M
    | sec a b i j => exact summable_dmul_moments a _ (hmom i j) M
  have hvec : Summable (fun k : Fin n → ℤ =>
      (Work.Diff.STE.wt k) ^ M * ∑ w : JetIx n, ‖jetDataJV c k w‖) := by
    have h := summable_sum (s := Finset.univ) (fun w _ => hcomp w)
    simpa only [Finset.mul_sum] using h
  have hnorm : ∀ k : Fin n → ℤ, ‖jetDataJ c k‖ ≤ ∑ w : JetIx n, ‖jetDataJV c k w‖ := by
    intro k
    have h1 : ‖jetDataJ c k‖ ≤ ∑ p : Fin (Fintype.card (JetIx n)), ‖jetDataJ c k p‖ :=
      (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun p =>
        Finset.single_le_sum
          (f := fun p : Fin (Fintype.card (JetIx n)) => ‖jetDataJ c k p‖)
          (fun p _ => norm_nonneg _) (Finset.mem_univ p)
    have h2 : (∑ p : Fin (Fintype.card (JetIx n)), ‖jetDataJ c k p‖)
        = ∑ w : JetIx n, ‖jetDataJV c k w‖ := by
      rw [← Equiv.sum_comp (jetIdxEquiv n) (fun p => ‖jetDataJ c k p‖)]
      exact Finset.sum_congr rfl fun w _ => by rw [jetDataJ, Equiv.symm_apply_apply]
    rw [h2] at h1
    exact h1
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) M) (norm_nonneg _))
    (fun k => mul_le_mul_of_nonneg_left (hnorm k)
      (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) M)) hvec

/-! ## The data bound -/

lemma CSq_jetDataJ_le {n : ℕ} (q L : ℕ) (hq : q + 1 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
      (∀ k' : Fin n → ℤ, k' ∉ box n N → c k' = 0) →
      (∑ p : Fin (Fintype.card (JetIx n)), Work.Diff.STE.CSq q (fun m => jetDataJ c m p))
        ≤ C * ENormSqFull L (seriesFunM c) := by
  obtain ⟨Cl, hCl0, hCl⟩ := Work.Diff.STE.CSq_le_ENormSq_seriesFun (ι := Fin n) L
  refine ⟨(Fintype.card (JetIx n) : ℝ) * (((2 * Real.pi) ^ 2) * Cl + Cl), ?_, ?_⟩
  · exact mul_nonneg (Nat.cast_nonneg _)
      (add_nonneg (mul_nonneg (sq_nonneg _) hCl0) hCl0)
  intro N c hc
  have hmom : ∀ (i j : Fin n) (M : ℕ),
      Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ M * ‖c k i j‖) :=
    fun i j M => summable_moment_box c hc i j M
  have hentry : ∀ (i j : Fin n), Work.Diff.STE.CSq L (fun m => c m i j)
      ≤ Cl * ENormSqFull L (seriesFunM c) := by
    intro i j
    have hfun : (fun x : Fin n → ℝ => seriesFunM c x i j)
        = Work.Diff.STE.seriesFun (fun m : Fin n → ℤ => c m i j) := by
      funext y; rw [seriesFunM_apply]
    have h1 := hCl (fun m : Fin n → ℤ => c m i j) (hmom i j)
    rw [← hfun] at h1
    have h2 : Work.Diff.STE.ENormSq L (fun x : Fin n → ℝ => seriesFunM c x i j)
        ≤ ENormSqM L (seriesFunM c) := ENormSq_le_ENormSqM _ i j
    have h3 : Work.Diff.STE.ENormSq 0 (fun x : Fin n → ℝ => seriesFunM c x i j)
        ≤ ENormSqM 0 (seriesFunM c) := ENormSq_le_ENormSqM _ i j
    have h4 : Work.Diff.STE.ENormSq L (fun x : Fin n → ℝ => seriesFunM c x i j)
        + Work.Diff.STE.ENormSq 0 (fun x : Fin n → ℝ => seriesFunM c x i j)
        ≤ ENormSqFull L (seriesFunM c) := by
      rw [ENormSqFull]; linarith
    exact h1.trans (mul_le_mul_of_nonneg_left h4 hCl0)
  have hkey : ∀ w : JetIx n, Work.Diff.STE.CSq q (fun m => jetDataJV c m w)
      ≤ (((2 * Real.pi) ^ 2) * Cl + Cl) * ENormSqFull L (seriesFunM c) := by
    intro w
    cases w with
    | val i j =>
        have hmono : Work.Diff.STE.CSq q (fun m => c m i j)
            ≤ Work.Diff.STE.CSq L (fun m => c m i j) :=
          ncb_CSq_mono_le _ (by omega)
            (Work.Diff.STE.summable_wt_pow_mul_norm_sq _ (hmom i j) L)
        have hE := ENormSqFull_nonneg L (seriesFunM c)
        have hnn : 0 ≤ ((2 * Real.pi) ^ 2) * Cl := mul_nonneg (sq_nonneg _) hCl0
        have h2 : Cl * ENormSqFull L (seriesFunM c)
            ≤ (((2 * Real.pi) ^ 2) * Cl + Cl) * ENormSqFull L (seriesFunM c) :=
          mul_le_mul_of_nonneg_right (by linarith) hE
        exact (hmono.trans (hentry i j)).trans h2
    | lin a i j =>
        have hdm : Work.Diff.STE.CSq q (Work.Diff.STE.dmul a (fun m => c m i j))
            ≤ ((2 * Real.pi) ^ 2) * Work.Diff.STE.CSq (q + 1) (fun m => c m i j) := by
          have h := CSq_dmulV_le (ι := Fin n) q [a] (fun m => c m i j) (hmom i j)
          simpa [dmulV_single] using h
        have hmono : Work.Diff.STE.CSq (q + 1) (fun m => c m i j)
            ≤ Work.Diff.STE.CSq L (fun m => c m i j) :=
          ncb_CSq_mono_le _ hq (Work.Diff.STE.summable_wt_pow_mul_norm_sq _ (hmom i j) L)
        have hE := ENormSqFull_nonneg L (seriesFunM c)
        have hnn : 0 ≤ ((2 * Real.pi) ^ 2) * Cl := mul_nonneg (sq_nonneg _) hCl0
        have h1 : Work.Diff.STE.CSq q (Work.Diff.STE.dmul a (fun m => c m i j))
            ≤ ((2 * Real.pi) ^ 2) * (Cl * ENormSqFull L (seriesFunM c)) :=
          hdm.trans (mul_le_mul_of_nonneg_left (hmono.trans (hentry i j)) (by positivity))
        have h2 : ((2 * Real.pi) ^ 2) * (Cl * ENormSqFull L (seriesFunM c))
            ≤ (((2 * Real.pi) ^ 2) * Cl + Cl) * ENormSqFull L (seriesFunM c) := by
          nlinarith [hE, hnn, hCl0]
        exact h1.trans h2
    | sec a b i j =>
        have hdm : Work.Diff.STE.CSq q (Work.Diff.STE.dmul a (fun m => c m i j))
            ≤ ((2 * Real.pi) ^ 2) * Work.Diff.STE.CSq (q + 1) (fun m => c m i j) := by
          have h := CSq_dmulV_le (ι := Fin n) q [a] (fun m => c m i j) (hmom i j)
          simpa [dmulV_single] using h
        have hmono : Work.Diff.STE.CSq (q + 1) (fun m => c m i j)
            ≤ Work.Diff.STE.CSq L (fun m => c m i j) :=
          ncb_CSq_mono_le _ hq (Work.Diff.STE.summable_wt_pow_mul_norm_sq _ (hmom i j) L)
        have hE := ENormSqFull_nonneg L (seriesFunM c)
        have hnn : 0 ≤ ((2 * Real.pi) ^ 2) * Cl := mul_nonneg (sq_nonneg _) hCl0
        have h1 : Work.Diff.STE.CSq q (Work.Diff.STE.dmul a (fun m => c m i j))
            ≤ ((2 * Real.pi) ^ 2) * (Cl * ENormSqFull L (seriesFunM c)) :=
          hdm.trans (mul_le_mul_of_nonneg_left (hmono.trans (hentry i j)) (by positivity))
        have h2 : ((2 * Real.pi) ^ 2) * (Cl * ENormSqFull L (seriesFunM c))
            ≤ (((2 * Real.pi) ^ 2) * Cl + Cl) * ENormSqFull L (seriesFunM c) := by
          nlinarith [hE, hnn, hCl0]
        exact h1.trans h2
  calc (∑ p : Fin (Fintype.card (JetIx n)), Work.Diff.STE.CSq q (fun m => jetDataJ c m p))
      ≤ ∑ _p : Fin (Fintype.card (JetIx n)),
        (((2 * Real.pi) ^ 2) * Cl + Cl) * ENormSqFull L (seriesFunM c) :=
        Finset.sum_le_sum fun p _ => hkey _
    _ = (Fintype.card (JetIx n) : ℝ)
          * ((((2 * Real.pi) ^ 2) * Cl + Cl) * ENormSqFull L (seriesFunM c)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]
    _ = (Fintype.card (JetIx n) : ℝ) * (((2 * Real.pi) ^ 2) * Cl + Cl)
          * ENormSqFull L (seriesFunM c) := by ring

/-! ## The uniform sup bound for the value and the first jet -/

/-- **Uniform sup bound.**  A box-supported family with `ENormSqFull k ≤ B²` has its value and its
first jet bounded by a constant depending only on `n`, `k`, `B` (Sobolev embedding at the level
`sob n`, plus the coefficient/energy comparison of `CSq_le_ENormSq_seriesFun`). -/
lemma jetP_sup_le_uniform {n k : ℕ} (hsob : sob n + 1 ≤ k) (B : ℝ) (hB : 0 ≤ B) :
    ∃ KA : ℝ, 0 ≤ KA ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
      (∀ k' : Fin n → ℤ, k' ∉ box n N → c k' = 0) →
      ENormSqFull k (seriesFunM c) ≤ B ^ 2 →
      ∀ x : Fin n → ℝ,
        (∀ i j, ‖seriesFunM c x i j‖ ≤ KA) ∧
        (∀ a i j, ‖pd a (fun y => seriesFunM c y i j) x‖ ≤ KA) := by
  obtain ⟨C0, hC00, hC0⟩ := Work.Diff.STE.norm_seriesFun_le (ι := Fin n) (sob n)
    (by simpa using n_lt_two_sob n)
  obtain ⟨Ck, hCk0, hCk⟩ := Work.Diff.STE.CSq_le_ENormSq_seriesFun (ι := Fin n) k
  refine ⟨(C0 * (2 * Real.pi) * Real.sqrt Ck) * (1 + B), ?_, ?_⟩
  · have h1 : 0 ≤ C0 * (2 * Real.pi) * Real.sqrt Ck :=
      mul_nonneg (mul_nonneg hC00 (by positivity)) (Real.sqrt_nonneg _)
    exact mul_nonneg h1 (by linarith)
  intro N c hc hE x
  have hmom : ∀ (i j : Fin n) (M : ℕ),
      Summable (fun m : Fin n → ℤ => (Work.Diff.STE.wt m) ^ M * ‖c m i j‖) :=
    fun i j M => summable_moment_box c hc i j M
  have hE' : 0 ≤ ENormSqFull k (seriesFunM c) := ENormSqFull_nonneg k (seriesFunM c)
  have hsqrtE : Real.sqrt (ENormSqFull k (seriesFunM c)) ≤ B :=
    (Real.sqrt_le_sqrt hE).trans_eq (Real.sqrt_sq hB)
  have hsCk : 0 ≤ Real.sqrt Ck := Real.sqrt_nonneg _
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hB1 : B ≤ 1 + B := by linarith
  have hfinal : C0 * ((2 * Real.pi) * Real.sqrt Ck * B)
      ≤ (C0 * (2 * Real.pi) * Real.sqrt Ck) * (1 + B) := by
    have h2 : (2 * Real.pi) * Real.sqrt Ck * B ≤ (2 * Real.pi) * Real.sqrt Ck * (1 + B) :=
      mul_le_mul_of_nonneg_left hB1 (by positivity)
    calc C0 * ((2 * Real.pi) * Real.sqrt Ck * B)
        ≤ C0 * ((2 * Real.pi) * Real.sqrt Ck * (1 + B)) :=
          mul_le_mul_of_nonneg_left h2 hC00
      _ = (C0 * (2 * Real.pi) * Real.sqrt Ck) * (1 + B) := by ring
  have hentry : ∀ (i j : Fin n), Work.Diff.STE.CSq k (fun m => c m i j)
      ≤ Ck * ENormSqFull k (seriesFunM c) := by
    intro i j
    have hfun : (fun x : Fin n → ℝ => seriesFunM c x i j)
        = Work.Diff.STE.seriesFun (fun m : Fin n → ℤ => c m i j) := by
      funext y; rw [seriesFunM_apply]
    have h1 := hCk (fun m : Fin n → ℤ => c m i j) (hmom i j)
    rw [← hfun] at h1
    have h2 : Work.Diff.STE.ENormSq k (fun x : Fin n → ℝ => seriesFunM c x i j)
        ≤ ENormSqM k (seriesFunM c) := ENormSq_le_ENormSqM _ i j
    have h3 : Work.Diff.STE.ENormSq 0 (fun x : Fin n → ℝ => seriesFunM c x i j)
        ≤ ENormSqM 0 (seriesFunM c) := ENormSq_le_ENormSqM _ i j
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hCk0)
    rw [ENormSqFull]; linarith
  constructor
  · intro i j
    have h1 := hC0 (fun m => c m i j)
      (Work.Diff.STE.summable_wt_pow_mul_norm_sq _ (hmom i j) (sob n)) x
    have h2 : Work.Diff.STE.CSq (sob n) (fun m => c m i j)
        ≤ Ck * ENormSqFull k (seriesFunM c) :=
      (ncb_CSq_mono_le _ (by omega)
        (Work.Diff.STE.summable_wt_pow_mul_norm_sq _ (hmom i j) k)).trans (hentry i j)
    have h3 : C0 * Real.sqrt (Work.Diff.STE.CSq (sob n) (fun m => c m i j))
        ≤ C0 * (Real.sqrt Ck * B) := by
      refine mul_le_mul_of_nonneg_left ?_ hC00
      calc Real.sqrt (Work.Diff.STE.CSq (sob n) (fun m => c m i j))
          ≤ Real.sqrt (Ck * ENormSqFull k (seriesFunM c)) := Real.sqrt_le_sqrt h2
        _ = Real.sqrt Ck * Real.sqrt (ENormSqFull k (seriesFunM c)) := Real.sqrt_mul hCk0 _
        _ ≤ Real.sqrt Ck * B := mul_le_mul_of_nonneg_left hsqrtE hsCk
    calc ‖seriesFunM c x i j‖
        ≤ C0 * Real.sqrt (Work.Diff.STE.CSq (sob n) (fun m => c m i j)) := by
          simpa only [seriesFunM_apply] using h1
      _ ≤ C0 * (Real.sqrt Ck * B) := h3
      _ ≤ C0 * ((2 * Real.pi) * Real.sqrt Ck * B) := by
          refine mul_le_mul_of_nonneg_left ?_ hC00
          have h5 : Real.sqrt Ck ≤ 2 * Real.pi * Real.sqrt Ck := by nlinarith [hsCk, hpi]
          exact mul_le_mul_of_nonneg_right h5 hB
      _ ≤ (C0 * (2 * Real.pi) * Real.sqrt Ck) * (1 + B) := hfinal
  · intro a i j
    have hdmm : ∀ M : ℕ, Summable (fun m : Fin n → ℤ =>
        (Work.Diff.STE.wt m) ^ M * ‖Work.Diff.STE.dmul a (fun m => c m i j) m‖) :=
      summable_dmul_moments a _ (hmom i j)
    have h1 := hC0 (Work.Diff.STE.dmul a (fun m => c m i j))
      (Work.Diff.STE.summable_wt_pow_mul_norm_sq _ hdmm (sob n)) x
    have hpd : pd a (fun y : Fin n → ℝ => seriesFunM c y i j) x
        = Work.Diff.STE.seriesFun (Work.Diff.STE.dmul a (fun m => c m i j)) x := by
      simpa only [seriesFunM_apply] using
        (Work.Diff.STE.pd_seriesFun a (fun m => c m i j) (hmom i j) x)
    have hdd : Work.Diff.STE.CSq (sob n) (Work.Diff.STE.dmul a (fun m => c m i j))
        ≤ ((2 * Real.pi) ^ 2) * Work.Diff.STE.CSq k (fun m => c m i j) := by
      have h := CSq_dmulV_le (ι := Fin n) (sob n) [a] (fun m => c m i j) (hmom i j)
      have h' : Work.Diff.STE.CSq (sob n) (Work.Diff.STE.dmul a (fun m => c m i j))
          ≤ ((2 * Real.pi) ^ 2) * Work.Diff.STE.CSq (sob n + 1) (fun m => c m i j) := by
        simpa [dmulV_single] using h
      exact h'.trans (mul_le_mul_of_nonneg_left
        (ncb_CSq_mono_le _ (by omega)
          (Work.Diff.STE.summable_wt_pow_mul_norm_sq _ (hmom i j) k)) (by positivity))
    have h3 : C0 * Real.sqrt (Work.Diff.STE.CSq (sob n) (Work.Diff.STE.dmul a (fun m => c m i j)))
        ≤ C0 * ((2 * Real.pi) * Real.sqrt Ck * B) := by
      refine mul_le_mul_of_nonneg_left ?_ hC00
      calc Real.sqrt (Work.Diff.STE.CSq (sob n) (Work.Diff.STE.dmul a (fun m => c m i j)))
          ≤ Real.sqrt (((2 * Real.pi) ^ 2)
              * (Ck * ENormSqFull k (seriesFunM c))) := by
            refine Real.sqrt_le_sqrt ?_
            refine hdd.trans ?_
            exact mul_le_mul_of_nonneg_left (hentry i j) (by positivity)
        _ = 2 * Real.pi * (Real.sqrt Ck * Real.sqrt (ENormSqFull k (seriesFunM c))) := by
            rw [Real.sqrt_mul (sq_nonneg (2 * Real.pi)), Real.sqrt_sq (by positivity),
              Real.sqrt_mul hCk0]
        _ ≤ 2 * Real.pi * (Real.sqrt Ck * B) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_left hsqrtE hsCk
        _ = (2 * Real.pi) * Real.sqrt Ck * B := by ring
    calc ‖pd a (fun y : Fin n → ℝ => seriesFunM c y i j) x‖
        ≤ C0 * Real.sqrt (Work.Diff.STE.CSq (sob n)
            (Work.Diff.STE.dmul a (fun m => c m i j))) := by
          rw [hpd]; exact h1
      _ ≤ C0 * ((2 * Real.pi) * Real.sqrt Ck * B) := h3
      _ ≤ (C0 * (2 * Real.pi) * Real.sqrt Ck) * (1 + B) := hfinal

/-! ## The one-jet cut-off -/

/-- The nondegenerate set of value-and-first-jet pairs is open. -/
lemma isOpen_det_ne_zero_j1 (n : ℕ) :
    IsOpen {w : MatC n × (Fin n → MatC n) | (reMat w.1).det ≠ 0} := by
  have hcont : Continuous fun w : MatC n × (Fin n → MatC n) => (reMat w.1).det := by
    refine Continuous.matrix_det ?_
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact Complex.continuous_re.comp (((continuous_apply j).comp (continuous_apply i)).comp
      (continuous_fst (X := MatC n)))
  exact (isOpen_ne (x := (0 : ℝ))).preimage hcont

/-- **Cutting a one-jet nonlinearity off away from its singular locus.**  Multiplying a
nonlinearity which is smooth on `{det (reMat A) ≠ 0}` by a smooth cut-off supported in that set
gives a *globally* smooth nonlinearity. -/
lemma cutoff_mul_contDiff_jet1 (n : ℕ)
    (Nfun : (Fin n → ℝ) × (MatC n × (Fin n → MatC n)) → MatC n)
    (hN : ContDiffOn ℝ (⊤ : ℕ∞) Nfun
      (Set.univ ×ˢ {w : MatC n × (Fin n → MatC n) | (reMat w.1).det ≠ 0}))
    (ch : MatC n × (Fin n → MatC n) → ℝ) (hch : ContDiff ℝ (⊤ : ℕ∞) ch)
    (hts : tsupport ch ⊆ {w : MatC n × (Fin n → MatC n) | (reMat w.1).det ≠ 0}) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (Fin n → ℝ) × (MatC n × (Fin n → MatC n)) => (ch p.2 : ℂ) • Nfun p) := by
  have hSopen := isOpen_det_ne_zero_j1 n
  have hchc : ContDiff ℝ (⊤ : ℕ∞) (fun p : (Fin n → ℝ) × (MatC n × (Fin n → MatC n)) =>
      (ch p.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hch.comp
      (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (MatC n × (Fin n → MatC n))).contDiff)
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.2 ∈ tsupport ch
  · have hpS : p.2 ∈ {w : MatC n × (Fin n → MatC n) | (reMat w.1).det ≠ 0} := hts hp
    have hmem : Set.univ ×ˢ {w : MatC n × (Fin n → MatC n) | (reMat w.1).det ≠ 0} ∈ 𝓝 p :=
      (IsOpen.prod isOpen_univ hSopen).mem_nhds ⟨trivial, hpS⟩
    exact hchc.contDiffAt.smul (hN.contDiffAt hmem)
  · have hev : (fun _ : (Fin n → ℝ) × (MatC n × (Fin n → MatC n)) => (0 : MatC n))
        =ᶠ[𝓝 p] (fun q => (ch q.2 : ℂ) • Nfun q) := by
      have hmemU : Set.univ ×ˢ (tsupport ch)ᶜ ∈ 𝓝 p :=
        (IsOpen.prod isOpen_univ (isClosed_tsupport ch).isOpen_compl).mem_nhds ⟨trivial, hp⟩
      refine Filter.eventually_of_mem hmemU ?_
      intro q hq
      have hq' : q.2 ∉ tsupport ch := hq.2
      have hz : ch q.2 = 0 := Function.notMem_support.mp (fun h => hq' (subset_closure h))
      simp [hz]
    exact (contDiffAt_const (c := (0 : MatC n))).congr_of_eventuallyEq hev.symm

/-! ## The main estimate -/

theorem Nfun_CSq_level_bound {n : ℕ} (hn : 1 ≤ n)
    (k : ℕ) (hk : Fintype.card (Fin n) + 4 < 2 * k)
    (Nfun : (Fin n → ℝ) × (Work.Diff.STE.Flat.MatC n × (Fin n → Work.Diff.STE.Flat.MatC n))
      → Work.Diff.STE.Flat.MatC n)
    (hNsm : ContDiffOn ℝ (⊤ : ℕ∞) Nfun (Set.prod Set.univ
        {w : Work.Diff.STE.Flat.MatC n × (Fin n → Work.Diff.STE.Flat.MatC n)
          | (Work.Diff.STE.Flat.reMat w.1).det ≠ 0}))
    (hNper : ∀ w : Work.Diff.STE.Flat.MatC n × (Fin n → Work.Diff.STE.Flat.MatC n),
        Work.Diff.STE.Periodic1 (fun x : Fin n → ℝ => Nfun (x, w)))
    (lam : ℝ) (hlam : 0 < lam) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ) (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
        (∀ k' : Fin n → ℤ, k' ∉ Work.Diff.STE.Flat.box n N → c k' = 0) →
        Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM c) ≤ B ^ 2 →
        (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
          lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
            Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) i j * v i * v j) →
        ∀ (i j : Fin n),
          Work.Diff.STE.CSq k (fun m => Work.Diff.STE.fourierCoeff
              (fun x => Nfun (x, Work.Diff.STE.flat.jetP c x) i j) m)
            ≤ C * (1 + Work.Diff.STE.Flat.ENormSqFull (k + 1) (Work.Diff.STE.Flat.seriesFunM c)) := by
  classical
  have hkc : n + 4 < 2 * k := by simpa using hk
  -- ### arithmetic
  have hsob2 : sob n + 2 ≤ k := by
    rw [sob]; omega
  have hsob1 : sob n + 1 ≤ k := by omega
  have hkρ : n < 2 * (k - 2) := by omega
  have hρk : k - 2 ≤ k := by omega
  -- ### the uniform sup bound and the cut-off
  obtain ⟨KA, hKAnn, hsup⟩ := jetP_sup_le_uniform (n := n) (k := k) hsob1 B hB
  obtain ⟨ch, hchsm, hch0, hchts, hchone⟩ := det_cutoff n hn lam hlam KA hKAnn
  set χ₁ : MatC n × (Fin n → MatC n) → ℝ :=
    fun w => ch (w.1, w.2, (0 : Fin n → Fin n → MatC n)) with hχ₁
  have hχ₁sm : ContDiff ℝ (⊤ : ℕ∞) χ₁ := by
    rw [hχ₁]
    refine hchsm.comp ?_
    exact (contDiff_fst (𝕜 := ℝ) (n := (⊤ : ℕ∞))).prodMk
      ((contDiff_snd (𝕜 := ℝ) (n := (⊤ : ℕ∞))).prodMk contDiff_const)
  have hχ₁ts : tsupport χ₁ ⊆ {w : MatC n × (Fin n → MatC n) | (reMat w.1).det ≠ 0} := by
    intro w hw
    by_contra hcon
    have hdet : (reMat w.1).det = 0 := by
      by_contra hne
      exact hcon (by simpa using hne)
    have h0 : (w.1, w.2, (0 : Fin n → Fin n → MatC n)) ∉ tsupport ch := fun h => hchts h hdet
    have hcont : Continuous fun v : MatC n × (Fin n → MatC n) =>
        (v.1, v.2, (0 : Fin n → Fin n → MatC n)) := by fun_prop
    have hev : ∀ᶠ v in 𝓝 w, ch (v.1, v.2, (0 : Fin n → Fin n → MatC n)) = 0 :=
      hcont.continuousAt.tendsto.eventually (notMem_tsupport_iff_eventuallyEq.mp h0)
    have hev' : χ₁ =ᶠ[𝓝 w] 0 := by
      rw [hχ₁]
      exact hev
    exact (notMem_tsupport_iff_eventuallyEq.mpr hev') hw
  have hNsm' : ContDiffOn ℝ (⊤ : ℕ∞) Nfun
      (Set.univ ×ˢ {w : MatC n × (Fin n → MatC n) | (reMat w.1).det ≠ 0}) := hNsm
  have hΦaux : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (Fin n → ℝ) × (MatC n × (Fin n → MatC n)) => (χ₁ p.2 : ℂ) • Nfun p) :=
    cutoff_mul_contDiff_jet1 n Nfun hNsm' χ₁ hχ₁sm hχ₁ts
  -- ### the data bounds
  obtain ⟨Cdρ, hCdρ0, hCdρ⟩ := CSq_jetDataJ_le (n := n) (k - 2) k (by omega)
  obtain ⟨Cdk, hCdk0, hCdk⟩ := CSq_jetDataJ_le (n := n) k (k + 1) (by omega)
  set B' : ℝ := Real.sqrt (Cdρ * B ^ 2 + 1) with hB'def
  have hB'nn : 0 ≤ B' := Real.sqrt_nonneg _
  have hB'sq : B' ^ 2 = Cdρ * B ^ 2 + 1 := Real.sq_sqrt (by positivity)
  -- ### the Moser composition estimate, entry by entry
  have hMoser : ∀ i j : Fin n, ∃ Cij : ℝ, 0 ≤ Cij ∧
      ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
        (∀ k' : Fin n → ℤ, k' ∉ box n N → c k' = 0) →
        ENormSqFull k (seriesFunM c) ≤ B ^ 2 →
        (∀ (x : Fin n → ℝ) (v : Fin n → ℝ), lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
            reMat (seriesFunM c x) i j * v i * v j) →
        CSq k (Work.Diff.STE.fourierCoeff (fun x => Nfun (x, jetP c x) i j))
          ≤ Cij * (1 + Cdk * ENormSqFull (k + 1) (seriesFunM c)) := by
    intro i j
    set Φij : (Fin n → ℝ) × (Fin (Fintype.card (JetIx n)) → ℂ) → ℂ :=
      fun p => (χ₁ (unpackJ p.2) : ℂ) • Nfun (p.1, unpackJ p.2) i j with hΦij
    have hΦij_sm : ContDiff ℝ (⊤ : ℕ∞) Φij := by
      rw [hΦij]
      have hp : ContDiff ℝ (⊤ : ℕ∞)
          (fun p : (Fin n → ℝ) × (Fin (Fintype.card (JetIx n)) → ℂ) =>
            (p.1, unpackJ p.2)) :=
        (contDiff_fst (𝕜 := ℝ) (n := (⊤ : ℕ∞))).prodMk
          ((contDiff_unpackJ (n := n)).comp (contDiff_snd (𝕜 := ℝ) (n := (⊤ : ℕ∞))))
      have h1 := hΦaux.comp hp
      exact contDiff_pi.mp (contDiff_pi.mp h1 i) j
    have hΦij_per : ∀ (v : Fin (Fintype.card (JetIx n)) → ℂ) (i' : Fin n) (x : Fin n → ℝ),
        Φij (x + Pi.single i' 1, v) = Φij (x, v) := by
      intro v i' x
      rw [hΦij]
      exact congrArg (fun w => (χ₁ (unpackJ v) : ℂ) • w i j) (hNper (unpackJ v) i' x)
    obtain ⟨Cm, hCm0, hCm⟩ := CSq_comp_xperiodic_le (n := n) (m := Fintype.card (JetIx n))
      k (k - 2) hkρ hρk Φij hΦij_sm hΦij_per B' hB'nn
    refine ⟨Cm, hCm0, ?_⟩
    intro N c hc hE hell
    have hmomJ : ∀ M : ℕ, Summable (fun m : Fin n → ℤ =>
        (Work.Diff.STE.wt m) ^ M * ‖jetDataJ c m‖) := summable_moment_jetDataJ c hc
    have hdatρ : (∑ p : Fin (Fintype.card (JetIx n)),
        CSq (k - 2) (fun m => jetDataJ c m p)) ≤ B' ^ 2 := by
      have h1 := hCdρ N c hc
      have h2 : Cdρ * ENormSqFull k (seriesFunM c) ≤ Cdρ * B ^ 2 :=
        mul_le_mul_of_nonneg_left hE hCdρ0
      rw [hB'sq]
      linarith
    obtain ⟨-, hbound⟩ := hCm (jetDataJ c) hmomJ hdatρ
    have hcongr : (fun x : Fin n → ℝ =>
          Φij (x, fun p => Work.Diff.STE.seriesFun (fun m => jetDataJ c m p) x))
        = fun x : Fin n → ℝ => Nfun (x, jetP c x) i j := by
      funext x
      show (χ₁ (unpackJ (fun p => Work.Diff.STE.seriesFun (fun m => jetDataJ c m p) x)) : ℂ)
          • Nfun (x, unpackJ (fun p => Work.Diff.STE.seriesFun (fun m => jetDataJ c m p) x)) i j
          = Nfun (x, jetP c x) i j
      rw [unpackJ_jetDataJ c hc x]
      have hsupx := hsup N c hc hE x
      set A : MatC n := seriesFunM c x with hA
      set L : Fin n → MatC n := fun a i j => pd a (fun y => seriesFunM c y i j) x with hL
      have hAL : jetP c x = (A, L) := rfl
      have hell' : ∀ v : Fin n → ℝ,
          lam / 2 * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, reMat A i j * v i * v j := by
        intro v
        have hS : 0 ≤ ∑ i, (v i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
        have h := hell x v
        rw [hA]
        have hstep : lam / 2 * ∑ i, (v i) ^ 2 ≤ lam * ∑ i, (v i) ^ 2 := by
          have h2 : lam / 2 = lam * (1 / 2) := by ring
          rw [h2]
          exact mul_le_mul_of_nonneg_right (by linarith) hS
        linarith
      have hχ1 : χ₁ (A, L) = 1 := by
        rw [hχ₁]
        exact hchone (A, L, (0 : Fin n → Fin n → MatC n))
          (fun i j => hsupx.1 i j) (fun a i j => hsupx.2 a i j)
          (fun c' d i' j' => by simp [hKAnn]) hell'
      rw [hAL]
      have hval : (χ₁ (A, L) : ℂ) = 1 := by rw [hχ1]; simp
      rw [hval, one_smul]
    rw [congrArg Work.Diff.STE.fourierCoeff hcongr] at hbound
    have hdatk := hCdk N c hc
    exact hbound.trans (mul_le_mul_of_nonneg_left (by linarith [hdatk]) hCm0)
  -- ### assembly
  choose Cij hCij0 hCij using hMoser
  refine ⟨((∑ ij : Fin n × Fin n, Cij ij.1 ij.2) + 1) * (1 + Cdk), ?_, ?_⟩
  · have h1 : 0 ≤ ∑ ij : Fin n × Fin n, Cij ij.1 ij.2 :=
      Finset.sum_nonneg fun ij _ => hCij0 ij.1 ij.2
    exact mul_nonneg (by linarith) (by linarith)
  intro N c hc hE hell i j
  have h1 := hCij i j N c hc hE hell
  have hE' : 0 ≤ ENormSqFull (k + 1) (seriesFunM c) := ENormSqFull_nonneg _ _
  have h2 : 1 + Cdk * ENormSqFull (k + 1) (seriesFunM c)
      ≤ (1 + Cdk) * (1 + ENormSqFull (k + 1) (seriesFunM c)) := by
    nlinarith [hE', hCdk0]
  have h3 : Cij i j ≤ (∑ ij : Fin n × Fin n, Cij ij.1 ij.2) + 1 := by
    have h := Finset.single_le_sum (f := fun ij : Fin n × Fin n => Cij ij.1 ij.2)
      (fun ij _ => hCij0 ij.1 ij.2) (Finset.mem_univ (i, j))
    linarith
  have hsum0 : 0 ≤ ∑ ij : Fin n × Fin n, Cij ij.1 ij.2 :=
    Finset.sum_nonneg fun ij _ => hCij0 ij.1 ij.2
  calc CSq k (Work.Diff.STE.fourierCoeff (fun x => Nfun (x, jetP c x) i j))
      ≤ Cij i j * (1 + Cdk * ENormSqFull (k + 1) (seriesFunM c)) := h1
    _ ≤ ((∑ ij : Fin n × Fin n, Cij ij.1 ij.2) + 1)
          * ((1 + Cdk) * (1 + ENormSqFull (k + 1) (seriesFunM c))) :=
        mul_le_mul h3 h2 (by have := mul_nonneg hCdk0 hE'; linarith) (by linarith)
    _ = ((∑ ij : Fin n × Fin n, Cij ij.1 ij.2) + 1) * (1 + Cdk)
          * (1 + ENormSqFull (k + 1) (seriesFunM c)) := by ring

end

end Work.Diff.STE.flat

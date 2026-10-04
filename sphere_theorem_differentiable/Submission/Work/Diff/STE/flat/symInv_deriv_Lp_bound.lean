import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.level_defs
import Submission.Work.Diff.STE.flat.inv_jet_bound_symm
import Submission.Work.Diff.STE.CSq_comp_vecarg_le
import Submission.Work.Diff.STE.CSq_le_ENormSq_seriesFun
import Submission.Work.Diff.STE.flat.Sobolev
import Submission.Work.Diff.STE.ENormSq_seriesFun_le
import Submission.Work.Diff.STE.flat.det_cutoff
import Submission.Work.Diff.STE.flat.cutoff_mul_contDiff
import Submission.Work.Diff.STE.flat.sobolev_uniform
import Submission.Work.Diff.STE.flat.CSq_symInvC_le
import Submission.Work.Diff.STE.flat.summable_wt_dmulV_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.Diff.STE.flat.symInv_deriv_Lp_bound`

The `L^{2p}` bound for the derivatives of the symmetrised inverse metric `symInvC c a b`, uniform
in the Galerkin truncation `N`, in the coefficient family `c`, in the multi-index `q` of
differentiation **and in the exponent** `p`.

The estimate is the classical sharp Sobolev statement

`q.length + n/2 - n/(2p) + 1 ≤ k  ⟹  ‖∂^q (reMat (seriesFunM c ·))⁻¹‖_{L^{2p}} ≤ C`,

where `C` may depend on `n, k, lam, B` but not on `p`, `q`, `N` or `c`.  The two analytic
ingredients are

* `Work.Diff.STE.flat.CSq_symInvC_le` (the Moser/composition bound): the level-`k` weighted `ℓ²`
  mass of the Fourier coefficients of `symInvC c a b` is bounded by a constant, uniformly in the
  data — this is the coefficient-side form of the Moser estimate for the matrix inverse;
* `Work.Diff.STE.flat.rnorm_seriesFun_uniform` (the sharp Sobolev embedding with a constant
  *uniform in the exponent*): `‖seriesFun γ‖_{L^{2p}} ≤ C (Σ_k ⟨k⟩^{2j}‖γ k‖²)^{1/2}` for every
  `p ≥ 1` and every `j ≥ n(1/2 - 1/(2p)) + 1/2`, with `C` depending only on the index type.

The assembly below (i) writes `symInvC c a b` as a Fourier series, (ii) applies the uniform sharp
Sobolev embedding to the level-`j` mass of the differentiated coefficients, and (iii) converts that
mass into the level-`k` mass using `dmulV`-monotonicity
(`Work.Diff.STE.flat.summable_wt_dmulV_le`).  The level `j` is chosen half-way between the sharp
threshold `n(1/2 - 1/(2p))` and the top level `k`.
-/

namespace Work.Diff.STE.flat

open MeasureTheory BigOperators
open Work.Diff.STE.Flat

noncomputable section

/-- **Smoothness and periodicity of the symmetrised inverse metric.**  Under box support, the
level-`k` energy bound and uniform ellipticity, each entry of the symmetrised inverse metric is
smooth and `1`-periodic.  (Both facts only need `sob n ≤ k`; the `n + 5` of `inv_jet_bound` is not
needed here.) -/
lemma symInvC_contDiff_periodic {n k : ℕ} (hσ : sob n ≤ k) {lam B : ℝ} (hB : 0 ≤ B)
    (hlam : 0 < lam) {N : ℕ} {c : (Fin n → ℤ) → MatC n}
    (hc : ∀ k' : Fin n → ℤ, k' ∉ box n N → c k' = 0)
    (hen : ENormSqFull k (seriesFunM c) ≤ B ^ 2)
    (hell : ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
      lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, reMat (seriesFunM c x) i j * v i * v j)
    (a b : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (symInvC c a b) ∧ Periodic1 (symInvC c a b) := by
  have hE : ∀ c' d' : Fin n, ContDiff ℝ (⊤ : ℕ∞) (invEntryFun n c c' d') ∧
      Periodic1 (invEntryFun n c c' d') :=
    fun c' d' => invJetSymm_invEntryFun_smooth (n := n) (s := k) (Bs := B)
      hB hσ hlam N c hc hen hell c' d'
  have hsym : ∀ a b : Fin n, symInvC c a b
      = (2 : ℂ)⁻¹ • (invEntryFun n c a b + invEntryFun n c b a) := by
    intro a b
    funext x
    rw [invEntryFun_eq n c a b, invEntryFun_eq n c b a]
    simp only [symInvC_apply, symInvR_apply, Pi.smul_apply, Pi.add_apply]
    push_cast
    ring
  refine ⟨?_, ?_⟩
  · rw [hsym a b]
    exact ((hE a b).1.add (hE b a).1).const_smul (2 : ℂ)⁻¹
  · rw [hsym a b]
    intro i x
    simp only [Pi.smul_apply, Pi.add_apply]
    rw [(hE a b).2 i x, (hE b a).2 i x]

/-- **The assembly of `Work.Diff.STE.flat.symInv_deriv_Lp_bound`.**  The two analytic pieces are
taken as explicit hypotheses, so that the assembly could be developed independently of them:

* `hCSQ` is the level-`k` coefficient bound for `symInvC` (the Moser/composition estimate),
* `hdmulV` is the `dmulV`-monotonicity of the weighted masses (which consumes one derivative order
  of the level). -/
theorem symInv_deriv_Lp_bound_of_pieces {n : ℕ} (hn : 1 ≤ n)
    (k : ℕ) (hk : Fintype.card (Fin n) + 4 < 2 * k)
    (lam : ℝ) (hlam : 0 < lam) (B : ℝ) (hB : 0 ≤ B)
    (hCSQ : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
        (∀ k' : Fin n → ℤ, k' ∉ box n N → c k' = 0) →
        ENormSqFull k (seriesFunM c) ≤ B ^ 2 →
        (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
          lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, reMat (seriesFunM c x) i j * v i * v j) →
        ∀ a b : Fin n, CSq k (fourierCoeff (fun y => symInvC c a b y)) ≤ C)
    (hdmulV : ∀ (q : List (Fin n)) (j : ℝ) (γ : (Fin n → ℤ) → ℂ),
        j + (q.length : ℝ) ≤ (k : ℝ) →
        Summable (fun m : Fin n → ℤ => (wt m) ^ k * ‖γ m‖ ^ 2) →
        Summable (fun m : Fin n → ℤ => (wt m) ^ j * ‖dmulV q γ m‖ ^ 2) ∧
          (∑' m : Fin n → ℤ, (wt m) ^ j * ‖dmulV q γ m‖ ^ 2)
            ≤ ((2 * Real.pi) ^ 2) ^ q.length
              * (∑' m : Fin n → ℤ, (wt m) ^ k * ‖γ m‖ ^ 2)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ) (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
        (∀ k' : Fin n → ℤ, k' ∉ Work.Diff.STE.Flat.box n N → c k' = 0) →
        Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM c) ≤ B ^ 2 →
        (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
          lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
            Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) i j * v i * v j) →
        ∀ (a b : Fin n) (q : List (Fin n)) (p : ℝ), 1 ≤ p →
          (q.length : ℝ) + (n : ℝ) / 2 - (n : ℝ) / (2 * p) + 1 ≤ (k : ℝ) →
          (∫ x in Work.Diff.STE.unitCube,
              ‖Work.Diff.STE.pdList q (fun y => Work.Diff.STE.flat.symInvC c a b y) x‖ ^ (2 * p))
            ^ (1 / (2 * p)) ≤ C := by
  classical
  obtain ⟨Csob, hCsob, hSob⟩ := rnorm_seriesFun_uniform (ι := Fin n)
  obtain ⟨Ccsq, hCcsq, hCSQ'⟩ := hCSQ
  set Cfin : ℝ := Csob * ((((2 * Real.pi) ^ 2) ^ (k - 1) * Ccsq)) ^ (1 / 2 : ℝ) with hCfindef
  refine ⟨Cfin, ?_, ?_⟩
  · rw [hCfindef]
    exact mul_nonneg hCsob (Real.rpow_nonneg (mul_nonneg (pow_nonneg (by positivity) _) hCcsq) _)
  intro N c hc hen hell a b q p hp hlev
  have hk' : n + 4 < 2 * k := by simpa using hk
  have hσ : sob n ≤ k := by
    have h := two_sob_le n
    omega
  -- the level-`k` coefficient bound for `symInvC`
  have hcsq : CSq k (fourierCoeff (fun y : Fin n → ℝ => symInvC c a b y)) ≤ Ccsq :=
    hCSQ' N c hc hen hell a b
  -- the function, its smoothness/periodicity and its Fourier series
  set f : (Fin n → ℝ) → ℂ := fun y => symInvC c a b y with hfdef
  have hfsm : ContDiff ℝ (⊤ : ℕ∞) f := by
    rw [hfdef]
    exact (symInvC_contDiff_periodic hσ hB hlam hc hen hell a b).1
  have hfper : Periodic1 f := by
    rw [hfdef]
    exact (symInvC_contDiff_periodic hσ hB hlam hc hen hell a b).2
  have hfd : ∀ K : ℕ, Summable (fun m : Fin n → ℤ =>
      (wt m) ^ K * ‖fourierCoeff f m‖ ^ 2) :=
    fun K => summable_weighted_fourierCoeff_of_contDiff f hfsm hfper K
  have hfl1 : ∀ K : ℕ, Summable (fun m : Fin n → ℤ =>
      (wt m) ^ K * ‖fourierCoeff f m‖) :=
    fun K => invJet_summable_moment_of_wt_sq _ hfd K
  have hFser : f = seriesFun (fourierCoeff f) :=
    funext fun x => (seriesFun_fourierCoeff f hfsm hfper x).symm
  have hpd : pdList q f = seriesFun (dmulV q (fourierCoeff f)) := by
    conv_lhs => rw [hFser]
    exact funext fun x => pdList_seriesFun q (fourierCoeff f) hfl1 x
  -- the level used for the sharp Sobolev embedding
  have hlev' : (q.length : ℝ) + (n : ℝ) * (1 / 2 - 1 / (2 * p)) + 1 ≤ (k : ℝ) := by
    have h1 : (n : ℝ) / 2 - (n : ℝ) / (2 * p) = (n : ℝ) * (1 / 2 - 1 / (2 * p)) := by ring
    linarith [hlev, h1]
  have hnjn : (0 : ℝ) ≤ (n : ℝ) * (1 / 2 - 1 / (2 * p)) := by
    have h2p : (2 : ℝ) ≤ 2 * p := by linarith
    have h1 : 1 / (2 * p) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2p
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
  set j : ℝ := ((n : ℝ) * (1 / 2 - 1 / (2 * p)) + ((k : ℝ) - (q.length : ℝ))) / 2 with hjdef
  have hjge : (Fintype.card (Fin n) : ℝ) * (1 / 2 - 1 / (2 * p)) + 1 / 2 ≤ j := by
    rw [hjdef]
    have hc : (Fintype.card (Fin n) : ℝ) = (n : ℝ) := by simp
    rw [hc]
    linarith
  have hjq : j + (q.length : ℝ) ≤ (k : ℝ) := by
    rw [hjdef]
    linarith
  -- the mass of the differentiated coefficients, at level `j`
  have hmass := hdmulV q j (fourierCoeff f) hjq (hfd k)
  -- the sharp Sobolev embedding, with a constant uniform in `p`
  have hsob := hSob p hp j hjge (dmulV q (fourierCoeff f)) hmass.1
  -- the order of differentiation does not exceed `k - 1`
  have hqk : q.length ≤ k - 1 := by
    have h : (q.length : ℝ) + 1 ≤ (k : ℝ) := by linarith [hlev', hnjn]
    have h1 : q.length + 1 ≤ k := by exact_mod_cast h
    omega
  have h2pi : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
  have hA0 : (0 : ℝ) ≤ ∑' m : Fin n → ℤ, (wt m) ^ j * ‖dmulV q (fourierCoeff f) m‖ ^ 2 :=
    tsum_nonneg fun m => mul_nonneg (Real.rpow_nonneg (le_of_lt (wt_pos m)) j) (sq_nonneg _)
  calc rnorm (2 * p) (pdList q f)
      = rnorm (2 * p) (seriesFun (dmulV q (fourierCoeff f))) := by rw [hpd]
    _ ≤ Csob * (∑' m : Fin n → ℤ,
          (wt m) ^ j * ‖dmulV q (fourierCoeff f) m‖ ^ 2) ^ (1 / 2 : ℝ) := hsob
    _ ≤ Csob * ((((2 * Real.pi) ^ 2) ^ q.length) * CSq k (fourierCoeff f)) ^ (1 / 2 : ℝ) := by
        refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hA0 ?_ (by norm_num)) hCsob
        simpa only [CSq] using hmass.2
    _ ≤ Csob * ((((2 * Real.pi) ^ 2) ^ (k - 1)) * Ccsq) ^ (1 / 2 : ℝ) := by
        refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
          (mul_nonneg (pow_nonneg (by positivity) _) (CSq_nonneg' k _)) ?_ (by norm_num)) hCsob
        exact mul_le_mul (pow_le_pow_right₀ h2pi hqk) hcsq (CSq_nonneg' k _)
          (pow_nonneg (by positivity) _)
    _ = Cfin := by rw [hCfindef]

/-- **`Work.Diff.STE.flat.symInv_deriv_Lp_bound`.** -/
theorem symInv_deriv_Lp_bound {n : ℕ} (hn : 1 ≤ n)
    (k : ℕ) (hk : Fintype.card (Fin n) + 4 < 2 * k)
    (lam : ℝ) (hlam : 0 < lam) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ) (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
        (∀ k' : Fin n → ℤ, k' ∉ Work.Diff.STE.Flat.box n N → c k' = 0) →
        Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM c) ≤ B ^ 2 →
        (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
          lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
            Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) i j * v i * v j) →
        ∀ (a b : Fin n) (q : List (Fin n)) (p : ℝ), 1 ≤ p →
          (q.length : ℝ) + (n : ℝ) / 2 - (n : ℝ) / (2 * p) + 1 ≤ (k : ℝ) →
          (∫ x in Work.Diff.STE.unitCube,
              ‖Work.Diff.STE.pdList q (fun y => Work.Diff.STE.flat.symInvC c a b y) x‖ ^ (2 * p))
            ^ (1 / (2 * p)) ≤ C := by
  have hσ : sob n ≤ k := by
    have h := two_sob_le n
    have hk' : n + 4 < 2 * k := by simpa using hk
    omega
  exact symInv_deriv_Lp_bound_of_pieces hn k hk lam hlam B hB
    (CSq_symInvC_le hn k hσ lam hlam B hB)
    (fun q j γ hjq hγ => summable_wt_dmulV_le q j k γ hjq hγ)

end

end Work.Diff.STE.flat

import Mathlib
import Submission.Work.Diff.STE.flat.level_aux
import Submission.Work.Diff.STE.flat.CSq_comp_vecarg_le_local
import Submission.Work.Diff.STE.flat.inv_jet_defs
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.ENormSq_seriesFun_le
import Submission.Work.Diff.STE.CSq_le_ENormSq_seriesFun
import Submission.Work.Diff.STE.norm_seriesFun_le
import Submission.Work.Diff.STE.summable_wt_zpow
import Submission.Work.Diff.STE.pd_seriesFun
import Submission.Work.Diff.EXT.contMDiffAt_matrix_inv
import Submission.Work.Diff.STE.flat.det_ne_zero_of_quadForm_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

set_option maxHeartbeats 2000000

open Work.Diff.STE.Flat

open MeasureTheory BigOperators

section Aids

variable {n s : ℕ}

/-- Monotonicity of `CSq` in the level (the weight `⟨k⟩² ≥ 1`). -/
lemma invJet_CSq_mono_le {ι : Type*} [Fintype ι] [DecidableEq ι] (c : (ι → ℤ) → ℂ) {k m : ℕ}
    (hkm : k ≤ m) (h : Summable (fun a : ι → ℤ => (wt a) ^ m * ‖c a‖ ^ 2)) :
    CSq k c ≤ CSq m c := by
  rw [CSq, CSq]
  refine Summable.tsum_le_tsum (fun a => ?_) ?_ h
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (wt_one_le a) hkm) (sq_nonneg _)
  · refine Summable.of_nonneg_of_le
      (fun a => mul_nonneg (pow_nonneg (wt_pos a).le k) (sq_nonneg _)) (fun a => ?_) h
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (wt_one_le a) hkm) (sq_nonneg _)

/-- Summability of the level-`k` weighted square from the level-`m` one, for `k ≤ m`. -/
lemma invJet_summable_wt_sq_mono {ι : Type*} [Fintype ι] [DecidableEq ι] (c : (ι → ℤ) → ℂ) {k m : ℕ}
    (hkm : k ≤ m) (h : Summable (fun a : ι → ℤ => (wt a) ^ m * ‖c a‖ ^ 2)) :
    Summable (fun a : ι → ℤ => (wt a) ^ k * ‖c a‖ ^ 2) :=
  Summable.of_nonneg_of_le (fun a => mul_nonneg (pow_nonneg (wt_pos a).le k) (sq_nonneg _))
    (fun a => mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (wt_one_le a) hkm) (sq_nonneg _)) h

/-- Weighted `ℓ¹`-moments from weighted `ℓ²`-bounds: summability of `⟨k⟩^N ‖d k‖` follows from
summability of `⟨k⟩^K ‖d k‖²` at all levels `K`. -/
lemma invJet_summable_moment_of_wt_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (d : (ι → ℤ) → ℂ)
    (hd : ∀ K : ℕ, Summable (fun k : ι → ℤ => (wt k) ^ K * ‖d k‖ ^ 2)) (N : ℕ) :
    Summable (fun k : ι → ℤ => (wt k) ^ N * ‖d k‖) := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, Fintype.card ι < 2 * K := ⟨Fintype.card ι + 1, by omega⟩
  have h2 : Summable (fun k : ι → ℤ => (wt k) ^ K *
      ‖(fun k : ι → ℤ => ((wt k) ^ N : ℂ) * d k) k‖ ^ 2) := by
    refine (hd (K + 2 * N)).congr (fun k => ?_)
    have h1 : ((wt k) ^ N) ^ 2 = (wt k) ^ (2 * N) := by rw [← pow_mul, Nat.mul_comm]
    rw [norm_mul, ← Complex.ofReal_pow, Complex.norm_of_nonneg (pow_nonneg (wt_pos k).le N),
      mul_pow, h1, pow_add]
    ring
  have h3 := Work.Diff.STE.summable_norm_of_CSq (ι := ι) K hK
    (fun k : ι → ℤ => ((wt k) ^ N : ℂ) * d k) h2
  exact h3.congr (fun k => by
    rw [norm_mul, ← Complex.ofReal_pow, Complex.norm_of_nonneg (pow_nonneg (wt_pos k).le N)])

/-- For a box-supported matrix coefficient family, the weighted `ℓ²`-norm of any single entry
family at any level is controlled by the full energy at the same level, with a constant that is
uniform in the truncation `N` and in the coefficient family `c`. -/
lemma invJet_CSq_entry_le_uniform {n : ℕ} (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
      (∀ k' : Fin n → ℤ, k' ∉ box n N → c k' = 0) → ∀ i j : Fin n,
      CSq k (fun m : Fin n → ℤ => c m i j) ≤ C * ENormSqFull k (seriesFunM c) := by
  obtain ⟨C2, hC2, h2⟩ := Work.Diff.STE.CSq_le_ENormSq_seriesFun (ι := Fin n) k
  refine ⟨C2, hC2, fun N c hc i j => ?_⟩
  have hmom : ∀ M : ℕ, Summable (fun l : Fin n → ℤ => (wt l) ^ M * ‖c l i j‖) :=
    fun M => summable_moment_box c hc i j M
  refine (h2 (fun l => c l i j) hmom).trans (mul_le_mul_of_nonneg_left ?_ hC2)
  have h1 : ENormSq k (seriesFun (fun l : Fin n → ℤ => c l i j))
      ≤ ENormSqM k (seriesFunM c) := ENormSq_le_ENormSqM (seriesFunM c) i j
  have h1' : ENormSq 0 (seriesFun (fun l : Fin n → ℤ => c l i j))
      ≤ ENormSqM 0 (seriesFunM c) := ENormSq_le_ENormSqM (seriesFunM c) i j
  calc ENormSq k (seriesFun (fun l : Fin n → ℤ => c l i j))
        + ENormSq 0 (seriesFun (fun l : Fin n → ℤ => c l i j))
      ≤ ENormSqM k (seriesFunM c) + ENormSqM 0 (seriesFunM c) := add_le_add h1 h1'
    _ = ENormSqFull k (seriesFunM c) := rfl

/-- **Sup bound for the entry vector.**  The entries of the matrix series of a box-supported
coefficient family satisfying the level-`s` energy bound `ENormSqFull s ≤ Bs²` are bounded by a
constant times `1 + Bs`, uniformly in the truncation and in the family. -/
lemma invJet_entryVec_sup_le {n s : ℕ} {Bs : ℝ} (hBs : 0 ≤ Bs) (hσs : sob n ≤ s) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
      (∀ k : Fin n → ℤ, k ∉ box n N → c k = 0) →
      ENormSqFull s (seriesFunM c) ≤ Bs ^ 2 →
      ∀ (x : Fin n → ℝ) (i : Fin (Fintype.card (Fin n × Fin n))),
        ‖seriesFun (fun k => invCvec n c k i) x‖ ≤ K * (1 + Bs) := by
  obtain ⟨C0, hC0, h0⟩ := Work.Diff.STE.norm_seriesFun_le (ι := Fin n) (sob n)
    (by simpa using n_lt_two_sob n)
  obtain ⟨C1, hC1, h1⟩ := invJet_CSq_entry_le_uniform (n := n) s
  refine ⟨C0 * Real.sqrt C1, by positivity, ?_⟩
  intro N c hc hen x i
  have hmom : ∀ M : ℕ, Summable (fun k : Fin n → ℤ => (wt k) ^ M * ‖c k (((invEv n).symm i).1)
      (((invEv n).symm i).2)‖) :=
    fun M => summable_moment_box c hc (((invEv n).symm i).1) (((invEv n).symm i).2) M
  have hsumσ : Summable (fun k : Fin n → ℤ => (wt k) ^ (sob n) * ‖invCvec n c k i‖ ^ 2) := by
    simpa only [invCvec_apply] using
      (Work.Diff.STE.summable_wt_pow_mul_norm_sq
        (fun k : Fin n → ℤ => c k (((invEv n).symm i).1) (((invEv n).symm i).2)) hmom (sob n))
  have hsums : Summable (fun k : Fin n → ℤ => (wt k) ^ s * ‖invCvec n c k i‖ ^ 2) := by
    simpa only [invCvec_apply] using
      (Work.Diff.STE.summable_wt_pow_mul_norm_sq
        (fun k : Fin n → ℤ => c k (((invEv n).symm i).1) (((invEv n).symm i).2)) hmom s)
  have hCsq : CSq (sob n) (fun k => invCvec n c k i) ≤ C1 * ENormSqFull s (seriesFunM c) := by
    calc CSq (sob n) (fun k => invCvec n c k i)
        ≤ CSq s (fun k => invCvec n c k i) := invJet_CSq_mono_le _ hσs hsums
      _ = CSq s (fun k => c k (((invEv n).symm i).1) (((invEv n).symm i).2)) := by
          congr 1
      _ ≤ C1 * ENormSqFull s (seriesFunM c) :=
          h1 N c hc (((invEv n).symm i).1) (((invEv n).symm i).2)
  calc ‖seriesFun (fun k => invCvec n c k i) x‖
      ≤ C0 * Real.sqrt (CSq (sob n) (fun k => invCvec n c k i)) := h0 _ hsumσ x
    _ ≤ C0 * Real.sqrt (C1 * ENormSqFull s (seriesFunM c)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hCsq) hC0
    _ ≤ C0 * Real.sqrt (C1 * Bs ^ 2) := by
        refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hC0
        exact mul_le_mul_of_nonneg_left hen hC1
    _ = C0 * Real.sqrt C1 * Bs := by
        rw [Real.sqrt_mul hC1, Real.sqrt_sq hBs]
        ring
    _ ≤ C0 * Real.sqrt C1 * (1 + Bs) := by
        have : (0:ℝ) ≤ C0 * Real.sqrt C1 := mul_nonneg hC0 (Real.sqrt_nonneg _)
        nlinarith

/-- **Membership in the elliptic set.**  Under the energy bound and the uniform ellipticity
hypothesis, the entry vector of the matrix series lies in the compact elliptic set. -/
lemma invJet_entryVec_mem_elliptic {n s : ℕ} {Bs lam : ℝ} (hBs : 0 ≤ Bs) (hσs : sob n ≤ s) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
      (∀ k : Fin n → ℤ, k ∉ box n N → c k = 0) →
      ENormSqFull s (seriesFunM c) ≤ Bs ^ 2 →
      (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, reMat (seriesFunM c x) i j * v i * v j) →
      ∀ x : Fin n → ℝ,
        (fun i => seriesFun (fun k => invCvec n c k i) x) ∈ invElliptic n lam ρ := by
  obtain ⟨K, hK, hK'⟩ := invJet_entryVec_sup_le (n := n) (s := s) (Bs := Bs) hBs hσs
  refine ⟨K * (1 + Bs), by positivity, fun N c hc hen hell x => ?_⟩
  refine ⟨fun i => hK' N c hc hen x i, ?_⟩
  intro v
  rw [reMatZ_invCvec]
  exact hell x v

end Aids

section Geometry

/-- The `(i, j)`-entry of the entry vector is a continuous linear (in particular smooth) function
of the entry vector. -/
@[fun_prop] lemma invJet_contDiff_reMatZ_entry {n : ℕ} (i j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin (Fintype.card (Fin n × Fin n)) → ℂ => reMatZ z i j) := by
  have h : (fun z : Fin (Fintype.card (Fin n × Fin n)) → ℂ => reMatZ z i j)
      = fun z => Complex.reCLM.comp
          (ContinuousLinearMap.proj
            (φ := fun _ : Fin (Fintype.card (Fin n × Fin n)) => ℂ) (invEv n (i, j))) z := by
    funext z; rfl
  rw [h]
  exact (Complex.reCLM.comp (ContinuousLinearMap.proj
    (φ := fun _ : Fin (Fintype.card (Fin n × Fin n)) => ℂ) (invEv n (i, j)))).contDiff

/-- The entry vector map `z ↦ reMatZ z` is smooth (as a map into the Pi-type of matrices). -/
lemma invJet_contDiff_reMatZ {n : ℕ} :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin (Fintype.card (Fin n × Fin n)) → ℂ => reMatZ z) := by
  rw [contDiff_pi]; intro i; rw [contDiff_pi]; intro j
  exact invJet_contDiff_reMatZ_entry i j

/-- The determinant of the real part of the entry vector is smooth. -/
lemma invJet_contDiff_detZ {n : ℕ} :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin (Fintype.card (Fin n × Fin n)) → ℂ =>
      Matrix.det (Matrix.of (reMatZ z))) :=
  Work.Diff.EXT.contDiff_matrix_det_pi.comp invJet_contDiff_reMatZ

/-- The open set of non-singular entry vectors is open. -/
lemma invJet_isOpen_invNonsing {n : ℕ} : IsOpen (invNonsing n) := by
  have hcont : Continuous (fun z : Fin (Fintype.card (Fin n × Fin n)) → ℂ =>
      Matrix.det (Matrix.of (reMatZ z))) := invJet_contDiff_detZ.continuous
  have heq : invNonsing n
      = (fun z : Fin (Fintype.card (Fin n × Fin n)) → ℂ =>
          Matrix.det (Matrix.of (reMatZ z))) ⁻¹' {x : ℝ | x ≠ 0} := rfl
  rw [heq]
  exact hcont.isOpen_preimage _ isClosed_singleton.isOpen_compl

/-- The ellipticity condition is closed in the entry vector. -/
lemma invJet_isClosed_invEllipticCond {n : ℕ} (lam : ℝ) :
    IsClosed {z : Fin (Fintype.card (Fin n × Fin n)) → ℂ |
      ∀ v : Fin n → ℝ, lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, reMatZ z i j * v i * v j} := by
  have heq : {z : Fin (Fintype.card (Fin n × Fin n)) → ℂ |
        ∀ v : Fin n → ℝ, lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, reMatZ z i j * v i * v j}
      = ⋂ (v : Fin n → ℝ), {z : Fin (Fintype.card (Fin n × Fin n)) → ℂ |
          lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, reMatZ z i j * v i * v j} := by
    ext z
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
  rw [heq]
  refine isClosed_iInter (fun v => ?_)
  have hcont : Continuous (fun z : Fin (Fintype.card (Fin n × Fin n)) → ℂ =>
      ∑ i, ∑ j, reMatZ z i j * v i * v j) := by
    have h1 : ∀ i j : Fin n, Continuous (fun z : Fin (Fintype.card (Fin n × Fin n)) → ℂ =>
        reMatZ z i j * v i * v j) := by
      intro i j
      exact ((invJet_contDiff_reMatZ_entry i j).continuous.mul continuous_const).mul continuous_const
    exact continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => h1 i j))
  have heq2 : {z : Fin (Fintype.card (Fin n × Fin n)) → ℂ |
        lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, reMatZ z i j * v i * v j}
      = (fun z : Fin (Fintype.card (Fin n × Fin n)) → ℂ =>
          ∑ i, ∑ j, reMatZ z i j * v i * v j) ⁻¹'
        (Set.Ici (lam * ∑ i, (v i) ^ 2)) := rfl
  rw [heq2]
  exact isClosed_Ici.preimage hcont

/-- The elliptic set is compact. -/
lemma invJet_isCompact_invElliptic {n : ℕ} (lam ρ : ℝ) : IsCompact (invElliptic n lam ρ) := by
  have heq : invElliptic n lam ρ
      = (Set.pi Set.univ (fun _ : Fin (Fintype.card (Fin n × Fin n)) =>
            Metric.closedBall (0 : ℂ) ρ))
        ∩ {z : Fin (Fintype.card (Fin n × Fin n)) → ℂ |
            ∀ v : Fin n → ℝ, lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, reMatZ z i j * v i * v j} := by
    ext z
    simp only [invElliptic, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_pi, Set.mem_univ,
      true_implies, Metric.mem_closedBall, dist_eq_norm, sub_zero]
  rw [heq]
  exact (isCompact_univ_pi (fun _ => isCompact_closedBall (0 : ℂ) ρ)).inter_right
    (invJet_isClosed_invEllipticCond lam)

/-- The elliptic set is contained in the set of non-singular entry vectors. -/
lemma invJet_invElliptic_subset_invNonsing {n : ℕ} {lam ρ : ℝ} (hlam : 0 < lam) :
    invElliptic n lam ρ ⊆ invNonsing n := by
  intro z hz
  have h : ∀ v : Fin n → ℝ, lam * ∑ i, (v i) ^ 2
      ≤ ∑ i, ∑ j, (Matrix.of (reMatZ z)) i j * v i * v j := by
    intro v
    simpa only [Matrix.of_apply] using hz.2 v
  exact det_ne_zero_of_quadForm_le (Matrix.of (reMatZ z)) hlam h

/-- **Smoothness of the inverse entry on the non-singular locus.** -/
lemma invJet_contDiffOn_invPhi {n : ℕ} (c' d' : Fin n) :
    ContDiffOn ℝ (⊤ : ℕ∞) (invPhi n c' d') (invNonsing n) := by
  have hreal : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => ((Matrix.of (reMatZ z) : Matrix (Fin n) (Fin n) ℝ)⁻¹) c' d') (invNonsing n) := by
    have hmain : (fun z => ((Matrix.of (reMatZ z) : Matrix (Fin n) (Fin n) ℝ)⁻¹) c' d')
        = fun z => (Matrix.det (Matrix.of (reMatZ z) : Matrix (Fin n) (Fin n) ℝ))⁻¹ *
            (Matrix.adjugate (Matrix.of (reMatZ z) : Matrix (Fin n) (Fin n) ℝ)) c' d' := by
      funext z
      rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
    rw [hmain]
    have hdet : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : Fin (Fintype.card (Fin n × Fin n)) → ℂ =>
          Matrix.det (Matrix.of (reMatZ z) : Matrix (Fin n) (Fin n) ℝ))
        (invNonsing n) := invJet_contDiff_detZ.contDiffOn
    have hadj : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : Fin (Fintype.card (Fin n × Fin n)) → ℂ =>
          (Matrix.adjugate (Matrix.of (reMatZ z) : Matrix (Fin n) (Fin n) ℝ)) c' d')
        (invNonsing n) :=
      ((Work.Diff.EXT.contDiff_matrix_adjugate_entry_pi c' d').comp invJet_contDiff_reMatZ).contDiffOn
    exact (hdet.inv (fun z hz => hz)).mul hadj
  have hcast : invPhi n c' d'
      = Complex.ofRealCLM ∘ (fun z =>
          ((Matrix.of (reMatZ z) : Matrix (Fin n) (Fin n) ℝ)⁻¹) c' d') := by
    funext z; rw [invPhi_apply, matInvEntry]; rfl
  rw [hcast]
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn hreal

end Geometry

section Series

variable {n : ℕ}

/-- The entry vector of the matrix series of a box-supported coefficient family is smooth. -/
lemma invJet_contDiff_invCvec_series {N : ℕ} (c : (Fin n → ℤ) → MatC n)
    (hc : ∀ k : Fin n → ℤ, k ∉ box n N → c k = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ =>
      fun i : Fin (Fintype.card (Fin n × Fin n)) =>
        Work.Diff.STE.seriesFun (fun k => invCvec n c k i) x) := by
  rw [contDiff_pi]; intro i
  refine Work.Diff.STE.contDiff_seriesFun _ (fun M => ?_)
  simpa only [invCvec_apply] using
    summable_moment_box c hc (((invEv n).symm i).1) (((invEv n).symm i).2) M

/-- The entry vector of the matrix series of a coefficient family is `1`-periodic. -/
lemma invJet_periodic1_invCvec_series (c : (Fin n → ℤ) → MatC n) :
    Work.Diff.STE.Periodic1 (fun x : Fin n → ℝ =>
      fun i : Fin (Fintype.card (Fin n × Fin n)) =>
        Work.Diff.STE.seriesFun (fun k => invCvec n c k i) x) := by
  intro i x
  funext j
  exact periodic1_seriesFun _ i x

end Series

section Core

variable {n s : ℕ}

/-- `1 ≤ (2π)²`, the base of the spectral weights. -/
lemma invJet_one_le_two_pi_sq : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]

/-- The `L²` bound for the jets of a Fourier series, with the explicit constant `((2π)²)^j`
(no hypothesis on the coefficient family beyond the moment summability needed to differentiate
term by term). -/
lemma invJet_integral_pdVec_seriesFun_le (d : (Fin n → ℤ) → ℂ)
    (hd : ∀ K : ℕ, Summable (fun k : Fin n → ℤ => (wt k) ^ K * ‖d k‖)) (j : ℕ)
    (l : Fin j → Fin n) :
    ∫ x in unitCube (ι := Fin n), ‖pdVec j l (seriesFun d) x‖ ^ 2
      ≤ ((2 * Real.pi) ^ 2) ^ j * CSq j d := by
  have hfun : pdVec j l (seriesFun d) = seriesFun (dmulV (List.ofFn l) d) :=
    funext (pdList_seriesFun (List.ofFn l) d hd)
  rw [hfun, ens_integral_normSq_seriesFun (dmulV (List.ofFn l) d)
    (by simpa using summable_dmulV (List.ofFn l) d hd 0)]
  simpa only [List.length_ofFn] using tsum_normSq_dmulV_le (List.ofFn l) d hd

/-- **Sup bound for the jets of a Fourier series**, with the explicit constants: if the coefficient
family `d` has all weighted `ℓ¹`-moments and `CSq s d ≤ Y (1+Bs)²`, then the jets of order
`j ≤ s - sob n` of `seriesFun d` are bounded by `Csup (2π)^s √Y (1+Bs)`. -/
lemma invJet_sup_pdVec_seriesFun_le {n s : ℕ} (hσs : sob n ≤ s) {d : (Fin n → ℤ) → ℂ}
    (hd1 : ∀ K : ℕ, Summable (fun k : Fin n → ℤ => (wt k) ^ K * ‖d k‖))
    {Csup Y Bs : ℝ} (hCsupnn : 0 ≤ Csup)
    (hCsup : ∀ (c : (Fin n → ℤ) → ℂ),
      Summable (fun k : Fin n → ℤ => (wt k) ^ (sob n) * ‖c k‖ ^ 2) →
      ∀ x : Fin n → ℝ, ‖seriesFun c x‖ ≤ Csup * Real.sqrt (CSq (sob n) c))
    (hY : 0 ≤ Y) (hBs : 0 ≤ Bs) (hcsq : CSq s d ≤ Y * (1 + Bs) ^ 2) :
    ∀ (j : ℕ) (hj : j + sob n ≤ s) (l : Fin j → Fin n) (x : Fin n → ℝ),
      ‖pdVec j l (seriesFun d) x‖ ≤ Csup * (2 * Real.pi) ^ s * Real.sqrt Y * (1 + Bs) := by
  intro j hj l x
  have hd2 : ∀ K : ℕ, Summable (fun k : Fin n → ℤ => (wt k) ^ K * ‖d k‖ ^ 2) :=
    fun K => Work.Diff.STE.summable_wt_pow_mul_norm_sq d hd1 K
  have h1 : pdVec j l (seriesFun d) = seriesFun (dmulV (List.ofFn l) d) :=
    funext (pdList_seriesFun (List.ofFn l) d hd1)
  rw [h1]
  have hsumm : Summable (fun k : Fin n → ℤ =>
      (wt k) ^ (sob n) * ‖dmulV (List.ofFn l) d k‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (pow_nonneg (wt_pos k).le _) (sq_nonneg _))
      (fun k => ?_) ((hd2 (sob n + j)).mul_left (((2 * Real.pi) ^ 2) ^ j))
    have hpt := mul_le_mul_of_nonneg_left (norm_sq_dmulV_le (List.ofFn l) d k)
      (pow_nonneg (wt_pos k).le (sob n))
    rw [List.length_ofFn] at hpt
    calc (wt k) ^ (sob n) * ‖dmulV (List.ofFn l) d k‖ ^ 2
        ≤ (wt k) ^ (sob n) * (((2 * Real.pi) ^ 2 * wt k) ^ j * ‖d k‖ ^ 2) := hpt
      _ = ((2 * Real.pi) ^ 2) ^ j * ((wt k) ^ (sob n + j) * ‖d k‖ ^ 2) := by
          rw [mul_pow, pow_add]; ring
  have hCsq : CSq (sob n) (dmulV (List.ofFn l) d) ≤ ((2 * Real.pi) ^ 2) ^ s * (Y * (1 + Bs) ^ 2) := by
    refine (CSq_dmulV_le (sob n) (List.ofFn l) d hd1).trans ?_
    rw [List.length_ofFn]
    have hmono : CSq (sob n + j) d ≤ CSq s d := invJet_CSq_mono_le d (by omega) (hd2 s)
    calc ((2 * Real.pi) ^ 2) ^ j * CSq (sob n + j) d
        ≤ ((2 * Real.pi) ^ 2) ^ j * CSq s d := mul_le_mul_of_nonneg_left hmono (by positivity)
      _ ≤ ((2 * Real.pi) ^ 2) ^ j * (Y * (1 + Bs) ^ 2) :=
          mul_le_mul_of_nonneg_left hcsq (by positivity)
      _ ≤ ((2 * Real.pi) ^ 2) ^ s * (Y * (1 + Bs) ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact pow_le_pow_right₀ invJet_one_le_two_pi_sq (by omega)
  have hsqrt : Real.sqrt (CSq (sob n) (dmulV (List.ofFn l) d))
      ≤ (2 * Real.pi) ^ s * Real.sqrt Y * (1 + Bs) := by
    refine (Real.sqrt_le_sqrt hCsq).trans ?_
    have hsq : ((2 * Real.pi) ^ 2) ^ s = ((2 * Real.pi) ^ s) ^ 2 := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [hsq, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), Real.sqrt_mul hY,
      Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 1 + Bs)]
    rw [mul_assoc]
  calc ‖seriesFun (dmulV (List.ofFn l) d) x‖
      ≤ Csup * Real.sqrt (CSq (sob n) (dmulV (List.ofFn l) d)) := hCsup _ hsumm x
    _ ≤ Csup * ((2 * Real.pi) ^ s * Real.sqrt Y * (1 + Bs)) :=
        mul_le_mul_of_nonneg_left hsqrt hCsupnn
    _ = Csup * (2 * Real.pi) ^ s * Real.sqrt Y * (1 + Bs) := by ring

/-- **The `L²` bound for the jets of a Fourier series up to order `s`. -/
lemma invJet_int_pdVec_seriesFun_le {n s : ℕ} {d : (Fin n → ℤ) → ℂ}
    (hd1 : ∀ K : ℕ, Summable (fun k : Fin n → ℤ => (wt k) ^ K * ‖d k‖))
    {Y Bs : ℝ} (hY : 0 ≤ Y) (hcsq : CSq s d ≤ Y * (1 + Bs) ^ 2) :
    ∀ (j : ℕ) (hj : j ≤ s) (l : Fin j → Fin n),
      ∫ x in unitCube (ι := Fin n), ‖pdVec j l (seriesFun d) x‖ ^ 2
        ≤ ((2 * Real.pi) ^ 2) ^ s * Y * (1 + Bs) ^ 2 := by
  intro j hj l
  refine (invJet_integral_pdVec_seriesFun_le d hd1 j l).trans ?_
  have h2 : CSq j d ≤ CSq s d :=
    invJet_CSq_mono_le d hj (Work.Diff.STE.summable_wt_pow_mul_norm_sq d hd1 s)
  calc ((2 * Real.pi) ^ 2) ^ j * CSq j d
      ≤ ((2 * Real.pi) ^ 2) ^ j * CSq s d := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ ((2 * Real.pi) ^ 2) ^ j * (Y * (1 + Bs) ^ 2) := mul_le_mul_of_nonneg_left hcsq (by positivity)
    _ ≤ ((2 * Real.pi) ^ 2) ^ s * (Y * (1 + Bs) ^ 2) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact pow_le_pow_right₀ invJet_one_le_two_pi_sq hj
    _ = ((2 * Real.pi) ^ 2) ^ s * Y * (1 + Bs) ^ 2 := by ring

/-- **The `L²` bound for the top-order jets.** -/
lemma invJet_int_pdVec_seriesFun_succ_le {n s : ℕ} {d : (Fin n → ℤ) → ℂ}
    (hd1 : ∀ K : ℕ, Summable (fun k : Fin n → ℤ => (wt k) ^ K * ‖d k‖))
    {Y : ℝ} (hcsq : CSq (s + 1) d ≤ Y) :
    ∀ (l : Fin (s + 1) → Fin n),
      ∫ x in unitCube (ι := Fin n), ‖pdVec (s + 1) l (seriesFun d) x‖ ^ 2
        ≤ ((2 * Real.pi) ^ 2) ^ (s + 1) * Y := by
  intro l
  exact (invJet_integral_pdVec_seriesFun_le d hd1 (s + 1) l).trans
    (mul_le_mul_of_nonneg_left hcsq (by positivity))

end Core

theorem inv_jet_bound {n s : ℕ} (hn : 1 ≤ n) (hs : n + 5 ≤ s)
    (lam : ℝ) (hlam : 0 < lam) (Bs : ℝ) (hBs : 0 ≤ Bs) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
      (∀ k : Fin n → ℤ, k ∉ Work.Diff.STE.Flat.box n N → c k = 0) →
      Work.Diff.STE.Flat.ENormSqFull s (Work.Diff.STE.Flat.seriesFunM c) ≤ Bs ^ 2 →
      (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
          Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) i j * v i * v j) →
      (∀ (c' d' : Fin n) (j : ℕ) (hj : j + Work.Diff.STE.flat.sob n ≤ s)
          (l : Fin j → Fin n) (x : Fin n → ℝ),
        ‖Work.Diff.STE.pdVec j l (fun y =>
          (((Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c y))⁻¹) c' d' : ℂ)) x‖
          ≤ C * (1 + Bs))
      ∧ (∀ (c' d' : Fin n) (j : ℕ) (hj : j ≤ s) (l : Fin j → Fin n),
        ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
          ‖Work.Diff.STE.pdVec j l (fun y =>
            (((Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c y))⁻¹) c' d' : ℂ)) x‖ ^ 2
          ≤ C * (1 + Bs) ^ 2)
      ∧ (∀ (c' d' : Fin n) (l : Fin (s + 1) → Fin n),
        ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
          ‖Work.Diff.STE.pdVec (s + 1) l (fun y =>
            (((Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c y))⁻¹) c' d' : ℂ)) x‖ ^ 2
          ≤ C * (1 + Bs) ^ 2
            * (1 + Work.Diff.STE.Flat.ENormSqFull (s + 1) (Work.Diff.STE.Flat.seriesFunM c))) := by
  classical
  have hσs : sob n ≤ s := by have h := two_sob_le n; omega
  have hσn : Fintype.card (Fin n) < 2 * sob n := by simpa using n_lt_two_sob n
  obtain ⟨Csup, hCsup, hCsup'⟩ := Work.Diff.STE.norm_seriesFun_le (ι := Fin n) (sob n) hσn
  obtain ⟨Kρ, hKρ, hKρ'⟩ := invJet_entryVec_sup_le (n := n) (s := s) (Bs := Bs) hBs hσs
  obtain ⟨Ce, hCe, hCe'⟩ := invJet_CSq_entry_le_uniform (n := n) s
  obtain ⟨Ce1, hCe1, hCe1'⟩ := invJet_CSq_entry_le_uniform (n := n) (s + 1)
  set M : ℝ := (Fintype.card (Fin n × Fin n) : ℝ) with hMdef
  have hMnn : 0 ≤ M := by rw [hMdef]; positivity
  set ρ : ℝ := Kρ * (1 + Bs) with hρdef
  have hρnn : 0 ≤ ρ := by rw [hρdef]; positivity
  set Bc : ℝ := Real.sqrt (M * Ce) * (1 + Bs) with hBcdef
  have hBcnn : 0 ≤ Bc := by rw [hBcdef]; positivity
  have hcmp : ∀ cd : Fin n × Fin n, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (c : (Fin n → ℤ) → (Fin (Fintype.card (Fin n × Fin n)) → ℂ)),
        (∀ M' : ℕ, Summable (fun k : Fin n → ℤ => (wt k) ^ M' * ‖c k‖)) →
        (∑ i : Fin (Fintype.card (Fin n × Fin n)), CSq (sob n) (fun k => c k i)) ≤ Bc ^ 2 →
        (∀ x : Fin n → ℝ, (fun i => seriesFun (fun k => c k i) x) ∈ invElliptic n lam ρ) →
        CSq s (fourierCoeff (fun x => invPhi n cd.1 cd.2
            (fun i => seriesFun (fun k => c k i) x)))
          ≤ C * (1 + ∑ i : Fin (Fintype.card (Fin n × Fin n)), CSq s (fun k => c k i)) ∧
        CSq (s + 1) (fourierCoeff (fun x => invPhi n cd.1 cd.2
            (fun i => seriesFun (fun k => c k i) x)))
          ≤ C * (1 + ∑ i : Fin (Fintype.card (Fin n × Fin n)), CSq (s + 1) (fun k => c k i)) := by
    intro cd
    obtain ⟨C1, hC1, hC1'⟩ := CSq_comp_vecarg_le_local (ι := Fin n)
      (m := Fintype.card (Fin n × Fin n)) s (sob n) hσn hσs (invPhi n cd.1 cd.2) (invNonsing n)
      invJet_isOpen_invNonsing (invJet_contDiffOn_invPhi cd.1 cd.2) (invElliptic n lam ρ)
      (invJet_isCompact_invElliptic lam ρ) (invJet_invElliptic_subset_invNonsing hlam) Bc hBcnn
    obtain ⟨C2, hC2, hC2'⟩ := CSq_comp_vecarg_le_local (ι := Fin n)
      (m := Fintype.card (Fin n × Fin n)) (s + 1) (sob n) hσn (by omega) (invPhi n cd.1 cd.2)
      (invNonsing n) invJet_isOpen_invNonsing (invJet_contDiffOn_invPhi cd.1 cd.2) (invElliptic n lam ρ)
      (invJet_isCompact_invElliptic lam ρ) (invJet_invElliptic_subset_invNonsing hlam) Bc hBcnn
    refine ⟨max C1 C2, le_max_of_le_left hC1, fun c hmom hB2 hKc => ⟨?_, ?_⟩⟩
    · exact (hC1' c hmom hB2 hKc).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by
          have h : (0 : ℝ) ≤ ∑ i : Fin (Fintype.card (Fin n × Fin n)), CSq s (fun k => c k i) :=
            Finset.sum_nonneg (fun i _ => CSq_nonneg' s _)
          linarith))
    · exact (hC2' c hmom hB2 hKc).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (by
          have h : (0 : ℝ) ≤ ∑ i : Fin (Fintype.card (Fin n × Fin n)), CSq (s + 1) (fun k => c k i) :=
            Finset.sum_nonneg (fun i _ => CSq_nonneg' (s + 1) _)
          linarith))
  choose Cf hCf using hcmp
  set Cfs : ℝ := Finset.sup' (Finset.univ : Finset (Fin n × Fin n))
      ⟨(⟨0, hn⟩, ⟨0, hn⟩), Finset.mem_univ _⟩ Cf with hCfsdef
  have hCfs0 : 0 ≤ Cfs := by
    rw [hCfsdef]
    exact le_trans (hCf (⟨0, hn⟩, ⟨0, hn⟩)).1
      (Finset.le_sup' (f := Cf) (Finset.mem_univ (⟨0, hn⟩, ⟨0, hn⟩)))
  have hCfsle : ∀ cd : Fin n × Fin n, Cf cd ≤ Cfs := by
    intro cd
    rw [hCfsdef]
    exact Finset.le_sup' (f := Cf) (Finset.mem_univ cd)
  set Y : ℝ := Cfs * (1 + M * Ce) with hYdef
  have hYnn : 0 ≤ Y := by rw [hYdef]; positivity
  set Y1 : ℝ := Cfs * (1 + M * Ce1) with hY1def
  have hY1nn : 0 ≤ Y1 := by rw [hY1def]; positivity
  set Cfin : ℝ := max (Csup * (2 * Real.pi) ^ s * Real.sqrt Y)
      (max (((2 * Real.pi) ^ 2) ^ s * Y) ((((2 * Real.pi) ^ 2) ^ (s + 1)) * Y1)) with hCfindef
  have hCfin0 : 0 ≤ Cfin := by
    rw [hCfindef]
    have hA0 : (0 : ℝ) ≤ Csup * (2 * Real.pi) ^ s * Real.sqrt Y := by positivity
    exact le_trans hA0 (le_max_left _ _)
  refine ⟨Cfin, hCfin0, ?_⟩
  intro N c hc hen hell
  have key : ∀ c' d' : Fin n,
      ((∀ (j : ℕ) (hj : j + sob n ≤ s) (l : Fin j → Fin n) (x : Fin n → ℝ),
          ‖pdVec j l (fun y => (((reMat (seriesFunM c y))⁻¹) c' d' : ℂ)) x‖
            ≤ Cfin * (1 + Bs)) ∧
        (∀ (j : ℕ) (hj : j ≤ s) (l : Fin j → Fin n),
          (∫ x in unitCube (ι := Fin n),
            ‖pdVec j l (fun y => (((reMat (seriesFunM c y))⁻¹) c' d' : ℂ)) x‖ ^ 2)
            ≤ Cfin * (1 + Bs) ^ 2) ∧
        (∀ (l : Fin (s + 1) → Fin n),
          (∫ x in unitCube (ι := Fin n),
            ‖pdVec (s + 1) l (fun y => (((reMat (seriesFunM c y))⁻¹) c' d' : ℂ)) x‖ ^ 2)
            ≤ Cfin * (1 + Bs) ^ 2 * (1 + ENormSqFull (s + 1) (seriesFunM c)))) := by
    intro c' d'
    have hWmem : ∀ x : Fin n → ℝ, entryVec n c x ∈ invElliptic n lam ρ := by
      intro x
      refine ⟨fun i => ?_, ?_⟩
      · simpa only [entryVec_apply] using hKρ' N c hc hen x i
      · intro v
        rw [reMatZ_entryVec]
        exact hell x v
    have hWdet : ∀ x, entryVec n c x ∈ invNonsing n :=
      fun x => invJet_invElliptic_subset_invNonsing hlam (hWmem x)
    have hWsm : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => entryVec n c x) :=
      invJet_contDiff_invCvec_series c hc
    have hWper : Periodic1 (fun x : Fin n → ℝ => entryVec n c x) := invJet_periodic1_invCvec_series c
    have hg : ContDiff ℝ (⊤ : ℕ∞) (invEntryFun n c c' d') := by
      rw [contDiff_iff_contDiffAt]
      intro x
      exact ((invJet_contDiffOn_invPhi c' d').contDiffAt
        (invJet_isOpen_invNonsing.mem_nhds (hWdet x))).comp x hWsm.contDiffAt
    have hgper : Periodic1 (invEntryFun n c c' d') := by
      intro i x
      have h : entryVec n c (x + Pi.single i 1) = entryVec n c x := hWper i x
      simp only [invEntryFun_apply]
      rw [h]
    have hdmom2 : ∀ K : ℕ, Summable (fun k : Fin n → ℤ =>
        (wt k) ^ K * ‖fourierCoeff (invEntryFun n c c' d') k‖ ^ 2) :=
      fun K => Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff _ hg hgper K
    have hdmom1 : ∀ K : ℕ, Summable (fun k : Fin n → ℤ =>
        (wt k) ^ K * ‖fourierCoeff (invEntryFun n c c' d') k‖) :=
      fun K => invJet_summable_moment_of_wt_sq _ hdmom2 K
    have hser : seriesFun (fourierCoeff (invEntryFun n c c' d'))
        = fun y => (((reMat (seriesFunM c y))⁻¹) c' d' : ℂ) :=
      (funext (seriesFun_fourierCoeff _ hg hgper)).trans (invEntryFun_eq n c c' d')
    have hfun : (fun y => (((reMat (seriesFunM c y))⁻¹) c' d' : ℂ))
        = seriesFun (fourierCoeff (invEntryFun n c c' d')) := hser.symm
    haveI : Nonempty (Fin (Fintype.card (Fin n × Fin n))) :=
      ⟨invEv n (⟨0, hn⟩, ⟨0, hn⟩)⟩
    have hmmom : ∀ K : ℕ, Summable (fun k : Fin n → ℤ => (wt k) ^ K * ‖invCvec n c k‖) := by
      intro K
      have hmaj : Summable (fun k : Fin n → ℤ => ∑ i : Fin (Fintype.card (Fin n × Fin n)),
          (wt k) ^ K * ‖invCvec n c k i‖) := by
        refine summable_sum (s := Finset.univ)
          (f := fun (i : Fin (Fintype.card (Fin n × Fin n))) (k : Fin n → ℤ) =>
            (wt k) ^ K * ‖invCvec n c k i‖) ?_
        intro i _
        simpa only [invCvec_apply] using
          summable_moment_box c hc ((invEv n).symm i).1 ((invEv n).symm i).2 K
      refine Summable.of_nonneg_of_le
        (fun k => mul_nonneg (pow_nonneg (wt_pos k).le K) (norm_nonneg _)) (fun k => ?_) hmaj
      calc (wt k) ^ K * ‖invCvec n c k‖
            ≤ (wt k) ^ K * ∑ i, ‖invCvec n c k i‖ := by
              refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (wt_pos k).le K)
              exact (pi_norm_le_iff_of_nonempty (invCvec n c k)).mpr
                (fun i => Finset.single_le_sum (fun i _ => norm_nonneg _) (Finset.mem_univ i))
          _ = ∑ i, (wt k) ^ K * ‖invCvec n c k i‖ := by rw [Finset.mul_sum]
    have hsumM : (∑ _i : Fin (Fintype.card (Fin n × Fin n)), Ce * ENormSqFull s (seriesFunM c))
        = M * (Ce * ENormSqFull s (seriesFunM c)) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      congr 1
      rw [hMdef]; simp
    have hsumM1 : (∑ _i : Fin (Fintype.card (Fin n × Fin n)), Ce1 * ENormSqFull (s + 1) (seriesFunM c))
        = M * (Ce1 * ENormSqFull (s + 1) (seriesFunM c)) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      congr 1
      rw [hMdef]; simp
    have hB2 : (∑ i : Fin (Fintype.card (Fin n × Fin n)), CSq (sob n) (fun k => invCvec n c k i))
        ≤ Bc ^ 2 := by
      have hstep : ∀ i : Fin (Fintype.card (Fin n × Fin n)),
          CSq (sob n) (fun k => invCvec n c k i) ≤ Ce * ENormSqFull s (seriesFunM c) := by
        intro i
        refine (invJet_CSq_mono_le _ hσs ?_).trans ?_
        · simpa only [invCvec_apply] using
            (Work.Diff.STE.summable_wt_pow_mul_norm_sq
              (fun k : Fin n → ℤ => c k ((invEv n).symm i).1 ((invEv n).symm i).2)
              (fun M' => summable_moment_box c hc ((invEv n).symm i).1 ((invEv n).symm i).2 M') s)
        · simpa only [invCvec_apply] using hCe' N c hc ((invEv n).symm i).1 ((invEv n).symm i).2
      have hsum : (∑ i : Fin (Fintype.card (Fin n × Fin n)), CSq (sob n) (fun k => invCvec n c k i))
          ≤ ∑ _i : Fin (Fintype.card (Fin n × Fin n)), Ce * ENormSqFull s (seriesFunM c) :=
        Finset.sum_le_sum (fun i _ => hstep i)
      rw [hsumM] at hsum
      refine hsum.trans ?_
      rw [hBcdef, mul_pow, Real.sq_sqrt (mul_nonneg hMnn hCe)]
      have hX : ENormSqFull s (seriesFunM c) ≤ Bs ^ 2 := hen
      have hBsq : Bs ^ 2 ≤ (1 + Bs) ^ 2 := by nlinarith [hBs]
      calc M * (Ce * ENormSqFull s (seriesFunM c)) ≤ M * (Ce * Bs ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ hMnn
            exact mul_le_mul_of_nonneg_left hX hCe
        _ ≤ M * (Ce * (1 + Bs) ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ hMnn
            exact mul_le_mul_of_nonneg_left hBsq hCe
        _ = M * Ce * (1 + Bs) ^ 2 := by ring
    have hcf := (hCf (c', d')).2 (invCvec n c) hmmom hB2 hWmem
    have hsum_s : (∑ i : Fin (Fintype.card (Fin n × Fin n)), CSq s (fun k => invCvec n c k i))
        ≤ M * (Ce * ENormSqFull s (seriesFunM c)) := by
      have hstep : ∀ i : Fin (Fintype.card (Fin n × Fin n)),
          CSq s (fun k => invCvec n c k i) ≤ Ce * ENormSqFull s (seriesFunM c) := by
        intro i
        simpa only [invCvec_apply] using hCe' N c hc ((invEv n).symm i).1 ((invEv n).symm i).2
      have hsum : (∑ i : Fin (Fintype.card (Fin n × Fin n)), CSq s (fun k => invCvec n c k i))
          ≤ ∑ _i : Fin (Fintype.card (Fin n × Fin n)), Ce * ENormSqFull s (seriesFunM c) :=
        Finset.sum_le_sum (fun i _ => hstep i)
      rw [hsumM] at hsum
      exact hsum
    have hsum_s1 : (∑ i : Fin (Fintype.card (Fin n × Fin n)), CSq (s + 1) (fun k => invCvec n c k i))
        ≤ M * (Ce1 * ENormSqFull (s + 1) (seriesFunM c)) := by
      have hstep : ∀ i : Fin (Fintype.card (Fin n × Fin n)),
          CSq (s + 1) (fun k => invCvec n c k i) ≤ Ce1 * ENormSqFull (s + 1) (seriesFunM c) := by
        intro i
        simpa only [invCvec_apply] using hCe1' N c hc ((invEv n).symm i).1 ((invEv n).symm i).2
      have hsum : (∑ i : Fin (Fintype.card (Fin n × Fin n)), CSq (s + 1) (fun k => invCvec n c k i))
          ≤ ∑ _i : Fin (Fintype.card (Fin n × Fin n)), Ce1 * ENormSqFull (s + 1) (seriesFunM c) :=
        Finset.sum_le_sum (fun i _ => hstep i)
      rw [hsumM1] at hsum
      exact hsum
    have hSs : CSq s (fourierCoeff (invEntryFun n c c' d')) ≤ Y * (1 + Bs) ^ 2 := by
      have h3 : (1 : ℝ) + (∑ i : Fin (Fintype.card (Fin n × Fin n)),
            CSq s (fun k => invCvec n c k i))
          ≤ (1 + M * Ce) * (1 + ENormSqFull s (seriesFunM c)) := by
        have hX := ENormSqFull_nonneg s (seriesFunM c)
        nlinarith [hsum_s, hX, hMnn, hCe]
      calc CSq s (fourierCoeff (invEntryFun n c c' d'))
          ≤ Cfs * (1 + ∑ i : Fin (Fintype.card (Fin n × Fin n)),
              CSq s (fun k => invCvec n c k i)) :=
            hcf.1.trans (mul_le_mul_of_nonneg_right (hCfsle (c', d')) (by
              have h : (0 : ℝ) ≤ ∑ i : Fin (Fintype.card (Fin n × Fin n)),
                  CSq s (fun k => invCvec n c k i) :=
                Finset.sum_nonneg (fun i _ => CSq_nonneg' s _)
              linarith))
        _ ≤ Cfs * ((1 + M * Ce) * (1 + ENormSqFull s (seriesFunM c))) :=
            mul_le_mul_of_nonneg_left h3 hCfs0
        _ = Y * (1 + ENormSqFull s (seriesFunM c)) := by rw [hYdef]; ring
        _ ≤ Y * (1 + Bs) ^ 2 := by
            refine mul_le_mul_of_nonneg_left ?_ hYnn
            nlinarith [hen, hBs]
    have hSs1 : CSq (s + 1) (fourierCoeff (invEntryFun n c c' d'))
        ≤ Y1 * (1 + ENormSqFull (s + 1) (seriesFunM c)) := by
      have h3 : (1 : ℝ) + (∑ i : Fin (Fintype.card (Fin n × Fin n)),
            CSq (s + 1) (fun k => invCvec n c k i))
          ≤ (1 + M * Ce1) * (1 + ENormSqFull (s + 1) (seriesFunM c)) := by
        have hX := ENormSqFull_nonneg (s + 1) (seriesFunM c)
        nlinarith [hsum_s1, hX, hMnn, hCe1]
      calc CSq (s + 1) (fourierCoeff (invEntryFun n c c' d'))
          ≤ Cfs * (1 + ∑ i : Fin (Fintype.card (Fin n × Fin n)),
              CSq (s + 1) (fun k => invCvec n c k i)) :=
            hcf.2.trans (mul_le_mul_of_nonneg_right (hCfsle (c', d')) (by
              have h : (0 : ℝ) ≤ ∑ i : Fin (Fintype.card (Fin n × Fin n)),
                  CSq (s + 1) (fun k => invCvec n c k i) :=
                Finset.sum_nonneg (fun i _ => CSq_nonneg' (s + 1) _)
              linarith))
        _ ≤ Cfs * ((1 + M * Ce1) * (1 + ENormSqFull (s + 1) (seriesFunM c))) :=
            mul_le_mul_of_nonneg_left h3 hCfs0
        _ = Y1 * (1 + ENormSqFull (s + 1) (seriesFunM c)) := by rw [hY1def]; ring
    refine ⟨?_, ?_, ?_⟩
    · intro j hj l x
      have h := invJet_sup_pdVec_seriesFun_le hσs hdmom1 hCsup hCsup' hYnn hBs hSs j hj l x
      rw [show (‖pdVec j l (fun y => (((reMat (seriesFunM c y))⁻¹) c' d' : ℂ)) x‖)
          = ‖pdVec j l (seriesFun (fourierCoeff (invEntryFun n c c' d'))) x‖ from by rw [hfun]]
      refine h.trans ?_
      refine mul_le_mul_of_nonneg_right (le_max_left _ _) ?_
      linarith [hBs]
    · intro j hj l
      have h := invJet_int_pdVec_seriesFun_le hdmom1 hYnn hSs j hj l
      rw [show (∫ x in unitCube (ι := Fin n),
            ‖pdVec j l (fun y => (((reMat (seriesFunM c y))⁻¹) c' d' : ℂ)) x‖ ^ 2)
          = ∫ x in unitCube (ι := Fin n),
            ‖pdVec j l (seriesFun (fourierCoeff (invEntryFun n c c' d'))) x‖ ^ 2 from by
          rw [hfun]]
      refine h.trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (by nlinarith [hBs])
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    · intro l
      have h := invJet_int_pdVec_seriesFun_succ_le hdmom1 hSs1 l
      rw [show (∫ x in unitCube (ι := Fin n),
            ‖pdVec (s + 1) l (fun y => (((reMat (seriesFunM c y))⁻¹) c' d' : ℂ)) x‖ ^ 2)
          = ∫ x in unitCube (ι := Fin n),
            ‖pdVec (s + 1) l (seriesFun (fourierCoeff (invEntryFun n c c' d'))) x‖ ^ 2 from by
          rw [hfun]]
      refine h.trans ?_
      have hX : (0 : ℝ) ≤ 1 + ENormSqFull (s + 1) (seriesFunM c) := by
        have := ENormSqFull_nonneg (s + 1) (seriesFunM c); linarith
      calc ((2 * Real.pi) ^ 2) ^ (s + 1) * (Y1 * (1 + ENormSqFull (s + 1) (seriesFunM c)))
          = (((2 * Real.pi) ^ 2) ^ (s + 1) * Y1) * (1 + ENormSqFull (s + 1) (seriesFunM c)) := by
            ring
        _ ≤ Cfin * (1 + ENormSqFull (s + 1) (seriesFunM c)) := by
            refine mul_le_mul_of_nonneg_right ?_ hX
            rw [hCfindef]
            exact le_trans (le_max_right _ _) (le_max_right _ _)
        _ ≤ Cfin * (1 + Bs) ^ 2 * (1 + ENormSqFull (s + 1) (seriesFunM c)) := by
            have h1 : (1 : ℝ) ≤ (1 + Bs) ^ 2 := by nlinarith [hBs]
            calc Cfin * (1 + ENormSqFull (s + 1) (seriesFunM c))
                = Cfin * 1 * (1 + ENormSqFull (s + 1) (seriesFunM c)) := by ring
              _ ≤ Cfin * (1 + Bs) ^ 2 * (1 + ENormSqFull (s + 1) (seriesFunM c)) := by
                  refine mul_le_mul_of_nonneg_right ?_ hX
                  exact mul_le_mul_of_nonneg_left h1 hCfin0
  exact ⟨fun c' d' j hj l x => (key c' d').1 j hj l x,
    fun c' d' j hj l => (key c' d').2.1 j hj l,
    fun c' d' l => (key c' d').2.2 l⟩

end Work.Diff.STE.flat

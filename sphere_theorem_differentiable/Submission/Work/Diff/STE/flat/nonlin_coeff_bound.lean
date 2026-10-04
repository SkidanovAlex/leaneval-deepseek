/-
# The nonlinearity composed with a jet of a Fourier series has controlled coefficients

This file proves `Work.Diff.STE.flat.nonlin_coeff_bound`, the "coefficient bound for the
nonlinearity" input of the flat Galerkin scheme for the DeTurck system.

The statement: for a nonlinearity `Φ` of DeTurck shape, a Sobolev level `k` with
`n + 4 < 2 k`, an ellipticity constant `lam > 0` and an energy bound `E ≥ 0`, there is a
constant `Λ ≥ 0` such that for *every* box-supported coefficient family `c` whose
level-`j` energies `CSqM j c` (`j ≤ k`) are bounded by `E` and whose series
`seriesFunM c` is uniformly `lam`-elliptic, the entries of
`x ↦ Φ (x, jetM (seriesFunM c) x)` have summable Fourier coefficients with
`∑'_m ‖fourierCoeff (…) m‖ ≤ Λ`.

## Proof

* the jet of `seriesFunM c` is, componentwise, the Fourier series of an explicit *multiplier*
  family applied to `c` (the value, `dmul a`, and `dmul a (dmul b)` blocks) — the families
  `jetData`, with the identification `jetUnpack_jetData`;
* the sup bounds on the jet (`jet_sup_le` at levels `0,1,2`) come from the energy bound
  `ENormSqFull k (seriesFunM c) ≤ F`, which follows from `CSqM j c ≤ E`;
* the nonlinearity is cut off on the good (compact, elliptic) set so that it becomes
  *globally* smooth (`smoothCutoff_goodSet` + `cutoff_mul_contDiff`), and the
  `x`-dependence (which is periodic) is handled by the character variables
  (the factorisation `pf_periodicFactor` + `CSq_comp_xperiodic_le_of_factor`);
* the Moser composition estimate `CSq_comp_xperiodic_le_of_factor` then bounds the weighted
  `ℓ²` norm of the Fourier coefficients of the composite by the data norms, and
  `l1_le_sqrt_CSq` converts it into the `ℓ¹` bound.
-/
import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.level_aux
import Submission.Work.Diff.STE.flat.det_cutoff_defs
import Submission.Work.Diff.STE.flat.cutoff_mul_contDiff
import Submission.Work.Diff.STE.flat.CSq_comp_xperiodic_le
import Submission.Work.Diff.STE.flat.det_ne_zero_of_quadForm_le
import Submission.Work.Diff.STE.flat.periodic_defs
import Submission.Work.Diff.STE.summable_norm_of_CSq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat

noncomputable section

set_option maxHeartbeats 2000000

/-! ## The vectorisation of the spatial `2`-jet -/

/-- The index set of the spatial `2`-jet: the value, the `n` first derivatives and the
`n × n` second derivatives, each carrying its matrix entry indices. -/
inductive JetIx (n : ℕ) where
  | val (i j : Fin n) : JetIx n
  | lin (c i j : Fin n) : JetIx n
  | sec (c d i j : Fin n) : JetIx n
  deriving DecidableEq, Fintype

/-- The canonical identification of the jet index set with `Fin (card (JetIx n))`, used to feed
the jet data into the vector-valued Moser estimate. -/
def jetIdxEquiv (n : ℕ) : JetIx n ≃ Fin (Fintype.card (JetIx n)) :=
  Fintype.equivFin _

/-- The Fourier multiplier family of a jet index: the coefficient family whose series is the
corresponding jet component of `seriesFunM c`. -/
def jetDataVec {n : ℕ} (c : (Fin n → ℤ) → MatC n) (k : Fin n → ℤ) : JetIx n → ℂ
  | .val i j => c k i j
  | .lin a i j => Work.Diff.STE.dmul a (fun m => c m i j) k
  | .sec a b i j => Work.Diff.STE.dmul a (Work.Diff.STE.dmul b (fun m => c m i j)) k

/-- The jet data family, indexed by `Fin (card (JetIx n))`. -/
def jetData {n : ℕ} (c : (Fin n → ℤ) → MatC n) :
    (Fin n → ℤ) → (Fin (Fintype.card (JetIx n)) → ℂ) :=
  fun k p => jetDataVec c k ((jetIdxEquiv n).symm p)

/-- The packing of a jet vector into an element of `Jet n`. -/
def jetUnpack {n m : ℕ} (e : JetIx n ≃ Fin m) (z : Fin m → ℂ) : Jet n :=
  (fun i j => z (e (.val i j)),
   (fun a i j => z (e (.lin a i j)), fun a b i j => z (e (.sec a b i j))))

lemma dmulV_single {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) (c : (ι → ℤ) → ℂ) :
    Work.Diff.STE.dmulV [a] c = Work.Diff.STE.dmul a c := by
  rw [Work.Diff.STE.dmulV_cons, Work.Diff.STE.dmulV_nil]

lemma summable_dmul_moments {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι)
    (c : (ι → ℤ) → ℂ) (h : ∀ N : ℕ, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖c k‖)) :
    ∀ N : ℕ, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖Work.Diff.STE.dmul a c k‖) := by
  intro N
  have hh := Work.Diff.STE.summable_dmulV [a] c h N
  rwa [dmulV_single] at hh

/-! ## The identification of the packed jet data with the jet of the series -/

/-- **The packed data vector is the jet of the Fourier series.** -/
theorem jetUnpack_jetData {n N : ℕ} (c : (Fin n → ℤ) → MatC n)
    (hc : ∀ k : Fin n → ℤ, k ∉ box n N → c k = 0) (x : Fin n → ℝ) :
    jetUnpack (jetIdxEquiv n) (fun p => Work.Diff.STE.seriesFun (fun k => jetData c k p) x)
      = jetM (seriesFunM c) x := by
  have hmom : ∀ (i j : Fin n) (M : ℕ),
      Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ M * ‖c k i j‖) :=
    fun i j M => summable_moment_box c hc i j M
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext i j
    simp only [jetM, jetUnpack, jetData, jetDataVec, jetIdxEquiv, Equiv.symm_apply_apply,
      seriesFunM_apply]
  · funext a i j
    simp only [jetM, jetUnpack, jetData, jetDataVec, jetIdxEquiv, Equiv.symm_apply_apply,
      seriesFunM_apply, pdM]
    exact (Work.Diff.STE.pd_seriesFun a (fun m => c m i j) (hmom i j) x).symm
  · funext a b i j
    simp only [jetM, jetUnpack, jetData, jetDataVec, jetIdxEquiv, Equiv.symm_apply_apply,
      seriesFunM_apply, pdM]
    rw [show (fun y : Fin n → ℝ => pd b (fun z : Fin n → ℝ => Work.Diff.STE.seriesFun
          (fun m : Fin n → ℤ => c m i j) z) y)
        = Work.Diff.STE.seriesFun (Work.Diff.STE.dmul b (fun m : Fin n → ℤ => c m i j)) from
      funext (fun y => Work.Diff.STE.pd_seriesFun b (fun m => c m i j) (hmom i j) y)]
    exact (Work.Diff.STE.pd_seriesFun a (Work.Diff.STE.dmul b (fun m => c m i j))
      (by rw [← dmulV_single]
          exact Work.Diff.STE.summable_dmulV [b] (fun m => c m i j) (hmom i j)) x).symm

/-- The unwrapped index of the packed data vector: the unpacking of a component of `Jet n`. -/
lemma jetUnpack_apply_val {n m : ℕ} (e : JetIx n ≃ Fin m) (z : Fin m → ℂ) (i j : Fin n) :
    (jetUnpack e z).1 i j = z (e (.val i j)) := rfl

/-- The evaluation of an entry of a matrix is smooth. -/
lemma contDiff_apply_matC {n : ℕ} (i j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) fun M : MatC n => M i j := by
  fun_prop

/-- The packing of a jet vector is smooth. -/
lemma contDiff_jetUnpack {n m : ℕ} (e : JetIx n ≃ Fin m) :
    ContDiff ℝ (⊤ : ℕ∞) (jetUnpack e) := by
  unfold jetUnpack
  fun_prop

/-! ## Two elementary estimates used below -/

/-- `1 ≤ (2π)²`. -/
lemma ncb_one_le_two_pi_sq : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by
  nlinarith [Real.pi_gt_three]

/-- Monotonicity of `CSq` in the level (the weight `⟨k⟩² ≥ 1`). -/
lemma ncb_CSq_mono_le {ι : Type*} [Fintype ι] [DecidableEq ι] (c : (ι → ℤ) → ℂ) {k m : ℕ}
    (hkm : k ≤ m) (h : Summable (fun a : ι → ℤ => (Work.Diff.STE.wt a) ^ m * ‖c a‖ ^ 2)) :
    Work.Diff.STE.CSq k c ≤ Work.Diff.STE.CSq m c := by
  rw [Work.Diff.STE.CSq, Work.Diff.STE.CSq]
  refine Summable.tsum_le_tsum (fun a => ?_) ?_ h
  · exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (Work.Diff.STE.wt_one_le a) hkm) (sq_nonneg _)
  · exact Summable.of_nonneg_of_le (fun a => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos a)) k)
      (sq_nonneg _)) (fun a => mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (Work.Diff.STE.wt_one_le a) hkm) (sq_nonneg _)) h

/-! ## Energy and sup bounds for a box-supported coefficient family -/

/-- **The energy bound.**  The level-`k` energy of the series of a box-supported family is
controlled by the level-`k` coefficient energy. -/
lemma ENormSqFull_seriesFunM_le {n : ℕ} {N k : ℕ} (c : (Fin n → ℤ) → MatC n)
    (hc : ∀ k' : Fin n → ℤ, k' ∉ box n N → c k' = 0) (E : ℝ) (hE : 0 ≤ E)
    (hcsq : ∀ j ≤ k, CSqM j c ≤ E) :
    ∃ F : ℝ, 0 ≤ F ∧ ENormSqFull k (seriesFunM c) ≤ F := by
  obtain ⟨Ck, hCk0, hCk⟩ := Work.Diff.STE.ENormSq_seriesFun_le (ι := Fin n) k
  obtain ⟨C0, hC00, hC0⟩ := Work.Diff.STE.ENormSq_seriesFun_le (ι := Fin n) 0
  have hmom : ∀ (i j : Fin n) (M : ℕ),
      Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ M * ‖c k i j‖) :=
    fun i j M => summable_moment_box c hc i j M
  have h1 : ENormSqM k (seriesFunM c) ≤ Ck * CSqM k c := by
    rw [ENormSqM, CSqM, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    exact hCk (fun m => c m i j) (hmom i j)
  have h2 : ENormSqM 0 (seriesFunM c) ≤ C0 * CSqM 0 c := by
    rw [ENormSqM, CSqM, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    exact hC0 (fun m => c m i j) (hmom i j)
  refine ⟨(Ck + C0) * E, by positivity, ?_⟩
  have h3 : Ck * CSqM k c ≤ Ck * E := mul_le_mul_of_nonneg_left (hcsq k le_rfl) hCk0
  have h4 : C0 * CSqM 0 c ≤ C0 * E := mul_le_mul_of_nonneg_left (hcsq 0 (Nat.zero_le k)) hC00
  rw [ENormSqFull]
  linarith

/-- **The jet lies in the good set.**  The entry bound comes from the *uniform* sup bound
`‖∂^l (seriesFunM c) x‖ ≤ Cs (2π)^m √E` for `m ≤ 2` (which is `norm_seriesFun_le` applied to the
multiplier families, the energy being bounded by `E`), and the ellipticity is the hypothesis. -/
lemma jetMem_goodSet {n N k : ℕ} (c : (Fin n → ℤ) → MatC n)
    (hc : ∀ k' : Fin n → ℤ, k' ∉ box n N → c k' = 0) {E : ℝ} (hE : 0 ≤ E)
    (hcsq : ∀ j ≤ k, CSqM j c ≤ E) (hsob2 : sob n + 2 ≤ k)
    {Cs : ℝ} (hCs0 : 0 ≤ Cs)
    (hCs : ∀ (d : (Fin n → ℤ) → ℂ),
      Summable (fun k => (Work.Diff.STE.wt k) ^ (sob n) * ‖d k‖ ^ 2) →
      ∀ x, ‖Work.Diff.STE.seriesFun d x‖ ≤ Cs * Real.sqrt (Work.Diff.STE.CSq (sob n) d))
    (lam : ℝ)
    (hell : ∀ (x : Fin n → ℝ) (v : Fin n → ℝ), (lam / 2) * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
      reMat (seriesFunM c x) i j * v i * v j) :
    ∀ x, jetM (seriesFunM c) x ∈ goodSet n lam (Cs * (2 * Real.pi) ^ 2 * (1 + Real.sqrt E)) := by
  intro x
  have hmom : ∀ (i j : Fin n) (M : ℕ),
      Summable (fun m : Fin n → ℤ => (Work.Diff.STE.wt m) ^ M * ‖c m i j‖) :=
    fun i j M => summable_moment_box c hc i j M
  have hCSqe : ∀ (i j : Fin n) (r : ℕ), r ≤ k →
      Work.Diff.STE.CSq r (fun m : Fin n → ℤ => c m i j) ≤ E := by
    intro i j r hr
    have h1 : Work.Diff.STE.CSq r (fun m : Fin n → ℤ => c m i j) ≤ CSqM r c := by
      have h2 := Finset.single_le_sum (f := fun i' : Fin n =>
          ∑ j' : Fin n, Work.Diff.STE.CSq r (fun m : Fin n → ℤ => c m i' j'))
        (fun i' _ => Finset.sum_nonneg fun j' _ => CSq_nonneg' _ _) (Finset.mem_univ i)
      have h3 := Finset.single_le_sum (f := fun j' : Fin n =>
          Work.Diff.STE.CSq r (fun m : Fin n → ℤ => c m i j'))
        (fun j' _ => CSq_nonneg' _ _) (Finset.mem_univ j)
      rw [CSqM]
      exact h3.trans h2
    exact h1.trans (hcsq r hr)
  have hJet : ∀ {m : ℕ} (l : Fin m → Fin n) (i j : Fin n), m ≤ 2 →
      ‖Work.Diff.STE.pdVec m l (fun y => seriesFunM c y i j) x‖
        ≤ Cs * (2 * Real.pi) ^ m * Real.sqrt E := by
    intro m l i j hm2
    have hfun : (fun y : Fin n → ℝ => seriesFunM c y i j)
        = Work.Diff.STE.seriesFun (fun k : Fin n → ℤ => c k i j) := by
      funext y
      rw [seriesFunM_apply]
    have hpd : Work.Diff.STE.pdVec m l (fun y => seriesFunM c y i j) x
        = Work.Diff.STE.seriesFun (Work.Diff.STE.dmulV (List.ofFn l)
            (fun k : Fin n → ℤ => c k i j)) x := by
      rw [Work.Diff.STE.pdVec, hfun]
      exact Work.Diff.STE.pdList_seriesFun (List.ofFn l) (fun k : Fin n → ℤ => c k i j)
        (hmom i j) x
    rw [hpd]
    have hd : Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ (sob n)
        * ‖Work.Diff.STE.dmulV (List.ofFn l) (fun k : Fin n → ℤ => c k i j) k‖ ^ 2) :=
      Work.Diff.STE.summable_wt_pow_mul_norm_sq _
        (Work.Diff.STE.summable_dmulV (List.ofFn l) _ (hmom i j)) (sob n)
    have h2 : Work.Diff.STE.CSq (sob n)
        (Work.Diff.STE.dmulV (List.ofFn l) (fun k : Fin n → ℤ => c k i j))
        ≤ ((2 * Real.pi) ^ 2) ^ m
          * Work.Diff.STE.CSq (sob n + m) (fun k : Fin n → ℤ => c k i j) := by
      have h := CSq_dmulV_le (ι := Fin n) (sob n) (List.ofFn l)
        (fun k : Fin n → ℤ => c k i j) (hmom i j)
      simpa [List.length_ofFn] using h
    have h3 : Work.Diff.STE.CSq (sob n + m) (fun k : Fin n → ℤ => c k i j) ≤ E :=
      hCSqe i j (sob n + m) (by omega)
    have h4 : Work.Diff.STE.CSq (sob n)
        (Work.Diff.STE.dmulV (List.ofFn l) (fun k : Fin n → ℤ => c k i j))
        ≤ ((2 * Real.pi) ^ 2) ^ m * E :=
      h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
    have h5 : Real.sqrt (Work.Diff.STE.CSq (sob n)
        (Work.Diff.STE.dmulV (List.ofFn l) (fun k : Fin n → ℤ => c k i j)))
        ≤ (2 * Real.pi) ^ m * Real.sqrt E := by
      refine (Real.sqrt_le_sqrt h4).trans (le_of_eq ?_)
      rw [show ((2 * Real.pi) ^ 2) ^ m = ((2 * Real.pi) ^ m) ^ 2 by rw [← pow_mul]; ring_nf]
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    calc ‖Work.Diff.STE.seriesFun (Work.Diff.STE.dmulV (List.ofFn l)
            (fun k : Fin n → ℤ => c k i j)) x‖
        ≤ Cs * Real.sqrt (Work.Diff.STE.CSq (sob n)
            (Work.Diff.STE.dmulV (List.ofFn l) (fun k : Fin n → ℤ => c k i j))) := hCs _ hd x
      _ ≤ Cs * ((2 * Real.pi) ^ m * Real.sqrt E) := mul_le_mul_of_nonneg_left h5 hCs0
      _ = Cs * (2 * Real.pi) ^ m * Real.sqrt E := by ring
  have hbound_m : ∀ m ≤ 2, Cs * (2 * Real.pi) ^ m * Real.sqrt E
      ≤ Cs * (2 * Real.pi) ^ 2 * (1 + Real.sqrt E) := by
    intro m hm
    have hpi1 : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hpm : (2 * Real.pi) ^ m ≤ (2 * Real.pi) ^ 2 := pow_le_pow_right₀ hpi1 hm
    have hsE : 0 ≤ Real.sqrt E := Real.sqrt_nonneg E
    calc Cs * (2 * Real.pi) ^ m * Real.sqrt E
        ≤ Cs * (2 * Real.pi) ^ 2 * Real.sqrt E :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpm hCs0) hsE
      _ ≤ Cs * (2 * Real.pi) ^ 2 * (1 + Real.sqrt E) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    simpa [Work.Diff.STE.pdVec, Work.Diff.STE.pdList, jetM] using
      (hJet (fun i : Fin 0 => i.elim0) i j (by norm_num)).trans (hbound_m 0 (by norm_num))
  · intro a i j
    simpa [Work.Diff.STE.pdVec, Work.Diff.STE.pdList, jetM, pdM] using
      (hJet (fun _ : Fin 1 => a) i j (by norm_num)).trans (hbound_m 1 (by norm_num))
  · intro a b i j
    simpa [Work.Diff.STE.pdVec, Work.Diff.STE.pdList, jetM, pdM] using
      (hJet (fun i : Fin 2 => if i = 0 then a else b) i j (by norm_num)).trans
        (hbound_m 2 (by norm_num))
  · exact hell x

/-! ## The coefficient norms of the jet data -/

/-- The sum of the level-`r` coefficient norms of the jet data is controlled by the level-`r+2`
energy of the family: each jet component is a product of at most two Fourier multipliers. -/
lemma sum_CSq_jetData_le {n : ℕ} {N : ℕ} (c : (Fin n → ℤ) → MatC n)
    (hc : ∀ k' : Fin n → ℤ, k' ∉ box n N → c k' = 0) (r : ℕ) :
    (∑ p : Fin (Fintype.card (JetIx n)), Work.Diff.STE.CSq r (fun k => jetData c k p))
      ≤ (Fintype.card (JetIx n) : ℝ)
          * (((2 * Real.pi) ^ 2) ^ 2 * CSqM (r + 2) c) := by
  classical
  have hmom : ∀ (i j : Fin n) (M : ℕ),
      Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ M * ‖c k i j‖) :=
    fun i j M => summable_moment_box c hc i j M
  have hQM : 0 ≤ CSqM (r + 2) c := by
    rw [CSqM]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => CSq_nonneg' _ _
  have hentry : ∀ (i j : Fin n),
      Work.Diff.STE.CSq (r + 2) (fun k : Fin n → ℤ => c k i j) ≤ CSqM (r + 2) c := by
    intro i j
    have h1 : Work.Diff.STE.CSq (r + 2) (fun k : Fin n → ℤ => c k i j)
        ≤ ∑ j' : Fin n, Work.Diff.STE.CSq (r + 2) (fun k : Fin n → ℤ => c k i j') :=
      Finset.single_le_sum (f := fun j' : Fin n =>
        Work.Diff.STE.CSq (r + 2) (fun k : Fin n → ℤ => c k i j'))
        (fun j' _ => CSq_nonneg' _ _) (Finset.mem_univ j)
    have h2 : (∑ j' : Fin n, Work.Diff.STE.CSq (r + 2) (fun k : Fin n → ℤ => c k i j'))
        ≤ ∑ i' : Fin n, ∑ j' : Fin n,
            Work.Diff.STE.CSq (r + 2) (fun k : Fin n → ℤ => c k i' j') :=
      Finset.single_le_sum (f := fun i' : Fin n => ∑ j' : Fin n,
          Work.Diff.STE.CSq (r + 2) (fun k : Fin n → ℤ => c k i' j'))
        (fun i' _ => Finset.sum_nonneg fun j' _ => CSq_nonneg' _ _) (Finset.mem_univ i)
    exact h1.trans (by rw [CSqM]; exact h2)
  have hQ1 : (1 : ℝ) ≤ ((2 * Real.pi) ^ 2) ^ 2 :=
    one_le_pow₀ ncb_one_le_two_pi_sq
  have hper : ∀ w : JetIx n,
      Work.Diff.STE.CSq r (fun k => jetDataVec c k w)
        ≤ ((2 * Real.pi) ^ 2) ^ 2 * CSqM (r + 2) c := by
    intro w
    cases w with
    | val i j =>
      refine (ncb_CSq_mono_le (fun m : Fin n → ℤ => c m i j) (Nat.le_add_right r 2)
        (Work.Diff.STE.summable_wt_pow_mul_norm_sq _ (hmom i j) (r + 2))).trans ?_
      exact (hentry i j).trans (le_mul_of_one_le_left hQM hQ1)
    | lin a i j =>
      have hd := CSq_dmulV_le (ι := Fin n) r [a] (fun m => c m i j) (hmom i j)
      rw [dmulV_single] at hd
      refine hd.trans ?_
      have hmono : Work.Diff.STE.CSq (r + 1) (fun k : Fin n → ℤ => c k i j)
          ≤ Work.Diff.STE.CSq (r + 2) (fun k : Fin n → ℤ => c k i j) :=
        ncb_CSq_mono_le _ (by omega) (Work.Diff.STE.summable_wt_pow_mul_norm_sq _ (hmom i j) (r + 2))
      have hle1 : ((2 * Real.pi) ^ 2) ^ ([a]).length ≤ ((2 * Real.pi) ^ 2) ^ 2 :=
        pow_le_pow_right₀ ncb_one_le_two_pi_sq (by simp)
      calc ((2 * Real.pi) ^ 2) ^ ([a]).length
              * Work.Diff.STE.CSq (r + [a].length) (fun k : Fin n → ℤ => c k i j)
          ≤ ((2 * Real.pi) ^ 2) ^ 2
              * Work.Diff.STE.CSq (r + 2) (fun k : Fin n → ℤ => c k i j) := by
            rw [List.length_cons, List.length_nil]
            exact mul_le_mul hle1 hmono (CSq_nonneg' _ _) (by positivity)
        _ ≤ ((2 * Real.pi) ^ 2) ^ 2 * CSqM (r + 2) c :=
            mul_le_mul_of_nonneg_left (hentry i j) (by positivity)
    | sec a b i j =>
      have hd := CSq_dmulV_le (ι := Fin n) r [a, b] (fun m => c m i j) (hmom i j)
      rw [show Work.Diff.STE.dmulV [a, b] (fun m : Fin n → ℤ => c m i j)
          = Work.Diff.STE.dmul a (Work.Diff.STE.dmul b (fun m : Fin n → ℤ => c m i j)) by
        rw [show ([a, b] : List (Fin n)) = a :: [b] from rfl, Work.Diff.STE.dmulV_cons,
          dmulV_single]] at hd
      refine hd.trans ?_
      refine mul_le_mul_of_nonneg_left (hentry i j) (by positivity)
  have hsum_const : (∑ _w : JetIx n, (((2 * Real.pi) ^ 2) ^ 2 * CSqM (r + 2) c))
      = (Fintype.card (JetIx n) : ℝ) * (((2 * Real.pi) ^ 2) ^ 2 * CSqM (r + 2) c) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Equiv.sum_comp (jetIdxEquiv n) (fun p : Fin (Fintype.card (JetIx n)) =>
    Work.Diff.STE.CSq r (fun k => jetData c k p))]
  refine le_trans (Finset.sum_le_sum fun w _ => ?_) (le_of_eq hsum_const)
  have hfun : (fun k : Fin n → ℤ => jetData c k ((jetIdxEquiv n) w))
      = fun k => jetDataVec c k w := by
    funext k
    simp [jetData]
  rw [hfun]
  exact hper w

end


/-! ## A smooth cutoff on the good (elliptic) set -/

/-- **A smooth cutoff function for the good set.**  The good set is closed (all its defining
conditions are closed) and contained in the open nondegenerate locus where `det (reMat ·) ≠ 0`;
a smooth bump supported in the latter and equal to `1` on the former therefore exists. -/
lemma cutoffGoodSet (n : ℕ) (hn : 1 ≤ n) (lam : ℝ) (hlam : 0 < lam) (KA : ℝ) :
    ∃ χ : Jet n → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ (∀ w, 0 ≤ χ w) ∧
      tsupport χ ⊆ {w : Jet n | (reMat w.1).det ≠ 0} ∧
      (∀ w : Jet n, w ∈ goodSet n lam KA → χ w = 1) := by
  classical
  have hdet : IsOpen {w : Jet n | (reMat w.1).det ≠ 0} := isOpen_det_reMat_ne_zero n
  have hsub : goodSet n lam KA ⊆ {w : Jet n | (reMat w.1).det ≠ 0} := by
    intro w hw
    obtain ⟨-, -, -, hquad⟩ := hw
    exact det_ne_zero_of_quadForm_le (reMat w.1) (by linarith) hquad
  -- each of the four defining conditions is closed
  have hc_val : ∀ i j : Fin n, IsClosed {w : Jet n | ‖w.1 i j‖ ≤ KA} := fun i j =>
    isClosed_le (by fun_prop) continuous_const
  have hc_lin : ∀ c i j : Fin n, IsClosed {w : Jet n | ‖w.2.1 c i j‖ ≤ KA} := fun c i j =>
    isClosed_le (by fun_prop) continuous_const
  have hc_sec : ∀ c d i j : Fin n, IsClosed {w : Jet n | ‖w.2.2 c d i j‖ ≤ KA} := fun c d i j =>
    isClosed_le (by fun_prop) continuous_const
  have hc_quad : ∀ v : Fin n → ℝ, IsClosed {w : Jet n | (lam / 2) * ∑ i, (v i) ^ 2 ≤
      ∑ i, ∑ j, reMat w.1 i j * v i * v j} := fun v =>
    isClosed_le continuous_const (by simp only [reMat]; fun_prop)
  have hclosed : IsClosed (goodSet n lam KA) := by
    have hEq : goodSet n lam KA = (⋂ i, ⋂ j, {w : Jet n | ‖w.1 i j‖ ≤ KA}) ∩
        ((⋂ c, ⋂ i, ⋂ j, {w : Jet n | ‖w.2.1 c i j‖ ≤ KA}) ∩
        ((⋂ c, ⋂ d, ⋂ i, ⋂ j, {w : Jet n | ‖w.2.2 c d i j‖ ≤ KA}) ∩
        (⋂ v : Fin n → ℝ, {w : Jet n | (lam / 2) * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
          reMat w.1 i j * v i * v j}))) := by
      unfold goodSet
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [hEq]
    exact IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => hc_val i j)
      (IsClosed.inter (isClosed_iInter fun c => isClosed_iInter fun i =>
          isClosed_iInter fun j => hc_lin c i j)
        (IsClosed.inter (isClosed_iInter fun c => isClosed_iInter fun d =>
            isClosed_iInter fun i => isClosed_iInter fun j => hc_sec c d i j)
          (isClosed_iInter fun v => hc_quad v)))
  obtain ⟨W, hWopen, hKcW, hWV⟩ := normal_exists_closure_subset hclosed hdet hsub
  obtain ⟨χ, hχdiff, hχrange, hχsupp, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hWopen hclosed hKcW
  refine ⟨χ, hχdiff, fun w => (hχrange ⟨w, rfl⟩).1, ?_, fun w hw => (hχone w).mp hw⟩
  show closure (Function.support χ) ⊆ {w : Jet n | (reMat w.1).det ≠ 0}
  rw [hχsupp]
  exact hWV


/-! ## The factorisation of a periodic smooth function through the characters

The nonlinearity `Φ` is smooth only on the nondegenerate locus and depends on the base point `x`
(periodically).  To apply the Moser composition estimate it must be written as a *globally* smooth
function of the characters `z_j = exp (2 π i x_j)` (these, unlike `x` itself, are Fourier series of
finitely supported families).  We build that factorisation from a finite partition of unity over
the two branches of the complex logarithm, following the construction of
`Work.Diff.STE.flat.periodic_factor` (`Submission/Work/Diff/STE/flat/periodic_defs.lean`).

For each coordinate one has two angle functions

* `thetaP z = (log z).im / (2π)` — smooth on the slit plane `{0 < re} ∪ {im ≠ 0}`, and
* `thetaM z = (log (-z)).im / (2π) + 1/2` — smooth on `{re < 0} ∪ {im ≠ 0}`,

with `exp (2 π i · thetaP z) = z` and `exp (2 π i · thetaM z) = z` on the unit circle.  The weights
`wB true z = hBump z.re * kBump ‖z‖²`, `wB false z = (1 - hBump z.re) * kBump ‖z‖²` vanish off the
corresponding branch domain and sum to `kBump ‖z‖²`, which is `1` on the unit circle.  Assembling
`Ξ (z, v) = ∑_s (∏_j wB (s j) (z j)) • Φ (fun j => thetaB (s j) (z j), v)` therefore gives a
globally smooth function with `Ξ (chars x, v) = Φ (x, v)`. -/

lemma pf_contDiff_re : ContDiff ℝ (⊤ : ℕ∞) Complex.re := Complex.reCLM.contDiff

lemma pf_contDiff_im : ContDiff ℝ (⊤ : ℕ∞) Complex.im := Complex.imCLM.contDiff

lemma pf_contDiff_normSq : ContDiff ℝ (⊤ : ℕ∞) fun z : ℂ => ‖z‖ ^ 2 := by
  have h : (fun z : ℂ => ‖z‖ ^ 2) = fun z => z.re ^ 2 + z.im ^ 2 := by
    funext z
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [h]
  simpa only [pow_two] using
    ((pf_contDiff_re.mul pf_contDiff_re).add (pf_contDiff_im.mul pf_contDiff_im))

lemma pf_contDiff_hBump : ContDiff ℝ (⊤ : ℕ∞) hBump := by
  unfold hBump
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

lemma pf_contDiff_kBump : ContDiff ℝ (⊤ : ℕ∞) kBump := by
  unfold kBump
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Real.smoothTransition.contDiff.comp (by fun_prop))

lemma pf_contDiff_wB (s : Bool) : ContDiff ℝ (⊤ : ℕ∞) (wB s) := by
  have hk : ContDiff ℝ (⊤ : ℕ∞) fun z : ℂ => kBump (‖z‖ ^ 2) :=
    pf_contDiff_kBump.comp pf_contDiff_normSq
  have hr : ContDiff ℝ (⊤ : ℕ∞) fun z : ℂ => hBump z.re :=
    pf_contDiff_hBump.comp pf_contDiff_re
  cases s with
  | true =>
    rw [show wB true = fun z : ℂ => hBump z.re * kBump (‖z‖ ^ 2) from
      funext fun z => wB_true z]
    exact hr.mul hk
  | false =>
    rw [show wB false = fun z : ℂ => (1 - hBump z.re) * kBump (‖z‖ ^ 2) from
      funext fun z => wB_false z]
    exact (contDiff_const.sub hr).mul hk

lemma pf_two_pi_I_mul_thetaP (z : ℂ) :
    2 * Real.pi * Complex.I * ((thetaP z : ℝ) : ℂ) = (Complex.arg z : ℂ) * Complex.I := by
  rw [show thetaP z = z.arg / (2 * Real.pi) from by simp [thetaP, Complex.log_im]]
  have h : (((z.arg / (2 * Real.pi) : ℝ)) : ℂ)
      = (z.arg : ℂ) * ((((2 * Real.pi : ℝ)) : ℂ))⁻¹ := by
    push_cast
    ring
  rw [h]
  have hne : (((2 * Real.pi : ℝ)) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    positivity
  field_simp
  push_cast
  ring

lemma pf_thetaP_exp (z : ℂ) (h : ‖z‖ = 1) :
    Complex.exp (2 * Real.pi * Complex.I * ((thetaP z : ℝ) : ℂ)) = z := by
  rw [pf_two_pi_I_mul_thetaP]
  have h1 := Complex.norm_mul_exp_arg_mul_I z
  rw [h] at h1
  simpa using h1

lemma pf_thetaM_exp (z : ℂ) (h : ‖z‖ = 1) :
    Complex.exp (2 * Real.pi * Complex.I * ((thetaM z : ℝ) : ℂ)) = z := by
  have hz : thetaM z = thetaP (-z) + 1 / 2 := rfl
  have hP : Complex.exp (2 * Real.pi * Complex.I * ((thetaP (-z) : ℝ) : ℂ)) = -z :=
    pf_thetaP_exp (-z) (by rw [norm_neg]; exact h)
  have hcast : (((thetaP (-z) + 1 / 2 : ℝ)) : ℂ)
      = ((thetaP (-z) : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hz, hcast, mul_add, Complex.exp_add, hP]
  have h2 : (2 : ℂ) * Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ) = (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h2, Complex.exp_pi_mul_I]
  ring

lemma pf_contDiffAt_thetaB (s : Bool) {z : ℂ} (h : good s z) :
    ContDiffAt ℝ (⊤ : ℕ∞) (thetaB s) z := by
  cases s with
  | true =>
    have hlog : ContDiffAt ℝ (⊤ : ℕ∞) Complex.log z :=
      ContDiffAt.restrict_scalars ℝ (Complex.contDiffAt_log h)
    have him : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : ℂ => (Complex.log w).im) z :=
      (Complex.imCLM.contDiff.contDiffAt).comp z hlog
    rw [show thetaB true = fun w : ℂ => (Complex.log w).im / (2 * Real.pi) from by
      funext w; simp [thetaB, thetaP]]
    exact him.div_const (2 * Real.pi)
  | false =>
    have hlog : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : ℂ => Complex.log (-w)) z :=
      (ContDiffAt.restrict_scalars ℝ (Complex.contDiffAt_log h)).comp z contDiff_neg.contDiffAt
    have him : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : ℂ => (Complex.log (-w)).im) z :=
      (Complex.imCLM.contDiff.contDiffAt).comp z hlog
    rw [show thetaB false = fun w : ℂ => (Complex.log (-w)).im / (2 * Real.pi) + 1 / 2 from by
      funext w; simp [thetaB, thetaM]]
    exact (him.div_const (2 * Real.pi)).add contDiffAt_const

lemma pf_wB_eventually_zero {s : Bool} {z : ℂ} (h : ¬ good s z) :
    ∀ᶠ w in nhds z, wB s w = 0 := by
  cases s with
  | true =>
    have h' : ¬ (z ∈ Complex.slitPlane) := h
    have hre : z.re ≤ 0 := by
      by_contra hlt
      exact h' (Or.inl (lt_of_not_ge hlt))
    have him : z.im = 0 := by
      by_contra hne
      exact h' (Or.inr hne)
    rcases lt_or_ge z.re (-1 / 8) with hlt | hge
    · filter_upwards [isOpen_lt Complex.continuous_re continuous_const |>.mem_nhds hlt] with w hw
      rw [wB_true, hBump_zero (le_of_lt hw), zero_mul]
    · have hz1 : ‖z‖ ≤ 1 / 8 := by
        have h2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          ring
        have h3 : ‖z‖ ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := by
          rw [h2, him]
          nlinarith
        nlinarith [norm_nonneg z]
      filter_upwards [Metric.ball_mem_nhds z (by norm_num : (0 : ℝ) < 1 / 8)] with w hw
      have hwd : ‖w - z‖ < 1 / 8 := by
        simpa [dist_eq_norm] using Metric.mem_ball.mp hw
      have hwn : ‖w‖ ≤ 1 / 8 + 1 / 8 := by
        calc ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
          _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
          _ ≤ 1 / 8 + 1 / 8 := by linarith
      have hk : ‖w‖ ^ 2 ≤ 1 / 16 := by nlinarith [norm_nonneg w]
      rw [wB_true, kBump_zero_of_le hk, mul_zero]
  | false =>
    have h' : ¬ ((-z) ∈ Complex.slitPlane) := h
    have hre : 0 ≤ z.re := by
      have h1 : ¬ (0 < (-z).re) := fun hh => h' (Or.inl hh)
      rw [Complex.neg_re] at h1
      linarith
    have him : z.im = 0 := by
      have h1 : ¬ ((-z).im ≠ 0) := fun hh => h' (Or.inr hh)
      rw [Complex.neg_im] at h1
      simpa using h1
    rcases lt_or_eq_of_le hre with hpos | hzero
    · filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hpos] with w hw
      rw [wB_false, hBump_one (le_of_lt hw), sub_self, zero_mul]
    · have hz0 : z = 0 := by
        apply Complex.ext
        · exact hzero.symm
        · exact him
      subst hz0
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 4)] with w hw
      have hwd : ‖w‖ < 1 / 4 := by
        simpa [dist_eq_norm, sub_zero] using Metric.mem_ball.mp hw
      have hk : ‖w‖ ^ 2 ≤ 1 / 16 := by nlinarith [norm_nonneg w]
      rw [wB_false, kBump_zero_of_le hk, mul_zero]

lemma pf_sum_wB {n : ℕ} (w : Fin n → ℂ) :
    (∑ s : Fin n → Bool, ∏ j, wB (s j) (w j)) = ∏ j, kBump (‖w j‖ ^ 2) := by
  rw [← Fintype.prod_sum (f := fun j (s : Bool) => wB s (w j))]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [Fintype.sum_bool, wB_true, wB_false]
  ring

lemma pf_norm_charExp {n : ℕ} (x : Fin n → ℝ) (j : Fin n) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (x j : ℂ))‖ = 1 := by
  have h : 2 * Real.pi * Complex.I * (x j : ℂ) = ((2 * Real.pi * x j : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

lemma pf_periodic_int {n m : ℕ} (Φ : (Fin n → ℝ) × (Fin m → ℂ) → ℂ)
    (hper : ∀ (v : Fin m → ℂ) (i : Fin n) (x : Fin n → ℝ), Φ (x + Pi.single i 1, v) = Φ (x, v))
    (u : Fin n → ℤ) (x : Fin n → ℝ) (v : Fin m → ℂ) :
    Φ (x + fun j => (u j : ℝ), v) = Φ (x, v) := by
  let S : AddSubgroup (Fin n → ℝ) :=
    { carrier := {w | ∀ (x : Fin n → ℝ) (v : Fin m → ℂ), Φ (x + w, v) = Φ (x, v)}
      zero_mem' := by intro x v; simp
      add_mem' := by
        intro a b ha hb x v
        have h1 : x + (a + b) = (x + a) + b := by abel
        rw [h1, hb, ha]
      neg_mem' := by
        intro a ha x v
        have h1 := ha (x + (-a)) v
        have h2 : x + (-a) + a = x := by abel
        rw [h2] at h1
        exact h1.symm }
  have hsingle : ∀ i : Fin n, Pi.single i (1 : ℝ) ∈ S := fun i x v => hper v i x
  have hdec : (∑ j : Fin n, (u j) • (Pi.single j (1 : ℝ))) = fun j : Fin n => (u j : ℝ) := by
    funext i
    simp_rw [Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      rw [Pi.single_eq_of_ne' hb, smul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hmem : (fun j : Fin n => (u j : ℝ)) ∈ S := by
    rw [← hdec]
    exact S.sum_mem (fun j _ => S.zsmul_mem (hsingle j) (u j))
  exact hmem x v

lemma pf_exists_int_of_exp_eq {θ x : ℝ}
    (h : Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ))
        = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) :
    ∃ m : ℤ, θ = x + m := by
  rw [Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  have hA : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have key : (2 * Real.pi * Complex.I : ℂ) * ((θ : ℂ) - (x : ℂ))
      = (2 * Real.pi * Complex.I : ℂ) * (k : ℂ) := by
    rw [mul_sub, hk]
    ring
  have h2 : (θ : ℂ) - (x : ℂ) = (k : ℂ) := mul_left_cancel₀ hA key
  have h3 : ((θ - x : ℝ) : ℂ) = ((k : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub, h2, Complex.ofReal_intCast]
  have h4 : θ - x = (k : ℝ) := Complex.ofReal_injective h3
  linarith

lemma pf_phi_thetaB_char {n m : ℕ} (Φ : (Fin n → ℝ) × (Fin m → ℂ) → ℂ)
    (hper : ∀ (v : Fin m → ℂ) (i : Fin n) (x : Fin n → ℝ), Φ (x + Pi.single i 1, v) = Φ (x, v))
    (s : Fin n → Bool) (x : Fin n → ℝ) (v : Fin m → ℂ) :
    Φ ((fun j : Fin n => thetaB (s j) (Complex.exp (2 * Real.pi * Complex.I * (x j : ℂ)))), v)
      = Φ (x, v) := by
  have hexp : ∀ j : Fin n,
      Complex.exp (2 * Real.pi * Complex.I
        * ((thetaB (s j) (Complex.exp (2 * Real.pi * Complex.I * (x j : ℂ))) : ℝ) : ℂ))
        = Complex.exp (2 * Real.pi * Complex.I * (x j : ℂ)) := by
    intro j
    cases hs : s j with
    | true => exact pf_thetaP_exp _ (pf_norm_charExp x j)
    | false => exact pf_thetaM_exp _ (pf_norm_charExp x j)
  have hex : ∀ j : Fin n, ∃ m : ℤ,
      thetaB (s j) (Complex.exp (2 * Real.pi * Complex.I * (x j : ℂ))) = x j + m :=
    fun j => pf_exists_int_of_exp_eq (hexp j)
  choose u hu using hex
  have hfun : (fun j : Fin n => thetaB (s j) (Complex.exp (2 * Real.pi * Complex.I * (x j : ℂ))))
      = x + fun j => (u j : ℝ) := by
    funext j
    exact hu j
  rw [hfun]
  exact pf_periodic_int Φ hper u x v

lemma pf_contDiff_assembled {n m : ℕ} (Φ : (Fin n → ℝ) × (Fin m → ℂ) → ℂ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : (Fin n → ℂ) × (Fin m → ℂ) =>
      ∑ s : Fin n → Bool, (∏ j, wB (s j) (p.1 j))
        • Φ ((fun j => thetaB (s j) (p.1 j)), p.2)) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  apply ContDiffAt.sum
  intro s _
  by_cases hg : ∀ j, good (s j) (p.1 j)
  · have hW : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun q : (Fin n → ℂ) × (Fin m → ℂ) => ∏ j, wB (s j) (q.1 j)) p :=
      contDiffAt_prod (fun j _ => (pf_contDiff_wB (s j)).contDiffAt.comp p
        ((contDiffAt_pi.mp (contDiffAt_fst (p := p))) j))
    have hθ : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun q : (Fin n → ℂ) × (Fin m → ℂ) => ((fun j => thetaB (s j) (q.1 j)), q.2)) p :=
      (contDiffAt_pi.mpr (fun j => (pf_contDiffAt_thetaB (s j) (hg j)).comp p
        ((contDiffAt_pi.mp (contDiffAt_fst (p := p))) j))).prodMk contDiffAt_snd
    exact hW.smul (hΦ.contDiffAt.comp p hθ)
  · push_neg at hg
    obtain ⟨j₀, hj₀⟩ := hg
    have hcont : Continuous fun q : (Fin n → ℂ) × (Fin m → ℂ) => q.1 j₀ :=
      (continuous_apply j₀).comp continuous_fst
    have hev : ∀ᶠ q in nhds p, wB (s j₀) (q.1 j₀) = 0 :=
      hcont.continuousAt.eventually (pf_wB_eventually_zero hj₀)
    have hzero : (fun q : (Fin n → ℂ) × (Fin m → ℂ) => (∏ j, wB (s j) (q.1 j))
        • Φ ((fun j => thetaB (s j) (q.1 j)), q.2)) =ᶠ[nhds p] 0 := by
      filter_upwards [hev] with q hq
      have hp : (∏ j, wB (s j) (q.1 j)) = 0 := by
        rw [← Finset.mul_prod_erase Finset.univ (fun j => wB (s j) (q.1 j))
          (Finset.mem_univ j₀), hq, zero_mul]
      simp [hp]
    exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hzero

lemma pf_periodicFactor {n m : ℕ}
    (Φ : (Fin n → ℝ) × (Fin m → ℂ) → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hper : ∀ (v : Fin m → ℂ) (i : Fin n) (x : Fin n → ℝ), Φ (x + Pi.single i 1, v) = Φ (x, v)) :
    ∃ Ξ : (Fin n → ℂ) × (Fin m → ℂ) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Ξ ∧
        ∀ (x : Fin n → ℝ) (v : Fin m → ℂ),
          Ξ ((fun j : Fin n => Complex.exp (2 * Real.pi * Complex.I * (x j : ℂ))), v)
            = Φ (x, v) := by
  refine ⟨fun p => ∑ s : Fin n → Bool, (∏ j, wB (s j) (p.1 j))
      • Φ ((fun j => thetaB (s j) (p.1 j)), p.2), pf_contDiff_assembled Φ hΦ, ?_⟩
  intro x v
  have hprod : (∏ j : Fin n,
      kBump (‖Complex.exp (2 * Real.pi * Complex.I * (x j : ℂ))‖ ^ 2)) = 1 := by
    refine Finset.prod_eq_one fun j _ => ?_
    rw [pf_norm_charExp x j]
    exact kBump_one (by norm_num) (by norm_num)
  calc ∑ s : Fin n → Bool,
        (∏ j, wB (s j) (Complex.exp (2 * Real.pi * Complex.I * (x j : ℂ))))
          • Φ ((fun j : Fin n => thetaB (s j)
              (Complex.exp (2 * Real.pi * Complex.I * (x j : ℂ)))), v)
      = ∑ s : Fin n → Bool,
          (∏ j, wB (s j) (Complex.exp (2 * Real.pi * Complex.I * (x j : ℂ)))) • Φ (x, v) :=
        Finset.sum_congr rfl fun s _ => by rw [pf_phi_thetaB_char Φ hper s x v]
    _ = (∑ s : Fin n → Bool,
          ∏ j, wB (s j) (Complex.exp (2 * Real.pi * Complex.I * (x j : ℂ)))) • Φ (x, v) := by
        rw [Finset.sum_smul]
    _ = (∏ j : Fin n,
          kBump (‖Complex.exp (2 * Real.pi * Complex.I * (x j : ℂ))‖ ^ 2)) • Φ (x, v) := by
        rw [pf_sum_wB]
    _ = (1 : ℝ) • Φ (x, v) := by rw [hprod]
    _ = Φ (x, v) := one_smul ℝ _

/-- **The coefficient bound for the nonlinearity**, taking the factorisation of periodic smooth
functions through the characters (`Work.Diff.STE.flat.FactorStatement`) as a hypothesis, so that
the main argument is independent of the analytic construction of the factorisation. -/
theorem nonlin_coeff_bound_of_factor (hfactor : FactorStatement)
    {n : ℕ} (hn : 1 ≤ n)
    (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (hshape : IsDeTurckNonlin Φ)
    (k : ℕ) (hk : n + 4 < 2 * k)
    (lam : ℝ) (hlam : 0 < lam) (E : ℝ) (hE : 0 ≤ E) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
      (∀ k', k' ∉ box n N → c k' = 0) →
      (∀ j ≤ k, CSqM j c ≤ E) →
      (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        (lam / 2) * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
          reMat (seriesFunM c x) i j * v i * v j) →
      ∀ i j : Fin n,
        Summable (fun m : Fin n → ℤ => ‖fourierCoeff
          (fun x => Φ (x, jetM (seriesFunM c) x) i j) m‖) ∧
        (∑' m : Fin n → ℤ, ‖fourierCoeff
          (fun x => Φ (x, jetM (seriesFunM c) x) i j) m‖) ≤ Λ := by
  classical
  -- ### arithmetic
  have hsobk : sob n + 2 ≤ k := by
    have hdec : 2 * (n / 2) + n % 2 = n := Nat.div_add_mod n 2
    have hmod : n % 2 = 0 ∨ n % 2 = 1 := by
      have h := Nat.mod_lt n (by norm_num : 0 < 2)
      omega
    simp only [sob]
    rcases hmod with h | h <;> omega
  have hρ : Fintype.card (Fin n) < 2 * sob n := by simpa using n_lt_two_sob n
  have hρs : sob n ≤ k - 2 := by omega
  have hs_card : Fintype.card (Fin n) < 2 * (k - 2) := by
    simp only [Fintype.card_fin]
    omega
  -- ### the uniform sup bound on the jets and the good set
  obtain ⟨Cs, hCs0, hCs⟩ := Work.Diff.STE.norm_seriesFun_le (ι := Fin n) (sob n) hρ
  set KA : ℝ := Cs * (2 * Real.pi) ^ 2 * (1 + Real.sqrt E) with hKAdef
  -- ### the cut-off and the extended nonlinearity
  obtain ⟨θ, hθdiff, -, hθtsup, hθone⟩ := cutoffGoodSet n hn lam hlam KA
  set Φθ : (Fin n → ℝ) × Jet n → MatC n := fun p => (θ p.2 : ℂ) • Φ p with hΦθdef
  have hΦθsmooth : ContDiff ℝ (⊤ : ℕ∞) Φθ := by
    rw [hΦθdef]
    exact cutoff_mul_contDiff n Φ hshape.1 θ hθdiff hθtsup
  have hperθ : ∀ (w : Jet n) (i : Fin n) (x : Fin n → ℝ),
      Φθ (x + Pi.single i 1, w) = Φθ (x, w) := by
    intro w i x
    by_cases hd : (reMat w.1).det = 0
    · have hθw : θ w = 0 := by
        by_contra hne
        exact (hθtsup (subset_closure (Function.mem_support.mpr hne))) hd
      simp only [hΦθdef, hθw, Complex.ofReal_zero, zero_smul]
    · obtain ⟨-, N, hNsm, hN, hNper⟩ := hshape
      have hΦp : Φ (x + Pi.single i 1, w) = Φ (x, w) := by
        rw [hN (x + Pi.single i 1) w.1 w.2.1 w.2.2 hd, hN x w.1 w.2.1 w.2.2 hd]
        simp only [hNper (w.1, w.2.1) i x]
      simp only [hΦθdef, hΦp]
  -- ### the vectorised nonlinearity
  set Φv : (Fin n → ℝ) × (Fin (Fintype.card (JetIx n)) → ℂ) → MatC n :=
    fun p => Φθ (p.1, jetUnpack (jetIdxEquiv n) p.2) with hΦvdef
  have hΦvsmooth : ∀ i j : Fin n, ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (Fin n → ℝ) × (Fin (Fintype.card (JetIx n)) → ℂ) => Φv p i j) := by
    intro i j
    have h1 : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : (Fin n → ℝ) × (Fin (Fintype.card (JetIx n)) → ℂ) =>
          (p.1, jetUnpack (jetIdxEquiv n) p.2)) :=
      ContDiff.prodMk contDiff_fst ((contDiff_jetUnpack (jetIdxEquiv n)).comp contDiff_snd)
    have h2 : ContDiff ℝ (⊤ : ℕ∞) Φv := by
      rw [hΦvdef]
      exact hΦθsmooth.comp h1
    exact ((contDiff_apply_matC i j)).comp h2
  have hΦvper : ∀ i j : Fin n,
      ∀ (v : Fin (Fintype.card (JetIx n)) → ℂ) (d : Fin n) (x : Fin n → ℝ),
        Φv (x + Pi.single d 1, v) i j = Φv (x, v) i j := by
    intro i j v d x
    simp only [hΦvdef]
    rw [hperθ (jetUnpack (jetIdxEquiv n) v) d x]
  -- ### the Moser estimate, with a constant independent of `N` and `c`
  set B : ℝ := Real.sqrt ((Fintype.card (JetIx n) : ℝ) * (((2 * Real.pi) ^ 2) ^ 2 * E))
    with hBdef
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hB2 : B ^ 2 = (Fintype.card (JetIx n) : ℝ) * (((2 * Real.pi) ^ 2) ^ 2 * E) := by
    rw [hBdef, Real.sq_sqrt]
    positivity
  obtain ⟨Cl1, hCl10, hCl1⟩ := Work.Diff.STE.l1_le_sqrt_CSq (ι := Fin n) (k - 2) hs_card
  set D : ℝ := (Fintype.card (JetIx n) : ℝ) * (((2 * Real.pi) ^ 2) ^ 2 * E) with hDdef
  have hMoser : ∀ i j : Fin n, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (c' : (Fin n → ℤ) → (Fin (Fintype.card (JetIx n)) → ℂ)),
        (∀ N' : ℕ, Summable (fun m : Fin n → ℤ => (Work.Diff.STE.wt m) ^ N' * ‖c' m‖)) →
        (∑ p : Fin (Fintype.card (JetIx n)),
            Work.Diff.STE.CSq (sob n) (fun m => c' m p)) ≤ B ^ 2 →
        Summable (fun m : Fin n → ℤ => (Work.Diff.STE.wt m) ^ (k - 2) *
            ‖Work.Diff.STE.fourierCoeff (fun x : Fin n → ℝ =>
              Φv (x, fun p => Work.Diff.STE.seriesFun (fun m => c' m p) x) i j) m‖ ^ 2) ∧
        Work.Diff.STE.CSq (k - 2) (Work.Diff.STE.fourierCoeff (fun x : Fin n → ℝ =>
              Φv (x, fun p => Work.Diff.STE.seriesFun (fun m => c' m p) x) i j))
          ≤ C * (1 + ∑ p : Fin (Fintype.card (JetIx n)),
              Work.Diff.STE.CSq (k - 2) (fun m => c' m p)) := by
    intro i j
    exact CSq_comp_xperiodic_le_of_factor (n := n) (m := Fintype.card (JetIx n))
      hfactor (k - 2) (sob n) (by simpa using hρ) hρs
      (fun p : (Fin n → ℝ) × (Fin (Fintype.card (JetIx n)) → ℂ) => Φv p i j)
      (hΦvsmooth i j) (hΦvper i j) B hB0
  -- ### the per-entry conclusion
  have hne : (Finset.univ : Finset (Fin n × Fin n)).Nonempty :=
    ⟨(⟨0, hn⟩, ⟨0, hn⟩), Finset.mem_univ _⟩
  refine ⟨max 0 ((Finset.univ : Finset (Fin n × Fin n)).sup' hne
      (fun ij => Cl1 * Real.sqrt (Classical.choose (hMoser ij.1 ij.2) * (1 + D)))),
    le_max_left _ _, ?_⟩
  intro N c hc hcsq hell i j
  have hmom : ∀ (i j : Fin n) (M : ℕ),
      Summable (fun m : Fin n → ℤ => (Work.Diff.STE.wt m) ^ M * ‖c m i j‖) :=
    fun i j M => summable_moment_box c hc i j M
  -- the data bound at level `sob n`
  have hdatab : (∑ p : Fin (Fintype.card (JetIx n)),
      Work.Diff.STE.CSq (sob n) (fun m => jetData c m p)) ≤ B ^ 2 := by
    rw [hB2]
    refine (sum_CSq_jetData_le c hc (sob n)).trans ?_
    have h2 : CSqM (sob n + 2) c ≤ E := hcsq (sob n + 2) hsobk
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left h2 (by positivity)) (by positivity)
  -- moment summability of the data
  have hdatamom : ∀ N' : ℕ,
      Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ N' * ‖jetData c k‖) := by
    intro N'
    have hperw : ∀ w : JetIx n,
        Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ N' * ‖jetDataVec c k w‖) := by
      intro w
      cases w with
      | val i j => exact hmom i j N'
      | lin a i j =>
        simpa only [jetDataVec] using summable_dmul_moments a _ (hmom i j) N'
      | sec a b i j =>
        simpa only [jetDataVec] using
          summable_dmul_moments a _ (summable_dmul_moments b _ (hmom i j)) N'
    have hvec : Summable (fun k : Fin n → ℤ =>
        (Work.Diff.STE.wt k) ^ N' * ∑ w : JetIx n, ‖jetDataVec c k w‖) := by
      have h := summable_sum (s := Finset.univ) (fun w _ => hperw w)
      simpa only [Finset.mul_sum] using h
    have hnorm : ∀ k : Fin n → ℤ, ‖jetData c k‖ ≤ ∑ w : JetIx n, ‖jetDataVec c k w‖ := by
      intro k
      have h1 : ‖jetData c k‖ ≤ ∑ p : Fin (Fintype.card (JetIx n)), ‖jetData c k p‖ :=
        (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun p =>
          Finset.single_le_sum (f := fun p : Fin (Fintype.card (JetIx n)) => ‖jetData c k p‖)
            (fun p _ => norm_nonneg _) (Finset.mem_univ p)
      have h2 : (∑ p : Fin (Fintype.card (JetIx n)), ‖jetData c k p‖)
          = ∑ w : JetIx n, ‖jetDataVec c k w‖ := by
        rw [← Equiv.sum_comp (jetIdxEquiv n) (fun p => ‖jetData c k p‖)]
        exact Finset.sum_congr rfl fun w _ => by simp [jetData]
      rw [h2] at h1
      exact h1
    refine Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) N') (norm_nonneg _))
      (fun k => mul_le_mul_of_nonneg_left (hnorm k)
        (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) N')) hvec
  obtain ⟨hsumm, hbound⟩ :=
    (Classical.choose_spec (hMoser i j)).2 (jetData c) hdatamom hdatab
  -- the identification of the composite with the nonlinearity at the jet
  have hfun : (fun y : Fin n → ℝ => Φv (y, fun p => Work.Diff.STE.seriesFun
        (fun k => jetData c k p) y) i j) = fun y => Φ (y, jetM (seriesFunM c) y) i j := by
    funext y
    have h1 := jetUnpack_jetData c hc y
    have h2 : θ (jetM (seriesFunM c) y) = 1 :=
      hθone _ (jetMem_goodSet c hc hE hcsq hsobk hCs0 hCs lam hell y)
    simp only [hΦvdef, h1]
    rw [hΦθdef]
    simp [h2]
  rw [hfun] at hsumm hbound
  -- the data bound at level `k - 2`
  have hdatas : (∑ p : Fin (Fintype.card (JetIx n)),
      Work.Diff.STE.CSq (k - 2) (fun k => jetData c k p)) ≤ D := by
    rw [hDdef]
    refine (sum_CSq_jetData_le c hc (k - 2)).trans ?_
    have h2 : CSqM (k - 2 + 2) c ≤ E := hcsq (k - 2 + 2) (by omega)
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left h2 (by positivity)) (by positivity)
  have hmid : Cl1 * Real.sqrt (Work.Diff.STE.CSq (k - 2) (Work.Diff.STE.fourierCoeff
      (fun y : Fin n → ℝ => Φ (y, jetM (seriesFunM c) y) i j)))
      ≤ Cl1 * Real.sqrt (Classical.choose (hMoser i j) * (1 + D)) := by
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hCl10
    exact hbound.trans (mul_le_mul_of_nonneg_left (by linarith)
      (Classical.choose_spec (hMoser i j)).1)
  refine ⟨Work.Diff.STE.summable_norm_of_CSq (k - 2) hs_card _ hsumm, ?_⟩
  exact (hCl1 _ hsumm).trans (hmid.trans
    ((Finset.le_sup' (fun ij : Fin n × Fin n =>
        Cl1 * Real.sqrt (Classical.choose (hMoser ij.1 ij.2) * (1 + D)))
      (Finset.mem_univ (i, j))).trans (le_max_right _ _)))

/-- **The coefficient bound for the nonlinearity** (the requested lemma). -/
theorem nonlin_coeff_bound {n : ℕ} (hn : 1 ≤ n)
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hshape : Work.Diff.STE.Flat.IsDeTurckNonlin Φ)
    (k : ℕ) (hk : Fintype.card (Fin n) + 4 < 2 * k)
    (lam : ℝ) (hlam : 0 < lam) (E : ℝ) (hE : 0 ≤ E) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
      (∀ k', k' ∉ Work.Diff.STE.Flat.box n N → c k' = 0) →
      (∀ j ≤ k, Work.Diff.STE.Flat.CSqM j c ≤ E) →
      (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        (lam / 2) * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
          Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) i j * v i * v j) →
      ∀ i j : Fin n,
        Summable (fun m : Fin n → ℤ => ‖Work.Diff.STE.fourierCoeff
          (fun x => Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM c) x) i j) m‖) ∧
        (∑' m : Fin n → ℤ, ‖Work.Diff.STE.fourierCoeff
          (fun x => Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM c) x) i j) m‖) ≤ Λ := by
  refine nonlin_coeff_bound_of_factor ?_ hn Φ hshape k (by simpa using hk) lam hlam E hE
  exact fun {n m} Φ hΦ hper => pf_periodicFactor Φ hΦ hper

end Work.Diff.STE.flat

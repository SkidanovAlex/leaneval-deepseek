import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseSym.Basic.exists_graphPoint_close
import Submission.Work.BoseSym.Minimiser.diagonal_nested
import Submission.Work.BoseSym.Mollify.convC_isL2_bdd_lip
import Submission.Work.BoseSym.Mollify.convC_zero_off_add
import Submission.Work.BoseSym.Mollify.conv_sub_eLpNorm_le
import Submission.Work.BoseSym.Mollify.mollifier_exists
import Submission.Work.BoseSym.Rellich.gradNorm_le_sum_dir
import Submission.Work.BoseSym.Rellich.lipschitz_precompact
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym.Minimiser — Rellich compactness of `Hsub N L → L²`

A sequence `u n` in the energy space `Hsub N L` (the closure in
`Amb N = L²(Conf N) × ∏_j L²(Conf N)` of the graph of the gradient of the
smooth compactly supported test functions on the box) whose graph norms
`hSq (u n) = ‖(u n).1‖² + ∑_j ‖(u n).2 j‖²` are uniformly bounded has an
`L²`-convergent subsequence.  This is Rellich–Kondrachov compactness of
`H¹₀(box) → L²(box)`, in the form needed by the bosonic reduction (existence
of a minimiser of the box energy).

The proof is the classical one:

* each `u n` is approximated, in the graph norm, by the graph point of a test
  function `F n` (`Basic.exists_graphPoint_close`); the approximation error is
  chosen to be `(n+1)⁻¹`, so it tends to `0` along every subsequence;
* mollifying `F n` at scale `(k+1)⁻¹` produces a sequence `g k n` which is
  uniformly bounded, uniformly Lipschitz and supported in the fixed compact set
  `K + closedBall 0 1`; by Arzelà–Ascoli (`Rellich.lipschitz_precompact`) it
  has a Cauchy subsequence;
* the mollification error is at most `δ_k · B'` with `δ_k = (k+1)⁻¹ → 0`
  (`Mollify.conv_sub_eLpNorm_le`);
* because the extraction at scale `k` has to be compatible with the one at
  scale `k+1`, the extractions are chosen *nested* (`Ω k` is a subsequence of
  `Ω (k-1)`); one diagonal subsequence `ψ` of the nested family is then Cauchy
  for `L²` at every scale, and the approximation errors `ε k → 0` finish the
  argument (`diagonal_nested`).

## Main result

* `Work.BoseSym.Minimiser.rellich_subseq`
-/

namespace Work.BoseSym.Minimiser

open MeasureTheory Filter
open BoseGases
open Submission.BoseGases
open scoped Topology Real ENNReal Pointwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 3000000

/-! ## Elementary properties of the graph norm -/

lemma rs_gSq_nonneg {N : ℕ} (p : Amb N) : 0 ≤ gSq p :=
  Finset.sum_nonneg fun j _ => sq_nonneg _

lemma rs_hSq_nonneg {N : ℕ} (p : Amb N) : 0 ≤ hSq p := by
  have h1 : (0 : ℝ) ≤ ∑ j : GIdx N, ‖p.2 j‖ ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  simp only [hSq, l2Sq, gSq]
  linarith [sq_nonneg ‖p.1‖]

/-- The first component of the ambient space is controlled by the graph norm. -/
lemma rs_norm_fst_le_sqrt_hSq {N : ℕ} (p : Amb N) : ‖p.1‖ ≤ Real.sqrt (hSq p) := by
  rw [Real.le_sqrt (norm_nonneg _) (rs_hSq_nonneg p)]
  calc ‖p.1‖ ^ 2 = l2Sq p := rfl
    _ ≤ hSq p := by
        have := rs_gSq_nonneg p
        simp only [hSq]
        linarith

/-- Each gradient component is controlled by the graph norm. -/
lemma rs_norm_snd_le_sqrt_hSq {N : ℕ} (p : Amb N) (j : GIdx N) :
    ‖p.2 j‖ ≤ Real.sqrt (hSq p) := by
  rw [Real.le_sqrt (norm_nonneg _) (rs_hSq_nonneg p)]
  calc ‖p.2 j‖ ^ 2 ≤ ∑ i : GIdx N, ‖p.2 i‖ ^ 2 :=
        Finset.single_le_sum (f := fun i : GIdx N => ‖p.2 i‖ ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    _ = gSq p := rfl
    _ ≤ hSq p := by
        have := sq_nonneg ‖p.1‖
        simp only [hSq, l2Sq]
        linarith

/-! ## `L²` classes and their distance -/

/-- The `L²` seminorm of a function is the `ofReal` of the norm of its class. -/
lemma rs_eLpNorm_eq_ofReal_norm_toLp {N : ℕ} {g : Conf N → ℝ} (h : MemLp g 2 (volC N)) :
    eLpNorm g 2 (volC N) = ENNReal.ofReal ‖MemLp.toLp g h‖ := by
  rw [Lp.norm_toLp]
  exact (ENNReal.ofReal_toReal (ne_of_lt h.eLpNorm_lt_top)).symm

/-- `toL2` does not depend on the proof of `MemLp`. -/
lemma rs_toL2_congr {N : ℕ} {g : Conf N → ℝ} (h1 h2 : IsL2 N g) :
    toL2 N g h1 = toL2 N g h2 :=
  MemLp.toLp_congr h1 h2 (Filter.EventuallyEq.refl _ _)

/-- The `L²` distance of two `toL2` classes is the (real) `L²` seminorm of the
difference. -/
lemma rs_dist_toL2_eq {N : ℕ} {f g : Conf N → ℝ} (hf : IsL2 N f) (hg : IsL2 N g) :
    dist (toL2 N f hf) (toL2 N g hg) = (eLp2 N (f - g)).toReal := by
  show dist (MemLp.toLp f hf) (MemLp.toLp g hg) = (eLpNorm (f - g) 2 (volC N)).toReal
  rw [dist_eq_norm, ← MemLp.toLp_sub hf hg, Lp.norm_toLp]

/-- `eLp2` of an `L²` function is the `ofReal` of the norm of its class. -/
lemma rs_eLp2_eq_ofReal_norm {N : ℕ} {g : Conf N → ℝ} (h : IsL2 N g) :
    eLp2 N g = ENNReal.ofReal ‖toL2 N g h‖ := by
  show eLpNorm g 2 (volC N) = ENNReal.ofReal ‖MemLp.toLp g h‖
  exact rs_eLpNorm_eq_ofReal_norm_toLp h

/-! ## Support of a convolution -/

/-- The topological support of `convC N f ρ` is contained in the sum of the
topological supports of `f` and `ρ` (both assumed compactly supported). -/
lemma rs_tsupport_convC_subset {N : ℕ} {f ρ : Conf N → ℝ} (hf : HasCompactSupport f)
    (hρ : HasCompactSupport ρ) : tsupport (convC N f ρ) ⊆ tsupport f + tsupport ρ := by
  refine closure_minimal (fun x hx => ?_) (IsCompact.add hf hρ).isClosed
  by_contra hx'
  rw [Set.mem_add] at hx'
  push Not at hx'
  exact hx (Mollify.convC_zero_off_add hx')

/-! ## Compactness for smooth functions -/

/-- **Rellich for smooth functions.** A sequence of smooth compactly supported
functions which are uniformly bounded in `L²` and in the `L²` norm of the
gradient, and whose supports lie in a fixed compact set, has an `L²`-convergent
subsequence. -/
theorem rs_smooth_precompact {N : ℕ} {K : Set (Conf N)} (hK : IsCompact K) {B B' : ℝ}
    (hBnn : 0 ≤ B) (hB'nn : 0 ≤ B') {f : ℕ → Conf N → ℝ} {hf : ∀ n, IsL2 N (f n)}
    (hsm : ∀ n, Smooth1 (f n)) (hcs : ∀ n, HasCompactSupport (f n))
    (hsup : ∀ n, tsupport (f n) ⊆ K)
    (hB : ∀ n, eLp2 N (f n) ≤ ofRealENN B) (hB' : ∀ n, gradNorm N (f n) ≤ ofRealENN B') :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ w : L2 N, Tendsto (fun n => toL2 N (f (φ n)) (hf (φ n))) atTop (nhds w) := by
  classical
  obtain ⟨ρ, hρsm, hρcs, hρ0, hρ1, hρsupp⟩ := Mollify.mollifier_exists N
  -- scalar bounds
  have hBfin : ∀ n, (eLp2 N (f n)).toReal ≤ B := fun n => by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hB n)
    rwa [ENNReal.toReal_ofReal hBnn] at h
  have hB'fin : ∀ n, (gradNorm N (f n)).toReal ≤ B' := fun n => by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hB' n)
    rwa [ENNReal.toReal_ofReal hB'nn] at h
  -- the mollified functions
  let g : ℕ → ℕ → Conf N → ℝ := fun k n => convC N (f n) (ρ k)
  have hg_reg : ∀ k n, IsL2 N (g k n) ∧ (∀ x, |g k n x| ≤ B * (eLp2 N (ρ k)).toReal) ∧
      LipsReal (B' * (eLp2 N (ρ k)).toReal) (g k n) := by
    intro k n
    exact Mollify.convC_isL2_bdd_lip (hsm n) (hcs n) (hρsm k) (hρcs k)
      (mul_nonneg hBnn ENNReal.toReal_nonneg)
      (mul_nonneg hB'nn ENNReal.toReal_nonneg)
      (mul_le_mul_of_nonneg_right (hBfin n) ENNReal.toReal_nonneg)
      (mul_le_mul_of_nonneg_right (hB'fin n) ENNReal.toReal_nonneg)
  have hgsupp : ∀ k n, tsupport (g k n) ⊆ K + Metric.closedBall (0 : Conf N) 1 := by
    intro k n
    refine (rs_tsupport_convC_subset (hcs n) (hρcs k)).trans ?_
    refine Set.add_subset_add (hsup n) ?_
    have hle : ((k : ℝ) + 1)⁻¹ ≤ 1 := by
      have h1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
      rwa [inv_le_one₀ (by positivity)]
    exact (hρsupp k).trans ((Metric.ball_subset_ball hle).trans Metric.ball_subset_closedBall)
  -- *nested* Cauchy subsequences at the mollification scales: the extraction at
  -- scale `k+1` refines the one at scale `k`
  have hstep : ∀ (k : ℕ) (ω : ℕ → ℕ), ∃ θ : ℕ → ℕ, StrictMono θ ∧
      CauchySeq (fun m => toL2 N (g k (ω (θ m))) (hg_reg k (ω (θ m))).1) := by
    intro k ω
    exact Rellich.lipschitz_precompact (K := K + Metric.closedBall (0 : Conf N) 1)
      (hK.add (isCompact_closedBall 0 1)) (fun n => (hg_reg k (ω n)).1)
      (mul_nonneg hB'nn ENNReal.toReal_nonneg) (fun n => (hg_reg k (ω n)).2.1)
      (fun n => (hg_reg k (ω n)).2.2) (fun n => hgsupp k (ω n))
  let Θ : ℕ → (ℕ → ℕ) → (ℕ → ℕ) := fun k ω => Classical.choose (hstep k ω)
  have hΘmono : ∀ (k : ℕ) (ω : ℕ → ℕ), StrictMono (Θ k ω) :=
    fun k ω => (Classical.choose_spec (hstep k ω)).1
  have hΘcau : ∀ (k : ℕ) (ω : ℕ → ℕ), CauchySeq (fun m => toL2 N (g k (ω (Θ k ω m)))
      (hg_reg k (ω (Θ k ω m))).1) := fun k ω => (Classical.choose_spec (hstep k ω)).2
  let Ω : ℕ → ℕ → ℕ := fun k =>
    Nat.rec (motive := fun _ => ℕ → ℕ) (Θ 0 id) (fun j ih => ih ∘ Θ (j + 1) ih) k
  have hΩzero : Ω 0 = Θ 0 id := rfl
  have hΩsucc : ∀ j, Ω (j + 1) = Ω j ∘ Θ (j + 1) (Ω j) := fun j => rfl
  have hΩmono : ∀ k, StrictMono (Ω k) := by
    intro k
    induction k with
    | zero => rw [hΩzero]; exact hΘmono 0 id
    | succ j ih =>
        rw [hΩsucc j]
        exact ih.comp (hΘmono (j + 1) (Ω j))
  have hΩstep : ∀ k, ∃ θ : ℕ → ℕ, StrictMono θ ∧ Ω (k + 1) = Ω k ∘ θ :=
    fun k => ⟨Θ (k + 1) (Ω k), hΘmono (k + 1) (Ω k), hΩsucc k⟩
  have hcau : ∀ k, CauchySeq (fun m => toL2 N (g k (Ω k m)) (hg_reg k (Ω k m)).1) := by
    intro k
    cases k with
    | zero => rw [hΩzero]; exact hΘcau 0 id
    | succ j => rw [hΩsucc j]; exact hΘcau (j + 1) (Ω j)
  -- the approximation errors
  let eps : ℕ → ℝ := fun k => (B' + 1) / ((k : ℝ) + 1)
  have hεpos : ∀ k, 0 < eps k := fun k => by
    show 0 < (B' + 1) / ((k : ℝ) + 1)
    exact div_pos (by linarith) (by positivity)
  have hε0 : Tendsto eps atTop (nhds 0) := by
    have h2 : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (nhds 0) := by
      have h1 : Tendsto (fun k : ℕ => (↑(k + 1) : ℝ)) atTop atTop :=
        (tendsto_add_atTop_iff_nat 1).mpr tendsto_natCast_atTop_atTop
      refine (h1.inv_tendsto_atTop).congr' ?_
      filter_upwards with k
      push_cast
      rfl
    have h4 := h2.mul_const (B' + 1)
    have heq : eps = fun k : ℕ => ((k : ℝ) + 1)⁻¹ * (B' + 1) := by
      funext k
      show (B' + 1) / ((k : ℝ) + 1) = ((k : ℝ) + 1)⁻¹ * (B' + 1)
      rw [div_eq_mul_inv, mul_comm]
    rw [heq]
    simpa using h4
  have happrox : ∀ k n,
      dist (toL2 N (f n) (hf n)) (toL2 N (g k n) (hg_reg k n).1) ≤ eps k := by
    intro k n
    have hδk : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
    have hkey := Mollify.conv_sub_eLpNorm_le (hsm n) (hcs n) (hρsm k) (hρcs k) (hρ0 k) (hρ1 k)
      (hρsupp k)
    have htrans : eLp2 N (f n - g k n) ≤ ofRealENN (((k : ℝ) + 1)⁻¹) * ofRealENN B' :=
      hkey.trans (mul_le_mul_of_nonneg_left (hB' n) bot_le)
    rw [rs_dist_toL2_eq (hf n) (hg_reg k n).1]
    calc (eLp2 N (f n - g k n)).toReal
        ≤ (ofRealENN (((k : ℝ) + 1)⁻¹) * ofRealENN B').toReal :=
          ENNReal.toReal_mono
            (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) htrans
      _ = ((k : ℝ) + 1)⁻¹ * B' := by
          simp only [ofRealENN, ENNReal.toReal_mul, ENNReal.toReal_ofReal hδk.le,
            ENNReal.toReal_ofReal hB'nn]
      _ ≤ eps k := by
          show ((k : ℝ) + 1)⁻¹ * B' ≤ (B' + 1) / ((k : ℝ) + 1)
          rw [div_eq_mul_inv, mul_comm (B' + 1) ((k : ℝ) + 1)⁻¹]
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  obtain ⟨ψ, hψ, hcauψ⟩ := diagonal_nested (x := fun n => toL2 N (f n) (hf n))
    (y := fun k n => toL2 N (g k n) (hg_reg k n).1) (ε := eps) (ω := Ω) hε0 happrox
    hΩmono hΩstep hcau
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hcauψ
  exact ⟨ψ, hψ, w, hw⟩

/-! ## The main compactness statement -/

/-- The Rellich compactness statement, in the case where the test functions of
the box are supported in a fixed compact set `K`. -/
theorem rs_rellich_of_compact {N : ℕ} {L : ℝ} (K : Set (Conf N)) (hK : IsCompact K)
    (hKs : ∀ F : testSub N L, tsupport (F : Conf N → ℝ) ⊆ K)
    (C : ℝ) (u : ℕ → Hsub N L) (hC : ∀ n, hSq (u n : Amb N) ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ w : L2 N, TendstoL2 N (fun n => jEmbed N L (u (φ n))) w := by
  classical
  have hCnn : 0 ≤ C := (rs_hSq_nonneg (u 0 : Amb N)).trans (hC 0)
  -- approximations of the `u n` by graph points of test functions
  have hex : ∀ n, ∃ F : testSub N L,
      hSq (graphPoint N L F - (u n : Amb N)) ≤ (((n : ℝ) + 1)⁻¹) ^ 2 := by
    intro n
    have hpos : (0 : ℝ) < (((n : ℝ) + 1)⁻¹) ^ 2 := by positivity
    exact Basic.exists_graphPoint_close (u n) hpos
  choose F hF using hex
  let f : ℕ → Conf N → ℝ := fun n => (F n : Conf N → ℝ)
  have hfL2 : ∀ n, IsL2 N (f n) := fun n =>
    memLp_of_contDiff_hasCompactSupport (F n).2.1 (hasCompactSupport_of_testFun (F n).2)
  have hfsm : ∀ n, Smooth1 (f n) := fun n => (F n).2.1.of_le (by norm_num)
  have hfcs : ∀ n, HasCompactSupport (f n) := fun n => hasCompactSupport_of_testFun (F n).2
  have hfsupp : ∀ n, tsupport (f n) ⊆ K := fun n => hKs (F n)
  -- the classes of the approximations agree with the graph points
  have hgp : ∀ n, toL2 N (f n) (hfL2 n) = (graphPoint N L (F n)).1 := fun n => rfl
  -- the approximation errors tend to zero
  have hδn : ∀ n, ‖(graphPoint N L (F n) - (u n : Amb N)).1‖ ≤ ((n : ℝ) + 1)⁻¹ := by
    intro n
    refine (rs_norm_fst_le_sqrt_hSq _).trans ?_
    rw [Real.sqrt_le_left (by positivity)]
    exact hF n
  -- uniform bounds on the approximations
  have hcomp : ∀ n, ‖(graphPoint N L (F n)).1‖ ≤ Real.sqrt C + 1 ∧
      ∀ j : GIdx N, ‖(graphPoint N L (F n)).2 j‖ ≤ Real.sqrt C + 1 := by
    intro n
    have hδ1 : ((n : ℝ) + 1)⁻¹ ≤ 1 := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      rwa [inv_le_one₀ (by positivity)]
    constructor
    · have h1 : ‖(u n : Amb N).1‖ ≤ Real.sqrt C :=
        (rs_norm_fst_le_sqrt_hSq (u n : Amb N)).trans (Real.sqrt_le_sqrt (hC n))
      have h2 : ‖(graphPoint N L (F n)).1‖ ≤ ‖(u n : Amb N).1‖ +
          ‖(graphPoint N L (F n) - (u n : Amb N)).1‖ := by
        calc ‖(graphPoint N L (F n)).1‖
            = ‖(u n : Amb N).1 + (graphPoint N L (F n) - (u n : Amb N)).1‖ := by
              congr 1
              rw [Prod.fst_sub]
              abel
          _ ≤ _ := norm_add_le _ _
      have := hδn n
      linarith
    · intro j
      have h1 : ‖(u n : Amb N).2 j‖ ≤ Real.sqrt C :=
        (rs_norm_snd_le_sqrt_hSq (u n : Amb N) j).trans (Real.sqrt_le_sqrt (hC n))
      have h2 : ‖(graphPoint N L (F n)).2 j‖ ≤ ‖(u n : Amb N).2 j‖ +
          ‖(graphPoint N L (F n) - (u n : Amb N)).2 j‖ := by
        have h4 : (graphPoint N L (F n)).2 j =
            (u n : Amb N).2 j + (graphPoint N L (F n) - (u n : Amb N)).2 j := by
          rw [Prod.snd_sub, Pi.sub_apply]
          abel
        rw [h4]
        exact norm_add_le _ _
      have h3 : ‖(graphPoint N L (F n) - (u n : Amb N)).2 j‖ ≤ ((n : ℝ) + 1)⁻¹ := by
        refine (rs_norm_snd_le_sqrt_hSq _ j).trans ?_
        rw [Real.sqrt_le_left (by positivity)]
        exact hF n
      linarith
  -- the uniform bounds feeding the compactness theorem
  have hB : ∀ n, eLp2 N (f n) ≤ ofRealENN (Real.sqrt C + 1) := by
    intro n
    have h1 : eLp2 N (f n) = ENNReal.ofReal ‖(graphPoint N L (F n)).1‖ := by
      rw [rs_eLp2_eq_ofReal_norm (hfL2 n), hgp n]
    rw [h1]
    exact ENNReal.ofReal_le_ofReal (hcomp n).1
  have hB' : ∀ n, gradNorm N (f n) ≤
      ofRealENN ((Fintype.card (GIdx N) : ℝ) * (Real.sqrt C + 1)) := by
    intro n
    have hcomp2 : ∀ j : GIdx N,
        eLpNorm (fun x => fderiv ℝ (f n) x (Submission.BoseGases.kcDir N j.1 j.2)) 2 (volC N)
          ≤ ofRealENN (Real.sqrt C + 1) := by
      intro j
      have hmem : MemLp (fun x => fderiv ℝ ((F n : testSub N L) : Conf N → ℝ) x
          (Submission.BoseGases.kcDir N j.1 j.2)) 2 (volC N) :=
        memLp_of_contDiff_hasCompactSupport
          (Submission.BoseGases.firstDir_contDiff (F n).2.1 (Submission.BoseGases.kcDir N j.1 j.2))
          (IsCompact.of_isClosed_subset (hasCompactSupport_of_testFun (F n).2) (isClosed_tsupport _)
            (Submission.BoseGases.tsupport_firstDir_subset _))
      have heq : MemLp.toLp (fun x => fderiv ℝ ((F n : testSub N L) : Conf N → ℝ) x
            (Submission.BoseGases.kcDir N j.1 j.2)) hmem = (graphPoint N L (F n)).2 j := rfl
      have hfun : (fun x => fderiv ℝ (f n) x (Submission.BoseGases.kcDir N j.1 j.2))
          = fun x => fderiv ℝ ((F n : testSub N L) : Conf N → ℝ) x
              (Submission.BoseGases.kcDir N j.1 j.2) := rfl
      rw [hfun, rs_eLpNorm_eq_ofReal_norm_toLp hmem, heq]
      exact ENNReal.ofReal_le_ofReal ((hcomp n).2 j)
    calc gradNorm N (f n)
        ≤ ∑ j : GIdx N,
            eLpNorm (fun x => fderiv ℝ (f n) x (Submission.BoseGases.kcDir N j.1 j.2)) 2 (volC N) :=
          Rellich.gradNorm_le_sum_dir (f n)
      _ ≤ ∑ _j : GIdx N, ofRealENN (Real.sqrt C + 1) := Finset.sum_le_sum fun j _ => hcomp2 j
      _ = ofRealENN ((Fintype.card (GIdx N) : ℝ) * (Real.sqrt C + 1)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          simp only [ofRealENN, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  obtain ⟨φ, hφ, w, hw⟩ := rs_smooth_precompact (K := K) hK (B := Real.sqrt C + 1)
    (B' := (Fintype.card (GIdx N) : ℝ) * (Real.sqrt C + 1))
    (by positivity) (by positivity) (f := f) (hf := hfL2) hfsm hfcs hfsupp hB hB'
  refine ⟨φ, hφ, w, ?_⟩
  -- the `L²` distance between `jEmbed (u (φ n))` and the approximation
  have hdist : ∀ n, dist (jEmbed N L (u (φ n))) (toL2 N (f (φ n)) (hfL2 (φ n)))
      ≤ ((φ n : ℝ) + 1)⁻¹ := by
    intro n
    have h1 : jEmbed N L (u (φ n)) - toL2 N (f (φ n)) (hfL2 (φ n))
        = -((graphPoint N L (F (φ n)) - (u (φ n) : Amb N)).1) := by
      rw [hgp (φ n)]
      show (u (φ n) : Amb N).1 - (graphPoint N L (F (φ n))).1 = _
      rw [Prod.fst_sub]
      abel
    rw [dist_eq_norm, h1, norm_neg]
    exact hδn (φ n)
  rw [TendstoL2, tendsto_iff_dist_tendsto_zero]
  set H : ℕ → ℝ := fun n => ((φ n : ℝ) + 1)⁻¹ +
    dist (toL2 N (f (φ n)) (hfL2 (φ n))) w with hHdef
  have hH0 : Tendsto H atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => ((φ n : ℝ) + 1)⁻¹) atTop (nhds 0) := by
      have hbase : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (nhds 0) := by
        have hk : Tendsto (fun k : ℕ => (↑(k + 1) : ℝ)) atTop atTop :=
          (tendsto_add_atTop_iff_nat 1).mpr tendsto_natCast_atTop_atTop
        refine (hk.inv_tendsto_atTop).congr' ?_
        filter_upwards with k
        push_cast
        rfl
      exact hbase.comp hφ.tendsto_atTop
    have h2 : Tendsto (fun n : ℕ => dist (toL2 N (f (φ n)) (hfL2 (φ n))) w) atTop (nhds 0) := by
      rw [← tendsto_iff_dist_tendsto_zero]
      exact hw
    have h3 := h1.add h2
    simpa only [hHdef, Pi.add_apply, zero_add] using h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ : ℕ => (0 : ℝ)) (h := H)
    tendsto_const_nhds hH0 (fun n => dist_nonneg) (fun n => ?_)
  show dist (jEmbed N L (u (φ n))) w ≤ H n
  rw [hHdef]
  calc dist (jEmbed N L (u (φ n))) w
      ≤ dist (jEmbed N L (u (φ n))) (toL2 N (f (φ n)) (hfL2 (φ n))) +
        dist (toL2 N (f (φ n)) (hfL2 (φ n))) w := dist_triangle _ _ _
    _ ≤ ((φ n : ℝ) + 1)⁻¹ + dist (toL2 N (f (φ n)) (hfL2 (φ n))) w := by
        linarith [hdist n]

/-- **Rellich compactness for the Dirichlet energy space.** -/
theorem rs_rellich (N : ℕ) (L : ℝ) (C : ℝ) (u : ℕ → Hsub N L)
    (hC : ∀ n, hSq (u n : Amb N) ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ w : L2 N, TendstoL2 N (fun n => jEmbed N L (u (φ n))) w := by
  by_cases hL : 0 < L
  · -- the box is a compact set containing the supports
    exact rs_rellich_of_compact (BoseGases.box N L) (Submission.BoseGases.box_compact hL)
      (fun F => F.2.2.trans (Submission.BoseGases.openBox_subset_box (N := N) (L := L))) C u hC
  · rcases eq_or_ne N 0 with hN | hN
    · -- the configuration space is a single point: `box 0 1` is everything
      subst hN
      refine rs_rellich_of_compact (BoseGases.box 0 1) (Submission.BoseGases.box_compact one_pos)
        (fun F x _ => ?_) C u hC
      exact fun i => i.elim0
    · -- the box has empty interior: the energy space is trivial
      have hIoo : Set.Ioo (0 : ℝ) L = ∅ := Set.Ioo_eq_empty hL
      have hopen : Submission.BoseGases.openBox N L = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
        obtain ⟨i⟩ : Nonempty (Fin N) := ⟨⟨0, Nat.pos_of_ne_zero hN⟩⟩
        have hmem : (x i).ofLp (0 : Fin 3) ∈ (∅ : Set ℝ) := by
          rw [← hIoo]
          exact hx i 0
        exact Set.notMem_empty _ hmem
      have htest : testSub N L = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro F hF
        funext x
        by_contra hx
        have hmem : x ∈ tsupport (F : Conf N → ℝ) :=
          subset_tsupport _ (Function.mem_support.mpr hx)
        have := hF.2 hmem
        rw [hopen] at this
        exact this
      have hrange : ∀ F : testSub N L, graphPoint N L F = 0 := by
        intro F
        have hmem : (F : Conf N → ℝ) ∈ (⊥ : Submodule ℝ (Conf N → ℝ)) := by
          rw [← htest]
          exact F.2
        have hF0 : (F : Conf N → ℝ) = 0 := (Submodule.mem_bot ℝ).mp hmem
        rw [show F = (0 : testSub N L) from Subtype.ext hF0, Basic.graphPoint_zero]
      have hHsub : Hsub N L = ⊥ := by
        have hspan : Submodule.span ℝ (Set.range (graphPoint N L)) = ⊥ := by
          rw [Submodule.span_eq_bot]
          rintro q ⟨F, rfl⟩
          exact hrange F
        have hclosed : IsClosed ((⊥ : Submodule ℝ (Amb N)) : Set (Amb N)) := by
          rw [Submodule.bot_coe]
          exact isClosed_singleton
        rw [Hsub]
        exact le_antisymm (Submodule.topologicalClosure_minimal _ (le_of_eq hspan) hclosed) bot_le
      have hzero : ∀ n, u n = 0 := fun n => by
        have hmem : (u n : Amb N) = 0 := (Submodule.eq_bot_iff (Hsub N L)).mp hHsub (u n) (u n).2
        exact Subtype.ext hmem
      refine ⟨id, strictMono_id, 0, ?_⟩
      have hconst : (fun n => jEmbed N L (u (id n))) = fun _ => (0 : L2 N) := by
        funext n
        show jEmbed N L (u n) = 0
        rw [hzero n, map_zero]
      rw [hconst]
      exact tendsto_const_nhds

/-! ## The requested statement -/

theorem rellich_subseq (N : ℕ) (L : ℝ) (C : ℝ) (u : ℕ → Work.BoseSym.Hsub N L)
    (hC : ∀ n, Work.BoseSym.hSq (u n : Work.BoseSym.Amb N) ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ w : Work.BoseSym.L2 N,
        Work.BoseSym.TendstoL2 N (fun n => Work.BoseSym.jEmbed N L (u (φ n))) w :=
  rs_rellich N L C u hC

end

end Work.BoseSym.Minimiser

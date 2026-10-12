import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseSym.Abs.exists_abs_point
import Submission.Work.BoseSym.Form.symAvgF_ne_zero
import Submission.Work.BoseSym.Minimiser.exists_minimiser
import Submission.Work.BoseSym.Minimiser.iInf_le_dirForm_unit
import Submission.Work.BoseSym.Perm.symAvgAmb_fst
import Submission.Work.BoseSym.Perm.symAvgAmb_isSym
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym.Minimiser — a permutation invariant minimiser of the Dirichlet form

The minimiser set of the Dirichlet form `dirForm W` on the unit sphere of the
energy space `Hsub N L` is invariant under the symmetrisation
`symAvgAmb N u = (N!)⁻¹ • ∑_σ permAmb N σ u` (`minimiser_set_symAvg`).  This
module combines that invariance with the fact that the energy can only decrease
when a minimiser `p` is replaced by `|p|` (Kato's inequality,
`Abs.exists_abs_point`), which produces a minimiser with an *almost everywhere
nonnegative* function part.  For such a minimiser `u` the symmetrisation has a
non-zero function part (`Form.symAvgF_ne_zero`), and after normalising it to
unit `L²` norm we obtain a permutation invariant minimiser.

## The argument

* `exists_minimiser` provides a unit vector `p` with
  `dirForm W p = m := ⨅ q, dirForm W q`;
* `Abs.exists_abs_point` provides `q : Hsub N L` with
  `q.1 =ᵐ |p.1|` and `gSq q ≤ gSq p`; since the potential energy only depends on
  `|p.1|² = (p.1)²`, `q` is again a unit minimiser, and `q.1 ≥ 0` a.e.;
* `minimiser_set_symAvg` shows that `symAvgAmb N q` is also a minimiser, i.e.
  `dirForm W (symAvgAmb N q) = m * l2Sq (symAvgAmb N q)`;
* `u := symAvgAmb N q` has `u.1 ≠ 0` (its first component is the symmetrised
  average of the a.e. nonnegative, a.e. nonzero function `q.1`), so
  `l2Sq u > 0`, and `Z := (l2Sq u)^{-1/2} • u` is a unit vector with
  `dirForm W Z = m`, which is permutation invariant because `u` is
  (`symAvgAmb_isSym`).

The bookkeeping lemma that makes `minimiser_set_symAvg` applicable here is that
the infimum `m` is a lower bound for the form on the whole energy space,
`m * l2Sq z ≤ dirForm W z` for `z : Hsub N L`.
-/

namespace Work.BoseSym.Minimiser

open MeasureTheory Filter
open Work.BoseSym
open scoped Topology Real ENNReal

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary properties of the energy forms -/

lemma l2Sq_nonneg {N : ℕ} (p : Amb N) : 0 ≤ l2Sq p := by
  simp only [l2Sq]
  positivity

lemma gSq_nonneg {N : ℕ} (p : Amb N) : 0 ≤ gSq p := by
  simp only [gSq]
  positivity

lemma l2Sq_smul {N : ℕ} (c : ℝ) (p : Amb N) : l2Sq (c • p) = c ^ 2 * l2Sq p := by
  simp only [l2Sq, Prod.smul_fst, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

lemma gSq_smul {N : ℕ} (c : ℝ) (p : Amb N) : gSq (c • p) = c ^ 2 * gSq p := by
  simp only [gSq, Prod.smul_snd, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [Finset.mul_sum]

lemma potSq_smul {N : ℕ} (W : Conf N → ℝ) (c : ℝ) (p : Amb N) :
    potSq W (c • p) = c ^ 2 * potSq W p := by
  simp only [potSq, Prod.smul_fst]
  have h : (fun x => W x * (((c • p.1 : L2 N)) : Conf N → ℝ) x ^ 2)
      =ᵐ[volC N] fun x => c ^ 2 * (W x * ((p.1 : Conf N → ℝ) x) ^ 2) := by
    filter_upwards [Lp.coeFn_smul c p.1] with x hx
    rw [hx]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [integral_congr_ae h, integral_const_mul]

lemma dirForm_smul {N : ℕ} (W : Conf N → ℝ) (c : ℝ) (p : Amb N) :
    dirForm W (c • p) = c ^ 2 * dirForm W p := by
  simp only [dirForm, gSq_smul, potSq_smul]
  ring

/-- The permutation action is compatible with scalar multiplication. -/
lemma permAmb_smul_apply {N : ℕ} (σ : Equiv.Perm (Fin N)) (c : ℝ) (p : Amb N) :
    permAmb N σ (c • p) = c • permAmb N σ p := by
  rw [← Work.BoseSym.Perm.permAmbCLM_apply σ (c • p), map_smul,
    Work.BoseSym.Perm.permAmbCLM_apply σ p]

/-! ## The infimum of the Dirichlet form is a lower bound on the energy space -/

/-- **The infimum of the Dirichlet form over the unit sphere is a lower bound
for the Dirichlet form on the whole energy space**, in the form
`m * l2Sq z ≤ dirForm W z`.  This is the hypothesis under which the minimiser
set is a linear subspace (`minimiser_set_linear`, `minimiser_set_symAvg`). -/
lemma iInf_mul_l2Sq_le_dirForm {N : ℕ} (L : ℝ) {W : Conf N → ℝ} (hWnn : AENonneg N W)
    (z : Hsub N L) :
    (⨅ q : {q : Hsub N L // l2Sq (q : Amb N) = 1}, dirForm W (q : Amb N)) * l2Sq (z : Amb N)
      ≤ dirForm W (z : Amb N) := by
  by_cases hz0 : l2Sq (z : Amb N) = 0
  · -- the function part vanishes, and the form is nonnegative
    rw [hz0, mul_zero]
    exact dirForm_nonneg hWnn (z : Amb N)
  · -- normalise `z` to a unit vector
    have hpos : 0 < l2Sq (z : Amb N) := lt_of_le_of_ne (l2Sq_nonneg _) (Ne.symm hz0)
    set c : ℝ := (Real.sqrt (l2Sq (z : Amb N)))⁻¹ with hc
    have hc2 : c ^ 2 * l2Sq (z : Amb N) = 1 := by
      rw [hc, inv_pow, Real.sq_sqrt (le_of_lt hpos), inv_mul_cancel₀ (ne_of_gt hpos)]
    have hcoe : ((c • z : Hsub N L) : Amb N) = c • (z : Amb N) := rfl
    have hy : l2Sq ((c • z : Hsub N L) : Amb N) = 1 := by
      rw [hcoe, l2Sq_smul, hc2]
    have hle : (⨅ q : {q : Hsub N L // l2Sq (q : Amb N) = 1}, dirForm W (q : Amb N))
        ≤ dirForm W ((c • z : Hsub N L) : Amb N) := iInf_le_dirForm_unit L hWnn hy
    rw [hcoe, dirForm_smul] at hle
    calc (⨅ q : {q : Hsub N L // l2Sq (q : Amb N) = 1}, dirForm W (q : Amb N)) * l2Sq (z : Amb N)
        ≤ (c ^ 2 * dirForm W (z : Amb N)) * l2Sq (z : Amb N) :=
          mul_le_mul_of_nonneg_right hle (le_of_lt hpos)
      _ = dirForm W (z : Amb N) * (c ^ 2 * l2Sq (z : Amb N)) := by ring
      _ = dirForm W (z : Amb N) := by rw [hc2, mul_one]

/-! ## The main theorem -/

theorem symMinimiser_exists {N : ℕ} (L : ℝ) (hL : 0 < L) {W : Conf N → ℝ} (C : ℝ)
    (hWperm : ∀ σ x, W (tauPerm N σ x) = W x) (hW : BddBy N W C) (hWnn : AENonneg N W)
    (hWm : AEMeas N W) :
    ∃ p : {p : Hsub N L // l2Sq (p : Amb N) = 1},
      IsSym N ((p : Hsub N L) : Amb N) ∧
      dirForm W ((p : Hsub N L) : Amb N) =
        ⨅ q : {q : Hsub N L // l2Sq (q : Amb N) = 1}, dirForm W ((q : Hsub N L) : Amb N) := by
  -- the value of the infimum
  set m : ℝ := ⨅ q : {q : Hsub N L // l2Sq (q : Amb N) = 1}, dirForm W (q : Amb N) with hm
  have hmin : ∀ z : Hsub N L, m * l2Sq (z : Amb N) ≤ dirForm W (z : Amb N) := fun z => by
    rw [hm]
    exact iInf_mul_l2Sq_le_dirForm L hWnn z
  -- a unit minimiser exists
  obtain ⟨p0, hp0⟩ := exists_minimiser N L hL C W hW hWnn hWm
  have hp0' : dirForm W ((p0 : Hsub N L) : Amb N) = m := by
    rw [hm]
    exact hp0
  -- Kato's inequality: replacing the minimiser by its absolute value
  obtain ⟨q, hqae, hqg⟩ := Work.BoseSym.Abs.exists_abs_point (p0 : Hsub N L)
  have hq1 : l2Sq (q : Amb N) = 1 := by
    have h1 : l2Sq (q : Amb N) = l2Sq ((p0 : Hsub N L) : Amb N) := by
      rw [Work.BoseSym.Form.l2Sq_eq_integral, Work.BoseSym.Form.l2Sq_eq_integral, intC, intC]
      refine integral_congr_ae ?_
      filter_upwards [hqae] with x hx
      rw [hx, sq_abs]
    rw [h1]
    exact p0.2
  have hqpot : potSq W (q : Amb N) = potSq W ((p0 : Hsub N L) : Amb N) := by
    simp only [potSq]
    refine integral_congr_ae ?_
    filter_upwards [hqae] with x hx
    rw [hx, sq_abs]
  have hqdir : dirForm W (q : Amb N) = m := by
    have hle : dirForm W (q : Amb N) ≤ m := by
      rw [← hp0', dirForm, dirForm, hqpot]
      linarith [hqg]
    have hge : m ≤ dirForm W (q : Amb N) := by
      have h := hmin q
      rw [hq1, mul_one] at h
      exact h
    linarith
  -- the symmetrisation of the minimiser is a minimiser
  have hsym : dirForm W (symAvgAmb N (q : Amb N)) = m * l2Sq (symAvgAmb N (q : Amb N)) :=
    minimiser_set_symAvg L hWperm hW hWm m hmin q.2 (by rw [hqdir, hq1, mul_one])
  -- its function part is a non-zero a.e. nonnegative average, hence non-zero
  have hqnn : AENonneg N ((q : Amb N).1) := by
    rw [AENonneg]
    filter_upwards [hqae] with x hx
    rw [hx]
    exact abs_nonneg _
  have hq0 : ¬ AEEq N ((q : Amb N).1) 0 := by
    intro h0
    have hzero : l2Sq (q : Amb N) = 0 := by
      rw [Work.BoseSym.Form.l2Sq_eq_integral, intC]
      have hz : (fun x => ((q : Amb N).1 : Conf N → ℝ) x ^ 2)
          =ᵐ[volC N] (0 : Conf N → ℝ) := by
        filter_upwards [h0] with x hx
        simp [hx]
      rw [integral_congr_ae hz]
      simp
    linarith [hq1]
  have hune : (symAvgAmb N (q : Amb N)).1 ≠ 0 := by
    intro h
    refine Work.BoseSym.Form.symAvgF_ne_zero (f := fun y => ((q : Amb N).1 : Conf N → ℝ) y)
      hqnn hq0 ?_
    have h1 : ((symAvgAmb N (q : Amb N)).1 : Conf N → ℝ) =ᵐ[volC N] (0 : Conf N → ℝ) := by
      rw [h]
      filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := volC N)] with x hx
      simp
    have h2 : ((symAvgAmb N (q : Amb N)).1 : Conf N → ℝ) =ᵐ[volC N]
        symAvgF N (fun y => ((q : Amb N).1 : Conf N → ℝ) y) :=
      Work.BoseSym.Perm.symAvgAmb_fst (q : Amb N)
    exact h2.symm.trans h1
  -- normalise the symmetric minimiser to unit norm
  set u : Amb N := symAvgAmb N (q : Amb N) with hu
  have huH : u ∈ Hsub N L := by
    rw [hu]
    exact Work.BoseSym.Perm.symAvgAmb_mem_Hsub q.2
  have hsymu : dirForm W u = m * l2Sq u := by
    rw [hu]
    exact hsym
  have husym : IsSym N u := by
    rw [hu]
    exact Work.BoseSym.Perm.symAvgAmb_isSym (q : Amb N)
  have huh : u.1 ≠ 0 := by
    rw [hu]
    exact hune
  have hupos : 0 < l2Sq u := by
    simp only [l2Sq]
    exact pow_pos (norm_pos_iff.mpr huh) 2
  set c : ℝ := (Real.sqrt (l2Sq u))⁻¹ with hc
  have hc2 : c ^ 2 * l2Sq u = 1 := by
    rw [hc, inv_pow, Real.sq_sqrt (le_of_lt hupos), inv_mul_cancel₀ (ne_of_gt hupos)]
  refine ⟨⟨c • ⟨u, huH⟩, ?_⟩, ?_, ?_⟩
  · change l2Sq (c • u) = 1
    rw [l2Sq_smul, hc2]
  · change IsSym N (c • u)
    intro σ
    rw [permAmb_smul_apply σ c u, husym σ]
  · change dirForm W (c • u) = m
    rw [dirForm_smul, hsymu]
    calc c ^ 2 * (m * l2Sq u) = m * (c ^ 2 * l2Sq u) := by ring
      _ = m * 1 := by rw [hc2]
      _ = m := by ring

end

end Work.BoseSym.Minimiser

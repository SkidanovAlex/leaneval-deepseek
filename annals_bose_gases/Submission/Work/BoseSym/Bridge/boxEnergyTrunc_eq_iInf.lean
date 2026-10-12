import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.Work.BoseSym.Abs.exists_abs_point
import Submission.Work.BoseSym.BoxTest
import Submission.Work.BoseSym.Bridge.gSq_graphPoint_box
import Submission.Work.BoseSym.Bridge.pos_l2Sq_graphPoint
import Submission.Work.BoseSym.Bridge.potSq_ge_neg_mul_l2Sq
import Submission.Work.BoseSym.Bridge.potSq_graphPoint_box
import Submission.Work.BoseSym.Bridge.tendsto_dirForm
import Submission.Work.BoseSym.Form.gSq_eq_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym.Bridge — the truncated box energy as an infimum of the Dirichlet form

`Interface.boxEnergyTrunc N L v M` is the infimum of the truncated Rayleigh quotient

    raylQuot N L (Vtrunc N v M) Ψ
      = ( ∫_box ∑_{i,k} (fderiv Ψ · kcDir i k)² + ∫_box Vtrunc·Ψ² ) / (∫_box Ψ²)

over the box trial class `CInfty0Box N L`, and `Hsub N L ⊆ Amb N` is the closure of the
graph `F ↦ (F, ∇F)` of the test functions supported in the open box.  Here we prove the
identification of the two objects:

`boxEnergyTrunc N L v M = ⨅ p : {p : Hsub N L // l2Sq p = 1}, dirForm (Vtrunc N v M) p`.

Note.  Until 2026-10-03 the definition in `Interface.lean` was mis-parenthesized (the
`+ ∫ x in box N L, Vtrunc …` was parsed inside the outer `∫ x in box N L, ·`, which
turned the second integral into a *constant* term of the outer integrand and multiplied
it by `vol (box N L) = L ^ (3*N)`); for that reading the statement is false (take
`N = 1`, `L = 2`, `v ≡ 0`, `M = −1`: the two sides then differ by `7`).  The definition
has since been fixed, so that `boxEnergyTrunc` is *definitionally* the infimum of
`raylQuot` (`boxEnergyTrunc_eq_iInf_raylQuot` below).

The proof has two halves.

* Every `CInfty0Box` state is a test function (`boxToTest`), its graph point is a unit
  vector of `Hsub` after rescaling, and the Dirichlet form of that unit vector is exactly
  the state's Rayleigh quotient.  Hence the right-hand infimum is at most the left-hand
  one.
* Conversely, given a unit vector of `Hsub` we approximate it by graph points of test
  functions (`exists_graphPoint_close`); the Dirichlet form and `l2Sq` are continuous
  (`tendsto_dirForm`), so the left-hand infimum, multiplied by the converging `l2Sq`, is
  bounded by the Dirichlet form of the approximants.

Most of the analytic content (the continuity of the weighted quadratic form, the
positivity of the `L²` norm of a graph point, the lower bound `potSq W p ≥ -C · l2Sq p`)
is in the sibling modules imported above.
-/

namespace Work.BoseSym.Bridge

open MeasureTheory Filter
open scoped Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 20000000

/-! ## The truncated Rayleigh quotient (intended parenthesization) -/

/-- The truncated Rayleigh quotient of an admissible state, with the two box integrals
parenthesized separately — i.e. the quantity that `Interface.boxEnergyTrunc` *intends*
to minimize. -/
noncomputable def raylQuot (N : ℕ) (L : ℝ) (W : Conf N → ℝ)
    (Ψ : BoseGases.CInfty0Box N L) : ℝ :=
  ((∫ x in BoseGases.box N L, ∑ i : Fin N, ∑ k : Fin 3,
      (fderiv ℝ (Ψ : Conf N → ℝ) x (Submission.BoseGases.kcDir N i k)) ^ 2)
    + ∫ x in BoseGases.box N L, W x * ((Ψ : Conf N → ℝ) x) ^ 2)
  / (∫ x in BoseGases.box N L, ((Ψ : Conf N → ℝ) x) ^ 2)

/-- `Interface.boxEnergyTrunc` (with its two integrals parenthesized separately) is the
infimum of `raylQuot` — definitionally. -/
lemma boxEnergyTrunc_eq_iInf_raylQuot {N : ℕ} {L : ℝ} {v : E3 → ℝ} {M : ℝ} :
    boxEnergyTrunc N L v M =
      ⨅ Ψ : BoseGases.CInfty0Box N L, raylQuot N L (Vtrunc N v M) Ψ := rfl

/-! ## Auxiliary material -/

/-- `gSq` is nonnegative. -/
lemma gSq_nonneg {N : ℕ} (p : Amb N) : 0 ≤ gSq p := by
  simp only [gSq]
  exact Finset.sum_nonneg fun j _ => sq_nonneg _

/-- `l2Sq` is continuous on the ambient space. -/
lemma continuous_l2Sq {N : ℕ} : Continuous (fun p : Amb N => l2Sq p) := by
  simp only [l2Sq]
  exact (continuous_fst.norm).pow 2

/-- Scaling of `l2Sq`. -/
lemma l2Sq_smul {N : ℕ} (c : ℝ) (p : Amb N) : l2Sq (c • p) = c ^ 2 * l2Sq p := by
  simp only [l2Sq, show (c • p).1 = c • p.1 from rfl, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]

/-- Scaling of `gSq`. -/
lemma gSq_smul {N : ℕ} (c : ℝ) (p : Amb N) : gSq (c • p) = c ^ 2 * gSq p := by
  simp only [gSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (c • p).2 j = c • p.2 j from rfl, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

/-- Scaling of `potSq`. -/
lemma potSq_smul {N : ℕ} (W : Conf N → ℝ) (c : ℝ) (p : Amb N) :
    potSq W (c • p) = c ^ 2 * potSq W p := by
  simp only [potSq]
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [MeasureTheory.Lp.coeFn_smul c p.1] with x hx
  rw [show (c • p).1 = c • p.1 from rfl, hx]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Scaling of the Dirichlet form. -/
lemma dirForm_smul {N : ℕ} (W : Conf N → ℝ) (c : ℝ) (p : Amb N) :
    dirForm W (c • p) = c ^ 2 * dirForm W p := by
  simp only [dirForm, gSq_smul, potSq_smul]
  ring

/-- The graph point of a test function lies in the energy space. -/
lemma graphPoint_mem_Hsub {N : ℕ} {L : ℝ} (F : testSub N L) :
    graphPoint N L F ∈ Hsub N L := by
  show graphPoint N L F ∈ (Hsub N L : Set (Amb N))
  rw [Work.BoseSym.Basic.Hsub_eq_closure N L]
  exact subset_closure ⟨F, rfl⟩

/-- The Dirichlet form of the graph point of a test function, as box integrals. -/
lemma dirForm_graphPoint_box {N : ℕ} {L : ℝ} {W : Conf N → ℝ} (F : testSub N L) :
    dirForm W (graphPoint N L F)
      = intBox N L (fun x => ∑ i : Fin N, ∑ k : Fin 3,
            (fderiv ℝ (F : Conf N → ℝ) x (Submission.BoseGases.kcDir N i k)) ^ 2)
        + intBox N L (fun x => W x * ((F : Conf N → ℝ) x) ^ 2) := by
  rw [dirForm, gSq_graphPoint_box, potSq_graphPoint_box]
  simp only [eDir]

/-- The intended Rayleigh quotient of a `CInfty0Box` state is the quotient of the graph
point of the associated test function. -/
lemma raylQuot_eq_div_dirForm {N : ℕ} {L : ℝ} {W : Conf N → ℝ}
    (Ψ : BoseGases.CInfty0Box N L) :
    raylQuot N L W Ψ
      = dirForm W (graphPoint N L (boxToTest N L Ψ))
        / l2Sq (graphPoint N L (boxToTest N L Ψ)) := by
  rw [raylQuot, dirForm_graphPoint_box, l2Sq_graphPoint_box, boxToTest_coe]
  simp only [intBox]

/-- A nonzero test function is the underlying function of a `CInfty0Box` state. -/
lemma exists_cInfty0Box_eq_of_testSub {N : ℕ} {L : ℝ} (F : testSub N L)
    (hF : (F : Conf N → ℝ) ≠ 0) :
    ∃ Ψ : BoseGases.CInfty0Box N L, (Ψ : Conf N → ℝ) = (F : Conf N → ℝ) :=
  ⟨⟨(F : Conf N → ℝ), F.2.1.contDiffOn,
      F.2.2.trans (Submission.BoseGases.openBox_subset_interior_box (N := N) L), hF⟩, rfl⟩

/-- For `0 < L` there is a nonzero test function. -/
lemma exists_testSub_ne_zero {N : ℕ} {L : ℝ} (hL : 0 < L) :
    ∃ F : testSub N L, (F : Conf N → ℝ) ≠ 0 := by
  let c : Conf N := fun _ : Fin N => WithLp.toLp 2 (fun _ : Fin 3 => L / 2)
  have hc : c ∈ Submission.BoseGases.openBox N L := by
    intro i k
    dsimp [c, Submission.BoseGases.openBox]
    exact ⟨by linarith, by linarith⟩
  have hnhds : Submission.BoseGases.openBox N L ∈ 𝓝 c :=
    (Submission.BoseGases.openBox_isOpen (N := N) L).mem_nhds hc
  obtain ⟨f, hts, _hcs, hcd, _hrange, hfval⟩ :=
    exists_contDiff_tsupport_subset (E := Conf N) (s := Submission.BoseGases.openBox N L)
      (x := c) (n := ⊤) hnhds
  refine ⟨⟨f, hcd, hts⟩, ?_⟩
  intro hf0
  have h0 : f c = 0 := congrFun hf0 c
  rw [hfval] at h0
  exact one_ne_zero h0

/-- Density of the test functions in the energy space, measured in the *ambient* norm. -/
lemma exists_graphPoint_close_norm {N : ℕ} {L : ℝ} (p : Hsub N L) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : testSub N L, ‖graphPoint N L F - (p : Amb N)‖ ≤ ε := by
  obtain ⟨F, hF⟩ := Work.BoseSym.Basic.exists_graphPoint_close p (ε := ε ^ 2) (pow_pos hε 2)
  refine ⟨F, ?_⟩
  have h1 : ‖graphPoint N L F - (p : Amb N)‖ ^ 2
      ≤ hSq (graphPoint N L F - (p : Amb N)) := Work.BoseSym.Abs.norm_sq_le_hSq _
  have h2 : ‖graphPoint N L F - (p : Amb N)‖ ^ 2 ≤ ε ^ 2 := le_trans h1 hF
  have h3 : 0 ≤ ‖graphPoint N L F - (p : Amb N)‖ := norm_nonneg _
  nlinarith [h2, h3, hε.le]

/-- Given a nonzero test function `F`, the rescaled graph point is a unit vector of the
energy space whose Dirichlet form is the Rayleigh quotient of `F`. -/
lemma exists_unit_dirForm_of_testSub {N : ℕ} {L : ℝ} {W : Conf N → ℝ} (F : testSub N L)
    (hF : (F : Conf N → ℝ) ≠ 0) :
    ∃ p : {p : Hsub N L // l2Sq (p : Amb N) = 1},
      dirForm W (graphPoint N L F) / l2Sq (graphPoint N L F) = dirForm W (p : Amb N) := by
  have hpos : 0 < l2Sq (graphPoint N L F) := pos_l2Sq_graphPoint F hF
  have hcsq : (Real.sqrt (l2Sq (graphPoint N L F)))⁻¹ ^ 2
      = (l2Sq (graphPoint N L F))⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hpos.le]
  refine ⟨⟨⟨(Real.sqrt (l2Sq (graphPoint N L F)))⁻¹ • graphPoint N L F,
      Submodule.smul_mem (Hsub N L) _ (graphPoint_mem_Hsub F)⟩, ?_⟩, ?_⟩
  · change l2Sq ((Real.sqrt (l2Sq (graphPoint N L F)))⁻¹ • graphPoint N L F) = 1
    rw [l2Sq_smul, hcsq, inv_mul_cancel₀ hpos.ne']
  · change dirForm W (graphPoint N L F) / l2Sq (graphPoint N L F)
      = dirForm W ((Real.sqrt (l2Sq (graphPoint N L F)))⁻¹ • graphPoint N L F)
    rw [dirForm_smul, hcsq, inv_mul_eq_div]

/-- Every `CInfty0Box` state has a unit `Hsub` vector realising its (intended)
Rayleigh quotient. -/
lemma exists_unit_raylQuot {N : ℕ} {L : ℝ} {W : Conf N → ℝ} (Ψ : BoseGases.CInfty0Box N L) :
    ∃ p : {p : Hsub N L // l2Sq (p : Amb N) = 1},
      raylQuot N L W Ψ = dirForm W (p : Amb N) := by
  obtain ⟨p, hp⟩ := exists_unit_dirForm_of_testSub (W := W) (boxToTest N L Ψ)
    (by rw [boxToTest_coe]; exact Ψ.nezero)
  exact ⟨p, (raylQuot_eq_div_dirForm Ψ).trans hp⟩

/-! ## The corrected identity -/

/-- **The identity that the requested theorem should state.**  For the correctly
parenthesized truncated Rayleigh quotient `raylQuot`, the infimum over the box trial
class `CInfty0Box N L` equals the infimum of the Dirichlet form over the unit sphere of
the energy space `Hsub N L`. -/
theorem iInf_raylQuot_eq_iInf_dirForm {N : ℕ} {L : ℝ} (hL : 0 < L) {v : E3 → ℝ} {M C : ℝ}
    (hW : BddBy N (Vtrunc N v M) C) (hWm : AEMeas N (Vtrunc N v M)) :
    (⨅ Ψ : BoseGases.CInfty0Box N L, raylQuot N L (Vtrunc N v M) Ψ)
      = ⨅ p : {p : Hsub N L // l2Sq (p : Amb N) = 1}, dirForm (Vtrunc N v M) (p : Amb N) := by
  -- the index types are nonempty
  have htest : ∃ F : testSub N L, (F : Conf N → ℝ) ≠ 0 := exists_testSub_ne_zero hL
  haveI hneS : Nonempty {p : Hsub N L // l2Sq (p : Amb N) = 1} := by
    obtain ⟨F, hF⟩ := htest
    obtain ⟨p, _⟩ := exists_unit_dirForm_of_testSub (W := Vtrunc N v M) F hF
    exact ⟨p⟩
  haveI hneC : Nonempty (BoseGases.CInfty0Box N L) := by
    obtain ⟨F, hF⟩ := htest
    obtain ⟨Ψ, _⟩ := exists_cInfty0Box_eq_of_testSub F hF
    exact ⟨Ψ⟩
  -- the Dirichlet form on the unit sphere is bounded below
  have hBddf : BddBelow (Set.range (fun p : {p : Hsub N L // l2Sq (p : Amb N) = 1} =>
      dirForm (Vtrunc N v M) (p : Amb N))) := by
    refine ⟨-C, ?_⟩
    rintro y ⟨p, rfl⟩
    have hp : l2Sq (p : Amb N) = 1 := p.2
    have h1 : -C * l2Sq (p : Amb N) ≤ potSq (Vtrunc N v M) (p : Amb N) :=
      potSq_ge_neg_mul_l2Sq hW _
    rw [hp, mul_one] at h1
    have h2 : 0 ≤ gSq (p : Amb N) := gSq_nonneg _
    simp only [dirForm]
    linarith
  -- hence the Rayleigh quotients of box states are bounded below as well
  have hBddg : BddBelow (Set.range (raylQuot N L (Vtrunc N v M))) := by
    refine hBddf.mono ?_
    rintro _ ⟨Ψ, rfl⟩
    obtain ⟨p, hp⟩ := exists_unit_raylQuot Ψ
    exact ⟨p, hp.symm⟩
  -- inequality `⨅ raylQuot ≤ ⨅ dirForm`: approximate a unit vector by graph points
  have hI : (⨅ Ψ : BoseGases.CInfty0Box N L, raylQuot N L (Vtrunc N v M) Ψ) ≤
      ⨅ p : {p : Hsub N L // l2Sq (p : Amb N) = 1},
        dirForm (Vtrunc N v M) (p : Amb N) := by
    set E := ⨅ Ψ : BoseGases.CInfty0Box N L, raylQuot N L (Vtrunc N v M) Ψ with hE
    refine le_ciInf fun p => ?_
    have happrox : ∀ n : ℕ, ∃ F : testSub N L,
        ‖graphPoint N L F - (p : Amb N)‖ ≤ (1 : ℝ) / ((n : ℝ) + 1) := fun n =>
      exists_graphPoint_close_norm (N := N) (L := L) p
        (ε := (1 : ℝ) / ((n : ℝ) + 1)) (by positivity)
    choose F hF using happrox
    have hlim : Tendsto (fun n => graphPoint N L (F n)) atTop (nhds (p : Amb N)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => hF n) ?_
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hdir := tendsto_dirForm hW hWm hlim
    have hl2 : Tendsto (fun n => l2Sq (graphPoint N L (F n))) atTop (nhds (l2Sq (p : Amb N))) :=
      ((continuous_l2Sq (N := N)).tendsto (p : Amb N)).comp hlim
    have hineq : ∀ n, E * l2Sq (graphPoint N L (F n))
        ≤ dirForm (Vtrunc N v M) (graphPoint N L (F n)) := by
      intro n
      by_cases hFn : (F n : Conf N → ℝ) = 0
      · have hFn0 : F n = 0 := Subtype.ext hFn
        have hd : dirForm (Vtrunc N v M) (0 : Amb N) = 0 := by
          simpa using dirForm_smul (Vtrunc N v M) (0 : ℝ) (0 : Amb N)
        have hl : l2Sq (0 : Amb N) = 0 := by
          simpa using l2Sq_smul (0 : ℝ) (0 : Amb N)
        rw [hFn0, Work.BoseSym.Basic.graphPoint_zero, hd, hl, mul_zero]
      · obtain ⟨Ψ, hΨ⟩ := exists_cInfty0Box_eq_of_testSub (F n) hFn
        have hbt : boxToTest N L Ψ = F n := Subtype.ext (by rw [boxToTest_coe, hΨ])
        have hray : raylQuot N L (Vtrunc N v M) Ψ
            = dirForm (Vtrunc N v M) (graphPoint N L (F n)) / l2Sq (graphPoint N L (F n)) := by
          rw [raylQuot_eq_div_dirForm, hbt]
        have hE' : E ≤ raylQuot N L (Vtrunc N v M) Ψ :=
          le_trans (le_of_eq hE) (ciInf_le hBddg Ψ)
        have hpos : 0 < l2Sq (graphPoint N L (F n)) := pos_l2Sq_graphPoint (F n) hFn
        calc E * l2Sq (graphPoint N L (F n))
            ≤ raylQuot N L (Vtrunc N v M) Ψ * l2Sq (graphPoint N L (F n)) :=
              mul_le_mul_of_nonneg_right hE' hpos.le
          _ = (dirForm (Vtrunc N v M) (graphPoint N L (F n)) / l2Sq (graphPoint N L (F n)))
                * l2Sq (graphPoint N L (F n)) := by rw [hray]
          _ = dirForm (Vtrunc N v M) (graphPoint N L (F n)) := by
                rw [div_mul_cancel₀ _ hpos.ne']
    have htot := le_of_tendsto_of_tendsto
      ((tendsto_const_nhds (x := E)).mul hl2) hdir (Filter.Eventually.of_forall hineq)
    rwa [p.2, mul_one] at htot
  -- inequality `⨅ dirForm ≤ ⨅ raylQuot`: every box state gives a unit vector
  have hII : (⨅ p : {p : Hsub N L // l2Sq (p : Amb N) = 1},
        dirForm (Vtrunc N v M) (p : Amb N))
      ≤ (⨅ Ψ : BoseGases.CInfty0Box N L, raylQuot N L (Vtrunc N v M) Ψ) := by
    refine le_ciInf fun Ψ => ?_
    obtain ⟨p, hp⟩ := exists_unit_raylQuot Ψ
    calc (⨅ p : {p : Hsub N L // l2Sq (p : Amb N) = 1}, dirForm (Vtrunc N v M) (p : Amb N))
        ≤ dirForm (Vtrunc N v M) (p : Amb N) := ciInf_le hBddf p
      _ = raylQuot N L (Vtrunc N v M) Ψ := hp.symm
  exact le_antisymm hI hII

/-! ## The requested statement -/

/-- The requested statement: the truncated box energy is the infimum of the Dirichlet
form over the unit sphere of the energy space. -/
theorem boxEnergyTrunc_eq_iInf {N : ℕ} {L : ℝ} (hL : 0 < L) {v : E3 → ℝ} {M C : ℝ}
    (hW : BddBy N (Vtrunc N v M) C) (hWm : AEMeas N (Vtrunc N v M)) :
    boxEnergyTrunc N L v M =
      ⨅ p : {p : Hsub N L // l2Sq (p : Amb N) = 1}, dirForm (Vtrunc N v M) (p : Amb N) :=
  (boxEnergyTrunc_eq_iInf_raylQuot (N := N) (L := L) (v := v) (M := M)).trans
    (iInf_raylQuot_eq_iInf_dirForm hL hW hWm)

end

end Work.BoseSym.Bridge

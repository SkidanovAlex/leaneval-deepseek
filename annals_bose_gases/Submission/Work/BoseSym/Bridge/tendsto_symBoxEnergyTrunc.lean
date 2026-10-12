import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseSym.Assemble.hsub_liminf_lsc_subseq
import Submission.Work.BoseSym.Assemble.symQuot_eq_dirichlet
import Submission.Work.BoseSym.Bridge.exists_symTestSub_quot_le
import Submission.Work.BoseSym.Bridge.tendsto_boxEnergyTrunc
import Submission.Work.BoseSym.Perm.aeInvariant_of_isSym_tendsto
import Submission.Work.BoseSym.Perm.continuous_symAvgAmb
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym — the truncated symmetric box energy converges

The requested bridge lemma

`symBoxEnergyTrunc N L v M → symBoxE N L v`  as `M → ∞`

for `0 ≤ v` and `IntOnBox N L (Vpot N v)`.

## The quantities

* `truncQuot N L v M Ψ` is the truncated Rayleigh quotient of a symmetric trial
  state `Ψ : SymBox N L`, and `Interface.symBoxEnergyTrunc` (with the two box
  integrals parenthesised separately) is by definition its infimum over `Ψ`:
  `symBoxEnergyTrunc_eq_iInf_truncQuot`.
* `fullQuot N L v Ψ` is the same quotient with the untruncated pair interaction
  `Vpot N v`.

## The pieces of the proof

* the truncated quotient is monotone in `M` and never exceeds the untruncated
  quotient (`B_M ≤ I` pointwise), so the truncated infima increase and their
  supremum is at most `symBoxE`;
* for each fixed state the truncated quotient converges to the untruncated one
  (monotone convergence, using `IntOnBox N L (Vpot N v)`);
* `Assemble.symQuot_eq_dirichlet` identifies the corpus quotient `symQuot`
  with the explicit Dirichlet quotient `fullQuot`, hence
  `symBoxE N L v = ⨅ Ψ, fullQuot N L v Ψ`;
* the hard direction is `⨅ Ψ, fullQuot N L v Ψ ≤ liminf_M symBoxEnergyTrunc N L v M`.

## The route for the hard direction

Write `E_M = symBoxEnergyTrunc N L v M` and `E = symBoxE N L v`, and suppose
`E_M ≤ E - δ` for all `M`.  Pick `Ψ_M : SymBox N L` with
`Q_M(Ψ_M) ≤ E - δ`, scaled so that `∫ Ψ_M² = 1` (the quotient is
scale-invariant).  Then `p_M := graphPoint N L (symBoxToTest N L Ψ_M)` is a
unit vector of `Hsub N L` with

  `gSq p_M + ∫_{box} Vtrunc N v M · (p_M.1)² ≤ E - δ`,

so `gSq p_M ≤ E` is uniformly bounded.  The compactness/lower semicontinuity
lemma `Assemble.hsub_liminf_lsc` (the `W n := Vtrunc N v n` instance) produces a
subsequence `φ` and `q : Hsub N L` with `l2Sq q = 1`,
`IntegrableOn (Vpot N v · (q.1)²) (box N L)` and

  `gSq q + ∫_{box} Vpot N v · (q.1)² ≤ liminf_n (...) ≤ E - δ`.

So `q` has value `V_q ≤ E - δ` with respect to the full potential.  The density
lemma `Assemble.density_testSub_quot_close` (with `V := Vpot N v`) produces a
test function `F` which is `L²`-close to `q.1` and whose quotient is at most
`V_q + η`.  Since `q.1` is almost everywhere permutation invariant (it is the
`L²` limit of the permutation invariant functions `p_M.1`, which are the graph
points of the invariant states `Ψ_M`), the symmetrisation `symAvgF N F` is close
to `F`, has kinetic energy at most that of `F` (convexity of the Dirichlet
integral plus the invariance of Lebesgue measure under the permutations), and
its potential energy exceeds that of `F` by an arbitrarily small amount
(dominated convergence: `F` and its symmetrisation are bounded and
`Vpot N v ∈ L¹`, while `∫ Vpot · F² < ∞`).  After converting the symmetrised
test function into a `SymBox N L` state this gives

  `E ≤ V_q + 2η ≤ E - δ + 2η`,

a contradiction for `2η < δ`.  Hence `liminf_M E_M ≥ E`, and with
`E_M ≤ E` for all `M` the convergence follows.
-/

namespace Work.BoseSym.Bridge

open MeasureTheory Filter
open BoseGases
open Submission.BoseGases
open scoped Topology Real

noncomputable section

set_option autoImplicit false

/-- The truncated Rayleigh quotient of a symmetric trial state. -/
def truncQuot (N : ℕ) (L : ℝ) (v : E3 → ℝ) (M : ℝ) (Ψ : SymBox N L) : ℝ :=
  ((intBox N L (fun x => ∑ i : Fin N, ∑ k : Fin 3,
      (fderiv ℝ (Ψ : Conf N → ℝ) x (eDir N i k)) ^ 2))
    + (intBox N L (fun x => Vtrunc N v M x * ((Ψ : Conf N → ℝ) x) ^ 2)))
    / (intBox N L (fun x => ((Ψ : Conf N → ℝ) x) ^ 2))

/-- The untruncated Rayleigh quotient of a symmetric trial state. -/
def fullQuot (N : ℕ) (L : ℝ) (v : E3 → ℝ) (Ψ : SymBox N L) : ℝ :=
  ((intBox N L (fun x => ∑ i : Fin N, ∑ k : Fin 3,
      (fderiv ℝ (Ψ : Conf N → ℝ) x (eDir N i k)) ^ 2))
    + (intBox N L (fun x => Vpot N v x * ((Ψ : Conf N → ℝ) x) ^ 2)))
    / (intBox N L (fun x => ((Ψ : Conf N → ℝ) x) ^ 2))

/-- The truncated symmetric box energy is the infimum of the truncated quotients. -/
theorem symBoxEnergyTrunc_eq_iInf_truncQuot {N : ℕ} {L : ℝ} {v : E3 → ℝ} {M : ℝ} :
    symBoxEnergyTrunc N L v M = ⨅ Ψ : SymBox N L, truncQuot N L v M Ψ := rfl

/-- The full-potential quotient is the Dirichlet quotient of the graph point of the
associated test function. -/
theorem fullQuot_eq_dirForm {N : ℕ} {L : ℝ} {v : E3 → ℝ} (Ψ : SymBox N L) :
    fullQuot N L v Ψ
      = dirForm (Vpot N v) (graphPoint N L (symBoxToTest N L Ψ))
        / l2Sq (graphPoint N L (symBoxToTest N L Ψ)) := by
  rw [fullQuot, dirForm, gSq_graphPoint_box, potSq_graphPoint_box, l2Sq_graphPoint_box]
  simp only [symBoxToTest_coe]

/-- The truncated quotient is the Dirichlet quotient of the graph point, with the
truncated weight. -/
theorem truncQuot_eq_dirForm {N : ℕ} {L : ℝ} {v : E3 → ℝ} {M : ℝ} (Ψ : SymBox N L) :
    truncQuot N L v M Ψ
      = dirForm (Vtrunc N v M) (graphPoint N L (symBoxToTest N L Ψ))
        / l2Sq (graphPoint N L (symBoxToTest N L Ψ)) := by
  rw [truncQuot, dirForm, gSq_graphPoint_box, potSq_graphPoint_box, l2Sq_graphPoint_box]
  simp only [symBoxToTest_coe]

/-- `symBoxE` is the infimum of the untruncated quotients. -/
theorem symBoxE_eq_iInf_fullQuot {N : ℕ} {L : ℝ} (hL : 0 < L) {v : E3 → ℝ} (hv : 0 ≤ v)
    (hV : IntOnBox N L (Vpot N v)) :
    symBoxE N L v = ⨅ Ψ : SymBox N L, fullQuot N L v Ψ := by
  have hq : ∀ Ψ : SymBox N L, Submission.BoseGases.symQuot N L v Ψ = fullQuot N L v Ψ := by
    intro Ψ
    rw [fullQuot, Assemble.symQuot_eq_dirichlet hL hv hV Ψ]
  have : Submission.BoseGases.symBoxEnergy N L v
      = ⨅ Ψ : SymBox N L, fullQuot N L v Ψ := by
    rw [Submission.BoseGases.symBoxEnergy]
    exact iInf_congr hq
  simpa [symBoxE] using this

/-! ## Elementary positivity facts -/

/-- `potSq W p ≥ 0` for a nonnegative weight. -/
lemma potSq_nonneg_bridge {N : ℕ} {W : Conf N → ℝ} (hW : 0 ≤ W) (p : Amb N) : 0 ≤ potSq W p :=
  integral_nonneg fun x => mul_nonneg (hW x) (sq_nonneg _)

/-- `gSq p ≥ 0`. -/
lemma gSq_nonneg_bridge {N : ℕ} (p : Amb N) : 0 ≤ gSq p :=
  Finset.sum_nonneg fun j _ => sq_nonneg _

/-- The potential energy is quadratic. -/
lemma potSq_smul_bridge {N : ℕ} (W : Conf N → ℝ) (c : ℝ) (p : Amb N) :
    potSq W (c • p) = c ^ 2 * potSq W p := by
  have hcoe : (((c • p : Amb N).1) : Conf N → ℝ)
      =ᵐ[volC N] fun x => c * ((p.1 : Conf N → ℝ) x) := MeasureTheory.Lp.coeFn_smul c p.1
  have hcongr : (∫ x, W x * (((c • p : Amb N).1) x) ^ 2)
      = ∫ x, c ^ 2 * (W x * ((p.1 : Conf N → ℝ) x) ^ 2) := by
    refine integral_congr_ae ?_
    filter_upwards [hcoe] with x hx
    rw [hx]
    ring
  rw [potSq, potSq, hcongr, integral_const_mul]

/-- The Dirichlet form is quadratic. -/
lemma dirForm_smul_bridge {N : ℕ} (W : Conf N → ℝ) (c : ℝ) (p : Amb N) :
    dirForm W (c • p) = c ^ 2 * dirForm W p := by
  rw [dirForm, dirForm, gSq_smul_amb, potSq_smul_bridge]
  ring

/-- The truncated Rayleigh quotient is nonnegative. -/
lemma truncQuot_nonneg {N : ℕ} {L : ℝ} {v : E3 → ℝ} (hv : 0 ≤ v) {M : ℝ} (hM : 0 ≤ M)
    (Ψ : SymBox N L) : 0 ≤ truncQuot N L v M Ψ := by
  rw [truncQuot, intBox]
  exact div_nonneg (add_nonneg
    (integral_nonneg fun x =>
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => sq_nonneg _)
    (integral_nonneg fun x =>
      mul_nonneg (Vtrunc_nonneg hv hM x) (sq_nonneg _)))
    (integral_nonneg fun x => sq_nonneg _)

/-- The untruncated Rayleigh quotient is nonnegative. -/
lemma fullQuot_nonneg {N : ℕ} {L : ℝ} {v : E3 → ℝ} (hv : 0 ≤ v) (Ψ : SymBox N L) :
    0 ≤ fullQuot N L v Ψ := by
  rw [fullQuot, intBox]
  exact div_nonneg (add_nonneg
    (integral_nonneg fun x =>
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => sq_nonneg _)
    (integral_nonneg fun x =>
      mul_nonneg (Vpot_nonneg hv x) (sq_nonneg _)))
    (integral_nonneg fun x => sq_nonneg _)

lemma symTruncQuot_bddBelow {N : ℕ} {L : ℝ} {v : E3 → ℝ} (hv : 0 ≤ v) {M : ℝ} (hM : 0 ≤ M) :
    BddBelow (Set.range (truncQuot N L v M)) :=
  ⟨0, by rintro _ ⟨Ψ, rfl⟩; exact truncQuot_nonneg hv hM Ψ⟩

lemma symFullQuot_bddBelow {N : ℕ} {L : ℝ} {v : E3 → ℝ} (hv : 0 ≤ v) :
    BddBelow (Set.range (fullQuot N L v)) :=
  ⟨0, by rintro _ ⟨Ψ, rfl⟩; exact fullQuot_nonneg hv Ψ⟩

/-- `Vpot · Ψ²` is integrable on the box for a symmetric box state. -/
lemma integrableOn_Vpot_mul_sq_symBox {N : ℕ} {L : ℝ} (hL : 0 < L) {v : E3 → ℝ}
    (hV : IntOnBox N L (Vpot N v)) (Ψ : SymBox N L) :
    IntegrableOn (fun x => Vpot N v x * ((Ψ : Conf N → ℝ) x) ^ 2) (box N L) := by
  simpa using integrableOn_Vpot_mul_sq_box hL hV Ψ.toCInfty0Box

/-- `Vtrunc M · Ψ²` is integrable on the box for a symmetric box state. -/
lemma integrableOn_Vtrunc_mul_sq_symBox {N : ℕ} {L : ℝ} (hL : 0 < L) {v : E3 → ℝ} (hv : 0 ≤ v)
    (hV : IntOnBox N L (Vpot N v)) {M : ℝ} (hM : 0 ≤ M) (Ψ : SymBox N L) :
    IntegrableOn (fun x => Vtrunc N v M x * ((Ψ : Conf N → ℝ) x) ^ 2) (box N L) := by
  simpa using integrableOn_Vtrunc_mul_sq_box hv hL hV hM Ψ.toCInfty0Box

/-! ## The truncated energy is at most the untruncated one -/

/-- At a fixed state, the truncated quotient is at most the untruncated one. -/
theorem truncQuot_le_fullQuot {N : ℕ} {L : ℝ} (hL : 0 < L) {v : E3 → ℝ} (hv : 0 ≤ v)
    (hV : IntOnBox N L (Vpot N v)) {M : ℝ} (hM : 0 ≤ M) (Ψ : SymBox N L) :
    truncQuot N L v M Ψ ≤ fullQuot N L v Ψ := by
  rw [truncQuot, fullQuot]
  refine div_le_div_of_nonneg_right (add_le_add le_rfl ?_)
    (integral_nonneg fun x => sq_nonneg _)
  refine integral_mono_of_nonneg (μ := volume.restrict (box N L))
    (f := fun x : Conf N => Vtrunc N v M x * ((Ψ : Conf N → ℝ) x) ^ 2)
    (g := fun x : Conf N => Vpot N v x * ((Ψ : Conf N → ℝ) x) ^ 2)
    (Eventually.of_forall fun x => mul_nonneg (Vtrunc_nonneg hv hM x) (sq_nonneg _))
    (integrableOn_Vpot_mul_sq_symBox hL hV Ψ)
    (Eventually.of_forall fun x =>
      mul_le_mul_of_nonneg_right (Vtrunc_le_Vpot N v M x) (sq_nonneg _))

/-- The truncated symmetric box energy is at most the symmetric box energy. -/
theorem symBoxEnergyTrunc_le_symBoxE {N : ℕ} {L : ℝ} (hL : 0 < L) {v : E3 → ℝ} (hv : 0 ≤ v)
    (hV : IntOnBox N L (Vpot N v)) {M : ℝ} (hM : 0 ≤ M) :
    symBoxEnergyTrunc N L v M ≤ symBoxE N L v := by
  haveI : Nonempty (SymBox N L) := nonempty_SymBox N hL
  rw [symBoxEnergyTrunc_eq_iInf_truncQuot, symBoxE_eq_iInf_fullQuot hL hv hV]
  refine le_ciInf fun Ψ =>
    le_trans (ciInf_le (symTruncQuot_bddBelow hv hM) Ψ) (truncQuot_le_fullQuot hL hv hV hM Ψ)

/-- The truncated symmetric box energy is monotone in the truncation level. -/
theorem symBoxEnergyTrunc_mono {N : ℕ} {L : ℝ} (hL : 0 < L) {v : E3 → ℝ} (hv : 0 ≤ v)
    (hV : IntOnBox N L (Vpot N v)) :
    Monotone fun M : ℕ => symBoxEnergyTrunc N L v M := by
  intro m n hmn
  haveI : Nonempty (SymBox N L) := nonempty_SymBox N hL
  show symBoxEnergyTrunc N L v (m : ℝ) ≤ symBoxEnergyTrunc N L v (n : ℝ)
  rw [symBoxEnergyTrunc_eq_iInf_truncQuot, symBoxEnergyTrunc_eq_iInf_truncQuot]
  refine le_ciInf fun Ψ => le_trans (ciInf_le (symTruncQuot_bddBelow hv (Nat.cast_nonneg m)) Ψ) ?_
  refine div_le_div_of_nonneg_right (add_le_add le_rfl ?_)
    (integral_nonneg fun x => sq_nonneg _)
  refine integral_mono_of_nonneg (μ := volume.restrict (box N L))
    (f := fun x : Conf N => Vtrunc N v (m : ℝ) x * ((Ψ : Conf N → ℝ) x) ^ 2)
    (g := fun x : Conf N => Vtrunc N v (n : ℝ) x * ((Ψ : Conf N → ℝ) x) ^ 2)
    (Eventually.of_forall fun x =>
      mul_nonneg (Vtrunc_nonneg hv (Nat.cast_nonneg m) x) (sq_nonneg _))
    (integrableOn_Vtrunc_mul_sq_symBox hL hv hV (Nat.cast_nonneg n) Ψ)
    (Eventually.of_forall fun x => mul_le_mul_of_nonneg_right
      (Vtrunc_mono N v (show (m : ℝ) ≤ (n : ℝ) from by exact_mod_cast hmn) x) (sq_nonneg _))

/-! ## Symmetry of the graph points of symmetric box states -/

/-- The graph point of a symmetric box state is a symmetric ambient element. -/
lemma isSym_graphPoint_symBoxToTest {N : ℕ} {L : ℝ} (Ψ : SymBox N L) :
    IsSym N (graphPoint N L (symBoxToTest N L Ψ)) := by
  intro σ
  rw [Perm.graphPoint_permTest]
  congr 1
  apply Subtype.ext
  funext x
  exact Ψ.sym σ x

/-- Scaling by a nonzero constant preserves symmetry. -/
lemma isSym_smul_iff {N : ℕ} (c : ℝ) (hc : c ≠ 0) (p : Amb N) :
    IsSym N (c • p) ↔ IsSym N p := by
  have hlin : ∀ σ : Equiv.Perm (Fin N), permAmb N σ (c • p) = c • permAmb N σ p := by
    intro σ
    rw [← Perm.permAmbCLM_apply σ (c • p), map_smul, Perm.permAmbCLM_apply]
  constructor
  · intro h σ
    have h1 := h σ
    rw [hlin σ] at h1
    have h2 := congrArg (fun q : Amb N => c⁻¹ • q) h1
    simpa [smul_smul, inv_mul_cancel₀ hc] using h2
  · intro h σ
    rw [hlin σ, h σ]

/-- A function vanishing a.e. off a measurable set has the same integral over the
set and over the whole space. -/
lemma setIntegral_eq_integral_of_ae_eq_zero_compl {N : ℕ} {L : ℝ} {f : Conf N → ℝ}
    (hf : ∀ᵐ x ∂(volC N), x ∉ box N L → f x = 0) :
    (∫ x in box N L, f x) = ∫ x, f x := by
  have h1 : f =ᵐ[volC N] (box N L).indicator f := by
    filter_upwards [hf] with x hx
    by_cases hmem : x ∈ box N L
    · rw [Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hmem, hx hmem]
  calc (∫ x in box N L, f x)
      = ∫ x, (box N L).indicator f x ∂(volC N) :=
        (MeasureTheory.integral_indicator (μ := volC N) (s := box N L) (f := f)
          (box_measurable N L)).symm
    _ = ∫ x, f x ∂(volC N) := (integral_congr_ae h1).symm

/-! ## The energy space bound on the untruncated energy -/

set_option maxHeartbeats 8000000 in
/-- **The hard direction.** The symmetric box energy is at most the supremum of the
truncated symmetric box energies. -/
theorem symBoxE_le_ciSup {N : ℕ} {L : ℝ} (hL : 0 < L) {v : E3 → ℝ} (hv : 0 ≤ v)
    (hV : IntOnBox N L (Vpot N v))
    (hbdd : BddAbove (Set.range fun M : ℕ => symBoxEnergyTrunc N L v M)) :
    symBoxE N L v ≤ ⨆ M : ℕ, symBoxEnergyTrunc N L v M := by
  classical
  haveI : Nonempty (SymBox N L) := nonempty_SymBox N hL
  by_contra hcon
  have hlt : (⨆ M : ℕ, symBoxEnergyTrunc N L v M) < symBoxE N L v := lt_of_not_ge hcon
  obtain ⟨ε, hε0, hε⟩ : ∃ ε : ℝ, 0 < ε ∧
      (⨆ M : ℕ, symBoxEnergyTrunc N L v M) + 4 * ε ≤ symBoxE N L v :=
    ⟨(symBoxE N L v - ⨆ M : ℕ, symBoxEnergyTrunc N L v M) / 8, by linarith, by linarith⟩
  have hle_sup : ∀ M : ℕ, symBoxEnergyTrunc N L v M ≤ ⨆ M : ℕ, symBoxEnergyTrunc N L v M :=
    fun M => le_ciSup hbdd M
  have hmin : ∀ M : ℕ, symBoxEnergyTrunc N L v M ≤ symBoxE N L v - 4 * ε :=
    fun M => le_trans (hle_sup M) (by linarith)
  -- near-minimisers of the truncated problems
  have hsel : ∀ M : ℕ, ∃ Ψ : SymBox N L, truncQuot N L v (M : ℝ) Ψ < symBoxE N L v - 3 * ε := by
    intro M
    have h1 : (⨅ Ψ : SymBox N L, truncQuot N L v (M : ℝ) Ψ) < symBoxE N L v - 3 * ε := by
      rw [← symBoxEnergyTrunc_eq_iInf_truncQuot]
      linarith [hmin M]
    exact exists_lt_of_ciInf_lt h1
  choose Ψ hΨ using hsel
  -- normalised near-minimisers in the energy space
  have hFne : ∀ M : ℕ, (symBoxToTest N L (Ψ M) : Conf N → ℝ) ≠ 0 := fun M => by
    simpa using (Ψ M).nezero
  have hpos : ∀ M : ℕ, 0 < l2Sq (graphPoint N L (symBoxToTest N L (Ψ M))) :=
    fun M => pos_l2Sq_graphPoint _ (hFne M)
  let p : ℕ → Hsub N L := fun M =>
    (Real.sqrt (l2Sq (graphPoint N L (symBoxToTest N L (Ψ M)))))⁻¹ •
      (⟨graphPoint N L (symBoxToTest N L (Ψ M)), graphPoint_mem_Hsub_self _⟩ : Hsub N L)
  have hp1 : ∀ M : ℕ, l2Sq ((p M : Amb N)) = 1 := by
    intro M
    show l2Sq ((Real.sqrt (l2Sq (graphPoint N L (symBoxToTest N L (Ψ M)))))⁻¹ •
      graphPoint N L (symBoxToTest N L (Ψ M))) = 1
    rw [l2Sq_smul_amb, inv_pow, Real.sq_sqrt (hpos M).le, inv_mul_cancel₀ (ne_of_gt (hpos M))]
  have hdir : ∀ M : ℕ, dirForm (Vtrunc N v (M : ℝ)) ((p M : Amb N)) < symBoxE N L v - 3 * ε := by
    intro M
    have h1 : dirForm (Vtrunc N v (M : ℝ)) ((p M : Amb N))
        = ((Real.sqrt (l2Sq (graphPoint N L (symBoxToTest N L (Ψ M)))))⁻¹) ^ 2
          * dirForm (Vtrunc N v (M : ℝ)) (graphPoint N L (symBoxToTest N L (Ψ M))) := by
      show dirForm (Vtrunc N v (M : ℝ))
        (((Real.sqrt (l2Sq (graphPoint N L (symBoxToTest N L (Ψ M)))))⁻¹) •
          graphPoint N L (symBoxToTest N L (Ψ M))) = _
      rw [dirForm_smul_bridge]
    have h2 : ((Real.sqrt (l2Sq (graphPoint N L (symBoxToTest N L (Ψ M)))))⁻¹) ^ 2
        * dirForm (Vtrunc N v (M : ℝ)) (graphPoint N L (symBoxToTest N L (Ψ M)))
        = truncQuot N L v (M : ℝ) (Ψ M) := by
      rw [truncQuot_eq_dirForm, inv_pow, Real.sq_sqrt (hpos M).le, div_eq_mul_inv, mul_comm]
    rw [h1, h2]
    exact hΨ M
  -- the box integral of the truncated potential energy
  have hboxeq : ∀ M : ℕ, (∫ x in box N L, Vtrunc N v (M : ℝ) x * (((p M : Amb N).1) x) ^ 2)
      = potSq (Vtrunc N v (M : ℝ)) ((p M : Amb N)) := by
    intro M
    rw [potSq]
    refine setIntegral_eq_integral_of_ae_eq_zero_compl (N := N) (L := L) (f := fun x : Conf N =>
      Vtrunc N v (M : ℝ) x * (((p M : Amb N).1) x) ^ 2) ?_
    filter_upwards [ae_eq_zero_off_box (p M)] with x hx hxbox
    rw [hx hxbox]
    ring
  have hCg : ∀ M : ℕ, gSq ((p M : Amb N)) ≤ symBoxE N L v - 3 * ε := by
    intro M
    have h3 := hdir M
    rw [dirForm, ← hboxeq M] at h3
    have h4 : gSq ((p M : Amb N)) ≤ gSq ((p M : Amb N))
        + ∫ x in box N L, Vtrunc N v (M : ℝ) x * (((p M : Amb N).1 : Conf N → ℝ) x) ^ 2 :=
      le_add_of_nonneg_right (integral_nonneg fun x =>
        mul_nonneg (Vtrunc_nonneg hv (Nat.cast_nonneg M) x) (sq_nonneg _))
    linarith
  have hCb : ∀ M : ℕ,
      (∫ x in box N L, Vtrunc N v (M : ℝ) x * (((p M : Amb N).1 : Conf N → ℝ) x) ^ 2)
        ≤ symBoxE N L v - 3 * ε := by
    intro M
    have h3 := hdir M
    rw [dirForm, ← hboxeq M] at h3
    have h4 : (∫ x in box N L, Vtrunc N v (M : ℝ) x * (((p M : Amb N).1 : Conf N → ℝ) x) ^ 2)
        ≤ gSq ((p M : Amb N))
          + ∫ x in box N L, Vtrunc N v (M : ℝ) x * (((p M : Amb N).1 : Conf N → ℝ) x) ^ 2 :=
      le_add_of_nonneg_left (gSq_nonneg_bridge _)
    linarith
  have hterm : ∀ M : ℕ, gSq ((p M : Amb N))
      + ∫ x in box N L, Vtrunc N v (M : ℝ) x * (((p M : Amb N).1 : Conf N → ℝ) x) ^ 2
      ≤ symBoxE N L v - 3 * ε := by
    intro M
    have h3 := hdir M
    rw [dirForm, ← hboxeq M] at h3
    exact le_of_lt h3
  -- the hypotheses of the liminf lemma
  have hW0 : ∀ M : ℕ, 0 ≤ Vtrunc N v (M : ℝ) := fun M => Vtrunc_nonneg hv (Nat.cast_nonneg M)
  have hWlim0 : 0 ≤ Vpot N v := Vpot_nonneg hv
  have hWm : ∀ M : ℕ, AEStronglyMeasurable (Vtrunc N v (M : ℝ)) (volume.restrict (box N L)) :=
    fun M => aestronglyMeasurable_Vtrunc_box hV M
  have hWlimm : AEStronglyMeasurable (Vpot N v) (volume.restrict (box N L)) :=
    aestronglyMeasurable_Vpot_box hV
  have hWmono : ∀ M : ℕ, ∀ x, Vtrunc N v (M : ℝ) x ≤ Vtrunc N v ((M + 1 : ℕ) : ℝ) x :=
    fun M x => Vtrunc_mono N v (by push_cast; linarith) x
  have hWtend : ∀ x, Filter.Tendsto (fun M : ℕ => Vtrunc N v (M : ℝ) x) Filter.atTop
      (nhds (Vpot N v x)) := by
    intro x
    have hev : (fun M : ℕ => Vtrunc N v (M : ℝ) x) =ᶠ[Filter.atTop] (fun _ => Vpot N v x) := by
      refine Filter.eventually_atTop.2 ⟨Nat.ceil (Vpot N v x), fun M hM => ?_⟩
      refine min_eq_left ?_
      calc Vpot N v x ≤ (Nat.ceil (Vpot N v x) : ℝ) := Nat.le_ceil _
        _ ≤ (M : ℝ) := by exact_mod_cast hM
    exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds
  have hCi : ∀ M : ℕ, IntegrableOn (fun x : Conf N =>
      Vtrunc N v (M : ℝ) x * (((p M : Amb N).1 : Conf N → ℝ) x) ^ 2) (box N L) :=
    fun M => integrableOn_Vtrunc_mul_sq_hsub hv hV (Nat.cast_nonneg M) (p M)
  obtain ⟨φ, hφ, q, hq1, hqconv, hqint, hqbound⟩ :=
    Assemble.hsub_liminf_lsc_subseq (C := symBoxE N L v - 3 * ε) (C' := symBoxE N L v - 3 * ε)
      p hp1 hCg (W := fun M : ℕ => Vtrunc N v (M : ℝ)) (Wlim := Vpot N v)
      hW0 hWlim0 hWm hWlimm hWmono hWtend hCi hCb
  have hQ : gSq (q : Amb N) + ∫ x in box N L, Vpot N v x * (((q : Amb N).1 : Conf N → ℝ) x) ^ 2
      ≤ symBoxE N L v - 3 * ε := by
    refine le_trans hqbound (Filter.liminf_le_of_frequently_le
      (Filter.Eventually.frequently (Eventually.of_forall fun M => hterm (φ M))) ?_)
    exact ⟨0, Filter.eventually_map.mpr (Eventually.of_forall fun M =>
      add_nonneg (gSq_nonneg_bridge _)
        (integral_nonneg fun x => mul_nonneg (hW0 (φ M) x) (sq_nonneg _)))⟩
  -- the limit vector is a.e. permutation invariant
  have hsym : ∀ M : ℕ, IsSym N ((p M : Amb N)) := by
    intro M
    have h1 : IsSym N (graphPoint N L (symBoxToTest N L (Ψ M))) :=
      isSym_graphPoint_symBoxToTest (Ψ M)
    show IsSym N (((Real.sqrt (l2Sq (graphPoint N L (symBoxToTest N L (Ψ M)))))⁻¹) •
      graphPoint N L (symBoxToTest N L (Ψ M)))
    exact (isSym_smul_iff _ (inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (hpos M)))) _).mpr h1
  have hqsym : AEEq N (((q : Amb N).1 : Conf N → ℝ))
      (symAvgF N (((q : Amb N).1 : Conf N → ℝ))) :=
    Perm.aeInvariant_of_isSym_tendsto (fun M => hsym (φ M)) hqconv
  -- realise the limit energy by a symmetric test function
  obtain ⟨G, hGne, hGinv, hGquot⟩ :=
    exists_symTestSub_quot_le hL hv hV q hq1 hqsym hqint
      (Q := symBoxE N L v - 3 * ε) (δ := ε) (by linarith) hε0
  -- and convert it into a symmetric box state
  have hts : tsupport (G : Conf N → ℝ) ⊆ interior (box N L) :=
    (G.2.2).trans (openBox_subset_interior_box (N := N) L)
  let Ξ : SymBox N L := ⟨⟨(G : Conf N → ℝ), G.2.1.contDiffOn, hts, hGne⟩, hGinv⟩
  have hbt : symBoxToTest N L Ξ = G := Subtype.ext rfl
  have hfull : fullQuot N L v Ξ ≤ symBoxE N L v - 3 * ε + ε := by
    rw [fullQuot_eq_dirForm Ξ, hbt, dirForm]
    exact hGquot
  have hci : symBoxE N L v ≤ fullQuot N L v Ξ := by
    rw [symBoxE_eq_iInf_fullQuot hL hv hV]
    exact ciInf_le (symFullQuot_bddBelow hv) Ξ
  linarith

/-! ## The main theorem -/

set_option maxHeartbeats 8000000 in
theorem tendsto_symBoxEnergyTrunc {N : ℕ} {L : ℝ} (hL : 0 < L) {v : E3 → ℝ} (hv : 0 ≤ v)
    (hV : IntOnBox N L (Vpot N v)) :
    Filter.Tendsto (fun M : ℕ => symBoxEnergyTrunc N L v M) Filter.atTop
      (nhds (symBoxE N L v)) := by
  have hle : ∀ M : ℕ, symBoxEnergyTrunc N L v M ≤ symBoxE N L v := fun M =>
    symBoxEnergyTrunc_le_symBoxE hL hv hV (Nat.cast_nonneg M)
  have hbdd : BddAbove (Set.range fun M : ℕ => symBoxEnergyTrunc N L v M) :=
    ⟨symBoxE N L v, by rintro _ ⟨M, rfl⟩; exact hle M⟩
  have hsup : ⨆ M : ℕ, symBoxEnergyTrunc N L v M = symBoxE N L v :=
    le_antisymm (ciSup_le hle) (symBoxE_le_ciSup hL hv hV hbdd)
  have htend := tendsto_atTop_ciSup (symBoxEnergyTrunc_mono hL hv hV) hbdd
  rwa [hsup] at htend

end

end Work.BoseSym.Bridge

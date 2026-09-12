import Submission.Notions
import Submission.AlgebraicBridge
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Order
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Assembly: converse output → Reduction input

Decomposed item 3 of the plan in `Submission/Converse.lean`, stated as a
a complete contract whose hypotheses match exactly what
`smith_converse_interval` produces together with the bridge:

* a sequence `R` of monic irreducible integer polynomials whose complex roots
  are all `> 0`, with `natDegree → ∞` and root means → `m`;
* a bound `m < c1`;
* the algebraic bridge (`Submission.AlgebraicBridge.bridge`) turning root-mean
  bounds into totally-positive roots.

The conclusion is the infinite injective family of totally positive algebraic
integers with `trace < c1 · degree` — precisely the input consumed by
`Submission.Reduction.lambda_SSS_le_of_family`.

Proof plan: (i) `hmean` gives `∀ᶠ n, rootMeanReal (R n) < c1`, so (bridge)
gives `∀ᶠ n, ∃ β root of R n` with `IsIntegral ℤ β ∧ IsTotallyPositive β ∧
trace β < c1 · degree β`; (ii) `hdeg` (`natDegree → ∞`) yields a strictly
degree-increasing subsequence `n_k`, making the chosen roots pairwise
distinct (`degree` is a function of the element); (iii) assemble `f k`.
-/

noncomputable section

open MeasureTheory
open ComplexOrder
open Filter
open AlgebraicIntegers
open scoped Real ENNReal Topology

namespace Submission.Assembly

open Submission.Notions
open Submission.AlgebraicBridge

/-! ## Private algebraic bridge helpers (copies of lemmas in `AlgebraicBridge`,
which are `private` there and hence not importable). -/

/-- Sum of a multiset of complex numbers with nonnegative real parts has
nonnegative real part. -/
private lemma multiset_re_sum_nonneg {m : Multiset ℂ} (hm : ∀ z ∈ m, 0 ≤ z.re) :
    0 ≤ (m.sum).re := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      have ha : 0 ≤ a.re := hm a (by simp)
      have hs : 0 ≤ (s.sum).re := ih (fun z hz => hm z (by simp [hz]))
      rw [Multiset.sum_cons, Complex.add_re]
      exact add_nonneg ha hs

/-- Sum of a multiset of complex numbers all of which are real (imaginary part
zero) has imaginary part zero. -/
private lemma multiset_sum_im {m : Multiset ℂ} (hm : ∀ z ∈ m, z.im = 0) :
    (m.sum).im = 0 := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      have ha : a.im = 0 := hm a (by simp)
      have hs : (s.sum).im = 0 := ih (fun z hz => hm z (by simp [hz]))
      simp [ha, hs]

/-- Evaluating a polynomial over ℚ at `z : ℂ` gives the same result as
evaluating the underlying integer polynomial at `z`. -/
private lemma aeval_rat_eq_aeval_int (p : Polynomial ℤ) (z : ℂ) :
    Polynomial.aeval z (p.map (algebraMap ℤ ℚ)) = Polynomial.aeval z p := by
  exact (Polynomial.aeval_eq_aeval_map (R := ℤ) (S := ℂ) (T := ℚ)
    (φ := algebraMap ℤ ℚ) (by
      exact (IsScalarTower.algebraMap_eq ℤ ℚ ℂ).symm) p z).symm

/-- If every complex root of `R` is a positive real number then the (real) root
mean (the mean of the roots) is nonnegative. -/
private lemma rootMeanReal_nonneg_of_pos_roots {R : Polynomial ℤ}
    (hpos : ∀ z : ℂ, Polynomial.aeval z R = 0 → (0 : ℂ) < z) : 0 ≤ rootMeanReal R := by
  unfold rootMeanReal rootSumComplex
  refine div_nonneg ?_ (by positivity)
  exact multiset_re_sum_nonneg (fun z hz => by
    have hzmem : (R.map (algebraMap ℤ ℚ)) ≠ 0 ∧
        Polynomial.aeval z (R.map (algebraMap ℤ ℚ)) = 0 := by
      exact (Polynomial.mem_aroots.mp hz)
    have hzR : Polynomial.aeval z R = 0 := by
      rw [← aeval_rat_eq_aeval_int R z]
      exact hzmem.2
    exact le_of_lt ((Complex.pos_iff.mp (hpos z hzR)).1))

/-! ## The strengthened algebraic bridge

`AlgebraicBridge.bridge` returns a root `β` with the trace bound, but does not
remember which polynomial `β` is a root of nor the identity
`degree β = natDegree R`.  For assembling an *injective* family we need those
facts, so we re-prove the bridge with a stronger conclusion. -/

/-- From a monic irreducible integer polynomial all of whose complex roots are
positive real numbers and whose root sum is below `c * natDegree`, extract a
totally positive algebraic integer root with `degree = natDegree` and
`trace < c * degree`. -/
theorem strong_bridge {R : Polynomial ℤ} (hmon : R.Monic) (hirr : Irreducible R)
    (hdeg : 1 ≤ R.natDegree) (hpos : ∀ z : ℂ, Polynomial.aeval z R = 0 → (0 : ℂ) < z) {c : ℝ}
    (hc : (rootSumComplex R).re < c * (R.natDegree : ℝ)) :
    ∃ β : ℂ, Polynomial.aeval β R = 0 ∧ degree β = R.natDegree ∧ IsIntegral ℤ β ∧
      IsTotallyPositive β ∧ trace β < (c : ℂ) * degree β := by
  -- `RQ` is the rational polynomial underlying `R`, `RC` its complex version.
  let RQ : Polynomial ℚ := R.map (algebraMap ℤ ℚ)
  let RC : Polynomial ℂ := R.map (algebraMap ℤ ℂ)
  -- By Gauss's lemma `RQ` is monic and irreducible over `ℚ`.
  have hRQ_mon : RQ.Monic := by
    simpa [RQ] using (hmon.map (algebraMap ℤ ℚ))
  have hRQ_irr : Irreducible RQ := by
    have hiff : Irreducible R ↔ Irreducible (R.map (algebraMap ℤ ℚ)) :=
      (hmon.irreducible_iff_irreducible_map_fraction_map (R := ℤ) (K := ℚ))
    simpa [RQ] using hiff.mp hirr
  -- `RC` is nonconstant, hence (ℂ algebraically closed) has a root `β`.
  have hRC_mon : RC.Monic := by
    simpa [RC] using (hmon.map (algebraMap ℤ ℂ))
  have hRC_natDegree : RC.natDegree = R.natDegree := by
    simpa [RC] using (hmon.natDegree_map (algebraMap ℤ ℂ))
  have hRC_deg_ne : RC.degree ≠ 0 := by
    have hnd : 0 < RC.natDegree := by
      rw [hRC_natDegree]
      exact lt_of_lt_of_le Nat.zero_lt_one hdeg
    exact ne_of_gt ((Polynomial.natDegree_pos_iff_degree_pos.mp hnd))
  obtain ⟨β, hβroot⟩ := IsAlgClosed.exists_root RC hRC_deg_ne
  have hβRC : Polynomial.eval β RC = 0 := by
    simpa [Polynomial.IsRoot] using hβroot
  have hβR : Polynomial.aeval β R = 0 := by
    rw [Polynomial.aeval_def]
    rw [Polynomial.eval₂_eq_eval_map]
    simpa [RC] using hβRC
  have hnatβ : Polynomial.aeval β RQ = Polynomial.aeval β R := by
    simpa [RQ] using (aeval_rat_eq_aeval_int R β)
  have hβRQ : Polynomial.aeval β RQ = 0 := by
    rw [hnatβ]
    exact hβR
  -- Minimal polynomial: since `RQ` is monic irreducible with root `β`,
  -- `minpoly ℚ β = RQ`.
  have hmin : minpoly ℚ β = RQ := by
    exact (minpoly.eq_of_irreducible_of_monic (A := ℚ) (x := β) hRQ_irr hβRQ hRQ_mon).symm
  have hdegβ : degree β = R.natDegree := by
    unfold degree
    rw [hmin]
    simpa [RQ] using (hmon.natDegree_map (algebraMap ℤ ℚ))
  have htraceβ : trace β = rootSumComplex R := by
    unfold trace
    rw [hmin, rootSumComplex]
  -- Every conjugate of `β` (root of `minpoly ℚ β`) is a complex root of `R`,
  -- hence positive by `hpos`.
  have hconj_pos : ∀ γ ∈ (minpoly ℚ β).aroots ℂ, 0 < γ := by
    intro γ hγ
    rw [hmin] at hγ
    have hγmem : RQ ≠ 0 ∧ Polynomial.aeval γ RQ = 0 := by
      exact (Polynomial.mem_aroots.mp hγ)
    have hnatγ : Polynomial.aeval γ RQ = Polynomial.aeval γ R := by
      simpa [RQ] using (aeval_rat_eq_aeval_int R γ)
    have hγR : Polynomial.aeval γ R = 0 := by
      rw [← hnatγ]
      exact hγmem.2
    exact hpos γ hγR
  refine ⟨β, hβR, hdegβ, ?_⟩
  constructor
  · exact ⟨R, hmon, hβR⟩
  · constructor
    · constructor
      · unfold IsAlgebraic
        refine ⟨RQ, ?_, hβRQ⟩
        exact hRQ_mon.ne_zero
      · exact hconj_pos
    · -- trace comparison: the trace is a real number, and its real part is
      -- bounded by `hc`; use the real-comparison criterion of `Reduction`.
      have htr_im : (trace β).im = 0 := by
        rw [htraceβ]
        unfold rootSumComplex
        apply multiset_sum_im
        intro z hz
        have hzmem : RQ ≠ 0 ∧ Polynomial.aeval z RQ = 0 := by
          exact (Polynomial.mem_aroots.mp hz)
        have hnatγ : Polynomial.aeval z RQ = Polynomial.aeval z R := by
          simpa [RQ] using (aeval_rat_eq_aeval_int R z)
        have hzR : Polynomial.aeval z R = 0 := by
          rw [← hnatγ]
          exact hzmem.2
        exact (Complex.pos_iff.mp (hpos z hzR)).2.symm
      have hre : (trace β).re < c * (degree β : ℝ) := by
        rw [htraceβ, hdegβ]
        exact hc
      exact (Submission.Reduction.trace_lt_mul_degree_iff htr_im).mpr hre


/-- From a converse-theorem-style polynomial sequence with root means tending
to `m < c1`, produce the injective totally-positive family bounded by `c1`. -/
theorem family_of_converse_data {R : ℕ → Polynomial ℤ} {m c1 : ℝ}
    (hR : ∀ n : ℕ, (R n).Monic ∧ Irreducible (R n) ∧ 1 ≤ (R n).natDegree)
    (hpos : ∀ n : ℕ, ∀ z : ℂ, Polynomial.aeval z (R n) = 0 → (0 : ℂ) < z)
    (hdeg : Tendsto (fun n : ℕ => (R n).natDegree) atTop atTop)
    (hmean : Tendsto (fun n : ℕ => rootMeanReal (R n)) atTop (𝓝 m))
    (hmlt : m < c1) :
    ∃ f : ℕ → ℂ, Function.Injective f ∧
      ∀ n : ℕ, IsIntegral ℤ (f n) ∧ IsTotallyPositive (f n) ∧
        trace (f n) < (c1 : ℂ) * degree (f n) := by
  -- Every root sum is nonnegative (all roots are positive reals), and the root
  -- sums tend to `m`; hence `0 ≤ m` and therefore `0 < c1`.
  have hsum_nonneg : ∀ n : ℕ, 0 ≤ rootMeanReal (R n) := by
    intro n
    exact rootMeanReal_nonneg_of_pos_roots (hpos n)
  have hm_nonneg : 0 ≤ m := by
    exact (le_of_tendsto_of_tendsto (f := fun _ : ℕ => (0 : ℝ))
      (g := fun n : ℕ => rootMeanReal (R n)) tendsto_const_nhds hmean
      (Eventually.of_forall hsum_nonneg))
  have hc1pos : 0 < c1 := lt_of_le_of_lt hm_nonneg hmlt
  -- From `m < c1` and the convergence of the root means: eventually the mean
  -- is `< c1`, and (as degrees are `≥ 1`) the root *sum* is therefore below
  -- `c1 * natDegree`, which is exactly the hypothesis of the bridge.
  have hev_lt : ∀ᶠ n in atTop, rootMeanReal (R n) < c1 := by
    exact hmean.eventually (eventually_lt_nhds hmlt)
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hev_lt
  have hmain : ∀ n : ℕ, N0 ≤ n → (rootSumComplex (R n)).re < c1 * ((R n).natDegree : ℝ) := by
    intro n hn
    have hlt : rootMeanReal (R n) < c1 := hN0 n hn
    have hdeg_pos : (0 : ℝ) < ((R n).natDegree : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hR n).2.2)
    have hEq : (rootSumComplex (R n)).re = rootMeanReal (R n) * ((R n).natDegree : ℝ) := by
      unfold rootMeanReal
      rw [div_mul_eq_mul_div]
      have hnd : ((R n).natDegree : ℝ) ≠ 0 := ne_of_gt hdeg_pos
      field_simp [hnd]
    rw [hEq]
    exact mul_lt_mul_of_pos_right hlt hdeg_pos
  -- Choice at each index `n ≥ N0` of a good root (strengthened bridge).
  have hchoice : ∀ n : ℕ, N0 ≤ n →
      ∃ β : ℂ, Polynomial.aeval β (R n) = 0 ∧ degree β = (R n).natDegree ∧
        IsIntegral ℤ β ∧ IsTotallyPositive β ∧
        trace β < (c1 : ℂ) * degree β := by
    intro n hn
    exact strong_bridge (hR n).1 (hR n).2.1 (hR n).2.2 (hpos n) (hmain n hn)
  -- A strictly degree-increasing subsequence of indices `≥ N0`.
  have hstep : ∀ i : ℕ, ∃ n : ℕ, N0 ≤ n ∧ (R i).natDegree < (R n).natDegree := by
    intro i
    have hev : ∀ᶠ n in atTop, (R i).natDegree < (R n).natDegree := by
      have hev1 : ∀ᶠ n in atTop, (R i).natDegree + 1 ≤ (R n).natDegree :=
        (tendsto_atTop.mp hdeg) ((R i).natDegree + 1)
      filter_upwards [hev1] with n hn
      exact Nat.lt_of_succ_le hn
    rcases eventually_atTop.mp hev with ⟨N, hN⟩
    refine ⟨max N0 N, le_max_left N0 N, ?_⟩
    exact hN (max N0 N) (le_max_right N0 N)
  let idx : ℕ → ℕ := fun k =>
    Nat.rec (motive := fun _ : ℕ => ℕ) N0 (fun _ prev => Classical.choose (hstep prev)) k
  have hidx_ge : ∀ k : ℕ, N0 ≤ idx k := by
    intro k
    induction k with
    | zero => simp [idx]
    | succ k ih =>
        change N0 ≤ Classical.choose (hstep (idx k))
        exact (Classical.choose_spec (hstep (idx k))).1
  have hd_mono : StrictMono (fun k : ℕ => (R (idx k)).natDegree) := by
    refine strictMono_nat_of_lt_succ ?_
    intro k
    change (R (idx k)).natDegree < (R (Classical.choose (hstep (idx k)))).natDegree
    exact (Classical.choose_spec (hstep (idx k))).2
  let f : ℕ → ℂ := fun k => Classical.choose (hchoice (idx k) (hidx_ge k))
  have fspec : ∀ k : ℕ, Polynomial.aeval (f k) (R (idx k)) = 0 ∧
      degree (f k) = (R (idx k)).natDegree ∧ IsIntegral ℤ (f k) ∧
      IsTotallyPositive (f k) ∧ trace (f k) < (c1 : ℂ) * degree (f k) := by
    intro k
    dsimp [f]
    exact Classical.choose_spec (hchoice (idx k) (hidx_ge k))
  have hinj : Function.Injective f := by
    intro k j hkj
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hd : (R (idx k)).natDegree < (R (idx j)).natDegree := hd_mono hlt
      have hdeq : (R (idx k)).natDegree = (R (idx j)).natDegree := by
        calc
          (R (idx k)).natDegree = degree (f k) := (fspec k).2.1.symm
          _ = degree (f j) := by rw [hkj]
          _ = (R (idx j)).natDegree := (fspec j).2.1
      exact (ne_of_lt hd) hdeq
    · have hd : (R (idx j)).natDegree < (R (idx k)).natDegree := hd_mono hlt
      have hdeq : (R (idx k)).natDegree = (R (idx j)).natDegree := by
        calc
          (R (idx k)).natDegree = degree (f k) := (fspec k).2.1.symm
          _ = degree (f j) := by rw [hkj]
          _ = (R (idx j)).natDegree := (fspec j).2.1
      exact (ne_of_lt hd) hdeq.symm
  refine ⟨f, hinj, ?_⟩
  intro k
  exact ⟨(fspec k).2.2.1, (fspec k).2.2.2.1, (fspec k).2.2.2.2⟩

end Submission.Assembly


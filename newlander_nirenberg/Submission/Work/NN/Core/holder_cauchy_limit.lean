/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Completeness of the Hölder space `C^{k,α}`, sequence form

We prove the sequence-space form of the completeness of the Hölder space: a sequence of
`C^k` functions on an open set that is Cauchy for the Hölder norm has a `C^k` pointwise
limit, and the convergence takes place in the Hölder norm.

The proof is by induction on `k`.  For the induction step we need the same statement for
functions with values in an *arbitrary* complete real normed space (namely the space
`X →L[ℝ] E` of differentials), so we set up the Hölder-type norms `iterDerivNormE`,
`holderSeminormE`, `holderNormE` for a general target space `E`, prove the general
statement, and specialise to `E = ℂ` at the end.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder

noncomputable section

open scoped NNReal ENNReal Topology
open Set Filter

namespace Work.NN.Core

universe u v w

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## The Hölder-type norms for a general target space -/

/-- Supremum over `Ω` of the operator norm of the `i`-th iterated derivative of `f`
(values in an arbitrary real normed space `E`). -/
noncomputable def iterDerivNormE {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : ℕ) (f : X → E) (Ω : Set X) : ℝ≥0∞ :=
  ⨆ x ∈ Ω, ENNReal.ofReal ‖iteratedFDerivWithin ℝ i f Ω x‖

/-- Hölder seminorm of order `α` of the `i`-th iterated derivative of `f` on `Ω`. -/
noncomputable def holderSeminormE {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : ℕ) (α : ℝ) (f : X → E) (Ω : Set X) : ℝ≥0∞ :=
  ⨆ x ∈ Ω, ⨆ y ∈ Ω, ⨆ (_ : x ≠ y),
    ENNReal.ofReal
      (‖iteratedFDerivWithin ℝ i f Ω x - iteratedFDerivWithin ℝ i f Ω y‖ / ‖x - y‖ ^ α)

/-- The `C^{k,α}` norm of `f` on `Ω`, for a general target space. -/
noncomputable def holderNormE {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (α : ℝ) (f : X → E) (Ω : Set X) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range (k + 1), (iterDerivNormE i f Ω + holderSeminormE i α f Ω)

/-- The conclusion of the completeness statement for a fixed target space: existence of a
`C^k` pointwise limit in which the sequence converges for the Hölder norm. -/
def HolderCauchyConclusion {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (α : ℝ) (Ω : Set X) (f : ℕ → X → E) : Prop :=
  ∃ F : X → E, ContDiffOn ℝ k F Ω ∧
    (∀ x ∈ Ω, Tendsto (fun n => f n x) atTop (𝓝 (F x))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      holderNormE k α (F - f n) Ω ≤ ENNReal.ofReal ε)

/-! ### Basic component lemmas -/

@[simp] lemma iterDerivNormE_zero {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : X → E) (Ω : Set X) :
    iterDerivNormE 0 f Ω = ⨆ x ∈ Ω, ENNReal.ofReal ‖f x‖ := by
  simp [iterDerivNormE, norm_iteratedFDerivWithin_zero]

lemma le_iterDerivNormE {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : ℕ) (f : X → E) (Ω : Set X) {x : X} (hx : x ∈ Ω) :
    ENNReal.ofReal ‖iteratedFDerivWithin ℝ i f Ω x‖ ≤ iterDerivNormE i f Ω :=
  le_iSup₂_of_le x hx le_rfl

lemma le_holderSeminormE {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : ℕ) (α : ℝ) (f : X → E) (Ω : Set X) {x y : X}
    (hx : x ∈ Ω) (hy : y ∈ Ω) (hxy : x ≠ y) :
    ENNReal.ofReal
        (‖iteratedFDerivWithin ℝ i f Ω x - iteratedFDerivWithin ℝ i f Ω y‖ / ‖x - y‖ ^ α)
      ≤ holderSeminormE i α f Ω :=
  le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl))

lemma iterDerivNormE_le_holderNormE {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (α : ℝ) (f : X → E) (Ω : Set X) {i : ℕ} (hi : i ≤ k) :
    iterDerivNormE i f Ω ≤ holderNormE k α f Ω := by
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun i => iterDerivNormE i f Ω + holderSeminormE i α f Ω)
    (fun _ _ => bot_le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))
  exact le_add_right le_rfl

lemma holderSeminormE_le_holderNormE {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (α : ℝ) (f : X → E) (Ω : Set X) {i : ℕ} (hi : i ≤ k) :
    holderSeminormE i α f Ω ≤ holderNormE k α f Ω := by
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun i => iterDerivNormE i f Ω + holderSeminormE i α f Ω)
    (fun _ _ => bot_le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))
  exact le_add_left le_rfl

/-! ### Congruence -/

lemma eqOn_iteratedFDerivWithin {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : X → E} {Ω : Set X} (h : EqOn f g Ω) (i : ℕ) :
    EqOn (iteratedFDerivWithin ℝ i f Ω) (iteratedFDerivWithin ℝ i g Ω) Ω := by
  induction i with
  | zero => intro x hx; simp [iteratedFDerivWithin_zero_eq_comp, h hx]
  | succ i ih =>
    intro x hx
    rw [iteratedFDerivWithin_succ_eq_comp_left, iteratedFDerivWithin_succ_eq_comp_left,
      Function.comp_apply, Function.comp_apply,
      fderivWithin_congr (fun y hy => ih hy) (ih hx)]

lemma iterDerivNormE_congr {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : X → E} {Ω : Set X} (h : EqOn f g Ω) (i : ℕ) :
    iterDerivNormE i f Ω = iterDerivNormE i g Ω := by
  refine iSup_congr fun x => iSup_congr fun hx => ?_
  rw [eqOn_iteratedFDerivWithin h i hx]

lemma holderSeminormE_congr {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : X → E} {Ω : Set X} (h : EqOn f g Ω) (i : ℕ) (α : ℝ) :
    holderSeminormE i α f Ω = holderSeminormE i α g Ω := by
  refine iSup_congr fun x => iSup_congr fun hx => iSup_congr fun y => iSup_congr fun hy => ?_
  refine iSup_congr fun hxy => ?_
  rw [eqOn_iteratedFDerivWithin h i hx, eqOn_iteratedFDerivWithin h i hy]

lemma holderNormE_congr {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : X → E} {Ω : Set X} (h : EqOn f g Ω) (k : ℕ) (α : ℝ) :
    holderNormE k α f Ω = holderNormE k α g Ω := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iterDerivNormE_congr h i, holderSeminormE_congr h i α]

/-! ### Passing to the derivative -/

lemma norm_iteratedFDerivWithin_deriv_sub {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : X → E} {Ω : Set X} (hΩ : IsOpen Ω) (i : ℕ) {x y : X} (hx : x ∈ Ω) (hy : y ∈ Ω) :
    ‖iteratedFDerivWithin ℝ i (fun z => fderivWithin ℝ f Ω z) Ω x
      - iteratedFDerivWithin ℝ i (fun z => fderivWithin ℝ f Ω z) Ω y‖
    = ‖iteratedFDerivWithin ℝ (i + 1) f Ω x - iteratedFDerivWithin ℝ (i + 1) f Ω y‖ := by
  rw [iteratedFDerivWithin_succ_eq_comp_right (𝕜 := ℝ) (f := f) (s := Ω) (n := i)
        hΩ.uniqueDiffOn hx,
      iteratedFDerivWithin_succ_eq_comp_right (𝕜 := ℝ) (f := f) (s := Ω) (n := i)
        hΩ.uniqueDiffOn hy]
  simp only [Function.comp_apply]
  rw [← LinearIsometryEquiv.map_sub ((continuousMultilinearCurryRightEquiv' ℝ i X E).symm)
      (iteratedFDerivWithin ℝ i (fun z => fderivWithin ℝ f Ω z) Ω x)
      (iteratedFDerivWithin ℝ i (fun z => fderivWithin ℝ f Ω z) Ω y),
      LinearIsometryEquiv.norm_map]

lemma iterDerivNormE_deriv {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : X → E} {Ω : Set X} (hΩ : IsOpen Ω) (i : ℕ) :
    iterDerivNormE i (fun x => fderivWithin ℝ f Ω x) Ω = iterDerivNormE (i + 1) f Ω := by
  refine iSup_congr fun x => iSup_congr fun hx => ?_
  rw [norm_iteratedFDerivWithin_fderivWithin hΩ.uniqueDiffOn hx]

lemma holderSeminormE_deriv {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : X → E} {Ω : Set X} (hΩ : IsOpen Ω) (i : ℕ) (α : ℝ) :
    holderSeminormE i α (fun x => fderivWithin ℝ f Ω x) Ω = holderSeminormE (i + 1) α f Ω := by
  refine iSup_congr fun x => iSup_congr fun hx => iSup_congr fun y => iSup_congr fun hy => ?_
  refine iSup_congr fun hxy => ?_
  rw [norm_iteratedFDerivWithin_deriv_sub hΩ i hx hy]

/-- Decomposition of the `C^{k+1,α}` norm into the order-zero part and the `C^{k,α}` norm of the
differential. -/
lemma holderNormE_decomp {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : X → E} {Ω : Set X} (hΩ : IsOpen Ω) (k : ℕ) (α : ℝ) :
    holderNormE (k + 1) α f Ω
      = (iterDerivNormE 0 f Ω + holderSeminormE 0 α f Ω)
        + holderNormE k α (fun x => fderivWithin ℝ f Ω x) Ω := by
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (iterDerivNormE (i + 1) f Ω + holderSeminormE (i + 1) α f Ω))
      = holderNormE k α (fun x => fderivWithin ℝ f Ω x) Ω := by
    rw [holderNormE]
    exact Finset.sum_congr rfl fun i _ => by rw [iterDerivNormE_deriv hΩ i, holderSeminormE_deriv hΩ i α]
  calc holderNormE (k + 1) α f Ω
      = ∑ i ∈ Finset.range ((k + 1) + 1),
          (iterDerivNormE i f Ω + holderSeminormE i α f Ω) := rfl
    _ = (∑ i ∈ Finset.range (k + 1),
          (iterDerivNormE (i + 1) f Ω + holderSeminormE (i + 1) α f Ω))
          + (iterDerivNormE 0 f Ω + holderSeminormE 0 α f Ω) := Finset.sum_range_succ' _ _
    _ = (iterDerivNormE 0 f Ω + holderSeminormE 0 α f Ω)
          + holderNormE k α (fun x => fderivWithin ℝ f Ω x) Ω := by rw [h1, add_comm]

lemma holderNormE_deriv_le {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : X → E} {Ω : Set X} (hΩ : IsOpen Ω) (k : ℕ) (α : ℝ) :
    holderNormE k α (fun x => fderivWithin ℝ f Ω x) Ω ≤ holderNormE (k + 1) α f Ω := by
  rw [holderNormE_decomp hΩ k α]
  exact le_add_left le_rfl

/-! ### Bound helpers -/

lemma iterDerivNormE_zero_le {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : X → E} {Ω : Set X} {C : ℝ} (h : ∀ x ∈ Ω, ‖f x‖ ≤ C) :
    iterDerivNormE 0 f Ω ≤ ENNReal.ofReal C := by
  rw [iterDerivNormE_zero]
  exact iSup₂_le fun x hx => ENNReal.ofReal_le_ofReal (h x hx)

lemma holderSeminormE_zero_le {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : X → E} {Ω : Set X} {α C : ℝ}
    (h : ∀ x ∈ Ω, ∀ y ∈ Ω, x ≠ y → ‖f x - f y‖ / ‖x - y‖ ^ α ≤ C) :
    holderSeminormE 0 α f Ω ≤ ENNReal.ofReal C := by
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  have hnorm : ‖iteratedFDerivWithin ℝ 0 f Ω x - iteratedFDerivWithin ℝ 0 f Ω y‖
      = ‖f x - f y‖ := by
    rw [← dist_eq_norm, dist_iteratedFDerivWithin_zero, dist_eq_norm]
  rw [hnorm]
  exact ENNReal.ofReal_le_ofReal (h x hx y hy hxy)

lemma iterDerivNormE_zero_le_of_tendsto {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℕ → X → E} {U : X → E} {Ω : Set X} {C : ℝ}
    (hU : ∀ x ∈ Ω, Tendsto (fun n => u n x) atTop (𝓝 (U x)))
    (hb : ∀ᶠ n in atTop, ∀ x ∈ Ω, ‖u n x‖ ≤ C) :
    iterDerivNormE 0 U Ω ≤ ENNReal.ofReal C := by
  refine iterDerivNormE_zero_le fun x hx => ?_
  exact le_of_tendsto (hU x hx).norm (hb.mono fun n hn => hn x hx)

lemma holderSeminormE_zero_le_of_tendsto {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℕ → X → E} {U : X → E} {Ω : Set X} {α C : ℝ}
    (hU : ∀ x ∈ Ω, Tendsto (fun n => u n x) atTop (𝓝 (U x)))
    (hb : ∀ᶠ n in atTop, ∀ x ∈ Ω, ∀ y ∈ Ω, x ≠ y → ‖u n x - u n y‖ / ‖x - y‖ ^ α ≤ C) :
    holderSeminormE 0 α U Ω ≤ ENNReal.ofReal C := by
  refine holderSeminormE_zero_le fun x hx y hy hxy => ?_
  have ht : Tendsto (fun n => ‖u n x - u n y‖ / ‖x - y‖ ^ α) atTop
      (𝓝 (‖U x - U y‖ / ‖x - y‖ ^ α)) := (((hU x hx).sub (hU y hy)).norm).div_const _
  exact le_of_tendsto ht (hb.mono fun n hn => hn x hx y hy hxy)

/-- The Cauchy condition in the Hölder norm gives uniform Cauchy in sup norm. -/
lemma uniform_bound_of_holderNormE_cauchy {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℕ → X → E} {Ω : Set X} {k : ℕ} {α : ℝ}
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      holderNormE k α (f n - f m) Ω ≤ ENNReal.ofReal ε)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m → ∀ x ∈ Ω, ‖(f n - f m) x‖ ≤ ε := by
  obtain ⟨N, hN⟩ := hcauchy ε hε
  refine ⟨N, fun n m hn hm x hx => ?_⟩
  have h := le_trans (le_iterDerivNormE 0 (f n - f m) Ω hx)
      (le_trans (iterDerivNormE_le_holderNormE k α (f n - f m) Ω (Nat.zero_le k))
        (hN n m hn hm))
  rw [norm_iteratedFDerivWithin_zero] at h
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp h

/-- The Cauchy condition in the Hölder norm gives uniform Cauchy for the Hölder quotient of
order zero. -/
lemma uniform_holder_bound_of_holderNormE_cauchy {E : Type v} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℕ → X → E} {Ω : Set X} {k : ℕ} {α : ℝ}
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      holderNormE k α (f n - f m) Ω ≤ ENNReal.ofReal ε)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m → ∀ x ∈ Ω, ∀ y ∈ Ω, x ≠ y →
      ‖(f n - f m) x - (f n - f m) y‖ / ‖x - y‖ ^ α ≤ ε := by
  obtain ⟨N, hN⟩ := hcauchy ε hε
  refine ⟨N, fun n m hn hm x hx y hy hxy => ?_⟩
  have h := le_trans (le_holderSeminormE 0 α (f n - f m) Ω hx hy hxy)
      (le_trans (holderSeminormE_le_holderNormE k α (f n - f m) Ω (Nat.zero_le k))
        (hN n m hn hm))
  rw [show ‖iteratedFDerivWithin ℝ 0 (f n - f m) Ω x
          - iteratedFDerivWithin ℝ 0 (f n - f m) Ω y‖
        = ‖(f n - f m) x - (f n - f m) y‖ from by
      rw [← dist_eq_norm, dist_iteratedFDerivWithin_zero, dist_eq_norm]] at h
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp h

/-! ### The base case -/

theorem holderNormE_zero {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {α : ℝ} {Ω : Set X} (_hΩ : IsOpen Ω) {f : ℕ → X → E}
    (hcd : ∀ n, ContDiffOn ℝ 0 (f n) Ω)
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      holderNormE 0 α (f n - f m) Ω ≤ ENNReal.ofReal ε) :
    HolderCauchyConclusion 0 α Ω f := by
  have hcs : ∀ x ∈ Ω, CauchySeq (fun n => f n x) := by
    intro x hx
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := uniform_bound_of_holderNormE_cauchy hcauchy (by linarith : 0 < ε / 2)
    refine ⟨N, fun n hn m hm => ?_⟩
    have h := hN n m hn hm x hx
    simp only [Pi.sub_apply] at h
    rw [dist_eq_norm]
    linarith
  have hconv : ∀ x : X, ∃ y : E, x ∈ Ω → Tendsto (fun n => f n x) atTop (𝓝 y) := by
    intro x
    by_cases hx : x ∈ Ω
    · obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete (hcs x hx)
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose F hF using hconv
  have hunif : TendstoUniformlyOn (fun n => f n) F atTop Ω := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := uniform_bound_of_holderNormE_cauchy hcauchy (by linarith : 0 < ε / 2)
    refine eventually_atTop.mpr ⟨N, fun n hn x hx => ?_⟩
    have htend : Tendsto (fun m => ‖(f n - f m) x‖) atTop (𝓝 ‖(f n - F) x‖) := by
      have h1 : Tendsto (fun m => (f n - f m) x) atTop (𝓝 ((f n - F) x)) := by
        have := (hF x hx).const_sub (f n x)
        simpa only [Pi.sub_apply] using this
      exact h1.norm
    have hev : ∀ᶠ m in atTop, ‖(f n - f m) x‖ ≤ ε / 2 :=
      eventually_atTop.mpr ⟨N, fun m hm => hN n m hn hm x hx⟩
    have hle := le_of_tendsto htend hev
    simp only [Pi.sub_apply] at hle
    rw [dist_eq_norm, norm_sub_rev]
    linarith
  have hFcd : ContDiffOn ℝ 0 F Ω := by
    rw [contDiffOn_zero]
    exact hunif.continuousOn
      (Eventually.of_forall fun n => (hcd n).continuousOn).frequently
  refine ⟨F, hFcd, hF, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := uniform_bound_of_holderNormE_cauchy hcauchy (by linarith : 0 < ε / 2)
  obtain ⟨N', hN'⟩ :=
    uniform_holder_bound_of_holderNormE_cauchy hcauchy (by linarith : 0 < ε / 2)
  refine ⟨max N N', fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnN' : N' ≤ n := le_trans (le_max_right _ _) hn
  have h1 : iterDerivNormE 0 (F - f n) Ω ≤ ENNReal.ofReal (ε / 2) := by
    refine iterDerivNormE_zero_le_of_tendsto (u := fun m => f m - f n) (U := F - f n)
      (fun x hx => ?_) (eventually_atTop.mpr ⟨N, fun m hm x hx => ?_⟩)
    · have := (hF x hx).sub_const (f n x)
      simpa only [Pi.sub_apply] using this
    · simpa only [Pi.sub_apply] using hN m n hm hnN x hx
  have h2 : holderSeminormE 0 α (F - f n) Ω ≤ ENNReal.ofReal (ε / 2) := by
    refine holderSeminormE_zero_le_of_tendsto (u := fun m => f m - f n) (U := F - f n)
      (fun x hx => ?_) (eventually_atTop.mpr ⟨N', fun m hm x hx y hy hxy => ?_⟩)
    · have := (hF x hx).sub_const (f n x)
      simpa only [Pi.sub_apply] using this
    · simpa only [Pi.sub_apply] using hN' m n hm hnN' x hx y hy hxy
  rw [holderNormE, Finset.sum_range_one]
  calc iterDerivNormE 0 (F - f n) Ω + holderSeminormE 0 α (F - f n) Ω
      ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add h1 h2
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by linarith : (0 : ℝ) ≤ ε / 2)
          (by linarith : (0 : ℝ) ≤ ε / 2)]
        norm_num

/-! ### The induction step -/

theorem holderNormE_succ {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (k : ℕ)
    (ih : ∀ {E' : Type (max u v)} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
      {α : ℝ} {Ω : Set X}, IsOpen Ω → ∀ {f : ℕ → X → E'},
      (∀ n, ContDiffOn ℝ k (f n) Ω) →
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
        holderNormE k α (f n - f m) Ω ≤ ENNReal.ofReal ε) →
      HolderCauchyConclusion k α Ω f)
    {α : ℝ} {Ω : Set X} (hΩ : IsOpen Ω) {f : ℕ → X → E}
    (hcd : ∀ n, ContDiffOn ℝ (k + 1) (f n) Ω)
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      holderNormE (k + 1) α (f n - f m) Ω ≤ ENNReal.ofReal ε) :
    HolderCauchyConclusion (k + 1) α Ω f := by
  let g : ℕ → X → (X →L[ℝ] E) := fun n x => fderivWithin ℝ (f n) Ω x
  have hdiff : ∀ n x, x ∈ Ω → DifferentiableWithinAt ℝ (f n) Ω x := fun n x hx =>
    ((hcd n).contDiffWithinAt hx).differentiableWithinAt (by simp)
  have hgcd : ∀ n, ContDiffOn ℝ k (g n) Ω := by
    intro n
    exact (hcd n).fderivWithin hΩ.uniqueDiffOn (by simp)
  have hgcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      holderNormE k α (g n - g m) Ω ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy ε hε
    refine ⟨N, fun n m hn hm => ?_⟩
    have hcongr : holderNormE k α (g n - g m) Ω
        = holderNormE k α (fun x => fderivWithin ℝ (f n - f m) Ω x) Ω := by
      refine holderNormE_congr (fun x hx => ?_) k α
      rw [fderivWithin_sub (hΩ.uniqueDiffWithinAt hx) (hdiff n x hx) (hdiff m x hx)]
      rfl
    rw [hcongr]
    exact le_trans (holderNormE_deriv_le hΩ k α) (hN n m hn hm)
  obtain ⟨G, hGcd, hGconv, hGbound⟩ := ih hΩ (f := g) hgcd hgcauchy
  have hcs : ∀ x ∈ Ω, CauchySeq (fun n => f n x) := by
    intro x hx
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := uniform_bound_of_holderNormE_cauchy hcauchy (by linarith : 0 < ε / 2)
    refine ⟨N, fun n hn m hm => ?_⟩
    have h := hN n m hn hm x hx
    simp only [Pi.sub_apply] at h
    rw [dist_eq_norm]
    linarith
  have hconv : ∀ x : X, ∃ y : E, x ∈ Ω → Tendsto (fun n => f n x) atTop (𝓝 y) := by
    intro x
    by_cases hx : x ∈ Ω
    · obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete (hcs x hx)
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose F hF using hconv
  have hunif : TendstoUniformlyOn g G atTop Ω := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hGbound (ε / 2) (by linarith)
    refine eventually_atTop.mpr ⟨N, fun n hn x hx => ?_⟩
    have hb : ENNReal.ofReal ‖(G - g n) x‖ ≤ ENNReal.ofReal (ε / 2) :=
      le_trans (by simpa using le_iterDerivNormE 0 (G - g n) Ω hx)
        (le_trans (iterDerivNormE_le_holderNormE k α (G - g n) Ω (Nat.zero_le k)) (hN n hn))
    have hb' : ‖(G - g n) x‖ ≤ ε / 2 :=
      (ENNReal.ofReal_le_ofReal_iff (by linarith : (0 : ℝ) ≤ ε / 2)).mp hb
    simp only [Pi.sub_apply] at hb'
    rw [dist_eq_norm]
    linarith
  have hFderiv : ∀ x ∈ Ω, HasFDerivAt F (G x) x := by
    intro x hx
    refine hasFDerivAt_of_tendstoUniformlyOn hΩ hunif (fun n y hy => ?_)
      (fun y hy => hF y hy) hx
    exact (hdiff n y hy).hasFDerivWithinAt.hasFDerivAt (hΩ.mem_nhds hy)
  have hFderivWithin : ∀ x ∈ Ω, HasFDerivWithinAt F (G x) Ω x :=
    fun x hx => (hFderiv x hx).hasFDerivWithinAt
  have hfw : ∀ x ∈ Ω, fderivWithin ℝ F Ω x = G x := fun x hx =>
    (hFderivWithin x hx).fderivWithin (hΩ.uniqueDiffWithinAt hx)
  have hFcd' : ContDiffOn ℝ ((k : WithTop ℕ∞) + 1) F Ω := by
    rw [contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hΩ.uniqueDiffOn]
    exact ⟨fun hcontra => absurd hcontra (by simp), G, hGcd, hFderivWithin⟩
  have hFcd : ContDiffOn ℝ (k + 1) F Ω := by simpa using hFcd'
  refine ⟨F, hFcd, hF, fun ε hε => ?_⟩
  obtain ⟨Ng, hNg⟩ := hGbound (ε / 3) (by linarith)
  obtain ⟨N1, hN1⟩ := uniform_bound_of_holderNormE_cauchy hcauchy (by linarith : 0 < ε / 3)
  obtain ⟨N2, hN2⟩ :=
    uniform_holder_bound_of_holderNormE_cauchy hcauchy (by linarith : 0 < ε / 3)
  refine ⟨max Ng (max N1 N2), fun n hn => ?_⟩
  have hnG : Ng ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : N1 ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
  have hn2 : N2 ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)
  have h1 : iterDerivNormE 0 (F - f n) Ω ≤ ENNReal.ofReal (ε / 3) := by
    refine iterDerivNormE_zero_le_of_tendsto (u := fun m => f m - f n) (U := F - f n)
      (fun x hx => ?_) (eventually_atTop.mpr ⟨N1, fun m hm x hx => ?_⟩)
    · have := (hF x hx).sub_const (f n x)
      simpa only [Pi.sub_apply] using this
    · simpa only [Pi.sub_apply] using hN1 m n hm hn1 x hx
  have h2 : holderSeminormE 0 α (F - f n) Ω ≤ ENNReal.ofReal (ε / 3) := by
    refine holderSeminormE_zero_le_of_tendsto (u := fun m => f m - f n) (U := F - f n)
      (fun x hx => ?_) (eventually_atTop.mpr ⟨N2, fun m hm x hx y hy hxy => ?_⟩)
    · have := (hF x hx).sub_const (f n x)
      simpa only [Pi.sub_apply] using this
    · simpa only [Pi.sub_apply] using hN2 m n hm hn2 x hx y hy hxy
  have h3 : holderNormE k α (fun x => fderivWithin ℝ (F - f n) Ω x) Ω
      ≤ ENNReal.ofReal (ε / 3) := by
    have hcongr : holderNormE k α (fun x => fderivWithin ℝ (F - f n) Ω x) Ω
        = holderNormE k α (G - g n) Ω := by
      refine holderNormE_congr (fun x hx => ?_) k α
      rw [fderivWithin_sub (hΩ.uniqueDiffWithinAt hx)
        (hFderivWithin x hx).differentiableWithinAt (hdiff n x hx)]
      simp only [Pi.sub_apply]
      rw [hfw x hx]
    rw [hcongr]
    exact hNg n hnG
  rw [holderNormE_decomp hΩ k α]
  calc (iterDerivNormE 0 (F - f n) Ω + holderSeminormE 0 α (F - f n) Ω)
        + holderNormE k α (fun x => fderivWithin ℝ (F - f n) Ω x) Ω
      ≤ (ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3)) + ENNReal.ofReal (ε / 3) :=
        add_le_add (add_le_add h1 h2) h3
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by linarith : (0 : ℝ) ≤ ε / 3)
            (by linarith : (0 : ℝ) ≤ ε / 3),
          ← ENNReal.ofReal_add (by linarith : (0 : ℝ) ≤ ε / 3 + ε / 3)
            (by linarith : (0 : ℝ) ≤ ε / 3)]
        congr 1
        ring

/-! ### The general theorem -/

theorem holderNormE_cauchy_limit (k : ℕ) :
    ∀ {E : Type (max u v)} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      {α : ℝ} {Ω : Set X}, IsOpen Ω → ∀ {f : ℕ → X → E},
      (∀ n, ContDiffOn ℝ k (f n) Ω) →
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
        holderNormE k α (f n - f m) Ω ≤ ENNReal.ofReal ε) →
      HolderCauchyConclusion k α Ω f := by
  induction k with
  | zero => intro E _ _ _ α Ω hΩ f hcd hcauchy; exact holderNormE_zero hΩ hcd hcauchy
  | succ k ih =>
    intro E _ _ _ α Ω hΩ f hcd hcauchy
    exact holderNormE_succ k ih hΩ hcd hcauchy

/-! ### The requested statement -/

/-- **Completeness of the Hölder space `C^{k,α}`, sequence form.**

Let `Ω` be open, `k : ℕ`, `α : ℝ` and `f n : X → ℂ` a sequence of `C^k` functions on `Ω` which is
Cauchy for the Hölder norm `holderNorm k α · Ω`.  Then there is `F : X → ℂ`, `C^k` on `Ω`, which is
the pointwise limit of the `f n` on `Ω`, and the sequence converges to `F` in the Hölder norm. -/
theorem holder_cauchy_limit {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {k : ℕ} {α : ℝ} {Ω : Set X} (hΩ : IsOpen Ω) {f : ℕ → X → ℂ}
    (hcd : ∀ n, ContDiffOn ℝ k (f n) Ω)
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      Work.CR.Flat.holderNorm k α (fun x => f n x - f m x) Ω ≤ ENNReal.ofReal ε) :
    ∃ F : X → ℂ, ContDiffOn ℝ k F Ω ∧
      (∀ x ∈ Ω, Tendsto (fun n => f n x) atTop (𝓝 (F x))) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        Work.CR.Flat.holderNorm k α (fun x => F x - f n x) Ω ≤ ENNReal.ofReal ε) := by
  cases k with
  | zero => exact holderNormE_zero hΩ hcd hcauchy
  | succ k' =>
    exact holderNormE_succ (X := X) (E := ℂ) k'
      (fun {E'} _ _ _ {α'} {Ω'} hΩ' {f'} hcd' hca' =>
        holderNormE_cauchy_limit (k := k') (E := E') hΩ' hcd' hca')
      hΩ hcd hcauchy

end Work.NN.Core

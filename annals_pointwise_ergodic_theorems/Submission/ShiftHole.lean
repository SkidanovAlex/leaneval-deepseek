import ChallengeDeps
import Mathlib.Tactic
import Submission.Transference
import Submission.ReductionR
import Submission.Port.Aesm

/-!
# The remaining gap: the variational ergodic theorem on the integers

In view of the Calderón transference principle (`Submission.Transference`), the whole content of
Theorem 1.17 (iv) is the corresponding variational estimate for the *integer shift model*
`(ℤ, μ_ℤ, T_ℤ)`, `T_ℤ(n) = n - 1`.  In the paper this is Theorem "end-var"
(Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
averages*, Annals 195 (2022)), which is stated for the *upper half* averages

`Ã_N(f,g)(x) = (1/⌊N⌋) ∑_{⌊N/2⌋ < n ≤ ⌊N⌋} f(x + n) g(x + P(n))`

at *finite* `λ`-lacunary sets of scales `D ⊂ [1,∞)`, and for `f ∈ ℓ^{p₁}(ℤ)`, `g ∈ ℓ^{p₂}(ℤ)`
with `p₁⁻¹ + p₂⁻¹ = p⁻¹` and `r > 2`.

This file isolates that estimate, in the paper's own *finite*-lacunary-set formulation, as
`exists_varEstHalfFin_Cv` (the **only** `sorry` of the whole development): for every `K` one has
the estimate for the halved averages at the finite set of scales `{a 0, …, a K}`, with a constant
independent of `K` and of the lacunary sequence `a`.  The rest of the chain is then formalised:

* `varEstHalf_of_varEstHalfFin` passes from the finite sets of scales to the infinite `Λ`-lacunary
  sequence `VarEstHalfR` (this is the monotone-convergence step performed in the paper's proof of
  Proposition 3.1 (i), using the clamping lemmas of `Submission.VarClamp`);
* `varEstZ_of_varEstHalf` passes from the halved averages to the *long* averages `VarEstZ` on the
  integers (Proposition 3.1 (iii), via `Submission.TelescopeR`/`Submission.ReductionR`);
* `Submission.Transference.varEst_of_varEstZ` is Proposition 3.1 (ii) (Calderón transference);
* `Submission.Reductions` is Proposition 3.1 (i) (long variational estimate ⟹ maximal estimate,
  a.e. convergence and `Lᵖ` convergence).

Together these yield the four theorems of the paper's Theorem 1.17.

One remark on the exact shape of the gap.  The estimate `exists_varEstHalfFin_Cv` — like the
paper's — concerns `ℓᵖ`-functions (`MemLp` together with the `Lᵖ`-seminorm on the right-hand
side), whereas the integer-shift formulation used by the transference argument, `VarEstZ`, is
stated for *arbitrary* functions `f, g : ℤ → ℂ` (possibly of infinite `ℓᵖ` seminorm).  The passage
between the two is carried out in `varEstZ_of_varEstHalf`: on `ℤ` with counting measure there are
no non-empty null sets, so a vanishing `eLpNorm` means *pointwise* vanishing, and every function
(and hence every `AhalfR`-average) is measurable; the remaining cases (where one of the `eLpNorm`s
is infinite) are vacuous because the constant `cvLong Cv Λ` is positive. -/


set_option maxHeartbeats 1000000

namespace Submission

open _root_.PointwiseErgodicTheorems
set_option autoImplicit false

namespace PointwiseErgodicTheorems

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {μ : Measure 𝓧} [SigmaFinite μ]
  {T : 𝓧 ≃ᵐ 𝓧} {P : ℤ[X]} {p₁ p₂ p : ℝ≥0∞} {r : ℝ≥0}

omit [SigmaFinite μ] in
/-- If `s` is a null set for `μ`, then almost every point has its entire `T`-orbit
(`T ^ k`, `k ∈ ℤ`) outside `s`. -/
lemma ae_forall_zpow_notMem (hT : MeasurePreserving T μ μ) {s : Set 𝓧} (hs : μ s = 0) :
    ∀ᵐ x ∂μ, ∀ k : ℤ, ((T : 𝓧 ≃ 𝓧) ^ k) x ∉ s := by
  have hZ : μ (⋃ k : ℤ, (fun x : 𝓧 => ((T : 𝓧 ≃ 𝓧) ^ k) x) ⁻¹' s) = 0 := by
    rw [measure_iUnion_null_iff]
    intro k
    exact (measurePreserving_zpow_apply (μ := μ) hT k).preimage_null hs
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hZ] with x hx k hk
  exact hx (Set.mem_iUnion.mpr ⟨k, hk⟩)

/-- The averages `A` agree at a point `x` as soon as `f, g` and `f', g'` agree along the whole
orbit of `x`. -/
lemma A_congr_pointwise (T : 𝓧 ≃ᵐ 𝓧) (N : ℝ≥0) (P₁ P₂ : ℤ[X]) {f f' g g' : 𝓧 → ℂ} {x : 𝓧}
    (hfx : ∀ k : ℤ, f (((T : 𝓧 ≃ 𝓧) ^ k) x) = f' (((T : 𝓧 ≃ 𝓧) ^ k) x))
    (hgx : ∀ k : ℤ, g (((T : 𝓧 ≃ 𝓧) ^ k) x) = g' (((T : 𝓧 ≃ 𝓧) ^ k) x)) :
    A T N P₁ P₂ f g x = A T N P₁ P₂ f' g' x := by
  simp only [A]
  have hsum : (∑ n ∈ Icc 1 (Nat.floor N),
        f ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x) * g ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x))
      = (∑ n ∈ Icc 1 (Nat.floor N),
        f' ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x) * g' ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x)) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hfx (P₁.eval (n : ℤ)), hgx (P₂.eval (n : ℤ))]
  rw [hsum]

omit [SigmaFinite μ] in
/-- If `f =ᵐ[μ] f'` and `g =ᵐ[μ] g'`, then the variational norms of the two families of averages
agree almost everywhere. -/
lemma ae_variationalNorm_A_eq (hT : MeasurePreserving T μ μ) {P₁ P₂ : ℤ[X]} {a : ℕ → ℝ≥0}
    {f f' g g' : 𝓧 → ℂ} (hff' : f =ᵐ[μ] f') (hgg' : g =ᵐ[μ] g') :
    (fun x => variationalNorm r (fun n => A T (a n) P₁ P₂ f g x))
      =ᵐ[μ] fun x => variationalNorm r (fun n => A T (a n) P₁ P₂ f' g' x) := by
  have h1 : μ {x | f x ≠ f' x} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hff'] with x hx
    exact fun hc => hc hx
  have h2 : μ {x | g x ≠ g' x} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hgg'] with x hx
    exact fun hc => hc hx
  have hS : μ ({x | f x ≠ f' x} ∪ {x | g x ≠ g' x}) = 0 := measure_union_null h1 h2
  filter_upwards [ae_forall_zpow_notMem hT hS] with x hx
  have hfx : ∀ k : ℤ, f (((T : 𝓧 ≃ 𝓧) ^ k) x) = f' (((T : 𝓧 ≃ 𝓧) ^ k) x) := by
    intro k
    have h := hx k
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
    exact h.1
  have hgx : ∀ k : ℤ, g (((T : 𝓧 ≃ 𝓧) ^ k) x) = g' (((T : 𝓧 ≃ 𝓧) ^ k) x) := by
    intro k
    have h := hx k
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
    exact h.2
  have hfun : (fun n => A T (a n) P₁ P₂ f g x) = (fun n => A T (a n) P₁ P₂ f' g' x) :=
    funext fun n => A_congr_pointwise T (a n) P₁ P₂ hfx hgx
  rw [hfun]


/-- The averaging operator annihilates a vanishing second factor. -/
lemma A_right_zero (T : 𝓧 ≃ᵐ 𝓧) (N : ℝ≥0) (P₁ P₂ : ℤ[X]) (f : 𝓧 → ℂ) (x : 𝓧) :
    A T N P₁ P₂ f 0 x = 0 := by
  simp [A]

/-- The averaging operator annihilates a vanishing first factor. -/
lemma A_left_zero (T : 𝓧 ≃ᵐ 𝓧) (N : ℝ≥0) (P₁ P₂ : ℤ[X]) (g : 𝓧 → ℂ) (x : 𝓧) :
    A T N P₁ P₂ 0 g x = 0 := by
  simp [A]

/-- On `ℤ` with counting measure, a function whose `eLpNorm` vanishes is identically zero: there
are no non-empty null sets, and every function is measurable. -/
lemma eq_zero_of_eLpNorm_count_eq_zero {q : ℝ≥0∞} (hq : q ≠ 0) {f : ℤ → ℂ}
    (h : eLpNorm f q Measure.count = 0) : ∀ n, f n = 0 := by
  have hae : AEStronglyMeasurable f (Measure.count : Measure ℤ) :=
    (measurable_of_countable f).aestronglyMeasurable
  have h0 : f =ᵐ[Measure.count] 0 := (eLpNorm_eq_zero_iff hq).mp h
  have hnull : Measure.count {m : ℤ | f m ≠ 0} = 0 := MeasureTheory.ae_iff.mp h0
  intro n
  by_contra hn
  have hne : Measure.count {m : ℤ | f m ≠ 0} ≠ 0 := by
    rw [Measure.count_ne_zero_iff]
    exact ⟨n, hn⟩
  exact hne hnull

/-- The `r`-variational norm of the zero sequence vanishes (for `r ≥ 1`), by homogeneity. -/
lemma variationalNorm_zero_of_one_le {r : ℝ≥0} (hr : 1 ≤ r) :
    variationalNorm r (0 : ℕ → ℂ) = 0 := by
  have h := variationalNorm_smul (r := r) hr (0 : ℂ) (0 : ℕ → ℂ)
  simpa using h

/-- The constant of the long variational estimate obtained from the halved estimate: the factor
`6` comes from the geometric weight `∑ 2^{-k}` of the telescoping, the term
`9 · rateConst Λ` from the telescoping error, and the `+ 1` only ensures positivity of the
constant (which is needed to dispose of functions of infinite `eLpNorm`). -/
noncomputable def cvLong (Cv : ℝ≥0 → ℝ≥0) (Λ : ℝ≥0) : ℝ≥0 :=
  6 * Cv Λ + 9 * rateConst Λ * Cv Λ + 1

lemma cvLong_pos (Cv : ℝ≥0 → ℝ≥0) (Λ : ℝ≥0) : 0 < cvLong Cv Λ := by
  unfold cvLong
  exact lt_of_lt_of_le one_pos (le_add_of_nonneg_left (zero_le : (0 : ℝ≥0) ≤ _))

lemma coe_cvCore_le_cvLong (Cv : ℝ≥0 → ℝ≥0) (Λ : ℝ≥0) :
    (((6 * Cv Λ + 9 * rateConst Λ * Cv Λ : ℝ≥0)) : ℝ≥0∞) ≤ (cvLong Cv Λ : ℝ≥0∞) := by
  unfold cvLong
  exact ENNReal.coe_le_coe.mpr (le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ 1))

/-- **The halved variational estimate implies the long variational estimate** (on the integer
shift model): Krause--Mirek--Tao, Proposition 3.1 (iii) (formalised in
`Submission.ReductionR`), together with the bookkeeping required by the `eLpNorm`-formulation of
`VarEstZ` (which, unlike Proposition 3.1 (iii), is stated for arbitrary functions; see the
module documentation). -/
theorem varEstZ_of_varEstHalf {P : ℤ[X]} {p₁ p₂ p : ℝ≥0∞} {r : ℝ≥0} {Cv : ℝ≥0 → ℝ≥0}
    (h1p₁ : 1 < p₁) (h1p₂ : 1 < p₂) (h1p : 1 ≤ p) (hpT : p ≠ ⊤) (hr : 1 ≤ r)
    (hHalf : VarEstHalfR TZ Measure.count P p₁ p₂ p r Cv) :
    VarEstZ P p₁ p₂ p r (cvLong Cv) := by
  intro Λ a hΛ ha ha1 f g
  change eLpNorm (fun j : ℤ => variationalNorm r (fun n => A TZ (a n) X P f g j))
      p Measure.count ≤ _
  have hkm : VarEstR TZ Measure.count P p₁ p₂ p r
      (fun Λ => 6 * Cv Λ + 9 * rateConst Λ * Cv Λ) :=
    varEstR_of_varEstHalfR hr measurePreserving_TZ h1p hpT hHalf
  set Cf : ℝ≥0∞ := (cvLong Cv Λ : ℝ≥0∞) with hCf
  have hCfpos : 0 < Cf := ENNReal.coe_pos.mpr (cvLong_pos Cv Λ)
  by_cases hg0 : eLpNorm g p₂ Measure.count = 0
  · -- `g` vanishes pointwise, hence so do all the averages
    have hgz : g = 0 := funext (eq_zero_of_eLpNorm_count_eq_zero (lt_trans one_pos h1p₂).ne' hg0)
    have hseq : (fun j : ℤ => variationalNorm r (fun n => A TZ (a n) X P f g j)) = fun _ => 0 := by
      funext j
      have hzero : (fun n => A TZ (a n) X P f g j) = 0 := by
        funext n
        rw [hgz]
        exact A_right_zero TZ (a n) X P f j
      rw [hzero, variationalNorm_zero_of_one_le hr]
    rw [hseq, hg0]
    simp
  by_cases hf0 : eLpNorm f p₁ Measure.count = 0
  · -- `f` vanishes pointwise
    have hfz : f = 0 := funext (eq_zero_of_eLpNorm_count_eq_zero (lt_trans one_pos h1p₁).ne' hf0)
    have hseq : (fun j : ℤ => variationalNorm r (fun n => A TZ (a n) X P f g j)) = fun _ => 0 := by
      funext j
      have hzero : (fun n => A TZ (a n) X P f g j) = 0 := by
        funext n
        rw [hfz]
        exact A_left_zero TZ (a n) X P g j
      rw [hzero, variationalNorm_zero_of_one_le hr]
    rw [hseq, hf0]
    simp
  by_cases hft : eLpNorm f p₁ Measure.count = ⊤
  · -- the right-hand side is infinite
    rw [hft, ENNReal.mul_top hCfpos.ne', ENNReal.top_mul hg0]
    exact le_top
  by_cases hgt : eLpNorm g p₂ Measure.count = ⊤
  · rw [hgt, ENNReal.mul_top (mul_ne_zero hCfpos.ne' hf0)]
    exact le_top
  · -- both seminorms are finite: apply the halved estimate
    have hfm : MemLp f p₁ (Measure.count : Measure ℤ) :=
      (MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hft))
    have hgm : MemLp g p₂ (Measure.count : Measure ℤ) :=
      (MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hgt))
    have hR := hkm f g hfm hgm a Λ hΛ ha ha1
    rw [Lp.enorm_toLp hfm, Lp.enorm_toLp hgm] at hR
    refine hR.trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (coe_cvCore_le_cvLong Cv Λ) (zero_le : (0 : ℝ≥0∞) ≤ _))
      (zero_le : (0 : ℝ≥0∞) ≤ _)

/-- **The finite variational estimate for the halved averages.**  For every `K`, the variational
estimate for the halved averages at the first `K + 1` scales `a 0, …, a K` of a `Λ`-lacunary
sequence `a` — encoded by clamping `a` at `K`, so that the variational norm only sees the finite
set of scales `{a 0, …, a K}`.  This is the form of the estimate that the paper proves
(Krause--Mirek--Tao, Theorem "end-var", stated there for *finite* `λ`-lacunary sets of scales),
and it is the statement of the single remaining gap of the development. -/
def VarEstHalfFin (T : 𝓧 ≃ᵐ 𝓧) (μ : Measure 𝓧) (P : ℤ[X]) (p₁ p₂ p : ℝ≥0∞) (r : ℝ≥0)
    (Cv : ℝ≥0 → ℝ≥0) : Prop :=
  ∀ (K : ℕ) (f g : 𝓧 → ℂ) (hf : MemLp f p₁ μ) (hg : MemLp g p₂ μ) (a : ℕ → ℝ≥0) (Λ : ℝ≥0),
    1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) →
    eLpNorm (fun x => variationalNorm r (fun n => AhalfR T (a (min n K)) X P f g x)) p μ
      ≤ (Cv Λ : ℝ≥0∞) * ‖hf.toLp‖ₑ * ‖hg.toLp‖ₑ

/-- The finite variational estimate implies the variational estimate for the whole lacunary
sequence: this is the monotone-convergence step in the proof of Krause--Mirek--Tao,
Proposition 3.1 (i), using that the variational norm of a sequence is the supremum of the
variational norms of its clamped versions (`Submission.VarClamp.variationalNorm_eq_iSup_comp_min`).
Hence the single remaining gap (`exists_varEstHalfFin_Cv` below, the paper's finite-set
formulation) implies the infinite-sequence formulation `VarEstHalfR` used by the rest of the
reduction chain. -/
theorem varEstHalf_of_varEstHalfFin {T : 𝓧 ≃ᵐ 𝓧} {μ : Measure 𝓧} {P : ℤ[X]}
    {p₁ p₂ p : ℝ≥0∞} {r : ℝ≥0} {Cv : ℝ≥0 → ℝ≥0} (hp0 : p ≠ 0) (hpT : p ≠ ⊤)
    (hr0 : 0 < r) (hT : MeasurePreserving T μ μ) (hFin : VarEstHalfFin T μ P p₁ p₂ p r Cv) :
    VarEstHalfR T μ P p₁ p₂ p r Cv := by
  intro f g hf hg a Λ hΛ ha ha1
  have hpt : (fun x => variationalNorm r (fun n => AhalfR T (a n) X P f g x))
      = fun x => ⨆ K, variationalNorm r (fun n => AhalfR T (a (min n K)) X P f g x) := by
    funext x
    exact variationalNorm_eq_iSup_comp_min r (fun n => AhalfR T (a n) X P f g x)
  rw [hpt]
  refine eLpNorm_iSup_le_of_le hp0 hpT (fun K => ?_) (fun x => ?_) (fun K => ?_)
  · exact aemeasurable_variationalNorm hr0 (fun n =>
      aemeasurable_AhalfR hT (a (min n K)) X P hf.aestronglyMeasurable.aemeasurable
        hg.aestronglyMeasurable.aemeasurable)
  · intro K K' hKK'
    exact variationalNorm_comp_min_mono r (fun m => AhalfR T (a m) X P f g x) hKK'
  · exact hFin K f g hf hg a Λ hΛ ha ha1

/- The paper's Theorem "end-var" (`exists_varEstHalfFin_Cv`) and its consequences
(`exists_varEstHalf_Cv`, `exists_varEstZ_Cv`, `CvShift`, `varEstZ_CvShift`) now live in
`Submission.ShiftHoleClosed`, where the hole is closed from the eight KMT areas. -/

end PointwiseErgodicTheorems

end Submission

import Mathlib
import Submission.Work.LinnikAreas.DhRepel.lemma8_5
import Submission.Work.ZeroFreeTables.ksum_positivity_six

open Complex DirichletCharacter Metric Filter Set Topology MeasureTheory MeromorphicOn
open scoped Real Topology BigOperators

namespace Work.ZeroFreeTables

set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

noncomputable section

/-! ## HB Lemma 8.7 — the requested hypothesis block is mis-stated

The statement requested as `Work.ZeroFreeTables.lemma8_7` carries the maximality height
`|γ₂| + 1` for **all five** characters and the height hypothesis `|γ₂| + 1 ≤ 10 log q`.
That block does not say what was meant, and its conclusion cannot be derived from it; the
declaration named `lemma8_7` is therefore **not** present in this module (consumers must not
silently pick up a differently-stated theorem under that name).  The corrected statement is
proved below as `lemma8_7_engine_proof`.

Exactly two hypotheses are missing from the requested block:

* the maximality hypotheses for `χ₂²` and for `χ₁ χ₂²` must be asked at height
  `2 * |γ₂| + 1` instead of `|γ₂| + 1`;
* the height hypothesis must be `2 * |γ₂| + 1 ≤ 10 log q` instead of `|γ₂| + 1 ≤ 10 log q`.

The conclusion, and every other hypothesis, is unchanged.

Why the requested block is insufficient (not merely inconvenient):

* The conclusion is Heath-Brown (8.11) together with the slack
  `f 0 * ((k^2+1/2)(c_1+2 eps) + 2 k (2c+2 eps) + (c+eps))`; with `c_1 = 1/8`, `c = 1/6`
  this is `f 0 * (psi87 k + 2(k+1)^2 eps)`, the engine from which HB's Table 7 is read
  (cf. `HBTable7_defs`).  Its only source is the pointwise positivity
  `0 <= (chi_0(n) + chi_1(n)) (k + Re(chi_2(n) n^{-i ga_2}))^2` (valid since `chi_1^2 = 1`
  forces `chi_1(n) in {0,+-1}`), whose expansion — using `2 (Re w)^2 = 1 + Re(w^2)` for
  `|w| = 1` — is
  `(k^2+1/2)(K(be_2,chi_0)+K(be_2,chi_1)) + 2k(K(be_2+i ga_2,chi_2)+K(be_2+i ga_2,chi_1chi_2))
   + (1/2)(K(be_2+2i ga_2,chi_2^2) + K(be_2+2i ga_2,chi_1chi_2^2)) >= 0`.
  Those weights are forced: dropping the `chi_2^2` terms leaves the summand
  `2k^2 + 1 + 4k Re(w)`, negative at `Re(w) = -1`, `k = 1`.  So the sums of `chi_2^2` and
  `chi_1 chi_2^2` enter at `s = be_2 + 2 i ga_2` with weight `1/2`, and the derived slack is
  *exactly* the requested one: each of `chi_2` and `chi_1 chi_2` contributes `2k(c+eps)` and
  each of `chi_2^2`, `chi_1 chi_2^2` contributes `(c+eps)/2`.  There is no slack to spare.
* Bounding those two sums sharply (by `f 0 (c+eps) log q`) is what HB Lemma 5.2
  (`Commons.NumberTheory.Linnik.Ksum_le_self_of_L52_phi`) does, and it needs every zero of
  the completed `L`-function in the window `||1 + 2 i ga_2 - u|| <= delta` to satisfy
  `u.re <= be_2`.  Window zeros satisfy `|u.im| <= 2 |ga_2| + delta`, and the transfer
  lemma `Work.LinnikAreas.DhRepel.window_le_of_Lzero_T` produces the window statement from
  a maximality hypothesis at height `T` with `|s.im| + delta <= T`, i.e. here
  `2 |ga_2| + delta <= T`.  With `T = |ga_2| + 1` this needs `|ga_2| + delta <= 1`, which
  the requested block does not provide; with `T = 2 |ga_2| + 1` it holds since `delta < 1`.
* The fallback bound `K(s,chi_2^2) <= K(be_2,chi_0) <= log q J_2 + f 0 eps log q` cannot
  replace it: it leaves the remainder `J_2 - c * f 0` (with `J_2 = ∫_0^{x_0} e^{lam_2 t} f`),
  and `J_2 > 0` while `x_0`, `B` and `f` are free, so the requested slack is not reached.
* HB Lemma 5.2 is applicable at `s = be_2 + 2 i ga_2` only when `2 |ga_2| <= 10 log q`,
  which is exactly what the corrected height hypothesis gives (the requested one gives only
  `|ga_2| + 1 <= 10 log q`).

That the corrected block is what was meant is documented by the requester's own scratch
files: `my_scratch_t7/stmt_check2.lean` (separate heights `|ρ₂.im| + 1`, `2|ρ₂.im| + 1`,
`2|ρ₂.im| + 1`, `|ρ₂.im| + 1`, `|ρ₂.im| + 1`) and `my_scratch_t7/stmt_check3.lean`
(`hball` at height `2 * |ρ₂.im| + 1` for every `ψ ≠ 1`, and `hγ₂ : 2 * |ρ₂.im| + 1 ≤ 10 log q`).
The corrected statement is also the statement of the requester's own
`Work.ZeroFreeTables.lemma8_7_engine` (`lemma8_7_engine.lean`, proved) and of
`Work.ZeroFreeTables.lemma8_7_v2` (`lemma8_7_v2.lean`, discharged in one line by
`exact Work.ZeroFreeTables.lemma8_7_engine_proof x₀ B c₁ c hx₀ hB`).

The proof of the corrected statement below is the analogue of the proof of
`Work.LinnikAreas.DhRepel.lemma8_5`, with the six-term positivity `ksum_positivity_six` in
place of `Ksum_positivity` and the four HB-5.2 bound producers; the algebraic core is
factored out as `lemma8_7_assembly`. -/

/-- **Algebraic core of the corrected Lemma 8.7.**  The six bounds on the six `K`-sums
together with the six-term positivity give the `k`-weighted inequality. -/
theorem lemma8_7_assembly {K₀ K₁ K₂ K₁₂ K₂₂ K₁₂₂ L J₂ J₁ J₀ f0 c₁ c ε k : ℝ}
    (hL : 0 < L) (hk : 0 ≤ k)
    (h6 : 0 ≤ (k ^ 2 + 1/2) * (K₁ + K₀) + 2 * k * (K₂ + K₁₂) + (1/2) * (K₂₂ + K₁₂₂))
    (h0 : K₀ ≤ L * J₂ + f0 * ε * L)
    (h1 : K₁ ≤ -(L) * J₁ + f0 * (c₁ + ε) * L)
    (h2 : K₂ ≤ -(L) * J₀ + f0 * (c + ε) * L)
    (h3 : K₁₂ ≤ f0 * (c + ε) * L)
    (h4 : K₂₂ ≤ f0 * (c + ε) * L)
    (h5 : K₁₂₂ ≤ f0 * (c + ε) * L) :
    0 ≤ (k ^ 2 + 1/2) * (J₂ - J₁) - 2 * k * J₀
        + f0 * ((k ^ 2 + 1/2) * (c₁ + 2 * ε) + 2 * k * (2 * c + 2 * ε) + (c + ε)) := by
  have hA : (0:ℝ) ≤ k ^ 2 + 1/2 := by positivity
  have hB : (0:ℝ) ≤ 2 * k := by linarith
  have hC : (0:ℝ) ≤ (1/2:ℝ) := by norm_num
  have e1 : (k ^ 2 + 1/2) * (K₁ + K₀) ≤
      (k ^ 2 + 1/2) * ((-(L) * J₁ + f0 * (c₁ + ε) * L) + (L * J₂ + f0 * ε * L)) :=
    mul_le_mul_of_nonneg_left (by linarith only [h1, h0]) hA
  have e2 : 2 * k * (K₂ + K₁₂) ≤
      2 * k * ((-(L) * J₀ + f0 * (c + ε) * L) + f0 * (c + ε) * L) :=
    mul_le_mul_of_nonneg_left (by linarith only [h2, h3]) hB
  have e3 : (1/2) * (K₂₂ + K₁₂₂) ≤ (1/2) * (f0 * (c + ε) * L + f0 * (c + ε) * L) :=
    mul_le_mul_of_nonneg_left (by linarith only [h4, h5]) hC
  have key : (0:ℝ) ≤ (k ^ 2 + 1/2) * ((-(L) * J₁ + f0 * (c₁ + ε) * L) + (L * J₂ + f0 * ε * L))
      + 2 * k * ((-(L) * J₀ + f0 * (c + ε) * L) + f0 * (c + ε) * L)
      + (1/2) * (f0 * (c + ε) * L + f0 * (c + ε) * L) := by
    linarith only [h6, e1, e2, e3]
  have hr : (k ^ 2 + 1/2) * ((-(L) * J₁ + f0 * (c₁ + ε) * L) + (L * J₂ + f0 * ε * L))
      + 2 * k * ((-(L) * J₀ + f0 * (c + ε) * L) + f0 * (c + ε) * L)
      + (1/2) * (f0 * (c + ε) * L + f0 * (c + ε) * L)
      = L * ((k ^ 2 + 1/2) * (J₂ - J₁) - 2 * k * J₀
          + f0 * ((k ^ 2 + 1/2) * (c₁ + 2 * ε) + 2 * k * (2 * c + 2 * ε) + (c + ε))) := by
    ring
  rw [hr] at key
  exact (mul_nonneg_iff_of_pos_left hL).mp key


theorem lemma8_7_engine_proof (x₀ B c₁ c : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B) :
    ∀ {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) (hf0 : 0 < f 0)
      (hfnn : ∀ t : ℝ, 0 ≤ f t)
      (hF : ∀ z : ℂ, 0 ≤ z.re →
        0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
      {k : ℝ} (hk : 0 ≤ k) {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1),
      ∃ q₀ : ℕ, ∀ {q : ℕ} [NeZero q], q₀ ≤ q →
      ∀ (χ₁ χ₂ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hχ₂χ₁ : χ₂ ≠ χ₁)
        (hχ₁χ₂ : χ₁ * χ₂ ≠ 1) (hχ₂χ₂ : χ₂ * χ₂ ≠ 1) (hχ₁χ₂χ₂ : χ₁ * (χ₂ * χ₂) ≠ 1)
        (hreal : χ₁ * χ₁ = 1)
        [NeZero χ₁.conductor] [NeZero χ₂.conductor]
        [NeZero (χ₁ * χ₂).conductor] [NeZero (χ₂ * χ₂).conductor]
        [NeZero (χ₁ * (χ₂ * χ₂)).conductor]
        {β₁ β₂ γ₂ : ℝ}
        (hβ₁ : |1 - β₁| ≤ δ) (hβ₂ : |1 - β₂| ≤ δ) (hβ₂β₁ : β₂ ≤ β₁)
        (hγ₂ : 2 * |γ₂| + 1 ≤ 10 * Real.log (q : ℝ))
        (hδle : δ ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ))
        (hzero₁ : DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0)
        (hzero₂ : DirichletCharacter.LFunction χ₂ ((β₂ : ℂ) + (γ₂ : ℂ) * Complex.I) = 0)
        (hmaxA : ∀ u : ℂ, DirichletCharacter.LFunction (χ₁ * χ₂).primitiveCharacter u = 0 →
          |u.im| ≤ |γ₂| + 1 → u.re ≤ β₂)
        (hmaxB : ∀ u : ℂ, DirichletCharacter.LFunction (χ₂ * χ₂).primitiveCharacter u = 0 →
          |u.im| ≤ 2 * |γ₂| + 1 → u.re ≤ β₂)
        (hmaxC : ∀ u : ℂ, DirichletCharacter.LFunction (χ₁ * (χ₂ * χ₂)).primitiveCharacter u = 0 →
          |u.im| ≤ 2 * |γ₂| + 1 → u.re ≤ β₂)
        (hmaxD : ∀ u : ℂ, DirichletCharacter.LFunction χ₂.primitiveCharacter u = 0 →
          |u.im| ≤ |γ₂| + 1 → u.re ≤ β₂)
        (hmaxE : ∀ u : ℂ, DirichletCharacter.LFunction χ₁.primitiveCharacter u = 0 →
          |u.im| ≤ |γ₂| + 1 → u = (β₁ : ℂ) ∨ u.re ≤ β₂)
        (hdivB : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₂.primitiveCharacter)
            (Metric.closedBall 0 (|γ₂| + 2))) ((β₂ : ℂ) + (γ₂ : ℂ) * Complex.I) ≠ 0)
        (hdivE : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
            (Metric.closedBall 0 (|γ₂| + 2))) (β₁ : ℂ) ≠ 0)
        (H₁ : Commons.NumberTheory.Linnik.L52Hyp χ₁ c₁ ε δ)
        (H₂ : Commons.NumberTheory.Linnik.L52Hyp χ₂ c ε δ)
        (H₃ : Commons.NumberTheory.Linnik.L52Hyp (χ₁ * χ₂) c ε δ)
        (H₄ : Commons.NumberTheory.Linnik.L52Hyp (χ₂ * χ₂) c ε δ)
        (H₅ : Commons.NumberTheory.Linnik.L52Hyp (χ₁ * (χ₂ * χ₂)) c ε δ),
      0 ≤ (k ^ 2 + 1/2) *
            ((∫ t in (0:ℝ)..x₀, Real.exp ((Real.log (q : ℝ) * (1 - β₂)) * t) * f t)
              - (∫ t in (0:ℝ)..x₀,
                  Real.exp (-((Real.log (q : ℝ) * (1 - β₁)) - (Real.log (q : ℝ) * (1 - β₂))) * t) * f t))
          - 2 * k * (∫ t in (0:ℝ)..x₀, f t)
          + f 0 * ((k ^ 2 + 1/2) * (c₁ + 2 * ε) + 2 * k * (2 * c + 2 * ε) + (c + ε)) := by
  intro f hcont hsupp hf2 hBnd hf0 hfnn hF k hk ε hε δ hδ0 hδ1
  obtain ⟨q₀p, hq₀p⟩ := (Commons.NumberTheory.Linnik.Ksum_principal_le x₀ B hx₀ hB)
    hcont hsupp hf2 hBnd hε hf0
  obtain ⟨q₀a, hq₀a⟩ := (Commons.NumberTheory.Linnik.Ksum_le_self_of_L52_phi x₀ B c hx₀ hB)
    hcont hsupp hf2 hBnd hf0 hF hε hδ0 hδ1
  obtain ⟨q₀b, hq₀b⟩ := (Commons.NumberTheory.Linnik.Ksum_le_single_of_L52_phi x₀ B c hx₀ hB)
    hcont hsupp hf2 hBnd hf0 hF hε hδ0 hδ1
  obtain ⟨q₀n, hq₀n⟩ := (Work.LinnikAreas.DhRepel.Ksum_le_single_ne_of_L52_phi x₀ B c₁ hx₀ hB)
    hcont hsupp hf2 hBnd hf0 hF hε hδ0 hδ1
  refine ⟨max (max (max (max q₀p q₀a) q₀b) q₀n) 8 + 6, ?_⟩
  intro q _inst hq χ₁ χ₂ hχ₁ hχ₂ hχ₂χ₁ hχ₁χ₂ hχ₂χ₂ hχ₁χ₂χ₂ hreal
    _ic₁ _ic₂ _ic₃ _ic₄ _ic₅ β₁ β₂ γ₂ hβ₁ hβ₂ hβ₂β₁ hγ₂ hδle hzero₁ hzero₂
    hmaxA hmaxB hmaxC hmaxD hmaxE hdivB hdivE H₁ H₂ H₃ H₄ H₅
  have hq6 : 6 ≤ q := by omega
  have hq8 : 8 ≤ q := by omega
  have hq_ge_p : q₀p ≤ q := by omega
  have hq_ge_a : q₀a ≤ q := by omega
  have hq_ge_b : q₀b ≤ q := by omega
  have hq_ge_n : q₀n ≤ q := by omega
  have hL2 : (2:ℝ) ≤ Real.log (q:ℝ) := by
    have h1 : Real.log 8 ≤ Real.log (q:ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hq8)
    have h3 : Real.log (8:ℝ) = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
    rw [h3] at h1
    have h4 : (2:ℝ) < 3 * Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    linarith
  have hLpos : 0 < Real.log (q:ℝ) := by linarith
  -- primitive characters are non-principal
  have hneA : (χ₁ * χ₂).primitiveCharacter ≠ 1 := by
    intro h
    apply hχ₁χ₂
    rw [← DirichletCharacter.changeLevel_primitiveCharacter (χ₁ * χ₂), h]
    exact DirichletCharacter.changeLevel_one (χ₁ * χ₂).conductor_dvd_level
  have hneB : (χ₂ * χ₂).primitiveCharacter ≠ 1 := by
    intro h
    apply hχ₂χ₂
    rw [← DirichletCharacter.changeLevel_primitiveCharacter (χ₂ * χ₂), h]
    exact DirichletCharacter.changeLevel_one (χ₂ * χ₂).conductor_dvd_level
  have hneC : (χ₁ * (χ₂ * χ₂)).primitiveCharacter ≠ 1 := by
    intro h
    apply hχ₁χ₂χ₂
    rw [← DirichletCharacter.changeLevel_primitiveCharacter (χ₁ * (χ₂ * χ₂)), h]
    exact DirichletCharacter.changeLevel_one (χ₁ * (χ₂ * χ₂)).conductor_dvd_level
  have hneD : χ₁.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ₁
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ₁, h]
    exact DirichletCharacter.changeLevel_one χ₁.conductor_dvd_level
  have hneE : χ₂.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ₂
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ₂, h]
    exact DirichletCharacter.changeLevel_one χ₂.conductor_dvd_level
  have habsβ₂ : |β₂ - 1| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) := by
    have h : |β₂ - 1| ≤ δ := by rw [abs_sub_comm]; exact hβ₂
    exact le_trans h hδle
  have hβ₂_ge : 1 - Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) ≤ β₂ := by
    have h : 1 - β₂ ≤ δ := (abs_le.mp hβ₂).2
    linarith only [h, hδle]
  -- window thresholds
  have hT_C : |((β₂:ℂ) : ℂ).im| + δ ≤ |γ₂| + 1 := by
    have h : ((β₂:ℂ) : ℂ).im = 0 := by simp
    rw [h, abs_zero]; linarith [abs_nonneg γ₂, hδ1]
  have hT_D : |(((β₂:ℂ) + (γ₂:ℂ)*Complex.I) : ℂ).im| + δ ≤ |γ₂| + 1 := by
    have h : (((β₂:ℂ) + (γ₂:ℂ)*Complex.I) : ℂ).im = γ₂ := by simp
    rw [h]; linarith [abs_nonneg γ₂, hδ1]
  have hγ₂' : |γ₂ + γ₂| = 2 * |γ₂| := by
    rw [show γ₂ + γ₂ = 2 * γ₂ by ring, abs_mul,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have hT_B : |(((β₂:ℂ) + ((γ₂:ℂ)+(γ₂:ℂ))*Complex.I) : ℂ).im| + δ ≤ 2 * |γ₂| + 1 := by
    have h : (((β₂:ℂ) + ((γ₂:ℂ)+(γ₂:ℂ))*Complex.I) : ℂ).im = γ₂ + γ₂ := by simp
    rw [h, hγ₂']; linarith [hδ1]
  -- window transfers
  have hzwE : ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|((β₂:ℂ) : ℂ).im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + (((β₂:ℂ) : ℂ).im : ℂ) * Complex.I - u‖ ≤ δ → u ≠ (β₁:ℂ) → u.re ≤ ((β₂:ℂ) : ℂ).re :=
    Work.LinnikAreas.DhRepel.window_hzero_of_Lzero_T χ₁.primitiveCharacter hneD hδ1 hT_C (by simp) hmaxE
  have hzwD : ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₂.primitiveCharacter)
        (Metric.closedBall 0 (|(((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + ((((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ (((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).re :=
    Work.LinnikAreas.DhRepel.window_le_of_Lzero_T χ₂.primitiveCharacter hneE hδ1 hT_D (by simp) hmaxD
  have hzwA : ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction (χ₁*χ₂).primitiveCharacter)
        (Metric.closedBall 0 (|(((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + ((((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ (((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).re :=
    Work.LinnikAreas.DhRepel.window_le_of_Lzero_T (χ₁*χ₂).primitiveCharacter hneA hδ1 hT_D (by simp) hmaxA
  have hzwB : ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction (χ₂*χ₂).primitiveCharacter)
        (Metric.closedBall 0 (|(((β₂:ℂ)+((γ₂:ℂ)+(γ₂:ℂ))*Complex.I):ℂ).im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + ((((β₂:ℂ)+((γ₂:ℂ)+(γ₂:ℂ))*Complex.I):ℂ).im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ (((β₂:ℂ)+((γ₂:ℂ)+(γ₂:ℂ))*Complex.I):ℂ).re :=
    Work.LinnikAreas.DhRepel.window_le_of_Lzero_T (χ₂*χ₂).primitiveCharacter hneB hδ1 hT_B (by simp) hmaxB
  have hzwC : ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction (χ₁*(χ₂*χ₂)).primitiveCharacter)
        (Metric.closedBall 0 (|(((β₂:ℂ)+((γ₂:ℂ)+(γ₂:ℂ))*Complex.I):ℂ).im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + ((((β₂:ℂ)+((γ₂:ℂ)+(γ₂:ℂ))*Complex.I):ℂ).im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ (((β₂:ℂ)+((γ₂:ℂ)+(γ₂:ℂ))*Complex.I):ℂ).re :=
    Work.LinnikAreas.DhRepel.window_le_of_Lzero_T (χ₁*(χ₂*χ₂)).primitiveCharacter hneC hδ1 hT_B (by simp) hmaxC
  -- divisor transfers
  have hβ₁_mem : (β₁:ℂ) ∈ Metric.closedBall 0 2 := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Complex.norm_real, Real.norm_eq_abs]
    have h1 : -(δ) ≤ 1 - β₁ := (abs_le.mp hβ₁).1
    have h2 : 1 - β₁ ≤ δ := (abs_le.mp hβ₁).2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hdivE2 : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|((β₂:ℂ) : ℂ).im| + 2))) (β₁:ℂ) ≠ 0 := by
    have h : ((β₂:ℂ) : ℂ).im = 0 := by simp
    rw [h, abs_zero, zero_add]
    rw [← Work.LinnikAreas.DhRepel.divisor_closedBall_congr (R := 2) (R' := |γ₂| + 2)
      (by linarith [abs_nonneg γ₂])
      (fun z _ => (DirichletCharacter.differentiable_completedLFunction hneD).analyticAt z) hβ₁_mem]
    exact hdivE
  have hdivD' : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₂.primitiveCharacter)
        (Metric.closedBall 0 (|(((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im| + 2))) ((β₂:ℂ)+(γ₂:ℂ)*Complex.I) ≠ 0 := by
    have h : (((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im = γ₂ := by simp
    rw [h]; exact hdivB
  -- non-negativity of the Laplace integral at the exceptional zero of χ₁
  have hρnn : 0 ≤ (∫ t in (0:ℝ)..x₀,
      Complex.exp (-((((β₂:ℂ) - (β₁:ℂ)) * (Real.log (q:ℝ))) * (t:ℂ))) * ((f t:ℝ):ℂ)).re := by
    have hcast : ((β₂:ℂ) - (β₁:ℂ)) * (Real.log (q:ℝ)) = (((β₂ - β₁) * Real.log (q:ℝ) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast]
    exact Work.LinnikAreas.DhRepel.laplaceIntegral_re_nonneg hx₀.le hfnn
  have hwin1 : ‖(1:ℂ) + (((β₂:ℂ):ℂ).im : ℂ) * Complex.I - (β₁:ℂ)‖ ≤ δ := by
    have h1 : (((β₂:ℂ):ℂ).im : ℂ) = 0 := by simp
    rw [h1, zero_mul, add_zero]
    have h2 : ‖(1:ℂ) - (β₁:ℂ)‖ = |1 - β₁| := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [h2]; exact hβ₁
  have hwin2 : ‖(1:ℂ) + ((((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im : ℂ) * Complex.I - ((β₂:ℂ)+(γ₂:ℂ)*Complex.I)‖ ≤ δ := by
    have h1 : ((((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im : ℂ) = (γ₂:ℂ) := by
      have h : (((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im = γ₂ := by simp
      rw [h]
    rw [h1]
    have h2 : ‖(1:ℂ) + (γ₂:ℂ)*Complex.I - ((β₂:ℂ)+(γ₂:ℂ)*Complex.I)‖ = |1 - β₂| := by
      rw [show (1:ℂ) + (γ₂:ℂ)*Complex.I - ((β₂:ℂ)+(γ₂:ℂ)*Complex.I) = ((1 - β₂ : ℝ):ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
    rw [h2]; exact hβ₂
  -- the s-conditions
  have hsim_1 : |((β₂:ℂ):ℂ).im| ≤ 10 * Real.log (q:ℝ) := by
    have h : ((β₂:ℂ):ℂ).im = 0 := by simp
    rw [h, abs_zero]; linarith [hLpos]
  have hsim_2 : |(((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im| ≤ 10 * Real.log (q:ℝ) := by
    have h : (((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im = γ₂ := by simp
    rw [h]
    have h2 : |γ₂| ≤ 2 * |γ₂| + 1 := by linarith [abs_nonneg γ₂]
    linarith [hγ₂, h2]
  have hsim_B : |(((β₂:ℂ)+((γ₂:ℂ)+(γ₂:ℂ))*Complex.I):ℂ).im| ≤ 10 * Real.log (q:ℝ) := by
    have h : (((β₂:ℂ)+((γ₂:ℂ)+(γ₂:ℂ))*Complex.I):ℂ).im = γ₂ + γ₂ := by simp
    rw [h, hγ₂']; linarith [hγ₂]
  have hsre_1 : |((β₂:ℂ):ℂ).re - 1| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) := by
    have h : ((β₂:ℂ):ℂ).re = β₂ := by simp
    rw [h]; exact habsβ₂
  have hsre_2 : |(((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).re - 1| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) := by
    have h : (((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).re = β₂ := by simp
    rw [h]; exact habsβ₂
  have hsre_B : |(((β₂:ℂ)+((γ₂:ℂ)+(γ₂:ℂ))*Complex.I):ℂ).re - 1| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) := by
    have h : (((β₂:ℂ)+((γ₂:ℂ)+(γ₂:ℂ))*Complex.I):ℂ).re = β₂ := by simp
    rw [h]; exact habsβ₂
  have hge_1 : 1 - Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) ≤ ((β₂:ℂ):ℂ).re := by
    have h : ((β₂:ℂ):ℂ).re = β₂ := by simp
    rw [h]; exact hβ₂_ge
  have hge_2 : 1 - Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) ≤ (((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).re := by
    have h : (((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).re = β₂ := by simp
    rw [h]; exact hβ₂_ge
  have hge_B : 1 - Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) ≤ (((β₂:ℂ)+((γ₂:ℂ)+(γ₂:ℂ))*Complex.I):ℂ).re := by
    have h : (((β₂:ℂ)+((γ₂:ℂ)+(γ₂:ℂ))*Complex.I):ℂ).re = β₂ := by simp
    rw [h]; exact hβ₂_ge
  -- the six bounds
  have hb0 := hq₀p (q := q) hq_ge_p (β := β₂) (lam := Real.log (q:ℝ) * (1 - β₂)) rfl habsβ₂
  have hb1 := hq₀n (q := q) hq_ge_n χ₁ hχ₁ hsre_1 hsim_1 hge_1 H₁ hdivE2 hwin1 hρnn hzwE
  have hb2 := hq₀b (q := q) hq_ge_b χ₂ hχ₂ hsre_2 hsim_2 hge_2 H₂ hdivD' hwin2 hzwD
  have hb3 := hq₀a (q := q) hq_ge_a (χ₁ * χ₂) hχ₁χ₂ hsre_2 hsim_2 hge_2 H₃ hzwA
  have hb4 := hq₀a (q := q) hq_ge_a (χ₂ * χ₂) hχ₂χ₂ hsre_B hsim_B hge_B H₄ hzwB
  have hb5 := hq₀a (q := q) hq_ge_a (χ₁ * (χ₂ * χ₂)) hχ₁χ₂χ₂ hsre_B hsim_B hge_B H₅ hzwC
  -- the six-term positivity
  have h6 := Work.ZeroFreeTables.ksum_positivity_six (q := q) (β := β₂) (γ := γ₂)
    hfnn hx₀ hLpos hsupp χ₁ χ₂ hreal hk
  -- integral rewrites
  have hRe1 : (∫ t in (0:ℝ)..x₀,
      Complex.exp (-((((β₂:ℂ) - (β₁:ℂ)) * (Real.log (q:ℝ))) * (t:ℂ))) * ((f t:ℝ):ℂ)).re
      = ∫ t in (0:ℝ)..x₀,
          Real.exp (-((Real.log (q:ℝ) * (1 - β₁)) - (Real.log (q:ℝ) * (1 - β₂))) * t) * f t := by
    have hz1 : (((β₂:ℂ) - (β₁:ℂ)) * (Real.log (q:ℝ))).im = 0 := by
      rw [← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.ofReal_im]
    rw [Work.LinnikAreas.DhRepel.re_integral_exp_ofReal (z := ((β₂:ℂ) - (β₁:ℂ)) * (Real.log (q:ℝ))) hz1 f]
    apply intervalIntegral.integral_congr
    intro t _
    simp only
    have h : (((β₂:ℂ) - (β₁:ℂ)) * (Real.log (q:ℝ))).re = (β₂ - β₁) * Real.log (q:ℝ) := by
      rw [← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.ofReal_re]
    have harg : -((((β₂:ℂ) - (β₁:ℂ)) * (Real.log (q:ℝ))).re * t)
        = -((Real.log (q:ℝ) * (1 - β₁)) - (Real.log (q:ℝ) * (1 - β₂))) * t := by
      rw [h]; ring
    rw [harg]
  have hRe2 : (∫ t in (0:ℝ)..x₀,
      Complex.exp (-(((((β₂:ℂ)+(γ₂:ℂ)*Complex.I) - ((β₂:ℂ)+(γ₂:ℂ)*Complex.I)) * (Real.log (q:ℝ))) * (t:ℂ))) * ((f t:ℝ):ℂ)).re
      = ∫ t in (0:ℝ)..x₀, f t := by
    have hzero : ((β₂:ℂ)+(γ₂:ℂ)*Complex.I) - ((β₂:ℂ)+(γ₂:ℂ)*Complex.I) = 0 := sub_self _
    simp only [hzero, zero_mul, neg_zero, Complex.exp_zero, one_mul]
    rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]
  -- final assembly
  rw [hRe1] at hb1
  rw [hRe2] at hb2
  exact lemma8_7_assembly (L := Real.log (q:ℝ)) (f0 := f 0)
    hLpos hk h6 hb0 hb1 hb2 hb3 hb4 hb5


/- NB.  There is deliberately no `Work.ZeroFreeTables.lemma8_7` in this module: the
requested hypothesis block (maximality at `|γ₂| + 1` for `χ₂²` and `χ₁(χ₂²)`, and
`|γ₂| + 1 ≤ 10 log q`) is mis-stated and its conclusion is not derivable from it — see the
file header.  `lemma8_7_engine_proof` above is the corrected (and intended) statement, and is
what `Work.ZeroFreeTables.lemma8_7_engine` / `Work.ZeroFreeTables.lemma8_7_v2` ask for. -/


end

end Work.ZeroFreeTables

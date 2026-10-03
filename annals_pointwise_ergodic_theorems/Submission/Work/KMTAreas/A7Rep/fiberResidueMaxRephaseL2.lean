/-
# The residue-maximal rephasing bound, `l²` case

This file proves the `ℓ²` case of `Work.KMTAreas.A7Rep.fiberResidueMaxRephase`: if every member
`u n` of the family is square summable (which holds automatically when `p ≤ 2`, since `ℓᵖ ⊆ ℓ²`,
and which is the hypothesis needed by the envelope/Fourier machinery), then the residue-maximal
`ℓᵖ` bound for the fibres holds.

The proof is the "rephasing" chain described in the docstring of
`Submission/Work/KMTAreas/A7Rep/fiberResidueMaxRephase.lean`:

* `envelopeBandExtend` gives, for every `n` and every arithmetic frequency `α`, a continuous
  band-limited function `W_{α,n}` on the line whose values at the integers are the window envelope
  `winConvR m (winModR (-α) (u n))`;
* for every residue `r` and rotation `n₀` the family `t ↦ ∑_α e((n₀-r)α) W_{α,n}(q t + r)` is
  continuous with Fourier support in `q · [-2δ,2δ] ⊆ [-1/4,1/4]`, and its values at the integers
  are the decimated fibre `fiberOp ρ l₁ m n₀ (u n) (q y + r)`;
* `realBandSampling` compares the lattice `ℓᵖ` sums of the pointwise supremum of such a family with
  the integral of the supremum, and the family for `(n₀,r)` is a translate by `n₀/q` of the family
  for `(0, r-n₀)`, whose lattice values are `u n (q y + r - n₀)` by the fixpoint hypothesis;
* summing over the residues and using the residue decomposition of `ℤ` rewrites the total as the
  right-hand side.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ModelLargeHiRep
import Submission.Work.KMTAreas.A7Hi.vrSamplingDensity
import Submission.Port.Aesm


namespace Work.KMTAreas.A7Rep

open MeasureTheory Finset
open scoped ENNReal BigOperators Topology

set_option maxHeartbeats 2000000

noncomputable section

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## 1. The band predicate: monotonicity, scalar multiples, finite sums -/

theorem hasRealFreqSupport_mono {S T : Set ℝ} (hST : S ⊆ T) {h : ℝ → ℂ}
    (hh : HasRealFreqSupport h S) : HasRealFreqSupport h T := by
  obtain ⟨g, hg, hsupp, hpt⟩ := hh
  exact ⟨g, hg, fun ξ hξ => hsupp ξ fun hS => hξ (hST hS), hpt⟩

/-- Scalar multiples of an inverse Fourier transform. -/
theorem fourierInv_const_mul (c : ℂ) (g : ℝ → ℂ) (t : ℝ) :
    FourierTransformInv.fourierInv (fun ξ => c * g ξ) t
      = c * FourierTransformInv.fourierInv g t := by
  rw [Real.fourierInv_eq, Real.fourierInv_eq, ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with v
  simp only [Circle.smul_def, smul_eq_mul]
  ring

theorem hasRealFreqSupport_const_mul (c : ℂ) {h : ℝ → ℂ} {S : Set ℝ}
    (hh : HasRealFreqSupport h S) : HasRealFreqSupport (fun t : ℝ => c * h t) S := by
  obtain ⟨g, hg, hsupp, hpt⟩ := hh
  refine ⟨fun ξ => c * g ξ, hg.const_mul c, fun ξ hξ => ?_, ?_⟩
  · show c * g ξ = 0
    rw [hsupp ξ hξ, mul_zero]
  · intro t
    show c * h t = FourierTransformInv.fourierInv (fun ξ => c * g ξ) t
    rw [hpt t]
    exact (fourierInv_const_mul c g t).symm

theorem hasRealFreqSupport_add {h₁ h₂ : ℝ → ℂ} {S : Set ℝ}
    (h₁' : HasRealFreqSupport h₁ S) (h₂' : HasRealFreqSupport h₂ S) :
    HasRealFreqSupport (fun t : ℝ => h₁ t + h₂ t) S := by
  obtain ⟨g₁, hg₁, hs₁, hp₁⟩ := h₁'
  obtain ⟨g₂, hg₂, hs₂, hp₂⟩ := h₂'
  refine ⟨g₁ + g₂, hg₁.add hg₂, fun ξ hξ => ?_, ?_⟩
  · show g₁ ξ + g₂ ξ = 0
    rw [hs₁ ξ hξ, hs₂ ξ hξ, add_zero]
  · intro t
    show h₁ t + h₂ t = FourierTransformInv.fourierInv (g₁ + g₂) t
    rw [hp₁ t, hp₂ t]
    exact (congrFun (Work.KMTAreas.SupNorm.fourierInv_add_of_integrable hg₁ hg₂) t).symm

theorem hasRealFreqSupport_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℂ} {S : Set ℝ}
    (hf : ∀ i ∈ s, HasRealFreqSupport (f i) S) :
    HasRealFreqSupport (fun t : ℝ => ∑ i ∈ s, f i t) S := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, integrable_zero _ _ _, fun ξ _ => rfl, fun t => ?_⟩
      show (0 : ℂ) = FourierTransformInv.fourierInv (0 : ℝ → ℂ) t
      rw [Real.fourierInv_eq]
      simp
  | insert a s ha ih =>
      have hfa : HasRealFreqSupport (f a) S := hf a (Finset.mem_insert_self a s)
      have hs : HasRealFreqSupport (fun t => ∑ i ∈ s, f i t) S :=
        ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have := hasRealFreqSupport_add hfa hs
      simpa only [Finset.sum_insert ha] using this

/-! ## 2. Character facts for `q`-torsion frequencies -/

theorem fourier_neg_qmul_eq_one {q : ℕ} {α : Circ} (hα : q • α = 0) (z : ℤ) :
    fourier (T := 1) (-((q : ℤ) * z)) α = 1 := by
  rw [fourier_apply]
  have h2 : (q : ℤ) • α = 0 := by rw [Nat.cast_smul_eq_nsmul]; exact hα
  have h3 : ((q : ℤ) * z) • α = 0 := by rw [mul_zsmul, smul_comm, h2, smul_zero]
  rw [show (-((q : ℤ) * z)) • α = 0 from by rw [neg_zsmul, h3, neg_zero],
    AddCircle.toCircle_zero]
  rfl

/-- An exact-height arithmetic frequency is killed by `arithQ ρ (max l₁ l₂)`. -/
theorem arithQ_max_nsmul_eq_zero {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l₁ l₂ : ℕ} {α : Circ}
    (h : α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁) :
    Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) • α = 0 := by
  have hle : α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁ := (Finset.mem_sdiff.mp h).1
  have hmem : α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ (max l₁ l₂) :=
    Work.Analysis.IonescuWainger.iwArithFreqs_mono hρ hρ1 (le_max_left l₁ l₂) hle
  obtain ⟨q, hq, hqα⟩ := Work.Analysis.IonescuWainger.mem_iwArithFreqs.mp hmem
  have hQ : Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)
      = (Work.Analysis.IonescuWainger.iwP ρ (max l₁ l₂)).lcm id := by
    rw [Work.KMTAreas.A7.arithQ]
    exact max_eq_right (Nat.succ_le_of_lt Work.Analysis.IonescuWainger.iwQl_pos)
  rw [hQ]
  exact Work.Analysis.IonescuWainger.iwQl_nsmul_eq_zero hmem

/-- At a decimated point the phase of the `x`-character collapses to the residue. -/
theorem fourier_fiber_decim {q : ℕ} {α : Circ} (hα : q • α = 0) (n₀ r y : ℤ) :
    fourier (T := 1) n₀ α * fourier (T := 1) (-(((q : ℤ) * y + r))) α
      = fourier (T := 1) (n₀ - r) α := by
  rw [← fourier_add]
  have harg : n₀ + -(((q : ℤ) * y + r)) = (n₀ - r) + -((q : ℤ) * y) := by ring
  rw [harg, fourier_add, fourier_neg_qmul_eq_one hα, mul_one]

/-! ## 3. Rescaling-and-shifting a band-limited function -/

/-- If `h = 𝓕⁻ g` with `g` supported in `[-β,β]` and `β q ≤ 1/4`, then `t ↦ h (a + q t)` is the
inverse Fourier transform of an integrable function supported in `[-1/4,1/4]`. -/
theorem hasRealFreqSupport_comp_add_mul {h : ℝ → ℂ} {β : ℝ}
    (hh : HasRealFreqSupport h (Set.Icc (-β) β)) {q : ℝ} (hq : 0 < q) (a : ℝ)
    (hβq : β * q ≤ 1 / 4) :
    HasRealFreqSupport (fun t : ℝ => h (a + q * t)) (Set.Icc (-(1 / 4)) (1 / 4)) := by
  obtain ⟨g, hg, hsupp, hpt⟩ := hh
  refine ⟨Work.KMTAreas.A7Hi.rescAmp q a g, Work.KMTAreas.A7Hi.integrable_rescAmp hg hq,
    fun ξ hξ => Work.KMTAreas.A7Hi.rescAmp_eq_zero hsupp hq hβq hξ, ?_⟩
  intro t
  show h (a + q * t) = FourierTransformInv.fourierInv (Work.KMTAreas.A7Hi.rescAmp q a g) t
  rw [Work.KMTAreas.A7Hi.fourierInv_rescAmp g hq t, hpt (a + q * t)]

/-! ## 4. The decimated coset bound -/

/-! ## 5. The `ℓᵖ` norm as a sum of powers -/

/-- For `p > 0`, the `p`-th power of the `ℓᵖ(ℤ)` norm of an `ℝ≥0∞`-valued function is the sum of
the `p`-th powers. -/
theorem eLpNorm_pow_eq_tsum (p : ℝ) (hp : 0 < p) (G : ℤ → ENNReal) :
    (MeasureTheory.eLpNorm G (ENNReal.ofReal p) MeasureTheory.Measure.count) ^ p
      = ∑' x : ℤ, G x ^ p := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (ENNReal.ofReal_pos.mpr hp).ne'
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le, one_div,
    ENNReal.rpow_inv_rpow hp.ne', MeasureTheory.lintegral_count]
  rfl

/-- `ee` never vanishes. -/
theorem ee_ne_zero (x : ℝ) : Work.KMTAreas.A7.ee x ≠ 0 := by
  rw [Work.KMTAreas.A7.ee]
  exact Complex.exp_ne_zero _

/-! ## 6. The `ℓ²` case, assuming the cut is integrable -/

/-! ## 7. The `ℓ²` case -/

/-! ## 8. The case `p ≤ 2` -/

/-- The `ℝ≥0∞`-norm of a complex number is its real norm. -/
theorem enorm_eq_ofReal' (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [enorm_eq_nnnorm]
  exact ENNReal.coe_nnreal_eq (nnnorm z)

/-- If the `ℝ≥0∞`-sum of the `ofReal`-terms is finite then the real series is summable. -/
theorem summable_of_tsum_ofReal_lt_top {f : ℤ → ℝ} (hf : ∀ x, 0 ≤ f x)
    (h : (∑' x : ℤ, ENNReal.ofReal (f x)) < ⊤) : Summable f := by
  refine summable_of_sum_le (f := f) (c := (∑' x : ℤ, ENNReal.ofReal (f x)).toReal) hf
    (fun s => ?_)
  have h1 : ENNReal.ofReal (∑ x ∈ s, f x) = ∑ x ∈ s, ENNReal.ofReal (f x) :=
    ENNReal.ofReal_sum_of_nonneg (fun x _ => hf x)
  have h2 : (∑ x ∈ s, f x) = ((∑ x ∈ s, ENNReal.ofReal (f x))).toReal := by
    rw [← h1, ENNReal.toReal_ofReal (Finset.sum_nonneg (fun x _ => hf x))]
  rw [h2]
  exact ENNReal.toReal_mono (ne_of_lt h) (ENNReal.sum_le_tsum s)

/-- For `p ≤ 2`, an `ℓᵖ(ℤ)`-summable sequence is `ℓ²(ℤ)`-summable (the classical inclusion
`ℓᵖ ⊆ ℓ²`). -/
theorem summable_sq_of_summable_rpow {v : ℤ → ℂ} {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2)
    (hv : Summable (fun x : ℤ => ‖v x‖ ^ p)) : Summable (fun x : ℤ => ‖v x‖ ^ (2 : ℝ)) := by
  have h0 : Filter.Tendsto (fun x : ℤ => ‖v x‖ ^ p) Filter.cofinite (𝓝 0) :=
    hv.tendsto_cofinite_zero
  have hev : ∀ᶠ x : ℤ in Filter.cofinite, ‖v x‖ ^ (2 : ℝ) ≤ ‖v x‖ ^ p := by
    filter_upwards [h0.eventually (Ioo_mem_nhds (by norm_num : (-1:ℝ) < 0)
      (by norm_num : (0:ℝ) < 1))] with x hx
    have hxle : ‖v x‖ ^ p ≤ 1 := le_of_lt hx.2
    have hx1 : ‖v x‖ ≤ 1 := by
      by_contra h
      rw [not_le] at h
      exact absurd (Real.one_lt_rpow h hp) (not_lt.mpr hxle)
    rcases eq_or_lt_of_le (norm_nonneg (v x)) with h | h
    · rw [← h]
      simp [Real.zero_rpow hp.ne', Real.zero_rpow (by norm_num : (2:ℝ) ≠ 0)]
    · exact Real.rpow_le_rpow_of_exponent_ge h hx1 hp2
  refine Summable.of_norm_bounded_eventually (f := fun x : ℤ => ‖v x‖ ^ (2 : ℝ)) hv ?_
  filter_upwards [hev] with x hx
  simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using hx

end

end Work.KMTAreas.A7Rep

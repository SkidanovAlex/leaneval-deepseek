import Mathlib
import Submission.Commons.Analysis.Fourier.nested_scales_maximal_l2_real

namespace Commons.Analysis.Fourier

open MeasureTheory Filter
open scoped ENNReal FourierTransform ComplexInnerProductSpace Topology BigOperators

noncomputable section

set_option maxHeartbeats 4000000

/-! ## Auxiliary lemmas -/

/-- **Conjugation and the Fourier transform.**  For an integrable `g : ℝ → ℂ`, the Fourier
transform of the pointwise conjugate of `g` is the conjugate of the Fourier transform of `g`
evaluated at the reflected point: `𝓕 (star ∘ g) y = star (𝓕 g (-y))`. -/
lemma fourier_star_neg_real (g : ℝ → ℂ) (y : ℝ) :
    𝓕 (fun x => star (g x)) y = star ((𝓕 g) (-y)) := by
  rw [Real.fourier_eq', Real.fourier_eq']
  have hpt : ∀ v : ℝ,
      Complex.exp ((↑(-2 * Real.pi * inner ℝ v y) : ℂ) * Complex.I) • star (g v)
        = star (Complex.exp ((↑(-2 * Real.pi * inner ℝ v (-y)) : ℂ) * Complex.I) • g v) := by
    intro v
    rw [smul_eq_mul, smul_eq_mul, Complex.star_def, map_mul]
    congr 1
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I, Real.inner_apply, Real.inner_apply]
    push_cast
    ring
  rw [show (∫ v : ℝ,
        Complex.exp ((↑(-2 * Real.pi * inner ℝ v y) : ℂ) * Complex.I) • star (g v))
      = ∫ v : ℝ,
          star (Complex.exp ((↑(-2 * Real.pi * inner ℝ v (-y)) : ℂ) * Complex.I) • g v) from
        integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [Complex.star_def]
  exact integral_conj

/-- **Self-adjointness of the band-pass operator.**  For `u, g ∈ L¹ ∩ L²(ℝ)` and `C` measurable
and bounded,
`∫ x, bandOp C u x * conj (g x) = ∫ x, u x * conj (bandOp C g x)`. -/
lemma bandOp_integral_pairing (C : Set ℝ) (hC : MeasurableSet C) (hbd : Bornology.IsBounded C)
    (u g : ℝ → ℂ) (hu1 : MemLp u 1 (volume : Measure ℝ)) (hu2 : MemLp u 2 (volume : Measure ℝ))
    (hg1 : MemLp g 1 (volume : Measure ℝ)) (hg2 : MemLp g 2 (volume : Measure ℝ)) :
    ∫ x, bandOp C u x * star (g x) = ∫ x, u x * star (bandOp C g x) := by
  have hu_int : Integrable u := memLp_one_iff_integrable.mp hu1
  have hg_int : Integrable g := memLp_one_iff_integrable.mp hg1
  have hHu1 : MemLp (Set.indicator C (𝓕 u)) 1 (volume : Measure ℝ) :=
    memLp_one_indicator_fourier C hC hbd u hu_int
  have hHu2 : MemLp (Set.indicator C (𝓕 u)) 2 (volume : Measure ℝ) :=
    memLp_two_indicator_fourier C hC hbd u hu_int
  have hHg1 : MemLp (Set.indicator C (𝓕 g)) 1 (volume : Measure ℝ) :=
    memLp_one_indicator_fourier C hC hbd g hg_int
  have hHg2 : MemLp (Set.indicator C (𝓕 g)) 2 (volume : Measure ℝ) :=
    memLp_two_indicator_fourier C hC hbd g hg_int
  have hsgu1 : MemLp (fun x => star (g x)) 1 (volume : Measure ℝ) := hg1.star
  have hsgu2 : MemLp (fun x => star (g x)) 2 (volume : Measure ℝ) := hg2.star
  have hsu1 : MemLp (fun x => star (u x)) 1 (volume : Measure ℝ) := hu1.star
  have hsu2 : MemLp (fun x => star (u x)) 2 (volume : Measure ℝ) := hu2.star
  have hL : ∫ x, bandOp C u x * star (g x)
      = ∫ ξ, Set.indicator C (𝓕 u) ξ * star ((𝓕 g) ξ) := by
    have h1 : ∫ x, bandOp C u x * star (g x)
        = ∫ x, (fun x => star (g x)) x * 𝓕⁻ (Set.indicator C (𝓕 u)) x := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [bandOp]
      ring
    rw [h1]
    rw [integral_mul_fourierInv (Set.indicator C (𝓕 u)) (fun x => star (g x))
        (memLp_one_iff_integrable.mp hHu1) (memLp_one_iff_integrable.mp hsgu1) hHu2 hsgu2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [fourier_star_neg_real g (-ξ), neg_neg]
  have hR : ∫ x, u x * star (bandOp C g x)
      = star (∫ ξ, Set.indicator C (𝓕 g) ξ * star ((𝓕 u) ξ)) := by
    have h1 : ∫ x, u x * star (bandOp C g x)
        = star (∫ x, (fun x => star (u x)) x * 𝓕⁻ (Set.indicator C (𝓕 g)) x) := by
      have hpt : (fun x => u x * star (bandOp C g x))
          = fun x => star ((fun x => star (u x)) x * 𝓕⁻ (Set.indicator C (𝓕 g)) x) := by
        funext x
        simp only [bandOp, star_mul, star_star]
        ring
      rw [hpt, Complex.star_def, integral_conj]
    rw [h1]
    congr 1
    rw [integral_mul_fourierInv (Set.indicator C (𝓕 g)) (fun x => star (u x))
        (memLp_one_iff_integrable.mp hHg1) (memLp_one_iff_integrable.mp hsu1) hHg2 hsu2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [fourier_star_neg_real u (-ξ), neg_neg]
  have key : ∫ ξ, Set.indicator C (𝓕 u) ξ * star ((𝓕 g) ξ)
      = ∫ ξ, star (Set.indicator C (𝓕 g) ξ * star ((𝓕 u) ξ)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    by_cases hx : ξ ∈ C
    · simp only [Set.indicator_of_mem hx, star_mul, star_star]
    · simp [Set.indicator_of_notMem hx]
  rw [hL, hR, key, Complex.star_def]
  exact integral_conj

/-- In `ℝ` (a conditionally complete linear order), an element of a finite index set is bounded
above by the corresponding bi-supremum. -/
lemma le_biSup_finset_real {ι : Type*} (J : Finset ι) (f : ι → ℝ) {i : ι} (hi : i ∈ J) :
    f i ≤ ⨆ j ∈ J, f j := by
  change f i ≤ ⨆ (j : ι), ⨆ (_ : j ∈ J), f j
  refine le_ciSup₂ (α := ℝ) (κ := fun j => j ∈ J)
    (f := fun j (_ : j ∈ J) => f j) ?_ i hi
  have hfin : (⋃ j, Set.range (fun (_ : j ∈ J) => f j)) ⊆ f '' (↑J : Set ι) := by
    intro y hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨j, h⟩ := hy
    rw [Set.mem_range] at h
    obtain ⟨hj, rfl⟩ := h
    exact ⟨j, hj, rfl⟩
  exact Set.Finite.bddAbove (Set.Finite.subset (J.finite_toSet.image f) hfin)

/-- In `ℝ`, a nonnegative bound valid on a finite index set bounds the bi-supremum. -/
lemma biSup_finset_le_real {ι : Type*} (J : Finset ι) (f : ι → ℝ) {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ i ∈ J, f i ≤ a) : (⨆ j ∈ J, f j) ≤ a := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hJ : J = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun i => isEmptyElim i)
    rw [hJ, iSup_of_empty', Real.sSup_empty]
    exact ha
  · refine ciSup_le ?_
    intro i
    by_cases hi : i ∈ J
    · rw [ciSup_pos hi]; exact h i hi
    · rw [ciSup_neg hi, Real.sSup_empty]; exact ha

/-- **Pairwise disjoint supports collapse the `ℓ²` norm of the sum of norms.** -/
lemma sq_sum_norm_eq_sum_sq_of_disjoint {ι : Type*} (J : Finset ι) (u : ι → ℝ → ℂ)
    (hdisj : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → ∀ x : ℝ, u i x * star (u j x) = 0) (x : ℝ) :
    (∑ i ∈ J, ‖u i x‖) ^ 2 = ∑ i ∈ J, ‖u i x‖ ^ 2 := by
  set s := J.filter (fun i => u i x ≠ 0) with hs
  have hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ‖u i x‖ * ‖u j x‖ = 0 := by
    intro i hi j hj hij
    have hi' := (Finset.mem_filter.mp hi)
    have hj' := (Finset.mem_filter.mp hj)
    have : u i x * star (u j x) = 0 := hdisj i hi'.1 j hj'.1 hij x
    by_contra h
    exact mul_ne_zero hi'.2 (star_ne_zero.mpr hj'.2) this
  calc (∑ i ∈ J, ‖u i x‖) ^ 2
      = (∑ i ∈ s, ‖u i x‖) ^ 2 := by
        rw [hs, Finset.sum_filter]
        congr 1
        refine Finset.sum_congr rfl (fun i _ => ?_)
        by_cases h : u i x = 0 <;> simp [h]
    _ = ∑ i ∈ s, ∑ j ∈ s, ‖u i x‖ * ‖u j x‖ := by rw [sq, Finset.sum_mul_sum]
    _ = ∑ i ∈ s, ‖u i x‖ * ‖u i x‖ := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [Finset.sum_eq_single i]
        · intro j hj hji
          exact hcross i hi j hj (fun h => hji h.symm)
        · intro h; exact absurd hi h
    _ = ∑ i ∈ s, ‖u i x‖ ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => by rw [sq])
    _ = ∑ i ∈ J, ‖u i x‖ ^ 2 := by
        rw [hs, Finset.sum_filter]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        by_cases h : u i x = 0 <;> simp [h]

/-! ## The main theorem -/

/-- **A maximal estimate for a family of band-pass operators implies the corresponding dual
"sum" estimate for disjointly supported weights.**

Let `C i` (`i : ι`) be measurable bounded frequency sets and suppose that for every finite index
set `J ⊆ ι` the truncated maximal operator is `L²`-bounded by `B`:
`√(∫ x, (⨆_{i∈J} ‖bandOp (C i) g x‖)²) ≤ B √(∫ x, ‖g x‖²)` for every `g ∈ L¹ ∩ L²`.
Then for every finite `J ⊆ ι` and every family `u i` (`i ∈ J`) of `L¹ ∩ L²` functions with
**pairwise disjoint supports**,
`√(∫ x, ‖∑_{i∈J} bandOp (C i) (u i) x‖²) ≤ B √(∑_{i∈J} ∫ x, ‖u i x‖²)`.

Proof: `bandOp (C i)` is self-adjoint, so for `g ∈ L¹ ∩ L²`
`∫ x, (∑_i bandOp (C i) (u i) x) · conj (g x) = ∑_i ∫ x, u i x · conj (bandOp (C i) g x)`,
and the pointwise bound
`|∑_i u i x · conj (bandOp (C i) g x)| ≤ (∑_i ‖u i x‖) · (⨆_i ‖bandOp (C i) g x‖)`
together with Cauchy–Schwarz, the identity `(∑_i ‖u i‖)² = ∑_i ‖u i‖²` (disjoint supports) and
the maximal estimate (applied to the finite index set `J`) give the result; `g` is taken to be a
bounded compactly supported truncation of the sum `∑_i bandOp (C i) (u i)` and one passes to the
limit. -/
theorem bandOp_dual_of_maximal {ι : Type*} (C : ι → Set ℝ)
    (hmeas : ∀ i, MeasurableSet (C i)) (hbd : ∀ i, Bornology.IsBounded (C i))
    (B : ℝ) (hB : 0 ≤ B)
    (hmax : ∀ (g : ℝ → ℂ), MeasureTheory.Integrable g →
      MeasureTheory.MemLp g 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
      ∀ (J : Finset ι),
        Real.sqrt (∫ x : ℝ, (⨆ i ∈ J, ‖bandOp (C i) g x‖) ^ 2)
          ≤ B * Real.sqrt (∫ x : ℝ, ‖g x‖ ^ 2))
    (J : Finset ι) (u : ι → ℝ → ℂ)
    (hu1 : ∀ i ∈ J, MeasureTheory.MemLp (u i) 1 (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hu2 : ∀ i ∈ J, MeasureTheory.MemLp (u i) 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hdisj : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → ∀ x : ℝ, u i x * star (u j x) = 0) :
    Real.sqrt (∫ x : ℝ, ‖∑ i ∈ J, bandOp (C i) (u i) x‖ ^ 2)
      ≤ B * Real.sqrt (∑ i ∈ J, ∫ x : ℝ, ‖u i x‖ ^ 2) := by
  classical
  by_cases hJ : J = ∅
  · subst hJ
    simp
  · obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hJ
    haveI : Nonempty ι := ⟨i₀⟩
    let h : ℝ → ℂ := fun x => ∑ i ∈ J, bandOp (C i) (u i) x
    let S : ℝ := ∑ i ∈ J, ∫ x : ℝ, ‖u i x‖ ^ 2
    let indr : ℕ → ℝ → ℝ :=
      fun n x => (Set.Icc (-(n : ℝ)) (n : ℝ)).indicator (fun _ => (1 : ℝ)) x
    let g : ℕ → ℝ → ℂ := fun n x => h x * ((indr n x : ℝ) : ℂ)
    have hindr_meas : ∀ n : ℕ, Measurable (indr n) :=
      fun n => measurable_const.indicator measurableSet_Icc
    have hindr_nn : ∀ n x, 0 ≤ indr n x := by
      intro n x
      show 0 ≤ (Set.Icc (-(n : ℝ)) (n : ℝ)).indicator (fun _ => (1 : ℝ)) x
      by_cases hx : x ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
      · rw [Set.indicator_of_mem hx]
        norm_num
      · rw [Set.indicator_of_notMem hx]
    have hindr_le : ∀ n x, indr n x ≤ 1 := by
      intro n x
      show (Set.Icc (-(n : ℝ)) (n : ℝ)).indicator (fun _ => (1 : ℝ)) x ≤ 1
      by_cases hx : x ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]
        norm_num
    have hindr_memLp : ∀ n : ℕ, MemLp (indr n) 2 (volume : Measure ℝ) := fun n =>
      memLp_indicator_const 2 measurableSet_Icc (1 : ℝ)
        (Or.inr (isCompact_Icc.measure_lt_top (μ := volume)).ne)
    have hSnn : 0 ≤ S := by
      show 0 ≤ ∑ i ∈ J, ∫ x : ℝ, ‖u i x‖ ^ 2
      exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
    have h_memLp : MemLp h 2 (volume : Measure ℝ) :=
      memLp_finsetSum J (fun i hi => bandOp_memLp (C i) (hmeas i) (hbd i) (u i)
        (memLp_one_iff_integrable.mp (hu1 i hi)) (hu2 i hi))
    have hNnn : 0 ≤ ∫ x : ℝ, ‖h x‖ ^ 2 := integral_nonneg (fun x => sq_nonneg _)
    have hgn2 : ∀ n : ℕ, MemLp (g n) 2 (volume : Measure ℝ) := by
      intro n
      refine MemLp.of_le h_memLp ?_ ?_
      · exact h_memLp.aestronglyMeasurable.mul
          ((memLp_ofReal (hindr_memLp n)).aestronglyMeasurable)
      · filter_upwards with x
        show ‖h x * ((indr n x : ℝ) : ℂ)‖ ≤ ‖h x‖
        rw [norm_mul]
        calc ‖h x‖ * ‖((indr n x : ℝ) : ℂ)‖ ≤ ‖h x‖ * 1 :=
              mul_le_mul_of_nonneg_left (by
                rw [norm_ofReal_eq, abs_of_nonneg (hindr_nn n x)]
                exact hindr_le n x) (norm_nonneg _)
          _ = ‖h x‖ := mul_one _
    have hgn1 : ∀ n : ℕ, MemLp (g n) 1 (volume : Measure ℝ) :=
      fun n => h_memLp.mul' (memLp_ofReal (hindr_memLp n))
    have hgnint : ∀ n : ℕ, Integrable (g n) := fun n => memLp_one_iff_integrable.mp (hgn1 n)
    -- the whole argument for a fixed truncation index `n`
    have key : ∀ n : ℕ, ‖∫ x : ℝ, h x * star (g n x)‖
        ≤ B * Real.sqrt S * Real.sqrt (∫ x : ℝ, ‖g n x‖ ^ 2) := by
      intro n
      let M : ℝ → ℝ := fun x => ⨆ i ∈ J, ‖bandOp (C i) (g n) x‖
      have hMmeas : Measurable M :=
        Measurable.biSup (↑J : Set ι) J.countable_toSet
          (fun i _ => (bandOp_cont (C i) (hmeas i) (hbd i) (g n) (hgnint n)).norm.measurable)
      have hMnn : ∀ x, 0 ≤ M x := fun x =>
        le_trans (norm_nonneg _) (le_biSup_finset_real J (fun i => ‖bandOp (C i) (g n) x‖) hi₀)
      have hMle : ∀ x, M x ≤ ∑ i ∈ J, ‖bandOp (C i) (g n) x‖ := fun x =>
        biSup_finset_le_real J (fun i => ‖bandOp (C i) (g n) x‖)
          (Finset.sum_nonneg (fun i _ => norm_nonneg _))
          (fun i hi => Finset.single_le_sum (f := fun j => ‖bandOp (C j) (g n) x‖)
            (fun j _ => norm_nonneg _) hi)
      have hMsum : MemLp (fun x : ℝ => ∑ i ∈ J, ‖bandOp (C i) (g n) x‖) 2
          (volume : Measure ℝ) :=
        memLp_finsetSum J (fun i _ =>
          (bandOp_memLp (C i) (hmeas i) (hbd i) (g n) (hgnint n) (hgn2 n)).norm)
      have hMmem : MemLp M 2 (volume : Measure ℝ) :=
        MemLp.of_le hMsum hMmeas.aestronglyMeasurable
          (Filter.Eventually.of_forall (fun x => by
            rw [Real.norm_of_nonneg (hMnn x),
              Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => norm_nonneg _))]
            exact hMle x))
      have hMbound : Real.sqrt (∫ x : ℝ, M x ^ 2) ≤ B * Real.sqrt (∫ x : ℝ, ‖g n x‖ ^ 2) :=
        hmax (g n) (hgnint n) (hgn2 n) J
      -- Step 1: expand the sum inside the integral
      have hmain : ∫ x : ℝ, h x * star (g n x)
          = ∫ x : ℝ, ∑ i ∈ J, u i x * star (bandOp (C i) (g n) x) := by
        have step1 : ∫ x : ℝ, h x * star (g n x)
            = ∑ i ∈ J, ∫ x : ℝ, bandOp (C i) (u i) x * star (g n x) := by
          have hpt : (fun x : ℝ => h x * star (g n x))
              = fun x => ∑ i ∈ J, bandOp (C i) (u i) x * star (g n x) := by
            funext x
            show (∑ i ∈ J, bandOp (C i) (u i) x) * star (g n x)
                = ∑ i ∈ J, bandOp (C i) (u i) x * star (g n x)
            rw [Finset.sum_mul]
          have hf : ∀ i ∈ J, Integrable (fun x : ℝ =>
              bandOp (C i) (u i) x * star (g n x)) := fun i hi => MemLp.integrable_mul
            (bandOp_memLp (C i) (hmeas i) (hbd i) (u i)
              (memLp_one_iff_integrable.mp (hu1 i hi)) (hu2 i hi)) (hgn2 n).star
          rw [hpt]
          exact integral_finsetSum J hf
        have step2 : ∑ i ∈ J, ∫ x : ℝ, bandOp (C i) (u i) x * star (g n x)
            = ∑ i ∈ J, ∫ x : ℝ, u i x * star (bandOp (C i) (g n) x) :=
          Finset.sum_congr rfl (fun i hi => bandOp_integral_pairing (C i) (hmeas i) (hbd i) (u i) (g n)
            (hu1 i hi) (hu2 i hi) (hgn1 n) (hgn2 n))
        have step3 : (∑ i ∈ J, ∫ x : ℝ, u i x * star (bandOp (C i) (g n) x))
            = ∫ x : ℝ, ∑ i ∈ J, u i x * star (bandOp (C i) (g n) x) := by
          rw [integral_finsetSum
            (f := fun i x => u i x * star (bandOp (C i) (g n) x)) J
            (fun i hi => MemLp.integrable_mul (hu2 i hi)
              ((bandOp_memLp (C i) (hmeas i) (hbd i) (g n) (hgnint n) (hgn2 n)).star))]
        rw [step1, step2, step3]
      -- Step 2: the Cauchy--Schwarz estimate
      have hFmem : MemLp (fun x : ℝ => ∑ i ∈ J, ‖u i x‖) 2 (volume : Measure ℝ) :=
        memLp_finsetSum J (fun i hi => (hu2 i hi).norm)
      have hFnn : ∀ x, 0 ≤ ∑ i ∈ J, ‖u i x‖ := fun x =>
        Finset.sum_nonneg (fun i _ => norm_nonneg _)
      have hholder : ∫ x : ℝ, (∑ i ∈ J, ‖u i x‖) * M x
          ≤ Real.sqrt (∫ x : ℝ, (∑ i ∈ J, ‖u i x‖) ^ 2)
            * Real.sqrt (∫ x : ℝ, M x ^ 2) := by
        have h2 := integral_mul_norm_le_Lp_mul_Lq (μ := (volume : Measure ℝ))
          (f := fun x : ℝ => ∑ i ∈ J, ‖u i x‖) (g := M) (p := 2) (q := 2)
          (by rw [Real.holderConjugate_iff]; norm_num)
          (by simpa only [ENNReal.ofReal_ofNat] using hFmem)
          (by simpa only [ENNReal.ofReal_ofNat] using hMmem)
        have hFabs : ∀ x : ℝ, ‖(fun x : ℝ => ∑ i ∈ J, ‖u i x‖) x‖ = ∑ i ∈ J, ‖u i x‖ :=
          fun x => Real.norm_of_nonneg (hFnn x)
        have hMabs : ∀ x : ℝ, ‖M x‖ = M x := fun x => Real.norm_of_nonneg (hMnn x)
        have hF2 : (∫ x : ℝ, ‖(fun x : ℝ => ∑ i ∈ J, ‖u i x‖) x‖ ^ (2 : ℝ))
            = ∫ x : ℝ, (∑ i ∈ J, ‖u i x‖) ^ 2 := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
          simp only []
          rw [hFabs x, Real.rpow_two]
        have hM2 : (∫ x : ℝ, ‖M x‖ ^ (2 : ℝ)) = ∫ x : ℝ, M x ^ 2 := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
          simp only []
          rw [hMabs x, Real.rpow_two]
        calc ∫ x : ℝ, (∑ i ∈ J, ‖u i x‖) * M x
            = ∫ x : ℝ, ‖(fun x : ℝ => ∑ i ∈ J, ‖u i x‖) x‖ * ‖M x‖ := by
              refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
              show (∑ i ∈ J, ‖u i x‖) * M x
                  = ‖(fun x : ℝ => ∑ i ∈ J, ‖u i x‖) x‖ * ‖M x‖
              rw [hFabs x, hMabs x]
          _ ≤ (∫ x : ℝ, ‖(fun x : ℝ => ∑ i ∈ J, ‖u i x‖) x‖ ^ (2 : ℝ)) ^ (1 / 2)
                * (∫ x : ℝ, ‖M x‖ ^ (2 : ℝ)) ^ (1 / 2) := h2
          _ = Real.sqrt (∫ x : ℝ, (∑ i ∈ J, ‖u i x‖) ^ 2) * Real.sqrt (∫ x : ℝ, M x ^ 2) := by
              rw [hF2, hM2, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
      have hsqS : ∫ x : ℝ, (∑ i ∈ J, ‖u i x‖) ^ 2 = S := by
        calc ∫ x : ℝ, (∑ i ∈ J, ‖u i x‖) ^ 2
            = ∫ x : ℝ, ∑ i ∈ J, ‖u i x‖ ^ 2 := by
              refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
              exact sq_sum_norm_eq_sum_sq_of_disjoint J u hdisj x
          _ = ∑ i ∈ J, ∫ x : ℝ, ‖u i x‖ ^ 2 :=
              integral_finsetSum J (fun i hi => ((hu2 i hi).norm).integrable_sq)
          _ = S := rfl
      have hbound : ‖∫ x : ℝ, ∑ i ∈ J, u i x * star (bandOp (C i) (g n) x)‖
          ≤ Real.sqrt S * Real.sqrt (∫ x : ℝ, M x ^ 2) := by
        have hpt : ∀ x : ℝ,
            ‖∑ i ∈ J, u i x * star (bandOp (C i) (g n) x)‖
              ≤ (∑ i ∈ J, ‖u i x‖) * M x := by
          intro x
          calc ‖∑ i ∈ J, u i x * star (bandOp (C i) (g n) x)‖
              ≤ ∑ i ∈ J, ‖u i x * star (bandOp (C i) (g n) x)‖ :=
                norm_sum_le _ _
            _ = ∑ i ∈ J, ‖u i x‖ * ‖bandOp (C i) (g n) x‖ := by
                refine Finset.sum_congr rfl (fun i _ => by rw [norm_mul, norm_star])
            _ ≤ ∑ i ∈ J, ‖u i x‖ * M x := by
                refine Finset.sum_le_sum (fun i hi => ?_)
                exact mul_le_mul_of_nonneg_left (le_biSup_finset_real J
                  (fun i => ‖bandOp (C i) (g n) x‖) hi) (norm_nonneg _)
            _ = (∑ i ∈ J, ‖u i x‖) * M x := by rw [Finset.sum_mul]
        have hHmem : MemLp (fun x : ℝ => ∑ i ∈ J, u i x * star (bandOp (C i) (g n) x)) 1
            (volume : Measure ℝ) :=
          memLp_finsetSum J (fun i hi => memLp_one_iff_integrable.mpr
            (MemLp.integrable_mul (hu2 i hi)
              ((bandOp_memLp (C i) (hmeas i) (hbd i) (g n) (hgnint n) (hgn2 n)).star)))
        have hFMn_int : Integrable (fun x : ℝ => (∑ i ∈ J, ‖u i x‖) * M x) :=
          MemLp.integrable_mul hFmem hMmem
        calc ‖∫ x : ℝ, ∑ i ∈ J, u i x * star (bandOp (C i) (g n) x)‖
            ≤ ∫ x : ℝ, ‖∑ i ∈ J, u i x * star (bandOp (C i) (g n) x)‖ :=
              norm_integral_le_integral_norm _
          _ ≤ ∫ x : ℝ, (∑ i ∈ J, ‖u i x‖) * M x :=
              integral_mono_ae (memLp_one_iff_integrable.mp hHmem).norm hFMn_int
                (Filter.Eventually.of_forall hpt)
          _ ≤ Real.sqrt (∫ x : ℝ, (∑ i ∈ J, ‖u i x‖) ^ 2) * Real.sqrt (∫ x : ℝ, M x ^ 2) :=
              hholder
          _ = Real.sqrt S * Real.sqrt (∫ x : ℝ, M x ^ 2) := by rw [hsqS]
      calc ‖∫ x : ℝ, h x * star (g n x)‖
          = ‖∫ x : ℝ, ∑ i ∈ J, u i x * star (bandOp (C i) (g n) x)‖ := by rw [hmain]
        _ ≤ Real.sqrt S * Real.sqrt (∫ x : ℝ, M x ^ 2) := hbound
        _ ≤ Real.sqrt S * (B * Real.sqrt (∫ x : ℝ, ‖g n x‖ ^ 2)) :=
              mul_le_mul_of_nonneg_left hMbound (Real.sqrt_nonneg S)
        _ = B * Real.sqrt S * Real.sqrt (∫ x : ℝ, ‖g n x‖ ^ 2) := by ring
    -- the truncated functions approximate `h`
    have key2 : ∀ n : ℕ, ∫ x : ℝ, h x * star (g n x)
        = ((∫ x : ℝ, ‖h x‖ ^ 2 * indr n x : ℝ) : ℂ) := by
      intro n
      have hpt : (fun x : ℝ => h x * star (g n x))
          = fun x => ((‖h x‖ ^ 2 * indr n x : ℝ) : ℂ) := by
        funext x
        show h x * star (h x * ((indr n x : ℝ) : ℂ))
            = ((‖h x‖ ^ 2 * indr n x : ℝ) : ℂ)
        have hmc : h x * star (h x) = ((‖h x‖ ^ 2 : ℝ) : ℂ) := by
          simpa [Complex.star_def] using RCLike.mul_conj (h x)
        calc h x * star (h x * ((indr n x : ℝ) : ℂ))
            = (h x * star (h x)) * ((indr n x : ℝ) : ℂ) := by
              rw [star_mul, Complex.star_def, Complex.conj_ofReal]
              ring
          _ = ((‖h x‖ ^ 2 : ℝ) : ℂ) * ((indr n x : ℝ) : ℂ) := by rw [hmc]
          _ = ((‖h x‖ ^ 2 * indr n x : ℝ) : ℂ) := by push_cast; ring
      rw [hpt, integral_complex_ofReal]
    have hgn_bound : ∀ n : ℕ, ∫ x : ℝ, ‖g n x‖ ^ 2 ≤ ∫ x : ℝ, ‖h x‖ ^ 2 := by
      intro n
      refine integral_mono_ae ((hgn2 n).norm.integrable_sq) (h_memLp.norm.integrable_sq)
        (Filter.Eventually.of_forall (fun x => ?_))
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      show ‖h x * ((indr n x : ℝ) : ℂ)‖ ≤ ‖h x‖
      rw [norm_mul]
      calc ‖h x‖ * ‖((indr n x : ℝ) : ℂ)‖ ≤ ‖h x‖ * 1 :=
            mul_le_mul_of_nonneg_left (by
              rw [norm_ofReal_eq, abs_of_nonneg (hindr_nn n x)]
              exact hindr_le n x) (norm_nonneg _)
        _ = ‖h x‖ := mul_one _
    have hlim : Tendsto (fun n : ℕ => ∫ x : ℝ, ‖h x‖ ^ 2 * indr n x) atTop
        (𝓝 (∫ x : ℝ, ‖h x‖ ^ 2)) := by
      refine tendsto_integral_of_dominated_convergence (fun x : ℝ => ‖h x‖ ^ 2) ?_ ?_ ?_ ?_
      · intro n
        exact (h_memLp.norm.aestronglyMeasurable.pow 2).mul
          ((hindr_meas n).aestronglyMeasurable)
      · exact h_memLp.norm.integrable_sq
      · intro n
        filter_upwards with x
        rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hindr_nn n x))]
        exact mul_le_of_le_one_right (sq_nonneg _) (hindr_le n x)
      · filter_upwards with x
        have hev : ∀ᶠ n : ℕ in atTop, indr n x = 1 := by
          filter_upwards [Filter.eventually_ge_atTop (Nat.ceil |x|)] with n hn
          show (Set.Icc (-(n : ℝ)) (n : ℝ)).indicator (fun _ => (1 : ℝ)) x = 1
          rw [Set.indicator_of_mem]
          exact abs_le.mp (le_trans (Nat.le_ceil |x|) (by exact_mod_cast hn))
        refine (tendsto_const_nhds (x := ‖h x‖ ^ 2)).congr' ?_
        filter_upwards [hev] with n hn
        rw [hn, mul_one]
    have hineq : ∫ x : ℝ, ‖h x‖ ^ 2 ≤ B * Real.sqrt S * Real.sqrt (∫ x : ℝ, ‖h x‖ ^ 2) := by
      refine le_of_tendsto hlim (Filter.Eventually.of_forall (fun n => ?_))
      have h1 : (0 : ℝ) ≤ ∫ x : ℝ, ‖h x‖ ^ 2 * indr n x :=
        integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hindr_nn n x))
      have h2 : ‖∫ x : ℝ, h x * star (g n x)‖ = ∫ x : ℝ, ‖h x‖ ^ 2 * indr n x := by
        rw [key2 n, norm_ofReal_eq, abs_of_nonneg h1]
      refine le_trans ?_ (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hgn_bound n))
        (mul_nonneg hB (Real.sqrt_nonneg S)))
      rw [← h2]
      exact key n
    rcases eq_or_lt_of_le hNnn with hN0 | hNpos
    · rw [← hN0, Real.sqrt_zero]
      exact mul_nonneg hB (Real.sqrt_nonneg S)
    · have hs : 0 < Real.sqrt (∫ x : ℝ, ‖h x‖ ^ 2) := Real.sqrt_pos.mpr hNpos
      have hkey4 : Real.sqrt (∫ x : ℝ, ‖h x‖ ^ 2) * Real.sqrt (∫ x : ℝ, ‖h x‖ ^ 2)
          ≤ (B * Real.sqrt S) * Real.sqrt (∫ x : ℝ, ‖h x‖ ^ 2) := by
        rw [← sq, Real.sq_sqrt hNnn]
        exact hineq
      exact le_of_mul_le_mul_right hkey4 hs

end

end Commons.Analysis.Fourier

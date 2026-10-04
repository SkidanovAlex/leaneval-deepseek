import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.fourierCoeff_pd
import Submission.Work.Diff.STE.one_add_sum_pow_le
import Submission.Work.Diff.STE.mFourier_mk_eq_fourierExp
import Submission.Work.Diff.STE.memLp_comp_rep

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Weighted `ℓ²` summability of the Fourier coefficients of a smooth torus function

Layer A of the STE Fourier toolkit, used to close the `Hˢ` (Sobolev) estimates: for a function
`f : (ι → ℝ) → ℂ` that is smooth (`C^∞`) and `1`-periodic in every coordinate, and every
`s : ℕ`, the weighted series

  `Σ_{k : ℤ^ι} ⟨k⟩^{2s} ‖û(k)‖²`   (`⟨k⟩² = wt k = 1 + Σ kᵢ²`)

converges, i.e. `f` lies in `Hˢ`.

The argument has two ingredients.

* **Parseval / Bessel on the cube** (`ste_summable_sq_fourierCoeff`): for every `L²` function `g`
  on the unit cube, `Σ_k ‖ĝ(k)‖² < ∞`.  This is Mathlib's Parseval identity
  `UnitAddTorus.hasSum_sq_mFourierCoeff` on the additive torus `UnitAddTorus ι`, transported to
  the cube: the coordinatewise `Ioc`-representative map is measure preserving
  (`memLp_comp_rep`) and the cube character `fourierExp` is Mathlib's torus character
  (`mFourier_mk_eq_fourierExp`), so the two families of Fourier coefficients agree
  (`ste_mFourierCoeff_lift`).

* **The multiplier identity** (`ste_fourierCoeff_iterate_pd`): `(∂ᵢ)ⁿ` acts on the Fourier side
  as multiplication by `(2πi kᵢ)ⁿ`, so that
  `‖(∂ᵢˢ f)^(k)‖ = (2π |kᵢ|)^s ‖û(k)‖` and hence `(kᵢ²)^s ‖û(k)‖² ≤ ‖(∂ᵢˢ f)^(k)‖²`
  (`ste_pow_le_normSq`).

The weight bound `⟨k⟩^{2s} ≤ (card ι + 1)^s (1 + Σᵢ (kᵢ²)^s)` — the power-mean inequality applied
to the `card ι + 1` nonnegative numbers `1, k₁², …, k_d²` (`one_add_sum_pow_le`) — then dominates
the target series pointwise by a finite sum of Bessel series, which is summable.
-/

noncomputable section

namespace Work.Diff.STE

open MeasureTheory BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. The `L²`-Parseval input on the cube -/

/-- The Haar probability measure on the unit circle, as the `MeasureSpace` structure used for
Mathlib's multivariate torus Fourier theory. -/
noncomputable local instance instMSUnitAddCircleSte : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

/-- The pullback of an `L²` function on the cube along the coordinatewise `Ioc`-representative
map is `L²` on the torus. -/
lemma ste_memLp_comp_rep {g : (ι → ℝ) → ℂ}
    (hg : MemLp g 2 (volume.restrict (unitCube (ι := ι)))) :
    MemLp (fun t : UnitAddTorus ι => g (fun i => (AddCircle.equivIoc 1 0 (t i)).1)) 2
      (Measure.pi (fun _ : ι => AddCircle.haarAddCircle)) :=
  memLp_comp_rep hg

/-- The Fourier coefficient of `g` on the cube equals Mathlib's torus Fourier coefficient of the
pullback of `g` along the coordinatewise `Ioc`-representative map. -/
theorem ste_mFourierCoeff_lift (g : (ι → ℝ) → ℂ) (k : ι → ℤ) :
    UnitAddTorus.mFourierCoeff (fun t : UnitAddTorus ι =>
        g (fun i => (AddCircle.equivIoc 1 0 (t i)).1)) k = fourierCoeff g k := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral (a := fun _ : ι => (0 : ℝ))]
  have hset : {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc (0:ℝ) (0 + 1)} = unitCube (ι := ι) := by
    ext x
    simp only [unitCube, Set.mem_pi, Set.mem_univ, true_implies, zero_add,
      Set.mem_ofPred_eq]
  rw [hset, fourierCoeff]
  refine setIntegral_congr_fun (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioc))
    ?_
  intro x hx
  have hx' : ∀ i, x i ∈ Set.Ioc (0:ℝ) (0 + 1) := by
    have h1 : ∀ i, x i ∈ Set.Ioc (0:ℝ) 1 := by
      simpa only [unitCube, Set.mem_pi, Set.mem_univ, true_implies] using hx
    intro i; simpa using h1 i
  have key : (fun i => (AddCircle.equivIoc (1:ℝ) (0:ℝ) ((x i : ℝ) : UnitAddCircle)).1) = x := by
    funext i
    exact congrArg Subtype.val
      (AddCircle.equivIoc_coe_eq (p := (1 : ℝ)) (a := (0 : ℝ)) (hx' i))
  simp only [key, mFourier_mk_eq_fourierExp, smul_eq_mul]

/-- **Parseval/Bessel on the cube.**  The Fourier coefficients of an `L²` function on the unit
cube are square summable. -/
theorem ste_summable_sq_fourierCoeff (g : (ι → ℝ) → ℂ)
    (hg : MemLp g 2 (volume.restrict (unitCube (ι := ι)))) :
    Summable (fun k : ι → ℤ => ‖fourierCoeff g k‖ ^ 2) := by
  set G : UnitAddTorus ι → ℂ := fun t => g (fun i => (AddCircle.equivIoc 1 0 (t i)).1) with hGdef
  have hG : MemLp G 2 (Measure.pi (fun _ : ι => AddCircle.haarAddCircle)) := memLp_comp_rep hg
  have hG' : MemLp G 2 (volume : Measure (UnitAddTorus ι)) := hG
  set u : Lp ℂ 2 (volume : Measure (UnitAddTorus ι)) := hG'.toLp G with hudef
  have hparse : HasSum (fun k : ι → ℤ =>
      ‖UnitAddTorus.mFourierCoeff (u : UnitAddTorus ι → ℂ) k‖ ^ 2)
      (∫ t, ‖(u : UnitAddTorus ι → ℂ) t‖ ^ 2) := UnitAddTorus.hasSum_sq_mFourierCoeff u
  have hcoef : ∀ k : ι → ℤ,
      UnitAddTorus.mFourierCoeff (u : UnitAddTorus ι → ℂ) k = fourierCoeff g k := by
    intro k
    have h1 : UnitAddTorus.mFourierCoeff (u : UnitAddTorus ι → ℂ) k
        = UnitAddTorus.mFourierCoeff G k := by
      rw [hudef]
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp hG'] with t ht
      rw [ht]
    rw [h1, ste_mFourierCoeff_lift g k]
  exact hparse.summable.congr fun k => by rw [hcoef k]

/-! ## 2. Continuity gives `MemLp` on the cube -/

omit [DecidableEq ι] in
lemma ste_memLp_of_continuous {g : (ι → ℝ) → ℂ} (hg : Continuous g) :
    MemLp g 2 (volume.restrict (unitCube (ι := ι))) := by
  rw [memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable]
  have hC : IsCompact (Set.pi Set.univ (fun _ : ι => Set.Icc (0:ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hsub : unitCube (ι := ι) ⊆ Set.pi Set.univ (fun _ : ι => Set.Icc (0:ℝ) 1) := by
    intro x hx
    simp only [unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx ⊢
    exact fun j => ⟨le_of_lt (hx j).1, (hx j).2⟩
  exact ((hg.norm.pow 2).continuousOn.integrableOn_compact hC).mono_set hsub

/-! ## 3. The multiplicative weight bound -/

omit [DecidableEq ι] in
lemma ste_wt_pow_le_card (s : ℕ) (k : ι → ℤ) :
    (wt k) ^ s ≤ (((Fintype.card ι : ℕ) : ℝ) + 1) ^ s
      * (1 + ∑ i, ((((k i : ℤ)) : ℝ) ^ 2) ^ s) :=
  one_add_sum_pow_le (fun i : ι => (((k i : ℤ)) : ℝ) ^ 2) (fun i => sq_nonneg _) s

/-! ## 4. The iterated Fourier multiplier -/

lemma ste_contDiff_pd (i : ι) {g : (ι → ℝ) → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : ContDiff ℝ (⊤ : ℕ∞) (pd i g) := by
  unfold pd
  exact (ContDiff.fderiv_right hg (by simp)).clm_apply contDiff_const

lemma ste_contDiff_iterate_pd (i : ι) (n : ℕ) {g : (ι → ℝ) → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : ContDiff ℝ (⊤ : ℕ∞) ((pd i)^[n] g) := by
  induction n with
  | zero => simpa using hg
  | succ m ih => rw [Function.iterate_succ_apply']; exact ste_contDiff_pd i ih

/-- The partial derivative of a function periodic in the `i`-th coordinate is again periodic in
the `i`-th coordinate. -/
lemma ste_periodicIn_pd (i j : ι) {g : (ι → ℝ) → ℂ} (hg : PeriodicIn i g) :
    PeriodicIn i (pd j g) := by
  intro x
  have hcomp : (fun y : ι → ℝ => g (y + Pi.single i 1)) = g := funext hg
  have key : fderiv ℝ (fun y : ι → ℝ => g (y + Pi.single i 1)) x = fderiv ℝ g x := by rw [hcomp]
  have key2 : fderiv ℝ (fun y : ι → ℝ => g (y + Pi.single i 1)) x
      = fderiv ℝ g (x + Pi.single i 1) := fderiv_comp_add_right (Pi.single i 1)
  have hd : fderiv ℝ g (x + Pi.single i 1) = fderiv ℝ g x := by rw [← key2, key]
  simp only [pd]
  rw [hd]

lemma ste_periodicIn_iterate_pd (i : ι) (n : ℕ) {g : (ι → ℝ) → ℂ} (hg : PeriodicIn i g) :
    PeriodicIn i ((pd i)^[n] g) := by
  induction n with
  | zero => simpa using hg
  | succ m ih => rw [Function.iterate_succ_apply']; exact ste_periodicIn_pd i i ih

/-- **The iterated Fourier multiplier.**  `(∂ᵢ)ⁿ` acts on the Fourier side as multiplication by
`(2πi kᵢ)ⁿ`. -/
theorem ste_fourierCoeff_iterate_pd (i : ι) (n : ℕ) (g : (ι → ℝ) → ℂ) (k : ι → ℤ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hper : PeriodicIn i g) :
    fourierCoeff ((pd i)^[n] g) k
      = (2 * Real.pi * Complex.I * (k i : ℂ)) ^ n * fourierCoeff g k := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    rw [fourierCoeff_pd i ((pd i)^[m] g) k
        ((ste_contDiff_iterate_pd i m hg).of_le (by norm_num))
        (ste_periodicIn_iterate_pd i m hper), ih, pow_succ]
    ring

/-! ## 5. The norm of the `s`-fold partial derivative -/

lemma ste_norm_ofReal (x : ℝ) : ‖((x : ℝ) : ℂ)‖ = |x| := by
  have h : ‖((x : ℝ) : ℂ)‖ ^ 2 = x ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
  calc ‖((x : ℝ) : ℂ)‖ = Real.sqrt (‖((x : ℝ) : ℂ)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (x ^ 2) := by rw [h]
    _ = |x| := Real.sqrt_sq_eq_abs x

omit [DecidableEq ι] in
lemma ste_norm_multiplier (i : ι) {k : ι → ℤ} :
    ‖(2 * Real.pi * Complex.I * (k i : ℂ))‖ = 2 * Real.pi * |(((k i : ℤ)) : ℝ)| := by
  rw [show (2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ))
      = ((((2 * Real.pi * ((k i : ℤ) : ℝ)) : ℝ)) : ℂ) * Complex.I by push_cast; ring]
  rw [norm_mul, Complex.norm_I, mul_one, ste_norm_ofReal, abs_mul,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi)]

lemma ste_norm_iterate (i : ι) (s : ℕ) (f : (ι → ℝ) → ℂ) (k : ι → ℤ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : PeriodicIn i f) :
    ‖fourierCoeff ((pd i)^[s] f) k‖
      = (2 * Real.pi * |(((k i : ℤ)) : ℝ)|) ^ s * ‖fourierCoeff f k‖ := by
  rw [ste_fourierCoeff_iterate_pd i s f k hf hper, norm_mul, norm_pow, ste_norm_multiplier i]

/-- The pointwise comparison of the weighted coefficient with one Parseval summand:
`(kᵢ²)^s ‖û(k)‖² ≤ ‖(∂ᵢˢ f)^(k)‖²`, because `(kᵢ²)^s ≤ (2π |kᵢ|)^{2s}`. -/
lemma ste_pow_le_normSq (i : ι) (s : ℕ) (f : (ι → ℝ) → ℂ) (k : ι → ℤ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : PeriodicIn i f) :
    ((((k i : ℤ)) : ℝ) ^ 2) ^ s * ‖fourierCoeff f k‖ ^ 2
      ≤ ‖fourierCoeff ((pd i)^[s] f) k‖ ^ 2 := by
  set x : ℝ := (((k i : ℤ)) : ℝ) with hx
  set B : ℝ := ‖fourierCoeff f k‖ with hB
  have hnorm : ‖fourierCoeff ((pd i)^[s] f) k‖ = (2 * Real.pi * |x|) ^ s * B := by
    rw [hB, ste_norm_iterate i s f k hf hper, hx]
  have h1 : ‖fourierCoeff ((pd i)^[s] f) k‖ ^ 2 = ((2 * Real.pi * |x|) ^ s) ^ 2 * B ^ 2 := by
    rw [hnorm]; exact mul_pow ((2 * Real.pi * |x|) ^ s) B 2
  have h2 : ((2 * Real.pi * |x|) ^ s) ^ 2 = (2 * Real.pi * |x|) ^ (2 * s) := by
    rw [← pow_mul, Nat.mul_comm s 2]
  have h3 : (2 * Real.pi * |x|) ^ (2 * s) = ((2 * Real.pi) ^ 2 * x ^ 2) ^ s := by
    rw [pow_mul, mul_pow (2 * Real.pi) |x| 2, sq_abs]
  have hx2 : (0:ℝ) ≤ x ^ 2 := sq_nonneg x
  have hpi2 : (1:ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
  have hge : (x ^ 2) ≤ (2 * Real.pi) ^ 2 * x ^ 2 := by nlinarith [hpi2, hx2]
  rw [h1, h2, h3]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx2 hge s) (sq_nonneg B)

/-! ## 6. The main theorem -/

theorem summable_weighted_fourierCoeff_of_contDiff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : Work.Diff.STE.Periodic1 f) (s : ℕ) :
    Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖Work.Diff.STE.fourierCoeff f k‖ ^ 2) := by
  classical
  set C : ℝ := (((Fintype.card ι : ℕ) : ℝ) + 1) ^ s with hC
  have hCnn : 0 ≤ C := pow_nonneg (by positivity) s
  -- Parseval summability for `f` and for its `s`-fold coordinate derivatives
  have hsumf : Summable (fun k : ι → ℤ => ‖fourierCoeff f k‖ ^ 2) :=
    ste_summable_sq_fourierCoeff f (ste_memLp_of_continuous hf.continuous)
  have hsumi : Summable (fun k : ι → ℤ =>
      ∑ i : ι, ‖fourierCoeff ((pd i)^[s] f) k‖ ^ 2) := by
    refine summable_sum (s := Finset.univ) (fun i _ => ?_)
    exact ste_summable_sq_fourierCoeff _
      (ste_memLp_of_continuous ((ste_contDiff_iterate_pd i s hf).continuous))
  have hdom : Summable (fun k : ι → ℤ => C * (‖fourierCoeff f k‖ ^ 2
      + ∑ i : ι, ‖fourierCoeff ((pd i)^[s] f) k‖ ^ 2)) :=
    (hsumf.add hsumi).mul_left C
  -- the pointwise domination of the weighted series by the Parseval series
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hdom
  · exact mul_nonneg (pow_nonneg (le_of_lt (wt_pos k)) s) (sq_nonneg _)
  · have hwt := ste_wt_pow_le_card (ι := ι) s k
    have hle : ∀ i : ι, ((((k i : ℤ)) : ℝ) ^ 2) ^ s * ‖fourierCoeff f k‖ ^ 2
        ≤ ‖fourierCoeff ((pd i)^[s] f) k‖ ^ 2 := fun i =>
      ste_pow_le_normSq i s f k hf (hper i)
    have h2 : (wt k) ^ s * ‖fourierCoeff f k‖ ^ 2
        ≤ C * (1 + ∑ i, ((((k i : ℤ)) : ℝ) ^ 2) ^ s) * ‖fourierCoeff f k‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hwt (sq_nonneg _)
    have h3 : C * (1 + ∑ i, ((((k i : ℤ)) : ℝ) ^ 2) ^ s) * ‖fourierCoeff f k‖ ^ 2
        = C * (‖fourierCoeff f k‖ ^ 2
            + ∑ i, ((((k i : ℤ)) : ℝ) ^ 2) ^ s * ‖fourierCoeff f k‖ ^ 2) := by
      rw [mul_assoc, add_mul, one_mul, Finset.sum_mul]
    have h4 : C * (‖fourierCoeff f k‖ ^ 2
          + ∑ i, ((((k i : ℤ)) : ℝ) ^ 2) ^ s * ‖fourierCoeff f k‖ ^ 2)
        ≤ C * (‖fourierCoeff f k‖ ^ 2
            + ∑ i, ‖fourierCoeff ((pd i)^[s] f) k‖ ^ 2) := by
      refine mul_le_mul_of_nonneg_left ?_ hCnn
      exact add_le_add (le_refl _) (Finset.sum_le_sum (fun i _ => hle i))
    exact h2.trans (h3.le.trans h4)

end Work.Diff.STE

import Mathlib
import Submission.Work.KMTAreas.A7.Btwist_bilinear_of_bounded
import Submission.Work.KMTPlan.A6.BtwistEx_eq_sum_bandPiece

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6Bile

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.KMTAreas.A7

/-! ## The band term and its basic properties -/

/-- The summand of a band piece: `cw m j · e(-jα) · h(x-j)`. -/
private noncomputable def bandTerm (m : ℝ → ℂ) (α : Work.Analysis.IonescuWainger.Circle)
    (h : ℤ → ℂ) (x j : ℤ) : ℂ :=
  cw m j * fourier (T := 1) (-j) α * h (x - j)

/-- The characters of the circle have modulus one. -/
private lemma norm_fourier_circle (n : ℤ) (α : Work.Analysis.IonescuWainger.Circle) :
    ‖fourier (T := 1) n α‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

/-- The modulus of a band term. -/
private lemma norm_bandTerm (m : ℝ → ℂ) (α : Work.Analysis.IonescuWainger.Circle)
    (h : ℤ → ℂ) (x j : ℤ) : ‖bandTerm m α h x j‖ = ‖cw m j‖ * ‖h (x - j)‖ := by
  rw [bandTerm, norm_mul, norm_mul, norm_fourier_circle, mul_one]

/-! ## Summability of the convolution series -/

/-- `MemLp h 2` against the counting measure is square summability. -/
private lemma summable_norm_sq_of_memLp {f : ℤ → ℂ}
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count) :
    Summable fun j : ℤ => ‖f j‖ ^ 2 := by
  have hmem : Memℓp f 2 := Work.KMTPlan.A6.memlpOfMemLpCount (p := 2) (by norm_num) (by norm_num) hf
  have h := (memℓp_gen_iff (p := (2 : ℝ≥0∞))
    (show (0 : ℝ) < (2 : ℝ≥0∞).toReal by norm_num)).mp hmem
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2] at h
  have h2' : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  rw [h2'] at h
  simpa only [Real.rpow_natCast] using h

/-- The `cw`-coefficients of a window are square summable as soon as they are summable. -/
private lemma summable_norm_cw_sq {m : ℝ → ℂ} (hc : Summable fun j : ℤ => ‖cw m j‖) :
    Summable fun j : ℤ => ‖cw m j‖ ^ 2 := by
  have hd := (hc.mul_of_nonneg hc (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).comp_injective
    (i := fun j : ℤ => (j, j)) (by intro a b hab; exact (Prod.ext_iff.mp hab).1)
  simpa [Function.comp_def, pow_two] using hd

/-- **The convolution series is absolutely summable.**  Cauchy–Schwarz for the `ℓ¹` window
coefficients and the `ℓ²` input: `Σ_j ‖cw m j‖ ‖h (x-j)‖ ≤ ‖cw m‖₂ ‖h‖₂ < ∞`. -/
private lemma summable_norm_cw_mul {m : ℝ → ℂ} {h : ℤ → ℂ} (x : ℤ)
    (hc : Summable fun j : ℤ => ‖cw m j‖)
    (hh : MeasureTheory.MemLp h 2 MeasureTheory.Measure.count) :
    Summable fun j : ℤ => ‖cw m j‖ * ‖h (x - j)‖ := by
  have hsq₁ : Summable fun j : ℤ => ‖cw m j‖ ^ 2 := summable_norm_cw_sq hc
  have hsq₂ : Summable fun j : ℤ => ‖h (x - j)‖ ^ 2 := by
    have h2 : Summable fun j : ℤ => ‖h j‖ ^ 2 := summable_norm_sq_of_memLp hh
    have hinj : Function.Injective (fun j : ℤ => x - j) := sub_right_injective
    simpa [Function.comp_def] using h2.comp_injective hinj
  have hmaj : Summable fun j : ℤ => (‖cw m j‖ ^ 2 + ‖h (x - j)‖ ^ 2) / 2 :=
    (hsq₁.add hsq₂).div_const 2
  refine Summable.of_nonneg_of_le (fun j => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun j => ?_) hmaj
  nlinarith [sq_nonneg (‖cw m j‖ - ‖h (x - j)‖)]

/-- The two–variable version, needed for the product family on `ℤ × ℤ`. -/
private lemma summable_norm_cw_mul_prod (m₁ m₂ : ℝ → ℂ) (h k : ℤ → ℂ) (x : ℤ)
    (hc₁ : Summable fun j : ℤ => ‖cw m₁ j‖) (hc₂ : Summable fun j : ℤ => ‖cw m₂ j‖)
    (hh : MeasureTheory.MemLp h 2 MeasureTheory.Measure.count)
    (hk : MeasureTheory.MemLp k 2 MeasureTheory.Measure.count) :
    Summable fun p : ℤ × ℤ =>
      (‖cw m₁ p.1‖ * ‖h (x - p.1)‖) * (‖cw m₂ p.2‖ * ‖k (x - p.2)‖) :=
  (summable_norm_cw_mul x hc₁ hh).mul_of_nonneg (summable_norm_cw_mul x hc₂ hk)
    (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- A band piece is absolutely summable. -/
private lemma summable_bandTerm (m : ℝ → ℂ) (α : Work.Analysis.IonescuWainger.Circle)
    (h : ℤ → ℂ) (x : ℤ) (hc : Summable fun j : ℤ => ‖cw m j‖)
    (hh : MeasureTheory.MemLp h 2 MeasureTheory.Measure.count) :
    Summable fun j : ℤ => bandTerm m α h x j := by
  refine Summable.of_norm ?_
  simpa only [norm_bandTerm] using summable_norm_cw_mul x hc hh

/-- The product of two band terms is summable over `ℤ × ℤ`. -/
private lemma summable_bandTerm_mul (m₁ m₂ : ℝ → ℂ) (h k : ℤ → ℂ)
    (α β : Work.Analysis.IonescuWainger.Circle) (x : ℤ)
    (hc₁ : Summable fun j : ℤ => ‖cw m₁ j‖) (hc₂ : Summable fun j : ℤ => ‖cw m₂ j‖)
    (hh : MeasureTheory.MemLp h 2 MeasureTheory.Measure.count)
    (hk : MeasureTheory.MemLp k 2 MeasureTheory.Measure.count) :
    Summable fun p : ℤ × ℤ => bandTerm m₁ α h x p.1 * bandTerm m₂ β k x p.2 := by
  refine Summable.of_norm ?_
  exact (summable_norm_cw_mul_prod m₁ m₂ h k x hc₁ hc₂ hh hk).congr (fun p => by
    rw [norm_mul, norm_bandTerm, norm_bandTerm])

/-! ## Interchanging a `tsum` with `Finset` sums -/

/-- A finite sum of summable families is summable. -/
private lemma summable_finset_sum {ι X M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    [ContinuousAdd M] [DecidableEq ι] (s : Finset ι) {g : ι → X → M}
    (h : ∀ i ∈ s, Summable (g i)) : Summable (fun x => ∑ i ∈ s, g i x) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using summable_zero
  | insert a s ha ih =>
      have ha' : Summable (g a) := h a (Finset.mem_insert_self a s)
      have hs' : ∀ i ∈ s, Summable (g i) := fun i hi => h i (Finset.mem_insert_of_mem hi)
      refine (ha'.add (ih hs')).congr (fun x => ?_)
      rw [Finset.sum_insert ha]

/-- **The `tsum` commutes with the two `Finset` sums.** -/
private lemma tsum_finset_finset_swap {ι : Type*} [DecidableEq ι] {M : Type*} [AddCommMonoid M]
    [TopologicalSpace M] [ContinuousAdd M] [T2Space M] (S₁ S₂ : Finset ι) (G : ι → ι → ℤ → M)
    (h₁ : ∀ α ∈ S₁, Summable (fun j => ∑ β ∈ S₂, G α β j))
    (h₂ : ∀ α ∈ S₁, ∀ β ∈ S₂, Summable (fun j => G α β j)) :
    (∑' j : ℤ, ∑ α ∈ S₁, ∑ β ∈ S₂, G α β j) = ∑ α ∈ S₁, ∑ β ∈ S₂, ∑' j : ℤ, G α β j :=
  (Summable.tsum_finsetSum (f := fun α (j : ℤ) => ∑ β ∈ S₂, G α β j) (s := S₁) h₁).trans
    (Finset.sum_congr rfl (fun α hα =>
      Summable.tsum_finsetSum (f := fun β (j : ℤ) => G α β j) (s := S₂)
        (fun β hβ => h₂ α hα β hβ)))

/-! ## The collapse -/

/-- One factor of the collapse: the series over `ℤ × ℤ` of a constant multiple of a product of two
band terms factors into the product of the two band pieces. -/
private lemma tsum_prod_factor (m₁ m₂ : ℝ → ℂ) (h k : ℤ → ℂ)
    (α β : Work.Analysis.IonescuWainger.Circle) (x : ℤ)
    (hbt₁ : Summable fun j : ℤ => bandTerm m₁ α h x j)
    (hbt₂ : Summable fun j : ℤ => bandTerm m₂ β k x j)
    (huv : Summable fun p : ℤ × ℤ => bandTerm m₁ α h x p.1 * bandTerm m₂ β k x p.2)
    (c : ℂ) :
    (∑' p : ℤ × ℤ, c * bandTerm m₁ α h x p.1 * bandTerm m₂ β k x p.2)
      = c * (∑' j : ℤ, bandTerm m₁ α h x j) * (∑' j : ℤ, bandTerm m₂ β k x j) := by
  have hsplit : (∑' p : ℤ × ℤ, c * bandTerm m₁ α h x p.1 * bandTerm m₂ β k x p.2)
      = c * ∑' p : ℤ × ℤ, bandTerm m₁ α h x p.1 * bandTerm m₂ β k x p.2 := by
    have hmiddle : (∑' p : ℤ × ℤ, c * bandTerm m₁ α h x p.1 * bandTerm m₂ β k x p.2)
        = ∑' p : ℤ × ℤ, c * (bandTerm m₁ α h x p.1 * bandTerm m₂ β k x p.2) :=
      tsum_congr (fun p => by ring)
    rw [hmiddle]
    exact tsum_mul_left
  have hfactor : (∑' p : ℤ × ℤ, bandTerm m₁ α h x p.1 * bandTerm m₂ β k x p.2)
      = (∑' j : ℤ, bandTerm m₁ α h x j) * (∑' j : ℤ, bandTerm m₂ β k x j) :=
    (Summable.tsum_mul_tsum hbt₁ hbt₂ huv).symm
  rw [hsplit, hfactor]
  ring

/-- The pointwise expansion of the arithmetic kernel as a finite double sum of products of band
terms. -/
private lemma btwist_kernel_eq (S₁ S₂ : Finset Work.Analysis.IonescuWainger.Circle)
    (c : Work.Analysis.IonescuWainger.Circle → Work.Analysis.IonescuWainger.Circle → ℂ)
    (m₁ m₂ : ℝ → ℂ) (h k : ℤ → ℂ) (x : ℤ) (j₁ j₂ : ℤ) :
    (∑ α ∈ S₁, ∑ β ∈ S₂, c α β * fourier (T := 1) (-j₁) α * fourier (T := 1) (-j₂) β)
        * cw m₁ j₁ * cw m₂ j₂ * h (x - j₁) * k (x - j₂)
      = ∑ α ∈ S₁, ∑ β ∈ S₂, c α β * bandTerm m₁ α h x j₁ * bandTerm m₂ β k x j₂ := by
  have hreassoc : (∑ α ∈ S₁, ∑ β ∈ S₂, c α β * fourier (T := 1) (-j₁) α
        * fourier (T := 1) (-j₂) β) * cw m₁ j₁ * cw m₂ j₂ * h (x - j₁) * k (x - j₂)
      = (∑ α ∈ S₁, ∑ β ∈ S₂, c α β * fourier (T := 1) (-j₁) α
        * fourier (T := 1) (-j₂) β) * (cw m₁ j₁ * cw m₂ j₂ * h (x - j₁) * k (x - j₂)) := by
    ring
  rw [hreassoc, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  unfold bandTerm
  ring

/-- **The unconditional window collapse.**  For any two finite sets of arithmetic frequencies
`S₁`, `S₂` and any coefficients `c`, the double `tsum` defining the twisted bilinear multiplier is
the finite double sum of the products of the corresponding band pieces. -/
private theorem tsum_collapse (S₁ S₂ : Finset Work.Analysis.IonescuWainger.Circle)
    (c : Work.Analysis.IonescuWainger.Circle → Work.Analysis.IonescuWainger.Circle → ℂ)
    (m₁ m₂ : ℝ → ℂ) (h k : ℤ → ℂ) (x : ℤ)
    (hc₁ : Summable fun j : ℤ => ‖cw m₁ j‖) (hc₂ : Summable fun j : ℤ => ‖cw m₂ j‖)
    (hh : MeasureTheory.MemLp h 2 MeasureTheory.Measure.count)
    (hk : MeasureTheory.MemLp k 2 MeasureTheory.Measure.count) :
    (∑' j₁ : ℤ, ∑' j₂ : ℤ,
        (∑ α ∈ S₁, ∑ β ∈ S₂, c α β * fourier (T := 1) (-j₁) α * fourier (T := 1) (-j₂) β)
          * cw m₁ j₁ * cw m₂ j₂ * h (x - j₁) * k (x - j₂))
      = ∑ α ∈ S₁, ∑ β ∈ S₂, c α β
          * (∑' j : ℤ, bandTerm m₁ α h x j) * (∑' j : ℤ, bandTerm m₂ β k x j) := by
  classical
  have hbt₁ : ∀ α : Work.Analysis.IonescuWainger.Circle,
      Summable (fun j : ℤ => bandTerm m₁ α h x j) :=
    fun α => summable_bandTerm m₁ α h x hc₁ hh
  have hbt₂ : ∀ β : Work.Analysis.IonescuWainger.Circle,
      Summable (fun j : ℤ => bandTerm m₂ β k x j) :=
    fun β => summable_bandTerm m₂ β k x hc₂ hk
  have hprod : ∀ α β : Work.Analysis.IonescuWainger.Circle,
      Summable (fun p : ℤ × ℤ => bandTerm m₁ α h x p.1 * bandTerm m₂ β k x p.2) :=
    fun α β => summable_bandTerm_mul m₁ m₂ h k α β x hc₁ hc₂ hh hk
  calc
    (∑' j₁ : ℤ, ∑' j₂ : ℤ,
        (∑ α ∈ S₁, ∑ β ∈ S₂, c α β * fourier (T := 1) (-j₁) α * fourier (T := 1) (-j₂) β)
          * cw m₁ j₁ * cw m₂ j₂ * h (x - j₁) * k (x - j₂))
      = ∑' j₁ : ℤ, ∑' j₂ : ℤ, ∑ α ∈ S₁, ∑ β ∈ S₂,
          c α β * bandTerm m₁ α h x j₁ * bandTerm m₂ β k x j₂ := by
        refine tsum_congr (fun j₁ => tsum_congr (fun j₂ => ?_))
        exact btwist_kernel_eq S₁ S₂ c m₁ m₂ h k x j₁ j₂
    _ = ∑' j₁ : ℤ, ∑ α ∈ S₁, ∑ β ∈ S₂, ∑' j₂ : ℤ,
          c α β * bandTerm m₁ α h x j₁ * bandTerm m₂ β k x j₂ := by
        refine tsum_congr (fun j₁ => ?_)
        exact tsum_finset_finset_swap S₁ S₂
          (fun α β j₂ => c α β * bandTerm m₁ α h x j₁ * bandTerm m₂ β k x j₂)
          (fun α _ => summable_finset_sum S₂ (fun β _ =>
            (hbt₂ β).mul_left (c α β * bandTerm m₁ α h x j₁)))
          (fun α _ β _ => (hbt₂ β).mul_left (c α β * bandTerm m₁ α h x j₁))
    _ = ∑' j₁ : ℤ, ∑ α ∈ S₁, ∑ β ∈ S₂,
          (c α β * bandTerm m₁ α h x j₁) * (∑' j₂ : ℤ, bandTerm m₂ β k x j₂) := by
        refine tsum_congr (fun j₁ => ?_)
        refine Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun β _ => ?_))
        exact tsum_mul_left
    _ = ∑ α ∈ S₁, ∑ β ∈ S₂, ∑' j₁ : ℤ,
          (c α β * bandTerm m₁ α h x j₁) * (∑' j₂ : ℤ, bandTerm m₂ β k x j₂) := by
        exact tsum_finset_finset_swap S₁ S₂
          (fun α β j₁ => (c α β * bandTerm m₁ α h x j₁) * (∑' j₂ : ℤ, bandTerm m₂ β k x j₂))
          (fun α _ => summable_finset_sum S₂ (fun β _ =>
            ((hbt₁ α).mul_left (c α β)).mul_right (∑' j₂ : ℤ, bandTerm m₂ β k x j₂)))
          (fun α _ β _ => ((hbt₁ α).mul_left (c α β)).mul_right
            (∑' j₂ : ℤ, bandTerm m₂ β k x j₂))
    _ = ∑ α ∈ S₁, ∑ β ∈ S₂, c α β
          * (∑' j : ℤ, bandTerm m₁ α h x j) * (∑' j : ℤ, bandTerm m₂ β k x j) := by
        refine Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun β _ => ?_))
        rw [tsum_mul_right]
        rw [tsum_mul_left]

/-- **Band decomposition of the twisted bilinear multiplier `Btwist` (the `≤`-frequency form).**

`Work.KMTAreas.A7.Btwist` is the bilinear convolution whose kernel is
`arithKernel ρ P q l₁ l₂ j₁ j₂ · cw m₁ j₁ · cw m₂ j₂` with
`arithKernel ρ P q l₁ l₂ j₁ j₂ = ∑_{α ∈ (ℚ/ℤ)_{≤l₁}} ∑_{β ∈ (ℚ/ℤ)_{≤l₂}} mZ P q α β · e(-j₁α) · e(-j₂β)`
(a *finite* double sum), so the whole defining double `tsum` may be rearranged into
`∑_{α,β} mZ P q α β · bandPiece m₁ α h x · bandPiece m₂ β k x`, where
`bandPiece m α h x = ∑'_j cw m j · fourier (-j) α · h (x-j)` (`Work.KMTPlan.A6.bandPiece`).

This is the `≤`-frequency counterpart of `Work.KMTPlan.A6.BtwistEx_eq_sum_bandPiece` (PROVED,
same statement for the exact-height kernel `arithKernelExact` over `diffFreqs`): the private
`tsum_collapse` there is generic in the two frequency finsets and the coefficient function, so a
copy with `arithKernelExact → arithKernel` and `diffFreqs → iwArithFreqs` proves this. -/
theorem BtwistSumBandPiece (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (h k : ℤ → ℂ) (x : ℤ)
    (hh : MeasureTheory.MemLp h 2 MeasureTheory.Measure.count)
    (hk : MeasureTheory.MemLp k 2 MeasureTheory.Measure.count)
    (hcw₁ : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw m₁ j‖))
    (hcw₂ : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw m₂ j‖)) :
    Work.KMTAreas.A7.Btwist ρ P l₁ l₂ m₁ m₂ h k x
      = ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
        ∑ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
          Work.KMTAreas.A7.mZ P (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) α β
            * Work.KMTPlan.A6.bandPiece m₁ α h x
            * Work.KMTPlan.A6.bandPiece m₂ β k x := by
  classical
  have key := tsum_collapse (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
    (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
    (Work.KMTAreas.A7.mZ P (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))) m₁ m₂ h k x
    hcw₁ hcw₂ hh hk
  simpa only [Btwist, arithKernel, Work.KMTPlan.A6.bandPiece, bandTerm] using key

end

end Work.KMTPlan.A6Bile

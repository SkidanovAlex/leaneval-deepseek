import Mathlib
import Submission.Work.Peluse.VanDerCorput.sum_muL_mul_eq
import Submission.Work.Peluse.VanDerCorput.shift_sum_zext_eq
import Submission.Work.Peluse.VanDerCorput.sum_window_zext_eq
import Submission.Work.Peluse.BoxNorm.sum_pairs_star_eq_normSq
import Submission.Work.Peluse.PET.vdc_boundary
import Submission.Work.Peluse.PET.muL_abs_bound

namespace Work.Peluse.PET

open scoped BigOperators
open Work.Peluse.VanDerCorput (zext)

noncomputable section

/-!
# Auxiliary lemmas for van der Corput's inequality with Peluse's weight `μ_H`

Everything in this section is elementary finite-sum bookkeeping:

* `star_mul_re_eq_normSq`, `norm_sum_sq_le_card` : the two analytic inputs (the norm is the real
  part of `star z * z`, and Cauchy–Schwarz for a finite sum in `ℂ`);
* `sum_Icc_natCast`, `sum_product_bij` : the two index-change lemmas (a sum over the `ℕ`-interval
  `[1,M]` is a sum over the `ℤ`-interval, and a sum over the `ℤ`-square `[1,H]²` is a sum over the
  product of two `ℕ`-intervals);
* `filtCorr`, `filtCorrC` : the *filtered* correlation sums `∑_y conj (g(y+a)) g y` over those `y`
  with `y` and `y + a` both in `[1,M]`.
-/

/-- The norm is the real part of `star z * z`. -/
lemma star_mul_re_eq_normSq (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- Cauchy–Schwarz for a finite sum with values in `ℂ`. -/
lemma norm_sum_sq_le_card {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le s f
  calc ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := sq_sum_le_card_mul_sum_sq

/-- A sum over the `ℕ`-interval `[1,M]` is a sum over the `ℤ`-interval `[1,M]`. -/
lemma sum_Icc_natCast (M : ℕ) {β : Type*} [AddCommMonoid β] (f : ℤ → β) :
    (∑ y ∈ Finset.Icc 1 M, f (y : ℤ)) = ∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ), f y := by
  have himg : (Finset.Icc 1 M).image (fun n : ℕ => (n : ℤ)) = Finset.Icc (1 : ℤ) (M : ℤ) := by
    ext z
    constructor
    · intro hz
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
      exact Finset.mem_Icc.mpr ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    · intro hz
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hz
      have hz0 : 0 ≤ z := by omega
      have hzt : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
      refine Finset.mem_image.mpr ⟨z.toNat, ?_, hzt⟩
      refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
      · rw [← hzt]; omega
      · rw [← hzt]; omega
  rw [← himg, Finset.sum_image]
  intro a _ b _ hab
  exact Int.ofNat_inj.mp hab

/-- A double sum over the `ℤ`-square `[1,H]²` is a sum over the product of the two `ℕ`-intervals. -/
lemma sum_product_bij (H : ℕ) (φ : ℤ → ℤ → ℂ) :
    (∑ h₁ ∈ Finset.Icc (1 : ℤ) (H : ℤ), ∑ h₂ ∈ Finset.Icc (1 : ℤ) (H : ℤ), φ h₁ h₂)
      = ∑ p ∈ (Finset.Icc 1 H).product (Finset.Icc 1 H), φ (p.1 : ℤ) (p.2 : ℤ) := by
  have hconj : (∑ h₁ ∈ Finset.Icc (1 : ℤ) (H : ℤ), ∑ h₂ ∈ Finset.Icc (1 : ℤ) (H : ℤ), φ h₁ h₂)
      = ∑ q ∈ (Finset.Icc (1 : ℤ) (H : ℤ)).product (Finset.Icc (1 : ℤ) (H : ℤ)), φ q.1 q.2 :=
    (Finset.sum_product _ _ (fun q : ℤ × ℤ => φ q.1 q.2)).symm
  rw [hconj]
  symm
  refine Finset.sum_bij (fun p _ => ((p.1 : ℤ), (p.2 : ℤ))) ?_ ?_ ?_ ?_
  · intro p hp
    have hp' := Finset.mem_product.mp hp
    obtain ⟨a1, b1⟩ := Finset.mem_Icc.mp hp'.1
    obtain ⟨a2, b2⟩ := Finset.mem_Icc.mp hp'.2
    have h1 : (1 : ℤ) ≤ (p.1 : ℤ) := by exact_mod_cast a1
    have h2 : (p.1 : ℤ) ≤ (H : ℤ) := by exact_mod_cast b1
    have h3 : (1 : ℤ) ≤ (p.2 : ℤ) := by exact_mod_cast a2
    have h4 : (p.2 : ℤ) ≤ (H : ℤ) := by exact_mod_cast b2
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨h1, h2⟩, Finset.mem_Icc.mpr ⟨h3, h4⟩⟩
  · intro p _ q _ hpq
    have h1 : (p.1 : ℤ) = (q.1 : ℤ) := congrArg Prod.fst hpq
    have h2 : (p.2 : ℤ) = (q.2 : ℤ) := congrArg Prod.snd hpq
    exact Prod.ext (Int.ofNat_inj.mp h1) (Int.ofNat_inj.mp h2)
  · intro q hq
    have hq' := Finset.mem_product.mp hq
    obtain ⟨a1, b1⟩ := Finset.mem_Icc.mp hq'.1
    obtain ⟨a2, b2⟩ := Finset.mem_Icc.mp hq'.2
    have hz1 : 0 ≤ q.1 := by omega
    have hz2 : 0 ≤ q.2 := by omega
    have ht1 : (q.1.toNat : ℤ) = q.1 := Int.toNat_of_nonneg hz1
    have ht2 : (q.2.toNat : ℤ) = q.2 := Int.toNat_of_nonneg hz2
    refine ⟨(q.1.toNat, q.2.toNat), ?_, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
    · exact Prod.ext ht1 ht2
  · intro p _
    rfl

/-- `(H^2 : ℂ) · z` has real part `(H^2 : ℝ) · z.re`. -/
lemma ofReal_sq_mul_re (H : ℕ) (z : ℂ) : (((H : ℂ) ^ 2) * z).re = (H : ℝ) ^ 2 * z.re := by
  rw [← Complex.ofReal_natCast H, ← Complex.ofReal_pow, Complex.re_ofReal_mul]

/-- The filtered (windowed) correlation of `g` over `[1,M]` at shift `a`, as a complex number. -/
def filtCorrC (M : ℕ) (g : ℤ → ℂ) (a : ℤ) : ℂ :=
  ∑ y ∈ (Finset.Icc (1 : ℤ) (M : ℤ)).filter
      (fun y => y + a ∈ Finset.Icc (1 : ℤ) (M : ℤ)), star (g (y + a)) * g y

/-- The real part of the filtered correlation. -/
def filtCorr (M : ℕ) (g : ℤ → ℂ) (a : ℤ) : ℝ := (filtCorrC M g a).re

lemma filtCorr_eq (M : ℕ) (g : ℤ → ℂ) (a : ℤ) :
    filtCorr M g a = ∑ y ∈ (Finset.Icc (1 : ℤ) (M : ℤ)).filter
      (fun y => y + a ∈ Finset.Icc (1 : ℤ) (M : ℤ)), (star (g (y + a)) * g y).re := by
  rw [filtCorr, filtCorrC, Complex.re_sum]

/-!
## The second moment of the windowed sums

The single analytic identity behind van der Corput: the sum of the squared norms of the windowed
sums `v ↦ ∑_{h ∈ [1,H]} zext g (v + h)` is `H²` times the `μ_H`-weighted average of the *real
parts* of the filtered correlations.  The fibre identity `sum_muL_mul_eq` and the reindexing
`shift_sum_zext_eq` are exactly what turn the double sum over `h₁, h₂` into the `μ_H`-average.
-/

/-- **Second moment of the windowed sums.** -/
lemma sum_normSq_window_eq (H M : ℕ) (hH : 1 ≤ H) (g : ℤ → ℂ) :
    (∑ v ∈ Finset.Icc (1 - (H : ℤ)) ((M : ℤ) - 1),
        ‖∑ h ∈ Finset.Icc (1 : ℤ) (H : ℤ), zext (Finset.Icc (1 : ℤ) (M : ℤ)) g (v + h)‖ ^ 2)
      = (H : ℝ) ^ 2 * ∑ a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
          Work.Peluse.muL H a * filtCorr M g a := by
  set I : Finset ℤ := Finset.Icc (1 : ℤ) (M : ℤ) with hI
  set J : Finset ℤ := Finset.Icc (1 - (H : ℤ)) ((M : ℤ) - 1) with hJ
  set K : Finset ℤ := Finset.Icc (1 : ℤ) (H : ℤ) with hK
  have hne : ((H : ℂ) ^ 2) ≠ 0 := by
    have hHc : (H : ℂ) ≠ 0 := by
      exact_mod_cast (by omega : H ≠ 0)
    exact pow_ne_zero 2 hHc
  have hmu := Work.Peluse.VanDerCorput.sum_muL_mul_eq (H := H) (by omega) (filtCorrC M g)
  calc (∑ v ∈ J, ‖∑ h ∈ K, zext I g (v + h)‖ ^ 2)
      = ∑ v ∈ J, (star (∑ h ∈ K, zext I g (v + h)) * (∑ h ∈ K, zext I g (v + h))).re := by
          refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [star_mul_re_eq_normSq]
    _ = (∑ v ∈ J, star (∑ h ∈ K, zext I g (v + h)) * (∑ h ∈ K, zext I g (v + h))).re :=
          (Complex.re_sum J _).symm
    _ = (∑ v ∈ J, ∑ h₁ ∈ K, ∑ h₂ ∈ K,
            star (zext I g (v + h₁)) * zext I g (v + h₂)).re := by
          congr 1
          refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [star_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl (fun h₁ _ => ?_)
          rw [Finset.mul_sum]
    _ = (∑ h₁ ∈ K, ∑ h₂ ∈ K, ∑ v ∈ J,
            star (zext I g (v + h₁)) * zext I g (v + h₂)).re := by
          congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun h₁ _ => ?_)
          rw [Finset.sum_comm]
    _ = (∑ h₁ ∈ K, ∑ h₂ ∈ K, filtCorrC M g (h₁ - h₂)).re := by
          congr 1
          refine Finset.sum_congr rfl (fun h₁ _ => ?_)
          refine Finset.sum_congr rfl (fun h₂ hh₂ => ?_)
          exact Work.Peluse.VanDerCorput.shift_sum_zext_eq g hh₂
    _ = (∑ p ∈ (Finset.Icc 1 H).product (Finset.Icc 1 H),
            filtCorrC M g ((p.1 : ℤ) - (p.2 : ℤ))).re := by
          congr 1
          exact sum_product_bij H (fun a b => filtCorrC M g (a - b))
    _ = (((H : ℂ) ^ 2) * ∑ a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
            (Work.Peluse.muL H a : ℂ) * filtCorrC M g a).re := by
          congr 1
          rw [hmu, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    _ = (H : ℝ) ^ 2 * ∑ a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
            Work.Peluse.muL H a * filtCorr M g a := by
          rw [ofReal_sq_mul_re, Complex.re_sum]
          refine congrArg (fun z => (H : ℝ) ^ 2 * z) ?_
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Complex.re_ofReal_mul, filtCorr]

/-!
## Van der Corput with Peluse's weight `μ_H`

The window identity `sum_window_zext_eq` (`∑_u ∑_h zext g (u+h) = H ∑_y g y`) together with
Cauchy–Schwarz bounds the square of the window sum by `(M+H)` times the sum of the squared norms
of the windowed sums; the second-moment identity above then converts this into the `μ_H`-average
of the filtered correlations.  This is Peluse's Lemma 4.1 in the form used by the PET step.
-/

/-- **Cauchy–Schwarz + window identity.** -/
lemma vdc_cs (H M : ℕ) (hH : 1 ≤ H) (g : ℤ → ℂ) :
    (H : ℝ) ^ 2 * ‖∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ), g y‖ ^ 2
      ≤ ((M : ℝ) + (H : ℝ)) *
        ∑ v ∈ Finset.Icc (1 - (H : ℤ)) ((M : ℤ) - 1),
          ‖∑ h ∈ Finset.Icc (1 : ℤ) (H : ℤ),
            zext (Finset.Icc (1 : ℤ) (M : ℤ)) g (v + h)‖ ^ 2 := by
  set I : Finset ℤ := Finset.Icc (1 : ℤ) (M : ℤ) with hI
  set J : Finset ℤ := Finset.Icc (1 - (H : ℤ)) ((M : ℤ) - 1) with hJ
  set K : Finset ℤ := Finset.Icc (1 : ℤ) (H : ℤ) with hK
  have hwin := Work.Peluse.VanDerCorput.sum_window_zext_eq (M := M) (H := H) g
  have hzext : (∑ y ∈ I, zext I g y) = ∑ y ∈ I, g y :=
    Finset.sum_congr rfl (fun y hy => Work.Peluse.VanDerCorput.zext_of_mem hy)
  have hcard : ((J.card : ℕ) : ℝ) ≤ (M : ℝ) + (H : ℝ) := by
    rw [hJ, Int.card_Icc]
    have h1 : ((M : ℤ) - 1 + 1 - (1 - (H : ℤ))) = ((M + H - 1 : ℕ) : ℤ) := by
      have h2 : 1 ≤ M + H := by omega
      omega
    rw [h1, Int.toNat_natCast]
    have h2 : ((M + H - 1 : ℕ) : ℝ) ≤ ((M + H : ℕ) : ℝ) := by
      exact_mod_cast (by omega : M + H - 1 ≤ M + H)
    have h3 : ((M + H : ℕ) : ℝ) = (M : ℝ) + (H : ℝ) := by push_cast; ring
    linarith
  have hnorm0 : ‖∑ v ∈ J, ∑ h ∈ K, zext I g (v + h)‖ = (H : ℝ) * ‖∑ y ∈ I, zext I g y‖ := by
    rw [hwin]
    rw [norm_mul, Complex.norm_natCast]
    congr 1
    rw [hzext]
  have hnorm : ‖∑ v ∈ J, ∑ h ∈ K, zext I g (v + h)‖ = (H : ℝ) * ‖∑ y ∈ I, g y‖ := by
    rw [hnorm0, hzext]
  have hCS := norm_sum_sq_le_card J (fun v : ℤ => ∑ h ∈ K, zext I g (v + h))
  have hnn : 0 ≤ ∑ v ∈ J, ‖∑ h ∈ K, zext I g (v + h)‖ ^ 2 :=
    Finset.sum_nonneg (fun v _ => sq_nonneg _)
  calc (H : ℝ) ^ 2 * ‖∑ y ∈ I, g y‖ ^ 2
      = ((H : ℝ) * ‖∑ y ∈ I, g y‖) ^ 2 := by ring
    _ = ‖∑ v ∈ J, ∑ h ∈ K, zext I g (v + h)‖ ^ 2 := by rw [hnorm]
    _ ≤ ((J.card : ℕ) : ℝ) * ∑ v ∈ J, ‖∑ h ∈ K, zext I g (v + h)‖ ^ 2 := hCS
    _ ≤ ((M : ℝ) + (H : ℝ)) * ∑ v ∈ J, ‖∑ h ∈ K, zext I g (v + h)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hcard hnn

/-- **Van der Corput's inequality with `μ_H` and filtered correlations** (Peluse, Lemma 4.1). -/
lemma vdc_filtered (H M : ℕ) (hH : 1 ≤ H) (g : ℤ → ℂ) :
    ‖∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ), g y‖ ^ 2
      ≤ ((M : ℝ) + (H : ℝ)) *
        ∑ a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), Work.Peluse.muL H a * filtCorr M g a := by
  have hH2 : (0 : ℝ) < (H : ℝ) ^ 2 := by positivity
  have h1 := vdc_cs H M hH g
  rw [sum_normSq_window_eq H M hH g] at h1
  have h2 : (H : ℝ) ^ 2 * ‖∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ), g y‖ ^ 2
      ≤ (H : ℝ) ^ 2 * (((M : ℝ) + (H : ℝ)) *
        ∑ a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), Work.Peluse.muL H a * filtCorr M g a) := by
    calc (H : ℝ) ^ 2 * ‖∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ), g y‖ ^ 2
        ≤ ((M : ℝ) + (H : ℝ)) * ((H : ℝ) ^ 2 *
            ∑ a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), Work.Peluse.muL H a * filtCorr M g a) := h1
      _ = (H : ℝ) ^ 2 * (((M : ℝ) + (H : ℝ)) *
            ∑ a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), Work.Peluse.muL H a * filtCorr M g a) := by
          ring
  exact le_of_mul_le_mul_left (by simpa [mul_comm] using h2) hH2

end


/-- **van der Corput's inequality with Peluse's weight `μ_H`** (Peluse, Lemma 4.1, in the form
needed by the PET step): for `M, H ≥ 1` and `‖g‖ ≤ 1`,

`‖∑_{y∈[M]} g y‖² ≤ (M+H) · ( ∑_{a∈[-H,H]} μ_H(a) · ∑_{y∈[M]} Re(conj (g (y+a)) g y) + H )`.

The `+ H` (added once, not per `a`) is exactly the boundary error `∑_a μ_H(a)·(|a|/M)·M ≤ H` from
extending the *filtered* correlation sums of Peluse's Lemma 4.1 to the *unfiltered* range `[M]`.

Useful already-proved material in the workspace (all `sorry`-free, please import them):
`Work.Peluse.VanDerCorput.sum_muL_mul_eq` (the fibre identity
`∑_h μ_L(h) φ h = L⁻² ∑_{h₁,h₂∈[L]} φ(h₁-h₂)`), `Work.Peluse.VanDerCorput.shift_sum_zext_eq`
(reindexing `u ↦ u + h₂` for the zero extension `zext`), and
`Work.Peluse.BoxNorm.sum_pairs_star_eq_normSq`.
WARNING: do NOT use anything from a module that contains a `sorry` (in particular do not use
`Work.Peluse.VanDerCorput.vanDerCorput` or `Work.Peluse.VanDerCorput.sum_window_zext_eq`, which are
still `sorry`); prove the window-counting identity `∑_{u∈[1-H,M-1]} ∑_{h∈[1,H]} zext g (u+h) =
H · ∑_{y∈[M]} g y` inline if you need it. -/
theorem vdc_muL (H M : ℕ) (hH : 1 ≤ H) (hM : 1 ≤ M) (g : ℤ → ℂ) (hg : ∀ y : ℤ, ‖g y‖ ≤ 1) :
    ‖∑ y ∈ Finset.Icc 1 M, g y‖ ^ 2 ≤
      ((M : ℝ) + (H : ℝ)) *
        (∑ a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), Work.Peluse.muL H a *
            (∑ y ∈ Finset.Icc 1 M, (star (g (y + a)) * g y).re) + (H : ℝ)) := by
  set S : Finset ℤ := Finset.Icc (-(H : ℤ)) (H : ℤ) with hS
  -- the inner sums over the `ℕ`-interval `[1,M]` are sums over the `ℤ`-interval
  have hcast : ∀ a : ℤ, (∑ y ∈ Finset.Icc 1 M, (star (g (y + a)) * g y).re)
      = ∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ), (star (g (y + a)) * g y).re :=
    fun a => sum_Icc_natCast M (fun z : ℤ => (star (g (z + a)) * g z).re)
  have hScast : (∑ y ∈ Finset.Icc 1 M, g y) = ∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ), g y :=
    sum_Icc_natCast M g
  -- Peluse's Lemma 4.1 with the *filtered* correlation sums
  have hmain := vdc_filtered H M hH g
  -- replacing the filtered sums by the unfiltered ones costs `H`
  have hbdd : ∑ a ∈ S, Work.Peluse.muL H a * filtCorr M g a
      ≤ ∑ a ∈ S, Work.Peluse.muL H a *
            (∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ), (star (g (y + a)) * g y).re) + (H : ℝ) := by
    calc ∑ a ∈ S, Work.Peluse.muL H a * filtCorr M g a
        ≤ ∑ a ∈ S, Work.Peluse.muL H a *
            ((∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ), (star (g (y + a)) * g y).re) + |(a : ℝ)|) := by
            refine Finset.sum_le_sum (fun a _ => ?_)
            refine mul_le_mul_of_nonneg_left ?_ (muL_nonneg H a)
            rw [filtCorr_eq]
            exact vdc_boundary hM g hg a
      _ = ∑ a ∈ S, Work.Peluse.muL H a *
              (∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ), (star (g (y + a)) * g y).re)
            + ∑ a ∈ S, Work.Peluse.muL H a * |(a : ℝ)| := by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl (fun a _ => by ring)
      _ ≤ ∑ a ∈ S, Work.Peluse.muL H a *
              (∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ), (star (g (y + a)) * g y).re) + (H : ℝ) := by
            rw [show S = Finset.Icc (-(H : ℤ)) (H : ℤ) from hS]
            exact add_le_add le_rfl (muL_abs_bound H hH)
  calc ‖∑ y ∈ Finset.Icc 1 M, g y‖ ^ 2
      = ‖∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ), g y‖ ^ 2 := by rw [hScast]
    _ ≤ ((M : ℝ) + (H : ℝ)) * ∑ a ∈ S, Work.Peluse.muL H a * filtCorr M g a := hmain
    _ ≤ ((M : ℝ) + (H : ℝ)) *
          (∑ a ∈ S, Work.Peluse.muL H a *
              (∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ), (star (g (y + a)) * g y).re) + (H : ℝ)) :=
          mul_le_mul_of_nonneg_left hbdd (by positivity)
    _ = ((M : ℝ) + (H : ℝ)) *
          (∑ a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), Work.Peluse.muL H a *
              (∑ y ∈ Finset.Icc 1 M, (star (g (y + a)) * g y).re) + (H : ℝ)) := by
          refine congrArg (fun z => ((M : ℝ) + (H : ℝ)) * z) ?_
          refine congrArg (fun z => z + (H : ℝ)) ?_
          exact (Finset.sum_congr rfl (fun a _ => by rw [hcast a])).symm

end Work.Peluse.PET

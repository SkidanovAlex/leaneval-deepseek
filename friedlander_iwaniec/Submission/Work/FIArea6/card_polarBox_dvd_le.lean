import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Work.FIArea4.polarBox_card_le
import Submission.Work.FIArea6.card_fiber_mod_le
import Submission.Work.FIArea6.card_zmod_sq_add_sq_zero_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.FIArea6.card_polarBox_dvd_le` — the `d`-refined size of the polar box

The polar box (5.14) is contained in a disc of radius `5θ√N` (`Work.FIArea4.dist_polarBox_le`),
so it contains `O(θ²N + θ√N + 1)` Gaussian integers.  Here the box is further restricted by the
congruence `d ∣ |z|²` (`d` squarefree): the residue class of `z = (r,s)` modulo `d` must satisfy
`r² + s² ≡ 0 (mod d)`, and the number of such classes is `ρ(d) ≤ ∏_{p ∣ d} (2p-1)`; each class
meets a disc of radius `ρ₀` in at most `(2ρ₀/d + 1)²` points.  With `ρ₀ = 5θ√N` and
`2ρ₀ = 10θ√N` this gives the bound

  `#{z ∈ polarBox : d ∣ |z|²} ≤ (∏_{p ∣ d}(2p-1)) · (10θ√N/d + 1)²`.
-/

namespace Work.FIArea6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `(gnorm z : ℤ) = z.re² + z.im²`. -/
private lemma gnorm_zcast (z : GaussianInt) :
    (Work.FIPlan.gnorm z : ℤ) = z.re ^ 2 + z.im ^ 2 := by
  have hnorm : z.norm = z.re ^ 2 + z.im ^ 2 := by rw [Zsqrtd.norm_def]; ring
  rw [Work.FIPlan.gnorm, hnorm,
    Int.natAbs_of_nonneg (by positivity : (0 : ℤ) ≤ z.re ^ 2 + z.im ^ 2)]

theorem card_polarBox_dvd_le (Pa : Work.FITop.Params) (φ : ℝ) (d : ℕ)
    (hd : d ≠ 0) (hdsq : Squarefree d)
    (s : Finset GaussianInt)
    (hs : ∀ z ∈ s, Work.FITop3.InPolarBox Pa φ z ∧ d ∣ Work.FIPlan.gnorm z) :
    (s.card : ℝ)
      ≤ (∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ))
          * (10 * Pa.θ * Real.sqrt Pa.N / (d : ℝ) + 1) ^ 2 := by
  haveI : NeZero d := ⟨hd⟩
  set ρ : ℝ := 5 * Pa.θ * Real.sqrt Pa.N with hρdef
  have hρ0 : 0 ≤ ρ := by
    rw [hρdef]
    exact mul_nonneg (mul_nonneg (by norm_num) Pa.hθ0.le) (Real.sqrt_nonneg _)
  set c : ℂ := (Real.sqrt Pa.N : ℂ)
    * Complex.exp (((φ + Real.pi * Pa.θ : ℝ) : ℂ) * Complex.I) with hcdef
  have hdist : ∀ z ∈ s, ‖z.toComplex - c‖ ≤ ρ := by
    intro z hz
    rw [hcdef, hρdef]
    exact Work.FIArea4.dist_polarBox_le Pa φ z (hs z hz).1
  set res : GaussianInt → ZMod d × ZMod d :=
    fun z => ((z.re : ZMod d), (z.im : ZMod d)) with hres
  set R : Finset (ZMod d × ZMod d) := s.image res with hRdef
  -- (1) each residue class meets `s` in at most `(2ρ/d + 1)²` points
  have hfib : ∀ r ∈ R, ((s.filter (fun z => res z = r)).card : ℝ)
      ≤ (2 * ρ / (d : ℝ) + 1) ^ 2 := by
    intro r hr
    obtain ⟨z₀, hz₀s, rfl⟩ := Finset.mem_image.mp hr
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    refine card_fiber_mod_le (s.filter (fun z => res z = res z₀)) c d hdpos z₀.re z₀.im ρ hρ0
      ?_ ?_ ?_
    · intro z hz
      exact hdist z (Finset.mem_of_mem_filter z hz)
    · intro z hz
      have hz' : res z = res z₀ := (Finset.mem_filter.mp hz).2
      have h1 : (z.re : ZMod d) = (z₀.re : ZMod d) := congrArg Prod.fst hz'
      exact (ZMod.intCast_eq_intCast_iff z.re z₀.re d).mp h1
    · intro z hz
      have hz' : res z = res z₀ := (Finset.mem_filter.mp hz).2
      have h1 : (z.im : ZMod d) = (z₀.im : ZMod d) := congrArg Prod.snd hz'
      exact (ZMod.intCast_eq_intCast_iff z.im z₀.im d).mp h1
  -- (2) split `s` into its residue classes
  have hdecomp : (s.card : ℝ)
      = ∑ r ∈ R, ((s.filter (fun z => res z = r)).card : ℝ) := by
    have hmap : Set.MapsTo res ↑s ↑R := fun z hz => Finset.mem_image.mpr ⟨z, hz, rfl⟩
    rw [Finset.card_eq_sum_card_fiberwise hmap, Nat.cast_sum]
  have hbound1 : (s.card : ℝ) ≤ (R.card : ℝ) * (2 * ρ / (d : ℝ) + 1) ^ 2 := by
    rw [hdecomp]
    calc ∑ r ∈ R, ((s.filter (fun z => res z = r)).card : ℝ)
        ≤ ∑ _r ∈ R, (2 * ρ / (d : ℝ) + 1) ^ 2 := Finset.sum_le_sum hfib
      _ = (R.card : ℝ) * (2 * ρ / (d : ℝ) + 1) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- (3) the residue classes of `s` lie in the solution set of `r² + s² ≡ 0 (mod d)`
  have hRsub : R ⊆ Finset.univ.filter
      (fun r : ZMod d × ZMod d => r.1 ^ 2 + r.2 ^ 2 = 0) := by
    intro r hr
    obtain ⟨z, hzs, rfl⟩ := Finset.mem_image.mp hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hgn := gnorm_zcast z
    have hdvd : (d : ℤ) ∣ z.re ^ 2 + z.im ^ 2 := by
      rw [← hgn]
      exact Int.natCast_dvd_natCast.mpr (hs z hzs).2
    have hz0 : ((z.re ^ 2 + z.im ^ 2 : ℤ) : ZMod d) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (z.re ^ 2 + z.im ^ 2) d).mpr hdvd
    rw [show (z.re : ZMod d) ^ 2 + (z.im : ZMod d) ^ 2
        = ((z.re ^ 2 + z.im ^ 2 : ℤ) : ZMod d) by push_cast; ring]
    exact hz0
  have hRcard : R.card ≤ ∏ p ∈ d.primeFactors, (2 * p - 1) :=
    le_trans (Finset.card_le_card hRsub) (card_zmod_sq_add_sq_zero_le d hdsq)
  have hRcast : (R.card : ℝ) ≤ ∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ) := by
    calc (R.card : ℝ) ≤ ((∏ p ∈ d.primeFactors, (2 * p - 1) : ℕ) : ℝ) := by
          exact_mod_cast hRcard
      _ = ∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ) := by push_cast; ring
  calc (s.card : ℝ) ≤ (R.card : ℝ) * (2 * ρ / (d : ℝ) + 1) ^ 2 := hbound1
    _ ≤ (∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ)) * (2 * ρ / (d : ℝ) + 1) ^ 2 :=
        mul_le_mul_of_nonneg_right hRcast (sq_nonneg _)
    _ = (∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ))
          * (10 * Pa.θ * Real.sqrt Pa.N / (d : ℝ) + 1) ^ 2 := by
        rw [hρdef]; ring

end

end Work.FIArea6

import Mathlib
import Submission.Work.Diff.STE.CSq_periodization_le_of_sup_bound
import Submission.Work.Diff.STE.B3.CSq_period_le_integral_deriv
import Submission.Work.Diff.STE.fourierCoeff_pdVec
import Submission.Work.Diff.STE.bessel_continuous

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Fourier multiplier of a periodised iterated derivative

For a smooth `f` supported in the open unit cube `(-1/2,1/2)^ι`, the periodisation of the iterated
partial derivative `∂^m_l f` has Fourier coefficients

  `fourierCoeff (per (∂^m_l f)) k = (∏ᵢ 2πi k (l i)) * fourierCoeff (per f) k`.

## Route

On the unit cube `(0,1]^ι` the periodisation of `∂^m_l f` is the *finite* sum over
`n ∈ {-1,0}^ι`: the support of `∂^m_l f` is contained in the closed cube, and `x ∈ (0,1]^ι`,
`n ∉ {-1,0}^ι` force `∂^m_l f (x + n) = 0` (`periodization_pdVec_eq_sum_boxIdx`).  The same finite
sum also computes `∂^m_l (per f) x` on the cube (`steB3_pdVec_periodization_eq_sum`), so the two
functions agree on the cube and hence have the same Fourier coefficients.  Finally
`fourierCoeff_pdVec` gives the multiplier `∏ᵢ 2πi k (l i)` for the smooth `1`-periodic function
`per f`.
-/

noncomputable section

namespace Work.Diff.STE.B3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- On the unit cube `(0,1]^ι` the periodisation of an iterated derivative `∂^m_l f` is the finite
sum over the lattice vectors `n ∈ {-1,0}^ι`.  Indeed `∂^m_l f` is supported in the closed unit
cube, and for `x ∈ (0,1]^ι` a coordinate `nᵢ ∉ {-1,0}` forces `xᵢ + nᵢ ∉ [-1/2,1/2]`. -/
lemma periodization_pdVec_eq_sum_boxIdx {f : (ι → ℝ) → ℂ}
    (hsupp : Function.support f ⊆ Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1/2:ℝ)) (1/2)))
    (m : ℕ) (l : Fin m → ι) {x : ι → ℝ} (hx : x ∈ unitCube (ι := ι)) :
    (∑' n : ι → ℤ, pdVec m l f (x + iVec n))
      = ∑ n ∈ csqp_boxIdx ι, pdVec m l f (x + iVec n) := by
  refine tsum_eq_sum (fun n hn => ?_)
  have hxIoc : ∀ i : ι, x i ∈ Set.Ioc (0:ℝ) 1 := fun i => by
    have := Set.mem_pi.mp hx i (Set.mem_univ i)
    simpa only [unitCube, Set.mem_Ioc] using this
  -- some coordinate of `n` is outside `{-1, 0}`
  have hnot : ∃ i : ι, n i ∉ Finset.Icc (-1 : ℤ) 0 := by
    by_contra hc
    push Not at hc
    exact hn (by rw [csqp_mem_boxIdx]; exact hc)
  obtain ⟨i, hi⟩ := hnot
  refine csqp_eq_zero_of_not_mem_closedCube (csqp_support_pdVec_subset_closedCube hsupp m l) ?_
  intro hmem
  have h1 := Set.mem_pi.mp hmem i (Set.mem_univ i)
  rw [Set.mem_Icc] at h1
  have hxlo : (0:ℝ) < x i := (Set.mem_Ioc.mp (hxIoc i)).1
  have hxhi : x i ≤ 1 := (Set.mem_Ioc.mp (hxIoc i)).2
  have hni : n i < -1 ∨ 0 < n i := by
    by_contra hc
    push Not at hc
    exact hi (by rw [Finset.mem_Icc]; exact hc)
  rcases hni with h | h
  · have hle : ((n i : ℤ) : ℝ) ≤ -2 := by
      have h2 : n i ≤ -2 := by omega
      exact_mod_cast h2
    have hle' : (x + iVec n) i ≤ -1 := by
      simp only [Pi.add_apply, iVec_apply]
      linarith
    linarith [h1.1]
  · have hge : (1:ℝ) ≤ ((n i : ℤ) : ℝ) := by
      have h2 : (1:ℤ) ≤ n i := by omega
      exact_mod_cast h2
    have hge' : (1:ℝ) ≤ (x + iVec n) i := by
      simp only [Pi.add_apply, iVec_apply]
      linarith
    linarith [h1.2]

theorem fourierCoeff_periodization_pdVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hsupp : Function.support f ⊆ Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1/2:ℝ)) (1/2)))
    (m : ℕ) (l : Fin m → ι) (k : ι → ℤ) :
    Work.Diff.STE.fourierCoeff (fun z : ι → ℝ => ∑' n : ι → ℤ,
        Work.Diff.STE.pdVec m l f (z + Work.Diff.STE.iVec n)) k
      = (∏ i : Fin m, (2 * Real.pi * Complex.I * (k (l i) : ℂ)))
          * Work.Diff.STE.fourierCoeff (fun z : ι → ℝ => ∑' n : ι → ℤ,
              f (z + Work.Diff.STE.iVec n)) k := by
  classical
  -- the periodisation of `f` is smooth and periodic
  have hPsm : ContDiff ℝ (⊤ : ℕ∞) (fun z : ι → ℝ => ∑' n : ι → ℤ, f (z + iVec n)) :=
    csqp_periodization_contDiff hf hsupp
  have hPper : Periodic1 (fun z : ι → ℝ => ∑' n : ι → ℤ, f (z + iVec n)) :=
    periodization_periodic f
  -- the multiplier for the iterated derivative of the smooth periodic function `per f`
  have hpd : Work.Diff.STE.fourierCoeff (pdVec m l (fun z : ι → ℝ => ∑' n : ι → ℤ,
        f (z + iVec n))) k
      = (∏ i : Fin m, (2 * Real.pi * Complex.I * (k (l i) : ℂ)))
          * Work.Diff.STE.fourierCoeff (fun z : ι → ℝ => ∑' n : ι → ℤ, f (z + iVec n)) k :=
    fourierCoeff_pdVec m l (fun z : ι → ℝ => ∑' n : ι → ℤ, f (z + iVec n))
      (hPsm.of_le (by exact_mod_cast le_top)) hPper k
  -- on the cube the two periodisations (`∂^m_l` of `per f`, and `per` of `∂^m_l f`) coincide
  have hfun : ∀ x ∈ unitCube (ι := ι),
      (∑' n : ι → ℤ, pdVec m l f (x + iVec n))
        = pdVec m l (fun z : ι → ℝ => ∑' n : ι → ℤ, f (z + iVec n)) x := by
    intro x hx
    rw [periodization_pdVec_eq_sum_boxIdx hsupp m l hx]
    exact (steB3_pdVec_periodization_eq_sum hf hsupp m l x hx).symm
  have hcoeff : Work.Diff.STE.fourierCoeff (fun z : ι → ℝ =>
        ∑' n : ι → ℤ, pdVec m l f (z + iVec n)) k
      = Work.Diff.STE.fourierCoeff (pdVec m l (fun z : ι → ℝ => ∑' n : ι → ℤ,
          f (z + iVec n))) k := by
    rw [Work.Diff.STE.fourierCoeff, Work.Diff.STE.fourierCoeff]
    exact setIntegral_congr_fun BesselCont.measSet_unitCube (fun x hx => by rw [hfun x hx])
  rw [hcoeff, hpd]

end Work.Diff.STE.B3

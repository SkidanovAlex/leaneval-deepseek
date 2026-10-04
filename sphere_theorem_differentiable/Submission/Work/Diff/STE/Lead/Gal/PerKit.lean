import Mathlib
import Submission.Work.Diff.STE.periodization_contDiff_periodic
import Submission.Work.Diff.STE.pd_periodization
import Submission.Work.Diff.STE.CSq_periodization_le_of_sup_bound
import Submission.Work.Diff.STE.Lead.Gal.gardJet_holds

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Small periodisation kit for the GardData assembly

Facts about the (real-valued) periodisation `per f z = ∑' m : Fin n → ℤ, f (z + iVec m)` of a
function supported in a ball of radius `< 1/2`:

* `per` is `1`-periodic (`per_periodic`), and integer shifts do not change a periodic function
  (`per_add_iVec`);
* `per` vanishes at (and near) points a coordinate of which is `1/2`, when the support is contained
  in the ball of radius `σ < 1/2` (`per_eq_zero_of_coord_half`,
  `per_eventuallyEq_zero_of_coord_half`);
* the partial derivative of a `1`-periodic function is `1`-periodic (`pd_periodic`);
* the support of an iterated partial derivative is contained in the topological support
  (`tsupport_pd_subset`, `tsupport_pdVec_subset`).
-/

noncomputable section

open Function
open scoped BigOperators

namespace Work.Diff.STE.Lead.Gal

variable {n : ℕ}

/-- The (real-valued) periodisation of `f`. -/
def per (f : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  fun z => ∑' m : Fin n → ℤ, f (z + Work.Diff.STE.iVec m)

@[simp] lemma per_apply (f : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) :
    per f z = ∑' m : Fin n → ℤ, f (z + Work.Diff.STE.iVec m) := rfl

/-- The periodisation of a function is `1`-periodic. -/
lemma per_periodic (f : (Fin n → ℝ) → ℝ) : Work.Diff.STE.Periodic1 (per f) := by
  intro i x
  change ∑' m : Fin n → ℤ, f ((x + Pi.single i 1) + Work.Diff.STE.iVec m)
    = ∑' m : Fin n → ℤ, f (x + Work.Diff.STE.iVec m)
  have h : ∀ m : Fin n → ℤ,
      f ((x + Pi.single i 1) + Work.Diff.STE.iVec m)
        = f (x + Work.Diff.STE.iVec (Pi.single i (1 : ℤ) + m)) := by
    intro m
    congr 1
    funext j
    by_cases hji : j = i
    · subst hji; simp [Pi.single_eq_same]; ring
    · simp [Pi.single_eq_of_ne hji]
  rw [tsum_congr h]
  exact (Equiv.addLeft (Pi.single i (1 : ℤ))).tsum_eq
    (fun n : Fin n → ℤ => f (x + Work.Diff.STE.iVec n))

/-- Shifting the argument by an integer vector does not change a `1`-periodic function. -/
lemma per_add_iVec {f : (Fin n → ℝ) → ℝ} (hf : Work.Diff.STE.Periodic1 f)
    (m : Fin n → ℤ) (z : Fin n → ℝ) : f (z + Work.Diff.STE.iVec m) = f z :=
  Work.Diff.STE.eb_periodic1_add_intVec (f := f) hf (Work.Diff.STE.iVec m)
    (fun i => ⟨m i, rfl⟩) z

/-- **The periodisation vanishes at a point a coordinate of which lies in `(σ, 1-σ)`**, when the
support of `f` is contained in a ball of radius `σ`. -/
lemma per_eq_zero_of_coord_between {f : (Fin n → ℝ) → ℝ} {σ : ℝ}
    (hsupp : ∀ y ∈ Function.support f, ‖y‖ < σ) {z : Fin n → ℝ} {i : Fin n}
    (h1 : σ < z i) (h2 : z i < 1 - σ) : per f z = 0 := by
  rw [per_apply]
  rw [show (fun m : Fin n → ℤ => f (z + Work.Diff.STE.iVec m)) = fun _ => (0 : ℝ) from ?_]
  · simp
  · funext m
    by_contra hm
    have hmem : z + Work.Diff.STE.iVec m ∈ Function.support f := Function.mem_support.mpr hm
    have h3 : ‖z + Work.Diff.STE.iVec m‖ < σ := hsupp _ hmem
    have h4 : ‖(z + Work.Diff.STE.iVec m) i‖ ≤ ‖z + Work.Diff.STE.iVec m‖ :=
      norm_le_pi_norm _ i
    have h5 : |z i + (m i : ℝ)| = ‖(z + Work.Diff.STE.iVec m) i‖ := by
      rw [Real.norm_eq_abs]
      simp only [Pi.add_apply, Work.Diff.STE.iVec_apply]
    have h6 : σ < |z i + (m i : ℝ)| := by
      rcases lt_trichotomy (m i) 0 with h | h | h
      · have hm2 : (m i : ℝ) ≤ -1 := by
          exact_mod_cast (show m i ≤ -1 by omega)
        have habs := neg_le_abs (z i + (m i : ℝ))
        linarith
      · have habs := le_abs_self (z i + (m i : ℝ))
        rw [h, Int.cast_zero, add_zero] at habs ⊢
        linarith
      · have hm2 : (1 : ℝ) ≤ (m i : ℝ) := by
          exact_mod_cast (show (1 : ℤ) ≤ m i by omega)
        have habs := le_abs_self (z i + (m i : ℝ))
        linarith
    rw [h5] at h6
    linarith

/-- **The periodisation vanishes near a point a coordinate of which lies in `(σ, 1-σ)`**, under
the same support hypothesis. -/
lemma per_eventuallyEq_zero_of_coord_between {f : (Fin n → ℝ) → ℝ} {σ : ℝ}
    (hsupp : ∀ y ∈ Function.support f, ‖y‖ < σ) {z : Fin n → ℝ} {i : Fin n}
    (h1 : σ < z i) (h2 : z i < 1 - σ) : per f =ᶠ[nhds z] fun _ => (0 : ℝ) := by
  set δ : ℝ := min (z i - σ) (1 - σ - z i) / 2 with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    have : 0 < min (z i - σ) (1 - σ - z i) := lt_min (by linarith) (by linarith)
    linarith
  refine Filter.eventually_iff_exists_mem.mpr
    ⟨Metric.ball z δ, Metric.ball_mem_nhds z hδpos, fun y hy => ?_⟩
  have hy' : dist y z < δ := by simpa [Metric.mem_ball] using hy
  refine per_eq_zero_of_coord_between (i := i) hsupp ?_ ?_
  · have h3 : |y i - z i| ≤ ‖y - z‖ := by
      rw [← Real.norm_eq_abs (y i - z i), ← Pi.sub_apply]
      exact norm_le_pi_norm _ i
    have h4 : |y i - z i| < δ := lt_of_le_of_lt h3 (by rwa [dist_eq_norm] at hy')
    have h5 := (abs_lt.mp h4).1
    rw [hδdef] at h5
    have h6 : min (z i - σ) (1 - σ - z i) / 2 ≤ z i - σ := by
      refine le_trans (div_le_self (by positivity) (by norm_num)) (min_le_left _ _)
    linarith
  · have h3 : |y i - z i| ≤ ‖y - z‖ := by
      rw [← Real.norm_eq_abs (y i - z i), ← Pi.sub_apply]
      exact norm_le_pi_norm _ i
    have h4 : |y i - z i| < δ := lt_of_le_of_lt h3 (by rwa [dist_eq_norm] at hy')
    have h5 := (abs_lt.mp h4).2
    rw [hδdef] at h5
    have h6 : min (z i - σ) (1 - σ - z i) / 2 ≤ 1 - σ - z i := by
      refine le_trans (div_le_self (by positivity) (by norm_num)) (min_le_right _ _)
    linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `i`-th partial derivative of a `1`-periodic complex-valued function is `1`-periodic. -/
lemma pd_periodic {f : (ι → ℝ) → ℂ} (hf : Work.Diff.STE.Periodic1 f) (i : ι) :
    Work.Diff.STE.Periodic1 (Work.Diff.STE.pd i f) := by
  intro j x
  have h1 : (fun y : ι → ℝ => f (y + Pi.single j 1)) = f := by
    funext y; exact hf j y
  have h2 : Work.Diff.STE.pd i (fun y : ι → ℝ => f (y + Pi.single j 1)) x
      = Work.Diff.STE.pd i f (x + Pi.single j 1) := by
    simp only [Work.Diff.STE.pd, fderiv_comp_add_right]
  rw [← h2, h1]

/-- The support of the `i`-th partial derivative of a complex-valued function is contained in its
(topological) support. -/
lemma tsupport_pd_subset (i : ι) {f : (ι → ℝ) → ℂ} :
    Function.support (Work.Diff.STE.pd i f) ⊆ tsupport f :=
  Work.Diff.STE.csqp_support_pd_subset_closure i

/-- The support of an iterated partial derivative is contained in the (topological) support. -/
lemma tsupport_pdVec_subset (m : ℕ) (l : Fin m → ι) {f : (ι → ℝ) → ℂ} :
    Function.support (Work.Diff.STE.pdVec m l f) ⊆ tsupport f := by
  simpa only [Work.Diff.STE.pdVec, tsupport] using
    Work.Diff.STE.csqp_support_pdList_subset_closure (List.ofFn l) f

/-- **On the half-open cube `(-1/2, 1/2]^n` the periodisation of a function supported in the
`σ`-ball (`σ < 1/2`) is the function itself.** -/
lemma per_eq_self_of_mem_halfCube {f : (Fin n → ℝ) → ℝ} {σ : ℝ} (hσ : σ < 1 / 2)
    (hsupp : ∀ y ∈ Function.support f, ‖y‖ < σ) {z : Fin n → ℝ}
    (hz : ∀ i, z i ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)) : per f z = f z := by
  rw [per_apply, tsum_eq_single (0 : Fin n → ℤ)]
  · simp
  · intro m hm
    by_contra hc
    have hmem : z + Work.Diff.STE.iVec m ∈ Function.support f := Function.mem_support.mpr hc
    have h1 : ‖z + Work.Diff.STE.iVec m‖ < σ := hsupp _ hmem
    have hi : ∃ i, m i ≠ 0 := by
      by_contra h'
      push_neg at h'
      exact hm (funext h')
    obtain ⟨i, hi⟩ := hi
    have h2 : (1 / 2 : ℝ) ≤ |z i + (m i : ℝ)| := by
      have hz1 := (Set.mem_Ioc.mp (hz i)).1
      have hz2 := (Set.mem_Ioc.mp (hz i)).2
      rcases lt_trichotomy (m i) 0 with h | h | h
      · have hm1 : m i ≤ -1 := by omega
        have hm2 : (m i : ℝ) ≤ -1 := by exact_mod_cast hm1
        rw [le_abs]
        right; linarith
      · exact absurd h hi
      · have hm1 : (1 : ℤ) ≤ m i := by omega
        have hm2 : (1 : ℝ) ≤ (m i : ℝ) := by exact_mod_cast hm1
        rw [le_abs]
        left; linarith
    have h3 : ‖(z + Work.Diff.STE.iVec m) i‖ ≤ ‖z + Work.Diff.STE.iVec m‖ :=
      norm_le_pi_norm _ i
    have h4 : |z i + (m i : ℝ)| = ‖(z + Work.Diff.STE.iVec m) i‖ := by
      rw [Real.norm_eq_abs]
      simp only [Pi.add_apply, Work.Diff.STE.iVec_apply]
    rw [h4] at h2
    linarith

end Work.Diff.STE.Lead.Gal

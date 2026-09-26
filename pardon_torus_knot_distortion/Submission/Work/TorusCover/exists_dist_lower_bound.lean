import Mathlib
import Submission.Work.TorusCover.Basic

/-!
# The parametrised torus is locally injective with a uniform Lipschitz lower bound

`Work.TorusCover.TorusParam` carries a uniform *pointwise* lower bound for the derivative of
`psiMap psi`:

  `P.c * ‖u‖ ≤ ‖fderiv ℝ (psiMap P.psi) p u‖`  for all `p` and `u`.

The present file upgrades it to a *two-point* lower bound, uniform over the whole parameter
plane (not just locally): for every `ε > 0` there is `δ > 0` such that

  `(P.c - ε) * ‖x - y‖ ≤ ‖psiMap P.psi x - psiMap P.psi y‖`  whenever `‖x - y‖ ≤ δ`.

The argument is the standard local argument (C¹-regularity turns the pointwise bound into a
ballwise bound via the mean value inequality) followed by two finiteness/compactness steps:
the bound holds on a ball around every point of the fundamental domain `[0, 2π]²`, and the
Lebesgue number lemma turns this into a single radius `δ` on that compact box; periodicity of
`psiMap` (invariance under the period lattice `2πℤ²`) then transports `δ` to all of `ℝ²`.
-/

open LeanEval.KnotTheory.PardonDistortion Set
open scoped ENNReal

namespace Work.TorusCover

noncomputable section

/-! ### The local lower bound -/

/-- **Local two-point lower bound.**  If a map `f : ℝ × ℝ → R3` is differentiable everywhere,
its derivative is continuous at `p`, the derivative at `p` dominates `c * ‖·‖`, and `ε > 0`,
then on a small ball around `p` the map `f` expands distances by at least `(c - ε)`.

The proof is the mean value inequality applied to `z ↦ f z - fderiv ℝ f p z`: the derivative
of the correction term is `fderiv ℝ f z - fderiv ℝ f p`, of operator norm at most `ε / 2`
near `p` by continuity. -/
lemma local_lower_bound {f : ℝ × ℝ → R3} {p : ℝ × ℝ} {c ε : ℝ}
    (hdiff : ∀ x, DifferentiableAt ℝ f x)
    (hcont : ContinuousAt (fderiv ℝ f) p)
    (hderiv : ∀ u : ℝ × ℝ, c * ‖u‖ ≤ ‖fderiv ℝ f p u‖)
    (hε : 0 < ε) :
    ∃ η > 0, ∀ x y : ℝ × ℝ, ‖x - p‖ ≤ η → ‖y - p‖ ≤ η →
      (c - ε) * ‖x - y‖ ≤ ‖f x - f y‖ := by
  have hε2 : 0 < ε / 2 := by linarith
  -- continuity of `fderiv f` at `p` gives a radius on which the derivative stays `ε/2`-close
  -- to its value at `p`.
  have hg : ContinuousAt (fun z => ‖fderiv ℝ f z - fderiv ℝ f p‖) p :=
    (hcont.sub continuousAt_const).norm
  obtain ⟨r, hr, hr'⟩ := (Metric.continuousAt_iff.mp hg) (ε / 2) hε2
  have hr2 : ∀ z, ‖z - p‖ < r → ‖fderiv ℝ f z - fderiv ℝ f p‖ < ε / 2 := by
    intro z hz
    have h0 : ‖fderiv ℝ f p - fderiv ℝ f p‖ = 0 := by simp
    have h1 := hr' (by simpa [dist_eq_norm] using hz)
    rw [h0, dist_zero_right] at h1
    simpa using h1
  refine ⟨r / 2, by linarith, ?_⟩
  intro x y hx hy
  have hx' : x ∈ Metric.closedBall p (r / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm]; linarith
  have hy' : y ∈ Metric.closedBall p (r / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm]; linarith
  have hbound : ∀ z ∈ Metric.closedBall p (r / 2),
      ‖fderiv ℝ f z - fderiv ℝ f p‖ ≤ ε / 2 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    exact le_of_lt (hr2 z (by linarith))
  -- mean value inequality on the convex ball
  have hmvt : ‖f y - f x - fderiv ℝ f p (y - x)‖ ≤ ε / 2 * ‖y - x‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le' (s := Metric.closedBall p (r / 2))
      (φ := fderiv ℝ f p) (C := ε / 2) (fun z _ => hdiff z) hbound
      (convex_closedBall p (r / 2)) hx' hy'
  have htri : ‖fderiv ℝ f p (y - x)‖ ≤
      ‖f y - f x‖ + ‖f y - f x - fderiv ℝ f p (y - x)‖ := by
    have h := norm_sub_le (f y - f x) (f y - f x - fderiv ℝ f p (y - x))
    rwa [sub_sub_cancel] at h
  have hAc : c * ‖y - x‖ ≤ ‖fderiv ℝ f p (y - x)‖ := hderiv (y - x)
  have key : (c - ε / 2) * ‖y - x‖ ≤ ‖f y - f x‖ := by linarith
  have hd : (0 : ℝ) ≤ ‖x - y‖ := norm_nonneg _
  calc (c - ε) * ‖x - y‖ ≤ (c - ε / 2) * ‖x - y‖ := by
        apply mul_le_mul_of_nonneg_right _ hd; linarith
    _ = (c - ε / 2) * ‖y - x‖ := by rw [norm_sub_rev]
    _ ≤ ‖f y - f x‖ := key
    _ = ‖f x - f y‖ := norm_sub_rev _ _

/-! ### Lattice translates into the fundamental domain -/

/-- Every real number has an integer translate lying in `[0, T]`. -/
lemma exists_int_add_mul_mem_Icc (t T : ℝ) (hT : 0 < T) :
    ∃ k : ℤ, t + (k : ℝ) * T ∈ Set.Icc (0 : ℝ) T := by
  refine ⟨⌈-t / T⌉, ?_, ?_⟩
  · have h1 : -t / T ≤ ((⌈-t / T⌉ : ℤ) : ℝ) := Int.le_ceil _
    have h2 : (-t / T) * T ≤ (⌈-t / T⌉ : ℝ) * T :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt hT)
    have h3 : (-t / T) * T = -t := by field_simp
    linarith
  · have h1 : ((⌈-t / T⌉ : ℤ) : ℝ) < -t / T + 1 := Int.ceil_lt_add_one _
    have h2 : ((⌈-t / T⌉ : ℝ)) * T < (-t / T + 1) * T := mul_lt_mul_of_pos_right h1 hT
    have h3 : (-t / T + 1) * T = -t + T := by field_simp
    linarith

/-- Every point of the parameter plane is a period-lattice translate of a point of the
fundamental domain `[0, 2π] × [0, 2π]`. -/
lemma exists_periodShift_add_mem_Icc (z : ℝ × ℝ) :
    ∃ v : ℤ × ℤ, z + periodShift v ∈
      Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi) := by
  obtain ⟨m, hm⟩ := exists_int_add_mul_mem_Icc z.1 (2 * Real.pi) Real.two_pi_pos
  obtain ⟨n, hn⟩ := exists_int_add_mul_mem_Icc z.2 (2 * Real.pi) Real.two_pi_pos
  refine ⟨(m, n), ?_⟩
  rw [Set.mem_prod]
  exact ⟨by simpa [periodShift] using hm, by simpa [periodShift] using hn⟩

/-! ### The uniform bound on the parameter plane -/

theorem exists_dist_lower_bound (P : Work.TorusCover.TorusParam) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x y : ℝ × ℝ, ‖x - y‖ ≤ δ →
      (P.c - ε) * ‖x - y‖ ≤ ‖Work.TorusCover.psiMap P.psi x - Work.TorusCover.psiMap P.psi y‖ := by
  have hcont : Continuous (fderiv ℝ (psiMap P.psi)) :=
    P.contDiff.continuous_fderiv (by simp)
  have hdiff : ∀ x, DifferentiableAt ℝ (psiMap P.psi) x :=
    fun x => P.contDiff.differentiable (by simp) x
  -- a valid radius around every single point
  have hloc : ∀ p : ℝ × ℝ, ∃ η : ℝ, 0 < η ∧ ∀ x y : ℝ × ℝ,
      ‖x - p‖ ≤ η → ‖y - p‖ ≤ η →
      (P.c - ε) * ‖x - y‖ ≤ ‖psiMap P.psi x - psiMap P.psi y‖ :=
    fun p => local_lower_bound hdiff hcont.continuousAt (fun u => P.deriv_lower p.1 p.2 u) hε
  choose η hη using hloc
  -- the fundamental domain and its cover by the balls of half the valid radii
  let D : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)
  have hDcompact : IsCompact D := isCompact_Icc.prod isCompact_Icc
  have hcover : D ⊆ ⋃ p : ℝ × ℝ, Metric.ball p (η p / 2) := by
    intro x _
    exact mem_iUnion.mpr ⟨x, by rw [Metric.mem_ball, dist_self]; linarith [(hη x).1]⟩
  -- Lebesgue number: a single radius valid for every point of `D`
  obtain ⟨δ, hδpos, hδ⟩ := lebesgue_number_lemma_of_metric hDcompact
    (fun p => Metric.isOpen_ball) hcover
  refine ⟨δ / 2, by linarith, ?_⟩
  have hmain : ∀ x ∈ D, ∀ y : ℝ × ℝ, ‖x - y‖ ≤ δ / 2 →
      (P.c - ε) * ‖x - y‖ ≤ ‖psiMap P.psi x - psiMap P.psi y‖ := by
    intro x hx y hxy
    obtain ⟨p, hp⟩ := hδ x hx
    have h1 : x ∈ Metric.ball x δ := by rw [Metric.mem_ball, dist_self]; linarith
    have h2 : y ∈ Metric.ball x δ := by
      rw [Metric.mem_ball, dist_comm, dist_eq_norm]; linarith
    have hxη : ‖x - p‖ ≤ η p := by
      have := hp h1
      rw [Metric.mem_ball, dist_eq_norm] at this
      linarith [(hη p).1]
    have hyη : ‖y - p‖ ≤ η p := by
      have := hp h2
      rw [Metric.mem_ball, dist_eq_norm] at this
      linarith [(hη p).1]
    exact (hη p).2 x y hxη hyη
  -- transport to the whole plane along the period lattice
  intro x y hxy
  obtain ⟨v, hv⟩ := exists_periodShift_add_mem_Icc x
  have hdist : ‖(x + periodShift v) - (y + periodShift v)‖ ≤ δ / 2 := by
    simpa using hxy
  have hfin := hmain (x + periodShift v) hv (y + periodShift v) hdist
  rw [P.psiMap_add_periodShift x v, P.psiMap_add_periodShift y v] at hfin
  have hsub : x + periodShift v - (y + periodShift v) = x - y := by abel
  rwa [hsub] at hfin

end

end Work.TorusCover

import Mathlib
import Submission.Work.Holonomy3.mv_lex_defs
import Submission.Work.Holonomy3.jensen_mean_ineq
import Submission.Work.Holonomy3.circleLog_average_ge
import Submission.Work.Holonomy3.pi_integral_cons
import Submission.Work.Holonomy3.isHomogF_sliceF
import Submission.Work.Holonomy3.pevalF_consPt
import Submission.Work.Holonomy3.sliceF_lexMin
import Submission.Work.Holonomy3.mv_lex_null_zero
import Submission.Work.Holonomy3.mv_lex_log_poly_integrable
import Submission.Work.Holonomy3.diag_slice_identity
import Submission.Work.Holonomy3.mv_lex_general_case

/-!
# The multivariable lexicographic-minimum coefficient bound

`Work.Holonomy3.mv_lexmin_coeff_le_integral`: for a multivariable power series `g` whose sum
function `G` is given on the polydisc of radius `ρ > 1` by `hG`, and whose graded-lexicographically
minimal nonzero coefficient sits at the multi-index `n`, the logarithm of that coefficient is
bounded by the average of `log ‖G‖` over the unit torus.  This is the analytic input behind the
"elementary" holonomy bound of Calegari--Dimitrov--Tang, arXiv:2408.15403, §6, in the form of the
lexicographic induction of Calegari--Dimitrov--Tang, *The Unbounded Denominators Conjecture*,
arXiv:2109.09040, §2.4.

The proof has three parts:

* `homog_poly_case` -- the homogeneous polynomial case, by the lexicographic induction on the
  number of variables (Jensen's formula in one variable, applied to the slice in the first
  variable);
* `poly_case` -- the finitely supported (polynomial) case, obtained from the homogeneous case and
  the diagonal substitution `z ↦ w z` together with Jensen's formula for the one-variable
  polynomial `w ↦ w^{-D} * pevalF c (w • z)`;
* `mv_lex_general_case` -- the passage from polynomials to a general power series, by truncation
  and Fatou's lemma,
fed into the statement below through the elementary conversions `tor`, `pevalF` and `toLex`.
-/

namespace Work.Holonomy3

open scoped BigOperators
open MeasureTheory

noncomputable section


/-- The unit-circle point `e^{2πiu}`. -/
abbrev tor1 (u : ℝ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (u : ℂ))

@[simp]
theorem norm_tor1 (u : ℝ) : ‖tor1 u‖ = 1 := norm_exp_two_pi_I u

/-- `tor` commutes with `Fin.cons`. -/
theorem tor_cons {d : ℕ} (u : ℝ) (s : Fin d → ℝ) :
    tor (Fin.cons u s) = consPt (tor1 u) (tor s) := by
  funext j
  refine Fin.cases ?_ ?_ j
  · simp [tor, consPt, tor1]
  · intro i; simp [tor, consPt, tor1]

/-- The one-variable polynomial attached to a slice: it is `w ↦ w^{-n₀}·P(w, z)`. -/
def slicePoly {d : ℕ} (c : (Fin (d + 1) →₀ ℕ) →₀ ℂ) (n : Fin (d + 1) →₀ ℕ)
    (z : Fin d → ℂ) : Polynomial ℂ :=
  ∑ t ∈ suppFst c, Polynomial.C (pevalF (sliceF c t) z) * Polynomial.X ^ (t - n 0)

theorem slicePoly_eval {d : ℕ} (c : (Fin (d + 1) →₀ ℕ) →₀ ℂ) (n : Fin (d + 1) →₀ ℕ)
    (z : Fin d → ℂ) (w : ℂ) :
    (slicePoly c n z).eval w = ∑ t ∈ suppFst c, w ^ (t - n 0) * pevalF (sliceF c t) z := by
  simp [slicePoly, Polynomial.eval_finsetSum, mul_comm]

theorem slicePoly_analytic {d : ℕ} (c : (Fin (d + 1) →₀ ℕ) →₀ ℂ) (n : Fin (d + 1) →₀ ℕ)
    (z : Fin d → ℂ) :
    AnalyticOnNhd ℂ (fun w : ℂ => (slicePoly c n z).eval w) (Metric.closedBall 0 1) := by
  have hd : DifferentiableOn ℂ (fun w : ℂ => (slicePoly c n z).eval w) (Metric.ball 0 2) :=
    ((Polynomial.differentiable (slicePoly c n z)).differentiableOn)
  have h1 := hd.analyticOnNhd (Metric.isOpen_ball)
  exact h1.mono (Metric.closedBall_subset_ball (by norm_num))

end

end Work.Holonomy3

namespace Work.Holonomy3
open scoped BigOperators
open MeasureTheory
noncomputable section

/-- If `n` is lex-minimal in the support of `c`, then `n 0 ≤ t` for every first coordinate
`t` occurring in the support. -/
theorem le_of_mem_suppFst {d : ℕ} {c : (Fin (d + 1) →₀ ℕ) →₀ ℂ} {n : Fin (d + 1) →₀ ℕ}
    (hlex : LexMinF c n) {t : ℕ} (ht : t ∈ suppFst c) : n 0 ≤ t := by
  obtain ⟨hnmem, hnmin⟩ := hlex
  obtain ⟨m, hm, hm0⟩ := mem_suppFst.mp ht
  by_contra hcon
  rw [not_le] at hcon
  have hlt : toLex m < toLex n := by
    rw [Finsupp.Lex.lt_iff]
    simp only [ofLex_toLex]
    refine ⟨0, ?_, ?_⟩
    · intro j hj; exact absurd hj (by simp)
    · rw [hm0]; exact hcon
  have hle := hnmin m hm
  exact absurd (lt_of_lt_of_le hlt hle) (lt_irrefl _)

theorem slicePoly_eval_mul {d : ℕ} (c : (Fin (d + 1) →₀ ℕ) →₀ ℂ) (n : Fin (d + 1) →₀ ℕ)
    (hlex : LexMinF c n) (z : Fin d → ℂ) (w : ℂ) :
    w ^ (n 0) * (slicePoly c n z).eval w = pevalF c (consPt w z) := by
  rw [slicePoly_eval, pevalF_consPt, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro t ht
  have h : n 0 ≤ t := le_of_mem_suppFst hlex ht
  rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' h, mul_comm]

theorem slicePoly_eval_zero {d : ℕ} (c : (Fin (d + 1) →₀ ℕ) →₀ ℂ) (n : Fin (d + 1) →₀ ℕ)
    (hlex : LexMinF c n) (z : Fin d → ℂ) :
    (slicePoly c n z).eval 0 = pevalF (sliceF c (n 0)) z := by
  rw [slicePoly_eval]
  have hmem : n 0 ∈ suppFst c := mem_suppFst.mpr ⟨n, hlex.1, rfl⟩
  rw [Finset.sum_eq_single (n 0)]
  · simp
  · intro t ht hne
    have h : n 0 ≤ t := le_of_mem_suppFst hlex ht
    have hpos : 0 < t - n 0 := by omega
    rw [zero_pow (Nat.pos_iff_ne_zero.mp hpos), zero_mul]
  · intro h; exact absurd hmem h

/-- **The one-variable Jensen step.**  For a lex-minimal coefficient `c n` of the family `c`, the
value of the slice `pevalF (sliceF c (n 0))` at `z` is bounded by the circle average of the
one-variable function `w ↦ pevalF c (consPt w z)`. -/
theorem jensen_slice_step {d : ℕ} (c : (Fin (d + 1) →₀ ℕ) →₀ ℂ) {n : Fin (d + 1) →₀ ℕ}
    (hlex : LexMinF c n) (z : Fin d → ℂ) (hz : pevalF (sliceF c (n 0)) z ≠ 0) :
    Real.log ‖pevalF (sliceF c (n 0)) z‖
      ≤ ∫ u in (0 : ℝ)..1, Real.log ‖pevalF c (consPt (tor1 u) z)‖ := by
  have h0 : (slicePoly c n z).eval 0 ≠ 0 := by
    rw [slicePoly_eval_zero c n hlex z]; exact hz
  have hJ := jensen_mean_ineq (fun w : ℂ => (slicePoly c n z).eval w) 1 (by norm_num)
    (slicePoly_analytic c n z) h0
  rw [circleAverage_zero_one_eq_integral] at hJ
  rw [slicePoly_eval_zero c n hlex z] at hJ
  have hint : ∀ t : ℝ, Real.log ‖(slicePoly c n z).eval
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)))‖
      = Real.log ‖pevalF c (consPt (tor1 t) z)‖ := by
    intro t
    have h2 : ‖(slicePoly c n z).eval (tor1 t)‖ = ‖pevalF c (consPt (tor1 t) z)‖ := by
      have hmul := slicePoly_eval_mul c n hlex z (tor1 t)
      have hnorm : ‖tor1 t ^ (n 0)‖ = 1 := by rw [norm_pow, norm_tor1, one_pow]
      rw [← hmul, norm_mul, hnorm, one_mul]
    exact congrArg Real.log h2
  rw [show (∫ t in (0 : ℝ)..1, Real.log ‖(slicePoly c n z).eval
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)))‖)
      = ∫ t in (0 : ℝ)..1, Real.log ‖pevalF c (consPt (tor1 t) z)‖ from by
    apply intervalIntegral.integral_congr
    intro t _
    exact hint t] at hJ
  exact hJ




/-- The unit interval measure. -/
abbrev mvUnitMeas : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)

/-- The interval integral over `(0,1)` is the integral against the volume restricted to `Icc 0 1`. -/
theorem integral_interval_eq_restrict (f : ℝ → ℝ) :
    ∫ u in (0 : ℝ)..1, f u = ∫ u, f u ∂(volume.restrict (Set.Icc (0:ℝ) 1)) := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := volume) (a := (0:ℝ)) (b := 1))]

/-- **The homogeneous polynomial case** of the lex-minimal coefficient bound, by induction on the
number of variables (the `UDC` lexicographic induction). -/
theorem homog_poly_case : ∀ (d : ℕ) (c : (Fin d →₀ ℕ) →₀ ℂ) (D : ℕ) (n : Fin d →₀ ℕ),
    IsHomogF c D → LexMinF c n →
    Real.log ‖c n‖ ≤ ∫ s : Fin d → ℝ, Real.log ‖pevalF c (tor s)‖ ∂(torMeasure d) := by
  intro d
  induction d with
  | zero =>
    intro c D n hhom hlex
    have hn : n = 0 := Subsingleton.elim n 0
    subst hn
    have hpe : ∀ s : Fin 0 → ℝ, pevalF c (tor s) = c 0 := by
      intro s
      rw [pevalF, Finset.sum_eq_single 0]
      · simp
      · intro m hm hne; exact absurd (Subsingleton.elim m 0) hne
      · intro h0
        rw [Finsupp.notMem_support_iff] at h0
        simpa using h0
    simp only [hpe]
    rw [integral_const]
    have hUniv : (torMeasure 0) Set.univ = 1 := by
      rw [torMeasure, Measure.pi_univ]; simp
    rw [show (torMeasure 0).real Set.univ = 1 from by
      rw [MeasureTheory.Measure.real, hUniv]; rfl, one_smul]
  | succ d ih =>
    intro c D n hhom hlex
    have hcn_ne : c n ≠ 0 := Finsupp.mem_support_iff.mp hlex.1
    have hc_ne : c ≠ 0 := fun h => hcn_ne (by rw [h]; rfl)
    obtain ⟨hzero, hlexp⟩ := sliceF_lexMin c hlex
    have hhomp : IsHomogF (sliceF c (n 0)) (D - n 0) := isHomogF_sliceF c hhom hlex.1
    have ih' := ih (sliceF c (n 0)) (D - n 0) (tailIdx n) hhomp hlexp
    have hcn : sliceF c (n 0) (tailIdx n) = c n := by rw [sliceF_apply, consIdx_tailIdx]
    rw [hcn] at ih'
    refine le_trans ih' ?_
    have hcp_ne : sliceF c (n 0) ≠ 0 := by
      intro h
      have h2 : sliceF c (n 0) (tailIdx n) = 0 := by rw [h]; rfl
      rw [hcn] at h2
      exact hcn_ne h2
    -- integrability of the two sides
    have hIntL : Integrable
        (fun s : Fin d → ℝ => Real.log ‖pevalF (sliceF c (n 0)) (tor s)‖) (torMeasure d) :=
      mv_lex_log_poly_integrable _ hcp_ne
    have hIntJ : Integrable (fun t : Fin (d+1) → ℝ => Real.log ‖pevalF c (tor t)‖)
        (torMeasure (d+1)) := mv_lex_log_poly_integrable c hc_ne
    -- the pointwise (a.e.) Jensen inequality
    have hae : ∀ᵐ s ∂(torMeasure d), Real.log ‖pevalF (sliceF c (n 0)) (tor s)‖ ≤
        ∫ u in (0:ℝ)..1, Real.log ‖pevalF c (consPt (tor1 u) (tor s))‖ := by
      rw [MeasureTheory.ae_iff]
      refine MeasureTheory.measure_mono_null ?_ (mv_lex_null_zero _ hcp_ne)
      intro s hs
      simp only [Set.mem_setOf_eq] at hs ⊢
      by_contra hcon
      exact absurd (jensen_slice_step c hlex (tor s) hcon) hs
    -- integrability of the right-hand side
    let e : ℝ × (Fin d → ℝ) ≃ᵐ (Fin (d+1) → ℝ) :=
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).symm
    have he : ∀ (u : ℝ) (s : Fin d → ℝ), e (u,s) = Fin.cons u s := by
      intro u s
      funext i
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    have hmp : MeasurePreserving (⇑e) (mvUnitMeas.prod (torMeasure d)) (torMeasure (d+1)) :=
      (measurePreserving_piFinSuccAbove (fun _ : Fin (d+1) => mvUnitMeas) 0).symm
    have hJ : Integrable (fun p : ℝ × (Fin d → ℝ) =>
        Real.log ‖pevalF c (tor (Fin.cons p.1 p.2))‖) (mvUnitMeas.prod (torMeasure d)) := by
      refine (hmp.integrable_comp_of_integrable hIntJ).congr ?_
      filter_upwards with p
      rw [Function.comp_apply, he]
    have hJ2 : Integrable (fun p : ℝ × (Fin d → ℝ) =>
        Real.log ‖pevalF c (consPt (tor1 p.1) (tor p.2))‖) (mvUnitMeas.prod (torMeasure d)) := by
      refine hJ.congr ?_
      filter_upwards with p
      rw [tor_cons]
    have hIntR' : Integrable (fun s : Fin d → ℝ =>
        ∫ u, Real.log ‖pevalF c (consPt (tor1 u) (tor s))‖ ∂mvUnitMeas) (torMeasure d) :=
      hJ2.integral_prod_right
    have hIntR : Integrable (fun s : Fin d → ℝ =>
        ∫ u in (0:ℝ)..1, Real.log ‖pevalF c (consPt (tor1 u) (tor s))‖) (torMeasure d) := by
      refine hIntR'.congr ?_
      filter_upwards with s
      exact (integral_interval_eq_restrict _).symm
    have hmono := integral_mono_ae hIntL hIntR hae
    -- identify the two sides
    have hjoint : Integrable (Function.uncurry (fun s : Fin d → ℝ => fun u : ℝ =>
        Real.log ‖pevalF c (consPt (tor1 u) (tor s))‖)) ((torMeasure d).prod mvUnitMeas) := by
      have hswap : MeasurePreserving (⇑(MeasurableEquiv.prodComm :
          (Fin d → ℝ) × ℝ ≃ᵐ ℝ × (Fin d → ℝ))) ((torMeasure d).prod mvUnitMeas)
          (mvUnitMeas.prod (torMeasure d)) := by
        refine ⟨MeasurableEquiv.prodComm.measurable, ?_⟩
        simpa [MeasurableEquiv.prodComm] using Measure.prod_swap (μ := torMeasure d) (ν := mvUnitMeas)
      exact hswap.integrable_comp_of_integrable hJ2
    have hconv : (∫ s : Fin d → ℝ, (∫ u in (0:ℝ)..1,
          Real.log ‖pevalF c (consPt (tor1 u) (tor s))‖) ∂(torMeasure d))
        = ∫ t : Fin (d+1) → ℝ, Real.log ‖pevalF c (tor t)‖ ∂(torMeasure (d+1)) := by
      rw [show (∫ s : Fin d → ℝ, (∫ u in (0:ℝ)..1,
            Real.log ‖pevalF c (consPt (tor1 u) (tor s))‖) ∂(torMeasure d))
          = ∫ s : Fin d → ℝ, (∫ u, Real.log ‖pevalF c (consPt (tor1 u) (tor s))‖ ∂mvUnitMeas)
              ∂(torMeasure d) from by
        apply integral_congr_ae
        filter_upwards with s
        exact integral_interval_eq_restrict _]
      rw [integral_integral_swap hjoint]
      rw [pi_integral_cons mvUnitMeas (fun t : Fin (d+1) → ℝ => Real.log ‖pevalF c (tor t)‖) hIntJ]
      apply integral_congr_ae
      filter_upwards with u
      apply integral_congr_ae
      filter_upwards with s
      rw [tor_cons]
    exact le_of_le_of_eq hmono hconv




/-- The degree-`k` part of a finitely supported coefficient family. -/
def degPartF {d : ℕ} (c : (Fin d →₀ ℕ) →₀ ℂ) (k : ℕ) : (Fin d →₀ ℕ) →₀ ℂ :=
  ∑ m ∈ c.support.filter (fun m => m.degree = k), Finsupp.single m (c m)

/-- The set of total degrees occurring in the support of `c`. -/
def degSuppF {d : ℕ} (c : (Fin d →₀ ℕ) →₀ ℂ) : Finset ℕ := c.support.image (fun m => m.degree)

theorem degSuppF_mem {d : ℕ} {c : (Fin d →₀ ℕ) →₀ ℂ} {k : ℕ} :
    k ∈ degSuppF c ↔ ∃ m ∈ c.support, m.degree = k := by
  simp [degSuppF]

theorem degPartF_apply {d : ℕ} (c : (Fin d →₀ ℕ) →₀ ℂ) (k : ℕ) (m : Fin d →₀ ℕ) :
    degPartF c k m = if m.degree = k then c m else 0 := by
  classical
  rw [degPartF, Finsupp.finsetSum_apply]
  by_cases hk : m.degree = k
  · rw [if_pos hk, Finset.sum_eq_single m]
    · simp
    · intro m' _ hne
      exact Finsupp.single_eq_of_ne (Ne.symm hne)
    · intro hm
      rw [Finset.mem_filter] at hm
      rw [Finsupp.single_eq_same, Finsupp.notMem_support_iff.mp (fun hc => hm ⟨hc, hk⟩)]
  · rw [if_neg hk]
    refine Finset.sum_eq_zero fun m' hm' => ?_
    rw [Finset.mem_filter] at hm'
    exact Finsupp.single_eq_of_ne (fun h => hk (h ▸ hm'.2))

theorem isHomogF_degPartF {d : ℕ} (c : (Fin d →₀ ℕ) →₀ ℂ) (k : ℕ) :
    IsHomogF (degPartF c k) k := by
  intro m hm
  rw [Finsupp.mem_support_iff] at hm
  rw [degPartF_apply] at hm
  by_cases h : m.degree = k
  · exact h
  · rw [if_neg h] at hm
    exact absurd rfl hm

theorem support_degPartF {d : ℕ} (c : (Fin d →₀ ℕ) →₀ ℂ) (k : ℕ) :
    (degPartF c k).support = c.support.filter (fun m => m.degree = k) := by
  ext m
  rw [Finsupp.mem_support_iff, degPartF_apply, Finset.mem_filter, Finsupp.mem_support_iff]
  constructor
  · intro h
    by_cases hk : m.degree = k
    · exact ⟨by rwa [if_pos hk] at h, hk⟩
    · rw [if_neg hk] at h; exact absurd rfl h
  · rintro ⟨hc, hk⟩
    rwa [if_pos hk]

theorem pevalF_degPartF {d : ℕ} (c : (Fin d →₀ ℕ) →₀ ℂ) (k : ℕ) (z : Fin d → ℂ) :
    pevalF (degPartF c k) z
      = ∑ m ∈ c.support.filter (fun m => m.degree = k), c m * ∏ j, z j ^ (m j) := by
  rw [pevalF, support_degPartF]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_filter] at hm
  rw [degPartF_apply, if_pos hm.2]

theorem pevalF_smul {d : ℕ} (c : (Fin d →₀ ℕ) →₀ ℂ) (w : ℂ) (z : Fin d → ℂ) :
    pevalF c (fun j => w * z j) = ∑ t ∈ degSuppF c, w ^ t * pevalF (degPartF c t) z := by
  have hL : pevalF c (fun j => w * z j)
      = ∑ m ∈ c.support, w ^ m.degree * (c m * ∏ j, z j ^ (m j)) := by
    rw [pevalF]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp_rw [mul_pow]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finsupp.degree_eq_sum]
    ring
  have hR : (∑ t ∈ degSuppF c, w ^ t * pevalF (degPartF c t) z)
      = ∑ t ∈ degSuppF c, ∑ m ∈ c.support.filter (fun m => m.degree = t),
          w ^ m.degree * (c m * ∏ j, z j ^ (m j)) := by
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [pevalF_degPartF, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_filter] at hm
    rw [hm.2]
  have hfib : (∑ t ∈ degSuppF c, ∑ m ∈ c.support.filter (fun m => m.degree = t),
        w ^ m.degree * (c m * ∏ j, z j ^ (m j)))
      = ∑ m ∈ c.support, w ^ m.degree * (c m * ∏ j, z j ^ (m j)) :=
    Finset.sum_fiberwise_of_maps_to (fun x hx => degSuppF_mem.mpr ⟨x, hx, rfl⟩) _
  rw [hL, hR, ← hfib]

/-- `tor1 u • tor s = tor (s + u)`. -/
theorem tor_smul {d : ℕ} (u : ℝ) (s : Fin d → ℝ) :
    (fun j => tor1 u * (tor s) j) = tor (fun j => s j + u) := by
  funext j
  simp only [tor, tor1, Pi.mul_apply]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `tor` is unchanged by adding `1` to a coordinate. -/
theorem tor_update_one {d : ℕ} (s : Fin d → ℝ) (j : Fin d) :
    tor (Function.update s j (s j + 1)) = tor s := by
  funext j'
  by_cases h : j' = j
  · subst h
    simp only [tor, Function.update_self]
    rw [Complex.exp_eq_exp_iff_exists_int]
    exact ⟨1, by push_cast; ring⟩
  · simp only [tor, Function.update_of_ne h]

/-- The one-variable polynomial `w ↦ w^{-D}·pevalF c (w • z)`. -/
def degPoly {d : ℕ} (c : (Fin d →₀ ℕ) →₀ ℂ) (D : ℕ) (z : Fin d → ℂ) : Polynomial ℂ :=
  ∑ t ∈ degSuppF c, Polynomial.C (pevalF (degPartF c t) z) * Polynomial.X ^ (t - D)

theorem degPoly_eval {d : ℕ} (c : (Fin d →₀ ℕ) →₀ ℂ) (D : ℕ) (z : Fin d → ℂ) (w : ℂ) :
    (degPoly c D z).eval w = ∑ t ∈ degSuppF c, w ^ (t - D) * pevalF (degPartF c t) z := by
  rw [degPoly, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  ring

theorem degPoly_analytic {d : ℕ} (c : (Fin d →₀ ℕ) →₀ ℂ) (D : ℕ) (z : Fin d → ℂ) :
    AnalyticOnNhd ℂ (fun w : ℂ => (degPoly c D z).eval w) (Metric.closedBall 0 1) := by
  have hd : DifferentiableOn ℂ (fun w : ℂ => (degPoly c D z).eval w) (Metric.ball 0 2) :=
    ((Polynomial.differentiable (degPoly c D z)).differentiableOn)
  exact (hd.analyticOnNhd (Metric.isOpen_ball)).mono
    (Metric.closedBall_subset_ball (by norm_num))

theorem degPoly_eval_zero {d : ℕ} (c : (Fin d →₀ ℕ) →₀ ℂ) (D : ℕ) (z : Fin d → ℂ)
    (hDle : ∀ t ∈ degSuppF c, D ≤ t) (hD : D ∈ degSuppF c) :
    (degPoly c D z).eval 0 = pevalF (degPartF c D) z := by
  rw [degPoly_eval]
  rw [Finset.sum_eq_single D]
  · simp
  · intro t ht hne
    have h := hDle t ht
    have hpos : 0 < t - D := by omega
    rw [zero_pow (Nat.pos_iff_ne_zero.mp hpos), zero_mul]
  · intro h; exact absurd hD h

theorem degPoly_mul {d : ℕ} (c : (Fin d →₀ ℕ) →₀ ℂ) (D : ℕ) (z : Fin d → ℂ)
    (hDle : ∀ t ∈ degSuppF c, D ≤ t) (w : ℂ) :
    w ^ D * (degPoly c D z).eval w = pevalF c (fun j => w * z j) := by
  rw [degPoly_eval, pevalF_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have h := hDle t ht
  rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' h, mul_comm]

theorem jensen_diag_step {d : ℕ} (c : (Fin d →₀ ℕ) →₀ ℂ) {D : ℕ}
    (hDle : ∀ t ∈ degSuppF c, D ≤ t) (hD : D ∈ degSuppF c)
    (z : Fin d → ℂ) (hz : pevalF (degPartF c D) z ≠ 0) :
    Real.log ‖pevalF (degPartF c D) z‖
      ≤ ∫ u in (0 : ℝ)..1, Real.log ‖pevalF c (fun j => tor1 u * z j)‖ := by
  have h0 : (degPoly c D z).eval 0 ≠ 0 := by
    rw [degPoly_eval_zero c D z hDle hD]; exact hz
  have hJ := jensen_mean_ineq (fun w : ℂ => (degPoly c D z).eval w) 1 (by norm_num)
    (degPoly_analytic c D z) h0
  rw [circleAverage_zero_one_eq_integral] at hJ
  rw [degPoly_eval_zero c D z hDle hD] at hJ
  have hint : ∀ t : ℝ, Real.log ‖(degPoly c D z).eval
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)))‖
      = Real.log ‖pevalF c (fun j => tor1 t * z j)‖ := by
    intro t
    have h2 : ‖(degPoly c D z).eval (tor1 t)‖
        = ‖pevalF c (fun j => tor1 t * z j)‖ := by
      have hmul := degPoly_mul c D z hDle (tor1 t)
      have hnorm : ‖tor1 t ^ D‖ = 1 := by rw [norm_pow, norm_tor1, one_pow]
      rw [← hmul, norm_mul, hnorm, one_mul]
    exact congrArg Real.log h2
  rw [show (∫ t in (0 : ℝ)..1, Real.log ‖(degPoly c D z).eval
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)))‖)
      = ∫ t in (0 : ℝ)..1, Real.log ‖pevalF c (fun j => tor1 t * z j)‖ from by
    apply intervalIntegral.integral_congr
    intro t _
    exact hint t] at hJ
  exact hJ

/-- **The polynomial case** (inhomogeneous): the lex-minimal coefficient of a finitely supported
family is bounded by the torus integral of its evaluation.  This reduces the general case to the
homogeneous case (`homog_poly_case`) via the diagonal substitution `z ↦ w z` and Jensen's formula
applied to the one-variable polynomial `w ↦ w^{-D} pevalF c (w • z)`. -/
theorem poly_case {d : ℕ} (c : (Fin d →₀ ℕ) →₀ ℂ) {D : ℕ}
    (hmin : ∀ m ∈ c.support, D ≤ m.degree) {n : Fin d →₀ ℕ} (hn : n ∈ c.support)
    (hndeg : n.degree = D) (hlex : ∀ m ∈ c.support, m.degree = D → toLex n ≤ toLex m) :
    Real.log ‖c n‖ ≤ ∫ s : Fin d → ℝ, Real.log ‖pevalF c (tor s)‖ ∂(torMeasure d) := by
  have hcn_ne : c n ≠ 0 := Finsupp.mem_support_iff.mp hn
  have hc_ne : c ≠ 0 := fun h => hcn_ne (by rw [h]; rfl)
  have hhomD : IsHomogF (degPartF c D) D := isHomogF_degPartF c D
  have hnD : degPartF c D n = c n := by rw [degPartF_apply, if_pos hndeg]
  have hmemD : n ∈ (degPartF c D).support := by
    rw [Finsupp.mem_support_iff, hnD]; exact hcn_ne
  have hlexD : LexMinF (degPartF c D) n := by
    refine ⟨hmemD, ?_⟩
    intro m hm
    rw [Finsupp.mem_support_iff] at hm
    rw [degPartF_apply] at hm
    by_cases hmd : m.degree = D
    · have hmc : c m ≠ 0 := by rwa [if_pos hmd] at hm
      exact hlex m (Finsupp.mem_support_iff.mpr hmc) hmd
    · rw [if_neg hmd] at hm; exact absurd rfl hm
  have h1 := homog_poly_case d (degPartF c D) D n hhomD hlexD
  rw [hnD] at h1
  refine le_trans h1 ?_
  -- diagonal reduction
  have hDmem : D ∈ degSuppF c := degSuppF_mem.mpr ⟨n, hn, hndeg⟩
  have hDle : ∀ t ∈ degSuppF c, D ≤ t := by
    intro t ht
    obtain ⟨m, hm, hmd⟩ := degSuppF_mem.mp ht
    rw [← hmd]; exact hmin m hm
  have hcp_ne : degPartF c D ≠ 0 := by
    intro h
    have h2 : degPartF c D n = 0 := by rw [h]; rfl
    rw [hnD] at h2; exact hcn_ne h2
  have hae : ∀ᵐ s ∂(torMeasure d), Real.log ‖pevalF (degPartF c D) (tor s)‖ ≤
      ∫ u in (0:ℝ)..1, Real.log ‖pevalF c (fun j => tor1 u * (tor s) j)‖ := by
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (mv_lex_null_zero _ hcp_ne)
    intro s hs
    simp only [Set.mem_ofPred_eq] at hs ⊢
    by_contra hcon
    exact absurd (jensen_diag_step c hDle hDmem (tor s) hcon) hs
  have hIntL : Integrable
      (fun s : Fin d → ℝ => Real.log ‖pevalF (degPartF c D) (tor s)‖) (torMeasure d) :=
    mv_lex_log_poly_integrable _ hcp_ne
  have hper : ∀ (s : Fin d → ℝ) (j : Fin d),
      (fun s : Fin d → ℝ => Real.log ‖pevalF c (tor s)‖) (Function.update s j (s j + 1))
        = (fun s : Fin d → ℝ => Real.log ‖pevalF c (tor s)‖) s := by
    intro s j
    simp only
    rw [tor_update_one]
  have hfInt : Integrable (fun s : Fin d → ℝ => Real.log ‖pevalF c (tor s)‖) (torMeasure d) :=
    mv_lex_log_poly_integrable c hc_ne
  have hdiag := diag_slice_identity (fun s : Fin d → ℝ => Real.log ‖pevalF c (tor s)‖) hper hfInt
  have hIntR : Integrable (fun s : Fin d → ℝ =>
      ∫ u in (0:ℝ)..1, Real.log ‖pevalF c (fun j => tor1 u * (tor s) j)‖) (torMeasure d) := by
    refine hdiag.1.congr ?_
    filter_upwards with s
    apply intervalIntegral.integral_congr
    intro u _
    simp only
    rw [tor_smul]
  have hmono := integral_mono_ae hIntL hIntR hae
  have hconv : (∫ s : Fin d → ℝ,
        (∫ u in (0:ℝ)..1, Real.log ‖pevalF c (fun j => tor1 u * (tor s) j)‖)
        ∂(torMeasure d)) = ∫ s, Real.log ‖pevalF c (tor s)‖ ∂(torMeasure d) := by
    have key : (fun s : Fin d → ℝ =>
          ∫ u in (0:ℝ)..1, Real.log ‖pevalF c (fun j => tor1 u * (tor s) j)‖)
        =ᵐ[torMeasure d] (fun s : Fin d → ℝ =>
          ∫ u in (0:ℝ)..1, (fun s : Fin d → ℝ => Real.log ‖pevalF c (tor s)‖)
            (fun j => s j + u)) := by
      filter_upwards with s
      apply intervalIntegral.integral_congr
      intro u _
      simp only
      rw [tor_smul]
    rw [integral_congr_ae key, hdiag.2]
  exact le_of_le_of_eq hmono hconv


/-- The lexicographic disjunction appearing in `mv_lexmin_coeff_le_integral` is the relation
`toLex n ≤ toLex m` on the lexicographic order of `Fin d →₀ ℕ` (first coordinate most
significant). -/
theorem toLex_le_iff {d : ℕ} {m n : Fin d →₀ ℕ} :
    toLex n ≤ toLex m ↔
      m = n ∨ ∃ j : Fin d, (∀ i : Fin d, i < j → m i = n i) ∧ n j < m j := by
  rw [le_iff_lt_or_eq, Finsupp.Lex.lt_iff]
  simp only [ofLex_toLex]
  constructor
  · rintro (⟨j, hj, hlt⟩ | h)
    · exact Or.inr ⟨j, fun i hi => (hj i hi).symm, hlt⟩
    · exact Or.inl (by have h' := congrArg ofLex h; simpa using h'.symm)
  · rintro (rfl | ⟨j, hj, hlt⟩)
    · exact Or.inr rfl
    · exact Or.inl ⟨j, fun i hi => (hj i hi).symm, hlt⟩

theorem mv_lexmin_coeff_le_integral {d : ℕ} (g : MvPowerSeries (Fin d) ℂ) (G : (Fin d → ℂ) → ℂ)
    (ρ : ℝ) (hρ : 1 < ρ)
    (hG : ∀ z : Fin d → ℂ, (∀ j, ‖z j‖ ≤ ρ) →
      HasSum (fun m : Fin d →₀ ℕ => MvPowerSeries.coeff m g * ∏ j, (z j) ^ (m j)) (G z))
    (n : Fin d →₀ ℕ) (hn : MvPowerSeries.coeff n g ≠ 0)
    (hmin : ∀ m : Fin d →₀ ℕ, m.degree < n.degree → MvPowerSeries.coeff m g = 0)
    (hlex : ∀ m : Fin d →₀ ℕ, m.degree = n.degree → MvPowerSeries.coeff m g ≠ 0 →
      m = n ∨ ∃ j : Fin d, (∀ i : Fin d, i < j → m i = n i) ∧ n j < m j) :
    Real.log ‖MvPowerSeries.coeff n g‖ ≤
      ∫ t : Fin d → ℝ,
        Real.log ‖G (fun j => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t j : ℂ)))‖
        ∂(MeasureTheory.Measure.pi (fun _ : Fin d =>
            MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1))) := by
  have hpoly : ∀ (c : (Fin d →₀ ℕ) →₀ ℂ) (D : ℕ) (n : Fin d →₀ ℕ),
      (∀ m ∈ c.support, D ≤ m.degree) → n ∈ c.support → n.degree = D →
      (∀ m ∈ c.support, m.degree = D → toLex n ≤ toLex m) →
      Real.log ‖c n‖ ≤ ∫ s : Fin d → ℝ, Real.log ‖pevalF c (tor s)‖ ∂(torMeasure d) :=
    fun c D n hmin' hn' hdeg hlex' => poly_case c hmin' hn' hdeg hlex'
  exact mv_lex_general_case g G hρ hG hpoly mv_lex_log_poly_integrable hn hmin hlex

end

end Work.Holonomy3

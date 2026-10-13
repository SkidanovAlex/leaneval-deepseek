import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.AngAWeak.AngWeakDefs
import Submission.Work.FTS.EllipticEst.AngAWeak.SliceGronwallDefs
import Submission.Work.FTS.EllipticEst.AngAWeak.sliceGronwallInterface
import Submission.Work.FTS.EllipticEst.AngAWeak.sliceGronwallPointwise
import Submission.Work.FTS.EllipticEst.AngAWeak.sliceLipschitzLeft
import Submission.Work.FTS.EllipticEst.AngAWeak.gronwallIntegralOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter intervalIntegral

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false

/-! ### Local copies of the transfer and Gronwall steps

`sliceLimLeft.lean` and `sliceGronwallLeft.lean` contain the proofs we need, but the latter does
not elaborate (it uses `sliceGronwallInterface` / `sliceGronwallPointwise` / `gronwallIntegralOn`
without importing them), so `sliceLimLeft` is unusable too.  The steps are reproduced here with
local names, importing the three building ingredients directly. -/

/-- `Iθ` agrees a.e. with the open interval. -/
lemma cr_Iθ_ae_eq : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have hpair : volume ({(0 : ℝ), Real.pi / 2} : Set ℝ) = 0 :=
    Set.Finite.measure_zero (by simp) volume
  have hpairab : ∀ᵐ x : ℝ, x ∉ ({(0 : ℝ), Real.pi / 2} : Set ℝ) := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hpair
  filter_upwards [hpairab] with x hx
  refine propext ⟨?_, ?_⟩
  · intro h
    rw [Work.Spaces.Iθ, Set.mem_Icc] at h
    rw [Set.mem_Ioo]
    exact ⟨lt_of_le_of_ne h.1 (fun hc => hx (Or.inl hc.symm)),
           lt_of_le_of_ne h.2 (fun hc => hx (Or.inr hc))⟩
  · intro h
    rw [Work.Spaces.Iθ, Set.mem_Icc]
    rw [Set.mem_Ioo] at h
    exact ⟨le_of_lt h.1, le_of_lt h.2⟩

lemma cr_aesm_Lzero1_sq (u : ℝ → ℝ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    MeasureTheory.AEStronglyMeasurable (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
  have hu : MeasureTheory.AEStronglyMeasurable u
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (hsm 0).continuousOn.aestronglyMeasurable measurableSet_Ioo
  have hd1 : MeasureTheory.AEStronglyMeasurable (fun θ => deriv (fun t => deriv u t) θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (measurable_deriv (fun t => deriv u t)).aestronglyMeasurable
  have hd2 : MeasureTheory.AEStronglyMeasurable (fun θ => deriv (fun t => Real.tan t * u t) θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (measurable_deriv (fun t => Real.tan t * u t)).aestronglyMeasurable
  have h : MeasureTheory.AEStronglyMeasurable
      (fun θ => -deriv (fun t => deriv u t) θ + deriv (fun t => Real.tan t * u t) θ
        - 6 * u θ) (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (hd1.neg.add hd2).sub (hu.const_mul 6)
  have hL : MeasureTheory.AEStronglyMeasurable (fun θ => Work.FTS.EllipticEst.Lzero1 u θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    simpa only [Work.FTS.EllipticEst.Lzero1] using h
  convert hL.pow 2 using 1

/-- Transfer: `(Lzero1 u)²·wq` integrable on `Iθ` gives `(Lzero1 u)²` integrable on
`(0, π/4)`. -/
lemma cr_integrableOn_Lzero1_sq {q : ℝ} (hq0 : 0 < q) (u : ℝ → ℝ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hg : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * wq q θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 4)) := by
  have hms : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set cr_Iθ_ae_eq
  have hg' : MeasureTheory.Integrable
      (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * wq q θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    rw [← hms]; exact hg
  have hsq : MeasureTheory.Integrable
      (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    refine hg'.mono' (cr_aesm_Lzero1_sq u hsm) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have h1 : 1 ≤ wq q θ := one_le_wq hq0 hθ
    have hsq0 : 0 ≤ (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 := sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hsq0]
    simpa using mul_le_mul_of_nonneg_left h1 hsq0
  have hsqOn : MeasureTheory.IntegrableOn (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hsq
  exact hsqOn.mono_set (Set.Ioo_subset_Ioo_right (by linarith [Real.pi_pos]))

/-- A nonnegative function has monotone interval integrals: for `a ≤ x ≤ b`,
`∫_x^b ψ ≤ ∫_a^b ψ`. -/
lemma cr_intervalIntegral_le_of_nonneg_of_Ioo {ψ : ℝ → ℝ} {a b x : ℝ} (hxa : a ≤ x)
    (hxb : x ≤ b) (hψi : IntegrableOn ψ (Set.Ioo a b))
    (hψnn : ∀ y ∈ Set.Ioo a b, 0 ≤ ψ y) :
    ∫ s in x..b, ψ s ≤ ∫ s in a..b, ψ s := by
  have hIcc : IntegrableOn ψ (Set.Icc a b) :=
    hψi.congr_set_ae MeasureTheory.Ioo_ae_eq_Icc.symm
  have hax : IntegrableOn ψ (Set.uIcc a x) := by
    rw [Set.uIcc_of_le hxa]
    exact hIcc.mono_set (Set.Icc_subset_Icc le_rfl hxb)
  have hxb' : IntegrableOn ψ (Set.uIcc x b) := by
    rw [Set.uIcc_of_le hxb]
    exact hIcc.mono_set (Set.Icc_subset_Icc hxa le_rfl)
  have haxi : IntervalIntegrable ψ volume a x := hax.intervalIntegrable
  have hxbi : IntervalIntegrable ψ volume x b := hxb'.intervalIntegrable
  have hnn : (0 : ℝ) ≤ ∫ s in a..x, ψ s := by
    have h0 : (∫ s in a..x, (0 : ℝ)) ≤ ∫ s in a..x, ψ s :=
      integral_mono_on_of_le_Ioo hxa intervalIntegrable_const haxi
        (fun y hy => hψnn y ⟨hy.1, lt_of_lt_of_le hy.2 hxb⟩)
    simpa using h0
  have hadj := intervalIntegral.integral_add_adjacent_intervals haxi hxbi
  linarith

/-- **Gronwall on the left quarter.**  A `C^∞` slice on `(0, π/2)` whose `Lzero1` is
square-integrable on `(0, π/4)` is bounded there together with its derivative. -/
theorem corr_gronwall_left (u : ℝ → ℝ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hg : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 4))) :
    ∃ M : ℝ, 0 < M ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      |u θ| ≤ M ∧ |deriv u θ| ≤ M := by
  set B : ℝ := Real.exp (8 * (Real.pi / 4)) *
    (Fsq u (Real.pi / 4) + ∫ s in (0 : ℝ)..(Real.pi / 4),
      (Work.FTS.EllipticEst.Lzero1 u s) ^ 2) with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    have h1 : 0 ≤ Fsq u (Real.pi / 4) := Fsq_nonneg u _
    have h2 : 0 ≤ ∫ s in (0 : ℝ)..(Real.pi / 4),
        (Work.FTS.EllipticEst.Lzero1 u s) ^ 2 :=
      intervalIntegral.integral_nonneg (by positivity)
        (fun s _ => by positivity)
    positivity
  refine ⟨Real.sqrt B + 1, by positivity, ?_⟩
  intro θ hθ
  have hθlt : θ < Real.pi / 4 := hθ.2
  have hθpos : 0 < θ := hθ.1
  have hπ : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  -- the smoothness interface on the closed slice
  obtain ⟨hφc, hφdc, hφd⟩ :=
    sliceGronwallInterface u hsm hθ
  -- the pointwise differential inequality
  have hpt : ∀ x ∈ Set.Ioo θ (Real.pi / 4),
      -(8 * Fsq u x + (Work.FTS.EllipticEst.Lzero1 u x) ^ 2) ≤ deriv (Fsq u) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 4) :=
      ⟨lt_trans hθpos hx.1, hx.2⟩
    have h := sliceGronwallPointwise u hsm hx'
    linarith [neg_le_abs (deriv (Fsq u) x), h]
  -- integrability of the source on the slice
  have hψint : IntegrableOn (fun s => (Work.FTS.EllipticEst.Lzero1 u s) ^ 2)
      (Set.Ioo θ (Real.pi / 4)) :=
    hg.mono_set (fun y hy => ⟨lt_trans hθpos hy.1, hy.2⟩)
  have hψi : IntervalIntegrable (fun s => (Work.FTS.EllipticEst.Lzero1 u s) ^ 2)
      volume θ (Real.pi / 4) := by
    have h : IntegrableOn (fun s => (Work.FTS.EllipticEst.Lzero1 u s) ^ 2)
        (Set.uIcc θ (Real.pi / 4)) := by
      rw [Set.uIcc_of_le hθlt.le]
      exact hψint.congr_set_ae MeasureTheory.Ioo_ae_eq_Icc.symm
    exact h.intervalIntegrable
  have hψnn : ∀ x ∈ Set.Ioo θ (Real.pi / 4),
      0 ≤ (Work.FTS.EllipticEst.Lzero1 u x) ^ 2 := fun x _ => by positivity
  have hφnn : ∀ x ∈ Set.Icc θ (Real.pi / 4), 0 ≤ Fsq u x := fun x _ => Fsq_nonneg u x
  -- Gronwall
  have hgr := gronwallIntegralOn (φ := Fsq u)
    (ψ := fun s => (Work.FTS.EllipticEst.Lzero1 u s) ^ 2) (C := 8)
    hθlt.le (by norm_num) hφnn hψi hψnn hφc hφd hφdc hpt θ ⟨le_rfl, hθlt.le⟩
  -- comparison of the tail integral with the full one
  have htail : ∫ s in θ..Real.pi / 4, (Work.FTS.EllipticEst.Lzero1 u s) ^ 2
      ≤ ∫ s in (0 : ℝ)..Real.pi / 4, (Work.FTS.EllipticEst.Lzero1 u s) ^ 2 :=
    cr_intervalIntegral_le_of_nonneg_of_Ioo hθpos.le hθlt.le hg
      (fun y _ => by positivity)
  have htailnn : 0 ≤ ∫ s in θ..Real.pi / 4, (Work.FTS.EllipticEst.Lzero1 u s) ^ 2 :=
    intervalIntegral.integral_nonneg hθlt.le (fun s _ => by positivity)
  have hB : Fsq u θ ≤ B := by
    rw [hBdef]
    have hsum : Fsq u (Real.pi / 4) + ∫ s in θ..Real.pi / 4,
          (Work.FTS.EllipticEst.Lzero1 u s) ^ 2
        ≤ Fsq u (Real.pi / 4) + ∫ s in (0 : ℝ)..Real.pi / 4,
          (Work.FTS.EllipticEst.Lzero1 u s) ^ 2 := by linarith
    calc Fsq u θ
        ≤ Real.exp (8 * (Real.pi / 4 - θ)) *
            (Fsq u (Real.pi / 4) + ∫ s in θ..Real.pi / 4,
              (Work.FTS.EllipticEst.Lzero1 u s) ^ 2) := hgr
      _ ≤ Real.exp (8 * (Real.pi / 4)) *
            (Fsq u (Real.pi / 4) + ∫ s in θ..Real.pi / 4,
              (Work.FTS.EllipticEst.Lzero1 u s) ^ 2) := by
          apply mul_le_mul_of_nonneg_right _
            (by linarith [Fsq_nonneg u (Real.pi / 4), htailnn])
          rw [Real.exp_le_exp]
          linarith
      _ ≤ Real.exp (8 * (Real.pi / 4)) *
            (Fsq u (Real.pi / 4) + ∫ s in (0 : ℝ)..Real.pi / 4,
              (Work.FTS.EllipticEst.Lzero1 u s) ^ 2) := by
          apply mul_le_mul_of_nonneg_left hsum (by positivity)
  have hu2 : (u θ) ^ 2 ≤ B := le_trans (sq_le_Fsq_left u θ) hB
  have hd2 : (deriv u θ) ^ 2 ≤ B := le_trans (sq_le_Fsq_right u θ) hB
  constructor
  · calc |u θ| = Real.sqrt ((u θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt B := Real.sqrt_le_sqrt hu2
      _ ≤ Real.sqrt B + 1 := by linarith
  · calc |deriv u θ| = Real.sqrt ((deriv u θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt B := Real.sqrt_le_sqrt hd2
      _ ≤ Real.sqrt B + 1 := by linarith

/-- Left-endpoint rate of a weak slice (piece of `Work.FTS.EllipticEst.AngAWeak.corrSlice_limits`).

`u` is `C^∞` on `(0, π/2)`, `u²·wq q` and `(Lzero1 u)²·wq q` are integrable on `Iθ` with
`0 < q < 1`, and `u → L` at `0⁺`.  Conclusion: on `(0, π/8)` the slice approaches its limit at
least linearly, `|u θ - L| ≤ M θ`, and both `u` and `deriv u` are bounded by `M`.

Route (readable in this workspace; `sliceLimLeft.lean` proves the same thing with an
unspecified limit `L'`): (1) transfer the weighted integrability to
`IntegrableOn ((Lzero1 u)²) (Ioo 0 (π/4))` (proof template: `sll_integrableOn_Lzero1_sq` in
`sliceLimLeft.lean`); (2) the Gronwall estimate on `Fsq u = u² + (deriv u)²` gives `|u| ≤ M`,
`|deriv u| ≤ M` on `(0, π/4)` (`sliceGronwallLeft`, which uses `sliceGronwallInterface` and
`sliceGronwallPointwise`); (3) `|u θ - L| ≤ M θ` from the mean value inequality and `t → 0⁺`
(`sliceLipschitzLeft` gives the two-sided limit; identify it with `L` by uniqueness of limits).

CAUTION: `Submission/Work/FTS/EllipticEst/AngAWeak/sliceGronwallLeft.lean` currently does NOT
elaborate (it uses `sliceGronwallInterface` without importing
`Submission.Work.FTS.EllipticEst.AngAWeak.sliceGronwallInterface`).  Do not import
`sliceGronwallLeft` / `sliceLimLeft`; import `sliceGronwallInterface`,
`sliceGronwallPointwise`, `sliceLipschitzLeft`, `SliceGronwallDefs` directly (they build). -/

theorem corrLeftRate (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) {u : ℝ → ℝ} {L : ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (hu2 : MeasureTheory.IntegrableOn
      (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.AngAWeak.wq q θ) Work.Spaces.Iθ)
    (hLu2 : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2
        * Work.FTS.EllipticEst.AngAWeak.wq q θ) Work.Spaces.Iθ)
    (hL : Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) :
    ∃ M : ℝ, 0 < M ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 8),
      |u θ - L| ≤ M * θ ∧ |u θ| ≤ M ∧ |deriv u θ| ≤ M := by
  have hsq : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
    cr_integrableOn_Lzero1_sq hq0 u hsm hLu2
  obtain ⟨M₁, hM₁pos, hM₁⟩ := corr_gronwall_left u hsm hsq
  have hder : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 4), HasDerivAt u (deriv u x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨hx.1, lt_of_lt_of_le hx.2 (by linarith [Real.pi_pos])⟩
    exact (((hsm 1).contDiffAt (isOpen_Ioo.mem_nhds hx')).differentiableAt
      (by norm_num)).hasDerivAt
  have hbd : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 4), |deriv u x| ≤ M₁ :=
    fun x hx => (hM₁ x hx).2
  obtain ⟨L', hL'tend, hL'bd⟩ := sliceLipschitzLeft u M₁ hder hbd
  -- the two limits coincide
  haveI : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := nhdsWithin_Ioi_neBot (le_refl (0 : ℝ))
  have hL'eq : L' = L := tendsto_nhds_unique hL'tend hL
  rw [hL'eq] at hL'bd
  refine ⟨max M₁ 1, ?_, ?_⟩
  · exact lt_of_lt_of_le hM₁pos (le_max_left _ _)
  · intro θ hθ
    have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4) :=
      ⟨hθ.1, lt_of_lt_of_le hθ.2 (by linarith [Real.pi_pos])⟩
    have hM₁1 : M₁ ≤ max M₁ 1 := le_max_left _ _
    refine ⟨?_, ?_, ?_⟩
    · calc |u θ - L| ≤ M₁ * θ := hL'bd θ hθ
        _ ≤ max M₁ 1 * θ := mul_le_mul_of_nonneg_right hM₁1 (le_of_lt hθ.1)
    · calc |u θ| ≤ M₁ := (hM₁ θ hθ').1
        _ ≤ max M₁ 1 := hM₁1
    · calc |deriv u θ| ≤ M₁ := (hM₁ θ hθ').2
        _ ≤ max M₁ 1 := hM₁1

end Work.FTS.EllipticEst.AngAWeak

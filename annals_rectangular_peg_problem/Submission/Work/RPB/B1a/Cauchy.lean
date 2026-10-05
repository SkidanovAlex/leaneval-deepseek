/-
# Cauchy's theorem for polygonal chains in a bounded domain with connected complement

This file contains the in-house proof of the "homology Cauchy theorem" step needed for
`Work.RPB.B1a.hasPrimitives_of_isConnected_compl`: for a closed polygonal chain `P` inside a bounded
open set `U ⊆ ℂ` whose complement is connected, and a function `f` holomorphic on `U`, the integral
of `f` along `P` vanishes.

The mathematical ingredients are
* the "Cauchy-type integral" `w ↦ ∫_P f(ζ)/(ζ-w)dζ` is holomorphic off the trace of `P`,
* the *symmetrized difference quotient* `dslope f w ζ = (f ζ - f w)/(ζ - w)` is holomorphic in the
  parameter `w ∈ U` and jointly continuous, so `w ↦ ∫_P dslope f w ζ dζ` is holomorphic on `U`
  (Morera + Fubini),
* the winding-number integral `N w = ∫_P (ζ-w)⁻¹dζ` vanishes far away (primitive of `(ζ-w)⁻¹` on
  `|ζ| < |w|`) and hence, by analytic continuation, on the whole connected component of the
  complement of the trace containing the far-away points; in particular on `Uᶜ`.
Gluing `∫_P dslope f w ζ dζ` (holomorphic on `U`) with `∫_P f(ζ)/(ζ-w)dζ` (holomorphic on that
component) produces an entire function tending to `0` at infinity, hence `0` by Liouville; letting
`w → ∞` gives `∫_P f = 0`.

The two holomorphy inputs are supplied by the separate modules
`differentiableOn_chainIntegral_div` and (`continuousOn_dslope_prod`, `continuousOn_chainIntegral`,
`isConservativeOn_chainIntegral`); they enter here as explicit hypotheses so that this file can be
developed and checked independently.
-/
import Mathlib
import Submission.Work.RPB.B1a.SegChain

namespace Work.RPB.B1a

open Complex Set MeasureTheory intervalIntegral Function Filter
open scoped Topology Filter

noncomputable section

variable {L : List (ℂ × ℂ)} {f : ℂ → ℂ}

/-! ## Symmetry of the symmetrized difference quotient -/

lemma dslope_comm (f : ℂ → ℂ) (a b : ℂ) : dslope f a b = dslope f b a := by
  rcases eq_or_ne a b with rfl | h
  · rfl
  · have hab : a - b ≠ 0 := sub_ne_zero.mpr h
    have hba : b - a ≠ 0 := sub_ne_zero.mpr h.symm
    rw [dslope_of_ne _ h, dslope_of_ne _ h.symm, slope_def_field, slope_def_field]
    field_simp
    ring

/-! ## Topology of the trace -/

theorem isCompact_segment' (a b : ℂ) : IsCompact (segment ℝ a b) := by
  rw [segment_eq_image']
  exact isCompact_Icc.image (by fun_prop)

theorem isCompact_chainTrace (L : List (ℂ × ℂ)) : IsCompact (chainTrace L) := by
  induction L with
  | nil => simp [chainTrace]
  | cons s L ih =>
    obtain ⟨a, b⟩ := s
    have hseg : chainTrace ((a, b) :: L) = segment ℝ a b ∪ chainTrace L := by
      ext z
      simp only [chainTrace, List.mem_cons, Set.mem_ofPred_eq, Set.mem_union]
      constructor
      · rintro ⟨s, hs | hs, hz⟩
        · obtain rfl : s = (a, b) := by simpa using hs
          exact Or.inl hz
        · exact Or.inr ⟨s, hs, hz⟩
      · rintro (hz | ⟨s, hs, hz⟩)
        · exact ⟨(a, b), Or.inl rfl, hz⟩
        · exact ⟨s, Or.inr hs, hz⟩
    rw [hseg]
    exact (isCompact_segment' a b).union ih

theorem isClosed_chainTrace (L : List (ℂ × ℂ)) : IsClosed (chainTrace L) :=
  (isCompact_chainTrace L).isClosed

theorem isBounded_chainTrace (L : List (ℂ × ℂ)) : Bornology.IsBounded (chainTrace L) :=
  (isCompact_chainTrace L).isBounded

theorem isOpen_compl_chainTrace (L : List (ℂ × ℂ)) : IsOpen (chainTrace L)ᶜ :=
  (isClosed_chainTrace L).isOpen_compl

/-- The connected component of the complement of the trace containing a given point is open. -/
theorem isOpen_connectedComponentIn_compl_chainTrace (L : List (ℂ × ℂ)) {w₀ : ℂ}
    (hw₀ : w₀ ∈ (chainTrace L)ᶜ) : IsOpen (connectedComponentIn (chainTrace L)ᶜ w₀) := by
  rw [isOpen_iff_mem_nhds]
  intro w hw
  obtain ⟨ε, hε, hε'⟩ := Metric.isOpen_iff.mp (isOpen_compl_chainTrace L) w
    (connectedComponentIn_subset _ _ hw)
  refine Metric.mem_nhds_iff.mpr ⟨ε, hε, fun z hz => ?_⟩
  have hunion : IsPreconnected (connectedComponentIn (chainTrace L)ᶜ w₀ ∪ Metric.ball w ε) :=
    IsPreconnected.union w hw (Metric.mem_ball_self hε) isPreconnected_connectedComponentIn
      (convex_ball w ε).isPreconnected
  have hsub : connectedComponentIn (chainTrace L)ᶜ w₀ ∪ Metric.ball w ε ⊆ (chainTrace L)ᶜ :=
    Set.union_subset (connectedComponentIn_subset _ _) hε'
  have := IsPreconnected.subset_connectedComponentIn hunion
    (Or.inl (mem_connectedComponentIn hw₀)) hsub
  exact this (Or.inr hz)

/-! ## The winding-number integral vanishes far away -/

/-- The chain integral of `ζ ↦ (ζ - w)⁻¹` vanishes for `w` further from the origin than the trace:
the ball `|ζ| < ‖w‖` contains the trace and on it `(ζ-w)⁻¹` has a primitive, so the closed chain
integral telescopes to `0`. -/
theorem chainIntegral_inv_eq_zero_of_norm_lt {L : List (ℂ × ℂ)} {p w : ℂ}
    (hL : IsChainFrom p p L) (hw : ∀ z ∈ chainTrace L, ‖z‖ < ‖w‖) :
    chainIntegral (fun ζ => (ζ - w)⁻¹) L = 0 := by
  obtain ⟨F, hF⟩ := DifferentiableOn.isExactOn_ball (E := ℂ) (c := (0 : ℂ)) (r := ‖w‖)
    (f := fun ζ : ℂ => (ζ - w)⁻¹) (by
      refine DifferentiableOn.inv (𝕜 := ℂ) (R := ℂ) (differentiableOn_id.sub_const w)
        fun z hz => ?_
      intro h
      have hz' : ‖z‖ < ‖w‖ := by simpa [Metric.mem_ball, dist_eq_norm] using hz
      rw [sub_eq_zero] at h
      rw [h] at hz'
      exact lt_irrefl _ hz')
  refine chainIntegral_eq_zero_of_hasDerivAt (f := fun ζ => (ζ - w)⁻¹) (F := F) hL
    (fun s hs t ht => ?_) (fun s hs => ?_)
  · exact hF _ (by simpa [Metric.mem_ball] using hw _ (mem_chainTrace_param hs ht))
  · refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) fun z hz => ?_
    refine sub_ne_zero.mpr fun h => ?_
    have := hw z (segment_subset_chainTrace hs hz)
    rw [h] at this
    exact lt_irrefl _ this

/-- The winding-number integral vanishes for every `w` outside the disc of radius `R` containing
the trace. -/
theorem chainIntegral_inv_eq_zero_of_le {L : List (ℂ × ℂ)} {p : ℂ} (hL : IsChainFrom p p L)
    {R : ℝ} (hR : ∀ z ∈ chainTrace L, ‖z‖ ≤ R) {w : ℂ} (hw : R < ‖w‖) :
    chainIntegral (fun ζ => (ζ - w)⁻¹) L = 0 :=
  chainIntegral_inv_eq_zero_of_norm_lt hL fun z hz => lt_of_le_of_lt (hR z hz) hw

/-! ## Estimates for chain integrals -/

/-- The total length of a polygonal chain. -/
def chainLength (L : List (ℂ × ℂ)) : ℝ := (L.map (fun s => ‖s.2 - s.1‖)).sum

lemma chainLength_cons (a b : ℂ) (L : List (ℂ × ℂ)) :
    chainLength ((a, b) :: L) = ‖b - a‖ + chainLength L := rfl

lemma chainLength_nonneg (L : List (ℂ × ℂ)) : 0 ≤ chainLength L := by
  induction L with
  | nil => simp [chainLength]
  | cons s L ih => obtain ⟨a, b⟩ := s; rw [chainLength_cons]; positivity

/-- Norm bound for a chain integral in terms of a bound for the integrand and the chain length. -/
theorem norm_chainIntegral_le {g : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C) :
    ∀ L : List (ℂ × ℂ), (∀ z ∈ chainTrace L, ‖g z‖ ≤ C) →
      ‖chainIntegral g L‖ ≤ C * chainLength L := by
  intro L
  induction L with
  | nil => intro _; simp [chainIntegral, chainLength]
  | cons s L ih =>
    obtain ⟨a, b⟩ := s
    intro h
    rw [chainIntegral_cons, chainLength_cons]
    have hseg : ‖segIntegral g a b‖ ≤ C * ‖b - a‖ := by
      rw [segIntegral]
      have h1 : ‖∫ t in (0 : ℝ)..1, g (a + (t : ℂ) * (b - a)) * (b - a)‖
          ≤ C * ‖b - a‖ * |(1 : ℝ) - 0| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
        have ht' : t ∈ Icc (0 : ℝ) 1 := by
          simpa [uIcc_of_le zero_le_one] using Set.uIoc_subset_uIcc ht
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          (h _ (mem_chainTrace_param (L := (a, b) :: L) List.mem_cons_self ht')) (norm_nonneg _)
      simpa using h1
    have hrest : ‖chainIntegral g L‖ ≤ C * chainLength L :=
      ih fun z hz => h z (chainTrace_tail_subset_cons (a, b) L hz)
    rw [mul_add]
    exact (norm_add_le _ _).trans (add_le_add hseg hrest)

/-- A uniform bound for the difference-quotient integrand `f ζ · ζ / (ζ - w)`. -/
theorem norm_mul_self_mul_inv_le {f : ℂ → ℂ} {Cf R : ℝ} (hCf0 : 0 ≤ Cf) (hR0 : 0 ≤ R)
    (hCf : ∀ z ∈ chainTrace L, ‖f z‖ ≤ Cf) (hR : ∀ z ∈ chainTrace L, ‖z‖ ≤ R)
    {w : ℂ} (hw : R < ‖w‖) :
    ∀ z ∈ chainTrace L, ‖f z * (z * (z - w)⁻¹)‖ ≤ Cf * R / (‖w‖ - R) := by
  intro z hz
  have hzR : ‖z‖ ≤ R := hR z hz
  have hpos : 0 < ‖w‖ - R := sub_pos.mpr hw
  have hden : ‖w‖ - R ≤ ‖z - w‖ := by
    have h1 : ‖w‖ - ‖z‖ ≤ ‖w - z‖ := norm_sub_norm_le w z
    rw [norm_sub_rev w z] at h1
    linarith
  have h1 : ‖f z‖ * ‖z‖ ≤ Cf * R := mul_le_mul (hCf z hz) hzR (norm_nonneg _) hCf0
  have h2 : (‖z - w‖)⁻¹ ≤ (‖w‖ - R)⁻¹ := inv_anti₀ hpos hden
  have hCR : 0 ≤ Cf * R := mul_nonneg hCf0 hR0
  rw [norm_mul, norm_mul, norm_inv]
  calc ‖f z‖ * (‖z‖ * (‖z - w‖)⁻¹)
      = ‖f z‖ * ‖z‖ * (‖z - w‖)⁻¹ := by ring
    _ ≤ Cf * R * (‖w‖ - R)⁻¹ := mul_le_mul h1 h2 (by positivity) hCR
    _ = Cf * R / (‖w‖ - R) := by rw [div_eq_mul_inv]

/-- Bound for the "correction term" `∫_P f ζ · ζ/(ζ-w) dζ`. -/
theorem norm_chainIntegral_correction_le {f : ℂ → ℂ} {Cf R : ℝ} (hCf0 : 0 ≤ Cf) (hR0 : 0 ≤ R)
    (hCf : ∀ z ∈ chainTrace L, ‖f z‖ ≤ Cf) (hR : ∀ z ∈ chainTrace L, ‖z‖ ≤ R)
    {w : ℂ} (hw : R < ‖w‖) :
    ‖chainIntegral (fun ζ => f ζ * (ζ * (ζ - w)⁻¹)) L‖
      ≤ Cf * R / (‖w‖ - R) * chainLength L :=
  norm_chainIntegral_le (div_nonneg (mul_nonneg hCf0 hR0) (by linarith))
    L fun z hz => norm_mul_self_mul_inv_le hCf0 hR0 hCf hR hw z hz

/-! ## The symmetrized difference quotient and the Cauchy integral -/

/-- On the complement of the trace, the `dslope`-integral agrees with the Cauchy integral up to the
correction `f w ∫_P dζ/(ζ-w)`. -/
theorem chainIntegral_dslope_eq {f : ℂ → ℂ} (L : List (ℂ × ℂ))
    (hf : ContinuousOn f (chainTrace L)) {w : ℂ} (hw : w ∉ chainTrace L) :
    chainIntegral (fun ζ => dslope f w ζ) L
      = chainIntegral (fun ζ => f ζ * (ζ - w)⁻¹) L
        - f w * chainIntegral (fun ζ => (ζ - w)⁻¹) L := by
  have hinv : ContinuousOn (fun ζ : ℂ => (ζ - w)⁻¹) (chainTrace L) :=
    ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
      fun z hz => sub_ne_zero.mpr fun h => hw (h ▸ hz)
  have h1 : chainIntegral (fun ζ => dslope f w ζ) L
      = chainIntegral (fun ζ => (f ζ - f w) * (ζ - w)⁻¹) L := by
    refine chainIntegral_congr L fun s hs z hz => ?_
    have hz' : z ≠ w := fun h => hw ⟨s, hs, h ▸ hz⟩
    rw [dslope_of_ne _ hz', slope_def_field, div_eq_mul_inv]
  have h2 : chainIntegral (fun ζ => (f ζ - f w) * (ζ - w)⁻¹) L
      = chainIntegral (fun ζ => f ζ * (ζ - w)⁻¹ - f w * (ζ - w)⁻¹) L := by
    refine chainIntegral_congr L fun s hs z hz => by ring
  rw [h1, h2,
    chainIntegral_sub (f := fun ζ => f ζ * (ζ - w)⁻¹)
      (g := fun ζ => f w * (ζ - w)⁻¹) L (hf.mul hinv) (continuousOn_const.mul hinv),
    chainIntegral_const_mul (f := fun ζ => (ζ - w)⁻¹) (f w) L]

/-! ## The winding-number integral vanishes off `U` -/

/-- **(★)** If `U` is bounded with connected complement, a closed chain lies in `U` and
`w ∉ U`, then the winding-number integral of the chain about `w` vanishes: the Cauchy-type integral
`N` is holomorphic off the trace and vanishes on the disc `|w| > R`, hence (by analytic
continuation) on the whole component of the complement of the trace containing that disc, which
contains `Uᶜ` because `Uᶜ` is connected, unbounded and disjoint from the trace. -/
theorem chainIntegral_inv_eq_zero_of_mem_compl {U : Set ℂ} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUcc : IsConnected Uᶜ) {L : List (ℂ × ℂ)} {p : ℂ}
    (hLc : IsChainFrom p p L) (hLin : ChainIn U L)
    (hN : DifferentiableOn ℂ (fun w => chainIntegral (fun ζ => (ζ - w)⁻¹) L) (chainTrace L)ᶜ)
    {w : ℂ} (hw : w ∉ U) :
    chainIntegral (fun ζ => (ζ - w)⁻¹) L = 0 := by
  have htraceU : chainTrace L ⊆ U := fun z ⟨s, hs, hz⟩ => (hLin s hs).2.2 hz
  obtain ⟨C₁, hC₁⟩ := hUb.exists_norm_le
  obtain ⟨C₂, hC₂⟩ := (isBounded_chainTrace L).exists_norm_le
  set R : ℝ := max (max C₁ C₂) 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have htraceR : ∀ z ∈ chainTrace L, ‖z‖ ≤ R := fun z hz =>
    le_trans (hC₂ z hz) (le_trans (le_max_right _ _) (le_max_left _ _))
  have hUR : ∀ z ∈ U, ‖z‖ ≤ R := fun z hz =>
    le_trans (hC₁ z hz) (le_trans (le_max_left _ _) (le_max_left _ _))
  set w₀ : ℂ := ((R + 1 : ℝ) : ℂ) with hw₀def
  have hw₀norm : ‖w₀‖ = R + 1 := by
    rw [hw₀def, Complex.norm_def, Complex.normSq_ofReal,
      Real.sqrt_mul_self (by linarith : (0 : ℝ) ≤ R + 1)]
  have hw₀trace : w₀ ∉ chainTrace L := by
    intro h
    have := htraceR w₀ h
    rw [hw₀norm] at this
    linarith
  set Ω : Set ℂ := connectedComponentIn (chainTrace L)ᶜ w₀ with hΩdef
  have hΩsub : Ω ⊆ (chainTrace L)ᶜ := connectedComponentIn_subset _ _
  have hw₀Ω : w₀ ∈ Ω := by rw [hΩdef]; exact mem_connectedComponentIn hw₀trace
  have hfar : ∀ z : ℂ, R < ‖z‖ → chainIntegral (fun ζ => (ζ - z)⁻¹) L = 0 :=
    fun z hz => chainIntegral_inv_eq_zero_of_le hLc htraceR hz
  have hNΩ : EqOn (fun z => chainIntegral (fun ζ => (ζ - z)⁻¹) L) 0 Ω := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      ((hN.analyticOnNhd (isOpen_compl_chainTrace L)).mono hΩsub) analyticOnNhd_const ?_ hw₀Ω ?_
    · rw [hΩdef]; exact isPreconnected_connectedComponentIn
    · filter_upwards [Metric.ball_mem_nhds w₀ zero_lt_one] with z hz
      refine hfar z ?_
      have hz' : dist z w₀ < 1 := Metric.mem_ball.mp hz
      have h1 : ‖w₀‖ - ‖z‖ ≤ ‖w₀ - z‖ := norm_sub_norm_le w₀ z
      have h2 : ‖w₀ - z‖ = dist z w₀ := by rw [dist_eq_norm, norm_sub_rev]
      rw [hw₀norm, h2] at h1
      linarith
  have hw₀U : w₀ ∉ U := by
    intro h
    have := hUR w₀ h
    rw [hw₀norm] at this
    linarith
  have hUccΩ : Uᶜ ⊆ Ω := by
    refine IsPreconnected.subset_connectedComponentIn hUcc.isPreconnected hw₀U ?_
    intro z hz hzt
    exact hz (htraceU hzt)
  exact hNΩ (hUccΩ hw)

/-! ## Estimates for the Cauchy integral -/

/-- Pointwise bound for the integrand of the Cauchy integral, away from the trace. -/
theorem norm_mul_inv_le {f : ℂ → ℂ} {Cf R : ℝ} (hCf : ∀ z ∈ chainTrace L, ‖f z‖ ≤ Cf)
    (hR : ∀ z ∈ chainTrace L, ‖z‖ ≤ R) {w : ℂ} (hw : R < ‖w‖) :
    ∀ z ∈ chainTrace L, ‖f z * (z - w)⁻¹‖ ≤ Cf / (‖w‖ - R) := by
  intro z hz
  have hpos : 0 < ‖w‖ - R := sub_pos.mpr hw
  have hden : ‖w‖ - R ≤ ‖z - w‖ := by
    have h1 : ‖w‖ - ‖z‖ ≤ ‖w - z‖ := norm_sub_norm_le w z
    rw [norm_sub_rev w z] at h1
    linarith [hR z hz]
  rw [norm_mul, norm_inv, div_eq_mul_inv]
  exact mul_le_mul (hCf z hz) (inv_anti₀ hpos hden) (by positivity)
    (le_trans (norm_nonneg _) (hCf z hz))

/-- The complement of a closed ball is a neighbourhood of infinity. -/
lemma mem_cocompact_norm_gt (R : ℝ) : {w : ℂ | R < ‖w‖} ∈ Filter.cocompact ℂ :=
  Metric.mem_cocompact_of_closedBall_compl_subset 0 ⟨R, fun w hw => by
    simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right] at hw
    exact lt_of_not_ge hw⟩

lemma tendsto_norm_sub_cocompact (R : ℝ) :
    Tendsto (fun w : ℂ => ‖w‖ - R) (Filter.cocompact ℂ) atTop := by
  rw [tendsto_atTop]
  intro a
  filter_upwards [mem_cocompact_norm_gt (R + a)] with w hw
  linarith

/-- The chain integral of `f` is the "correction term" minus `w` times the Cauchy integral:
this is the algebraic identity behind the computation of the "residue at infinity". -/
theorem chainIntegral_eq_correction_add {f : ℂ → ℂ} (L : List (ℂ × ℂ))
    (hf : ContinuousOn f (chainTrace L)) {w : ℂ} (hw : w ∉ chainTrace L) :
    chainIntegral (fun ζ => f ζ * (ζ * (ζ - w)⁻¹)) L
      = chainIntegral f L + w * chainIntegral (fun ζ => f ζ * (ζ - w)⁻¹) L := by
  have hinv : ContinuousOn (fun ζ : ℂ => (ζ - w)⁻¹) (chainTrace L) :=
    ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
      fun z hz => sub_ne_zero.mpr fun h => hw (h ▸ hz)
  have h1 : chainIntegral (fun ζ => w * (f ζ * (ζ - w)⁻¹)) L
      = w * chainIntegral (fun ζ => f ζ * (ζ - w)⁻¹) L :=
    chainIntegral_const_mul (f := fun ζ => f ζ * (ζ - w)⁻¹) w L
  have h2 : chainIntegral (fun ζ => f ζ + w * (f ζ * (ζ - w)⁻¹)) L
      = chainIntegral f L + chainIntegral (fun ζ => w * (f ζ * (ζ - w)⁻¹)) L :=
    chainIntegral_add L hf (continuousOn_const.mul (hf.mul hinv))
  have h3 : chainIntegral (fun ζ => f ζ + w * (f ζ * (ζ - w)⁻¹)) L
      = chainIntegral (fun ζ => f ζ * (ζ * (ζ - w)⁻¹)) L := by
    refine chainIntegral_congr L fun s hs z hz => ?_
    have hz' : z ≠ w := fun h => hw ⟨s, hs, h ▸ hz⟩
    have hzw : z - w ≠ 0 := sub_ne_zero.mpr hz'
    field_simp
    ring
  calc chainIntegral (fun ζ => f ζ * (ζ * (ζ - w)⁻¹)) L
      = chainIntegral (fun ζ => f ζ + w * (f ζ * (ζ - w)⁻¹)) L := h3.symm
    _ = chainIntegral f L + chainIntegral (fun ζ => w * (f ζ * (ζ - w)⁻¹)) L := h2
    _ = chainIntegral f L + w * chainIntegral (fun ζ => f ζ * (ζ - w)⁻¹) L := by rw [h1]

/-! ## Cauchy's theorem for a closed polygonal chain -/

/-- **Cauchy's theorem, polygonal form.** For a closed polygonal chain `P` inside a bounded open set
`U` with connected complement, and `f` holomorphic on `U`, the integral of `f` along `P` vanishes.

The two analytic inputs are the holomorphy of the `dslope`-integral on `U` (Morera/Fubini) and the
holomorphy of the Cauchy-type integral off the trace. -/
theorem chainIntegral_eq_zero_of_isChainFrom_self {U : Set ℂ} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUcc : IsConnected Uᶜ) {f : ℂ → ℂ}
    (hfd : DifferentiableOn ℂ f U) {L : List (ℂ × ℂ)} {p : ℂ} (hLc : IsChainFrom p p L)
    (hLin : ChainIn U L)
    (hG : DifferentiableOn ℂ (fun w => chainIntegral (fun ζ => dslope f w ζ) L) U)
    (hK : DifferentiableOn ℂ (fun w => chainIntegral (fun ζ => f ζ * (ζ - w)⁻¹) L)
      (chainTrace L)ᶜ)
    (hN : DifferentiableOn ℂ (fun w => chainIntegral (fun ζ => (ζ - w)⁻¹) L)
      (chainTrace L)ᶜ) :
    chainIntegral f L = 0 := by
  classical
  have htraceU : chainTrace L ⊆ U := fun z ⟨s, hs, hz⟩ => (hLin s hs).2.2 hz
  have hcontf : ContinuousOn f (chainTrace L) := hfd.continuousOn.mono htraceU
  -- bounds
  obtain ⟨C₁, hC₁⟩ := hUb.exists_norm_le
  obtain ⟨C₂, hC₂⟩ := (isBounded_chainTrace L).exists_norm_le
  set R : ℝ := max (max C₁ C₂) 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have htraceR : ∀ z ∈ chainTrace L, ‖z‖ ≤ R := fun z hz =>
    le_trans (hC₂ z hz) (le_trans (le_max_right _ _) (le_max_left _ _))
  have hUR : ∀ z ∈ U, ‖z‖ ≤ R := fun z hz =>
    le_trans (hC₁ z hz) (le_trans (le_max_left _ _) (le_max_left _ _))
  obtain ⟨Cf, hCf⟩ := (isCompact_chainTrace L).exists_bound_of_continuousOn hcontf
  set Cf' : ℝ := max Cf 0 with hCf'def
  have hCf'0 : 0 ≤ Cf' := le_max_right _ _
  have hCf' : ∀ z ∈ chainTrace L, ‖f z‖ ≤ Cf' := fun z hz =>
    le_trans (hCf z hz) (le_max_left _ _)
  -- the far-away vanishing and the component
  set w₀ : ℂ := ((R + 1 : ℝ) : ℂ) with hw₀def
  have hw₀norm : ‖w₀‖ = R + 1 := by
    rw [hw₀def, Complex.norm_def, Complex.normSq_ofReal,
      Real.sqrt_mul_self (by linarith : (0 : ℝ) ≤ R + 1)]
  have hw₀trace : w₀ ∉ chainTrace L := by
    intro h
    have := htraceR w₀ h
    rw [hw₀norm] at this
    linarith
  set Ω : Set ℂ := connectedComponentIn (chainTrace L)ᶜ w₀ with hΩdef
  have hΩsub : Ω ⊆ (chainTrace L)ᶜ := connectedComponentIn_subset _ _
  have hΩopen : IsOpen Ω := by
    rw [hΩdef]
    exact isOpen_connectedComponentIn_compl_chainTrace L hw₀trace
  have hw₀Ω : w₀ ∈ Ω := by rw [hΩdef]; exact mem_connectedComponentIn hw₀trace
  have hfar : ∀ z : ℂ, R < ‖z‖ → chainIntegral (fun ζ => (ζ - z)⁻¹) L = 0 :=
    fun z hz => chainIntegral_inv_eq_zero_of_le hLc htraceR hz
  have hNΩ : EqOn (fun z => chainIntegral (fun ζ => (ζ - z)⁻¹) L) 0 Ω := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      ((hN.analyticOnNhd (isOpen_compl_chainTrace L)).mono hΩsub) analyticOnNhd_const ?_ hw₀Ω ?_
    · rw [hΩdef]; exact isPreconnected_connectedComponentIn
    · filter_upwards [Metric.ball_mem_nhds w₀ zero_lt_one] with z hz
      refine hfar z ?_
      have hz' : dist z w₀ < 1 := Metric.mem_ball.mp hz
      have h1 : ‖w₀‖ - ‖z‖ ≤ ‖w₀ - z‖ := norm_sub_norm_le w₀ z
      have h2 : ‖w₀ - z‖ = dist z w₀ := by rw [dist_eq_norm, norm_sub_rev]
      rw [hw₀norm, h2] at h1
      linarith
  have hw₀U : w₀ ∉ U := by
    intro h
    have := hUR w₀ h
    rw [hw₀norm] at this
    linarith
  have hUccΩ : Uᶜ ⊆ Ω := by
    refine IsPreconnected.subset_connectedComponentIn hUcc.isPreconnected hw₀U ?_
    intro z hz hzt
    exact hz (htraceU hzt)
  have hN0 : ∀ w ∉ U, chainIntegral (fun ζ => (ζ - w)⁻¹) L = 0 :=
    fun w hw => hNΩ (hUccΩ hw)
  -- the glued function
  set Φ : ℂ → ℂ := fun w => if w ∈ U then chainIntegral (fun ζ => dslope f w ζ) L
    else chainIntegral (fun ζ => f ζ * (ζ - w)⁻¹) L with hΦdef
  have hΦG : ∀ w ∈ U, Φ w = chainIntegral (fun ζ => dslope f w ζ) L := by
    intro w hw
    rw [hΦdef]; exact if_pos hw
  have hΦK : ∀ w ∉ U, Φ w = chainIntegral (fun ζ => f ζ * (ζ - w)⁻¹) L := by
    intro w hw
    rw [hΦdef]; exact if_neg hw
  have hGKΩ : ∀ w ∈ Ω, chainIntegral (fun ζ => dslope f w ζ) L
      = chainIntegral (fun ζ => f ζ * (ζ - w)⁻¹) L := by
    intro w hw
    have h := hNΩ hw
    simp only [Pi.zero_apply] at h
    rw [chainIntegral_dslope_eq L hcontf (hΩsub hw), h, mul_zero, sub_zero]
  have hΦ_diff : Differentiable ℂ Φ := by
    intro w
    by_cases hwU : w ∈ U
    · have hev : Φ =ᶠ[𝓝 w] fun w => chainIntegral (fun ζ => dslope f w ζ) L := by
        filter_upwards [hUo.mem_nhds hwU] with z hz
        by_cases hzU : z ∈ U
        · rw [hΦG z hzU]
        · rw [hΦK z hzU, hGKΩ z (hUccΩ hzU)]
      exact (hG.differentiableAt (hUo.mem_nhds hwU)).congr_of_eventuallyEq hev
    · have hwΩ : w ∈ Ω := hUccΩ hwU
      have hwtr : w ∉ chainTrace L := hΩsub hwΩ
      have hev : Φ =ᶠ[𝓝 w] fun w => chainIntegral (fun ζ => f ζ * (ζ - w)⁻¹) L := by
        filter_upwards [hΩopen.mem_nhds hwΩ] with z hz
        by_cases hzU : z ∈ U
        · rw [hΦG z hzU, hGKΩ z hz]
        · rw [hΦK z hzU]
      exact (hK.differentiableAt ((isOpen_compl_chainTrace L).mem_nhds hwtr)).congr_of_eventuallyEq hev
  -- `Φ` tends to `0` at infinity, hence vanishes identically
  have hbound : ∀ w : ℂ, R < ‖w‖ → ‖Φ w‖ ≤ Cf' * chainLength L / (‖w‖ - R) := by
    intro w hw
    have hwU : w ∉ U := by
      intro h
      have := hUR w h
      linarith
    rw [hΦK w hwU]
    have hpos : 0 ≤ Cf' / (‖w‖ - R) :=
      div_nonneg hCf'0 (le_of_lt (sub_pos.mpr hw))
    refine (norm_chainIntegral_le hpos L fun z hz => norm_mul_inv_le hCf' htraceR hw z hz).trans_eq
      (by ring)
  have hΦ_zero : Φ = fun _ => 0 := by
    refine Differentiable.eq_const_of_tendsto_cocompact hΦ_diff ?_
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hg : Tendsto (fun w : ℂ => Cf' * chainLength L / (‖w‖ - R)) (Filter.cocompact ℂ) (𝓝 0) :=
      (tendsto_const_nhds (x := Cf' * chainLength L) (f := Filter.cocompact ℂ)).div_atTop
        (tendsto_norm_sub_cocompact R)
    refine squeeze_zero' (Filter.Eventually.of_forall fun w => norm_nonneg _) ?_ hg
    filter_upwards [mem_cocompact_norm_gt R] with w hw
    exact hbound w hw
  have hK0 : ∀ w ∉ U, chainIntegral (fun ζ => f ζ * (ζ - w)⁻¹) L = 0 := by
    intro w hw
    rw [← hΦK w hw, congrFun hΦ_zero w]
  -- the estimate, and the conclusion
  have hcorr : ∀ w : ℂ, R < ‖w‖ →
      chainIntegral f L = chainIntegral (fun ζ => f ζ * (ζ * (ζ - w)⁻¹)) L := by
    intro w hw
    have hwU : w ∉ U := by
      intro h
      have := hUR w h
      linarith
    have hwtr : w ∉ chainTrace L := fun h => hwU (htraceU h)
    have hid := chainIntegral_eq_correction_add L hcontf hwtr
    rw [hK0 w hwU, mul_zero, add_zero] at hid
    exact hid.symm
  have hest : ∀ w : ℂ, R < ‖w‖ →
      ‖chainIntegral f L‖ ≤ Cf' * R / (‖w‖ - R) * chainLength L := by
    intro w hw
    rw [hcorr w hw]
    exact norm_chainIntegral_correction_le hCf'0 hR0 hCf' htraceR hw
  have hlim : Tendsto (fun w : ℂ => Cf' * R / (‖w‖ - R) * chainLength L)
      (Filter.cocompact ℂ) (𝓝 0) := by
    have h1 : Tendsto (fun w : ℂ => Cf' * R / (‖w‖ - R)) (Filter.cocompact ℂ) (𝓝 0) :=
      (tendsto_const_nhds (x := Cf' * R) (f := Filter.cocompact ℂ)).div_atTop
        (tendsto_norm_sub_cocompact R)
    simpa using h1.mul (tendsto_const_nhds (x := chainLength L) (f := Filter.cocompact ℂ))
  have hev : ∀ᶠ w : ℂ in Filter.cocompact ℂ,
      ‖chainIntegral f L‖ ≤ Cf' * R / (‖w‖ - R) * chainLength L := by
    filter_upwards [mem_cocompact_norm_gt R] with w hw
    exact hest w hw
  have hle : ‖chainIntegral f L‖ ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim hev
  exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))

end

end Work.RPB.B1a

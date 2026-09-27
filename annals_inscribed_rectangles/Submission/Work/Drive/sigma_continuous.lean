import Mathlib
import Submission.Work.Drive.UmlaufSetup
import Submission.Work.Drive.exists_angle_line

/-!
# Continuity of Hopf's secant map `sigma` on the triangle `t₀ ≤ s ≤ t ≤ t₀ + 2π`

`Work.Drive.sigma c t₀ : tri t₀ → Circle` is Hopf's secant map: it sends a point `(s,t)` of the
closed triangle `t₀ ≤ s ≤ t ≤ t₀ + 2π` to the direction of the secant `c t - c s` when `s < t`,
to the tangent direction `tangDir c s` when `s = t`, and to the *negated* tangent direction at the
corner `(t₀, t₀ + 2π)` (where the secant degenerates to `0`).

Continuity at the diagonal `s = t` and at the corner uses the limit of the secant direction as the
two points collapse:

* if `s < t` are close to `a`, then `secDir c s t → tangDir c a`;
* if `s → a` and `t → a + 2π` from below, then `secDir c s t → -tangDir c a` (one rewrites
  `c t = c (t - 2π)` using periodicity and the secant slope is negative).

Both follow from the *strict* differentiability of `c` (`ContDiff ℝ 1 c`), which gives the
two-parameter slope limit `slope c u v → deriv c a` as `u, v → a`, `u ≠ v`.

The proof avoids case analysis on closed pieces of the triangle: it defines a globally continuous
map `sigmaAux c : ℝ × ℝ → Circle` which agrees with `sigmaPt c t₀` on `tri t₀`, and concludes by
composing with the continuous inclusion `tri t₀ → ℝ × ℝ`.
-/

namespace Work.Drive

open Filter Asymptotics
open scoped Topology

noncomputable section

/-! ## Preliminaries: `dirOf` and the two-parameter slope limit -/

/-- Multiplying by a positive real number does not change the direction. -/
lemma dirOf_ofReal_mul_pos {r : ℝ} (hr : 0 < r) (z : ℂ) : dirOf ((r : ℂ) * z) = dirOf z := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [mul_zero]
  have hrne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have hz' : (r : ℂ) * z ≠ 0 := mul_ne_zero hrne hz
  refine Subtype.ext ?_
  rw [dirOf_coe hz', dirOf_coe hz, norm_mul, norm_ofReal_complex,
    Complex.ofReal_mul, abs_of_pos hr]
  field_simp

/-- Multiplying by a negative real number flips the direction. -/
lemma dirOf_ofReal_mul_neg {r : ℝ} (hr : r < 0) {z : ℂ} (hz : z ≠ 0) :
    dirOf ((r : ℂ) * z) = -dirOf z := by
  have hrne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_lt hr)
  have hz' : (r : ℂ) * z ≠ 0 := mul_ne_zero hrne hz
  apply Circle.ext
  rw [Circle.coe_neg, dirOf_coe hz', dirOf_coe hz, norm_mul, norm_ofReal_complex,
    Complex.ofReal_mul, abs_of_neg hr, Complex.ofReal_neg]
  field_simp

/-- `dirOf` is continuous at every nonzero complex number. -/
lemma continuousAt_dirOf {z : ℂ} (hz : z ≠ 0) : ContinuousAt dirOf z := by
  have hcoe : ContinuousAt (fun w : ℂ => (dirOf w : ℂ)) z := by
    have hdiv : ContinuousAt (fun w : ℂ => w / (‖w‖ : ℂ)) z := by
      refine ContinuousAt.div continuousAt_id ?_ ?_
      · exact Complex.continuous_ofReal.continuousAt.comp continuous_norm.continuousAt
      · simp [Complex.ofReal_eq_zero, norm_ne_zero_iff.mpr hz]
    refine hdiv.congr_of_eventuallyEq ?_
    filter_upwards [eventually_ne_nhds hz] with w hw
    rw [dirOf, dif_neg hw]
    rfl
  exact (Topology.IsEmbedding.subtypeVal.tendsto_nhds_iff).mpr hcoe

/-- **The two-parameter slope limit.**  For a `C¹` curve `c`, the slope `slope c u v` tends to
`deriv c a` as `u, v → a` along any filter on which `u ≠ v` eventually.  This is strict
differentiability of `c` at `a`. -/
lemma slope_tendsto_general (c : ℝ → ℝ × ℝ) (hcd : ContDiff ℝ 1 c) (a : ℝ)
    {ι : Type*} {l : Filter ι} {u v : ι → ℝ}
    (hu : Tendsto u l (𝓝 a)) (hv : Tendsto v l (𝓝 a))
    (hne : ∀ᶠ i in l, u i ≠ v i) :
    Tendsto (fun i => slope c (u i) (v i)) l (𝓝 (deriv c a)) := by
  have hstrict : HasStrictFDerivAt c (fderiv ℝ c a) a := hcd.hasStrictFDerivAt one_ne_zero
  have hlo : (fun p : ℝ × ℝ => c p.1 - c p.2 - fderiv ℝ c a (p.1 - p.2)) =o[𝓝 (a,a)]
      (fun p => p.1 - p.2) := (isLittleOTVS_iff_isLittleO (𝕜 := ℝ)).mp hstrict.isLittleOTVS
  have hpair : Tendsto (fun i => (u i, v i)) l (𝓝 (a,a)) := by
    rw [nhds_prod_eq]
    exact Tendsto.prodMk hu hv
  have hlo2 : (fun i => c (u i) - c (v i) - fderiv ℝ c a (u i - v i)) =o[l]
      (fun i => u i - v i) := hlo.comp_tendsto hpair
  have hq : Tendsto (fun i => (u i - v i)⁻¹ • (c (u i) - c (v i) - fderiv ℝ c a (u i - v i)))
      l (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hhalf : 0 < ε / 2 := by linarith
    have hev := (isLittleO_iff.mp hlo2) hhalf
    filter_upwards [hev, hne] with p hp hpne
    have hd : u p - v p ≠ 0 := sub_ne_zero.mpr hpne
    calc dist ((u p - v p)⁻¹ • (c (u p) - c (v p) - fderiv ℝ c a (u p - v p))) 0
        = ‖(u p - v p)⁻¹‖ * ‖c (u p) - c (v p) - fderiv ℝ c a (u p - v p)‖ := by
          rw [dist_zero_right, norm_smul]
      _ ≤ ‖(u p - v p)⁻¹‖ * ((ε/2) * ‖u p - v p‖) :=
          mul_le_mul_of_nonneg_left hp (norm_nonneg _)
      _ = ε / 2 := by
          rw [norm_inv, Real.norm_eq_abs, mul_comm (ε/2),
            inv_mul_cancel_left₀ (abs_ne_zero.mpr hd)]
      _ < ε := by linarith
  have h1 : Tendsto (fun i => deriv c a + (u i - v i)⁻¹ •
      (c (u i) - c (v i) - fderiv ℝ c a (u i - v i))) l (𝓝 (deriv c a)) := by
    simpa using hq.const_add (deriv c a)
  refine Tendsto.congr' ?_ h1
  filter_upwards [hne] with p hpne
  have hd : u p - v p ≠ 0 := sub_ne_zero.mpr hpne
  have hmul : fderiv ℝ c a (u p - v p) = (u p - v p) • deriv c a := by
    conv_lhs => rw [show u p - v p = (u p - v p) • (1 : ℝ) by simp]
    rw [map_smul]
    rfl
  rw [hmul, smul_sub, inv_smul_smul₀ hd, slope_comm, slope_def_module]
  abel

/-! ## Elementary facts about a `RegCurve` -/

/-- If the parameters are closer than one period, the curve takes different values. -/
lemma c_ne_of_gap (c : ℝ → ℝ × ℝ) (hc : RegCurve c) {s t : ℝ}
    (h1 : s < t) (h2 : t < s + 2 * Real.pi) : c s ≠ c t := by
  intro h
  obtain ⟨k, hk⟩ := (hc.eq_iff s t).mp h
  have hk_eq : (k : ℝ) * (2 * Real.pi) = s - t := by linarith [hk]
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  have hklt : (k:ℝ) < 0 := by nlinarith
  have hkgt : (-1:ℝ) < (k:ℝ) := by nlinarith
  have hki : (-1:ℤ) < k ∧ k < 0 := ⟨by exact_mod_cast hkgt, by exact_mod_cast hklt⟩
  omega

/-- The slope is nonzero as soon as the two points are distinct. -/
lemma slope_ne_zero_of_ne (c : ℝ → ℝ × ℝ) {s t : ℝ} (hst : s ≠ t) (hct : c s ≠ c t) :
    slope c s t ≠ 0 := by
  intro h0
  rw [slope_def_module] at h0
  have hd : t - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hst)
  have := (smul_eq_zero.mp h0).resolve_left (inv_ne_zero hd)
  exact hct (sub_eq_zero.mp this).symm

/-! ## The secant direction is continuous at the diagonal and at the corner -/

/-- As `(s,t) → (a,a)` with `s < t`, the secant direction tends to the tangent direction. -/
lemma tendsto_secDir_diag (c : ℝ → ℝ × ℝ) (hc : RegCurve c) (a : ℝ) :
    Tendsto (fun p : ℝ × ℝ => secDir c p.1 p.2)
      (𝓝 (a, a) ⊓ 𝓟 {p | p.1 < p.2}) (𝓝 (tangDir c a)) := by
  set l : Filter (ℝ × ℝ) := 𝓝 (a, a) ⊓ 𝓟 {p | p.1 < p.2} with hl
  have hw : ∀ᶠ p in l, p.1 < p.2 := by
    rw [hl]; exact eventually_inf_principal.mpr (Eventually.of_forall fun p hp => hp)
  have hu : Tendsto (fun p : ℝ × ℝ => p.1) l (𝓝 a) :=
    (continuous_fst.tendsto (a,a)).mono_left inf_le_left
  have hv : Tendsto (fun p : ℝ × ℝ => p.2) l (𝓝 a) :=
    (continuous_snd.tendsto (a,a)).mono_left inf_le_left
  have hslope := slope_tendsto_general c hc.contDiff a hu hv (hw.mono fun p hp => ne_of_lt hp)
  have h1 : Tendsto (fun p : ℝ × ℝ => toC (slope c p.1 p.2)) l (𝓝 (toC (deriv c a))) :=
    (continuous_toC.tendsto (deriv c a)).comp hslope
  have h2 : Tendsto (fun p : ℝ × ℝ => dirOf (toC (slope c p.1 p.2))) l (𝓝 (tangDir c a)) :=
    (continuousAt_dirOf (toC_ne_zero_iff.mpr (hc.deriv_ne_zero a))).tendsto.comp h1
  refine h2.congr' ?_
  filter_upwards [hw] with p hp
  have h : c p.2 - c p.1 = (p.2 - p.1) • slope c p.1 p.2 := by
    simpa using (sub_smul_slope c p.1 p.2).symm
  rw [secDir, h, toC_smul, dirOf_ofReal_mul_pos (sub_pos.mpr hp)]

/-- The open middle band `{s < t < s + 2π}` of the plane. -/
def midBand : Set (ℝ × ℝ) := {p | p.1 < p.2 ∧ p.2 < p.1 + 2 * Real.pi}

lemma isOpen_midBand : IsOpen midBand := by
  have h1 : IsOpen {p : ℝ × ℝ | p.1 < p.2} := isOpen_lt continuous_fst continuous_snd
  have h2 : IsOpen {p : ℝ × ℝ | p.2 < p.1 + 2 * Real.pi} :=
    isOpen_lt continuous_snd (continuous_fst.add continuous_const)
  show IsOpen {p : ℝ × ℝ | p.1 < p.2 ∧ p.2 < p.1 + 2 * Real.pi}
  rw [Set.ofPred_and]
  exact h1.inter h2

lemma closure_midBand_subset :
    closure midBand ⊆ {p : ℝ × ℝ | p.1 ≤ p.2 ∧ p.2 ≤ p.1 + 2 * Real.pi} := by
  refine closure_minimal ?_ ?_
  · intro p hp
    exact ⟨le_of_lt hp.1, le_of_lt hp.2⟩
  · exact (isClosed_le continuous_fst continuous_snd).inter
      (isClosed_le continuous_snd (continuous_fst.add continuous_const))

/-- As `(s,t) → (a, a+2π)` with `s < t`, the secant direction tends to the negated tangent
direction: the two parameters differ by a full period in the limit. -/
lemma tendsto_secDir_corner (c : ℝ → ℝ × ℝ) (hc : RegCurve c) (a : ℝ) :
    Tendsto (fun p : ℝ × ℝ => secDir c p.1 p.2)
      (𝓝 (a, a + 2 * Real.pi) ⊓ 𝓟 midBand) (𝓝 (-(tangDir c a))) := by
  set l : Filter (ℝ × ℝ) := 𝓝 (a, a + 2 * Real.pi) ⊓ 𝓟 midBand with hl
  have hw : ∀ᶠ p in l, midBand p := by
    rw [hl]; exact eventually_inf_principal.mpr (Eventually.of_forall fun p hp => hp)
  have hu : Tendsto (fun p : ℝ × ℝ => p.1) l (𝓝 a) :=
    (continuous_fst.tendsto (a, a + 2 * Real.pi)).mono_left inf_le_left
  have hv : Tendsto (fun p : ℝ × ℝ => p.2 - 2 * Real.pi) l (𝓝 a) := by
    have h2 : Tendsto (fun p : ℝ × ℝ => p.2) l (𝓝 (a + 2 * Real.pi)) :=
      (continuous_snd.tendsto (a, a + 2 * Real.pi)).mono_left inf_le_left
    simpa using h2.sub (tendsto_const_nhds (x := (2 * Real.pi : ℝ)))
  have hne : ∀ᶠ p in l, p.1 ≠ p.2 - 2 * Real.pi := hw.mono (fun p hp => by
    have := hp.2; intro h; linarith)
  have hslope := slope_tendsto_general c hc.contDiff a hu hv hne
  have h1 : Tendsto (fun p : ℝ × ℝ => toC (slope c p.1 (p.2 - 2 * Real.pi))) l
      (𝓝 (toC (deriv c a))) :=
    (continuous_toC.tendsto (deriv c a)).comp hslope
  have h2 : Tendsto (fun p : ℝ × ℝ => dirOf (toC (slope c p.1 (p.2 - 2 * Real.pi)))) l
      (𝓝 (tangDir c a)) :=
    (continuousAt_dirOf (toC_ne_zero_iff.mpr (hc.deriv_ne_zero a))).tendsto.comp h1
  have h3 : Tendsto (fun p : ℝ × ℝ => -(dirOf (toC (slope c p.1 (p.2 - 2 * Real.pi))))) l
      (𝓝 (-(tangDir c a))) := h2.neg
  refine h3.congr' ?_
  filter_upwards [hw] with p hp
  have hper : c p.2 = c (p.2 - 2 * Real.pi) := by
    simpa [sub_add_cancel] using hc.periodic (p.2 - 2 * Real.pi)
  have hne0 : slope c p.1 (p.2 - 2 * Real.pi) ≠ 0 :=
    slope_ne_zero_of_ne c (by intro h; linarith [hp.2, h])
      (by rw [← hper]; exact c_ne_of_gap c hc hp.1 hp.2)
  have hz : toC (slope c p.1 (p.2 - 2 * Real.pi)) ≠ 0 := toC_ne_zero_iff.mpr hne0
  have h : c p.2 - c p.1 = (p.2 - 2 * Real.pi - p.1) • slope c p.1 (p.2 - 2 * Real.pi) := by
    rw [hper]
    simpa using (sub_smul_slope c p.1 (p.2 - 2 * Real.pi)).symm
  rw [secDir, h, toC_smul, dirOf_ofReal_mul_neg (by linarith [hp.2]) hz]

/-- Version of `tendsto_secDir_diag` at an arbitrary diagonal point `p` with `p.1 = p.2`. -/
lemma tendsto_secDir_diag' (c : ℝ → ℝ × ℝ) (hc : RegCurve c) {p : ℝ × ℝ} (hp : p.1 = p.2) :
    Tendsto (fun q : ℝ × ℝ => secDir c q.1 q.2) (𝓝 p ⊓ 𝓟 {q | q.1 < q.2})
      (𝓝 (tangDir c p.1)) := by
  obtain ⟨u, v⟩ := p
  simp only at hp
  subst hp
  exact tendsto_secDir_diag c hc u

/-- Version of `tendsto_secDir_corner` at an arbitrary point `p` with `p.2 = p.1 + 2π`. -/
lemma tendsto_secDir_corner' (c : ℝ → ℝ × ℝ) (hc : RegCurve c) {p : ℝ × ℝ}
    (hp : p.2 = p.1 + 2 * Real.pi) :
    Tendsto (fun q : ℝ × ℝ => secDir c q.1 q.2) (𝓝 p ⊓ 𝓟 midBand)
      (𝓝 (-(tangDir c p.1))) := by
  obtain ⟨u, v⟩ := p
  simp only at hp
  subst hp
  exact tendsto_secDir_corner c hc u

/-- The two-variable secant direction is continuous wherever `c` takes different values. -/
lemma continuousAt_secDir_pair (c : ℝ → ℝ × ℝ) (hc : RegCurve c) {u v : ℝ}
    (h : c v ≠ c u) : ContinuousAt (fun q : ℝ × ℝ => secDir c q.1 q.2) (u, v) := by
  have h1 : Continuous fun q : ℝ × ℝ => toC (c q.2 - c q.1) :=
    continuous_toC.comp (((hc.contDiff.continuous.comp continuous_snd).sub
      (hc.contDiff.continuous.comp continuous_fst)))
  have h2 : ContinuousAt dirOf (toC (c v - c u)) :=
    continuousAt_dirOf (toC_ne_zero_iff.mpr (sub_ne_zero.mpr h))
  have h4 : ContinuousAt (fun q : ℝ × ℝ => dirOf (toC (c q.2 - c q.1))) (u, v) :=
    ContinuousAt.comp (g := dirOf) (f := fun q : ℝ × ℝ => toC (c q.2 - c q.1))
      h2 h1.continuousAt
  simpa only [secDir] using h4

/-! ## The auxiliary globally continuous map -/

/-- The auxiliary map.  On the middle band `s < t < s + 2π` it is the secant direction, on
`t + 2π ≤ s` (and on the diagonal and the antidiagonal, where it is forced by continuity) it is
`±` the tangent direction.  It agrees with `sigmaPt c t₀` on the triangle `tri t₀`. -/
noncomputable def sigmaAux (c : ℝ → ℝ × ℝ) (p : ℝ × ℝ) : Circle :=
  if p.1 < p.2 then
    (if p.2 < p.1 + 2 * Real.pi then secDir c p.1 p.2 else -(tangDir c p.1))
  else tangDir c p.1

lemma continuous_sigmaAux (c : ℝ → ℝ × ℝ) (hc : RegCurve c) : Continuous (sigmaAux c) := by
  have htg : Continuous fun q : ℝ × ℝ => tangDir c q.1 :=
    (continuous_tangDir c hc).comp continuous_fst
  -- on the two closed halves of the complement of the middle band
  have hC₁ : ContinuousOn (sigmaAux c) {p : ℝ × ℝ | p.2 ≤ p.1} := by
    refine htg.continuousOn.congr ?_
    intro q hq
    have hq' : q.2 ≤ q.1 := hq
    simp only [sigmaAux]
    rw [if_neg (not_lt.mpr hq')]
  have hC₂ : ContinuousOn (sigmaAux c) {p : ℝ × ℝ | p.1 + 2 * Real.pi ≤ p.2} := by
    have hneg : Continuous fun q : ℝ × ℝ => -(tangDir c q.1) := htg.neg
    refine hneg.continuousOn.congr ?_
    intro q hq
    have hq' : q.1 + 2 * Real.pi ≤ q.2 := hq
    have hlt : q.1 < q.2 := by linarith [hq', Real.pi_pos]
    simp only [sigmaAux]
    rw [if_pos hlt, if_neg (not_lt.mpr hq')]
  have hcompl : ContinuousOn (sigmaAux c) midBandᶜ := by
    have hunion : midBandᶜ =
        {p : ℝ × ℝ | p.2 ≤ p.1} ∪ {p : ℝ × ℝ | p.1 + 2 * Real.pi ≤ p.2} := by
      ext p
      constructor
      · intro h
        by_cases h2 : p.1 < p.2
        · refine Or.inr ?_
          by_contra h3
          exact h ⟨h2, not_le.mp h3⟩
        · exact Or.inl (not_lt.mp h2)
      · rintro (h | h) ⟨h1, h2⟩
        · exact absurd h1 (not_lt.mpr h)
        · exact absurd h2 (not_lt.mpr h)
    rw [hunion]
    exact hC₁.union_of_isClosed hC₂ (isClosed_le continuous_snd continuous_fst)
      (isClosed_le (continuous_fst.add continuous_const) continuous_snd)
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p ∈ midBand
  · -- in the open middle band: locally the secant direction
    have h1 : ContinuousAt (fun q : ℝ × ℝ => secDir c q.1 q.2) p :=
      continuousAt_secDir_pair c hc (Ne.symm (c_ne_of_gap c hc hp.1 hp.2))
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_midBand.mem_nhds hp] with q hq
    simp only [sigmaAux]; rw [if_pos hq.1, if_pos hq.2]
  · -- outside the middle band: split `𝓝 p` into the band and its closed complement
    have hsplit : 𝓝 p = 𝓝[midBand] p ⊔ 𝓝[midBandᶜ] p := by
      rw [← nhdsWithin_union, Set.union_compl_self, nhdsWithin_univ]
    rw [ContinuousAt, hsplit]
    refine Tendsto.sup ?_ (hcompl p hp)
    by_cases hpcl : p ∈ closure midBand
    · have hpmem' : p.1 ≤ p.2 ∧ p.2 ≤ p.1 + 2 * Real.pi := closure_midBand_subset hpcl
      rcases lt_or_eq_of_le hpmem'.1 with hlt | heq
      · -- the corner: `p.2 = p.1 + 2π`
        have hpe : p.2 = p.1 + 2 * Real.pi := by
          rcases lt_or_eq_of_le hpmem'.2 with h | h
          · exact absurd (show midBand p from ⟨hlt, h⟩) hp
          · exact h
        have hval : sigmaAux c p = -(tangDir c p.1) := by
          simp only [sigmaAux]
          rw [if_pos hlt, if_neg (by rw [hpe]; exact lt_irrefl _)]
        have hev : (fun q : ℝ × ℝ => secDir c q.1 q.2) =ᶠ[𝓝[midBand] p] (sigmaAux c) := by
          filter_upwards [self_mem_nhdsWithin] with q hq
          simp only [sigmaAux]; rw [if_pos hq.1, if_pos hq.2]
        rw [hval]
        exact (tendsto_secDir_corner' c hc hpe).congr' hev
      · -- the diagonal: `p.1 = p.2`
        have hle : 𝓝[midBand] p ≤ 𝓝 p ⊓ 𝓟 {q : ℝ × ℝ | q.1 < q.2} := by
          rw [nhdsWithin]
          exact le_inf inf_le_left (le_trans inf_le_right
            (Filter.principal_mono.mpr (fun q hq => hq.1)))
        have hval : sigmaAux c p = tangDir c p.1 := by
          simp only [sigmaAux]
          rw [if_neg (by rw [heq]; exact lt_irrefl _)]
        have hev : (fun q : ℝ × ℝ => secDir c q.1 q.2) =ᶠ[𝓝[midBand] p] (sigmaAux c) := by
          filter_upwards [self_mem_nhdsWithin] with q hq
          simp only [sigmaAux]; rw [if_pos hq.1, if_pos hq.2]
        rw [hval]
        exact ((tendsto_secDir_diag' c hc heq).mono_left hle).congr' hev
    · -- not in the closure of the band: the band contributes nothing
      rw [notMem_closure_iff_nhdsWithin_eq_bot.mp hpcl]
      exact tendsto_bot

/-! ## Agreement with `sigmaPt` on the triangle -/

/-- On the closed triangle `t₀ ≤ s ≤ t ≤ t₀ + 2π` the map `sigmaAux c` coincides with
`sigmaPt c t₀`. -/
lemma sigmaAux_eq_sigmaPt (c : ℝ → ℝ × ℝ) (_hc : RegCurve c) (t₀ : ℝ) {p : ℝ × ℝ}
    (hp : p ∈ tri t₀) : sigmaAux c p = sigmaPt c t₀ p := by
  obtain ⟨h1, h2, h3⟩ := hp
  have hle : p.2 ≤ p.1 + 2 * Real.pi := by linarith
  rcases lt_trichotomy p.1 p.2 with hlt | heq | hgt
  · -- `p.1 < p.2`
    rcases lt_or_eq_of_le hle with hlt2 | heq2
    · -- strictly inside the middle band
      have hA : sigmaAux c p = secDir c p.1 p.2 := by
        simp only [sigmaAux]; rw [if_pos hlt, if_pos hlt2]
      have hB : sigmaPt c t₀ p = secDir c p.1 p.2 := by
        simp only [sigmaPt]
        rw [if_neg (by rintro ⟨hp1, hp2⟩; rw [← hp1] at hp2; linarith)]
        rw [if_pos hlt]
      rw [hA, hB]
    · -- the corner
      have hp1 : p.1 = t₀ := by linarith
      have hp2 : p.2 = t₀ + 2 * Real.pi := by linarith
      have hA : sigmaAux c p = -(tangDir c p.1) := by
        simp only [sigmaAux]; rw [if_pos hlt, if_neg (not_lt.mpr heq2.ge)]
      have hB : sigmaPt c t₀ p = -(tangDir c t₀) := by
        simp only [sigmaPt]; rw [if_pos ⟨hp1, hp2⟩]
      rw [hA, hB, hp1]
  · -- the diagonal `p.1 = p.2`
    have hA : sigmaAux c p = tangDir c p.1 := by
      simp only [sigmaAux]; rw [if_neg (not_lt.mpr heq.ge)]
    have hB : sigmaPt c t₀ p = tangDir c p.1 := by
      simp only [sigmaPt]
      rw [if_neg (by rintro ⟨hp1, hp2⟩; rw [← hp1] at hp2; linarith [hp2, heq, Real.pi_pos])]
      rw [if_neg (not_lt.mpr heq.ge)]
    rw [hA, hB]
  · -- `p.1 > p.2` contradicts the triangle
    linarith

/-! ## The main theorem -/

/-- Hopf's secant map on the closed triangle is continuous for a regular closed plane curve. -/
theorem sigma_continuous (c : ℝ → ℝ × ℝ) (hc : Work.Drive.RegCurve c) (t₀ : ℝ) :
    Continuous (Work.Drive.sigma c t₀) := by
  have hcont : Continuous (sigmaAux c) := continuous_sigmaAux c hc
  have hfun : sigma c t₀ = fun p : tri t₀ => sigmaAux c (p : ℝ × ℝ) := by
    funext p
    exact (sigmaAux_eq_sigmaPt c hc t₀ p.2).symm
  rw [hfun]
  exact hcont.comp continuous_subtype_val

end

end Work.Drive

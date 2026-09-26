import Submission.Work.Smooth.JordanSeparation.LocalSides
import Submission.Work.Smooth.JordanSeparation.FrontierComponent
import Submission.Work.Smooth.JordanSeparation.SimpleCurves
import Submission.Work.Smooth.JordanSeparation.frontier_eq_trace

/-!
# At most two complementary domains, from the non-separation of a proper subcontinuum

The Jordan separation theorem for a `C¹` simple closed plane curve is reduced here to the single
classical statement that a *proper* subcontinuum of the curve does not separate the plane
(`hArc` below; it is a corollary of the classical theorem that an arc does not separate the plane).

* `frontier_eq_trace_of_component` — every component of the complement has frontier the whole
  curve;
* `atMostTwo_of_no_separation` — hence there are at most two components.
-/

open Set Metric
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- **Every complementary domain has the whole curve as its frontier.**  Assuming that the
complement of every proper subcontinuum of the trace is path connected, the frontier of each
component of the complement of a simple `C¹` closed curve is the whole trace. -/
theorem frontier_eq_trace_of_component (c : SmoothPlaneCurve) (_hs : c.toPlaneCurve.IsSimple)
    (hArc : ∀ S : Set ℂ, S ⊆ c.trace → IsConnected S → IsCompact S → S ≠ c.trace →
      IsPathConnected Sᶜ)
    {x : ℂ} (hx : x ∉ c.trace) :
    frontier (connectedComponentIn c.traceᶜ x) = c.trace := by
  set C : Set ℂ := connectedComponentIn c.traceᶜ x with hC
  have hKp : IsPreconnected c.trace := by
    rw [PlaneCurve.trace_eq_image_Icc]
    exact isPreconnected_Icc.image _ c.cont.continuousOn
  have hKne : c.trace.Nonempty := ⟨c.γ 0, c.mem_trace 0⟩
  have hfront := frontier_component_continuum c.isCompact_trace hKp hKne hx
  by_contra hne
  have hSsub : frontier C ⊆ c.trace := by
    rw [frontier_connectedComponentIn_eq c.isClosed_trace]
    exact Set.inter_subset_right
  have hSc : IsConnected (frontier C) := ⟨hfront.1, hfront.2⟩
  have hScomp : IsCompact (frontier C) := by
    rw [frontier_connectedComponentIn_eq c.isClosed_trace]
    exact c.isCompact_trace.of_isClosed_subset (isClosed_closure.inter c.isClosed_trace)
      Set.inter_subset_right
  obtain ⟨p, hpK, hpS⟩ :=
    Set.exists_of_ssubset (lt_of_le_of_ne hSsub hne)
  have hpath : IsPathConnected (frontier C)ᶜ := hArc _ hSsub hSc hScomp hne
  have hxC : x ∈ C := mem_connectedComponentIn hx
  have hCopen : IsOpen C := c.isOpen_compl_trace.connectedComponentIn
  have hxS : x ∈ (frontier C)ᶜ := by
    rw [Set.mem_compl_iff]
    intro h
    rw [hCopen.frontier_eq] at h
    exact h.2 hxC
  have hpS' : p ∈ (frontier C)ᶜ := hpS
  obtain ⟨γ, hγ⟩ := hpath.joinedIn (x := x) hxS (y := p) hpS' 
  -- the first time the path meets the trace
  set T : Set (Set.Icc (0:ℝ) 1) := {t | (γ t : ℂ) ∈ c.trace} with hTdef
  have hTclosed : IsClosed T := c.isClosed_trace.preimage γ.continuous
  have hTne : T.Nonempty := ⟨1, by
    rw [hTdef]; simp only [Set.mem_setOf_eq]; rw [Path.target]; exact hpK⟩
  obtain ⟨t₀, ht₀T, ht₀min⟩ := (isCompact_univ.of_isClosed_subset hTclosed (subset_univ T)).exists_isMinOn
    hTne continuous_id.continuousOn
  have ht₀K : (γ t₀ : ℂ) ∈ c.trace := ht₀T
  have ht₀ne : t₀ ≠ 0 := by
    intro h0
    rw [h0, Path.source] at ht₀K
    exact hx ht₀K
  have ht₀pos : (0 : ℝ) < (t₀ : ℝ) := by
    rcases lt_or_eq_of_le t₀.2.1 with h | h
    · exact h
    · exact absurd (Subtype.ext h).symm ht₀ne
  -- the points before `t₀` avoid the trace, hence lie in `C`
  set S : Set (Set.Icc (0:ℝ) 1) := {t | (t : ℝ) < (t₀ : ℝ)} with hSdef
  have hSpre : IsPreconnected S := by
    rw [isPreconnected_iff_ordConnected]
    refine ⟨fun a ha b hb c hc => ?_⟩
    rw [hSdef] at ha hb ⊢
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [Set.mem_Icc] at hc
    exact lt_of_le_of_lt hc.2 hb
  have hSsubC : γ '' S ⊆ C := by
    rintro z ⟨t, ht, rfl⟩
    rw [hSdef] at ht
    simp only [Set.mem_setOf_eq] at ht
    have htT : t ∉ T := fun hT => absurd (ht₀min hT) (not_le.mpr ht)
    have hpre : IsPreconnected (γ '' S) := hSpre.image _ γ.continuous.continuousOn
    refine hpre.subset_connectedComponentIn ?_ ?_ (⟨t, ht, rfl⟩ : γ t ∈ γ '' S)
    · exact ⟨0, by rw [hSdef]; simp only [Set.mem_setOf_eq]; exact ht₀pos, Path.source γ⟩
    · intro z hz
      obtain ⟨t, htS, rfl⟩ := hz
      rw [Set.mem_compl_iff]
      intro htT
      have htT' : t ∈ T := by rw [hTdef]; exact htT
      have htlt : (t : ℝ) < (t₀ : ℝ) := by
        rw [hSdef] at htS
        exact htS
      exact absurd (ht₀min htT') (not_le.mpr htlt)
  -- hence `γ t₀ ∈ closure C ∩ trace`
  have ht₀cl : t₀ ∈ closure S := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨⟨max 0 ((t₀ : ℝ) - ε / 2), ?_⟩, ?_, ?_⟩
    · exact ⟨le_max_left _ _, max_le zero_le_one (by linarith [t₀.2.2, hε])⟩
    · rw [hSdef]
      simp only [Set.mem_setOf_eq]
      by_cases h : (t₀ : ℝ) - ε / 2 ≤ 0
      · rw [max_eq_left h]; exact ht₀pos
      · have h' : 0 ≤ (t₀ : ℝ) - ε / 2 := le_of_lt (not_le.mp h)
        rw [max_eq_right h']; linarith
    · show |(t₀ : ℝ) - (max 0 ((t₀ : ℝ) - ε / 2))| < ε
      by_cases h : (t₀ : ℝ) - ε / 2 ≤ 0
      · rw [max_eq_left h, sub_zero, abs_of_pos ht₀pos]
        linarith
      · have h' : 0 ≤ (t₀ : ℝ) - ε / 2 := le_of_lt (not_le.mp h)
        rw [max_eq_right h', sub_sub_cancel, abs_of_pos (by linarith : (0:ℝ) < ε / 2)]
        linarith
  have hmem : γ t₀ ∈ closure C :=
    closure_mono hSsubC (image_closure_subset_closure_image γ.continuous ⟨t₀, ht₀cl, rfl⟩)
  have : γ t₀ ∈ frontier C := by
    rw [frontier_connectedComponentIn_eq c.isClosed_trace]
    exact ⟨hmem, ht₀K⟩
  exact hγ t₀ this

/-- **At most two components, from the non-separation of a proper subcontinuum.**  `hArc` is the
classical statement that the complement of a proper subcontinuum of a simple closed curve is path
connected (a corollary of "an arc does not separate the plane"). -/
theorem atMostTwo_of_no_separation (c : SmoothPlaneCurve) (hs : c.toPlaneCurve.IsSimple)
    (hArc : ∀ S : Set ℂ, S ⊆ c.trace → IsConnected S → IsCompact S → S ≠ c.trace →
      IsPathConnected Sᶜ) :
    ∀ x y z : ℂ, x ∉ c.trace → y ∉ c.trace → z ∉ c.trace →
      connectedComponentIn c.traceᶜ x = connectedComponentIn c.traceᶜ y ∨
      connectedComponentIn c.traceᶜ x = connectedComponentIn c.traceᶜ z ∨
      connectedComponentIn c.traceᶜ y = connectedComponentIn c.traceᶜ z := by
  intro x y z hx hy hz
  by_contra hcon
  have hxy : connectedComponentIn c.traceᶜ x ≠ connectedComponentIn c.traceᶜ y :=
    fun h => hcon (Or.inl h)
  have hxz : connectedComponentIn c.traceᶜ x ≠ connectedComponentIn c.traceᶜ z :=
    fun h => hcon (Or.inr (Or.inl h))
  have hyz : connectedComponentIn c.traceᶜ y ≠ connectedComponentIn c.traceᶜ z :=
    fun h => hcon (Or.inr (Or.inr h))
  -- a regular parameter, and the local sides there
  obtain ⟨a, ha⟩ := exists_deriv_ne_zero_of_isSimple c hs
  set c' : SmoothPlaneCurve := shiftCurve c a with hc'
  have hreg' : deriv c'.γ 0 ≠ 0 := by rw [hc', deriv_shiftCurve, zero_add]; exact ha
  have hs' : c'.toPlaneCurve.IsSimple := by rw [hc']; exact shiftCurve_isSimple c a hs
  have htr : c'.trace = c.trace := by rw [hc']; exact shiftCurve_trace c a
  have hN0 : ‖normalField c' 0‖ = 1 := by
    have h : normalField c' 0 = locN c' := rfl
    rw [h, locN, norm_mul, Complex.norm_I, one_mul]
    exact norm_locE c' hreg'
  obtain ⟨U, P, M, hUopen, hpU, hPpre, hMpre, hPne, hMne, hPoff, hMoff, hcover⟩ :=
    local_sides c' hs' hreg'
  have hPoff' : P ⊆ c.traceᶜ := fun z hz => by rw [← htr]; exact hPoff hz
  have hMoff' : M ⊆ c.traceᶜ := fun z hz => by rw [← htr]; exact hMoff hz
  -- the index jumps at `γ a`
  obtain ⟨δ, hδpos, hjump⟩ := ind_jump_of_deriv_ne_zero c' hreg' hs'
  obtain ⟨ρ, hρpos, hρU⟩ := Metric.isOpen_iff.mp hUopen (c'.γ 0) hpU
  set s : ℝ := min (δ / 2) (ρ / 2) with hsdef
  have hs0 : 0 < s := by rw [hsdef]; exact lt_min (by linarith) (by linarith)
  have hsδ : s < δ := by
    rw [hsdef]; exact lt_of_le_of_lt (min_le_left (δ / 2) (ρ / 2)) (by linarith)
  have hsρ : s < ρ := by
    rw [hsdef]; exact lt_of_le_of_lt (min_le_right (δ / 2) (ρ / 2)) (by linarith)
  obtain ⟨hzp, hzm, hsub⟩ := hjump s hs0 hsδ
  set zp : ℂ := c'.γ 0 + (s : ℂ) * normalField c' 0 with hzpdef
  set zm : ℂ := c'.γ 0 - (s : ℂ) * normalField c' 0 with hzmdef
  have hzpU : zp ∈ U := by
    refine hρU ?_
    rw [Metric.mem_ball, hzpdef, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, hN0, mul_one, abs_of_pos hs0]
    exact hsρ
  have hzmU : zm ∈ U := by
    refine hρU ?_
    rw [Metric.mem_ball, hzmdef, dist_eq_norm,
      show c'.γ 0 - (s : ℂ) * normalField c' 0 - c'.γ 0 = -((s:ℂ) * normalField c' 0) from by ring,
      norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, hN0, mul_one, abs_of_pos hs0]
    exact hsρ
  have hzpK : zp ∉ c'.trace := hzp
  have hzmK : zm ∉ c'.trace := hzm
  have hzpK' : zp ∉ c.trace := by rw [← htr]; exact hzpK
  have hzmK' : zm ∉ c.trace := by rw [← htr]; exact hzmK
  -- the two components at the jump
  set Dp : Set ℂ := connectedComponentIn c.traceᶜ zp with hDp
  set Dm : Set ℂ := connectedComponentIn c.traceᶜ zm with hDm
  have hDpne : Dp ≠ Dm := by
    intro heq
    have hpre : IsPreconnected Dp := isPreconnected_connectedComponentIn
    have hsub' : Dp ⊆ c.traceᶜ := connectedComponentIn_subset _ _
    have h1 : zp ∈ Dp := mem_connectedComponentIn hzpK'
    have h2 : zm ∈ Dp := by rw [heq]; exact mem_connectedComponentIn hzmK'
    have e1 : ind c' zp = ind c zp := by rw [hc']; exact ind_shiftCurve c a hzpK'
    have e2 : ind c' zm = ind c zm := by rw [hc']; exact ind_shiftCurve c a hzmK'
    have hconst : ind c zp = ind c zm := ind_const_on_preconnected c hpre hsub' h1 h2
    rw [e1, e2, hconst] at hsub
    linarith
  -- the two local sides lie in the two components
  obtain ⟨yP, hyP⟩ := hPne
  obtain ⟨yM, hyM⟩ := hMne
  have hzpPM : zp ∈ P ∪ M := hcover ⟨hzpU, hzpK⟩
  have hzmPM : zm ∈ P ∪ M := hcover ⟨hzmU, hzmK⟩
  have hPD : connectedComponentIn c.traceᶜ yP ≠ connectedComponentIn c.traceᶜ yM := by
    intro heq
    have h1 : ∀ w ∈ P ∪ M, connectedComponentIn c.traceᶜ w = connectedComponentIn c.traceᶜ yP := by
      intro w hw
      rcases hw with hw | hw
      · exact (connectedComponentIn_eq (hPpre.subset_connectedComponentIn hyP hPoff' hw)).symm
      · have h1 : connectedComponentIn c.traceᶜ w = connectedComponentIn c.traceᶜ yM :=
          (connectedComponentIn_eq (hMpre.subset_connectedComponentIn hyM hMoff' hw)).symm
        rw [h1, heq]
    exact hDpne ((h1 zp hzpPM).trans (h1 zm hzmPM).symm)
  -- every component of the complement meets `U`, hence is one of the two
  have hpK : c'.γ 0 ∈ c.trace := by rw [← htr]; exact c'.mem_trace 0
  have hkey : ∀ w : ℂ, w ∉ c.trace →
      connectedComponentIn c.traceᶜ w = connectedComponentIn c.traceᶜ yP ∨
      connectedComponentIn c.traceᶜ w = connectedComponentIn c.traceᶜ yM := by
    intro w hw
    have hfr := frontier_eq_trace_of_component c hs hArc hw
    have hmem : c'.γ 0 ∈ closure (connectedComponentIn c.traceᶜ w) := by
      have hpF : c'.γ 0 ∈ frontier (connectedComponentIn c.traceᶜ w) := by
        rw [hfr]; exact hpK
      exact frontier_subset_closure hpF
    obtain ⟨y, hyU, hyC⟩ := mem_closure_iff.mp hmem U hUopen hpU
    have hyK : y ∉ c.trace := connectedComponentIn_subset _ _ hyC
    have hyPM : y ∈ P ∪ M := hcover ⟨hyU, by rw [htr]; exact hyK⟩
    have hycomp : connectedComponentIn c.traceᶜ y = connectedComponentIn c.traceᶜ w :=
      (connectedComponentIn_eq hyC).symm
    rcases hyPM with hyP' | hyM'
    · left
      rw [← hycomp]
      exact (connectedComponentIn_eq (hPpre.subset_connectedComponentIn hyP hPoff' hyP')).symm
    · right
      rw [← hycomp]
      exact (connectedComponentIn_eq (hMpre.subset_connectedComponentIn hyM hMoff' hyM')).symm
  rcases hkey x hx with hx' | hx' <;> rcases hkey y hy with hy' | hy' <;>
    rcases hkey z hz with hz' | hz'
  all_goals
    first
      | exact hxy (hx'.trans hy'.symm)
      | exact hxy (hy'.trans hx'.symm)
      | exact hxz (hx'.trans hz'.symm)
      | exact hxz (hz'.trans hx'.symm)
      | exact hyz (hy'.trans hz'.symm)
      | exact hyz (hz'.trans hy'.symm)

end

end Work.Smooth.JordanSeparation

import Mathlib
import Submission.Work.Smooth.SphereJordan.brouwer_disc
import Submission.Work.Smooth.JordanSeparation.FrontierComponent
import Submission.Work.Smooth.JordanSeparation.bounded_component_of_notMem

/-!
# An arc does not separate the plane

`Work.Smooth.JordanSeparation.arc_not_separate`: the complement of the image of a closed interval
under a continuous injective map `f : ℝ → ℂ` is path connected.

The proof follows R. Luisto, *Proof of the Jordan curve theorem*, Lemma 2.12.  If the complement of
the arc `A` had a bounded component `Ω` with `x₀ ∈ Ω`, one first extends the parameter of the arc
to a continuous **retraction** `s : ℂ → ℂ` of the plane onto `A` (`arc_retraction_aux`, Tietze
extension of the inverse parameterisation), and uses it to build a continuous map
`q : closedBall x₀ r → closedBall x₀ r ∖ {x₀}` which fixes the boundary sphere pointwise.  The
radial projection of `q` followed by the antipodal map is then a continuous self-map of the closed
ball without fixed points, contradicting Brouwer's fixed point theorem
(`brouwer_closedBall_aux`, a rescaling of `Work.Smooth.SphereJordan.brouwer_disc`).

Consequently `Aᶜ` has no bounded component; since it has at most one unbounded component
(`Work.Smooth.JordanSeparation.bounded_component_of_notMem`) it is preconnected, and being open it
is path connected.
-/

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

private theorem isPreconnected_compl_closedBall_aux {x0 : ℂ} {r : ℝ} (hr : 0 < r) :
    IsPreconnected ((Metric.closedBall x0 r)ᶜ) := by
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  have heq : (Metric.closedBall x0 r)ᶜ = {z : ℂ | r < ‖z - x0‖} := by
    ext z
    rw [Set.mem_compl_iff, Metric.mem_closedBall, not_le, dist_eq_norm, Set.mem_ofPred_eq]
  rw [heq]
  have hprod : IsPreconnected (Set.Ioi r ×ˢ Metric.sphere (0 : ℂ) 1) :=
    isPreconnected_Ioi.prod (isPreconnected_sphere hrank 0 1)
  have hcont : ContinuousOn (fun p : ℝ × ℂ => x0 + p.1 • p.2)
      (Set.Ioi r ×ˢ Metric.sphere (0 : ℂ) 1) := by fun_prop
  have himg : (fun p : ℝ × ℂ => x0 + p.1 • p.2) '' (Set.Ioi r ×ˢ Metric.sphere (0 : ℂ) 1)
      = {z : ℂ | r < ‖z - x0‖} := by
    ext z
    constructor
    · rintro ⟨⟨t, w⟩, ⟨ht, hw⟩, rfl⟩
      rw [Metric.mem_sphere, dist_zero_right] at hw
      simp only [Set.mem_ofPred_eq, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg (le_of_lt (lt_trans hr ht)), hw, mul_one]
      exact ht
    · intro hz
      simp only [Set.mem_ofPred_eq] at hz
      have hzp : 0 < ‖z - x0‖ := lt_trans hr hz
      refine ⟨(‖z - x0‖, (‖z - x0‖)⁻¹ • (z - x0)), ⟨hz, ?_⟩, ?_⟩
      · rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hzp), inv_mul_cancel₀ (ne_of_gt hzp)]
      · show x0 + ‖z - x0‖ • ((‖z - x0‖)⁻¹ • (z - x0)) = z
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hzp), one_smul]
        ring
  rw [← himg]
  exact hprod.image _ hcont

/-- Brouwer for a general closed ball, by rescaling. -/
theorem brouwer_closedBall_aux (x0 : ℂ) {r : ℝ} (hr : 0 < r) (Φ : ℂ → ℂ)
    (hΦ : ContinuousOn Φ (Metric.closedBall x0 r))
    (hΦB : ∀ z ∈ Metric.closedBall x0 r, Φ z ∈ Metric.closedBall x0 r) :
    ∃ z ∈ Metric.closedBall x0 r, Φ z = z := by
  have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  have hT : ∀ w : Work.Smooth.SphereJordan.Disc,
      x0 + (r : ℂ) * (w : ℂ) ∈ Metric.closedBall x0 r := by
    intro w
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h1 : ‖(w : ℂ)‖ ≤ 1 := by
      have := w.2; rw [Metric.mem_closedBall, dist_zero_right] at this; exact this
    have h2 : ‖x0 + (r : ℂ) * (w : ℂ) - x0‖ = r * ‖(w : ℂ)‖ := by
      rw [show x0 + (r : ℂ) * (w : ℂ) - x0 = (r : ℂ) * (w : ℂ) by ring, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    rw [h2]
    nlinarith
  let Ψ : Work.Smooth.SphereJordan.Disc → Work.Smooth.SphereJordan.Disc := fun w =>
    ⟨((Φ (x0 + (r : ℂ) * (w : ℂ)) - x0) / (r : ℂ)), by
      rw [Metric.mem_closedBall, dist_zero_right, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr, div_le_one hr]
      have h := hΦB (x0 + (r : ℂ) * (w : ℂ)) (hT w)
      rw [Metric.mem_closedBall, dist_eq_norm] at h
      exact h⟩
  have hΨcont : Continuous Ψ := by
    have hbase : Continuous fun w : Work.Smooth.SphereJordan.Disc =>
        Φ (x0 + (r : ℂ) * (w : ℂ)) := by
      have hTcont : Continuous fun w : Work.Smooth.SphereJordan.Disc =>
          (⟨x0 + (r : ℂ) * (w : ℂ), hT w⟩ : Metric.closedBall x0 r) := by
        apply Continuous.subtype_mk
        fun_prop
      have hΦc : Continuous fun v : Metric.closedBall x0 r => Φ (v : ℂ) :=
        continuousOn_iff_continuous_domRestrict.mp hΦ
      exact hΦc.comp hTcont
    exact Continuous.subtype_mk ((hbase.sub continuous_const).div_const _) _
  obtain ⟨w, hw⟩ := Work.Smooth.SphereJordan.brouwer_disc ⟨Ψ, hΨcont⟩
  have hw' : (Φ (x0 + (r : ℂ) * (w : ℂ)) - x0) / (r : ℂ) = (w : ℂ) :=
    congrArg Subtype.val hw
  have h1 : Φ (x0 + (r : ℂ) * (w : ℂ)) - x0 = (r : ℂ) * (w : ℂ) := by
    have h2 : (Φ (x0 + (r : ℂ) * (w : ℂ)) - x0) / (r : ℂ) * (r : ℂ) = (w : ℂ) * (r : ℂ) := by
      rw [hw']
    rw [div_mul_cancel₀ _ hrne] at h2
    rw [h2, mul_comm]
  refine ⟨x0 + (r : ℂ) * (w : ℂ), hT w, ?_⟩
  calc Φ (x0 + (r : ℂ) * (w : ℂ)) = (Φ (x0 + (r : ℂ) * (w : ℂ)) - x0) + x0 := by ring
    _ = (r : ℂ) * (w : ℂ) + x0 := by rw [h1]
    _ = x0 + (r : ℂ) * (w : ℂ) := by ring

/-- The main contradiction: no compact retract of the plane has a bounded complementary component. -/
theorem no_bounded_component_of_retract_aux {A : Set ℂ} (hAcomp : IsCompact A)
    (s : ℂ → ℂ) (hsc : Continuous s) (hsmem : ∀ z, s z ∈ A) (hsid : ∀ z ∈ A, s z = z)
    {x0 : ℂ} (hx0 : x0 ∉ A) (hbdd : Bornology.IsBounded (connectedComponentIn Aᶜ x0)) :
    False := by
  classical
  have hAcl : IsClosed A := hAcomp.isClosed
  set Ω : Set ℂ := connectedComponentIn Aᶜ x0 with hΩ
  have hx0Ω : x0 ∈ Ω := by rw [hΩ]; exact mem_connectedComponentIn hx0
  have hΩopen : IsOpen Ω := by rw [hΩ]; exact hAcl.isOpen_compl.connectedComponentIn
  have hfrΩ : frontier Ω ⊆ A := by
    rw [hΩ, frontier_connectedComponentIn_eq hAcl]; exact inter_subset_right
  obtain ⟨r, hrpos, hrA⟩ : ∃ r : ℝ, 0 < r ∧ A ⊆ Metric.ball x0 r := by
    obtain ⟨ρ, hρ⟩ := hAcomp.isBounded.subset_ball x0
    exact ⟨|ρ| + 1, by positivity, fun z hz =>
      Metric.ball_subset_ball (by linarith [le_abs_self ρ, abs_nonneg ρ]) (hρ hz)⟩
  have hSΩc : Metric.sphere x0 r ⊆ Ωᶜ := by
    have hextA : (Metric.closedBall x0 r)ᶜ ⊆ Aᶜ := by
      intro z hz
      rw [Set.mem_compl_iff] at hz ⊢
      exact fun hzA => hz (Metric.ball_subset_closedBall (hrA hzA))
    set e : ℂ := x0 + (((r : ℝ) + 1 : ℝ) : ℂ) with he
    have heext : e ∈ (Metric.closedBall x0 r)ᶜ := by
      rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, he,
        show x0 + ((r + 1 : ℝ) : ℂ) - x0 = ((r + 1 : ℝ) : ℂ) by ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    set W : Set ℂ := connectedComponentIn Aᶜ e with hW
    have hextW : (Metric.closedBall x0 r)ᶜ ⊆ W :=
      (isPreconnected_compl_closedBall_aux hrpos).subset_connectedComponentIn heext hextA
    have hWunbdd : ¬ Bornology.IsBounded W := by
      rw [isBounded_iff_subset_ball x0]
      rintro ⟨R, hR⟩
      have hmem : x0 + (((r + |R| + 1 : ℝ)) : ℂ) ∈ W := hextW (by
        rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_eq_norm,
          show x0 + ((r + |R| + 1 : ℝ) : ℂ) - x0 = ((r + |R| + 1 : ℝ) : ℂ) by ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [abs_nonneg R])]
        linarith [abs_nonneg R])
      have hthis := hR hmem
      rw [Metric.mem_ball, dist_eq_norm,
        show x0 + ((r + |R| + 1 : ℝ) : ℂ) - x0 = ((r + |R| + 1 : ℝ) : ℂ) by ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [abs_nonneg R])] at hthis
      linarith [le_abs_self R]
    have hWne : W ≠ Ω := fun h => hWunbdd (h.symm ▸ hbdd)
    have hSW : Metric.sphere x0 r ⊆ W := by
      intro z hz
      have hzA : z ∈ Aᶜ := by
        rw [Set.mem_compl_iff]
        intro hzA
        have h1 := hrA hzA
        rw [Metric.mem_ball] at h1
        rw [Metric.mem_sphere] at hz
        linarith [dist_comm z x0]
      obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp hAcl.isOpen_compl z hzA
      have hzcl : z ∈ closure ((Metric.closedBall x0 r)ᶜ) := by
        have hzfr : z ∈ frontier (Metric.closedBall x0 r) := by
          rw [frontier_closedBall x0 (ne_of_gt hrpos)]; exact hz
        rw [frontier_eq_closure_inter_closure] at hzfr; exact hzfr.2
      obtain ⟨w, hwext, hwz⟩ := Metric.mem_closure_iff.mp hzcl ε hεpos
      have hwball : w ∈ Metric.ball z ε := by
        rw [Metric.mem_ball, dist_comm]; exact hwz
      have hwW : w ∈ W := hextW hwext
      have h1 : Metric.ball z ε ⊆ connectedComponentIn Aᶜ w :=
        IsPreconnected.subset_connectedComponentIn (convex_ball z ε).isPreconnected hwball hεsub
      have h2 : connectedComponentIn Aᶜ w = W := by
        rw [hW]; exact (connectedComponentIn_eq hwW).symm
      exact h2 ▸ h1 (Metric.mem_ball_self hεpos)
    intro z hz
    rw [Set.mem_compl_iff]
    intro hzΩ
    exact hWne ((connectedComponentIn_eq (hSW hz)).trans (connectedComponentIn_eq hzΩ).symm)
  let q : ℂ → ℂ := fun z => if z ∈ Ω then s z else z
  have hqΩbar : ∀ z ∈ closure Ω, q z = s z := by
    intro z hz
    by_cases hzΩ : z ∈ Ω
    · simp only [q, hzΩ, if_true]
    · have hzfr : z ∈ frontier Ω := by
        rw [hΩopen.frontier_eq]; exact ⟨hz, hzΩ⟩
      simp only [q, hzΩ, if_false]
      exact (hsid z (hfrΩ hzfr)).symm
  have hqΩc : ∀ z ∈ Ωᶜ, q z = z := by
    intro z hz
    rw [Set.mem_compl_iff] at hz
    simp only [q, hz, if_false]
  have hqcont : Continuous q := by
    have h1 : ContinuousOn q (closure Ω) :=
      (hsc.continuousOn.mono (subset_univ _)).congr hqΩbar
    have h2 : ContinuousOn q (Ωᶜ) := continuousOn_id.congr hqΩc
    have h3 : ContinuousOn q (closure Ω ∪ Ωᶜ) :=
      h1.union_of_isClosed h2 isClosed_closure hΩopen.isClosed_compl
    have h4 : (univ : Set ℂ) ⊆ closure Ω ∪ Ωᶜ := by
      intro z _
      by_cases h : z ∈ Ω
      · exact Or.inl (subset_closure h)
      · exact Or.inr h
    exact continuousOn_univ.mp (h3.mono h4)
  have hqB : ∀ z ∈ Metric.closedBall x0 r, q z ∈ Metric.closedBall x0 r := by
    intro z hz
    by_cases h : z ∈ Ω
    · have hq : q z = s z := hqΩbar z (subset_closure h)
      rw [hq]; exact Metric.ball_subset_closedBall (hrA (hsmem z))
    · have hq : q z = z := hqΩc z h
      rw [hq]; exact hz
  have hqx0 : ∀ z, q z ≠ x0 := by
    intro z
    by_cases h : z ∈ Ω
    · have hq : q z = s z := hqΩbar z (subset_closure h)
      rw [hq]
      exact fun hc => hx0 (hc ▸ hsmem z)
    · have hq : q z = z := hqΩc z h
      rw [hq]
      exact fun hc => h (hc ▸ hx0Ω)
  have hqS : ∀ z ∈ Metric.sphere x0 r, q z = z := fun z hz => hqΩc z (hSΩc hz)
  let Phi : ℂ → ℂ := fun z => x0 - (r : ℂ) * ((q z - x0) / ((‖q z - x0‖ : ℝ) : ℂ))
  have hw1 : ∀ z, ‖(q z - x0) / ((‖q z - x0‖ : ℝ) : ℂ)‖ = 1 := by
    intro z
    have hne := hqx0 z
    have hpos : ‖q z - x0‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      div_self hpos]
  have hPhi_cont : ContinuousOn Phi (Metric.closedBall x0 r) := by
    have hg : ContinuousOn (fun w : ℂ => (w - x0) / ((‖w - x0‖ : ℝ) : ℂ)) {w : ℂ | w ≠ x0} := by
      refine ContinuousOn.div ((continuous_id.sub continuous_const)).continuousOn ?_ ?_
      · exact (Complex.continuous_ofReal.comp
          (continuous_norm.comp (continuous_id.sub continuous_const))).continuousOn
      · intro w hw
        rw [Complex.ofReal_ne_zero]
        exact ne_of_gt (norm_pos_iff.mpr (sub_ne_zero.mpr hw))
    have hmaps : MapsTo q (Metric.closedBall x0 r) {w : ℂ | w ≠ x0} := fun z _ => hqx0 z
    have h1 : ContinuousOn (fun z => (q z - x0) / ((‖q z - x0‖ : ℝ) : ℂ))
        (Metric.closedBall x0 r) := hg.comp hqcont.continuousOn hmaps
    exact continuousOn_const.sub (continuousOn_const.mul h1)
  have hPhiB : ∀ z ∈ Metric.closedBall x0 r, Phi z ∈ Metric.closedBall x0 r := by
    intro z hz
    have hval : ‖Phi z - x0‖ = r := by
      have hsub : Phi z - x0 = -((r : ℂ) * ((q z - x0) / ((‖q z - x0‖ : ℝ) : ℂ))) := by
        rw [show Phi z = x0 - (r : ℂ) * ((q z - x0) / ((‖q z - x0‖ : ℝ) : ℂ)) from rfl]; ring
      rw [hsub, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos,
        hw1 z, mul_one]
    rw [Metric.mem_closedBall, dist_eq_norm, hval]
  have hPhinofix : ∀ z ∈ Metric.closedBall x0 r, Phi z ≠ z := by
    intro z hz hfix
    have hval : ‖Phi z - x0‖ = r := by
      have hsub : Phi z - x0 = -((r : ℂ) * ((q z - x0) / ((‖q z - x0‖ : ℝ) : ℂ))) := by
        rw [show Phi z = x0 - (r : ℂ) * ((q z - x0) / ((‖q z - x0‖ : ℝ) : ℂ)) from rfl]; ring
      rw [hsub, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos,
        hw1 z, mul_one]
    have hznorm : ‖z - x0‖ = r := by rw [← hfix]; exact hval
    have hzS : z ∈ Metric.sphere x0 r := by rw [Metric.mem_sphere, dist_eq_norm]; exact hznorm
    have hqz : q z = z := hqS z hzS
    have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hrpos
    have hPhival : Phi z = 2 * x0 - z := by
      rw [show Phi z = x0 - (r : ℂ) * ((q z - x0) / ((‖q z - x0‖ : ℝ) : ℂ)) from rfl,
        hqz, hznorm]
      field_simp
      ring
    have hzeq : z = x0 := by
      have h2 : (2 : ℂ) * x0 = 2 * z := by
        rw [hPhival] at hfix
        linear_combination hfix
      exact (mul_left_cancel₀ (two_ne_zero) h2).symm
    rw [hzeq, sub_self, norm_zero] at hznorm
    linarith [hrpos]
  obtain ⟨z, hzB, hzfix⟩ := brouwer_closedBall_aux x0 hrpos Phi hPhi_cont hPhiB
  exact hPhinofix z hzB hzfix

/-- Tietze-based retraction onto an arc. -/
theorem arc_retraction_aux {f : ℝ → ℂ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b)
    (hinj : Set.InjOn f (Set.Icc a b)) :
    ∃ s : ℂ → ℂ, Continuous s ∧ (∀ z, s z ∈ f '' Set.Icc a b) ∧
      (∀ z ∈ f '' Set.Icc a b, s z = z) := by
  classical
  set f' : Set.Icc a b → ℂ := fun t => f (t : ℝ) with hf'
  have hf'cont : Continuous f' := hf.comp continuous_subtype_val
  have hf'inj : Function.Injective f' := fun t1 t2 h => Subtype.ext (hinj t1.2 t2.2 h)
  have he : Topology.IsEmbedding f' := (hf'cont.isClosedEmbedding hf'inj).toIsEmbedding
  let e : Set.Icc a b ≃ₜ Set.range f' := he.toHomeomorph
  have hrange : Set.range f' = f '' Set.Icc a b := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨(t : ℝ), t.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
  have hclosed : IsClosed (Set.range f') := by
    rw [hrange]; exact (isCompact_Icc.image hf).isClosed
  have he_apply : ∀ t : Set.Icc a b, ((e t : Set.range f') : ℂ) = f (t : ℝ) := fun t => rfl
  have hgcont : Continuous fun z : Set.range f' => ((e.symm z : Set.Icc a b) : ℝ) :=
    (continuous_subtype_val : Continuous (fun t : Set.Icc a b => (t : ℝ))).comp e.symm.continuous
  have hgf : ∀ z : Set.range f', f ((e.symm z : Set.Icc a b) : ℝ) = (z : ℂ) := by
    intro z
    rw [← he_apply (e.symm z)]
    exact congrArg Subtype.val (e.apply_symm_apply z)
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq (X := ℂ) hclosed
    (⟨fun z : Set.range f' => ((e.symm z : Set.Icc a b) : ℝ), hgcont⟩ : C(Set.range f', ℝ))
  have hGz : ∀ z (hz : z ∈ Set.range f'), G z = ((e.symm ⟨z, hz⟩ : Set.Icc a b) : ℝ) := by
    intro z hz
    have h := congrArg (fun φ : C(Set.range f', ℝ) => (φ : Set.range f' → ℝ)) hG
    exact congrFun h ⟨z, hz⟩
  refine ⟨fun z => f (min (max (G z) a) b), ?_, ?_, ?_⟩
  · exact hf.comp ((G.continuous.max continuous_const).min continuous_const)
  · intro z
    exact ⟨_, ⟨le_min (le_max_right _ _) hab, min_le_right _ _⟩, rfl⟩
  · intro z hz
    have hz' : z ∈ Set.range f' := by rw [hrange]; exact hz
    have hGv : G z = ((e.symm ⟨z, hz'⟩ : Set.Icc a b) : ℝ) := hGz z hz'
    have hmem : G z ∈ Set.Icc a b := by rw [hGv]; exact (e.symm ⟨z, hz'⟩).2
    have hclamp : min (max (G z) a) b = G z := by
      rw [max_eq_left hmem.1, min_eq_left hmem.2]
    change f (min (max (G z) a) b) = z
    rw [hclamp, hGv]
    exact hgf ⟨z, hz'⟩

/-- **An arc does not separate the plane.** -/
theorem arc_not_separate {f : ℝ → ℂ} (hf : Continuous f) {a b : ℝ}
    (hinj : Set.InjOn f (Set.Icc a b)) : IsPathConnected ((f '' (Set.Icc a b))ᶜ) := by
  by_cases hab : a ≤ b
  · obtain ⟨s, hsc, hsmem, hsid⟩ := arc_retraction_aux hf hab hinj
    have hAcomp : IsCompact (f '' Set.Icc a b) := isCompact_Icc.image hf
    have hAopen : IsOpen ((f '' Set.Icc a b)ᶜ) := hAcomp.isClosed.isOpen_compl
    rw [← hAopen.isConnected_iff_isPathConnected]
    have hne : ((f '' Set.Icc a b)ᶜ).Nonempty := by
      obtain ⟨ρ, hρ⟩ := hAcomp.isBounded.subset_closedBall (0 : ℂ)
      refine ⟨(((max ρ 0 : ℝ) + 1 : ℝ) : ℂ), ?_⟩
      rw [Set.mem_compl_iff]
      intro hmem
      have h1 := hρ hmem
      rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at h1
      rw [abs_of_pos (by positivity : (0:ℝ) < max ρ 0 + 1)] at h1
      linarith [le_max_left ρ (0:ℝ)]
    refine ⟨hne, ?_⟩
    obtain ⟨p, hp⟩ := hne
    have hkey : ∀ y ∈ (f '' Set.Icc a b)ᶜ,
        y ∈ connectedComponentIn (f '' Set.Icc a b)ᶜ p := by
      intro y hy
      by_contra hxy
      rcases bounded_component_of_notMem hAcomp hp hy hxy with hb | hb
      · exact no_bounded_component_of_retract_aux hAcomp s hsc hsmem hsid hp hb
      · exact no_bounded_component_of_retract_aux hAcomp s hsc hsmem hsid hy hb
    rw [show (f '' Set.Icc a b)ᶜ = connectedComponentIn (f '' Set.Icc a b)ᶜ p from
      Subset.antisymm (fun y hy => hkey y hy) (connectedComponentIn_subset _ _)]
    exact isPreconnected_connectedComponentIn
  · rw [Icc_eq_empty hab, Set.image_empty, Set.compl_empty]
    exact isPathConnected_univ

end

end Work.Smooth.JordanSeparation

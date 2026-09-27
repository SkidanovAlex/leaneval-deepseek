import Mathlib
import Submission.Work.Drive.N2.exists_levelComponentCurves
import Submission.Work.Drive.N2Lead.saddleArcs
import Submission.Work.Drive.N2C.arcLiftSaddle
import Submission.Work.Drive.N2Lead.saddlePinDefs
import Submission.Work.Drive.N2Lead.range_eq_connectedComponentIn
import Submission.Work.Drive.N2Lead.pinSetup
import Submission.Work.Drive.N2.saddlePack
import Submission.Work.Drive.N2.packetDefs
import Submission.Work.Drive.N2C.levelCurves_reverse
import Submission.Work.Drive.N2C.levelCurves_ofComponentCurves
import Submission.Work.Drive.N2.dichotomyOneComp
import Submission.Work.Drive.N2Lead.exists_hord_shifts_anti
import Submission.Work.Drive.N2Lead.exists_hord_shifts_mixed

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

/-!
# The lift data of the two anchor arcs of the saddle window

`Work.Drive.N2Lead.saddleWindowLiftData` supplies, for every small `η` whose anchor pin
`saddlePin D (f p - 3η/2) (99/50)` lies on one component of the level `f = f p - 3η/2`, a
`LevelCurves` parametrisation `L` of that level, an index `i` and the two reparametrisations
`τU`, `τL` of the upper and the lower anchor arc, with:

* `τU` is `C^∞` and strictly *antitone*, `τL` is `C^∞` and strictly monotone *or* antitone;
* in the antitone case the four endpoints are cyclically ordered as
  `τL m < τL (-m) < τU m < τU (-m) < τL m + 1` (the **split** pattern);
* in the monotone case as `τU m < τU (-m) < τL (-m) < τL m < τU m + 1` (the **Möbius** pattern).

The proof: the level curves of the anchor level (`exists_levelComponentCurves` +
`levelCurves_ofComponentCurves`); the marked component `i` through the anchor arc point at `w = 0`;
the two arc points over `Ioo (-3) 3` in the range of that component (the arc traces are connected and
`OnOneComponent` puts the two anchor points on one component); the lifts
(`Work.Drive.N2C.exists_arcReparam_up`/`_dn`), oriented so that `τU` is antitone
(`Work.Drive.N2C.levelCurves_reverse`); the span estimates
(`Work.Drive.N2.span_lt_one_of_exists_notMem` and its antitone companion), the disjointness of the
two arcs in the chart coordinate `cl_saddleZ`, and the horizontal-order lemmas
`Work.Drive.N2Lead.exists_hord_shifts_anti`/`_mixed`.
-/

section Helpers

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]

/-- The datum chart coordinate `zs = φ₀ + i φ₁` is `λ · Z` in the scaled coordinate
`Z = cl_saddleZ D 1` (`λ = ρ j / 8`). -/
lemma chartCplx_cl_saddleZ {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) (y : M) :
    chartCplx D y = ((D.ρ D.j / 8 : ℝ) : ℂ) * Work.Drive.N2.cl_saddleZ D 1 y := by
  rw [Work.Drive.N2.cl_saddleZ_apply, chartCplx, cplxE2]
  have hρ : ((D.ρ D.j / 8 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact ne_of_gt (div_pos (D.hρ D.j) (by norm_num))
  field_simp

/-- The scaled saddle chart coordinate is `C^∞` on the datum's chart source. -/
lemma contMDiffOn_cl_saddleZ {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) :
    ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Drive.N2.cl_saddleZ D 1)
      (D.φ D.j).source := by
  have h1 : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => Work.Drive.N2.cl_chartZLM (D.φ D.j y)) (D.φ D.j).source :=
    Work.Drive.N2.cl_chartZLM.contMDiff.comp_contMDiffOn (D.hφ D.j)
  have h2 := (Work.Drive.N2.cl_scaleCLM
    ((1 : ℂ) / ((D.ρ D.j / 8 : ℝ) : ℂ))).contMDiff.comp_contMDiffOn h1
  change ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun y => Work.Drive.N2.cl_scaleCLM ((1 : ℂ) / ((D.ρ D.j / 8 : ℝ) : ℂ))
      (Work.Drive.N2.cl_chartZLM (D.φ D.j y))) (D.φ D.j).source
  exact h2

/-- The upper anchor arc point lies on the anchor level. -/
lemma f_arcUpPt {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {Z : M → ℂ}
    {ηs w : ℝ} (hball : ‖arcZ ηs w‖ < 8)
    (hZrel : ∀ x : M, chartCplx D x = ((D.ρ D.j / 8 : ℝ) : ℂ) * Z x)
    (hlev : ∀ y ∈ (D.φ D.j).source, f y = f p + (D.ρ D.j / 8) ^ 2 * ((Z y) ^ 2).re) :
    f (arcUpPt D (D.ρ D.j / 8) ηs w) = f p - (D.ρ D.j / 8) ^ 2 * ηs := by
  rw [hlev _ (arcUpPt_mem_source D hball rfl),
    Z_arcUpPt D hball (div_pos (D.hρ D.j) (by norm_num)) rfl hZrel, arcZ_sq_re]
  ring

/-- The lower anchor arc point lies on the anchor level. -/
lemma f_arcDnPt {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {Z : M → ℂ}
    {ηs w : ℝ} (hball : ‖arcZ ηs w‖ < 8)
    (hZrel : ∀ x : M, chartCplx D x = ((D.ρ D.j / 8 : ℝ) : ℂ) * Z x)
    (hlev : ∀ y ∈ (D.φ D.j).source, f y = f p + (D.ρ D.j / 8) ^ 2 * ((Z y) ^ 2).re) :
    f (arcDnPt D (D.ρ D.j / 8) ηs w) = f p - (D.ρ D.j / 8) ^ 2 * ηs := by
  rw [hlev _ (by
      refine (D.φ D.j).map_target ?_
      refine Work.Drive.N2.windowBall_subset_target D D.j ?_
      rw [show -((((D.ρ D.j / 8 : ℝ)) : ℂ) * arcZ ηs w)
          = (((D.ρ D.j / 8 : ℝ)) : ℂ) * (-(arcZ ηs w)) by ring,
        cE2_norm, norm_mul, Complex.norm_of_nonneg (div_pos (D.hρ D.j) (by norm_num)).le,
        norm_neg]
      nlinarith [hball, D.hρ D.j]),
    Work.Drive.N2C.Z_arcDnPt D hball (div_pos (D.hρ D.j) (by norm_num)) rfl hZrel,
    neg_sq, arcZ_sq_re]
  ring

/-- The two anchor arcs are disjoint as point sets (the scaled chart coordinate separates them:
`Z (arcUpPt w) = arcZ η w` and `Z (arcDnPt w') = -arcZ η w'`). -/
lemma arcUpPt_ne_arcDnPt {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {Z : M → ℂ}
    {ηs : ℝ} (hηs : 0 < ηs)
    (hZrel : ∀ x : M, chartCplx D x = ((D.ρ D.j / 8 : ℝ) : ℂ) * Z x)
    {w w' : ℝ} (hw : ‖arcZ ηs w‖ < 8) (hw' : ‖arcZ ηs w'‖ < 8) :
    arcUpPt D (D.ρ D.j / 8) ηs w ≠ arcDnPt D (D.ρ D.j / 8) ηs w' := by
  intro hcon
  have hlam8 : 0 < D.ρ D.j / 8 := div_pos (D.hρ D.j) (by norm_num)
  have h1 := Z_arcUpPt D hw hlam8 rfl hZrel
  have h2 := Work.Drive.N2C.Z_arcDnPt D hw' hlam8 rfl hZrel
  have h3 : arcZ ηs w = -arcZ ηs w' := h1.symm.trans ((congrArg Z hcon).trans h2)
  have h4 : (arcZ ηs w) ^ 2 = (arcZ ηs w') ^ 2 := by rw [h3]; ring
  have h5 : w = w' := by
    have him := congrArg Complex.im h4
    rwa [arcZ_sq_im, arcZ_sq_im] at him
  subst h5
  have h6 : arcZ ηs w = 0 := by
    have h7 : arcZ ηs w + arcZ ηs w = 0 := by
      nth_rewrite 1 [h3]; ring
    rw [← two_mul] at h7
    exact (mul_eq_zero.mp h7).resolve_left (by norm_num)
  have h8 := arcZ_sq ηs w
  rw [h6] at h8
  have h9 : (0 : ℝ) = -ηs := by
    have := congrArg Complex.re h8
    simpa using this
  linarith

/-- **The parameter span of an antitone lift is `< 1`**: the antitone companion of
`Work.Drive.N2.span_lt_one_of_exists_notMem`, obtained from it by the substitution `w ↦ -w`. -/
lemma span_lt_one_of_exists_notMem_anti {γ α : ℝ → M} {τ : ℝ → ℝ}
    {u : ℝ} (hγper : ∀ x : ℝ, γ (x + 1) = γ x)
    (hγα : ∀ w ∈ Set.Icc (-u) u, γ (τ w) = α w)
    (hτc : ContinuousOn τ (Set.Icc (-u) u)) (hanti : StrictAntiOn τ (Set.Icc (-u) u)) (hu : 0 < u)
    (hx : ∃ x ∈ Set.range γ, x ∉ α '' Set.Icc (-u) u) :
    τ (-u) - τ u < 1 := by
  have hγα' : ∀ w ∈ Set.Icc (-u) u, γ (τ (-w)) = (fun y => α (-y)) w := by
    intro w hw
    exact hγα (-w) ⟨by linarith [hw.2], by linarith [hw.1]⟩
  have hτc' : ContinuousOn (fun y : ℝ => τ (-y)) (Set.Icc (-u) u) :=
    hτc.comp continuous_neg.continuousOn
      (fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩)
  have hmono' : StrictMonoOn (fun y : ℝ => τ (-y)) (Set.Icc (-u) u) := by
    intro a ha b hb hab
    exact hanti ⟨by linarith [hb.2], by linarith [hb.1]⟩
      ⟨by linarith [ha.2], by linarith [ha.1]⟩ (by linarith)
  have hx' : ∃ x ∈ Set.range γ, x ∉ (fun y => α (-y)) '' Set.Icc (-u) u := by
    obtain ⟨x, hxr, hxn⟩ := hx
    refine ⟨x, hxr, ?_⟩
    rintro ⟨w, hw, hwx⟩
    exact hxn ⟨-w, ⟨by linarith [hw.2], by linarith [hw.1]⟩, hwx⟩
  have hkey := Work.Drive.N2.span_lt_one_of_exists_notMem (γ := γ) (α := fun y => α (-y))
    (τ := fun y => τ (-y)) (u := u) hγper hγα' hτc' hmono' hu hx'
  simpa using hkey

end Helpers

section Main

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- **The lift data of the two anchor arcs, given the marked component.**  From a `LevelCurves`
parametrisation `L` of the anchor level `f = f p - λ² ηs`, an index `i` whose component carries the
two arcs over `Ioo (-3) 3`, and the chart rows of the scaled coordinate `Z`, produce the two
reparametrisations `τU`, `τL` with the split (`Or.inl`) or the Möbius (`Or.inr`) order. -/
theorem liftData_of_levelCurves {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {a m ηs : ℝ} {n : ℕ} {L : Work.Drive.N2C.LevelCurves f a n} {i : Fin n}
    (ha : a = f p - (D.ρ D.j / 8) ^ 2 * ηs)
    (hηs : 0 < ηs) (hηs1 : |ηs| ≤ 1) (hm : 0 < m) (hm3 : m < 3)
    {Z : M → ℂ} (hZrel : ∀ x : M, chartCplx D x = ((D.ρ D.j / 8 : ℝ) : ℂ) * Z x)
    (hZsm : ∀ x ∈ (D.φ D.j).source,
      ContMDiffAt (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z x)
    (hU : ∀ w ∈ Set.Ioo (-3) 3, arcUpPt D (D.ρ D.j / 8) ηs w ∈ Set.range (L.γ i))
    (hDn : ∀ w ∈ Set.Ioo (-3) 3, arcDnPt D (D.ρ D.j / 8) ηs w ∈ Set.range (L.γ i)) :
    ∃ (L' : Work.Drive.N2C.LevelCurves f a n) (τU τL : ℝ → ℝ),
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τU (Set.Ioo (-3) 3) ∧
      (∀ w ∈ Set.Ioo (-3) 3, deriv τU w ≠ 0) ∧
      StrictAntiOn τU (Set.Ioo (-3) 3) ∧
      (∀ w ∈ Set.Ioo (-3) 3, L'.γ i (τU w) = arcUpPt D (D.ρ D.j / 8) ηs w) ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τL (Set.Ioo (-3) 3) ∧
      (∀ w ∈ Set.Ioo (-3) 3, deriv τL w ≠ 0) ∧
      (∀ w ∈ Set.Ioo (-3) 3, L'.γ i (τL w) = arcDnPt D (D.ρ D.j / 8) ηs w) ∧
      ((StrictAntiOn τL (Set.Ioo (-3) 3) ∧
          τL m < τL (-m) ∧ τL (-m) < τU m ∧ τU m < τU (-m) ∧ τU (-m) < τL m + 1) ∨
        (StrictMonoOn τL (Set.Ioo (-3) 3) ∧
          τU m < τU (-m) ∧ τU (-m) < τL (-m) ∧ τL (-m) < τL m ∧ τL m < τU m + 1)) := by
  classical
  have hlam8 : 0 < D.ρ D.j / 8 := div_pos (D.hρ D.j) (by norm_num)
  subst ha
  -- ## the two raw lifts
  obtain ⟨τU₀, hτU₀sm, hτU₀val, hτU₀d, hτU₀m⟩ :=
    Work.Drive.N2C.exists_arcReparam_up D hηs hηs1 hlam8 rfl hZrel hZsm L i hU
  obtain ⟨τL₀, hτL₀sm, hτL₀val, hτL₀d, hτL₀m⟩ :=
    Work.Drive.N2C.exists_arcReparam_dn D hηs hηs1 hlam8 rfl hZrel hZsm L i hDn
  -- ## orient so that `τU` is antitone
  have hkey : ∃ (L' : Work.Drive.N2C.LevelCurves f (f p - (D.ρ D.j / 8) ^ 2 * ηs) n)
      (τU τL : ℝ → ℝ),
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τU (Set.Ioo (-3) 3) ∧
      (∀ w ∈ Set.Ioo (-3) 3, deriv τU w ≠ 0) ∧
      StrictAntiOn τU (Set.Ioo (-3) 3) ∧
      (∀ w ∈ Set.Ioo (-3) 3, L'.γ i (τU w) = arcUpPt D (D.ρ D.j / 8) ηs w) ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τL (Set.Ioo (-3) 3) ∧
      (∀ w ∈ Set.Ioo (-3) 3, deriv τL w ≠ 0) ∧
      (∀ w ∈ Set.Ioo (-3) 3, L'.γ i (τL w) = arcDnPt D (D.ρ D.j / 8) ηs w) ∧
      (StrictMonoOn τL (Set.Ioo (-3) 3) ∨ StrictAntiOn τL (Set.Ioo (-3) 3)) := by
    rcases hτU₀m with hmono | hanti
    · obtain ⟨L', hL'⟩ := Work.Drive.N2C.levelCurves_reverse L
      refine ⟨L', fun w => -τU₀ w, fun w => -τL₀ w, hτU₀sm.neg, ?_, ?_, ?_,
        hτL₀sm.neg, ?_, ?_, ?_⟩
      · intro w hw
        rw [show (fun w : ℝ => -τU₀ w) = -τU₀ from funext fun w => rfl, deriv.neg]
        exact neg_ne_zero.mpr (hτU₀d w hw)
      · intro x hx y hy hxy
        exact neg_lt_neg_iff.mpr (hmono hx hy hxy)
      · intro w hw
        simp only []
        rw [hL' i (-τU₀ w)]
        simpa using hτU₀val w hw
      · intro w hw
        rw [show (fun w : ℝ => -τL₀ w) = -τL₀ from funext fun w => rfl, deriv.neg]
        exact neg_ne_zero.mpr (hτL₀d w hw)
      · intro w hw
        simp only []
        rw [hL' i (-τL₀ w)]
        simpa using hτL₀val w hw
      · rcases hτL₀m with h | h
        · exact Or.inr (fun x hx y hy hxy => neg_lt_neg_iff.mpr (h hx hy hxy))
        · exact Or.inl (fun x hx y hy hxy => neg_lt_neg_iff.mpr (h hx hy hxy))
    · exact ⟨L, τU₀, τL₀, hτU₀sm, hτU₀d, hanti, hτU₀val, hτL₀sm, hτL₀d, hτL₀val, hτL₀m⟩
  obtain ⟨L', τU, τL, hτUsm, hτUd, hτUanti, hτUval, hτLsm, hτLd, hτLval, hτLmm⟩ := hkey
  -- ## the interval `[-m, m]` sits inside `(-3, 3)`; the restrictions of the rows
  have hmIoo : Set.Icc (-m) m ⊆ Set.Ioo (-3 : ℝ) 3 := by
    intro x hx
    exact ⟨by linarith [hx.1, hm3], by linarith [hx.2, hm3]⟩
  have hτUcont : ContinuousOn τU (Set.Icc (-m) m) := hτUsm.continuousOn.mono hmIoo
  have hτUantiIcc : StrictAntiOn τU (Set.Icc (-m) m) := hτUanti.mono hmIoo
  have hτUvalIcc : ∀ w ∈ Set.Icc (-m) m, L'.γ i (τU w) = arcUpPt D (D.ρ D.j / 8) ηs w :=
    fun w hw => hτUval w (hmIoo hw)
  have hτLcont : ContinuousOn τL (Set.Icc (-m) m) := hτLsm.continuousOn.mono hmIoo
  have hτLvalIcc : ∀ w ∈ Set.Icc (-m) m, L'.γ i (τL w) = arcDnPt D (D.ρ D.j / 8) ηs w :=
    fun w hw => hτLval w (hmIoo hw)
  have h0mem : (0 : ℝ) ∈ Set.Icc (-m) m := ⟨by linarith, hm.le⟩
  -- ## the two arcs are disjoint over the window
  have hdisj : ∀ w ∈ Set.Icc (-m) m, ∀ w' ∈ Set.Icc (-m) m,
      arcUpPt D (D.ρ D.j / 8) ηs w ≠ arcDnPt D (D.ρ D.j / 8) ηs w' := by
    intro w hw w' hw'
    have h3 : |w| ≤ 3 := by
      rw [abs_le]; exact ⟨by linarith [hw.1, hm3], by linarith [hw.2, hm3]⟩
    have h3' : |w'| ≤ 3 := by
      rw [abs_le]; exact ⟨by linarith [hw'.1, hm3], by linarith [hw'.2, hm3]⟩
    exact arcUpPt_ne_arcDnPt D hηs hZrel (Work.Drive.N2C.norm_arcZ_lt_eight hηs1 h3)
      (Work.Drive.N2C.norm_arcZ_lt_eight hηs1 h3')
  -- ## the span of the upper lift
  have hspanU : τU (-m) - τU m < 1 := by
    refine span_lt_one_of_exists_notMem_anti (γ := L'.γ i)
      (α := fun w => arcUpPt D (D.ρ D.j / 8) ηs w) (τ := τU) (u := m)
      (L'.per i) hτUvalIcc hτUcont hτUantiIcc hm ?_
    refine ⟨arcDnPt D (D.ρ D.j / 8) ηs 0,
      ⟨τL 0, hτLval 0 (by norm_num)⟩, ?_⟩
    rintro ⟨w, hw, hwx⟩
    exact hdisj w hw 0 h0mem hwx
  rcases hτLmm with hτLmono | hτLanti
  · -- ## Möbius pattern: the lower lift is monotone
    have hspanL : τL m - τL (-m) < 1 := by
      refine Work.Drive.N2.span_lt_one_of_exists_notMem (γ := L'.γ i)
        (α := fun w => arcDnPt D (D.ρ D.j / 8) ηs w) (τ := τL) (u := m)
        (L'.per i) hτLvalIcc hτLcont (hτLmono.mono hmIoo) hm ?_
      refine ⟨arcUpPt D (D.ρ D.j / 8) ηs 0,
        ⟨τU 0, hτUval 0 (by norm_num)⟩, ?_⟩
      rintro ⟨w, hw, hwx⟩
      exact hdisj 0 h0mem w hw hwx.symm
    obtain ⟨kU, kL, ho1, ho2, ho3, ho4⟩ :=
      exists_hord_shifts_mixed (D := D) (lam0 := D.ρ D.j / 8) (η := ηs) (m := m) hm
        (L := L') (i := i) hτUcont hτUantiIcc hspanU hτUvalIcc hτLcont
        (hτLmono.mono hmIoo) hspanL hτLvalIcc hdisj
    refine ⟨L', fun w => τU w + (kU : ℝ), fun w => τL w + (kL : ℝ), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      Or.inr ⟨?_, ho1, ho2, ho3, ho4⟩⟩
    · exact hτUsm.add contDiffOn_const
    · intro w hw
      rw [deriv_add_const]
      exact hτUd w hw
    · intro x hx y hy hxy
      exact add_lt_add_left (hτUanti hx hy hxy) (kU : ℝ)
    · intro w hw
      simp only []
      rw [Work.Drive.N2C.eq_of_add_intCast_of_periodic (L'.per i) (τU w) kU,
        hτUval w hw]
    · exact hτLsm.add contDiffOn_const
    · intro w hw
      rw [deriv_add_const]
      exact hτLd w hw
    · intro w hw
      simp only []
      rw [Work.Drive.N2C.eq_of_add_intCast_of_periodic (L'.per i) (τL w) kL,
        hτLval w hw]
    · intro x hx y hy hxy
      exact add_lt_add_left (hτLmono hx hy hxy) (kL : ℝ)
  · -- ## split pattern: the lower lift is antitone too
    have hspanL : τL (-m) - τL m < 1 := by
      refine span_lt_one_of_exists_notMem_anti (γ := L'.γ i)
        (α := fun w => arcDnPt D (D.ρ D.j / 8) ηs w) (τ := τL) (u := m)
        (L'.per i) hτLvalIcc hτLcont (hτLanti.mono hmIoo) hm ?_
      refine ⟨arcUpPt D (D.ρ D.j / 8) ηs 0,
        ⟨τU 0, hτUval 0 (by norm_num)⟩, ?_⟩
      rintro ⟨w, hw, hwx⟩
      exact hdisj 0 h0mem w hw hwx.symm
    obtain ⟨kU, kL, ho1, ho2, ho3, ho4⟩ :=
      exists_hord_shifts_anti (D := D) (lam0 := D.ρ D.j / 8) (η := ηs) (m := m) hm
        (L := L') (i := i) hτUcont hτUantiIcc hspanU hτUvalIcc hτLcont
        (hτLanti.mono hmIoo) hspanL hτLvalIcc hdisj
    refine ⟨L', fun w => τU w + (kU : ℝ), fun w => τL w + (kL : ℝ), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      Or.inl ⟨?_, ho1, ho2, ho3, ho4⟩⟩
    · exact hτUsm.add contDiffOn_const
    · intro w hw
      rw [deriv_add_const]
      exact hτUd w hw
    · intro x hx y hy hxy
      exact add_lt_add_left (hτUanti hx hy hxy) (kU : ℝ)
    · intro w hw
      simp only []
      rw [Work.Drive.N2C.eq_of_add_intCast_of_periodic (L'.per i) (τU w) kU,
        hτUval w hw]
    · exact hτLsm.add contDiffOn_const
    · intro w hw
      rw [deriv_add_const]
      exact hτLd w hw
    · intro w hw
      simp only []
      rw [Work.Drive.N2C.eq_of_add_intCast_of_periodic (L'.per i) (τL w) kL,
        hτLval w hw]
    · intro x hx y hy hxy
      exact add_lt_add_left (hτLanti hx hy hxy) (kL : ℝ)

end Main

theorem saddleWindowLiftData {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} (hf : Work.Drive.Morse.IsMorseDistinct f) {p : M}
    (D : Work.Drive.N2.WindowDatum f p)
    (hs1 : D.s₁ D.j = 1) (hs2 : D.s₂ D.j = -1)
    (hjunk : ∀ y : M, y ∉ (D.φ D.j).source → D.φ D.j y = 0)
    (hmorse : Work.Drive.Morse.MorseLemma2) :
    ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ η : ℝ, 0 < η → η ≤ η₁ →
      Work.Drive.N2Lead.OnOneComponent (f := f) (f p - 3 * η / 2)
          (Work.Drive.N2Lead.saddlePin D (f p - 3 * η / 2) (99 / 50)) →
      ∃ (n : ℕ) (L : Work.Drive.N2C.LevelCurves f (f p - 3 * η / 2) n) (i : Fin n)
        (τU τL : ℝ → ℝ),
        ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τU (Set.Ioo (-3) 3) ∧
        (∀ w ∈ Set.Ioo (-3) 3, deriv τU w ≠ 0) ∧
        StrictAntiOn τU (Set.Ioo (-3) 3) ∧
        (∀ w ∈ Set.Ioo (-3) 3,
          L.γ i (τU w)
            = Work.Drive.N2Lead.arcUpPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w) ∧
        ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τL (Set.Ioo (-3) 3) ∧
        (∀ w ∈ Set.Ioo (-3) 3, deriv τL w ≠ 0) ∧
        (∀ w ∈ Set.Ioo (-3) 3,
          L.γ i (τL w)
            = Work.Drive.N2Lead.arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w) ∧
        ((StrictAntiOn τL (Set.Ioo (-3) 3) ∧
            τL (99 / 50) < τL (-(99 / 50)) ∧ τL (-(99 / 50)) < τU (99 / 50) ∧
            τU (99 / 50) < τU (-(99 / 50)) ∧ τU (-(99 / 50)) < τL (99 / 50) + 1) ∨
          (StrictMonoOn τL (Set.Ioo (-3) 3) ∧
            τU (99 / 50) < τU (-(99 / 50)) ∧ τU (-(99 / 50)) < τL (-(99 / 50)) ∧
            τL (-(99 / 50)) < τL (99 / 50) ∧ τL (99 / 50) < τU (99 / 50) + 1)) := by
  classical
  have hlampos : 0 < (D.ρ D.j / 8) ^ 2 := by
    have := D.hρ D.j; positivity
  refine ⟨min ((D.ρ D.j / 8) ^ 2 / 2) D.ηd, lt_min (by positivity) D.hηd, ?_⟩
  intro η hη hηle hone
  have hle1 : η ≤ (D.ρ D.j / 8) ^ 2 / 2 := le_trans hηle (min_le_left _ _)
  have hle2 : η ≤ D.ηd := le_trans hηle (min_le_right _ _)
  have hηs_pos : 0 < Work.Drive.N2.packetEta D η := Work.Drive.N2.packetEta_pos D hη
  have hηs_le_one : Work.Drive.N2.packetEta D η ≤ 1 := by
    rw [Work.Drive.N2.packetEta,
      div_le_one (by positivity : (0 : ℝ) < 2 * (D.ρ D.j / 8) ^ 2)]
    nlinarith [hle1, hlampos]
  have hηs1 : |Work.Drive.N2.packetEta D η| ≤ 1 := by
    rw [abs_of_pos hηs_pos]; exact hηs_le_one
  have hlam : (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEta D η = 3 * η / 2 :=
    Work.Drive.N2.packetEta_law D η
  have hsmall : (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEta D η < 2 * D.ηd := by
    rw [hlam]; nlinarith [hle2, D.hηd]
  -- ## the chart rows
  have hZrel : ∀ x : M, chartCplx D x
      = ((D.ρ D.j / 8 : ℝ) : ℂ) * Work.Drive.N2.cl_saddleZ D 1 x :=
    fun x => chartCplx_cl_saddleZ D x
  have hZsm : ∀ x ∈ (D.φ D.j).source,
      ContMDiffAt (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Drive.N2.cl_saddleZ D 1) x :=
    fun x hx => (contMDiffOn_cl_saddleZ D).contMDiffAt ((D.φ D.j).open_source.mem_nhds hx)
  have hlev : ∀ y ∈ (D.φ D.j).source,
      f y = f p + (D.ρ D.j / 8) ^ 2 * ((Work.Drive.N2.cl_saddleZ D 1 y) ^ 2).re := by
    intro y hy
    exact Work.Drive.N2.cl_saddleZ_level D hs1 hs2 (by norm_num) (by norm_num) hy
  have harcBall : ∀ w : ℝ, |w| ≤ 3 →
      ‖arcZ (Work.Drive.N2.packetEta D η) w‖ < 8 :=
    fun w hw => Work.Drive.N2C.norm_arcZ_lt_eight hηs1 hw
  have habs : ∀ {w : ℝ}, w ∈ Set.Ioo (-3 : ℝ) 3 → |w| ≤ 3 := by
    intro w hw
    rw [abs_le]
    exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hUplev : ∀ w ∈ Set.Ioo (-3 : ℝ) 3,
      f (arcUpPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w) = f p - 3 * η / 2 := by
    intro w hw
    rw [f_arcUpPt D (harcBall w (habs hw)) hZrel hlev, hlam]
  have hDnlev : ∀ w ∈ Set.Ioo (-3 : ℝ) 3,
      f (arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w) = f p - 3 * η / 2 := by
    intro w hw
    rw [f_arcDnPt D (harcBall w (habs hw)) hZrel hlev, hlam]
  have hball0 : ‖arcZ (Work.Drive.N2.packetEta D η) 0‖ < 8 := harcBall 0 (by norm_num)
  -- ## the two anchor points are in the pin
  have hpinU : arcUpPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) 0
      ∈ saddlePin D (f p - 3 * η / 2) (99 / 50) := by
    rw [saddlePin_eq_scaled D (div_pos (D.hρ D.j) (by norm_num)) rfl hZrel]
    refine ⟨arcUpPt_mem_source D hball0 rfl, ?_, hUplev 0 ⟨by norm_num, by norm_num⟩, ?_⟩
    · rw [Z_arcUpPt D hball0 (div_pos (D.hρ D.j) (by norm_num)) rfl hZrel]; exact hball0
    · rw [Z_arcUpPt D hball0 (div_pos (D.hρ D.j) (by norm_num)) rfl hZrel, arcZ_sq_im]
      norm_num
  have hmemDn : arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) 0
      ∈ (D.φ D.j).source := by
    refine (D.φ D.j).map_target ?_
    refine Work.Drive.N2.windowBall_subset_target D D.j ?_
    rw [show -((((D.ρ D.j / 8 : ℝ)) : ℂ) * arcZ (Work.Drive.N2.packetEta D η) 0)
        = (((D.ρ D.j / 8 : ℝ)) : ℂ) * (-(arcZ (Work.Drive.N2.packetEta D η) 0)) by ring,
      cE2_norm, norm_mul, Complex.norm_of_nonneg (div_pos (D.hρ D.j) (by norm_num)).le,
      norm_neg]
    nlinarith [hball0, D.hρ D.j]
  have hpinD : arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) 0
      ∈ saddlePin D (f p - 3 * η / 2) (99 / 50) := by
    rw [saddlePin_eq_scaled D (div_pos (D.hρ D.j) (by norm_num)) rfl hZrel]
    refine ⟨hmemDn, ?_, hDnlev 0 ⟨by norm_num, by norm_num⟩, ?_⟩
    · rw [Work.Drive.N2C.Z_arcDnPt D hball0 (div_pos (D.hρ D.j) (by norm_num)) rfl hZrel,
        norm_neg]
      exact hball0
    · rw [Work.Drive.N2C.Z_arcDnPt D hball0 (div_pos (D.hρ D.j) (by norm_num)) rfl hZrel,
        neg_sq, arcZ_sq_im]
      norm_num
  -- ## the two anchor points lie on one component
  have hcc : connectedComponentIn {z : M | f z = f p - 3 * η / 2}
        (arcUpPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) 0)
      = connectedComponentIn {z : M | f z = f p - 3 * η / 2}
        (arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) 0) :=
    connectedComponentIn_eq (hone _ hpinU _ hpinD)
  -- ## the level curves of the anchor level
  have hreg : ∀ x : M, f x = f p - 3 * η / 2 → ¬ Work.Drive.Morse.IsCritical f x := by
    intro x hx
    refine Work.Drive.N2.level_noCrit D hηs_pos hsmall x ?_
    rwa [hlam]
  have hne : ∃ x : M, f x = f p - 3 * η / 2 :=
    ⟨arcUpPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) 0,
      hUplev 0 ⟨by norm_num, by norm_num⟩⟩
  obtain ⟨n, γ, hγsm, hγper, hγinj, hγval, hγimm, hγker, hγcov, hγdisj, hγcl, hγmod⟩ :=
    Work.Drive.N2.exists_levelComponentCurves f hf.1 (f p - 3 * η / 2) hreg hne
  have hγcov' : ∀ x : M, f x = f p - 3 * η / 2 → ∃ (i : Fin n) (t : ℝ), x = γ i t := by
    intro x hx
    have hxU : x ∈ ⋃ i, Set.range (γ i) := by rw [hγcov]; exact hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxU
    obtain ⟨t, ht⟩ := hi
    exact ⟨i, t, ht.symm⟩
  obtain ⟨L⟩ := Work.Drive.N2C.levelCurves_ofComponentCurves hγsm hγper hγinj hγval hγker
    hγcov' hγdisj
  -- ## the marked component
  obtain ⟨i, t0, ht0⟩ := L.cover (arcUpPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) 0)
    (hUplev 0 ⟨by norm_num, by norm_num⟩)
  have hUpc : ContinuousOn (fun w : ℝ =>
      arcUpPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w) (Set.Ioo (-3 : ℝ) 3) :=
    (Work.Drive.N2C.contMDiffOn_arcUpPt D hηs_pos hηs1 (div_pos (D.hρ D.j) (by norm_num))
      rfl).continuousOn
  have hDnc : ContinuousOn (fun w : ℝ =>
      arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w) (Set.Ioo (-3 : ℝ) 3) :=
    (Work.Drive.N2C.contMDiffOn_arcDnPt D hηs_pos hηs1 (div_pos (D.hρ D.j) (by norm_num))
      rfl).continuousOn
  -- ## the range rows of the two arcs
  have hU : ∀ w ∈ Set.Ioo (-3 : ℝ) 3,
      arcUpPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w ∈ Set.range (L.γ i) := by
    intro w hw
    rw [range_eq_connectedComponentIn L i t0, ← ht0]
    exact (isPreconnected_Ioo.image _ hUpc).subset_connectedComponentIn ⟨0, by norm_num, rfl⟩
      (fun z ⟨u, hu, hzu⟩ => by rw [← hzu]; exact hUplev u hu) ⟨w, hw, rfl⟩
  have hDn : ∀ w ∈ Set.Ioo (-3 : ℝ) 3,
      arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w ∈ Set.range (L.γ i) := by
    intro w hw
    have hmem : arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w
        ∈ connectedComponentIn {z : M | f z = f p - 3 * η / 2}
          (arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) 0) :=
      (isPreconnected_Ioo.image _ hDnc).subset_connectedComponentIn ⟨0, by norm_num, rfl⟩
        (fun z ⟨u, hu, hzu⟩ => by rw [← hzu]; exact hDnlev u hu) ⟨w, hw, rfl⟩
    rw [range_eq_connectedComponentIn L i t0, ← ht0]
    rw [← hcc] at hmem
    exact hmem
  -- ## assemble
  obtain ⟨L', τU, τL, hrows⟩ := liftData_of_levelCurves (a := f p - 3 * η / 2) (m := 99 / 50) D
    (by rw [hlam]) hηs_pos hηs1 (by norm_num) (by norm_num) hZrel hZsm hU hDn
  exact ⟨n, L', i, τU, τL, hrows⟩

end Work.Drive.N2Lead

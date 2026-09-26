import Mathlib
import Submission.Work.SphereJordan.tgtSpansTiling
import Submission.Work.SphereJordan.windIdentitiesProof
import Submission.Work.SphereJordan.span_pairing
import Submission.Work.SphereJordan.tgtUpPC_isSimple
import Submission.Work.SphereJordan.prelim
import Submission.Work.SphereJordan.dnPCIsSimple

/-!
# The two spanning discs of the cut annulus (cycle-free variant)

This module assembles the `Work.SphereJordan.annulusTargetSpansCore` statement from the cycle-free
part of the two-cuts library.  The point is that `Work.SphereJordan.aipSetup` and
`Work.SphereJordan.tilingSchoenflies` cannot be imported together with
`Submission.Work.SphereJordan.annulusTargetSpans`, because
`Submission.Work.Smooth.SphereJordan.annulusSchoenfliesCore` (imported by `aipSetup`) imports
`annulusTargetSpans` itself.  The non-`_S` family (`tilingOfPairing`, `prelim`,
`windIdentitiesProof`, `span_pairing`) is cycle-free, so it *can* be used underneath
`annulusTargetSpans`.

Contents, all proved here (the `_S`-free analogues of the lemmas of `aipSetup.lean`):

* `tgtSpans_upSch`, `tgtSpans_dnSch` — Schoenflies data of `H.upPC b` and `H.dnPC b` from `h`;
* `tgtSpans_sideUp`, `tgtSpans_sideDn` — `S.V` lies on one side of each curve;
* `tgtSpans_pairingExists` — the flag `b` for which `S.V` is on the *unbounded* side of both;
* `tgtSpans_spansOfPairing` — the tiling plus the containment of the two bounded sides in the
  annulus, giving the cover and the meet of the two spanning discs;
* `tgtSpansCore` — the bundled statement.
-/

open Set

namespace Work.SphereJordan

noncomputable section

variable {γ : Work.Smooth.Jordan.PlaneCurve}

variable {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
  {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}

/-- Schoenflies data of the upper four-arc curve `H.upPC b`, from the Jordan–Schoenflies
hypothesis `h`. -/
noncomputable def tgtSpans_upSch (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (H : SpanHyp h hs hball S) (b : Bool) :
    Work.Smooth.Jordan.PlaneSchoenflies (H.upPC b) :=
  (h (H.upPC b) (tgtUpPC_isSimple h hs hball S H b)).some

/-- Schoenflies data of the lower four-arc curve `H.dnPC b`, from the Jordan–Schoenflies
hypothesis `h`. -/
noncomputable def tgtSpans_dnSch (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (H : SpanHyp h hs hball S) (b : Bool) :
    Work.Smooth.Jordan.PlaneSchoenflies (H.dnPC b) :=
  (h (H.dnPC b) (dnPCIsSimple h hs hball S H b)).some

/-- The bounded side of `γ` lies on one side of the upper four-arc curve. -/
theorem tgtSpans_sideUp (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (H : SpanHyp h hs hball S) (b : Bool)
    (T : Work.Smooth.Jordan.PlaneSchoenflies (H.upPC b)) :
    S.V ⊆ T.U ∨ S.V ⊆ T.V := by
  refine Work.Smooth.Jordan.plane_separation_preconnected_subset T.toPlaneSeparation
    S.preconn_V ?_
  intro z hz htr
  rcases htr with ⟨τ, hτ⟩
  rw [← hτ] at hz
  exact upPC_notMem_V h hs hball S H b τ hz

/-- The bounded side of `γ` lies on one side of the lower four-arc curve. -/
theorem tgtSpans_sideDn (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (H : SpanHyp h hs hball S) (b : Bool)
    (T : Work.Smooth.Jordan.PlaneSchoenflies (H.dnPC b)) :
    S.V ⊆ T.U ∨ S.V ⊆ T.V := by
  refine Work.Smooth.Jordan.plane_separation_preconnected_subset T.toPlaneSeparation
    S.preconn_V ?_
  intro z hz htr
  rcases htr with ⟨τ, hτ⟩
  rw [← hτ] at hz
  exact dnPC_notMem_V h hs hball S H b τ hz

/-- **The pairing exists**: there is a flag `b` for which the bounded side of `γ` lies on the
unbounded side of both four-arc curves of the pairing `b`. -/
theorem tgtSpans_pairingExists (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (H : SpanHyp h hs hball S) :
    ∃ b : Bool, S.V ⊆ (tgtSpans_upSch h hs hball S H b).U ∧
      S.V ⊆ (tgtSpans_dnSch h hs hball S H b).U := by
  have hUp : ∀ b : Bool,
      S.V ⊆ (tgtSpans_upSch h hs hball S H b).U ∨
        S.V ⊆ (tgtSpans_upSch h hs hball S H b).V :=
    fun b => tgtSpans_sideUp h hs hball S H b _
  have hDn : ∀ b : Bool,
      S.V ⊆ (tgtSpans_dnSch h hs hball S H b).U ∨
        S.V ⊆ (tgtSpans_dnSch h hs hball S H b).V :=
    fun b => tgtSpans_sideDn h hs hball S H b _
  have hpair := span_pairing_of_identities h hs hball S H (windIdentitiesProof h hs hball S H)
    (tgtSpans_upSch h hs hball S H true) (tgtSpans_upSch h hs hball S H false)
    (tgtSpans_dnSch h hs hball S H true) (tgtSpans_dnSch h hs hball S H false)
  by_cases hc : S.V ⊆ (tgtSpans_upSch h hs hball S H true).V
  · refine ⟨false, ?_, ?_⟩
    · rcases hUp false with hh | hh
      · exact hh
      · exact absurd (hpair.2.1.mp hc) (not_not.mpr hh)
    · rcases hDn false with hh | hh
      · exact hh
      · exact absurd (hpair.2.2.mp (hpair.1.mp hc)) (not_not.mpr hh)
  · refine ⟨true, ?_, ?_⟩
    · rcases hUp true with hh | hh
      · exact hh
      · exact absurd hh hc
    · rcases hDn true with hh | hh
      · exact hh
      · exact absurd (hpair.1.mpr hh) hc

/-- **The two spanning discs of a pairing.**  Given the flag `b` for which the bounded side of `γ`
lies on the unbounded side of both four-arc curves, the two Schoenflies discs have images that
cover `annulus S` and meet exactly in the two crosscuts. -/
theorem tgtSpans_spansOfPairing {γ : Work.Smooth.Jordan.PlaneCurve}
    {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) (b : Bool)
    (TU : Work.Smooth.Jordan.PlaneSchoenflies (H.upPC b))
    (TD : Work.Smooth.Jordan.PlaneSchoenflies (H.dnPC b))
    (hb : S.V ⊆ TU.U ∧ S.V ⊆ TD.U) :
    Function.Injective TU.e ∧ Function.Injective TD.e ∧
      (∀ τ : ℝ, TU.e (Work.Smooth.SphereJordan.circlePoint τ) =
        Work.Smooth.SphereJordan.tgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ τ) ∧
      (∀ τ : ℝ, TD.e (Work.Smooth.SphereJordan.circlePoint τ) =
        Work.Smooth.SphereJordan.tgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ τ) ∧
      Set.range TU.e ⊆ Work.Smooth.SphereJordan.annulus S ∧
      Set.range TD.e ⊆ Work.Smooth.SphereJordan.annulus S ∧
      Set.range TU.e ∪ Set.range TD.e = Work.Smooth.SphereJordan.annulus S ∧
      Set.range TU.e ∩ Set.range TD.e =
        (Work.Smooth.SphereJordan.cut₁ S H.t₁ H.s₁ ∪
          Work.Smooth.SphereJordan.cut₂ S H.t₂ H.s₂) := by
  have htile := tgtT_tilingOfPairing h hs hball S H b TU TD hb
  have hVU := tgtT_upPC_V_subset_annulus' H b TU hb.1
  have hVD := tgtT_dnPC_V_subset_annulus' H b TD hb.2
  refine ⟨TU.inj, TD.inj, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro τ
    rw [TU.boundary]
    rfl
  · intro τ
    rw [TD.boundary]
    rfl
  · rw [TU.range_e]
    exact closure_minimal hVU (tgtT_isClosed_annulus S)
  · rw [TD.range_e]
    exact closure_minimal hVD (tgtT_isClosed_annulus S)
  · rw [TU.range_e, TD.range_e]
    exact htile.1
  · rw [TU.range_e, TD.range_e]
    exact htile.2

/-- **Two cuts cut the annulus into two discs.**  For the two-cuts configuration, there is a flag
`b` and two continuous injections of the model disc, with boundary parametrisations `tgtUpB` and
`tgtDnB`, whose images cover the annulus `annulus S = 𝔻 ∖ S.V` and meet exactly in the two
crosscuts. -/
theorem tgtSpansCore (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    {γ : Work.Smooth.Jordan.PlaneCurve} (hs : γ.IsSimple) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ t₂ s₂ θ₁ θ₂ : ℝ)
    (ht₁ : 0 < t₁) (ht₁s₁ : t₁ < s₁) (ht₂ : 0 < t₂) (ht₂s₂ : t₂ < s₂)
    (ha₁ : (Work.Smooth.SphereJordan.base S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.cutDir S ∈ γ.trace)
    (hseg₁ : ∀ σ : ℝ, t₁ < σ → σ < s₁ →
      (Work.Smooth.SphereJordan.base S : ℂ) + (σ : ℂ) * Work.Smooth.SphereJordan.cutDir S ∈
        Metric.ball (0 : ℂ) 1 \ S.V)
    (hout₁ : (Work.Smooth.SphereJordan.base S : ℂ) +
      (s₁ : ℂ) * Work.Smooth.SphereJordan.cutDir S = Work.Smooth.SphereJordan.cutDir S)
    (ha₂ : (Work.Smooth.SphereJordan.base S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.cutDir S ∈ γ.trace)
    (hseg₂ : ∀ σ : ℝ, t₂ < σ → σ < s₂ →
      (Work.Smooth.SphereJordan.base S : ℂ) - (σ : ℂ) * Work.Smooth.SphereJordan.cutDir S ∈
        Metric.ball (0 : ℂ) 1 \ S.V)
    (hout₂ : (Work.Smooth.SphereJordan.base S : ℂ) -
      (s₂ : ℂ) * Work.Smooth.SphereJordan.cutDir S = -Work.Smooth.SphereJordan.cutDir S)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.base S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.cutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.base S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.cutDir S)
    (hθ : θ₂ < θ₁) (hθ' : θ₁ < θ₂ + 2 * Real.pi)
    (hmax₁ : ∀ σ : ℝ, t₁ < σ →
      (Work.Smooth.SphereJordan.base S : ℂ) + (σ : ℂ) * Work.Smooth.SphereJordan.cutDir S ∉
        closure S.V)
    (hmax₂ : ∀ σ : ℝ, t₂ < σ →
      (Work.Smooth.SphereJordan.base S : ℂ) - (σ : ℂ) * Work.Smooth.SphereJordan.cutDir S ∉
        closure S.V) :
    ∃ (b : Bool) (Φ_up Φ_dn : C(Work.Smooth.SphereJordan.Disc, ℂ)),
      Function.Injective Φ_up ∧ Function.Injective Φ_dn ∧
      (∀ τ : ℝ, Φ_up (Work.Smooth.SphereJordan.circlePoint τ) =
        Work.Smooth.SphereJordan.tgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ τ) ∧
      (∀ τ : ℝ, Φ_dn (Work.Smooth.SphereJordan.circlePoint τ) =
        Work.Smooth.SphereJordan.tgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ τ) ∧
      Set.range Φ_up ⊆ Work.Smooth.SphereJordan.annulus S ∧
      Set.range Φ_dn ⊆ Work.Smooth.SphereJordan.annulus S ∧
      Set.range Φ_up ∪ Set.range Φ_dn = Work.Smooth.SphereJordan.annulus S ∧
      Set.range Φ_up ∩ Set.range Φ_dn =
        Work.Smooth.SphereJordan.cut₁ S t₁ s₁ ∪ Work.Smooth.SphereJordan.cut₂ S t₂ s₂ := by
  let H : SpanHyp h hs hball S :=
    { t₁ := t₁, s₁ := s₁, t₂ := t₂, s₂ := s₂, θ₁ := θ₁, θ₂ := θ₂,
      ht₁ := ht₁, ht₁s₁ := ht₁s₁, ht₂ := ht₂, ht₂s₂ := ht₂s₂,
      ha₁ := ha₁, hseg₁ := hseg₁, hout₁ := hout₁, ha₂ := ha₂, hseg₂ := hseg₂, hout₂ := hout₂,
      hθ₁ := hθ₁, hθ₂ := hθ₂, hθ := hθ, hθ' := hθ', hmax₁ := hmax₁, hmax₂ := hmax₂ }
  obtain ⟨b, hbU, hbD⟩ := tgtSpans_pairingExists h hs hball S H
  exact ⟨b, (tgtSpans_upSch h hs hball S H b).e, (tgtSpans_dnSch h hs hball S H b).e,
    tgtSpans_spansOfPairing H b _ _ ⟨hbU, hbD⟩⟩

end

end Work.SphereJordan

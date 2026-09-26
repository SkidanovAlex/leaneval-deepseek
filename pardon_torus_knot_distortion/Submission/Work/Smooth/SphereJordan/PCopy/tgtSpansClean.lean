import Mathlib
import Submission.Work.Smooth.SphereJordan.PCopy.tgtSpansTiling
import Submission.Work.Smooth.SphereJordan.PCopy.windIdentitiesProof
import Submission.Work.Smooth.SphereJordan.PCopy.span_pairing
import Submission.Work.Smooth.SphereJordan.PCopy.tgtUpPC_isSimple
import Submission.Work.Smooth.SphereJordan.PCopy.prelim
import Submission.Work.Smooth.SphereJordan.PCopy.dnPCIsSimple

/-!
# The two spanning discs of the cut pcannulus (cycle-free variant)

This module assembles the `Work.SphereJordan.annulusTargetSpansCore` statement from the cycle-free
part of the two-pccuts library.  The point is that `Work.SphereJordan.aipSetup` and
`Work.SphereJordan.tilingSchoenflies` cannot be imported together with
`Submission.Work.SphereJordan.pcannulusTargetSpans`, because
`Submission.Work.Smooth.SphereJordan.annulusSchoenfliesCore` (imported by `aipSetup`) imports
`pcannulusTargetSpans` itself.  The non-`_S` family (`tilingOfPairing`, `prelim`,
`pcwindIdentitiesProof`, `pcspan_pairing`) is cycle-free, so it *can* be used underneath
`pcannulusTargetSpans`.

Contents, all proved here (the `_S`-free analogues of the lemmas of `aipSetup.lean`):

* `pctgtSpans_upSch`, `pctgtSpans_dnSch` — Schoenflies data of `H.pcupPC b` and `H.pcdnPC b` from `h`;
* `pctgtSpans_sideUp`, `pctgtSpans_sideDn` — `S.V` lies on one side of each curve;
* `pctgtSpans_pairingExists` — the flag `b` for which `S.V` is on the *unbounded* side of both;
* `pctgtSpans_spansOfPairing` — the tiling plus the containment of the two bounded sides in the
  pcannulus, giving the cover and the meet of the two spanning discs;
* `pctgtSpansCore` — the bundled statement.
-/

open Set

namespace Work.SphereJordan

noncomputable section

variable {γ : Work.Smooth.Jordan.PlaneCurve}

variable {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
  {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}

/-- Schoenflies data of the upper four-arc curve `H.pcupPC b`, from the Jordan–Schoenflies
hypothesis `h`. -/
noncomputable def pctgtSpans_upSch (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (H : pcSpanHyp h hs hball S) (b : Bool) :
    Work.Smooth.Jordan.PlaneSchoenflies (H.pcupPC b) :=
  (h (H.pcupPC b) (pctgtUpPC_isSimple h hs hball S H b)).some

/-- Schoenflies data of the lower four-arc curve `H.pcdnPC b`, from the Jordan–Schoenflies
hypothesis `h`. -/
noncomputable def pctgtSpans_dnSch (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (H : pcSpanHyp h hs hball S) (b : Bool) :
    Work.Smooth.Jordan.PlaneSchoenflies (H.pcdnPC b) :=
  (h (H.pcdnPC b) (pcdnPCIsSimple h hs hball S H b)).some

/-- The bounded side of `γ` lies on one side of the upper four-arc curve. -/
theorem pctgtSpans_sideUp (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (H : pcSpanHyp h hs hball S) (b : Bool)
    (T : Work.Smooth.Jordan.PlaneSchoenflies (H.pcupPC b)) :
    S.V ⊆ T.U ∨ S.V ⊆ T.V := by
  refine Work.Smooth.Jordan.plane_separation_preconnected_subset T.toPlaneSeparation
    S.preconn_V ?_
  intro z hz htr
  rcases htr with ⟨τ, hτ⟩
  rw [← hτ] at hz
  exact pcupPC_notMem_V h hs hball S H b τ hz

/-- The bounded side of `γ` lies on one side of the lower four-arc curve. -/
theorem pctgtSpans_sideDn (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (H : pcSpanHyp h hs hball S) (b : Bool)
    (T : Work.Smooth.Jordan.PlaneSchoenflies (H.pcdnPC b)) :
    S.V ⊆ T.U ∨ S.V ⊆ T.V := by
  refine Work.Smooth.Jordan.plane_separation_preconnected_subset T.toPlaneSeparation
    S.preconn_V ?_
  intro z hz htr
  rcases htr with ⟨τ, hτ⟩
  rw [← hτ] at hz
  exact pcdnPC_notMem_V h hs hball S H b τ hz

/-- **The pairing exists**: there is a flag `b` for which the bounded side of `γ` lies on the
unbounded side of both four-arc curves of the pairing `b`. -/
theorem pctgtSpans_pairingExists (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (H : pcSpanHyp h hs hball S) :
    ∃ b : Bool, S.V ⊆ (pctgtSpans_upSch h hs hball S H b).U ∧
      S.V ⊆ (pctgtSpans_dnSch h hs hball S H b).U := by
  have hUp : ∀ b : Bool,
      S.V ⊆ (pctgtSpans_upSch h hs hball S H b).U ∨
        S.V ⊆ (pctgtSpans_upSch h hs hball S H b).V :=
    fun b => pctgtSpans_sideUp h hs hball S H b _
  have hDn : ∀ b : Bool,
      S.V ⊆ (pctgtSpans_dnSch h hs hball S H b).U ∨
        S.V ⊆ (pctgtSpans_dnSch h hs hball S H b).V :=
    fun b => pctgtSpans_sideDn h hs hball S H b _
  have hpair := pcspan_pairing_of_identities h hs hball S H (pcwindIdentitiesProof h hs hball S H)
    (pctgtSpans_upSch h hs hball S H true) (pctgtSpans_upSch h hs hball S H false)
    (pctgtSpans_dnSch h hs hball S H true) (pctgtSpans_dnSch h hs hball S H false)
  by_cases hc : S.V ⊆ (pctgtSpans_upSch h hs hball S H true).V
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
cover `pcannulus S` and meet exactly in the two crosscuts. -/
theorem pctgtSpans_spansOfPairing {γ : Work.Smooth.Jordan.PlaneCurve}
    {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) (b : Bool)
    (TU : Work.Smooth.Jordan.PlaneSchoenflies (H.pcupPC b))
    (TD : Work.Smooth.Jordan.PlaneSchoenflies (H.pcdnPC b))
    (hb : S.V ⊆ TU.U ∧ S.V ⊆ TD.U) :
    Function.Injective TU.e ∧ Function.Injective TD.e ∧
      (∀ τ : ℝ, TU.e (Work.Smooth.SphereJordan.circlePoint τ) =
        Work.Smooth.SphereJordan.pctgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ τ) ∧
      (∀ τ : ℝ, TD.e (Work.Smooth.SphereJordan.circlePoint τ) =
        Work.Smooth.SphereJordan.pctgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ τ) ∧
      Set.range TU.e ⊆ Work.Smooth.SphereJordan.pcannulus S ∧
      Set.range TD.e ⊆ Work.Smooth.SphereJordan.pcannulus S ∧
      Set.range TU.e ∪ Set.range TD.e = Work.Smooth.SphereJordan.pcannulus S ∧
      Set.range TU.e ∩ Set.range TD.e =
        (Work.Smooth.SphereJordan.pccut₁ S H.t₁ H.s₁ ∪
          Work.Smooth.SphereJordan.pccut₂ S H.t₂ H.s₂) := by
  have htile := pctgtT_tilingOfPairing h hs hball S H b TU TD hb
  have hVU := pctgtT_upPC_V_subset_annulus' H b TU hb.1
  have hVD := pctgtT_dnPC_V_subset_annulus' H b TD hb.2
  refine ⟨TU.inj, TD.inj, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro τ
    rw [TU.boundary]
    rfl
  · intro τ
    rw [TD.boundary]
    rfl
  · rw [TU.range_e]
    exact closure_minimal hVU (pctgtT_isClosed_annulus S)
  · rw [TD.range_e]
    exact closure_minimal hVD (pctgtT_isClosed_annulus S)
  · rw [TU.range_e, TD.range_e]
    exact htile.1
  · rw [TU.range_e, TD.range_e]
    exact htile.2

/-- **Two pccuts cut the pcannulus into two discs.**  For the two-pccuts configuration, there is a flag
`b` and two continuous injections of the model disc, with boundary parametrisations `pctgtUpB` and
`pctgtDnB`, whose images cover the pcannulus `pcannulus S = 𝔻 ∖ S.V` and meet exactly in the two
crosscuts. -/
theorem pctgtSpansCore (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    {γ : Work.Smooth.Jordan.PlaneCurve} (hs : γ.IsSimple) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ t₂ s₂ θ₁ θ₂ : ℝ)
    (ht₁ : 0 < t₁) (ht₁s₁ : t₁ < s₁) (ht₂ : 0 < t₂) (ht₂s₂ : t₂ < s₂)
    (ha₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∈ γ.trace)
    (hseg₁ : ∀ σ : ℝ, t₁ < σ → σ < s₁ →
      (Work.Smooth.SphereJordan.pcbase S : ℂ) + (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∈
        Metric.ball (0 : ℂ) 1 \ S.V)
    (hout₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (s₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S = Work.Smooth.SphereJordan.pccutDir S)
    (ha₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∈ γ.trace)
    (hseg₂ : ∀ σ : ℝ, t₂ < σ → σ < s₂ →
      (Work.Smooth.SphereJordan.pcbase S : ℂ) - (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∈
        Metric.ball (0 : ℂ) 1 \ S.V)
    (hout₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (s₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S = -Work.Smooth.SphereJordan.pccutDir S)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ : θ₂ < θ₁) (hθ' : θ₁ < θ₂ + 2 * Real.pi)
    (hmax₁ : ∀ σ : ℝ, t₁ < σ →
      (Work.Smooth.SphereJordan.pcbase S : ℂ) + (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∉
        closure S.V)
    (hmax₂ : ∀ σ : ℝ, t₂ < σ →
      (Work.Smooth.SphereJordan.pcbase S : ℂ) - (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∉
        closure S.V) :
    ∃ (b : Bool) (Φ_up Φ_dn : C(Work.Smooth.SphereJordan.Disc, ℂ)),
      Function.Injective Φ_up ∧ Function.Injective Φ_dn ∧
      (∀ τ : ℝ, Φ_up (Work.Smooth.SphereJordan.circlePoint τ) =
        Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ τ) ∧
      (∀ τ : ℝ, Φ_dn (Work.Smooth.SphereJordan.circlePoint τ) =
        Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ τ) ∧
      Set.range Φ_up ⊆ Work.Smooth.SphereJordan.pcannulus S ∧
      Set.range Φ_dn ⊆ Work.Smooth.SphereJordan.pcannulus S ∧
      Set.range Φ_up ∪ Set.range Φ_dn = Work.Smooth.SphereJordan.pcannulus S ∧
      Set.range Φ_up ∩ Set.range Φ_dn =
        Work.Smooth.SphereJordan.pccut₁ S t₁ s₁ ∪ Work.Smooth.SphereJordan.pccut₂ S t₂ s₂ := by
  let H : pcSpanHyp h hs hball S :=
    { t₁ := t₁, s₁ := s₁, t₂ := t₂, s₂ := s₂, θ₁ := θ₁, θ₂ := θ₂,
      ht₁ := ht₁, ht₁s₁ := ht₁s₁, ht₂ := ht₂, ht₂s₂ := ht₂s₂,
      ha₁ := ha₁, hseg₁ := hseg₁, hout₁ := hout₁, ha₂ := ha₂, hseg₂ := hseg₂, hout₂ := hout₂,
      hθ₁ := hθ₁, hθ₂ := hθ₂, hθ := hθ, hθ' := hθ', hmax₁ := hmax₁, hmax₂ := hmax₂ }
  obtain ⟨b, hbU, hbD⟩ := pctgtSpans_pairingExists h hs hball S H
  exact ⟨b, (pctgtSpans_upSch h hs hball S H b).e, (pctgtSpans_dnSch h hs hball S H b).e,
    pctgtSpans_spansOfPairing H b _ _ ⟨hbU, hbD⟩⟩

end

end Work.SphereJordan

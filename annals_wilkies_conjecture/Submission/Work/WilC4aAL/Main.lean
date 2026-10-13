/-
  Work.WilC4aAL.Main

  The deliverable of area C4a-AL: the hole

      WilkiesDesign.CG.C4a.C4a_arcLift (hP : PuiseuxReal) : ArcLift

  of `Submission/Work/Wilkies/CG/C4a/Spec.lean`, proved as `Work.WilC4aAL.C4a_arcLift_proved`
  from the sub-lemmas of this directory:

  * `puiseux_root_cover`  (AL.1): `PuiseuxReal` gives ONE ramification exponent `N` and analytic
    branches covering the real zeros of every polynomial of the family,
  * `analytic_sign_selection` (AL.3): a sign vector realisable at every small parameter value is
    realised by a single analytic selector built from the cell representatives `cand`,
  * `selector_zero_of_sign_zero` (AL.4): if one of the sign conditions is `0` and the coefficients
    of that family vanish at `0`, the selector also vanishes at `0` (used by `C4a_CS_step` when it
    applies `ArcLift` to the Weierstrass polynomial of the last coordinate).

  `ArcLift` and `C4a_arcLift_proved` have the same type; the `example` at the end checks this.
-/
import Submission.Work.WilC4aAL.Defs
import Submission.Work.WilC4aAL.Basic
import Submission.Work.WilC4aAL.puiseux_root_cover
import Submission.Work.WilC4aAL.analytic_sign_selection
import Submission.Work.WilC4aAL.selector_zero_of_sign_zero

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical Topology Filter
namespace Work.WilC4aAL
open WilkiesDesign.CG.C4a

/-- The witness hypothesis transported from the parameter `s` to the parameter `r ^ N`:
if every small `s > 0` admits a realiser of `σ` then so does every small `r > 0`, for the family
whose coefficients are precomposed with `r ↦ r ^ N`. -/
theorem exists_witness_comp_pow {k : ℕ} {d : Fin k → ℕ} {c : ∀ i, Fin (d i) → ℝ → ℝ}
    {N : ℕ} (hN : 0 < N) {σ : Fin k → SignType}
    (h : ∃ s₀ > (0 : ℝ), ∀ s ∈ Set.Ioo (0 : ℝ) s₀, ∃ z : ℝ, SignVectorOk c σ s z) :
    ∃ r₁ > (0 : ℝ), ∀ r ∈ Set.Ioo (0 : ℝ) r₁, ∃ z : ℝ,
      SignVectorOk (fun i j r => c i j (r ^ N)) σ r z := by
  obtain ⟨s₀, hs₀, hs⟩ := h
  refine ⟨min s₀ 1, lt_min hs₀ one_pos, ?_⟩
  intro r hr
  have hr1 : r ≤ 1 := le_of_lt (lt_of_lt_of_le hr.2 (min_le_right _ _))
  have hrs₀ : r < s₀ := lt_of_lt_of_le hr.2 (min_le_left _ _)
  have hrN : r ^ N < s₀ := lt_of_le_of_lt (pow_le_of_le_one hr.1.le hr1 hN.ne') hrs₀
  obtain ⟨z, hz⟩ := hs (r ^ N) ⟨pow_pos hr.1 N, hrN⟩
  exact ⟨z, fun i => hz i⟩

/-- **C4a.AL, the deliverable.** Sign conditions realisable for all small `s` are realised by a
single real-analytic `ζ` along the Puiseux parametrisation `s = r ^ N`. -/
theorem C4a_arcLift_proved (hP : PuiseuxReal) : ArcLift := by
  intro k d c σ hc hwit
  obtain ⟨N, hN, m, ζ, hζ, hcov⟩ := puiseux_root_cover hP hc
  obtain ⟨ρ, hρ, r₂, hr₂, hsel⟩ :=
    analytic_sign_selection (c := fun i j r => c i j (r ^ N)) (m := m) (ζ := ζ)
      (fun i j => analyticAt_comp_pow (hc i j) hN) hζ hcov σ
      (exists_witness_comp_pow hN hwit)
  exact ⟨N, ρ, hN, hρ, r₂, hr₂, fun r hr i => hsel r hr i⟩

/-- `C4a_arcLift_proved` has exactly the type of the SPEC hole `C4a_arcLift`. -/
example : (PuiseuxReal → ArcLift) := @C4a_arcLift_proved

/-- **The strengthened form used by the curve-selection induction step.**  If one of the sign
conditions is `0` and the coefficients of the corresponding family vanish at `0`, the selector
produced by `ArcLift` also vanishes at `0`.  With `γ(r) = L(γ'(r^N), ζ(r))` and `L` linear this
is what makes `γ(0) = 0`. -/
theorem C4a_arcLift_zero_proved (hP : PuiseuxReal) {k : ℕ} {d : Fin k → ℕ}
    {c : ∀ i, Fin (d i) → ℝ → ℝ} (hc : ∀ i j, AnalyticAt ℝ (c i j) 0)
    (i₀ : Fin k) (hc₀ : ∀ j, c i₀ j 0 = 0) (σ : Fin k → SignType) (hσ : σ i₀ = 0)
    (hwit : ∃ s₀ > (0 : ℝ), ∀ s ∈ Set.Ioo (0 : ℝ) s₀, ∃ z : ℝ, ∀ i,
      SignType.sign (mpoly (c i) s z) = σ i) :
    ∃ N ζ, 0 < N ∧ AnalyticAt ℝ ζ 0 ∧ ζ 0 = 0 ∧ ∃ r₀ > (0 : ℝ),
      ∀ r ∈ Set.Ioo (0 : ℝ) r₀, ∀ i,
        SignType.sign (mpoly (c i) (r ^ N) (ζ r)) = σ i := by
  obtain ⟨N, ζ, hN, hζ, r₀, hr₀, hsel⟩ := C4a_arcLift_proved hP k d c σ hc hwit
  refine ⟨N, ζ, hN, hζ, ?_, r₀, hr₀, hsel⟩
  refine selector_zero_of_sign_zero (c := fun i j r => c i j (r ^ N)) i₀ ?_ ?_ hζ hσ
    ⟨r₀, hr₀, fun r hr => hsel r hr⟩
  · intro j
    simpa using analyticAt_comp_pow (hc i₀ j) hN
  · intro j
    simpa [zero_pow hN.ne'] using hc₀ j

end Work.WilC4aAL

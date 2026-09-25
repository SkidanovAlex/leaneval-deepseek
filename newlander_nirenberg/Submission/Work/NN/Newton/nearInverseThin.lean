import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Newton.closedBallContraction
import Submission.Work.NN.Newton.expansionNearId
import Submission.Work.NN.Newton.inverseSmooth
import Submission.Work.NN.Newton.inverseDerivBounds

open scoped ContDiff Topology
open Filter

namespace Work.NN.Newton

/-- For a polydisc of positive radius around the origin, membership is the ordinary ball condition. -/
private lemma mem_polydisc_zero_iff' {n : ℕ} {r : ℝ} (hr : 0 < r) (z : Fin n → ℂ) :
    z ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => r) ↔ ‖z‖ < r := by
  rw [Work.CR.Flat.mem_polydisc]
  simp [pi_norm_lt_iff hr]

/-- A polydisc of positive radius around the origin is the open ball for the sup norm. -/
private lemma polydisc_zero_eq_ball' {n : ℕ} {r : ℝ} (hr : 0 < r) :
    Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => r) = Metric.ball (0 : Fin n → ℂ) r := by
  ext z
  rw [mem_polydisc_zero_iff' hr z, mem_ball_zero_iff]

/-- A continuous linear endomorphism within `1/2` of the identity is an equivalence. -/
private lemma exists_equiv_of_norm_sub_id_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {A : E →L[ℝ] E}
    (hA : ‖A - ContinuousLinearMap.id ℝ E‖ ≤ (1 / 2 : ℝ)) :
    ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = A := by
  have h1 : ‖(1 : E →L[ℝ] E) - A‖ ≤ (1 / 2 : ℝ) := by rw [← norm_sub_rev A 1]; exact hA
  have h2 : ‖(1 : E →L[ℝ] E) - A‖ < 1 := lt_of_le_of_lt h1 (by norm_num)
  have hu : IsUnit A := by
    have h := isUnit_one_sub_of_norm_lt_one (x := (1 : E →L[ℝ] E) - A) h2
    rwa [sub_sub_cancel] at h
  have hbij : Function.Bijective A := ContinuousLinearMap.isUnit_iff_bijective.mp hu
  exact ⟨ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr hbij.1)
      (LinearMap.range_eq_top.mpr hbij.2), ContinuousLinearEquiv.coe_ofBijective _ _ _⟩

set_option maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
theorem nearInverseThin {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {R R' ε : ℝ} (hR : 0 < R) (hR' : 0 < R') (hR'R : R' < R) (hε : 0 < ε)
    (hε4 : ε ≤ (R - R') / 4)
    {w : (Fin n → ℂ) → (Fin n → ℂ)}
    (hw : ∀ m : ℕ, ContDiffOn ℝ m w (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R)))
    (hb : ∀ z ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R),
      ‖fderiv ℝ w z - ContinuousLinearMap.id ℝ (Fin n → ℂ)‖ ≤ 1 / 2)
    (hh : ∀ z ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R),
      ∀ z' ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R),
      ‖fderiv ℝ w z - fderiv ℝ w z'‖ ≤ (1 / 16) * ‖z - z'‖ ^ α)
    (hc : ∀ z ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R),
      ∀ j : Fin n, ‖(w z) j - z j‖ ≤ ε) :
    ∃ Ψ : (Fin n → ℂ) → (Fin n → ℂ),
      (∀ ζ ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R'), w (Ψ ζ) = ζ) ∧
      (∀ ζ ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R'),
        Ψ ζ ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => (R + R') / 2)) ∧
      (∀ ζ ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R'),
        ∀ z ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R), w z = ζ → Ψ ζ = z) ∧
      (∀ m : ℕ, ContDiffOn ℝ m Ψ (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R'))) ∧
      (∀ ζ ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R'),
        ∀ ζ' ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R'),
        ‖Ψ ζ - Ψ ζ'‖ ≤ 2 * ‖ζ - ζ'‖) ∧
      (∀ ζ ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R'), ‖fderiv ℝ Ψ ζ‖ ≤ 2) ∧
      (∀ ζ ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R'),
        ∀ ζ' ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R'),
        ‖fderiv ℝ Ψ ζ - fderiv ℝ Ψ ζ'‖ ≤ (1 / 2) * ‖ζ - ζ'‖ ^ α) := by
  classical
  have hmem_s : ∀ z : Fin n → ℂ,
      z ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R) ↔ ‖z‖ < R :=
    fun z => mem_polydisc_zero_iff' hR z
  have hmem_t : ∀ z : Fin n → ℂ,
      z ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R') ↔ ‖z‖ < R' :=
    fun z => mem_polydisc_zero_iff' hR' z
  have hopen : IsOpen (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R)) :=
    Work.CR.Flat.isOpen_polydisc _ _
  have hopen' : IsOpen (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R')) :=
    Work.CR.Flat.isOpen_polydisc _ _
  have hconv : Convex ℝ (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R)) := by
    rw [polydisc_zero_eq_ball' hR]; exact convex_ball 0 R
  have hρ_pos : 0 < R' + ε := by linarith
  have hρ_lt : R' + ε < R := by linarith
  have hρ_mid : R' + ε < (R + R') / 2 := by linarith
  have hclosed_sub : Metric.closedBall (0 : Fin n → ℂ) (R' + ε) ⊆
      Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R) := by
    intro z hz
    rw [hmem_s z]
    have h1 : ‖z‖ ≤ R' + ε := mem_closedBall_zero_iff.mp hz
    linarith
  have hdiff_w : ∀ x ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R),
      DifferentiableAt ℝ w x :=
    fun x hx => ((hw 1).contDiffAt (hopen.mem_nhds hx)).differentiableAt (by norm_num)
  have hexp := expansionNearId (f := w) hconv hdiff_w hb
  -- Existence of a preimage in the closed ball of radius `R' + ε` for every `ζ` in the
  -- polydisc of radius `R'`: the map `z ↦ ζ - (w z - z)` is a `1/2`-contraction of that ball.
  have hexists : ∀ ζ : Fin n → ℂ, ζ ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R') →
      ∃ z : Fin n → ℂ, z ∈ Metric.closedBall (0 : Fin n → ℂ) (R' + ε) ∧ w z = ζ := by
    intro ζ hζ
    have hζn : ‖ζ‖ < R' := (hmem_t ζ).mp hζ
    have hmaps : ∀ z ∈ Metric.closedBall (0 : Fin n → ℂ) (R' + ε),
        ζ - (w z - z) ∈ Metric.closedBall (0 : Fin n → ℂ) (R' + ε) := by
      intro z hz
      have hzs : z ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R) := hclosed_sub hz
      have hwz : ‖w z - z‖ ≤ ε := by
        rw [pi_norm_le_iff_of_nonneg hε.le]
        intro j
        exact hc z hzs j
      rw [mem_closedBall_zero_iff]
      calc ‖ζ - (w z - z)‖ ≤ ‖ζ‖ + ‖w z - z‖ := norm_sub_le _ _
        _ ≤ R' + ε := by linarith
    have hcontr : ∀ z ∈ Metric.closedBall (0 : Fin n → ℂ) (R' + ε),
        ∀ z' ∈ Metric.closedBall (0 : Fin n → ℂ) (R' + ε),
        ‖(ζ - (w z - z)) - (ζ - (w z' - z'))‖ ≤ (1 / 2) * ‖z - z'‖ := by
      intro z hz z' hz'
      have h1 := hexp.1 z (hclosed_sub hz) z' (hclosed_sub hz')
      have heq : (ζ - (w z - z)) - (ζ - (w z' - z')) = -((w z - w z') - (z - z')) := by abel
      rw [heq, norm_neg]
      exact h1
    obtain ⟨z, hzmem, hzfix⟩ :=
      closedBallContraction (E := Fin n → ℂ) (ρ := R' + ε) hρ_pos.le hmaps hcontr
    refine ⟨z, hzmem, ?_⟩
    have h2 : ζ - w z = 0 := by
      have h3 : ζ - (w z - z) - z = 0 := by rw [hzfix, sub_self]
      rwa [show ζ - (w z - z) - z = ζ - w z from by abel] at h3
    exact (sub_eq_zero.mp h2).symm
  -- Turn the dependent existence into a plain choice, so that `Ψ` is an ordinary function.
  have hexists' : ∀ ζ : Fin n → ℂ, ∃ z : Fin n → ℂ,
      (ζ ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R') →
        (z ∈ Metric.closedBall (0 : Fin n → ℂ) (R' + ε) ∧ w z = ζ)) := by
    intro ζ
    by_cases h : ζ ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R')
    · obtain ⟨z, hz1, hz2⟩ := hexists ζ h
      exact ⟨z, fun _ => ⟨hz1, hz2⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose Ψ hΨ using hexists'
  have hΨ_spec : ∀ ζ (h : ζ ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R')),
      Ψ ζ ∈ Metric.closedBall (0 : Fin n → ℂ) (R' + ε) ∧ w (Ψ ζ) = ζ :=
    fun ζ h => hΨ ζ h
  have hΨw : ∀ ζ ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R'), w (Ψ ζ) = ζ :=
    fun ζ h => (hΨ_spec ζ h).2
  have hΨmem_closed : ∀ ζ ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R'),
      Ψ ζ ∈ Metric.closedBall (0 : Fin n → ℂ) (R' + ε) := fun ζ h => (hΨ_spec ζ h).1
  have hΨmem_s : ∀ ζ ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R'),
      Ψ ζ ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R) :=
    fun ζ h => hclosed_sub (hΨmem_closed ζ h)
  have hmem_mid : ∀ z : Fin n → ℂ,
      z ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => (R + R') / 2) ↔
        ‖z‖ < (R + R') / 2 :=
    fun z => mem_polydisc_zero_iff' (by linarith) z
  have hΨmem_mid : ∀ ζ ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R'),
      Ψ ζ ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => (R + R') / 2) := by
    intro ζ h
    rw [hmem_mid (Ψ ζ)]
    have h1 : ‖Ψ ζ‖ ≤ R' + ε := mem_closedBall_zero_iff.mp (hΨmem_closed ζ h)
    linarith
  have hΨuniq : ∀ ζ ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R'),
      ∀ z ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R), w z = ζ → z = Ψ ζ := by
    intro ζ hζ z hz hwz
    exact hexp.2.2 hz (hΨmem_s ζ hζ) (by rw [hwz, hΨw ζ hζ])
  have hΨlip : ∀ ζ ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R'),
      ∀ ζ' ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R'),
      ‖Ψ ζ - Ψ ζ'‖ ≤ 2 * ‖ζ - ζ'‖ := by
    intro ζ hζ ζ' hζ'
    have h1 := hexp.1 (Ψ ζ) (hΨmem_s ζ hζ) (Ψ ζ') (hΨmem_s ζ' hζ')
    have h2 : ‖w (Ψ ζ) - w (Ψ ζ')‖ = ‖ζ - ζ'‖ := by rw [hΨw ζ hζ, hΨw ζ' hζ']
    have h3 : ‖Ψ ζ - Ψ ζ'‖ ≤ ‖w (Ψ ζ) - w (Ψ ζ')‖
        + ‖(w (Ψ ζ) - w (Ψ ζ')) - (Ψ ζ - Ψ ζ')‖ := norm_le_insert _ _
    rw [h2] at h3
    linarith
  have hinv : ∀ x ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R),
      ∃ e : (Fin n → ℂ) ≃L[ℝ] (Fin n → ℂ),
        (e : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)) = fderiv ℝ w x :=
    fun x hx => exists_equiv_of_norm_sub_id_le (hb x hx)
  have hsm : ∀ m : ℕ,
      ContDiffOn ℝ m Ψ (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R')) :=
    inverseSmooth (w := w) (s := Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R))
      (Ψ := Ψ) (t := Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R'))
      hopen hw hinv hexp.2.2 hopen' hΨmem_s hΨw
  have hΨdiff : ∀ ζ ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R'),
      DifferentiableAt ℝ Ψ ζ :=
    fun ζ hζ => ((hsm 1).contDiffAt (hopen'.mem_nhds hζ)).differentiableAt (by norm_num)
  have hwdiff : ∀ ζ ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R'),
      DifferentiableAt ℝ w (Ψ ζ) :=
    fun ζ hζ => ((hw 1).contDiffAt (hopen.mem_nhds (hΨmem_s ζ hζ))).differentiableAt (by norm_num)
  have hchain : ∀ ζ ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R'),
      (fderiv ℝ w (Ψ ζ)).comp (fderiv ℝ Ψ ζ)
        = ContinuousLinearMap.id ℝ (Fin n → ℂ) := by
    intro ζ hζ
    have heq : (w ∘ Ψ) =ᶠ[𝓝 ζ] id := by
      filter_upwards [hopen'.mem_nhds hζ] with y hy
      exact hΨw y hy
    have hcomp : fderiv ℝ (w ∘ Ψ) ζ = (fderiv ℝ w (Ψ ζ)).comp (fderiv ℝ Ψ ζ) :=
      fderiv_comp ζ (hwdiff ζ hζ) (hΨdiff ζ hζ)
    have hidd : fderiv ℝ (w ∘ Ψ) ζ = ContinuousLinearMap.id ℝ (Fin n → ℂ) := by
      rw [heq.fderiv_eq, fderiv_id]
    rw [hcomp] at hidd
    exact hidd
  obtain ⟨hbnd_deriv, hbnd_holder⟩ :=
    inverseDerivBounds (F := w) (Ψ := Ψ)
      (s := Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R))
      (t := Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => R'))
      hα0 hα1.le hchain hb hh hΨmem_s hΨlip
  refine ⟨Ψ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ζ hζ; exact hΨw ζ hζ
  · intro ζ hζ; exact hΨmem_mid ζ hζ
  · intro ζ hζ z hz hwz; exact (hΨuniq ζ hζ z hz hwz).symm
  · intro m; exact hsm m
  · intro ζ hζ ζ' hζ'; exact hΨlip ζ hζ ζ' hζ'
  · intro ζ hζ; exact hbnd_deriv ζ hζ
  · intro ζ hζ ζ' hζ'; exact hbnd_holder ζ hζ ζ' hζ'

end Work.NN.Newton

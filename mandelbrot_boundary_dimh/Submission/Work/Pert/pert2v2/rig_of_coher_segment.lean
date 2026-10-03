import Mathlib
import Submission.Work.Pert.pert2v2.rig_of_coher
import Submission.Work.Pert.pert2v2.XcConst
import Submission.Work.Pert.pert2v2.exists_Psi_lower

/-!
# `Work.Pert.pert2v2.rig_of_coher_segment`

The **segment** form of `Work.Pert.pert2v2.rig_of_coher`: the rigidity `(RIG)` of the perturbed
lower-gate coordinate `Φm` at *all* the points `w = x + i y₀` (`x ∈ [0,1)`) of the datum's curve,
with a **uniform** `δ₀` in `x`.

`rig_of_coher` compares `Φm` with a *model* Fatou coordinate `Ψ` of `F0f = τ₀ ∘ f₀ ∘ τ₀` on the
left cone at one datum-level point `Xc d w`; its `δ₀` (produced by
`gate_coord_close_minus_gen_r`) depends on the compact set on which the comparison is made, hence
on `w`, so it cannot be applied to each `x ∈ [0,1)` separately.  Here the compact set is the whole
curve segment

  `K = {Xc d (x + i y₀) | x ∈ [0,1]}`,

which is compact because `x ↦ Xc d (x + i y₀)` is differentiable on `[0,1]` (each `x + i y₀` lies
in the repelling sector `QLeft ξ₀`, so in `Dφ`, and the curve value has nonzero modulus by the
segment hypothesis).  Then **one** application of `gate_coord_close_minus_gen_r` on `K` gives the
uniform `δ₀`.

The two model inputs are the ones produced in `XcConst` / `exists_Psi_lower`:

* `exists_Psi_lower` produces a model coordinate `Ψ` of `F0f` on `Qreg none (some (-Ξ'))` from the
  FATOU contract — this is why the statement needs no `Ψ`-hypothesis;
* `Xc_coher_pin` gives the *same* constant `c` with `Ψ (Xc d u) = u + c` both at the deep anchor
  `u = -M` and at every segment point `u = x + i y₀`, `x ∈ [0,1)`.

With the pin `Φm (Xc d (-M)) = -M` the relative closeness of `gate_coord_close_minus_gen_r` then
collapses to the absolute statement `‖Φm (Xc d w) - w‖ < εp`:

  `(Φm ζ - Φm z₀) - (Ψ ζ - Ψ z₀) = Φm ζ - ζ`   for `ζ = Xc d w`, `z₀ = Xc d (-M)`.
-/

namespace Work.Pert.pert2v2

open _root_.MandelDim Complex Set Metric Filter Topology
open scoped Topology

noncomputable section

/-- **Differentiability of the curve along the segment.**  If `Ξ' > 0`, `y₀` dominates the sector
threshold `2 (1 + ξ₀)`, and the curve values `Xc d (x + i y₀)`, `x ∈ [0,1]`, lie in the left cone
`Qreg none (some (-Ξ'))`, then `x ↦ Xc d (x + i y₀)` is differentiable at every `x ∈ [0,1]`.

Each `x + i y₀` lies in the repelling sector `QLeft ξ₀` (so in `Dφ`), and its curve value is
nonzero because it is in `Qreg none (some (-Ξ'))`, which does not contain `0`. -/
theorem differentiableAt_Xc_segment {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {Ξ' y₀ : ℝ} (hΞ' : 0 < Ξ') (hy : 2 * (1 + d.ξ₀) < y₀)
    (hseg : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I)
        ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ)))) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (fun x : ℝ => Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I)) x := by
  intro x hx
  obtain ⟨hx0, hx1⟩ := hx
  -- the point `x + i y₀` lies in the repelling sector, hence in `Dφ`
  have huQ : ((x : ℂ) + (y₀ : ℂ) * Complex.I) ∈ MandelDim.QLeft d.ξ₀ :=
    mem_QLeft_ray (by linarith)
  have huD : ((x : ℂ) + (y₀ : ℂ) * Complex.I) ∈ d.Dφ := d.Q_sub huQ
  -- its curve value is in the cone, hence nonzero, hence `d.φ` does not vanish there
  have hXcQ : Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I)
      ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ))) := hseg x hx0 hx1
  have hφne : d.φ ((x : ℂ) + (y₀ : ℂ) * Complex.I) ≠ 0 := by
    intro h0
    exact Xc_ne_zero_of_mem d hΞ' hXcQ (by simp [Work.Pert.Xc, h0, MandelDim.tau0])
  have hdXc : DifferentiableAt ℂ (Work.Pert.Xc d) ((x : ℂ) + (y₀ : ℂ) * Complex.I) :=
    differentiableAt_Xc d huD hφne
  have h1 : DifferentiableAt ℝ (fun x : ℝ => (x : ℂ) + (y₀ : ℂ) * Complex.I) x := by fun_prop
  exact DifferentiableAt.comp (x := x) (g := fun u : ℂ => Work.Pert.Xc d u)
    (hdXc.restrictScalars ℝ) h1

/-- **Compactness of the curve segment** `K = Xc d '' {(x + i y₀) | x ∈ [0,1]}`. -/
theorem isCompact_Xc_segment_image {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {Ξ' y₀ : ℝ} (hΞ' : 0 < Ξ') (hy : 2 * (1 + d.ξ₀) < y₀)
    (hseg : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I)
        ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ)))) :
    IsCompact ((fun x : ℝ => Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I))
      '' Set.Icc (0 : ℝ) 1) :=
  isCompact_Icc.image_of_continuousOn fun x hx =>
    ((differentiableAt_Xc_segment d hΞ' hy hseg x hx).continuousAt).continuousWithinAt

theorem rig_of_coher_segment {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement) (hd : MandelDim.IsParabolicGerm f₀ D₀) :
    ∃ Ξ₀ : ℝ, 0 < Ξ₀ ∧ ∃ r : ℝ, 0 < r ∧ ∀ Ξ' : ℝ, Ξ₀ ≤ Ξ' → ∃ Y : ℝ, 0 < Y ∧
      ∀ y₀ : ℝ, Y ≤ y₀ → ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
      Work.Pert.Xc d (-M) ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ))) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 →
        Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I)
          ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ)))) →
      ∀ εp : ℝ, 0 < εp → ∀ L : Set ℂ, IsCompact L → L ⊆ D₀ →
      ∀ ρ : ℝ, r ≤ ρ → Metric.closedBall (0 : ℂ) ρ ⊆ L →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (f : ℂ → ℂ) (Df : Set ℂ) (u : ℂ → ℂ) (σ α : ℂ) (Φm : ℂ → ℂ),
        MandelDim.NearOn f₀ f Df L δ₀ → f 0 = 0 → MandelDim.InF1 (MandelDim.rotOf f) →
        α = MandelDim.rotOf f → DifferentiableOn ℂ u (Metric.ball 0 ρ) →
        (∀ z ∈ Metric.ball 0 ρ, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
        (∀ z ∈ Metric.ball 0 ρ, f z = z + z * (z - σ) * u z) →
        1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
        (∀ z ∈ Work.Pert.Qm Ξ' α, Work.Pert.tauC σ α z ∈ Metric.ball 0 ρ) →
        MandelDim.QAdm (some ((Ξ' : ℂ) - 1 / α)) (some (-(Ξ' : ℂ))) →
        MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ' α) →
        MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ' α) →
        Φm (Work.Pert.Xc d (-M)) = (-M : ℂ) →
        ∀ x : ℝ, 0 ≤ x → x < 1 →
          ‖Φm (Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I))
            - ((x : ℂ) + (y₀ : ℂ) * Complex.I)‖ < εp := by
  -- the three producers: the gate limit theorem (with its uniform radius), the model coherence
  -- with the same constant at the anchor and on the segment, and the model coordinate itself.
  obtain ⟨ξg, hξg, r, hr, Hgate⟩ := gate_coord_close_minus_gen_r d hF hd
  obtain ⟨ξc, hξc, Hcoher⟩ := Xc_coher_pin d hF hd
  obtain ⟨ξP, hξP, HPsi⟩ := exists_Psi_lower d hF hd
  refine ⟨max (max ξg ξc) (max ξP 1), ?_, r, hr, fun Ξ' hΞ' => ?_⟩
  · exact lt_of_lt_of_le hξg (le_trans (le_max_left ξg ξc) (le_max_left _ _))
  have hΞ'g : ξg ≤ Ξ' := le_trans (le_trans (le_max_left ξg ξc) (le_max_left _ _)) hΞ'
  have hΞ'c : ξc ≤ Ξ' := le_trans (le_trans (le_max_right ξg ξc) (le_max_left _ _)) hΞ'
  have hΞ'P : ξP ≤ Ξ' := le_trans (le_trans (le_max_left ξP 1) (le_max_right _ _)) hΞ'
  have hΞ'one : (1 : ℝ) ≤ Ξ' := le_trans (le_trans (le_max_right ξP 1) (le_max_right _ _)) hΞ'
  have hΞ'pos : 0 < Ξ' := lt_of_lt_of_le zero_lt_one hΞ'one
  -- the model coordinate `Ψ` of `F0f` on the left cone (from the FATOU contract)
  obtain ⟨Ψ, hΨ⟩ := HPsi Ξ' hΞ'P
  -- the model coherence at the anchor and on the segment, with one common constant `c`
  obtain ⟨Yc, hYc, hcoh⟩ := Hcoher Ξ' hΞ'c
  refine ⟨max Yc (2 * (1 + d.ξ₀) + 1), ?_, fun y₀ hy₀ => ?_⟩
  · exact lt_of_lt_of_le hYc (le_max_left Yc (2 * (1 + d.ξ₀) + 1))
  have hyc : Yc ≤ y₀ := le_trans (le_max_left _ _) hy₀
  have hyξ : 2 * (1 + d.ξ₀) + 1 ≤ y₀ := le_trans (le_max_right _ _) hy₀
  have hy : 2 * (1 + d.ξ₀) < y₀ := by linarith
  obtain ⟨c, Mc, hcM, hcx⟩ := hcoh y₀ hyc Ψ hΨ
  refine ⟨max Mc 1, lt_of_lt_of_le zero_lt_one (le_max_right Mc 1), fun M hM => ?_⟩
  have hMc : Mc ≤ M := le_trans (le_max_left Mc 1) hM
  intro hz0Q hsegQ εp hεp L hLc hLD0 ρ hρ hρball
  -- the compact curve segment, contained in the left cone by the segment hypothesis
  set K : Set ℂ :=
    (fun x : ℝ => Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I)) '' Set.Icc (0 : ℝ) 1
    with hKdef
  have hKc : IsCompact K := by
    rw [hKdef]
    exact isCompact_Xc_segment_image d hΞ'pos hy hsegQ
  have hKQ : K ⊆ MandelDim.Qreg none (some (-(Ξ' : ℂ))) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact hsegQ x hx.1 hx.2
  -- ONE application of the gate limit theorem on the whole segment
  obtain ⟨δ₀, hδ₀, hkey⟩ := Hgate Ξ' hΞ'g Ψ hΨ (Work.Pert.Xc d (-M)) hz0Q K hKc hKQ
    εp hεp L hLc hLD0 ρ hρ hρball
  refine ⟨δ₀, hδ₀, ?_⟩
  intro f Df u σ α Φm hNear hf0 hInF1 hα hu hu2 hf hσ htauC hQAdm hNT hΦm hpin x hx0 hx1
  have hζK : Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I) ∈ K := by
    rw [hKdef]
    exact ⟨x, ⟨hx0, le_of_lt hx1⟩, rfl⟩
  have hk := hkey f Df u σ α Φm hNear hf0 hInF1 hα hu hu2 hf hσ htauC hQAdm hNT hΦm
    (Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I)) hζK
  -- the coherence at the two points turns the relative closeness into the absolute one
  have hΨx : Ψ (Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I))
      = ((x : ℂ) + (y₀ : ℂ) * Complex.I) + c := by
    have h := hcx x hx0 hx1
    linear_combination h
  have hΨz : Ψ (Work.Pert.Xc d (-M)) = (-M : ℂ) + c := by
    have h := hcM M hMc
    linear_combination h
  have hEq : (Φm (Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I)) - Φm (Work.Pert.Xc d (-M)))
      - (Ψ (Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I)) - Ψ (Work.Pert.Xc d (-M)))
      = Φm (Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I))
        - ((x : ℂ) + (y₀ : ℂ) * Complex.I) := by
    rw [hpin, hΨx, hΨz]
    ring
  rw [hEq] at hk
  exact hk

end

end Work.Pert.pert2v2

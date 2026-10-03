import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.chain

/-!
# L62 (c): elementary auxiliary lemmas for the end choice and for perturbation control

This file collects the elementary, sorry-free parts of the third L62 stretch:

* the geometry of the two horn-data components `Bu`, `Bl` (they are bounded away from the
  opposite half-planes) and the resulting bound `|Im z| ≤ η` for points outside `d.DE`;
* `T`-equivariance of the lifted horn map on `Bu` and `Bl`;
* **the end/centre choice** (`exists_avoiding_center`): for two points `ζa ≠ ζb mod ℤ` at least
  one of them keeps the disc `ball ζ ρ` away from the critical values `v + ℤ - β`;
* **the Cauchy-type control of a perturbation** (`perturbation_deriv_bound`): a function
  `R - E` holomorphic on `DR ⊇ {y₁ < im}` and bounded by `δ` there has derivative bounded by
  `δ / r` on `{y₁ + r < im}`.
-/

namespace Work.L62

open MandelDim Set Filter Topology
open scoped Topology

noncomputable section

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

/-! ## Elementary geometry of `Bu`, `Bl` -/

/-- `Bu` is bounded below by `-η` (otherwise it would meet `Bl`). -/
theorem Bu_im_ge (d : ParabData g₀ D) (hd : HornData d) {w : ℂ} (hw : w ∈ hd.Bu) :
    -hd.η ≤ w.im := by
  by_contra h
  exact hd.disj.le_bot ⟨hw, hd.lower (lt_of_not_ge h)⟩

/-- `Bl` is bounded above by `η` (otherwise it would meet `Bu`). -/
private theorem Bl_im_le (d : ParabData g₀ D) (hd : HornData d) {w : ℂ} (hw : w ∈ hd.Bl) :
    w.im ≤ hd.η := by
  by_contra h
  exact hd.disj.le_bot ⟨hd.upper (lt_of_not_ge h), hw⟩

/-- A point outside the maximal lift domain `d.DE` lies in the horizontal strip `|Im| ≤ η`. -/
theorem not_mem_DE_im_bounds (d : ParabData g₀ D) (hd : HornData d) {z : ℂ}
    (hz : z ∉ d.DE) : z.im ≤ hd.η ∧ -hd.η ≤ z.im := by
  constructor
  · by_contra h
    exact hz (hd.sub (Or.inl (hd.upper (lt_of_not_ge h))))
  · by_contra h
    exact hz (hd.sub (Or.inr (hd.lower (lt_of_not_ge h))))

/-- `E = Φ ∘ φ` is `T`-equivariant on `Bu` (the upper component of `φ⁻¹(basin)`). -/
theorem E_add_one_Bu (d : ParabData g₀ D) (hd : HornData d) {w : ℂ} (hw : w ∈ hd.Bu) :
    d.E (w + 1) = d.E w + 1 := by
  have hw1 : w + 1 ∈ hd.Bu := (hd.Bu_T w).mp hw
  obtain ⟨hwφ, hwb⟩ := hd.sub (Or.inl hw)
  obtain ⟨hw1φ, -⟩ := hd.sub (Or.inl hw1)
  show d.Φ (d.φ (w + 1)) = d.Φ (d.φ w) + 1
  rw [d.φ_abel w hwφ hw1φ]
  exact d.Φ_abel (d.φ w) hwb

/-- `E` is `T`-equivariant on `Bl`. -/
theorem E_add_one_Bl (d : ParabData g₀ D) (hd : HornData d) {w : ℂ} (hw : w ∈ hd.Bl) :
    d.E (w + 1) = d.E w + 1 := by
  have hw1 : w + 1 ∈ hd.Bl := (hd.Bl_T w).mp hw
  obtain ⟨hwφ, hwb⟩ := hd.sub (Or.inr hw)
  obtain ⟨hw1φ, -⟩ := hd.sub (Or.inr hw1)
  show d.Φ (d.φ (w + 1)) = d.Φ (d.φ w) + 1
  rw [d.φ_abel w hwφ hw1φ]
  exact d.Φ_abel (d.φ w) hwb

/-! ## The end/centre choice -/

/-- **The choice of the disc centre.**  Let `ζa ≢ ζb (mod ℤ)` with separation `δ`
(`δ ≤ ‖(ζa - ζb) - k‖` for all `k : ℤ`) and let `ρ < δ / 2`.  Then at least one of `ζa`, `ζb`
has its `β`-translate at distance more than `ρ` from the critical values `v + ℤ` of `E - β`;
hence the disc of radius `ρ` around it misses the critical values, so that the inverse branch of
`E - β` exists over it. -/
theorem exists_avoiding_center (d : ParabData g₀ D) (hd : HornData d) {ζa ζb β : ℂ} {ρ δ : ℝ}
    (hδ : 0 < δ) (hsep : ∀ k : ℤ, δ ≤ ‖(ζa - ζb) - (k : ℂ)‖) (hρ : 2 * ρ < δ) :
    ∃ ζ ∈ ({ζa, ζb} : Set ℂ), ∀ k : ℤ, ρ < ‖ζ + β - (hd.v + (k : ℂ))‖ := by
  by_contra h
  push_neg at h
  obtain ⟨k₁, hk₁⟩ := h ζa (Or.inl rfl)
  obtain ⟨k₂, hk₂⟩ := h ζb (Or.inr rfl)
  have htri : ‖(ζa - ζb) - ((k₁ - k₂ : ℤ) : ℂ)‖
      = ‖(ζa + β - (hd.v + (k₁ : ℂ))) - (ζb + β - (hd.v + (k₂ : ℂ)))‖ := by
    push_cast
    ring_nf
  have hle : ‖(ζa - ζb) - ((k₁ - k₂ : ℤ) : ℂ)‖ ≤ 2 * ρ := by
    rw [htri]
    exact le_trans (norm_sub_le _ _) (by linarith)
  have := hsep (k₁ - k₂)
  linarith

/-! ## Cauchy-type control of a perturbation on the deep region -/

/-- If `R - E` is holomorphic on `DR ⊇ {y₁ < im}` and bounded by `δ` there, then on the deeper
half-plane `{y₁ + r < im}` its derivative is bounded by `δ / r`. -/
theorem perturbation_deriv_bound {R E : ℂ → ℂ} {DR : Set ℂ}
    (hR : DifferentiableOn ℂ R DR) (hE : DifferentiableOn ℂ E DR)
    {y₁ δ r : ℝ} (hr : 0 < r)
    (hball : ∀ w : ℂ, y₁ + r < w.im → Metric.closedBall w r ⊆ DR)
    (hclose : ∀ w : ℂ, y₁ < w.im → ‖R w - E w‖ < δ) :
    ∀ w : ℂ, y₁ + r < w.im → ‖deriv (fun u => R u - E u) w‖ ≤ δ / r := by
  intro w hw
  have hf : DifferentiableOn ℂ (fun u => R u - E u) DR := hR.sub hE
  have hdc : DiffContOnCl ℂ (fun u => R u - E u) (Metric.ball w r) :=
    hf.diffContOnCl_ball (hball w hw)
  have hsph : ∀ z ∈ Metric.sphere w r, ‖(fun u => R u - E u) z‖ ≤ δ := by
    intro z hz
    have hdist : dist z w = r := Metric.mem_sphere.mp hz
    have hnorm : ‖z - w‖ = r := by simpa [dist_eq_norm] using hdist
    have him : y₁ < z.im := by
      have h1 : |(z - w).im| ≤ ‖z - w‖ := Complex.abs_im_le_norm _
      rw [Complex.sub_im] at h1
      have h2 := (abs_le.mp h1).1
      linarith
    exact le_of_lt (hclose z him)
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdc hsph

end

end Work.L62

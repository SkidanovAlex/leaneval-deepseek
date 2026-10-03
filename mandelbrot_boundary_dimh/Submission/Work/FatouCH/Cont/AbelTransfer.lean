import Mathlib
import Submission.Work.Interfaces.Fatou

namespace Work.FatouCH.Cont

open Set Filter Metric
open scoped Topology

set_option linter.unusedVariables false

/-- **Abel transfer.** If `Φ n` are Fatou coordinates for `F n` on the moving domains
`Qreg (b₁ n) (b₂ n)`, if every compact subset of the limit domain `Q = Qreg c₁ c₂` is eventually
contained in the moving domains, if `F n → F₀` uniformly on compacts of `Q` and
`Φ n → Ψ` locally uniformly on `Q`, then `Ψ` satisfies the Abel equation for `F₀` on `Q`:
`Ψ (F₀ z) = Ψ z + 1` whenever `z` and `F₀ z` lie in `Q`.

This is the "passage to the limit" step (Shishikura A.2.1(iii) interface): the Abel relation for
the approximating coordinates survives the locally uniform limit, because the points `z` and
`F n z` are eventually confined to a fixed compact subset of `Q` (which is then contained in the
moving domains), and `Ψ` is continuous at `F₀ z`. -/
theorem AbelTransfer {b₁ b₂ : ℕ → Option ℂ} {c₁ c₂ : Option ℂ} {F : ℕ → ℂ → ℂ} {F₀ : ℂ → ℂ}
    {Φ : ℕ → ℂ → ℂ} {Ψ : ℂ → ℂ} (hOpen : IsOpen (MandelDim.Qreg c₁ c₂))
    (hNT : ∀ n, MandelDim.NearTranslationOn (F n) (MandelDim.Qreg (b₁ n) (b₂ n)))
    (hΦ : ∀ n, MandelDim.IsFatouCoordOn (F n) (Φ n) (MandelDim.Qreg (b₁ n) (b₂ n)))
    (hdom : ∀ K ⊆ MandelDim.Qreg c₁ c₂, IsCompact K →
      ∀ᶠ n in atTop, K ⊆ MandelDim.Qreg (b₁ n) (b₂ n))
    (hF : ∀ K ⊆ MandelDim.Qreg c₁ c₂, IsCompact K → TendstoUniformlyOn F F₀ atTop K)
    (hΨ : TendstoLocallyUniformlyOn Φ Ψ atTop (MandelDim.Qreg c₁ c₂)) :
    ∀ z ∈ MandelDim.Qreg c₁ c₂, F₀ z ∈ MandelDim.Qreg c₁ c₂ → Ψ (F₀ z) = Ψ z + 1 := by
  intro z hz hFz
  -- `Q` is open, so both `z` and `F₀ z` admit closed neighbourhoods inside it.
  obtain ⟨r₁, hr₁pos, hr₁⟩ := Metric.isOpen_iff.mp hOpen z hz
  obtain ⟨r₂, hr₂pos, hr₂⟩ := Metric.isOpen_iff.mp hOpen (F₀ z) hFz
  -- The compact set confining the orbits of `z` near the limit point `z`.
  set K : Set ℂ := Metric.closedBall z (r₁ / 2) ∪ Metric.closedBall (F₀ z) (r₂ / 2) with hKdef
  set A : Set ℂ := Metric.closedBall (F₀ z) (r₂ / 2) with hAdef
  have hKcomp : IsCompact K :=
    (isCompact_closedBall z (r₁ / 2)).union (isCompact_closedBall (F₀ z) (r₂ / 2))
  have hKQ : K ⊆ MandelDim.Qreg c₁ c₂ := by
    intro x hx
    rw [hKdef, mem_union] at hx
    rcases hx with hx | hx
    · exact hr₁ (Metric.closedBall_subset_ball (by linarith) hx)
    · exact hr₂ (Metric.closedBall_subset_ball (by linarith) hx)
  have hAK : A ⊆ K := by
    intro x hx
    rw [hAdef] at hx
    rw [hKdef, mem_union]
    exact Or.inr hx
  have hzu : z ∈ K := by
    rw [hKdef, mem_union]
    left
    rw [Metric.mem_closedBall, dist_self]
    positivity
  -- uniform convergence of `Φ n` resp. `F n` on `K`, hence pointwise at `z`.
  have hKu : TendstoUniformlyOn Φ Ψ atTop K :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hOpen).mp hΨ K hKQ hKcomp
  have hFun : TendstoUniformlyOn F F₀ atTop K := hF K hKQ hKcomp
  have hFnz : Tendsto (fun n => F n z) atTop (𝓝 (F₀ z)) := hFun.tendsto_at hzu
  have hFnzK : ∀ᶠ n in atTop, F n z ∈ K := by
    filter_upwards
      [Metric.tendsto_nhds.mp hFnz (r₂ / 2) (half_pos hr₂pos)] with n hn
    rw [hKdef, mem_union]
    exact Or.inr (Metric.ball_subset_closedBall (Metric.mem_ball.mpr hn))
  -- the moving domains eventually contain `K`, hence `z` and `F n z`.
  have hKQn : ∀ᶠ n in atTop, K ⊆ MandelDim.Qreg (b₁ n) (b₂ n) := hdom K hKQ hKcomp
  -- `Ψ` is continuous at `F₀ z`, being a uniform limit on `A ∋ F₀ z` of continuous maps.
  have hAu : TendstoUniformlyOn Φ Ψ atTop A := hKu.mono hAK
  have hAcontEv : ∀ᶠ n in atTop, ContinuousOn (Φ n) A := by
    filter_upwards [hKQn] with n hn
    exact ((hΦ n).1.mono (fun x hx => hn (hAK hx))).continuousOn
  have hAcont : ContinuousOn Ψ A := hAu.continuousOn hAcontEv.frequently
  have hAnhds : A ∈ 𝓝 (F₀ z) := by
    rw [hAdef]
    exact mem_of_superset (Metric.ball_mem_nhds (F₀ z) (half_pos hr₂pos))
      Metric.ball_subset_closedBall
  have hΨcontAt : ContinuousAt Ψ (F₀ z) := hAcont.continuousAt hAnhds
  have hlim_ΨFz : Tendsto (fun n => Ψ (F n z)) atTop (𝓝 (Ψ (F₀ z))) :=
    hΨcontAt.tendsto.comp hFnz
  have hlim_Φz : Tendsto (fun n => Φ n z) atTop (𝓝 (Ψ z)) := hKu.tendsto_at hzu
  -- the "uniform convergence at a moving point" step: `Φ n (F n z) - Ψ (F n z) → 0`.
  have hdiff : Tendsto (fun n => Φ n (F n z) - Ψ (F n z)) atTop (𝓝 (0 : ℂ)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hKu ε hε, hFnzK] with n hn hnK
    have h := hn (F n z) hnK
    rw [dist_eq_norm] at h
    rw [dist_eq_norm, sub_zero, norm_sub_rev]
    exact h
  have hlim_ΦFz : Tendsto (fun n => Φ n (F n z)) atTop (𝓝 (Ψ (F₀ z))) := by
    have h := hdiff.add hlim_ΨFz
    simpa using h
  -- and the other limit, using the Abel equation for `Φ n` at `z` (valid eventually).
  have hlim_abel : Tendsto (fun n => Φ n (F n z)) atTop (𝓝 (Ψ z + 1)) := by
    refine Tendsto.congr' ?_ (hlim_Φz.add tendsto_const_nhds)
    filter_upwards [hKQn, hFnzK] with n hnK hnFz
    exact ((hΦ n).2.2 z (hnK hzu) (hnK hnFz)).symm
  exact (tendsto_nhds_unique hlim_abel hlim_ΦFz).symm

end Work.FatouCH.Cont

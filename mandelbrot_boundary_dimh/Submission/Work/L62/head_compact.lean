import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.l62c_mid
import Submission.Work.L62.avail_horn_section_up
import Submission.Work.L62.cylinder_model
import Submission.Work.L62.uniform_escape2
import Submission.Work.L62.int_separation
import Submission.Work.L62.local_branch_disc
import Submission.Work.L62.section_chain
import Submission.Work.L62.branch_translate_image
import Submission.Work.L62.compact_uniform_subcover

namespace Work.L62

open MandelDim Set Filter Topology
open scoped Topology

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

/-! ## The compactness of the `β`-box -/

/-- The box `{0 ≤ Re ≤ 1, |Im| ≤ b}` of Lemma 6.2 is compact (it is the image of the rectangle
`[0,1] × [-b,b]` under `(x,y) ↦ x + iy`). -/
private theorem isCompact_box (b : ℝ) :
    IsCompact {β : ℂ | 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b} := by
  have himg : ((fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
      (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (-b) b))
      = {β : ℂ | 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b} := by
    ext β
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨hp1, hp2⟩ := hp
      refine ⟨by simpa using hp1.1, by simpa using hp1.2, ?_⟩
      have h2 : ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I).im = p.2 := by simp
      rw [h2]
      exact abs_le.mpr ⟨hp2.1, hp2.2⟩
    · intro hβ
      refine ⟨(β.re, β.im), ⟨⟨hβ.1, hβ.2.1⟩, ?_⟩, ?_⟩
      · exact abs_le.mp hβ.2.2
      · simp
  rw [← himg]
  exact (isCompact_Icc.prod isCompact_Icc).image (by continuity)

/-! ## The pointwise local data for the head chain -/

/-- **Pointwise local data for the head chain.**  For every `β` (no availability hypothesis is
needed for a *single* step) there are

* a centre `ζ₀ ∈ {ζa, ζb}` with `dist (ζ₀ + β) (v + ℤ) > δ/4`, chosen by `exists_avoiding_center`
  from the fact that `ζa ≢ ζb mod ℤ` (so one of the two discs avoids the critical values of
  `ĥ = d.E - β`),
* a radius `r > 0` and a compact `A ⊆ hd.Bu`,

such that for every `β'` with `β' ∈ ball β (r/4)` and every `ρ ≤ r/4` there is a one-step chain
with `W 0 = ball ζ₀ ρ` whose first step `W 1` lies in `A`.  The inverse branch `ψ` of `ĥ_β` at a
non-critical preimage of `ζ₀` (`exists_preimage_noncritical`, `local_branch_disc`) is transported
to `β'` by the translation `ψ (· + (β' - β))`, since `ĥ_{β'} = ĥ_β - (β' - β)`
(`branch_translate_image`). -/
private theorem local_head_data (d : MandelDim.ParabData g₀ D) (hd : MandelDim.HornData d)
    {ζa ζb : ℂ} {δ : ℝ} (hδ : 0 < δ) (h2ρ : 2 * (δ / 4) < δ)
    (hsep : ∀ k : ℤ, δ ≤ ‖(ζa - ζb) - (k : ℂ)‖) (β : ℂ) :
    ∃ (ζ₀ : ℂ) (r : ℝ) (A : Set ℂ), (ζ₀ = ζa ∨ ζ₀ = ζb) ∧ 0 < r ∧ IsCompact A ∧ A ⊆ hd.Bu ∧
      ∀ β' : ℂ, β' ∈ Metric.ball β (r / 4) → ∀ ρ : ℝ, 0 < ρ → ρ ≤ r / 4 →
        ∃ W : ℕ → Set ℂ, (W 0 = Metric.ball ζa ρ ∨ W 0 = Metric.ball ζb ρ) ∧
          IsOpen (W 0) ∧ IsConnected (W 0) ∧ IsOpen (W 1) ∧ IsConnected (W 1) ∧
          Set.InjOn (fun w => d.E w - β') (W 1) ∧
          (fun w => d.E w - β') '' W 1 = W 0 ∧ W 1 ⊆ A ∧
          Bornology.IsBounded (W 0) ∧ Bornology.IsBounded (W 1) := by
  obtain ⟨ζ₀, hζ₀mem, hζ₀dist⟩ := Work.L62.exists_avoiding_center d hd (ρ := δ / 4) (δ := δ)
    (β := β) hδ hsep h2ρ
  have hζ₀ : ζ₀ = ζa ∨ ζ₀ = ζb := by simpa using hζ₀mem
  have hξ : ∀ k : ℤ, ζ₀ + β ≠ hd.v + (k : ℂ) := by
    intro k hk
    have h := hζ₀dist k
    rw [hk] at h
    simp at h
    linarith
  obtain ⟨ζ₁, hζ₁Bu, hζ₁E, hζ₁d⟩ := Work.L62.exists_preimage_noncritical d hd hξ
  have hFana : AnalyticAt ℂ (fun w => d.E w - β) ζ₁ :=
    ((Work.L62.differentiableOn_E_Bu d hd).analyticAt (hd.Bu_open.mem_nhds hζ₁Bu)).sub
      analyticAt_const
  have hder : deriv (fun w => d.E w - β) ζ₁ ≠ 0 := by
    rw [deriv_sub_const]; exact hζ₁d
  obtain ⟨r, hr, ψ, hψd, hψ0, hψinv, hψmap, hψinj⟩ :=
    Work.L62.local_branch_disc hFana hder hd.Bu_open hζ₁Bu
  rw [hζ₁E] at hψd hψinv hψmap hψinj
  refine ⟨ζ₀, r, ψ '' Metric.closedBall ζ₀ (r / 2), hζ₀, hr, ?_, ?_, ?_⟩
  · refine (isCompact_closedBall ζ₀ (r / 2)).image_of_continuousOn ?_
    refine hψd.continuousOn.mono ?_
    intro z hz
    rw [Metric.mem_ball]
    have := Metric.mem_closedBall.mp hz
    linarith
  · rintro z ⟨u, hu, rfl⟩
    exact hψmap (by rw [Metric.mem_ball]; have := Metric.mem_closedBall.mp hu; linarith)
  · intro β' hβ'ball ρ hρ hρr
    have hc : ‖β' - β‖ < r / 4 := by
      have h := Metric.mem_ball.mp hβ'ball
      rwa [dist_eq_norm] at h
    have hρc : ρ + ‖β' - β‖ < r / 2 := by linarith
    have hkey := Work.L62.branch_translate_image (F := fun w => d.E w - β) (ψ := ψ)
      (c₀ := ζ₀) (c := β' - β) (r := r) (ρ := ρ) (U := hd.Bu)
      hr hρ hρc hψd hψinv hψmap hψinj
    obtain ⟨hopen, hconn, himg, hinj, hcomp, hcompU, hsub, hbdd⟩ := hkey
    have hshift : (fun w => (d.E w - β) - (β' - β)) = fun w => d.E w - β' := by
      funext w; ring
    rw [hshift] at himg hinj
    let V : Set ℂ := ψ '' Metric.ball (ζ₀ + (β' - β)) ρ
    let W : ℕ → Set ℂ := fun j => match j with | 0 => Metric.ball ζ₀ ρ | (_ + 1) => V
    have hW0 : W 0 = Metric.ball ζ₀ ρ := rfl
    have hW1 : W 1 = V := rfl
    have hVopen : IsOpen V := hopen
    have hVconn : IsConnected V := hconn
    have hVimg : (fun w => d.E w - β') '' V = Metric.ball ζ₀ ρ := himg
    have hVinj : Set.InjOn (fun w => d.E w - β') V := hinj
    have hVsub : V ⊆ ψ '' Metric.closedBall ζ₀ (r / 2) := hsub
    have hVbdd : Bornology.IsBounded V := hbdd
    refine ⟨W, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hW0]
      rcases hζ₀ with h | h
      · left; rw [h]
      · right; rw [h]
    · rw [hW0]; exact Metric.isOpen_ball
    · rw [hW0]; exact (convex_ball ζ₀ ρ).isConnected ⟨ζ₀, Metric.mem_ball_self hρ⟩
    · rw [hW1]; exact hVopen
    · rw [hW1]; exact hVconn
    · rw [hW1]; exact hVinj
    · rw [hW1, hW0]; exact hVimg
    · rw [hW1]; exact hVsub
    · rw [hW0]
      exact (isCompact_closedBall ζ₀ ρ).isBounded.subset Metric.ball_subset_closedBall
    · rw [hW1]; exact hVbdd

/-- **The head chain fits in a fixed compact subset of the upper horn.**  The uniformity-in-`β`
input of `Work.L62.model_head_up` (see `Submission/Work/L62/NOTES_L62_head_up.md`): the chain
exists for each `(ρ, β)` (`middle_chain_ball` + `secChain_spec`), and the content here is that it
can be chosen inside ONE fixed compact `K ⊆ hd.Bu` with a fixed step count `J`.

Route (Shishikura, proof of Lemma 6.2, the stability step): for `AvailableUp β` the global
`T`-equivariant section `σ_β` of `ĥ_β` over the *fixed* horn `Bu` (`avail_horn_section_up`), a
continuously chosen preimage `ζ₁ β` of the centre (`exists_preimage_noncritical`, and for
continuity a selection argument / `selection_unique_compact`), the chain `W (j+1) = σ_β^[j] '' W 1 β`,
continuity of `σ_β` in `β` (parametric uniqueness of sections of a covering over the fixed simply
connected `Bu`, as in `cylinder_model`), and compactness of
`Λ = {0 ≤ Re ≤ 1, |Im| ≤ b} ∩ AvailableUp` (`isClosed_availableUp`).  The uniform bound on the
number of steps is `cylinder_model` + `uniform_escape2`. -/
theorem head_compact {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {b : ℝ} (hb : 0 < b) {ζa ζb : ℂ} (hζa : ζa ∉ d.DE)
    (hζb : ζb ∉ d.DE) (hsep : ∀ k : ℤ, ζa ≠ ζb + (k : ℂ)) :
    ∃ (ρ₀ : ℝ) (K : Set ℂ) (J : ℕ),
      0 < ρ₀ ∧ IsCompact K ∧ K ⊆ hd.Bu ∧ 0 < J ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ β : ℂ, 0 ≤ β.re → β.re ≤ 1 → |β.im| ≤ b →
        Work.L62.AvailableUp d hd β →
        ∃ W : ℕ → Set ℂ,
          (W 0 = Metric.ball ζa ρ ∨ W 0 = Metric.ball ζb ρ) ∧
          (∀ j, j ≤ J → IsOpen (W j) ∧ IsConnected (W j)) ∧
          (∀ j, j < J → Set.InjOn (fun w => d.E w - β) (W (j + 1)) ∧
            (fun w => d.E w - β) '' W (j + 1) = W j) ∧
          (∀ j, 1 ≤ j → j ≤ J → W j ⊆ K) ∧
          (∀ j, j ≤ J → Bornology.IsBounded (W j)) := by
  -- ## Route
  --
  -- The proof uses `J = 1`: only the *first* step of the chain is needed, and it is obtained as
  -- the translation of a *pointwise* inverse branch of `ĥ_β = d.E - β`, so that the
  -- uniformity-in-`β` is a compactness statement over the box (`compact_uniform_subcover`)
  -- rather than an escape argument.  Concretely (see `local_head_data`): for each `β` one of
  -- `ζa`, `ζb` has its `(δ/4)`-disc avoiding the critical values of `ĥ_β`, an inverse branch `ψ`
  -- of `ĥ_β` exists over a disc around it (`local_branch_disc`), and the elements of the chain at
  -- `β' ≈ β` are the `ψ`-images of discs translated by `β' - β` (`branch_translate_image`); all of
  -- them lie in the compact `ψ '' closedBall ζ₀ (r/2) ⊆ Bu`.  Note that *availability*
  -- (`AvailableUp β`) is not needed for a single step; it is a hypothesis here because this lemma
  -- is the uniformity input of `model_head_up`, whose longer chains do use the drift.
  classical
  -- a positive separation of `ζa` and `ζb` modulo `ℤ`
  obtain ⟨δ, hδ, hδsep⟩ := Work.L62.int_separation (x := ζa - ζb)
    (fun k hk => hsep k (by linear_combination hk))
  have h2rho : 2 * (δ / 4) < δ := by linarith
  -- the compact box of admissible `β`
  set Λ : Set ℂ := {β : ℂ | 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b} ∩
    {β : ℂ | Work.L62.AvailableUp d hd β} with hΛdef
  have hΛc : IsCompact Λ := (isCompact_box b).inter_right (Work.L62.isClosed_availableUp d hd)
  -- pointwise local data, as functions of `β`
  have key : ∀ β : ℂ, ∃ (r : ℝ) (A : Set ℂ), (0 < r ∧ IsCompact A ∧ A ⊆ hd.Bu) ∧
      ∀ β' : ℂ, β' ∈ Metric.ball β (r / 4) → ∀ ρ : ℝ, 0 < ρ → ρ ≤ r / 4 →
        ∃ W : ℕ → Set ℂ, (W 0 = Metric.ball ζa ρ ∨ W 0 = Metric.ball ζb ρ) ∧
          IsOpen (W 0) ∧ IsConnected (W 0) ∧ IsOpen (W 1) ∧ IsConnected (W 1) ∧
          Set.InjOn (fun w => d.E w - β') (W 1) ∧
          (fun w => d.E w - β') '' W 1 = W 0 ∧ W 1 ⊆ A ∧
          Bornology.IsBounded (W 0) ∧ Bornology.IsBounded (W 1) := by
    intro β
    obtain ⟨ζ₀, r, A, hζ₀, hr, hAc, hAB, hprop⟩ := local_head_data d hd hδ h2rho hδsep β
    exact ⟨r, A, ⟨hr, hAc, hAB⟩, hprop⟩
  choose r A hdata hprop using key
  -- a uniform radius and a uniform compact set
  obtain ⟨ρ₀, K, hρ₀, hKc, hKBu, hcover⟩ := compact_uniform_subcover hΛc
    (fun β _ => (hdata β).1) (fun β _ => (hdata β).2.1) (fun β _ => (hdata β).2.2)
  refine ⟨ρ₀, K, 1, hρ₀, hKc, hKBu, by norm_num, ?_⟩
  intro ρ hρ hρρ₀ β hβ0 hβ1 hβim hav
  have hβΛ : β ∈ Λ := ⟨⟨hβ0, hβ1, hβim⟩, hav⟩
  obtain ⟨βi, hβiΛ, hβiball, hρ₀le, hAiK⟩ := hcover β hβΛ
  obtain ⟨W, hW0, hW0o, hW0c, hW1o, hW1c, hinj, himg, hW1A, hW0b, hW1b⟩ :=
    hprop βi β hβiball ρ hρ (le_trans hρρ₀ hρ₀le)
  refine ⟨W, hW0, ?_, ?_, ?_, ?_⟩
  · intro j hj
    interval_cases j
    · exact ⟨hW0o, hW0c⟩
    · exact ⟨hW1o, hW1c⟩
  · intro j hj
    interval_cases j
    · exact ⟨hinj, himg⟩
  · intro j hj1 hj2
    interval_cases j
    · exact fun w hw => hAiK (hW1A hw)
  · intro j hj
    interval_cases j
    · exact hW0b
    · exact hW1b

end Work.L62

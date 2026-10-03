import Mathlib
import Submission.Work.L62.l62c_end
import Submission.Work.L62.avail_up
import Submission.Work.L62.local_ratio_contraction
import Submission.Work.L62.uniform_escape2
import Submission.Work.L62.head_anchor

namespace Work.L62

/-!
# `Work.L62.head_escape_J` — uniform escape to the thin ball `|ζ| < e^{-2π y₁}`

Shishikura, Lemma 6.2 (the tail of the head chain): for a holomorphic family `H β` of self-maps of
the cylinder neighbourhood `Ω = {0} ∪ π(B^u)` with `H β 0 = 0`, `(H β)'(0) = π β = e^{2πiβ}`,
which is jointly continuous on `Λ × Ω` and whose orbits escape to `0` on compacts, there is a
*single* `J` such that

  `‖((H β)^[J-1]) (π z)‖ < e^{-2π y₁}`  for every admissible `β` and every `z ∈ K₀ ⊆ B^u`.

The available `β` (those for which `B^u` misses the critical class of `Ê - β`) in the box
`{0 ≤ Re ≤ 1, |Im| ≤ b}` form a *compact* set `Λ` (`isClosed_availableUp` + `isCompact_betaBox`),
and on it the multiplier is bounded away from `1` on both sides:

* `avail_up` gives `0 < Im β`, and `exists_dist_to_line` upgrades this to `δ₀ ≤ Im β` with
  `δ₀ > 0` (the closed, `1`-periodic set of available `β` avoids the line `Im = 0`); hence
  `‖π β‖ = e^{-2π Im β} ≤ e^{-2π δ₀} < 1`, while `|Im β| ≤ b` gives the lower bound
  `e^{-2π b} ≤ ‖π β‖`.

`local_ratio_contraction` then produces a *`β`-uniform* contraction radius `ρ` and factor `μ < 1`
(Cauchy's estimate on the disk of radius `R` around `0` contained in `Ω`, with the family bound
coming from compactness of `Λ`), and `uniform_escape2` converts the per-`β` escape hypothesis
(`Hesc`) into a uniform time `J₀` for the compact set `π '' K₀`; the target ball has radius
`eps = e^{-2π y₁}`, and `J = J₀ + 1`.
-/

theorem head_escape_J {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {b : ℝ} (hb : 0 < b) {y₁ : ℝ}
    (H : ℂ → ℂ → ℂ)
    (Hdiff : ∀ β : ℂ, Work.L62.AvailableUp d hd β →
      DifferentiableOn ℂ (H β) (Work.L62.upOmega d hd))
    (Hmem : ∀ β : ℂ, Work.L62.AvailableUp d hd β →
      Set.MapsTo (H β) (Work.L62.upOmega d hd) (Work.L62.upOmega d hd))
    (H0 : ∀ β : ℂ, Work.L62.AvailableUp d hd β → H β 0 = 0)
    (Hder : ∀ β : ℂ, Work.L62.AvailableUp d hd β →
      deriv (H β) 0 = MandelDim.piExp β)
    (Hesc : ∀ β : ℂ, Work.L62.AvailableUp d hd β → ∀ δ : ℝ, 0 < δ → ∀ K : Set ℂ,
      K ⊆ Work.L62.upOmega d hd → IsCompact K →
        ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ K, ((H β)^[n]) z ∈ Metric.ball 0 δ)
    (Hcont : ContinuousOn (fun p : ℂ × ℂ => H p.1 p.2)
      (({β : ℂ | 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b} ∩
        {β : ℂ | Work.L62.AvailableUp d hd β}) ×ˢ Work.L62.upOmega d hd))
    {K₀ : Set ℂ} (hK₀c : IsCompact K₀) (hK₀ : K₀ ⊆ hd.Bu) :
    ∃ J : ℕ, 0 < J ∧ ∀ β : ℂ, 0 ≤ β.re → β.re ≤ 1 → |β.im| ≤ b →
      Work.L62.AvailableUp d hd β → ∀ z ∈ K₀,
        ‖((H β)^[J - 1]) (MandelDim.piExp z)‖ < Real.exp (-(2 * Real.pi) * y₁) := by
  classical
  -- ## (A) The available set is `1`-periodic, closed, and avoids the real axis.
  -- `avail_up` gives `0 < Im β` on it, and the elementary compactness lemma
  -- `exists_dist_to_line` upgrades this to a uniform bound away from `0`.
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := Work.L62.exists_dist_to_line
    (S := {β : ℂ | Work.L62.AvailableUp d hd β}) (t := 0)
    (Work.L62.isClosed_availableUp d hd) (Work.L62.availableUp_add_one d hd)
    (fun β hβ => ne_of_gt (Work.L62.avail_up d hd hβ))
  -- ## (B) The admissible parameter set is compact.
  set Λ : Set ℂ := {β : ℂ | 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b} ∩
    {β : ℂ | Work.L62.AvailableUp d hd β} with hΛdef
  have hΛc : IsCompact Λ := (isCompact_betaBox b).inter_right (Work.L62.isClosed_availableUp d hd)
  have hcontΛ : ContinuousOn (fun p : ℂ × ℂ => H p.1 p.2) (Λ ×ˢ Work.L62.upOmega d hd) :=
    Hcont.mono (Set.prod_mono_left fun β hβ => hβ)
  -- ## (C) Uniform two-sided bounds for the multiplier `π β`.
  set lam0 : ℝ := Real.exp (-(2 * Real.pi) * b) with hlam0def
  set lam1 : ℝ := Real.exp (-(2 * Real.pi) * δ₀) with hlam1def
  have hlam0pos : 0 < lam0 := Real.exp_pos _
  have hlam1lt : lam1 < 1 := by
    rw [hlam1def]
    exact Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, hδ₀pos])
  have hlam : ∀ β ∈ Λ, lam0 ≤ ‖deriv (H β) 0‖ ∧ ‖deriv (H β) 0‖ ≤ lam1 := by
    intro β hβ
    have hav : Work.L62.AvailableUp d hd β := hβ.2
    have himabs : |β.im| ≤ b := hβ.1.2.2
    have himlo : δ₀ ≤ β.im := by
      have h := hδ₀ β hav
      rw [sub_zero, abs_of_pos (Work.L62.avail_up d hd hav)] at h
      exact h
    rw [Hder β hav, Work.L62.norm_piExp]
    refine ⟨?_, ?_⟩
    · rw [hlam0def]
      exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, (abs_le.mp himabs).2])
    · rw [hlam1def]
      exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, himlo])
  -- ## (D) A uniform contraction radius and factor for the family.
  obtain ⟨ρ, hρpos, hρΩ, μ, hμ0, hμ1, hcontr, -⟩ :=
    local_ratio_contraction (Ω := Work.L62.upOmega d hd) (Λ := Λ) (H := H)
      (lam0 := lam0) (lam1 := lam1) (Work.L62.isOpen_upOmega d hd)
      (Set.mem_insert_iff.mpr (Or.inl rfl)) hΛc hlam0pos hlam1lt hlam
      (fun β hβ => Hdiff β hβ.2) (fun β hβ => H0 β hβ.2) hcontΛ
  -- ## (E) Uniform escape to the ball of radius `e^{-2π y₁}`.
  have hKc : IsCompact (MandelDim.piExp '' K₀) := hK₀c.image Work.L62.continuous_piExp
  have hKsub : MandelDim.piExp '' K₀ ⊆ Work.L62.upOmega d hd := by
    rintro ζ ⟨z, hz, rfl⟩
    exact Set.mem_insert_iff.mpr (Or.inr ⟨z, hK₀ hz, rfl⟩)
  obtain ⟨J₀, hJ₀⟩ := uniform_escape2 (Ω := Work.L62.upOmega d hd) (Λ := Λ)
    (K := MandelDim.piExp '' K₀) (H := H) (r := ρ) (μ := μ)
    (eps := Real.exp (-(2 * Real.pi) * y₁))
    (Work.L62.isOpen_upOmega d hd) hΛc hKc hKsub hρpos hρΩ hμ0 hμ1
    (Real.exp_pos _) (fun β hβ => Hmem β hβ.2)
    (fun β hβ w hw => hcontr β hβ w (le_of_lt (by
      simpa [Metric.mem_ball, dist_eq_norm] using hw))) hcontΛ
    (fun β hβ z hz => by
      obtain ⟨N, hN⟩ := Hesc β hβ.2 ρ hρpos (MandelDim.piExp '' K₀) hKsub hKc
      exact ⟨N, hN N le_rfl z hz⟩)
  refine ⟨J₀ + 1, Nat.succ_pos J₀, ?_⟩
  intro β h0 h1 h2 hav z hz
  have hβΛ : β ∈ Λ := ⟨⟨h0, h1, h2⟩, hav⟩
  have h := hJ₀ β hβΛ J₀ le_rfl (MandelDim.piExp z) ⟨z, hz, rfl⟩
  rw [Metric.mem_ball, dist_zero_right] at h
  simpa using h

end Work.L62

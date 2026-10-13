import Mathlib
import Submission.Work.WilkiesH.Mfd.Defs
import Submission.Work.WilkiesH.Basic
import Submission.Work.WilkiesI.MemAlg

namespace Work.WilkiesH.Mfd

open WilkiesConjecture

/-- `S` semialgebraic, `μ ≥ 1`, `S` a `μ`-dimensional topological manifold at `x`
(`Work.WilkiesH.IsGraphAt μ S x`) and locally contained in `X` at `x`
(`Work.WilkiesH.LocallyIn S X x`) imply `x ∈ X.alg`.

Witness: with the local data `S ∩ boxAround x δ = ψ '' Ω`, the graph `Y := ψ '' cbox(t₀,ρ)`
over a small coordinate box `cbox(t₀,ρ) ⊆ Ω` around `t₀` (where `x = ψ t₀`) is semialgebraic
(it equals `S ∩ boxAround x δ ∩ π_e⁻¹ cbox(t₀,ρ)`), connected (continuous image of a
connected set), infinite (`ψ` is injective and `μ ≥ 1`, so `cbox(t₀,ρ)` is infinite) and
contained in `X` (local fullness); conclude with `Work.WilkiesH.subset_alg_of_semialg` or
`Work.WilkiesH.mem_alg_iff`.

Note: `Submission.Work.WilkiesI.MemAlg` (`Work.WilkiesI.mem_alg_of_local_graph`) already
proves the same statement with the graph condition written out explicitly instead of through
`IsGraphAt`; deriving from it is the cheapest route, but a direct proof is fine too. -/
theorem mem_alg_of_isGraphAt {n μ : ℕ} (hμ : 1 ≤ μ) {S X : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hS : WilkiesConjecture.IsSemialgebraic S) (hg : Work.WilkiesH.IsGraphAt μ S x)
    (hfull : Work.WilkiesH.LocallyIn S X x) : x ∈ X.alg := by
  -- Unpack the local manifold chart at `x`.
  obtain ⟨e, Ω, ψ, δ, hδ, hΩ, hcont, hsec, ⟨t₀, ht₀Ω, hψt₀⟩, hgraph⟩ := hg
  -- Unpack local fullness.
  obtain ⟨δ', hδ', hfull'⟩ := hfull
  have hμ0 : 0 < μ := by omega
  -- A box radius small enough for both the graph condition and fullness.
  have hδ''pos : 0 < min δ δ' := lt_min hδ hδ'
  have hδ''δ : min δ δ' ≤ δ := min_le_left δ δ'
  have hδ''δ' : min δ δ' ≤ δ' := min_le_right δ δ'
  -- The `e`-coordinates of `t₀` are the `e`-coordinates of `x`.
  have ht₀e : ∀ j : Fin μ, t₀ j = x (e j) := by
    intro j
    have h := congr_fun (hsec t₀ ht₀Ω) j
    rw [hψt₀] at h
    exact h.symm
  -- `ψ` is continuous at `t₀` (the domain `Ω` is open).
  have hcontAt : ContinuousAt ψ t₀ :=
    (hcont.continuousWithinAt ht₀Ω).continuousAt (hΩ.mem_nhds ht₀Ω)
  -- A radius inside `Ω`, and a radius on which `ψ` stays in the box of radius `min δ δ'`
  -- around `x`.
  obtain ⟨ε₁, hε₁, hε₁Ω⟩ := Metric.isOpen_iff.mp hΩ t₀ ht₀Ω
  obtain ⟨ε₂, hε₂, hε₂ψ⟩ := Metric.continuousAt_iff.mp hcontAt (min δ δ') hδ''pos
  have hρpos : 0 < min ε₁ ε₂ := lt_min hε₁ hε₂
  have hρε₁ : min ε₁ ε₂ ≤ ε₁ := min_le_left _ _
  have hρε₂ : min ε₁ ε₂ ≤ ε₂ := min_le_right _ _
  have hUsub : Metric.ball t₀ (min ε₁ ε₂) ⊆ Ω := fun t ht =>
    hε₁Ω (Metric.ball_subset_ball hρε₁ ht)
  -- The enlarged `e`-coordinate box `B` and the open piece `U` of the chart.
  have hB : IsSemialgebraic (boxAround x (min δ δ') ∩
      {y : Fin n → ℝ | ∀ j, |y (e j) - x (e j)| < min ε₁ ε₂}) :=
    Work.WilkiesI.isSemialgebraic_inter (Work.WilkiesI.isSemialgebraic_box x (min δ δ'))
      (Work.WilkiesI.isSemialgebraic_eBox e x (min ε₁ ε₂))
  -- The key set identity: on `B`, `S` is the image of the ball of radius `min ε₁ ε₂`.
  have hgraph' : S ∩ (boxAround x (min δ δ') ∩
      {y : Fin n → ℝ | ∀ j, |y (e j) - x (e j)| < min ε₁ ε₂})
      = ψ '' Metric.ball t₀ (min ε₁ ε₂) := by
    ext y
    constructor
    · rintro ⟨hyS, hybox, hye⟩
      have hboxδ : y ∈ boxAround x δ := fun i => lt_of_lt_of_le (hybox i) hδ''δ
      obtain ⟨t, htΩ, hty⟩ := (hgraph y hboxδ).mp hyS
      refine ⟨t, ?_, hty⟩
      rw [Metric.mem_ball, dist_pi_lt_iff hρpos]
      intro j
      rw [Real.dist_eq]
      have hyj : y (e j) = t j := by
        rw [← hty]
        exact congr_fun (hsec t htΩ) j
      rw [← hyj, ht₀e j]
      exact hye j
    · rintro ⟨t, ht, rfl⟩
      have htΩ : t ∈ Ω := hUsub ht
      have hdist : dist t t₀ < min ε₁ ε₂ := Metric.mem_ball.mp ht
      have hmem : ψ t ∈ boxAround x (min δ δ') := by
        intro i
        have hd : dist (ψ t) (ψ t₀) < min δ δ' := hε₂ψ (lt_of_lt_of_le hdist hρε₂)
        rw [hψt₀] at hd
        have hdi := (dist_pi_lt_iff hδ''pos).mp hd i
        rwa [Real.dist_eq] at hdi
      refine ⟨?_, hmem, fun j => ?_⟩
      · rw [hgraph (ψ t) (fun i => lt_of_lt_of_le (hmem i) hδ''δ)]
        exact ⟨t, htΩ, rfl⟩
      · have hje : ψ t (e j) = t j := congr_fun (hsec t htΩ) j
        have hdj := dist_le_pi_dist t t₀ j
        rw [Real.dist_eq] at hdj
        rw [hje, (ht₀e j).symm]
        exact lt_of_le_of_lt hdj hdist
  -- `x` lies in the piece `B` and in `S`.
  have hpB : x ∈ boxAround x (min δ δ') ∩
      {y : Fin n → ℝ | ∀ j, |y (e j) - x (e j)| < min ε₁ ε₂} := by
    refine ⟨fun i => ?_, fun j => ?_⟩
    · rw [sub_self, abs_zero]; exact hδ''pos
    · rw [sub_self, abs_zero]; exact hρpos
  have hpV : x ∈ S := by
    rw [hgraph x (fun i => by rw [sub_self, abs_zero]; exact hδ)]
    exact ⟨t₀, ht₀Ω, hψt₀⟩
  -- The piece is contained in `X` by local fullness.
  have hX : S ∩ (boxAround x (min δ δ') ∩
      {y : Fin n → ℝ | ∀ j, |y (e j) - x (e j)| < min ε₁ ε₂}) ⊆ X := by
    rintro y ⟨hyS, hybox, -⟩
    exact hfull' y (fun i => lt_of_lt_of_le (hybox i) hδ''δ') hyS
  exact Work.WilkiesI.mem_alg_of_local_graph hμ0 X S
    (boxAround x (min δ δ') ∩
      {y : Fin n → ℝ | ∀ j, |y (e j) - x (e j)| < min ε₁ ε₂})
    hS hB x hpB e (Metric.ball t₀ (min ε₁ ε₂)) Metric.isOpen_ball ψ
    (hcont.mono hUsub) (fun t ht => hsec t (hUsub ht)) hgraph' hpV hX

end Work.WilkiesH.Mfd

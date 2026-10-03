import Mathlib
import Submission.Work.Pert.RBlock
import Submission.Work.Pert.invOn_sub_id_tendsto_upper

/-!
# PERT · `Work.Pert.retOf_sub_id_tendsto_upper`

Shishikura (4.2.2) at the **upper** end: the lifted return map
`retOf Φ (Qm ξ α) α w = Φ (Tt α (invOn Φ (Qm ξ α) w))` satisfies

> `retOf Φ Q α w - w + 1/α → 0` as `im w → +∞`.

The point of the statement is the *cancellation* of the asymptotic translation constant `c`
of `Φ`: write `ζ = invOn Φ Q w`, so `Φ ζ = w` and `ζ - 1/α = Tt α ζ`.  Since `hproper` propagates
"`w` high ⇒ `ζ` high" (the contrapositive of the height bound), both `ζ` and `ζ - 1/α` run to the
upper end with `w`, so `hEnd` applies at both, and

`Φ (ζ - 1/α) - w + 1/α = [Φ (ζ - 1/α) - (ζ - 1/α) - c] - [Φ ζ - ζ - c]`,

each bracket tending to `0` — the constant `c` and the translation `-1/α` cancel exactly.
-/

namespace Work.Pert

open MandelDim Filter Metric Set

noncomputable section

theorem retOf_sub_id_tendsto_upper {Φ : ℂ → ℂ} {Ξ : ℝ} {α c : ℂ}
    (hinj : Set.InjOn Φ (Work.Pert.Qm Ξ α))
    (hcover : ∀ᶠ w in MandelDim.upperEnd, w ∈ Φ '' (Work.Pert.Qm Ξ α))
    (hproper : ∀ R : ℝ, ∃ N : ℝ, ∀ ζ ∈ Work.Pert.Qm Ξ α, ζ.im ≤ R → (Φ ζ).im ≤ N)
    (hEnd : Filter.Tendsto (fun z => Φ z - z) MandelDim.upperEnd (nhds c)) :
    Filter.Tendsto (fun w => Work.Pert.retOf Φ (Work.Pert.Qm Ξ α) α w - w + 1 / α)
      MandelDim.upperEnd (nhds 0) := by
  -- `w` is eventually a genuine image point of the gate, and `Φ z - z → c`.
  obtain ⟨T₁, hT₁⟩ := eventually_upperEnd_iff.mp hcover
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [eventually_upperEnd_iff]
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ z : ℂ, R < z.im → dist (Φ z - z) c < ε / 2 :=
    eventually_upperEnd_iff.mp ((Metric.tendsto_nhds.mp hEnd) (ε / 2) (by linarith))
  -- Any gate point `ζ` with `(Φ ζ).im` beyond `N` has imaginary part beyond `R + Im (1/α)`.
  obtain ⟨N, hN⟩ := hproper (R + |(1 / α).im|)
  refine ⟨max T₁ N, fun w hw => ?_⟩
  have hwT : T₁ < w.im := lt_of_le_of_lt (le_max_left T₁ N) hw
  have hwN : N < w.im := lt_of_le_of_lt (le_max_right T₁ N) hw
  obtain ⟨ζ₀, hζ₀Q, hΦζ₀⟩ := hT₁ w hwT
  have hex : ∃ z ∈ Work.Pert.Qm Ξ α, Φ z = w := ⟨ζ₀, hζ₀Q, hΦζ₀⟩
  set z : ℂ := Work.Pert.invOn Φ (Work.Pert.Qm Ξ α) w with hz
  have hzQ : z ∈ Work.Pert.Qm Ξ α := Work.Pert.invOn_mem hex
  have hzspec : Φ z = w := Work.Pert.invOn_spec hex
  -- `ζ` is high: otherwise `hproper` would bound `w = Φ ζ` from above.
  have hzim : R + |(1 / α).im| < z.im := by
    by_contra hcon
    have hle : z.im ≤ R + |(1 / α).im| := not_lt.mp hcon
    have := hN z hzQ hle
    rw [hzspec] at this
    linarith
  -- the return map is the conjugate of the deck translation at `z`
  have hret : Work.Pert.retOf Φ (Work.Pert.Qm Ξ α) α w = Φ (z - 1 / α) := by
    rw [Work.Pert.retOf_eq hinj hex hzQ hzspec, Work.Pert.Tt]
  -- both `z` and `z - 1/α` are beyond the threshold `R`
  have hz1 : R < (z - 1 / α).im := by
    rw [Complex.sub_im]
    linarith [le_abs_self ((1 / α).im)]
  have h1 : ‖Φ (z - 1 / α) - (z - 1 / α) - c‖ < ε / 2 := by
    simpa only [dist_eq_norm] using hR (z - 1 / α) hz1
  have h2 : ‖Φ z - z - c‖ < ε / 2 := by
    simpa only [dist_eq_norm] using hR z (by linarith [abs_nonneg ((1 / α).im)])
  rw [hret, dist_eq_norm, sub_zero]
  have halg : Φ (z - 1 / α) - w + 1 / α
      = (Φ (z - 1 / α) - (z - 1 / α) - c) - (Φ z - z - c) := by
    rw [← hzspec]; ring
  rw [halg]
  calc ‖(Φ (z - 1 / α) - (z - 1 / α) - c) - (Φ z - z - c)‖
      ≤ ‖Φ (z - 1 / α) - (z - 1 / α) - c‖ + ‖Φ z - z - c‖ := norm_sub_le _ _
    _ < ε := by linarith

end

end Work.Pert

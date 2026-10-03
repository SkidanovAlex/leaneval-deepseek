import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.Setup

namespace Work.Repel

/-- **Existence of the Lemma 6.2 chain data at level 1.**  This is a direct reading of
`L62Statement` at the level-1 base germ `ǧ₀ = g0germ S.d₀` with its horn data `S.d₁`,
the two starting points `S.ζa, S.ζb` (which lie outside `S.d₁.DE` and are not congruent
modulo `ℤ`), and the radius `ρ = ρ₀ / 2`, which is admissible for the `ρ₀` produced by
Lemma 6.2. -/
theorem chain_setup_exists (hL62 : MandelDim.L62Statement) (S : Work.Repel.Setup) (b : ℝ)
    (hb : 0 < b) : Nonempty (Work.Repel.ChainSetup S b) := by
  obtain ⟨ρ₀, hρ₀pos, hρ₀⟩ :=
    hL62 (g0germ S.d₀) (Dg0germ S.d₀ S.hd₀) (inF0_g0germ S.d₀ S.hd₀) S.d₁ S.hd₁ b hb
      S.ζa S.ζb S.hζa S.hζb S.hdisj
  obtain ⟨K, hKc, hKsub, y₁, δ, C₀, C₁, C₁', hy₁, hδ, hC₁, hchain⟩ :=
    hρ₀ (ρ₀ / 2) (by linarith) (by linarith)
  refine ⟨{ ρ := ρ₀ / 2, hρ := by linarith, K₂ := K, hK₂c := hKc, hK₂sub := hKsub,
            y₁ := y₁, hy₁ := hy₁, δ := δ, hδ := hδ, C₀ := C₀, C₁ := C₁, C₁' := C₁',
            hC₁ := hC₁, chain := ?_ }⟩
  intro R DR hDR hT hdiff hsub hclose β hβre₀ hβre₁ hβim
  obtain ⟨W, s, hs, hW0, hopen, hch, hdisj, hmarch, hbnd, hcl, hder⟩ :=
    hchain R DR hDR hT hdiff hsub hclose β hβre₀ hβre₁ hβim
  exact ⟨W, s, ⟨hs, hW0, hopen, hch, hdisj, hmarch, hbnd, hcl, hder⟩⟩

end Work.Repel

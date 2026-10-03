import Mathlib
import Submission.Work.Pert.RBlock
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.Gates
import Submission.Work.Pert.AsmDefs
import Submission.Work.Pert.RBlock3

namespace Work.Pert.pert2v2

/-- **The low piece at a gate point of the crux, along a walk whose endpoint is *given* as the
`τ`-preimage.**  If `ς` is a *waist* point of the gate `Qm Ξ α ∩ Qp Ξ α` whose `F`-walk stays in
`Qp Ξ α`, and if the low chart's landing time `m` is such that the chosen `τ`-preimage of
`f^[m] (τ ς)` inside `Qp'` is exactly `F^[m] ς` (the hypothesis `hcoinc`, which the caller supplies
from the shadowing/coincidence estimate `(SHADOW)`), then the low piece of the return map at the
level-`0` image point `ΨE ς` reproduces the gate value `retOf ΨE (Qm Ξ α) α (ΨE ς)`.

The whole computation is:
`coordP … (ΨE ς) = τ ς` (level `0`, `hE.injOn`), hence `f^[m] (φ w) = f^[m] (τ ς)`, so
`Rlow w = Ψp (F^[m] ς) - m + d = Ψp ς + d` (Abel along the walk), and `Ψp ς = ΨE (Tt α ς) - d`
(Shishikura (A.4.2), the hypothesis `hrel`), while
`retOf ΨE (Qm Ξ α) α (ΨE ς) = ΨE (Tt α ς)` at the level-`0` point. -/
theorem Rlow_eq_retOf_crux_walk {f F τ ΨE Ψp : ℂ → ℂ} {Df Qp' : Set ℂ} {Ξ : ℝ} {α d : ℂ}
    {m : ℕ} {ς : ℂ}
    (hE : MandelDim.IsFatouCoordOn F ΨE (Work.Pert.Qm Ξ α))
    (hrel : ∀ z ∈ Work.Pert.Qp Ξ α, Ψp z = ΨE (Work.Pert.Tt α z) - d)
    (hτF : ∀ z ∈ Work.Pert.Qp Ξ α, τ (F z) = f (τ z))
    (hAbel : ∀ z ∈ Work.Pert.Qp Ξ α, F z ∈ Work.Pert.Qp Ξ α → Ψp (F z) = Ψp z + 1)
    (hinjτ : Set.InjOn τ Qp')
    (hQp'sub : Qp' ⊆ Work.Pert.Qp Ξ α)
    (hς : ς ∈ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α)
    (hwalk : ∀ j : ℕ, j ≤ m → F^[j] ς ∈ Work.Pert.Qp Ξ α)
    (hcoinc : Work.Pert.invOn τ Qp' (f^[m] (τ ς)) = F^[m] ς) :
    Work.Pert.Rlow f Qp' τ Ψp
        (Work.Pert.coordP f Df τ ΨE (Work.Pert.Qm Ξ α)) m 0 d (ΨE ς)
      = Work.Pert.retOf ΨE (Work.Pert.Qm Ξ α) α (ΨE ς) := by
  -- `hE` gives injectivity of the gate coordinate `ΨE` on `Qm Ξ α`
  have hinjE : Set.InjOn ΨE (Work.Pert.Qm Ξ α) := hE.2.1
  have hςQ : ς ∈ Work.Pert.Qm Ξ α := hς.1
  have hςQp : ς ∈ Work.Pert.Qp Ξ α := hς.2
  have himg : ΨE ς ∈ ΨE '' Work.Pert.Qm Ξ α := ⟨ς, hςQ, rfl⟩
  -- the chosen preimage of the image point is `ς` itself
  have hinvE : Work.Pert.invOn ΨE (Work.Pert.Qm Ξ α) (ΨE ς) = ς :=
    Work.Pert.invOn_eq hinjE himg hςQ rfl
  -- `φ_f` at a level-`0` point of the gate: `coordP … (ΨE ς) = τ ς`
  have hφ : Work.Pert.coordP f Df τ ΨE (Work.Pert.Qm Ξ α) (ΨE ς) = τ ς := by
    rw [Work.Pert.coordP_eq_tauC_of_mem_image hinjE himg, hinvE]
  -- the landing point of the low chart is the walk endpoint (the `hcoinc` input)
  have hinv : Work.Pert.invOn τ Qp'
      (f^[m] (Work.Pert.coordP f Df τ ΨE (Work.Pert.Qm Ξ α) (ΨE ς))) = F^[m] ς := by
    rw [hφ]
    exact hcoinc
  -- the iterated Abel equation for `Ψp` along the walk of `ς`
  have habel : Ψp (F^[m] ς) = Ψp ς + (m : ℂ) := Work.Pert.abel_iter hwalk hAbel
  -- the gate value at the level-`0` point is `ΨE (Tt α ς)`
  have hret : Work.Pert.retOf ΨE (Work.Pert.Qm Ξ α) α (ΨE ς) = ΨE (Work.Pert.Tt α ς) :=
    Work.Pert.retOf_eq hinjE himg hςQ rfl
  -- (A.4.2) at the gate point `ς ∈ Qp Ξ α`
  have hrel' : Ψp ς = ΨE (Work.Pert.Tt α ς) - d := hrel ς hςQp
  simp only [Work.Pert.Rlow]
  rw [hinv, habel, hret, hrel']
  push_cast
  ring

end Work.Pert.pert2v2

import Mathlib
import Submission.Lib.Unif2.Work.Kernel.GreenCover
import Submission.Lib.Unif2.Work.Drive.energyGreenRung
import Submission.Lib.Unif2.Work.Drive.greenEnergyPairing

/-!
# Relabelling the two distinguished charts of a `Work.Kernel.GreenCover`

The certificate machinery of the energy route (`Work.Kernel.pairing_pole_smooth`,
`Work.Kernel.pairing_pole_kernel_general`) computes the pairing with a test function against the
Green function *of the pole carried by the chart `E.ia`*.  Applying the pole identity at the *other*
pole (`E.ib`) for the *same* pairing therefore needs either a ~600-line generalisation of that proof
or the observation of this file: the two distinguished charts can simply be **relabelled**, i.e.
`E.swap` is a cover of `(Ω, K, b, a)` with exactly the same chart data.

Every field of the structure is either index-independent (`y`, `s`, `σ`, `ρ`, `ψ`, `β` and their
positivity/support/partition/differentiability fields) or comes in the two swapped versions
(`ia ↔ ib`, `ha_mem ↔ hb_mem`, `ha_nmem ↔ hb_nmem`), so `E.swap` is built by a direct structure
literal — Lean checks every field is the expected one.  Consequently `E.swap.y = E.y`, `E.swap.ρ =
E.ρ`, … **definitionally**, and the pairing of the swapped cover is *the same sum*
(`Work.Kernel.pairing_swap_eq`, proved by `rfl`).  Hence

* `Work.Kernel.pairing_pole_smooth E.swap … gB Ψ = 2π Ψ b` is the pole identity at `b` for the very
  same pairing `Work.Drive.pairing E.y E.ρ E.σ E.ψ`;
* no generalisation of the pole-identity proof is needed for the second pole.
-/

open MeasureTheory Set Filter
open scoped Manifold Topology

noncomputable section

namespace Work.Kernel

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **Relabelling the two distinguished charts of a `GreenCover`.**  Swapping `ia` with `ib` and the
two poles `a` with `b` turns a cover of `(Ω, K, a, b)` into a cover of `(Ω, K, b, a)` with exactly
the same charts, radii, weights and bumps. -/
def GreenCover.swap {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X}
    (E : GreenCover ι Ω K a b) : GreenCover ι Ω K b a where
  y := E.y
  s := E.s
  σ := E.σ
  ρ := E.ρ
  ψ := E.ψ
  β := E.β
  ia := E.ib
  ib := E.ia
  hspos := E.hspos
  hsσ := E.hsσ
  hσρ := E.hσρ
  htgt := E.htgt
  hballΩ := E.hballΩ
  hψnonneg := E.hψnonneg
  hψsupp := E.hψsupp
  hsum := E.hsum
  hψdiff := E.hψdiff
  ha_mem := E.hb_mem
  ha_nmem := E.hb_nmem
  hb_mem := E.ha_mem
  hb_nmem := E.ha_nmem
  hβone := E.hβone
  hβsupp := E.hβsupp
  hβdiff := E.hβdiff

@[simp] theorem GreenCover.swap_y {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X}
    (E : GreenCover ι Ω K a b) : E.swap.y = E.y := rfl

@[simp] theorem GreenCover.swap_s {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X}
    (E : GreenCover ι Ω K a b) : E.swap.s = E.s := rfl

@[simp] theorem GreenCover.swap_σ {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X}
    (E : GreenCover ι Ω K a b) : E.swap.σ = E.σ := rfl

@[simp] theorem GreenCover.swap_ρ {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X}
    (E : GreenCover ι Ω K a b) : E.swap.ρ = E.ρ := rfl

@[simp] theorem GreenCover.swap_ψ {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X}
    (E : GreenCover ι Ω K a b) : E.swap.ψ = E.ψ := rfl

@[simp] theorem GreenCover.swap_β {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X}
    (E : GreenCover ι Ω K a b) : E.swap.β = E.β := rfl

@[simp] theorem GreenCover.swap_ia {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X}
    (E : GreenCover ι Ω K a b) : E.swap.ia = E.ib := rfl

@[simp] theorem GreenCover.swap_ib {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X}
    (E : GreenCover ι Ω K a b) : E.swap.ib = E.ia := rfl

/-- **The pairing of the swapped cover is the same pairing.**  This is what makes the pole identity
at `b` (`Work.Kernel.pairing_pole_smooth E.swap …`) a statement about the *same* pairing
`Work.Drive.pairing E.y E.ρ E.σ E.ψ` as the pole identity at `a`. -/
theorem pairing_swap_eq {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X}
    (E : GreenCover ι Ω K a b) (f χ : X → ℝ) :
    Work.Drive.pairing E.swap.y E.swap.ρ E.swap.σ E.swap.ψ f χ
      = Work.Drive.pairing E.y E.ρ E.σ E.ψ f χ := rfl

/-- The pole chart of the swapped cover is the chart at the second pole. -/
theorem swap_y_ia {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X}
    (E : GreenCover ι Ω K a b) : E.swap.y E.swap.ia = E.y E.ib := rfl

end Work.Kernel

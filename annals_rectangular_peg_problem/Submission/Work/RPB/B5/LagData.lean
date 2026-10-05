import Mathlib
import Submission.Work.RPV.Defs
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.Defs

/-!
# B5: the data of the assembled Lagrangian family (interface)

`Work.RPB.B5.LagData` packages everything the assembly of `Work.RPB.B5.exists_lagFamily` needs
about the pieces `W` (the `ρ = r²`-chart of the chord annulus), `(Γc, Ac)` (the collar) and
`rho` (the monotone chord reparametrisation of the middle region).  All the *field* lemmas of
`Work.RPV.LagFamily` are stated against this structure, so that they can be delegated in
parallel; the structure itself is instantiated in `exists_lagFamily.lean` from the sibling
lemmas (`chart_C12_level_inverse`, `collar_exists_noL`, `exists_rho_per_kappa`, ...).

Conventions (see `Submission/Work/RPB/B5/Defs.lean`):

* `sig x = x²/2 - 1`; the collar sits at `x ≤ -√2` (level `σ = sig x ≥ 0`), the chord chart at
  `-√2 ≤ x ≤ 0` (radius `r = √(rho τ x t)`, `r = 0` at `x = -√2`, `r = π/2` at `x = 0`);
* the right half `x > 0` is `tau π` of the reflected left half (`symm` is definitional there);

**Smoothness is only required on the `τ`-slab `[0,1]`** — that is all the sibling constructions
provide (the curve family `CI` is only an *isotopy* on `[0,1]`).  The assembled family is
therefore defined as `ℓ τ = lagPt … (clamp τ) …` with a smooth idempotent clamp
(`Real.smoothTransition`), which is why every statement about `lagPt` below is a `ContDiffOn` /
`∀ τ ∈ Icc 0 1` statement.

**No `IsLevelData`**: `Work.RPB.B3.levelData_coversFalse` shows that `Work.RPB.IsLevelData` is
*unsatisfiable* for some `CurveIsotopy`s, so the assembly is built from the chord data alone: the
chart `W` (`Work.RPB.B5.chordSurf_rhoChart_full`) and its **level inverse** `ρh`
(`Work.RPB.B5.chart_C12_level_inverse`), both sorry-free statements about `CI` and `a`.

The two *junction* hypotheses of the assembly are

* `hrhonearδ` : `rho` is the level inverse `ρh ∘ sig` on a two-sided neighbourhood of `x = -√2`
  (and the quadratic `(π²/4)(1+x/√2)²` near `0`) — this is what makes the chart branch and the
  collar branch meet smoothly at `x = -√2` and the two halves meet at `x = 0`;
* `σjet` : the collar's one-sided (`σ ≥ 0`) jets at `σ = 0` agree with those of the chart's
  σ-function `σ ↦ W τ t (ρh τ t σ)`; together with the smoothness of both surfaces this makes the
  *difference* flat at `σ = 0`, which is the hypothesis of `Work.RPB.B5.FlatGlue`.

-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- The data of the assembled family: the chord chart `W`, the collar `(Γc, Ac)`, the middle
reparametrisation `rho` and the level inverse `ρh`, together with everything the field lemmas
need. -/
structure LagData (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ) where
  /-- the `ρ = r²`-chart of the chord annulus -/
  W : ℝ → ℝ → ℝ → Work.RPV.PS
  /-- the collar's reduced coordinate -/
  Γc : ℝ → ℝ → ℝ → ℂ
  /-- the collar's phase -/
  Ac : ℝ → ℝ → ℝ → ℝ
  /-- the chord parameter `ρ = r²` of the middle region -/
  rho : ℝ → ℝ → ℝ → ℝ
  /-- the level inverse of the chart on the blown-up diagonal -/
  ρh : ℝ → ℝ → ℝ → ℝ
  /-- the radius of the chart's box -/
  ρ₀ : ℝ
  /-- the level at which the collar reaches the standard zero section -/
  σ₂ : ℝ
  /-- the radius of the interval on which the level inverse is available -/
  κ : ℝ
  hρ₀ : 0 < ρ₀
  hσ₂ : 0 < σ₂
  hκ : 0 < κ
  hπρ₀ : Real.pi ^ 2 / 4 < ρ₀
  /- ### the chart -/
  hWsm : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
    (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀)
  hWchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
    W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r
  hWper : ∀ τ t ρ, W τ (t + 2 * Real.pi) ρ = Work.RPV.Tk 1 (W τ t ρ)
  /- ### the collar -/
  hΓsm : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => Γc z.1 z.2.1 z.2.2)
    (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ))
  hAsm : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => Ac z.1 z.2.1 z.2.2)
    (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ))
  hΓper : ∀ τ σ t, Γc τ σ (t + 2 * Real.pi) = Γc τ σ t
  hAper : ∀ τ σ t, Ac τ σ (t + 2 * Real.pi) = Ac τ σ t + 2 * Real.pi
  hlag : ∀ τ σ t,
    deriv (fun s => Ac τ σ s) t
      = Work.RPV.ωC (deriv (fun s => Γc τ s t) σ) (deriv (fun s => Γc τ σ s) t)
  hemb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ, 0 ≤ σ →
    (∀ t, deriv (fun s => Γc τ σ s) t ≠ 0) ∧
      (∀ t t', Γc τ σ t = Γc τ σ t' → ∃ m : ℤ, t' = t + 2 * Real.pi * m)
  hfar : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ, σ₂ ≤ σ → ∀ t,
    Γc τ σ t = (Real.sqrt (2 + 2 * σ) : ℂ) * Complex.exp ((t - Real.pi / 2) * Complex.I) ∧
      Ac τ σ t = t
  hτ0 : ∀ σ, 0 ≤ σ → ∀ t,
    (Work.RPV.levelPt (Γc 0 σ t) σ (Ac 0 σ t)).2 = 0
  /- ### the level inverse of the chart -/
  hρh : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
    (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ)
  hρh0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ρh τ t 0 = 0
  hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
    ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀
  hρhl : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
    Work.RPV.K0 (W τ t (ρh τ t σ)) + 1 = -σ
  hρhper : ∀ τ t σ, ρh τ (t + 2 * Real.pi) σ = ρh τ t σ
  hρhmono : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
    deriv (fun s : ℝ => ρh τ t s) σ ≠ 0
  hρhpos : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) 0, 0 < ρh τ t σ
  /- ### the middle reparametrisation -/
  hrhosm : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => rho z.1 z.2.1 z.2.2)
  hrhoper : ∀ τ x t, rho τ x (t + 2 * Real.pi) = rho τ x t
  hrhorng : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Icc (-Real.sqrt 2) 0, ∀ t : ℝ,
    rho τ x t ∈ Set.Ioo (-ρ₀) ρ₀
  hrhoval : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Ioc (-Real.sqrt 2) 0, ∀ t : ℝ,
    0 < rho τ x t ∧ rho τ x t ≤ Real.pi ^ 2 / 4
  hrhoderiv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Ioc (-Real.sqrt 2) 0, ∀ t : ℝ,
    deriv (fun y => rho τ y t) x ≠ 0
  hrho0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, rho τ 0 t = Real.pi ^ 2 / 4
  hrhom : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, rho τ (-Real.sqrt 2) t = 0
  /- ### the two junctions -/
  hrhonearδ : ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 4 ∧ δ ≤ κ / (4 * Real.sqrt 2) ∧
    (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Ioo (-Real.sqrt 2 - δ) (-Real.sqrt 2 + δ), ∀ t : ℝ,
      rho τ x t = ρh τ t (sig x)) ∧
    (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Icc (-δ) 0, ∀ t : ℝ,
      rho τ x t = Real.pi ^ 2 / 4 * (1 + x / Real.sqrt 2) ^ 2)
  σjet : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ k : ℕ, k ≤ 8 →
    iteratedDerivWithin k (fun σ : ℝ => Work.RPV.levelPt (Γc τ σ t) σ (Ac τ σ t))
        (Set.Ioi 0) 0
      = iteratedDeriv k (fun σ : ℝ => W τ t (ρh τ t σ)) 0

end Work.RPB.B5

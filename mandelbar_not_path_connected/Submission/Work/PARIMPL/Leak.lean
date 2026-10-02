/-
Copyright: subproject `Submission/Work/PARIMPL/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL.Leak` — LEAK: the robust leak disc

Item §1.4 of `Submission/Work/NOTES_LEAD_mandelbar_residuals.md`: the **leak** of the equator
curve and its **robustness**.

* the equator leak of the root arc (ELRig, `Work.EL.equatorLeak`): there is a real `x*` with
  `Ψ x* ∉ K_{c₀}`, i.e. the equator point at `x*` is in the basin of infinity;
* it is **robust**: the leak set is open and invariant under `x ↦ x ± 1` (`Ψ_shift`, and the
  total invariance of `K`), so there are an integer `j₀` and a radius `r₀ > 0` such that
  `Ψ(closedBall (x* − j₀) r₀)` is **deep** in the escaping region;
* **(I2)**, the robustness of the leak for the family: for parameters close to `c₀`, everything
  close to `Ψ(closedBall (x* − j₀) r₀)` is again outside the filled Julia set.  This is the
  input that needs the **joint continuity of the Green function** `(c, z) ↦ G_c z` of the family
  (NAKANE; `Work.PARIMPL.GreenEscapeOpen`), which is *not* delivered by `Work.Escape` (it has
  continuity in `z` only);
* `trans_escape`: if the **transit coordinate** of a parameter `c ∈ Nm` lands on the leak point
  modulo `ℤ`, then `c ∉ Mb`.  This is `trans_exit`/`Work.PARIMPL.TransitLockstep` + (I2):
  the exit point of the transit is a point of the critical orbit whose repelling coordinate is
  the transit coordinate up to an integer, and the orbit point near the leak disc escapes, so
  the critical orbit of `c` is unbounded.

## Main results

* `Work.PARIMPL.distZ`, `Work.PARIMPL.distZ_le` — the distance to the `ℤ`-orbit;
* `Work.PARIMPL.GreenEscapeOpen` — the NAKANE input (joint continuity of the Green function);
* `Work.PARIMPL.LeakData` — the leak data, including (I2) and `trans_escape`;
* `Work.PARIMPL.green_pos_of_notMem_K`, `Work.PARIMPL.green_pos_iff_notMem_K` — the dictionary
  between the filled Julia set and the positivity of the Green function.
-/
import Submission.Work.PARIMPL.Transit
import Submission.Work.Bottcher.Green.green_pos_iff
import Submission.Work.Bottcher.Green.green_eq_zero_iff_bounded
import Submission.Work.Bottcher.Green.green_nonneg

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

variable {c₀ : ℂ}

/-! ## The distance to the `ℤ`-orbit -/

/-- The distance from `x` to the `ℤ`-orbit of `y` (in the `Ψ`-plane the shift `x ↦ x+1` is the
dynamical shift `Ψ ↦ F ∘ Ψ`, so the leak disc is only determined modulo `ℤ`). -/
noncomputable def distZ (x y : ℂ) : ℝ := ⨅ k : ℤ, dist (x + (k : ℂ)) y

theorem distZ_le (x y : ℂ) (k : ℤ) : distZ x y ≤ dist (x + (k : ℂ)) y :=
  ciInf_le ⟨0, by rintro _ ⟨k, rfl⟩; exact dist_nonneg⟩ k

theorem distZ_nonneg (x y : ℂ) : 0 ≤ distZ x y :=
  le_ciInf fun k => dist_nonneg

/-! ## The Green function of the family -/

/-- The dictionary between the filled Julia set and the Green function: the orbit of `z` under
`T_c` is bounded exactly when the Green function vanishes. -/
theorem green_eq_zero_iff_mem_K (c z : ℂ) :
    Work.Bottcher.green c z = 0 ↔ z ∈ Work.EL.K c :=
  Work.Bottcher.Green.green_eq_zero_iff_bounded c z

/-- A point outside the filled Julia set has positive Green function. -/
theorem green_pos_of_notMem_K {c z : ℂ} (h : z ∉ Work.EL.K c) :
    0 < Work.Bottcher.green c z := by
  rcases lt_or_eq_of_le (Work.Bottcher.Green.green_nonneg c z) with hlt | heq
  · exact hlt
  · exact absurd ((green_eq_zero_iff_mem_K c z).mp heq.symm) h

/-- Positive Green function means outside the filled Julia set. -/
theorem notMem_K_of_green_pos {c z : ℂ} (h : 0 < Work.Bottcher.green c z) :
    z ∉ Work.EL.K c := by
  intro hz
  rw [← green_eq_zero_iff_mem_K c z] at hz
  linarith

/-- **NAKANE** — the joint continuity of the Green function `(c, z) ↦ G_c z` of the family
`T_c`, in the form consumed by the robust-leak argument (I2): the **escape region is open** in
the product of the parameter plane and the dynamical plane.  `Work.Escape` delivers continuity
in `z` only (its `NOTES` §7); this is the missing half. -/
def GreenEscapeOpen : Prop :=
  ∀ c z : ℂ, 0 < Work.Bottcher.green c z →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ c' ∈ ball c ρ, ∀ z' ∈ ball z ρ, 0 < Work.Bottcher.green c' z'

/-! ## LEAK -/

/-- **LEAK** — the robust leak disc of §1.4.

The leak point `x*` of the equator (`Ψ x* ∉ K_{c₀}`, the ELRig input `Work.EL.equatorLeak`), the
shift `j₀` and the radius `r₀` that make the **disc deep** in the escaping region, the robustness
(I2) of the leak for parameters near `c₀` (the NAKANE input `GreenEscapeOpen` enters its
derivation), and the `trans_escape` of §1.4: a parameter of `Nm` whose transit coordinate lands
on the leak point modulo `ℤ` is **not** in the mandelbar. -/
structure LeakData {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) (P : ParNormal d)
    (Pa : Set ℂ) (φa : ℂ → ℂ) (Ψ : ℂ → ℂ)
    (M : MatchData d P Pa φa Ψ) (T : TransitData d P Pa φa Ψ M) where
  /-- the leak point of the equator of `c₀`. -/
  xstar : ℝ
  /-- the shift that makes the leak disc deep in the escaping region. -/
  j₀ : ℤ
  /-- the radius of the leak disc. -/
  r₀ : ℝ
  hr₀ : 0 < r₀
  /-- the leak point of the equator is in the basin of infinity (`Work.EL.equatorLeak`). -/
  leak : Ψ ((xstar : ℝ) : ℂ) ∉ Work.EL.K c₀
  /-- the leak disc is deep in the escaping region: every point of `Ψ '' closedBall (x* − j₀) r₀`
  has positive Green function at `c₀`. -/
  deep : ∀ y ∈ closedBall (((xstar - (j₀ : ℝ)) : ℝ) : ℂ) r₀,
    0 < Work.Bottcher.green c₀ (Ψ y)
  /-- **(I2)** the robustness of the leak for the family: if a point is within `ρ` of the image of
  the leak disc, then it is outside the filled Julia set of every parameter in `ball c₀ ρ`. -/
  robust : ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ ball c₀ ρ, ∀ y : ℂ,
    (∃ z ∈ closedBall (((xstar - (j₀ : ℝ)) : ℝ) : ℂ) r₀, dist y (Ψ z) ≤ ρ) →
      y ∉ Work.EL.K c
  /-- **`trans_escape`**, in the **tracked** form of §1.4 (the form the two-sided argument
  `GATE2` consumes): the escape holds for *both* leak classes — the `b`-tongue `x* − j₀` and its
  `ι`-shift `x* − j₀ + 1/2` (the "`ι b`-tongue", via `equatorLeak_shift` and the `g`-invariance
  of `K`) — with the integer shift of the transit length absorbed into `distZ`.
  Taking `y = x* − j₀` gives the one-sided form
  `distZ (transU) (x* − j₀) < r₀/2 → c ∉ Mb` used by `Work.PARIMPL.noPath`. -/
  escape : ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ P.Nm ∩ ball c₀ ρ, ∀ y : ℝ,
    (y = xstar - (j₀ : ℝ) ∨ y = xstar - (j₀ : ℝ) + 1 / 2) →
    distZ (transU P M.nIn c) ((y : ℝ) : ℂ) < r₀ / 2 → c ∉ Mandelbar

namespace LeakData

variable {d : Work.EL.RootParabolic c₀} {P : ParNormal d}
  {Pa : Set ℂ} {φa : ℂ → ℂ} {Ψ : ℂ → ℂ}
  {M : MatchData d P Pa φa Ψ} {T : TransitData d P Pa φa Ψ M}

/-- The leak point, as a complex number shifted by `j₀`. -/
def liftRe (L : LeakData d P Pa φa Ψ M T) : ℝ := L.xstar - (L.j₀ : ℝ)

theorem liftRe_def (L : LeakData d P Pa φa Ψ M T) :
    L.liftRe = L.xstar - (L.j₀ : ℝ) := rfl

/-! ## The interface for the leak-centre choice

`LeakData` does **not** pin the centre of the leak disc: `xstar` is any real point of the equator
outside `K c₀` and `j₀` any integer shift, and the three contentful fields (`deep`, `robust`,
`escape`) are *statements about the disc centred at* `L.yLeak = xstar − j₀` with radius `r₀`.
A constructor of `LeakData` may therefore take, for the centre, whichever point of the escaping
region it likes — in particular GATE2's leak centre `y₀` (`NOTES_LEAD_mandelbar_gaps2.md` §4: the
maximiser of `ρ(w) = log₁₀₂₄ G(Ψ w) − Re w` over the Stolz sector, chosen *real* so that the
`ι`-tongue `y₀ + 1/2` is `conj y₀ + 1/2` and `Ψ_anti` applies) — by putting

  `xstar := y₀ + N`,  `j₀ := N`  for a large integer `N` (making the disc deep),

which only needs the integer shift-invariance of the off-`K` property,
`Work.PARIMPL.leak_shift_int`: `Ψ x ∉ K c₀ → Ψ (x + n) ∉ K c₀` (from `Ψ_shift` and the total
invariance of `K`).  The *radius* `r₀` remains free as well: the escape field wants it large, the
depth of the disc (off `K`, hence positive Green) wants it small, and the height constraint
`|Im trans| ≤ r₀/4` of `Path.noPath` can be met for *any* `r₀ > 0` by shrinking the neighbourhood
of `c₀` (that is what `TransitData.height` provides). -/

/-- The centre of the leak disc: `xstar − j₀`.  This is the real number that GATE2's leak centre
`xLeak`/`y₀` must be; the fields `deep`, `robust` and `escape` of `LeakData` are statements about
the disc of radius `r₀` centred here. -/
def yLeak (L : LeakData d P Pa φa Ψ M T) : ℝ := L.xstar - (L.j₀ : ℝ)

theorem yLeak_eq_liftRe (L : LeakData d P Pa φa Ψ M T) : L.yLeak = L.liftRe := rfl

/-- The leak centre is a **real** number — so the `ι`-tongue `yLeak + 1/2` is `conj yLeak + 1/2`
and `ParabolicFlower.Psi_anti` applies to it (this is exactly why GATE2 chooses its `ρ`-maximiser
over the real points). -/
theorem yLeak_im (L : LeakData d P Pa φa Ψ M T) : (((L.yLeak : ℝ) : ℂ)).im = 0 := by
  simp

/-- The one-sided from of `escape` (the `b`-tongue): the form used by `Work.PARIMPL.noPath`. -/
theorem escape_one {d : Work.EL.RootParabolic c₀} {P : ParNormal d}
    {Pa : Set ℂ} {φa : ℂ → ℂ} {Ψ : ℂ → ℂ}
    {M : MatchData d P Pa φa Ψ} {T : TransitData d P Pa φa Ψ M}
    (L : LeakData d P Pa φa Ψ M T) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ P.Nm ∩ ball c₀ ρ,
      distZ (transU P M.nIn c) ((L.liftRe : ℝ) : ℂ) < L.r₀ / 2 → c ∉ Mandelbar := by
  obtain ⟨ρ, hρ, h⟩ := L.escape
  refine ⟨ρ, hρ, fun c hc hZ => h c hc L.liftRe (Or.inl rfl) hZ⟩

end LeakData

end Work.PARIMPL

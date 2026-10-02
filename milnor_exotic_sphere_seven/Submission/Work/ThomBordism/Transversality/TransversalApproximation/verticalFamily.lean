import Mathlib
import Submission.Work.ThomBordism.Transversality.Basic
import Submission.Work.ThomBordism.Transversality.BoxFamily.Smooth

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vertical families: the local model of a vertical translation of `Φ`

This file isolates the *interface* used by the construction of the perturbed map in the
transversality homotopy theorem (`TransversalApproximation.exists_perturbation`).

At a point `y₀` where the vertical coordinate `Φ : X.E → ℝ^k` of a `CoreTarget` is a submersion, the
submersion normal form (`BoxFamily`) produces, for every `y` near `y₀` and small `t : ℝ^k`, a point
`box y t` with `Φ (box y t) = Φ y + t`.  That construction is only *smooth* on the open set of pairs
`(y,t)` where all its ingredients are defined (`BoxFamily.boxSet`); elsewhere its value is junk.

Since `X.E` is not assumed to be Hausdorff, there is **no** globally smooth `Ψ` with the exact
identity (this is machine-refuted in `BoxFamily/Counterexample.lean`).  What *does* exist, and what
the perturbation argument uses, is a total function `Ψ` which is smooth on an open set `valid`,
equals the identity outside `valid`, and satisfies the exact identity on `valid`.  This is the
structure `VerticalFamily`.

The main result is `exists_verticalFamily`: at every submersion point of `Φ` such a family exists,
with `valid` containing a whole box `W × {‖t‖ ≤ δ}`.

## Main definitions

* `VerticalFamily` — the interface;
* `VerticalFamily.ofIsSubmersionAt` — the family attached to a submersion point of `Φ`;
* `exists_verticalFamily` — the box neighbourhood version.

## How the perturbation argument uses it

This is the plan of `TransversalApproximation.exists_perturbation` (in `perturbation.lean`), which
should import this file and reproduce the following construction:

* **The cover.**  `tsupport χ` is compact.  For each `y ∈ F '' tsupport χ` use `exists_verticalFamily`
  to get a vertical family `V y`, an open `W y ∋ y` and `δ y > 0` with
  `(z, t) ∈ (V y).valid` for `z ∈ W y`, `‖t‖ ≤ δ y`.  Compactness
  (`IsCompact.elim_finite_subcover`) gives finitely many points `y_i` (`i : Fin N`) with
  `F '' tsupport χ ⊆ ⋃ i, W i`.
* **The partition of unity.**  On the compact set `tsupport χ` use
  `SmoothPartitionOfUnity.exists_isSubordinate` with the open cover `F ⁻¹' W i` to get
  `ρ : Fin N → M → ℝ`, smooth, `0 ≤ ρ i ≤ 1`, `tsupport (ρ i) ⊆ F ⁻¹' (W i)` and
  `∑ i, ρ i x = 1` for `x ∈ tsupport χ`.
* **The composition.**  Let `V i := V y_i`, `W i := W y_i`, `δ i := δ y_i`.  Define, for
  `t : ℝ^k`,
  `G 0 x t := F x`,
  `G (i+1) x t := if x ∈ tsupport (ρ i) then (V i).Ψ (G i x t) (ρ i x • χ x • t) else G i x t`,
  with `σ i := ∑_{j < i} ρ j` the running sum.
  Prove by induction on `i` the statement **(P i)**: there is `ε i > 0` such that
  (a) `ContMDiffOn (I.prod (𝓡 k)) (𝓡 n) ∞ (fun p : M × ℝ^k => G i p.1 p.2) (Set.univ ×ˢ Metric.ball 0 (ε i))`,
  (b) `∀ x t, ‖t‖ < ε i → G i x 0 = F x` (in particular `G i x 0 = F x` holds once `ε i > 0`),
  (c) `∀ x t, ‖t‖ < ε i → X.Φ (G i x t) = X.Φ (F x) + (σ i x) • (χ x • t)`,
  (d) `∀ x ∈ tsupport (ρ i), ∀ t, ‖t‖ < ε i → (G i x t, ρ i x • χ x • t) ∈ (V i).valid`
      (the condition making the *next* step legitimate).
  *Induction step.*  (d) for `i` and openness of `(V i).valid` give, by
  `exists_uniform_ball_of_isCompact_of_continuousAt` applied to
  `x ↦ (t ↦ (G i x t, ρ i x • χ x • t))` on the compact set `tsupport (ρ i)`, a `δ' > 0` such that
  the argument stays in `(V i).valid` for `x ∈ tsupport (ρ i)`, `‖t‖ < δ'`; take
  `ε (i+1) := min (ε i) δ' (possibly `δ i` to keep the amounts small)`.  Then
  (a) is the open-cover argument: on `{x ∉ tsupport (ρ i)} × B` the value is `G i` and on the open
  set where the argument lies in `(V i).valid` it is `(V i).Ψ` composed with the smooth data; the two
  open sets cover `M × B` because the second contains a neighbourhood of `tsupport (ρ i)`.  Use
  `ContMDiffOn.congr` on each, and glue with `ContMDiffOn.union`/pointwise `ContMDiffAt` reasoning.
  (c) is `VerticalFamily.Φ_apply` in the first case and `σ i x = σ (i+1) x`, `ρ i x = 0` in the
  second (outside `tsupport (ρ i)`, where the value is `G i`).
* **Conclusion.**  `𝒢 := G N` and `ε := ε N` satisfy the three conclusions, since `σ N = 1` on
  `tsupport χ` (and `χ = 0` outside, making `σ N x • χ x • t = χ x • t` everywhere).

Nota bene: the amount `ρ i x • χ x • t` satisfies `‖ρ i x • χ x • t‖ ≤ ‖t‖` because `0 ≤ ρ i ≤ 1`
and `0 ≤ χ ≤ 1`, which is how (d) at the base step is reduced to the box bound `δ i`.  Note also
`G i x 0 = F x`: at `t = 0` the amount vanishes and `VerticalFamily.zero_apply` applies (the `if`
branch also uses `zero_apply` when `(y, 0) ∈ valid`). -/

open scoped Manifold ContDiff
open Function Set Topology Manifold Filter

set_option autoImplicit false

namespace Work.ThomBordism.Transversality.TransversalApproximation

noncomputable section

open Work.ThomBordism.Transversality (CoreTarget)
open Work.ThomBordism.Transversality.BoxFamily

variable {n k : ℕ}

/-- **A vertical family at a submersion point of `Φ`.**

`Ψ : X.E → ℝ^k → X.E` is a total function, smooth on the open set `valid`, equal to the identity
outside `valid`, with `Ψ y 0 = y` for all `y`, and satisfying the *exact* identity
`Φ (Ψ y t) = Φ y + t` on `valid`.

The point of the "identity outside `valid`" convention is that the perturbed map is built as a
composition `x ↦ Ψ (G x) (a x)`: on the open set where the argument lies in `valid` this is the
smooth composition of `Ψ` with the data, and where it does not, the amount `a` vanishes and both
branches agree. -/
structure VerticalFamily (X : CoreTarget n k) where
  /-- the point obtained from `y` by translating vertically by `t` -/
  Ψ : X.E → EuclideanSpace ℝ (Fin k) → X.E
  /-- the open set of pairs on which `Ψ` is smooth and satisfies the exact identity -/
  valid : Set (X.E × EuclideanSpace ℝ (Fin k))
  isOpen_valid : IsOpen valid
  contMDiffOn :
    ContMDiffOn ((𝓡 n).prod (𝓡 k)) (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : X.E × EuclideanSpace ℝ (Fin k) => Ψ p.1 p.2) valid
  /-- outside `valid`, `Ψ` is the identity -/
  self_of_not_mem : ∀ y t, (y, t) ∉ valid → Ψ y t = y
  /-- the amount `0` gives back the point -/
  zero_apply : ∀ y, Ψ y 0 = y
  /-- the exact vertical translation on `valid` -/
  Φ_apply : ∀ y t, (y, t) ∈ valid → X.Φ (Ψ y t) = X.Φ y + t

/-- **The vertical family of a submersion point of `Φ`**, built from the submersion normal form
(`BoxFamily`): `box` where the construction is valid, the identity elsewhere. -/
noncomputable def VerticalFamily.ofIsSubmersionAt (X : CoreTarget n k) {y₀ : X.E}
    (h : IsSubmersionAt (𝓡 n) (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞) X.Φ y₀) : VerticalFamily X := by
  classical
  exact
  { Ψ := fun y t => if (y, t) ∈ boxSet h.isSubmersionAtOfComplement_complement
      then box h.isSubmersionAtOfComplement_complement y t else y
    valid := boxSet h.isSubmersionAtOfComplement_complement
    isOpen_valid := boxSet_isOpen _
    contMDiffOn := (contMDiffOn_box _).congr (fun p hp => by simp only [hp, if_true])
    self_of_not_mem := fun y t ht => by simp only [ht, if_false]
    zero_apply := fun y => by
      by_cases hyt : (y, 0) ∈ boxSet h.isSubmersionAtOfComplement_complement
      · simp only [hyt, if_true]
        exact box_zero _ hyt.1
      · simp only [hyt, if_false]
    Φ_apply := fun y t hyt => by
      simp only [hyt, if_true]
      exact box_Phi _ hyt }

/-- **The box neighbourhood of a vertical family**: at a submersion point of `Φ` there is a vertical
family `V` and a box `W × {‖t‖ ≤ δ}` (`W` open, `y₀ ∈ W`, `δ > 0`) contained in `V.valid`. -/
theorem exists_verticalFamily (X : CoreTarget n k) {y₀ : X.E}
    (h : IsSubmersionAt (𝓡 n) (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞) X.Φ y₀) :
    ∃ V : VerticalFamily X, ∃ (W : Set X.E) (δ : ℝ), IsOpen W ∧ y₀ ∈ W ∧ 0 < δ ∧
      ∀ y ∈ W, ∀ t : EuclideanSpace ℝ (Fin k), ‖t‖ ≤ δ → (y, t) ∈ V.valid := by
  obtain ⟨W, δ, hW, hyW, hδ, hbox⟩ := exists_boxSet_nhds h.isSubmersionAtOfComplement_complement
  refine ⟨VerticalFamily.ofIsSubmersionAt X h, W, δ, hW, hyW, hδ, ?_⟩
  intro y hy t ht
  change (y, t) ∈ boxSet h.isSubmersionAtOfComplement_complement
  exact hbox y hy t ht

end

end Work.ThomBordism.Transversality.TransversalApproximation

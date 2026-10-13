import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.thetaGrowth
import Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.poleBoundOfSourcePow
import Submission.Work.FTS.EllipticEst.H2W.PropH2Base
import Submission.Work.FTS.EllipticEst.Endpt.slice_regularity_of_uncurry
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.TT.bslOp_DzIter_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `WeakPureAux/towerAscent` — the level tower, and the ascent/descent of the slice bound

Let `(G, Φ)` be a pair on the open quadrant with `bslOp α Φ = G` there and `Φ` smooth, and write
`Φ_j := ∂_z^j Φ` for the radial levels.  The equation at level `0` in *slice* form is

  `Lzero1 (Φ z ·) = G z · + α²z²·Φ_2(z,·) + α(5+α)z·Φ_1(z,·)`   on `(0, π/2)`
  (`lzero1_slice_eq_of_class` below),

and differentiating it `m` times in `z` (`D_z` commutes with `bslOp α`, `TT.bslOp_DzIter_eq`)
gives the same relation with every level shifted by `m`.  Note that *no* `HkMem` hypothesis is
used: only the equation and the smoothness — so the statements below apply to the shifted data
`(D_z^m G, D_z^m Φ)` as well, which is what makes the full index descent iterative.

Combining the slice tower with the *indicial step* for `Lzero1` (a source of growth
`θ^{-(R+2)}`/`(π/2-θ)^{-(R+2)}` forces a solution of growth `θ^{-R}`/`(π/2-θ)^{-R}`, for `R > 1`,
proved as `WeakPureAux.poleBoundOfSourcePow`) gives the **ascent**:

> if the slices of `G`, `Φ_1` and `Φ_2` at a fixed `z` are all of growth `≤ t^{-(R+2)}`, then the
> slice of `Φ` at that `z` is of growth `≤ t^{-R}`  (`towerAscent_of_eq`);

and its contrapositive, the **descent**:

> if the slice of `Φ` at `z` fails to grow like `t^{-R}`, then one of the three slices `G z ·`,
> `∂_zΦ(z,·)`, `∂_z²Φ(z,·)` fails to grow like `t^{-(R+2)}`  (`towerDescent_of_eq`).

`towerAscent` / `towerDescent` are the `WeakPos0` instances (the class is only used for its
equation and smoothness fields, both of which the general versions take separately).

**Where the argument stops** (`NOTES_weakPhiPoleBound.md` §U): the descent's first alternative —
"the source `G` is to blame" — is not refutable from the class, since `HkMem α 0 G` constrains
`G`'s slice only in the weighted-`L²(sEta)` sense, which admits growth as bad as `t^{-3.5}`.
Closing the target needs the *quantitative* cascade of §K rather than the indicial step alone.
-/

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.WeakPureAux

/-- The pointwise identification of the slice source: `Lzero1 (Φ z ·) = G z · + E_z` with
`E_z = α²z²·∂_z²Φ(z,·) + α(5+α)z·∂_zΦ(z,·)` (the slice form of `bslOp α Φ = G`). -/
theorem lzero1_slice_eq_of_class {α : ℝ} {G Φ : ℝ → ℝ → ℝ}
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Φ z θ = G z θ)
    {z : ℝ} (hz : 0 < z) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 (fun θ' => Φ z θ') θ
        = G z θ + (α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Φ z θ
            + (α * (5 + α) * z) * Work.Spaces.pz Φ z θ) := by
  intro θ hθ
  have h1 : Work.Elliptic.bslOp α Φ z θ = G z θ := heq z hz θ hθ.1 hθ.2
  rw [Work.Elliptic.bslOp_apply] at h1
  have h2 : Work.FTS.EllipticEst.Lzero1 (fun θ' => Φ z θ') θ
      = Work.Elliptic.Lzero Φ z θ := by
    rw [Work.FTS.EllipticEst.Lzero1_eq_Lzero (fun θ' => Φ z θ') z]
    simp only [Work.Elliptic.Lzero, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
      Work.Spaces.pth]
  rw [h2]
  linarith

/-- **The indicial step in the hypothesis shape used below.**  This is
`poleBoundOfSourcePow` with the source written as `Lzero1 u` (so that the hypothesis bounds
`|Lzero1 u|` directly); it is the `c = 0` instance of the *shifted* indicial step. -/
theorem indicialStep_zero : ∀ (R : ℝ) (u : ℝ → ℝ), 1 < R →
    ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)) →
    (∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.FTS.EllipticEst.Lzero1 u θ|
        ≤ C * (1 / θ ^ (R + 2) + 1 / (Real.pi / 2 - θ) ^ (R + 2))) →
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |u θ| ≤ C' * (1 / θ ^ R + 1 / (Real.pi / 2 - θ) ^ R) := by
  intro R u hR hu hsrc
  obtain ⟨C, hC, hb⟩ := hsrc
  exact Work.FTS.EllipticEst.H2W.WeakPureAux.poleBoundOfSourcePow (R := R) (u := u)
    (g := fun θ => Work.FTS.EllipticEst.Lzero1 u θ) hR hu (fun θ _ => rfl) hC
    (fun θ hθ => hb θ hθ)

/-- **The ascent of the slice bound along the level tower** (conditional form, so that any future
variant of the indicial step — e.g. the *shifted* one, `sliceLzeroShiftPowPoleBound` — can be
plugged in).  Hypotheses: only `0 < α`, the equation on the open quadrant and the smoothness of
`Φ` (no `HkMem`); hence the statement applies verbatim to the shifted data
`(G, Φ) := (DzIter m G, DzIter m Φ)` via `TT.bslOp_DzIter_eq`. -/
theorem towerAscent_of_indicialStep
    (hstep : ∀ (R : ℝ) (u : ℝ → ℝ), 1 < R →
      ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)) →
      (∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Work.FTS.EllipticEst.Lzero1 u θ|
          ≤ C * (1 / θ ^ (R + 2) + 1 / (Real.pi / 2 - θ) ^ (R + 2))) →
      ∃ C' : ℝ, 0 ≤ C' ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |u θ| ≤ C' * (1 / θ ^ R + 1 / (Real.pi / 2 - θ) ^ R)) :
    ∀ (α : ℝ) (G Φ : ℝ → ℝ → ℝ), 0 < α →
    (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Φ z θ = G z θ) →
    (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
    ∀ z, 0 < z → ∀ R : ℝ, 1 < R →
    (∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |G z θ| ≤ C * (1 / θ ^ (R + 2) + 1 / (Real.pi / 2 - θ) ^ (R + 2))) →
    (∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Work.Spaces.pz Φ z θ| ≤ C * (1 / θ ^ (R + 2) + 1 / (Real.pi / 2 - θ) ^ (R + 2))) →
    (∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Work.Spaces.pzIter 2 Φ z θ|
          ≤ C * (1 / θ ^ (R + 2) + 1 / (Real.pi / 2 - θ) ^ (R + 2))) →
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Φ z θ| ≤ C' * (1 / θ ^ R + 1 / (Real.pi / 2 - θ) ^ R) := by
  intro α G Φ hα heq hsm z hz R hR hG h1 h2
  obtain ⟨CG, hCG, hGb⟩ := hG
  obtain ⟨C1, hC1, h1b⟩ := h1
  obtain ⟨C2, hC2, h2b⟩ := h2
  -- smoothness of the slice and the slice form of the equation
  have hu2 : ContDiffOn ℝ 2 (fun θ => Φ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_uncurry hz 2 (hsm 2)
  -- the source bound
  have hsrc : ∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.FTS.EllipticEst.Lzero1 (fun θ' => Φ z θ') θ|
        ≤ C * (1 / θ ^ (R + 2) + 1 / (Real.pi / 2 - θ) ^ (R + 2)) := by
    refine ⟨CG + α ^ 2 * z ^ 2 * C2 + α * (5 + α) * z * C1, by positivity, fun θ hθ => ?_⟩
    have hg := hGb θ hθ
    have hA := h1b θ hθ
    have hB := h2b θ hθ
    have hcA : 0 ≤ α ^ 2 * z ^ 2 := by positivity
    have hcB : 0 ≤ α * (5 + α) * z := by positivity
    rw [lzero1_slice_eq_of_class heq hz θ hθ]
    calc |G z θ + (α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Φ z θ
          + (α * (5 + α) * z) * Work.Spaces.pz Φ z θ)|
        ≤ |G z θ| + |α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Φ z θ
            + (α * (5 + α) * z) * Work.Spaces.pz Φ z θ| := abs_add_le _ _
      _ ≤ |G z θ| + (|α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Φ z θ|
            + |(α * (5 + α) * z) * Work.Spaces.pz Φ z θ|) := by
            linarith [abs_add_le (α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Φ z θ)
              ((α * (5 + α) * z) * Work.Spaces.pz Φ z θ)]
      _ = |G z θ| + α ^ 2 * z ^ 2 * |Work.Spaces.pzIter 2 Φ z θ|
            + α * (5 + α) * z * |Work.Spaces.pz Φ z θ| := by
            have hAa : |α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Φ z θ|
                = α ^ 2 * z ^ 2 * |Work.Spaces.pzIter 2 Φ z θ| := by
              rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ α ^ 2 * z ^ 2)]
            have hBb : |(α * (5 + α) * z) * Work.Spaces.pz Φ z θ|
                = α * (5 + α) * z * |Work.Spaces.pz Φ z θ| := by
              rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ α * (5 + α) * z)]
            rw [hAa, hBb]
            ring
      _ ≤ CG * (1 / θ ^ (R + 2) + 1 / (Real.pi / 2 - θ) ^ (R + 2))
            + α ^ 2 * z ^ 2 * (C2 * (1 / θ ^ (R + 2) + 1 / (Real.pi / 2 - θ) ^ (R + 2)))
            + α * (5 + α) * z * (C1 * (1 / θ ^ (R + 2)
                + 1 / (Real.pi / 2 - θ) ^ (R + 2))) := by
            linarith [hg, mul_le_mul_of_nonneg_left hB hcA,
              mul_le_mul_of_nonneg_left hA hcB]
      _ = (CG + α ^ 2 * z ^ 2 * C2 + α * (5 + α) * z * C1)
            * (1 / θ ^ (R + 2) + 1 / (Real.pi / 2 - θ) ^ (R + 2)) := by ring
  exact hstep R (fun θ => Φ z θ) hR hu2 hsrc

/-- **The unconditional ascent.** -/
theorem towerAscent_of_eq :
    ∀ (α : ℝ) (G Φ : ℝ → ℝ → ℝ), 0 < α →
    (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Φ z θ = G z θ) →
    (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
    ∀ z, 0 < z → ∀ R : ℝ, 1 < R →
    (∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |G z θ| ≤ C * (1 / θ ^ (R + 2) + 1 / (Real.pi / 2 - θ) ^ (R + 2))) →
    (∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Work.Spaces.pz Φ z θ| ≤ C * (1 / θ ^ (R + 2) + 1 / (Real.pi / 2 - θ) ^ (R + 2))) →
    (∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Work.Spaces.pzIter 2 Φ z θ|
          ≤ C * (1 / θ ^ (R + 2) + 1 / (Real.pi / 2 - θ) ^ (R + 2))) →
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Φ z θ| ≤ C' * (1 / θ ^ R + 1 / (Real.pi / 2 - θ) ^ R) :=
  towerAscent_of_indicialStep indicialStep_zero

/-- **The descent** (the contrapositive of `towerAscent_of_eq`): if the slice of `Φ` at `z` fails
to grow like `t^{-R}` (`R > 1`), then one of the three slices `G z ·`, `∂_zΦ(z,·)`,
`∂_z²Φ(z,·)` fails to grow like `t^{-(R+2)}`.  Iterating this over the levels `D_z^m` — the
hypotheses of `towerAscent_of_eq` are stable under `D_z^m` by `TT.bslOp_DzIter_eq` — is the index
descent of `NOTES_weakPhiPoleBound.md` §U. -/
theorem towerDescent_of_eq :
    ∀ (α : ℝ) (G Φ : ℝ → ℝ → ℝ), 0 < α →
    (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Φ z θ = G z θ) →
    (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
    ∀ z, 0 < z → ∀ R : ℝ, 1 < R →
    ¬ (∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Φ z θ| ≤ C * (1 / θ ^ R + 1 / (Real.pi / 2 - θ) ^ R)) →
    (¬ (∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          |G z θ| ≤ C * (1 / θ ^ (R + 2) + 1 / (Real.pi / 2 - θ) ^ (R + 2)))
      ∨ ¬ (∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          |Work.Spaces.pz Φ z θ| ≤ C * (1 / θ ^ (R + 2) + 1 / (Real.pi / 2 - θ) ^ (R + 2)))
      ∨ ¬ (∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          |Work.Spaces.pzIter 2 Φ z θ|
            ≤ C * (1 / θ ^ (R + 2) + 1 / (Real.pi / 2 - θ) ^ (R + 2)))) := by
  intro α G Φ hα heq hsm z hz R hR hbad
  by_contra hcon
  push_neg at hcon
  obtain ⟨hG, h1, h2⟩ := hcon
  obtain ⟨C', hC'0, hb'⟩ := towerAscent_of_eq α G Φ hα heq hsm z hz R hR hG h1 h2
  refine hbad ⟨C' + 1, by linarith, fun θ hθ => ?_⟩
  have hθb := hb' θ hθ
  have hS0 : 0 ≤ 1 / θ ^ R + 1 / (Real.pi / 2 - θ) ^ R := by
    have hp1 : 0 < θ ^ R := Real.rpow_pos_of_pos hθ.1 _
    have hp2 : 0 < (Real.pi / 2 - θ) ^ R := Real.rpow_pos_of_pos (by linarith [hθ.2]) _
    positivity
  calc |Φ z θ| ≤ C' * (1 / θ ^ R + 1 / (Real.pi / 2 - θ) ^ R) := hθb
    _ ≤ (C' + 1) * (1 / θ ^ R + 1 / (Real.pi / 2 - θ) ^ R) :=
        mul_le_mul_of_nonneg_right (by linarith) hS0

/-- **The `WeakPos0` instance of the ascent** (the class is used only for its equation and
smoothness fields; `HkMem α 0 G` and the moment conditions are not used). -/
theorem towerAscent :
    ∀ (α : ℝ) (G Φ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.WeakPos0 α G Φ →
    ∀ z, 0 < z → ∀ R : ℝ, 1 < R →
    (∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |G z θ| ≤ C * (1 / θ ^ (R + 2) + 1 / (Real.pi / 2 - θ) ^ (R + 2))) →
    (∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Work.Spaces.pz Φ z θ| ≤ C * (1 / θ ^ (R + 2) + 1 / (Real.pi / 2 - θ) ^ (R + 2))) →
    (∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Work.Spaces.pzIter 2 Φ z θ|
          ≤ C * (1 / θ ^ (R + 2) + 1 / (Real.pi / 2 - θ) ^ (R + 2))) →
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Φ z θ| ≤ C' * (1 / θ ^ R + 1 / (Real.pi / 2 - θ) ^ R) := by
  intro α G Φ hα hα4 hW
  obtain ⟨heq, -, -, -, -, hsm, -⟩ := hW
  exact towerAscent_of_eq α G Φ hα heq hsm

/-- **The `WeakPos0` instance of the descent.** -/
theorem towerDescent :
    ∀ (α : ℝ) (G Φ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.WeakPos0 α G Φ →
    ∀ z, 0 < z → ∀ R : ℝ, 1 < R →
    ¬ (∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Φ z θ| ≤ C * (1 / θ ^ R + 1 / (Real.pi / 2 - θ) ^ R)) →
    (¬ (∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          |G z θ| ≤ C * (1 / θ ^ (R + 2) + 1 / (Real.pi / 2 - θ) ^ (R + 2)))
      ∨ ¬ (∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          |Work.Spaces.pz Φ z θ| ≤ C * (1 / θ ^ (R + 2) + 1 / (Real.pi / 2 - θ) ^ (R + 2)))
      ∨ ¬ (∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          |Work.Spaces.pzIter 2 Φ z θ|
            ≤ C * (1 / θ ^ (R + 2) + 1 / (Real.pi / 2 - θ) ^ (R + 2)))) := by
  intro α G Φ hα hα4 hW
  obtain ⟨heq, -, -, -, -, hsm, -⟩ := hW
  exact towerDescent_of_eq α G Φ hα heq hsm

/-- **The level-shifted descent.**  `towerDescent_of_eq` applied to the shifted datum
`(D_z^m G, D_z^m Φ)`: the hypotheses are stable under `D_z^m` (`TT.bslOp_DzIter_eq` for the
equation, `SmoothOpen.DzIter` for the smoothness), and no `HkMem` is needed.  Read
`Φ_m := DzIter m Φ`, the three alternatives say that if the level-`m` slice fails to grow like
`t^{-R}` then the *source* `G_m` or one of the two neighbouring slices (written here as
`∂_zΦ_m`, `∂_z²Φ_m`; note `DzIter (m+1) Φ = z·∂_zΦ_m` and
`DzIter (m+2) Φ = DzIter (m+1) Φ + z²·∂_z²Φ_m`) fails to grow like `t^{-(R+2)}`. -/
theorem towerDescent_level :
    ∀ (α : ℝ) (G Φ : ℝ → ℝ → ℝ), 0 < α →
    (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Φ z θ = G z θ) →
    (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
    ∀ m : ℕ, ∀ z, 0 < z → ∀ R : ℝ, 1 < R →
    ¬ (∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Work.Spaces.DzIter m Φ z θ| ≤ C * (1 / θ ^ R + 1 / (Real.pi / 2 - θ) ^ R)) →
    (¬ (∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          |Work.Spaces.DzIter m G z θ| ≤ C * (1 / θ ^ (R + 2) + 1 / (Real.pi / 2 - θ) ^ (R + 2)))
      ∨ ¬ (∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          |Work.Spaces.pz (Work.Spaces.DzIter m Φ) z θ|
            ≤ C * (1 / θ ^ (R + 2) + 1 / (Real.pi / 2 - θ) ^ (R + 2)))
      ∨ ¬ (∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          |Work.Spaces.pzIter 2 (Work.Spaces.DzIter m Φ) z θ|
            ≤ C * (1 / θ ^ (R + 2) + 1 / (Real.pi / 2 - θ) ^ (R + 2)))) := by
  intro α G Φ hα heq hsm m z hz R hR hbad
  have hSO : Work.FTS.EllipticEst.SmoothOpen Φ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hsm' : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.DzIter m Φ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun n => (hSO.DzIter m).forall n
  have heq' : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α (Work.Spaces.DzIter m Φ) z θ = Work.Spaces.DzIter m G z θ :=
    Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α G Φ m hsm heq
  exact towerDescent_of_eq α (Work.Spaces.DzIter m G) (Work.Spaces.DzIter m Φ) hα heq' hsm'
    z hz R hR hbad

end Work.FTS.EllipticEst.H2W.WeakPureAux

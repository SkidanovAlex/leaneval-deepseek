import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.Cube.Defs
import Submission.Work.BoseFixB1S.perBoxIntegratedUnifCube
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.Defs` — the **cube-window a-priori chapter**: vocabulary

Area `BoseB1Cube` owns the last mile of node D5 (`Work.BoseFixB1.nodeB1B_holds`).

`Work.BoseFixB1.nodeB1B_holds_of_cubePieces` (`Submission/Work/BoseFixB1/Cube/Headline.lean`,
PROVED, axiom-clean) derives FS `thm:aprioribounds` from exactly two matched-window pieces:

* `Work.BoseFixB1B.SlidingBCube v h` — FS `eq:BSsliding2` / Bratteli–Solovej Thm 3.10 at the
  **single cube cutoff** `chiSmallB` (FS's own modelling, `eq:chiBdefinition`) — **PROVED**, see
  `Submission/Work/BoseFixB1C/slidingBCubeHolds.lean` (`Work.BoseFixB1C.SlidingBCube_holds`),
  re-exported here as `Work.BoseB1Cube.slidingBCube_holds`;
* `Work.BoseFixB1.SmallBoxCollectedCube v h J` — FS `thm:smallbox` integrated over the sliding
  boxes at the same cutoff (`Cube/Defs.lean`).

This module fixes the vocabulary in which the second is attacked.  It **adds no mathematics**: it
names the four residuals out of which `SmallBoxCollectedCube` is assembled, and states the two
*elementary* passages that are proved in the sibling modules of the area
(`Absorb.lean`, `Assembly.lean`, `PerBox.lean`).

## The residual ledger of the cube chapter (all four statements are *stated* here)

    SmallBoxCollectedCube v h J
      ⟸ [elementary, `Absorb.lean`]  CollectedUnifCube v h  +  SlidingBCube v h
      ⟸ [elementary, `Assembly.lean`]  CubePerBox v h R  +  CubeTrim v h  (+ the mass law, PROVED)
      ⟸ [`PerBox.lean`]  the per-box F-row + the PROVED paying instruments
                          (`Work.BoseFixB1B.sbWordCube_ge_a0Main_add_boxA2`, the rung-4 payment
                          `Work.BoseFixB1S.a0A2PaymentAdm_holds` and the port
                          `Work.BoseFixB1B.slidingBogPort_proved`)

The four names:

* `Work.BoseB1Cube.CollectedUnifCube` — an **abbreviation** for
  `Work.BoseFixB1S.CollectedUnifCube`: FS `thm:smallbox` integrated over the interior set at one
  triple of constants, with the constant `c` on `R_Ψ` kept explicit (`c ≤ 1`; the `1/c` is absorbed
  by the *difference trick* of `Absorb.lean`, not by dividing).
* `Work.BoseB1Cube.CubePerBox v h R` — the per-`u` per-box row `Work.BoseFixB1S.PerBoxFCube` on
  FS's *good* set, with constants existentially quantified.  This is the genuine analytic residual:
  FS `thm:smallbox` at the sliding box, in the matched (single cube cutoff) vocabulary.
* `Work.BoseB1Cube.CubeTrim v h` — FS `eq:badset`: the interior `u`-integral of `sbWordCube` is
  dominated by the full `ℝ³`-integral, at the cost of the a-priori error.
* `Work.BoseB1Cube.CubeMassLaw v h` — FS `eq:appw1sliding`: `∫_{I₋} w_{1,B(u)} du ≤ 8π(a v)ℓ³(1+Cκ)`.
  **This one is a theorem**, proved at `Work.BoseFixB1B.w1MassB_integral_le_holds`; it is stated
  here as a `Prop` only so that `Assembly.lean` can be read as a pure ledger
  (`cubeMassLaw_holds` discharges it).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The cube-window collected per-box bound** — an abbreviation for the established
`Work.BoseFixB1S.CollectedUnifCube`: there are `ε₀ > 0`, `0 ≤ C`, `0 < c` such that for every
admissible `μ`, every `J ≤ K_B³` and every low box state,

`0 ≤ R_Ψ` and `c·R_Ψ ≤ ∫_{ℝ³} sbWordCube + 4πμ²(a v)ℓ³(1 + C·K_B³(μ(a v)³)^{1/2})‖Φ‖²`.

The constant `c ∈ (0,1]` on `R_Ψ` is FS's convexity constant of the `F`-weight; the
coefficient-`1` form is `Work.BoseFixB1.SmallBoxCollectedCube`. -/
abbrev CollectedUnifCube (v : E3 → ℝ) (h : ScatSol v) : Prop :=
  Work.BoseFixB1S.CollectedUnifCube v h

/-- **The per-`u` per-box row at the cube cutoff on FS's good set** — the analytic residual of the
matched chapter: FS `thm:smallbox` at the sliding box `B(u)`, in the single-cutoff vocabulary
`sbWordCube`, with constants `(ε₀, c₁, C)` existentially quantified over all admissible `μ` and
*all* states (no lowness restriction; the lowness enters only in `CubeTrim`).

This is `Work.BoseFixB1S.PerBoxFCube` on `Work.SmallBoxSliding.goodSet`.  It is the *repair* of the
mixed-window frozen target `Work.BoseFixB1.PerBoxF`: the kinetic slot of the word is read at the
same bump `chiSmallB` as the kernels, so the proved paying instruments apply directly. -/
def CubePerBox (v : E3 → ℝ) (h : ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
        Work.BoseFixB1S.PerBoxFCube v h R c₁ C μ n Φ u

/-- The same residual read on the **interior** set `I₋` — the shape consumed by the integration
step (`Work.BoseFixB1S.perBoxIntegratedUnifCube`).  It is *implied* by `CubePerBox`, because
`I₋ ⊆ goodSet` (`Work.SmallBoxSliding.interiorSet_subset_goodSet`). -/
def CubePerBoxInterior (v : E3 → ℝ) (h : ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3),
        u ∈ Work.SmallBoxSliding.interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
        Work.BoseFixB1S.PerBoxFCube v h R c₁ C μ n Φ u

/-- **FS `eq:badset` at the cube cutoff**: the interior `u`-integral of the matched word is
dominated by the whole-space one, at the cost of the a-priori error
`C·μ²(a v)ℓ³K_B³(μ(a v)³)^{1/2}‖Φ‖²`.  Uniform in the threshold `J ≤ K_B³`. -/
def CubeTrim (v : E3 → ℝ) (h : ScatSol v) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ (J : ℝ) (μ : ℝ), Adm v ε₀ μ →
      J ≤ (paramsAt μ (a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
        IsLowB v h J μ n Φ →
        (∫ u in Work.SmallBoxSliding.interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
            Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
          ≤ (∫ u : E3, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
            + C * (μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
                    * (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
              * normB v μ n (Φ : X n → ℝ)

/-- **FS `eq:appw1sliding`**: the `u`-integral of the sliding-box mass `w_{1,B(u)}` is at most
`8π(a v)ℓ³(1 + Cκ)`, so that `½μ²·∫w_{1,B} = 4πμ²(a v)ℓ³(1+o(1))` — the mean-field energy. -/
def CubeMassLaw (v : E3 → ℝ) (h : ScatSol v) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ μ : ℝ, Adm v ε₀ μ →
    (∫ u in Work.SmallBoxSliding.interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
        Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
          (paramsAt μ (a v)).d u)
      ≤ 8 * π * (a v) * sideAt μ (a v) ^ 3
          * (1 + C * (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))

/-- **The crude per-`u` lower bound (FS `final_v2.tex` l.4083) at the cube cutoff** — what remains
of `PerBoxFCube` after the nonnegative `F`-remainder is dropped: the matched word dominates a
negative multiple of the box mass `μ²(a v)χ_B(u)² + μ(a v)`.  It is the input of FS `eq:badset`
(`CubeTrim`) and the cube twin of `Work.BoseFixB1S.PerBoxCrudeB1`. -/
def CubeCrude (v : E3 → ℝ) (h : ScatSol v) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ (J : ℝ) (μ : ℝ), Adm v ε₀ μ →
      J ≤ (paramsAt μ (a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3),
        IsLowB v h J μ n Φ →
        -(C * (μ ^ 2 * (a v)
                * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                    (paramsAt μ (a v)).d u
              + μ * (a v)))
            * normB v μ n (Φ : X n → ℝ)
          ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)

/-- **The crude per-`u` lower bound restricted to FS's good set** — the shape of `CubeCrude` on
`Work.SmallBoxSliding.goodSet`, which is what the F-weighted per-box row `CubePerBox` implies (drop
the nonnegative `F`-remainder, use `Work.BoseFixB1.w1MassB_le_const_mul_chiMass_regime`).  It is
the cube twin of the PROVED `Work.BoseFixB1S.perBoxCrudeLower_of_perBoxF`. -/
def CubeCrudeGood (v : E3 → ℝ) (h : ScatSol v) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ (J : ℝ) (μ : ℝ), Adm v ε₀ μ →
      J ≤ (paramsAt μ (a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
        IsLowB v h J μ n Φ →
        -(C * (μ ^ 2 * (a v)
                * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                    (paramsAt μ (a v)).d u
              + μ * (a v)))
            * normB v μ n (Φ : X n → ℝ)
          ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)

/-- `CubeMassLaw` is a **theorem** of the corpus (`Work.BoseFixB1B.w1MassB_integral_le_holds`). -/
theorem cubeMassLaw_holds {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < a v) :
    CubeMassLaw v h :=
  Work.BoseFixB1B.w1MassB_integral_le_holds h hv hv1 hvrad hR hv_supp hav

/-- `CubePerBox` (good set) implies `CubePerBoxInterior` (interior set). -/
theorem cubePerBoxInterior_of_cubePerBox {v : E3 → ℝ} {h : ScatSol v} {R : ℝ}
    (hF : CubePerBox v h R) : CubePerBoxInterior v h R := by
  obtain ⟨ε₀, c₁, C, hε₀, hc₁, hC, hbody⟩ := hF
  refine ⟨ε₀, c₁, C, hε₀, hc₁, hC, ?_⟩
  intro μ hAdm n Φ u hu
  exact hbody μ hAdm n Φ u
    (Work.SmallBoxSliding.interiorSet_subset_goodSet (Work.BoseFixB1.adm_mu_pos hAdm) hu)

/-! ## 3. The left-hand side of `PerBoxFCube`, as a number

`Work.BoseFixB1S.PerBoxFCube` is a `Prop`; the ledger of the cube chapter (`WordRow.lean`) adds
numbers to its left-hand side, so that side has to be named.  The body is copied *verbatim* from
the definition in `Submission/Work/BoseFixB1S/LowCountWindowAllJCube.lean`, hence the `iff` below
is `Iff.rfl`. -/

/-- The left-hand side of `Work.BoseFixB1S.PerBoxFCube`: the `F`-weighted mean-field demand at the
sliding box, minus FS's error bracket. -/
noncomputable def perBoxCubeLHS (v : E3 → ℝ) (h : ScatSol v) (R c₁ C : ℝ) (μ : ℝ) (n : ℕ)
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3) : ℝ :=
  c₁ * (Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u *
        (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
          Work.SmallBoxSliding.psiWeight 1 μ
            (Work.BoseFixB1.nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
              Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                (paramsAt μ (a v)).d u)))
    - (1 / 2) * μ ^ 2 * Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)
    - C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
            + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
          * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)
        + μ * (a v) * normB v μ n (Φ : X n → ℝ))

/-- `PerBoxFCube` is exactly `perBoxCubeLHS ≤ sbWordCube`. -/
theorem perBoxFCube_iff (v : E3 → ℝ) (h : ScatSol v) (R c₁ C μ : ℝ) (n : ℕ)
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3) :
    Work.BoseFixB1S.PerBoxFCube v h R c₁ C μ n Φ u
      ↔ perBoxCubeLHS v h R c₁ C μ n Φ u
          ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ) :=
  Iff.rfl

/-- **`IsLowB` is monotone *downward* in the threshold `J`**: the bound at a *larger* threshold is
weaker, because `ℓ³Θ(a v) J μ = −4πμ²(a v)ℓ³(1 − J√(μa³))` *increases* with `J`.  (Contrapositive
form of the fact used all over the chapter: a state that is low at `J` is low at every `J' ≥ J`.)
This is the only monotonicity of the hypothesis available, and it is what makes the J-inner and
J-outer spellings of the trim interchangeable *only in the direction `J ≤ J'`*. -/
theorem isLowB_mono_J {v : E3 → ℝ} {h : ScatSol v} {ε₀ J J' μ : ℝ} {n : ℕ} {Φ : X n → ℝ}
    (hAdm : Adm v ε₀ μ) (hav : 0 < a v) (hJJ : J ≤ J') (hlow : IsLowB v h J μ n Φ) :
    IsLowB v h J' μ n Φ := by
  rw [Work.BoseFixB1.isLowB_iff hav] at hlow ⊢
  have hA : 0 ≤ 4 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3 := by
    have hℓ : 0 < sideAt μ (a v) := Work.BoseFixB1.adm_ell_pos hAdm
    have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
    have hπ : 0 < Real.pi := Real.pi_pos
    positivity
  have hs : 0 ≤ Real.sqrt (μ * (a v) ^ 3) := Real.sqrt_nonneg _
  have hN : 0 ≤ normB v μ n Φ := Work.BoseFixB1.normB_nonneg Φ
  have h1 : (1 : ℝ) - J' * Real.sqrt (μ * (a v) ^ 3)
      ≤ 1 - J * Real.sqrt (μ * (a v) ^ 3) := by
    nlinarith [hs, hJJ]
  have h2 : -(4 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
        * (1 - J * Real.sqrt (μ * (a v) ^ 3)))
      ≤ -(4 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
        * (1 - J' * Real.sqrt (μ * (a v) ^ 3))) := by
    have := mul_le_mul_of_nonneg_left h1 hA
    linarith
  have h3 := mul_le_mul_of_nonneg_right h2 hN
  linarith [hlow, h3]

end Work.BoseB1Cube

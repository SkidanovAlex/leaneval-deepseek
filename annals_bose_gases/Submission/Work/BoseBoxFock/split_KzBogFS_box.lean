import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseBoxFock.KzOpC
import Submission.Work.BoseBoxFock.split_sandwiches
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.split_KzBogFS_box` — the Bogoliubov row of FS `eq:Kz` under `split`

`Work.BoseBoxFock.KzBogFS` is FS `eq:BogHamPositive-1` with the correct normalisation
(weight `½` per mode, the `𝒬₁(z)` term folded in),

    `𝒦^Bog = ∑_k ½ [𝒜_k (n_k + n_{−k}) + ℬ_k (a_k a_{−k} + a_k† a_{−k}†) + 𝒞_k (a_k + a_k† + a_{−k} + a_{−k}†)]`

on the mode lattice `Work.BoseB4.RealFock m`.  `Work.BoseBoxFock.KzBogC` is the same
operator with every superposed mode replaced by its spectator image
(`F.a k ↦ annOfE (f k)`, `F.aDag k ↦ creOfE (f k)`, `F.nOp k ↦ nOpC (f k)`) on the
zero-condensate slice `FockCore (cfock (Excited m))`.  This module proves the transport
identity

    `split (𝒦^Bog y) = lift (KzBogC f E ρ) (split y)`,

the Bogoliubov row of the dictionary of `Work.BoseBoxFock.KafzHonest`.

## Structure of the proof

The row is a sum over the modes; each summand is a real-linear combination of three
operator shapes,

* `bogRowA1 = creOf (f k) ∘ annOf (f k) + creOf (f (−k)) ∘ annOf (f (−k))` (the `n`-pair),
* `bogRowA2 = annOf (f k) ∘ annOf (f (−k)) + creOf (f k) ∘ creOf (f (−k))` (the pair),
* `bogRowA3 = annOf (f k) + creOf (f k) + annOf (f (−k)) + creOf (f (−k))` (the linear term),

each of which transports (`split_bogRowA1`, `split_bogRowA2`, `split_bogRowA3`) to the
`lift` of the corresponding spectator operator by the dictionary lemmas
`split_creOf_annOf`, `ss_split_annOf_annOf`, `split_creOf_creOf`, `split_annOf`,
`split_creOf` of `Work.BoseBoxFock.KafzHonest` / `split_sandwiches`.

The three pieces are deliberately stated at the *canonical* types
(`RealFock m →ₗ[ℝ] RealFock m`, `cfock (Excited m) →ₗ[ℂ] cfock (Excited m)`) rather than
through the projections of the `FockData` structure: the projections carry the
structure's own (definitionally, but not syntactically equal) instances, and
`LinearMap.add_apply` / `lift_add` do not see through them.

The per-mode identity `split_kzBogRow` is then summed over the modes with the weighting
lemma `Work.BoseBoxFock.ss_lift_weighted` (`s = univ`, weights `½`), and the two
`∑`-expressions are identified with `KzBogFS` and `KzBogC` definitionally.
-/

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {m : ℕ} [NeZero m]
variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## 1. The per-mode pieces -/

/-- The `n`-pair piece `creOf (f k) ∘ annOf (f k) + creOf (f (−k)) ∘ annOf (f (−k))`
of the Bogoliubov row. -/
noncomputable def bogRowA1 (f : Mode → Fin m → ℝ) (k : Mode) : RealFock m →ₗ[ℝ] RealFock m :=
  (creOf m (f k)).comp (annOf m (f k)) + (creOf m (f (-k))).comp (annOf m (f (-k)))

/-- The pair piece `annOf (f k) ∘ annOf (f (−k)) + creOf (f k) ∘ creOf (f (−k))`. -/
noncomputable def bogRowA2 (f : Mode → Fin m → ℝ) (k : Mode) : RealFock m →ₗ[ℝ] RealFock m :=
  (annOf m (f k)).comp (annOf m (f (-k))) + (creOf m (f k)).comp (creOf m (f (-k)))

/-- The linear piece `annOf (f k) + creOf (f k) + annOf (f (−k)) + creOf (f (−k))`. -/
noncomputable def bogRowA3 (f : Mode → Fin m → ℝ) (k : Mode) : RealFock m →ₗ[ℝ] RealFock m :=
  annOf m (f k) + creOf m (f k) + annOf m (f (-k)) + creOf m (f (-k))

/-- The spectator image of `bogRowA1`. -/
noncomputable def bogRowB1 (f : Mode → Fin m → ℝ) (k : Mode) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  nOpC (f k) + nOpC (f (-k))

/-- The spectator image of `bogRowA2`. -/
noncomputable def bogRowB2 (f : Mode → Fin m → ℝ) (k : Mode) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  (annOfE (f k)).comp (annOfE (f (-k))) + (creOfE (f k)).comp (creOfE (f (-k)))

/-- The spectator image of `bogRowA3`. -/
noncomputable def bogRowB3 (f : Mode → Fin m → ℝ) (k : Mode) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  annOfE (f k) + creOfE (f k) + annOfE (f (-k)) + creOfE (f (-k))

/-- The per-mode Bogoliubov operator (`Work.BoseBoxFock.KzBogFS`'s summand) at the
canonical type. -/
noncomputable def kzBogRowA (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ)
    (k : Mode) : RealFock m →ₗ[ℝ] RealFock m :=
  (E.tau k + ρ * E.W1 k) • bogRowA1 f k + (ρ * E.W1 k) • bogRowA2 f k
    + ((ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3)) • bogRowA3 f k

/-- The spectator form of the per-mode Bogoliubov operator (`KzBogC`'s summand). -/
noncomputable def kzBogRowB (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ)
    (k : Mode) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  (((E.tau k + ρ * E.W1 k : ℝ)) : ℂ) • bogRowB1 f k + (((ρ * E.W1 k : ℝ)) : ℂ) • bogRowB2 f k
    + ((((ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3) : ℝ)) : ℂ) • bogRowB3 f k

/-! ## 2. The dictionary lemmas for the three shapes -/

omit [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode] in
/-- `split` of `creOf φ ∘ creOf ψ` (`φ 0 = ψ 0 = 0`). -/
theorem split_creOf_creOf (f : Mode → Fin m → ℝ) (hφ : ∀ k : Mode, f k 0 = 0) (i j : Mode)
    (y : RealFock m) :
    split (creOf m (f i) (creOf m (f j) y))
      = lift ((creOfE (f i)).comp (creOfE (f j))) (split y) := by
  rw [split_creOf (f i) (hφ i), split_creOf (f j) (hφ j), lift_comp, LinearMap.comp_apply]

omit [Fintype Mode] [DecidableEq Mode] in
/-- The `n`-pair transports. -/
theorem split_bogRowA1 (f : Mode → Fin m → ℝ) (hφ : ∀ k : Mode, f k 0 = 0) (k : Mode)
    (y : RealFock m) :
    split (bogRowA1 f k y) = lift (bogRowB1 f k) (split y) := by
  rw [bogRowA1, bogRowB1, LinearMap.add_apply, map_add, LinearMap.comp_apply,
    LinearMap.comp_apply]
  rw [split_creOf_annOf (f k) (f k) (hφ k) (hφ k) y,
    split_creOf_annOf (f (-k)) (f (-k)) (hφ (-k)) (hφ (-k)) y,
    ← LinearMap.add_apply, ← lift_add]
  try rfl

omit [Fintype Mode] [DecidableEq Mode] in
/-- The pair transports. -/
theorem split_bogRowA2 (f : Mode → Fin m → ℝ) (hφ : ∀ k : Mode, f k 0 = 0) (k : Mode)
    (y : RealFock m) :
    split (bogRowA2 f k y) = lift (bogRowB2 f k) (split y) := by
  rw [bogRowA2, bogRowB2, LinearMap.add_apply, map_add, LinearMap.comp_apply,
    LinearMap.comp_apply]
  rw [ss_split_annOf_annOf (f k) (f (-k)) (hφ k) (hφ (-k)) y,
    split_creOf_creOf f hφ k (-k) y,
    ← LinearMap.add_apply, ← lift_add]
  try rfl

omit [Fintype Mode] [DecidableEq Mode] in
/-- The linear term transports. -/
theorem split_bogRowA3 (f : Mode → Fin m → ℝ) (hφ : ∀ k : Mode, f k 0 = 0) (k : Mode)
    (y : RealFock m) :
    split (bogRowA3 f k y) = lift (bogRowB3 f k) (split y) := by
  rw [bogRowA3, bogRowB3, LinearMap.add_apply, LinearMap.add_apply, LinearMap.add_apply,
    map_add, map_add, map_add]
  rw [split_annOf (f k) (hφ k) y, split_creOf (f k) (hφ k) y,
    split_annOf (f (-k)) (hφ (-k)) y, split_creOf (f (-k)) (hφ (-k)) y,
    ← LinearMap.add_apply, ← LinearMap.add_apply, ← LinearMap.add_apply,
    ← lift_add, ← lift_add, ← lift_add]
  try rfl

/-! ## 3. The per-mode identity -/

omit [DecidableEq Mode] in
/-- **The per-mode Bogoliubov identity**: the summand of `KzBogFS` at the mode `k`
transports to the summand of `KzBogC`. -/
theorem split_kzBogRow (f : Mode → Fin m → ℝ) (hφ : ∀ k : Mode, f k 0 = 0)
    (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) (k : Mode) (y : RealFock m) :
    split (kzBogRowA f E ρ k y) = lift (kzBogRowB f E ρ k) (split y) := by
  rw [kzBogRowA, kzBogRowB, LinearMap.add_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    map_add, map_add, map_smul, map_smul, map_smul,
    split_bogRowA1 f hφ k y, split_bogRowA2 f hφ k y, split_bogRowA3 f hφ k y]
  rw [lift_add, lift_add, lift_smul, lift_smul, lift_smul,
    LinearMap.add_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    Complex.coe_smul, Complex.coe_smul, Complex.coe_smul]
  try rfl

/-! ## 4. The row -/

omit [NeZero m] in
/-- `KzBogFS` is the sum of its per-mode pieces (definitionally).  Stated at the applied
level so that the (definitionally equal, but not syntactically equal) instances of the
`FockData` structure never have to be re-elaborated under a coercion. -/
theorem KzBogFS_apply (B : Work.BoseB4.BoxData) {ℓ : ℝ}
    (kmom : Mode → EuclideanSpace ℝ (Fin 3)) (hkmom : ∀ i : Mode, kmom (-i) = -kmom i)
    (f : Mode → Fin m → ℝ)
    (hf : ∀ i j : Mode, gram (f i) (f j)
      = Work.BoseB7.ccrKernel ℓ B.hatChiSq B.hatChi (kmom i) (kmom j))
    (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) (y : RealFock m) :
    KzBogFS (boxFockData B kmom hkmom m f hf) E ρ y
      = (∑ k : Mode, (1 / 2 : ℝ) • kzBogRowA f E ρ k) y := rfl

omit [DecidableEq Mode] in
/-- `KzBogC` is the sum of its per-mode pieces (definitionally). -/
theorem KzBogC_eq_sum (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) :
    KzBogC f E ρ = ∑ k : Mode, ((1 / 2 : ℝ) : ℂ) • kzBogRowB f E ρ k := rfl

theorem split_KzBogFS_box {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (B : Work.BoseB4.BoxData) {ℓ : ℝ} (kmom : Mode → EuclideanSpace ℝ (Fin 3))
    (hkmom : ∀ i : Mode, kmom (-i) = -kmom i) (f : Mode → Fin m → ℝ)
    (hf : ∀ i j : Mode, Work.BoseB4.gram (f i) (f j)
      = Work.BoseB7.ccrKernel ℓ B.hatChiSq B.hatChi (kmom i) (kmom j))
    (hφ : ∀ k : Mode, f k 0 = 0) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) :
    ∀ y : Work.BoseB4.RealFock m,
      Work.BoseB4.split (Work.BoseBoxFock.KzBogFS (Work.BoseB4.boxFockData B kmom hkmom m f hf) E ρ y)
        = Work.BoseB4.lift (Work.BoseBoxFock.KzBogC f E ρ) (Work.BoseB4.split y) := by
  intro y
  rw [KzBogFS_apply B kmom hkmom f hf E ρ y,
    ss_lift_weighted (Finset.univ : Finset Mode) (fun _ => (1 / 2 : ℝ)) (kzBogRowA f E ρ)
      (kzBogRowB f E ρ) (fun k _ y => split_kzBogRow f hφ E ρ k y) y,
    KzBogC_eq_sum f E ρ]

end Work.BoseBoxFock

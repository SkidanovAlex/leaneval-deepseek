import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs8.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

/-- **The marginal collapse.**  For a measurable `A ⊆ acube ℓ` and any kernel `φ`, the
integral of `1_A(y)1_A(z)φ(y,z)` over `acube ℓ × acube ℓ` collapses to the integral of `φ`
over `A ×ˢ A`.  (Nothing is assumed about `φ`: both sides are set integrals of the same
function against measures that agree on `A ×ˢ A`.) -/
theorem pairCollapse {ℓ : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ acube ℓ)
    (φ : (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → ℝ) :
    (∫ p, (A.indicator (fun _ => (1:ℝ)) p.1 * A.indicator (fun _ => (1:ℝ)) p.2) * φ p.1 p.2
        ∂((volume.restrict (acube ℓ)).prod (volume.restrict (acube ℓ))))
      = ∫ p in A ×ˢ A, φ p.1 p.2 := by
  have hpt : (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        (A.indicator (fun _ => (1:ℝ)) p.1 * A.indicator (fun _ => (1:ℝ)) p.2) * φ p.1 p.2)
      = (A ×ˢ A).indicator (fun q => φ q.1 q.2) := by
    funext p
    rcases p with ⟨y, z⟩
    by_cases hy : y ∈ A <;> by_cases hz : z ∈ A
    · simp [Set.mem_prod, hy, hz]
    · simp [Set.mem_prod, hy, hz]
    · simp [Set.mem_prod, hy, hz]
    · simp [Set.mem_prod, hy, hz]
  rw [hpt]
  have hmeas : MeasurableSet (A ×ˢ A) := hA.prod hA
  rw [integral_indicator
    (f := fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => φ q.1 q.2) hmeas]
  congr 1
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)))
      = (volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
          (volume : Measure (EuclideanSpace ℝ (Fin 3))) := Measure.volume_eq_prod _ _
  rw [Measure.prod_restrict, hvol]
  rw [Measure.restrict_restrict hmeas]
  congr 1
  exact Set.inter_eq_left.mpr (Set.prod_mono hAc hAc)

/-- The flat collapse: the volume of `A ×ˢ A` is `volA²` when `volA = |A|`. -/
theorem flatCollapse {volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hvolA : volA = (volume A).toReal) :
    (∫ p in A ×ˢ A, (1:ℝ)) = volA ^ 2 := by
  rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def,
    MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod,
    ENNReal.toReal_mul, hvolA]
  ring

/-- The square of the product of two `0/1`-indicators is the product itself. -/
theorem ind_pair_mul_self (A : Set (EuclideanSpace ℝ (Fin 3)))
    (y z : EuclideanSpace ℝ (Fin 3)) :
    (A.indicator (fun _ => (1:ℝ)) y * A.indicator (fun _ => (1:ℝ)) z)^2
      = A.indicator (fun _ => (1:ℝ)) y * A.indicator (fun _ => (1:ℝ)) z := by
  by_cases hy : y ∈ A
  · by_cases hz : z ∈ A
    · simp [Set.indicator_of_mem hy, Set.indicator_of_mem hz]
    · simp [Set.indicator_of_mem hy, Set.indicator_of_notMem hz]
  · by_cases hz : z ∈ A
    · simp [Set.indicator_of_notMem hy, Set.indicator_of_mem hz]
    · simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hz]

/-- **The double-projection factorization.**  For distinct slots `i ≠ j` the doubly
projected state is the product of the two slot indicators and of the `A`-double mean of
the state over the two slots (evaluated with those slots overwritten). -/
theorem boxPInd_pair_factor {N : ℕ} (volA : ℝ)
    (A : Set (EuclideanSpace ℝ (Fin 3))) (i j : Fin N) (hij : i ≠ j)
    (Φ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) :
    Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
      = (1/volA) * (1/volA) * (A.indicator (fun _ => (1:ℝ)) (x i)
          * A.indicator (fun _ => (1:ℝ)) (x j))
        * (∫ y in A, ∫ z in A, Φ (Function.update (Function.update x i y) j z)) := by
  have key : ∀ y : EuclideanSpace ℝ (Fin 3),
      Work.UBBInputs8.boxPInd volA A j Φ (Function.update x i y)
      = (1/volA) * (∫ z in A, Φ (Function.update (Function.update x i y) j z))
          * A.indicator (fun _ => (1:ℝ)) (x j) := by
    intro y
    rw [Work.UBBInputs8.boxPInd, Function.update_of_ne hij.symm y x]
  have h1 : Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
      = (1/volA) * (∫ y in A, Work.UBBInputs8.boxPInd volA A j Φ (Function.update x i y))
          * A.indicator (fun _ => (1:ℝ)) (x i) := rfl
  rw [h1, MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall key)]
  rw [show (fun y : EuclideanSpace ℝ (Fin 3) =>
        (1/volA) * (∫ z in A, Φ (Function.update (Function.update x i y) j z))
          * A.indicator (fun _ => (1:ℝ)) (x j))
      = fun y : EuclideanSpace ℝ (Fin 3) =>
          ((1/volA) * A.indicator (fun _ => (1:ℝ)) (x j))
          * (∫ z in A, Φ (Function.update (Function.update x i y) j z)) from
    funext fun y => by ring]
  rw [MeasureTheory.integral_const_mul]
  ring

/-- **The two-slot mean is a function of the rest.**  The `A`-double mean of `Φ` with the
two distinguished slots overwritten is unchanged when the inserted values vary. -/
theorem pairMean_const {p : ℕ} (A : Set (EuclideanSpace ℝ (Fin 3)))
    (i : Fin (p+2)) (j' : Fin (p+1)) {j : Fin (p+2)} (hj' : i.succAbove j' = j)
    (Φ : Submission.BoseGases.X (p+2) → ℝ)
    (y z : EuclideanSpace ℝ (Fin 3)) (r2 : Submission.BoseGases.X p) :
    (∫ a in A, ∫ b in A,
        Φ (Function.update (Function.update (ins2 i j' y z r2) i a) j b))
      = (∫ a in A, ∫ b in A,
        Φ (Function.update (Function.update (rest2 i j' r2) i a) j b)) := by
  have e1 : ∀ a b : EuclideanSpace ℝ (Fin 3),
      Function.update (Function.update (ins2 i j' y z r2) i a) j b = ins2 i j' a b r2 := by
    intro a b
    rw [ins2_update_i, ← hj', ins2_update_succ]
  have e2 : ∀ a b : EuclideanSpace ℝ (Fin 3),
      Function.update (Function.update (rest2 i j' r2) i a) j b = ins2 i j' a b r2 := by
    intro a b
    dsimp only [rest2]
    rw [ins2_update_i, ← hj', ins2_update_succ]
  rw [show (fun a : EuclideanSpace ℝ (Fin 3) =>
          ∫ b in A, Φ (Function.update (Function.update (ins2 i j' y z r2) i a) j b))
      = fun a : EuclideanSpace ℝ (Fin 3) => ∫ b in A, Φ (ins2 i j' a b r2) from
    funext fun a => by
      apply integral_congr_ae; filter_upwards with b; rw [e1 a b]]
  rw [show (fun a : EuclideanSpace ℝ (Fin 3) =>
          ∫ b in A, Φ (Function.update (Function.update (rest2 i j' r2) i a) j b))
      = fun a : EuclideanSpace ℝ (Fin 3) => ∫ b in A, Φ (ins2 i j' a b r2) from
    funext fun a => by
      apply integral_congr_ae; filter_upwards with b; rw [e2 a b]]

end Work.BoseFixB1S

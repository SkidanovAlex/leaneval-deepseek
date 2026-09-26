import Mathlib
import Submission.Work.PTCert.GlueDefs

/-! Guidance from the project lead (the requester):

Context: `Submission/Work/PTCert/GlueDefs.lean` (definitions + Props; read it first) glues the
kernel-checked certificate data to the proved generic chain (`Chain.lean`, `Math.lean`,
`Interfaces.lean`; all their Props are already PROVED: avgPrinciple, labelPrinciple, gramSOS,
avgGram, avgMatInvariant, rowFormula, psdOfBlock, psdSignedPerm, ldlScaledPrinciple,
twistedFourierCriterion, residualAbsorption, letterAction, signCodes8, sigmaGroupFacts, modelSound,
permCheckKSound, ...). The design note is `NOTES_LEAD_glue.md` at the workspace root.
Do NOT change GlueDefs.lean. If the statement is false, `declare_false` with a concrete counterexample.
Put helper lemmas in your own file or under `Submission/Work/PTCert/<yourLemma>/`.
Route (pure algebra, no representation theory).
1. `gramForm f P = Σ_x Σ_y P x y • of((f x)⁻¹ * f y)`; split the outer sum by `rowOf x = r`
   (Finset.sum_fiberwise).
2. Fix x with rowOf x = r; choose σ ∈ Sg with act σ (x0 r) = x (hypothesis). Reindex the inner sum by
   y = act σ y' (act σ bijective ⇒ Equiv via Equiv.ofBijective, Fintype.sum_equiv). Then
   P x y = P (act σ (x0 r)) (act σ y') = P (x0 r) y' and, by ConjAction (f (act σ i) = σ f i σ⁻¹),
   (f x)⁻¹ f y = σ ((f (x0 r))⁻¹ f y') σ⁻¹. So the inner sum is `of σ * Z_r * of σ⁻¹` with
   Z_r = Σ_y' P (x0 r) y' • of((f (x0 r))⁻¹ f y')  (MonoidAlgebra.of is multiplicative; smul commutes).
3. `conjAvg Sg (of σ * Z * of σ⁻¹) = conjAvg Sg Z` for σ ∈ Sg: reindex s ↦ s * σ in the sum over Sg
   (a bijection of Sg because Sg is a finite subgroup: IsFinSubgroup gives closure/inverses).
4. conjAvg is additive and ℝ-linear (it is a finite sum of `of s * _ * of s⁻¹`), so conjAvg of the
   whole sum = Σ_r (card of the fibre) • conjAvg Z_r = conjAvg (Σ_r card • Z_r).
-/

namespace Work.PTCert

open Submission.PTCert
open scoped BigOperators

/-! ## Elementary lemmas about `conjAvg` and pushing conjugators through a sum -/

/-- Pushing a conjugating pair `a (·) d` through a scalar-weighted finite sum. -/
private lemma pullOut {G : Type} [Group G] {κ : Type} (I : Finset κ) (c : κ → ℝ)
    (a d : MonoidAlgebra ℝ G) (b : κ → MonoidAlgebra ℝ G) :
    ∑ i ∈ I, c i • (a * b i * d) = a * (∑ i ∈ I, c i • b i) * d := by
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_smul_comm, smul_mul_assoc]

/-- `conjAvg` is additive in its second argument. -/
private lemma cA_add {G : Type} [Group G] (Sg : Finset G) (x y : MonoidAlgebra ℝ G) :
    conjAvg Sg (x + y) = conjAvg Sg x + conjAvg Sg y := by
  simp only [conjAvg, mul_add, add_mul, Finset.sum_add_distrib]

/-- `conjAvg` is `ℝ`-linear in its second argument. -/
private lemma cA_smul {G : Type} [Group G] (Sg : Finset G) (a : ℝ) (x : MonoidAlgebra ℝ G) :
    conjAvg Sg (a • x) = a • conjAvg Sg x := by
  simp only [conjAvg]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro s _
  rw [mul_smul_comm, smul_mul_assoc]

/-- `conjAvg` distributes over a finite sum. -/
private lemma cA_sum {G : Type} [Group G] {κ : Type} (Sg : Finset G) (s : Finset κ)
    (F : κ → MonoidAlgebra ℝ G) :
    conjAvg Sg (∑ i ∈ s, F i) = ∑ i ∈ s, conjAvg Sg (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [conjAvg]
  | insert a t ha ih => rw [Finset.sum_insert ha, cA_add, ih, Finset.sum_insert ha]

/-- **Reindexing by a left-conjugator.**  For `s ∈ Sg` with `Sg` a finite subgroup, the
`Sg`-average of `of s⁻¹ * x * of s` equals that of `x`. -/
private lemma cA_conj_inv {G : Type} [Group G] (Sg : Finset G) (hSg : IsFinSubgroup Sg)
    {s : G} (hs : s ∈ Sg) (x : MonoidAlgebra ℝ G) :
    conjAvg Sg (MonoidAlgebra.of ℝ G s⁻¹ * x * MonoidAlgebra.of ℝ G s) = conjAvg Sg x := by
  simp only [conjAvg]
  refine Finset.sum_nbij' (fun u => u * s⁻¹) (fun v => v * s) ?_ ?_ ?_ ?_ ?_
  · intro u hu; exact hSg.2.1 u hu s⁻¹ (hSg.2.2 s hs)
  · intro v hv; exact hSg.2.1 v hv s hs
  · intro u _; simp [mul_assoc]
  · intro v _; simp [mul_assoc]
  · intro u _
    rw [mul_inv_rev, inv_inv, map_mul, map_mul]
    noncomm_ring

/-- **(GL2) Orbit decomposition of a Gram form.** -/
theorem orbitDecomp : OrbitDecomp := by
  intro G _ _ Sg hSg ι _ _ f act hact hbij P hP R _ _ x0 rowOf hx0
  classical
  -- The row-orbit sums `Z r`, and the cardinalities of the row classes.
  let Z : R → MonoidAlgebra ℝ G :=
    fun r => ∑ y, P (x0 r) y • MonoidAlgebra.of ℝ G ((f (x0 r))⁻¹ * f y)
  let cnt : R → Nat := fun r => (Finset.univ.filter (fun x => rowOf x = r)).card
  -- Every row sum is a conjugate of the corresponding `Z r`.
  have innerEq : ∀ (x : ι) (r : R) (σ : G), σ ∈ Sg → act σ (x0 r) = x →
      (∑ y, P x y • MonoidAlgebra.of ℝ G ((f x)⁻¹ * f y)) =
      MonoidAlgebra.of ℝ G σ * (Z r) * MonoidAlgebra.of ℝ G σ⁻¹ := by
    intro x r σ hσ hactσ
    -- reindex the inner sum along the bijection `act σ`
    rw [← Fintype.sum_bijective (act σ) (hbij σ hσ)
      (fun y' => P x (act σ y') • MonoidAlgebra.of ℝ G ((f x)⁻¹ * f (act σ y')))
      (fun y => P x y • MonoidAlgebra.of ℝ G ((f x)⁻¹ * f y)) (fun _ => rfl)]
    have hterm : ∀ y', P x (act σ y') • MonoidAlgebra.of ℝ G ((f x)⁻¹ * f (act σ y'))
        = P (x0 r) y' • (MonoidAlgebra.of ℝ G σ * MonoidAlgebra.of ℝ G ((f (x0 r))⁻¹ * f y')
            * MonoidAlgebra.of ℝ G σ⁻¹) := by
      intro y'
      have hfx : f x = σ * f (x0 r) * σ⁻¹ := by rw [← hactσ]; exact hact.2 σ hσ (x0 r)
      have hfy : f (act σ y') = σ * f y' * σ⁻¹ := hact.2 σ hσ y'
      have hxy : P x (act σ y') = P (x0 r) y' := by rw [← hactσ, hP σ hσ (x0 r) y']
      have hA : (f x)⁻¹ * f (act σ y') = σ * ((f (x0 r))⁻¹ * f y') * σ⁻¹ := by
        rw [hfx, hfy]; group
      rw [hxy, hA, map_mul, map_mul]
    rw [Finset.sum_congr rfl (fun y' _ => hterm y')]
    rw [pullOut Finset.univ (fun y => P (x0 r) y) (MonoidAlgebra.of ℝ G σ)
      (MonoidAlgebra.of ℝ G σ⁻¹) (fun y => MonoidAlgebra.of ℝ G ((f (x0 r))⁻¹ * f y))]
  have hxstep : ∀ x : ι,
      conjAvg Sg (∑ y, P x y • MonoidAlgebra.of ℝ G ((f x)⁻¹ * f y))
        = conjAvg Sg (Z (rowOf x)) := by
    intro x
    obtain ⟨σ, hσ, hσx⟩ := hx0 x
    rw [innerEq x (rowOf x) σ hσ hσx]
    have h2 : conjAvg Sg (MonoidAlgebra.of ℝ G σ⁻¹⁻¹ * Z (rowOf x) * MonoidAlgebra.of ℝ G σ⁻¹)
        = conjAvg Sg (Z (rowOf x)) :=
      cA_conj_inv Sg hSg (hSg.2.2 σ hσ) (Z (rowOf x))
    simpa using h2
  -- Group the rows by their class, using `Finset.sum_fiberwise` and constant sums.
  have hfib : (∑ x : ι, conjAvg Sg (Z (rowOf x)))
      = ∑ r : R, (cnt r : ℝ) • conjAvg Sg (Z r) := by
    rw [← Finset.sum_fiberwise Finset.univ rowOf (fun x : ι => conjAvg Sg (Z (rowOf x)))]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    have hconst : (∑ i ∈ Finset.univ.filter (fun i => rowOf i = r), conjAvg Sg (Z (rowOf i)))
        = ∑ i ∈ Finset.univ.filter (fun i => rowOf i = r), conjAvg Sg (Z r) :=
      Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2])
    rw [hconst, Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have hlast : conjAvg Sg (∑ r : R, (cnt r : ℝ) • Z r)
      = ∑ r : R, (cnt r : ℝ) • conjAvg Sg (Z r) := by
    rw [cA_sum]
    exact Finset.sum_congr rfl (fun r _ => cA_smul Sg (cnt r) (Z r))
  calc conjAvg Sg (gramForm f P)
      = conjAvg Sg (∑ x, ∑ y, P x y • MonoidAlgebra.of ℝ G ((f x)⁻¹ * f y)) := by
        simp only [gramForm]
    _ = ∑ x, conjAvg Sg (∑ y, P x y • MonoidAlgebra.of ℝ G ((f x)⁻¹ * f y)) :=
        cA_sum Sg Finset.univ _
    _ = ∑ x, conjAvg Sg (Z (rowOf x)) := Finset.sum_congr rfl (fun x _ => hxstep x)
    _ = ∑ r : R, (cnt r : ℝ) • conjAvg Sg (Z r) := hfib
    _ = conjAvg Sg (∑ r : R, (cnt r : ℝ) • Z r) := hlast.symm

end Work.PTCert

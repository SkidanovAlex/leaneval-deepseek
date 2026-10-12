import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Submission.Work.BoseFixB1.BoxD1Pair
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter Function
open scoped Topology Real BigOperators ENNReal ContDiff Pointwise

namespace Work.BoseFixB1

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-!
## `boxPairDensSum_schwartz_of_fibre`

The relative-coordinate box pair density

`boxPairDens volA ℓ A χ Φ i j u = ∫ z in A, χ (z + u) * χ z * boxPairFibreFun volA ℓ A Φ i j (z + u) z`

is, for every ordered pair `i ≠ j`, a smooth function of `u` (differentiation under the integral
sign, with the compact box `acube ℓ` as the surrogate integration domain: the integrand vanishes
off `A` since `χ` does) and has compact support (the integrand can only be nonzero when
`z + u ∈ tsupport χ` with `z ∈ acube ℓ`, i.e. `u ∈ tsupport χ + (-acube ℓ)`).  A finite sum of
smooth compactly supported functions is a Schwartz function.

The two general facts used are isolated below; they are the parametric-integral toolbox for a
*kernel vanishing in the relative variable off `A`* (`contDiff_setIntegral_isCompact` only applies
to compact domains, hence the replacement `A ↝ acube ℓ`).
-/

/-- **Smoothness of a shifted parametric integral.**  If the kernel `K` vanishes in its second
slot outside `A`, and `A` is contained in a compact set `k`, then `u ↦ ∫ z in A, K (z + u) z` is
smooth as soon as `K` is (the integral over `A` may be replaced by the integral over the compact
set `k`, where differentiation under the integral sign is available). -/
theorem boxPair_contDiff_setIntegral_shift {A k : Set (EuclideanSpace ℝ (Fin 3))}
    {K : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hK : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry K)) (hk : IsCompact k) (hAk : A ⊆ k)
    (h0 : ∀ y z, z ∉ A → K y z = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun u => ∫ z in A, K (z + u) z) := by
  have hEq : (fun u => ∫ z in A, K (z + u) z) = fun u => ∫ z in k, K (z + u) z := by
    funext u
    exact (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hk.measurableSet hAk
      (fun z hz => h0 (z + u) z hz.2)).symm
  rw [hEq]
  refine Commons.Analysis.Calculus.contDiff_setIntegral_isCompact
    (P := EuclideanSpace ℝ (Fin 3)) (F := fun u z => K (z + u) z) (n := (⊤ : ℕ∞)) hk ?_
  have hfun : (Function.uncurry (fun u z : EuclideanSpace ℝ (Fin 3) => K (z + u) z))
      = fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => K (q.2 + q.1) q.2 := by
    ext q
    simp only [Function.uncurry]
  rw [hfun]
  have hT : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => (q.2 + q.1, q.2)) := by
    fun_prop
  exact hK.comp hT

/-- **Compact support of a shifted parametric integral.**  If every pair `(z, u)` on which the
kernel does not vanish has `u` in a fixed compact set `U`, then `u ↦ ∫ z in A, K (z + u) z` has
compact support. -/
theorem boxPair_hasCompactSupport_setIntegral_shift {A U : Set (EuclideanSpace ℝ (Fin 3))}
    {K : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ} (hU : IsCompact U)
    (hcover : ∀ u, (∃ z ∈ A, K (z + u) z ≠ 0) → u ∈ U) :
    HasCompactSupport (fun u => ∫ z in A, K (z + u) z) :=
  HasCompactSupport.intro hU fun u hu =>
    setIntegral_eq_zero_of_forall_eq_zero fun z hz => by
      by_contra hz'
      exact hu (hcover u ⟨z, hz, hz'⟩)

theorem boxPairDensSum_schwartz_of_fibre {N : ℕ} {ℓ volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvolpos : 0 < volA)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχs : HasCompactSupport χ) (hχsupp : ∀ z, z ∉ A → χ z = 0)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hfib : ∀ (i j : Fin (N + 2)), i ≠ j → ContDiff ℝ (⊤ : ℕ∞)
      (Function.uncurry (fun y z : EuclideanSpace ℝ (Fin 3) =>
        χ y * χ z * Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ i j y z))) :
    ∃ g : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ,
      ∀ u, g u = ((Work.BoseFixB1.boxPairDensSum volA ℓ A χ Φ u : ℝ) : ℂ) := by
  classical
  have hkc : IsCompact (Submission.BoseGases.acube ℓ) := Submission.BoseGases.acube_compact hℓ
  -- the compact set in which the relative coordinate must lie
  have hUc : IsCompact (tsupport χ + -(Submission.BoseGases.acube ℓ)) :=
    (show IsCompact (tsupport χ) from hχs).add hkc.neg
  have hcoverχ : ∀ u, (∃ z ∈ A, χ (z + u) ≠ 0) →
      u ∈ tsupport χ + -(Submission.BoseGases.acube ℓ) := by
    rintro u ⟨z, hzA, hχ0⟩
    exact Set.mem_add.mpr ⟨z + u, subset_tsupport χ (Function.mem_support.mpr hχ0),
      -z, by simpa only [Set.mem_neg, neg_neg] using hAc hzA, by abel⟩
  -- one ordered pair at a time
  have hpair : ∀ p ∈ Submission.BoseGases.pairSet (N + 2),
      ContDiff ℝ (⊤ : ℕ∞) (boxPairDens volA ℓ A χ Φ p.1 p.2) ∧
        HasCompactSupport (boxPairDens volA ℓ A χ Φ p.1 p.2) := by
    intro p hp
    have hne : p.1 ≠ p.2 := by simpa [Submission.BoseGases.pairSet] using hp
    have hKc : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry
        (fun y z : EuclideanSpace ℝ (Fin 3) =>
          χ y * χ z * boxPairFibreFun volA ℓ A Φ p.1 p.2 y z)) := hfib p.1 p.2 hne
    have hden : boxPairDens volA ℓ A χ Φ p.1 p.2
        = fun u => ∫ z in A, (fun y z : EuclideanSpace ℝ (Fin 3) =>
            χ y * χ z * boxPairFibreFun volA ℓ A Φ p.1 p.2 y z) (z + u) z := rfl
    constructor
    · rw [hden]
      exact boxPair_contDiff_setIntegral_shift (A := A)
        (K := fun y z : EuclideanSpace ℝ (Fin 3) =>
          χ y * χ z * boxPairFibreFun volA ℓ A Φ p.1 p.2 y z)
        hKc hkc hAc (fun y z hz => by simp [hχsupp z hz])
    · rw [hden]
      refine boxPair_hasCompactSupport_setIntegral_shift (A := A)
        (K := fun y z : EuclideanSpace ℝ (Fin 3) =>
          χ y * χ z * boxPairFibreFun volA ℓ A Φ p.1 p.2 y z) hUc ?_
      rintro u ⟨z, hzA, hz⟩
      exact hcoverχ u ⟨z, hzA, fun h0 => hz (by simp [h0])⟩
  -- the finite sum over the ordered pairs is smooth
  have hsumCD : ContDiff ℝ (⊤ : ℕ∞)
      (fun u => ∑ p ∈ Submission.BoseGases.pairSet (N + 2),
        boxPairDens volA ℓ A χ Φ p.1 p.2 u) :=
    ContDiff.sum fun p hp => (hpair p hp).1
  have hCD : ContDiff ℝ (⊤ : ℕ∞) (boxPairDensSum volA ℓ A χ Φ) := by
    rw [show boxPairDensSum volA ℓ A χ Φ
        = fun u => ∑ p ∈ Submission.BoseGases.pairSet (N + 2),
            boxPairDens volA ℓ A χ Φ p.1 p.2 u from rfl]
    exact hsumCD
  -- ... and has compact support
  have hCS : HasCompactSupport (boxPairDensSum volA ℓ A χ Φ) :=
    HasCompactSupport.intro hUc fun u hu => by
      simp only [boxPairDensSum]
      refine Finset.sum_eq_zero fun p hp => ?_
      simp only [boxPairDens]
      refine setIntegral_eq_zero_of_forall_eq_zero fun z hz => ?_
      have hχ0 : χ (z + u) = 0 := by
        by_contra h
        exact hu (hcoverχ u ⟨z, hz, h⟩)
      simp [hχ0]
  -- complexify and read off the Schwartz function
  have hSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun u => ((boxPairDensSum volA ℓ A χ Φ u : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hCD
  have hCS' : HasCompactSupport
      (fun u => ((boxPairDensSum volA ℓ A χ Φ u : ℝ) : ℂ)) :=
    hCS.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  exact ⟨hCS'.toSchwartzMap hSmooth, fun u => rfl⟩

end Work.BoseFixB1

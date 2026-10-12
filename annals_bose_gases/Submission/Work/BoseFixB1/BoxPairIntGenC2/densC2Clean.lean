import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxPairIntGenC2.fibreFactorFixed
import Submission.Work.BoseFixB1.BoxPairIntGenC2.fibreFreeContDiffP
import Submission.Work.BoseFixB1.boxPairDensSum_schwartz_of_fibre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.BoxPairIntGenC2.boxPairDensSum_contDiff_two`

The relative-coordinate box pair density

    `boxPairDensSum volA ℓ A χ Ψ u
       = ∑_{i≠j} ∫_{z∈A} χ(z+u)·χ z·boxPairFibreFun … i j (z+u) z`

is twice continuously differentiable in `u` when the window `χ` is only twice differentiable
(and `Ψ` is smooth), and it is compactly supported.

The point is that the peeled box pair fibre of `Work.BoseFixB1.boxPairFibreFun` carries the two
box indicators `1_A` of the *distinguished* slots.  These are not smooth, but in the density they
are absorbed by the window `χ`: since `χ` vanishes off `A` (`hχsupp`), one has
`χ w · 1_A w = χ w` for every `w`, and the two indicators sit exactly on the two factors
`χ (z+u)`, `χ z`.  What remains is the indicator-free fibre `boxPairFibreFree`
(`BoxPairIntGenC2/Defs.lean`), which is jointly smooth in its two arguments
(`BoxPairIntGenC2.fibreFreeContDiff`), the factorisation being
`BoxPairIntGenC2.fibreFactor`.

This is the `C²` version of `Work.BoseFixB1.boxPairDensSum_schwartz` (which needs `ContDiff ⊤ χ`),
and the smoothness input `P5` of the route note
`Submission/Work/BoseFixB1/FINDING_boxPairIntGenC2_route.md` for the `C²`-window box pairing
identity `Work.BoseFixB1.boxPairIntGenC2`.
-/

noncomputable section

open MeasureTheory
open scoped Pointwise

namespace Work.BoseFixB1.BoxPairIntGenC2

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- **Compact support of the box pair density.**  If the window `χ` vanishes off `A` and
`A ⊆ acube ℓ`, then `u ↦ boxPairDensSum volA ℓ A χ Ψ u` can only be nonzero when
`z + u ∈ tsupport χ` for some `z ∈ acube ℓ`, i.e. `u ∈ tsupport χ + (-(acube ℓ))`, a compact
set.  (No smoothness of `χ` or of `Ψ` is used.) -/
theorem boxPairDensSum_cs {N : ℕ} {ℓ volA : ℝ} {A : Set E3}
    (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {χ : E3 → ℝ} (hχs : HasCompactSupport χ) (hχsupp : ∀ z, z ∉ A → χ z = 0)
    (Ψ : Submission.BoseGases.X (N + 2) → ℝ) :
    HasCompactSupport (Work.BoseFixB1.boxPairDensSum volA ℓ A χ Ψ) := by
  classical
  -- the compact set in which the relative coordinate `u` must lie
  have hUc : IsCompact (tsupport χ + -(Submission.BoseGases.acube ℓ)) :=
    (show IsCompact (tsupport χ) from hχs).add (Submission.BoseGases.acube_compact hℓ).neg
  -- one ordered pair at a time
  have hpair : ∀ p ∈ Submission.BoseGases.pairSet (N + 2),
      HasCompactSupport (Work.BoseFixB1.boxPairDens volA ℓ A χ Ψ p.1 p.2) := by
    intro p _
    set K : E3 → E3 → ℝ :=
      fun y z => χ y * χ z * Work.BoseFixB1.boxPairFibreFun volA ℓ A Ψ p.1 p.2 y z with hKdef
    have hK0 : ∀ y z, z ∉ A → K y z = 0 := by
      intro y z hz
      rw [hKdef]
      simp [hχsupp z hz]
    have hden : Work.BoseFixB1.boxPairDens volA ℓ A χ Ψ p.1 p.2
        = fun u => ∫ z in A, K (z + u) z := by
      funext u
      simp only [Work.BoseFixB1.boxPairDens, hKdef]
    rw [hden]
    refine Work.BoseFixB1.boxPair_hasCompactSupport_setIntegral_shift (A := A) (K := K) hUc ?_
    rintro u ⟨z, hzA, hz⟩
    have hχne : χ (z + u) ≠ 0 := fun h0 => hz (by rw [hKdef]; simp [h0])
    exact Set.mem_add.mpr
      ⟨z + u, subset_tsupport χ (Function.mem_support.mpr hχne),
        -z, by simpa only [Set.mem_neg, neg_neg] using hAc hzA, by abel⟩
  -- the finite sum over all ordered pairs
  have hsumEq : Work.BoseFixB1.boxPairDensSum volA ℓ A χ Ψ
      = fun u => ∑ p ∈ Submission.BoseGases.pairSet (N + 2),
          Work.BoseFixB1.boxPairDens volA ℓ A χ Ψ p.1 p.2 u := rfl
  rw [hsumEq]
  have heq : (∑ p ∈ Submission.BoseGases.pairSet (N + 2),
        Work.BoseFixB1.boxPairDens volA ℓ A χ Ψ p.1 p.2)
      = fun u => ∑ p ∈ Submission.BoseGases.pairSet (N + 2),
        Work.BoseFixB1.boxPairDens volA ℓ A χ Ψ p.1 p.2 u := by
    funext u
    simp only [Finset.sum_apply]
  rw [← heq]
  exact HasCompactSupport.finset_sum fun p hp => hpair p hp

set_option maxHeartbeats 1000000 in
theorem boxPairDensSum_contDiff_two_clean {N : ℕ} {ℓ volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvolpos : 0 < volA)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : ContDiff ℝ 2 χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ A → χ z = 0)
    {Ψ : Submission.BoseGases.X (N + 2) → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    ContDiff ℝ 2 (Work.BoseFixB1.boxPairDensSum volA ℓ A χ Ψ)
      ∧ HasCompactSupport (Work.BoseFixB1.boxPairDensSum volA ℓ A χ Ψ) := by
  classical
  refine ⟨?_, boxPairDensSum_cs hℓ hAc hχs hχsupp Ψ⟩
  -- the window absorbs the two box indicators
  have hχind : ∀ w : E3, χ w * A.indicator (fun _ => (1:ℝ)) w = χ w := by
    intro w
    by_cases hw : w ∈ A
    · rw [Set.indicator_of_mem hw, mul_one]
    · rw [Set.indicator_of_notMem hw, mul_zero, hχsupp w hw]
  have htop2 : ((2:ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr le_top
  -- expand the finite sum over the ordered pairs
  rw [show Work.BoseFixB1.boxPairDensSum volA ℓ A χ Ψ
      = fun u => ∑ p ∈ Submission.BoseGases.pairSet (N + 2),
          Work.BoseFixB1.boxPairDens volA ℓ A χ Ψ p.1 p.2 u from rfl]
  refine ContDiff.sum (fun p hp => ?_)
  obtain ⟨i, j⟩ := p
  have hij : i ≠ j := by simpa [Submission.BoseGases.pairSet] using hp
  -- replace the (indicator-carrying) fibre by the indicator-free one
  have hstep1 : Work.BoseFixB1.boxPairDens volA ℓ A χ Ψ i j
      = fun u => ∫ z in A, χ (z + u) * χ z
          * Work.BoseFixB1.BoxPairIntGenC2.boxPairFibreFree volA ℓ A Ψ i
              (Submission.BoseGases.sucAboveInv i j hij) (z + u) z := by
    funext u
    rw [Work.BoseFixB1.boxPairDens]
    refine setIntegral_congr_fun hA (fun z _ => ?_)
    rw [fibreFactorC hℓ hAc i j hij hΨ.continuous (z + u) z]
    calc χ (z + u) * χ z * (A.indicator (fun _ => (1 : ℝ)) (z + u)
            * A.indicator (fun _ => (1 : ℝ)) z
            * Work.BoseFixB1.BoxPairIntGenC2.boxPairFibreFree volA ℓ A Ψ i
                (Submission.BoseGases.sucAboveInv i j hij) (z + u) z)
        = (χ (z + u) * A.indicator (fun _ => (1 : ℝ)) (z + u))
            * (χ z * A.indicator (fun _ => (1 : ℝ)) z)
            * Work.BoseFixB1.BoxPairIntGenC2.boxPairFibreFree volA ℓ A Ψ i
                (Submission.BoseGases.sucAboveInv i j hij) (z + u) z := by ring
      _ = χ (z + u) * χ z * Work.BoseFixB1.BoxPairIntGenC2.boxPairFibreFree volA ℓ A Ψ i
                (Submission.BoseGases.sucAboveInv i j hij) (z + u) z := by
            rw [hχind, hχind]
  -- joint smoothness of the integrand in `(u, z)`
  have hF : ContDiff ℝ 2 (Function.uncurry (fun u z : E3 =>
      χ (z + u) * χ z * Work.BoseFixB1.BoxPairIntGenC2.boxPairFibreFree volA ℓ A Ψ i
          (Submission.BoseGases.sucAboveInv i j hij) (z + u) z)) := by
    have h1 : ContDiff ℝ 2 (fun q : E3 × E3 => χ (q.2 + q.1)) :=
      hχc.comp ((contDiff_snd.add contDiff_fst).of_le htop2)
    have h2 : ContDiff ℝ 2 (fun q : E3 × E3 => χ q.2) :=
      hχc.comp (contDiff_snd.of_le htop2)
    have h3 : ContDiff ℝ 2 (fun q : E3 × E3 =>
        Work.BoseFixB1.BoxPairIntGenC2.boxPairFibreFree volA ℓ A Ψ i
          (Submission.BoseGases.sucAboveInv i j hij) (q.2 + q.1) q.2) := by
      have hcomp : ContDiff ℝ 2 (Function.uncurry (fun y z : E3 =>
          Work.BoseFixB1.BoxPairIntGenC2.boxPairFibreFree volA ℓ A Ψ i
            (Submission.BoseGases.sucAboveInv i j hij) y z)) :=
        (fibreFreeContDiffP (volA := volA) hA hℓ hAc hΨ i
          (Submission.BoseGases.sucAboveInv i j hij)).of_le htop2
      have := hcomp.comp (ContDiff.prodMk ((contDiff_snd.add contDiff_fst).of_le htop2)
        (contDiff_snd.of_le htop2))
      simpa [Function.uncurry, Function.comp_def] using this
    change ContDiff ℝ 2 (fun q : E3 × E3 => χ (q.2 + q.1) * χ q.2
      * Work.BoseFixB1.BoxPairIntGenC2.boxPairFibreFree volA ℓ A Ψ i
          (Submission.BoseGases.sucAboveInv i j hij) (q.2 + q.1) q.2)
    exact (h1.mul h2).mul h3
  -- differentiate under the integral sign over `A ⊆ acube ℓ`
  rw [hstep1]
  exact Work.BoseFixB1.contDiff_setIntegral_subset_isCompact (P := E3)
    (A := A) (K := Submission.BoseGases.acube ℓ) hA (Submission.BoseGases.acube_compact hℓ) hAc
    (F := fun u z : E3 => χ (z + u) * χ z
      * Work.BoseFixB1.BoxPairIntGenC2.boxPairFibreFree volA ℓ A Ψ i
          (Submission.BoseGases.sucAboveInv i j hij) (z + u) z)
    (n := (2 : ℕ∞)) hF

end Work.BoseFixB1.BoxPairIntGenC2

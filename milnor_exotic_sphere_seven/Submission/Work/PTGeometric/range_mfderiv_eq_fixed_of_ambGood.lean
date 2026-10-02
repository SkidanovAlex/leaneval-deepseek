import Mathlib
import Submission.Work.PTGeometric.AmbientPerturbation
import Submission.Work.PTGeometric.isSubmersionAt_and_boundary_of_chartModel
import Submission.Work.PTGeometric.mfderiv_surjective_of_isSubmersionAt

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `range (mfderiv v x) = {z | P x z = z}` at a good zero of a `P`-valued field

Let `P : M → EndOp n` be a smooth field of endomorphisms and `v : M → Amb n` a smooth field with
`P y (v y) = v y` for all `y`.  At a point `x` with `v x = 0`:

* the **inclusion** `range (mfderiv v x) ⊆ {z | P x z = z}` holds by differentiating the identity
  `P (v ·) = v ·` at `x` (the derivative of `y ↦ P y (v y)` is `P x ∘ mfderiv v x`, because
  `v x = 0`);
* the **reverse inclusion** uses `AmbGood C v x`: since `v x = 0`, there is a chart index `l` with
  `x ∈ C.U l` and `(C.ell l) ∘ v` a submersion at `x`; its `mfderiv` is surjective
  (`Work.PTGeometric.mfderiv_surjective_of_isSubmersionAt`), hence for `z` fixed by `P x` there is
  `w` with `C.ell l (mfderiv v x w) = C.ell l z`; then `z - mfderiv v x w` is fixed by `P x`
  (by the inclusion) and killed by `C.ell l`, so it vanishes by `C.ell_inj`, and `z` is in the
  range.  No dimension count is needed.

The main theorem is `Work.PTGeometric.range_mfderiv_eq_fixed_of_ambGood`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section


/-- **The inclusion direction.**  If `v` is a smooth `P`-valued field with `v x = 0`, then the
range of `mfderiv v x` is contained in the fixed space of `P x`.

Proof: `mfderiv (P · (v ·)) x = P x ∘ mfderiv v x`, the second term of the Leibniz rule dropping out
because `v x = 0`; and `P (v ·) = v ·` as functions. -/
theorem range_mfderiv_subset_fixed_of_mem
    {n k : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) ((⊤ : ENat) : WithTop ENat) M]
    {P : M → Work.PTGeometric.EndOp n} {v : M → Work.PTGeometric.Amb n}
    (hPsm : ContMDiff (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      (modelWithCornersSelf ℝ (Work.PTGeometric.EndOp n)) ((⊤ : ENat) : WithTop ENat) P)
    (hv : ContMDiff (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      (modelWithCornersSelf ℝ (Work.PTGeometric.Amb n)) ((⊤ : ENat) : WithTop ENat) v)
    (hmem : ∀ y, P y (v y) = v y) {x : M} (hx : v x = 0) :
    Set.range (mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      (modelWithCornersSelf ℝ (Work.PTGeometric.Amb n)) v x)
      ⊆ {z : Work.PTGeometric.Amb n | P x z = z} := by
  have hPd : MDifferentiableAt (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Work.PTGeometric.EndOp n) P x :=
    hPsm.contMDiffAt.mdifferentiableAt (by simp)
  have hvd : MDifferentiableAt (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Work.PTGeometric.Amb n) v x :=
    hv.contMDiffAt.mdifferentiableAt (by simp)
  have hw1 : writtenInExtChartAt (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Work.PTGeometric.EndOp n) x P
      = fun z => P ((extChartAt (𝓡∂ ((8 + k) + 1)) x).symm z) := by
    funext z
    simp only [writtenInExtChartAt, Function.comp_apply]
    rw [extChartAt_self_eq]
    rfl
  have hPder : HasFDerivWithinAt (fun z => P ((extChartAt (𝓡∂ ((8 + k) + 1)) x).symm z))
      (mfderiv (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Work.PTGeometric.EndOp n) P x)
      (Set.range (𝓡∂ ((8 + k) + 1))) ((extChartAt (𝓡∂ ((8 + k) + 1)) x) x) := by
    have h := hPd.hasMFDerivAt
    unfold HasMFDerivAt at h
    rw [hw1] at h
    exact h.2
  have hw2 : writtenInExtChartAt (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Work.PTGeometric.Amb n) x v
      = fun z => v ((extChartAt (𝓡∂ ((8 + k) + 1)) x).symm z) := by
    funext z
    simp only [writtenInExtChartAt, Function.comp_apply]
    rw [extChartAt_self_eq]
    rfl
  have hvder : HasFDerivWithinAt (fun z => v ((extChartAt (𝓡∂ ((8 + k) + 1)) x).symm z))
      (mfderiv (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Work.PTGeometric.Amb n) v x)
      (Set.range (𝓡∂ ((8 + k) + 1))) ((extChartAt (𝓡∂ ((8 + k) + 1)) x) x) := by
    have h := hvd.hasMFDerivAt
    unfold HasMFDerivAt at h
    rw [hw2] at h
    exact h.2
  have hcomb := hPder.clm_apply hvder
  have hψx : (extChartAt (𝓡∂ ((8 + k) + 1)) x).symm
      ((extChartAt (𝓡∂ ((8 + k) + 1)) x) x) = x :=
    PartialEquiv.left_inv _ (mem_extChartAt_source x)
  have hder : HasFDerivWithinAt
      (fun z => P ((extChartAt (𝓡∂ ((8 + k) + 1)) x).symm z)
        (v ((extChartAt (𝓡∂ ((8 + k) + 1)) x).symm z)))
      ((P x).comp (mfderiv (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Work.PTGeometric.Amb n) v x))
      (Set.range (𝓡∂ ((8 + k) + 1))) ((extChartAt (𝓡∂ ((8 + k) + 1)) x) x) := by
    have h := hcomb
    rw [hψx, hx] at h
    simp only [map_zero, add_zero] at h
    exact h
  have hw3 : writtenInExtChartAt (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Work.PTGeometric.Amb n) x v
      = fun z => P ((extChartAt (𝓡∂ ((8 + k) + 1)) x).symm z)
          (v ((extChartAt (𝓡∂ ((8 + k) + 1)) x).symm z)) := by
    funext z
    simp only [writtenInExtChartAt, Function.comp_apply]
    rw [extChartAt_self_eq]
    exact (hmem _).symm
  have hder' : HasFDerivWithinAt
      (writtenInExtChartAt (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Work.PTGeometric.Amb n) x v)
      ((P x).comp (mfderiv (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Work.PTGeometric.Amb n) v x))
      (Set.range (𝓡∂ ((8 + k) + 1))) ((extChartAt (𝓡∂ ((8 + k) + 1)) x) x) := by
    rw [hw3]; exact hder
  have hmfd : HasMFDerivAt (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Work.PTGeometric.Amb n) v x
      ((P x).comp (mfderiv (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Work.PTGeometric.Amb n) v x)) :=
    ⟨hv.contMDiffAt.continuousAt, hder'⟩
  have h6 : mfderiv (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Work.PTGeometric.Amb n) v x
      = (P x).comp (mfderiv (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Work.PTGeometric.Amb n) v x) :=
    hmfd.mfderiv
  rintro z ⟨w, rfl⟩
  have hzw : (mfderiv (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Work.PTGeometric.Amb n) v x) w
      = P x ((mfderiv (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Work.PTGeometric.Amb n) v x) w) :=
    congr_arg (fun L : EuclideanSpace ℝ (Fin ((8 + k) + 1)) →L[ℝ]
      Work.PTGeometric.Amb n => L w) h6
  exact hzw.symm

/-- **The chain rule with a continuous linear map.**  `mfderiv x` of `y ↦ ℓ (v y)` is `ℓ` composed
with `mfderiv x v`. -/
theorem mfderiv_comp_clm_of_contMDiff
    {n k : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) ((⊤ : ENat) : WithTop ENat) M]
    {v : M → Work.PTGeometric.Amb n}
    (hv : ContMDiff (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      (modelWithCornersSelf ℝ (Work.PTGeometric.Amb n)) ((⊤ : ENat) : WithTop ENat) v)
    (ℓ : Work.PTGeometric.Amb n →L[ℝ] Work.PTGeometric.Amb k) (x : M) :
    mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
        (modelWithCornersSelf ℝ (Work.PTGeometric.Amb k)) (fun y => ℓ (v y)) x
      = ℓ.comp (mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
          (modelWithCornersSelf ℝ (Work.PTGeometric.Amb n)) v x) := by
  have hℓd : MDifferentiableAt 𝓘(ℝ, Work.PTGeometric.Amb n) 𝓘(ℝ, Work.PTGeometric.Amb k)
      (fun w => ℓ w) (v x) :=
    (ℓ.contMDiffAt (n := ((⊤ : ENat) : WithTop ENat))).mdifferentiableAt (by simp)
  have hvd : MDifferentiableAt (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Work.PTGeometric.Amb n) v x :=
    hv.contMDiffAt.mdifferentiableAt (by simp)
  have h1 := mfderiv_comp (f := v) (g := fun w => ℓ w) x hℓd hvd
  rw [Function.comp_def] at h1
  rw [h1]
  congr 1
  rw [mfderiv_eq_fderiv]
  exact ℓ.hasFDerivAt.fderiv

theorem range_mfderiv_eq_fixed_of_ambGood
    {n k : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) ((⊤ : ENat) : WithTop ENat) M]
    {P : M → Work.PTGeometric.EndOp n} {m : ℕ} (C : Work.PTGeometric.AmbCharts n k M P m)
    (hPsm : ContMDiff (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      (modelWithCornersSelf ℝ (Work.PTGeometric.EndOp n)) ((⊤ : ENat) : WithTop ENat) P)
    {v : M → Work.PTGeometric.Amb n}
    (hv : ContMDiff (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      (modelWithCornersSelf ℝ (Work.PTGeometric.Amb n)) ((⊤ : ENat) : WithTop ENat) v)
    (hmem : ∀ y, P y (v y) = v y)
    {x : M} (hx : v x = 0) (hgood : Work.PTGeometric.AmbGood C v x) :
    Set.range (mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      (modelWithCornersSelf ℝ (Work.PTGeometric.Amb n)) v x) = {z : Work.PTGeometric.Amb n | P x z = z} := by
  refine Set.Subset.antisymm (range_mfderiv_subset_fixed_of_mem hPsm hv hmem hx) ?_
  intro z hz
  obtain ⟨l, hxl, hsub⟩ : ∃ l : Fin m, x ∈ C.U l ∧ IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓡 k) ∞
      (fun y => C.ell l (v y)) x := by
    rw [Work.PTGeometric.AmbGood] at hgood
    rcases hgood with hbad | hgood
    · exact absurd hx hbad
    · exact hgood
  have hsurj := mfderiv_surjective_of_isSubmersionAt (𝓡∂ ((8 + k) + 1)) hsub
  have hchain := mfderiv_comp_clm_of_contMDiff hv (C.ell l) x
  obtain ⟨w, hw⟩ := hsurj (C.ell l z)
  have hw' : C.ell l ((mfderiv (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Work.PTGeometric.Amb n) v x) w)
      = C.ell l z := by
    rw [hchain] at hw
    exact hw
  refine ⟨w, ?_⟩
  have hwfix : P x ((mfderiv (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Work.PTGeometric.Amb n) v x) w)
      = (mfderiv (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Work.PTGeometric.Amb n) v x) w :=
    range_mfderiv_subset_fixed_of_mem hPsm hv hmem hx ⟨w, rfl⟩
  have hfix : P x (z - (mfderiv (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Work.PTGeometric.Amb n) v x) w)
      = z - (mfderiv (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Work.PTGeometric.Amb n) v x) w := by
    rw [map_sub, hz, hwfix]
  have hkill : C.ell l (z - (mfderiv (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Work.PTGeometric.Amb n) v x) w) = 0 := by
    rw [map_sub, hw', sub_self]
  have hzero := C.ell_inj l x hxl
    (z - (mfderiv (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Work.PTGeometric.Amb n) v x) w) hfix hkill
  exact (sub_eq_zero.mp hzero).symm

end

end Work.PTGeometric

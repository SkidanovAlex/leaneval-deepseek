import Mathlib
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.ThomBordism.Grassmann.inclusionBundleIso
import Submission.Work.Thom.pontryagin1_comap
import Submission.Work.Thom.pontryaginClass_one
import Submission.Work.Agree.complexificationIso
import Submission.Work.ThomBordism.Grassmann.FibreBaseDefs
import Submission.Work.ThomBordism.Grassmann.AddLineGauge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
# From `p1Rat 2 2 ≠ 0` to `p1Rat k m ≠ 0` for all `k, m ≥ 4`

The two **stabilisation steps** of the oriented Grassmannian

* `CohMap_p1_incl` — the ambient inclusion `OG k m → OG k (m+1)` (`inclusionBundleIso`);
* `CohMap_p1_addLine` — the "add a line" map `OG k m → OG (k+1) m` (`addLineBundleIso`),

each pull the tautological bundle back to (a bundle isomorphic to) the tautological bundle of the
smaller Grassmannian, so by naturality of `p₁` (`Work.Thom.pontryagin1_comap`), stability
(`Work.Thom.pontryagin1_sumEpsR`) and isomorphism-invariance (derived from
`Work.Agree.chernClass_complexificationCore_eq`) they pull `p₁` back to `p₁`.  Rationalising
(`1 ⊗ ·`) turns this into the two implications

`p1Rat k m ≠ 0 ⟹ p1Rat (k+1) m ≠ 0`,  `p1Rat k m ≠ 0 ⟹ p1Rat k (m+1) ≠ 0`,

and iterating these from `(2,2)` gives every `(k,m)` with `k, m ≥ 4`.
-/

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}

/-! ## Isomorphism-invariance of the first Pontryagin class -/

/-- **`p₁` depends only on the isomorphism class of a real bundle**: two real bundles over the same
base with the same model fibre `ℝ^k` and isomorphic gluing data have the same first Pontryagin
class.  Immediate from `Work.Agree.chernClass_complexificationCore_eq` (isomorphism-invariance of
the Chern classes of the complexifications) and `p₁ = -c₂(· ⊗_ℝ ℂ)`. -/
theorem pontryagin1_eq_of_bundleIso {k : ℕ} {ι ι' : Type} [Fintype ι] [Fintype ι']
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι)
    (Z' : RealBundle B (EuclideanSpace ℝ (Fin k)) ι')
    (e : Work.Thom.BundleIso Z Z') :
    Work.Thom.pontryagin1 Z = Work.Thom.pontryagin1 Z' := by
  rw [Work.Thom.pontryagin1_def, Work.Thom.pontryagin1_def]
  rw [Work.Agree.chernClass_complexificationCore_eq (rfl : k = k) Z Z' e 2]

/-! ## The two one-step bundle comparisons -/

/-- **The `m`-step**: there is a continuous map `OG k m → OG k (m+1)` (the ambient inclusion)
whose pullback of the tautological bundle is isomorphic to `γ_{k,m}`, hence which pulls `p₁` back
to `p₁`. -/
theorem CohMap_p1_incl (k m : ℕ) :
    ∃ φ : C(OG k m, OG k (m + 1)),
      (Work.Thom.CohMap φ ℤ 4).hom (p1 k (m + 1)) = p1 k m := by
  obtain ⟨φ, ⟨e⟩⟩ := inclusionBundleIso k m
  refine ⟨φ, ?_⟩
  have hnat : (Work.Thom.CohMap φ ℤ 4).hom
        (Work.Thom.pontryagin1 (tautologicalBundle k (m + 1)))
      = Work.Thom.pontryagin1 (Work.Thom.bundleComap (tautologicalBundle k (m + 1)) φ) :=
    (Work.Thom.pontryagin1_comap (tautologicalBundle k (m + 1)) φ).symm
  have hiso : Work.Thom.pontryagin1 (Work.Thom.bundleComap (tautologicalBundle k (m + 1)) φ)
      = Work.Thom.pontryagin1 (tautologicalBundle k m) :=
    pontryagin1_eq_of_bundleIso _ _ e
  rw [show p1 k (m + 1) = Work.Thom.pontryaginClass 1 (tautologicalBundle k (m + 1)) from rfl,
    show p1 k m = Work.Thom.pontryaginClass 1 (tautologicalBundle k m) from rfl,
    Work.Thom.pontryaginClass_one, Work.Thom.pontryaginClass_one, hnat, hiso]

/-- **The `k`-step (crux)**: there is a continuous map `OG k m → OG (k+1) m` (adding a line
`⟨e_last⟩`) whose pullback of `γ_{k+1,m}` is isomorphic to `γ_{k,m} ⊕ ε¹`, hence which pulls `p₁`
back to `p₁` by stability. -/
theorem CohMap_p1_addLine (k m : ℕ) :
    ∃ φ : C(OG k m, OG (k + 1) m),
      (Work.Thom.CohMap φ ℤ 4).hom (p1 (k + 1) m) = p1 k m := by
  obtain ⟨φ, ⟨e⟩⟩ := addLineBundleIso k m (Fin 1)
  refine ⟨φ, ?_⟩
  have hnat : (Work.Thom.CohMap φ ℤ 4).hom
        (Work.Thom.pontryagin1 (tautologicalBundle (k + 1) m))
      = Work.Thom.pontryagin1 (Work.Thom.bundleComap (tautologicalBundle (k + 1) m) φ) :=
    (Work.Thom.pontryagin1_comap (tautologicalBundle (k + 1) m) φ).symm
  have hstab : Work.Thom.pontryagin1 (Work.Thom.bundleComap (tautologicalBundle (k + 1) m) φ)
      = Work.Thom.pontryagin1 (tautologicalBundle k m) :=
    Work.Thom.pontryagin1_sumEpsR (Fin 1) (tautologicalBundle k m)
      (Work.Thom.bundleComap (tautologicalBundle (k + 1) m) φ) e.symm
  rw [show p1 (k + 1) m
        = Work.Thom.pontryaginClass 1 (tautologicalBundle (k + 1) m) from rfl,
    show p1 k m = Work.Thom.pontryaginClass 1 (tautologicalBundle k m) from rfl,
    Work.Thom.pontryaginClass_one, Work.Thom.pontryaginClass_one, hnat, hstab]

/-- **Pullback of `1 ⊗ x`**: rationalising commutes with the pullback on pure tensors. -/
theorem ratCohMap_tmul {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (φ : C(X, Y)) {x : Work.Thom.Coh ℤ 4 Y} {y : Work.Thom.Coh ℤ 4 X}
    (h : (Work.Thom.CohMap φ ℤ 4).hom x = y) :
    TensorProduct.map (LinearMap.id : ℚ →ₗ[ℤ] ℚ) ((Work.Thom.CohMap φ ℤ 4).hom)
        ((1 : ℚ) ⊗ₜ[ℤ] x) = (1 : ℚ) ⊗ₜ[ℤ] y := by
  rw [TensorProduct.map_tmul, h]
  rfl

/-! ## The target -/

theorem p1RatNeZero_of_twoTwo (h : Work.ThomBordism.Grassmann.p1Rat 2 2 ≠ 0) :
    ∀ k m : ℕ, 4 ≤ k → 4 ≤ m → Work.ThomBordism.Grassmann.p1Rat k m ≠ 0 := by
  have stepK : ∀ k m : ℕ, p1Rat k m ≠ 0 → p1Rat (k + 1) m ≠ 0 := by
    intro k m hk
    obtain ⟨φ, hφ⟩ := CohMap_p1_addLine k m
    have hrat : TensorProduct.map (LinearMap.id : ℚ →ₗ[ℤ] ℚ) ((Work.Thom.CohMap φ ℤ 4).hom)
        (p1Rat (k + 1) m) = p1Rat k m := by
      rw [show p1Rat (k + 1) m = (1 : ℚ) ⊗ₜ[ℤ] p1 (k + 1) m from rfl,
        show p1Rat k m = (1 : ℚ) ⊗ₜ[ℤ] p1 k m from rfl]
      exact ratCohMap_tmul φ hφ
    intro h0
    exact hk (by rw [← hrat, h0, map_zero])
  have stepM : ∀ k m : ℕ, p1Rat k m ≠ 0 → p1Rat k (m + 1) ≠ 0 := by
    intro k m hk
    obtain ⟨φ, hφ⟩ := CohMap_p1_incl k m
    have hrat : TensorProduct.map (LinearMap.id : ℚ →ₗ[ℤ] ℚ) ((Work.Thom.CohMap φ ℤ 4).hom)
        (p1Rat k (m + 1)) = p1Rat k m := by
      rw [show p1Rat k (m + 1) = (1 : ℚ) ⊗ₜ[ℤ] p1 k (m + 1) from rfl,
        show p1Rat k m = (1 : ℚ) ⊗ₜ[ℤ] p1 k m from rfl]
      exact ratCohMap_tmul φ hφ
    intro h0
    exact hk (by rw [← hrat, h0, map_zero])
  have h44 : p1Rat 4 4 ≠ 0 := by
    have h32 : p1Rat 3 2 ≠ 0 := stepK 2 2 h
    have h42 : p1Rat 4 2 ≠ 0 := stepK 3 2 h32
    have h43 : p1Rat 4 3 ≠ 0 := stepM 4 2 h42
    exact stepM 4 3 h43
  have hk4 : ∀ k : ℕ, 4 ≤ k → p1Rat k 4 ≠ 0 := by
    intro k hk
    refine Nat.le_induction h44 (fun n _ ih => ?_) k hk
    exact stepK n 4 ih
  intro k m hk hm
  exact Nat.le_induction (hk4 k hk) (fun n _ ih => stepM k n ih) m hm

end

end Work.ThomBordism.Grassmann

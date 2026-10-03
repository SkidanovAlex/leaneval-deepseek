import Mathlib
import Submission.Work.ORP311.Defs
import Submission.Work.ORP311.prop311_of_core311
import Submission.Work.ORP311.BlockShift
import Submission.Work.ORP311.FolnerWindow
import Submission.Work.ORP311.LuckDim
import Submission.Work.ORP311.HdimInject
import Submission.Work.ORP311.tDim_eq_card_mul_hdim
import Submission.Work.ORP311.mem_ell2Sub_iff
import Submission.Work.ORP311.tDim_mono
import Submission.Work.ORP311.ell2Sub_orthogonal
import Submission.Work.ORP311.lp_extend_isometry
import Submission.Work.ORVonNeumann.Rep.vnKeyRank
import Submission.Work.ORVonNeumann.Rep.vnMatOpAdjoint
import Submission.Work.ORVonNeumann.Rep.vnMatOpMul
import Submission.Work.ORVonNeumann.Rep.vnMatOpEquivariant
import Submission.Work.ORVonNeumann.Rep.Phi_mem_nonZeroDivisors
import Submission.Work.ORVonNeumann.VonNeumannAlgebra.exists_liftU_of_diagHom
import Submission.Work.ORVonNeumann.VonNeumannAlgebra.starRegularAffiliated
import Submission.Work.ORVonNeumann.Regular.matrix_vonNeumannRegular
import Submission.Work.ORVonNeumann.CountableEnvelope
import Submission.Work.Rep.Ore.injective_of_mem_nonZeroDivisors

set_option autoImplicit false

open scoped InnerProductSpace

namespace Work.ORP311.P311

open Work.ORVonNeumann Work.ORP311

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

instance ell2Sub_hasOrthogonalProjection (n : ℕ) (Z : Set G) :
    (ell2Sub (G := G) n Z).HasOrthogonalProjection := by
  haveI : CompleteSpace (ell2Sub (G := G) n Z) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  infer_instance

/-- The hypotheses on `(N, t)`: `t` normalises `N` and has infinite order modulo `N`. -/
structure TwistData (N : Subgroup G) (t : G) : Prop where
  conj : ∀ x ∈ N, t * x * t⁻¹ ∈ N
  conj_inv : ∀ x ∈ N, t⁻¹ * x * t ∈ N
  inf : ∀ k : ℤ, t ^ k ∈ N → k = 0

/-- The block projection onto `ℓ²(N t^j)ⁿ`. -/
noncomputable abbrev blk (n : ℕ) (N : Subgroup G) (t : G) (j : ℤ) :
    Rep.HSum (G := G) n →L[ℂ] Rep.HSum (G := G) n :=
  (ell2Sub (G := G) n (coset N t j)).starProjection

open scoped Classical in
/-- The transversal `{t^j : |j| ≤ m}`. -/
noncomputable def sWin (t : G) (m : ℕ) : Finset G :=
  (Finset.Icc (-(m : ℤ)) m).image (fun j : ℤ => t ^ j)

/-- The window kernel of the two-term operator `Z`. -/
noncomputable def Ewin (n : ℕ) (N : Subgroup G) (t : G) (m : ℕ)
    (Z : Rep.HSum (G := G) n →L[ℂ] Rep.HSum (G := G) n) : Submodule ℂ (Rep.HSum (G := G) n) :=
  ell2Sub (G := G) n (window N t m) ⊓
    ⨅ (j : ℤ) (_ : -(m : ℤ) < j ∧ j ≤ m), LinearMap.ker (blk n N t j ∘L Z).toLinearMap

noncomputable def cosetDataN (N : Subgroup G) : Rep.CosetData G N :=
  (Rep.exists_diagHom N).choose

noncomputable def PhiN (N : Subgroup G) :
    ↥(groupVonNeumann ↥N) →ₐ[ℂ] ↥(groupVonNeumann G) :=
  (Rep.exists_diagHom N).choose_spec.choose

theorem PhiN_spec (N : Subgroup G) :
    (∀ (h : ↥N), PhiN N ⟨Rep.leftRegOp h, Rep.leftRegOp_mem_groupVonNeumann h⟩ =
        ⟨Rep.leftRegOp (h : G), Rep.leftRegOp_mem_groupVonNeumann (h : G)⟩) ∧
    (∀ b, PhiN N (star b) = star (PhiN N b)) ∧ Function.Injective (PhiN N) ∧
    (∀ b (q : (cosetDataN N).Q) (y : l2 ↥N),
      (PhiN N b : boundedEnd G) ((cosetDataN N).e q y) =
        (cosetDataN N).e q ((b : boundedEnd ↥N) y)) :=
  (Rep.exists_diagHom N).choose_spec.choose_spec

noncomputable def liftUN (N : Subgroup G) :
    (Rep.countableGroupVonNeumann (G := ↥N)).affiliated →+* (concreteEnvelope G).U :=
  (VonNeumannAlgebra.exists_liftU_of_diagHom N (cosetDataN N) (PhiN N) (PhiN_spec N).2.1
    (PhiN_spec N).2.2.1 (PhiN_spec N).2.2.2).choose

/-- The numerator map `N(G) → U(G)` with its target displayed as `(concreteEnvelope G).U`. -/
noncomputable def numG (G : Type*) [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] :
    ↥(groupVonNeumann G) →+* (concreteEnvelope G).U :=
  VonNeumannAlgebra.numOf (countableModel G)

end Work.ORP311.P311

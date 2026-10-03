import Mathlib
import Submission.Work.ORCoherence.Tor
import Submission.Work.ORFlatness.Flat
import Submission.Work.ORFlatness.DiagonalRight
import Submission.Work.ORFP2.Basic
import Submission.Work.ORFP2.mem_augIdeal_iff
import Submission.Work.ORHomAlg.Tor
import Submission.Work.ORHomAlg.JL52.jl_5_2_2
import Submission.Work.ORHomAlg.Tor.torDimensionShift
import Submission.Work.ORHomAlg.Bridge.torEquiv
import Submission.Work.ORBridgeTor.tor1Vanishes_iff_tor
import Submission.Work.ORBridgeTor.TrivMod
import Submission.Work.ORBridgeTor.torSwap
import Submission.Work.ORBridgeTor.trivTensorEquiv
import Submission.Work.ORBridgeTor.torEquivOfEquiv
import Submission.Work.ORFinal.Chain.ChainDefs
import Submission.Work.ORFinal.Chain.torDiagSwap
import Submission.Work.ORFinal.Chain.torShiftAug

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MonoidAlgebra TensorProduct MulOpposite
open scoped TensorProduct
open Work.ORFinal.Chain

namespace Work.ORFinal.Chain

theorem chainOfJL52 (K : Type) [Field K] (G : Type) [Group G] (S : Type) [Ring S] [Algebra K S]
    (φ : MonoidAlgebra K G →ₐ[K] S)
    [Jinst : Module ((MonoidAlgebra K G)ᵐᵒᵖ) (TensorProduct K S ↥(Work.ORFP2.augIdeal K G))]
    (hJinst : Jinst = Work.ORFlatness.diagRightModule K G S φ ↥(Work.ORFP2.augIdeal K G))
    (M : ModuleCat (MonoidAlgebra K G)) :
    CategoryTheory.Limits.IsZero (Work.ORCoherence.Tor φ.toRingHom 2 M) ↔
      Work.ORFlatness.Tor1Vanishes (MonoidAlgebra K G)
        (TensorProduct K S ↥(Work.ORFP2.augIdeal K G)) (↥M) := by
  subst hJinst
  -- `S` as a right `K[G]`-module through `φ`
  letI : Module (MonoidAlgebra K G)ᵐᵒᵖ S := rightModuleOfRingHom K G S φ.toRingHom
  have hSright : ∀ (x : MonoidAlgebra K G) (s : S), (MulOpposite.op x) • s = s * φ x :=
    fun x s => rfl
  haveI hcomm : SMulCommClass S (MonoidAlgebra K G)ᵐᵒᵖ S :=
    smulCommClass_rightModuleOfRingHom φ.toRingHom
  -- the `K`-structures
  haveI hscM : SMulCommClass K (MonoidAlgebra K G) ↥M := smulCommClass_catK M
  haveI hstK : IsScalarTower K (MonoidAlgebra K G) K := isScalarTower_trivLeft K G
  -- pin the diagonal right structures
  letI hdM : Module (MonoidAlgebra K G)ᵐᵒᵖ (TensorProduct K S ↥M) :=
    Work.ORFlatness.diagRightModule K G S φ ↥M
  letI hdI : Module (MonoidAlgebra K G)ᵐᵒᵖ (TensorProduct K S ↥(Work.ORFP2.augIdeal K G)) :=
    Work.ORFlatness.diagRightModule K G S φ ↥(Work.ORFP2.augIdeal K G)
  -- pin the diagonal left structures on the tensors of two left `K[G]`-modules
  letI hlMK : Module (MonoidAlgebra K G) (TensorProduct K ↥M K) :=
    Work.ORHomAlg.JL52.instDiagModule ↥M K
  letI hlMI : Module (MonoidAlgebra K G) (TensorProduct K ↥M ↥(Work.ORFP2.augIdeal K G)) :=
    Work.ORHomAlg.JL52.instDiagModule ↥M ↥(Work.ORFP2.augIdeal K G)
  letI hlIM : Module (MonoidAlgebra K G) (TensorProduct K ↥(Work.ORFP2.augIdeal K G) ↥M) :=
    Work.ORHomAlg.JL52.instDiagModule ↥(Work.ORFP2.augIdeal K G) ↥M
  -- the bridge to the `Work.ORHomAlg` vocabulary
  have hbridge : Subsingleton (Work.ORCoherence.Tor φ.toRingHom 2 M) ↔
      Subsingleton (Work.ORHomAlg.Tor (R := MonoidAlgebra K G) 2 S ↥M) := by
    obtain ⟨e0⟩ := Work.ORHomAlg.Bridge.torEquiv φ.toRingHom hSright hcomm ↥M 2
    constructor
    · intro h
      exact ⟨fun a b => e0.symm.injective (h.elim (e0.symm a) (e0.symm b))⟩
    · intro h
      exact ⟨fun a b => e0.injective (h.elim (e0 a) (e0 b))⟩
  -- the chain of `ℤ`-linear equivalences
  obtain ⟨eM⟩ := tensorTrivRight (K := K) (G := G) (M := ↥M)
  obtain ⟨t1⟩ := Work.ORBridgeTor.torEquivOfEquiv (MonoidAlgebra K G)
    (LinearEquiv.refl (R := (MonoidAlgebra K G)ᵐᵒᵖ) (M := S)) eM.symm 2
  obtain ⟨t2⟩ := torDiagSwap K G S φ hSright ↥M K 2
  obtain ⟨t3⟩ := torShiftAug K G (TensorProduct K S ↥M) 0
  obtain ⟨t4⟩ := torDiagSwap K G S φ hSright ↥M ↥(Work.ORFP2.augIdeal K G) 1
  obtain ⟨eFlip⟩ := tensorCommDiag (K := K) (G := G) ↥M ↥(Work.ORFP2.augIdeal K G)
  obtain ⟨t5⟩ : Nonempty (Work.ORHomAlg.Tor (R := MonoidAlgebra K G) 1 S
      (TensorProduct K ↥M ↥(Work.ORFP2.augIdeal K G)) ≃ₗ[ℤ]
      Work.ORHomAlg.Tor (R := MonoidAlgebra K G) 1 S
      (TensorProduct K ↥(Work.ORFP2.augIdeal K G) ↥M)) :=
    Work.ORBridgeTor.torEquivOfEquiv (MonoidAlgebra K G)
      (LinearEquiv.refl (R := (MonoidAlgebra K G)ᵐᵒᵖ) (M := S)) eFlip 1
  obtain ⟨t6⟩ := torDiagSwap K G S φ hSright ↥(Work.ORFP2.augIdeal K G) ↥M 1
  obtain ⟨t⟩ : Nonempty (Work.ORHomAlg.Tor (R := MonoidAlgebra K G) 2 S ↥M ≃ₗ[ℤ]
      Work.ORHomAlg.Tor (R := MonoidAlgebra K G) 1
        (TensorProduct K S ↥(Work.ORFP2.augIdeal K G)) ↥M) :=
    ⟨t1.trans (t2.trans (t3.trans (t4.symm.trans (t5.trans t6))))⟩
  have hchain : Subsingleton (Work.ORHomAlg.Tor (R := MonoidAlgebra K G) 2 S ↥M) ↔
      Subsingleton (Work.ORHomAlg.Tor (R := MonoidAlgebra K G) 1
        (TensorProduct K S ↥(Work.ORFP2.augIdeal K G)) ↥M) :=
    ⟨fun h => ⟨fun a b => t.symm.injective (h.elim (t.symm a) (t.symm b))⟩,
      fun h => ⟨fun a b => t.injective (h.elim (t a) (t b))⟩⟩
  rw [moduleCat_isZero_iff, hbridge, hchain]
  exact (Work.ORBridgeTor.tor1Vanishes_iff_tor (MonoidAlgebra K G)
    (TensorProduct K S ↥(Work.ORFP2.augIdeal K G)) ↥M).symm

end Work.ORFinal.Chain

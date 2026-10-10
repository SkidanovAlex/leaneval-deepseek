import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.PT.LocalPairingAux
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.ZConstruction.AuxInterface
import Submission.Work.SSGRoute.ZConstruction.auxPairingGate_odd_aux
import Submission.Work.SSGRoute.ZConstruction.even_finrank_H1loc_levelK
import Submission.Work.SSGRoute.ZDataMup.OddForm.oPairForm_sum_attach_eq_zero_of_outside
import Submission.Work.SSGRoute.ZDataMup.OddForm.oTheta_eq_one_of_ne_oddPrime
import Submission.Work.SSGRoute.ZSplit.KTransport.isLocConstOn_mapFix_iff
import Submission.Work.SSGRoute.exists_openSubgroup_comap_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

/-- The `hreal` clause of `Work.SSGRoute.PT.relaxed_converse_of_finiteS_v2` (the converse of
clause (8)), in a shape whose *type* is free of `finZB`/`g1FinHalf`: a functional on the locally
constant `M^∨(1)`-cocycles at a finite place which kills the coboundaries and is additive on
cocycles is represented by a locally constant `M`-cocycle through the local pairing.

This is the "surjectivity" half of clause (4) (perfectness of the pairing), written as the dual
statement the consumer needs.  The pairing enters only through its local clause bundle: additivity
in each variable (`hadd_left`, `hadd_right`), vanishing on a coboundary (`hcob_pair`), and the two
perfectness clauses (`hperf_left`, `hperf_right`) — exactly the clauses `(1)`–`(4)` of the family
glued in `PT/canonical_localPairing_reciprocity_converse.lean` (whose `hpc` supplies them).

Route (a dimension count, using the proved `PT.pt_localPairingDual`).  Let
`X = {locally constant M-cocycles}/cob` and `Y = {locally constant M^∨(1)-cocycles}/cob`;
`hadd_*`/`hcob_pair` make the pairing descend to a bilinear form `β : X →ₗ Y →ₗ ZMod p`, whose two
non-degeneracy clauses are `hperf_left`/`hperf_right`; `hfinA`/`hfinB` give finite spanning sets of
`X`/`Y` modulo coboundaries (this holds at a finite place: the quotient is the finite local `H¹`,
`Work.SSGRoute.finite_H1loc_decomp_loc` / `finiteDimensional_H1loc_localGroup`).  `hadd`/`hcob` make
`lam` a linear functional on `Y`, and `PT.pt_localPairingDual` (applied with the two roles swapped)
realises it as `β x` for some `x : X`; lifting `x` to a locally constant cocycle `a` gives the
conclusion. -/
theorem localPairing_surjective_dual (p : ℕ) [Fact p.Prime]
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
      ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p)
    (hadd_left : ∀ (a a' : (Ω ≃ₐ[k] Ω) → M)
      (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a' →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a' →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      pair (SSGRoute.decomp k A) (a + a') b =
        pair (SSGRoute.decomp k A) a b + pair (SSGRoute.decomp k A) a' b)
    (hadd_right : ∀ (a : (Ω ≃ₐ[k] Ω) → M)
      (b b' : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b' →
      pair (SSGRoute.decomp k A) a (b + b') =
        pair (SSGRoute.decomp k A) a b + pair (SSGRoute.decomp k A) a b')
    (hcob_pair : ∀ (a : (Ω ≃ₐ[k] Ω) → M)
      (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      (SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∨
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b) →
      pair (SSGRoute.decomp k A) a b = 0)
    (hperf_left : ∀ a : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
      (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
        pair (SSGRoute.decomp k A) a b = 0) →
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) a)
    (hperf_right : ∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      (∀ a : (Ω ≃ₐ[k] Ω) → M,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
        pair (SSGRoute.decomp k A) a b = 0) →
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hfinA : ∃ (n : ℕ) (φ : Fin n → (Ω ≃ₐ[k] Ω) → M),
      ∀ a : (Ω ≃ₐ[k] Ω) → M,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
        ∃ (c : Fin n → ZMod p) (z : (Ω ≃ₐ[k] Ω) → M),
          SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) z ∧
            a = (∑ i, c i • φ i) + z)
    (hfinB : ∃ (n : ℕ) (ψ : Fin n → (Ω ≃ₐ[k] Ω) →
        Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      ∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
        ∃ (c : Fin n → ZMod p) (z : (Ω ≃ₐ[k] Ω) →
            Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
          SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) z ∧
            b = (∑ i, c i • ψ i) + z)
    (lam : ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p)
    (hadd : ∀ b b' : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
      lam (b + b') = lam b + lam b')
    (hcob : ∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b → lam b = 0) :
    ∃ a : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a ∧
      ∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
        pair (SSGRoute.decomp k A) a b = lam b := by
  classical
  exact pairing_surjective_dual_general (p := p) (Γ := Ω ≃ₐ[k] Ω) (G := K ≃ₐ[k] K)
    (M := M) (N := Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (SSGRoute.res k K) (SSGRoute.decomp k A)
    (fun a b => pair (SSGRoute.decomp k A) a b)
    hadd_left hadd_right hcob_pair hperf_left hperf_right hfinA hfinB lam hadd hcob

end Work.SSGRoute.PT

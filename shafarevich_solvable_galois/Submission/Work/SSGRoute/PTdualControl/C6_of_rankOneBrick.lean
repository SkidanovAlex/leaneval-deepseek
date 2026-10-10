import Mathlib.GroupTheory.Nilpotent
import Mathlib.RepresentationTheory.Induced
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.SSGRoute.PTdualControl.zetaAdjoinDescent
import Submission.Work.SSGRoute.Sha2Lib.unramifiedDetector_indNormal_of_rankOne
import Submission.Work.SSGRoute.Sha2Lib.unramifiedDetector_indNormal_rankOne
import Submission.Work.SSGRoute.Sha2Lib.unramifiedDetector_of_indNormal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The node `C6` from its last brick

The remaining gap of the node `Work.Sha2Lib.unramifiedDetector` (node `C6` of the Poitou--Tate
route, the single `sorry` reached from `Work.SSGRoute.PTdualControl.sha2_dual_control_alt`) is
`Work.SSGRoute.Sha2Lib.unramifiedDetector_indNormal_rankOne`: the detector for the permutation
module `Ind_N^Γ 𝔽_p`, for a normal subgroup `N ⊴ Gal(K/k)` containing the inertia at `q ∧ ∤ p`
and fixing a primitive `p`-th root of unity `ζ ∈ K`.

This file proves that *this one brick implies the node*, by composing

* `Work.SSGRoute.Sha2Lib.unramifiedDetector_indNormal_of_rankOne` (proved): `Ind_N^Γ W` for an
  arbitrary finite trivial `p`-torsion `N`-module `W` follows from the rank-one case `W = 𝔽_p`;
* `Work.SSGRoute.Sha2Lib.unramifiedDetector_of_indNormal` (proved): the leaf for an arbitrary
  finite `p`-torsion `M` with `I_q` acting trivially follows from the `Ind_N^Γ W` node (this is the
  `μ_p ⊆ K` case — the leaf carries `ζ : K`);
* `Work.SSGRoute.PTdualControl.unramifiedDetector_of_mup` (this lane): the leaf for arbitrary `K`
  follows from its `μ_p ⊆ K` case, by adjoining `ζ_p` (`K' = K⟮ζ_p⟯`, of degree prime to `p`) and
  applying the base-change descent `IsUnramifiedDetector.of_baseChange`.

So the theorem below is the *whole* remaining obligation of `C6`, isolated as a single hypothesis in
the node's exact spelling: the moment `unramifiedDetector_indNormal_rankOne` is proved, the `sorry`
of `Work.Sha2Lib.unramifiedDetector` can be closed by

`exact Work.SSGRoute.PTdualControl.unramifiedDetector_of_rankOneBrick p k Ω
  (fun K _ _ _ _ _ _ _ _ w q hwq hpq N _ hNI ζ hζ hNζ =>
    Work.SSGRoute.Sha2Lib.unramifiedDetector_indNormal_rankOne p k K Ω w q hwq hpq N hNI ζ hζ hNζ)
  K w q hwq hpq M hM hI`.
-/

namespace Work.SSGRoute.PTdualControl

open CategoryTheory SSGRoute.PTExt

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

/-- **The rank-one brick of `C6` as a hypothesis**: the detector for the permutation module
`Ind_N^Γ 𝔽_p`, for every finite Galois `K/k`, every place `q ∤ p` and every normal `N ⊴ Gal(K/k)`
containing the inertia at `q` and fixing a primitive `p`-th root of unity `ζ ∈ K`.

This is the statement of `Work.SSGRoute.Sha2Lib.unramifiedDetector_indNormal_rankOne`, packaged as
a single hypothesis so that it can be discharged by whoever proves it. -/
def RankOneBrick (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [NumberField k]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Algebra K Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
    (hNI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → σ ∈ N)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (hNζ : ∀ σ ∈ N, σ ζ = ζ),
    Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq
      (Rep.ind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p)))

/-- **The `μ_p ⊆ K` case of `C6` follows from the rank-one brick**
(`unramifiedDetector_indNormal_of_rankOne` composed with `unramifiedDetector_of_indNormal`). -/
theorem isUnramifiedDetectorMup_of_rankOneBrick (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [NumberField k] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    (hbrick : RankOneBrick p k Ω) : IsUnramifiedDetectorMup p k Ω := by
  intro K _ _ _ _ _ _ _ hζex w q hwq hpq M _ hM hI
  obtain ⟨ζ, hζ⟩ := hζex
  refine Work.SSGRoute.Sha2Lib.unramifiedDetector_of_indNormal p k K Ω w q hwq hpq
    ζ hζ M hM hI ?_
  -- `Ind_N^Γ W` for an arbitrary finite trivial `p`-torsion `N`-module `W`
  intro N _ hNI hNζ W _ hWp hWtriv
  exact Work.SSGRoute.Sha2Lib.unramifiedDetector_indNormal_of_rankOne (p := p) (k := k) (K := K)
    (Ω := Ω) (w := w) (q := q) (hwq := hwq) (hpq := hpq)
    (hrankOne := fun N' _ hNI' ζ' hζ' hNζ' => hbrick K w q hwq hpq N' hNI' ζ' hζ' hNζ')
    (N := N) (hNI := hNI) (ζ := ζ) (hζ := hζ) (hNζ := hNζ)
    (W := W) (hWp := hWp) (hWtriv := hWtriv)

/-- **The node `C6` from the rank-one brick** — the exact spelling of
`Work.Sha2Lib.unramifiedDetector`, with the single remaining arithmetic brick as a hypothesis. -/
theorem unramifiedDetector_of_rankOneBrick (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [NumberField k] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    (hbrick : RankOneBrick p k Ω)
    (K : Type) [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Algebra K Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (hI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m) :
    Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq M :=
  unramifiedDetector_of_mup p k Ω (isUnramifiedDetectorMup_of_rankOneBrick p k Ω hbrick)
    K w q hwq hpq M hM hI

/-- **The node `Work.Sha2Lib.unramifiedDetector`, in its exact spelling, from the rank-one brick
`Work.SSGRoute.Sha2Lib.unramifiedDetector_indNormal_rankOne`.**

This is the *wiring* flagged in `_lead_design/ssg_pt_design_1002/ssg_1120/NOTE.md` §2(a): the body
of `Submission/Work/Sha2Lib/unramifiedDetector.lean` can be replaced by the one line

`exact Work.SSGRoute.PTdualControl.unramifiedDetector_via_rankOneBrick p k K Ω w q hwq hpq M hM hI`

(plus the imports `Submission.Work.SSGRoute.PTdualControl.C6_of_rankOneBrick`).  Measured: this
module does **not** import `Submission.Work.Sha2Lib.unramifiedDetector`, so the import is acyclic. -/
theorem unramifiedDetector_via_rankOneBrick (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (hI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m) :
    Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq M :=
  unramifiedDetector_of_rankOneBrick p k Ω
    (fun K' _ _ _ _ _ _ _ w' q' hwq' hpq' N _ hNI ζ hζ hNζ =>
      Work.SSGRoute.Sha2Lib.unramifiedDetector_indNormal_rankOne p k K' Ω w' q' hwq' hpq' N hNI
        ζ hζ hNζ)
    K w q hwq hpq M hM hI

end Work.SSGRoute.PTdualControl

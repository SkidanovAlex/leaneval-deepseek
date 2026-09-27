/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# Cohomology is the dual of the annihilator of the boundaries in the cycles

For a simplicial set `S` and any degree `n`, the `n`-th rational cohomology of `S` is the dual
of the homology of `S` in degree `n`.  The purpose of this file is to make this statement
available in the exact form needed elsewhere in the project:

`H S ℚ n ≃ₗ[ℚ] (chainBoundariesInCycles S ℚ n).dualAnnihilator`,

where `chainBoundariesInCycles S ℚ n` is the submodule of the `n`-cycles of the *chain* complex
of `S` consisting of the boundaries (the image of `∂ : C_{n+1} → C_n`), viewed as a submodule of
the cycles.  Equivalently, both sides are `ℚ`-linearly isomorphic to the dual of the `n`-th
homology of the chain complex of `S`.

The pairing is realised explicitly.  A cochain `u` is a cocycle precisely when the functional
`seval u` on chains vanishes on the boundaries, so evaluation on chains gives a linear map

`pairingMap : cycles S ℚ n →ₗ[ℚ] Dual ℚ (chainCycles S ℚ n)`,  `u ↦ (c ↦ seval u c)`,

which restricts (co-restricts) to a linear map `pairingToAnn` into
`(chainBoundariesInCycles S ℚ n).dualAnnihilator`.  It kills the coboundaries
(`boundariesInCycles_le_ker_pairingToAnn`), so it descends to the quotient `H S ℚ n`
(`HToAnn`).  The descent is injective because a cocycle pairing to zero with all cycles is a
coboundary (Mathlib's `LinearMap.range_dualMap_eq_dualAnnihilator_ker`, used through
`mem_boundaries_of_forall_chainCycles_seval_eq_zero` of `exists_chain_eval_ne_zero`), and
surjective because a functional on the cycles killing the boundaries is extended to the chains by
`Subspace.dualLift` and read back as a cocycle by `seval_cochainOfDual`; this is where the
fundamental fact `∂ ∘ ∂ = 0` (`sbdry_sbdry_eq_zero`) is used.
-/
import Mathlib
import Submission.Work.Cohomology.Chains
import Submission.Work.Cohomology.Cohomology
import Submission.Work.Cohomology.exists_chain_eval_ne_zero

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology

open Submission.Cohomology

/-! ## `∂ ∘ ∂ = 0` for the boundary of the chain complex -/

/-- The boundary of a chain complex and its iterates vanish: `∂_{n} ∘ ∂_{n+1} = 0`.  This is the
transpose of `δ ∘ δ = 0` (`Submission.Cohomology.coboundary_coboundary`) under the evaluation
pairing `seval`, which is non-degenerate in the chain variable. -/
lemma sbdry_sbdry_eq_zero (S : SSet.{0}) (n : ℕ) (c : SChain S ℚ (n+2)) :
    sbdry S ℚ n (sbdry S ℚ (n+1) c) = 0 := by
  have h : ∀ u : Cochain S ℚ n,
      seval S ℚ n u (sbdry S ℚ n (sbdry S ℚ (n+1) c)) = 0 := by
    intro u
    rw [← seval_coboundary S ℚ n u (sbdry S ℚ (n+1) c)]
    rw [← seval_coboundary S ℚ (n+1) (coboundary S ℚ n u) c]
    rw [coboundary_coboundary]
    rw [seval_apply]
    simp
  rw [← Module.forall_dual_apply_eq_zero_iff ℚ (sbdry S ℚ n (sbdry S ℚ (n+1) c))]
  intro V
  have := h (fun σ => V (Finsupp.single σ 1))
  rwa [seval_cochainOfDual V] at this

/-- The boundaries of the chain complex are cycles: `im ∂ ⊆ ker ∂`. -/
lemma chainBoundaries_le_chainCycles (S : SSet.{0}) (n : ℕ) :
    chainBoundaries S ℚ n ≤ chainCycles S ℚ n := by
  match n with
  | 0 => exact le_top
  | m + 1 =>
    rintro c ⟨d, rfl⟩
    exact sbdry_sbdry_eq_zero S m d

/-! ## The evaluation pairing as a linear map on cocycles -/

/-- Evaluation of cocycles on chains, as a `ℚ`-linear map: a cocycle `u` is sent to the
functional `c ↦ seval S ℚ n u c` on the cycles of the chain complex of `S`. -/
noncomputable def pairingMap (S : SSet.{0}) (n : ℕ) :
    cycles S ℚ n →ₗ[ℚ] Module.Dual ℚ (chainCycles S ℚ n) :=
  LinearMap.comp ((Submodule.subtype (chainCycles S ℚ n)).dualMap)
    (LinearMap.comp (Finsupp.llift ℚ ℚ ℚ (S.obj (op ⦋n⦌))).toLinearMap
      (Submodule.subtype (cycles S ℚ n)))

lemma pairingMap_apply (S : SSet.{0}) (n : ℕ) (u : cycles S ℚ n)
    (z : chainCycles S ℚ n) :
    pairingMap S n u z = seval S ℚ n (u : Cochain S ℚ n) (z : SChain S ℚ n) := by
  simp only [pairingMap, LinearMap.comp_apply, LinearMap.dualMap_apply, Submodule.subtype_apply,
    LinearEquiv.coe_coe, Finsupp.llift_apply, Finsupp.lift_apply, seval_apply, smul_eq_mul]

/-- A cocycle pairs to zero with the boundaries: the pairing of a cohomology class with a cycle
depends only on the class. -/
lemma pairingMap_mem_dualAnnihilator (S : SSet.{0}) (n : ℕ) (u : cycles S ℚ n) :
    pairingMap S n u ∈ (chainBoundariesInCycles S ℚ n).dualAnnihilator := by
  rw [Submodule.mem_dualAnnihilator]
  intro z hz
  have hzB : (z : SChain S ℚ n) ∈ chainBoundaries S ℚ n := Submodule.mem_comap.mp hz
  obtain ⟨d, hd⟩ := hzB
  rw [pairingMap_apply, ← hd, ← seval_coboundary S ℚ n (u : Cochain S ℚ n) d]
  have hu : coboundary S ℚ n (u : Cochain S ℚ n) = 0 := LinearMap.mem_ker.mp u.2
  rw [hu, seval_apply]
  simp

/-- Evaluation of cocycles on cycles, with values in the annihilator of the boundaries in the
cycles. -/
noncomputable def pairingToAnn (S : SSet.{0}) (n : ℕ) :
    cycles S ℚ n →ₗ[ℚ] (chainBoundariesInCycles S ℚ n).dualAnnihilator :=
  (pairingMap S n).codRestrict _ (pairingMap_mem_dualAnnihilator S n)

@[simp] lemma pairingToAnn_apply_val (S : SSet.{0}) (n : ℕ) (u : cycles S ℚ n) :
    ((pairingToAnn S n u : (chainBoundariesInCycles S ℚ n).dualAnnihilator) :
      Module.Dual ℚ (chainCycles S ℚ n)) = pairingMap S n u := rfl

/-- The pairing kills the coboundaries, so it descends to cohomology. -/
lemma boundariesInCycles_le_ker_pairingToAnn (S : SSet.{0}) (n : ℕ) :
    boundariesInCycles S ℚ n ≤ LinearMap.ker (pairingToAnn S n) := by
  intro u hu
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  rw [Submodule.coe_zero]
  apply LinearMap.ext
  intro z
  rw [pairingToAnn_apply_val, pairingMap_apply]
  have huB : (u : Cochain S ℚ n) ∈ boundaries S ℚ n := Submodule.mem_comap.mp hu
  match n with
  | 0 =>
      rw [boundaries, Submodule.mem_bot] at huB
      rw [huB, seval_apply]
      simp
  | m + 1 =>
      obtain ⟨v, hv⟩ := (mem_boundaries_succ (u : Cochain S ℚ (m+1))).mp huB
      rw [← hv, seval_coboundary, mem_chainCycles_succ.mp z.2]
      rw [seval_apply]
      simp

/-- A cocycle pairing to zero with every cycle is a coboundary: the pairing is injective on
cohomology. -/
lemma ker_pairingToAnn_le (S : SSet.{0}) (n : ℕ) :
    LinearMap.ker (pairingToAnn S n) ≤ boundariesInCycles S ℚ n := by
  intro u hu
  rw [LinearMap.mem_ker] at hu
  have hval : pairingMap S n u = 0 := by
    have h1 := Subtype.ext_iff.mp hu
    rwa [pairingToAnn_apply_val, Submodule.coe_zero] at h1
  rw [boundariesInCycles, Submodule.mem_comap]
  apply mem_boundaries_of_forall_chainCycles_seval_eq_zero
  intro c hc
  have h1 : pairingMap S n u ⟨c, hc⟩ = 0 := by rw [hval]; rfl
  rwa [pairingMap_apply] at h1

/-- Every functional on the cycles killing the boundaries is the pairing with some cocycle: the
pairing is surjective onto the annihilator of the boundaries. -/
lemma pairingToAnn_surjective (S : SSet.{0}) (n : ℕ) :
    Function.Surjective (pairingToAnn S n) := by
  intro θ
  have hmem : ∀ c : SChain S ℚ n,
      seval S ℚ n (fun σ => (Subspace.dualLift (chainCycles S ℚ n) θ.1)
        (Finsupp.single σ 1)) c
      = (Subspace.dualLift (chainCycles S ℚ n) θ.1) c :=
    fun c => seval_cochainOfDual (Subspace.dualLift (chainCycles S ℚ n) θ.1) c
  have hu : (fun σ => (Subspace.dualLift (chainCycles S ℚ n) θ.1) (Finsupp.single σ 1))
      ∈ cycles S ℚ n := by
    rw [mem_cycles_iff]
    ext σ
    rw [Pi.zero_apply]
    rw [show coboundary S ℚ n (fun σ => (Subspace.dualLift (chainCycles S ℚ n) θ.1)
          (Finsupp.single σ 1)) σ
        = seval S ℚ (n+1) (coboundary S ℚ n (fun σ => (Subspace.dualLift (chainCycles S ℚ n) θ.1)
          (Finsupp.single σ 1))) (Finsupp.single σ 1) by rw [seval_single, one_mul]]
    rw [seval_coboundary, hmem]
    rw [Subspace.dualLift_of_mem (W := chainCycles S ℚ n) (φ := θ.1)
      (chainBoundaries_le_chainCycles S n ⟨Finsupp.single σ 1, rfl⟩)]
    refine (Submodule.mem_dualAnnihilator θ.1).mp θ.2 ⟨sbdry S ℚ n (Finsupp.single σ 1),
      chainBoundaries_le_chainCycles S n ⟨Finsupp.single σ 1, rfl⟩⟩ ?_
    exact Submodule.mem_comap.mpr ⟨Finsupp.single σ 1, rfl⟩
  refine ⟨⟨fun σ => (Subspace.dualLift (chainCycles S ℚ n) θ.1) (Finsupp.single σ 1), hu⟩, ?_⟩
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  rw [pairingToAnn_apply_val, pairingMap_apply, hmem]
  exact Subspace.dualLift_of_mem z.2

/-! ## The isomorphism on cohomology -/

/-- The evaluation pairing, descended to cohomology: the `ℚ`-linear map from `H S ℚ n` to the
annihilator of the boundaries in the cycles. -/
noncomputable def HToAnn (S : SSet.{0}) (n : ℕ) :
    H S ℚ n →ₗ[ℚ] (chainBoundariesInCycles S ℚ n).dualAnnihilator :=
  Submodule.liftQ (boundariesInCycles S ℚ n) (pairingToAnn S n)
    (boundariesInCycles_le_ker_pairingToAnn S n)

/-- The descended pairing is injective. -/
lemma HToAnn_ker_eq_bot (S : SSet.{0}) (n : ℕ) :
    LinearMap.ker (HToAnn S n) = ⊥ :=
  Submodule.ker_liftQ_eq_bot _ _ _ (ker_pairingToAnn_le S n)

/-- The descended pairing is surjective. -/
lemma HToAnn_surjective (S : SSet.{0}) (n : ℕ) : Function.Surjective (HToAnn S n) := by
  have h : LinearMap.range (HToAnn S n) = LinearMap.range (pairingToAnn S n) :=
    Submodule.range_liftQ _ _ _
  rw [← LinearMap.range_eq_top, h, LinearMap.range_eq_top]
  exact pairingToAnn_surjective S n

/-- **Rational cohomology is the dual of the homology of the chain complex.** The `n`-th rational
cohomology of a simplicial set `S` is linearly isomorphic to the annihilator of the boundaries
inside the cycles of the chain complex, i.e. to the dual of the `n`-th homology of `S`. -/
theorem H_equiv_dual_annihilator (S : SSet.{0}) (n : ℕ) :
    Nonempty (Submission.Cohomology.H S ℚ n ≃ₗ[ℚ]
      (Submission.Cohomology.chainBoundariesInCycles S ℚ n).dualAnnihilator) :=
  ⟨LinearEquiv.ofBijective (HToAnn S n)
    ⟨LinearMap.ker_eq_bot.mp (HToAnn_ker_eq_bot S n), HToAnn_surjective S n⟩⟩

end Work.Cohomology

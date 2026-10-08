import Mathlib
import Submission.Work.L2F.Props.oddsub.eigenline_setup
import Submission.Work.L2F.Props.oddsub.eigenbasis_mul_eq_det_and_eq_one

/-!
# A finite subgroup of `SL(2,F)` fixing two distinct points of the projective line is cyclic

Let `F` be a field, `E = F̄` its algebraic closure, and `G ≤ SL(2,F)` a finite subgroup.
If there are two **distinct** points `p ≠ q` of `ℙ¹(E)` which are fixed by every element of
`G` (viewed in `SL(2,E)` through the base change `F → E`), then `G` is cyclic.

The reason is linear algebra: the representatives `p.rep`, `q.rep` of two distinct points are
linearly independent, so every `g ∈ G` acts as `diag(λ_g, μ_g)` in that basis, with
`λ_g * μ_g = det = 1`.  Hence `g ↦ λ_g` is an injective group homomorphism `G → Eˣ` into the
units of a field, and a finite subgroup of the units of a domain is cyclic.

## Main results

* `Work.L2F.Props.oddsub.eq_of_smul_eq_smul`
* `Work.L2F.Props.oddsub.baseChangeSL_injective`
* `Work.L2F.Props.oddsub.linearIndependent_rep_of_ne`
* `Work.L2F.Props.oddsub.isCyclic_of_common_eigenbasis`
* `Work.L2F.Props.oddsub.isCyclic_of_fixes_two_points`

The linear-algebra input `Work.L2F.Props.oddsub.eigenbasis_mul_eq_det_and_eq_one` is proved in
its own file.
-/

namespace Work.L2F.Props.oddsub

open scoped MatrixGroups LinearAlgebra.Projectivization
open Matrix

noncomputable section

/-! ## Uniqueness of the eigenvalue on a nonzero vector -/

/-- Two scalars giving the same multiple of the same nonzero vector are equal. -/
theorem eq_of_smul_eq_smul {K : Type*} [Field K] {n : Type*} {v : n → K} (hv : v ≠ 0)
    {c d : K} (h : c • v = d • v) : c = d := by
  have h' : (c - d) • v = 0 := by rw [sub_smul, h, sub_self]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have hi' : v i ≠ 0 := by simpa using hi
  have h2 : (c - d) * v i = 0 := by
    have h3 := congrFun h' i
    simpa using h3
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact sub_eq_zero.mp h3
  · exact absurd h3 hi'

/-! ## The base change `SL(2,F) → SL(2,F̄)` is injective -/

/-- Base change of `SL(2,F)` to the algebraic closure is injective. -/
theorem baseChangeSL_injective (F : Type*) [Field F] :
    Function.Injective (baseChangeSL F) := by
  have halg : Function.Injective (algebraMap F (AlgebraicClosure F)) := by
    intro a b h
    have h1 : algebraMap F (AlgebraicClosure F) (a - b) = 0 := by
      rw [map_sub, h, sub_self]
    by_contra hab
    have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
    have h2 : algebraMap F (AlgebraicClosure F) (a - b) *
        algebraMap F (AlgebraicClosure F) (a - b)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hne, map_one]
    rw [h1, zero_mul] at h2
    exact zero_ne_one h2
  have hcoe : ∀ z : Matrix.SpecialLinearGroup (Fin 2) F,
      ((baseChangeSL F z : Matrix.SpecialLinearGroup (Fin 2) (AlgebraicClosure F)) :
          Matrix (Fin 2) (Fin 2) (AlgebraicClosure F))
        = (algebraMap F (AlgebraicClosure F)).mapMatrix (z : Matrix (Fin 2) (Fin 2) F) :=
    fun _ => rfl
  intro x y h
  have hh : ((baseChangeSL F x : Matrix.SpecialLinearGroup (Fin 2) (AlgebraicClosure F)) :
        Matrix (Fin 2) (Fin 2) (AlgebraicClosure F))
      = ((baseChangeSL F y : Matrix.SpecialLinearGroup (Fin 2) (AlgebraicClosure F)) :
        Matrix (Fin 2) (Fin 2) (AlgebraicClosure F)) :=
    congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) (AlgebraicClosure F) =>
      (z : Matrix (Fin 2) (Fin 2) (AlgebraicClosure F))) h
  have hxy : (algebraMap F (AlgebraicClosure F)).mapMatrix (x : Matrix (Fin 2) (Fin 2) F)
      = (algebraMap F (AlgebraicClosure F)).mapMatrix (y : Matrix (Fin 2) (Fin 2) F) :=
    (hcoe x).symm.trans (hh.trans (hcoe y))
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  have h3 : algebraMap F (AlgebraicClosure F) ((x : Matrix (Fin 2) (Fin 2) F) i j)
      = algebraMap F (AlgebraicClosure F) ((y : Matrix (Fin 2) (Fin 2) F) i j) := by
    have h4 := congrFun (congrFun hxy i) j
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply] using h4
  exact halg h3

/-! ## Distinct points have linearly independent representatives -/

/-- The representatives of two distinct points of `ℙ¹(F̄)` are linearly independent. -/
theorem linearIndependent_rep_of_ne (F : Type*) [Field F]
    (p q : PLineFbar F) (hpq : p ≠ q) :
    LinearIndependent (AlgebraicClosure F) ![p.rep, q.rep] := by
  refine (Projectivization.independent_mk_iff_LinearIndependent
    (Projectivization.rep_nonzero p) (Projectivization.rep_nonzero q)).mp ?_
  rw [Projectivization.mk_rep, Projectivization.mk_rep]
  exact (Projectivization.independent_pair_iff_ne p q).mpr hpq

/-! ## The abstract cyclicity criterion -/

/-- A finite group acting through `SL(2,K)` with two common eigenvectors, in a basis, is cyclic:
the eigenvalue on the first eigenvector is a group homomorphism into the multiplicative monoid
of the field `K`, and it is injective. -/
theorem isCyclic_of_common_eigenbasis {K : Type*} [Field K] {G : Type*} [Group G] [Finite G]
    (ρ : G →* Matrix.SpecialLinearGroup (Fin 2) K) (hinj : Function.Injective ρ)
    (v w : Fin 2 → K) (hv : v ≠ 0) (hind : LinearIndependent K ![v, w])
    (hB : ∀ g : G, ∃ c : K, Matrix.mulVec (ρ g : Matrix (Fin 2) (Fin 2) K) v = c • v)
    (hC : ∀ g : G, ∃ c : K, Matrix.mulVec (ρ g : Matrix (Fin 2) (Fin 2) K) w = c • w) :
    IsCyclic G := by
  classical
  choose f hf using hB
  choose f' hf' using hC
  have huniq : ∀ {c d : K}, c • v = d • v → c = d := fun h => eq_of_smul_eq_smul hv h
  have hf_one : f 1 = 1 := by
    refine huniq ?_
    rw [← hf 1, map_one ρ, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, one_smul]
  have hf_mul : ∀ g h : G, f (g * h) = f h * f g := by
    intro g h
    refine huniq ?_
    calc f (g * h) • v
        = Matrix.mulVec (ρ (g * h) : Matrix (Fin 2) (Fin 2) K) v := (hf (g * h)).symm
      _ = Matrix.mulVec ((ρ g * ρ h : Matrix.SpecialLinearGroup (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K) v := by rw [map_mul ρ g h]
      _ = Matrix.mulVec ((ρ g : Matrix (Fin 2) (Fin 2) K) *
            (ρ h : Matrix (Fin 2) (Fin 2) K)) v := by
            rw [Matrix.SpecialLinearGroup.coe_mul]
      _ = Matrix.mulVec (ρ g : Matrix (Fin 2) (Fin 2) K)
            (Matrix.mulVec (ρ h : Matrix (Fin 2) (Fin 2) K) v) := by
            rw [← Matrix.mulVec_mulVec]
      _ = Matrix.mulVec (ρ g : Matrix (Fin 2) (Fin 2) K) (f h • v) := by rw [hf h]
      _ = f h • Matrix.mulVec (ρ g : Matrix (Fin 2) (Fin 2) K) v := by
            rw [Matrix.mulVec_smul]
      _ = f h • (f g • v) := by rw [hf g]
      _ = (f h * f g) • v := by rw [smul_smul]
  have hker : ∀ g : G, f g = 1 → g = 1 := by
    intro g hg
    have hdet : (ρ g : Matrix (Fin 2) (Fin 2) K).det = 1 :=
      Matrix.SpecialLinearGroup.det_coe (ρ g)
    have hM1 : (ρ g : Matrix (Fin 2) (Fin 2) K) = 1 :=
      (eigenbasis_mul_eq_det_and_eq_one (M := (ρ g : Matrix (Fin 2) (Fin 2) K))
        v w hind (f g) (f' g) (hf g) (hf' g)).2 hdet hg
    exact hinj ((Subtype.ext (by simpa using hM1)).trans (map_one ρ).symm)
  let φ : G →* K :=
    { toFun := f
      map_one' := hf_one
      map_mul' := fun g h => (hf_mul g h).trans (mul_comm _ _) }
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    exact hker x (MonoidHom.mem_ker.mp hx)
  exact isCyclic_of_injective_ringHom φ hφinj

/-! ## The main theorem -/

theorem isCyclic_of_fixes_two_points (F : Type*) [Field F]
    (G : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) [Finite G]
    (p q : Work.L2F.Props.oddsub.PLineFbar F) (hpq : p ≠ q)
    (hp : ∀ g : G, Work.L2F.Props.oddsub.baseChangeSL F
      (g : Matrix.SpecialLinearGroup (Fin 2) F) • p = p)
    (hq : ∀ g : G, Work.L2F.Props.oddsub.baseChangeSL F
      (g : Matrix.SpecialLinearGroup (Fin 2) F) • q = q) :
    IsCyclic G := by
  classical
  have hB : ∀ g : G, ∃ c : AlgebraicClosure F,
      Matrix.mulVec (((baseChangeSL F (g : Matrix.SpecialLinearGroup (Fin 2) F)) :
          Matrix.SpecialLinearGroup (Fin 2) (AlgebraicClosure F)) :
          Matrix (Fin 2) (Fin 2) (AlgebraicClosure F)) p.rep = c • p.rep := by
    intro g
    exact (mem_fixedBy_iff_mem_eigenPointSet
      (baseChangeSL F (g : Matrix.SpecialLinearGroup (Fin 2) F)) p).mp
      (MulAction.mem_fixedBy.mpr (hp g))
  have hC : ∀ g : G, ∃ c : AlgebraicClosure F,
      Matrix.mulVec (((baseChangeSL F (g : Matrix.SpecialLinearGroup (Fin 2) F)) :
          Matrix.SpecialLinearGroup (Fin 2) (AlgebraicClosure F)) :
          Matrix (Fin 2) (Fin 2) (AlgebraicClosure F)) q.rep = c • q.rep := by
    intro g
    exact (mem_fixedBy_iff_mem_eigenPointSet
      (baseChangeSL F (g : Matrix.SpecialLinearGroup (Fin 2) F)) q).mp
      (MulAction.mem_fixedBy.mpr (hq g))
  refine isCyclic_of_common_eigenbasis (K := AlgebraicClosure F)
    ((baseChangeSL F).comp G.subtype) ?_ p.rep q.rep (Projectivization.rep_nonzero p)
    (linearIndependent_rep_of_ne F p q hpq) hB hC
  intro x y h
  exact Subtype.ext (baseChangeSL_injective F (by simpa using h))

end

end Work.L2F.Props.oddsub

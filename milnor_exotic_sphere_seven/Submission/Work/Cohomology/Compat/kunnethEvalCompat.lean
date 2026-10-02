import Mathlib
import Submission.Work.Cohomology.sphere3DiscPairDefs
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.Pullback
import Submission.Work.Cohomology.Kronecker
import Submission.Work.Cohomology.Kunneth.KunnethPullbackAux
import Submission.Work.Cohomology.cup1Identity
import Submission.Work.Cohomology.CompatTrans.Crux33.sph3DiscCupEval
import Submission.Work.Cohomology.Crux33.ezGen_isCycle

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology.Compat

noncomputable section

open Work.Cohomology

/-- **The Künneth external product of the two sphere factors of `A = S³ × S³`, in evaluated
chain-level form.**

There are `3`-cocycles `θ'` on the sphere `S³ ⊆ D⁴` (`TopCat.of (sphereInUnit 4)`) and `β` on
`Sph3T = S³` and a `6`-cycle `a` of `A = PairAT = S³ × S³ ⊆ S³ × D⁴`, such that the
Alexander–Whitney product of the pullbacks of `θ'` along `pj2A : A → S³ ⊆ D⁴` and of `β` along
`pj1A : A → S³` evaluates nontrivially on `a`.  Equivalently the external product
`H³(S³) ⊗ H³(S³) → H⁶(A) ≅ ℤ` is nonzero (Künneth).

The proof obtains the two cocycles and the cycle from the chain-level Künneth witness
`Work.Cohomology.Crux33.sph3DiscCupEval` (which produces them with the two factors in the opposite
order) and swaps the two factors of the Alexander–Whitney product with the cup-1 identity
(`Work.Cohomology.cup1Identity`): `cup α β` and `cup β α` differ by the coboundary
`d (cup1 α β)`, which evaluates to `0` on the cycle. -/
theorem kunnethEvalCompat :
    ∃ (θ' : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj (TopCat.of (Work.Cohomology.sphereInUnit 4))) 3)
      (β : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj Work.Cohomology.Sph3T) 3)
      (a : (Work.Cohomology.singularChains ℤ (TopCat.of Work.Cohomology.PairAT)).X 6),
      Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (Work.Cohomology.sphereInUnit 4))) θ' = 0
      ∧ Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj Work.Cohomology.Sph3T) β = 0
      ∧ (Work.Cohomology.singularChains ℤ (TopCat.of Work.Cohomology.PairAT)).d 6 5 a = 0
      ∧ Work.Cohomology.kronecker ℤ (TopCat.toSSet.obj (TopCat.of Work.Cohomology.PairAT))
          (Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of Work.Cohomology.PairAT))
            ((Work.Cohomology.cochainPullbackHom ℤ (TopCat.of Work.Cohomology.PairAT)
              (TopCat.of (Work.Cohomology.sphereInUnit 4)) Work.Cohomology.pj2A 3).hom θ')
            ((Work.Cohomology.cochainPullbackHom ℤ (TopCat.of Work.Cohomology.PairAT)
              Work.Cohomology.Sph3T Work.Cohomology.pj1A 3).hom β))
          a ≠ 0 := by
  obtain ⟨β₀, β₁, Δ, hβ₀, hβ₁, hΔ, hev⟩ := Work.Cohomology.Crux33.sph3DiscCupEval
  -- `β₀` lives on `Sph3T` (first factor), `β₁` on `sphereInUnit 4` (second factor).
  set α : Cochain ℤ (TopCat.toSSet.obj (TopCat.of PairAT)) 3 :=
    (cochainPullbackHom ℤ (TopCat.of PairAT) Sph3T pj1A 3).hom β₀ with hαdef
  set α' : Cochain ℤ (TopCat.toSSet.obj (TopCat.of PairAT)) 3 :=
    (cochainPullbackHom ℤ (TopCat.of PairAT) (TopCat.of (sphereInUnit 4)) pj2A 3).hom β₁ with hα'def
  have hα : cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of PairAT)) α = 0 := by
    rw [hαdef]
    exact Work.Cohomology.Kunneth.pullback_cocycle (TopCat.of PairAT) Sph3T pj1A 3 β₀ hβ₀
  have hα' : cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of PairAT)) α' = 0 := by
    rw [hα'def]
    exact Work.Cohomology.Kunneth.pullback_cocycle (TopCat.of PairAT) (TopCat.of (sphereInUnit 4)) pj2A 3 β₁ hβ₁
  have hev' : kronecker ℤ (TopCat.toSSet.obj (TopCat.of PairAT))
      (cup ℤ (TopCat.toSSet.obj (TopCat.of PairAT)) α α') Δ ≠ 0 := by
    rw [hαdef, hα'def] at hev
    exact hev
  -- the coboundary of `cup1 α α'` evaluates to `0` on the cycle `Δ`
  have hcup1 : kronecker ℤ (TopCat.toSSet.obj (TopCat.of PairAT))
      (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of PairAT))
        (cup1 ℤ (TopCat.toSSet.obj (TopCat.of PairAT)) 3 3 α α')) Δ = 0 := by
    show (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of PairAT))
        (cup1 ℤ (TopCat.toSSet.obj (TopCat.of PairAT)) 3 3 α α')) Δ = 0
    show (cup1 ℤ (TopCat.toSSet.obj (TopCat.of PairAT)) 3 3 α α')
      (((TopCat.toSSet.obj (TopCat.of PairAT)).chainComplex (ModuleCat.of ℤ ℤ)).d 6 5 Δ) = 0
    rw [show ((TopCat.toSSet.obj (TopCat.of PairAT)).chainComplex (ModuleCat.of ℤ ℤ)).d 6 5 Δ
        = 0 from hΔ, map_zero]
  -- casts in the cup-1 identity
  have hcast1 : ((Nat.sub_add_cancel (by norm_num : 1 ≤ 3 + 3)) ▸
      (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of PairAT))
        (cup1 ℤ (TopCat.toSSet.obj (TopCat.of PairAT)) 3 3 α α') :
        Cochain ℤ (TopCat.toSSet.obj (TopCat.of PairAT)) (3 + 3)))
      = cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of PairAT))
        (cup1 ℤ (TopCat.toSSet.obj (TopCat.of PairAT)) 3 3 α α') := by
    rw [Subsingleton.elim (Nat.sub_add_cancel (by norm_num : 1 ≤ 3 + 3)) rfl]
  have hcast2 : (((Nat.add_comm 3 3 : 3 + 3 = 3 + 3)) ▸
      (cup ℤ (TopCat.toSSet.obj (TopCat.of PairAT)) α' α :
        Cochain ℤ (TopCat.toSSet.obj (TopCat.of PairAT)) (3 + 3)))
      = cup ℤ (TopCat.toSSet.obj (TopCat.of PairAT)) α' α := by
    rw [Subsingleton.elim (Nat.add_comm 3 3 : 3 + 3 = 3 + 3) rfl]
  have hid := cup1Identity ℤ (TopCat.toSSet.obj (TopCat.of PairAT)) 3 3
    (by norm_num) (by norm_num) α α' hα hα'
  rw [hcast1, hcast2, show (-1:ℤ)^(3*3) = -1 from by norm_num] at hid
  have h2 := congrArg (fun (γ : Cochain ℤ (TopCat.toSSet.obj (TopCat.of PairAT)) (3+3)) =>
    kronecker ℤ (TopCat.toSSet.obj (TopCat.of PairAT)) γ Δ) hid
  rw [hcup1] at h2
  have h3 : ∀ (a b : Cochain ℤ (TopCat.toSSet.obj (TopCat.of PairAT)) (3+3)),
      kronecker ℤ (TopCat.toSSet.obj (TopCat.of PairAT)) (a - b) Δ
        = kronecker ℤ (TopCat.toSSet.obj (TopCat.of PairAT)) a Δ
          - kronecker ℤ (TopCat.toSSet.obj (TopCat.of PairAT)) b Δ := fun a b => rfl
  rw [h3] at h2
  clear hα hα' hid hcast1 hcast2 hcup1 h3
  refine ⟨β₁, β₀, Δ, hβ₁, hβ₀, hΔ, ?_⟩
  rw [← hα'def, ← hαdef]
  intro h0
  have hB : kronecker ℤ (TopCat.toSSet.obj (TopCat.of PairAT))
      ((-1 : ℤ) • cup ℤ (TopCat.toSSet.obj (TopCat.of PairAT)) α' α) Δ
      = - kronecker ℤ (TopCat.toSSet.obj (TopCat.of PairAT))
          (cup ℤ (TopCat.toSSet.obj (TopCat.of PairAT)) α' α) Δ := by
    rw [kronecker_smul]
    simp
  rw [hB, h0] at h2
  have hz : kronecker ℤ (TopCat.toSSet.obj (TopCat.of PairAT))
      (cup ℤ (TopCat.toSSet.obj (TopCat.of PairAT)) α α') Δ = 0 := by
    simpa using h2.symm
  exact hev' hz
end

end Work.Cohomology.Compat

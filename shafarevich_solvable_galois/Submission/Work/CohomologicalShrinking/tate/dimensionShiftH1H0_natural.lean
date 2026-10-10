import Mathlib.Tactic.Abel
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Submission.Work.GroupCohomology.ConnectingLift
import Submission.Work.GroupCohomology.CyclicTriv
import Submission.Work.GroupCohomology.Shapiro
import Submission.Work.GroupCohomology.TrivialGroup
import Submission.Work.GroupCohomology.Vanishing
import Submission.Work.Tate.DimensionShiftH
import Submission.Work.Tate.Equivs
import Submission.Work.Tate.Hm1ToCoinv_injective
import Submission.Work.Tate.coind_augmentation_eq_ker_norm
import Submission.Work.Tate.coind_norm_eq_const
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking.tate

/-- **Naturality of the dimension-shifting isomorphism `Ĥ⁰(G, A^*) ≅ H¹(G, A)`.**

The isomorphism `Work.Tate.dimensionShiftH1H0Symm` is by definition the connecting map
`δ₀ : Ĥ⁰(G, A^*) → H¹(G, A)` of the shift sequence `0 → A → Coind(A) → A^* → 0`.  Here we prove
that this connecting map is natural in a map of coefficients `φ : A → B` together with a
compatible map `ψ : A^* → B^*` (i.e. one commuting with the projections `Coind(A) → A^*` and
`Coind(B) → B^*`): the square

`Ĥ⁰(G, A^*) --δ₀--> H¹(G, A)`
`   | ψ_*                 | φ_*`
`Ĥ⁰(G, B^*) --δ₀--> H¹(G, B)`

commutes.  On representatives this is the statement that the two obvious cocycles
`φ ∘ delta0Cocycle_A(c)` and `delta0Cocycle_B(ψ_* c)` differ by the coboundary `γ ↦ γ • d - d`,
where `d` measures the failure of the chosen lifts of `ψ(c)` in `Coind(B)` to agree. -/
theorem dimensionShiftH1H0_natural (p : ℕ) (G : Type*) [Group G] [Fintype G]
    (A : Type*) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
      [SMulCommClass G (ZMod p) A]
    (B : Type*) [AddCommGroup B] [Module (ZMod p) B] [DistribMulAction G B]
      [SMulCommClass G (ZMod p) B]
    (φ : A →ₗ[ZMod p] B) (hφ : ∀ (γ : G) (a : A), φ (γ • a) = γ • φ a)
    (ψ : Work.Tate.coindShift G A →+ Work.Tate.coindShift G B)
    (hψproj : ∀ x : G → A,
      ψ (Work.Tate.coindProj G A x) = Work.Tate.coindProj G B (Work.Tate.coindMap (φ.toAddMonoidHom) x))
    (hψ : ∀ (γ : G) (x : Work.Tate.coindShift G A), ψ (γ • x) = γ • ψ x) :
    (Work.GroupCohomology.mapH1 G (φ.toAddMonoidHom) hφ).comp
        (Work.Tate.dimensionShiftH1H0Symm G A).toAddMonoidHom
      = (Work.Tate.dimensionShiftH1H0Symm G B).toAddMonoidHom.comp
          (Work.Tate.H0Map G (Work.Tate.coindShift G A) (Work.Tate.coindShift G B) ψ hψ) := by
  -- Both `dimensionShiftH1H0Symm` are, definitionally, the connecting maps `δ₀` of the shift
  -- sequences.
  rw [show (Work.Tate.dimensionShiftH1H0Symm G A).toAddMonoidHom
        = (Work.Tate.coindSES G A).delta0 from rfl,
      show (Work.Tate.dimensionShiftH1H0Symm G B).toAddMonoidHom
        = (Work.Tate.coindSES G B).delta0 from rfl]
  apply AddMonoidHom.ext
  intro x
  induction x using Work.Tate.H0_induction_on with
  | h c =>
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, Work.Tate.SES.delta0_H0π,
      Work.Tate.H0Map_H0π, Work.Tate.SES.delta0_H0π]
    -- The fixed point of `B^*` coding `ψ c`.
    set F := Work.Tate.mapFixed G (Work.Tate.coindShift G A) (Work.Tate.coindShift G B) ψ hψ c
      with hF
    -- Rewrite the left-hand side through the formula for `mapH1` on cocycle classes.
    have hmap : (Work.GroupCohomology.mapH1 G (φ.toAddMonoidHom) hφ)
          ((Work.GroupCohomology.H1π G A)
            ⟨(Work.Tate.coindSES G A).delta0Cocycle c,
              (Work.Tate.coindSES G A).delta0Cocycle_mem_Z1 c⟩)
        = (Work.GroupCohomology.H1π G B)
            (Work.GroupCohomology.mapZ1 G (φ.toAddMonoidHom) hφ
              ⟨(Work.Tate.coindSES G A).delta0Cocycle c,
                (Work.Tate.coindSES G A).delta0Cocycle_mem_Z1 c⟩) :=
      Work.GroupCohomology.mapH1_H1π G (φ.toAddMonoidHom) hφ _
    rw [hmap]
    -- ## The element `d ∈ B` measuring the discrepancy of the two lifts
    have hinj : Function.Injective (Work.Tate.coindUnit G B) := by
      intro x y h
      have := congrFun h 1
      simpa using this
    -- The diagonal inclusion is compatible with postcomposition.
    have hφunit : ∀ t : A, Work.Tate.coindUnit G B (φ t)
        = Work.Tate.coindMap (φ.toAddMonoidHom) (Work.Tate.coindUnit G A t) := by
      intro t; funext x
      simp only [Work.Tate.coindUnit_apply, Work.Tate.coindMap_apply]
      exact (hφ x t).symm
    have hFcoe : (F : Work.Tate.coindShift G B) = ψ (c : Work.Tate.coindShift G A) := by
      rw [hF, Work.Tate.mapFixed_apply]
    have hsecA : Work.Tate.coindProj G A ((Work.Tate.coindSES G A).sec (c : Work.Tate.coindShift G A))
        = (c : Work.Tate.coindShift G A) := (Work.Tate.coindSES G A).sec_spec (c : _)
    have hsecB : Work.Tate.coindProj G B ((Work.Tate.coindSES G B).sec (F : Work.Tate.coindShift G B))
        = (F : Work.Tate.coindShift G B) := (Work.Tate.coindSES G B).sec_spec (F : _)
    -- The two lifts `φ(sec_A c)` and `sec_B(ψ c)` of `ψ c` project to the same element of `B^*`.
    have hprojA : Work.Tate.coindProj G B (Work.Tate.coindMap (φ.toAddMonoidHom)
          ((Work.Tate.coindSES G A).sec (c : Work.Tate.coindShift G A)))
        = ψ (c : Work.Tate.coindShift G A) := by
      rw [← hψproj ((Work.Tate.coindSES G A).sec (c : Work.Tate.coindShift G A)), hsecA]
    have hprojB : Work.Tate.coindProj G B ((Work.Tate.coindSES G B).sec (F : Work.Tate.coindShift G B))
        = ψ (c : Work.Tate.coindShift G A) := by
      rw [hsecB, hFcoe]
    have hmem : Work.Tate.coindMap (φ.toAddMonoidHom)
          ((Work.Tate.coindSES G A).sec (c : Work.Tate.coindShift G A))
        - (Work.Tate.coindSES G B).sec (F : Work.Tate.coindShift G B)
        ∈ Work.Tate.coindDiag G B := by
      rw [← Work.Tate.coindProj_eq_zero_iff, map_sub, hprojA, hprojB, sub_self]
    obtain ⟨d, hd⟩ := (Work.Tate.mem_coindDiag_iff G B).mp hmem
    have hd' : Work.Tate.coindMap (φ.toAddMonoidHom)
          ((Work.Tate.coindSES G A).sec (c : Work.Tate.coindShift G A))
        - (Work.Tate.coindSES G B).sec (F : Work.Tate.coindShift G B)
        = Work.Tate.coindUnit G B d := hd
    have hfA : ∀ γ : G, Work.Tate.coindUnit G A ((Work.Tate.coindSES G A).delta0Cocycle c γ)
        = γ • (Work.Tate.coindSES G A).sec (c : Work.Tate.coindShift G A)
          - (Work.Tate.coindSES G A).sec (c : Work.Tate.coindShift G A) :=
      fun γ => (Work.Tate.coindSES G A).f_delta0Cocycle c γ
    have hfB : ∀ γ : G, Work.Tate.coindUnit G B ((Work.Tate.coindSES G B).delta0Cocycle F γ)
        = γ • (Work.Tate.coindSES G B).sec (F : Work.Tate.coindShift G B)
          - (Work.Tate.coindSES G B).sec (F : Work.Tate.coindShift G B) :=
      fun γ => (Work.Tate.coindSES G B).f_delta0Cocycle F γ
    -- ## The two cocycles differ by the coboundary `γ ↦ γ • d - d`
    have key : ∀ γ : G, φ ((Work.Tate.coindSES G A).delta0Cocycle c γ)
        - (Work.Tate.coindSES G B).delta0Cocycle F γ = γ • d - d := by
      intro γ
      apply hinj
      calc Work.Tate.coindUnit G B (φ ((Work.Tate.coindSES G A).delta0Cocycle c γ)
              - (Work.Tate.coindSES G B).delta0Cocycle F γ)
          = Work.Tate.coindUnit G B (φ ((Work.Tate.coindSES G A).delta0Cocycle c γ))
            - Work.Tate.coindUnit G B ((Work.Tate.coindSES G B).delta0Cocycle F γ) :=
            map_sub _ _ _
        _ = Work.Tate.coindMap (φ.toAddMonoidHom)
              (Work.Tate.coindUnit G A ((Work.Tate.coindSES G A).delta0Cocycle c γ))
            - (γ • (Work.Tate.coindSES G B).sec (F : Work.Tate.coindShift G B)
                - (Work.Tate.coindSES G B).sec (F : Work.Tate.coindShift G B)) := by
              rw [hφunit ((Work.Tate.coindSES G A).delta0Cocycle c γ), hfB γ]
        _ = Work.Tate.coindMap (φ.toAddMonoidHom)
              (γ • (Work.Tate.coindSES G A).sec (c : Work.Tate.coindShift G A)
                - (Work.Tate.coindSES G A).sec (c : Work.Tate.coindShift G A))
            - (γ • (Work.Tate.coindSES G B).sec (F : Work.Tate.coindShift G B)
                - (Work.Tate.coindSES G B).sec (F : Work.Tate.coindShift G B)) := by
              rw [hfA γ]
        _ = (γ • Work.Tate.coindMap (φ.toAddMonoidHom)
                ((Work.Tate.coindSES G A).sec (c : Work.Tate.coindShift G A))
              - Work.Tate.coindMap (φ.toAddMonoidHom)
                ((Work.Tate.coindSES G A).sec (c : Work.Tate.coindShift G A)))
            - (γ • (Work.Tate.coindSES G B).sec (F : Work.Tate.coindShift G B)
                - (Work.Tate.coindSES G B).sec (F : Work.Tate.coindShift G B)) := by
              rw [map_sub, Work.Tate.coindMap_equiv (φ.toAddMonoidHom) hφ]
        _ = γ • (Work.Tate.coindMap (φ.toAddMonoidHom)
                ((Work.Tate.coindSES G A).sec (c : Work.Tate.coindShift G A))
              - (Work.Tate.coindSES G B).sec (F : Work.Tate.coindShift G B))
            - (Work.Tate.coindMap (φ.toAddMonoidHom)
                ((Work.Tate.coindSES G A).sec (c : Work.Tate.coindShift G A))
              - (Work.Tate.coindSES G B).sec (F : Work.Tate.coindShift G B)) := by
              rw [Work.Tate.coind_smul_sub]; abel
        _ = γ • Work.Tate.coindUnit G B d - Work.Tate.coindUnit G B d := by rw [hd']
        _ = Work.Tate.coindUnit G B (γ • d) - Work.Tate.coindUnit G B d := by
              rw [Work.Tate.coindUnit_equiv]
        _ = Work.Tate.coindUnit G B (γ • d - d) := (map_sub _ _ _).symm
    -- ## Conclusion: the two classes in `H¹(G, B)` agree
    refine (Work.GroupCohomology.H1pi_eq_iff
      (Work.GroupCohomology.mapZ1 G (φ.toAddMonoidHom) hφ
        ⟨(Work.Tate.coindSES G A).delta0Cocycle c,
          (Work.Tate.coindSES G A).delta0Cocycle_mem_Z1 c⟩)
      ⟨(Work.Tate.coindSES G B).delta0Cocycle F,
        (Work.Tate.coindSES G B).delta0Cocycle_mem_Z1 F⟩).mpr ?_
    rw [Work.GroupCohomology.mem_B1_iff]
    refine ⟨d, ?_⟩
    funext γ
    rw [Work.GroupCohomology.d0_apply]
    show γ • d - d = φ ((Work.Tate.coindSES G A).delta0Cocycle c γ)
        - (Work.Tate.coindSES G B).delta0Cocycle F γ
    exact (key γ).symm

end Work.CohomologicalShrinking.tate

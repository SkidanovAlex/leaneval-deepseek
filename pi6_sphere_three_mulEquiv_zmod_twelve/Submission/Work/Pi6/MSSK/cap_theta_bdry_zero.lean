import Mathlib
import Submission.Work.Pi6.MSSK.CapThetaBasic
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSSK

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
open CategoryTheory CategoryTheory.Limits Simplicial Opposite

/-- **Combinatorics of `∂Δ[s]`**: a simplex `α : Δ[s] _⦋N⦌` whose front `s`-face is the top
simplex of `Δ[s]` (equivalently, whose underlying monotone map is the identity on the first `s+1`
vertices) is *surjective*, hence is not in the boundary `∂Δ[s]`.

This is the geometric input of `cap_theta_bdry_zero`: the cochain `thetaTop` is the indicator of
the simplices over the top simplex, and a front face over the top simplex forces the whole simplex
to be surjective, so it cannot lie over `∂Δ[s]`. -/
lemma notMem_boundary_of_frontIncl {s N : ℕ} (h : s ≤ N)
    (α : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) _⦋N⦌)
    (hα : Work.Cohomology.frontIncl s N h ≫ SSet.stdSimplex.objEquiv α = 𝟙 ⦋s⦌) :
    α ∉ (SSet.boundary s).obj (op ⦋N⦌) := by
  rw [SSet.mem_boundary_iff_notMem_range]
  push Not
  intro j
  refine ⟨(Work.Cohomology.frontIncl s N h).toOrderHom j, ?_⟩
  refine Fin.ext ?_
  have h2 : (SSet.stdSimplex.objEquiv α).toOrderHom.comp
      (Work.Cohomology.frontIncl s N h).toOrderHom = OrderHom.id := by
    rw [← SimplexCategory.comp_toOrderHom, hα]
    exact SimplexCategory.id_toOrderHom _
  have h3 := congrArg (fun (f : OrderHom (Fin (s+1)) (Fin (s+1))) => f j) h2
  simp only [OrderHom.comp_coe, Function.comp_apply, OrderHom.id_coe] at h3
  simpa using congrArg Fin.val h3

/-- **`thetaTop` vanishes on the boundary piece.**  `thetaTop` is the `s`-cochain on
`T_σ = Δ[s] ×_{Sing B} Sing E` which is `1` exactly on the simplices over the top simplex of
`Δ[s]`; capping it with a chain of the boundary subcomplex `∂T_σ = bdryAlong σ` (the preimage of
`∂Δ[s]`) therefore gives `0`.

This is step (b) of the cap/transport lemma: for a chain `c` representing a class in
`pieceAlong σ = C(T_σ)/C(∂T_σ)`, the boundary `∂c` is a chain of `∂T_σ`, so `thetaTop ⌢ ∂c = 0`,
which is what makes `thetaTop ⌢ c` a cycle. -/
theorem cap_theta_bdry_zero (R : Type) [CommRing R] [Nontrivial R] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) {s K : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (y : (Work.SSSR.sCC R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ)).X (s + K)) :
    Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
        (Work.Pi6.MSSK.thetaTop R p σ) K
        ((Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι).f (s + K) y) = 0 := by
  -- On the generators of the boundary subcomplex, the cap product with `thetaTop` vanishes:
  -- the front `s`-face of a simplex of `∂T_σ` projects to a simplex of `∂Δ[s]`, which cannot be
  -- the top simplex.
  have key : ∀ (w : (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ : SSet.{0}) _⦋s+K⦌),
      (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).ιChainComplex (R := ModuleCat.of R R) w.1
        ≫ Work.Cohomology.capHom R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
            (Work.Pi6.MSSK.thetaTop R p σ) K = 0 := by
    intro w
    -- the cap product on the generator `w`
    rw [Work.Cohomology.ιChainComplex_capHom]
    rw [Work.Pi6.MSSK.genEval_thetaTop]
    have hfront : ¬ ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋s⦌)
        (Work.Cohomology.frontFace (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) s (s+K)
          (Nat.le_add_right s K) w.1) = Work.Pi6.MSSK.topS s) := by
      intro htop
      -- the front face of the projection is the projection of the front face
      have h1 : Work.Cohomology.frontFace
          (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) s (s+K)
          (Nat.le_add_right s K) ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋s+K⦌) w.1)
          = Work.Pi6.MSSK.topS s := by
        rw [← Work.Pi6.MSSK.fst_frontFace p σ (Nat.le_add_right s K) w.1]
        exact htop
      have h2 : Work.Cohomology.frontIncl s (s+K) (Nat.le_add_right s K)
          ≫ SSet.stdSimplex.objEquiv
              ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋s+K⦌) w.1) = 𝟙 ⦋s⦌ :=
        (Work.Pi6.MSSK.frontFace_eq_topS_iff _ _).mp h1
      -- ... but `w` lies over `∂Δ[s]`
      exact notMem_boundary_of_frontIncl _ _ h2 w.2
    rw [Work.Pi6.MSSK.thetaVal, if_neg hfront]
    simp
  -- Hence the chain-level composite `sCCMap ι ≫ capHom thetaTop` is zero: check it on generators.
  have hcomp : (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι).f (s + K)
      ≫ Work.Cohomology.capHom R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
          (Work.Pi6.MSSK.thetaTop R p σ) K = 0 := by
    apply SSet.chainComplex_hom_ext
    intro w
    -- the generator of the subcomplex maps to the generator of the ambient complex
    have hnat : (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ : SSet.{0}).ιChainComplex
          (R := ModuleCat.of R R) w
        ≫ (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι).f (s+K)
        = (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).ιChainComplex (R := ModuleCat.of R R) w.1 := by
      rw [show (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι).f (s+K)
          = (SSet.chainComplexMap (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι
              (ModuleCat.of R R)).f (s+K) from rfl]
      rw [SSet.ι_chainComplexMap_f]
      rfl
    rw [← Category.assoc, hnat, key w]
    simp
  -- Evaluate the chain-level identity at `y`.
  have h2 := congrArg (fun (g : (Work.SSSR.sCC R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ)).X (s+K) ⟶
      (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X K) =>
        ModuleCat.Hom.hom g y) hcomp
  simpa [Work.Cohomology.cap, ModuleCat.hom_comp] using h2

end Work.Pi6.MSSK

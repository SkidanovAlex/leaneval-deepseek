import Mathlib
import Submission.Work.Pi6.MSSK.Defs
import Submission.Work.SSSR.serreE1Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

/-- The `s`-simplices of the standard simplex `Δ[s]` are the monotone self-maps of `[s]`; the only
injective one is the identity, i.e. the top simplex `topS s`.  Hence every `s`-simplex of `Δ[s]`
other than `topS s` is degenerate. -/
lemma stdSimplex_mem_degenerate_of_ne_topS {s : ℕ}
    (x : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) _⦋s⦌)
    (hx : x ≠ Work.Pi6.MSSK.topS s) :
    x ∈ SSet.degenerate (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) s := by
  rw [SSet.mem_degenerate_iff_notMem_nonDegenerate]
  intro hnd
  apply hx
  have hmono : Mono (SSet.stdSimplex.objEquiv x) :=
    (SSet.stdSimplex.mem_nonDegenerate_iff_mono x).mp hnd
  have h := @SimplexCategory.eq_id_of_mono _ (SSet.stdSimplex.objEquiv x) hmono
  show x = _
  rw [← SSet.stdSimplex.objEquiv.symm_apply_apply x, h, Work.Pi6.MSSK.topS]

/-- **The pullback of a normalised cochain is constant on the top simplex.**  For a simplicial set
`X`, the `s`-simplices of the standard simplex `Δ[s]` are the monotone maps `[s] → [s]`; every such
map different from the identity is non-injective, hence factors through a degeneracy, so a cochain
vanishing on degenerate simplices (`SSet.degenerate`) takes the value `0` on it.  Consequently, for
a map `p : E → B`, a simplex `σ : Δ[s] → Sing B` and the pullback `T_σ = Δ[s] ×_{Sing B} Sing E`,
the pullback of a normalised `s`-cochain `β` of `B` along `T_σ → Δ[s] → Sing B` is `β(σ)` on the
simplices of `T_σ` lying over the identity of `Δ[s]` and `0` elsewhere: it is `β(σ) • thetaTop`.
This is the combinatorial input (`γ = id` vs `γ ≠ id` in the Eilenberg–Zilber decomposition of the
Serre filtration) for the multiplicativity of the `E_2` page of the Serre spectral sequence. -/
theorem normalizedPullback (𝕜 : Type) [CommRing 𝕜] {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) {s : ℕ} (β : Work.Cohomology.Cochain 𝕜 (Work.SSSR.sSing B) s)
    (hβ : ∀ (τ : (Work.SSSR.sSing B) _⦋s⦌),
      τ ∈ SSet.degenerate (Work.SSSR.sSing B) s → Work.Cohomology.genEval 𝕜 (Work.SSSR.sSing B) β τ = 0)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋s⦌) :
    Work.Cohomology.genEval 𝕜 (Work.SSSR.sSing B) β
        ((ConcreteCategory.hom ((pullback.fst σ (Work.SSSR.sSingP p) ≫ σ).app (op ⦋s⦌))) w)
      = Work.Cohomology.genEval 𝕜 (Work.SSSR.sSing B) β
          (σ.app (op ⦋s⦌) (Work.Pi6.MSSK.topS s)) *
        Work.Pi6.MSSK.thetaVal 𝕜 p σ w := by
  classical
  -- the simplex of `Δ[s]` underlying `w`
  set x : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) _⦋s⦌ :=
    (pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋s⦌) w with hx
  -- the left hand side is `β` evaluated at `σ x`
  have hkey : Work.Cohomology.genEval 𝕜 (Work.SSSR.sSing B) β
        ((ConcreteCategory.hom ((pullback.fst σ (Work.SSSR.sSingP p) ≫ σ).app (op ⦋s⦌))) w)
      = Work.Cohomology.genEval 𝕜 (Work.SSSR.sSing B) β (σ.app (op ⦋s⦌) x) := rfl
  rw [hkey]
  -- `thetaVal` is the indicator of `x = topS s`
  have htheta : Work.Pi6.MSSK.thetaVal 𝕜 p σ w
      = (if x = Work.Pi6.MSSK.topS s then (1 : 𝕜) else 0) := by
    classical
    rfl
  rw [htheta]
  split_ifs with htop
  · -- `x` is the top simplex: both sides are `β(σ (topS s))`
    rw [htop, mul_one]
  · -- otherwise `x` is degenerate, so `σ x` is a degenerate simplex of `Sing B` and `β` kills it
    rw [mul_zero]
    exact hβ (σ.app (op ⦋s⦌) x)
      (SSet.degenerate_app_apply (stdSimplex_mem_degenerate_of_ne_topS x htop) σ)

end Work.Pi6.MSS

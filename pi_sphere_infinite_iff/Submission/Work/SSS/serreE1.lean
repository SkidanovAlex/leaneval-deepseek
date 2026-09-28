import Mathlib
import Submission.Work.SSS.serreE1Main
import Submission.Work.SSS.serreE1Chain

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits
open scoped Topology

/-- **The first page of the Serre spectral sequence.**  For a Serre fibration `p : E → B` over a
simply connected base, the E¹ page of the Serre filtration of `C_*(E)` — the row complex
`E1Complex ξ t` with terms `E¹_{s,t} = H_{s+t}(F_s/F_{s-1})` and differential `d¹` — is isomorphic,
as a chain complex, to the **normalized** (non-degenerate) singular chains of the base tensored with
the homology of the fibre, `N_*(B) ⊗ H_t(F)` (`F = p⁻¹(p e₀)`).

Indeed the graded piece `F_s/F_{s-1}` is spanned by the simplices whose image in `Sing B` has
nondegenerate dimension exactly `s`, so `E¹_{s,t}` is free on the nondegenerate `s`-simplices of
`Sing B` tensored with `H_t(F)`; the differential `d¹` keeps exactly the nondegenerate faces, which
is the differential of the normalized Moore complex.  The isomorphism is the composite of the
Eilenberg–Zilber decomposition of the graded pieces (a sum, over the nondegenerate `s`-simplices
`σ` of `Sing B`, of the "σ-piece" `H_{s+t}(T_σ, ∂T_σ)`), the computation
`H_{s+t}(T_σ, ∂T_σ) ≅ H_t(F_{σ(v₀)})` by prism contraction, and the identification of the fibres
`H_t(F_b) ≅ H_t(F)` along paths (well defined, and flat, because `B` is simply connected). -/
theorem serreE1 (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (e₀ : E)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (ξ : Work.SSS.Filtration (Work.Cohomology.singularChains ℤ (TopCat.of E)))
    (hξ : ξ.F = Work.SSS.natShift ⋙
      Work.StemsB.serreChainFiltration (TopCat.toSSet.map (TopCat.ofHom p)) ℤ) (t : ℕ) :
    Nonempty (Work.SSS.E1Complex ξ t ≅
      Work.SSS.tensorComplex
        ((TopCat.toSSet.obj (TopCat.of B)).normalizedChainComplex (ModuleCat.of ℤ ℤ))
        ((Work.Cohomology.singularChains ℤ
          (TopCat.of (Work.StemsB.fibre p (p e₀)))).homology t)) :=
  Work.SSS.serreE1_of_chainCondition p e₀ hfib hconn t
    (Work.SSS.serreE1_chainCondition p e₀ hfib hconn t) ξ hξ

end Work.SSS

import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.SSS.serreE1Defs
import Submission.Work.StemsB.Fibrations
import Submission.Work.Cohomology.Chains
import Submission.Work.Serre.serreE2dSimplex
import Submission.Work.SSS.serreE1PieceDefs
import Submission.Work.SSS.pieceContraction
import Submission.Work.SSS.pieceHornAcyclic
import Submission.Work.SSS.pieceBdryHornIso
import Submission.Work.SSS.pieceConnectingIso
import Submission.Work.SSS.pieceAlongZero
import Submission.Work.SSS.sigmaVert_face

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

/-- **The σ-piece of the Serre filtration over a simplex.**  For a Serre fibration `p : E → B`, a
simplex `σ : Δ[s] ⟶ Sing B` of the base and `k : ℕ`, the relative homology
`H_{s+k}(T_σ, ∂T_σ)` of the pullback `T_σ = Δ[s] ×_{Sing B} Sing E` over the boundary
`∂T_σ = (∂Δ[s]) ×_{Sing B} Sing E` is the homology `H_k(F)` of the fibre of `p` over the `0`-th
vertex of `σ` (`Work.SSS.sigmaVert σ`).

This is `REFS/NOTES_LEAD_SSS.md` §1(b)–(d).  `T_σ` is the *simplicial* pullback of the singular
simplicial sets, whose `n`-simplices over `σ` are the pairs `(u, τ)` with `u : [n] ⟶ [s]` monotone
and `p ∘ τ = σ ∘ |u|`; `∂T_σ` is the part with `u` non-surjective, so
`(pieceAlong (sSingP p) σ)_n` is free on the pairs with `u` surjective, and its homology in degree
`s + k` is `H_{s+k}(T_σ, ∂T_σ)`.

Two possible routes:

* (topological, probably cheapest)  `T_σ ↪ Sing (Δ[s] ×_B E)`, `(u,τ) ↦ (|u|, τ)`, is an
  inclusion of simplicial sets; show that it is a homology isomorphism on the relative complexes
  (the quotient is spanned by the singular simplices of the pullback whose first coordinate is not
  affine, and is acyclic — e.g. by the same prism construction), and then apply
  `Work.Serre.serreE2dSimplex` to the pullback of `p` along the continuous map `σ`
  (`(TopCat.toSSetObjEquivT … (SSet.yonedaEquiv σ))`), whose value at `v₀` is `sigmaVert σ` by
  definition.  See `Submission/Work/Serre/serreE2dSimplex.lean`, which computes
  `H_{k+s}(C(τ^*E)/C(τ^*E|_{∂})) ≅ H_k(p⁻¹(τ v₀))` for `τ : Δ[s] → B`.

* (simplicial, the notes' plan)  Construct the "coherent lifts" `Φ_τ : Δ[s] × Δ^k → E` of the
  simplex `σ` (relative cube HLP, `Work.Serre.serreE2a` / `Work.StemsB.IsSerreFibration`) and the
  chain map `C_*(F) → C(T_σ)/C(∂T_σ)` of `NOTES_LEAD_SSS.md` §1(c), and prove it is a quasi-iso by
  the prism contraction of §1(d).  The prism combinatorics already exist in the workspace:
  `Work.Serre.prismChain`, `Work.Serre.prismChainBoundary` (`Submission/Work/Stems/PerSimplex/`),
  `Work.Serre.prismSimplex`, `Work.Serre.hpChain` (`Submission/Work/Serre/homotopyPrism*.lean`).

Vocabulary: `Submission/Work/SSS/serreE1Defs.lean` (`Work.SSS.sSing`, `Work.SSS.sSingP`,
`Work.SSS.pullAlong`, `Work.SSS.bdryAlong`, `Work.SSS.pieceAlong`, `Work.SSS.sigmaVert`),
`Work.StemsB.IsSerreFibration`, `Work.StemsB.fibre`, `Work.Cohomology.singularChains`.

Do NOT use `sorry`, `axiom` or `admit`. -/
theorem serreE1Piece {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (hfib : Work.StemsB.IsSerreFibration p) (s k : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSS.sSing B) :
    Nonempty ((Work.SSS.pieceAlong (Work.SSS.sSingP p) σ).homology (s + k) ≅
      (Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.StemsB.fibre p (Work.SSS.sigmaVert σ)))).homology k) := by
  induction s with
  | zero =>
    obtain ⟨e⟩ := Work.SSS.pieceAlongZero p σ
    rw [Nat.zero_add]
    exact ⟨HomologicalComplex.homologyMapIso e k⟩
  | succ t ih =>
    obtain ⟨g, H, hg, hH⟩ :=
      Work.SSS.pieceContraction p hfib (Nat.succ_le_succ (Nat.zero_le t)) σ
    have hZero : ∀ (j : ℕ), IsZero ((Work.SSS.pieceHornC (Work.SSS.sSingP p) σ).homology j) :=
      fun j => ModuleCat.isZero_iff_subsingleton.mpr
        (Work.SSS.pieceHornAcyclic p σ g H hg hH j)
    obtain ⟨e1⟩ :=
      Work.SSS.pieceConnectingIso (Work.SSS.sSingP p) t σ (t + 1 + k) (by omega) (hZero _) (hZero _)
    obtain ⟨e2⟩ := Work.SSS.pieceBdryHornIso (Work.SSS.sSingP p) t σ
    obtain ⟨e3⟩ := ih (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ)
    have h1 : t + 1 + k - 1 = t + k := by omega
    have h2 : Fin.last (t+1) ≠ (0 : Fin (t+2)) := by
      intro h
      have hv := congrArg Fin.val h
      simp [Fin.last] at hv
    have hsv := Work.SSS.sigmaVert_face (Fin.last (t+1)) h2 σ
    exact ⟨e1 ≪≫
      eqToIso (congrArg (fun (m : ℕ) =>
        (Work.SSS.pieceBdryHornC (Work.SSS.sSingP p) σ).homology m) h1) ≪≫
      HomologicalComplex.homologyMapIso e2 (t + k) ≪≫ e3 ≪≫
      eqToIso (congrArg (fun (x : B) =>
        (Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre p x))).homology k) hsv)⟩

end Work.SSS

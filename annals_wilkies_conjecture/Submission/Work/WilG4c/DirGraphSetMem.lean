/-
  WilG4c — `DirGraphSetMem`: the **good piece** of the graph of the directional derivative is
  `Ω`-definable.

  If the `ε`-`δ` derivative relation `epsFDerivSet N φ` is `Ω F D (N+N)`-definable, then the set
  `dirGraphSet N φ e = {x | ∃ c, HasFDerivAt φ (Lin c) (Fin.init x) ∧ x (last N) = Lin c e}` of
  points `(w, fderiv φ w e)` with `w` a differentiability point of `φ` is `Ω`-definable in `ℝ^{N+1}`
  with format `F + K` and degree `D + 3` (`K` a constant depending only on `N`).

  The set-theoretic content is the identity (`FDerivDirDefs.projLastIter_dirRelSet`)

      projLastIter (N+1) N (dirRelSet N φ e) = dirGraphSet N φ e,

  where `dirRelSet N φ e = {p | p ∘ dirSub N ∈ epsFDerivSet N φ} ∩ {p | eval p (dirLinPoly N e) = 0}`
  is the pullback of `epsFDerivSet` along the coordinate map `dirSub N` (which reads a point of
  `ℝ^{(N+1)+N}` as an `(x,c)`-point of `ℝ^{N+N}`), intersected with the linear hypersurface
  `u = Σⱼ cⱼ eⱼ`.

  The `Ω`-bookkeeping is therefore: a coordinate substitution (`Ω` is closed under pullback along
  arbitrary `σ : Fin n → Fin N`, `GraphComp.subst_mem`), one hypersurface (`SOMin.hyp`, degree `1`),
  a binary intersection (format `+1`, degrees added: `+2+1 = +3`), and `N` projections
  (`projLastIter_mem`).
-/
import Mathlib
import Submission.Work.WilG4c.FDerivDirDefs
import Submission.Work.WilG4c.GraphOfComp

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG Work.WilG0 Work.WilG1

/-- The format cost: substituting into the ambient space `ℝ^{(N+1)+N}` along `dirSub N`
(`2 * (ambient + source) + 1`), one `+1` for the intersection, and `N + (N+1)` for the
projection of the coefficient block. -/
private def dirK (N : ℕ) : ℕ :=
  max (2 * (((N + 1) + N) + (N + N)) + 1) ((N + 1) + N) + 1 + N + (N + 1)

theorem DirGraphSetMem (S : WilkiesDesign.SOMin) (N : ℕ) (e : Fin N → ℝ) :
    ∃ K : ℕ, ∀ (A : ℕ) (b : Polynomial ℕ) (D : ℕ) (φ : (Fin N → ℝ) → ℝ),
      Work.WilG4c.epsFDerivSet N φ ∈ S.Ω A (b.eval D) (N + N) →
      Work.WilG4c.dirGraphSet N φ e ∈
        S.Ω (A + K) ((b + Polynomial.C 3).eval D) (N + 1) := by
  refine ⟨dirK N, fun A b D φ h => ?_⟩
  -- 1. Pull `epsFDerivSet N φ ⊆ ℝ^{N+N}` back along `dirSub N : Fin (N+N) → Fin ((N+1)+N)`.
  --    Format `A + 2 * (((N+1)+N) + (N+N)) + 1`, degree `b.eval D + 2`.
  have hsub : {p : Fin ((N + 1) + N) → ℝ |
        p ∘ Work.WilG4c.dirSub N ∈ Work.WilG4c.epsFDerivSet N φ} ∈
      S.Ω (A + 2 * (((N + 1) + N) + (N + N)) + 1) (b.eval D + 2) ((N + 1) + N) :=
    Work.WilG4c.GraphComp.subst_mem S (Work.WilG4c.dirSub N) h
  -- rewrite the degree as `(b + C 2).eval D`, the form `Omega.inter₂` consumes
  have hsub' : {p : Fin ((N + 1) + N) → ℝ |
        p ∘ Work.WilG4c.dirSub N ∈ Work.WilG4c.epsFDerivSet N φ} ∈
      S.Ω (A + 2 * (((N + 1) + N) + (N + N)) + 1)
        (((b + Polynomial.C 2)).eval D) ((N + 1) + N) := by
    simpa only [Polynomial.eval_add, Polynomial.eval_C] using hsub
  -- 2. The linear hypersurface `u = Σⱼ cⱼ eⱼ`: format = dimension, degree `1`.
  have hhyp : {p : Fin ((N + 1) + N) → ℝ |
        MvPolynomial.eval p (Work.WilG4c.dirLinPoly N e) = 0} ∈
      S.Ω ((N + 1) + N) ((Polynomial.C 1 : Polynomial ℕ).eval D) ((N + 1) + N) := by
    have h1 : {p : Fin ((N + 1) + N) → ℝ |
        MvPolynomial.eval p (Work.WilG4c.dirLinPoly N e) = 0} ∈
        S.Ω ((N + 1) + N) 1 ((N + 1) + N) :=
      Omega.mono (S.hyp ((N + 1) + N) (Work.WilG4c.dirLinPoly N e)) le_rfl
        (Work.WilG4c.dirLinPoly_totalDegree_le N e)
    simpa only [Polynomial.eval_C] using h1
  -- 3. Intersect: get `dirRelSet`, format `max ... + 1`, degree `b.eval D + 2 + 1`.
  have hrel : Work.WilG4c.dirRelSet N φ e ∈
      S.Ω (max (A + 2 * (((N + 1) + N) + (N + N)) + 1) ((N + 1) + N) + 1)
        ((((b + Polynomial.C 2) + Polynomial.C 1)).eval D) ((N + 1) + N) :=
    Omega.inter₂ hsub' hhyp
  -- 4. Project the coefficient block away.
  have hproj : Work.WilG0.projLastIter (N + 1) N (Work.WilG4c.dirRelSet N φ e) ∈
      S.Ω (max (A + 2 * (((N + 1) + N) + (N + N)) + 1) ((N + 1) + N) + 1 + N + (N + 1))
        ((((b + Polynomial.C 2) + Polynomial.C 1)).eval D) (N + 1) :=
    projLastIter_mem S (N + 1) N _ _ _ hrel
  rw [Work.WilG4c.projLastIter_dirRelSet] at hproj
  -- 5. Absorb the format cost into `K` and the degree `b.eval D + 3` into `(b + C 3).eval D`.
  refine Omega.mono hproj ?_ ?_
  · have : dirK N =
        max (2 * (((N + 1) + N) + (N + N)) + 1) ((N + 1) + N) + 1 + N + (N + 1) := rfl
    omega
  · simp only [Polynomial.eval_add, Polynomial.eval_C]
    omega

end Work.WilG4c

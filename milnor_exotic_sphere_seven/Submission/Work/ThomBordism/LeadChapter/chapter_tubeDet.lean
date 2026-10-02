import Mathlib
import Submission.Work.ThomBordism.LeadChapter.Defs
import Submission.Work.ThomBordism.LeadChapter.TubeDetDefs
import Submission.Work.ThomBordism.LeadChapter.TubeDetCore
import Submission.Work.ThomBordism.LeadChapter.tubeDetShear
import Submission.Work.ThomBordism.LeadChapter.tubeDetKernel
import Submission.Work.ThomBordism.LeadChapter.tubeDetDetSign

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000
/-! Guidance from the project lead (the requester):

# S3 `Work.ThomBordism.chapter_tubeDet` — the tube determinant (the geometric heart)
File: `Submission/Work/ThomBordism/LeadChapter/S3_tubeDet.lean`. Pure calculus in ℝ^{9+k}; no homology.

**Statement.** For `G, m, hpow` and the specified identification `h` (`BdryIdSpec`): ∃ ε₃ = ±1 (after `G … h`,
before pieces/points) such that for every piece `a`, chart `i` of `Fam a.2`, `y ∈ src i` there is `δ > 0`:
for every `z : E9` with `0 < z 0 < δ`, `tail 8 z = φᵢ y`, `collarPiece G m hpow h a i` has a derivative
`B` at `z`, `srcHf (Ψ z) ≠ t₀`, and for every derivative `Lv` of `vSrc` at `Ψ z` and every `N` with
`Lv ∘ N = ogFrameCLM (G.gauss ⟨srcHf (Ψ z), _⟩)`: `0 < ε₃ · frameSign (Fam a.2) i y · blockDet k B N`.

**Proof sketch.**
1. Block coordinates: by `BdryIdSpec`, for `x = h.symm (a,y')`: `e_a y' = Aff_a(tail x)` with
   `Aff_a = cubeToEuc ∘ blockTubePoint ∘ cubeCoord ∘ tail ∘ srcCast`, affine with positive diagonal on the
   block of `a` (`genLoopListConcatStep_snd_eq_of_index`, `blockTubePoint_apply`, `det_cubeEuc_cubeCoord_pos`).
   Hence `Ψ(t,u) = (t, Aff_a⁻¹(e_a(φᵢ⁻¹ u)))` near `z`: `B = [e₀ | Aff_a⁻¹ ∘ de ∘ dφᵢ⁻¹]`.
2. On `{x₀ < 1/2}` near the block: `srcHf u = alphaV … (blockTubePoint (cubeCoord …))`
   (`flatSourceHomotopy8_eq_collapse`), so `vSrc = padEuc ∘ tubeNormalCoord ∘ Aff_a` (`G.coord_collapse`);
   on the piece, `d tubeNormalCoord` = projection on the normal space. So `Lv ∘ N = ogFrame(gauss)` forces
   `N ≡ Aff_a⁻¹ ∘ (unpadded Gauss frame)` modulo `range B` (which does not change `blockDet`).
3. Gauss orientation: `G.gauss = (s = 1 ? id : ogFlip) (padGaussFunM …)` with ONE `s` for all pieces
   (`gaussBranch_uniform_of_universal`); `padGaussFunM_eq_of_normalData`, `canonicalLift_plane`.
4. TEL: `pairSign (flipTan E i x (frameSign V i.1 x)) (Gauss.gframe E ND i x) = 1` (`sigmaTelescope_gauss`)
   ⇒ `sgn det[de∘dφᵢ⁻¹ | gframe] = frameSign · const`.
5. `sgn blockDet B N = const(k) · sgn det Aff_a⁻¹ (=+1) · s · frameSign`. Set ε₃ := const(k)·s.

**Proved lemmas.** `sourceZeroSet_boundary_homeo_spec_coord`, `blockTubePoint_apply`, `concatBlockCoord`
(`outerStep`, `innerStep`, `blockTubePoint`), `genLoopListConcatStep_snd_eq_of_index`,
`det_cubeEuc_cubeCoord_pos` (all `Submission.Work.ThomBordism.<same name>`),
`flatSourceHomotopy8_eq_collapse` (`Submission.Work.PTGeometric.SourceNull`),
`GenuineTubeGeometry.coord_collapse/gauss_proj/core_iff_vec` (`Submission.Work.PTGeometric.ConcreteCollapse`),
`gaussBranch_uniform_of_universal` (`…/gaussBranchUniformOfUniversal`),
`sigmaTelescope_gauss` (`…/sigmaGaussTelescope`), `pairSign_tanFrame_gframe` (`…/KeyLocal/pairSignGauss`),
`padGaussFunM_eq_of_normalData`, `canonicalLift_plane` (same-name modules), `FrameSigns.frameSign_of_mem`.

**Traps.**
- ε₃ is quantified after `G m hpow h` (the branch `s` depends on `G`), but BEFORE `a i y`; never per piece.
- The `∃ B` is pinned by `HasFDerivAt`; `N` is arbitrary modulo `range B` — prove the sign for all such N.
- `finCongr`/`srcCast` reindexings are index-preserving (no permutation sign); check, don't assume.
- No `respectTransparency false`.
-/

namespace Work.ThomBordism.LeadChapter

open scoped Manifold ContDiff Topology in
open CategoryTheory Work.PTGeometric in
theorem chapter_tubeDet {k : ℕ} (hk : 1 ≤ k) {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8}
    (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1)
    (h : BdryId G m hpow) (hspec : BdryIdSpec G m hpow h) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ (a : Fin m × ι) (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) (y : (Fam a.2).pt)
        (hy : y ∈ Work.ThomBordism.FrameSigns.src (Fam a.2) i),
        ∃ δ : ℝ, 0 < δ ∧
          ∀ z : CofAtlas.E9, 0 < z 0 → z 0 < δ →
            tail 8 z = (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y →
            ∃ B : CofAtlas.E9 →L[ℝ] CofAtlas.ModN k,
              HasFDerivAt (collarPiece G m hpow h a i) B z ∧
              ∃ hne : srcHf G m hpow (collarPiece G m hpow h a i z) ≠ D.t₀,
                ∀ (Lv : CofAtlas.ModN k →L[ℝ] EuclideanSpace ℝ (Fin (k + G.mU))),
                  HasFDerivAt (vSrc G m hpow) Lv (collarPiece G m hpow h a i z) →
                  ∀ N : EuclideanSpace ℝ (Fin k) →L[ℝ] CofAtlas.ModN k,
                    Lv.comp N = ogFrameCLM (G.gauss ⟨srcHf G m hpow (collarPiece G m hpow h a i z), hne⟩) →
                    0 < ε * Work.ThomBordism.FrameSigns.frameSign (Fam a.2) i y * blockDet k B N := by
  obtain ⟨ε, hε, hsign⟩ :=
    tubeDetDetSign (k := k) hk (D := D) (ι := ι) (Fam := Fam) G m hpow h hspec
  refine ⟨ε, hε, ?_⟩
  intro a i y hy
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro z hz0 hz12 hz
  have hBd : HasFDerivAt (collarPiece G m hpow h a i)
      (collarB k (spatialDeriv G m a i y)) z :=
    hasFDerivAt_collarPiece (G := G) m hpow h hspec a i y hy z hz
  have hmem : srcHf G m hpow (collarPiece G m hpow h a i z) ∈ G.core :=
    srcHf_collarPiece_mem_core (G := G) m hpow h hspec a i y hy z hz (le_of_lt hz12)
  have hne : srcHf G m hpow (collarPiece G m hpow h a i z) ≠ D.t₀ :=
    fun hh => G.t0_notMem_core (hh ▸ hmem)
  refine ⟨collarB k (spatialDeriv G m a i y), hBd, hne, ?_⟩
  intro Lv hLv N hN
  have hker := tubeDetKernel (k := k) hk (D := D) (ι := ι) (Fam := Fam) G m hpow h hspec
    a i y hy z hz hz0 (le_of_lt hz12) hne hBd Lv hLv
  have hsub : ∀ v, ∃ x, collarB k (spatialDeriv G m a i y) x
      = N v - frameN G m hpow h a i y z hne v := by
    intro v
    exact LinearMap.mem_range.mp (hker.2 N hN v)
  rw [tubeDetShear (collarB k (spatialDeriv G m a i y)) N
    (frameN G m hpow h a i y z hne) hsub]
  exact hsign a i y hy z hz hz0 (le_of_lt hz12) hne


end Work.ThomBordism.LeadChapter

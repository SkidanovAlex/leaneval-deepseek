import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.cuspCorrDefs
import Submission.Work.Mostow.horSpec
import Submission.Work.Mostow.hptOf_yc
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.hptOf_hdist
import Submission.Work.Mostow.StabHoroForm
import Submission.Work.Mostow.ematSpec
import Submission.Work.Mostow.bdFixIff
import Submission.Work.Mostow.normalForm
import Submission.Work.Mostow.hptOfHliftSub
import Submission.Work.Mostow.hptOfZeroHlift
import Submission.Work.Mostow.hliftDecomp

/-!
# `horoActTrivId`: an isometry of ℍⁿ fixing a horosphere pointwise is the identity

If `g : PO(n,1)` fixes the boundary point `ξ ∈ Sph n`, preserves the Busemann level `lev ξ`
(so it maps every horosphere of `ξ` onto itself) and fixes the horosphere at level `D > 0`
*pointwise*, then `g = 1`.

The proof linearises: `L := emat g` acts on `ℝ^{Fin n ⊕ Fin 1}` by `L *ᵥ hlift u = hlift (g • u)`
(`nf_hlift_smul`), and

* `hlev` forces `L *ᵥ θ_ξ = θ_ξ` where `θ_ξ = (ξ,1)` is the null vector of `ξ`:
  `bd g ξ = ξ` alone gives `L *ᵥ θ_ξ = μ • θ_ξ`, and the level preservation says
  `(J Lᵀ J) *ᵥ θ_ξ = θ_ξ`; since `J Lᵀ J` is a left inverse of the invertible `L`
  (`Lᵀ J L = J`), this forces `μ = 1`;
* `htriv` and the explicit horosphere parametrisation `hlift (hptOf ξ y D)` (`y ⊥ ξ`) give
  `L *ᵥ hlift (hptOf ξ y D) = hlift (hptOf ξ y D)`; subtracting the `y = 0` point (which is a
  combination of `θ_ξ` and `hlift 0`) shows that `L` fixes `wvec Z` for every `Z ⊥ ξ` and fixes
  `hlift 0`;
* every `hlift u` decomposes as `⟪u,ξ⟫ • θ_ξ + (tpart u − ⟪u,ξ⟫) • hlift 0 + wvec (u − ⟪u,ξ⟫ • ξ)`,
  so `L` fixes `hlift u` for all `u`; injectivity of `hlift` and faithfulness of the action
  (`POActionProp`) give `g = 1`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix

variable {n : ℕ}

/-- The Busemann level at `ξ` is minus the Minkowski pairing with `θ_ξ = (ξ,1)`:
`lev ξ u = -⟨hlift u, θ_ξ⟩`. -/
lemma lev_eq_neg_mform (ξ u : E n) : lev ξ u = - mform (hlift u) (theta ξ) := by
  rw [lev, mform_hlift_theta']; ring

/-- The linear-algebra core of `horoActTrivId`, with the three coordinate identities
(`h2`, `h3`, `h4` below, proved in the sibling modules `hptOfHliftSub`, `hptOfZeroHlift` and
`hliftDecomp`) taken as hypotheses. -/
theorem horoActTrivId_aux (hA : POActionProp n)
    (g : PO n 1) (ξ : E n) (hξ : ξ ∈ Sph n) (D : ℝ) (hD : 0 < D)
    (hfix : bd g ξ = ξ)
    (hlev : ∀ u : E n, lev ξ (g • u) = lev ξ u)
    (htriv : ∀ u : E n, lev ξ u = D → g • u = u)
    (h2 : ∀ y : E n, inner ℝ y ξ = 0 →
      hlift (hptOf ξ y D) - hlift (hptOf ξ 0 D)
        = (D * ‖y‖ ^ 2 / 2) • theta ξ + wvec (D • y))
    (h3 : hlift (hptOf ξ 0 D)
        = ((1 - D ^ 2) / (2 * D)) • theta ξ + D • hlift (0 : E n))
    (h4 : ∀ u : E n, hlift u = (inner ℝ u ξ) • theta ξ
        + (tpart u - inner ℝ u ξ) • hlift (0 : E n) + wvec (u - (inner ℝ u ξ) • ξ)) :
    g = 1 := by
  -- ## Step 1: `L := emat g` fixes the null vector `θ_ξ`
  have hLθ : emat g *ᵥ theta ξ = theta ξ := by
    -- (a) `hfix` gives `L *ᵥ θ = μ • θ`
    obtain ⟨c, hc⟩ := ((ematSpec g).2.2 hξ).1 hfix
    rw [nvec_eq_theta] at hc
    have hμ : emat g *ᵥ theta ξ = (tsign (rep g) * c) • theta ξ := by
      rw [emat, Matrix.smul_mulVec, hc, smul_smul]
    -- (b) `hlev` gives `(J Lᵀ J) *ᵥ θ = θ`
    have hMθ : (pmOneMat * (emat g)ᵀ * pmOneMat) *ᵥ theta ξ = theta ξ := by
      apply eq_of_forall_mform_hlift
      intro u
      have e1 : mform (hlift (g • u)) (theta ξ) = - lev ξ (g • u) := by
        rw [lev_eq_neg_mform]; ring
      have e2 : mform (hlift u) (theta ξ) = - lev ξ u := by
        rw [lev_eq_neg_mform]; ring
      rw [← mform_mulVec_left (emat g) (hlift u) (theta ξ), ← nf_hlift_smul g u, e1, e2,
        hlev u]
    -- (c) `(J Lᵀ J) * L = 1`
    have hML : (pmOneMat * (emat g)ᵀ * pmOneMat) * emat g = 1 := by
      rw [Matrix.mul_assoc (pmOneMat * (emat g)ᵀ) pmOneMat (emat g),
          Matrix.mul_assoc pmOneMat (emat g)ᵀ (pmOneMat * emat g),
          ← Matrix.mul_assoc (emat g)ᵀ pmOneMat (emat g),
          nf_emat_isJOrth g, pmOneMat_mul_pmOneMat (Fin n) (Fin 1) ℝ]
    -- (d) hence `θ = μ • θ`, so `μ = 1`
    have hμid : theta ξ = (tsign (rep g) * c) • theta ξ := by
      calc theta ξ = (1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) *ᵥ theta ξ :=
            (Matrix.one_mulVec _).symm
        _ = ((pmOneMat * (emat g)ᵀ * pmOneMat) * emat g) *ᵥ theta ξ := by rw [hML]
        _ = (pmOneMat * (emat g)ᵀ * pmOneMat) *ᵥ (emat g *ᵥ theta ξ) :=
              (mulVec_mulVec (theta ξ) (pmOneMat * (emat g)ᵀ * pmOneMat) (emat g)).symm
        _ = (pmOneMat * (emat g)ᵀ * pmOneMat) *ᵥ ((tsign (rep g) * c) • theta ξ) := by
              rw [hμ]
        _ = (tsign (rep g) * c) • ((pmOneMat * (emat g)ᵀ * pmOneMat) *ᵥ theta ξ) :=
              Matrix.mulVec_smul _ _ _
        _ = (tsign (rep g) * c) • theta ξ := by rw [hMθ]
    have hc1 : (1 : ℝ) = tsign (rep g) * c := by
      have h := congrFun hμid (Sum.inr 0)
      simpa [theta] using h
    rw [hμ, ← hc1, one_smul]
  -- ## Step 2: `L` fixes the level-`D` horosphere pointwise in the hyperboloid model
  have hP : ∀ y : E n, inner ℝ y ξ = 0 →
      emat g *ᵥ hlift (hptOf ξ y D) = hlift (hptOf ξ y D) := by
    intro y hy
    have hlevy : lev ξ (hptOf ξ y D) = D := (hptOf_level ξ hξ D hD y hy).1
    rw [← nf_hlift_smul g (hptOf ξ y D), htriv _ hlevy]
  have hP0 : emat g *ᵥ hlift (hptOf ξ 0 D) = hlift (hptOf ξ 0 D) := hP 0 (by simp)
  -- ## Step 3a: `L` fixes `hlift 0`
  have hL0 : emat g *ᵥ hlift (0 : E n) = hlift (0 : E n) := by
    have hsplit : D • hlift (0 : E n)
        = hlift (hptOf ξ 0 D) - ((1 - D ^ 2) / (2 * D)) • theta ξ := by
      rw [h3]; module
    have key : D • (emat g *ᵥ hlift (0 : E n)) = D • hlift (0 : E n) := by
      calc D • (emat g *ᵥ hlift (0 : E n))
          = emat g *ᵥ (D • hlift (0 : E n)) := (Matrix.mulVec_smul _ _ _).symm
        _ = emat g *ᵥ (hlift (hptOf ξ 0 D) - ((1 - D ^ 2) / (2 * D)) • theta ξ) := by
              rw [hsplit]
        _ = emat g *ᵥ hlift (hptOf ξ 0 D)
              - ((1 - D ^ 2) / (2 * D)) • (emat g *ᵥ theta ξ) := by
              rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
        _ = hlift (hptOf ξ 0 D) - ((1 - D ^ 2) / (2 * D)) • theta ξ := by rw [hP0, hLθ]
        _ = D • hlift (0 : E n) := hsplit.symm
    exact smul_right_injective _ (ne_of_gt hD) key
  -- ## Step 3b: `L` fixes `wvec Z` for `Z ⊥ ξ`
  have hLw : ∀ Z : E n, inner ℝ Z ξ = 0 → emat g *ᵥ wvec Z = wvec Z := by
    intro Z hZ
    have hyZ : inner ℝ ((1 / D) • Z) ξ = 0 := by
      rw [real_inner_smul_left, hZ, mul_zero]
    have hdiff := h2 ((1 / D) • Z) hyZ
    have hDZ : D • ((1 / D) • Z) = Z := by
      rw [smul_smul, mul_one_div_cancel (ne_of_gt hD), one_smul]
    have hw : wvec Z = hlift (hptOf ξ ((1 / D) • Z) D) - hlift (hptOf ξ 0 D)
        - (D * ‖(1 / D) • Z‖ ^ 2 / 2) • theta ξ := by
      have h := hdiff
      rw [hDZ] at h
      rw [h]; abel
    rw [hw, Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_smul,
      hP ((1 / D) • Z) hyZ, hP0, hLθ]
  -- ## Step 4: `L` fixes everything, hence `g = 1`
  refine (POBasic.ofProp hA).faithful g (fun u => ?_)
  have hZu : inner ℝ (u - (inner ℝ u ξ) • ξ) ξ = 0 := by
    rw [inner_sub_left, real_inner_smul_left, hptOf_level_aux_inner_self hξ]
    ring
  apply hlift_injective
  rw [nf_hlift_smul g u]
  rw [h4 u]
  rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    hLθ, hL0, hLw (u - (inner ℝ u ξ) • ξ) hZu]

theorem horoActTrivId {n : ℕ} (hA : Submission.Mostow.POActionProp n)
    (g : LeanEval.Geometry.MostowRigidity.PO n 1) (ξ : Submission.Mostow.E n)
    (hξ : ξ ∈ Submission.Mostow.Sph n) (D : ℝ) (hD : 0 < D)
    (hfix : Submission.Mostow.bd g ξ = ξ)
    (hlev : ∀ u : Submission.Mostow.E n, Work.Mostow.lev ξ (g • u) = Work.Mostow.lev ξ u)
    (htriv : ∀ u : Submission.Mostow.E n, Work.Mostow.lev ξ u = D → g • u = u) :
    g = 1 :=
  horoActTrivId_aux hA g ξ hξ D hD hfix hlev htriv
    (fun y hy => hptOfHliftSub ξ y hξ hy D hD)
    (hptOfZeroHlift ξ hξ D hD)
    (fun u => hliftDecomp ξ u)

end Work.Mostow

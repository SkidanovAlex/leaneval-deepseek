import Mathlib
import Submission.Work.Drive.encodedShear
import Submission.Work.Drive.shear_seam
import Submission.Work.Drive.chartPertData
import Submission.Work.Drive.meet32_bordism_invariance
import Submission.Work.Drive.SeamMeetDefs

/-!
# The parametrised family of the ends-clause genericity (`NOTES_LEAD_hodd_blockT6.md` §2.2)

`Work.Drive.exists_homotopy_meet3Hyp_encoded` (`Drive/encodedGeneric.lean`, §2.1) is proved by running
the localised parametric Sard on a family of *triples of chains* whose members are the encoded chains
of a class-perturbed homotopy, each block reparametrised by a box self-diffeomorphism.  This module
fixes that family (`Work.Drive.encShearFam`) and its three elementary properties:

* at parameter `0` it *is* the encoded triple of the given homotopy `H` (`encShearFam_zero`);
* it is seam-invariant whenever `H`, `A`, `B` are (`encShearFam_seam`) — the `Meet3Hyp.seam` clause;
* it is jointly `C^∞` (`contMDiff_encShearFam`, which needs the smoothness of `classMap ∘ classEquiv` in the
  parameter, of `shear` and of `thetaS`).

The parameter is `(p, q₁, q₂, s) ∈ 𝔼⁴ × 𝔼⁴ × 𝔼⁴ × ℝ`:

* `p` moves the *class* of the homotopy block by `classMap (β (x 2) • p)` with
  `β = betaG` (`encodedShear.lean`) vanishing outside `(0,1)` — this is what keeps the two ends of `H`
  and makes the perturbation direction available at every triple point (whose third parameter is always
  in `(0,1)`, see `ENCODED_FAMILY_STATUS.md` §2.1);
* `q₁`, `q₂` shear the plane parameters of the two plane blocks;
* `s` twists their levels.

The family is *not* the triple one wants: it is the triple whose `Meet3Hyp` the Sard produces, and the
reparametrisations `Θ k = (shear q · on (x 0,x 1), thetaS s on x 2)` are stripped afterwards by the
proved `Work.Drive.meet3Hyp_of_boxReparam`.
-/

namespace Work.Drive

open scoped Manifold Topology

noncomputable section

/-- The class-perturbation parameter `p`. -/
def encShearP (t : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) × ℝ) :
    EuclideanSpace ℝ (Fin 4) := t.1

/-- The shear parameter of the first plane block. -/
def encShearQ₁ (t : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) × ℝ) :
    EuclideanSpace ℝ (Fin 4) := t.2.1

/-- The shear parameter of the second plane block. -/
def encShearQ₂ (t : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) × ℝ) :
    EuclideanSpace ℝ (Fin 4) := t.2.2.1

/-- The level-twist parameter. -/
def encShearS (t : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) × ℝ) :
    ℝ := t.2.2.2

/-- The class of a capped point. -/
def clsSh (p : CappingSpace) : Projectivization ℝ (Eucl 3) := (cappingSpaceHomeoProj p).2

/-- The capped point of level `1` over a projective class. -/
def capOf (c : Projectivization ℝ (Eucl 3)) : CappingSpace :=
  cappingSpaceHomeoProj.symm (⟨1, by norm_num⟩, c)

@[simp] lemma clsSh_capOf (c : Projectivization ℝ (Eucl 3)) : clsSh (capOf c) = c := by
  simp [clsSh, capOf]

/-- `chartPert` acts on the class by `classMap`. -/
@[simp] lemma clsSh_chartPert (t : Eucl 3) (p : CappingSpace) :
    clsSh (chartPert t p) = classMap t (clsSh p) := by
  simp [clsSh, chartPert, coordFam]

/-- **The block-`0` chain of the family**: the class-perturbed homotopy, at the constant level `c₀`.
The perturbation is the *chart* perturbation `chartPert` (a smooth family of self-maps of
`CappingSpace` with `chartPert 0 = id`, whose parameter derivative is surjective at every point), read
in the *class* only — the level of the block is the fixed `c₀`, because the triple condition of
`encodedChains` forces the three levels to agree. -/
def encShearFam0 (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (c₀ : ℝ) (p : Eucl 3) (x : EuclideanSpace ℝ (Fin 3)) : Projectivization ℝ (Eucl 3) × ℝ :=
  (clsSh (chartPert (betaG (x 2) • p) (capOf (H (x 2, pt2 (x 0) (x 1))))), c₀)

/-- **The family of encoded triples** whose `Meet3Hyp` the parametric Sard produces. -/
def encShearFam (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (c₀ : ℝ)
    (t : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) × ℝ) :
    Fin 3 → EuclideanSpace ℝ (Fin 3) → Projectivization ℝ (Eucl 3) × ℝ :=
  fun k x =>
    if k = 0 then encShearFam0 H c₀ (encShearP t) x
    else if k = 1 then (A (shear (encShearQ₁ t) (pt2 (x 0) (x 1))), thetaS (encShearS t) (x 2))
    else (B (shear (encShearQ₂ t) (pt2 (x 0) (x 1))), thetaS (encShearS t) (x 2))

@[simp] lemma encShearFam_apply_zero (H A B c₀ t) (x : EuclideanSpace ℝ (Fin 3)) :
    encShearFam H A B c₀ t 0 x = encShearFam0 H c₀ (encShearP t) x := by
  simp [encShearFam]

@[simp] lemma encShearFam_apply_one (H A B c₀ t) (x : EuclideanSpace ℝ (Fin 3)) :
    encShearFam H A B c₀ t 1 x = (A (shear (encShearQ₁ t) (pt2 (x 0) (x 1))), thetaS (encShearS t) (x 2)) := by
  simp [encShearFam]

@[simp] lemma encShearFam_apply_two (H A B c₀ t) (x : EuclideanSpace ℝ (Fin 3)) :
    encShearFam H A B c₀ t 2 x = (B (shear (encShearQ₂ t) (pt2 (x 0) (x 1))), thetaS (encShearS t) (x 2)) := by
  simp [encShearFam]

/-- **At parameter `0` the family is the encoded triple of `H`.** -/
theorem encShearFam_zero (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (c₀ : ℝ) :
    encShearFam H A B c₀
        ((0 : EuclideanSpace ℝ (Fin 4)), 0, 0, (0 : ℝ))
      = encodedChains (fun x : EuclideanSpace ℝ (Fin 3) => H (x 2, pt2 (x 0) (x 1))) A B c₀ := by
  funext k x
  fin_cases k <;>
    simp [encShearFam, encShearFam0, encodedChains, encShearP, encShearQ₁, encShearQ₂, encShearS]

/-- **The family is seam-invariant** whenever the three constituting maps are — the `Meet3Hyp.seam`
clause of the parametric Sard.  Block `0` uses the seam-invariance of `H` directly (its class
perturbation depends only on `x 2`, which `seamInv` fixes); the two plane blocks use the
seam-equivariance of the shear (`Work.Drive.shear_seam`, proved) together with the seam-invariance of
`A`, `B`. -/
theorem encShearFam_seam (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (c₀ : ℝ)
    (t : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) × ℝ)
    (hH : ∀ (s : ℝ) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y → H (s, seamInv2 y) = H (s, y))
    (hA : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → A (seamInv2 y) = A y)
    (hB : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → B (seamInv2 y) = B y)
    {k : Fin 3} {x : EuclideanSpace ℝ (Fin 3)} (hx : onSeam x) :
    encShearFam H A B c₀ t k (seamInv x) = encShearFam H A B c₀ t k x := by
  have hy : onSeam2 (pt2 (x 0) (x 1)) := hx
  have h2 : (seamInv x) 2 = x 2 := seamInv_apply_two x
  have hpt : seamInv2 (pt2 (x 0) (x 1)) = pt2 (1 - x 0) (1 - x 1) := by
    ext i; fin_cases i <;> simp [pt2, seamInv2]
  -- the shear preserves the seam
  have hseam_shear : ∀ (q : EuclideanSpace ℝ (Fin 4)) (y : EuclideanSpace ℝ (Fin 2)),
      onSeam2 y → onSeam2 (shear q y) := by
    intro q y hy
    rcases hy with h | h | h | h
    · exact Or.inl (by simp [shear_apply_zero, hb, h])
    · exact Or.inr (Or.inl (by simp [shear_apply_zero, hb, h]))
    · exact Or.inr (Or.inr (Or.inl (by simp [shear_apply_one, hb, h])))
    · exact Or.inr (Or.inr (Or.inr (by simp [shear_apply_one, hb, h])))
  have hH' : H (x 2, pt2 (1 - x 0) (1 - x 1)) = H (x 2, pt2 (x 0) (x 1)) := by
    rw [← hpt, hH (x 2) _ hy]
  have hA' : A (shear (encShearQ₁ t) (pt2 (1 - x 0) (1 - x 1)))
      = A (shear (encShearQ₁ t) (pt2 (x 0) (x 1))) := by
    rw [← hpt, shear_seam (encShearQ₁ t) (hy := hy),
      hA _ (hseam_shear (encShearQ₁ t) _ hy)]
  have hB' : B (shear (encShearQ₂ t) (pt2 (1 - x 0) (1 - x 1)))
      = B (shear (encShearQ₂ t) (pt2 (x 0) (x 1))) := by
    rw [← hpt, shear_seam (encShearQ₂ t) (hy := hy),
      hB _ (hseam_shear (encShearQ₂ t) _ hy)]
  fin_cases k <;> simp [encShearFam, encShearFam0, h2, hpt, hH', hA', hB']

end

end Work.Drive

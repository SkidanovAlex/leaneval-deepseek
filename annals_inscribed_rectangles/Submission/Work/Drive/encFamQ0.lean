import Mathlib
import Submission.Work.Drive.encFamTwo

/-!
# The ends-clause family of the **corrected** §2.1 design: with the block-`0` domain shear `Sh_{q₀}`

`ENCODED_GENERIC_DEAD.md` §0 (second version) retracts the claim that the parametrised-Sard route to
§2.1 is dead, and identifies the reason: the families `Work.Drive.encShearFam` / `Work.Drive.encFamTwo`
(and the certificate `Work.Drive.not_surjective_paramDeriv_encFamTwo_of_time_face`, which is a correct
statement about them) do **not** reparametrise the *domain* of block `0`, whereas the lead's
`NOTES_LEAD_hodd_blockT6.md` §2.2 family does — its block `0` is
`H^p (ρ (x 2), Sh_{q₀} (ρ x 0, ρ x 1))`.

This file provides that family (without the `ρ`-clamp, which is inessential: see
`ENCODED_GENERIC_DEAD.md` §3 of the first version — `ρ` is the identity on `[-1/8, 9/8] ⊇ [0,1]` and
its only role was to keep the shear's argument bounded, which the `ballClamp` in the shear already
takes care of).  The parameter is

> `(p, q₀, q₁, q₂, r₁, r₂) ∈ 𝔼⁴ × 𝔼⁴ × 𝔼⁴ × 𝔼⁴ × ℝ × ℝ`

(the nested-product form used throughout this lane; `Work.Drive.localSard_family_in_open` consumes a
parameter space `𝔼^m`, so the final step reparametrises by a linear isometry, exactly as planned for
`Work.Drive.encShearFam`).

Block `0` is `encFamQ0₀`: the class-perturbed homotopy evaluated at the *sheared* plane coordinates;
the shear is what supplies the `2`-dimensional class reach `W₀` at zeros where `betaG` vanishes — by
`Work.Drive.range_mfderiv_shear_eq` (`Drive/range_mfderiv_shear_eq.lean`) applied to the homotopy's
plane derivative, and `Work.Drive.exists_mem_inter_cosets_of_sup_eq_top`
(`Drive/blockZeroCoset.lean`) shows that a `2`-dimensional reach is enough.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

/-- The parameter `(p, q₀, q₁, q₂, r₁, r₂)` of the corrected family. -/
abbrev EncParQ0 :=
  EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) ×
    EuclideanSpace ℝ (Fin 4) × ℝ × ℝ

/-- The class-perturbation parameter. -/
def q0P (t : EncParQ0) : EuclideanSpace ℝ (Fin 4) := t.1

/-- The shear parameter of block `0`. -/
def q0Q0 (t : EncParQ0) : EuclideanSpace ℝ (Fin 4) := t.2.1

/-- The shear parameter of the first plane block. -/
def q0Q1 (t : EncParQ0) : EuclideanSpace ℝ (Fin 4) := t.2.2.1

/-- The shear parameter of the second plane block. -/
def q0Q2 (t : EncParQ0) : EuclideanSpace ℝ (Fin 4) := t.2.2.2.1

/-- The level-twist parameter of the first plane block. -/
def q0R1 (t : EncParQ0) : ℝ := t.2.2.2.2.1

/-- The level-twist parameter of the second plane block. -/
def q0R2 (t : EncParQ0) : ℝ := t.2.2.2.2.2

/-- The zero parameter. -/
def q0Zero : EncParQ0 := ((0 : EuclideanSpace ℝ (Fin 4)), 0, 0, 0, (0 : ℝ), 0)

@[simp] lemma q0P_zero : q0P q0Zero = 0 := rfl
@[simp] lemma q0Q0_zero : q0Q0 q0Zero = 0 := rfl
@[simp] lemma q0Q1_zero : q0Q1 q0Zero = 0 := rfl
@[simp] lemma q0Q2_zero : q0Q2 q0Zero = 0 := rfl
@[simp] lemma q0R1_zero : q0R1 q0Zero = 0 := rfl
@[simp] lemma q0R2_zero : q0R2 q0Zero = 0 := rfl

/-- **Block `0` of the corrected family**: the class-perturbed homotopy `H`, evaluated at the sheared
plane coordinates and at the (unclamped) homotopy time, at the constant level `c₀`. -/
def encFamQ0₀ (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (c₀ : ℝ)
    (p q : EuclideanSpace ℝ (Fin 4)) (x : EuclideanSpace ℝ (Fin 3)) : Projectivization ℝ (Eucl 3) × ℝ :=
  (clsSh (chartPert (betaG (x 2) • p) (capOf (H (x 2, shear q (pt2 (x 0) (x 1)))))), c₀)

/-- **The corrected family of encoded triples** (block `0` with the domain shear `Sh_{q₀}`, the two
plane blocks with their own shears and independent level twists). -/
def encFamQ0 (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (c₀ : ℝ) (t : EncParQ0) :
    Fin 3 → EuclideanSpace ℝ (Fin 3) → Projectivization ℝ (Eucl 3) × ℝ :=
  fun k x =>
    if k = 0 then encFamQ0₀ H c₀ (q0P t) (q0Q0 t) x
    else if k = 1 then (A (shear (q0Q1 t) (pt2 (x 0) (x 1))), thetaS (q0R1 t) (x 2))
    else (B (shear (q0Q2 t) (pt2 (x 0) (x 1))), thetaS (q0R2 t) (x 2))

@[simp] lemma encFamQ0_apply_zero (H A B c₀ t) (x : EuclideanSpace ℝ (Fin 3)) :
    encFamQ0 H A B c₀ t 0 x = encFamQ0₀ H c₀ (q0P t) (q0Q0 t) x := by
  simp [encFamQ0]

@[simp] lemma encFamQ0_apply_one (H A B c₀ t) (x : EuclideanSpace ℝ (Fin 3)) :
    encFamQ0 H A B c₀ t 1 x =
      (A (shear (q0Q1 t) (pt2 (x 0) (x 1))), thetaS (q0R1 t) (x 2)) := by
  simp [encFamQ0]

@[simp] lemma encFamQ0_apply_two (H A B c₀ t) (x : EuclideanSpace ℝ (Fin 3)) :
    encFamQ0 H A B c₀ t 2 x =
      (B (shear (q0Q2 t) (pt2 (x 0) (x 1))), thetaS (q0R2 t) (x 2)) := by
  simp [encFamQ0]

/-- **At the zero parameter the family is the encoded triple of `H`.** -/
theorem encFamQ0_zero (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (c₀ : ℝ) :
    encFamQ0 H A B c₀ q0Zero
      = encodedChains (fun x : EuclideanSpace ℝ (Fin 3) => H (x 2, pt2 (x 0) (x 1))) A B c₀ := by
  funext k x
  fin_cases k <;>
    simp [encFamQ0, encFamQ0₀, encodedChains, q0Zero, q0P, q0Q0, q0Q1, q0Q2, q0R1, q0R2]

/-- **The family is seam-invariant** whenever `H`, `A`, `B` are.  Block `0` uses the seam-equivariance
of the shear (`Work.Drive.shear_seam`) inside the argument of `H` and the seam-invariance of `H`; the
weight `betaG (x 2)` and the level `c₀` are untouched by `seamInv` (which changes only `x 0`, `x 1`). -/
theorem encFamQ0_seam (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (c₀ : ℝ) (t : EncParQ0)
    (hH : ∀ (s : ℝ) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y → H (s, seamInv2 y) = H (s, y))
    (hA : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → A (seamInv2 y) = A y)
    (hB : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → B (seamInv2 y) = B y)
    {k : Fin 3} {x : EuclideanSpace ℝ (Fin 3)} (hx : onSeam x) :
    encFamQ0 H A B c₀ t k (seamInv x) = encFamQ0 H A B c₀ t k x := by
  have hy : onSeam2 (pt2 (x 0) (x 1)) := hx
  have h2 : (seamInv x) 2 = x 2 := seamInv_apply_two x
  have hpt : pt2 ((seamInv x) 0) ((seamInv x) 1) = seamInv2 (pt2 (x 0) (x 1)) := by
    ext i; fin_cases i <;> simp [pt2, seamInv2]
  have h1 : (seamInv x) 1 = 1 - x 1 := by simp
  have h0 : (seamInv x) 0 = 1 - x 0 := by simp
  have hseam_shear : ∀ (q : EuclideanSpace ℝ (Fin 4)) (y : EuclideanSpace ℝ (Fin 2)),
      onSeam2 y → onSeam2 (shear q y) := by
    intro q y hy'
    rcases hy' with h | h | h | h
    · exact Or.inl (by simp [shear_apply_zero, hb, h])
    · exact Or.inr (Or.inl (by simp [shear_apply_zero, hb, h]))
    · exact Or.inr (Or.inr (Or.inl (by simp [shear_apply_one, hb, h])))
    · exact Or.inr (Or.inr (Or.inr (by simp [shear_apply_one, hb, h])))
  have hH' : ∀ q : EuclideanSpace ℝ (Fin 4),
      H (x 2, shear q (seamInv2 (pt2 (x 0) (x 1)))) = H (x 2, shear q (pt2 (x 0) (x 1))) := by
    intro q
    rw [shear_seam q (hy := hy)]
    exact hH (x 2) _ (hseam_shear q _ hy)
  have hq0 : shear (q0Q0 t) (seamInv2 (pt2 (x 0) (x 1)))
      = seamInv2 (shear (q0Q0 t) (pt2 (x 0) (x 1))) :=
    shear_seam (q0Q0 t) (hy := hy)
  have hq1 : shear (q0Q1 t) (seamInv2 (pt2 (x 0) (x 1)))
      = seamInv2 (shear (q0Q1 t) (pt2 (x 0) (x 1))) :=
    shear_seam (q0Q1 t) (hy := hy)
  have hq2 : shear (q0Q2 t) (seamInv2 (pt2 (x 0) (x 1)))
      = seamInv2 (shear (q0Q2 t) (pt2 (x 0) (x 1))) :=
    shear_seam (q0Q2 t) (hy := hy)
  have hA' : A (shear (q0Q1 t) (seamInv2 (pt2 (x 0) (x 1))))
      = A (shear (q0Q1 t) (pt2 (x 0) (x 1))) := by
    rw [hq1, hA _ (hseam_shear (q0Q1 t) _ hy)]
  have hB' : B (shear (q0Q2 t) (seamInv2 (pt2 (x 0) (x 1))))
      = B (shear (q0Q2 t) (pt2 (x 0) (x 1))) := by
    rw [hq2, hB _ (hseam_shear (q0Q2 t) _ hy)]
  have hH0 : H (x 2, shear (q0Q0 t) (seamInv2 (pt2 (x 0) (x 1))))
      = H (x 2, shear (q0Q0 t) (pt2 (x 0) (x 1))) := hH' (q0Q0 t)
  have hpt' : pt2 ((seamInv x) 0) ((seamInv x) 1) = seamInv2 (pt2 (x 0) (x 1)) := hpt
  have hpt2 : seamInv2 (pt2 (x 0) (x 1)) = pt2 (1 - x 0) (1 - x 1) := by
    ext i; fin_cases i <;> simp [pt2, seamInv2]
  fin_cases k <;>
    simp only [encFamQ0, encFamQ0₀, Fin.isValue, Fin.zero_eta, if_true, h2, hpt', ← hpt2,
      hH0, hA', hB']

end

end Work.Drive

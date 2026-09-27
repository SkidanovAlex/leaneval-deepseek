import Mathlib
import Submission.Work.Drive.cone_chain
import Submission.Work.Drive.cappingSpace_homeomorph_prod
import Submission.Work.Drive.omegaChainInterface

/-!
# The radial dilation of the capping space, and the sweep of a plane

Stage 2 of the chain route (`Submission/Work/Drive/CHAIN_LEVEL_PLAN.md` §2, `OMEGA_CHAIN_STATUS.md`)
asks for the relative `3`-chain `V_u` of the capped plane `P_u`, with `∂V_u = P_u + P_{u,-λ}`: the
paper's `ω_{P_u}` is represented by the part of the model `Y = (0,∞) × LensSpace` *below* the plane,
and the operation that produces it is the **radial dilation** — the flow of the model's radial
coordinate, which sweeps a plane down to the axis end `r → 0`.

This file provides that flow and the sweep it defines:

* `Work.Drive.scaleModel`, `Work.Drive.scaleCapping` — the dilation `(r, q) ↦ (a·r, q)` of the model
  and its transport to the capping space `CappingSpace` along `Work.Drive.Φ`/`Ψ`
  (`cappingSpace_homeomorph_prod`), with continuity, the identity and composition laws, injectivity,
  the **level formula** `r (scaleCapping a p) = a · r p`, and compatibility with the rotation
  `rotCapping` (the dilation is radial, the rotation acts on the slice);
* `Work.Drive.sweepChain` — the **sweep** of a parametrised plane `P : ℝ² → CappingSpace`: the
  `3`-chain `(x, s) ↦ s · P (x 0, x 1)` with the dilation parameter
  `s = exp ((1 - x 2) · log a)` running from `a` (at `x 2 = 0`) to `1` (at `x 2 = 1`).  Its two end
  faces are the dilated plane (`x 2 = 0`, `Work.Drive.sweepChain_face_zero`) and the plane itself
  (`x 2 = 1`, `Work.Drive.sweepChain_face_one`); its four side faces are the sweep of the boundary of
  the plane's own parametrisation — which for a plane presented by a *closed* surface is empty, i.e.
  `∂V_u = P_u + P_{u,-λ}`.

The end behaviour is the model statement `Work.Drive.omegaChain_mem_iff`: below the level planes the
sweep is exactly the part of the model under the plane, i.e. the `ω`-chain of `Work.Drive.omegaChain`.

The dilation parameter is carried as an element of `Set.Ioi (0 : ℝ)` rather than as `a : ℝ` together
with a proof `0 < a`, so that the parameter can be rewritten freely (no dependent rewriting).
-/

namespace Work.Drive

open scoped Topology Manifold ContDiff

noncomputable section

/-! ## The radial dilation -/

/-- The positive dilations, as a subtype (so that parameters can be rewritten freely). -/
abbrev Pos : Type := Set.Ioi (0 : ℝ)

/-- A positive real number, as a dilation parameter. -/
def pos (a : ℝ) (ha : 0 < a) : Pos := ⟨a, Set.mem_Ioi.mpr ha⟩

@[simp] lemma pos_val (a : ℝ) (ha : 0 < a) : ((pos a ha : Pos) : ℝ) = a := rfl

/-- **The radial dilation of the model `(0,∞) × LensSpace`**: the radial coordinate is multiplied by
the positive parameter `A`, the slice coordinate is untouched. -/
def scaleModel (A : Pos) (p : Set.Ioi (0 : ℝ) × LensSpace) : Set.Ioi (0 : ℝ) × LensSpace :=
  (⟨(A : ℝ) * (p.1 : ℝ), Set.mem_Ioi.mpr (mul_pos A.2 p.1.2)⟩, p.2)

@[simp] lemma scaleModel_fst (A : Pos) (p : Set.Ioi (0 : ℝ) × LensSpace) :
    ((scaleModel A p).1 : ℝ) = (A : ℝ) * (p.1 : ℝ) := by simp [scaleModel]

@[simp] lemma scaleModel_snd (A : Pos) (p : Set.Ioi (0 : ℝ) × LensSpace) :
    (scaleModel A p).2 = p.2 := by simp [scaleModel]

lemma continuous_scaleModel (A : Pos) : Continuous (scaleModel A) := by
  refine Continuous.prodMk ?_ continuous_snd
  refine Continuous.subtype_mk ?_ _
  exact continuous_const.mul (continuous_subtype_val.comp continuous_fst)

lemma scaleModel_one (p : Set.Ioi (0 : ℝ) × LensSpace) : scaleModel (pos 1 one_pos) p = p :=
  Prod.ext (Subtype.ext (by simp [scaleModel, pos])) rfl

lemma scaleModel_injective (A : Pos) : Function.Injective (scaleModel A) := by
  intro p q h
  have h1 : (p.1 : ℝ) = (q.1 : ℝ) := by
    have h2 := congrArg (fun z => ((z.1 : Set.Ioi (0 : ℝ)) : ℝ)) h
    simp only [scaleModel_fst] at h2
    exact mul_left_cancel₀ (ne_of_gt A.2) h2
  refine Prod.ext (Subtype.ext h1) ?_
  have h3 := congrArg Prod.snd h
  simpa only [scaleModel_snd] using h3

/-- The multiplication of the positive parameters of the dilation. -/
def posMul (A B : Pos) : Pos := ⟨(A : ℝ) * (B : ℝ), Set.mem_Ioi.mpr (mul_pos A.2 B.2)⟩

lemma scaleModel_mul (A B : Pos) (p : Set.Ioi (0 : ℝ) × LensSpace) :
    scaleModel (posMul A B) p = scaleModel A (scaleModel B p) :=
  Prod.ext (Subtype.ext (by simp only [scaleModel_fst, posMul]; ring)) rfl

/-- **The radial dilation of the capping space**: the flow of the radial coordinate of the model
`Y ≅ (0,∞) × LensSpace`, transported along `Work.Drive.Φ`. -/
def scaleCapping (A : Pos) (p : CappingSpace) : CappingSpace :=
  Ψ (scaleModel A (Φ p))

lemma continuous_scaleCapping (A : Pos) : Continuous (scaleCapping A) :=
  continuous_Ψ.comp ((continuous_scaleModel A).comp continuous_Φ)

@[simp] lemma Φ_scaleCapping (A : Pos) (p : CappingSpace) :
    Φ (scaleCapping A p) = scaleModel A (Φ p) :=
  Φ_Ψ _

/-- **The level formula**: the radial coordinate of a dilated point is the dilated radial
coordinate.  (The radial coordinate is the model's `λ`; its two ends are the `±λ` ends of the
paper.) -/
lemma level_scaleCapping (A : Pos) (p : CappingSpace) :
    ((Φ (scaleCapping A p)).1 : ℝ) = (A : ℝ) * ((Φ p).1 : ℝ) := by
  rw [Φ_scaleCapping, scaleModel_fst]

lemma scaleCapping_injective (A : Pos) : Function.Injective (scaleCapping A) := by
  intro p q h
  have h1 : Φ (scaleCapping A p) = Φ (scaleCapping A q) := congrArg Φ h
  rw [Φ_scaleCapping, Φ_scaleCapping] at h1
  have hpq : Φ p = Φ q := scaleModel_injective A h1
  calc p = Ψ (Φ p) := (Ψ_Φ p).symm
    _ = Ψ (Φ q) := by rw [hpq]
    _ = q := Ψ_Φ q

@[simp] lemma scaleCapping_one : scaleCapping (pos 1 one_pos) = id := by
  funext p
  show Ψ (scaleModel (pos 1 one_pos) (Φ p)) = p
  rw [scaleModel_one, Ψ_Φ]

lemma scaleCapping_mul (A B : Pos) :
    scaleCapping (posMul A B) = scaleCapping A ∘ scaleCapping B := by
  funext p
  show Ψ (scaleModel (posMul A B) (Φ p)) = Ψ (scaleModel A (Φ (scaleCapping B p)))
  rw [Φ_scaleCapping, scaleModel_mul]

/-- **The dilation commutes with the rotation**: the rotation acts on the slice coordinate only, and
the dilation on the radial coordinate only (`Work.Drive.Phi_rot_equivariant`).  This is what makes a
rotation-invariant count of sweeps evaluable in the model. -/
lemma rotCapping_scaleCapping (v : UnitAddCircle) (A : Pos) (p : CappingSpace) :
    rotCapping v (scaleCapping A p) = scaleCapping A (rotCapping v p) := by
  have hL : Φ (rotCapping v (scaleCapping A p)) =
      ((scaleModel A (Φ p)).1, rotLens v (scaleModel A (Φ p)).2) := by
    rw [(Phi_rot_equivariant v).1 (scaleCapping A p), Φ_scaleCapping]
  have hR : Φ (scaleCapping A (rotCapping v p)) =
      scaleModel A ((Φ p).1, rotLens v (Φ p).2) := by
    rw [Φ_scaleCapping, (Phi_rot_equivariant v).1 p]
  have h : Φ (rotCapping v (scaleCapping A p)) = Φ (scaleCapping A (rotCapping v p)) := by
    rw [hL, hR]
    exact Prod.ext (Subtype.ext (by simp only [scaleModel_fst])) rfl
  calc rotCapping v (scaleCapping A p) = Ψ (Φ (rotCapping v (scaleCapping A p))) :=
        (Ψ_Φ _).symm
    _ = Ψ (Φ (scaleCapping A (rotCapping v p))) := by rw [h]
    _ = scaleCapping A (rotCapping v p) := Ψ_Φ _

/-! ## The sweep of a parametrised plane -/

/-- The positive dilation parameter of the sweep: `exp ((1 - x 2) · log a)` runs from `a` (at
`x 2 = 0`) to `1` (at `x 2 = 1`). -/
def sweepParam (a : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : Pos :=
  ⟨Real.exp ((1 - x 2) * Real.log a), Set.mem_Ioi.mpr (Real.exp_pos _)⟩

@[simp] lemma sweepParam_val (a : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    (sweepParam a x : ℝ) = Real.exp ((1 - x 2) * Real.log a) := rfl

lemma sweepParam_eq_of_second_coord_zero (a : ℝ) (ha : 0 < a) (x : EuclideanSpace ℝ (Fin 3))
    (hx : x 2 = 0) : sweepParam a x = pos a ha := by
  refine Subtype.ext ?_
  show Real.exp ((1 - x 2) * Real.log a) = a
  rw [hx, sub_zero, one_mul, Real.exp_log ha]

lemma sweepParam_eq_of_second_coord_one (a : ℝ) (_ha : 0 < a) (x : EuclideanSpace ℝ (Fin 3))
    (hx : x 2 = 1) : sweepParam a x = pos 1 one_pos := by
  refine Subtype.ext ?_
  show Real.exp ((1 - x 2) * Real.log a) = 1
  rw [hx, sub_self, zero_mul, Real.exp_zero]

/-- **The sweep of a parametrised plane.**  For `a > 0` and a plane presented by
`P : ℝ² → CappingSpace`, the sweep is the `3`-chain `(x, s) ↦ s · P (x 0, x 1)` with the dilation
parameter `s = exp ((1 - x 2) · log a)` running from `a` (at `x 2 = 0`) to `1` (at `x 2 = 1`); it is
smooth and positive, so the dilation is always defined. -/
def sweepChain (a : ℝ) (ha : 0 < a) (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) :
    EuclideanSpace ℝ (Fin 3) → CappingSpace :=
  fun x => scaleCapping (sweepParam a x) (P (mk2 (x 0) (x 1)))

@[simp] lemma sweepChain_apply (a : ℝ) (ha : 0 < a)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (x : EuclideanSpace ℝ (Fin 3)) :
    sweepChain a ha P x = scaleCapping (sweepParam a x) (P (mk2 (x 0) (x 1))) := rfl

/-- The `x 2 = 0` face of the sweep is the dilated plane. -/
lemma sweepChain_face_zero (a : ℝ) (ha : 0 < a)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (x : EuclideanSpace ℝ (Fin 3))
    (hx : x 2 = 0) :
    sweepChain a ha P x = scaleCapping (pos a ha) (P (mk2 (x 0) (x 1))) := by
  rw [sweepChain_apply, sweepParam_eq_of_second_coord_zero a ha x hx]

/-- The `x 2 = 1` face of the sweep is the plane itself. -/
lemma sweepChain_face_one (a : ℝ) (ha : 0 < a)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (x : EuclideanSpace ℝ (Fin 3))
    (hx : x 2 = 1) :
    sweepChain a ha P x = P (mk2 (x 0) (x 1)) := by
  rw [sweepChain_apply, sweepParam_eq_of_second_coord_one a ha x hx, scaleCapping_one]
  rfl

end

end Work.Drive

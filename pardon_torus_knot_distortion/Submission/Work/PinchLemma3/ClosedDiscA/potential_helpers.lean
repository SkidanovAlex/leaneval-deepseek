import Mathlib
import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.PinchLemma3.ClosedDiscA.exists_alternating_partition
import Submission.Work.SurgeryInvariance.WindingOf.homotopic_eq
import Submission.Work.PinchLemma3.ClosedDiscA.exists_functional_kernel_eq
import Submission.Work.PinchLemma3.ClosedDiscA.windingSpan_union_le_sup_of_isPathConnected_inter

/-!
# The "developing potential" of an inessential region of a parametrised torus

If a region `X` of the torus `F = P.carrier` has vanishing winding span, every closed curve
inside `X` has zero displacement in the parameter plane, so the `ψ`-image of the displacement
of a path inside `X` depends only on its endpoints.  Choosing a base point `a ∈ X` and a path
from `a` to each point then gives a well defined "potential"

`potential hXc hXpc a ha ψ x  =  ψ(displacement of any path in X from a to x)`,

with `psiDisp ψ u = potential y - potential x` for every path `u` in `X` from `x` to `y`.
-/

open LeanEval.KnotTheory.PardonDistortion Set
open scoped unitInterval

namespace Work.PinchLemma3.ClosedDiscA

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- A path in the ambient space whose image lies in `X ⊆ P.carrier`, viewed as a path in the
carrier. -/
theorem exists_carrierPath {X : Set R3} (hXc : X ⊆ P.carrier) {p q : P.carrier}
    (h : JoinedIn X (p : R3) (q : R3)) :
    ∃ u : Path p q, ∀ t : unitInterval, ((u t) : R3) ∈ X := by
  obtain ⟨u, hu⟩ := h
  exact ⟨⟨⟨fun t => ⟨u t, hXc (hu t)⟩, u.continuous.subtype_mk (fun t => hXc (hu t))⟩,
      Subtype.ext u.source, Subtype.ext u.target⟩, fun t => hu t⟩

/-- **The `ψ`-displacement of a path in an inessential region depends only on its endpoints.** -/
theorem psiDisp_eq_of_mem {X : Set R3} (hVX : Work.SurgeryInvariance.WindingSpan P X = ⊥)
    {W : Type*} [AddCommGroup W] [Module ℝ W] (ψ : (ℝ × ℝ) →ₗ[ℝ] W)
    {x y : P.carrier} (u v : Path x y)
    (hu : ∀ t : unitInterval, ((u t) : R3) ∈ X) (hv : ∀ t : unitInterval, ((v t) : R3) ∈ X) :
    psiDisp ψ u = psiDisp ψ v := by
  have hloop : psiDisp ψ (u.trans v.symm) = 0 := by
    refine psiDisp_eq_zero_of_subset ψ ?_ (le_of_eq hVX) (u.trans v.symm) ?_
    · intro w hw
      rw [Submodule.mem_bot] at hw
      have hv1 : w.1 = 0 := by
        have : ((w.1 : ℚ)) = 0 := congrArg Prod.fst hw
        exact_mod_cast this
      have hv2 : w.2 = 0 := by
        have : ((w.2 : ℚ)) = 0 := congrArg Prod.snd hw
        exact_mod_cast this
      rw [hv1, hv2]
      simp only [Int.cast_zero]
      exact map_zero ψ
    · exact Path.trans_coe_mem u v.symm hu (Path.symm_coe_mem v hv)
  rw [psiDisp_trans, psiDisp_symm] at hloop
  exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hloop)

/-- A chosen path in the region `X` from the base point `a` to `x`. -/
noncomputable def potentialPath {X : Set R3} (hXc : X ⊆ P.carrier) (hXpc : IsPathConnected X)
    (a : P.carrier) (ha : (a : R3) ∈ X) (x : P.carrier) (hx : (x : R3) ∈ X) : Path a x :=
  Classical.choose (exists_carrierPath (P := P) hXc (hXpc.joinedIn (a : R3) ha (x : R3) hx))

theorem potentialPath_mem {X : Set R3} (hXc : X ⊆ P.carrier) (hXpc : IsPathConnected X)
    (a : P.carrier) (ha : (a : R3) ∈ X) (x : P.carrier) (hx : (x : R3) ∈ X) :
    ∀ t : unitInterval, ((potentialPath hXc hXpc a ha x hx t) : R3) ∈ X :=
  Classical.choose_spec (exists_carrierPath (P := P) hXc (hXpc.joinedIn (a : R3) ha (x : R3) hx))

/-- **The developing potential** of the region `X` based at `a`. -/
noncomputable def potential {X : Set R3} (hXc : X ⊆ P.carrier) (hXpc : IsPathConnected X)
    (a : P.carrier) (ha : (a : R3) ∈ X)
    {W : Type*} [AddCommGroup W] [Module ℝ W] (ψ : (ℝ × ℝ) →ₗ[ℝ] W) :
    {x : P.carrier // (x : R3) ∈ X} → W :=
  fun x => psiDisp ψ (potentialPath hXc hXpc a ha x.1 x.2)

/-- **The defining property of the potential**: the displacement of a path in `X` is the
difference of the potentials of its endpoints. -/
theorem potential_spec {X : Set R3} (hXc : X ⊆ P.carrier) (hXpc : IsPathConnected X)
    (hVX : Work.SurgeryInvariance.WindingSpan P X = ⊥)
    (a : P.carrier) (ha : (a : R3) ∈ X)
    {W : Type*} [AddCommGroup W] [Module ℝ W] (ψ : (ℝ × ℝ) →ₗ[ℝ] W)
    {x y : P.carrier} (hx : (x : R3) ∈ X) (hy : (y : R3) ∈ X)
    (u : Path x y) (hu : ∀ t : unitInterval, ((u t) : R3) ∈ X) :
    psiDisp ψ u = potential hXc hXpc a ha ψ ⟨y, hy⟩ - potential hXc hXpc a ha ψ ⟨x, hx⟩ := by
  have hcx := potentialPath_mem (P := P) hXc hXpc a ha x hx
  have hcy := potentialPath_mem (P := P) hXc hXpc a ha y hy
  have hcy' : psiDisp ψ (potentialPath hXc hXpc a ha y hy)
      = psiDisp ψ ((potentialPath hXc hXpc a ha x hx).trans u) :=
    psiDisp_eq_of_mem hVX ψ _ _ hcy (Path.trans_coe_mem _ u hcx hu)
  have htrans : psiDisp ψ ((potentialPath hXc hXpc a ha x hx).trans u)
      = psiDisp ψ (potentialPath hXc hXpc a ha x hx) + psiDisp ψ u :=
    psiDisp_trans ψ _ u
  simp only [potential]
  rw [hcy', htrans]
  abel

/-- The potential is computed by *any* path in `X` from the base point. -/
theorem potential_eq_of_path {X : Set R3} (hXc : X ⊆ P.carrier) (hXpc : IsPathConnected X)
    (hVX : Work.SurgeryInvariance.WindingSpan P X = ⊥)
    (a : P.carrier) (ha : (a : R3) ∈ X)
    {W : Type*} [AddCommGroup W] [Module ℝ W] (ψ : (ℝ × ℝ) →ₗ[ℝ] W)
    {x : P.carrier} (hx : (x : R3) ∈ X) (u : Path a x) (hu : ∀ t : unitInterval, ((u t) : R3) ∈ X) :
    potential hXc hXpc a ha ψ ⟨x, hx⟩ = psiDisp ψ u := by
  simp only [potential]
  exact psiDisp_eq_of_mem hVX ψ _ _ (potentialPath_mem hXc hXpc a ha x hx) hu

/-- The potential is insensitive to the proof of membership. -/
theorem potential_congr {X : Set R3} (hXc : X ⊆ P.carrier) (hXpc : IsPathConnected X)
    (a : P.carrier) (ha : (a : R3) ∈ X)
    {W : Type*} [AddCommGroup W] [Module ℝ W] (ψ : (ℝ × ℝ) →ₗ[ℝ] W)
    {x : P.carrier} (h1 h2 : (x : R3) ∈ X) :
    potential hXc hXpc a ha ψ ⟨x, h1⟩ = potential hXc hXpc a ha ψ ⟨x, h2⟩ :=
  congrArg _ (Subtype.ext rfl)

end

end Work.PinchLemma3.ClosedDiscA

import Mathlib
import Submission.Work.EKLC6Route.Defs
import Submission.Work.EKLComp.X3Background
import Submission.Work.EKLComp.LeafDefs
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLContract.Lemmas.SL3Topology

/-!
# Measurable coordinate maps of the big cell `G⁰G⁺(t) · z₀`

`Work.EKLC6Route.bigcell` decomposes a neighbourhood of the identity of `SL₃(ℝ)` as
`g = u · k` with `u ∈ Uminus t = G⁻(t)` the stable horospherical part and `k` in the parabolic
part `VtSet t = G⁰G⁺(t)` (the matrices with zeros on the contracted positions).  Consequently,
on the "big cell"

  `S = Ucl (Uminus t) A × (VtSet t ∩ Ucl (⊤ : Subgroup SL₃(ℝ)) B) ⊆ SL₃(ℝ) × SL₃(ℝ)`

of the model space, the parametrising map `Φ (u,k) = (u * k) • z₀` is injective whenever the
decomposition is unique on that cell (the hypothesis `hinj` of `exists_coord_maps`).

The content of this file is that **the coordinates `u` and `k` are Borel functions of the point
`x = (u * k) • z₀` of `X₃`**.  The proof is the standard Lusin–Suslin argument: `S` is a Borel
set (it is a product of closed sets, cf. the two `have`s in the proof of `exists_coord_maps`),
`Φ` is continuous, and by `ContinuousOn.measurableEmbedding`, an injective continuous map defined
on a Borel subset of a Polish space is a *measurable embedding*; its inverse is measurable
(`MeasurableEmbedding.measurable_rangeSplitting`) and can be extended off the image by a constant
(`MeasurableEmbedding.exists_measurable_extend`).  Applying this to the two projections of the
inverse of `Φ` yields the measurable coordinate maps `uc`, `θ`.

Note that the hypotheses `0 < A`, `0 < B` are not needed for the measurability statement: the
argument only uses that the two factors are closed (hence Borel) subsets of `SL₃(ℝ)`, which holds
for every `A` and `B`.
-/

open MeasureTheory Filter Topology
open Work.EKLContract

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.EKLC6Route

/-- **Measurable coordinates for an injective orbit parametrisation.**

If `S ⊆ SL₃(ℝ) × SL₃(ℝ)` is Borel and the map `p ↦ (p.1 * p.2) • z₀` is injective on `S`, then
the two coordinates `p.1`, `p.2` of a point of `S` are Borel functions of the orbit point
`(p.1 * p.2) • z₀`; the resulting maps are defined on all of `X₃` (junk values off the image of
`S`, which is not needed anywhere). -/
theorem exists_coord_maps_of_injOn (z0 : X3) (S : Set (SL3 × SL3)) (hS : MeasurableSet S)
    (hinj : Set.InjOn (fun p : SL3 × SL3 => (p.1 * p.2) • z0) S) :
    ∃ uc θ : X3 → SL3, Measurable uc ∧ Measurable θ ∧
      ∀ p ∈ S, uc ((p.1 * p.2) • z0) = p.1 ∧ θ ((p.1 * p.2) • z0) = p.2 := by
  classical
  -- `SL₃(ℝ)` (and hence `SL₃(ℝ) × SL₃(ℝ)`) is a Polish space
  haveI hpolSL : PolishSpace SL3 := Work.EKLContract.Lemmas.polishSpace_specialLinearGroup
  -- the parametrising map of the big cell is continuous
  have hcont : Continuous (fun p : SL3 × SL3 => (p.1 * p.2) • z0) := by fun_prop
  -- Lusin–Suslin: an injective continuous map on a Borel set of a Polish space is a measurable
  -- embedding, so it is a Borel isomorphism onto its image
  have hmb : MeasurableEmbedding (S.domRestrict (fun p : SL3 × SL3 => (p.1 * p.2) • z0)) :=
    ContinuousOn.measurableEmbedding hS hcont.continuousOn hinj
  -- the two coordinate functions on `S` are measurable ...
  obtain ⟨uc, huc, hucComp⟩ := hmb.exists_measurable_extend
    (g := fun p : S => (p : SL3 × SL3).1) (by fun_prop) (fun _ => ⟨(1 : SL3)⟩)
  obtain ⟨θ, hθ, hθComp⟩ := hmb.exists_measurable_extend
    (g := fun p : S => (p : SL3 × SL3).2) (by fun_prop) (fun _ => ⟨(1 : SL3)⟩)
  -- ... and they recover the coordinates of `p ∈ S` at the orbit point of `p`
  refine ⟨uc, θ, huc, hθ, ?_⟩
  intro p hp
  have h1 : uc ((p.1 * p.2) • z0) = ((⟨p, hp⟩ : S) : SL3 × SL3).1 := by
    have := congrFun hucComp ⟨p, hp⟩
    simpa [Set.domRestrict_apply] using this
  have h2 : θ ((p.1 * p.2) • z0) = ((⟨p, hp⟩ : S) : SL3 × SL3).2 := by
    have := congrFun hθComp ⟨p, hp⟩
    simpa [Set.domRestrict_apply] using this
  exact ⟨h1, h2⟩

theorem exists_coord_maps (t : Fin 3 → ℝ) (z0 : Work.EKLContract.X3) (A B : ℝ)
    (hA : 0 < A) (hB : 0 < B)
    (hinj : ∀ u : Work.EKLContract.SL3, u ∈ Work.EKLComp.Ucl (Work.EKLC6Core.Uminus t) A →
      ∀ k : Work.EKLContract.SL3, k ∈ Work.EKLC6Route.VtSet t ∩
        Work.EKLComp.Ucl (⊤ : Subgroup Work.EKLContract.SL3) B →
      ∀ u' : Work.EKLContract.SL3, u' ∈ Work.EKLComp.Ucl (Work.EKLC6Core.Uminus t) A →
      ∀ k' : Work.EKLContract.SL3, k' ∈ Work.EKLC6Route.VtSet t ∩
        Work.EKLComp.Ucl (⊤ : Subgroup Work.EKLContract.SL3) B →
      (u * k) • z0 = (u' * k') • z0 → u = u' ∧ k = k') :
    ∃ uc θ : Work.EKLContract.X3 → Work.EKLContract.SL3, Measurable uc ∧ Measurable θ ∧
      (∀ u : Work.EKLContract.SL3, u ∈ Work.EKLComp.Ucl (Work.EKLC6Core.Uminus t) A →
        ∀ k : Work.EKLContract.SL3, k ∈ Work.EKLC6Route.VtSet t ∩
          Work.EKLComp.Ucl (⊤ : Subgroup Work.EKLContract.SL3) B →
        uc ((u * k) • z0) = u ∧ θ ((u * k) • z0) = k) := by
  classical
  -- `SL₃(ℝ)`, and hence `SL₃(ℝ) × SL₃(ℝ)`, is Polish, so that the Borel σ-algebras on
  -- products and on `SL₃(ℝ)` are the ones coming from the topology
  haveI hpolSL : PolishSpace SL3 := Work.EKLContract.Lemmas.polishSpace_specialLinearGroup
  -- `Ucl (Uminus t) A` is closed: the closed horospherical subgroup `Uminus t`, cut out by the
  -- closed entrywise condition `‖g - 1‖ ≤ A`
  have hUcl : IsClosed (Work.EKLComp.Ucl (Work.EKLC6Core.Uminus t) A) := by
    have hU : IsClosed ((Work.EKLC6Core.Uminus t : Subgroup SL3) : Set SL3) :=
      (Work.EKLC6Core.uminus_isHoro t).1.1
    rw [show Work.EKLComp.Ucl (Work.EKLC6Core.Uminus t) A
        = ((Work.EKLC6Core.Uminus t : Subgroup SL3) : Set SL3) ∩
          {g : SL3 | ∀ i j : Fin 3, |(g : Matrix (Fin 3) (Fin 3) ℝ) i j
            - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ A} from by
      ext g; constructor <;> intro h <;> exact h]
    refine hU.inter ?_
    rw [show {g : SL3 | ∀ i j : Fin 3, |(g : Matrix (Fin 3) (Fin 3) ℝ) i j
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ A}
        = ⋂ i : Fin 3, ⋂ j : Fin 3, {g : SL3 | |(g : Matrix (Fin 3) (Fin 3) ℝ) i j
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ A} from by
      ext g; simp]
    exact isClosed_iInter (fun i => isClosed_iInter (fun j =>
      isClosed_le (by fun_prop) continuous_const))
  -- `VtSet t` is closed: it is cut out by the equations `g i j = 0` at the contracted positions
  have hVt : IsClosed (VtSet t) := by
    rw [show VtSet t = ⋂ (i : Fin 3), ⋂ (j : Fin 3), ⋂ (_ : t i < t j),
        {g : SL3 | (g : Matrix (Fin 3) (Fin 3) ℝ) i j = 0} from by
      ext g; simp [VtSet]]
    exact isClosed_iInter (fun i => isClosed_iInter (fun j => isClosed_iInter (fun _ =>
      isClosed_eq (by fun_prop) continuous_const)))
  -- `Ucl (⊤ : Subgroup SL3) B` is closed (the entrywise box)
  have hUclTop : IsClosed (Work.EKLComp.Ucl (⊤ : Subgroup SL3) B) := by
    rw [show Work.EKLComp.Ucl (⊤ : Subgroup SL3) B
        = ⋂ i : Fin 3, ⋂ j : Fin 3, {g : SL3 | |(g : Matrix (Fin 3) (Fin 3) ℝ) i j
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ B} from by
      ext g; simp [Work.EKLComp.Ucl]]
    exact isClosed_iInter (fun i => isClosed_iInter (fun j =>
      isClosed_le (by fun_prop) continuous_const))
  -- the parametrising set of the big cell is Borel
  have hS : MeasurableSet (Work.EKLComp.Ucl (Work.EKLC6Core.Uminus t) A ×ˢ
      (VtSet t ∩ Work.EKLComp.Ucl (⊤ : Subgroup SL3) B)) :=
    (hUcl.prod (hVt.inter hUclTop)).measurableSet
  -- the parametrising map is injective on it, by uniqueness of the decomposition
  have hinjOn : Set.InjOn (fun p : SL3 × SL3 => (p.1 * p.2) • z0)
      (Work.EKLComp.Ucl (Work.EKLC6Core.Uminus t) A ×ˢ
        (VtSet t ∩ Work.EKLComp.Ucl (⊤ : Subgroup SL3) B)) := by
    rintro p ⟨hp1, hp2⟩ q ⟨hq1, hq2⟩ hpq
    obtain ⟨h1, h2⟩ := hinj p.1 hp1 p.2 hp2 q.1 hq1 q.2 hq2 hpq
    exact Prod.ext h1 h2
  obtain ⟨uc, θ, huc, hθ, hcoord⟩ := exists_coord_maps_of_injOn z0 _ hS hinjOn
  exact ⟨uc, θ, huc, hθ, fun u hu k hk => hcoord (u, k) ⟨hu, hk⟩⟩

end Work.EKLC6Route

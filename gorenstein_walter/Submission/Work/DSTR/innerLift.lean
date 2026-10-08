import Mathlib
import Submission.Work.DSTR.Defs

namespace Work.DSTR

open Subgroup

/-- **DS10b** (`Work.GW2.InnerLiftProp`): if `x` acts on a perfect normal `E <= X` as an inner automorphism modulo `Z(E)`, then it acts as an inner automorphism of `E`.  The cocycle `y |-> (x y x^-1)(e y e^-1)^-1` is a homomorphism `E -> Z(E)`, hence trivial because `E = E'`. -/
theorem innerLift : Work.GW2.InnerLiftProp := by
  intro X _ _ E hE hq x h
  obtain ⟨e, heE, hh⟩ := h
  -- `E` is perfect, i.e. `⁅E, E⁆ = E` in `X`, equivalently `↥E` is a perfect group.
  have hperf : Group.IsPerfect ↥E := Subgroup.isPerfect_iff.mpr hq.1
  -- The cocycle `F y = (x y x⁻¹) * (e y e⁻¹)⁻¹` lies in `E`.
  have hFmem : ∀ y : ↥E, (x * (y:X) * x⁻¹) * (e * (y:X) * e⁻¹)⁻¹ ∈ E := by
    intro y
    have h1 : x * (y:X) * x⁻¹ ∈ E := hE.conj_mem (y:X) y.2 x
    have h2 : e * (y:X) * e⁻¹ ∈ E := E.mul_mem (E.mul_mem heE y.2) (E.inv_mem heE)
    exact E.mul_mem h1 (E.inv_mem h2)
  -- The cocycle is multiplicative, because its values are central in `E`.
  have hFmul : ∀ a b : ↥E,
      (x * (↑(a*b) : X) * x⁻¹) * (e * (↑(a*b) : X) * e⁻¹)⁻¹
        = ((x * (a:X) * x⁻¹) * (e * (a:X) * e⁻¹)⁻¹) *
          ((x * (b:X) * x⁻¹) * (e * (b:X) * e⁻¹)⁻¹) := by
    have hcent : ∀ (y : ↥E) (w : X), w ∈ E →
        ((x * (y : X) * x⁻¹) * (e * (y : X) * e⁻¹)⁻¹) * w
          = w * ((x * (y : X) * x⁻¹) * (e * (y : X) * e⁻¹)⁻¹) := by
      intro y w hw
      obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.mp (hh (y:X) y.2)
      have h1 : (⟨w, hw⟩ : ↥E) * z = z * ⟨w, hw⟩ := Subgroup.mem_center_iff.mp hz ⟨w, hw⟩
      have h2 : (w : X) * (z : X) = (z : X) * w := by
        have := congrArg (fun t : ↥E => (t : X)) h1
        simpa using this
      have hzeq' : (z : X) = (x * (y : X) * x⁻¹) * (e * (y : X) * e⁻¹)⁻¹ := hzeq
      rw [← hzeq']
      exact h2.symm
    intro a b
    have hCin : (e * (a:X) * e⁻¹)⁻¹ ∈ E := E.inv_mem (E.mul_mem (E.mul_mem heE a.2) (E.inv_mem heE))
    have key : ((x * (b:X) * x⁻¹) * (e * (b:X) * e⁻¹)⁻¹) * (e * (a:X) * e⁻¹)⁻¹
        = (e * (a:X) * e⁻¹)⁻¹ * ((x * (b:X) * x⁻¹) * (e * (b:X) * e⁻¹)⁻¹) := hcent b _ hCin
    show (x * ((a:X) * (b:X)) * x⁻¹) * (e * ((a:X) * (b:X)) * e⁻¹)⁻¹ = _
    have hA : x * ((a:X) * (b:X)) * x⁻¹ = (x * (a:X) * x⁻¹) * (x * (b:X) * x⁻¹) := by group
    have hB : (e * ((a:X) * (b:X)) * e⁻¹)⁻¹ = (e * (b:X) * e⁻¹)⁻¹ * (e * (a:X) * e⁻¹)⁻¹ := by group
    rw [hA, hB]
    calc ((x * (a:X) * x⁻¹) * (x * (b:X) * x⁻¹)) * ((e * (b:X) * e⁻¹)⁻¹ * (e * (a:X) * e⁻¹)⁻¹)
        = (x * (a:X) * x⁻¹) * (((x * (b:X) * x⁻¹) * (e * (b:X) * e⁻¹)⁻¹) * (e * (a:X) * e⁻¹)⁻¹) := by group
      _ = (x * (a:X) * x⁻¹) * ((e * (a:X) * e⁻¹)⁻¹ * ((x * (b:X) * x⁻¹) * (e * (b:X) * e⁻¹)⁻¹)) := by rw [key]
      _ = ((x * (a:X) * x⁻¹) * (e * (a:X) * e⁻¹)⁻¹) * ((x * (b:X) * x⁻¹) * (e * (b:X) * e⁻¹)⁻¹) := by group
  -- Assemble the cocycle as a genuine homomorphism `↥E →* ↥E`.
  let fE : ↥E →* ↥E := {
    toFun := fun y => ⟨(x * (y:X) * x⁻¹) * (e * (y:X) * e⁻¹)⁻¹, hFmem y⟩
    map_one' := by ext; simp
    map_mul' := by intro a b; exact Subtype.ext (hFmul a b) }
  -- Its image lies in the center of `E`.
  have hcent : ∀ y : ↥E, fE y ∈ Subgroup.center ↥E := by
    intro y
    obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.mp (hh (y:X) y.2)
    have hzy : fE y = z := by
      apply Subtype.ext
      exact hzeq.symm
    rw [hzy]; exact hz
  let g : ↥E →* ↥(Subgroup.center ↥E) := fE.codRestrict _ hcent
  -- A homomorphism from a perfect group to an abelian group is trivial.
  have hle : _root_.commutator ↥E ≤ g.ker := Abelianization.commutator_subset_ker g
  have hker : g.ker = ⊤ := top_le_iff.mp (hperf.commutator_eq_top ▸ hle)
  have hg : ∀ y : ↥E, g y = 1 := fun y => MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top y)
  refine ⟨e, heE, fun y hy => ?_⟩
  have hfy : fE ⟨y, hy⟩ = 1 := by
    have := hg ⟨y, hy⟩
    simpa [g] using congrArg (fun t : ↥(Subgroup.center ↥E) => (t : ↥E)) this
  have h1 : (x * y * x⁻¹) * (e * y * e⁻¹)⁻¹ = 1 := by
    have : ((fE ⟨y, hy⟩ : ↥E) : X) = 1 := by rw [hfy]; rfl
    simpa [fE] using this
  exact mul_inv_eq_one.mp h1

end Work.DSTR

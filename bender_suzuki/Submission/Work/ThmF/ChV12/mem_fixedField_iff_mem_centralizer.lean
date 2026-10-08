import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Fixed points of `P ≤ V` on `Q₀` are the fixed field of the image of `P`

Setting of Ch. V §1 Prop. 3 of the Bender–Suzuki development: `Q₀ = ⟨Inv H ∪ {1}⟩` is
identified through `e : Q₀sub H ≃* Multiplicative F` with the additive group of a finite field
`F`, and `V = centD H t` acts on `Q₀` by field automorphisms through
`ρ : V →* (F ≃+* F)` (`hact` says that the conjugation action of `V` on `Q₀` transports under
`e` to the action of `ρ` on `F`).

For a subgroup `P ≤ V`, an element `x ∈ Q₀` is fixed by `P` (i.e. `x ∈ C_{Q₀}(P)`) exactly when
its image `toAdd (e x) ∈ F` lies in the fixed field of the image
`(P.subgroupOf V).map ρ ≤ F ≃+* F`.

The only group-theoretic input is `hconj`: conjugation by an element of `H` preserves `Q₀sub H`
(see `Work.ThmF.ChV12.conj_mem_Q0sub`, which proves it in the form needed here).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV12

open Classical Submission.Blueprint

/-- The fixed points of `P` in `Q₀` are exactly the elements lying in the fixed field of the
image of `P` in the automorphism group of `F`. -/
theorem mem_fixedField_iff_mem_centralizer {G : Type} [Group G] (H Q : Subgroup G) (t : G)
    {P : Subgroup G} (hPV : P ≤ centD H t)
    (hconj : ∀ v ∈ H, ∀ x ∈ Q0sub H, v * x * v⁻¹ ∈ Q0sub H)
    {F : Type} [Field F] (e : ↥(Q0sub H) ≃* Multiplicative F)
    (ρ : ↥(centD H t) →* (F ≃+* F))
    (hact : ∀ (v : ↥(centD H t)) (x : ↥(Q0sub H)) (hx : (v : G) * x * (v : G)⁻¹ ∈ Q0sub H),
      Multiplicative.toAdd (e ⟨(v : G) * x * (v : G)⁻¹, hx⟩) = ρ v (Multiplicative.toAdd (e x)))
    (x : ↥(Q0sub H)) :
    Multiplicative.toAdd (e x) ∈ FixedPoints.subfield ((P.subgroupOf (centD H t)).map ρ) F ↔
      (x : G) ∈ Subgroup.centralizer (P : Set G) := by
  have hVH : ∀ v : ↥(centD H t), (v : G) ∈ H := fun v => (centD_le_twoPoint t v.2).1
  -- for `v ∈ P` the two conditions `v * x = x * v` and `ρ v` fixing `toAdd (e x)` agree
  have key : ∀ v : ↥(centD H t), (v : G) ∈ P →
      (((v : G) * (x : G) = (x : G) * (v : G)) ↔
        ρ v (Multiplicative.toAdd (e x)) = Multiplicative.toAdd (e x)) := by
    intro v hv
    have hmem : (v : G) * (x : G) * (v : G)⁻¹ ∈ Q0sub H := hconj v (hVH v) (x : G) x.2
    have h := hact v x hmem
    constructor
    · intro hcomm
      have hc : (v : G) * (x : G) * (v : G)⁻¹ = (x : G) := by rw [hcomm]; group
      have hc' : (⟨(v : G) * (x : G) * (v : G)⁻¹, hmem⟩ : ↥(Q0sub H)) = x := Subtype.ext hc
      rw [← h, hc']
    · intro hfix
      have hc : (⟨(v : G) * (x : G) * (v : G)⁻¹, hmem⟩ : ↥(Q0sub H)) = x :=
        e.injective (Multiplicative.toAdd.injective (by rw [h, hfix]))
      have h3 : (v : G) * (x : G) * (v : G)⁻¹ = (x : G) := congrArg Subtype.val hc
      calc (v : G) * (x : G) = (v : G) * (x : G) * (v : G)⁻¹ * (v : G) := by group
        _ = (x : G) * (v : G) := by rw [h3]
  constructor
  · intro hfix
    refine Subgroup.mem_centralizer_iff.mpr (fun v hv => ?_)
    have hv' : (⟨v, hPV hv⟩ : ↥(centD H t)) ∈ P.subgroupOf (centD H t) :=
      Subgroup.mem_subgroupOf.mpr hv
    exact (key ⟨v, hPV hv⟩ hv).mpr
      (by simpa using hfix ⟨ρ ⟨v, hPV hv⟩, Subgroup.mem_map_of_mem ρ hv'⟩)
  · intro hx a
    obtain ⟨v, hv, hva⟩ := Subgroup.mem_map.mp a.2
    have hcomm : (v : G) * (x : G) = (x : G) * (v : G) := Subgroup.mem_centralizer_iff.mp hx v hv
    show (a : F ≃+* F) (Multiplicative.toAdd (e x)) = Multiplicative.toAdd (e x)
    rw [← hva]
    exact (key v hv).mp hcomm

end Work.ThmF.ChV12

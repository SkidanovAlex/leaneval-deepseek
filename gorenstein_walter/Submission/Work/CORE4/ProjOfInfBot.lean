import Mathlib
import Submission.Work.CORE4.Defs

namespace Work.CORE4

/-- `P` commutes with `E`, so `P ≤ N_G(E)`; hence `↑(P ⊔ E) = ↑P * ↑E` (every element of
`P ⊔ E` is a product `p * e`). -/
private theorem mem_sup_iff_prod {G : Type} [Group G] (P E : Subgroup G)
    (hcomm : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x) :
    ∀ x : G, x ∈ (P ⊔ E : Subgroup G) ↔ ∃ p ∈ P, ∃ e ∈ E, p * e = x := by
  have hPcent : ∀ x ∈ P, x ∈ Subgroup.centralizer (E : Set G) :=
    fun x hx => Subgroup.mem_centralizer_iff.mpr (fun h hh => (hcomm x hx h hh).symm)
  have hLE : P ≤ Subgroup.normalizer (E : Set G) :=
    fun x hx => Subgroup.centralizer_le_normalizer (E : Set G) (hPcent x hx)
  intro x
  constructor
  · intro hx
    have hx' : x ∈ (↑(P ⊔ E) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right P E hLE] at hx'
    exact Set.mem_mul.mp hx'
  · rintro ⟨p, hp, e, he, rfl⟩
    exact Subgroup.mul_mem_sup hp he

theorem ProjOfInfBot {G : Type} [Group G] (P E : Subgroup G)
    (hcomm : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x) (hinf : P ⊓ E = ⊥) :
    ∃ π : ↥(P ⊔ E) →* ↥E, ∀ (p : G) (hp : p ∈ P) (e : G) (he : e ∈ E),
      π ⟨p * e, Subgroup.mul_mem_sup hp he⟩ = ⟨e, he⟩ := by
  have hmem := mem_sup_iff_prod P E hcomm
  -- The multiplication map `↥P × ↥E → ↥(P ⊔ E)` is an isomorphism (internal direct product).
  let F : ↥P × ↥E →* ↥(P ⊔ E) :=
    MonoidHom.mk' (fun x => ⟨(x.1 : G) * (x.2 : G), Subgroup.mul_mem_sup x.1.2 x.2.2⟩)
      (by
        intro a b
        apply Subtype.ext
        show ((a.1 : G) * (b.1 : G)) * ((a.2 : G) * (b.2 : G)) =
          ((a.1 : G) * (a.2 : G)) * ((b.1 : G) * (b.2 : G))
        calc ((a.1 : G) * (b.1 : G)) * ((a.2 : G) * (b.2 : G))
            = (a.1 : G) * ((b.1 : G) * (a.2 : G)) * (b.2 : G) := by group
          _ = (a.1 : G) * ((a.2 : G) * (b.1 : G)) * (b.2 : G) := by
                rw [hcomm (b.1 : G) b.1.2 (a.2 : G) a.2.2]
          _ = ((a.1 : G) * (a.2 : G)) * ((b.1 : G) * (b.2 : G)) := by group)
  have hFval : ∀ (p : G) (hp : p ∈ P) (e : G) (he : e ∈ E),
      F (⟨p, hp⟩, ⟨e, he⟩) = ⟨p * e, Subgroup.mul_mem_sup hp he⟩ := by
    intro p hp e he
    apply Subtype.ext
    rfl
  have hinj : Function.Injective F := by
    rintro ⟨⟨p1, hp1⟩, ⟨e1, he1⟩⟩ ⟨⟨p2, hp2⟩, ⟨e2, he2⟩⟩ h
    have h' : p1 * e1 = p2 * e2 := by
      have := congrArg (fun z : ↥(P ⊔ E) => (z : G)) h
      simpa only [hFval] using this
    -- `p2⁻¹ * p1 = e2 * e1⁻¹` lies in `P ⊓ E = ⊥`, forcing `p1 = p2` and `e1 = e2`.
    have hkey : p2⁻¹ * p1 = e2 * e1⁻¹ := by
      calc p2⁻¹ * p1 = p2⁻¹ * (p1 * e1) * e1⁻¹ := by group
        _ = p2⁻¹ * (p2 * e2) * e1⁻¹ := by rw [h']
        _ = e2 * e1⁻¹ := by group
    have hmem_inf : p2⁻¹ * p1 ∈ P ⊓ E :=
      ⟨P.mul_mem (P.inv_mem hp2) hp1, by rw [hkey]; exact E.mul_mem he2 (E.inv_mem he1)⟩
    have h1 : p2⁻¹ * p1 = 1 := by
      have := hmem_inf
      rw [hinf, Subgroup.mem_bot] at this
      exact this
    have hp_eq : p1 = p2 := by
      have : p2⁻¹ * p1 = p2⁻¹ * p2 := by rw [h1, inv_mul_cancel]
      exact mul_left_cancel this
    have he_eq : e1 = e2 := by
      have h2 : e2 * e1⁻¹ = 1 := by rw [← hkey, h1]
      have : e1 * e1⁻¹ = e2 * e1⁻¹ := by rw [mul_inv_cancel, h2]
      exact mul_right_cancel this
    exact Prod.ext (Subtype.ext hp_eq) (Subtype.ext he_eq)
  have hsurj : Function.Surjective F := by
    intro y
    obtain ⟨p, hp, e, he, hpe⟩ := (hmem (y : G)).mp y.2
    refine ⟨(⟨p, hp⟩, ⟨e, he⟩), ?_⟩
    rw [hFval p hp e he]
    apply Subtype.ext
    simpa using hpe
  let eF : ↥P × ↥E ≃* ↥(P ⊔ E) := MulEquiv.ofBijective F ⟨hinj, hsurj⟩
  -- Project onto the `E`-coordinate.
  let π : ↥(P ⊔ E) →* ↥E := (MonoidHom.snd ↥P ↥E).comp (eF.symm : ↥(P ⊔ E) →* (↥P × ↥E))
  refine ⟨π, ?_⟩
  intro p hp e he
  have hx : eF (⟨p, hp⟩, ⟨e, he⟩) = ⟨p * e, Subgroup.mul_mem_sup hp he⟩ := hFval p hp e he
  change (MonoidHom.snd ↥P ↥E) (eF.symm ⟨p * e, Subgroup.mul_mem_sup hp he⟩) = ⟨e, he⟩
  rw [← hx, MulEquiv.symm_apply_apply]
  rfl

end Work.CORE4

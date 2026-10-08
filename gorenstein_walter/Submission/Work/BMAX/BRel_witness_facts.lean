import Mathlib
import Submission.Work.BMAX.D17Defs
import Submission.Work.BMAX.Defs
import Submission.Work.BMAX.Basic
import Submission.Work.BMAX.LayerCentralizesFitting

namespace Work.BMAX

open Subgroup

/-! ## Auxiliary facts about `centralizer` / `normalizer` / `zcenterIn` -/

/-- The centralizer of `H` normalizes every subgroup of `H`. -/
theorem centralizer_le_normalizer_of_le {G : Type*} [Group G] {K H : Subgroup G}
    (h : K ≤ H) :
    Subgroup.centralizer (H : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro c hc k hk
  have hcomm : c * k = k * c :=
    (Subgroup.mem_centralizer_iff.mp hc k (h hk)).symm
  have hconj : c * k * c⁻¹ = k := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  rwa [hconj]

/-- The centre of a subgroup centralizes it. -/
theorem zcenterIn_le_centralizer {G : Type*} [Group G] (K : Subgroup G) :
    Work.GW2.zcenterIn K ≤ Subgroup.centralizer (K : Set G) := by
  intro x hx
  obtain ⟨-, hxc⟩ := Work.GW2.mem_zcenterIn.mp hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (hxc y hy).symm

/-- **Witness facts for `A ⇝ B`.**

The witness `X ≤ F(A)` supplied by `BRel A B` also has the following companion properties:
it is normalized by `F*(A)` — indeed by everything that centralizes `F(A) ≅ F*(A)`... more
precisely, by the layer `E(A)` (`E(A)` centralizes `F(A)` and `X ≤ F(A)`) and by the centre
`Z(F(A))`.  These are exactly the ingredients used when the relation `A ⇝ B` is pushed
through the maximal-subgroup argument (Bender 1981, Lemma 2.4). -/
theorem BRel_witness_facts {G : Type} [Group G] [Finite G] (A B : Subgroup G)
    (hrel : Work.GW2.BRel A B) :
    ∃ X : Subgroup G, X ≤ Work.GW2.fittingIn A ∧
      (Subgroup.normalizer (X : Set G) ⊓ Work.GW2.fstarIn A ≤ B) ∧
      (Work.GW2.layerIn A ≤ Subgroup.normalizer (X : Set G)) ∧
      (Work.GW2.zcenterIn (Work.GW2.fittingIn A) ≤ Subgroup.normalizer (X : Set G)) ∧
      (Work.GW2.layerIn A ≤ Subgroup.normalizer (X : Set G) ⊓ Work.GW2.fstarIn A) := by
  obtain ⟨X, hX, hXB⟩ := hrel
  -- `E(A) ≤ F*(A)`, `Z(F(A))` both centralize `F(A) ⊇ X`, hence normalize `X`
  have hlayer : Work.GW2.layerIn A ≤ Subgroup.normalizer (X : Set G) :=
    le_trans (LayerCentralizesFitting G A) (centralizer_le_normalizer_of_le hX)
  have hzcen : Work.GW2.zcenterIn (Work.GW2.fittingIn A) ≤
      Subgroup.normalizer (X : Set G) :=
    le_trans (zcenterIn_le_centralizer (Work.GW2.fittingIn A))
      (centralizer_le_normalizer_of_le hX)
  exact ⟨X, hX, hXB, hlayer, hzcen,
    le_inf hlayer (Work.GW2.layerIn_le_fstarIn A)⟩

end Work.BMAX

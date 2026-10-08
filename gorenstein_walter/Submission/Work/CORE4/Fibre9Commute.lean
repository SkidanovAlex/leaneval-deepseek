import Mathlib
import Submission.Work.CORE4.Case2CentCard

namespace Work.CORE4

/-- **The fibre-9 commutation.**  Let `P, E ≤ G` commute elementwise with `P` commutative, and let
`π : ↥(P ⊔ E) →* ↥E` be the projection onto the `E`-coordinate of the internal direct product
`P ⊔ E` (so `π ⟨p * e, _⟩ = ⟨e, _⟩`).  If `Y ≤ P ⊔ E` and `Z ≤ P ⊔ E` centralize each other, then
their images under `π`, viewed inside `G` via `E.subtype`, still centralize each other.

The proof reads `a ∈ πY` and `b ∈ πZ` off representatives `ya, zb` of `Y` resp. `Z`; the
hypothesis `hc` gives `zb * ya = ya * zb`, and `commute_iff_proj` — which says two elements of the
internal direct product commute iff their `E`-coordinates do, the `P`-coordinates being
commutative — transfers this to `π zb * π ya = π ya * π zb`. -/
theorem Fibre9Commute {G : Type} [Group G] [Finite G] {P E Y Z : Subgroup G}
    (hcomm : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x)
    (hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (π : ↥(P ⊔ E) →* ↥E)
    (hπ : ∀ (p : G) (hp : p ∈ P) (e : G) (he : e ∈ E),
      π ⟨p * e, Subgroup.mul_mem_sup hp he⟩ = ⟨e, he⟩)
    (hY : Y ≤ P ⊔ E) (hZ : Z ≤ P ⊔ E)
    (hc : Y ≤ Subgroup.centralizer (Z : Set G)) :
    Subgroup.map E.subtype ((Y.subgroupOf (P ⊔ E)).map π) ≤
      Subgroup.centralizer
        (((Subgroup.map E.subtype ((Z.subgroupOf (P ⊔ E)).map π) : Subgroup G)) : Set G) := by
  intro a ha b hb
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨ya, hya, rfl⟩ := Subgroup.mem_map.mp ha'
  obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
  obtain ⟨zb, hzb, rfl⟩ := Subgroup.mem_map.mp hb'
  have hcz : (zb : G) * (ya : G) = (ya : G) * (zb : G) :=
    Subgroup.mem_centralizer_iff.mp (hc (Subgroup.mem_subgroupOf.mp hya)) (zb : G)
      (Subgroup.mem_subgroupOf.mp hzb)
  exact (commute_iff_proj hcomm hPab π hπ zb ya).mp hcz

end Work.CORE4

import Mathlib
import Submission.Work.CORE2A.TorusDefs

namespace Work.CORE2A

/-- **T1'** (Bender 1981 p. 220, "hence `S` normalizes `R^y`"; design pass 14 leaf `T1'`,
`Submission/Work/_design_gw/Core14.lean` §3).

Let `E := E(Ĥ) = layerIn B.Hhat`, `S = B.S`, and suppose that any two elements of `S` outside
`E` multiply into `E` (`hmul`, which is `P1` transported along `S ≤ SE`).  If `X ≤ C_G(E)` is a
subgroup obeyed by some `v ∈ S ∖ E` as an *inverting* element, `v x v⁻¹ = x⁻¹` for all `x ∈ X`,
then `S` normalizes `X`.

Proof (as in the source): write an arbitrary `w ∈ S` as:
* `w ∈ S ∩ E`: then `w` centralizes `X` because `X ≤ C_G(E)`, so `w x w⁻¹ = x ∈ X`;
* `w ∈ S ∖ E`: then `w v ∈ E` by `hmul`, hence `w v` centralizes `X`, while
  `v⁻¹ x v = x⁻¹` (`v` inverts `X`, and inversion is an involution of `X`).  Therefore
  `w x w⁻¹ = (w v) (v⁻¹ x v) (w v)⁻¹ = x⁻¹ ∈ X`.

(`S = (S ∩ E) ⟨v⟩`: `|S : S ∩ E| = 2`, so every `w` is in one of the two cases.) -/
theorem c14_S_normalizes {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) (hmul : ∀ a ∈ (B.S : Subgroup G), ∀ b ∈ (B.S : Subgroup G), a ∉ Work.GW2.layerIn B.Hhat → b ∉ Work.GW2.layerIn B.Hhat → a * b ∈ Work.GW2.layerIn B.Hhat) {X : Subgroup G} (hXC : X ≤ Subgroup.centralizer (Work.GW2.layerIn B.Hhat : Set G)) {v : G} (hvS : v ∈ (B.S : Subgroup G)) (hvE : v ∉ Work.GW2.layerIn B.Hhat) (hinv : ∀ x ∈ X, v * x * v⁻¹ = x⁻¹) : ∀ w ∈ (B.S : Subgroup G), ∀ x ∈ X, w * x * w⁻¹ ∈ X := by
  intro w hwS x hx
  by_cases hwE : w ∈ Work.GW2.layerIn B.Hhat
  · -- `w ∈ E` centralizes `X`.
    have hcomm : w * x = x * w := (Subgroup.mem_centralizer_iff.mp (hXC hx)) w hwE
    have hwx : w * x * w⁻¹ = x := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [hwx]; exact hx
  · -- `w ∉ E`: then `w * v ∈ E` centralizes `X`, and `v` inverts `X`.
    have hwv : w * v ∈ Work.GW2.layerIn B.Hhat := hmul w hwS v hvS hwE hvE
    have hxinv : x⁻¹ ∈ X := X.inv_mem hx
    -- `v⁻¹` also inverts `X`: inversion is an involution of `X`.
    have hvinv : v⁻¹ * x * v = x⁻¹ := by
      have h' : v * x⁻¹ * v⁻¹ = x := by
        have := congrArg Inv.inv (hinv x hx)
        simpa [mul_assoc] using this
      calc v⁻¹ * x * v = v⁻¹ * (v * x⁻¹ * v⁻¹) * v := by rw [h']
        _ = x⁻¹ := by group
    have hcomm : (w * v) * x⁻¹ = x⁻¹ * (w * v) :=
      (Subgroup.mem_centralizer_iff.mp (hXC hxinv)) (w * v) hwv
    have key : w * x * w⁻¹ = x⁻¹ := by
      calc w * x * w⁻¹ = (w * v) * (v⁻¹ * x * v) * (w * v)⁻¹ := by group
        _ = (w * v) * x⁻¹ * (w * v)⁻¹ := by rw [hvinv]
        _ = x⁻¹ := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [key]; exact hxinv

end Work.CORE2A

import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.piCore_isPiNat

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Fitting.pCoreSeries_one`

The first term of the upper `p`-series of a finite group `G` is `O_{p'}(G)`:

`pCoreSeries p G 1 = (O_{p'}(G/1)).comap (mk' 1) = O_{p'}(G)`.

The mathematical content is that `O_π` is invariant under group isomorphisms: pulling back
`O_π(H)` along a bijective homomorphism `f : G →* H` of finite groups returns `O_π(G)`
(both groups being finite, `|O_π(H)|` is a `π`-number).
-/

noncomputable section

open Classical

namespace Work.Fitting

/-- Pull back `O_π` along a bijective homomorphism of finite groups. -/
theorem piCore_comap_of_bijective {π : ℕ → Prop} {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] (f : G →* H) (hinj : Function.Injective f)
    (hsurj : Function.Surjective f) :
    (piCore π H).comap f = piCore π G := by
  have hrange : piCore π H ≤ f.range := by
    rw [MonoidHom.range_eq_top.mpr hsurj]
    exact le_top
  refine le_antisymm ?_ ?_
  · -- `(O_π H).comap f` is a normal `π`-subgroup of `G`
    refine le_piCore (Subgroup.normal_comap f) ?_
    have hmap : Subgroup.map f (Subgroup.comap f (piCore π H)) = piCore π H :=
      Subgroup.map_comap_eq_self hrange
    have hcard : Nat.card ↥(Subgroup.comap f (piCore π H)) = Nat.card ↥(piCore π H) := by
      conv_lhs => rw [← Subgroup.card_map_of_injective hinj]
      rw [hmap]
    rw [hcard]
    exact piCore_isPiNat H π
  · -- conversely `O_π G` maps into `O_π H`
    rw [← Subgroup.map_le_iff_le_comap]
    have hnorm : (piCore π G).Normal := inferInstance
    refine le_piCore (hnorm.map f hsurj) ?_
    rw [Subgroup.card_map_of_injective hinj]
    exact piCore_isPiNat G π

/-- The first term of the upper `p`-series is `O_{p'}(G)`. -/
theorem pCoreSeries_one (p : ℕ) (G : Type*) [Group G] [Finite G] :
    Work.Fitting.pCoreSeries p G 1 = Work.Fitting.pPrimeCore p G := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, pCoreSeries_succ]
  have hπ : (fun q : ℕ => (if Even 0 then q ≠ p else q = p)) = (fun q : ℕ => q ≠ p) := by
    funext q
    simp [Even.zero]
  rw [hπ]
  haveI : Finite (G ⧸ pCoreSeries p G 0) :=
    Finite.of_surjective (QuotientGroup.mk' (pCoreSeries p G 0))
      (QuotientGroup.mk'_surjective (pCoreSeries p G 0))
  have hinj : Function.Injective (QuotientGroup.mk' (pCoreSeries p G 0)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk' (pCoreSeries p G 0),
      pCoreSeries_zero]
  have hsurj : Function.Surjective (QuotientGroup.mk' (pCoreSeries p G 0)) :=
    QuotientGroup.mk'_surjective (pCoreSeries p G 0)
  exact (piCore_comap_of_bijective (π := fun q => q ≠ p) (H := G ⧸ pCoreSeries p G 0)
    (QuotientGroup.mk' (pCoreSeries p G 0)) hinj hsurj).trans rfl

end Work.Fitting

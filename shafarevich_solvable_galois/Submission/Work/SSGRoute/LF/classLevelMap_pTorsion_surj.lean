import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.phi1_level_index
import Submission.Work.SSGRoute.phi1_class_level
import Submission.Work.SSGRoute.pt_char_pTorsion
import Submission.Work.SSGRoute.E4R3.inflC_injective
import Submission.Work.SSGRoute.sylow_infl_injective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option synthInstance.maxHeartbeats 400000

set_option linter.style.haveILetI false

namespace Work.SSGRoute.LF

/-- **The `p`-torsion is realised at every level.**  Let `K ≤ L ≤ L' ≤ Ω` be levels with
`p ∣ [L : k]`, and let `y ∈ H²(Gal(L'/k), C_{L'})` be killed by `p`.  Then `y` is the inflation of a
`p`-torsion class at the level `L`.  (Both `p`-torsion subgroups are cyclic of order `p`
-- `Work.SSGRoute.pt_char_pTorsion` -- and inflation is injective on them
-- `Work.SSGRoute.SylowLevel.inflCIn_injective` / `Work.SSGRoute.E4R3.inflC_injective` -- so the
transition map between them is a bijection.) -/
theorem classLevelMap_pTorsion_surj (p : ℕ) [Fact p.Prime] {k K Ω : Type} [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
    [IsGalois k K] [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (L L' : Work.SSGRoute.Lvl k K Ω) (h : L ≤ L') (hp : p ∣ Module.finrank k ↥L.1)
    (y : Work.SSGRoute.ClassLevel L') (hy : p • y = 0) :
    ∃ w : Work.SSGRoute.ClassLevel L, p • w = 0 ∧
      Work.SSGRoute.classLevelMap (k := k) L L' h w = y := by
  -- The `p`-torsion at the level `L`, as a subgroup with a bijection onto `ZMod p`.
  obtain ⟨P, χ, hP, hχ⟩ := Work.SSGRoute.pt_char_pTorsion p k K (↥L.1) hp
  -- `p` divides the degree of any higher level `L'`.
  letI : Algebra ↥L.1 ↥L'.1 := (IntermediateField.inclusion (K := K) (L := Ω) h).toAlgebra
  haveI : IsScalarTower k ↥L.1 ↥L'.1 := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hp' : p ∣ Module.finrank k ↥L'.1 := by
    rw [← Module.finrank_mul_finrank k ↥L.1 ↥L'.1]
    exact Dvd.dvd.mul_right hp _
  -- The `p`-torsion at the level `L'`.
  obtain ⟨P', χ', hP', hχ'⟩ := Work.SSGRoute.pt_char_pTorsion p k K (↥L'.1) hp'
  -- Inflation restricted to the `p`-torsion subgroups.
  let g : P → P' := fun v =>
    ⟨Work.SSGRoute.classLevelMap (k := k) L L' h v.1,
      (hP' _).mpr (by rw [← map_nsmul, (hP v.1).mp v.2, map_zero])⟩
  -- It is injective, since inflation is injective on the whole `H²`.
  have hg_inj : Function.Injective g := by
    intro v w hvw
    apply Subtype.ext
    have h1 : Work.SSGRoute.classLevelMap (k := k) L L' h v.1
        = Work.SSGRoute.classLevelMap (k := k) L L' h w.1 := congrArg Subtype.val hvw
    exact SylowLevel.inflCIn_injective (k := k) (K := K) (Ω := Ω) L.1 L'.1 h
      (by simpa only [Work.SSGRoute.classLevelMap_apply] using h1)
  -- Both `p`-torsion subgroups are cyclic of order `p`.
  have hcardP : Nat.card P = p := by
    rw [Nat.card_eq_of_bijective (⇑χ) hχ, Nat.card_zmod]
  have hcardP' : Nat.card P' = p := by
    rw [Nat.card_eq_of_bijective (⇑χ') hχ', Nat.card_zmod]
  haveI : Finite P' :=
    Nat.finite_of_card_ne_zero (by rw [hcardP']; exact (Fact.out : p.Prime).ne_zero)
  -- Hence the injective transition map is bijective, in particular surjective.
  have hbij : Function.Bijective g :=
    hg_inj.bijective_of_nat_card_le (by rw [hcardP, hcardP'])
  obtain ⟨w, hw⟩ := hbij.surjective ⟨y, (hP' y).mpr hy⟩
  refine ⟨w.1, (hP w.1).mp w.2, ?_⟩
  have := congrArg Subtype.val hw
  simpa [g] using this

end Work.SSGRoute.LF

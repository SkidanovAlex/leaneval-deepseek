import Mathlib
import Submission.NK.CFTLib.ARL.IdeleCongruenceLift
import Submission.NK.CFTLib.ARL.RelNormFI
import Submission.NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.CFTLib.ARL

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

open NK.GlobalCFT

/-- **The ideal of `z` lies in the ray times the norm group** whenever `z` is congruent to `1`
modulo `m` and `z = N_{L/K}(y)·(β)` for some idèle `y` of `L` and `β ∈ Kˣ`.

Proof plan (the statement is TRUE; note that the second review below is mistaken, its alleged
counterexample `z_7 = 3` does *not* lie in the congruence subgroup since `v(3-1) = v(2) = 1 > v(7)`
in the additive convention used by `congruenceSubgroup`):
* use `NK.CFTLib.ARL.exists_adjust_congruenceSubgroup L m hm y` to find `d : Lˣ` with
  `y' := y * principalIdele L d ∈ congruenceSubgroup L m` (adjust in `L`, not in `K`!);
* `normIdeleHom_mem_congruenceSubgroup` gives `N(y') ∈ congruenceSubgroup K m`, so
  `principalIdele K (β / N_{L/K} d) = z * (N y')⁻¹ ∈ congruenceSubgroup K m`, whence
  `unitsToIdealUnits K (β / N_{L/K} d) ∈ principalRay K m`
  (`NK.CFTLib.ARL.unitsToIdealUnits_mem_principalRay`);
* `idealOf (N y') = relNormFI (idealOf y')` (`NK.CFTLib.ARL.idealOf_normIdeleHom`), and
  `count L 𝔓 (idealOf y') = 0` for every `𝔓 ∋ (m)`
  (`NK.CFTLib.ARL.count_idealOf_eq_zero_of_congruence`), so
  `relNormUnit (idealOf y') ∈ normIdeals K L m` (`NK.CFTLib.ARL.relNormUnit_mem_normIdeals`);
* `z = N(y')·(β/N_{L/K} d)`, so `idealOf z` is the product of the two ideals above, and
  `Subgroup.mul_mem` finishes. -/
theorem idealOf_mem_principalRay_sup_normIdeals {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] {m : ℕ} (hm : 0 < m) {y : NK.GlobalCFT.Idele L} {β : Kˣ} {z : NK.GlobalCFT.Idele K} (hz : z ∈ NK.CFTLib.Arl.congruenceSubgroup K m) (hzy : z = NK.GlobalCFT.Idele.normIdeleHom K L y * NK.GlobalCFT.Idele.principalIdele K β) : Units.mk0 (NK.GlobalCFT.Idele.idealOf z) (NK.GlobalCFT.Idele.idealOf_ne_zero z) ∈ NK.CFTLib.ARL.principalRay K m ⊔ NK.CFTLib.ARL.normIdeals K L m := by
  classical
  -- adjust `y` in `L` so that it becomes congruent to `1` modulo `m`
  obtain ⟨d, hd⟩ := NK.CFTLib.ARL.exists_adjust_congruenceSubgroup L m hm y
  set y' : Idele L := y * Idele.principalIdele L d with hy'_def
  have hd' : y' ∈ NK.CFTLib.Arl.congruenceSubgroup L m := hd
  -- the norm of the adjusted idèle is congruent to `1` modulo `m`
  have hNy'mem : Idele.normIdeleHom K L y' ∈ NK.CFTLib.Arl.congruenceSubgroup K m :=
    NK.CFTLib.Arl.normIdeleHom_mem_congruenceSubgroup m hm hd'
  have hNy'_eq : Idele.normIdeleHom K L y' =
      Idele.normIdeleHom K L y * Idele.principalIdele K (Units.map (Algebra.norm K) d) := by
    rw [hy'_def, map_mul, Idele.normIdeleHom_principalIdele]
  -- the leftover principal idèle
  have hprinc : Idele.principalIdele K (β / Units.map (Algebra.norm K) d) =
      z * (Idele.normIdeleHom K L y')⁻¹ := by
    rw [hzy, hNy'_eq, map_div]
    simp [div_eq_mul_inv, mul_assoc, mul_comm]
  have hprinc_mem : Idele.principalIdele K (β / Units.map (Algebra.norm K) d) ∈
      NK.CFTLib.Arl.congruenceSubgroup K m := by
    rw [hprinc]
    exact Subgroup.mul_mem _ hz (Subgroup.inv_mem _ hNy'mem)
  -- its ideal lies in the ray
  have hray : unitsToIdealUnits K (β / Units.map (Algebra.norm K) d) ∈ principalRay K m :=
    NK.CFTLib.ARL.unitsToIdealUnits_mem_principalRay m hprinc_mem
  -- the ideal of `N y'` lies in the norm group
  have hnorm : Units.mk0 (Idele.idealOf (Idele.normIdeleHom K L y'))
      (Idele.idealOf_ne_zero _) ∈ normIdeals K L m := by
    have hA : ∀ 𝔓 : HeightOneSpectrum (𝓞 L), (m : 𝓞 L) ∈ 𝔓.asIdeal →
        FractionalIdeal.count L 𝔓 (Units.mk0 (Idele.idealOf y') (Idele.idealOf_ne_zero y') :
          FractionalIdeal (𝓞 L)⁰ L) = 0 := by
      intro 𝔓 h𝔓
      rw [Units.val_mk0]
      exact NK.CFTLib.ARL.count_idealOf_eq_zero_of_congruence hd' 𝔓 h𝔓
    have hmem := NK.CFTLib.ARL.relNormUnit_mem_normIdeals (K := K) (L := L) m
      (A := Units.mk0 (Idele.idealOf y') (Idele.idealOf_ne_zero y')) hA
    convert hmem using 1
    apply Units.ext
    simp only [Units.val_mk0]
    exact NK.CFTLib.ARL.idealOf_normIdeleHom y'
  -- split `z` as the product of the two pieces
  have hz_split : z = Idele.normIdeleHom K L y' *
      Idele.principalIdele K (β / Units.map (Algebra.norm K) d) := by
    rw [hprinc]
    simp
  suffices h : Units.mk0 (Idele.idealOf z) (Idele.idealOf_ne_zero z) =
      Units.mk0 (Idele.idealOf (Idele.normIdeleHom K L y')) (Idele.idealOf_ne_zero _) *
        unitsToIdealUnits K (β / Units.map (Algebra.norm K) d) by
    rw [h]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hnorm) (Subgroup.mem_sup_left hray)
  apply Units.ext
  simp only [Units.val_mk0, Units.val_mul]
  rw [hz_split, Idele.idealOf_mul, unitsToIdealUnits_coe, Idele.idealOf_principalIdele]

end NK.CFTLib.ARL

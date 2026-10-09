import Mathlib
import Submission.NK.NUV2.ChebAux.auxLocalCondition
import Submission.NK.LocalReciprocity.NormGroup
import Submission.NK.Unramified.normGroup_eq_unramifiedNormGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The index of the sup of the `d`-unramified norm group and the local norm group

Let `L / K` be a finite Galois extension of number fields, `Q` a finite place of `K` and `r` a
place of `L` above `Q`, with local inertia degree `f = f(r | Q)`.  Writing `N = N_{L_r/K_Q} L_rˣ`
for the norm group of the corresponding local extension of completions, and
`U^0 = O_{K_Q}ˣ` for the units of the ring of integers of `K_Q`, the elementary valuation
computation of the norm group (`unitsValLog (N u) = (unitsValLog u)^f`) gives

  `U^0 ⊔ N = {x ∈ K_Qˣ | f ∣ v(x)} = (reduced valuation)⁻¹(1)`,

so that `[K_Qˣ : U^0 ⊔ N] = f`.  Since `⟨π^{d}⟩ ⊆ U^0 ⊔ N` whenever `f ∣ d` (`π` a uniformiser),
we get the same index `f` for `⟨π^d⟩ · U^0 ⊔ N = N_{L_{d}/K_Q} · U^0 ⊔ N`, where
`N_{L_d/K_Q} = ⟨π^d⟩ · U^0` is the norm group of the unramified extension of degree `d`.

This is the "unramified index" computation used in the descent step of the Hasse principle.
-/

namespace NK.CFTLib.IdeleHasse.Descent

open IsDedekindDomain.HeightOneSpectrum
open Commons.NumberTheory.NumberField.Completion
open Commons.NumberTheory.NumberField.Completion.NormIndexUnits
open scoped NumberField

noncomputable section

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

/-- The map `z ↦ z.toAdd mod n` kills every `n`-th power of `Multiplicative ℤ`. -/
lemma multIntToZMod_pow_self (n : ℕ) (z : Multiplicative ℤ) :
    multIntToZMod n (z ^ n) = 1 := by
  rw [multIntToZMod_apply, toAdd_pow_multiplicative, Int.cast_mul, Int.cast_natCast,
    ZMod.natCast_self, zero_mul]
  rfl

theorem indexSupNormGroupUnramified {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (r : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hr : r.asIdeal.LiesOver Q.asIdeal)
    (d : ℕ) (hd : r.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) ∣ d) :
    letI : Algebra (Q.adicCompletion K) (r.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q r hr)
    (NK.LocalReciprocityLubinTate.unramifiedNormGroup K Q d ⊔
      NK.LocalReciprocity.normGroup (Q.adicCompletion K) (r.adicCompletion L)).index
      = r.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
  letI : Algebra (Q.adicCompletion K) (r.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q r hr)
  set f : ℕ := r.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) with hf
  set N : Subgroup (Q.adicCompletion K)ˣ :=
    NK.LocalReciprocity.normGroup (Q.adicCompletion K) (r.adicCompletion L) with hN
  set w : (Q.adicCompletion K)ˣ →* Multiplicative (ZMod f) :=
    (multIntToZMod f).comp (unitsValLog (Q.adicCompletion K)) with hw
  have hw_apply : ∀ x : (Q.adicCompletion K)ˣ,
      w x = multIntToZMod f (unitsValLog (Q.adicCompletion K) x) := fun x => rfl
  -- `U^0 = ker unitsValLog`
  have hU : NK.LocalReciprocityLubinTate.adicUnits K Q =
      (unitsValLog (Q.adicCompletion K)).ker := by
    rw [NK.Unramified.NormGroupEqUnramified.adicUnits_eq_unitGroup,
      ← adicUnitsVal_eq_unitGroup K Q]
    rfl
  have hUle : NK.LocalReciprocityLubinTate.adicUnits K Q ≤ w.ker := by
    intro x hx
    have hx1 : unitsValLog (Q.adicCompletion K) x = 1 := MonoidHom.mem_ker.mp (hU ▸ hx)
    rw [MonoidHom.mem_ker, hw_apply, hx1, map_one]
  have hNle : N ≤ w.ker := by
    intro x hx
    rw [hN, NK.LocalReciprocity.normGroup_eq_range, MonoidHom.mem_range] at hx
    obtain ⟨u, rfl⟩ := hx
    rw [MonoidHom.mem_ker, hw_apply, unitsValLog_norm Q r hr u]
    exact multIntToZMod_pow_self f _
  have hker_le : w.ker ≤ NK.LocalReciprocityLubinTate.adicUnits K Q ⊔ N := by
    intro x hx
    rw [MonoidHom.mem_ker, hw_apply, multIntToZMod_eq_one_iff] at hx
    obtain ⟨k, hk⟩ := hx
    obtain ⟨u, hu⟩ := unitsValLog_adicCompletion_surjective L r (Multiplicative.ofAdd k)
    set z : (Q.adicCompletion K)ˣ :=
      Units.map (Algebra.norm (Q.adicCompletion K) :
        (r.adicCompletion L) →* (Q.adicCompletion K)) u with hz
    have hzval : unitsValLog (Q.adicCompletion K) z = unitsValLog (Q.adicCompletion K) x := by
      apply Multiplicative.toAdd.injective
      rw [hz, unitsValLog_norm Q r hr u, hu, toAdd_pow_multiplicative, hk, toAdd_ofAdd]
    have hmem : x * z⁻¹ ∈ NK.LocalReciprocityLubinTate.adicUnits K Q := by
      rw [hU, MonoidHom.mem_ker, map_mul, map_inv, hzval, mul_inv_cancel]
    refine Subgroup.mem_sup.mpr ⟨x * z⁻¹, hmem, z, ?_, ?_⟩
    · rw [hN, NK.LocalReciprocity.normGroup_eq_range]
      exact MonoidHom.mem_range.mpr ⟨u, hz.symm⟩
    · rw [mul_assoc, inv_mul_cancel, mul_one]
  have hUN : NK.LocalReciprocityLubinTate.adicUnits K Q ⊔ N = w.ker :=
    le_antisymm (sup_le hUle hNle) hker_le
  -- `π^d ∈ w.ker` because `f ∣ d`
  have hpi : (NK.LocalReciprocityLubinTate.uniformizerUnit K Q) ^ d ∈ w.ker := by
    rw [MonoidHom.mem_ker, hw_apply, multIntToZMod_eq_one_iff, map_pow,
      NK.Unramified.NormGroupEqUnramified.unitsValLog_uniformizerUnit Q,
      toAdd_pow_multiplicative, toAdd_ofAdd]
    obtain ⟨c, hc⟩ := hd
    refine ⟨(c : ℤ) * (-1), ?_⟩
    rw [hc]
    push_cast
    ring
  have hAsup : NK.LocalReciprocityLubinTate.unramifiedNormGroup K Q d ⊔ N = w.ker := by
    have hz : Subgroup.zpowers ((NK.LocalReciprocityLubinTate.uniformizerUnit K Q) ^ d) ≤
        w.ker := Subgroup.zpowers_le.mpr hpi
    rw [NK.LocalReciprocityLubinTate.unramifiedNormGroup, sup_assoc, hUN,
      sup_eq_right.mpr hz]
  rw [hAsup, Subgroup.index_ker]
  have hrange : w.range = ⊤ := MonoidHom.range_eq_top.mpr
    ((multIntToZMod_surjective f).comp (unitsValLog_adicCompletion_surjective K Q))
  rw [hrange, Subgroup.card_top]
  exact Nat.card_zmod f

end

end NK.CFTLib.IdeleHasse.Descent

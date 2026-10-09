import Mathlib
import Submission.Work.SSGRoute.CycLevel.GrunwaldImports
import Submission.Work.SSGRoute.ZDataMup.onePlace_mem_normImage_of_mem_sup_abelian
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.CycLevel

/-- **The one-place dictionary between the global norm class subgroup and the local norm group.**

For a finite Galois extension `L/k` of number fields with *commutative* Galois group, a finite place
`Q` of `k` and `x ∈ k_Qˣ`: the class of the one-place idèle at `Q` with value `x` lies in the global
norm class subgroup `N_{L/k} C_L` if and only if `x` is a local norm at `Q`.

The converse direction is the dictionary `onePlace_mem_normImage_iff`; the forward direction is the
one-place form of Hilbert's reciprocity law (the abelian hypothesis is essential: the statement is
false for non-abelian `L/k`). -/
theorem localNormSubgroup_eq_preimage_normClass {k L : Type} [Field k] [NumberField k]
    [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    [IsMulCommutative (L ≃ₐ[k] L)]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (x : (Q.adicCompletion k)ˣ) :
    (NK.GlobalCFT.IdeleClassGroup.mk k
        (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q) x) ∈
      NK.GlobalCFT.Idele.normClassSubgroup k L) ↔
    x ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := k) (L := L)
          (NK.GlobalCFT.Place.ofFinite Q) := by
  constructor
  · -- forward: a norm class modulo principal idèles is a norm, by one-place Hilbert reciprocity
    intro hq
    rw [NK.GlobalCFT.Idele.normClassSubgroup, Subgroup.mem_map] at hq
    obtain ⟨n, hn, hmn⟩ := hq
    have hpr : n⁻¹ * NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q) x ∈
        NK.GlobalCFT.Idele.principalSubgroup k :=
      (NK.GlobalCFT.IdeleClassGroup.mk_eq_mk_iff).mp hmn
    have hmem : NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q) x ∈
        NK.GlobalCFT.Idele.normImage k L ⊔ NK.GlobalCFT.Idele.principalSubgroup k := by
      rw [← mul_inv_cancel_left n (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite Q) x)]
      exact Subgroup.mul_mem_sup hn hpr
    have hcomm : ∀ a b : L ≃ₐ[k] L, a * b = b * a := fun a b => mul_comm' a b
    exact (NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := k) (L := L)
      (NK.GlobalCFT.Place.ofFinite Q) x).mp
      (Work.SSGRoute.ZDataMup.onePlace_mem_normImage_of_mem_sup_abelian (K := k) (L := L)
        hcomm hmem)
  · -- backward: a local norm is an idèle norm, hence its class is a norm class
    intro hx
    rw [NK.GlobalCFT.Idele.normClassSubgroup, Subgroup.mem_map]
    exact ⟨_, (NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := k) (L := L)
      (NK.GlobalCFT.Place.ofFinite Q) x).mpr hx, rfl⟩

end Work.SSGRoute.CycLevel

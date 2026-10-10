import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.LocalAnabelian.ResidueField.Recovery
import Submission.NK.TameStructureDeep.Support.mem_unramifiedClosure_of_isPrimitiveRoot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.TameStructureDeep.Tame

theorem kummer_tateTwist_of_pow_eq {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']
    [IsSepClosure κ K'] {p q n : ℕ} (hn : ¬ p ∣ n) {a : κ} (ha : a ≠ 0) {β : K'}
    (hβ : β ^ n = algebraMap κ K' a)
    {F : Gal(K'/κ)} (hF : NK.LocalAnabelian.IsFrobeniusFor (κ := κ) (K' := K') p q F)
    (σ : Gal(K'/κ))
    (hσ : σ ∈ (NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p).fixingSubgroup) :
    (F * σ * F⁻¹) β / β = (σ β / β) ^ q := by
  -- `n ≠ 0` since `p ∣ 0`
  have hn0 : n ≠ 0 := fun h => hn (h ▸ dvd_zero p)
  -- `a` is nonzero, hence so is `β`
  have ha' : algebraMap κ K' a ≠ 0 :=
    fun h => ha (FaithfulSMul.algebraMap_injective κ K' (by simpa using h))
  have hβne : β ≠ 0 := by
    intro h
    rw [h, zero_pow hn0] at hβ
    exact ha' hβ.symm
  -- `σ` fixes `κ^{ur}` pointwise
  have hσfix := hσ
  simp only [IntermediateField.mem_fixingSubgroup_iff] at hσfix
  -- the Kummer character of `σ` at `β`
  set γ : K' := σ β / β with hγdef
  have hγpow : γ ^ n = 1 := by
    rw [hγdef, div_pow, ← map_pow σ β n, hβ, AlgEquiv.commutes, div_self ha']
  -- `γ` has order prime to `p`, so the Frobenius sends it to its `q`-th power
  have hγF : F γ = γ ^ q := by
    refine hF.2 (orderOf γ) ?_ γ (IsPrimitiveRoot.iff_orderOf.mpr rfl)
    intro h
    exact hn (h.trans (orderOf_dvd_iff_pow_eq_one.mpr hγpow))
  -- `δ = F⁻¹β / β` is a root of unity of order dividing `n`, hence prime to `p`,
  -- so it lies in `κ^{ur}` and is fixed by `σ`
  set δ : K' := F.symm β / β with hδdef
  have hβ₁pow : (F.symm β) ^ n = algebraMap κ K' a := by
    rw [← map_pow, hβ, AlgEquiv.commutes]
  have hδpow : δ ^ n = 1 := by
    rw [hδdef, div_pow, hβ₁pow, hβ, div_self ha']
  have hδmem : δ ∈ NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p := by
    refine mem_unramifiedClosure_of_isPrimitiveRoot (p := p) (ζ := δ) ?_
      (IsPrimitiveRoot.iff_orderOf.mpr rfl)
    intro h
    exact hn (h.trans (orderOf_dvd_iff_pow_eq_one.mpr hδpow))
  have hσδ : σ δ = δ := hσfix δ hδmem
  -- the Kummer character is independent of the chosen `n`-th root of `a`
  have hσβ : σ β = γ * β := by
    rw [hγdef]
    exact (div_mul_cancel₀ (σ β) hβne).symm
  have hσβ₁ : σ (F.symm β) = γ * (F.symm β) := by
    have hβ₁eq : F.symm β = δ * β := by
      rw [hδdef]
      exact (div_mul_cancel₀ (F.symm β) hβne).symm
    rw [hβ₁eq, map_mul, hσδ, hσβ]
    ring
  -- the main computation
  have hmain : (F * σ * F⁻¹) β = γ ^ q * β := by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
    show F (σ (F.symm β)) = γ ^ q * β
    rw [hσβ₁, map_mul, hγF, AlgEquiv.apply_symm_apply]
  rw [div_eq_iff hβne]
  exact hmain

end NK.TameStructureDeep.Tame

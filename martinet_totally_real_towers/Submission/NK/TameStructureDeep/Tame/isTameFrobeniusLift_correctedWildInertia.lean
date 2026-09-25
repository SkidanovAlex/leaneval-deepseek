import Mathlib
import Submission.NK.TameStructureDeep.Tame.TameClosure
import Submission.NK.TameStructureDeep.Tame.kummer_tateTwist_of_pow_eq
import Submission.NK.TameStructureDeep.Tame.mem_correctedWildInertia_of_forall
import Submission.NK.LocalTame.Basic
import Submission.NK.LocalAnabelian.ResidueField.Recovery
import Submission.NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure
import Submission.NK.LocalAnabelian.ResidueField.isGalois_unramifiedClosure

/-!
# A Frobenius element acts on the tame inertia by the `q`-th power map

This file proves the local Frobenius normalisation of NSW (12.1.8) in the form in which the
corrected wild inertia `V_κ = Gal(K'/κ^{tr})` (`NK.TameStructureDeep.Tame.correctedWildInertia`)
is used: if `F ∈ Gal(K'/κ)` is a Frobenius element for the residue field order `q`
(`NK.LocalAnabelian.IsFrobeniusFor p q F`), then for every `y` in the inertia subgroup
`I_κ = Gal(K'/κ^{ur})` the element `F y F⁻¹ y^{-q}` fixes the maximal tamely ramified extension
`κ^{tr} = κ^{ur}(π^{1/n} : p ∤ n)`, i.e. lies in `V_κ`:

  `IsTameFrobeniusLift q V_κ I_κ F`.

The mathematical content is the Tate twist `(F y F⁻¹) β / β = (y β / β) ^ q` on each Kummer layer
`β ^ n = π` (`kummer_tateTwist_of_pow_eq`): the two automorphisms `F y F⁻¹` and `y ^ q` of the
Kummer layer agree on the generator `β`, hence their quotient fixes `κ^{ur}(β)`.  Since `κ^{tr}` is
generated over `κ^{ur}` by all such roots `β`, the quotient fixes `κ^{tr}`
(`mem_correctedWildInertia_of_forall`).
-/

set_option linter.style.haveILetI false

open scoped Classical
open IntermediateField

namespace NK.TameStructureDeep.Tame

/-- **The Frobenius normalisation on a prime-to-`p` Kummer layer.**
For `n` prime to `p`, `a ∈ κ^×`, `β ^ n = a`, `F` a Frobenius element for the residue cardinality
`q` and `σ` fixing `κ^{ur} = κ(μ_{p'})` pointwise, the element `F σ F⁻¹ (σ ^ q)⁻¹` fixes both
`κ^{ur}` (the fixing subgroup of the Galois extension `κ^{ur}/κ` is normal) and the generator `β`
of the Kummer layer (by the Tate twist `kummer_tateTwist_of_pow_eq`, both `F σ F⁻¹` and `σ ^ q`
act on the Kummer line through the same character `γ ^ q`).

This is `NK.TameStructureDeep.Tame.conj_mul_pow_inv_mem_fixingSubgroup_adjoin` with the
primality of the exponent replaced by `p ∤ n`, via `kummer_tateTwist_of_pow_eq`. -/
theorem conj_mul_pow_inv_mem_fixingSubgroup_unramifiedClosure {κ K' : Type*} [Field κ] [Field K']
    [Algebra κ K'] [IsSepClosure κ K'] {p q n : ℕ} (hn : ¬ p ∣ n) {a : κ} (ha : a ≠ 0)
    {β : K'} (hβ : β ^ n = algebraMap κ K' a)
    {F : Gal(K'/κ)} (hF : NK.LocalAnabelian.IsFrobeniusFor (κ := κ) (K' := K') p q F)
    (σ : Gal(K'/κ))
    (hσ : σ ∈ (NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p).fixingSubgroup) :
    F * σ * F⁻¹ * (σ ^ q)⁻¹ ∈
        (NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p).fixingSubgroup ∧
      (F * σ * F⁻¹ * (σ ^ q)⁻¹) β = β := by
  -- `n ≠ 0` since `p ∣ 0`, and `β ≠ 0` since `a ≠ 0`
  have hn0 : n ≠ 0 := fun h => hn (h ▸ dvd_zero p)
  have ha' : algebraMap κ K' a ≠ 0 := fun h =>
    ha (FaithfulSMul.algebraMap_injective κ K' (by simpa using h))
  have hβne : β ≠ 0 := by
    intro h
    rw [h, zero_pow hn0] at hβ
    exact ha' hβ.symm
  -- the Kummer character of `σ` at `β`
  set γ : K' := σ β / β with hγdef
  have hγne : γ ≠ 0 := by
    rw [hγdef]
    exact div_ne_zero ((map_ne_zero σ).mpr hβne) hβne
  have hγpow : γ ^ n = 1 := by
    rw [hγdef, div_pow, ← map_pow σ β n, hβ, AlgEquiv.commutes, div_self ha']
  -- `γ` is a root of unity of order dividing `n`, hence of order prime to `p`, so it lies in
  -- `κ^{ur}`
  have hγL : γ ∈ NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p := by
    refine NK.TameStructureDeep.mem_unramifiedClosure_of_isPrimitiveRoot (p := p) ?_
      (IsPrimitiveRoot.iff_orderOf.mpr rfl)
    intro h
    exact hn (h.trans (orderOf_dvd_iff_pow_eq_one.mpr hγpow))
  -- and then is fixed by `σ`
  have hσγ : σ γ = γ :=
    (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ γ hγL
  -- `κ^{ur}/κ` is Galois, so its fixing subgroup is normal: `F σ F⁻¹` fixes `κ^{ur}`
  haveI hLgal : IsGalois κ (NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p) :=
    NK.LocalAnabelian.ResidueField.isGalois_unramifiedClosure p
  have hnorm :
      (NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p).fixingSubgroup.Normal :=
    inferInstance
  have hconj : F * σ * F⁻¹ ∈
      (NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p).fixingSubgroup :=
    hnorm.conj_mem σ hσ F
  -- `σ` acts on the Kummer line `κ β` through the fixed character `γ`
  have hσpowγ : ∀ k : ℕ, (σ ^ k) γ = γ := by
    intro k
    induction k with
    | zero => rfl
    | succ m ih => rw [pow_succ, AlgEquiv.mul_apply, hσγ, ih]
  have hσβ : σ β = γ * β := by
    rw [hγdef]
    exact (div_mul_cancel₀ (σ β) hβne).symm
  have hpow : ∀ k : ℕ, (σ ^ k) β = γ ^ k * β := by
    intro k
    induction k with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, AlgEquiv.mul_apply, hσβ, map_mul, hσpowγ m, ih, pow_succ]
      ring
  -- consequently `(σ ^ q)⁻¹ β = (γ ^ q)⁻¹ β`
  have hw : (σ ^ q)⁻¹ β = (γ ^ q)⁻¹ * β := by
    refine (σ ^ q).injective ?_
    have h2 : (σ ^ q) ((γ ^ q)⁻¹ * β) = β := by
      rw [map_mul, map_inv₀, map_pow, hσpowγ q, hpow q,
        inv_mul_cancel_left₀ (pow_ne_zero q hγne)]
    rw [h2]
    exact AlgEquiv.apply_symm_apply (σ ^ q) β
  -- `F σ F⁻¹` fixes `κ^{ur}`, in particular `(γ ^ q)⁻¹`
  have hconjγ : (F * σ * F⁻¹) ((γ ^ q)⁻¹) = (γ ^ q)⁻¹ :=
    (IntermediateField.mem_fixingSubgroup_iff _ (F * σ * F⁻¹)).mp hconj _
      (inv_mem (pow_mem hγL q))
  -- the Tate twist `kummer_tateTwist_of_pow_eq`: `(F σ F⁻¹) β = γ ^ q * β`
  have hFσβ : (F * σ * F⁻¹) β = γ ^ q * β := by
    rw [hγdef]
    exact (div_eq_iff hβne).mp (kummer_tateTwist_of_pow_eq (K' := K') hn ha hβ hF σ hσ)
  -- hence `F σ F⁻¹ (σ ^ q)⁻¹` fixes `β`
  have heβ : (F * σ * F⁻¹ * (σ ^ q)⁻¹) β = β := by
    rw [AlgEquiv.mul_apply, hw, map_mul, hconjγ, hFσβ,
      inv_mul_cancel_left₀ (pow_ne_zero q hγne)]
  -- and it fixes `κ^{ur}`
  have heL : F * σ * F⁻¹ * (σ ^ q)⁻¹ ∈
      (NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p).fixingSubgroup :=
    mul_mem hconj (Subgroup.inv_mem _ (Subgroup.pow_mem _ hσ q))
  exact ⟨heL, heβ⟩

/-- **Frobenius elements act on the tame inertia by the `q`-th power map** (NSW (12.1.8) Lemma;
Iwasawa): for `F` a Frobenius element for the residue field order `q`, the element
`F y F⁻¹ (y ^ q)⁻¹` lies in the corrected wild inertia `V_κ = Gal(K'/κ^{tr})` for every `y` in the
inertia subgroup `I_κ`.

Equivalently, `F` is a tame Frobenius lift:
`IsTameFrobeniusLift q V_κ I_κ F`.  The proof checks the two generators of `κ^{tr}` over `κ`:
`F y F⁻¹ (y ^ q)⁻¹` fixes `κ^{ur}` because `V_κ ≤ I_κ = Gal(K'/κ^{ur})` is normal in `Gal(K'/κ)`,
and it fixes every root `β` of the uniformiser of order prime to `p` by the Tate twist of
`conj_mul_pow_inv_mem_fixingSubgroup_unramifiedClosure`; hence it fixes `κ^{tr}` by
`mem_correctedWildInertia_of_forall`. -/
theorem isTameFrobeniusLift_correctedWildInertia {κ K' : Type*} [Field κ] [Field K']
    [Algebra κ K'] [IsSepClosure κ K'] {p q : ℕ} (hp : p ≠ 1) {π : κ} (hπ : π ≠ 0)
    {F : Gal(K'/κ)}
    (hF : NK.LocalAnabelian.IsFrobeniusFor (κ := κ) (K' := K') p q F) :
    NK.LocalTame.IsTameFrobeniusLift q
      (NK.TameStructureDeep.Tame.correctedWildInertia (K' := K') p π)
      (NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p) F := by
  refine ⟨hF.1, fun y hy => ?_⟩
  -- it suffices to show that `F y F⁻¹ (y ^ q)⁻¹` fixes `κ^{ur}` and all prime-to-`p` roots of `π`
  refine mem_correctedWildInertia_of_forall hp (F * y * F⁻¹ * (y ^ q)⁻¹) ?_ ?_
  · -- it fixes `κ^{ur}`, since it lies in the normal subgroup `I_κ = Gal(K'/κ^{ur})`
    intro z hz
    have hconj : F * y * F⁻¹ ∈ NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p :=
      (NK.LocalAnabelian.inertiaSubgroup_normal p).conj_mem y hy F
    have hmem : F * y * F⁻¹ * (y ^ q)⁻¹ ∈
        NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p :=
      mul_mem hconj (Subgroup.inv_mem _ (Subgroup.pow_mem _ hy q))
    rw [NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure]
      at hmem
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hmem z hz
  · -- it fixes every `n`-th root of `π` with `p ∤ n` by the Tate twist
    intro n hn β hβ
    have hσ : y ∈
        (NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p).fixingSubgroup := by
      rw [← NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure]
      exact hy
    exact (conj_mul_pow_inv_mem_fixingSubgroup_unramifiedClosure (K' := K') (p := p) (q := q)
      (n := n) hn (a := π) hπ (β := β) hβ hF y hσ).2

end NK.TameStructureDeep.Tame

import Mathlib
import Submission.Work.Tower.CyclotomicBase.Defs
import Submission.Work.Tower.CyclotomicBase.Basic
import Submission.Work.Tower.CyclotomicBase.inertia_eq_inertiaSub
import Submission.Work.Tower.CyclotomicBase.inertia_le_fixingSubgroup_of_ramificationIdxIn_eq_one
import Submission.Work.Tower.CyclotomicBase.exists_unitsMap_eq_one_and

/-!
# The rational prime `rᵢ` ramifies in `F` (paper Proposition 3.2)

The field `F = Ffield r hr hr3 ⊆ ℚ(ζ_D)` is cut out by the product character `χ₁⋯χ_ℓ`, i.e. it is
the fixed field of `(sumHom ℓ).comp (galMap r hr hr3)`.  We show that the rational prime `rᵢ`
(which divides the conductor `D` of `F` through every character factor) has ramification index
`≠ 1` in `F`, i.e. ramifies.

The argument is a direct computation with the inertia group of `rᵢ` inside `ℚ(ζ_D)`:

* If `e(rᵢ) = 1` in `F`, then by `inertia_le_fixingSubgroup_of_ramificationIdxIn_eq_one` the
  inertia subgroup of any prime `P` of `ℚ(ζ_D)` over `rᵢ` is contained in the fixing subgroup of
  `F`, which is the kernel of `(sumHom ℓ).comp (galMap r hr hr3)`.
* By `inertia_eq_inertiaSub` this inertia subgroup is `(inertiaSub r i).comap (galEquiv r)`, i.e.
  the units of `(ℤ/D)ˣ` that are `1` modulo `D / rᵢ`.
* But by the Chinese remainder theorem there is such a unit `u` whose `i`-th coordinate is an
  arbitrary unit `v` of `(ℤ/rᵢ)ˣ` — in particular one with `χᵢ(v) ≠ 1`.  For this `u` the product
  character takes the value `χᵢ(v) ≠ 1`, contradicting membership in the kernel.
-/

set_option linter.style.haveILetI false

open NumberField
open scoped Classical nonZeroDivisors

namespace Work.Tower.CyclotomicBase

theorem ramificationIdxIn_Ffield_ne_one {ℓ : ℕ} (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i))
    (hr3 : ∀ i, r i % 3 = 1) (hrinj : Function.Injective r) [NeZero (D r)] (i : Fin ℓ) :
    (Ideal.span {(r i : ℤ)}).ramificationIdxIn (NumberField.RingOfIntegers ↥(Ffield r hr hr3)) ≠ 1 := by
  intro hram
  haveI : Fact (Nat.Prime (r i)) := ⟨hr i⟩
  haveI hcyc : IsCyclotomicExtension {D r} ℚ (Cyc r) := isCyclotomicExtension_cyc r
  haveI hgal : IsGalois ℚ (Cyc r) := IsCyclotomicExtension.isGalois {D r} ℚ (Cyc r)
  haveI hgalF : IsGalois ℚ ↥(Ffield r hr hr3) := isGalois_Ffield r hr hr3
  -- a prime `P` of `𝓞 ℚ(ζ_D)` lying over the rational prime `rᵢ`
  obtain ⟨P⟩ := (inferInstance : Nonempty ((Ideal.span {(r i : ℤ)}).primesOver (𝓞 (Cyc r))))
  -- `e(rᵢ) = 1` would force the inertia group into the fixing subgroup of `F`
  have hle : Ideal.inertia Gal(Cyc r/ℚ) P.1 ≤ (Ffield r hr hr3).fixingSubgroup :=
    inertia_le_fixingSubgroup_of_ramificationIdxIn_eq_one (K := Cyc r) (Ffield r hr hr3) (r i) P.1
      (Ideal.under (𝓞 ↥(Ffield r hr hr3)) P.1) hram
  have hfix : (Ffield r hr hr3).fixingSubgroup = ((sumHom ℓ).comp (galMap r hr hr3)).ker :=
    IntermediateField.fixingSubgroup_fixedField _
  rw [inertia_eq_inertiaSub r hr hrinj i P.1, hfix] at hle
  -- a unit `v` mod `rᵢ` with nontrivial cubic character
  obtain ⟨v, hv⟩ := cubeChar_surjective (r i) (hr i) (hr3 i) (Multiplicative.ofAdd 1)
  have ha : Multiplicative.ofAdd (1 : ZMod 3) ≠ 1 := by decide
  -- Chinese remainder theorem: a unit `u` mod `D` congruent to `1` mod `D / rᵢ` and to `v` mod `rᵢ`
  haveI hmz' : NeZero (r i) := ⟨(hr i).pos.ne'⟩
  have hcop : (D r / r i).Coprime (r i) :=
    ((hr i).coprime_iff_not_dvd.mpr (not_dvd_div_D r hr hrinj i)).symm
  obtain ⟨x, hxA, hxB⟩ := Nat.chineseRemainder hcop 1 (v : ZMod (r i)).val
  have hbv : (((v : ZMod (r i)).val : ℕ) : ZMod (r i)) = (v : ZMod (r i)) := ZMod.natCast_zmod_val _
  have hbcop : ((v : ZMod (r i)).val).Coprime (r i) := ZMod.val_coe_unit_coprime v
  have hcopA : x.Coprime (D r / r i) := by
    rw [Nat.coprime_iff_gcd_eq_one, Nat.ModEq.gcd_eq hxA, Nat.gcd_one_left]
  have hcopB : x.Coprime (r i) := by
    rw [Nat.coprime_iff_gcd_eq_one, Nat.ModEq.gcd_eq hxB]
    exact Nat.coprime_iff_gcd_eq_one.mp hbcop
  have hcopD : x.Coprime (D r) := by
    rw [D_eq_mul_div r i]
    exact hcopB.mul_right hcopA
  obtain ⟨u, huA, huB⟩ : ∃ u : (ZMod (D r))ˣ,
      ZMod.unitsMap (div_r_dvd_D r i) u = 1 ∧ ZMod.unitsMap (r_dvd_D r i) u = v := by
    refine ⟨ZMod.unitOfCoprime x hcopD, ?_, ?_⟩
    · apply Units.ext
      rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, Units.val_one,
        ZMod.cast_natCast (div_r_dvd_D r i) x, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
      exact hxA
    · apply Units.ext
      rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.cast_natCast (r_dvd_D r i) x, ← hbv,
        ZMod.natCast_eq_natCast_iff]
      exact hxB
  -- the Galois element `σ` corresponding to `u` lies in the inertia subgroup
  obtain ⟨σ, hσeq⟩ := (galEquiv r).surjective u
  have hgalu : (galEquiv r).toMonoidHom σ = u := hσeq
  have hσmem : σ ∈ (inertiaSub r i).comap (galEquiv r).toMonoidHom := by
    rw [Subgroup.mem_comap, inertiaSub, MonoidHom.mem_ker, hgalu]
    exact huA
  have hσker := hle hσmem
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hσker
  -- yet the product character is nontrivial on `σ`: it equals `χᵢ(v) ≠ 1`
  have hgalMap : galMap r hr hr3 σ = piChar r hr hr3 u := by
    show (piChar r hr hr3).comp (galEquiv r).toMonoidHom σ = piChar r hr hr3 u
    rw [MonoidHom.comp_apply, hgalu]
  have hcomp : sumHom ℓ (galMap r hr hr3 σ) = Multiplicative.ofAdd 1 := by
    rw [hgalMap, sumHom_apply, Finset.prod_eq_single i]
    · rw [piChar_apply]
      simp only [coordChar, MonoidHom.comp_apply]
      rw [huB]
      exact hv
    · intro j _ hji
      rw [piChar_apply]
      simp only [coordChar, MonoidHom.comp_apply]
      rw [← ZMod.unitsMap_comp (r_dvd_div_D r hr hrinj hji) (div_r_dvd_D r i),
        MonoidHom.comp_apply, huA]
      simp
    · simp
  rw [hcomp] at hσker
  exact ha hσker

end Work.Tower.CyclotomicBase

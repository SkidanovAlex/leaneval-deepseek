/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area ZASS2: step Z6.0, the coordinate bijection `Θ : X ≃ Option E`

`Work.GW2.ZassCoordProp` (stated in `Submission/Work/ZASS/Leaf9.lean`) repackages the proved
Z5 coordinate step `Work.ZASS.exists_coordinate_equiv` into the `Option E` form `ZassCoords`.

Everything of substance is in `Work.ZASS.exists_coordinate_equiv`: a field `E` with `|E| = p^k`,
a multiplicative equivalence `Φ' : U ≃* Multiplicative E`, a monoid homomorphism
`φ : G_{∞0} →* Eˣ` whose range is the squares, and a bijection `Φ : X ≃ ℙ¹(E)` carrying `∞` to
`∞` and `0` to `0`, under which `U` acts by translations `x ↦ x + τ u` and `G_{∞0}` by
multiplications `x ↦ a²x`.  Here we only

* transport `ℙ¹(E)` to `Option E` along the affine chart `none ↦ ∞`, `some y ↦ [y : 1]`
  (`ptEquiv`), and
* restate the two equivariance formulas in that chart.
-/
import Mathlib
import Submission.Work.ZASS.Leaf9
import Submission.Work.ZASS.Basic
import Submission.Work.ZASS.Z5
import Submission.Work.ZASS.exists_coordinate_equiv
import Submission.Work.ZASS.psl_smul_ptOf

open scoped MatrixGroups LinearAlgebra.Projectivization

namespace Work.ZASS2

open Work.GW2
open Work.Zassenhaus (borel pairStab)

/-- The affine chart `Option E → ℙ¹(E)`: `none ↦ ∞`, `some y ↦ [y : 1]`. -/
noncomputable def ptOfOption (E : Type) [Field E] : Option E → Projectivization E (Fin 2 → E)
  | none => Work.PSL2.ptInf E
  | some y => Work.PSL2.ptOf E y

@[simp] theorem ptOfOption_none (E : Type) [Field E] :
    ptOfOption E none = Work.PSL2.ptInf E := rfl

@[simp] theorem ptOfOption_some (E : Type) [Field E] (y : E) :
    ptOfOption E (some y) = Work.PSL2.ptOf E y := rfl

theorem ptOfOption_injective (E : Type) [Field E] : Function.Injective (ptOfOption E) := by
  intro a b hab
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some y =>
          rw [ptOfOption_none, ptOfOption_some] at hab
          exact absurd hab (Ne.symm (Work.ZASS.ptOf_ne_ptInf E y))
  | some x =>
      cases b with
      | none =>
          rw [ptOfOption_none, ptOfOption_some] at hab
          exact absurd hab (Work.ZASS.ptOf_ne_ptInf E x)
      | some y =>
          rw [ptOfOption_some, ptOfOption_some] at hab
          exact congrArg some (Work.ZASS.ptOf_injective E hab)

/-- The affine chart as a bijection `Option E ≃ ℙ¹(E)`: both sides have `|E| + 1` elements. -/
noncomputable def ptEquiv (E : Type) [Field E] [Fintype E] :
    Option E ≃ Projectivization E (Fin 2 → E) :=
  Equiv.ofBijective (ptOfOption E) (by
    haveI : Fintype (Projectivization E (Fin 2 → E)) := Fintype.ofFinite _
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨ptOfOption_injective E, ?_⟩
    rw [Fintype.card_option,
      ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    have hfinrank : Module.finrank E (Fin 2 → E) = 2 := Module.finrank_fin_fun (R := E)
    rw [Projectivization.card_of_finrank (k := E) (V := Fin 2 → E) hfinrank]
    simp)

@[simp] theorem ptEquiv_none (E : Type) [Field E] [Fintype E] :
    ptEquiv E none = Work.PSL2.ptInf E := rfl

@[simp] theorem ptEquiv_some (E : Type) [Field E] [Fintype E] (y : E) :
    ptEquiv E (some y) = Work.PSL2.ptOf E y := rfl

/-- The affine chart intertwines `Option.map (· + b)` with the translation
`Work.PSL2.pslUnipotent E b`. -/
theorem ptEquiv_map_add (E : Type) [Field E] [Fintype E] (b : E) (y : Option E) :
    ptEquiv E (y.map (· + b)) = Work.PSL2.pslUnipotent E b • ptEquiv E y := by
  cases y with
  | none =>
      show Work.PSL2.ptInf E = Work.PSL2.pslUnipotent E b • Work.PSL2.ptInf E
      exact (Work.ZASS.pslUnipotent_smul_ptInf E b).symm
  | some t =>
      show Work.PSL2.ptOf E (t + b) = Work.PSL2.pslUnipotent E b • Work.PSL2.ptOf E t
      exact (Work.ZASS.psl_smul_ptOf_unipotent E b t).symm

/-- The affine chart intertwines `Option.map (fun t => a^2 * t)` with the dilation
`Work.PSL2.pslDiag E a`. -/
theorem ptEquiv_map_mul (E : Type) [Field E] [Fintype E] (a : Eˣ) (y : Option E) :
    ptEquiv E (y.map (fun t => (a : E) ^ 2 * t)) = Work.PSL2.pslDiag E a • ptEquiv E y := by
  cases y with
  | none =>
      show Work.PSL2.ptInf E = Work.PSL2.pslDiag E a • Work.PSL2.ptInf E
      exact (Work.ZASS.pslDiag_smul_ptInf E a).symm
  | some t =>
      show Work.PSL2.ptOf E ((a : E) ^ 2 * t) = Work.PSL2.pslDiag E a • Work.PSL2.ptOf E t
      exact (Work.ZASS.psl_smul_ptOf_diag E a t).symm

/-- **Step Z6.0.**  From the Z2–Z5 structure and the cyclicity of `G_{∞0}` one gets field
coordinates `Θ : X ≃ Option E`. -/
theorem zassCoord : Work.GW2.ZassCoordProp := by
  intro G X _ _ _ _ p k _ hp hq h inf zero hne hcyc
  obtain ⟨U, hUB, hcardU, hN, hdec, hfree, _hequiv, hcomm, hexp⟩ :=
    Work.ZASS.exists_unipotent_structure (p := p) (k := k) hp hq h (inf := inf) (zero := zero) hne
  have hcardH : Nat.card (pairStab G inf zero) = (p ^ k - 1) / 2 :=
    Work.ZASS.card_pairStab h hne
  have hUData : ZassUData G X p k inf zero U :=
    ⟨hUB, hcardU, hN, hdec, hfree, hcomm, hexp⟩
  refine ⟨U, hUData, ?_⟩
  obtain ⟨E, hE, hEF, _hEc, Φ', φ, Φ, _hcardE, _hφinj, hφrange, hΦinf, hΦzero, hΦU, hΦH⟩ :=
    Work.ZASS.exists_coordinate_equiv hp hq h hne hUB hcardU hcardH hN hcyc hfree
  letI : Field E := hE
  letI : Fintype E := hEF
  let τ : U → E := fun u => Multiplicative.toAdd (Φ' u)
  let α : pairStab G inf zero → E := fun hh => ((φ hh : Eˣ) : E)
  let Θ : X ≃ Option E := Φ.trans (ptEquiv E).symm
  have hτbij : Function.Bijective τ := by
    have h1 : Function.Bijective (fun u : U => (Φ' u : Multiplicative E)) := Φ'.bijective
    have h2 : Function.Bijective (Multiplicative.toAdd (α := E)) :=
      (Multiplicative.toAdd (α := E)).bijective
    exact h2.comp h1
  refine ⟨E, Θ, ?_, ?_, τ, hτbij, ?_, α, ?_, ?_⟩
  · rw [show Θ inf = (ptEquiv E).symm (Φ inf) from rfl, hΦinf]
    exact (Equiv.symm_apply_eq (ptEquiv E)).mpr (ptEquiv_none E).symm
  · rw [show Θ zero = (ptEquiv E).symm (Φ zero) from rfl, hΦzero]
    exact (Equiv.symm_apply_eq (ptEquiv E)).mpr (ptEquiv_some E 0).symm
  · intro u x
    have h1 := hΦU u x
    show (ptEquiv E).symm (Φ ((u : G) • x)) =
      Option.map (fun t => t + τ u) ((ptEquiv E).symm (Φ x))
    rw [h1, Equiv.symm_apply_eq]
    rw [ptEquiv_map_add E (τ u) ((ptEquiv E).symm (Φ x)), Equiv.apply_symm_apply]
  · intro hh x
    obtain ⟨a, ha, hact⟩ := hΦH hh hh.2
    have hα : α hh = (a : E) ^ 2 := by
      show ((φ hh : Eˣ) : E) = (a : E) ^ 2
      rw [ha, Units.val_pow_eq_pow_val]
    show (ptEquiv E).symm (Φ ((hh : G) • x)) =
      Option.map (fun t => α hh * t) ((ptEquiv E).symm (Φ x))
    rw [hact x, hα, Equiv.symm_apply_eq]
    rw [ptEquiv_map_mul E a ((ptEquiv E).symm (Φ x)), Equiv.apply_symm_apply]
  · intro e he
    constructor
    · rintro ⟨hh, hhα⟩
      obtain ⟨f, hf⟩ := (hφrange (φ hh)).mp ⟨hh, rfl⟩
      refine ⟨(f : E), ?_⟩
      rw [← hhα]
      show ((φ hh : Eˣ) : E) = (f : E) * (f : E)
      rw [← hf, Units.val_pow_eq_pow_val, pow_two]
    · rintro ⟨r, hr⟩
      have hr0 : r ≠ 0 := fun h0 => he (by rw [hr, h0, mul_zero])
      let ru : Eˣ := Units.mk0 r hr0
      have hru : (ru : E) = r := rfl
      obtain ⟨hh, hhh⟩ := (hφrange (ru ^ 2)).mpr ⟨ru, rfl⟩
      refine ⟨hh, ?_⟩
      show ((φ hh : Eˣ) : E) = e
      rw [hhh, Units.val_pow_eq_pow_val, hru, pow_two]
      exact hr.symm

end Work.ZASS2

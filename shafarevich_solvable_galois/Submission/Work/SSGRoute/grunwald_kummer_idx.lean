import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.Kummer.kummerCharacter_eq_iff_div_mem
import Submission.Work.SSGRoute.zmod_roots_of_unity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Kummer index of an automorphism at a `p`-th root

For a field extension `F ⊆ E` (with `algebraMap F E` injective), a primitive `p`-th root of unity
`ζ ∈ F`, a unit `c ∈ Fˣ` and a unit `γ ∈ Eˣ` with `γ ^ p = Units.map (algebraMap F E) c`, the
*Kummer index* of `σ : E ≃ₐ[F] E` at `(c, γ)` is the exponent `i : ZMod p` with

`σ γ = ζ ^ i · γ`.

It is defined through the isomorphism `Work.SSGRoute.zr : Multiplicative (ZMod p) ≃* μ_p(E)` of
`zmod_roots_of_unity.lean` applied to the Kummer ratio `σ γ / γ` (`Work.Kummer.kummerRatio`), so
that all the algebraic properties of the ratio (`Work.Kummer.kummerRatio_mul`,
`kummerRatio_congr`, `kummerRatio_mul_apply`, `kummerRatio_unitsMap`) transfer directly.

## Main results

* `Work.SSGRoute.kummerIdx` — the index, with `kummerIdx_spec` the defining property;
* `kummerIdx_mul_apply`, `kummerIdx_one`, `kummerIdx_eq_zero_of_apply_eq` — additivity in `σ`;
* `kummerIdx_congr` — independence of the chosen `p`-th root;
* `kummerIdx_mul` — multiplicativity in `(c, γ)`;
* `kummerIdx_eq_zero_of_mem_pow`, `kummerIdx_eq_of_mul_pow` — triviality on `p`-th powers, and
  invariance under multiplying the class by a `p`-th power;
* `zr_map_eq`, `zr_comp` — naturality of `zr` under `F`-algebra maps and ring homomorphisms.
-/

namespace Work.SSGRoute

open scoped Classical

universe u v

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]

/-- The image of the chosen primitive `p`-th root of unity of `F` in the units of `E`. -/
noncomputable def mappedRoot (p : ℕ) [Fact p.Prime] {ζ : F} (hζ : IsPrimitiveRoot ζ p) : Eˣ :=
  Units.map (algebraMap F E) (Work.Kummer.primRootUnit hζ)

lemma isPrimitiveRoot_primRootUnit (p : ℕ) [Fact p.Prime] {ζ : F} (hζ : IsPrimitiveRoot ζ p) :
    IsPrimitiveRoot (Work.Kummer.primRootUnit hζ) p := by
  rw [← IsPrimitiveRoot.coe_units_iff, Work.Kummer.primRootUnit_coe]
  exact hζ

lemma isPrimitiveRoot_mappedRoot (p : ℕ) [Fact p.Prime] {ζ : F} (hζ : IsPrimitiveRoot ζ p) :
    IsPrimitiveRoot (mappedRoot (E := E) p hζ) p := by
  rw [← IsPrimitiveRoot.coe_units_iff]
  have h : IsPrimitiveRoot ((algebraMap F E) ζ) p :=
    hζ.map_of_injective ((algebraMap F E).injective)
  simpa [mappedRoot, Units.coe_map, Work.Kummer.primRootUnit_coe] using h

/-- The valuation form of the hypothesis `γ ^ p = Units.map (algebraMap F E) c`. -/
lemma val_pow_of_units_eq {p : ℕ} {γ : Eˣ} {c : Fˣ}
    (h : γ ^ p = Units.map (algebraMap F E) c) :
    (γ : E) ^ p = algebraMap F E (c : F) := by
  have := congrArg (fun u : Eˣ => (u : E)) h
  simpa [Units.val_pow_eq_pow_val, Units.coe_map] using this

/-- **The Kummer index** of `σ : E ≃ₐ[F] E` at a unit `γ` with `γ ^ p = Units.map (algebraMap F E) c`:
the exponent `i : ZMod p` with `σ γ = ζ ^ i γ`, encoded through `zr` and the Kummer ratio
`σ γ / γ`. -/
noncomputable def kummerIdx (p : ℕ) [Fact p.Prime] {ζ : F} (hζ : IsPrimitiveRoot ζ p) (c : Fˣ)
    (γ : Eˣ) (h : γ ^ p = Units.map (algebraMap F E) c) (σ : E ≃ₐ[F] E) : ZMod p :=
  Multiplicative.toAdd ((zr (isPrimitiveRoot_mappedRoot (E := E) p hζ)).symm
    ⟨Work.Kummer.kummerRatio σ γ,
      Work.Kummer.kummerRatio_mem_rootsOfUnity hζ (val_pow_of_units_eq h) σ⟩)

/-- **The defining property of the Kummer index**: the Kummer ratio `σ γ / γ` is the `zr`-image of
the index. -/
lemma kummerIdx_spec (p : ℕ) [Fact p.Prime] {ζ : F} (hζ : IsPrimitiveRoot ζ p) (c : Fˣ)
    (γ : Eˣ) (h : γ ^ p = Units.map (algebraMap F E) c) (σ : E ≃ₐ[F] E) :
    Work.Kummer.kummerRatio σ γ =
      (((zr (isPrimitiveRoot_mappedRoot (E := E) p hζ)
          (Multiplicative.ofAdd (kummerIdx p hζ c γ h σ)) : ↥(rootsOfUnity p E)) : Eˣ)) := by
  rw [kummerIdx, ofAdd_toAdd]
  have hspec := MulEquiv.apply_symm_apply (zr (isPrimitiveRoot_mappedRoot (E := E) p hζ))
    (⟨Work.Kummer.kummerRatio σ γ,
      Work.Kummer.kummerRatio_mem_rootsOfUnity hζ (val_pow_of_units_eq h) σ⟩ :
        ↥(rootsOfUnity p E))
  exact (congrArg (fun x : ↥(rootsOfUnity p E) => (x : Eˣ)) hspec).symm

/-- The common form of the two "the Kummer ratio is `1`" conclusions: a vanishing index. -/
private lemma kummerIdx_eq_zero_of_ratio_eq_one (p : ℕ) [Fact p.Prime] {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) (c : Fˣ) (γ : Eˣ) (h : γ ^ p = Units.map (algebraMap F E) c)
    (σ : E ≃ₐ[F] E) (hratio : Work.Kummer.kummerRatio σ γ = 1) :
    kummerIdx p hζ c γ h σ = 0 := by
  have h1 := kummerIdx_spec p hζ c γ h σ
  rw [hratio] at h1
  have h2 : zr (isPrimitiveRoot_mappedRoot (E := E) p hζ)
      (Multiplicative.ofAdd (kummerIdx p hζ c γ h σ)) = 1 := by
    apply Subtype.ext
    simpa using h1.symm
  have h3 : Multiplicative.ofAdd (kummerIdx p hζ c γ h σ) = 1 := by
    apply (zr (isPrimitiveRoot_mappedRoot (E := E) p hζ)).injective
    rw [h2, map_one]
  simpa using congrArg Multiplicative.toAdd h3

/-- **Additivity of the Kummer index in the automorphism.** -/
lemma kummerIdx_mul_apply (p : ℕ) [Fact p.Prime] {ζ : F} (hζ : IsPrimitiveRoot ζ p) (c : Fˣ)
    (γ : Eˣ) (h : γ ^ p = Units.map (algebraMap F E) c) (σ τ : E ≃ₐ[F] E) :
    kummerIdx p hζ c γ h (σ * τ) = kummerIdx p hζ c γ h σ + kummerIdx p hζ c γ h τ := by
  have hratio := Work.Kummer.kummerRatio_mul hζ (a := c) (val_pow_of_units_eq h) σ τ
  have h1 := kummerIdx_spec p hζ c γ h (σ * τ)
  have h2 := kummerIdx_spec p hζ c γ h σ
  have h3 := kummerIdx_spec p hζ c γ h τ
  have hkey : (zr (isPrimitiveRoot_mappedRoot (E := E) p hζ)
        (Multiplicative.ofAdd (kummerIdx p hζ c γ h (σ * τ))) : Eˣ) =
      (zr (isPrimitiveRoot_mappedRoot (E := E) p hζ)
        (Multiplicative.ofAdd (kummerIdx p hζ c γ h σ + kummerIdx p hζ c γ h τ)) : Eˣ) := by
    rw [← h1, hratio, h3, h2, ← Subgroup.coe_mul, ← map_mul]
    congr 1
    rw [← ofAdd_add, add_comm]
  have h2' := (zr (isPrimitiveRoot_mappedRoot (E := E) p hζ)).injective (Subtype.ext hkey)
  simpa using congrArg Multiplicative.toAdd h2'

/-- The Kummer index at the identity automorphism is zero. -/
lemma kummerIdx_one (p : ℕ) [Fact p.Prime] {ζ : F} (hζ : IsPrimitiveRoot ζ p) (c : Fˣ)
    (γ : Eˣ) (h : γ ^ p = Units.map (algebraMap F E) c) :
    kummerIdx p hζ c γ h 1 = 0 :=
  kummerIdx_eq_zero_of_ratio_eq_one p hζ c γ h 1 (Work.Kummer.kummerRatio_one γ)

/-- If `σ` fixes the `p`-th root `γ`, the Kummer index vanishes. -/
lemma kummerIdx_eq_zero_of_apply_eq (p : ℕ) [Fact p.Prime] {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (c : Fˣ) (γ : Eˣ) (h : γ ^ p = Units.map (algebraMap F E) c) (σ : E ≃ₐ[F] E)
    (hσ : (σ : E → E) (γ : E) = γ) :
    kummerIdx p hζ c γ h σ = 0 := by
  refine kummerIdx_eq_zero_of_ratio_eq_one p hζ c γ h σ ?_
  apply Units.ext
  rw [Work.Kummer.kummerRatio_coe, Units.val_one, show (σ : E ≃ₐ[F] E) (γ : E) = γ from hσ,
    div_self (Units.ne_zero γ)]

/-- **The Kummer index only depends on `γ ^ p`.** -/
lemma kummerIdx_congr (p : ℕ) [Fact p.Prime] {ζ : F} (hζ : IsPrimitiveRoot ζ p) (c : Fˣ)
    {γ γ' : Eˣ} (h : γ ^ p = Units.map (algebraMap F E) c)
    (h' : γ' ^ p = Units.map (algebraMap F E) c) (σ : E ≃ₐ[F] E) :
    kummerIdx p hζ c γ h σ = kummerIdx p hζ c γ' h' σ := by
  have hratio := Work.Kummer.kummerRatio_congr hζ (a := c) (val_pow_of_units_eq h)
    (val_pow_of_units_eq h') σ
  have h1 := kummerIdx_spec p hζ c γ h σ
  have h2 := kummerIdx_spec p hζ c γ' h' σ
  have hkey : (zr (isPrimitiveRoot_mappedRoot (E := E) p hζ)
        (Multiplicative.ofAdd (kummerIdx p hζ c γ h σ)) : Eˣ) =
      (zr (isPrimitiveRoot_mappedRoot (E := E) p hζ)
        (Multiplicative.ofAdd (kummerIdx p hζ c γ' h' σ)) : Eˣ) := by
    rw [← h1, ← h2, hratio]
  exact congrArg Multiplicative.toAdd
    ((zr (isPrimitiveRoot_mappedRoot (E := E) p hζ)).injective (Subtype.ext hkey))

/-- **Multiplicativity of the Kummer index in the `p`-th root.** -/
lemma kummerIdx_mul (p : ℕ) [Fact p.Prime] {ζ : F} (hζ : IsPrimitiveRoot ζ p) (c d : Fˣ)
    (γ δ : Eˣ) (h : γ ^ p = Units.map (algebraMap F E) c)
    (h' : δ ^ p = Units.map (algebraMap F E) d)
    (hcd : (γ * δ) ^ p = Units.map (algebraMap F E) (c * d)) (σ : E ≃ₐ[F] E) :
    kummerIdx p hζ (c * d) (γ * δ) hcd σ =
      kummerIdx p hζ c γ h σ + kummerIdx p hζ d δ h' σ := by
  have hratio : Work.Kummer.kummerRatio σ (γ * δ) =
      Work.Kummer.kummerRatio σ γ * Work.Kummer.kummerRatio σ δ :=
    Work.Kummer.kummerRatio_mul_apply σ γ δ
  have h1 := kummerIdx_spec p hζ (c * d) (γ * δ) hcd σ
  have h2 := kummerIdx_spec p hζ c γ h σ
  have h3 := kummerIdx_spec p hζ d δ h' σ
  have hkey : (zr (isPrimitiveRoot_mappedRoot (E := E) p hζ)
        (Multiplicative.ofAdd (kummerIdx p hζ (c * d) (γ * δ) hcd σ)) : Eˣ) =
      (zr (isPrimitiveRoot_mappedRoot (E := E) p hζ)
        (Multiplicative.ofAdd (kummerIdx p hζ c γ h σ + kummerIdx p hζ d δ h' σ)) : Eˣ) := by
    rw [← h1, hratio, h2, h3, ← Subgroup.coe_mul, ← map_mul, ← ofAdd_add]
  have h2' := (zr (isPrimitiveRoot_mappedRoot (E := E) p hζ)).injective (Subtype.ext hkey)
  simpa using congrArg Multiplicative.toAdd h2'

/-- **The Kummer index of a `p`-th power is zero.**  If `c = u ^ p` with `u ∈ Fˣ`, then the index
of a `p`-th root `γ` of `c` vanishes: `γ / (u : E)` is a `p`-th root of unity, hence fixed by `σ`. -/
lemma kummerIdx_eq_zero_of_mem_pow (p : ℕ) [Fact p.Prime] {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (c : Fˣ) (u : Fˣ) (hc : c = u ^ p) (γ : Eˣ)
    (h : γ ^ p = Units.map (algebraMap F E) c) (σ : E ≃ₐ[F] E) :
    kummerIdx p hζ c γ h σ = 0 := by
  set η : Eˣ := γ / Units.map (algebraMap F E) u with hηdef
  have hcval : (c : F) = (u : F) ^ p := by
    rw [congrArg (fun z : Fˣ => (z : F)) hc, Units.val_pow_eq_pow_val]
  have hηpow : (η : E) ^ p = 1 := by
    have hcoe : ((Units.map (algebraMap F E) u : Eˣ) : E) = algebraMap F E (u : F) := rfl
    rw [hηdef, Units.val_div_eq_div_val, div_pow, val_pow_of_units_eq h, hcval, map_pow, hcoe]
    exact div_self (pow_ne_zero _ ((map_ne_zero (algebraMap F E)).mpr (Units.ne_zero u)))
  obtain ⟨i, -, hi⟩ := Work.Kummer.exists_primRootUnit_pow_eq_of_pow_eq_one hζ (u := η) hηpow
  have hfix : Work.Kummer.algEquivUnitsMap σ η = η := by
    rw [hi, Work.Kummer.algEquivUnitsMap_unitsMap]
  have hη1 : Work.Kummer.kummerRatio σ η = 1 := by
    rw [Work.Kummer.kummerRatio, hfix, div_self']
  refine kummerIdx_eq_zero_of_ratio_eq_one p hζ c γ h σ ?_
  have hγ : γ = η * Units.map (algebraMap F E) u := by
    rw [hηdef]; exact (div_mul_cancel γ _).symm
  rw [hγ, Work.Kummer.kummerRatio_mul_apply, hη1,
    Work.Kummer.kummerRatio_unitsMap σ u, mul_one]

/-- **Invariance of the Kummer index under multiplying the class by a `p`-th power.** -/
lemma kummerIdx_eq_of_mul_pow (p : ℕ) [Fact p.Prime] {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (c c' : Fˣ) (u : Fˣ) (hc : c = c' * u ^ p) (γ γ' : Eˣ)
    (h : γ ^ p = Units.map (algebraMap F E) c)
    (h' : γ' ^ p = Units.map (algebraMap F E) c') (σ : E ≃ₐ[F] E) :
    kummerIdx p hζ c γ h σ = kummerIdx p hζ c' γ' h' σ := by
  set δ : Eˣ := Units.map (algebraMap F E) u with hδdef
  set η : Eˣ := γ / (γ' * δ) with hηdef
  have hcval : (c : F) = (c' : F) * (u : F) ^ p := by
    rw [congrArg (fun z : Fˣ => (z : F)) hc, Units.val_mul, Units.val_pow_eq_pow_val]
  have hδcoe : (δ : E) = algebraMap F E (u : F) := rfl
  have hnum : (γ : E) ^ p = algebraMap F E (c : F) := val_pow_of_units_eq h
  have hden : ((γ' * δ : Eˣ) : E) ^ p = algebraMap F E (c : F) := by
    rw [Units.val_mul, mul_pow, val_pow_of_units_eq h', hδcoe, ← map_pow, ← map_mul, ← hcval]
  have hηpow : (η : E) ^ p = 1 := by
    rw [hηdef, Units.val_div_eq_div_val, div_pow, hnum, hden]
    exact div_self ((map_ne_zero (algebraMap F E)).mpr (Units.ne_zero c))
  obtain ⟨i, -, hi⟩ := Work.Kummer.exists_primRootUnit_pow_eq_of_pow_eq_one hζ (u := η) hηpow
  have hfix : Work.Kummer.algEquivUnitsMap σ η = η := by
    rw [hi, Work.Kummer.algEquivUnitsMap_unitsMap]
  have hη1 : Work.Kummer.kummerRatio σ η = 1 := by
    rw [Work.Kummer.kummerRatio, hfix, div_self']
  have hδ1 : Work.Kummer.kummerRatio σ δ = 1 := Work.Kummer.kummerRatio_unitsMap σ u
  have hγ : γ = η * (γ' * δ) := by
    rw [hηdef]; exact (div_mul_cancel γ _).symm
  have hratio : Work.Kummer.kummerRatio σ γ = Work.Kummer.kummerRatio σ γ' := by
    rw [hγ, Work.Kummer.kummerRatio_mul_apply, Work.Kummer.kummerRatio_mul_apply, hη1, hδ1]
    group
  have h1 := kummerIdx_spec p hζ c γ h σ
  have h2 := kummerIdx_spec p hζ c' γ' h' σ
  have hkey : (zr (isPrimitiveRoot_mappedRoot (E := E) p hζ)
        (Multiplicative.ofAdd (kummerIdx p hζ c γ h σ)) : Eˣ) =
      (zr (isPrimitiveRoot_mappedRoot (E := E) p hζ)
        (Multiplicative.ofAdd (kummerIdx p hζ c' γ' h' σ)) : Eˣ) := by
    rw [← h1, ← h2, hratio]
  exact congrArg Multiplicative.toAdd
    ((zr (isPrimitiveRoot_mappedRoot (E := E) p hζ)).injective (Subtype.ext hkey))

/-- **Compatibility of `zr` with the algebra map**: the `zr`-image of an index over `E` is the
image of its `zr`-image over `F`. -/
lemma zr_map_eq (p : ℕ) [Fact p.Prime] {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (k : Multiplicative (ZMod p)) :
    ((zr (isPrimitiveRoot_mappedRoot (E := E) p hζ) k : ↥(rootsOfUnity p E)) : Eˣ) =
      Units.map (algebraMap F E)
        (((zr (isPrimitiveRoot_primRootUnit (F := F) p hζ) k : ↥(rootsOfUnity p F)) : Fˣ)) := by
  have hE := zr_apply_int (isPrimitiveRoot_mappedRoot (E := E) p hζ)
    ((Multiplicative.toAdd k).val : ℤ)
  have hF := zr_apply_int (isPrimitiveRoot_primRootUnit (F := F) p hζ)
    ((Multiplicative.toAdd k).val : ℤ)
  rw [show (Multiplicative.ofAdd (((Multiplicative.toAdd k).val : ℤ) : ZMod p)) = k from by
    ext; simp] at hE hF
  rw [hE, hF]
  apply Units.ext
  simp only [Units.val_zpow_eq_zpow_val, Units.coe_map, map_zpow]
  congr 1

/-- **Naturality of `zr` under a ring homomorphism.** -/
lemma zr_comp {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] (p : ℕ)
    [Fact p.Prime] (f : R →+* S) (hf : Function.Injective f) (ζ : Rˣ)
    (hζ : IsPrimitiveRoot ζ p) (hζ' : IsPrimitiveRoot (Units.map f.toMonoidHom ζ) p)
    (k : Multiplicative (ZMod p)) :
    ((zr hζ' k : ↥(rootsOfUnity p S)) : Sˣ) =
      Units.map f.toMonoidHom ((zr hζ k : ↥(rootsOfUnity p R)) : Rˣ) := by
  have hS := zr_apply_int hζ' ((Multiplicative.toAdd k).val : ℤ)
  have hR := zr_apply_int hζ ((Multiplicative.toAdd k).val : ℤ)
  rw [show (Multiplicative.ofAdd (((Multiplicative.toAdd k).val : ℤ) : ZMod p)) = k from by
    ext; simp] at hS hR
  rw [hS, hR]
  apply Units.ext
  simp only [Units.val_zpow_eq_zpow_val, Units.coe_map, map_zpow]

/-- The existence of `p`-th roots in an algebraically closed field. -/
lemma exists_pow_eq_of_isAlgClosed {K : Type*} [Field K] [IsAlgClosed K] (p : ℕ) (hp : p ≠ 0)
    (c : K) : ∃ x : K, x ^ p = c := by
  have hnpos : 0 < p := Nat.pos_of_ne_zero hp
  have hdeg : (Polynomial.X ^ p - Polynomial.C c : Polynomial K).degree ≠ 0 := by
    rw [Polynomial.degree_X_pow_sub_C hnpos]
    simp [hp]
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root
    (Polynomial.X ^ p - Polynomial.C c : Polynomial K) hdeg
  refine ⟨x, ?_⟩
  rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, sub_eq_zero] at hx
  exact hx

end Work.SSGRoute

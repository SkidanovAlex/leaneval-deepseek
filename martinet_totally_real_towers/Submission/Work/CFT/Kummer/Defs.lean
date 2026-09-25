import Mathlib
import Submission.Work.Tower.Shafarevich.Defs

/-!
# Kummer theory over number fields: vocabulary

This file fixes the vocabulary for the area `Work.CFT.Kummer`, the Kummer / Poitou–Tate
formalisation of **Shafarevich's relation-rank estimate** for the Galois group of the maximal
pro-`p` extension of a number field unramified outside a finite set `S` of finite places
(D. Hajir, C. Maire, R. Ramakrishna, *Cutting towers of number fields*, arXiv:1901.04354,
§"Some set up"; H. Koch, *Galois theory of p-extensions*, Chapter 11).

The objects are the ones used there:

* `V_S`, the group of `x ∈ Kˣ` whose generated ideal is a `p`-th power of a fractional ideal and
  which are `p`-th powers in every completion `K_v`, `v ∈ S` (`selmerGroupAt`);
* `𝓒_S`, the "Kummer character group" `Hom(V_S/K^{×p}, 𝔽_p)` (`kummerDual`);
* the `p`-torsion of the class group `Cl_K[p]` (`classGroupTorsion`) and the `𝔽_p`-space
  `𝒪_Kˣ/(𝒪_Kˣ)^p` (`unitsModPow`), which compute `dim V_∅/K^{×p}` by Dirichlet's unit theorem
  and the finiteness of the class number;
* `δ_{F,p} = 1` if `F` contains a primitive `p`-th root of unity, `0` otherwise (`deltaK`,
  `deltaLocal`).

The cohomological invariants `H¹(G, 𝔽_p)`, `H²(G, 𝔽_p)` are the ones of
`Work.Tower.Shafarevich` (with trivial coefficients), so that the estimates proved here are
directly comparable with Shafarevich's estimate as used by the Golod–Shafarevich tower.

## Main definitions

* `Work.CFT.Kummer.pthPowerSubgroup F p` — the subgroup of `p`-th powers of a commutative group.
* `Work.CFT.Kummer.KummerGroup F p` — `Fˣ/Fˣ^p`.
* `Work.CFT.Kummer.deltaK K p`, `Work.CFT.Kummer.deltaLocal K p v` — `δ_{K,p}`, `δ_{K_v,p}`.
* `Work.CFT.Kummer.selmerGroup K p` — `V_∅`.
* `Work.CFT.Kummer.selmerGroupAt K p S` — `V_S`.
* `Work.CFT.Kummer.kummerClasses K p S` — `V_S/K^{×p}` as an `𝔽_p`-vector space.
* `Work.CFT.Kummer.kummerDual K p S` — `𝓒_S = Hom(V_S/K^{×p}, 𝔽_p)`.
* `Work.CFT.Kummer.classGroupTorsion K p` — `Cl_K[p]`.
* `Work.CFT.Kummer.unitsModPow K p` — `𝒪_Kˣ/(𝒪_Kˣ)^p`.

## Implementation notes

The `𝔽_p`-vector-space structures on the various elementary abelian `p`-groups are installed with
`AddCommGroup.zmodModule` from the fact that every element has order dividing `p`; the helpers
`quotient_pow_eq_one` and `moduleQuotientPowSubgroup` do this once and for all for quotients of a
commutative group by a subgroup containing all `p`-th powers.
-/

open scoped nonZeroDivisors
open NumberField

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Work.CFT.Kummer

/-! ## `p`-th powers and the Kummer group of a field -/

/-- The subgroup of `p`-th powers of a commutative group `F`. -/
def pthPowerSubgroup (F : Type*) [CommGroup F] (p : ℕ) : Subgroup F := (powMonoidHom p).range

theorem mem_pthPowerSubgroup {F : Type*} [CommGroup F] {p : ℕ} {x : F} :
    x ∈ pthPowerSubgroup F p ↔ ∃ y : F, y ^ p = x :=
  MonoidHom.mem_range

/-- In a quotient `G ⧸ H` of a commutative group by a subgroup `H` containing all `p`-th powers,
every element has order dividing `p`. -/
theorem quotient_pow_eq_one {G : Type*} [CommGroup G] {H : Subgroup G} {p : ℕ}
    (hH : ∀ x : G, x ^ p ∈ H) (q : G ⧸ H) : q ^ p = 1 := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective H q
  rw [← map_pow (QuotientGroup.mk' H) u p, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hH u

/-- The `𝔽_p`-vector space structure on a quotient `G ⧸ H` of a commutative group by a subgroup
containing all `p`-th powers. -/
abbrev moduleQuotientPowSubgroup {G : Type*} [CommGroup G] (H : Subgroup G) (p : ℕ)
    (hH : ∀ x : G, x ^ p ∈ H) : Module (ZMod p) (Additive (G ⧸ H)) :=
  AddCommGroup.zmodModule (fun x => by
    have h : x.toMul ^ p = 1 := quotient_pow_eq_one hH x.toMul
    have : Additive.ofMul (x.toMul ^ p) = (0 : Additive (G ⧸ H)) := by rw [h]; rfl
    simpa using this)

/-- `Fˣ ⧸ (Fˣ)^p`: the **Kummer group** of a field `F`.  It is an elementary abelian `p`-group,
hence (via `Work.CFT.Kummer.instModuleKummerGroup`) an `𝔽_p`-vector space. -/
abbrev KummerGroup (F : Type*) [Field F] (p : ℕ) : Type _ := Fˣ ⧸ pthPowerSubgroup Fˣ p

/-- Every element of the Kummer group `Fˣ/Fˣ^p` has order dividing `p`. -/
theorem kummerGroup_pow_eq_one (F : Type*) [Field F] (p : ℕ) (q : KummerGroup F p) :
    q ^ p = 1 :=
  quotient_pow_eq_one (fun x : Fˣ => mem_pthPowerSubgroup.mpr ⟨x, rfl⟩) q

/-- The `𝔽_p`-vector space structure on the Kummer group `Fˣ/Fˣ^p`. -/
instance instModuleKummerGroup (F : Type*) [Field F] (p : ℕ) :
    Module (ZMod p) (Additive (KummerGroup F p)) :=
  moduleQuotientPowSubgroup (pthPowerSubgroup Fˣ p) p
    (fun x => mem_pthPowerSubgroup.mpr ⟨x, rfl⟩)

/-- A class in `Fˣ/Fˣ^p` is trivial iff it is represented by a `p`-th power. -/
theorem kummerGroup_mk_eq_one_iff {F : Type*} [Field F] {p : ℕ} (u : Fˣ) :
    (QuotientGroup.mk u : KummerGroup F p) = 1 ↔ u ∈ pthPowerSubgroup Fˣ p :=
  QuotientGroup.eq_one_iff u

/-! ## The local and global root-of-unity indicators -/

/-- `δ_{K,p} = 1` if the number field `K` contains a primitive `p`-th root of unity, and `0`
otherwise (Hajir–Maire–Ramakrishna, §"Some set up"). -/
def deltaK (K : Type*) [Field K] [NumberField K] (p : ℕ) : ℕ :=
  if ∃ ζ : Kˣ, IsPrimitiveRoot ζ p then 1 else 0

theorem deltaK_eq_one_iff (K : Type*) [Field K] [NumberField K] (p : ℕ) :
    deltaK K p = 1 ↔ ∃ ζ : Kˣ, IsPrimitiveRoot ζ p := by
  unfold deltaK
  split <;> simp_all

theorem deltaK_eq_zero_iff (K : Type*) [Field K] [NumberField K] (p : ℕ) :
    deltaK K p = 0 ↔ ¬ ∃ ζ : Kˣ, IsPrimitiveRoot ζ p := by
  unfold deltaK
  split <;> simp_all

/-- `δ_{K_v,p} = 1` if the completion `K_v` at the finite place `v` contains a primitive `p`-th
root of unity, `0` otherwise. -/
def deltaLocal (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℕ :=
  if ∃ ζ : (v.adicCompletion K)ˣ, IsPrimitiveRoot ζ p then 1 else 0

theorem deltaLocal_eq_one_iff (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    deltaLocal K p v = 1 ↔ ∃ ζ : (v.adicCompletion K)ˣ, IsPrimitiveRoot ζ p := by
  unfold deltaLocal
  split <;> simp_all

theorem deltaK_le_one (K : Type*) [Field K] [NumberField K] (p : ℕ) : deltaK K p ≤ 1 := by
  unfold deltaK
  split <;> simp

theorem deltaLocal_le_one (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : deltaLocal K p v ≤ 1 := by
  unfold deltaLocal
  split <;> simp

/-- The finite place `v` of `K` lies **above** `p` (i.e. `p ∈ v`). -/
def IsAboveP (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : Prop :=
  (p : 𝓞 K) ∈ v.asIdeal

/-! ## The Selmer groups `V_S` -/

/-- `x : Kˣ` is a **local `p`-th power** at the finite place `v`: `x ∈ K_v^{×p}`. -/
def IsLocalPthPower (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : Kˣ) : Prop :=
  ∃ y : (v.adicCompletion K)ˣ,
    (y : v.adicCompletion K) ^ p = NumberField.FinitePlace.embedding v (x : K)

/-- **`V_∅`**, the group of `x ∈ Kˣ` whose associated fractional ideal is a `p`-th power:
`{x ∈ Kˣ | (x) = 𝔞^p}`.  Equivalently (by unique factorisation of ideals) `v(x) ≡ 0 mod p` for
every finite place `v`. -/
def selmerGroup (K : Type*) [Field K] [NumberField K] (p : ℕ) : Subgroup Kˣ where
  carrier := {x | ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K,
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (x : K) = I ^ p}
  mul_mem' := by
    rintro x y ⟨I, hI⟩ ⟨J, hJ⟩
    refine ⟨I * J, ?_⟩
    rw [mul_pow, ← hI, ← hJ]
    simp only [Units.val_mul]
    exact (FractionalIdeal.spanSingleton_mul_spanSingleton
      (S := nonZeroDivisors (𝓞 K)) (x : K) (y : K)).symm
  one_mem' := by
    refine ⟨1, ?_⟩
    rw [one_pow]
    exact FractionalIdeal.spanSingleton_one (S := nonZeroDivisors (𝓞 K))
  inv_mem' := by
    rintro x ⟨I, hI⟩
    refine ⟨I⁻¹, ?_⟩
    rw [inv_pow, ← hI]
    simp only [Units.val_inv_eq_inv_val]
    exact (FractionalIdeal.spanSingleton_inv K (R₁ := 𝓞 K) (x : K)).symm

theorem mem_selmerGroup (K : Type*) [Field K] [NumberField K] (p : ℕ) {x : Kˣ} :
    x ∈ selmerGroup K p ↔ ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K,
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (x : K) = I ^ p :=
  Iff.rfl

/-- **`V_S`**: the group of `x ∈ Kˣ` which are `p`-th powers in `K_v` for all `v ∈ S` and whose
associated fractional ideal is a `p`-th power. -/
def selmerGroupAt (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) : Subgroup Kˣ where
  carrier := {x | x ∈ selmerGroup K p ∧ ∀ v ∈ S, IsLocalPthPower K p v x}
  mul_mem' := by
    rintro x y ⟨hx, hxS⟩ ⟨hy, hyS⟩
    refine ⟨(selmerGroup K p).mul_mem hx hy, fun v hv => ?_⟩
    obtain ⟨a, ha⟩ := hxS v hv
    obtain ⟨b, hb⟩ := hyS v hv
    exact ⟨a * b, by
      simp only [Units.val_mul, mul_pow, map_mul, ha, hb]⟩
  one_mem' := by
    refine ⟨(selmerGroup K p).one_mem, fun v hv => ?_⟩
    exact ⟨1, by simp⟩
  inv_mem' := by
    rintro x ⟨hx, hxS⟩
    refine ⟨(selmerGroup K p).inv_mem hx, fun v hv => ?_⟩
    obtain ⟨a, ha⟩ := hxS v hv
    refine ⟨a⁻¹, ?_⟩
    have hx : (↑(x⁻¹) : K) = (x : K)⁻¹ := Units.val_inv_eq_inv_val x
    rw [Units.val_inv_eq_inv_val, inv_pow, ha, hx]
    exact (map_inv₀ (NumberField.FinitePlace.embedding v) (x : K)).symm

theorem mem_selmerGroupAt (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) {x : Kˣ} :
    x ∈ selmerGroupAt K p S ↔
      x ∈ selmerGroup K p ∧ ∀ v ∈ S, IsLocalPthPower K p v x :=
  Iff.rfl

theorem selmerGroupAt_le_selmerGroup (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    selmerGroupAt K p S ≤ selmerGroup K p := fun _ hx => hx.1

/-- `p`-th powers of `Kˣ` lie in `V_S`. -/
theorem pthPower_le_selmerGroupAt (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    pthPowerSubgroup Kˣ p ≤ selmerGroupAt K p S := by
  intro x hx
  obtain ⟨y, rfl⟩ := mem_pthPowerSubgroup.mp hx
  refine ⟨⟨FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (y : K), ?_⟩,
    fun v hv => ?_⟩
  · rw [FractionalIdeal.spanSingleton_pow, Units.val_pow_eq_pow_val]
  · refine ⟨Units.mk0 (NumberField.FinitePlace.embedding v (y : K)) (by simp), ?_⟩
    rw [Units.val_mk0, Units.val_pow_eq_pow_val, map_pow]

/-! ## Kummer generators of an extension -/

/-- The group `Lˣ^p ∩ Kˣ` of **Kummer generators** of an extension `L/K`: the elements of `Kˣ`
which become `p`-th powers in `L`.  For `μ_p ⊆ K` and `L/K` abelian of exponent `p`, these are
exactly the `d ∈ Kˣ` with `L = K(ᵖ√d)`; see `Work.CFT.Kummer.kummer_adjoin_eq_top`. -/
abbrev kummerGenerators (K L : Type*) [Field K] [Field L] [Algebra K L] (p : ℕ) : Subgroup Kˣ :=
  (pthPowerSubgroup Lˣ p).comap (Units.map (algebraMap K L).toMonoidHom)

/-- `(Lˣ^p ∩ Kˣ)/Kˣ^p`, the group of **Kummer generator classes** of an extension `L/K`. -/
abbrev kummerGeneratorsQuotient (K L : Type*) [Field K] [Field L] [Algebra K L]
    (p : ℕ) : Type _ :=
  kummerGenerators K L p ⧸ (pthPowerSubgroup Kˣ p).comap (kummerGenerators K L p).subtype

/-! ## The Kummer character group `𝓒_S = Hom(V_S/K^{×p}, 𝔽_p)` -/

/-- `V_S/K^{×p}` — the **Kummer generator group** of `V_S`, as an `𝔽_p`-vector space. -/
abbrev kummerClasses (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) : Type _ :=
  Additive (selmerGroupAt K p S ⧸
    (pthPowerSubgroup Kˣ p).comap (selmerGroupAt K p S).subtype)

instance instAddCommGroupKummerClasses (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    AddCommGroup (kummerClasses K p S) := inferInstance

/-- The `𝔽_p`-vector space structure on `V_S/K^{×p}`. -/
instance instModuleKummerClasses (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    Module (ZMod p) (kummerClasses K p S) :=
  moduleQuotientPowSubgroup
    ((pthPowerSubgroup Kˣ p).comap (selmerGroupAt K p S).subtype) p
    (fun x => ⟨x, rfl⟩)

/-- **The Kummer character group** `𝓒_S = Hom(V_S/K^{×p}, 𝔽_p)`. -/
abbrev kummerDual (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) : Type _ :=
  Module.Dual (ZMod p) (kummerClasses K p S)

/-! ## The class group and the units modulo `p`-th powers -/

/-- The `p`-torsion subgroup `Cl_K[p]` of the class group. -/
def classGroupP (K : Type*) [Field K] [NumberField K] (p : ℕ) :
    Subgroup (ClassGroup (𝓞 K)) where
  carrier := {c | c ^ p = 1}
  mul_mem' := by
    intro a b ha hb
    show (a * b) ^ p = 1
    rw [mul_pow, ha, hb, one_mul]
  one_mem' := by
    show (1 : ClassGroup (𝓞 K)) ^ p = 1
    rw [one_pow]
  inv_mem' := by
    intro a ha
    show (a⁻¹) ^ p = 1
    rw [inv_pow, ha, inv_one]

/-- `Cl_K[p]` as an `𝔽_p`-vector space. -/
abbrev classGroupTorsion (K : Type*) [Field K] [NumberField K] (p : ℕ) : Type _ :=
  Additive (classGroupP K p)

/-- The `𝔽_p`-vector space structure on `Cl_K[p]`. -/
instance instModuleClassGroupTorsion (K : Type*) [Field K] [NumberField K] (p : ℕ) :
    Module (ZMod p) (classGroupTorsion K p) :=
  AddCommGroup.zmodModule (fun x => by
    have h : x.toMul ^ p = 1 := Subtype.ext x.toMul.2
    have : Additive.ofMul (x.toMul ^ p) = (0 : classGroupTorsion K p) := by rw [h]; rfl
    simpa using this)

/-- `𝒪_Kˣ/(𝒪_Kˣ)^p` as an `𝔽_p`-vector space. -/
abbrev unitsModPow (K : Type*) [Field K] [NumberField K] (p : ℕ) : Type _ :=
  Additive ((𝓞 K)ˣ ⧸ pthPowerSubgroup (𝓞 K)ˣ p)

/-- The `𝔽_p`-vector space structure on `𝒪_Kˣ/(𝒪_Kˣ)^p`. -/
instance instModuleUnitsModPow (K : Type*) [Field K] [NumberField K] (p : ℕ) :
    Module (ZMod p) (unitsModPow K p) :=
  moduleQuotientPowSubgroup (pthPowerSubgroup (𝓞 K)ˣ p) p
    (fun x => mem_pthPowerSubgroup.mpr ⟨x, rfl⟩)

end Work.CFT.Kummer

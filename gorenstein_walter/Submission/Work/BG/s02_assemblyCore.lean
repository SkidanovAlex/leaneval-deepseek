import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.sconjLam
import Submission.Work.BG.conjByH_basic

/-!
# Area BG: assembly of the Coherence Theorem 2.3 core from the per-orbit lemma (A-1)

This file proves `Work.BG.s02_assemblyCore`, the design-pass-10 item **A-1** of
`NOTES_BG_s02_leaves.md`:

```
AssemblyCoreProp C  =  SconjLamProp C → OrbitCoherenceProp C → Coherence23CoreProp C.
```

In words: if (i) `s` maps every `Λ`-orbit to a `Λ`-orbit by inverting the character
(`SconjLamProp`, Bender–Glauberman Lemma 2.1(b), proved as `Work.BG.sconjLam`) and (ii) on
every key `orbitKey C ν = Λν ∪ (Λν)^s` there is a *good* map `f` (`GoodOn`, i.e. Theorem
2.3's clauses (i), (ii), (iii), (vi) and `ν̃^s = ν̃` on that key), then there is a **single**
map `f` which is good on every key simultaneously, i.e. the core of Theorem 2.3.

The construction is the one prescribed by the design:

* `gOf E := if h : ∃ f, GoodOn C E f then Classical.choose h else 0` (choice on a key);
* `f ν := gOf (orbitKey C ν) ν`.

The only point to check is that the choice is *coherent* on a key, namely that

  `orbitKey C μ = orbitKey C ν`  for every `μ ∈ orbitKey C ν`

(`s02c_orbitKey_eq_of_mem`), so that `f` agrees with the chosen `gOf (orbitKey C ν)` at every
element of the key.  That reduces to two facts about `Λ`-orbits:

* `Λ`-equivalence is an equivalence relation on `CF(H₀)` (`s02c_LamEquiv_{refl,symm,trans}`),
  which is multiplicativity of `λ ↦ lamCF C λ` (`s02c_lamCF_mul`) plus `lamCF C 1 = 1`
  (`s02c_lamCF_one_mul`);
* `s` maps the orbit `Λν` bijectively onto `Λ(ν^s)` (`s02c_sconj_image_lamOrbit`), which is
  `SconjLamProp` plus `s² = 1` (`s02c_sconj_involutive`).

Nothing else from §2 is used: the file is independent of the remaining leaves of the area.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G]

/-! ## 1. `Λ` is a group of class functions: `LamEquiv` is an equivalence relation -/

/-- Pointwise product of linear class functions corresponds to the product of the
characters: `λ_{χψ} = λ_χ · λ_ψ`. -/
theorem s02c_linearClassFunction_mul {K : Type} [Group K] (χ ψ : K →* ℂˣ) :
    linearClassFunction (χ * ψ) = linearClassFunction χ * linearClassFunction ψ := by
  ext g
  simp only [ClassFunction.mul_apply, linearClassFunction_apply, MonoidHom.mul_apply,
    Units.val_mul]

/-- The pointwise product of class functions is associative.  (`ClassFunction` carries `Mul`
and `AddCommGroup` but no `Semigroup` instance, cf. `CharacterProduct.lean`.) -/
theorem s02c_cf_mul_assoc {K : Type} [Group K] (a b c : ClassFunction K ℂ) :
    a * b * c = a * (b * c) := by
  ext g
  simp only [ClassFunction.mul_apply, mul_assoc]

/-- `λ : β ↦ lamCF C β` is a homomorphism `Λ → CF(H₀)`: `λ_{βγ} = λ_β · λ_γ`. -/
theorem s02c_lamCF_mul (C : Sec2Ctx G) (β γ : quotGroup C.P →* ℂˣ) :
    lamCF C (β * γ) = lamCF C β * lamCF C γ := by
  simp only [lamCF, s02c_linearClassFunction_mul, ClassFunction.compHom_mul]

/-- `λ_1 = 1`, in the form used below: `λ_1 · ν = ν` for every class function `ν`. -/
theorem s02c_lamCF_one_mul (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) :
    lamCF C (1 : quotGroup C.P →* ℂˣ) * ν = ν := by
  ext h
  simp only [ClassFunction.mul_apply, lamCF, ClassFunction.compHom_apply,
    linearClassFunction_apply, MonoidHom.one_apply, Units.val_one, one_mul]

/-- `LamEquiv` is reflexive. -/
theorem s02c_LamEquiv_refl (C : Sec2Ctx G) (μ : ClassFunction ↥C.P.H0 ℂ) : LamEquiv C μ μ :=
  ⟨1, (s02c_lamCF_one_mul C μ).symm⟩

/-- `LamEquiv` is symmetric (invert the character `β`). -/
theorem s02c_LamEquiv_symm (C : Sec2Ctx G) {μ ν : ClassFunction ↥C.P.H0 ℂ}
    (h : LamEquiv C μ ν) : LamEquiv C ν μ := by
  obtain ⟨β, hβ⟩ := h
  refine ⟨β⁻¹, ?_⟩
  rw [hβ, ← s02c_cf_mul_assoc, ← s02c_lamCF_mul,
    show (β⁻¹ * β) = (1 : quotGroup C.P →* ℂˣ) from inv_mul_cancel β, s02c_lamCF_one_mul]

/-- `LamEquiv` is transitive (multiply the characters). -/
theorem s02c_LamEquiv_trans (C : Sec2Ctx G) {μ ν χ : ClassFunction ↥C.P.H0 ℂ}
    (h1 : LamEquiv C μ ν) (h2 : LamEquiv C ν χ) : LamEquiv C μ χ := by
  obtain ⟨β, hβ⟩ := h1
  obtain ⟨γ, hγ⟩ := h2
  refine ⟨γ * β, ?_⟩
  rw [hγ, hβ, s02c_lamCF_mul, s02c_cf_mul_assoc]

/-- `lamOrbit C ν` is the `LamEquiv`-class of `ν`. -/
theorem s02c_lamOrbit_eq_of_lamEquiv (C : Sec2Ctx G) {μ ν : ClassFunction ↥C.P.H0 ℂ}
    (h : LamEquiv C μ ν) : lamOrbit C μ = lamOrbit C ν := by
  ext χ
  exact ⟨fun hχ => s02c_LamEquiv_trans C (s02c_LamEquiv_symm C h) hχ,
    fun hχ => s02c_LamEquiv_trans C h hχ⟩

/-! ## 2. The `s`-conjugation -/

/-- `conjMulEquiv P 1 = id`. -/
theorem s02c_conjMulEquiv_one_apply (P : Hyp12 G) (h : ↥P.H0) :
    conjMulEquiv P (1 : ↥P.H) h = h := by
  apply Subtype.ext
  rw [conjMulEquiv_apply]
  simp

/-- `(·)^1 = id`. -/
theorem s02c_conjByH_one (P : Hyp12 G) (ν : ClassFunction ↥P.H0 ℂ) : conjByH P 1 ν = ν := by
  ext h
  rw [conjByH_apply, s02c_conjMulEquiv_one_apply]

/-- `s` has order two, hence `ν^{s²} = ν`. -/
theorem s02c_sconj_involutive (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) :
    sconj C (sconj C ν) = ν := by
  have h1 : C.s * C.s = (1 : ↥C.P.H) := by
    have := C.s_sq
    simpa [pow_two] using this
  have h2 := conjByH_mul C.P C.s C.s ν
  rw [h1, s02c_conjByH_one] at h2
  exact h2.symm

/-- **`s` maps the `Λ`-orbit of `ν` onto the `Λ`-orbit of `ν^s`**:
`(Λν)^s = Λ(ν^s)`.  This is the orbit form of `SconjLamProp` (BG Lemma 2.1(b)), using that
`β ↦ β⁻¹` is a bijection of the character group and `(ν^s)^s = ν`. -/
theorem s02c_sconj_image_lamOrbit (C : Sec2Ctx G) (hS : SconjLamProp C)
    (ν : ClassFunction ↥C.P.H0 ℂ) :
    sconj C '' lamOrbit C ν = lamOrbit C (sconj C ν) := by
  ext χ
  constructor
  · rintro ⟨ξ, hξ, rfl⟩
    obtain ⟨β, hβ⟩ := hξ
    refine ⟨β⁻¹, ?_⟩
    rw [hβ, hS β ν]
  · intro hχ
    obtain ⟨β, hβ⟩ := hχ
    refine ⟨sconj C χ, ?_, s02c_sconj_involutive C χ⟩
    refine ⟨β⁻¹, ?_⟩
    rw [hβ, hS β (sconj C ν), s02c_sconj_involutive]

/-! ## 3. The keys `orbitKey C ν = Λν ∪ (Λν)^s` -/

/-- Equivalent class functions have the same key. -/
theorem s02c_orbitKey_eq_of_lamEquiv (C : Sec2Ctx G) {μ ν : ClassFunction ↥C.P.H0 ℂ}
    (h : LamEquiv C μ ν) : orbitKey C μ = orbitKey C ν := by
  rw [orbitKey, orbitKey, s02c_lamOrbit_eq_of_lamEquiv C h]

/-- The key is `s`-invariant: `Λ(ν^s) ∪ Λ(ν^{s²}) = Λν ∪ Λ(ν^s)`. -/
theorem s02c_orbitKey_sconj (C : Sec2Ctx G) (hS : SconjLamProp C)
    (ν : ClassFunction ↥C.P.H0 ℂ) : orbitKey C (sconj C ν) = orbitKey C ν := by
  rw [orbitKey, orbitKey, s02c_sconj_image_lamOrbit C hS ν,
    s02c_sconj_image_lamOrbit C hS (sconj C ν), s02c_sconj_involutive]
  exact Set.union_comm _ _

/-- **The key depends only on its elements**: `μ ∈ orbitKey C ν` implies
`orbitKey C μ = orbitKey C ν`.  This is the coherence of the choice `gOf`. -/
theorem s02c_orbitKey_eq_of_mem (C : Sec2Ctx G) (hS : SconjLamProp C)
    {μ ν : ClassFunction ↥C.P.H0 ℂ} (hμ : μ ∈ orbitKey C ν) :
    orbitKey C μ = orbitKey C ν := by
  rcases hμ with hμ | hμ
  · exact (s02c_orbitKey_eq_of_lamEquiv C hμ).symm
  · obtain ⟨ξ, hξ, rfl⟩ := hμ
    rw [s02c_orbitKey_sconj C hS ξ, s02c_orbitKey_eq_of_lamEquiv C hξ]

/-- Every key is closed under `s`. -/
theorem s02c_sconj_mem_orbitKey (C : Sec2Ctx G)
    {ν : ClassFunction ↥C.P.H0 ℂ} {x : ClassFunction ↥C.P.H0 ℂ} (hx : x ∈ orbitKey C ν) :
    sconj C x ∈ orbitKey C ν := by
  rcases hx with hx | hx
  · exact Or.inr ⟨x, hx, rfl⟩
  · obtain ⟨ξ, hξ, rfl⟩ := hx
    rw [s02c_sconj_involutive C ξ]
    exact Or.inl hξ

/-! ## 4. The assembly -/

section Assembly

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- The chosen good map on a key `E` (arbitrary — e.g. `0` — if there is none; by
`OrbitCoherenceProp` there always is one on a key). -/
noncomputable def s02c_gOf (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (E : Set (ClassFunction ↥C.P.H0 ℂ)) : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ := by
  classical
  exact if h : ∃ f, GoodOn C E f then Classical.choose h else 0

/-- The chosen map is good on its key. -/
theorem s02c_gOf_spec (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {E : Set (ClassFunction ↥C.P.H0 ℂ)} (h : ∃ f, GoodOn C E f) :
    GoodOn C E (s02c_gOf C E) := by
  classical
  rw [s02c_gOf, dite_eq_left h]
  exact Classical.choose_spec h

/-- The choice only depends on the key. -/
theorem s02c_gOf_congr (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {E E' : Set (ClassFunction ↥C.P.H0 ℂ)} (h : E = E') : s02c_gOf C E = s02c_gOf C E' := by
  rw [h]

/-- `GoodOn` only depends on the values of `f` on `E` and on `s · E`; if `E` is `s`-invariant
it depends only on the values on `E`. -/
theorem s02c_GoodOn_congr (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {E : Set (ClassFunction ↥C.P.H0 ℂ)}
    {f g : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ}
    (hfg : ∀ x ∈ E, f x = g x) (hsc : ∀ x ∈ E, sconj C x ∈ E) (hf : GoodOn C E f) :
    GoodOn C E g := by
  intro μ hμ ν hν hμi hνi
  have h := hf μ hμ ν hν hμi hνi
  simpa only [hfg ν hν, hfg (sconj C ν) (hsc ν hν), hfg μ hμ] using h

/-- **A-1. BG Theorem 2.3, assembly of the core from the per-orbit lemma.**

If `s` inverts the `Λ`-orbits (`SconjLamProp`) and every key carries a good map
(`OrbitCoherenceProp`), then a single map is good on every key
(`Coherence23CoreProp`).  Explicitly `f ν := gOf (orbitKey C ν) ν`, which is well defined
because `gOf` depends only on the key (`s02c_orbitKey_eq_of_mem`). -/
theorem s02_assemblyCore {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.BG.AssemblyCoreProp C := by
  intro hS hO
  refine ⟨fun ν => s02c_gOf C (orbitKey C ν) ν, ?_⟩
  intro ν hν
  have hE : ∃ f, GoodOn C (orbitKey C ν) f := hO ν hν
  refine s02c_GoodOn_congr C ?_ ?_ (s02c_gOf_spec C hE)
  · intro x hx
    show s02c_gOf C (orbitKey C ν) x = s02c_gOf C (orbitKey C x) x
    rw [s02c_orbitKey_eq_of_mem C hS hx]
  · intro x hx
    exact s02c_sconj_mem_orbitKey C hx

end Assembly

end Work.BG

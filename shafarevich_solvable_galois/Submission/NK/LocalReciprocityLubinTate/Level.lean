import Submission.NK.LocalReciprocityLubinTate.Existence
import Submission.NK.LocalReciprocityLubinTate.Units.natCard_quotient_zpowers_pow_sup_higherUnits
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Lubin–Tate levels: degrees and reciprocity isomorphisms

This file collects the *level-wise* consequences of the Lubin–Tate tower, i.e. item 3 of the
chapter's specification:

* the reciprocity isomorphism at every finite abelian level
  `Fˣ ⧸ N_{L/F} Lˣ ≃* Gal(L/F)` (from the norm residue symbol and the norm index theorem), in
  particular at the Lubin–Tate levels `E_{m,n}`;
* the **degree** of the Lubin–Tate levels: `[E_{m,n} : F] = (m+1)·(q-1)·q^n`; in particular the
  classical `[F(π_n) : F] = (q-1)·q^{n-1}` for the pure Lubin–Tate level `E_{0,n-1}`.

The degrees are computed from the classical index of the norm group,
`[Fˣ : ⟨π^{m+1}⟩ · U^{n+1}] = (m+1)·(q-1)·q^n`
(`NK.LocalReciprocityLubinTate.Units.natCard_quotient_zpowers_pow_sup_higherUnits`, the index of the
Lubin–Tate norm group), combined with the norm index theorem
`[Fˣ : N_{L/F} Lˣ] = [L : F]` (`NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion`,
or `NK.LocalArtin.NormIndex` in general) and `Nat.card Gal(L/F) = [L : F]`
(`IsGalois.card_aut_eq_finrank`).

The companion statement — that the pure Lubin–Tate levels are *totally ramified* — is the standard
description of the ramification of `F(π_n)/F` (Serre, *Local Fields*, Ch. XV §3, Cor. to Thm. 3.4);
it is *not* formalised here, since neither Mathlib nor this workspace has a notion of total
ramification for an abstract finite extension of a local field.  What is proved here is the degree,
which is the numerical content used by the reciprocity theory.

## Main results

* `NK.LocalReciprocityLubinTate.nonempty_levelMulEquiv_of_kernelCondition`;
* `NK.LocalReciprocityLubinTate.card_aut_level_eq_index`;
* `NK.LocalReciprocityLubinTate.finrank_level_of_tower_higherUnits`.
-/

open scoped Classical

namespace NK.LocalReciprocityLubinTate

universe u v

noncomputable section

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']

/-- **The reciprocity isomorphism at a finite abelian level**, from the norm residue symbol with the
correct kernels and the norm index theorem: `Fˣ ⧸ N_{L/F} Lˣ ≃* Gal(L/F)`.

This is the level-wise form of local class field theory used by the consumer
(`NK.LocalCFT.ArtinReciprocity.artinLevelMulEquiv`), stated here as an existential so that a caller
who does not want to handle the datum can use it directly. -/
theorem nonempty_levelMulEquiv_of_kernelCondition (hK : NK.LocalArtin.KernelCondition F F')
    (hN : NK.LocalArtin.NormIndex F F')
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L]
    (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ) :
    Nonempty ((Fˣ ⧸ NK.LocalReciprocity.normGroup F ↥L) ≃* (↥L ≃ₐ[F] ↥L)) := by
  obtain ⟨R⟩ := NK.LocalArtin.Reduction.kernelCondition_toReciprocityMap hK hN
  exact ⟨R.artinLevelMulEquiv L hcomm⟩

/-- **The order of the Galois group of a level is the index of its norm group** — the norm index
theorem in the `Nat.card` form used to compute degrees. -/
theorem card_aut_level_eq_index (hN : NK.LocalArtin.NormIndex F F')
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L] :
    Nat.card (↥L ≃ₐ[F] ↥L) = (NK.LocalReciprocity.normGroup F ↥L).index := by
  haveI : FiniteDimensional F L := inferInstance
  haveI : Normal F L := inferInstance
  rw [hN L, IsGalois.card_aut_eq_finrank]

/-- **The degree of a Lubin–Tate level.**

For a uniformiser `π` with residue cardinality `q`, the level `E_{m,n}` of the Lubin–Tate tower
— the compositum of the unramified extension of degree `m+1` with the `(n+1)`-st Lubin–Tate level
`F(π_{n+1})` — has degree `(m+1)·(q-1)·q^n` over `F`.  For `m = 0` this is the classical
`[F(π_n) : F] = (q-1)·q^{n-1}` (Serre, *Local Fields*, Ch. XV §3, Thm. 3.4).

The proof is the chain `[E_{m,n} : F] = [Fˣ : N E_{m,n}ˣ] = [Fˣ : ⟨π^{m+1}⟩·U^{n+1}]`, using the
norm index theorem, the norm-group description of the tower, and the classical index computation
`[Fˣ : ⟨π^{m+1}⟩·U^{n+1}] = (m+1)(q-1)q^n`. -/
theorem finrank_level_of_tower_higherUnits (F : Type u) (F' : Type v) [Field F] [Field F']
    [Algebra F F'] [IsGalois F F'] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {π : Fˣ} {q : ℕ}
    (hπ : IsUniformizer F (π : F)) (T : LubinTateTower F F' π (higherUnits F) q)
    (hN : NK.LocalArtin.NormIndex F F') (m n : ℕ) :
    Module.finrank F ↥(T.level m n) =
      (m + 1) * (residueCard F - 1) * residueCard F ^ n := by
  haveI := T.finiteDimensional m n
  haveI := T.normal m n
  rw [← hN (T.level m n)]
  change (NK.LocalReciprocity.normGroup F ↥(T.level m n)).index =
    (m + 1) * (residueCard F - 1) * residueCard F ^ n
  rw [T.normGroup_eq m n, Subgroup.index_eq_card]
  exact NK.LocalReciprocityLubinTate.Units.natCard_quotient_zpowers_pow_sup_higherUnits
    F π hπ m n

/-- **The order of the Galois group of a Lubin–Tate level**: with `U = higherUnits F`, the Galois
group of `E_{m,n}` has order `(m+1)(q-1)q^n`; for `m = 0` this is the classical
`#Gal(F(π_n)/F) = (q-1)q^{n-1}` of Lubin–Tate theory. -/
theorem card_aut_level_of_tower_higherUnits (F : Type u) (F' : Type v) [Field F] [Field F']
    [Algebra F F'] [IsGalois F F'] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {π : Fˣ} {q : ℕ}
    (hπ : IsUniformizer F (π : F)) (T : LubinTateTower F F' π (higherUnits F) q)
    (hN : NK.LocalArtin.NormIndex F F') (m n : ℕ) :
    Nat.card (↥(T.level m n) ≃ₐ[F] ↥(T.level m n)) =
      (m + 1) * (residueCard F - 1) * residueCard F ^ n := by
  haveI := T.finiteDimensional m n
  haveI := T.normal m n
  rw [card_aut_level_eq_index hN (T.level m n)]
  change (NK.LocalReciprocity.normGroup F ↥(T.level m n)).index =
    (m + 1) * (residueCard F - 1) * residueCard F ^ n
  rw [T.normGroup_eq m n, Subgroup.index_eq_card]
  exact NK.LocalReciprocityLubinTate.Units.natCard_quotient_zpowers_pow_sup_higherUnits
    F π hπ m n

/-- **The degree of a pure Lubin–Tate level**: `[F(π_n) : F] = (q-1)q^{n-1}`, the classical formula
of Lubin–Tate theory (Serre, *Local Fields*, Ch. XV §3, Thm. 3.4), obtained from the two-parameter
degree formula at `m = 0`. -/
theorem finrank_level_zero_of_tower_higherUnits (F : Type u) (F' : Type v) [Field F] [Field F']
    [Algebra F F'] [IsGalois F F'] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {π : Fˣ} {q : ℕ}
    (hπ : IsUniformizer F (π : F)) (T : LubinTateTower F F' π (higherUnits F) q)
    (hN : NK.LocalArtin.NormIndex F F') (n : ℕ) :
    Module.finrank F ↥(T.level 0 n) = (residueCard F - 1) * residueCard F ^ n := by
  rw [finrank_level_of_tower_higherUnits F F' hπ T hN 0 n]
  ring

end

end NK.LocalReciprocityLubinTate

import Mathlib.FieldTheory.IsSepClosed
import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.NK.LocalCFT.Instance.intermediateField_eq_bot_or_top
import Submission.NK.LocalCFT.Instance.normGroup_real_complex
import Submission.NK.LocalCFT.Instance.posSubgroup_le_of_finiteIndex
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Local class field theory for the real place: `ArtinReciprocity ℝ ℂ`

`NK.LocalCFT.ArtinReciprocity F F'` is the canonical local Artin reciprocity datum for a field `F`
with a separable closure `F'`: the Artin map `Fˣ →* Gal(F^{ab}/F)`, its reciprocity isomorphisms at
the finite abelian levels of `F^{ab}`, and the existence theorem.  This file constructs that datum
for the archimedean local field `F = ℝ`, with `F' = ℂ` its separable closure.

## The mathematics

`Gal(ℂ/ℝ) = {1, conj} ≅ ℤ/2` is commutative, so every extension `ℝ ⊆ L ⊆ ℂ` is abelian
(`maxAbelianSubext ℝ ℂ = ℂ`), and every intermediate field `L` of finite dimension over `ℝ` is
`ℝ` or `ℂ` (degree `2` is prime).  The datum is therefore:

* `artin : ℝˣ →* Gal(ℂ/ℝ)` is the **sign map** — the unique surjection `ℝˣ → ℤ/2 ≅ Gal(ℂ/ℝ)`,
  sending a real unit to the identity if it is positive and to complex conjugation otherwise.
  Equivalently it is the norm residue map of the quadratic extension `ℂ/ℝ`:
  `Gal(ℂ/ℝ) ≅ ℝˣ ⧸ N_{ℂ/ℝ} ℂˣ = ℝˣ ⧸ ℝ_{>0}`;
* the level axiom holds at the two levels: at `L = ℝ`, `Gal(ℝ/ℝ) = 1` and the norm group is
  `N_{ℝ/ℝ} ℝˣ = ℝˣ` (so the kernel of the (trivial) composite is everything); at `L = ℂ`, the
  restriction is an isomorphism and `ker artin = ℝ_{>0} = N_{ℂ/ℝ} ℂˣ`;
* the existence theorem holds because every finite-index subgroup of `ℝˣ` contains the positive
  units (which are divisible), so the level `ℂ` already has its norm group inside any of them.

This is a genuine — if degenerate — instance of local class field theory (the archimedean place of
`ℚ`), and it is the local input for the real place in the Neukirch–Uchida theorem.

## Main result

* `NK.LocalCFT.Instance.artinReciprocity_complex` : `Nonempty (ArtinReciprocity ℝ ℂ)`.
-/

open scoped Classical

-- Several `haveI` below genuinely introduce typeclass instances (the normality of the top level,
-- and the triviality of the Galois group of the bottom level) for later instance search; the
-- style linter cannot see that.
set_option linter.style.haveILetI false

namespace NK.LocalCFT.Instance

noncomputable section

section GaloisGroup

/-- Every `ℝ`-algebra automorphism of `ℂ` is the identity or complex conjugation. -/
theorem galComplex_eq_one_or_conj (x : ℂ ≃ₐ[ℝ] ℂ) : x = 1 ∨ x = Complex.conjAe := by
  rcases Complex.real_algHom_eq_id_or_conj (x : ℂ →ₐ[ℝ] ℂ) with h | h
  · left
    ext z
    exact congrFun (congrArg (fun (f : ℂ →ₐ[ℝ] ℂ) => (f : ℂ → ℂ)) h) z
  · right
    ext z
    exact congrFun (congrArg (fun (f : ℂ →ₐ[ℝ] ℂ) => (f : ℂ → ℂ)) h) z

/-- Complex conjugation is an involution. -/
theorem conjAe_mul_conjAe : Complex.conjAe * Complex.conjAe = (1 : ℂ ≃ₐ[ℝ] ℂ) := by
  ext z
  simp [Complex.conjAe_coe]

/-- Complex conjugation is not the identity. -/
theorem conjAe_ne_one : (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ) ≠ 1 := by
  intro h
  have hc := congrArg (fun f : ℂ ≃ₐ[ℝ] ℂ => f Complex.I) h
  rw [Complex.conjAe_coe] at hc
  simp at hc
  have h2 : (2 : ℂ) * Complex.I = 0 := by
    rw [two_mul, add_eq_zero_iff_eq_neg]
    exact hc.symm
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 (by norm_num)
  · exact Complex.I_ne_zero h3

/-- **`Gal(ℂ/ℝ) ≅ ℤ/2` is commutative**: it has only the two elements `1` and conjugation. -/
theorem galComplex_mul_comm (σ τ : ℂ ≃ₐ[ℝ] ℂ) : σ * τ = τ * σ := by
  rcases galComplex_eq_one_or_conj σ with rfl | rfl <;>
    rcases galComplex_eq_one_or_conj τ with rfl | rfl <;> simp

/-- The commutator subgroup of `Gal(ℂ/ℝ)` is trivial. -/
theorem commutator_galComplex : commutator (ℂ ≃ₐ[ℝ] ℂ) = ⊥ := by
  rw [commutator_eq_bot_iff]
  exact IsMulCommutative.of_comm galComplex_mul_comm

end GaloisGroup

section Transfer

/-- Commutativity of an automorphism group transfers across an `R`-algebra isomorphism. -/
theorem mul_comm_of_autCongr {R : Type*} {A₁ : Type*} {A₂ : Type*} [CommSemiring R] [Semiring A₁]
    [Semiring A₂] [Algebra R A₁] [Algebra R A₂] (e : A₁ ≃ₐ[R] A₂)
    (h : ∀ σ τ : A₂ ≃ₐ[R] A₂, σ * τ = τ * σ) : ∀ σ τ : A₁ ≃ₐ[R] A₁, σ * τ = τ * σ := by
  intro σ τ
  have h' := h (e.autCongr σ) (e.autCongr τ)
  rw [← map_mul, ← map_mul] at h'
  exact e.autCongr.injective h'

end Transfer

section LevelHelpers

variable {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E]

/-- **The restriction map to the top level is injective**: an `F`-algebra automorphism of `E` is
determined by its restriction to (all of) `E`. -/
theorem restrictNormalHom_eq_one_iff_of_eq_top (L : IntermediateField F E) [Normal F L]
    (hL : L = ⊤) (σ : E ≃ₐ[F] E) :
    AlgEquiv.restrictNormalHom (F := F) (K₁ := E) L σ = 1 ↔ σ = 1 := by
  subst hL
  rw [show AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (⊤ : IntermediateField F E) σ
      = AlgEquiv.restrictNormal σ (⊤ : IntermediateField F E) from rfl,
    AlgEquiv.restrictNormal_eq_one_iff]
  constructor
  · intro h
    ext x
    exact h x IntermediateField.mem_top
  · intro h x _
    rw [h]
    rfl

/-- **The restriction map to the bottom level is trivial**. -/
theorem restrictNormalHom_eq_one_of_eq_bot (L : IntermediateField F E) [Normal F L]
    (hL : L = ⊥) (σ : E ≃ₐ[F] E) :
    AlgEquiv.restrictNormalHom (F := F) (K₁ := E) L σ = 1 := by
  subst hL
  rw [show AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (⊥ : IntermediateField F E) σ
      = AlgEquiv.restrictNormal σ (⊥ : IntermediateField F E) from rfl,
    AlgEquiv.restrictNormal_eq_one_iff]
  intro x hx
  rw [IntermediateField.mem_bot] at hx
  obtain ⟨r, rfl⟩ := hx
  rw [AlgEquiv.commutes]

end LevelHelpers

section Subsingleton

/-- `ℝ` has no nontrivial `ℝ`-algebra automorphism. -/
theorem subsingleton_algEquiv_real : Subsingleton (ℝ ≃ₐ[ℝ] ℝ) :=
  ⟨fun f g => by ext r; simp⟩

/-- The Galois group of the bottom level of an `ℝ`-extension is trivial. -/
theorem subsingleton_algEquiv_bot {E : Type*} [Field E] [Algebra ℝ E] :
    Subsingleton (↥(⊥ : IntermediateField ℝ E) ≃ₐ[ℝ] ↥(⊥ : IntermediateField ℝ E)) :=
  ⟨fun f g => (AlgEquiv.autCongr (IntermediateField.botEquiv ℝ E)).injective <| by
    haveI := subsingleton_algEquiv_real
    exact Subsingleton.elim _ _⟩

end Subsingleton

/-- **Local Artin reciprocity at the real place.**  The archimedean local field `ℝ` has separable
closure `ℂ`, and the canonical local Artin reciprocity datum for `ℝ ⊆ ℂ` is given by the sign map
`ℝˣ →* Gal(ℂ/ℝ) ≅ ℤ/2`, whose kernel is the group `ℝ_{>0} = N_{ℂ/ℝ} ℂˣ` of positive units.

The map is the unique nontrivial homomorphism `ℝˣ →* Gal(ℂ/ℝ)`: it sends a unit to `1` if the unit
is positive and to complex conjugation otherwise.  Concretely it identifies
`Gal(ℂ/ℝ) ≅ ℤ/2` with `ℝˣ ⧸ N_{ℂ/ℝ} ℂˣ`, which is the reciprocity law of the quadratic extension
`ℂ/ℝ`, and the existence theorem is supplied by the divisibility of `ℝ_{>0}`. -/
theorem artinReciprocity_complex [IsSepClosure ℝ ℂ] :
    Nonempty (NK.LocalCFT.ArtinReciprocity ℝ ℂ) := by
  haveI : IsGalois ℝ ℂ := inferInstance
  -- The Galois group of `ℂ/ℝ` is commutative, so the maximal abelian subextension is all of `ℂ`.
  have hM : NK.LocalReciprocity.maxAbelianSubext ℝ ℂ = ⊤ := by
    rw [NK.LocalReciprocity.maxAbelianSubext, commutator_galComplex,
      IntermediateField.fixedField_bot]
  -- The identification of the ambient field with `ℂ`.
  have eM : ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ) ≃ₐ[ℝ] ℂ :=
    (IntermediateField.equivOfEq hM).trans IntermediateField.topEquiv
  have hfinM : Module.finrank ℝ ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ) = 2 :=
    eM.toLinearEquiv.finrank_eq.trans Complex.finrank_real_complex
  -- The top level is normal (it is the whole extension `↥(maxAbelianSubext ℝ ℂ)/ℝ`, which is a
  -- Galois extension).
  haveI : Normal ℝ (⊤ : IntermediateField ℝ ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ)) :=
    Normal.of_algEquiv (IntermediateField.topEquiv (F := ℝ)
      (E := ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ))).symm
  -- Norm groups at the two levels.
  have hnormBot : NK.LocalReciprocity.normGroup ℝ
      ↥(⊥ : IntermediateField ℝ ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ)) = ⊤ := by
    rw [NK.LocalReciprocity.normGroup_eq_of_algEquiv
        (IntermediateField.botEquiv ℝ ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ)),
      NK.LocalReciprocity.normGroup, Algebra.norm_self, Units.map_id,
      MonoidHom.range_eq_top]
    intro x
    exact ⟨x, rfl⟩
  have hnormTop : NK.LocalReciprocity.normGroup ℝ
      ↥(⊤ : IntermediateField ℝ ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ)) =
      Units.posSubgroup ℝ := by
    rw [NK.LocalReciprocity.normGroup_eq_of_algEquiv
        (IntermediateField.topEquiv (F := ℝ)
          (E := ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ))),
      NK.LocalReciprocity.normGroup_eq_of_algEquiv eM, normGroup_real_complex]
  -- Complex conjugation, transported to `↥(maxAbelianSubext ℝ ℂ)`.
  let cM : ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ) ≃ₐ[ℝ]
      ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ) :=
    (AlgEquiv.autCongr eM).symm Complex.conjAe
  have hcM2 : cM * cM = 1 := by
    rw [← map_mul, conjAe_mul_conjAe, map_one]
  have hcM_ne_one : cM ≠ 1 := by
    intro h
    refine conjAe_ne_one ?_
    have h2 : (AlgEquiv.autCongr eM) cM = Complex.conjAe :=
      MulEquiv.apply_symm_apply (AlgEquiv.autCongr eM) Complex.conjAe
    rw [h, map_one] at h2
    exact h2.symm
  -- The Artin map: the sign of a real unit, with values in `Gal(ℂ/ℝ) ≅ ℤ/2`.
  let artin : ℝˣ →* (↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ) ≃ₐ[ℝ]
      ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ)) :=
    { toFun := fun x => if (0 : ℝ) < (x : ℝ) then 1 else cM
      map_one' := by
        rw [if_pos (show (0 : ℝ) < ((1 : ℝˣ) : ℝ) by norm_num)]
      map_mul' := by
        intro x y
        rw [Units.val_mul]
        rcases lt_trichotomy (0 : ℝ) (x : ℝ) with hx | hx | hx
        · rcases lt_trichotomy (0 : ℝ) (y : ℝ) with hy | hy | hy
          · rw [if_pos hx, if_pos hy, if_pos (mul_pos hx hy), one_mul]
          · exact absurd hy.symm (Units.ne_zero y)
          · rw [if_pos hx, if_neg (not_lt.mpr hy.le),
              if_neg (not_lt.mpr (le_of_lt (mul_neg_of_pos_of_neg hx hy))), one_mul]
        · exact absurd hx.symm (Units.ne_zero x)
        · rcases lt_trichotomy (0 : ℝ) (y : ℝ) with hy | hy | hy
          · rw [if_neg (not_lt.mpr hx.le), if_pos hy,
              if_neg (not_lt.mpr (le_of_lt (mul_neg_of_neg_of_pos hx hy))), mul_one]
          · exact absurd hy.symm (Units.ne_zero y)
          · rw [if_neg (not_lt.mpr hx.le), if_neg (not_lt.mpr hy.le),
              if_pos (mul_pos_of_neg_of_neg hx hy), hcM2] }
  have hartin_apply : ∀ x : ℝˣ, artin x = if (0 : ℝ) < (x : ℝ) then 1 else cM := fun _ => rfl
  have hartin_ker : ∀ x : ℝˣ, artin x = 1 ↔ 0 < (x : ℝ) := by
    intro x
    rw [hartin_apply x]
    by_cases hx : (0 : ℝ) < (x : ℝ)
    · rw [if_pos hx]
      exact ⟨fun _ => hx, fun _ => rfl⟩
    · rw [if_neg hx]
      exact ⟨fun h => absurd h hcM_ne_one, fun h => absurd h hx⟩
  have hartin_surj : Function.Surjective artin := by
    intro g
    have hg : g = 1 ∨ g = cM := by
      rcases galComplex_eq_one_or_conj ((AlgEquiv.autCongr eM) g) with h | h
      · left
        have h' := congrArg (AlgEquiv.autCongr eM).symm h
        rw [MulEquiv.symm_apply_apply, map_one] at h'
        exact h'
      · right
        have h' := congrArg (AlgEquiv.autCongr eM).symm h
        rw [MulEquiv.symm_apply_apply] at h'
        exact h'
    rcases hg with rfl | rfl
    · exact ⟨1, by rw [hartin_apply 1, if_pos (show (0 : ℝ) < ((1 : ℝˣ) : ℝ) by norm_num)]⟩
    · exact ⟨-1, by rw [hartin_apply (-1),
        if_neg (show ¬ (0 : ℝ) < ((-1 : ℝˣ) : ℝ) by norm_num)]⟩
  -- A level that is everything has abelian Galois group over `ℝ`.
  have hcommTop : ∀ σ τ :
      ↥(⊤ : IntermediateField ℝ ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ)) ≃ₐ[ℝ]
        ↥(⊤ : IntermediateField ℝ ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ)),
      σ * τ = τ * σ :=
    mul_comm_of_autCongr (IntermediateField.topEquiv (F := ℝ)
        (E := ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ)))
      (mul_comm_of_autCongr eM galComplex_mul_comm)
  refine ⟨{ artin := artin, isLevelIso := ?_, cofinal := ?_ }⟩
  · intro L _ _ _
    rcases intermediateField_eq_bot_or_top L hfinM with hL | hL
    · -- the level is trivial: the restriction is the trivial map
      have hnL : NK.LocalReciprocity.normGroup ℝ ↥L = ⊤ := by
        rw [NK.LocalReciprocity.normGroup_eq_of_algEquiv (IntermediateField.equivOfEq hL),
          hnormBot]
      haveI : Subsingleton (↥L ≃ₐ[ℝ] ↥L) :=
        ⟨fun f g => (AlgEquiv.autCongr (IntermediateField.equivOfEq hL)).injective <| by
          haveI := subsingleton_algEquiv_bot (E := ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ))
          exact Subsingleton.elim _ _⟩
      constructor
      · intro g
        exact ⟨1, Subsingleton.elim _ _⟩
      · have htriv : (NK.LocalCFT.levelRestrict L).comp artin = 1 := by
          refine MonoidHom.ext fun x => ?_
          simpa [NK.LocalCFT.levelRestrict] using
            restrictNormalHom_eq_one_of_eq_bot L hL (artin x)
        rw [htriv, MonoidHom.ker_eq_top_iff.mpr rfl, hnL]
    · -- the level is everything: the restriction is an isomorphism
      have hnL : NK.LocalReciprocity.normGroup ℝ ↥L = Units.posSubgroup ℝ := by
        rw [NK.LocalReciprocity.normGroup_eq_of_algEquiv (IntermediateField.equivOfEq hL),
          hnormTop]
      constructor
      · intro g
        have hsurj := AlgEquiv.restrictNormalHom_surjective (F := ℝ) (K₁ := L)
          (E := ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ))
        obtain ⟨τ, hτ⟩ := hsurj g
        obtain ⟨x, hx⟩ := hartin_surj τ
        exact ⟨x, by
          show (NK.LocalCFT.levelRestrict L) (artin x) = g
          have hlevel : (NK.LocalCFT.levelRestrict L) (artin x) =
              AlgEquiv.restrictNormalHom (F := ℝ)
                (K₁ := ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ)) L (artin x) := rfl
          rw [hlevel, hx, hτ]⟩
      · have hker : MonoidHom.ker ((NK.LocalCFT.levelRestrict L).comp artin) =
            Units.posSubgroup ℝ := by
          ext x
          rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
          have hlevel : (NK.LocalCFT.levelRestrict L) (artin x) =
              AlgEquiv.restrictNormalHom (F := ℝ)
                (K₁ := ↥(NK.LocalReciprocity.maxAbelianSubext ℝ ℂ)) L (artin x) := rfl
          rw [hlevel, propext (restrictNormalHom_eq_one_iff_of_eq_top L hL (artin x)),
            hartin_ker x, Units.mem_posSubgroup]
        rw [hker, hnL]
  · -- the existence theorem: the level `ℂ` works for every finite-index subgroup
    intro M' hM'
    refine ⟨⊤, inferInstance, inferInstance, hcommTop, ?_⟩
    rw [hnormTop]
    exact posSubgroup_le_of_finiteIndex M' hM'

end

end NK.LocalCFT.Instance

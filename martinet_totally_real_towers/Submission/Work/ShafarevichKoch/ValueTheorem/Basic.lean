import Mathlib
import Submission.Work.HopfGaschutz.Setup
import Submission.Work.ConCohomology.TrivialAction
import Submission.Work.RelatorRank.CohomologyH2
import Submission.Work.ShafarevichKoch.zmodTwoInstances
import Submission.Work.ShafarevichKoch.ZModTwoTrivialAction

/-!
# `Work.ShafarevichKoch.ValueTheorem.Basic` -- the `𝔽₂`-module structure of `H¹`, `H²`

**Namespace** `Work.ShafarevichKoch`; module `Submission.Work.ShafarevichKoch.ValueTheorem.Basic`.

The cohomology groups `H¹(Γ,𝔽₂)` and `H²(Γ,𝔽₂)` of `Work.ConCohomology` are quotients of groups of
locally constant cochains with values in `ZMod 2`, hence have **exponent two**; the additive structure
of an exponent-two abelian group is an `𝔽₂`-module structure (`AddCommGroup.zmodModule`).  This
module records that structure, and the two conversions between the chapter's cardinality form of a
dimension bound (`Work.RelatorRank.ContH2DimLe`) and the `Module.finrank` form.

Everything is proved by the elementary computation of `Work.ShaAssembly.Basic`, but in the
vocabulary of *this* chapter (no dependence on the sibling area). -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Work.ShafarevichKoch

open Work.ConCohomology

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-! ## Exponent two and the `𝔽₂`-module structure -/

/-- **`H²(Γ,𝔽₂)` has exponent two**: it is a quotient of the group of `2`-cocycles with values in
`𝔽₂`, in which every element is its own negative. -/
theorem exponent_two_contH2 (x : Work.ConCohomology.H2 Γ (ZMod 2)) : (2 : ℕ) • x = 0 := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective (Work.ConCohomology.B2' Γ (ZMod 2)) x
  rw [← map_nsmul, show (2 : ℕ) • z = 0 from ?_, map_zero]
  refine Subtype.ext ?_
  ext p
  exact CharTwo.two_nsmul _

/-- **`H¹(Γ,𝔽₂)` has exponent two.** -/
theorem exponent_two_contH1 (x : Work.ConCohomology.H1 Γ (ZMod 2)) : (2 : ℕ) • x = 0 := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective (Work.ConCohomology.B1' Γ (ZMod 2)) x
  rw [← map_nsmul, show (2 : ℕ) • z = 0 from ?_, map_zero]
  refine Subtype.ext ?_
  ext p
  exact CharTwo.two_nsmul _

/-- **`H²(Γ,𝔽₂)` is an `𝔽₂`-vector space** (through its exponent-two additive structure). -/
noncomputable instance instModuleContH2 :
    Module (ZMod 2) (Work.ConCohomology.H2 Γ (ZMod 2)) :=
  AddCommGroup.zmodModule (exponent_two_contH2 (Γ := Γ))

/-- **`H¹(Γ,𝔽₂)` is an `𝔽₂`-vector space.** -/
noncomputable instance instModuleContH1 :
    Module (ZMod 2) (Work.ConCohomology.H1 Γ (ZMod 2)) :=
  AddCommGroup.zmodModule (exponent_two_contH1 (Γ := Γ))

/-! ## The two normalisations of a dimension bound -/

/-- **A finite-dimensional `𝔽₂`-vector space of dimension `k` has `2 ^ k` elements.** -/
theorem natCard_eq_two_pow_finrank (V : Type*) [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
  rwa [Nat.card_zmod] at h

/-- **The dimension bound in `Module.finrank` form, for `H²`.**

`Work.RelatorRank.ContH2DimLe Γ r` (phrased as "`#H²(Γ,𝔽₂) = 2 ^ k` for some `k ≤ r`") holds if
and only if `H²(Γ,𝔽₂)` is finite dimensional over `𝔽₂` of dimension `≤ r`. -/
theorem contH2DimLe_iff_finrank {r : ℕ} :
    Work.RelatorRank.ContH2DimLe Γ r ↔
      FiniteDimensional (ZMod 2) (Work.ConCohomology.H2 Γ (ZMod 2)) ∧
        Module.finrank (ZMod 2) (Work.ConCohomology.H2 Γ (ZMod 2)) ≤ r := by
  constructor
  · rintro ⟨k, hk, hcard⟩
    have hne : Nat.card (Work.ConCohomology.H2 Γ (ZMod 2)) ≠ 0 := by
      rw [hcard]; exact pow_ne_zero _ (by norm_num)
    have hfin : Finite (Work.ConCohomology.H2 Γ (ZMod 2)) := Nat.finite_of_card_ne_zero hne
    haveI : Module.Finite (ZMod 2) (Work.ConCohomology.H2 Γ (ZMod 2)) := Module.Finite.of_finite
    have hcard' : Nat.card (Work.ConCohomology.H2 Γ (ZMod 2)) =
        2 ^ Module.finrank (ZMod 2) (Work.ConCohomology.H2 Γ (ZMod 2)) :=
      natCard_eq_two_pow_finrank _
    have : Module.finrank (ZMod 2) (Work.ConCohomology.H2 Γ (ZMod 2)) = k :=
      Nat.pow_right_injective (le_refl 2) (hcard'.symm.trans hcard)
    exact ⟨inferInstance, by omega⟩
  · rintro ⟨hfin, hle⟩
    exact ⟨Module.finrank (ZMod 2) (Work.ConCohomology.H2 Γ (ZMod 2)), hle,
      natCard_eq_two_pow_finrank _⟩

/-- The same conversion for `H¹`. -/
theorem contH1DimLe_iff_finrank {r : ℕ} :
    (∃ k : ℕ, k ≤ r ∧ Nat.card (Work.ConCohomology.H1 Γ (ZMod 2)) = 2 ^ k) ↔
      FiniteDimensional (ZMod 2) (Work.ConCohomology.H1 Γ (ZMod 2)) ∧
        Module.finrank (ZMod 2) (Work.ConCohomology.H1 Γ (ZMod 2)) ≤ r := by
  constructor
  · rintro ⟨k, hk, hcard⟩
    have hne : Nat.card (Work.ConCohomology.H1 Γ (ZMod 2)) ≠ 0 := by
      rw [hcard]; exact pow_ne_zero _ (by norm_num)
    have hfin : Finite (Work.ConCohomology.H1 Γ (ZMod 2)) := Nat.finite_of_card_ne_zero hne
    haveI : Module.Finite (ZMod 2) (Work.ConCohomology.H1 Γ (ZMod 2)) := Module.Finite.of_finite
    have hcard' : Nat.card (Work.ConCohomology.H1 Γ (ZMod 2)) =
        2 ^ Module.finrank (ZMod 2) (Work.ConCohomology.H1 Γ (ZMod 2)) :=
      natCard_eq_two_pow_finrank _
    have : Module.finrank (ZMod 2) (Work.ConCohomology.H1 Γ (ZMod 2)) = k :=
      Nat.pow_right_injective (le_refl 2) (hcard'.symm.trans hcard)
    exact ⟨inferInstance, by omega⟩
  · rintro ⟨hfin, hle⟩
    exact ⟨Module.finrank (ZMod 2) (Work.ConCohomology.H1 Γ (ZMod 2)), hle,
      natCard_eq_two_pow_finrank _⟩

/-! ## `H¹` is the group of continuous characters -/

/-- **`H¹(Γ,𝔽₂)` is the group of continuous homomorphisms `Γ → 𝔽₂`** (for the trivial action),
through the chapter's `Work.ConCohomology.H1EquivContAddHom`.  In particular
`#H¹(Γ,𝔽₂) = #Hom(Γ,𝔽₂) = #(Γ ⧸ Φ(Γ))^∨`. -/
noncomputable def contH1EquivContAddHom :
    Work.ConCohomology.H1 Γ (ZMod 2) ≃ Work.ConCohomology.ContAddHom Γ (ZMod 2) :=
  H1EquivContAddHom (fun _ _ => Work.ShafarevichKoch.smul_zmodTwo_eq _ _)

@[simp] theorem contH1EquivContAddHom_apply (x : Work.ConCohomology.H1 Γ (ZMod 2)) (γ : Γ) :
    (contH1EquivContAddHom x : Γ → ZMod 2) γ
      = (Work.ConCohomology.H1ToContAddHom
          (fun _ _ => Work.ShafarevichKoch.smul_zmodTwo_eq _ _) x : Γ → ZMod 2) γ := rfl

/-- `Nat.card` of `H¹(Γ,𝔽₂)` is the cardinality of the group of continuous characters. -/
theorem natCard_contH1_eq_natCard_contAddHom :
    Nat.card (Work.ConCohomology.H1 Γ (ZMod 2))
      = Nat.card (Work.ConCohomology.ContAddHom Γ (ZMod 2)) :=
  Nat.card_congr contH1EquivContAddHom

/-! ## Finiteness at a finite level -/

/-- **`H²(Γ,𝔽₂)` is finite for a finite group `Γ`**: it is a quotient of the group of locally
constant `2`-cochains, which is a subquotient of `𝔽₂ ^ (Γ × Γ)`. -/
theorem finite_contH2_of_finite (Γ' : Type*) [Group Γ'] [TopologicalSpace Γ']
    [IsTopologicalGroup Γ'] [Finite Γ'] : Finite (Work.ConCohomology.H2 Γ' (ZMod 2)) := by
  haveI hC : Finite (Work.ConCohomology.Cochain2 Γ' (ZMod 2)) :=
    Finite.of_injective
      (fun f : Work.ConCohomology.Cochain2 Γ' (ZMod 2) => fun p : Γ' × Γ' => f p)
      (fun a b h => DFunLike.ext _ _ (fun p => congrFun h p))
  haveI hZ : Finite (Work.ConCohomology.Z2 Γ' (ZMod 2)) :=
    Finite.of_injective (Subtype.val) Subtype.val_injective
  exact Finite.of_surjective (QuotientAddGroup.mk' (Work.ConCohomology.B2' Γ' (ZMod 2)))
    (QuotientAddGroup.mk'_surjective _)

/-- **`H¹(Γ,𝔽₂)` is finite for a finite group `Γ`.** -/
theorem finite_contH1_of_finite (Γ' : Type*) [Group Γ'] [TopologicalSpace Γ']
    [IsTopologicalGroup Γ'] [Finite Γ'] : Finite (Work.ConCohomology.H1 Γ' (ZMod 2)) := by
  haveI hC : Finite (Work.ConCohomology.Cochain1 Γ' (ZMod 2)) :=
    Finite.of_injective
      (fun f : Work.ConCohomology.Cochain1 Γ' (ZMod 2) => fun p : Γ' => f p)
      (fun a b h => DFunLike.ext _ _ (fun p => congrFun h p))
  haveI hZ : Finite (Work.ConCohomology.Z1 Γ' (ZMod 2)) :=
    Finite.of_injective (Subtype.val) Subtype.val_injective
  exact Finite.of_surjective (QuotientAddGroup.mk' (Work.ConCohomology.B1' Γ' (ZMod 2)))
    (QuotientAddGroup.mk'_surjective _)

end Work.ShafarevichKoch

import Mathlib
import Submission.Work.ShafarevichKoch.KummerPairing
import Submission.Work.ShafarevichKoch.exists_kummerChar
import Submission.Work.ClassFieldTower.Defs

/-!
# `Work.ShafarevichKoch.kummerChar_eq_one_iff`

Let `F` be a number field, `F_∅ = M.K` its maximal unramified pro-`2` extension,
`G_∅ = Gal(F_∅/F)`.  Let `x ∈ Fˣ`, `b ∈ F_∅` with `b * b = x`, and let
`χ : G_∅ → 𝔽₂` be a continuous character whose kernel is *exactly* the stabiliser of `b`
(`χ σ = 1 ↔ σ b = b`).

The lemma says that `χ` is the trivial character if and only if `x` is a square in `Fˣ`.
This is the elementary Kummer-theoretic core of the Shafarevich--Koch relation count: it
identifies the kernel of the Kummer pairing `V_∅ → H¹(G_∅,𝔽₂)` restricted to the units,
i.e. it says that the class of `x` in `Fˣ/Fˣ²` dies in `H¹(G_∅,𝔽₂)` precisely when `x` is
already a square in `F`.

* `⟸`: if `x = y²` then `b² = y²`, so `b = ± y ∈ F`; every `σ ∈ G_∅` fixes `b`, hence
  `χ σ = 1` by the defining property of `χ`.
* `⟹`: if `χ` is trivial then `σ b = b` for every `σ ∈ G_∅`, i.e. `b` lies in the fixed
  field of the *whole* group `G_∅`; since `F_∅/F` is Galois (here in the infinite sense)
  this fixed field is the base field `F` (`InfiniteGalois.fixedField_bot`).  So
  `b = c` for some `c ∈ F`, and `x = b² = c²` is a square (`c ≠ 0` because `b ≠ 0`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

/-- **The Kummer character of a square root of a unit is trivial iff the unit is a square.**
Given `b ∈ F_∅` with `b * b = x` for `x ∈ Fˣ`, and any continuous character
`χ : Gal(F_∅/F) → 𝔽₂` cutting out the stabiliser of `b`, `χ` is trivial exactly when `x`
is a square in `Fˣ`. -/
theorem kummerChar_eq_one_iff (F : Type*) [Field F] [NumberField F]
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} F 2) (x : Fˣ) (b : M.K)
    (hb : b * b = algebraMap F M.K (x : F)) (χ : Work.ShafarevichKoch.ProTwoChar F M)
    (hχ : ∀ σ : Work.ClassFieldTower.galoisGroup M,
      ((χ : Work.ClassFieldTower.galoisGroup M →* Multiplicative (ZMod 2)) σ = 1 ↔ σ b = b)) :
    ((∀ σ : Work.ClassFieldTower.galoisGroup M,
        (χ : Work.ClassFieldTower.galoisGroup M →* Multiplicative (ZMod 2)) σ = 1)
      ↔ ∃ y : Fˣ, x = y ^ 2) := by
  constructor
  · -- `χ` trivial ⟹ `b` is fixed by all of `G_∅`, hence lies in `F`.
    intro htriv
    have hfix : b ∈ IntermediateField.fixedField
        (⊤ : Subgroup (Work.ClassFieldTower.galoisGroup M)) := by
      rw [IntermediateField.mem_fixedField_iff]
      intro σ _
      exact (hχ σ).mp (htriv σ)
    -- the fixed field of the full Galois group of a Galois extension is the base field
    rw [InfiniteGalois.fixedField_bot] at hfix
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hfix
    have hb0 : b ≠ 0 := kummer_sq_root_ne_zero M x b hb
    have hc0 : c ≠ 0 := fun h => hb0 (by rw [← hc, h, map_zero])
    refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0]
    apply (algebraMap F M.K).injective
    rw [map_pow, hb.symm, ← hc, pow_two]
  · -- `x = y²` ⟹ `b = ± y`, so every `σ` fixes `b`.
    rintro ⟨y, rfl⟩
    intro σ
    refine (hχ σ).mpr ?_
    have hval : ((y ^ 2 : Fˣ) : F) = ((y : Fˣ) : F) * ((y : Fˣ) : F) := by
      rw [Units.val_pow_eq_pow_val, pow_two]
    have hkey : b * b
        = (algebraMap F M.K ((y : Fˣ) : F)) * (algebraMap F M.K ((y : Fˣ) : F)) := by
      rw [hb, hval, map_mul]
    rcases (mul_self_eq_mul_self_iff.mp hkey) with h | h
    · rw [h, AlgEquiv.commutes]
    · rw [h, map_neg, AlgEquiv.commutes]

end Work.ShafarevichKoch

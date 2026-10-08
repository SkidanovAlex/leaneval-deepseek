import Submission.Work.BG.Defs
import Submission.Work.BG.CharBridge

/-!
# Area BG: Bender–Glauberman 1981, Lemma 1.3 (Brauer–Suzuki TI isometry)

Hypothesis 1.2 of Bender–Glauberman 1981 (`Work.BG.Hyp12`) says that `T = H₀ ∖ U` is a
TI-subset of `G` whose normalizer is `H`.  Lemma 1.3 of the paper is the Brauer–Suzuki
TI isometry for class functions **of `H`** vanishing outside `T`:

* `(δ₁^G, δ₂^G)_G = (δ₁, δ₂)_H`, and
* `δ^G = δ` on `T`.

Both statements are instances of the Feit–Thompson closure's TI-induction theory
(`ClassFunction.inner_induce_eq_of_isTISubset`,
`ClassFunction.induce_apply_coe_of_isTISubset`), which is stated exactly for a TI-subset
`A` with normalizer bound `H` and class functions on `↥H` vanishing off `A`.

**Remark on the source.**  Bender–Glauberman state Lemma 1.3 for "class functions of `H₁`
vanishing outside `T`", and pair it with the `H`-inner product.  The literal `H₁`-version
(the inducing subgroup being `H₁ < H`) is **false**: see
`Submission/Work/BG/NOTES_FALSE_lemma13.md` for a counterexample in `A₅ ⊃ A₄ ⊃ V₄`.
The version formalised here is the one the paper's own later use requires (in §2 the
`δ`'s are differences `ν^H - μ^H` of characters induced up to `H`); the corrected
hypothesis is that the class functions live on `↥H` and vanish off `T`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory
open Subgroup

variable {G : Type} [Group G] [Finite G]

/-- **Bender–Glauberman 1981, Lemma 1.3 (isometry).**  Under Hypothesis 1.2, induction
from `H = N_G(T)` to `G` is an isometry on the class functions of `H` supported on
`T = H₀ ∖ U`: `(δ₁^G, δ₂^G)_G = (δ₁, δ₂)_H`. -/
theorem lemma13_isometry (P : Hyp12 G) [Fintype G] [Fintype ↥P.H]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥P.H : ℂ)]
    {δ₁ δ₂ : ClassFunction ↥P.H ℂ}
    (h₁ : ∀ x : ↥P.H, (x : G) ∉ Tset P.H0 P.U → δ₁ x = 0)
    (h₂ : ∀ x : ↥P.H, (x : G) ∉ Tset P.H0 P.U → δ₂ x = 0) :
    ClassFunction.inner (ClassFunction.induce P.H δ₁) (ClassFunction.induce P.H δ₂) =
      ClassFunction.inner δ₁ δ₂ :=
  ClassFunction.inner_induce_eq_of_isTISubset (k := ℂ) P.H P.TI h₁ h₂

/-- **Bender–Glauberman 1981, Lemma 1.3 (value identity).**  Under Hypothesis 1.2, for a
class function `δ` of `H` vanishing off `T = H₀ ∖ U` one has `δ^G = δ` on `T`. -/
theorem lemma13_value (P : Hyp12 G) [Fintype G] [Fintype ↥P.H]
    [Invertible (Nat.card ↥P.H : ℂ)]
    {δ : ClassFunction ↥P.H ℂ}
    (h : ∀ x : ↥P.H, (x : G) ∉ Tset P.H0 P.U → δ x = 0)
    {a : ↥P.H} (ha : (a : G) ∈ Tset P.H0 P.U) :
    ClassFunction.induce P.H δ (a : G) = δ a :=
  ClassFunction.induce_apply_coe_of_isTISubset (k := ℂ) P.H P.TI h ha

/-- The class functions of `H` supported on `T = H₀ ∖ U` (Bender–Glauberman's "class
functions of `H` vanishing outside `T`"). -/
def supportedOnT (P : Hyp12 G) : Set (ClassFunction ↥P.H ℂ) :=
  {δ | ∀ x : ↥P.H, (x : G) ∉ Tset P.H0 P.U → δ x = 0}

@[simp] theorem mem_supportedOnT {P : Hyp12 G} {δ : ClassFunction ↥P.H ℂ} :
    δ ∈ supportedOnT P ↔ ∀ x : ↥P.H, (x : G) ∉ Tset P.H0 P.U → δ x = 0 := Iff.rfl

end Work.BG

import Mathlib
import Submission.Work.BG.Defs
import Submission.Work.BG.Lambda
import Submission.Work.BG.CharBridge
-- `ClassFunction G k` carries its pointwise product only here
-- (`ClassFunction.instMul`), and this is also where the twisting lemmas live.
import Submission.OddOrder.GroupTheory.RepresentationTheory.CharacterProduct

/-!
# Area BG: `Λ` preserves `Irr(H₀)` — twisting by a member of `Λ` is irreducible

Bender–Glauberman 1981, §2: the group `Λ` of linear characters of `H₀/U` (inflated to `H₀`,
`Work.BG.Lambda`) acts on the set `Irr(H₀)` of irreducible characters of `H₀` by pointwise
multiplication, `ν ↦ λ·ν`.  The reason is that each `λ ∈ Λ` is a **linear** (degree-one)
character of `H₀`: it is the inflation of a homomorphism `β : H₀/U →* ℂˣ`, hence the character
of the one-dimensional representation `h ↦ β(h) • id`, and twisting an irreducible character by
a degree-one character of unit norm preserves irreducibility
(`OddOrder.RepresentationTheory.isIrreducibleCharacter_mul_linearClassFunction`, proved by the
norm/degree criterion: `⟨λν, λν⟩ = ⟨ν, ν⟩ = 1` and `(λν)(1) = ν(1) > 0`).

This is the structural fact behind the `Λ`-orbit decomposition of `CF(H₀)` used in
Bender–Glauberman's Lemma 1.7(ii),(iii): the `Λ`-orbit of `ν ∈ Irr(H₀)` consists of
irreducible characters, and the orbit sum `r(Λν) = r(Λ)·ν` (`Work.BG.lambdaOrbitSum_eq_mul`)
is a sum of `|Λ_ν|` members of `Irr(H₀)`.
-/

namespace Work.BG

open Subgroup
open OddOrder.RepresentationTheory

/-- **`Λ` acts on `Irr(H₀)` by multiplication.**  If `lam ∈ Λ` (the inflated linear characters
of `H₀/U`) and `δ` is an irreducible character of `H₀`, then the pointwise product `lam * δ`
is again an irreducible character of `H₀`.

`lam` is the inflation of some `β : H₀/U →* ℂˣ`, i.e. the linear character
`linearClassFunction (β.comp (quotMk P))`; the product is transported to `δ * lam` (the
pointwise product is commutative) and then dispatched to the FT lemma
`isIrreducibleCharacter_mul_linearClassFunction`. -/
theorem lambda_mul_irreducible {G : Type} [Group G] [Finite G] (P : Work.BG.Hyp12 G)
    [(P.U.subgroupOf P.H0).Normal]
    {lam δ : OddOrder.RepresentationTheory.ClassFunction ↥P.H0 ℂ}
    (hlam : lam ∈ Work.BG.Lambda P)
    (hδ : OddOrder.RepresentationTheory.IsIrreducibleCharacter δ) :
    OddOrder.RepresentationTheory.IsIrreducibleCharacter (lam * δ) := by
  -- `lam` is the inflation of a linear character of `H₀/U`
  obtain ⟨β, rfl⟩ := hlam
  haveI : Fintype ↥P.H0 := Fintype.ofFinite _
  haveI : Nonempty ↥P.H0 := ⟨1⟩
  haveI : Invertible (Nat.card ↥P.H0 : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- ... which is the linear class function of `β.comp (quotMk P)` on `H₀`
  have hcomp : ClassFunction.compHom (quotMk P) (linearClassFunction β)
      = linearClassFunction (β.comp (quotMk P)) := by
    ext x
    rfl
  rw [hcomp]
  -- the pointwise product of class functions is commutative
  have hcomm : linearClassFunction (β.comp (quotMk P)) * δ
      = δ * linearClassFunction (β.comp (quotMk P)) := by
    ext x
    simp only [ClassFunction.mul_apply]
    ring
  rw [hcomm]
  exact isIrreducibleCharacter_mul_linearClassFunction hδ (β.comp (quotMk P))

end Work.BG

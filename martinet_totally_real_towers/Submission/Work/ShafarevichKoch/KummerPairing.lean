import Mathlib
import Submission.Work.ShafarevichKoch.GeneratorRank
import Submission.Work.ShafarevichKoch.mem_VTwo_of_unramified

/-!
# `Work.ShafarevichKoch.KummerPairing` -- the Kummer pairing of `G_∅` with `V_∅`

Let `F` be a number field, `F_∅ = M.K` its maximal unramified pro-`2` extension and
`G_∅ = Gal(F_∅/F)`.  For `x ∈ Fˣ` and `b ∈ F_∅` with `b² = x`:

*every* `σ ∈ G_∅` acts on `b` by a sign, `σ b = ± b`, because `σ` fixes `x = b²`.

The resulting map `σ ↦ σb/b ∈ μ_2 = {±1}` is the **Kummer pairing** — the elementary
Kummer-theoretic bridge between the group `V_∅` of classes of order `2` (Koch's group
`Work.ShafarevichKoch.VTwo`, the `x` with `(x)` a square ideal) and the character group
`ProTwoChar F M = H¹(G_∅,𝔽₂)`.  This is the first node of the road towards the
Shafarevich--Koch relation count (Koch, *Galois Theory of `p`-Extensions*, Ch. 11); it uses
no class field theory.

Restricting to those `x` for which the square root `b` actually lies in `F_∅` (equivalently, by
`Work.ShafarevichKoch.mem_VTwo_of_unramified`, for which `F(√x)/F` is unramified) gives the
subgroup `V_∅^{unr} ⊆ V_∅` mapping into `H¹(G_∅,𝔽₂)`; its kernel is the image of the units,
which is the exact statement pinned down by item (1) of the deliverable (`V_∅ / K^{×2}` has
dimension `rank₂ Cl(F) + d₂(O_F^×)`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

variable {F : Type*} [Field F] [NumberField F]

/-- **The Kummer pairing is `μ_2`-valued.**  If `b ∈ F_∅` satisfies `b * b = x` for `x ∈ Fˣ`, then
every `σ ∈ G_∅` satisfies `σ b = b` or `σ b = -b`. -/
theorem kummerPairing_sq (M : MaximalUnramifiedProP.{0} F 2) (x : Fˣ) (b : M.K)
    (hb : b * b = algebraMap F M.K (x : F)) (σ : galoisGroup M) :
    σ b = b ∨ σ b = -b := by
  have h : σ b * (σ b) = b * b := by
    rw [← map_mul, hb, AlgEquiv.commutes, ← hb]
  exact mul_self_eq_mul_self_iff.mp h

end Work.ShafarevichKoch

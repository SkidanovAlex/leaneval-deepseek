import Mathlib
import Submission.Work.ShafarevichKoch.mem_VTwo_of_unramified
import Submission.Work.ShafarevichKoch.neg_one_kummer_slack_Kc
import Submission.Work.ClassFieldTower.All

/-!
# `Work.ShafarevichKoch.VTwoUnramified` -- the *unramified* Kummer radical

Koch's Kummer radical `V_∅ = VTwo F` collects the `x ∈ Fˣ` whose principal ideal is a square.  Its
subgroup of classes with `√x ∈ F_∅` -- i.e. those for which `F(√x)/F` is **unramified** -- is the
Kummer radical of the *unramified* tower, and is *strictly* smaller when `√-1 ∉ F_∅`, which is the
case for `Kc = ℚ(√-30030)`:

```lean
def VTwoUnramified (M : MaximalUnramifiedProP.{0} F 2) : Subgroup Fˣ :=
  {x | ∃ b : M.K, b ≠ 0 ∧ b * b = algebraMap F M.K (x : F)}
```

The point of the definition (and of the chapter's §9.4) is the *slack*: for `Kc`

* `V_∅/Kc^{×2}` has `𝔽₂`-dimension `unitTwoRank Kc + classGroupTwoRank Kc = 1 + 5 = 6`
  (`vTwo_rank_two_corrected`), while
* `V^{unr}/Kc^{×2}` has `𝔽₂`-dimension `rank₂ Cl(Kc) = d(G_∅) = 5`,

and the difference is the single class of the unit `-1` (`neg_one_kummer_slack_Kc`).  This is the
local shadow of the classical relation bound `r(G_∅) ≤ d(G_∅) + d₂(O_K^×) = 5 + 1 = 6`: the
possible extra relation is a *unit* relation (`Hajir--Maire--Ramakrishna`, arXiv:2103.09508:
`df(G_∅) = d₂(E_{Kc}/N E_∅) ≤ d₂(E_{Kc}) = 1`).

## Main results

* `mem_VTwoUnramified_iff` -- the defining property;
* `VTwoUnramified_le_VTwo` -- unramified forces the square ideal (`mem_VTwo_of_unramified`,
  transported to `F_∅` through a finite Galois intermediate level);
* `sq_mem_VTwoUnramified` -- squares lie in `V^{unr}` (so `(Fˣ)² ≤ V^{unr}` and the quotient
  `V^{unr}/Fˣ²` makes sense);
* `neg_one_not_mem_VTwoUnramified_Kc` -- `-1 ∉ V^{unr}` for `Kc`, while `-1 ∈ V_∅`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

/-- **The unramified Kummer radical** `V^{unr} = {x ∈ Fˣ : √x ∈ F_∅}`, equivalently the set of `x`
for which `F(√x)/F` is unramified over `F`: `(x)` is a square ideal and `x` is a local square at
every place above `2` (and at the infinite places). -/
def VTwoUnramified (F : Type*) [Field F] [NumberField F]
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} F 2) : Subgroup Fˣ where
  carrier := {x | ∃ b : M.K, b ≠ 0 ∧ b * b = algebraMap F M.K (x : F)}
  mul_mem' := by
    rintro x y ⟨b, hb0, hb⟩ ⟨c, hc0, hc⟩
    refine ⟨b * c, mul_ne_zero hb0 hc0, ?_⟩
    calc (b * c) * (b * c) = (b * b) * (c * c) := by rw [mul_mul_mul_comm]
      _ = algebraMap F M.K (x : F) * algebraMap F M.K (y : F) := by rw [hb, hc]
      _ = algebraMap F M.K ((x * y : Fˣ) : F) := by rw [← map_mul, ← Units.val_mul]
  one_mem' := ⟨1, one_ne_zero, by simp⟩
  inv_mem' := by
    rintro x ⟨b, hb0, hb⟩
    refine ⟨b⁻¹, inv_ne_zero hb0, ?_⟩
    rw [← mul_inv_rev, hb, ← map_inv₀]
    simp

/-- Membership in the unramified Kummer radical, unfolded. -/
theorem mem_VTwoUnramified_iff (F : Type*) [Field F] [NumberField F]
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} F 2) (x : Fˣ) :
    x ∈ VTwoUnramified F M ↔ ∃ b : M.K, b ≠ 0 ∧ b * b = algebraMap F M.K (x : F) :=
  Iff.rfl

/-- **Squares lie in the unramified radical**: `y²` has the square root `y ∈ F ⊆ F_∅`. -/
theorem sq_mem_VTwoUnramified (F : Type*) [Field F] [NumberField F]
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} F 2) (y : Fˣ) :
    y ^ 2 ∈ VTwoUnramified F M := by
  refine ⟨algebraMap F M.K (y : F), ?_, ?_⟩
  · intro h
    exact Units.ne_zero y ((algebraMap F M.K).injective (by simpa using h))
  · rw [← map_mul, ← Units.val_mul, pow_two]

/-- **The unramified radical is contained in Koch's radical** `V_∅`.

If `b² = x` with `b ∈ F_∅`, then `b` lies in a finite intermediate field `E ⊆ F_∅`; enlarging `E`
to its normal closure inside `F_∅` produces a finite Galois level of the unramified tower, and
`mem_VTwo_of_unramified` gives that the principal ideal `(x)` is a square. -/
theorem VTwoUnramified_le_VTwo (F : Type*) [Field F] [NumberField F]
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} F 2) :
    VTwoUnramified F M ≤ VTwo F := by
  intro x hx
  obtain ⟨b, _hb0, hb⟩ := hx
  let E : IntermediateField F M.K := IntermediateField.adjoin F ({b} : Set M.K)
  haveI hfdE : FiniteDimensional F E :=
    IntermediateField.finiteDimensional_adjoin
      (fun z _ => IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic z))
  let L : IntermediateField F M.K := IntermediateField.normalClosure F E M.K
  haveI hfdL : FiniteDimensional F L := normalClosure.is_finiteDimensional F E M.K
  haveI hgalL : IsGalois F L := IsGalois.normalClosure F E M.K
  haveI hNFL : NumberField ↥L := NumberField.of_module_finite F ↥L
  have hbL : b ∈ L :=
    (IntermediateField.subset_adjoin F ({b} : Set M.K)).trans
      (IntermediateField.le_normalClosure E) (by simp)
  refine mem_VTwo_of_unramified F ↥L x ⟨b, hbL⟩ ?_ (M.unramified L hfdL hgalL)
  have hz : ((⟨b, hbL⟩ : ↥L) * ⟨b, hbL⟩ : ↥L) = algebraMap F ↥L (x : F) := by
    ext
    simpa using hb
  exact hz

/-- **`-1` does not lie in the unramified radical of `Kc`**: `√-1 ∉ Kc_∅`. -/
theorem neg_one_not_mem_VTwoUnramified_Kc
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2) :
    (-1 : Work.ClassFieldTower.Kcˣ) ∉ VTwoUnramified Work.ClassFieldTower.Kc M := by
  rintro ⟨b, _hb0, hb⟩
  exact (neg_one_kummer_slack_Kc M).2.2 ⟨b, hb⟩

end Work.ShafarevichKoch

import Mathlib
import Submission.Work.ShafarevichKoch.RatCoeff
import Submission.Work.ShafarevichKoch.Bockstein.exists_two_smul_eq
import Submission.Work.ShafarevichKoch.Bockstein.two_smul_eq_zero_iff
import Submission.Work.ConCohomology.All
import Submission.Work.RelatorRank.CohomologyH2

/-!
# `Work.ShafarevichKoch.Bockstein.SES` -- the coefficient sequence `0 → μ₂ → ℚ/ℤ →² ℚ/ℤ → 0`

This module supplies the *second* coefficient sequence of the relation count (the first being
`0 → ℤ →² ℤ → ℤ/2 → 0` of `CoeffZ.lean`, and the third `0 → ℤ → ℚ → ℚ/ℤ → 0` of
`RatCoeff.lean`): for the trivial action of a group `G` on `ℚ/ℤ`,

```
0 ⟶ ℤ/2 ⟶^{n ↦ n/2} ℚ/ℤ ⟶^{·2} ℚ/ℤ ⟶ 0 ,
```

whose long exact sequence identifies `H³(G,ℤ)[2] = H²(G,ℚ/ℤ)[2]` with the cokernel of the Bockstein
connecting map `H¹(G,ℚ/ℤ) → H²(G,ℤ/2)`.  In the classical picture
(`Classical.choice`-free: the two pieces are two delegated lemmas of
`Bockstein/exists_two_smul_eq.lean` and `Bockstein/two_smul_eq_zero_iff.lean`) the first map is the
inclusion of the roots of unity `μ_2 ↪ ℚ/ℤ` and the second is multiplication by `2`.

## Main declarations

* `Work.ShafarevichKoch.Bockstein.halfElem` -- the class of `1/2` in `ℚ/ℤ`;
* `Work.ShafarevichKoch.Bockstein.muTwoOfZMod` : `ℤ/2 → ℚ/ℤ`, `0 ↦ 0`, `1 ↦ 1/2`;
* `Work.ShafarevichKoch.Bockstein.muTwoInjective`, `muTwoSurjectiveTwo`, `muTwoExact`;
* `Work.ShafarevichKoch.Bockstein.muTwoZModEqHom`, `muTwoDoubleEqHom`, `muTwoSES` : the coefficient
  sequence as a `CoeffSES`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Work.ShafarevichKoch.Bockstein

open Work.ConCohomology

variable {G : Type*} [Group G]
variable [DistribMulAction G (ZMod 2)] [DistribMulAction G QZ]

/-- The class of `1/2` in `ℚ/ℤ = QZ`. -/
def halfElem : QZ := QuotientAddGroup.mk (1 / 2 : ℚ)

/-- `2 • halfElem = 0` in `ℚ/ℤ`: the class of `1/2` is `2`-torsion. -/
theorem two_smul_halfElem : (2 : ℕ) • halfElem = 0 := by
  rw [halfElem, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
  have h : (2 : ℕ) • (1 / 2 : ℚ) = 1 := by norm_num
  rw [h]
  exact AddSubgroup.mem_zmultiples 1

/-- `halfElem ≠ 0`, because `1/2` is not an integer. -/
theorem halfElem_ne_zero : halfElem ≠ 0 := by
  intro h
  rw [halfElem, QuotientAddGroup.eq_zero_iff] at h
  -- `zmultiples 1` is contained in the image of `ℤ` in `ℚ`
  have hH : AddSubgroup.zmultiples (1 : ℚ) ≤ AddSubgroup.map (Int.castAddHom ℚ) ⊤ := by
    rw [AddSubgroup.zmultiples_le]
    exact ⟨1, by simp⟩
  obtain ⟨n, -, hn⟩ := hH h
  have hn' : (n : ℚ) = 1 / 2 := hn
  have h2 : (2 * n : ℤ) = 1 := by
    apply Int.cast_injective (α := ℚ)
    push_cast
    linarith [hn']
  omega

/-- **The inclusion `μ_2 ↪ ℚ/ℤ`**: `0 ↦ 0`, `1 ↦ 1/2`. -/
def muTwoOfZMod (n : ZMod 2) : QZ := if n = 0 then 0 else halfElem

@[simp] lemma muTwoOfZMod_zero : muTwoOfZMod (0 : ZMod 2) = 0 := by
  simp [muTwoOfZMod]

@[simp] lemma muTwoOfZMod_one : muTwoOfZMod (1 : ZMod 2) = halfElem := by
  simp [muTwoOfZMod]

/-- `μ_2 ↪ ℚ/ℤ` is injective (its kernel is trivial). -/
theorem muTwoInjective : Function.Injective muTwoOfZMod := by
  intro a b h
  have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hne : halfElem ≠ 0 := halfElem_ne_zero
  rcases hcases a with rfl | rfl <;> rcases hcases b with rfl | rfl
  · rfl
  · exact absurd (by simpa [muTwoOfZMod] using h.symm) hne
  · exact absurd (by simpa [muTwoOfZMod] using h) hne
  · rfl

/-- `μ_2 ↪ ℚ/ℤ` is additive, hence an `EqHom` for any trivial actions. -/
theorem muTwoOfZMod_add (a b : ZMod 2) : muTwoOfZMod (a + b) = muTwoOfZMod a + muTwoOfZMod b := by
  have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have hh : halfElem + halfElem = 0 := by
    rw [← two_nsmul]
    exact two_smul_halfElem
  rcases hcases a with rfl | rfl <;> rcases hcases b with rfl | rfl
  · simp
  · simp [muTwoOfZMod_zero, muTwoOfZMod_one]
  · simp [muTwoOfZMod_zero, muTwoOfZMod_one]
  · rw [h11, muTwoOfZMod_zero, muTwoOfZMod_one, hh]

/-- **The exactness clause**: for `b : ℚ/ℤ`, `2 • b = 0` iff `b` is in the image of `μ_2 ↪ ℚ/ℤ`.
This is the 2-torsion description of `ℚ/ℤ` (the delegated lemma
`Work.ShafarevichKoch.Bockstein.two_smul_eq_zero_iff`), rewritten as an image statement. -/
theorem muTwoExact (b : QZ) : (2 : ℕ) • b = 0 ↔ ∃ a : ZMod 2, muTwoOfZMod a = b := by
  rw [two_smul_eq_zero_iff b]
  constructor
  · rintro (hb | hb)
    · exact ⟨0, by rw [hb, muTwoOfZMod_zero]⟩
    · exact ⟨1, by rw [hb, muTwoOfZMod_one, halfElem]⟩
  · rintro ⟨a, ha⟩
    have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases hcases a with rfl | rfl
    · left
      rw [← ha, muTwoOfZMod_zero]
    · right
      rw [← ha, muTwoOfZMod_one, halfElem]

/-- Equivariance of the inclusion `μ_2 ↪ ℚ/ℤ` for trivial actions. -/
theorem muTwoZMod_smul (htriv2 : ∀ (σ : G) (m : ZMod 2), σ • m = m)
    (htrivQZ : ∀ (σ : G) (r : QZ), σ • r = r) (σ : G) (m : ZMod 2) :
    muTwoOfZMod (σ • m) = σ • muTwoOfZMod m := by
  rw [htriv2 σ m, htrivQZ σ (muTwoOfZMod m)]

/-- Equivariance of multiplication by `2` on `ℚ/ℤ` for trivial actions. -/
theorem muTwoDouble_smul (htrivQZ : ∀ (σ : G) (r : QZ), σ • r = r) (σ : G) (x : QZ) :
    (2 : ℕ) • (σ • x) = σ • ((2 : ℕ) • x) := by
  rw [htrivQZ σ x, htrivQZ σ ((2 : ℕ) • x)]

/-- The `EqHom` `ℤ/2 → ℚ/ℤ` of the coefficient sequence (trivial actions). -/
def muTwoZModEqHom (htriv2 : ∀ (σ : G) (m : ZMod 2), σ • m = m)
    (htrivQZ : ∀ (σ : G) (r : QZ), σ • r = r) : EqHom G (ZMod 2) QZ where
  toFun := muTwoOfZMod
  map_zero' := muTwoOfZMod_zero
  map_add' := muTwoOfZMod_add
  map_smul' := muTwoZMod_smul htriv2 htrivQZ

@[simp] lemma muTwoZModEqHom_apply (htriv2 : ∀ (σ : G) (m : ZMod 2), σ • m = m)
    (htrivQZ : ∀ (σ : G) (r : QZ), σ • r = r) (a : ZMod 2) :
    muTwoZModEqHom htriv2 htrivQZ a = muTwoOfZMod a := rfl

/-- The `EqHom` `ℚ/ℤ → ℚ/ℤ` of the coefficient sequence (multiplication by `2`). -/
def muTwoDoubleEqHom (htrivQZ : ∀ (σ : G) (r : QZ), σ • r = r) : EqHom G QZ QZ where
  toFun := fun x => (2 : ℕ) • x
  map_zero' := by simp
  map_add' := by
    intro x y
    rw [two_nsmul, two_nsmul, two_nsmul]
    abel
  map_smul' := muTwoDouble_smul htrivQZ

@[simp] lemma muTwoDoubleEqHom_apply (htrivQZ : ∀ (σ : G) (r : QZ), σ • r = r) (x : QZ) :
    muTwoDoubleEqHom htrivQZ x = (2 : ℕ) • x := rfl

/-- Multiplication by `2` on `ℚ/ℤ` is surjective (the delegated `2`-divisibility lemma). -/
theorem muTwoSurjectiveTwo (htrivQZ : ∀ (σ : G) (r : QZ), σ • r = r) :
    Function.Surjective (muTwoDoubleEqHom htrivQZ) := by
  intro y
  obtain ⟨x, hx⟩ := exists_two_smul_eq y
  exact ⟨x, by simpa only [muTwoDoubleEqHom_apply] using hx⟩

/-- The exactness clause of `0 → μ_2 → ℚ/ℤ →² ℚ/ℤ → 0` (the delegated `2`-torsion lemma). -/
theorem muTwoExactHom (htriv2 : ∀ (σ : G) (m : ZMod 2), σ • m = m)
    (htrivQZ : ∀ (σ : G) (r : QZ), σ • r = r) (b : QZ) :
    muTwoDoubleEqHom htrivQZ b = 0 ↔ ∃ a : ZMod 2, muTwoZModEqHom htriv2 htrivQZ a = b := by
  simp only [muTwoDoubleEqHom_apply, muTwoZModEqHom_apply]
  exact muTwoExact b

/-- **The coefficient sequence `0 → μ_2 → ℚ/ℤ →² ℚ/ℤ → 0`** (for trivial actions), in the
workspace's `CoeffSES` encoding.  Its connecting map `H¹(G,ℚ/ℤ) → H²(G,ℤ/2)` is the Bockstein whose
cokernel is (up to the identification of `RatCoeff.lean`) the `2`-torsion of `H³(G,ℤ)`. -/
def muTwoSES (htriv2 : ∀ (σ : G) (m : ZMod 2), σ • m = m)
    (htrivQZ : ∀ (σ : G) (r : QZ), σ • r = r) : CoeffSES G (ZMod 2) QZ QZ where
  f := muTwoZModEqHom htriv2 htrivQZ
  g := muTwoDoubleEqHom htrivQZ
  injective_f := by
    intro a b h
    exact muTwoInjective (by simpa only [muTwoZModEqHom_apply] using h)
  surjective_g := muTwoSurjectiveTwo htrivQZ
  exact := muTwoExactHom htriv2 htrivQZ

end Work.ShafarevichKoch.Bockstein

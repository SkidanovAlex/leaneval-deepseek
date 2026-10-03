/-
# `rootHom_conj_mem_range`

Let `P = F(RootIdx α t)` be the free group obtained from `F(α)` by adjoining a letter `z`
(`RootIdx α t = {a : α // a ≠ t} ⊕ Unit`, `z = Sum.inr ()`), let `K = (rootHom t p).range` be the
image of `F(α)` under `rootHom : t ↦ z ^ p`, `a ↦ a` (`a ≠ t`), and let `r ≠ 1` be an element of
`F(α)` with `⟪r⟫ ∩ ⟨t⟩ = ⊥`.

The theorem proved here is the "malnormality" statement used to feed
`cohenLyndonNC_of_malnormal`: a `g ∈ P` for which a nonzero power of `g · rootHom r · g⁻¹` lies in
`K` must itself lie in `K`.

The proof uses two ingredients from the companion files:

* `rootHom_mem_iff_good` (`rootHomConjCriterion.lean`): the "`z`-run criterion" for `K`;
* `rootHom_descent` (`rootHom_descent.lean`): if `g ∉ K`, `M ∈ K` and `g M g⁻¹ ∈ K`, then `M` is
  conjugate within `K` to an element of the cyclic subgroup `⟨z ^ p⟩` (the Karrass--Solitar
  descent along the amalgam `P = K ∗_{⟨z^p⟩} ⟨z⟩`).

Given the second, one transports the conjugacy relation back to `F(α)` along `rootHom` and
contradicts `⟪r⟫ ∩ ⟨t⟩ = ⊥` using that free groups are torsion-free.
-/
import Mathlib
import Submission.Work.ORLocInd.CohenLyndon.substDefs
import Submission.Work.ORLocInd.CohenLyndon.rootHomConjCriterion
import Submission.Work.ORLocInd.CohenLyndon.rootHom_descent

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

universe u

namespace Work.ORLocInd.CohenLyndon

variable {α : Type u} [DecidableEq α]

/-- A free generator is not the identity. -/
theorem of_ne_one' (t : α) : FreeGroup.of t ≠ (1 : FreeGroup α) := by
  intro h
  have h' := congr_arg FreeGroup.toWord h
  rw [FreeGroup.toWord_of, FreeGroup.toWord_one] at h'
  simp at h'

/-- A power of a free generator equals `1` only if the exponent is `0`. -/
theorem of_zpow_eq_one_iff (t : α) (l : ℤ) : (FreeGroup.of t) ^ l = 1 ↔ l = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h]; simp⟩
  rcases lt_trichotomy l 0 with hl | hl | hl
  · have hpos : (0 : ℤ) < -l := by omega
    have hnat : (((-l).natAbs : ℕ) : ℤ) = -l := Int.natAbs_of_nonneg (le_of_lt hpos)
    have hpw : (FreeGroup.of t) ^ ((-l).natAbs) = 1 := by
      have h' := congr_arg Inv.inv h
      rw [inv_one] at h'
      rw [← zpow_neg] at h'
      simpa [hnat] using h'
    have h1 : (FreeGroup.of t) ^ ((-l).natAbs) = (1 : FreeGroup α) ^ ((-l).natAbs) := by
      simpa using hpw
    exact absurd (IsMulTorsionFree.pow_left_injective (n := ((-l).natAbs)) (by omega) h1)
      (of_ne_one' t)
  · exact hl
  · have hnat : ((l.natAbs : ℕ) : ℤ) = l := Int.natAbs_of_nonneg (le_of_lt hl)
    have hpw : (FreeGroup.of t) ^ (l.natAbs) = 1 := by
      have h' := h
      rw [← hnat] at h'
      simpa using h'
    have h1 : (FreeGroup.of t) ^ (l.natAbs) = (1 : FreeGroup α) ^ (l.natAbs) := by
      simpa using hpw
    exact absurd (IsMulTorsionFree.pow_left_injective (n := l.natAbs) (by omega) h1)
      (of_ne_one' t)

/-- **The Karrass--Solitar malnormality input for the Cohen--Lyndon substitution step.** -/
theorem rootHom_conj_mem_range {α : Type u} [DecidableEq α] (t x : α) (hxt : x ≠ t) (p : ℤ)
    (hp : p ≠ 0) {r : FreeGroup α} (hr1 : r ≠ 1)
    (hnd : Subgroup.normalClosure ({r} : Set (FreeGroup α)) ⊓
      Subgroup.zpowers (FreeGroup.of t) = ⊥) :
    ∀ g : FreeGroup (RootIdx α t),
      (∃ j : ℤ, j ≠ 0 ∧ (g * rootHom t p r * g⁻¹) ^ j ∈ (rootHom t p).range) →
      g ∈ (rootHom t p).range := by
  intro g ⟨j, hj, hjmem⟩
  by_contra hgK
  have hM : (rootHom t p r) ^ j ∈ (rootHom t p).range :=
    Subgroup.zpow_mem _ (MonoidHom.mem_range.mpr ⟨r, rfl⟩) j
  have hconj : g * (rootHom t p r ^ j) * g⁻¹ ∈ (rootHom t p).range := by
    have heq : (g * rootHom t p r * g⁻¹) ^ j = g * (rootHom t p r ^ j) * g⁻¹ := by
      rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
    rw [← heq]
    exact hjmem
  obtain ⟨Q, hQ, hQc⟩ := rootHom_descent hp hM hgK hconj
  obtain ⟨q, rfl⟩ := hQ
  rw [show Subgroup.zpowers (rootLetter t ^ p) =
      Subgroup.zpowers (rootHom t p (FreeGroup.of t)) from by rw [rootHom_of_eq]] at hQc
  obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp hQc
  have hkey : rootHom t p (q * r ^ j * q⁻¹) = rootHom t p ((FreeGroup.of t) ^ l) := by
    rw [map_mul, map_mul, map_zpow, map_zpow, map_inv, hl]
  have hqr : q * r ^ j * q⁻¹ = (FreeGroup.of t) ^ l := rootHom_injective hxt hp hkey
  have hmem : (FreeGroup.of t) ^ l ∈ Subgroup.normalClosure ({r} : Set (FreeGroup α)) := by
    rw [← hqr]
    exact Subgroup.Normal.conj_mem Subgroup.normalClosure_normal (r ^ j)
      (Subgroup.zpow_mem _ (Subgroup.subset_normalClosure (by simp)) j) q
  have hbot : (FreeGroup.of t) ^ l ∈ (⊥ : Subgroup (FreeGroup α)) := by
    rw [← hnd]
    exact Subgroup.mem_inf.mpr
      ⟨hmem, Subgroup.zpow_mem _ (Subgroup.mem_zpowers (FreeGroup.of t)) l⟩
  have hl0 : l = 0 := (of_zpow_eq_one_iff t l).mp (by simpa using hbot)
  have hrj : r ^ j = 1 := by
    have h1 : q * r ^ j * q⁻¹ = 1 := by rw [hqr, hl0]; simp
    have h2 := congr_arg (fun y => q⁻¹ * y * q) h1
    simpa [mul_assoc] using h2
  -- torsion-freeness of the free group
  have hr1' : r = 1 := by
    rcases lt_trichotomy j 0 with hj' | hj' | hj'
    · have hpos : (0 : ℤ) < -j := by omega
      have hnat : (((-j).natAbs : ℕ) : ℤ) = -j := Int.natAbs_of_nonneg (le_of_lt hpos)
      have hpw : r ^ ((-j).natAbs) = 1 := by
        have h := congr_arg Inv.inv hrj
        rw [inv_one] at h
        rw [← zpow_neg] at h
        simpa [hnat] using h
      have h1 : r ^ ((-j).natAbs) = (1 : FreeGroup α) ^ ((-j).natAbs) := by simpa using hpw
      exact IsMulTorsionFree.pow_left_injective (n := ((-j).natAbs)) (by omega) h1
    · exact absurd hj' hj
    · have hnat : ((j.natAbs : ℕ) : ℤ) = j := Int.natAbs_of_nonneg (le_of_lt hj')
      have hpw : r ^ (j.natAbs) = 1 := by
        have h := hrj
        rw [← hnat] at h
        simpa using h
      have h1 : r ^ (j.natAbs) = (1 : FreeGroup α) ^ (j.natAbs) := by simpa using hpw
      exact IsMulTorsionFree.pow_left_injective (n := j.natAbs) (by omega) h1
  exact hr1 hr1'

end Work.ORLocInd.CohenLyndon

import Mathlib
import Submission.Work.Mostow.axisDichotomy

/-!
# The axis datum for a discrete subgroup of `PO 1 1`

`PO 1 1` is the isometry group of `ℍ¹ = E 1`.  For a discrete subgroup `D ≤ PO 1 1` the set

`T = {h ∈ D | h = 1 ∨ h is fixed point free}`

is a subgroup: it is the set of "translations" of `D` (an isometry of the line is either a
translation or a reflection, and the latter always has a fixed point).  `axisDichotomy` applied to
`T` plus the observation that a non-trivial element of `T` is exactly a fixed point free element of
`D` yields the dichotomy of `axisDatum`:

* either `D` has a fixed point free element `g₀` of minimal displacement, and every square `h * h`
  (`h ∈ D`) is a power of `g₀` (here `D` is an infinite cyclic extension of a reflection),
* or the square of every element of `D` is trivial (`D` is a `2`-group, in fact of order `≤ 2`).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity
open AxisDich

/-- A fixed point free isometry of `ℍ¹` acts on the signed coordinate as a translation
`x ↦ c + x` with `c ≠ 0`.  (An element acting as `x ↦ c - x` fixes the point at signed
coordinate `c/2`.) -/
lemma Phi_form_free (hI : HypIsoData 1) (g : PO 1 1) (hg : ∀ x : E 1, g • x ≠ x) :
    ∃ c : ℝ, c ≠ 0 ∧ ∀ x : ℝ, Phi g x = c + x := by
  rcases Phi_form hI g with ⟨c, hc | hc⟩
  · refine ⟨c, fun hc0 => hg 0 ?_, hc⟩
    refine (Phi_fix_iff hI g 0).mpr ?_
    show Phi g (sc (0 : E 1)) = sc (0 : E 1)
    rw [hc, hc0, zero_add]
  · exfalso
    refine hg (pt (c / 2)) ?_
    refine (Phi_fix_iff hI g (pt (c / 2))).mpr ?_
    rw [sc_pt, hc]
    ring

/-- The set of elements of `D` that are trivial or fixed point free is a subgroup: it is the
"translation subgroup" of `D`. -/
def transSub (hA : POBasic 1) (hI : HypIsoData 1) (D : Subgroup (PO 1 1)) : Subgroup (PO 1 1) where
  carrier := {h | h ∈ D ∧ (h = 1 ∨ ∀ x : E 1, h • x ≠ x)}
  one_mem' := ⟨D.one_mem, Or.inl rfl⟩
  mul_mem' := by
    intro h k hh hk
    obtain ⟨hhD, hh2⟩ := hh
    obtain ⟨hkD, hk2⟩ := hk
    refine ⟨D.mul_mem hhD hkD, ?_⟩
    rcases hh2 with h1 | hf
    · subst h1; simpa using hk2
    rcases hk2 with h1 | kf
    · subst h1; exact Or.inr (by simpa using hf)
    -- both are fixed point free, hence translations `x ↦ c + x`, `x ↦ d + x`
    obtain ⟨c, hc0, hc⟩ := Phi_form_free hI h hf
    obtain ⟨d, hd0, hd⟩ := Phi_form_free hI k kf
    by_cases hcd : c + d = 0
    · left
      refine (Phi_eq_one_iff hA hI (h * k)).mp ?_
      intro x
      rw [Phi_mul hA h k, Function.comp_apply, hc, hd]
      linarith
    · right
      intro x hx
      have hfix : Phi (h * k) (sc x) = sc x := (Phi_fix_iff hI (h * k) x).mp hx
      rw [Phi_mul hA h k, Function.comp_apply, hc, hd] at hfix
      exact hcd (by linarith)
  inv_mem' := by
    intro h hh
    obtain ⟨hhD, hh2⟩ := hh
    refine ⟨D.inv_mem hhD, ?_⟩
    rcases hh2 with h1 | hf
    · subst h1; exact Or.inl (by rw [inv_one])
    · right
      intro x hx
      have h2 : h • (h⁻¹ • x) = x := by
        rw [← hA.mul_smul, mul_inv_cancel, hA.one_smul]
      rw [hx] at h2
      exact hf x h2

theorem axisDatum (hA : Submission.Mostow.POActionProp 1) (hI : Submission.Mostow.HypIsometryProp 1)
    (D : Subgroup (LeanEval.Geometry.MostowRigidity.PO 1 1)) (hdisc : IsDiscrete (SetLike.coe D)) :
    (∃ g₀ ∈ D, (∀ x : Submission.Mostow.E 1, g₀ • x ≠ x) ∧
      (∀ h ∈ D, (∀ x : Submission.Mostow.E 1, h • x ≠ x) →
        Submission.Mostow.hdist (0 : Submission.Mostow.E 1) (g₀ • (0 : Submission.Mostow.E 1))
          ≤ Submission.Mostow.hdist (0 : Submission.Mostow.E 1) (h • (0 : Submission.Mostow.E 1))) ∧
      (∀ h ∈ D, h * h ∈ Subgroup.zpowers g₀))
    ∨ (∀ h ∈ D, h * h = 1) := by
  have hA' : POBasic 1 := POBasic.ofProp hA
  have hI' : HypIsoData 1 := HypIsoData.ofProp hI
  have hT : ∀ h, h ∈ transSub hA' hI' D ↔ h ∈ D ∧ (h = 1 ∨ ∀ x : E 1, h • x ≠ x) :=
    fun h => Iff.rfl
  obtain ⟨hsq, hdich⟩ := axisDichotomy hA hI D hdisc (transSub hA' hI' D) hT
  rcases hdich with hbot | ⟨g₀, hg₀T, hg₀free, hTeq, hg₀min⟩
  · right
    intro h hh
    have hmem : h * h ∈ transSub hA' hI' D := hsq h hh
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  · left
    refine ⟨g₀, ((hT g₀).mp hg₀T).1, hg₀free, ?_, ?_⟩
    · intro h hh hfree
      refine hg₀min h ((hT h).mpr ⟨hh, Or.inr hfree⟩) ?_
      intro h1
      exact hfree 0 (by rw [h1, hA'.one_smul])
    · intro h hh
      have hmem : h * h ∈ transSub hA' hI' D := hsq h hh
      rw [hTeq] at hmem
      rw [Subgroup.zpowers_eq_closure]
      exact hmem

end Work.Mostow

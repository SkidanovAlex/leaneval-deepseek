/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The "all coefficients are units" case of the induction of [JZLA20, Theorem 6.1]

This is the branch of the induction of [JZLA20, Theorem 6.1] in which no coefficient of the skew
Laurent series `f` of `e aH` attains the top complexity `Tree_H(e aH)`.  Then every non-zero
coefficient `f.1 k` has `Tree_H(f.1 k) < Tree_H(e aH)`, so it is a unit of `D_{H,P}` by the
induction hypothesis `hInv`; lying in `D_{N,P}`, its inverse lies in `D_{N,P}` by
`Prop51Data.DN_inv_closed`.  Hence `f` is a unit of the skew Laurent series ring
(`SkewLaurentSeries.exists_inverse_of_vanishesBelow_of_coeff_isUnit`), `e aH = laurentEmbed f` is a
unit of `P`, and its inverse lies in `D_{H,P}` by `Prop51Data.DH_inv_closed`.  Finally, `aH` is a
unit of `D_{K[↥H],U}` and `inclSub φ H aH` — i.e. `Φ_{Kˣ×G}(ofSubgroup (ratUnitsTimesEquiv α))` —
is a unit of `D_{K[G],U}`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Section6.Thm61Step
import Submission.Work.ORHughesFree.Section6.Thm61InductionAux
import Submission.Work.ORHughesFree.SkewLaurentSeries.exists_inverse_of_vanishesBelow_of_coeff_isUnit
import Submission.Work.ORHughesFree.SkewLaurentSeries.exists_least_nonzero_coeff

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.ORHughesFree.Section6

open Work.ORHughesFree

variable {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]

/-- **The "all coefficients are units" case of [JZLA20, Theorem 6.1].** -/
theorem isUnit_of_unitSeries
    (φ : MonoidAlgebra K G →+* U) [Nontrivial U] {H : Subgroup G}
    {P : Type} [Ring P] {DN : Subring P} [MulSemiringAction (Multiplicative ℤ) ↥DN]
    (data : Prop51Data (Kˣ × H) P DN)
    (e : ↥(divisionClosure (Set.range (φ.comp (inducedMapRing (K := K) H)))) ≃+* ↥data.DH)
    (aH : ↥(divisionClosure (Set.range (φ.comp (inducedMapRing (K := K) H)))))
    (haH0 : aH ≠ 0)
    (hInv : Prop51Inv data (e aH))
    (α : RatU (Kˣ × H))
    (hincl : inclSub φ H aH = (Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H)
        (ratUnitsTimesEquiv (K := K) H α)))
    (hb_ne : (e aH : P) ≠ 0)
    (f : SkewLaurentSeries ↥DN)
    (hf : data.laurentEmbed f = (e aH : P))
    (hbound : ∀ k : ℤ, Tree.le (data.treeH (data.coeffToP (f.1 k))) (data.treeH (e aH)))
    (hnoAtt : ∀ k : ℤ, f.1 k ≠ 0 → data.treeH (data.coeffToP (f.1 k)) ≠ data.treeH (e aH)) :
    IsUnit ((Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H)
        (ratUnitsTimesEquiv (K := K) H α))) := by
  have hunit : ∀ f' : SkewLaurentSeries ↥DN,
      data.laurentEmbed f' = (e aH : P) →
      ∀ k : ℤ, f'.1 k ≠ 0 → IsUnit (f'.1 k) := by
    intro f' hf' k hk
    have hff : f' = f := data.laurentEmbed_injective (by rw [hf', hf])
    rw [hff] at hk ⊢
    have hlt : Tree.lt (data.treeH (data.coeffToP (f.1 k))) (data.treeH (e aH)) :=
      Tree.lt_of_le_of_ne (hbound k) (hnoAtt k hk)
    obtain ⟨y, _hy, hy1, hy2⟩ := hInv (data.coeffToP (f.1 k))
      (data.coeffToP_mem _) (fun h0 => hk (Subtype.ext h0)) (Tree.le_of_lt hlt)
      (fun heq => Tree.lt_irrefl (heq ▸ hlt))
    have hP : IsUnit (data.coeffToP (f.1 k)) :=
      ⟨⟨(f.1 k : P), y, hy1, hy2⟩, rfl⟩
    obtain ⟨y', hy', hy1', hy2'⟩ := data.DN_inv_closed (f.1 k) (f.1 k).2 hP
    exact ⟨⟨⟨f.1 k, (f.1 k).2⟩, ⟨y', hy'⟩, Subtype.ext hy1', Subtype.ext hy2'⟩, rfl⟩
  have hf0 : f ≠ 0 := fun h0 => hb_ne (by rw [← hf, h0, map_zero])
  obtain ⟨m, hm', hm⟩ := SkewLaurentSeries.exists_least_nonzero_coeff f hf0
  obtain ⟨g, hfg, hgf, -⟩ :=
    SkewLaurentSeries.exists_inverse_of_vanishesBelow_of_coeff_isUnit hm (hunit f hf m hm')
  have hfgP : (e aH : P) * data.laurentEmbed g = 1 := by
    rw [← hf, ← map_mul, hfg, map_one]
  have hgfP : data.laurentEmbed g * (e aH : P) = 1 := by
    rw [← hf, ← map_mul, hgf, map_one]
  have hunitP : IsUnit (e aH : P) :=
    ⟨⟨(e aH : P), data.laurentEmbed g, hfgP, hgfP⟩, rfl⟩
  obtain ⟨y, hy, hy1⟩ := data.DH_inv_closed (e aH : P) (e aH).2 hunitP
  have hy_eq : y = data.laurentEmbed g := by
    calc y = 1 * y := (one_mul y).symm
      _ = (data.laurentEmbed g * (e aH : P)) * y := by rw [hgfP]
      _ = data.laurentEmbed g * ((e aH : P) * y) := mul_assoc _ _ _
      _ = data.laurentEmbed g * 1 := by rw [hy1]
      _ = data.laurentEmbed g := mul_one _
  have hDH_unit : IsUnit (e aH) :=
    ⟨⟨e aH, ⟨data.laurentEmbed g, hy_eq ▸ hy⟩,
      by apply Subtype.ext; simpa using hfgP,
      by apply Subtype.ext; simpa using hgfP⟩, rfl⟩
  have huH : IsUnit aH := by
    simpa using (hDH_unit.map e.symm.toRingHom)
  rw [← hincl]
  exact huH.map (inclSub φ H)

end Work.ORHughesFree.Section6

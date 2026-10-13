import Mathlib
import Submission.Work.WilC5.stdPart
import Submission.Work.WilC5.Values
import Submission.Work.WilC4.dcl_elementary
import Submission.Work.WilC4.elementary_valBase
import Submission.Work.WilVP.natCastMulInvLtInv

open FirstOrder FirstOrder.Language

namespace Work.WilVP

/-- Every real constant of the language `LRc` lies in every elementary substructure `S ≼ M`:
the constant symbol `r` is a nullary function symbol of `LRc`, so `Substructure.fun_mem` (or,
what is the same, the realization of the constant *term* `constTermL r`) puts its
interpretation `realConst M r` in `S`. -/
theorem realConst_mem {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    (S : WilkiesDesign.CG.LRc.ElementarySubstructure M) (r : ℝ) :
    Work.WilC5.realConst M r ∈ (S : Set M) := by
  have hmem := @Term.realize_mem WilkiesDesign.CG.LRc M _ S.toSubstructure Empty
    (Work.WilC5.constTermL (α := Empty) r) (fun e : Empty => e.elim) (fun a => a.elim)
  rwa [Work.WilC5.realize_constTermL] at hmem

/-- The carrier of an elementary substructure of a model of `TR` is closed under addition:
addition is the interpretation of the binary ring symbol `addFunc` of `LRc`
(`Work.WilC5.addEL_eq_add` identifies the two operations). -/
theorem add_mem {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    [FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TR]
    (S : WilkiesDesign.CG.LRc.ElementarySubstructure M) {x y : M}
    (hx : x ∈ (S : Set M)) (hy : y ∈ (S : Set M)) : x + y ∈ (S : Set M) := by
  have h : Work.WilC5.addEL x y ∈ (S : Set M) :=
    S.toSubstructure.fun_mem (Sum.inl (Sum.inl Ring.addFunc)) ![x, y] (by
      intro i; fin_cases i <;> assumption)
  rwa [Work.WilC5.addEL_eq_add] at h

/-- **Old translates never have a closest one.**  If `p ∈ S` and `c(z-p)` is a unit for some
`c ∈ S`, then some `a ∈ S` is much closer to `z` than `p`:
take `d := c * (z - p)`; `Work.WilC5.stdPart` (with `d` of finite value, from `IsUnitVal`) gives
`r : ℝ` with `d - realConst M r` infinitesimal, and `a := p + realConst M r * c⁻¹`.
Then `c(z - a) = d - realConst M r` is infinitesimal while `|d| ≥ 1/(N₀+1)`, so
`K|z - a| < |z - p|`.  Membership `a ∈ S` (review fix F4) uses: the real constants
`realConst M r` are (the interpretations of the constant symbols of `LRc`, hence) in `S`, and `S`
is closed under the field operations — `Work.WilC4.elementary_valBase` gives `IsValBase (S : Set M)`
(so `S` is closed under multiplication and inversion) and `add_mem` above gives closure under
addition.  Equivalently, by `Work.WilC4.dcl_elementary` (`Work.WilC4.Dcl (S : Set M) ∅ = (S : Set M)`)
it suffices that each ingredient is definable from `S` (e.g. `a` is the unique solution of
`c * (X - p) = realConst M r`). -/
theorem exists_closer_translate {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    [FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TR]
    (S : WilkiesDesign.CG.LRc.ElementarySubstructure M) {z p : M} (hp : p ∈ (S : Set M))
    (hzp : z - p ≠ 0)
    (hold : ∃ c ∈ (S : Set M), WilkiesDesign.CG.IsUnitVal (c * (z - p))) (K : ℕ) :
    ∃ a ∈ (S : Set M), (K : M) * |z - a| < |z - p| := by
  classical
  obtain ⟨c, hcS, N₀, hlow, hhigh⟩ := hold
  -- `S` is closed under the field operations (`elementary_valBase` for `*` and `⁻¹`)
  have hvc : Work.WilC4.IsValBase (S : Set M) := Work.WilC4.elementary_valBase S
  have hinv := hvc.2.1
  have hmul := hvc.2.2
  -- `c ≠ 0`, since `|c * (z - p)| ≥ 1/(N₀ + 1) > 0`
  have hcpos : 0 < |c * (z - p)| := lt_of_lt_of_le (by positivity) hlow
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_mul, abs_zero] at hcpos
    exact lt_irrefl 0 hcpos
  -- the standard part `r` of `d = c * (z - p)`, which is of finite value
  obtain ⟨r, hr⟩ := Work.WilC5.stdPart (M := M) (x := c * (z - p)) ⟨N₀, hhigh⟩
  -- the new translate
  set a : M := p + Work.WilC5.realConst M r * c⁻¹ with ha
  have haS : a ∈ (S : Set M) :=
    add_mem S hp (hmul _ (realConst_mem S r) _ (hinv c hcS hc0))
  refine ⟨a, haS, ?_⟩
  -- `c * (z - a) = c * (z - p) - realConst M r` is infinitesimal
  have hza : z - a = (z - p) - Work.WilC5.realConst M r * c⁻¹ := by
    rw [ha]; ring
  have hcr : c * (Work.WilC5.realConst M r * c⁻¹) = Work.WilC5.realConst M r := by
    rw [← mul_assoc, mul_comm c (Work.WilC5.realConst M r), mul_assoc,
      mul_inv_cancel₀ hc0, mul_one]
  have hca : c * (z - a) = c * (z - p) - Work.WilC5.realConst M r := by
    rw [hza, mul_sub, hcr]
  have hins : Work.WilC5.IsInfinitesimal (c * (z - a)) := by rw [hca]; exact hr
  have hbound : |c * (z - a)| ≤ (((K * (N₀ + 1) : ℕ) : M) + 1)⁻¹ := hins (K * (N₀ + 1))
  -- `K / (K (N₀+1) + 1) < 1/(N₀+1) ≤ |c (z-p)|`
  have hnum : (K : M) * (((K * (N₀ + 1) : ℕ) : M) + 1)⁻¹ < ((N₀ : M) + 1)⁻¹ :=
    natCastMulInvLtInv (K := M) K N₀
  have hless : (K : M) * |c * (z - a)| < |c * (z - p)| := by
    calc (K : M) * |c * (z - a)|
        ≤ (K : M) * (((K * (N₀ + 1) : ℕ) : M) + 1)⁻¹ :=
          mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg K)
      _ < ((N₀ : M) + 1)⁻¹ := hnum
      _ ≤ |c * (z - p)| := hlow
  -- divide the strict inequality by `|c| > 0`
  have hcabs : 0 < |c| := abs_pos.mpr hc0
  have h3 : ((K : M) * |z - a|) * |c| < |z - p| * |c| := by
    calc ((K : M) * |z - a|) * |c| = (K : M) * |c * (z - a)| := by rw [abs_mul]; ring
      _ < |c * (z - p)| := hless
      _ = |z - p| * |c| := by rw [abs_mul]; ring
  exact lt_of_mul_lt_mul_right h3 (le_of_lt hcabs)

end Work.WilVP

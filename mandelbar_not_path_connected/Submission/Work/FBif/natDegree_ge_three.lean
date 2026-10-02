import Mathlib
import Submission.Work.FBif.Glue
import Submission.Work.FBif.Cycle

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FBif

/-- A nonzero polynomial that is divisible by `(X - z̄_j)^2` for `j = 0, 1, 2, 3` has degree at
least `3`.

Only the two factors `j = 0` and `j = 1` are used: since `z₁` has exact period `5`, the points
`z₀ = z₁` and `z₁ = T z₁` are distinct, hence so are their conjugates `z̄₀ ≠ z̄₁`; the two double
factors are then coprime and their product `(X - z̄₀)^2 (X - z̄₁)^2` of degree `4` divides `P`. -/
theorem natDegree_ge_three {P : Polynomial ℂ} {c z₁ : ℂ}
    (hP0 : ¬ (P = 0)) (hper : (LeanEval.ComplexAnalysis.Tantibar c)^[5] z₁ = z₁)
    (hne : ∀ k ∈ Finset.Ioo 0 5, (LeanEval.ComplexAnalysis.Tantibar c)^[k] z₁ ≠ z₁)
    (hdiv : ∀ j : ℕ, j ≤ 3 →
      (Polynomial.X - Polynomial.C (star (Work.FBif.cyclePt c z₁ j)))^2 ∣ P) :
    3 ≤ P.natDegree := by
  -- The two conjugate cycle points `z̄₀`, `z̄₁` are distinct.
  set a : ℂ := star (cyclePt c z₁ 0) with ha
  set b : ℂ := star (cyclePt c z₁ 1) with hb
  have hab : a ≠ b := by
    intro h
    have h' : cyclePt c z₁ 0 = cyclePt c z₁ 1 := star_injective h
    exact cyclePt_ne_of_lt (i := 0) (j := 1) (by norm_num) (by norm_num) hper hne h'
  -- The corresponding double factors both divide `P`.
  have h0 : (Polynomial.X - Polynomial.C a)^2 ∣ P := by
    have := hdiv 0 (by norm_num)
    simpa [ha] using this
  have h1 : (Polynomial.X - Polynomial.C b)^2 ∣ P := by
    have := hdiv 1 (by norm_num)
    simpa [hb] using this
  -- Distinct linear factors are coprime, so the two double factors are coprime, and their
  -- product divides `P`.
  have hcop : IsCoprime ((Polynomial.X - Polynomial.C a)^2)
      ((Polynomial.X - Polynomial.C b)^2) :=
    (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hab))).pow
  have hprod : (Polynomial.X - Polynomial.C a)^2 * (Polynomial.X - Polynomial.C b)^2 ∣ P :=
    hcop.mul_dvd h0 h1
  -- Read the product as the product of `(X - C ·)` over the multiset `{a, a, b, b}`.
  set s : Multiset ℂ := Multiset.replicate 2 a + Multiset.replicate 2 b with hs_def
  have hmap : (s.map (fun x : ℂ => Polynomial.X - Polynomial.C x)).prod =
      (Polynomial.X - Polynomial.C a)^2 * (Polynomial.X - Polynomial.C b)^2 := by
    rw [hs_def]
    simp only [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate, Multiset.prod_replicate]
  -- Hence `{a, a, b, b}` embeds into the root multiset of `P`, which has at most `natDegree P`
  -- elements.
  have hle : s ≤ P.roots :=
    (Multiset.prod_X_sub_C_dvd_iff_le_roots hP0 s).mp (hmap.symm ▸ hprod)
  have hcard : s.card ≤ P.natDegree :=
    (Multiset.card_le_card hle).trans (Polynomial.card_roots' P)
  have hs4 : s.card = 4 := by simp [hs_def]
  omega

end Work.FBif

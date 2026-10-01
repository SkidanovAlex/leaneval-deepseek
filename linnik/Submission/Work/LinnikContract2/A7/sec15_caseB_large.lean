/-
# §15 — Case B, large `λ₁` (`λ₁ ≥ 43/40`): the crude global box bound

This is the branch of the area-7 assembly in which the numbered zero `ρ₁` of HB §6 is
**large**: `λ₁ = λ(ρ₁) ≥ 43/40`.  In that regime the §15 refinement (`core15`, the `C`-function
and the Table 13 counting) is not needed: every character of `Aset q R` has a zero in the working
region `|Im| ≤ 1`, its least zero-parameter `λ_χ` dominates a working-region minimiser `λ*`, and
`Φ/w` and `e^{-aλ}/w` are antitone, so each term is bounded by a constant times `w(λ_χ)` and the
whole sum by `(9/100)(9968/10000) + (9/100)η·1000` using only `(D1)`
`Σ w(λ_χ) ≤ 67/6 + εw`.  This is exactly round 1's `Work.A7.sec15_crude` ("Region V"), which
consumes a *round-1* minimal pair (`IsMin1N`, i.e. minimality over the working region).

## Why `IsMin1` (round 2) plus `hnarrow` supplies a round-1 pair

Round 1's objects are definitional copies in round 2 (`LinnikContract2.Bridge`), so the only
genuinely different hypothesis is `IsMin1`: round 2's is minimality over the *wide* region
`|Im| ≤ 10`.  The extra hypothesis `hnarrow` of this lemma provides a pair `(χ₀,ρ₀)` with
`IsMin1N χ₀ ρ₀` — i.e. a round-1 minimal pair — and:

* `(χ₀,ρ₀)` is a wide zero, so wide minimality of `ρ₁` gives `λ(ρ₀) ≥ λ(ρ₁) ≥ 43/40`; hence
  `(χ₀,ρ₀)` is a round-1 minimal pair with parameter `≥ 43/40`, precisely the input of
  `sec15_crude`.
-/
import Mathlib
import Submission.Work.LinnikContract2.Defs
import Submission.Work.LinnikContract2.API
import Submission.Work.LinnikContract2.Areas
import Submission.Work.A7.sec15_uniform
import Submission.Work.LinnikAreas.A7.WBox

namespace Work.LinnikContract2.A7

set_option linter.unusedVariables false

theorem sec15_caseB_large {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw : ℝ}
    {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ Work.LinnikContract2.lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hmin : Work.LinnikContract2.IsMin1 χ₁ ρ₁) (h43 : (43:ℝ)/40 ≤ Work.LinnikContract2.lamOf q ρ₁)
    (hnarrow : ∃ (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ), Work.LinnikContract2.IsMin1N χ₀ ρ₀)
    (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, Work.LinnikContract2.IsZ χ ρ ∧ Work.LinnikContract2.lamOf q ρ ≤ Work.LinnikContract2.lamMax q)
    (hD1 : ∑ χ ∈ hS, Work.LinnikContract2.wHB (Work.LinnikContract2.lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, Work.LinnikContract2.IsZ χ ρ → lam' ≤ Work.LinnikContract2.lamOf q ρ) →
        Work.LinnikContract2.boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Work.LinnikContract2.Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract2.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract2.IsZW χ ρ → e.2.1 ≤ Work.LinnikContract2.lamOf q ρ) →
        Work.LinnikContract2.Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Work.LinnikAreas.A7.Aset q R, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
      ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  -- the narrow (`IsMin1N`) minimiser is a round-1 minimal pair (the objects are definitional
  -- copies in round 2, `LinnikContract2.Bridge`)
  obtain ⟨χ₀, ρ₀, hmin0⟩ := hnarrow
  have hminN : Work.LinnikContract.IsMin1 χ₀ ρ₀ := hmin0
  -- it is a zero of height `≤ 1 ≤ 50`, so wide minimality of `ρ₁` bounds `λ(ρ₀)` from below
  have hZW : Work.LinnikContract2.IsZH 50 χ₀ ρ₀ :=
    Work.LinnikContract2.isZH_mono (by norm_num) hmin0.1
  have hle : Work.LinnikContract2.lamOf q ρ₁ ≤ Work.LinnikContract2.lamOf q ρ₀ :=
    hmin.2 χ₀ ρ₀ hZW
  have h43' : (43:ℝ)/40 ≤ Work.LinnikContract.lamOf q ρ₀ := le_trans h43 hle
  -- round 1's "Region V" bound
  exact Work.A7.sec15_crude (q := q) (R := R) (η := η) (εw := εw)
    (lam₁ := Work.LinnikContract.lamOf q ρ₀) (χ₁ := χ₀) (ρ₁ := ρ₀)
    hq hR hRlog hRmax hη hεw hεw1 hminN rfl h43' hS hSiff hD1 hPC

end Work.LinnikContract2.A7

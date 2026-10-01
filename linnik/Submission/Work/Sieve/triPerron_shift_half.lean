import Mathlib
import Submission.Work.Sieve.triPerron_shift_gen

namespace Work.Sieve

open DirichletCharacter Complex MeasureTheory intervalIntegral
open scoped Real Topology BigOperators
open Commons.NumberTheory.DirichletCharacter
open Work.LinnikAreas

noncomputable section

/-!
# The Perron contour shift with left edge `1/2 - β`

`Work.Sieve.triPerron_shift_gen` proves the contour shift for the rectangle
`[σ₀ - β, 1] × [-T, T]` with `1/2 < σ₀ < 1`.  The present file treats the endpoint case
`σ₀ = 1/2`, whose left edge `1/2 - β` lies exactly on the boundary of the region
`Re s > 1/2 - β` used there.

The only input of that proof which used `1/2 < σ₀` is the holomorphy of the regularised
remainder `dslope (triPerronM ψ β x) (1 - β)` on the (now wider) rectangle.  But `triPerronM`
is holomorphic on the whole plane minus the single point `s = -1` — it is a product of the
entire functions `ζ₁(·+β)`, `dslope(L(ψ,·+β),0,·)`, `x^·` divided by `s+1` — and the rectangle
`[1/2 - β, 1] × [-T, T]` avoids `-1` because `1/2 - β > -1`.  Hence the same argument applies
verbatim, with `A = 1/2`.
-/

/-- `triPerronM ψ β x` is complex differentiable on `ℂ \ {-1}`: it is the product of the
entire functions `ζ₁(·+β)`, `dslope(L(ψ,·+β),0,·)` (entire for `ψ ≠ 1`) and `x^·`, divided by
`s + 1`. -/
lemma differentiableOn_triPerronM_ne_neg_one {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N)
    (hψ : ψ ≠ 1) {β x : ℝ} (hx : 0 < x) :
    DifferentiableOn ℂ (triPerronM ψ β x) {s : ℂ | s ≠ -1} := by
  have hne : ∀ s ∈ {s : ℂ | s ≠ -1}, s + 1 ≠ 0 := by
    intro s hs
    simp only [Set.mem_ofPred_eq] at hs
    intro h
    exact hs (by linear_combination h)
  have hA : Differentiable ℂ (fun s : ℂ => riemannZeta₁ (s + (β:ℂ))) :=
    differentiable_riemannZeta₁.comp (differentiable_id.add_const _)
  have hB : Differentiable ℂ
      (fun s : ℂ => dslope (fun t : ℂ => DirichletCharacter.LFunction ψ (t + (β:ℂ))) 0 s) :=
    differentiableOn_univ.mp ((Complex.differentiableOn_dslope (s := Set.univ) (c := 0)
      (f := fun t : ℂ => DirichletCharacter.LFunction ψ (t + (β:ℂ))) Filter.univ_mem).mpr
        ((DirichletCharacter.differentiable_LFunction hψ).comp
          (differentiable_id.add_const _)).differentiableOn)
  have hC : Differentiable ℂ (fun s : ℂ => (x:ℂ)^s) :=
    differentiable_id.const_cpow (Or.inl (by exact_mod_cast hx.ne'))
  have hnum : DifferentiableOn ℂ (fun s : ℂ => riemannZeta₁ (s + (β:ℂ))
      * dslope (fun t : ℂ => DirichletCharacter.LFunction ψ (t + (β:ℂ))) 0 s
      * (x:ℂ)^s) {s : ℂ | s ≠ -1} := ((hA.mul hB).mul hC).differentiableOn
  have hden : DifferentiableOn ℂ (fun s : ℂ => s + 1) {s : ℂ | s ≠ -1} :=
    differentiable_id.differentiableOn.add_const 1
  exact (hnum.div hden hne).congr (fun s _ => by simp only [triPerronM, Pi.div_apply])

/-- `dslope (triPerronM ψ β x) (triPerronU β)` is complex differentiable on the closed
rectangle `[A - β, 1] × [-T, T]` for every `A ≥ 1/2` (and `β < 1`, so that the rectangle
stays away from the pole `s = -1`).  This is `differentiableOn_dslope_triPerronM_gen` with the
strict inequality `1/2 < A` weakened to `1/2 ≤ A`. -/
lemma differentiableOn_dslope_triPerronM_le {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N)
    (hψ : ψ ≠ 1) {β x T A : ℝ} (hA : 1 / 2 ≤ A) (hβ1 : β < 1) (hx : 0 < x) (hT : 0 < T) :
    DifferentiableOn ℂ (dslope (triPerronM ψ β x) (triPerronU β))
      (Complex.reProdIm (Set.Icc (A - β) 1) (Set.Icc (-T) T)) := by
  set V : Set ℂ := {s : ℂ | s ≠ -1} with hVdef
  have hVopen : IsOpen V := by rw [hVdef]; exact isOpen_ne
  have hsub : Complex.reProdIm (Set.Icc (A - β) 1) (Set.Icc (-T) T) ⊆ V := by
    intro s hs
    rw [hVdef]
    simp only [Set.mem_ofPred_eq]
    have hre : (A - β) ≤ s.re := (Complex.mem_reProdIm.mp hs).1.1
    intro h
    have h0 : s.re = -1 := by
      have := congrArg Complex.re h; simp at this; linarith
    linarith [hA]
  have hcV : triPerronU β ∈ V := by
    rw [hVdef]; simp only [Set.mem_ofPred_eq]
    intro h
    have := congrArg Complex.re h
    rw [triPerronU_re] at this
    simp at this
    linarith
  have hfV : DifferentiableOn ℂ (triPerronM ψ β x) V := by
    rw [hVdef]; exact differentiableOn_triPerronM_ne_neg_one ψ hψ hx
  exact differentiableOn_dslope_of_isOpen_mem hVopen hsub hcV hfV

/-- The Perron contour shift for the rectangle `[1/2 - β, 1] × [-T, T]`. -/
theorem triPerron_shift_half {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1)
    {β x T : ℝ} (hβ0 : 1/2 < β) (hβ1 : β < 1) (hx : 0 < x) (hT : 0 < T)
    (hL0 : DirichletCharacter.LFunction ψ (β : ℂ) = 0) :
    (1 / (2 * Real.pi)) *
        (∫ y in (-T)..T, Work.LinnikAreas.triFun ψ β x (1 + (y : ℂ) * Complex.I))
      = Work.LinnikAreas.triPerronRes ψ β x
        + (1 / (2 * Real.pi)) *
            (∫ y in (-T)..T, Work.LinnikAreas.triFun ψ β x ((1/2 - β : ℝ) + (y : ℂ) * Complex.I))
        + (1 / (2 * Real.pi * Complex.I)) *
            ((∫ u in ((1/2 - β : ℝ))..1, Work.LinnikAreas.triFun ψ β x ((u : ℂ) + T * Complex.I))
              - (∫ u in ((1/2 - β : ℝ))..1, Work.LinnikAreas.triFun ψ β x ((u : ℂ) - T * Complex.I))) := by
  have hβpos : 0 < β := by linarith
  -- the rectangle `z = (1/2-β) - iT`, `w = 1 + iT`
  set z : ℂ := (((1/2 - β : ℝ)) : ℂ) - (T : ℂ) * Complex.I with hzdef
  set w : ℂ := (1 : ℂ) + (T : ℂ) * Complex.I with hwdef
  have hzre : z.re = 1/2 - β := by rw [hzdef]; simp
  have hzim : z.im = -T := by rw [hzdef]; simp
  have hwre : w.re = 1 := by rw [hwdef]; simp
  have hwim : w.im = T := by rw [hwdef]; simp
  have hc1 : (1/2 - β) < 1 := by linarith
  have hTm : -T < T := by linarith
  have hzre' : z.re < w.re := by rw [hzre, hwre]; linarith
  have hzim' : z.im < w.im := by rw [hzim, hwim]; linarith
  have huin : z.re < (triPerronU β).re ∧ (triPerronU β).re < w.re ∧
      z.im < (triPerronU β).im ∧ (triPerronU β).im < w.im := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [hzre, hwre, hzim, hwim, triPerronU_re, triPerronU_im] <;> linarith
  -- holomorphy of the regularised integrand on the closed rectangle
  have hGdiff : DifferentiableOn ℂ (dslope (triPerronM ψ β x) (triPerronU β))
      (rectSet z w) := by
    have h := differentiableOn_dslope_triPerronM_le (N := N) ψ hψ (β := β) (x := x) (T := T)
      (A := 1/2) le_rfl hβ1 hx hT
    have hset : Complex.reProdIm (Set.Icc (1/2 - β : ℝ) 1) (Set.Icc (-T) T) = rectSet z w := by
      unfold rectSet
      rw [hzre, hwre, hzim, hwim, Set.uIcc_of_le hc1.le, Set.uIcc_of_le hTm.le]
    rwa [hset] at h
  -- pointwise residue decomposition off `s = 0`
  have hbd : ∀ s ∈ rectBoundary z w, s ≠ 0 →
      triFun ψ β x s = triPerronRes ψ β x / (s - triPerronU β)
        + dslope (triPerronM ψ β x) (triPerronU β) s := by
    intro s hs hs0
    have hsu : s ≠ triPerronU β := ne_of_mem_rectBoundary_of_inside huin hs
    have hsm1 : s + 1 ≠ 0 := by
      intro h
      have hsV := rectBoundary_subset_rectSet hzre' hzim' hs
      have hre : s.re ∈ Set.uIcc z.re w.re := (Complex.mem_reProdIm.mp hsV).1
      rw [hzre, hwre, Set.uIcc_of_le hc1.le] at hre
      have h1 : s.re = -1 := by
        have := congrArg Complex.re h
        simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this
        linarith
      linarith [hre.1]
    exact triFun_residue_decomp ψ hψ hβ1 hx hL0 hs0 hsu hsm1
  -- the rectangle integral of `triFun` picks up exactly the residue at `1-β`
  have hrect : rectInt z w (triFun ψ β x)
      = triPerronRes ψ β x * (2 * (Real.pi : ℂ) * Complex.I) := by
    have hcontf : ContinuousOn (fun s : ℂ => triPerronRes ψ β x / (s - triPerronU β))
        {s : ℂ | s ≠ triPerronU β} :=
      continuousOn_const.div (by fun_prop) (fun s hs => sub_ne_zero.mpr hs)
    obtain ⟨a1, a2, a3, a4⟩ := edgeIntegrable_of_continuousOn_ne huin hcontf
    obtain ⟨b1, b2, b3, b4⟩ := edgeIntegrable_of_continuousOn hGdiff.continuousOn
    rw [rectInt_congr_boundary_off_zero hbd,
      rectInt_add'' a1 b1 a2 b2 a3 b3 a4 b4,
      rectInt_const_div_sub_inside (triPerronRes ψ β x) hzre' hzim' huin,
      rectInt_eq_zero_of_differentiableOn hGdiff, add_zero]
  -- the four sides, in the shapes used by the statement
  set P : ℂ := ∫ u in ((1/2 - β : ℝ))..1, triFun ψ β x ((u : ℂ) - T * Complex.I) with hP
  set Q : ℂ := ∫ u in ((1/2 - β : ℝ))..1, triFun ψ β x ((u : ℂ) + T * Complex.I) with hQ
  set R : ℂ := ∫ y in (-T)..T, triFun ψ β x (1 + (y : ℂ) * Complex.I) with hR
  set S : ℂ := ∫ y in (-T)..T, triFun ψ β x ((((1/2 - β : ℝ)) : ℂ) + (y : ℂ) * Complex.I) with hS
  have hrel' : P - Q + Complex.I * R - Complex.I * S
      = triPerronRes ψ β x * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [hP, hQ, hR, hS, ← rectInt_expand_gen z w (σ₀ := 1/2) (β := β) (T := T)
      hzre hzim hwre hwim (triFun ψ β x)]
    exact hrect
  have hrel : P - Q + Complex.I * (R - S)
      = triPerronRes ψ β x * (2 * (Real.pi : ℂ) * Complex.I) := by
    linear_combination hrel'
  -- elementary algebra: solve the rectangle identity for the top edge integral
  have hgoal : (1 / (2 * (Real.pi : ℂ))) * R
      = triPerronRes ψ β x + (1 / (2 * (Real.pi : ℂ))) * S
        + (1 / (2 * (Real.pi : ℂ) * Complex.I)) * (Q - P) :=
    perronShift_topEdge_solve hrel
  simpa [hP, hQ, hR, hS] using hgoal

end

end Work.Sieve

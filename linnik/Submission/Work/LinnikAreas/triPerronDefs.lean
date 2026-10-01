import Mathlib
import Submission.Work.LinnikAreas.LoneLowerDefs

/-!
# Vocabulary for the Perron contour shift `Work.LinnikAreas.triPerron_shift`

The target identity

`(1/2π) ∫_{-T}^{T} triFun ψ β x (1+it) dt
   = Res + (1/2π) ∫_{-T}^{T} triFun ψ β x (5/8-β+it) dt
     + (1/2πi) (∫_{5/8-β}^{1} triFun ψ β x (u+iT) du - ∫_{5/8-β}^{1} triFun ψ β x (u-iT) du)`

is the statement that the contour integral of `F := triFun ψ β x` over the boundary of the
rectangle `[5/8-β, 1] × [-T, T]` picks up the single residue at `s = 1 - β`.

Here we fix the vocabulary:

* `triPerronZ β T = (5/8-β) - iT` and `triPerronW T = 1 + iT` are the two corners;
* `triPerronU β = 1 - β` is the pole of `F` (from `ζ(s+β)`), which lies strictly inside;
* `triPerronRes ψ β x = L(1,ψ) x^{1-β}/((1-β)(2-β))` is the residue;
* `triPerronM ψ β x s = ζ₁(s+β) · ((L(ψ,·+β) - L(ψ,β))/(s)) · x^s / (s+1)` is the *holomorphic*
  remainder: since `L(ψ,β) = 0` (the exceptional zero hypothesis), writing
  `ζ(s+β) = (s-(1-β))⁻¹ ζ₁(s+β)` and `L(ψ,s+β) = s · dslope(L(ψ,·+β),0,s)` turns
  `F = M/(s-(1-β))` into `F = M(1-β)/(s-(1-β)) + dslope(M,1-β)`, with `M(1-β) = triPerronRes`.
-/

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped BigOperators

noncomputable section

/-- Bottom-left corner of the contour rectangle: `s = (5/8 - β) - iT`. -/
def triPerronZ (β T : ℝ) : ℂ := ((5 / 8 - β : ℝ) : ℂ) - (T : ℂ) * Complex.I

/-- Top-right corner of the contour rectangle: `s = 1 + iT`. -/
def triPerronW (T : ℝ) : ℂ := (1 : ℂ) + (T : ℂ) * Complex.I

/-- The location `1 - β` of the simple pole of the integrand. -/
def triPerronU (β : ℝ) : ℂ := ((1 - β : ℝ) : ℂ)

/-- The residue of `triFun ψ β x` at `s = 1 - β`. -/
def triPerronRes {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (β x : ℝ) : ℂ :=
  DirichletCharacter.LFunction ψ 1 * (x : ℂ) ^ (((1 - β : ℝ)) : ℂ)
    / ((((1 - β : ℝ)) : ℂ) * (((2 - β : ℝ)) : ℂ))

/-- The holomorphic part of the integrand: `ζ₁(s+β)·dslope(L(ψ,·+β),0,s)·x^s/(s+1)`. -/
def triPerronM {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (β x : ℝ) (s : ℂ) : ℂ :=
  riemannZeta₁ (s + (β : ℂ))
    * dslope (fun t : ℂ => DirichletCharacter.LFunction ψ (t + (β : ℂ))) 0 s
    * (x : ℂ) ^ s / (s + 1)

@[simp] lemma triPerronZ_re (β T : ℝ) : (triPerronZ β T).re = 5 / 8 - β := by
  simp [triPerronZ]

@[simp] lemma triPerronZ_im (β T : ℝ) : (triPerronZ β T).im = -T := by
  simp [triPerronZ]

@[simp] lemma triPerronW_re (T : ℝ) : (triPerronW T).re = 1 := by
  simp [triPerronW]

@[simp] lemma triPerronW_im (T : ℝ) : (triPerronW T).im = T := by
  simp [triPerronW]

@[simp] lemma triPerronU_re (β : ℝ) : (triPerronU β).re = 1 - β := by
  simp [triPerronU]

@[simp] lemma triPerronU_im (β : ℝ) : (triPerronU β).im = 0 := by
  simp [triPerronU]

end

end Work.LinnikAreas

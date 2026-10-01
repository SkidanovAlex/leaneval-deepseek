import Mathlib
import Submission.Work.LinnikAreas.triPerronDefs

/-!
# Holomorphy of the `dslope` remainder `triPerronM`

In `triPerron_shift` the integrand `triFun ψ β x` is split at its simple pole `s = 1 - β = triPerronU β`
into a residue term plus the holomorphic remainder
`triPerronM ψ β x s = ζ₁(s+β) · dslope(L(ψ,·+β),0,s) · x^s / (s+1)`.

For the contour shift one needs that this remainder -- and hence the difference quotient
`dslope (triPerronM ψ β x) (triPerronU β)` that isolates its value at the pole -- is complex
differentiable on the closed rectangle `[5/8-β, 1] × [-T, T]`.  This file proves that.

The proof is organised as follows.

* `differentiableOn_dslope_of_isOpen_mem`: a general (Mathlib-level) fact.  If `V` is an open set
  containing `c` and `f` is complex differentiable on `V`, then for **every** `s ⊆ V` the function
  `dslope f c` is complex differentiable on `s`.  Indeed `Complex.differentiableOn_dslope` upgrades
  `DifferentiableOn ℂ f V` to `DifferentiableOn ℂ (dslope f c) V` (here `V` is a neighbourhood of
  the base point `c`), and off `c` this is just the equivalence
  `differentiableWithinAt_dslope_of_ne`.  This removes all case distinctions about whether the base
  point lies on the boundary of the rectangle.

* `triPerronM` is a product of the entire functions `ζ₁(·+β)`, `dslope(L(ψ,·+β),0,·)` (entire
  because `L(ψ,·)` is, for `ψ ≠ 1`) and `x^(·)`, divided by `s+1`; it is therefore holomorphic on
  the open rectangle `V = (1/2-β, 2-β) × (-T-1, T+1)`, which contains both the closed rectangle
  `[5/8-β, 1] × [-T, T]` and the base point `1 - β`, and which avoids the pole `s = -1` because
  `re s > 1/2 - β > -1`.
-/

namespace Work.LinnikAreas

open Complex DirichletCharacter

noncomputable section

/-- If `f` is complex differentiable on an open set `V` containing `c`, then the difference
quotient `dslope f c` (which equals `deriv f c` at `c`) is complex differentiable on any subset
of `V`. -/
lemma differentiableOn_dslope_of_isOpen_mem {f : ℂ → ℂ} {V s : Set ℂ} {c : ℂ}
    (hV : IsOpen V) (hsub : s ⊆ V) (hc : c ∈ V) (hf : DifferentiableOn ℂ f V) :
    DifferentiableOn ℂ (dslope f c) s := by
  have hds : DifferentiableOn ℂ (dslope f c) V :=
    (Complex.differentiableOn_dslope (f := f) (c := c) (s := V) (hV.mem_nhds hc)).mpr hf
  intro p hp
  by_cases hpc : p = c
  · rw [hpc]
    exact (hds.differentiableAt (hV.mem_nhds hc)).differentiableWithinAt
  · exact (differentiableWithinAt_dslope_of_ne (f := f) (a := c) (s := s) hpc).mpr
      ((hf.mono hsub) p hp)

/-- `triPerronM ψ β x` is complex differentiable on the open rectangle
`(1/2-β, 2-β) × (-T-1, T+1)` (for `β < 1`, so that this rectangle avoids the pole `s = -1`). -/
lemma differentiableOn_triPerronM {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N)
    (hψ : ψ ≠ 1) {β x T : ℝ} (hβ1 : β < 1) (hx : 0 < x) :
    DifferentiableOn ℂ (triPerronM ψ β x)
      (Complex.reProdIm (Set.Ioo (1 / 2 - β) (2 - β)) (Set.Ioo (-T - 1) (T + 1))) := by
  set V : Set ℂ := Complex.reProdIm (Set.Ioo (1 / 2 - β) (2 - β)) (Set.Ioo (-T - 1) (T + 1))
    with hVdef
  have hne : ∀ s ∈ V, s + 1 ≠ 0 := by
    intro s hs h
    rw [hVdef] at hs
    have hre : (1:ℝ)/2 - β < s.re := (Complex.mem_reProdIm.mp hs).1.1
    have h2 : (s + 1).re = 0 := by rw [h]; simp
    rw [Complex.add_re, Complex.one_re] at h2
    linarith
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
      * (x:ℂ)^s) V := ((hA.mul hB).mul hC).differentiableOn
  have hden : DifferentiableOn ℂ (fun s : ℂ => s + 1) V :=
    differentiable_id.differentiableOn.add_const 1
  exact (hnum.div hden hne).congr
    (fun s _ => by simp only [triPerronM, Pi.div_apply])

theorem triPerron_dslope_diff {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N)
    (hψ : ψ ≠ 1) {β x T : ℝ} (hβ1 : β < 1) (hx : 0 < x) (hT : 0 < T) :
    DifferentiableOn ℂ (dslope (triPerronM ψ β x) (triPerronU β))
      (Complex.reProdIm (Set.Icc (5 / 8 - β) 1) (Set.Icc (-T) T)) := by
  set R : Set ℂ := Complex.reProdIm (Set.Icc (5 / 8 - β) 1) (Set.Icc (-T) T) with hRdef
  set V : Set ℂ := Complex.reProdIm (Set.Ioo (1 / 2 - β) (2 - β)) (Set.Ioo (-T - 1) (T + 1))
    with hVdef
  have hRV : R ⊆ V := by
    intro s hs
    rw [hRdef] at hs
    rw [hVdef]
    obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hs
    exact Complex.mem_reProdIm.mpr
      ⟨⟨by linarith [hre.1], by linarith [hre.2, hβ1]⟩,
       ⟨by linarith [him.1], by linarith [him.2]⟩⟩
  have hVopen : IsOpen V := by
    rw [hVdef]; exact isOpen_Ioo.reProdIm isOpen_Ioo
  have hcV : triPerronU β ∈ V := by
    rw [hVdef]
    exact Complex.mem_reProdIm.mpr
      ⟨⟨by rw [triPerronU_re]; linarith, by rw [triPerronU_re]; linarith⟩,
       ⟨by rw [triPerronU_im]; linarith, by rw [triPerronU_im]; linarith⟩⟩
  have hfV : DifferentiableOn ℂ (triPerronM ψ β x) V := by
    rw [hVdef]
    exact differentiableOn_triPerronM ψ hψ hβ1 hx
  exact differentiableOn_dslope_of_isOpen_mem hVopen hRV hcV hfV

end

end Work.LinnikAreas

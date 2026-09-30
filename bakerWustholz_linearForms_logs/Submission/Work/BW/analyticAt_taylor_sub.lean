import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Taylor expansion at a point of `ℂ`: if `f` is analytic at `p` then its Taylor polynomial of
order `n` approximates `f` up to `(z - p) ^ n` times a function analytic at `p`. (Shift the Mathlib
lemma `AnalyticAt.exists_eq_sum_add_pow_mul`, which is the same statement at `0`, along `z ↦ z - p`.) -/
theorem analyticAt_taylor_sub {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p) (n : ℕ) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F p ∧ ∀ z : ℂ,
      f z = (∑ i ∈ Finset.range n, (z - p) ^ i / (i.factorial : ℂ) * iteratedDeriv i f p) +
        (z - p) ^ n * F z := by
  -- Shift `f` to the origin: `w ↦ f (p + w)` is analytic at `0`.
  have hg : AnalyticAt ℂ (fun w : ℂ ↦ f (p + w)) 0 := by
    have h1 : AnalyticAt ℂ (fun w : ℂ ↦ p + w) 0 := by fun_prop
    have h2 := AnalyticAt.comp (g := f) (f := fun w : ℂ ↦ p + w) (x := 0)
      (by simpa using hf) h1
    simpa [Function.comp_def] using h2
  -- Mathlib's Taylor theorem at the origin for `g`.
  obtain ⟨F₀, hF₀a, hF₀⟩ := hg.exists_eq_sum_add_pow_mul n
  refine ⟨fun z : ℂ ↦ F₀ (z - p), ?_, ?_⟩
  · -- `z ↦ F₀ (z - p)` is analytic at `p`.
    have hshift : AnalyticAt ℂ (fun z : ℂ ↦ z - p) p := by fun_prop
    have h2 := AnalyticAt.comp (g := F₀) (f := fun z : ℂ ↦ z - p) (x := p)
      (by simpa using hF₀a) hshift
    simpa [Function.comp_def] using h2
  · intro z
    have hz := hF₀ (z - p)
    -- The iterated derivatives of the shifted function are those of `f` at `p`.
    have hder : ∀ i, iteratedDeriv i (fun w : ℂ ↦ f (p + w)) 0 = iteratedDeriv i f p :=
      fun i => by
        simpa using congrFun (iteratedDeriv_comp_const_add (𝕜 := ℂ) (F := ℂ) i f p) 0
    simp only [hder] at hz
    have h1 : p + (z - p) = z := by ring
    rw [h1] at hz
    simpa [smul_eq_mul] using hz

end Work.BW

import Mathlib.MeasureTheory.Integral.DivergenceTheorem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn

set_option linter.unusedVariables false in
theorem box_divergence_identity {F : (Fin 3 → ℝ) → Fin 3 → ℝ}
    {F' : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)}
    (a b : Fin 3 → ℝ) (hle : a ≤ b) (hlt : ∀ i, a i < b i)
    (hgood : ∀ x ∈ Set.pi Set.univ (fun i => Set.Ioo (a i) (b i)), x 0 ≠ 0 ∧ x 2 ≠ 0)
    (hcont : ContinuousOn F (Set.Icc a b))
    (hdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt F (F' x) x)
    (hint : MeasureTheory.IntegrableOn (fun x => ∑ i, F' x (Pi.single i 1) i) (Set.Icc a b)) :
    (∫ x in Set.Icc a b, ∑ i, F' x (Pi.single i 1) i) =
      ∑ i : Fin 3,
        ((∫ x in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (i.insertNth (b i) x) i) -
          ∫ x in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (i.insertNth (a i) x) i) := by
  -- This is Mathlib's Bochner divergence theorem on the box `[a, b]`, with `n = 2` and the
  -- empty exception set: `hgood` says that the *interior* of the box meets neither of the two
  -- planes `x 0 = 0`, `x 2 = 0` off which `hdiff` is available, so `F` is differentiable on the
  -- whole interior of `[a, b]`.
  exact MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable (n := 2) a b hle F F'
    (∅ : Set (Fin 3 → ℝ)) Set.countable_empty hcont
    (fun x hx => hdiff x (hgood x hx.1).1 (hgood x hx.1).2) hint

end Work.FTS.PressureOn

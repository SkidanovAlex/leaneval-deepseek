import Mathlib
import Submission.Work.LT.Defs
import Submission.Work.LT.sl3_gap_relT

/-! # Relative property (T) for a column subgroup, finite form

This file records the requested node `Work.LT.sl3_relT_column`.

The statement is a finite form of relative property (T) for
`(SL₂(𝔽_p) ⋉ 𝔽_p², 𝔽_p²)` (the column subgroup `U = {E_ac(s)·E_bc(t)} ≅ (𝔽_p)²`,
normalised by the `SL₂` on the indices `{a,b}`), inside `SL₃(ℤ/p)` acting by left translation
`(L_u f)(g) = f (u * g)`: a function almost invariant under the twelve generators `E_ij(±1)` is
almost invariant under all of `U`, on average, with a constant uniform in the odd prime `p`.

The same statement is proved (sorry-free, `#print axioms` = `propext`, `Classical.choice`,
`Quot.sound`) as `Work.LT.sl3_gap_relT` in `Submission/Work/LT/sl3_gap_relT.lean`, where it is the
"relative (T)" input of the spectral-gap node `sl3_gap`.  The present node is the specialisation of
that theorem; the only difference is that `sl3_gap_relT` also returns the positivity of the
constant, which is not needed here.  (`sl3_gap_relT` is stated through the local abbreviations
`sl3ColDF`/`sl3DF` of `Submission/Work/LT/sl3_gap_defs.lean`; both are definitionally equal to the
sums below.)

Guidance received with the request (kept for the record): the design routed this node through
`mgg_dual_gap`; that lemma turned out to be **false** (its prover found the machine-checked
counterexample `F = 1_{(𝔽_p)²∖{0}}`: both dual transvections are bijections fixing `0`, so this `F`
satisfies `F 0 = 0`, has vanishing Dirichlet energy and `∑F² = p² - 1 > 0`).  The proof actually
used in the workspace replaces it by the "bow-tie" Margulis–Gabber–Galil estimate `mgg_bowtie`
together with the concentration estimate `fourier_concentration` (mass near the two coordinate axes,
coming from the `U`-generators themselves) and the Lipschitz estimate `relT_smooth` for the norm of
the Fourier components under the four dual transvections; see `Submission/Work/LT/sl3_gap_relT.lean`.
-/

namespace Work.LT

/-- **Relative property (T) for a column subgroup, finite form.** The column subgroup
`U = {E_ac(s) E_bc(t)} ≅ (ℤ/p)²` is normalised by the copy of `SL₂` on indices `{a, b}`. A function
that is almost invariant under the 12 generators is almost invariant under all of `U`, on
average, with a constant uniform in the odd prime `p`. -/
theorem sl3_relT_column :
    ∃ K : ℝ, ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c →
      ∀ f : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℝ,
        ∑ s : ZMod p, ∑ t : ZMod p, ∑ g, (f (sl3E p a c s * sl3E p b c t * g) - f g) ^ 2 ≤
          K * (p : ℝ) ^ 2 * ∑ k, ∑ g, (f (sl3Gen p k * g) - f g) ^ 2 := by
  obtain ⟨K, -, hK⟩ := sl3_gap_relT
  exact ⟨K, hK⟩

end Work.LT

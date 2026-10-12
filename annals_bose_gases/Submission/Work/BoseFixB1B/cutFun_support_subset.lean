import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB1B.cutoffDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B

/-- **The product cutoff `cutFun` has its support in the product box.**

`cutFun ((ℓ*d)•u) f g` is the product of the six one-dimensional plateau factors
`f (xᵢ)` and `g ((x − (ℓd)•u)ᵢ)`.  If `f` vanishes for `|t| ≥ ℓ/2` and `g` vanishes
for `|t| ≥ ℓd/2`, then every point where the product is nonzero satisfies
`|xᵢ| < ℓ/2` and `|(x − (ℓd)•u)ᵢ| < ℓd/2`, i.e. lies in the open product of the two
cubes, which is contained in `dlBox ℓ d u = acube ℓ ∩ ((ℓd)•u + acube (ℓd))`.
Since `dlBox ℓ d u` is closed (an intersection of the closed cube `acube ℓ` with the
preimage of `acube (ℓd)` under the continuous translation `x ↦ x − (ℓd)•u`), the
closure of the support — the topological support of `cutFun` — is contained in it.

No positivity of `ℓ` or `d` is needed: for `ℓ ≤ 0` (resp. `ℓd ≤ 0`) the hypothesis
forces `f ≡ 0` (resp. `g ≡ 0`), so `cutFun` vanishes identically and the claim is
vacuous. -/
theorem cutFun_support_subset {ℓ d : ℝ} (u : EuclideanSpace ℝ (Fin 3)) {f g : ℝ → ℝ}
    (hf : ∀ t : ℝ, ℓ / 2 ≤ |t| → f t = 0)
    (hg : ∀ t : ℝ, ℓ * d / 2 ≤ |t| → g t = 0) :
    tsupport (cutFun ((ℓ * d) • u) f g) ⊆ Submission.BoseGases.dlBox ℓ d u := by
  refine closure_minimal (fun x hx => ?_) ?_
  · rw [Function.mem_support] at hx
    rw [Submission.BoseGases.mem_dlBox_iff]
    -- decompose the non-vanishing product into its six factors
    simp only [cutFun, mul_ne_zero_iff] at hx
    obtain ⟨⟨⟨⟨⟨hf0, hf1⟩, hf2⟩, hg0⟩, hg1⟩, hg2⟩ := hx
    have hfx : ∀ m : Fin 3, f (x m) ≠ 0 := by
      intro m; fin_cases m
      · simpa using hf0
      · simpa using hf1
      · simpa using hf2
    have hgy : ∀ m : Fin 3, g ((x - (ℓ * d) • u) m) ≠ 0 := by
      intro m; fin_cases m
      · simpa using hg0
      · simpa using hg1
      · simpa using hg2
    refine ⟨?_, ?_⟩
    · rw [Submission.BoseGases.mem_acube_iff]
      intro m
      have hlt : |x m| < ℓ / 2 := not_le.mp (fun h => hfx m (hf (x m) h))
      have hb := abs_le.mp hlt.le
      simp only [Set.mem_Icc]
      exact ⟨by linarith [hb.1], hb.2⟩
    · rw [Submission.BoseGases.mem_acube_iff]
      intro m
      have hlt : |(x - (ℓ * d) • u) m| < ℓ * d / 2 :=
        not_le.mp (fun h => hgy m (hg ((x - (ℓ * d) • u) m) h))
      have hb := abs_le.mp hlt.le
      simp only [Set.mem_Icc]
      exact ⟨by linarith [hb.1], hb.2⟩
  · unfold Submission.BoseGases.dlBox
    exact (Submission.BoseGases.acube_isClosed ℓ).inter
      ((Submission.BoseGases.acube_isClosed (ℓ * d)).preimage (by fun_prop))

end Work.BoseFixB1B

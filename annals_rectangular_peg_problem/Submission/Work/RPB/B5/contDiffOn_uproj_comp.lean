import Mathlib
import Submission.Work.RPV.V

namespace Work.RPB.B5

open Work.RPV

/-- The reduced coordinate `uproj p = e^{i q₂}(p₁ + i q₁)` is `C^∞` (hence `C¹`) as a function
of the point `p ∈ PS = ℝ⁴`. -/
lemma contDiff_uproj : ContDiff ℝ 1 (fun p : PS => uproj p) := by
  unfold uproj
  have h12 : ContDiff ℝ 1 (fun p : PS => ((p.1.2 : ℝ) : ℂ)) :=
    (ContinuousLinearMap.contDiff Complex.ofRealCLM).comp (contDiff_id.fst.snd)
  have h11 : ContDiff ℝ 1 (fun p : PS => ((p.1.1 : ℝ) : ℂ)) :=
    (ContinuousLinearMap.contDiff Complex.ofRealCLM).comp (contDiff_id.fst.fst)
  have h21 : ContDiff ℝ 1 (fun p : PS => ((p.2.1 : ℝ) : ℂ)) :=
    (ContinuousLinearMap.contDiff Complex.ofRealCLM).comp (contDiff_id.snd.fst)
  exact ((Complex.contDiff_exp.comp (h12.mul contDiff_const))).mul
    (h21.add (h11.mul contDiff_const))

/-- The reduced coordinate `uproj(W τ t (rho τ t σ))` is `C¹` in `(τ,t,σ)` on the slab
`[0,1] × ℝ × (-δ,δ)`, provided `rho` takes values in `(-ε,ε)` there and `W`, `rho` are `C¹` on
`[0,1] × ℝ × (-ε,ε)`. -/
theorem contDiffOn_uproj_comp {W : ℝ → ℝ → ℝ → Work.RPV.PS} {rho : ℝ → ℝ → ℝ → ℝ} {ε δ : ℝ}
    (hδε : δ ≤ ε)
    (hWc : ContDiffOn ℝ 1 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ε) ε))
    (hrhoc : ContDiffOn ℝ 1 (fun z : ℝ × (ℝ × ℝ) => rho z.1 z.2.1 z.2.2)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ε) ε))
    (hbound : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ σ : ℝ, |σ| < δ → ∀ t : ℝ, |rho τ t σ| < ε) :
    ContDiffOn ℝ 1 (fun z : ℝ × (ℝ × ℝ) => Work.RPV.uproj (W z.1 z.2.1 (rho z.1 z.2.1 z.2.2)))
      (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-δ) δ) := by
  -- `uproj ∘ W` is `C¹` on the large slab
  have houter : ContDiffOn ℝ 1 (fun w : ℝ × (ℝ × ℝ) => uproj (W w.1 w.2.1 w.2.2))
      (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ε) ε) :=
    ContDiffOn.comp ((contDiffOn_univ).mpr contDiff_uproj) hWc (fun w _ => Set.mem_univ w)
  -- the small slab sits inside the large one (when the small slab is nonempty)
  have hmapL : Set.MapsTo (fun z : ℝ × (ℝ × ℝ) => (z.1, z.2.1, z.2.2))
      (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-δ) δ)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ε) ε) := by
    intro z hz
    simp only [Set.mem_prod, Set.mem_univ, Set.mem_Ioo, Set.mem_Icc, true_and] at hz ⊢
    exact ⟨hz.1, by linarith [hz.2.1, hz.2.2], by linarith [hz.2.1, hz.2.2]⟩
  -- hence `rho` (composed with the projections) is `C¹` on the small slab
  have hρ : ContDiffOn ℝ 1 (fun z : ℝ × (ℝ × ℝ) => rho z.1 z.2.1 z.2.2)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-δ) δ) :=
    hrhoc.comp (contDiffOn_fst.prodMk (contDiffOn_snd.fst.prodMk contDiffOn_snd.snd)) hmapL
  -- the map `Φ z = (z.1, z.2.1, rho z)` sending the small slab into the large one
  have hΦ : ContDiffOn ℝ 1 (fun z : ℝ × (ℝ × ℝ) => (z.1, z.2.1, rho z.1 z.2.1 z.2.2))
      (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-δ) δ) :=
    contDiffOn_fst.prodMk (contDiffOn_snd.fst.prodMk hρ)
  have hmapΦ : Set.MapsTo (fun z : ℝ × (ℝ × ℝ) => (z.1, z.2.1, rho z.1 z.2.1 z.2.2))
      (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-δ) δ)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ε) ε) := by
    intro z hz
    simp only [Set.mem_prod, Set.mem_univ, Set.mem_Ioo, Set.mem_Icc, true_and] at hz ⊢
    have hb : |rho z.1 z.2.1 z.2.2| < ε :=
      hbound z.1 hz.1 z.2.2 (abs_lt.mpr ⟨hz.2.1, hz.2.2⟩) z.2.1
    exact ⟨hz.1, (abs_lt.mp hb).1, (abs_lt.mp hb).2⟩
  exact houter.comp hΦ hmapΦ

end Work.RPB.B5

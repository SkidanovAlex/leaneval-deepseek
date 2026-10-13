import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.H2.Defs
import Submission.Work.Spaces.WProductRule
import Submission.Work.FTS.LocData.DzIter_mul_smoothQuad
import Submission.Work.FTS.LocData.DthIter_mul_smoothQuad
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Spaces.aesm_HkIntegrand_quad
import Submission.Work.FTS.H2.WPQ.Defs
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.H2.WPQ.Leibniz
import Submission.Work.FTS.H2.WPQ.AesmPkg
import Submission.Work.FTS.H2.WPQ.Final
import Submission.Work.FTS.H2.WPQ.Pointwise
import Submission.Work.H2.WPQ.z_term_le_smoothQuad
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H2.WPQ.hardy_slice_Aang

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

open scoped Real Topology
open Set MeasureTheory Filter

/-- Elgindi's `WProductRule` (tex 1086) in the *interior* class
`Work.FTS.Nonlin.RegQ` of the frozen `Submission/Work/FTS/Vocab.lean` and **without the
hypothesis `VanishTheta` on `g`**: for `f` smooth on the open quadrant with `f ∈ 𝒲^{4,∞}`
(encoded by `WlInfMem α 4 f`, which makes the finitely many suprema of the norm finite) and
`g ∈ ℋ⁴` with `RegQ α 4 g`, one has `fg ∈ ℋ⁴` and
`|fg|_{ℋ⁴} ≤ C/√(γ-1)|f|_{𝒲^{4,∞}}|g|_{ℋ⁴}`, `C` universal.  This is the design document's
`WProdQ` (§3.3 L-N4.5).

The two changes relative to the delivered `Work.Spaces.WProductRule` are those that make the
estimate usable by N4: `Spaces.SmoothNbhd` is `ContDiffOn ℝ ⊤` = analyticity on a neighbourhood
of the closed quadrant (false for `F_*`: `Γ = (sinθcos²θ)^{α/3}` is not analytic at `θ = 0, π/2`),
and `VanishTheta g` is false for the radial functions (`L₁₂(g)`, `FK(g)`) that N4 multiplies by
`g`.  On the `f`-side the hypothesis `Work.FTS.LocData.SmoothQuad f` (interior `C^∞`, which
`F_*` satisfies) supplies the differentiability that the Leibniz expansion and the pointwise
bounds `(z+1)^k|∂_z^k f| ≤ |f|_W`, `|D_θ^j f|·sin(2θ)^{-α/5}/(α+sin2θ) ≤ |f|_W` need (the
delivered proof used `SmoothInt`, i.e. analyticity in `z` across `z = 0` and on the boundary
lines).  The `g`-side `L^∞`-`L²` trade-offs come from `Work.FTS.H2.LinfQ` instead of
`Spaces.sup_mixed_le_H4`. -/
theorem WProdQ : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 →
    Work.FTS.LocData.SmoothQuad f → Work.Spaces.WlInfMem α 4 f →
    Work.FTS.Nonlin.RegQ α 4 g →
    Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.Spaces.HkSq α 4 (fun z θ => f z θ * g z θ)
        ≤ C / (Work.Spaces.gam α - 1) * (Work.Spaces.WlInf α 4 f) ^ 2
          * Work.Spaces.HkSq α 4 g := by
  refine ⟨10 ^ 18, by norm_num, ?_⟩
  intro α f g hα hα1 hf hfm hgreg
  obtain ⟨hgsm, hgm, hbd⟩ := hgreg
  -- the angular-Hardy sup bound for the radial iterates of `g`
  have hhardy : ∀ d ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo 0 (π / 2),
      (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
        ≤ (100 / (Work.Spaces.gam α - 1)) * Work.FTS.H2.WPQ.Aang α g d z :=
    fun d hd z hz θ hθ =>
      Work.H2.WPQ.hardy_slice_Aang (α := α) (g := g) hα hα1 hgsm hgm hbd (d := d) hd
        (Set.mem_Ici.mpr (le_of_lt hz)) hz hθ
  -- the pointwise majorant of the `ℋ⁴`-integrand of the product
  have hpbi : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (fun z θ => f z θ * g z θ) z θ
        ≤ 10 ^ 14 * (Work.Spaces.WlInf α 4 f) ^ 2 * Work.FTS.H2.WPQ.GmajQ α g z θ :=
    Work.FTS.H2.WPQ.HkIntegrand_mul_le_Q hα hα1 hf hgsm hfm hgm
      (fun i hi z hz θ hθ =>
        Work.H2.WPQ.z_term_le_smoothQuad hf hgsm hfm hi hz hθ)
      (fun I J hI hIJ z hzpos θ hθ =>
        Work.H2.WPQ.m_term_le_smoothQuad (α := α) (f := f) (g := g) hα hα1 hf hgsm hfm hhardy
          (I := I) (J := J) hI hIJ (Set.mem_Ici.mpr (le_of_lt hzpos)) hzpos hθ)
  exact Work.FTS.H2.WPQ.WProdQ_final hα hα1 hf hgsm hfm hgm hpbi

end Work.FTS.H2

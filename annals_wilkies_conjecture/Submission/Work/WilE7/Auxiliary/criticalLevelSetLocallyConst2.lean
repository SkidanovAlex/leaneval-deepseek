import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.Auxiliary.criticalLevelSetLocallyConst

namespace Work.WilE7.Auxiliary

/-- **Local constancy of an analytic function along a regular level set.**

This is the same statement as `Work.WilE7.Aux.criticalLevelSetLocallyConst`, which is proved in
`Submission/Work/WilE7/Auxiliary/criticalLevelSetLocallyConst.lean` (via the implicit function
theorem: the zero set of `g` near a regular point `p` is an analytic graph over `ker (fderiv g p)`,
and `dF` vanishes on `ker dg` there, so `F` is constant on that graph).  We state it here under the
name requested by the downstream development and derive it from the library lemma. -/

theorem criticalLevelSetLocallyConst2 {n k : ℕ} (g : (Fin n → ℝ) → (Fin k → ℝ))
    (F : (Fin n → ℝ) → ℝ) (p : Fin n → ℝ)
    (hg : ∀ q, AnalyticAt ℝ g q) (hF : ∀ q, AnalyticAt ℝ F q)
    (hsurj : (fderiv ℝ g p).range = ⊤)
    (hcrit : ∀ᶠ y in nhds p, g y = 0 → ∀ v, (fderiv ℝ g y) v = 0 → (fderiv ℝ F y) v = 0) :
    ∀ᶠ y in nhds p, g y = 0 → F y = F p :=
  Work.WilE7.Aux.criticalLevelSetLocallyConst g F p hg hF hsurj hcrit

end Work.WilE7.Auxiliary

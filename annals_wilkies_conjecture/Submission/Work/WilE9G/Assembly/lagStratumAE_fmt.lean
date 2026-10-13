import Mathlib
import Submission.Work.WilE9G.Assembly.Defs

namespace Work.WilE9G.Assembly

theorem lagStratumAE_fmt {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (Phi : WilkiesDesign.E.EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ) :
    (Work.WilE9G.Assembly.lagStratumAE S Phi c).X.fmt = S.X.fmt + S.j + 1 := by
  simp only [Work.WilE9G.Assembly.lagStratumAE, WilkiesDesign.E.SemiPf.fmt]
  omega

end Work.WilE9G.Assembly

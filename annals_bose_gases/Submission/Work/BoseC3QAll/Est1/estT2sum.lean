import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Real.Basic
import Submission.Work.BoseC3QAll.Est1.Assembly
import Submission.Work.BoseC3QAll.Est1.estT2sum_assembly
import Submission.Work.BoseC3QAll.Est1.estT2sum_comZ
import Submission.Work.BoseC3QAll.Est1.estT2sum_opZb
import Submission.Work.BoseC3QAll.NWindow_linear_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseC3QAll.Est1

theorem estT2sum (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) :
    ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : Work.BoseB7.FockData Mode) (T : Work.BoseC3QAll.TildeData F) (E : Work.BoseB7.Q3Env Mode)
        (hv : Work.BoseB7.FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Work.BoseC3QAll.Q3KernelFSAll K₀ F T E →
        ∀ Φ : F.H, T.NWindow E.bigM Φ →
          ∑ k ∈ F.PHset E, (Work.BoseC3QAll.Est1.cD E k)⁻¹ *
              F.bp (Work.BoseC3QAll.Est1.shift F T E k Φ) (Work.BoseC3QAll.Est1.shift F T E k Φ)
            ≤ (E.lille ^ 2 / 4) * F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat))
              + 2 * E.rho * E.W1omega0 * F.qw Φ (T.Gop E)
              + C * Work.BoseC3QAll.e1A E * F.normSq Φ
              + (E.b / 200) * F.qw Φ (T.gapOpT E) :=
  estT2sum_of_pieces K₀ b₀ hb₀ (estT2sum_comZ K₀ b₀ hb₀) (estT2sum_opZ K₀ b₀ hb₀)

end Work.BoseC3QAll.Est1

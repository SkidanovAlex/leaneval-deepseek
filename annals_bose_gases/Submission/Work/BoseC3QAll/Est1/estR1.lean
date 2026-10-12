import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Real.Basic
import Submission.Work.BoseC3QAll.Est1.R1_split
import Submission.Work.BoseC3QAll.Est1.Wb1_boundb
import Submission.Work.BoseC3QAll.Est1.Wb2_boundb
import Submission.Work.BoseC3QAll.Est1.cost_arith
import Submission.Work.BoseC3QAll.Est1.estR1_assembly
import Submission.Work.BoseC3QAll.Est1.wta_bound_auxb
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.Est1.estR1` — piece **C** of FS `eq:EstimateQ3Tilde1`

The leftover `R1` (FS's `T₁(k)` together with the commutator part of `T₂(k)`) is
the linear word

`R1 = (z/ℓ³) Σ_{s,k} γ_{sk}β_{sk} ( κB(b_k†+b_k) + κA(b_{s-k}†+b_{s-k}) - κC(ã_{-s}†+ã_{-s}) )`,

and this module proves

`-(C·e1A)‖Φ‖² - (𝓁²/4)⟨Φ, dNumOpR(P_H^q) Φ⟩ - (b/800)⟨Φ, gapOpT Φ⟩ ≤ ⟨Φ, R1 Φ⟩`

for every `Φ` in FS's number window `T.NWindow E.bigM Φ` (FS ll. 3300–3320, with
the `D7` correction of the design note: the `σ₂`-commutator is *not* small — it is
bounded by `alpha_lip` and charged to the energy gap).

The objects (`suppL`, `cTa`, `Wta`, `Wb1`, `Wb2`, `Mc`, `costTa`, `costB2`,
`costB3`) are defined in `Est1.estR1_defs`; the assembly `estR1_of_pieces` (the
split + the three word bounds + the arithmetic) is `Est1.estR1_assembly`; and the
four pieces are

* `Est1.R1_split` — `R1 = Wta + Wb1 + Wb2`;
* `Est1.wta_bound_aux` — the `θ`-word (`σ₂`/`κC`) against the energy gap
  (`Est1.Wta_bound_aux`, with the pointwise coefficient bound `Est1.cTa_pointwise`);
* `Est1.Wb1_bound`, `Est1.Wb2_bound` — the two squeezed-mode words (`σ₁`/`κA`,
  `κB`) against the quarter-region reserve;
* `Est1.cost_arith` — `costTa + costB2 + costB3 ≤ C·e1A`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseC3QAll

namespace Est1

theorem estR1 (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) :
    ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : Work.BoseB7.FockData Mode) (T : Work.BoseC3QAll.TildeData F) (E : Work.BoseB7.Q3Env Mode)
        (hv : Work.BoseB7.FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Work.BoseC3QAll.Q3KernelFSAll K₀ F T E →
        ∀ Φ : F.H, T.NWindow E.bigM Φ →
          -(C * Work.BoseC3QAll.e1A E) * F.normSq Φ
              - (E.lille ^ 2 / 4) * F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat))
              - (E.b / 800) * F.qw Φ (T.gapOpT E)
            ≤ F.qw Φ (Work.BoseC3QAll.Est1.R1 F T E) :=
  estR1_of_pieces K₀ b₀ hb₀ R1_split (Wta_bound_aux K₀ b₀ hb₀) (Wb1_bound K₀ b₀ hb₀)
    (Wb2_bound K₀ b₀ hb₀) (cost_arith K₀ b₀ hb₀)

end Est1

end Work.BoseC3QAll

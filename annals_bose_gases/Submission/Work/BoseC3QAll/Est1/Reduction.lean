import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Real.Basic
import Submission.Work.BoseC3QAll.Est1.Assembly
import Submission.Work.BoseC3QAll.Est1.estR1
import Submission.Work.BoseC3QAll.Glue
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.Est1.Reduction` — `EstQ3oneA` reduces to piece **B**

The assembly `Est1.estQ3oneA_of_pieces` needs three inputs.  Two of them are
**proved**:

* piece **C** (`Est1.estR1`, `Submission/Work/BoseB7A/Est1/estR1.lean`,
  sorry-free): `R1 ≥ -(C e1A)‖Φ‖² - (𝓁²/4)⟨R_{P_H^q}⟩ - (b/800)⟨gapOpT⟩`;
* the substitution hypothesis (`Glue.substHyp_of_kernel`, sorry-free).

This module therefore records the exact remaining gap: `EstQ3oneA` holds as soon
as **piece B** does, i.e. as soon as

`Σ_{k∈P_H} c_k⁻¹‖Y_kΦ‖² ≤ (𝓁²/4)⟨R_{P_H^q}Φ⟩ + 2ρ_zŴ₁ω(0)⟨G Φ⟩ + C·e1A·‖Φ‖² + (b/200)⟨gapOpT Φ⟩`

(`Est1.estT2sum`, delegated).  This is also a machine check that the statements of
`estR1` and `substHyp_of_kernel` are *exactly* the hypotheses of the assembly.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseC3QAll

namespace Est1

open Work.BoseB7

universe u v

/-- **`EstQ3oneA` from piece B alone.**  Piece C and the substitution hypothesis
are supplied by the proved `Est1.estR1` and `Glue.substHyp_of_kernel`. -/
theorem estQ3oneA_of_estT2sum (K₀ b₀ : ℝ) (hb₀ : 0 < b₀)
    (hB : ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧
      ∀ {Mode : Type u} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : FockData.{u, v} Mode) (T : Work.BoseB7A.TildeData.{u, v} F) (E : Q3Env.{u} Mode)
        (hv : FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Q3KernelFSAll K₀ F T E →
        ∀ Φ : F.H, T.NWindow E.bigM Φ →
          ∑ k ∈ F.PHset E, (cD E k)⁻¹ * F.bp (shift F T E k Φ) (shift F T E k Φ)
            ≤ (E.lille ^ 2 / 4) * F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat))
              + 2 * E.rho * E.W1omega0 * F.qw Φ (T.Gop E)
              + C * e1A E * F.normSq Φ
              + (E.b / 200) * F.qw Φ (T.gapOpT E)) :
    EstQ3oneA.{u, v} K₀ b₀ hb₀ :=
  estQ3oneA_of_pieces K₀ b₀ hb₀ hB (estR1 K₀ b₀ hb₀) (substHyp_of_kernel K₀ b₀ hb₀)

end Est1

end Work.BoseC3QAll

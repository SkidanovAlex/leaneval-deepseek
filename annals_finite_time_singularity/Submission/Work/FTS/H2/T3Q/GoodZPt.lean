import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.H2.Transport3Aux.Defs
import Submission.Work.FTS.H2.Transport3Aux.Z3Defs
import Submission.Work.FTS.H2.Transport3Aux.Z3Aux
import Submission.Work.FTS.H2.Transport3Aux.mx_monomial_bound
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.H2.WPQ.Leibniz
import Submission.Work.FTS.H2.STQ.Basic
import Submission.Work.FTS.H2.HQ.DthDzIterComm
import Submission.Work.FTS.H2.STSigma
import Submission.Work.FTS.H2.T3Q.MultQ
import Submission.Work.FTS.H2.T3Q.QuadZLeibniz
import Submission.Work.FTS.H2.T3Q.easyZ_abs_le_Q
import Submission.Work.FTS.H2.T3Q.Msurv_abs_le_Q
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.T3Q

open scoped Real Topology
open Work.FTS.H2.Transport3Aux.Z3

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The "good" part of the `D_z`-pairing of Elgindi's `Transport3` (tex 1119) in the interior
class `SmoothQuad`: with `Badz2 = Badz + Mismatchz` (the order-five "all derivatives on `g`"
summands together with the "mismatch" summands in which all the `θ`-derivatives fall on `f`),
the integrand `H4PairInt α (f·D_z g) g - Badz2 α f g` is bounded pointwise by
`C |f|_{𝒲^{4,∞}} · HkIntegrand α 4 g`.
Route: the Leibniz expansions of `D_z^i (f·D_zg)` and `D_z^jD_θ^i(f·D_zg)` in the interior class
(the `SmoothQuad` analogues of `Z3.DzIter_mul_Dz_eq` / `Z3.mixed_mul_Dz_eq`, whose proofs only
need the `z`-slice smoothness at the given `θ ∈ (0,π/2)`), the bookkeeping identities
`Z3.H4PairInt_sub_Badz_eq` and `Z3.easyM_sub_Mismatchz` (pure algebra), the `f`-bounds
`Work.FTS.H2.WPQ.DzIter_le_WlInf` / `Mixed_le_WlInf` and the unconditional `g`-AM–GM lemmas
`Transport3Aux.abs_mixed_pair_mul_weight_le_HkIntegrand`,
`Transport3Aux.abs_dzIter_mul_Whz_le_sqrt`, `Transport3Aux.abs_mul_le_of_abs_le_sqrt`.
The only surviving mixed summands have `a < i`, so both their `g`-blocks carry at least one
`θ`-derivative and the weight comparison is exact. -/
theorem GoodZPt : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 → Work.FTS.LocData.SmoothQuad f → Work.Spaces.WlInfMem α 4 f →
    Work.FTS.LocData.SmoothQuad g → Work.Spaces.HkMem α 4 g →
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.H2.H4PairInt α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g z θ
         - Work.FTS.H2.Badz2 α f g z θ|
        ≤ C * Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ := by
  refine ⟨5000000, by norm_num, ?_⟩
  intro α f g hα hα1 hsf hwf hsg hkg z hz θ hθ
  by_cases hθi : θ ∈ Set.Ioo 0 (π / 2)
  · -- interior point: expand, cancel the mismatch family, and bound the two remainders
    have hexp := H4PairInt_sub_Badz_eq_Q α f g hsf hsg z hz θ hθi
    have hcanc := easyM_sub_Mismatchz α f g z θ
    have hmain : Work.FTS.H2.H4PairInt α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g z θ
          - Work.FTS.H2.Badz2 α f g z θ
        = easyZ α f g z θ + Msurv α f g z θ := by
      have hB : Work.FTS.H2.Badz2 α f g z θ
          = Work.FTS.H2.Badz α f g z θ + Mismatchz α f g z θ := rfl
      calc Work.FTS.H2.H4PairInt α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g z θ
            - Work.FTS.H2.Badz2 α f g z θ
          = (Work.FTS.H2.H4PairInt α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g z θ
              - Work.FTS.H2.Badz α f g z θ) - Mismatchz α f g z θ := by rw [hB]; ring
        _ = (easyZ α f g z θ + easyM α f g z θ) - Mismatchz α f g z θ := by rw [hexp]
        _ = easyZ α f g z θ + (easyM α f g z θ - Mismatchz α f g z θ) := by ring
        _ = easyZ α f g z θ + Msurv α f g z θ := by rw [hcanc]
    rw [hmain]
    have h1 := easyZ_abs_le_Q α f g hα hα1 hsf hwf z hz θ hθi
    have h2 := Msurv_abs_le_Q α f g hα hα1 hsf hwf z hz θ hθi
    have hK : 0 ≤ Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ :=
      mul_nonneg (Work.FTS.H2.WPQ.WlInf_nonneg' hwf)
        (Work.Spaces.HkIntegrand_nonneg α 4 g z θ)
    refine le_trans (abs_add_le _ _) ?_
    refine le_trans (add_le_add h1 h2) ?_
    nlinarith [hK]
  · -- angular boundary: `sin(2θ) = 0`, both sides vanish
    have hsin : Real.sin (2 * θ) = 0 := Work.Spaces.sin_two_eq_zero_of_not_Ioo hθ hθi
    rw [H4PairInt_eq_zero_of_sin_two_eq_zero α hα hsin,
      Badz2_eq_zero_of_sin_two_eq_zero α hα f g hsin,
      HkIntegrand_eq_zero_of_sin_two_eq_zero hα hsin]
    simp

end Work.FTS.H2.T3Q

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.BaseCase
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.logPair_conv_transfer_iter
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.leaf_logW_shift_uniform
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.integrable_pairing_Jeps

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs

/-- **Weighted near-self-adjointness of the log-coordinate mollifier `J_ε` at level six, with no
derivative loss.**

`IP6o α = IP6 1 1 … 1 α` is the level-six pairing of the coercivity chapter, which in the log
coordinates `(s,ζ) = (log z, log tan θ)` is a weighted slot pairing; `J_ε` is an even convolution
there, so the weight-difference form of the commutator `[J_ε, IP6o]` is `O(ε)` in the `ℋ⁶`-norms.

The proof is the recursion of the transfer defect `Δₙ` along `IPn α (n+1) = HkIPStep 1 1 (IPn α n)`
(`JepsTransfer.Recur.IPn_succ_Jeps`): the base case `Δ₀` is the level-one transfer estimate
(`JepsTransfer.BaseCase.H1IP_transfer_of`, whose four `wip`-slots are handled by the analytic
transfer `logPair_conv_transfer_iter` after two log-coordinate substitutions), and each recursion
step costs one `ℋ`-level, so `Δ₅` is controlled by `3⁵` times the level-one constant. -/
theorem Jeps_IP6_transfer_proof {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hρs : ∀ p : ℝ × ℝ, ρ (-p) = ρ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
      ∀ f h : Work.FTS.Galerkin.Fn,
      Work.FTS.VocabO.HQo α 6 f → Work.FTS.VocabO.HQo α 6 h →
      |Work.FTS.StrongEps.EpsE4Thr.E4R4.IP6o α (Work.FTS.StrongEps.Jeps ρ ε f) h
        - Work.FTS.StrongEps.EpsE4Thr.E4R4.IP6o α f (Work.FTS.StrongEps.Jeps ρ ε h)|
        ≤ C * ε * Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 h := by
  -- the three analytic inputs
  have hLT : JT.LogPlaneTransfer := fun {k ε Cw} hε0 hε1 hCw hkcont hk0 hkmass hksupp hkeven
      hkmomint {Q} hQ0 hQm hQsh hQsh' {G₁ G₂} hG1m hG2m hconv1 hconv2 hI1 hI2 =>
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.logPair_conv_transfer_iter
      hε0 hε1 hCw hkcont hk0 hkmass hksupp hkeven hkmomint hQ0 hQm hQsh hQsh' hG1m hG2m
      hconv1 hconv2 hI1 hI2
  have hShift : JT.LeafShiftUniform :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.leaf_logW_shift_uniform
  have hInt : JT.LeafPairIntegrable ρ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.integrable_pairing_Jeps hρ
  obtain ⟨K, hK0, hK⟩ := JT.delta_bound_of hρ hρs hLT hShift hInt
  refine ⟨K, hK0, ?_⟩
  intro α hα ε hε f h hf hh
  have hb := hK α hα ε hε f h hf hh
  simpa only [Work.FTS.StrongPersist.N6TPPriced.IP6_one_eq_IPn_five] using hb

end Work.FTS.StrongEps.E4R3.Apriori4Proofs

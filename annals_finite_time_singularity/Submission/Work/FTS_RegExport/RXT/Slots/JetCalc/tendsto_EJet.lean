import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Slots.JetCalc

open Filter

/-- **Convergence of one Leibniz sum.**  If every mixed jet `D_z^b D_θ^a X` of order
`a + b ≤ 3` of a sequence `Ξ n` converges pointwise to the corresponding jet of `Ξlim`,
then so does every finite Leibniz sum `coefJetS d j i s` whose highest occurring jet
`D_z^j D_θ^{i+s} X` has order at most `3`.

The `θ`-dependent coefficients `D_θ^k d` are fixed, hence convergent as constant
sequences. -/
theorem tendsto_coefJetS {Ξ : ℕ → ℝ → ℝ → ℝ} {Ξlim : ℝ → ℝ → ℝ}
    (hconv : ∀ (b a : ℕ), a + b ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed b a (Ξ n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed b a Ξlim z θ)))
    (d : ℝ → ℝ) {j i s : ℕ} (hord : j + (i + s) ≤ 3) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun n : ℕ => coefJetS d j i s (Ξ n) z θ) Filter.atTop
        (nhds (coefJetS d j i s Ξlim z θ)) := by
  intro z θ hz hθ hθlt
  unfold coefJetS
  refine tendsto_finsetSum (Finset.range (i + 1)) ?_
  intro k hk
  have hk_le : k ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hle : (i - k + s) + j ≤ 3 := by omega
  have hterm := hconv j (i - k + s) hle z θ hz hθ hθlt
  have hconst : Filter.Tendsto
      (fun _ : ℕ => (i.choose k : ℝ)
        * Work.Spaces.DthIter k (fun _ (θ' : ℝ) => d θ') z θ) Filter.atTop
      (nhds ((i.choose k : ℝ)
        * Work.Spaces.DthIter k (fun _ (θ' : ℝ) => d θ') z θ)) :=
    tendsto_const_nhds
  simpa only [mul_assoc] using hconst.mul hterm

theorem tendsto_EJet {Ξ : ℕ → ℝ → ℝ → ℝ} {Ξlim : ℝ → ℝ → ℝ}
    (hconv : ∀ (b a : ℕ), a + b ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed b a (Ξ n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed b a Ξlim z θ)))
    (a b c : ℝ → ℝ) {j i : ℕ} (hji : j + i ≤ 2) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun n : ℕ => Work.FTS_RegExport.RXT.Slots.JetCalc.EJet a b c j i (Ξ n) z θ)
        Filter.atTop
        (nhds (Work.FTS_RegExport.RXT.Slots.JetCalc.EJet a b c j i Ξlim z θ)) := by
  intro z θ hz hθ hθlt
  have h1 := tendsto_coefJetS hconv a (j := j) (i := i) (s := 0) (by omega) z θ hz hθ hθlt
  have h2 := tendsto_coefJetS hconv b (j := j + 1) (i := i) (s := 0) (by omega) z θ hz hθ hθlt
  have h3 := tendsto_coefJetS hconv (fun θ' : ℝ => c θ' / Real.sin (2 * θ'))
    (j := j) (i := i) (s := 1) (by omega) z θ hz hθ hθlt
  unfold EJet
  exact (h1.add h2).add h3

end Work.FTS_RegExport.RXT.Slots.JetCalc

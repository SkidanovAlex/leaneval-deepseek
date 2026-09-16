import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Topology.Algebra.Valued.ValuationTopology

open scoped WithZero Topology
open WithZero

namespace Commons.Topology.Algebra.Valued

theorem exp_balls_is_basis {K : Type*} [Field K] [vK : Valued K ℤᵐ⁰]
    (U : Set K) :
    letI : UniformSpace K := vK.toUniformSpace
    letI : TopologicalSpace K := UniformSpace.toTopologicalSpace
    U ∈ 𝓝 (0 : K) → ∃ n : ℤ, {x : K | Valued.v x < exp n} ⊆ U := by
  intro hU
  rcases (Valued.mem_nhds_zero.mp hU) with ⟨γ, hγ⟩
  let g : ℤᵐ⁰ := MonoidWithZeroHom.ValueGroup₀.embedding γ.1
  have hg0 : g ≠ 0 := by
    intro hg0
    have hγ0 : (γ : (MonoidWithZeroHom.ofClass (Valued.v : Valuation K ℤᵐ⁰)).ValueGroup₀) ≠ 0 :=
      Units.ne_zero γ
    apply hγ0
    exact (MonoidWithZeroHom.ValueGroup₀.embedding_inj.mp hg0)
  refine ⟨WithZero.log g, ?_⟩
  intro x hx
  apply hγ
  change Valued.v.restrict x < (γ : (MonoidWithZeroHom.ofClass (Valued.v : Valuation K ℤᵐ⁰)).ValueGroup₀)
  rw [Valuation.restrict_lt_iff_lt_embedding (v := Valued.v)]
  change Valued.v x < g
  have hg : WithZero.exp (WithZero.log g) = g := WithZero.exp_log hg0
  simpa [hg] using hx

end Commons.Topology.Algebra.Valued
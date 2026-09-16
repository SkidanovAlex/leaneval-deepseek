import Mathlib.Topology.Algebra.Valued.ValuedField

/-!
# A valued field is a nonarchimedean topological ring

The topology on a valued ring comes from a valuation, and the open balls centered at zero
`{x | v x < γ}` are open additive subgroups forming a neighbourhood basis of zero.  Hence the
topological ring underlying a valued field is nonarchimedean.
-/

namespace Commons.Topology.Algebra.Valued

/-- The topology induced by a valuation on a field makes it a nonarchimedean topological ring. -/
theorem nonarchimedeanRing {K Γ₀ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] [vK : Valued K Γ₀] :
    letI : UniformSpace K := vK.toUniformSpace
    letI : TopologicalSpace K := UniformSpace.toTopologicalSpace
    NonarchimedeanRing K := by
  refine { is_nonarchimedean := ?_ }
  intro U hU
  rw [Valued.mem_nhds_zero] at hU
  rcases hU with ⟨γ, hγ⟩
  refine ⟨⟨vK.v.restrict.ltAddSubgroup γ, ?_⟩, ?_⟩
  · have hset : (vK.v.restrict.ltAddSubgroup γ).carrier =
        {x | vK.v.restrict x < (γ : MonoidWithZeroHom.ValueGroup₀ (.ofClass vK.v))} := by
      ext x
      simp
    rw [hset]
    simpa using (Valued.isOpen_ball K
      (γ : MonoidWithZeroHom.ValueGroup₀ (.ofClass vK.v)))
  · intro x hx
    apply hγ
    change x ∈ (vK.v.restrict.ltAddSubgroup γ : Set K) at hx
    simpa using hx

end Commons.Topology.Algebra.Valued
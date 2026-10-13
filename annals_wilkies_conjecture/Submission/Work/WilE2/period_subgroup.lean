import Mathlib
import Submission.Work.WilE2.integral_curve_unique_global

/-!
# The subgroup of periods of an integral curve

For a curve `γ : ℝ → Fin m → ℝ`, define

`periodSubgroup γ = {τ : ℝ | ∀ t, γ (t + τ) = γ t}`,

the set of *periods* of `γ`.  It is an additive subgroup of `ℝ`; if `γ` is differentiable, it is
closed.  These are the basic companions of `exists_fundamental_period`.
-/

open Filter
open scoped Topology

namespace Work.WilE2

variable {m : ℕ}

/-- The additive subgroup of **periods** of a curve `γ : ℝ → Fin m → ℝ`:
`τ` is a period iff `γ (t + τ) = γ t` for every `t`. -/
def periodSubgroup (γ : ℝ → Fin m → ℝ) : AddSubgroup ℝ where
  carrier := {τ | ∀ t, γ (t + τ) = γ t}
  zero_mem' := by intro t; simp
  add_mem' := by
    intro a b ha hb t
    have h1 : γ (t + a + b) = γ (t + a) := hb (t + a)
    have h2 : γ (t + a) = γ t := ha t
    rw [add_assoc] at h1
    exact h1.trans h2
  neg_mem' := by
    intro a ha t
    have h := ha (t + (-a))
    simp only [add_assoc, neg_add_cancel, add_zero] at h
    exact h.symm

@[simp]
theorem mem_periodSubgroup {γ : ℝ → Fin m → ℝ} (τ : ℝ) :
    τ ∈ periodSubgroup γ ↔ ∀ t, γ (t + τ) = γ t := Iff.rfl

theorem continuous_of_hasDerivAt {γ : ℝ → Fin m → ℝ} {X : (Fin m → ℝ) → (Fin m → ℝ)}
    (hγ : ∀ t, HasDerivAt γ (X (γ t)) t) : Continuous γ :=
  continuous_iff_continuousAt.mpr fun t => (hγ t).continuousAt

theorem isClosed_periodSubgroup {γ : ℝ → Fin m → ℝ} {X : (Fin m → ℝ) → (Fin m → ℝ)}
    (hγ : ∀ t, HasDerivAt γ (X (γ t)) t) : IsClosed (periodSubgroup γ : Set ℝ) := by
  have hcont := continuous_of_hasDerivAt hγ
  have hset : (periodSubgroup γ : Set ℝ) = ⋂ t, {τ : ℝ | γ (t + τ) = γ t} := by
    ext τ
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe, mem_periodSubgroup]
  rw [hset]
  exact isClosed_iInter fun t =>
    isClosed_eq (hcont.comp (continuous_const.add continuous_id)) continuous_const

/-- If `γ` is an integral curve of a vector field that never vanishes along `γ`, then the period
subgroup is not everything: otherwise `γ` would be constant, forcing `X (γ t) = 0`. -/
theorem periodSubgroup_ne_top {γ : ℝ → Fin m → ℝ} {X : (Fin m → ℝ) → (Fin m → ℝ)}
    (hγ : ∀ t, HasDerivAt γ (X (γ t)) t) (hX0 : ∀ t, X (γ t) ≠ 0) :
    periodSubgroup γ ≠ ⊤ := by
  intro htop
  have hconst : γ = fun _ => γ 0 := by
    funext t
    have hmem : -t ∈ periodSubgroup γ := by rw [htop]; exact AddSubgroup.mem_top (-t)
    have := (mem_periodSubgroup (-t)).mp hmem t
    simpa using this.symm
  have h1 : HasDerivAt (fun _ : ℝ => γ 0) (X ((fun _ : ℝ => γ 0) 0)) 0 := hconst ▸ hγ 0
  have h2 : HasDerivAt (fun _ : ℝ => γ 0) 0 0 := hasDerivAt_const (0 : ℝ) (γ 0)
  exact hX0 0 (by simpa using h1.unique h2)

end Work.WilE2

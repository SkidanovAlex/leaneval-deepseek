import Submission.Metric

/-! A speed-zero locally linear path is constant. -/

open scoped ENNReal
open Set

namespace Submission
namespace Metric
namespace IsLocLinear

variable {M : Type*} [EMetricSpace M]

/-- The centre `t₀` of a speed-zero window lies inside the window. -/
private lemma mem_zero_window {a b t₀ : ℝ} (ht : t₀ ∈ Ioo a b) {δ : ℝ} (hδ : 0 < δ) :
    t₀ ∈ Ioo (max a (t₀ - δ)) (min b (t₀ + δ)) := by
  constructor
  · exact max_lt ht.1 (by linarith)
  · exact lt_min ht.2 (by linarith)

lemma eq_of_speed_zero {a b : ℝ} {γ : ℝ → M} (hγ : IsLocLinear a b 0 γ)
    {s t : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) : γ s = γ t := by
  -- On the open interval `(a,b)` (viewed as a subtype of `ℝ`), the map `γ` is
  -- locally constant: around each `x` the defining window of `IsLocLinear`
  -- forces `edist (γ y) (γ x) = 0` for every `y` in the window, hence
  -- `γ y = γ x` because `M` is an extended metric space.
  let X : Type := {x : ℝ // x ∈ Ioo a b}
  let f : X → M := fun x => γ x.1
  have hlc : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    rcases hγ x.1 x.2 with ⟨δ, hδ, hwin⟩
    let W : Set ℝ := Ioo (max a (x.1 - δ)) (min b (x.1 + δ))
    refine ⟨{y : X | y.1 ∈ W}, ?_, ?_, ?_⟩
    · exact isOpen_Ioo.preimage (continuous_subtype_val (p := fun r : ℝ => r ∈ Ioo a b))
    · dsimp [W]
      exact mem_zero_window x.2 hδ
    · intro y hy
      have hw := hwin y.1 x.1 hy (mem_zero_window (a := a) (b := b) x.2 hδ)
      have heq : edist (γ y.1) (γ x.1) = 0 := by simpa using hw
      exact edist_eq_zero.mp heq
  -- An open interval of `ℝ` is preconnected; a locally constant function on a
  -- preconnected space is constant, so `γ s = γ t`.
  let hI : PreconnectedSpace X := Subtype.preconnectedSpace (isPreconnected_Ioo (a := a) (b := b))
  have hEq : f ⟨s, hs⟩ = f ⟨t, ht⟩ :=
    @IsLocallyConstant.apply_eq_of_preconnectedSpace X M _ hI f hlc ⟨s, hs⟩ ⟨t, ht⟩
  simpa [f] using hEq

end IsLocLinear
end Metric
end Submission

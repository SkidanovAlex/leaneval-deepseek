import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.Tau

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Tame.irr_not_trivial_on_K` — an irreducible not trivial on a normal subgroup

A small character-theoretic step used in the proof of Feit–Thompson 9.2 (second part) and of
FT 10.3: if an irreducible character `θ` of `𝔑 = N(𝔎)` has restriction to `𝔎` orthogonal to the
principal character of `𝔎`, then `θ` is not the constant function `θ 1` on `𝔎`: some `H ∈ 𝔎`
has `θ(H) ≠ θ(1)`.
-/

namespace Work.Tame

open Classical

/-- If `θ` is an irreducible character of `N(𝔎)` whose restriction to `𝔎 = K` is orthogonal to
the principal character of `K`, then `θ|_K` is not the constant `θ 1`. -/
theorem irr_not_trivial_on_K {X : Type*} [Group X] [Fintype X] {K : Subgroup X}
    {θ : ↥(Lgrp (K : Set X)) → ℂ} (hθ : θ ∈ CharCore.Irr ↥(Lgrp (K : Set X)))
    (hθker : Coherence.cfInner (fun hh : ↥K => θ ⟨(hh : X), K.le_normalizer hh.2⟩)
      (1 : ↥K → ℂ) = 0) :
    ∃ H : ↥K, θ ⟨(H : X), K.le_normalizer H.2⟩ ≠ θ 1 := by
  by_contra h
  push_neg at h
  have hconst : (fun hh : ↥K => θ ⟨(hh : X), K.le_normalizer hh.2⟩) =
      (θ 1) • (1 : ↥K → ℂ) := by
    funext hh
    rw [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    exact h hh
  rw [hconst, Coherence.cfInner_smul_left] at hθker
  have hone : Coherence.cfInner (1 : ↥K → ℂ) (1 : ↥K → ℂ) = 1 := by
    rw [Coherence.cfInner_apply]
    simp only [Pi.one_apply, map_one, mul_one]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  rw [hone, mul_one] at hθker
  have hne : θ 1 ≠ 0 := by
    rw [CharCore.irrDeg_spec hθ]
    exact CharCore.irrDeg_ne_zero hθ
  exact hne hθker

end Work.Tame

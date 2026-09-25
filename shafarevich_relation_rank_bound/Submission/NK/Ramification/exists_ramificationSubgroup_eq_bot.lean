import Mathlib
import Submission.NK.Ramification.Defs

namespace NK.Ramification

set_option linter.style.haveILetI false

/-- **The higher ramification filtration is eventually trivial** for a Noetherian valuation
ring `A` whose decomposition subgroup is finite: `G_N = 1` for some `N`.

Indeed `A` is a Noetherian local ring, so Krull's intersection theorem gives
`⋂_n 𝔪_A^n = 0`; combined with `iInf_ramificationSubgroup_eq_bot` this says that
`⋂_i G_i = 1`, and a decreasing sequence of subgroups of a finite group with trivial
intersection must reach `1`. -/
theorem exists_ramificationSubgroup_eq_bot {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [Finite (A.decompositionSubgroup K)] [IsNoetherianRing A] :
    ∃ N : ℕ, NK.Ramification.ramificationSubgroup (K := K) A N = ⊥ := by
  -- Krull's intersection theorem in the Noetherian local ring `A`.
  have hA : (⨅ n : ℕ, IsLocalRing.maximalIdeal A ^ n) = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  have hbot : (⨅ i : ℕ, ramificationSubgroup (K := K) A i) = ⊥ :=
    iInf_ramificationSubgroup_eq_bot A hA
  classical
  haveI : Fintype (A.decompositionSubgroup K) := Fintype.ofFinite _
  -- Every non-identity element leaves the filtration at some finite level.
  have hex : ∀ σ : A.decompositionSubgroup K, σ ≠ 1 →
      ∃ i : ℕ, σ ∉ ramificationSubgroup (K := K) A i := by
    intro σ hσ
    by_contra h
    refine hσ ((Subgroup.eq_bot_iff_forall _).mp hbot σ ?_)
    rw [Subgroup.mem_iInf]
    intro i
    by_contra hmem
    exact h ⟨i, hmem⟩
  -- Choose such a level for every element (and `0` for the identity), and take the maximum.
  let f : A.decompositionSubgroup K → ℕ := fun σ =>
    if h : σ = 1 then 0 else Classical.choose (hex σ h)
  refine ⟨Finset.univ.sup f, ?_⟩
  rw [Subgroup.eq_bot_iff_forall]
  intro σ hσ
  by_contra hne
  have hf : f σ = Classical.choose (hex σ hne) := dif_neg hne
  have hnot : σ ∉ ramificationSubgroup (K := K) A (Classical.choose (hex σ hne)) :=
    Classical.choose_spec (hex σ hne)
  rw [← hf] at hnot
  have hle : f σ ≤ Finset.univ.sup f := Finset.le_sup (Finset.mem_univ σ)
  exact hnot ((ramificationSubgroup_antitone A hle) hσ)

end NK.Ramification

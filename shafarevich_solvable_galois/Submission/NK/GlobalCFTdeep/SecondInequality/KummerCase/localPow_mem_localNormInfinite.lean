import Mathlib
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.Defs
import Submission.NK.GlobalCFTdeep.Herbrand.index_normGroup_completion_eq_finrank
import Submission.NK.GlobalCFT.Galois.exists_stabilizer_isConj_of_isReal_isComplex
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField.LiesOver

namespace NK.GlobalCFTdeep.SecondInequality.KummerCase

/-- Every `p`-th power in `K_vˣ` at an archimedean place `v` is a norm from `L_wˣ`, for `L/K`
finite Galois of prime degree `p`.  This is the archimedean companion of
`localPow_mem_localNormFinite`.  The local extension `L_w/K_v` is either trivial (of degree one,
when the norm map on units is onto) or `ℂ/ℝ` (`w` complex over a real `v`); in the latter case
`p = 2`, and the norm group has index two, so it contains all squares. -/
theorem localPow_mem_localNormInfinite {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card (L ≃ₐ[K] L) = p)
    (v : NumberField.InfinitePlace K) (w : NumberField.InfinitePlace L) [w.LiesOver v]
    {x : v.Completionˣ} (hx : x ∈ NK.GlobalCFTdeep.SecondInequality.KummerCase.localPow (K := K) p
      (NK.GlobalCFT.Place.ofInfinite v)) :
    ∃ u : w.Completionˣ, NK.GlobalCFT.Place.localNormInfinite w v u = x := by
  obtain ⟨α, hα⟩ := hx
  have hα' : α ^ p = x := hα
  have hindex : (NK.LocalReciprocity.normGroup v.Completion w.Completion).index
      = Module.finrank v.Completion w.Completion :=
    NK.GlobalCFTdeep.Herbrand.index_normGroup_completion_eq_finrank v w
  have key : x ∈ NK.LocalReciprocity.normGroup v.Completion w.Completion := by
    rcases NumberField.InfinitePlace.isUnramified_or_isRamified K w with h | h
    · -- unramified: the local extension has degree one, so the norm on units is onto
      have hfin : Module.finrank v.Completion w.Completion = 1 := h.finrank_eq_one v
      have htop : NK.LocalReciprocity.normGroup v.Completion w.Completion = ⊤ :=
        Subgroup.index_eq_one.mp (by rw [hindex, hfin])
      rw [htop]
      exact Subgroup.mem_top x
    · -- ramified: `w` is complex over a real `v`, so `2 ∣ p` and hence `p = 2`
      have heven : Even (Nat.card Gal(L/K)) :=
        NumberField.InfinitePlace.even_nat_card_aut_of_not_isUnramified h
      rw [hcard] at heven
      have hp2 : p = 2 := by
        rcases hp.eq_two_or_odd with h2 | hodd
        · exact h2
        · rw [Nat.even_iff] at heven; omega
      have hfin : Module.finrank v.Completion w.Completion = 2 := h.finrank_eq_two v
      have hidx : (NK.LocalReciprocity.normGroup v.Completion w.Completion).index = 2 := by
        rw [hindex, hfin]
      -- the norm group has index `p`, so it contains all `p`-th powers
      have hpow := Subgroup.pow_index_mem
        (NK.LocalReciprocity.normGroup v.Completion w.Completion) α
      rw [hidx, ← hp2, hα'] at hpow
      exact hpow
  rw [NK.LocalReciprocity.mem_normGroup_iff] at key
  obtain ⟨u, hu⟩ := key
  refine ⟨u, ?_⟩
  apply Units.ext
  simpa [NK.GlobalCFT.Place.localNormInfinite] using hu

end NK.GlobalCFTdeep.SecondInequality.KummerCase

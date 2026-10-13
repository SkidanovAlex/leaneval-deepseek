import Mathlib
import Submission.Work.WilC4aU.Defs

namespace Work.WilC4aU

/-- **C4aU.Finite.**  A countable existentially definable subset of the line is finite.

This is uniform finiteness (`WilkiesDesign.CG.UnifFiniteRExp`) at `k = 0`: the frozen statement
says that for every `Z ⊆ Fin (k + 1) → ℝ` in `RExpExist` there is `N` such that every fibre
`{t | Fin.cons t c ∈ Z}` (`c : Fin k → ℝ`) is a union of at most `N` preconnected sets.  With
`k = 0` the fibre is `Z` itself, up to the bijection `ℝ → (Fin 1 → ℝ)`, `t ↦ fun _ => t`.

Proof plan, using `subsingleton_of_countable_isPreconnected`
(`Submission/Work/WilC4aU/Defs.lean`): a countable preconnected subset of `ℝ` is a subsingleton.
Apply `hUF 0 Z hZ` and take `c := fun i : Fin 0 => i.elim0` to get a `Finset s` of at most `N`
preconnected sets with `{t : ℝ | Fin.cons t (fun i : Fin 0 => i.elim0) ∈ Z} = ⋃₀ s`.  Each
`I ∈ s` is a subset of that set, which is countable (it is the preimage of `Z` under the
injective map `t ↦ fun _ : Fin 1 => t`), so each `I` is a subsingleton and hence finite.  A
finite union of finite sets is finite, so `{t | (fun _ : Fin 1 => t) ∈ Z}` is finite; finally
`Z = (fun t : ℝ => fun _ : Fin 1 => t) '' {t | (fun _ : Fin 1 => t) ∈ Z}` because every
`v : Fin 1 → ℝ` is the constant tuple `fun _ => v 0`, so `Z` is finite. -/
theorem finite_of_countable_rexExist {Z : Set (Fin 1 → ℝ)}
    (hUF : WilkiesDesign.CG.UnifFiniteRExp) (hZ : WilkiesDesign.RExpExist Z)
    (hc : Z.Countable) : Z.Finite := by
  -- Uniform finiteness at `k = 0`: the `Fin 0`-fibre is `Z` itself, seen as a set of reals.
  obtain ⟨N, hN⟩ := hUF 0 Z hZ
  obtain ⟨s, _hcard, hpre, hunion⟩ := hN (fun i : Fin 0 => i.elim0)
  -- `S` is `Z` transported to `ℝ` along the constant-tuple injection.
  set S : Set ℝ := (fun t : ℝ => fun _ : Fin 1 => t) ⁻¹' Z with hSdef
  -- Every `Fin.cons t c` with `c : Fin 0 → ℝ` is the constant tuple.
  have hcons : ∀ t : ℝ, Fin.cons t (fun i : Fin 0 => i.elim0) = (fun _ : Fin 1 => t) := by
    intro t; funext i; fin_cases i; rfl
  have hScount : S.Countable := Set.Countable.preimage hc injective_const_fin1
  -- The fibre computed by uniform finiteness is exactly `S`.
  have hunion' : S = ⋃₀ (s : Set (Set ℝ)) := by
    have h1 : {t : ℝ | Fin.cons t (fun i : Fin 0 => i.elim0) ∈ Z}
        = {t : ℝ | (fun _ : Fin 1 => t) ∈ Z} := by
      ext t
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hcons t]
    have h2 : (fun t : ℝ => fun _ : Fin 1 => t) ⁻¹' Z
        = {t : ℝ | (fun _ : Fin 1 => t) ∈ Z} := rfl
    rw [hSdef, h2, ← h1]
    exact hunion
  -- Each preconnected member of `s` is countable, hence a subsingleton, hence finite.
  have hSfin : S.Finite := by
    rw [hunion']
    refine Set.Finite.sUnion (Finset.finite_toSet s) ?_
    intro I hI
    have hsub : I ⊆ S := by rw [hunion']; exact Set.subset_sUnion_of_mem hI
    have hIcount : I.Countable := hScount.mono hsub
    exact (subsingleton_of_countable_isPreconnected hIcount (hpre I hI)).finite
  -- `Z` is the image of `S` under the constant-tuple injection, so it is finite.
  have hZeq : Z = (fun t : ℝ => fun _ : Fin 1 => t) '' S := by
    ext v
    constructor
    · intro hv
      refine ⟨v 0, ?_, ?_⟩
      · change (fun _ : Fin 1 => v 0) ∈ Z
        have hv' : v = (fun _ : Fin 1 => v 0) := by funext i; fin_cases i; rfl
        rw [← hv']; exact hv
      · funext i; fin_cases i; rfl
    · rintro ⟨t, ht, rfl⟩
      exact ht
  rw [hZeq]
  exact hSfin.image _

end Work.WilC4aU

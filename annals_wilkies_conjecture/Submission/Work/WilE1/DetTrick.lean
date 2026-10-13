import Mathlib
import Submission.Work.WilE1.Setup

namespace Work.WilE1

theorem DetTrick {R : Type*} [CommRing R] [IsNoetherianRing R]
    {I M : Ideal R} (hM : M.IsMaximal) (hI : I ≤ M) (h : M ≤ I ⊔ M ^ 2) :
    ∀ y ∈ M, ∃ s : R, s ∉ M ∧ s * y ∈ I := by
  -- The hypothesis `M ≤ I + M²` together with `I ≤ M` says that in the (local, Noetherian)
  -- quotient `R ⧸ I` the maximal ideal `M ⧸ I` is idempotent.  We do not need to form the
  -- quotient: Nakayama's lemma in the "determinant trick" form
  -- `Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup` applied to the ideal `M`
  -- (viewed as a submodule of `R`, finitely generated since `R` is Noetherian) as the
  -- ambient set `P = N' = M` and the ideal `I` as the submodule `N` produces `r` with
  -- `r - 1 ∈ M` and `r • M ≤ I`.
  obtain ⟨r, hr1, hr2⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
      (I := M) (N := (I : Submodule R R)) (N' := (M : Submodule R R))
      (P := (M : Submodule R R))
      (Ideal.fg_of_isNoetherianRing M) le_rfl
      (by simpa only [Ideal.smul_eq_mul, pow_two] using h)
  intro y hy
  refine ⟨r, ?_, ?_⟩
  · -- `r ∉ M`: otherwise `1 = r - (r - 1) ∈ M`, contradicting maximality of `M`.
    intro hr
    exact hM.ne_top (Ideal.eq_top_iff_one M |>.mpr (by
      have hh := M.sub_mem hr hr1
      rwa [sub_sub_cancel] at hh))
  · -- `r * y ∈ I` because `r • y ∈ r • M ≤ I` and `r • y = r * y`.
    have hmem : r • y ∈ I :=
      hr2 (Submodule.mem_smul_pointwise_iff_exists (r • y) r (M : Submodule R R)
        |>.mpr ⟨y, hy, rfl⟩)
    simpa [smul_eq_mul] using hmem

end Work.WilE1

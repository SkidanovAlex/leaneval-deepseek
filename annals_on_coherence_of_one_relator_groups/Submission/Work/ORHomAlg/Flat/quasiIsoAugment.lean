
import Mathlib
import Submission.Work.ORHomAlg.Tor

namespace Work.ORHomAlg.Flat

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The augmentation of a complex that is exact in positive degrees is a quasi-isomorphism. -/
theorem quasiIsoAugment {R : Type u} [Ring R] (C : ChainComplex (ModuleCat R) ℕ)
    {X Y : ModuleCat R} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) (g : X ⟶ Y) (hg : f ≫ g = 0)
    (hC : ∀ n : ℕ, C.ExactAt (n + 1))
    (hex1 : (ShortComplex.mk (C.d 1 0) f w).Exact)
    (hex0 : (ShortComplex.mk f g hg).Exact) (hepi : Epi g) :
    QuasiIso ((ChainComplex.toSingle₀Equiv (C.augment f w) Y).symm
      ⟨g, by rw [ChainComplex.augment_d_one_zero]; exact hg⟩) := by
  classical
  let D : ChainComplex (ModuleCat R) ℕ := C.augment f w
  let piD : D ⟶ (ChainComplex.single₀ (ModuleCat R)).obj Y :=
    (ChainComplex.toSingle₀Equiv D Y).symm
      ⟨g, by rw [ChainComplex.augment_d_one_zero]; exact hg⟩
  have hpiD0 : piD.f 0 = g :=
    ChainComplex.toSingle₀Equiv_symm_apply_f_zero (C := D) (X := Y) (f := g)
      (by rw [ChainComplex.augment_d_one_zero]; exact hg)
  have hexD1 : D.ExactAt 1 := by
    rw [HomologicalComplex.exactAt_iff' D 2 1 0 (by simp) (by simp)]
    exact hex1
  have hexD : ∀ m : ℕ, 1 ≤ m → D.ExactAt m := by
    intro m hm
    obtain _ | k := m
    · omega
    obtain _ | k := k
    · exact hexD1
    rw [HomologicalComplex.exactAt_iff' D (k + 3) (k + 2) (k + 1) (by simp) (by simp)]
    exact (HomologicalComplex.exactAt_iff' C (k + 2) (k + 1) k (by simp) (by simp)).mp (hC k)
  change QuasiIso piD
  refine ⟨fun n => ?_⟩
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · dsimp
      refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2 ⟨hex0, hepi⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by exact (ChainComplex.augment_d_one_zero C f w).symm)
        (by simp [hpiD0])
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt' _ (n + 1) (ChainComplex.exactAt_succ_single_obj Y n)]
    exact hexD (n + 1) (Nat.le_add_left 1 n)

end Work.ORHomAlg.Flat

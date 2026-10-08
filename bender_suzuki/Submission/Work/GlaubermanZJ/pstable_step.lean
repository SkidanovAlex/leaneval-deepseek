import Mathlib
import Submission.Work.GlaubermanZJ.theorem3_2_defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Glauberman 1968, Theorem 3.2, step (3.5)

This is step (3.5) of the proof of Glauberman's Theorem 3.2 (pp. 1109–1110 of
*Canad. J. Math.* **20** (1968)): with `C = Z(J(S)) ∩ B` and `L` the largest normal subgroup of
`X` inside `N_X(C)` (i.e. the normal core `(N_X(C)).normalCore`), `p`-stability of `X` implies
`A ≤ L` for every normal `p`-subgroup `C₁ ⊴ X` with `C ≤ C₁` and every `p`-subgroup `A ≤ S` with
`[C₁,A,A] = 1`.

The proof is the argument of (3.4)+(3.5): let `M = π⁻¹(O_p(X/C_X(C₁)))`, where
`π : X → X/C_X(C₁)` is the quotient map.  `O_p` of the quotient is a normal `p`-subgroup, so it
lies in the image of the Sylow subgroup `S`; hence `M ≤ S · C_X(C₁) ≤ N_X(C)`.  As `M ⊴ X` this
gives `M ≤ L`.  Finally `p`-stability applied to the normal `p`-subgroup `C₁` and the
`p`-subgroup `A` (which satisfies `[C₁,A,A] = 1`) shows that the image of `A` lies in
`O_p(X/C_X(C₁))`, i.e. `A ≤ M ≤ L`.
-/

set_option autoImplicit false

open scoped Classical Pointwise

namespace Work.GlaubermanZJ

theorem pstable_step {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hstab : IsPStable p X) (S : Sylow p X) (B : Subgroup X) [B.Normal] :
    ∀ (C₁ : Subgroup X), C₁.Normal → IsPGroup p C₁ → ZJcore S B ≤ C₁ →
      ∀ (A : Subgroup X), A ≤ (S : Subgroup X) → IsPGroup p A → ⁅⁅C₁, A⁆, A⁆ = ⊥ →
        A ≤ (Subgroup.normalizer ((ZJcore S B : Subgroup X) : Set X)).normalCore := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro C₁ hC₁norm hC₁p hC₁
  haveI : C₁.Normal := hC₁norm
  set C : Subgroup X := ZJcore S B with hCdef
  -- `S` normalises `C = Z(J(S)) ∩ B`
  have hS_NC : (S : Subgroup X) ≤ Subgroup.normalizer (C : Set X) := by
    rw [hCdef]
    exact le_normalizer_ZJcore S B
  -- `C_X(C₁)` normalises `C` (it centralises the larger subgroup `C₁ ⊇ C`)
  have hcent_NC : Subgroup.centralizer (C₁ : Set X) ≤ Subgroup.normalizer (C : Set X) :=
    (Subgroup.centralizer_le (show (C : Set X) ⊆ (C₁ : Set X) from hC₁)).trans
      (Subgroup.centralizer_le_normalizer _)
  intro A hAS hAp hcomm
  -- the quotient map `π : X → X/C_X(C₁)`
  set π : X →* X ⧸ Subgroup.centralizer (C₁ : Set X) :=
    QuotientGroup.mk' (Subgroup.centralizer (C₁ : Set X)) with hπdef
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  -- `M = π⁻¹(O_p(X/C_X(C₁)))`
  set M : Subgroup X :=
    (Work.HallHigman.pCore p (X ⧸ Subgroup.centralizer (C₁ : Set X))).comap π with hMdef
  have hMnorm : M.Normal := inferInstance
  -- `O_p` of the quotient is a normal `p`-subgroup, so it lies in the image of the Sylow `S`
  have hcore_le : Work.HallHigman.pCore p (X ⧸ Subgroup.centralizer (C₁ : Set X)) ≤
      (S : Subgroup X).map π :=
    IsPGroup.le_sylow_of_normal (isPGroup_pCore p _) (S.mapSurjective hπsurj)
  -- hence `M ≤ S ⊔ C_X(C₁) ≤ N_X(C)`
  have hM_le : M ≤ Subgroup.normalizer (C : Set X) := by
    have h1 : M ≤ ((S : Subgroup X).map π).comap π := Subgroup.comap_mono hcore_le
    rw [Subgroup.comap_map_eq] at h1
    have hker : π.ker = Subgroup.centralizer (C₁ : Set X) := by
      rw [hπdef]
      exact QuotientGroup.ker_mk' _
    rw [hker] at h1
    exact h1.trans (sup_le hS_NC hcent_NC)
  -- `A ≤ M` by `p`-stability
  have hA_le_M : A ≤ M := by
    have h := hstab C₁ hC₁p A hAp hcomm
    exact Subgroup.map_le_iff_le_comap.mp h
  -- conclude
  haveI : M.Normal := hMnorm
  exact hA_le_M.trans (Subgroup.normal_le_normalCore.mpr hM_le)

end Work.GlaubermanZJ

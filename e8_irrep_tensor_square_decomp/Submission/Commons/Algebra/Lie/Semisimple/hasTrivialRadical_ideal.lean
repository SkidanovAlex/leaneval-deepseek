import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Order.CompletePartialOrder

/-!
# Ideals of a semisimple Lie algebra are semisimple

Every Lie ideal `I` of a semisimple Lie algebra `L` has trivial radical (i.e. is
semisimple in the sense of `LieAlgebra.HasTrivialRadical`).

The argument is purely lattice-theoretic, using that in a semisimple Lie algebra the
lattice of Lie ideals is a Boolean algebra
(`LieAlgebra.IsSemisimple.instBooleanAlgebra`): an ideal `I` has a Lie-ideal complement `Iᶜ`
with `I ⊔ Iᶜ = ⊤` and `I ⊓ Iᶜ = ⊥`.  It follows that *every* Lie ideal `J` of `I`
(regarded as a subset of `L`) is already a Lie ideal of `L`:  writing `x = a + b` with
`a ∈ I`, `b ∈ Iᶜ`, one has `⁅x, y⁆ = ⁅a, y⁆ + ⁅b, y⁆` for `y ∈ J`, the first summand lies in
`J` because `J` is an ideal of `I`, and the second lies in `I ⊓ Iᶜ = ⊥`.

Consequently, if `J` is an abelian ideal of `I`, its image in `L` is an abelian ideal of `L`,
which must vanish since `L` has trivial radical; hence `J = ⊥` and `I` has trivial radical.
-/

namespace Commons.Algebra.Lie.Semisimple

open LieAlgebra

theorem hasTrivialRadical_ideal {K L : Type*} [Field K] [LieRing L]
    [LieAlgebra K L] [LieAlgebra.IsSemisimple K L] (I : LieIdeal K L) :
    LieAlgebra.HasTrivialRadical K I := by
  rw [LieAlgebra.hasTrivialRadical_iff_no_abelian_ideals]
  intro J hJ
  -- The underlying map `I → L` of the inclusion, expressed on the subtype.
  have hcoe : ∀ z : I, I.incl.toLinearMap z = (z : L) := fun z => by
    erw [LieIdeal.incl_coe, Submodule.coe_subtype]
  -- Step 1: the image of `J` in `L` is a Lie ideal of `L`.
  let J' : LieIdeal K L :=
    { toSubmodule := (J : Submodule K I).map I.incl.toLinearMap
      lie_mem := by
        rintro x m ⟨y, hy, rfl⟩
        -- decompose `x = a + b` with `a ∈ I` and `b` in the complement of `I`.
        obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ I, ∃ b ∈ Iᶜ, a + b = x := by
          have h : x ∈ I ⊔ Iᶜ := by
            rw [codisjoint_iff.mp (isCompl_compl (x := I)).codisjoint]
            trivial
          rw [LieSubmodule.mem_sup] at h
          exact h
        rw [← hab]
        rw [add_lie]
        apply Submodule.add_mem
        · -- `⁅a, y⁆ ∈ J`, since `J` is an ideal of `I`.
          refine Submodule.mem_map.mpr ⟨⁅(⟨a, ha⟩ : I), y⁆, J.lie_mem hy, ?_⟩
          erw [LieIdeal.incl_coe, Submodule.coe_subtype]
          rfl
        · -- `⁅b, y⁆ ∈ I ⊓ Iᶜ = ⊥`, hence vanishes.
          have hmem : ⁅b, (y : L)⁆ ∈ I ⊓ (Iᶜ : LieIdeal K L) :=
            ⟨I.lie_mem y.property, lie_mem_left K L (Iᶜ : LieIdeal K L) b (y : L) hb⟩
          have hzero : ⁅b, (y : L)⁆ = 0 := by
            have := hmem
            rw [disjoint_iff.mp (isCompl_compl (x := I)).disjoint, LieSubmodule.mem_bot] at this
            exact this
          rw [hcoe y, hzero]
          exact Submodule.zero_mem _ }
  -- Step 2: `J'` is abelian, being isomorphic (via the inclusion) to the abelian `J`.
  have hJ'ab : IsLieAbelian J' := by
    refine ⟨fun u v => ?_⟩
    apply Subtype.ext
    change ⁅(u : L), (v : L)⁆ = (0 : L)
    obtain ⟨j, hj, hju⟩ := Submodule.mem_map.mp u.property
    obtain ⟨k, hk, hkv⟩ := Submodule.mem_map.mp v.property
    rw [← hju, ← hkv, hcoe j, hcoe k]
    have h0 := hJ.trivial (⟨j, hj⟩ : J) (⟨k, hk⟩ : J)
    have : (↑⁅(⟨j, hj⟩ : J), (⟨k, hk⟩ : J)⁆ : L) = 0 := by rw [h0]; rfl
    exact this
  -- Step 3: `L` has trivial radical, so its non-zero abelian ideal `J'` cannot exist.
  have hJ'bot : J' = ⊥ :=
    (LieAlgebra.hasTrivialRadical_iff_no_abelian_ideals (R := K) (L := L)).mp
      (inferInstance : LieAlgebra.HasTrivialRadical K L) J' hJ'ab
  -- Finally `J = ⊥` follows because the inclusion `J → J'` is injective.
  rw [eq_bot_iff]
  intro j hj
  rw [LieSubmodule.mem_bot]
  have hmem : (j : L) ∈ J' := Submodule.mem_map.mpr ⟨j, hj, rfl⟩
  rw [hJ'bot] at hmem
  rw [LieSubmodule.mem_bot] at hmem
  exact Subtype.ext hmem

end Commons.Algebra.Lie.Semisimple
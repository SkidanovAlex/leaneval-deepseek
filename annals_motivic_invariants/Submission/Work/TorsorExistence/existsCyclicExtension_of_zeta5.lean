import Mathlib
import Submission.Work.TorsorExistence.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.TorsorExistence

universe u

open Polynomial

/-- **Kummer theory, degree five.**  If `𝕜` contains a primitive `5`-th root of unity `ζ` and
`a ∈ 𝕜` is not a fifth power, then `𝕜` has a cyclic extension of degree `5` (a root field of
`X ^ 5 - a`, which is a cyclic degree-`5` Galois extension of `𝕜`). -/
theorem existsCyclicExtension_of_zeta5 {𝕜 : Type u} [Field 𝕜] (ζ : 𝕜) (hζ : IsPrimitiveRoot ζ 5)
    (a : 𝕜) (ha : ¬ ∃ b : 𝕜, b ^ 5 = a) : Nonempty (CyclicExtension 𝕜 5) := by
  classical
  have hprime5 : Nat.Prime 5 := by norm_num
  have hζmem : (primitiveRoots 5 𝕜).Nonempty :=
    ⟨ζ, (mem_primitiveRoots (by norm_num : (0 : ℕ) < 5)).mpr hζ⟩
  -- `X ^ 5 - a` is irreducible, since `a` is not a fifth power and `5` is an odd prime.
  have Hirr : Irreducible (X ^ 5 - C a : 𝕜[X]) := by
    rw [X_pow_sub_C_irreducible_iff_forall_prime_of_odd (n := 5) (by norm_num) (a := a)]
    intro p hp hpdvd b hb
    have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp hprime5).mp hpdvd
    exact ha ⟨b, hp5 ▸ hb⟩
  -- The root field of `X ^ 5 - a`.
  let L := AdjoinRoot (X ^ 5 - C a : 𝕜[X])
  haveI : Fact (Irreducible (X ^ 5 - C a : 𝕜[X])) := ⟨Hirr⟩
  haveI : IsSplittingField 𝕜 L (X ^ 5 - C a : 𝕜[X]) :=
    isSplittingField_AdjoinRoot_X_pow_sub_C hζmem Hirr
  haveI : FiniteDimensional 𝕜 L := IsSplittingField.finiteDimensional L (X ^ 5 - C a : 𝕜[X])
  -- `L/𝕜` is Galois of degree `5` with cyclic Galois group (Kummer theory).
  haveI : IsGalois 𝕜 L := isGalois_of_isSplittingField_X_pow_sub_C hζmem Hirr L
  have hfin : Module.finrank 𝕜 L = 5 := finrank_of_isSplittingField_X_pow_sub_C hζmem Hirr L
  haveI : IsCyclic Gal(L/𝕜) := isCyclic_of_isSplittingField_X_pow_sub_C hζmem Hirr L
  obtain ⟨gen, hgen⟩ := IsCyclic.exists_generator (α := L ≃ₐ[𝕜] L)
  haveI : Fintype (L ≃ₐ[𝕜] L) := AlgEquiv.fintype 𝕜 L
  haveI : Finite (L ≃ₐ[𝕜] L) := Finite.of_fintype _
  have horder : orderOf gen = 5 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, IsGalois.card_aut_eq_finrank 𝕜 L, hfin]
  refine ⟨{ L := L
            finrank_eq := hfin
            gen := gen
            gen_generator := ?_
            orderOf_gen := horder }⟩
  intro g
  have hmem : g ∈ Submonoid.powers gen :=
    (isOfFinOrder_of_finite gen).mem_powers_iff_mem_zpowers.mpr (hgen g)
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff g gen).mp hmem
  exact ⟨k, hk.symm⟩

end Work.TorsorExistence

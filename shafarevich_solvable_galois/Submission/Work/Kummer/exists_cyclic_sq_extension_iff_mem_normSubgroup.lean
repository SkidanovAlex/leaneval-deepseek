import Mathlib
import Submission.Work.Kummer.Norm
import Submission.Work.Kummer.exists_norm_eq_primRoot_of_cyclic_sq_extension
import Submission.Work.Kummer.exists_cyclic_sq_extension_of_norm_eq_primRoot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u

namespace Work.Kummer

/-- **Kummer-theoretic criterion for the cyclic embedding problem.**

Let `L/K` be a finite cyclic Galois extension of degree `n` and let `ζ ∈ K` be a primitive
`n`-th root of unity.  Then `L` is contained in a finite cyclic Galois extension `M/K` of
degree `n ^ 2` if and only if `ζ` is a norm from `L` to `K`.

The two implications are `exists_norm_eq_primRoot_of_cyclic_sq_extension` (the norm of a
generator of `Gal(M/L)` is a root of unity, and the resulting norm computation gives `ζ`) and
`exists_cyclic_sq_extension_of_norm_eq_primRoot` (the Kummer construction `M = L(β)`,
`β ^ n = μ`, where `σ μ / μ = η ^ n`). -/
theorem exists_cyclic_sq_extension_iff_mem_normSubgroup {K L : Type u} [Field K] [Field L]
    [Algebra K L] {n : ℕ} [NeZero n] {ζ : K} [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic Gal(L/K)] (hζ : IsPrimitiveRoot ζ n) (hn : Module.finrank K L = n) :
    (∃ (M : Type u) (_ : Field M) (_ : Algebra K M) (_ : Algebra L M) (_ : IsScalarTower K L M)
      (_ : FiniteDimensional K M) (_ : IsGalois K M) (_ : IsCyclic Gal(M/K)),
      Module.finrank K M = n ^ 2) ↔ primRootUnit hζ ∈ normSubgroup K L := by
  constructor
  · rintro ⟨M, _hFieldM, _hAlgKM, _hAlgLM, _hTower, _hFinM, _hGalM, _hCycM, hfinM⟩
    obtain ⟨η, hη⟩ := exists_norm_eq_primRoot_of_cyclic_sq_extension (M := M) hζ hn hfinM
    exact ⟨η, by rw [primRootUnit_coe hζ]; exact hη⟩
  · intro h
    obtain ⟨η, hη⟩ := h
    rw [primRootUnit_coe hζ] at hη
    exact exists_cyclic_sq_extension_of_norm_eq_primRoot hζ hn η hη

end Work.Kummer

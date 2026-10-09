import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace NK.Chebotarev

/-- Second orthogonality relation in a form suited to Chebotarev arguments: if a family
of class functions satisfies the off-diagonal orthogonality relation and the diagonal
relation `∑ i, χ i g * star (χ i g) = |C(g)|`, then for a *fixed* `g₀` the pairing
`g ↦ ∑ i, χ i g₀ * star (χ i g)` detects conjugacy to `g₀`: it equals `|C(g₀)|` exactly
when `g` is conjugate to `g₀`, and `0` otherwise. -/
theorem SumChiMulStarChiEq {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {ι : Type*} [Fintype ι] (χ : ι → Gal(L/K) → ℂ) (i₀ : ι) (g₀ : Gal(L/K))
    (hχ_class : ∀ (i : ι) (g h : Gal(L/K)), χ i (h⁻¹ * g * h) = χ i g)
    (horth_off : ∀ g h : Gal(L/K), ¬ IsConj g h → ∑ i, χ i g * star (χ i h) = 0)
    (hnorm : ∀ g : Gal(L/K),
      ∑ i, χ i g * star (χ i g) =
        (Nat.card (Subgroup.centralizer ({g} : Set (Gal(L/K)))) : ℂ))
    (g : Gal(L/K)) :
    ((∑ i, χ i g₀ * star (χ i g) =
        (Nat.card (Subgroup.centralizer ({g₀} : Set (Gal(L/K)))) : ℂ)) ↔ IsConj g g₀) := by
  -- `Gal(L/K)` is finite, being the automorphism group of a finite extension.
  haveI hFintype : Fintype (Gal(L/K)) := AlgEquiv.fintype K L
  haveI hFinite : Finite (Gal(L/K)) := Finite.of_fintype _
  haveI hNe : Nonempty (Subgroup.centralizer ({g₀} : Set (Gal(L/K)))) :=
    ⟨1, Subgroup.one_mem _⟩
  constructor
  · -- Forward: the pairing is nonzero only on the conjugacy class of `g₀`.
    intro hsum
    by_contra hnc
    have hz : ∑ i, χ i g₀ * star (χ i g) = 0 :=
      horth_off g₀ g (fun hc => hnc hc.symm)
    have hcard0 : (Nat.card (Subgroup.centralizer ({g₀} : Set (Gal(L/K)))) : ℂ) = 0 := by
      rw [← hsum, hz]
    have hcard : Nat.card (Subgroup.centralizer ({g₀} : Set (Gal(L/K)))) = 0 :=
      Nat.cast_eq_zero.mp hcard0
    have hpos : 0 < Nat.card (Subgroup.centralizer ({g₀} : Set (Gal(L/K)))) := Nat.card_pos
    omega
  · -- Backward: conjugate elements give the same value as the diagonal term at `g₀`.
    intro hconj
    rw [isConj_iff] at hconj
    obtain ⟨c, hc⟩ := hconj
    have hval : ∀ i, χ i g₀ = χ i g := by
      intro i
      have h1 : χ i (c * g * c⁻¹) = χ i g := by simpa using hχ_class i g c⁻¹
      rw [hc] at h1
      exact h1
    calc ∑ i, χ i g₀ * star (χ i g)
        = ∑ i, χ i g₀ * star (χ i g₀) :=
          Finset.sum_congr rfl (fun i _ => by rw [← hval i])
      _ = (Nat.card (Subgroup.centralizer ({g₀} : Set (Gal(L/K)))) : ℂ) := hnorm g₀

end NK.Chebotarev

import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.RingTheory.RegularLocalRing.Defs

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Commons.Lattice.Counting

/-- If `R ≤ M` is a submodule of an abelian group `M` with finite quotient,
then there are only finitely many intermediate submodules `P` with `R ≤ P ≤ M`. -/
private lemma finite_submodules_containing_of_finite_quotient {M : Type*} [AddCommGroup M]
    (R : Submodule ℤ M) [Finite (M ⧸ R)] :
    Finite {P : Submodule ℤ M // R ≤ P} := by
  classical
  haveI : Finite (Submodule ℤ (M ⧸ R)) := by
    refine Finite.of_injective (fun P : Submodule ℤ (M ⧸ R) => (P : Set (M ⧸ R))) ?_
    exact SetLike.coe_injective
  refine Finite.of_injective (fun P : {P : Submodule ℤ M // R ≤ P} =>
    Submodule.map R.mkQ P.1) ?_
  intro A B h
  apply Subtype.ext
  have h' : Submodule.map R.mkQ A.1 = Submodule.map R.mkQ B.1 := by simpa using h
  have hA : (Submodule.map R.mkQ A.1).comap R.mkQ = A.1 := by
    rw [Submodule.comap_map_mkQ R A.1, sup_eq_right.mpr A.2]
  have hB : (Submodule.map R.mkQ B.1).comap R.mkQ = B.1 := by
    rw [Submodule.comap_map_mkQ R B.1, sup_eq_right.mpr B.2]
  calc
    A.1 = (Submodule.map R.mkQ A.1).comap R.mkQ := by rw [hA]
    _ = (Submodule.map R.mkQ B.1).comap R.mkQ := by rw [h']
    _ = B.1 := by rw [hB]

/-- Multiplication by `L` on a submodule `M` of `ℤⁿ` is injective when `L > 0`. -/
private lemma nsmul_injective {n : ℕ} (M : Submodule ℤ (Fin n → ℤ)) {L : ℕ} (hL : 0 < L) :
    Function.Injective (DistribSMul.toLinearMap ℤ M (L : ℤ)) := by
  intro x y h
  apply Subtype.ext
  have hxy : (L : ℤ) • (x : Fin n → ℤ) = (L : ℤ) • (y : Fin n → ℤ) := by
    simpa [DistribSMul.toLinearMap] using congrArg Subtype.val h
  ext i
  exact mul_left_cancel₀ (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hL)) (congrFun hxy i)

/-- A submodule of `ℤⁿ` contained in `M` is recovered from its pullback along the
subtype embedding of `M`. -/
private lemma comap_map_eq_of_le {n : ℕ} {M N : Submodule ℤ (Fin n → ℤ)} (h : N ≤ M) :
    (N.comap M.subtype).map M.subtype = N := by
  rw [Submodule.map_comap_subtype, inf_eq_right.mpr h]

/-- There are only finitely many submodules `N` of `M` with `L • M ⊆ N ⊆ M`. -/
theorem finite_submodules_between_nsmul (n : ℕ) (M : Submodule ℤ (Fin n → ℤ)) (L : ℕ) (hL : 0 < L) :
    {N : Submodule ℤ (Fin n → ℤ) | N ≤ M ∧ (∀ x : Fin n → ℤ, x ∈ M → (L : ℤ) • x ∈ N)}.Finite := by
  classical
  let f : M →ₗ[ℤ] M := DistribSMul.toLinearMap ℤ M (L : ℤ)
  let R : Submodule ℤ M := f.range
  have hrank : Module.finrank ℤ R = Module.finrank ℤ M := by
    simpa [R] using LinearMap.finrank_range_of_inj (nsmul_injective M hL)
  haveI : Finite (M ⧸ R) :=
    Submodule.finiteQuotientOfFreeOfRankEq (M := M) (N := R) hrank
  have hfinT : Finite {P : Submodule ℤ M // R ≤ P} :=
    finite_submodules_containing_of_finite_quotient R
  let U : Type := {N : Submodule ℤ (Fin n → ℤ) //
    N ≤ M ∧ (∀ x : Fin n → ℤ, x ∈ M → (L : ℤ) • x ∈ N)}
  let φ : U → {P : Submodule ℤ M // R ≤ P} := fun N => by
    refine ⟨N.1.comap M.subtype, ?_⟩
    intro z hz
    rw [Submodule.mem_comap]
    rcases hz with ⟨x, hx⟩
    have hx' : (L : ℤ) • (x : Fin n → ℤ) ∈ N.1 := N.2.2 (x : Fin n → ℤ) x.2
    have hzE : (z : Fin n → ℤ) = (L : ℤ) • (x : Fin n → ℤ) := by
      calc
        (z : Fin n → ℤ) = ((DistribSMul.toLinearMap ℤ M (L : ℤ)) x : Fin n → ℤ) :=
          congrArg Subtype.val hx.symm
        _ = (L : ℤ) • (x : Fin n → ℤ) := rfl
    simpa [Submodule.subtype_apply, hzE] using hx'
  have hφinj : Function.Injective φ := by
    intro A B h
    apply Subtype.ext
    have hAmem : A.1 ≤ M := A.2.1
    have hBmem : B.1 ≤ M := B.2.1
    have hAB : (A.1.comap M.subtype).map M.subtype = (B.1.comap M.subtype).map M.subtype := by
      simpa [φ] using congrArg (fun P : {P : Submodule ℤ M // R ≤ P} => P.1.map M.subtype) h
    calc
      A.1 = (A.1.comap M.subtype).map M.subtype := by rw [comap_map_eq_of_le hAmem]
      _ = (B.1.comap M.subtype).map M.subtype := hAB
      _ = B.1 := by rw [comap_map_eq_of_le hBmem]
  exact (Set.finite_coe_iff.mpr (Finite.of_injective φ hφinj))

end Commons.Lattice.Counting
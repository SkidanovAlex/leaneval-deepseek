import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.Minkowski2

open Submodule

/-- **Splitting off one rank from a pure submodule.**

Let `N ≤ O` be submodules of `ℤ^m`, with `N` *pure* (`c • x ∈ N` and `c ≠ 0` forces `x ∈ N`).
If `finrank ℤ O = finrank ℤ N + 1`, then `O = N ⊕ ℤ·y` for some `y ∈ O`:
`y` has infinite order modulo `N` and its class generates `O ⧸ N`.

In particular `O ⧸ N ≃ ℤ`. -/
theorem exists_split_step {m : ℕ} (N O : Submodule ℤ (Fin m → ℤ)) (hNO : N ≤ O)
    (hpure : ∀ (c : ℤ) (x : Fin m → ℤ), c ≠ 0 → c • x ∈ N → x ∈ N)
    (hrank : Module.finrank ℤ O = Module.finrank ℤ N + 1) :
    ∃ y : Fin m → ℤ, y ∈ O ∧
      (∀ (c : ℤ) (x : Fin m → ℤ), x ∈ N → c • y + x = 0 → c = 0) ∧
      (∀ z ∈ O, ∃ c : ℤ, z + c • y ∈ N) := by
  -- `N` viewed as a submodule of `O`.
  let Ñ : Submodule ℤ O := N.comap O.subtype
  have hfinrank_Ñ : Module.finrank ℤ Ñ = Module.finrank ℤ N :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (p := N) (q := O) hNO)
  -- The quotient `O ⧸ N` has rank one.
  have hq : Module.finrank ℤ (O ⧸ Ñ) = 1 := by
    have h := Submodule.finrank_quotient_add_finrank (R := ℤ) Ñ
    omega
  -- Purity of `N` means `O ⧸ N` is torsion-free.
  haveI htf : Module.IsTorsionFree ℤ (O ⧸ Ñ) :=
    Module.IsTorsionFree.of_smul_eq_zero fun c q hcq => by
      revert hcq
      refine Submodule.Quotient.induction_on Ñ q fun z => ?_
      intro hz
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hz
      by_cases hc : c = 0
      · exact Or.inl hc
      · refine Or.inr ?_
        rw [Submodule.Quotient.mk_eq_zero]
        have h2 : O.subtype (c • z) ∈ N := (Submodule.mem_comap (f := O.subtype) (p := N)).mp hz
        exact hpure c (z : Fin m → ℤ) hc (by simpa using h2)
  haveI hfree : Module.Free ℤ (O ⧸ Ñ) := Module.free_of_finite_type_torsion_free'
  -- A basis of the rank-one quotient, and a lift of its generator.
  let b : Module.Basis (Fin 1) ℤ (O ⧸ Ñ) := Module.finBasisOfFinrankEq ℤ (O ⧸ Ñ) hq
  obtain ⟨y₀, hy₀⟩ := Submodule.Quotient.mk_surjective Ñ (b 0)
  refine ⟨(y₀ : Fin m → ℤ), y₀.2, ?_, ?_⟩
  · -- `y` has infinite order modulo `N`.
    intro c x hxN hsum
    have hw0 : (c • y₀ + ⟨x, hNO hxN⟩ : O) = 0 := by
      apply Subtype.ext
      simpa using hsum
    have hcb : c • b 0 = 0 := by
      have h1 : (Submodule.Quotient.mk (p := Ñ) (c • y₀ + ⟨x, hNO hxN⟩) : O ⧸ Ñ) = 0 := by
        rw [hw0]; simp
      have hx0 : (Submodule.Quotient.mk (p := Ñ) (⟨x, hNO hxN⟩ : O) : O ⧸ Ñ) = 0 := by
        rw [Submodule.Quotient.mk_eq_zero]; exact hxN
      rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul, hy₀, hx0, add_zero] at h1
      exact h1
    have hb0 : b 0 ≠ 0 := b.ne_zero 0
    rcases smul_eq_zero.mp hcb with hc | hb
    · exact hc
    · exact absurd hb hb0
  · -- The class of `y` generates `O ⧸ N`.
    intro z hzO
    let z₀ : O := ⟨z, hzO⟩
    let c : ℤ := (b.repr (Submodule.Quotient.mk (p := Ñ) z₀)) 0
    refine ⟨-c, ?_⟩
    have hmk : (Submodule.Quotient.mk (p := Ñ) z₀ : O ⧸ Ñ) = c • b 0 := by
      have := b.sum_repr (Submodule.Quotient.mk (p := Ñ) z₀)
      rw [Fin.sum_univ_one] at this
      exact this.symm
    have hzero : (Submodule.Quotient.mk (p := Ñ) (z₀ - c • y₀) : O ⧸ Ñ) = 0 := by
      rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, hy₀, hmk, sub_self]
    rw [Submodule.Quotient.mk_eq_zero] at hzero
    have h2 : O.subtype (z₀ - c • y₀) ∈ N :=
      (Submodule.mem_comap (f := O.subtype) (p := N)).mp hzero
    simpa [z₀, sub_eq_add_neg, neg_smul] using h2

end Work.BW.Minkowski2

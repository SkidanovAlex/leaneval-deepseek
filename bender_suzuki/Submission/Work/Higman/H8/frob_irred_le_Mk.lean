/-
# The Frobenius component of an irreducible `𝔽₂⟨ξ⟩`-submodule of `End(GF(2^n))`

`Work.Higman.H8.frob_irred_submodule_le_Mk`: a nonzero `𝔽₂⟨ξ⟩`-stable *irreducible* submodule of
`End_{𝔽₂}(GF(2^n))` (with `ξ = conjAction ν`, `ν` a generator of `GF(2^n)ˣ`) lies inside a single
Frobenius component `Mk k = {x ↦ c · x ^ (2^k)}` (`k < n`).

This is the structural statement extracted from the proof of
`Work.Higman.H8.FSB.frob_component_bijective_aux` (which already contains the whole argument,
since the bijectivity conclusion is proved via the containment `T ≤ Mk k`); it is what pins the
`ξ`-eigenvalue of an irreducible module of order `2 ^ n` to be `lam ν k = ν ^ (1 - 2 ^ k)`.
-/
import Mathlib
import Submission.Work.Higman.H8.frob_submodule_bijective

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Polynomial

namespace Work.Higman.H8

open FSB

/-- **A nonzero irreducible `𝔽₂⟨ξ⟩`-submodule of `End_{𝔽₂}(GF(2^n))` lies in one Frobenius
component.**  With `ν` of order `2 ^ n - 1` and `ξ = singAct ν = conjAction ν`, an `𝔽₂⟨ξ⟩`-stable
submodule `T ≤ End_{𝔽₂}(GF(2^n))` with no proper nonzero `ξ`-stable submodule satisfies
`T ≤ Mk k` for some `k < n`. -/
theorem frob_irred_submodule_le_Mk {n : ℕ} (hn : 2 ≤ n)
    (ν : (GaloisField 2 n)ˣ) (hν : orderOf ν = 2 ^ n - 1)
    (T : Submodule (ZMod 2) (GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n))
    (hTξ : ∀ f ∈ T, singAct ν f ∈ T)
    (hirr : ∀ T' : Submodule (ZMod 2) (GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n),
      (∀ f ∈ T', singAct ν f ∈ T') → T' ≤ T → T' = ⊥ ∨ T' = T) :
    ∃ k : ℕ, k < n ∧ T ≤ Mk k := by
  classical
  have hn0 : n ≠ 0 := by omega
  rcases eq_or_ne T ⊥ with hTbot | hTne
  · exact ⟨0, by omega, by rw [hTbot]; exact bot_le⟩
  · obtain ⟨f₀, hf₀T, hf₀⟩ : ∃ f ∈ T, f ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hTne (le_antisymm (fun x hx => by simpa using hcon x hx) bot_le)
    have key : ∀ m : ℕ, ∀ f ∈ T, f ≠ 0 → (supp f).card ≤ m →
        ∃ g ∈ T, g ≠ 0 ∧ (supp g).card = 1 := by
      intro m
      induction m with
      | zero =>
        intro f hfT hf hle
        have hpos : 0 < (supp f).card := Finset.card_pos.mpr ((ne_zero_iff_supp_nonempty hn0).mp hf)
        omega
      | succ m ih =>
        intro f hfT hf hle
        rcases Nat.lt_or_ge (supp f).card 2 with hlt | hge
        · refine ⟨f, hfT, hf, ?_⟩
          have hpos : 0 < (supp f).card :=
            Finset.card_pos.mpr ((ne_zero_iff_supp_nonempty hn0).mp hf)
          omega
        · obtain ⟨k₀, hk₀⟩ := Finset.card_pos.mp (by omega : 0 < (supp f).card)
          have hk₀n : k₀ < n := (mem_supp.mp hk₀).1
          have hgp : Polynomial.aeval (singAct ν) (minpoly (ZMod 2) (lam ν k₀)) f ∈ T :=
            aeval_mem hTξ hfT (minpoly (ZMod 2) (lam ν k₀))
          refine ih _ hgp ?_ ?_
          · rw [ne_zero_iff_supp_nonempty hn0, supp_aeval_minpoly hn ν hν hk₀n f]
            exact Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hk₀]; omega)
          · rw [supp_aeval_minpoly hn ν hν hk₀n f, Finset.card_erase_of_mem hk₀]
            omega
    obtain ⟨g, hgT, hg, hgcard⟩ := key (supp f₀).card f₀ hf₀T hf₀ le_rfl
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hgcard
    have hkmem : k ∈ supp g := by rw [hk]; exact Finset.mem_singleton_self k
    have hkn : k < n := (mem_supp.mp hkmem).1
    have hgMk : g ∈ Mk k := by
      refine mem_Mk.mpr ⟨pol g k, ?_⟩
      refine (eq_frobComp_of_supp_subset hn0 hkn ?_).symm
      intro j hj hjk
      by_contra hne
      have hjm : j ∈ supp g := mem_supp.mpr ⟨hj, hne⟩
      rw [hk, Finset.mem_singleton] at hjm
      exact hjk hjm
    let T' : Submodule (ZMod 2) (EndF n) := LinearMap.range (polEval ν g)
    have hT'le : T' ≤ T := by
      rintro h ⟨p, rfl⟩
      exact aeval_mem hTξ hgT p
    have hT'stab : ∀ h ∈ T', singAct ν h ∈ T' := by
      rintro h ⟨p, rfl⟩
      refine ⟨Polynomial.X * p, ?_⟩
      rw [polEval_apply, polEval_apply, Polynomial.aeval_mul, Polynomial.aeval_X,
        Module.End.mul_apply]
    have hT'ne : T' ≠ ⊥ := by
      intro hbot
      have hmem : g ∈ T' := ⟨1, by rw [polEval_apply, map_one, Module.End.one_apply]⟩
      rw [hbot] at hmem
      exact hg (by simpa using hmem)
    have hT'T : T' = T := by
      rcases hirr T' hT'stab hT'le with h | h
      · exact absurd h hT'ne
      · exact h
    have hT'Mk : T' ≤ Mk k := by
      rintro h ⟨p, rfl⟩
      exact aeval_mem (T := Mk k) (fun f hf => singAct_mem_Mk ν hf) hgMk p
    exact ⟨k, hkn, hT'T ▸ hT'Mk⟩

end Work.Higman.H8

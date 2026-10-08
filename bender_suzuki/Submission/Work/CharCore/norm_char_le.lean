import Mathlib
import Submission.Work.CharCore.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Bound on the values of an irreducible character: `‖χ g‖ ≤ χ 1`

For a finite group `G`, an irreducible complex character `χ` and any `g : G`, the value
`χ g` is a sum of `χ 1` roots of unity (the eigenvalues of `ρ g`), whence `‖χ g‖ ≤ χ 1`.

The main work is the general statement `norm_character_le_finrank` for an arbitrary
finite-dimensional complex representation: the eigenvalues of `ρ g` are `orderOf g`-th roots
of unity (because `(ρ g) ^ orderOf g = 1`), the trace is their sum (the characteristic
polynomial splits over `ℂ`), and the number of eigenvalues counted with multiplicity is
`finrank ℂ V`.
-/

noncomputable section

open Classical

namespace Work.CharCore

variable {G : Type*} [Group G] [Fintype G]

/-- For any finite-dimensional complex representation `ρ` of a finite group and any `g : G`,
the character value `ρ.character g` — a sum of `finrank ℂ V` roots of unity — has norm at
most `finrank ℂ V`. -/
theorem norm_character_le_finrank {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    ‖ρ.character g‖ ≤ (Module.finrank ℂ V : ℝ) := by
  have hsplits : (ρ g).charpoly.Splits := IsAlgClosed.splits _
  have htr : ρ.character g = (ρ g).charpoly.roots.sum :=
    Module.End.trace_eq_sum_roots_charpoly_of_splits hsplits
  -- every eigenvalue of `ρ g` is an `orderOf g`-th root of unity
  have hroot : ∀ x ∈ (ρ g).charpoly.roots, ‖x‖ = 1 := by
    intro x hx
    have hev : Module.End.HasEigenvalue (ρ g) x :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly (ρ g) x).2
        (Polynomial.isRoot_of_mem_roots hx)
    obtain ⟨v, hv⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hev
    have hpowmap : (ρ g) ^ orderOf g = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    have key : x ^ orderOf g • v = v := by
      rw [← Module.End.HasEigenvector.pow_apply hv (orderOf g), hpowmap, Module.End.one_apply]
    have hpow : x ^ orderOf g = 1 :=
      smul_left_injective ℂ hv.2 (by simpa using key)
    exact Complex.norm_eq_one_of_pow_eq_one hpow (ne_of_gt (orderOf_pos g))
  -- the number of eigenvalues with multiplicity is `finrank`
  have hcard : ((ρ g).charpoly.roots.card : ℝ) = (Module.finrank ℂ V : ℝ) := by
    have h1 := hsplits.natDegree_eq_card_roots
    have h2 := LinearMap.charpoly_natDegree (ρ g)
    rw [← h1, h2]
  have hsum : ‖(ρ g).charpoly.roots.sum‖ ≤ ((ρ g).charpoly.roots.card : ℝ) := by
    calc ‖((ρ g).charpoly.roots).sum‖
        ≤ (((ρ g).charpoly.roots).map (fun x => ‖x‖)).sum := norm_multiset_sum_le _
      _ = ((ρ g).charpoly.roots.map (fun _ => (1 : ℝ))).sum := by
            rw [Multiset.map_congr rfl hroot]
      _ = (((ρ g).charpoly.roots).card : ℝ) := by
            rw [Multiset.map_const']; simp [Multiset.sum_replicate]
  rw [htr]
  calc ‖(ρ g).charpoly.roots.sum‖ ≤ ((ρ g).charpoly.roots.card : ℝ) := hsum
    _ = (Module.finrank ℂ V : ℝ) := hcard

theorem norm_char_le {G : Type*} [Group G] [Fintype G] {χ : G → ℂ} (hχ : χ ∈ Irr G) (g : G) :
    ‖χ g‖ ≤ (irrDeg χ : ℝ) := by
  obtain ⟨N, hN, hNχ⟩ := exists_mem_irrSubmodules_of_mem_Irr hχ
  have h := norm_character_le_finrank (submoduleRep N) g
  rw [irrDeg_eq_finrank hχ hN hNχ, ← hNχ]
  exact h

end Work.CharCore

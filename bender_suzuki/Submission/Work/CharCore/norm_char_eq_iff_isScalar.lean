import Mathlib
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.irreducible_character_mem_Irr
import Submission.Work.CharCore.norm_sum_multiset

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Scalar values of an irreducible representation

For a finite group `G`, an irreducible finite-dimensional complex representation
`ρ : Representation ℂ G V` and an element `g : G`, the value `χ(g)` of the character is the
sum of the eigenvalues of `ρ g`, which are `orderOf g`-th roots of unity (with multiplicity
`finrank ℂ V = irrDeg χ`).  Hence `‖χ(g)‖ ≤ irrDeg χ` with equality precisely when all
eigenvalues coincide, i.e. when `ρ g` is a scalar matrix `c • 1` with `‖c‖ = 1`.

This is `Work.CharCore.norm_char_eq_iff_isScalar`.
-/

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

noncomputable section

open Classical

namespace Work.CharCore

/-- For an irreducible complex representation `ρ` of a finite group `G` and `g : G`, the
character value `ρ.character g` has modulus equal to the degree `irrDeg ρ.character` if and
only if `ρ g` is multiplication by a complex number of modulus `1`. -/
theorem norm_char_eq_iff_isScalar {G : Type*} [Group G] [Fintype G] {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (h : ρ.IsIrreducible)
    (g : G) : ‖ρ.character g‖ = (irrDeg ρ.character : ℝ) ↔
      ∃ c : ℂ, ‖c‖ = 1 ∧ ρ g = c • 1 := by
  have hχ : ρ.character ∈ Irr G := irreducible_character_mem_Irr ρ h
  -- `irrDeg ρ.character` is the dimension of `V`
  have hirr : irrDeg ρ.character = Module.finrank ℂ V := by
    have h1 := irrDeg_spec hχ
    rw [Representation.char_one] at h1
    exact Nat.cast_inj.mp h1.symm
  -- an irreducible representation is non-trivial
  haveI : Nontrivial V := by
    haveI : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp h
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  have hdpos : (0 : ℝ) < (Module.finrank ℂ V : ℝ) := by exact_mod_cast Module.finrank_pos
  constructor
  · -- the extremal case `‖χ(g)‖ = deg χ` forces a single eigenvalue
    intro hnorm
    have hnorm' : ‖ρ.character g‖ = (Module.finrank ℂ V : ℝ) := by rw [hnorm, hirr]
    have hsplits : (LinearMap.charpoly (ρ g)).Splits := IsAlgClosed.splits _
    have htrace : (ρ g).charpoly.roots.sum = ρ.character g := by
      rw [Representation.character, Module.End.trace_eq_sum_roots_charpoly_of_splits hsplits]
    -- all eigenvalues are roots of unity, hence of modulus one
    have hroots_norm : ∀ z ∈ (ρ g).charpoly.roots, ‖z‖ = 1 := by
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
    -- the number of eigenvalues with multiplicity is the dimension
    have hcardNat : (ρ g).charpoly.roots.card = Module.finrank ℂ V := by
      have h1 := hsplits.natDegree_eq_card_roots
      have h2 := LinearMap.charpoly_natDegree (ρ g)
      rw [← h1]; exact h2
    -- equality case of the triangle inequality
    have hsum_norm : ‖(ρ g).charpoly.roots.sum‖ = (((ρ g).charpoly.roots.card : ℕ) : ℝ) := by
      rw [htrace, hnorm', hcardNat]
    have hroots_eq := norm_sum_multiset hroots_norm hsum_norm
    refine ⟨ρ.character g / (Module.finrank ℂ V : ℂ), ?_, ?_⟩
    · rw [norm_div, Complex.norm_natCast, hnorm']
      exact div_self (by positivity)
    · -- every eigenvalue is `χ(g)/dim V`
      have heig : ∀ μ : ℂ, Module.End.HasEigenvalue (ρ g) μ →
          μ = ρ.character g / (Module.finrank ℂ V : ℂ) := by
        intro μ hμ
        have hmem : μ ∈ (ρ g).charpoly.roots := by
          rw [Polynomial.mem_roots (LinearMap.charpoly_monic (ρ g)).ne_zero]
          exact (Module.End.hasEigenvalue_iff_isRoot_charpoly (ρ g) μ).mp hμ
        have hh := hroots_eq μ hmem
        rw [hh, htrace, hcardNat]
      -- `ρ g` is semisimple because `(ρ g) ^ orderOf g = 1`
      have hTsemi : Module.End.IsSemisimple (ρ g) := by
        have hTpow : (ρ g) ^ orderOf g = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
        have hsep : (Polynomial.X ^ orderOf g - 1 : Polynomial ℂ).Separable :=
          Polynomial.X_pow_sub_one_separable_iff.mpr (by exact_mod_cast (orderOf_pos g).ne')
        have haeval : Polynomial.aeval (ρ g)
            (Polynomial.X ^ orderOf g - 1 : Polynomial ℂ) = 0 := by
          rw [map_sub, map_pow, Polynomial.aeval_X, map_one, hTpow, sub_self]
        exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree haeval
      -- the scalar `χ(g)/dim V` is semisimple
      have hcsemi : Module.End.IsSemisimple
          (algebraMap ℂ (Module.End ℂ V) (ρ.character g / (Module.finrank ℂ V : ℂ))) := by
        rw [Algebra.algebraMap_eq_smul_one]
        exact Module.End.IsSemisimple_smul _
          (by simpa [Module.End.one_eq_id] using Module.End.isSemisimple_id (R := ℂ) (M := V))
      -- so is their difference, which therefore vanishes since all its eigenvalues are zero
      have hzero : (ρ g) - algebraMap ℂ (Module.End ℂ V)
          (ρ.character g / (Module.finrank ℂ V : ℂ)) = 0 := by
        rw [Module.End.IsSemisimple.eq_zero_iff_forall_eigenvalue
          (Module.End.IsSemisimple.sub_of_commute
            (Algebra.commute_algebraMap_right _ (ρ g)) hTsemi hcsemi)]
        intro μ hμ
        rw [Module.End.hasEigenvalue_iff] at hμ
        obtain ⟨x, hx, hxne⟩ := (Submodule.ne_bot_iff _).mp hμ
        rw [Module.End.mem_eigenspace_iff] at hx
        have h1 : ((ρ g) - algebraMap ℂ (Module.End ℂ V)
            (ρ.character g / (Module.finrank ℂ V : ℂ))) x
            = (ρ g) x - (ρ.character g / (Module.finrank ℂ V : ℂ)) • x := by
          rw [LinearMap.sub_apply, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
            Module.End.one_apply]
        rw [h1] at hx
        have hTx : (ρ g) x = (μ + (ρ.character g / (Module.finrank ℂ V : ℂ))) • x := by
          rw [sub_eq_iff_eq_add] at hx
          rw [hx, ← add_smul]
        have he : Module.End.HasEigenvalue (ρ g)
            (μ + (ρ.character g / (Module.finrank ℂ V : ℂ))) := by
          rw [Module.End.hasEigenvalue_iff]
          exact (Submodule.ne_bot_iff _).mpr ⟨x, by
            rw [Module.End.mem_eigenspace_iff]; exact hTx, hxne⟩
        have hfin := heig _ he
        linear_combination hfin
      rw [sub_eq_zero, Algebra.algebraMap_eq_smul_one] at hzero
      exact hzero
  · -- conversely a scalar value has modulus exactly the degree
    rintro ⟨c, hc1, hcg⟩
    have hχg : ρ.character g = c * (Module.finrank ℂ V : ℂ) := by
      rw [Representation.character, hcg]
      rw [map_smul, LinearMap.trace_one]
      simp [smul_eq_mul]
    rw [hχg, hirr, norm_mul, Complex.norm_natCast, hc1, one_mul]

end Work.CharCore

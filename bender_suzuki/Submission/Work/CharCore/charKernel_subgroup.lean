import Mathlib
import Submission.Work.CharCore.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The kernel of an irreducible character is a normal subgroup

For an irreducible complex character `χ` of a finite group `G`, the level set
`charKernel χ = {g | χ g = χ 1}` is the underlying set of a normal subgroup of `G`
(namely the kernel of a representation affording `χ`).

Mathlib contains the character-theoretic facts (`Representation.character`,
`Module.End.trace_eq_sum_roots_charpoly_of_splits`), but not the elementary
linear-algebra input, which is proved here from scratch:

* `Work.CharCore.eq_one_of_trace_eq_finrank`: if `T` is an endomorphism of a
  finite dimensional complex vector space with `T ^ n = 1` for some `n > 0` and
  `trace T = finrank`, then `T = 1`.  Indeed `T` is semisimple (its minimal
  polynomial divides the squarefree polynomial `X ^ n - 1`), hence diagonalisable
  over `ℂ`, and the eigenvalues are roots of unity; their sum is `trace T`, which
  forces every eigenvalue to be `1`.  Then `T - 1` is semisimple, nilpotent, hence
  zero.

The main result is `Work.CharCore.charKernel_subgroup`.
-/

open Polynomial

namespace Work.CharCore

/-- `X ^ n - 1` is squarefree over `ℂ` for `n > 0`. -/
lemma sqf_X_pow_sub_one (n : ℕ) (hn : 0 < n) : Squarefree (X ^ n - 1 : ℂ[X]) := by
  have hn' : (n : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; omega
  have h1 : IsCoprime (X ^ n - 1 : ℂ[X]) (X ^ (n - 1)) := by
    refine ⟨-1, X, ?_⟩
    have hX : (X : ℂ[X]) * X ^ (n - 1) = X ^ n := by
      rw [← pow_succ']; congr 1; omega
    rw [hX]; ring
  have h2 : IsCoprime (X ^ n - 1 : ℂ[X]) (C (n : ℂ)) := by
    refine ⟨0, C ((n : ℂ)⁻¹), ?_⟩
    rw [zero_mul, zero_add, ← C_mul, inv_mul_cancel₀ hn']
    simp
  have h3 : IsCoprime (X ^ n - 1 : ℂ[X]) (C (n : ℂ) * X ^ (n - 1)) := h2.mul_right h1
  refine Polynomial.Separable.squarefree ?_
  show IsCoprime (X ^ n - 1 : ℂ[X]) (derivative (X ^ n - 1 : ℂ[X]))
  rw [derivative_sub, derivative_X_pow, derivative_one, sub_zero]
  exact h3

/-- A multiset of nonnegative reals with zero sum consists of zeros. -/
lemma multiset_sum_eq_zero_of_nonneg {s : Multiset ℝ} :
    (∀ x ∈ s, 0 ≤ x) → s.sum = 0 → ∀ x ∈ s, x = 0 := by
  induction s using Multiset.induction_on with
  | empty => intro _ _ x hx; simp at hx
  | cons a t ih =>
    intro h hs x hx
    have ha : 0 ≤ a := h a (Multiset.mem_cons_self a t)
    have ht : ∀ y ∈ t, 0 ≤ y := fun y hy => h y (Multiset.mem_cons_of_mem hy)
    rw [Multiset.sum_cons] at hs
    have htsum : 0 ≤ t.sum := Multiset.sum_nonneg ht
    have ha0 : a = 0 := by linarith
    have ht0 : t.sum = 0 := by linarith
    rcases Multiset.mem_cons.mp hx with rfl | hx'
    · exact ha0
    · exact ih ht ht0 x hx'

/-- An eigenvalue of an endomorphism of finite order is a root of unity. -/
lemma eig_pow_eq_one {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V →ₗ[ℂ] V) {n : ℕ} (hT : T ^ n = 1) {a : ℂ}
    (ha : Module.End.HasEigenvalue T a) : a ^ n = 1 := by
  obtain ⟨v, hv⟩ := ha.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hpow : ∀ k : ℕ, (T ^ k) v = (a ^ k) • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, hv.apply_eq_smul, map_smul, ih, smul_smul,
        mul_comm a (a ^ k), ← pow_succ]
  have h1 : (a ^ n) • v = v := by
    rw [← hpow n, hT]; simp
  exact smul_left_injective ℂ hv0 (by simpa using h1)

/-- **Key linear algebra input.**  An endomorphism of a finite dimensional complex vector
space that is of finite order and whose trace equals the dimension is the identity. -/
theorem eq_one_of_trace_eq_finrank {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) {n : ℕ} (hn : 0 < n) (hT : T ^ n = 1)
    (htr : LinearMap.trace ℂ V T = (Module.finrank ℂ V : ℂ)) : T = 1 := by
  -- `T` is a root of the squarefree polynomial `X ^ n - 1`, hence semisimple
  have hss : Module.End.IsSemisimple T :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero (sqf_X_pow_sub_one n hn) (by
      show Polynomial.aeval T (X ^ n - 1 : ℂ[X]) = 0
      simp only [map_sub, map_pow, Polynomial.aeval_X, map_one]
      rw [hT]; simp)
  -- the trace is the sum of the roots of the characteristic polynomial
  have hsp : T.charpoly.Splits := IsAlgClosed.splits _
  have hsum : T.charpoly.roots.sum = ((Module.finrank ℂ V : ℕ) : ℂ) := by
    rw [← Module.End.trace_eq_sum_roots_charpoly_of_splits hsp]
    exact htr
  -- every root is an eigenvalue, hence a root of unity
  have hroot_normSq : ∀ a ∈ T.charpoly.roots, Complex.normSq a = 1 := by
    intro a ha
    have hev : Module.End.HasEigenvalue T a :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly T a).mpr (Polynomial.isRoot_of_mem_roots ha)
    have han : a ^ n = 1 := eig_pow_eq_one T hT hev
    have hns : (Complex.normSq a) ^ n = 1 := by
      rw [← map_pow, han]; simp
    exact (pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg a) (Nat.pos_iff_ne_zero.mp hn)).mp hns
  have hroot_re : ∀ a ∈ T.charpoly.roots, a.re ≤ 1 := by
    intro a ha
    have hns := hroot_normSq a ha
    have hnorm : ‖a‖ = 1 := by
      have h2 : ‖a‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq, hns]
      rcases sq_eq_one_iff.mp h2 with h | h
      · exact h
      · linarith [norm_nonneg a]
    calc a.re ≤ ‖a‖ := Complex.re_le_norm a
      _ = 1 := hnorm
  have hcard : T.charpoly.roots.card = Module.finrank ℂ V :=
    (Polynomial.splits_iff_card_roots.mp hsp).trans (LinearMap.charpoly_natDegree T)
  have hkey : ∀ (m : Multiset ℂ), (m.map (fun z : ℂ => (1 : ℝ) - z.re)).sum =
      (m.card : ℝ) - (m.map Complex.re).sum := by
    intro m
    induction m using Multiset.induction_on with
    | empty => simp
    | cons a t ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih]
      push_cast
      ring
  -- summing `1 - re` over the roots gives zero, so every root has real part one
  have hroot_one : ∀ a ∈ T.charpoly.roots, a = 1 := by
    have hsum0 : (T.charpoly.roots.map (fun z : ℂ => (1 : ℝ) - z.re)).sum = 0 := by
      rw [hkey, hcard]
      have hre : (T.charpoly.roots.map Complex.re).sum = ((Module.finrank ℂ V : ℕ) : ℝ) := by
        have h := Multiset.sum_hom (T.charpoly.roots) Complex.reAddGroupHom
        simpa [hsum] using h
      rw [hre]; ring
    have hnonneg : ∀ x ∈ T.charpoly.roots.map (fun z : ℂ => (1 : ℝ) - z.re), 0 ≤ x := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
      linarith [hroot_re a ha]
    intro a ha
    have h1 : (1 : ℝ) - a.re = 0 :=
      multiset_sum_eq_zero_of_nonneg hnonneg hsum0 _ (Multiset.mem_map.mpr ⟨a, ha, rfl⟩)
    have hre : a.re = 1 := by linarith
    have hns : Complex.normSq a = 1 := hroot_normSq a ha
    have him : a.im = 0 := by
      have him2 : a.im * a.im = 0 := by
        rw [Complex.normSq_apply, hre] at hns
        linarith
      exact mul_self_eq_zero.mp him2
    exact Complex.ext hre (by rw [him]; simp)
  -- hence every eigenvalue of `T` is `1`
  have hEig : ∀ a : ℂ, Module.End.HasEigenvalue T a → a = 1 := by
    intro a ha
    have hmem : a ∈ T.charpoly.roots := by
      rw [Polynomial.mem_roots (LinearMap.charpoly_monic T).ne_zero]
      exact (Module.End.hasEigenvalue_iff_isRoot_charpoly T a).mp ha
    exact hroot_one a hmem
  -- `T - 1` is semisimple with all eigenvalues zero, hence zero
  have hSss : Module.End.IsSemisimple (T - 1) := by
    have := (Module.End.isSemisimple_sub_algebraMap_iff (f := T) (μ := (1 : ℂ))).mpr hss
    simpa using this
  have hS0 : T - 1 = 0 := by
    refine (Module.End.IsSemisimple.eq_zero_iff_forall_eigenvalue hSss).mpr ?_
    intro μ hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    have hv0 : v ≠ 0 := hv.2
    have hTμ : Module.End.HasEigenvalue T (1 + μ) := by
      refine (Submodule.ne_bot_iff _).mpr ⟨v, ?_, hv0⟩
      rw [Module.End.mem_eigenspace_iff]
      have h1 : (T : Module.End ℂ V) v = ((T - 1) + 1) v := by rw [sub_add_cancel]
      rw [h1, LinearMap.add_apply, hv.apply_eq_smul,
        show (1 : V →ₗ[ℂ] V) v = v from rfl, add_smul, one_smul, add_comm]
    exact add_left_cancel (by rw [hEig (1 + μ) hTμ]; ring)
  exact sub_eq_zero.mp hS0

/-- **The kernel of an irreducible character is a normal subgroup.** -/
theorem charKernel_subgroup {G : Type*} [Group G] [Fintype G] {χ : G → ℂ} (hχ : χ ∈ Irr G) :
    ∃ K : Subgroup G, K.Normal ∧ (K : Set G) = charKernel χ := by
  obtain ⟨N, _hN, hNχ⟩ := exists_mem_irrSubmodules_of_mem_Irr hχ
  refine ⟨(MonoidHom.toHomUnits (submoduleRep N)).ker, MonoidHom.normal_ker _, ?_⟩
  ext g
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  constructor
  · intro h
    have hρ : submoduleRep N g = 1 := by
      have h1 : ((MonoidHom.toHomUnits (submoduleRep N)) g : N →ₗ[ℂ] N) = 1 := by
        rw [h, Units.val_one]
      rwa [MonoidHom.coe_toHomUnits] at h1
    rw [← hNχ]
    exact congrArg (fun h => LinearMap.trace ℂ N h) (by rw [hρ, map_one (submoduleRep N)])
  · intro h
    have hchar : (submoduleRep N).character g = (submoduleRep N).character 1 := by
      rw [hNχ]; exact h
    have htr : LinearMap.trace ℂ N ((submoduleRep N) g) = (Module.finrank ℂ N : ℂ) := by
      rw [← Representation.char_one (submoduleRep N)]
      exact hchar
    have hpow : ((submoduleRep N) g) ^ (Fintype.card G) = 1 := by
      rw [← map_pow (submoduleRep N) g (Fintype.card G), pow_card_eq_one, map_one]
    have hρ : submoduleRep N g = 1 :=
      eq_one_of_trace_eq_finrank ((submoduleRep N) g) (Fintype.card_pos_iff.mpr ⟨1⟩) hpow htr
    rw [← Units.val_eq_one, MonoidHom.coe_toHomUnits]
    exact hρ

end Work.CharCore

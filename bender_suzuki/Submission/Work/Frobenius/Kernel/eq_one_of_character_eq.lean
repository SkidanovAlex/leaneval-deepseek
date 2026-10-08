import Mathlib
import Submission.Work.Frobenius.Char

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `χ x = χ 1` implies that `x` lies in the kernel

If the character of a finite-dimensional complex representation of a finite group takes the
same value at `x` and at `1`, then `ρ x = 1`.

The proof is the classical eigenvalue argument.  Let `V` be the space of the representation
and `f = ρ x`, of finite order `n = orderOf x`.  Over `ℂ`:

* `X ^ n - 1` is squarefree and kills `f`, so `f` is semisimple
  (`Module.End.isSemisimple_of_squarefree_aeval_eq_zero`);
* the characteristic polynomial of `f` splits, and its roots are the eigenvalues of `f`
  counted with multiplicity (they sum to `LinearMap.trace ℂ V f` and there are
  `finrank ℂ V` of them); every root `z` satisfies `z ^ n = 1`, so `‖z‖ = 1` and
  `z.re ≤ 1`;
* `LinearMap.trace ℂ V f = finrank ℂ V` therefore says that a sum of `finrank ℂ V` complex
  numbers of modulus one equals `finrank ℂ V`; taking real parts shows that every root is `1`;
* hence every eigenvalue of `f` is `1`, so `f - 1` is a semisimple endomorphism all of whose
  eigenvalues vanish, whence `f - 1 = 0`.

Nothing here uses the irreducibility of the representation; the statement holds for an
arbitrary finite-dimensional complex representation of a finite group.
-/

@[expose] public section

noncomputable section

namespace Work.Frobenius.Kernel

variable {G : Type*} [Group G] [Fintype G]

/-- A sum of nonnegative reals which vanishes has only zero terms. -/
theorem Multiset_eq_zero_of_sum_eq_zero_of_nonneg (s : Multiset ℝ) :
    (∀ x ∈ s, 0 ≤ x) → s.sum = 0 → ∀ x ∈ s, x = 0 := by
  induction s using Multiset.induction with
  | empty => intro _ _ x hx; simp at hx
  | cons a s ih =>
    intro h hs x hx
    have ha : 0 ≤ a := h a (Multiset.mem_cons_self a s)
    have hs' : 0 ≤ s.sum := Multiset.sum_nonneg fun y hy => h y (Multiset.mem_cons_of_mem hy)
    rw [Multiset.sum_cons] at hs
    have ha0 : a = 0 := by linarith
    have hs0 : s.sum = 0 := by linarith
    rcases Multiset.mem_cons.mp hx with rfl | hx
    · exact ha0
    · exact ih (fun y hy => h y (Multiset.mem_cons_of_mem hy)) hs0 x hx

/-- The sum of the real parts of the numbers `1 - z`, `z` running through a multiset. -/
theorem multiset_sum_one_sub_re (s : Multiset ℂ) :
    (s.map (fun z => (1 - z).re)).sum = (s.card : ℝ) - (s.sum).re := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons, Multiset.card_cons, ih]
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re]
    push_cast
    ring

/-- A complex number of modulus one with real part one is `1`. -/
theorem complex_eq_one_of_re_eq_one_of_norm_eq_one {z : ℂ} (hre : z.re = 1) (hn : ‖z‖ = 1) :
    z = 1 := by
  have hns : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hn, one_pow]
  rw [Complex.normSq_apply] at hns
  have him : z.im = 0 := by
    have : z.im * z.im = 0 := by nlinarith [hre, hns]
    exact mul_self_eq_zero.mp this
  exact Complex.ext (by simp [hre]) (by simp [him])

/-- A multiset of `n`-th roots of unity whose sum equals its cardinality consists only of
ones. -/
theorem multiset_eq_one_of_pow_eq_one_of_sum_eq_card {n : ℕ} (hn : 0 < n) (s : Multiset ℂ) :
    (∀ z ∈ s, z ^ n = 1) → s.sum = (s.card : ℂ) → ∀ z ∈ s, z = 1 := by
  intro hpow hsum z hz
  have hnorm : ∀ w ∈ s, ‖w‖ = 1 :=
    fun w hw => Complex.norm_eq_one_of_pow_eq_one (hpow w hw) hn.ne'
  have hre : ∀ w ∈ s, w.re ≤ 1 := by
    intro w hw
    simpa [hnorm w hw] using Complex.re_le_norm w
  have hzero : (s.map (fun w => (1 - w).re)).sum = 0 := by
    rw [multiset_sum_one_sub_re, hsum]
    simp
  have h1 : ∀ x ∈ s.map (fun w => (1 - w).re), x = 0 :=
    Multiset_eq_zero_of_sum_eq_zero_of_nonneg _
      (fun x hx => by
        obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hx
        simp [Complex.sub_re, hre w hw]) hzero
  have hzre : z.re = 1 := by
    have h := h1 _ (Multiset.mem_map_of_mem (fun w => (1 - w).re) hz)
    simp only [Complex.sub_re, Complex.one_re] at h
    linarith
  exact complex_eq_one_of_re_eq_one_of_norm_eq_one hzre (hnorm z hz)

/-- A finite order complex endomorphism whose trace is the dimension of the space is the
identity.  (Indeed its eigenvalues are roots of unity, so this follows from the fact that a
sum of `finrank` complex numbers of modulus one equals `finrank` only if all of them are
one.) -/
theorem end_eq_one_of_pow_eq_one_of_trace_eq_finrank
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) {n : ℕ} (hn : 0 < n) (hpow : f ^ n = 1)
    (htr : LinearMap.trace ℂ V f = (Module.finrank ℂ V : ℂ)) : f = 1 := by
  have hsep : (Polynomial.X ^ n - 1 : Polynomial ℂ).Separable := by
    rw [Polynomial.X_pow_sub_one_separable_iff]
    exact_mod_cast hn.ne'
  have haeval : Polynomial.aeval f (Polynomial.X ^ n - 1 : Polynomial ℂ) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, map_one, hpow, sub_self]
  have hsemi : f.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree haeval
  have hsplits : (LinearMap.charpoly f).Splits := IsAlgClosed.splits _
  have hcard : (LinearMap.charpoly f).roots.card = Module.finrank ℂ V := by
    rw [← hsplits.natDegree_eq_card_roots, LinearMap.charpoly_natDegree]
  have hsum : (LinearMap.charpoly f).roots.sum = (((LinearMap.charpoly f).roots.card : ℕ) : ℂ) := by
    rw [← Module.End.trace_eq_sum_roots_charpoly_of_splits hsplits, htr, hcard]
  have hroot1 : ∀ z ∈ (LinearMap.charpoly f).roots, z = 1 := by
    refine multiset_eq_one_of_pow_eq_one_of_sum_eq_card hn _ ?_ hsum
    intro z hz
    have hev : f.HasEigenvalue z :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly f z).mpr (Polynomial.isRoot_of_mem_roots hz)
    obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
    have key : z ^ n • v = v := by
      rw [← hv.pow_apply n, hpow, Module.End.one_apply]
    exact smul_left_injective ℂ hv.2 (by simpa using key)
  have heig : ∀ μ : ℂ, f.HasEigenvalue μ → μ = 1 := by
    intro μ hμ
    exact hroot1 μ ((Polynomial.mem_roots (LinearMap.charpoly_monic f).ne_zero).mpr
      ((Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).mp hμ))
  have hg : (f - 1).IsSemisimple := by
    have := hsemi.aeval (Polynomial.X - 1)
    simpa [map_sub, Polynomial.aeval_X, Polynomial.aeval_one] using this
  have hzero : f - 1 = 0 := (Module.End.IsSemisimple.eq_zero_iff_forall_eigenvalue hg).mpr (by
    intro μ hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    have hv' : f.HasEigenvector (μ + 1) v := by
      refine (Module.End.hasEigenvector_iff).mpr ⟨(Module.End.mem_eigenspace_iff).mpr ?_, hv.2⟩
      have h := hv.apply_eq_smul
      rw [LinearMap.sub_apply, Module.End.one_apply] at h
      rw [sub_eq_iff_eq_add.mp h, add_smul, one_smul]
    have h1 := heig (μ + 1) (Module.End.hasEigenvalue_of_hasEigenvector hv')
    have h2 : (μ + 1) - 1 = 1 - 1 := congrArg (fun z => z - 1) h1
    simpa using h2)
  exact sub_eq_zero.mp hzero

theorem eq_one_of_character_eq {G : Type*} [Group G] [Fintype G] (d : IrrRep G) {x : G} (h : d.ρ.character x = d.ρ.character 1) : x ∈ d.ρ.ker := by
  rw [MonoidHom.mem_ker]
  have htr : LinearMap.trace ℂ d.V (d.ρ x) = (Module.finrank ℂ d.V : ℂ) := by
    simpa [Representation.character] using h
  refine end_eq_one_of_pow_eq_one_of_trace_eq_finrank (d.ρ x) (orderOf_pos x) ?_ htr
  rw [← map_pow, pow_orderOf_eq_one, map_one]

end Work.Frobenius.Kernel

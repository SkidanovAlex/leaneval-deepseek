import Mathlib
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_compl
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_union_of_disjoint
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_union_of_density_zero
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_finite
import Submission.Work.CFTLib.splitSetOf_density

/-!
# Class fields with the same split set come from proportional characters

This file proves that two nontrivial characters of the ideal class group of a number field `K`,
whose class fields (of prime degree `p`) have the same set of primes of inertia degree `1`, are
proportional.

The argument is the classical one: writing `χ_a := χ · (χ')^{-a}` for `a ∈ F_p` and
`T_a := {v | χ_a [v] = 1}`, `T_∞ := {v | χ' [v] = 1}`, the `p+1` sets `T_a`, `T_∞` cover all
primes, any two of them meet exactly in `C := {v | χ [v] = χ' [v] = 1}`, and each of them is the
split set of a genuine class field, hence has Dirichlet density `1/p`.  If `C = T_0` (which is what
the hypothesis that `L` and `L'` have the same split set provides), each `T_i \ C` has density
`1/p - 1/p = 0`, so the whole set of primes — a finite union of copies of `C` and of such
`T_i \ C` — has density `1/p`, forcing `1/p = 1`.  Hence some `χ_a` is trivial, i.e. `χ = (χ')^a`.
-/

namespace Work.CFTLib

open NumberField

/-- The ideal class of a nonzero prime ideal. -/
noncomputable def primeCls {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ClassGroup (𝓞 K) :=
  ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩

/-! ## Density tools -/

/-- The set of all primes of a number field has Dirichlet density `1`. -/
theorem hasDirichletDensity_univ {K : Type*} [Field K] [NumberField K] :
    NumberField.Set.HasDirichletDensity
      (Set.univ : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) 1 := by
  have h := Commons.NumberTheory.NumberField.Set.hasDirichletDensity_compl (K := K)
    (S := (∅ : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))))
    (δ := 0)
    (Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_finite (K := K)
      (S := (∅ : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))) Set.finite_empty)
  simpa using h

/-- If `C ⊆ T` and both `T` and `C` have Dirichlet densities `δ` and `γ`, then `T \ C` has
Dirichlet density `δ - γ`. -/
theorem hasDirichletDensity_sdiff {K : Type*} [Field K] [NumberField K]
    {C T : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))} {δ γ : ℝ} (hCT : C ⊆ T)
    (hT : NumberField.Set.HasDirichletDensity T δ)
    (hC : NumberField.Set.HasDirichletDensity C γ) :
    NumberField.Set.HasDirichletDensity (T \ C) (δ - γ) := by
  have hdisj : Disjoint Tᶜ C := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hx (hCT hx')
  have hTc : NumberField.Set.HasDirichletDensity Tᶜ (1 - δ) :=
    Commons.NumberTheory.NumberField.Set.hasDirichletDensity_compl hT
  have hun : NumberField.Set.HasDirichletDensity (Tᶜ ∪ C) ((1 - δ) + γ) :=
    Commons.NumberTheory.NumberField.Set.hasDirichletDensity_union_of_disjoint hdisj hTc hC
  have hc := Commons.NumberTheory.NumberField.Set.hasDirichletDensity_compl hun
  have hset : (Tᶜ ∪ C)ᶜ = T \ C := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_sdiff]
    tauto
  rw [hset] at hc
  convert hc using 1
  ring

/-- A finite union of sets of Dirichlet density `0` has Dirichlet density `0`. -/
theorem hasDirichletDensity_iUnion_finset_zero {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] (P : ι → Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (h : ∀ i, NumberField.Set.HasDirichletDensity (P i) 0) :
    NumberField.Set.HasDirichletDensity (⋃ i, P i) 0 := by
  classical
  have key : ∀ s : Finset ι,
      NumberField.Set.HasDirichletDensity (⋃ i ∈ s, P i) 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        have h0 : (⋃ i ∈ (∅ : Finset ι), P i) =
            (∅ : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) := by
          ext x
          simp
        rw [h0]
        exact Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_finite
          Set.finite_empty
    | insert a s ha ih =>
        have hun : (⋃ i ∈ insert a s, P i) = P a ∪ ⋃ i ∈ s, P i :=
          Finset.set_biUnion_insert a s P
        rw [hun]
        exact Commons.NumberTheory.NumberField.Set.hasDirichletDensity_union_of_density_zero
          (h a) ih
  simpa using key Finset.univ

/-- **A finite family of sets of primes of equal density, meeting pairwise in a common subset.**

If a finite nonempty family `T` of sets of primes all have the same Dirichlet density `δ` as a
common subset `C ⊆ T i`, if `T i ∩ T j ⊆ C` for `i ≠ j` and the `T i` cover all primes, and if
`δ ≠ 1`, then we reach a contradiction: each `T i \ C` has density `0`, finitely many of them
cover `univ \ C`, so `univ` has density `δ`, whence `δ = 1`. -/
theorem false_of_density_family {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {T : ι → Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))}
    {C : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))} {δ : ℝ}
    (hT : ∀ i, NumberField.Set.HasDirichletDensity (T i) δ)
    (hC : NumberField.Set.HasDirichletDensity C δ)
    (hsub : ∀ i, C ⊆ T i)
    (hpair : ∀ i j, i ≠ j → T i ∩ T j ⊆ C)
    (hcov : (⋃ i, T i) = Set.univ)
    (hδ : δ ≠ 1) : False := by
  classical
  -- each `T i \ C` has density `δ - δ = 0`
  have hpiece : ∀ i, NumberField.Set.HasDirichletDensity (T i \ C) (δ - δ) :=
    fun i => hasDirichletDensity_sdiff (hsub i) (hT i) hC
  -- the pieces are pairwise disjoint
  have hdisj : ∀ i j, i ≠ j → Disjoint (T i \ C) (T j \ C) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hx hy
    obtain ⟨hxT, hxC⟩ := (Set.mem_sdiff x).mp hx
    obtain ⟨hyT, -⟩ := (Set.mem_sdiff x).mp hy
    exact hxC (hpair i j hij ⟨hxT, hyT⟩)
  -- the union of the pieces has density `0`
  have hU : NumberField.Set.HasDirichletDensity (⋃ i, T i \ C) 0 := by
    have h1 : NumberField.Set.HasDirichletDensity (⋃ i ∈ (Finset.univ : Finset ι), T i \ C) 0 := by
      refine hasDirichletDensity_iUnion_finset_zero _ ?_
      intro i
      simpa using hpiece i
    simpa using h1
  -- the union of the pieces is everything outside `C`
  have hUeq : (⋃ i, T i \ C) = Set.univ \ C := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hx'⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hxT, hxC⟩ := (Set.mem_sdiff x).mp hx'
      refine (Set.mem_sdiff x).mpr ⟨?_, hxC⟩
      rw [← hcov]
      exact Set.mem_iUnion.mpr ⟨i, hxT⟩
    · intro hx
      obtain ⟨hxU, hxC⟩ := (Set.mem_sdiff x).mp hx
      have hx' : x ∈ ⋃ i, T i := by rw [hcov]; exact hxU
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx'
      exact Set.mem_iUnion.mpr ⟨i, (Set.mem_sdiff x).mpr ⟨hi, hxC⟩⟩
  -- `univ` splits as `C ⊔ (univ \ C)`
  rw [hUeq] at hU
  have huniv : NumberField.Set.HasDirichletDensity
      (Set.univ : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) (δ + 0) := by
    have h2 : NumberField.Set.HasDirichletDensity
        (C ∪ (Set.univ \ C)) (δ + 0) :=
      Commons.NumberTheory.NumberField.Set.hasDirichletDensity_union_of_disjoint
        disjoint_sdiff_self_right hC hU
    rw [Set.union_sdiff_self, Set.union_univ] at h2
    exact h2
  have h1 : NumberField.Set.HasDirichletDensity
      (Set.univ : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) 1 :=
    hasDirichletDensity_univ
  have : δ + 0 = 1 := tendsto_nhds_unique huniv h1
  exact hδ (by simpa using this)

/-! ## The split set of a nontrivial character -/

/-- The set of primes `v` with `χ [v] = 1` has Dirichlet density `1/p`, provided `χ ≠ 1` has a
class field of degree `p`. -/
theorem hasDirichletDensity_charSplitSet {K : Type} [Field K] [NumberField K] (p : ℕ)
    [Fact p.Prime]
    (hCF : ∀ (χ : ClassGroup (𝓞 K) →* Multiplicative (ZMod p)), χ ≠ 1 →
      ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L)
        (_ : FiniteDimensional K L),
        IsGalois K L ∧ Module.finrank K L = p ∧
        ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          (Ideal.inertiaDegIn v.asIdeal (𝓞 L) = 1 ↔
            χ (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) = 1))
    (χ : ClassGroup (𝓞 K) →* Multiplicative (ZMod p)) (hχ : χ ≠ 1) :
    NumberField.Set.HasDirichletDensity
      {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) | χ (primeCls v) = 1}
      (1 / (p : ℝ)) := by
  obtain ⟨L, hLf, hLn, hLa, hLfd, _hgal, hfr, hlaw⟩ := hCF χ hχ
  have h := splitSetOf_density (K := K) (L := L)
  rw [hfr] at h
  have hset : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
        Ideal.inertiaDegIn v.asIdeal (𝓞 L) = 1} =
      {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) | χ (primeCls v) = 1} := by
    ext v
    exact hlaw v
  rw [hset] at h
  exact h

/-! ## The character `χ - a χ'` -/

/-- The character `χ · (χ')^{-a}`, i.e. `v ↦ χ[v] - a χ'[v]` in additive notation. -/
noncomputable def chiSub {p : ℕ} {K : Type*} [Field K] [NumberField K]
    (χ χ' : ClassGroup (𝓞 K) →* Multiplicative (ZMod p)) (a : ZMod p) :
    ClassGroup (𝓞 K) →* Multiplicative (ZMod p) :=
  χ * (χ' ^ a.val)⁻¹

theorem chiSub_apply {p : ℕ} {K : Type*} [Field K] [NumberField K]
    (χ χ' : ClassGroup (𝓞 K) →* Multiplicative (ZMod p)) (a : ZMod p)
    (c : ClassGroup (𝓞 K)) :
    chiSub χ χ' a c = χ c * ((χ' c) ^ a.val)⁻¹ := by
  rw [chiSub, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply]

/-- `χ - a χ'` vanishes at a prime class iff `χ = a χ'` there, in additive notation. -/
theorem chiSub_eq_one_iff {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
    (χ χ' : ClassGroup (𝓞 K) →* Multiplicative (ZMod p)) (a : ZMod p)
    (c : ClassGroup (𝓞 K)) :
    chiSub χ χ' a c = 1 ↔ (χ c).toAdd = a * (χ' c).toAdd := by
  rw [chiSub_apply, mul_inv_eq_one]
  constructor
  · intro h
    rw [h, toAdd_pow, nsmul_eq_mul, ZMod.natCast_zmod_val]
  · intro h
    have h2 : ((χ' c) ^ a.val).toAdd = a * (χ' c).toAdd := by
      rw [toAdd_pow, nsmul_eq_mul, ZMod.natCast_zmod_val]
    exact Multiplicative.toAdd.injective (h.trans h2.symm)

/-! ## The family of split sets of the characters `χ - a χ'`, and of `χ'` -/

/-- The family of primes with `χ [v] = a χ' [v]` for `a ∈ F_p`, together with the primes with
`χ' [v] = 0` (the index `none`). -/
def charFamily {K : Type*} [Field K] [NumberField K] {p : ℕ}
    (χ χ' : ClassGroup (𝓞 K) →* Multiplicative (ZMod p)) :
    Option (ZMod p) → Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) := fun i =>
  match i with
  | none => {v | (χ' (primeCls v)).toAdd = 0}
  | some a => {v | (χ (primeCls v)).toAdd = a * (χ' (primeCls v)).toAdd}

/-- The "kernel" set `{v | χ [v] = 0}`. -/
def charKernel {K : Type*} [Field K] [NumberField K] {p : ℕ}
    (χ : ClassGroup (𝓞 K) →* Multiplicative (ZMod p)) :
    Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
  {v | (χ (primeCls v)).toAdd = 0}

theorem charFamily_zero_eq_charKernel {K : Type*} [Field K] [NumberField K] {p : ℕ}
    (χ χ' : ClassGroup (𝓞 K) →* Multiplicative (ZMod p)) :
    charFamily χ χ' (some 0) = charKernel χ := by
  ext v
  simp [charFamily, charKernel]

theorem charFamily_none_eq {K : Type*} [Field K] [NumberField K] {p : ℕ}
    (χ χ' : ClassGroup (𝓞 K) →* Multiplicative (ZMod p)) :
    charFamily χ χ' none = {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) | χ' (primeCls v) = 1} := by
  ext v
  simp only [charFamily]
  exact toAdd_eq_zero

theorem charKernel_eq {K : Type*} [Field K] [NumberField K] {p : ℕ}
    (χ : ClassGroup (𝓞 K) →* Multiplicative (ZMod p)) :
    charKernel χ = {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) | χ (primeCls v) = 1} := by
  ext v
  exact toAdd_eq_zero

/-- Two distinct values of `a` in a field force `w = 0` from `u = a w = b w`. -/
theorem zmod_eq_zero_of_mul_eq {p : ℕ} [Fact p.Prime] {a b u w : ZMod p}
    (h1 : u = a * w) (h2 : u = b * w) (hab : a ≠ b) : u = 0 ∧ w = 0 := by
  have h : (a - b) * w = 0 := by rw [sub_mul, ← h1, ← h2, sub_self]
  have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hw : w = 0 := (mul_eq_zero.mp h).resolve_left hne
  exact ⟨by rw [h1, hw, mul_zero], hw⟩

/-- **Class fields with the same split set come from proportional characters.**

Let `K` be a number field, `p` a prime, and let `χ`, `χ' : Cl(𝓞 K) →* Multiplicative (ZMod p)` be
nontrivial characters with class fields `L`, `L'` (Galois of degree `p` over `K`, with
`inertiaDegIn v (𝓞 L) = 1 ↔ χ [v] = 1`, and similarly for `χ'`).  If `L` and `L'` have the same
set of primes with inertia degree `1`, then `χ` and `χ'` are proportional, i.e. `χ = χ'^a` for
some `a`.

(Proof strategy: put `T_a := {v | χ_a [v] = 1}` for `χ_a := χ - a χ'` (`a ∈ ZMod p`) and
`T_∞ := T_{χ'}`.  Each `T_a` is the split set of the class field of `χ_a` (a genuine class field
by the hypothesis on characters), hence has Dirichlet density `1/p`; the `T_a` for
`a ∈ P¹(F_p)` cover all but finitely many primes; and `T_a ∩ T_b = {χ = χ' = 0}` for `a ≠ b` up
to finite sets.  Hence the density of `C := {v | χ [v] = χ' [v] = 0}` is `1/p²`.  If the split
sets of `L` and `L'` are equal they are both contained in `C` and have density `1/p`, whence
`1/p ≤ 1/p²`, a contradiction unless `χ, χ'` are proportional.) -/
theorem splitSet_eq_imp_proportional {K : Type} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (hCF : ∀ (χ : ClassGroup (𝓞 K) →* Multiplicative (ZMod p)), χ ≠ 1 →
      ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L)
        (_ : FiniteDimensional K L),
        IsGalois K L ∧ Module.finrank K L = p ∧
        ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          (Ideal.inertiaDegIn v.asIdeal (𝓞 L) = 1 ↔
            χ (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) = 1))
    {χ χ' : ClassGroup (𝓞 K) →* Multiplicative (ZMod p)} (hχ : χ ≠ 1) (hχ' : χ' ≠ 1)
    {L L' : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Field L'] [NumberField L'] [Algebra K L'] [FiniteDimensional K L'] [IsGalois K L']
    (hL : Module.finrank K L = p) (hL' : Module.finrank K L' = p)
    (hlaw : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      (Ideal.inertiaDegIn v.asIdeal (𝓞 L) = 1 ↔
        χ (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) = 1))
    (hlaw' : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      (Ideal.inertiaDegIn v.asIdeal (𝓞 L') = 1 ↔
        χ' (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) = 1))
    (hsplit : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
        Ideal.inertiaDegIn v.asIdeal (𝓞 L) = 1} =
      {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
        Ideal.inertiaDegIn v.asIdeal (𝓞 L') = 1}) :
    ∃ a : ℕ, ∀ c : ClassGroup (𝓞 K), χ c = χ' c ^ a := by
  classical
  by_cases hex : ∃ a : ZMod p, chiSub χ χ' a = 1
  · -- some `χ - a χ'` is trivial: done
    obtain ⟨a, ha⟩ := hex
    have h1 : χ = χ' ^ a.val := mul_inv_eq_one.mp ha
    exact ⟨a.val, fun c => by rw [h1, MonoidHom.pow_apply]⟩
  · -- otherwise the family of split sets contradicts the density computation
    have hne : ∀ a : ZMod p, chiSub χ χ' a ≠ 1 := fun a ha => hex ⟨a, ha⟩
    exfalso
    -- `C` is the set of primes where both `χ` and `χ'` vanish
    have hCT : charKernel χ = charFamily χ χ' none := by
      rw [charKernel_eq, charFamily_none_eq]
      have e1 : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
            Ideal.inertiaDegIn v.asIdeal (𝓞 L) = 1} =
          {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) | χ (primeCls v) = 1} := by
        ext v
        exact hlaw v
      have e2 : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
            Ideal.inertiaDegIn v.asIdeal (𝓞 L') = 1} =
          {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) | χ' (primeCls v) = 1} := by
        ext v
        exact hlaw' v
      rw [← e1, ← e2]
      exact hsplit
    refine false_of_density_family (ι := Option (ZMod p))
      (T := charFamily χ χ') (C := charKernel χ) (δ := 1 / (p : ℝ)) ?_ ?_ ?_ ?_ ?_ ?_
    · -- each member of the family has density `1/p`
      intro i
      rcases i with _ | a
      · rw [charFamily_none_eq]
        exact hasDirichletDensity_charSplitSet p hCF χ' hχ'
      · have hset : charFamily χ χ' (some a) =
            {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) | chiSub χ χ' a (primeCls v) = 1} := by
          ext v
          simp only [charFamily, Set.mem_ofPred_eq]
          exact (chiSub_eq_one_iff χ χ' a (primeCls v)).symm
        rw [hset]
        exact hasDirichletDensity_charSplitSet p hCF (chiSub χ χ' a) (hne a)
    · -- `C` has density `1/p`
      rw [charKernel_eq]
      exact hasDirichletDensity_charSplitSet p hCF χ hχ
    · -- `C ⊆ T i` for all `i`
      intro i
      rcases i with _ | a
      · exact le_of_eq hCT
      · intro v hv
        have hv1 : (χ (primeCls v)).toAdd = 0 := hv
        have hv2 : (χ' (primeCls v)).toAdd = 0 := by
          have : v ∈ charFamily χ χ' none := by rw [← hCT]; exact hv
          simpa only [charFamily, Set.mem_ofPred_eq] using this
        show (χ (primeCls v)).toAdd = a * (χ' (primeCls v)).toAdd
        rw [hv1, hv2, mul_zero]
    · -- distinct members meet in `C`
      intro i j hij v hv
      rcases i with _ | a <;> rcases j with _ | b
      · exact absurd rfl hij
      · have h1 : (χ' (primeCls v)).toAdd = 0 := hv.1
        have h2 : (χ (primeCls v)).toAdd = b * (χ' (primeCls v)).toAdd := hv.2
        show (χ (primeCls v)).toAdd = 0
        rw [h2, h1, mul_zero]
      · have h1 : (χ (primeCls v)).toAdd = a * (χ' (primeCls v)).toAdd := hv.1
        have h2 : (χ' (primeCls v)).toAdd = 0 := hv.2
        show (χ (primeCls v)).toAdd = 0
        rw [h1, h2, mul_zero]
      · have h1 : (χ (primeCls v)).toAdd = a * (χ' (primeCls v)).toAdd := hv.1
        have h2 : (χ (primeCls v)).toAdd = b * (χ' (primeCls v)).toAdd := hv.2
        have hab : a ≠ b := fun h => hij (by rw [h])
        exact (zmod_eq_zero_of_mul_eq h1 h2 hab).1
    · -- the family covers all primes
      ext v
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      by_cases hw : (χ' (primeCls v)).toAdd = 0
      · exact ⟨none, hw⟩
      · refine ⟨some ((χ (primeCls v)).toAdd * ((χ' (primeCls v)).toAdd)⁻¹), ?_⟩
        show (χ (primeCls v)).toAdd =
          ((χ (primeCls v)).toAdd * ((χ' (primeCls v)).toAdd)⁻¹) * (χ' (primeCls v)).toAdd
        rw [mul_assoc, inv_mul_cancel₀ hw, mul_one]
    · -- and `1/p ≠ 1`
      have hp : (1 : ℝ) < (p : ℝ) := by
        exact_mod_cast (Fact.out : p.Prime).one_lt
      have hlt : (1 : ℝ) / (p : ℝ) < 1 := by
        rw [div_lt_one (by positivity : (0 : ℝ) < (p : ℝ))]
        simpa using hp
      exact ne_of_lt hlt

end Work.CFTLib

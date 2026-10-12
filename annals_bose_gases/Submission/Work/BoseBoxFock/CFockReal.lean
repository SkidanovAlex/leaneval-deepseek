import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseBoxFock.KzOpC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.CFockReal` — the real locus of `cfock X` and the coordinate calculus

The Fock core `cfock X` (`Work.BoseB4.CFock`) is the ℓ²-space on the index set
`X →₀ ℕ`, with orthonormal basis `e_β = toCFock X (Finsupp.single β 1)`.  Its
"real locus" is the set of vectors all of whose basis coefficients are real:

* `IsRealF f` — a Finsupp of complex numbers, all of whose coefficients are real;
* `IsRealC v` — a vector of `cfock X` with all basis coefficients real;
* `IsRealMap A` — a ℂ-linear endomorphism of `cfock X` carrying the real locus into
  itself, i.e. a map whose matrix in the basis `e_β` has real entries.

The file collects (all proved, no `sorry`):

* closure of `IsRealF` / `IsRealC` / `IsRealMap` under the algebraic operations
  (`+`, real scalar multiples, compositions, finite sums, the identity);
* the fact that the ladder operators `annC`, `creC` (hence `annOfE`, `creOfE`,
  `nOpC`, `nPlusC`) are real maps;
* the coordinate form of the Fock inner product and of the norm,
  `⟪f, g⟫ = Σ_α conj (f α) * g α`, `‖f‖² = Σ_α ((f α).re² + (f α).im²)`;
* the *expansion of a quadratic form in coordinates*: for a real map `A` and any
  `f`, `Re ⟪f, A f⟫ = Σ_{α,β} (A_{αβ}).re ((f α).re (f β).re + (f α).im (f β).im)`,
  where `A_{αβ} = colOp A β α` are the real matrix entries of `A`.

These are the two ingredients of `Work.BoseBoxFock.KzOpC_re_decomp`: the realness
of `KzOpC` (`KzOpC_isRealMap`, `Submission.Work.BoseBoxFock.KzOpC_real`) and the
real/imaginary decomposition of its quadratic form.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {X : Type*} [DecidableEq X]

/-! ## 1. The real locus -/

/-- A Finsupp of complex numbers is **real** when every coefficient is real. -/
def IsRealF (f : (X →₀ ℕ) →₀ ℂ) : Prop := ∀ α, (f α).im = 0

/-- A vector of `cfock X` is **real** when every coefficient in the Fock basis
`β ↦ e_β = toCFock X (Finsupp.single β 1)` is a real number. -/
def IsRealC (v : cfock X) : Prop := IsRealF ((toCFock X).symm v)

lemma isRealC_iff (v : cfock X) :
    IsRealC v ↔ ∀ β : X →₀ ℕ, ((toCFock X).symm v β).im = 0 := Iff.rfl

lemma isRealC_toCFock_iff (f : (X →₀ ℕ) →₀ ℂ) : IsRealC (toCFock X f) ↔ IsRealF f := by
  rw [IsRealC, LinearEquiv.symm_apply_apply]

/-- The Finsupp underlying the real Fock vector `toCFock X f`. -/
lemma isRealF_iff (f : (X →₀ ℕ) →₀ ℂ) : IsRealF f ↔ ∀ α, (f α).im = 0 := Iff.rfl

/-! ### 1.1 Closure of `IsRealF` -/

lemma IsRealF.zero : IsRealF (0 : (X →₀ ℕ) →₀ ℂ) := fun α => by simp

lemma IsRealF.add {f g : (X →₀ ℕ) →₀ ℂ} (hf : IsRealF f) (hg : IsRealF g) :
    IsRealF (f + g) := by
  intro α; rw [Finsupp.add_apply, Complex.add_im, hf α, hg α, add_zero]

lemma IsRealF.neg {f : (X →₀ ℕ) →₀ ℂ} (hf : IsRealF f) : IsRealF (-f) := by
  intro α; rw [Finsupp.neg_apply, Complex.neg_im, hf α, neg_zero]

lemma IsRealF.sub {f g : (X →₀ ℕ) →₀ ℂ} (hf : IsRealF f) (hg : IsRealF g) :
    IsRealF (f - g) := by
  intro α; rw [Finsupp.sub_apply, Complex.sub_im, hf α, hg α, sub_zero]

lemma IsRealF.smul {c : ℂ} (hc : c.im = 0) {f : (X →₀ ℕ) →₀ ℂ} (hf : IsRealF f) :
    IsRealF (c • f) := by
  intro α
  rw [Finsupp.smul_apply, smul_eq_mul, Complex.mul_im, hc, hf α]
  ring

lemma IsRealF.single (β : X →₀ ℕ) {c : ℂ} (hc : c.im = 0) :
    IsRealF (Finsupp.single β c) := by
  intro α
  by_cases h : α = β
  · subst h; rw [Finsupp.single_eq_same, hc]
  · rw [Finsupp.single_eq_of_ne h, Complex.zero_im]

lemma IsRealF.sum {ι : Type*} (s : Finset ι) (g : ι → (X →₀ ℕ) →₀ ℂ)
    (h : ∀ i ∈ s, IsRealF (g i)) : IsRealF (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using IsRealF.zero
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact IsRealF.add (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ### 1.2 Closure of `IsRealC` -/

lemma IsRealC.zero : IsRealC (0 : cfock X) := by
  rw [IsRealC, map_zero]; exact IsRealF.zero

lemma IsRealC.sub {u v : cfock X} (hu : IsRealC u) (hv : IsRealC v) :
    IsRealC (u - v) := by
  rw [IsRealC, map_sub]; exact IsRealF.sub hu hv

lemma IsRealC.add {u v : cfock X} (hu : IsRealC u) (hv : IsRealC v) :
    IsRealC (u + v) := by
  rw [IsRealC, map_add]; exact IsRealF.add hu hv

lemma IsRealC.neg {v : cfock X} (hv : IsRealC v) : IsRealC (-v) := by
  rw [IsRealC, map_neg]; exact IsRealF.neg hv

lemma IsRealC.smul {c : ℂ} (hc : c.im = 0) {v : cfock X} (hv : IsRealC v) :
    IsRealC (c • v) := by
  rw [IsRealC, map_smul]; exact IsRealF.smul hc hv

lemma IsRealC.sum {ι : Type*} (s : Finset ι) (w : ι → cfock X)
    (h : ∀ i ∈ s, IsRealC (w i)) : IsRealC (∑ i ∈ s, w i) := by
  rw [IsRealC, map_sum]; exact IsRealF.sum s _ fun i hi => h i hi

/-- The basis vector `e_β = toCFock X (single β 1)` is real. -/
lemma IsRealC.basis (β : X →₀ ℕ) : IsRealC (toCFock X (Finsupp.single β (1 : ℂ))) := by
  rw [isRealC_toCFock_iff]
  exact IsRealF.single β (by simp)

/-! ## 2. Real maps `cfock X →ₗ[ℂ] cfock X` -/

/-- A ℂ-linear endomorphism of `cfock X` is **real** when it maps the real locus into
itself — equivalently, when its matrix in the Fock basis has real entries. -/
def IsRealMap (A : cfock X →ₗ[ℂ] cfock X) : Prop := ∀ v, IsRealC v → IsRealC (A v)

lemma IsRealMap.zero : IsRealMap (0 : cfock X →ₗ[ℂ] cfock X) := fun v _ => by
  rw [LinearMap.zero_apply]; exact IsRealC.zero

lemma IsRealMap.id : IsRealMap (1 : cfock X →ₗ[ℂ] cfock X) := fun v hv => hv

lemma IsRealMap.add {A B : cfock X →ₗ[ℂ] cfock X} (hA : IsRealMap A) (hB : IsRealMap B) :
    IsRealMap (A + B) := fun v hv => by
  rw [LinearMap.add_apply]; exact IsRealC.add (hA v hv) (hB v hv)

lemma IsRealMap.neg {A : cfock X →ₗ[ℂ] cfock X} (hA : IsRealMap A) : IsRealMap (-A) :=
  fun v hv => by rw [LinearMap.neg_apply]; exact IsRealC.neg (hA v hv)

lemma IsRealMap.sub {A B : cfock X →ₗ[ℂ] cfock X} (hA : IsRealMap A) (hB : IsRealMap B) :
    IsRealMap (A - B) := fun v hv => by
  rw [LinearMap.sub_apply]; exact IsRealC.sub (hA v hv) (hB v hv)

lemma IsRealMap.smul_real {c : ℂ} (hc : c.im = 0) {A : cfock X →ₗ[ℂ] cfock X}
    (hA : IsRealMap A) : IsRealMap (c • A) := fun v hv => by
  rw [LinearMap.smul_apply]; exact IsRealC.smul hc (hA v hv)

/-- A multiple of a real map by a (cast of a) real scalar is real.  Convenience form of
`IsRealMap.smul_real` for the scalars `((r : ℝ) : ℂ)` that occur throughout `KzOpC`. -/
lemma IsRealMap.ofReal_smul {r : ℝ} {A : cfock X →ₗ[ℂ] cfock X} (hA : IsRealMap A) :
    IsRealMap (((r : ℝ) : ℂ) • A) :=
  IsRealMap.smul_real (by simp) hA

lemma IsRealMap.comp {A B : cfock X →ₗ[ℂ] cfock X} (hA : IsRealMap A) (hB : IsRealMap B) :
    IsRealMap (A.comp B) := fun v hv => hA (B v) (hB v hv)

lemma IsRealMap.sum {ι : Type*} (s : Finset ι) (A : ι → cfock X →ₗ[ℂ] cfock X)
    (h : ∀ i ∈ s, IsRealMap (A i)) : IsRealMap (∑ i ∈ s, A i) := fun v hv => by
  rw [LinearMap.sum_apply]
  exact IsRealC.sum s (fun i => A i v) fun i hi => h i hi v hv

/-- The finite-sum form of `IsRealMap.sum` over a `Fintype`. -/
lemma IsRealMap.univ_sum {ι : Type*} [Fintype ι] (A : ι → cfock X →ₗ[ℂ] cfock X)
    (h : ∀ i, IsRealMap (A i)) : IsRealMap (∑ i, A i) :=
  IsRealMap.sum Finset.univ A fun i _ => h i

/-! ## 3. The ladder operators are real -/

lemma annF_realF_single {j : X} {γ : X →₀ ℕ} {c : ℂ} (hc : c.im = 0) :
    IsRealF (annF X j (Finsupp.single γ c)) := by
  rw [annF_single]
  exact IsRealF.smul (by rw [Complex.mul_im, hc, Complex.ofReal_im]; ring)
    (IsRealF.single (γ - Finsupp.single j 1) (by simp))

lemma creF_realF_single {j : X} {γ : X →₀ ℕ} {c : ℂ} (hc : c.im = 0) :
    IsRealF (creF X j (Finsupp.single γ c)) := by
  rw [creF, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, smul_smul]
  exact IsRealF.smul (by rw [Complex.mul_im, hc, Complex.ofReal_im]; ring)
    (IsRealF.single (γ + Finsupp.single j 1) (by simp))

lemma IsRealF.annF (j : X) {f : (X →₀ ℕ) →₀ ℂ} (hf : IsRealF f) : IsRealF (annF X j f) := by
  have hdec : f = ∑ γ ∈ f.support, Finsupp.single γ (f γ) := (Finsupp.sum_single f).symm
  rw [hdec, map_sum]
  exact IsRealF.sum _ _ fun γ _ => annF_realF_single (hf γ)

lemma IsRealF.creF (j : X) {f : (X →₀ ℕ) →₀ ℂ} (hf : IsRealF f) : IsRealF (creF X j f) := by
  have hdec : f = ∑ γ ∈ f.support, Finsupp.single γ (f γ) := (Finsupp.sum_single f).symm
  rw [hdec, map_sum]
  exact IsRealF.sum _ _ fun γ _ => creF_realF_single (hf γ)

lemma IsRealMap.annC (j : X) : IsRealMap (annC X j) := fun v hv =>
  (isRealC_toCFock_iff _).mpr (IsRealF.annF j hv)

lemma IsRealMap.creC (j : X) : IsRealMap (creC X j) := fun v hv =>
  (isRealC_toCFock_iff _).mpr (IsRealF.creF j hv)

/-! ## 4. The coordinate calculus of the Fock inner product -/

/-- **The Fock inner product in coordinates**: `⟪f, g⟫ = Σ_α conj (f α) * g α`. -/
lemma inner_toCFock (f g : (X →₀ ℕ) →₀ ℂ) :
    inner ℂ (toCFock X f) (toCFock X g) = ∑ α ∈ f.support, (starRingEnd ℂ) (f α) * g α := by
  have hfs : f = ∑ α ∈ f.support, Finsupp.single α (f α) := (Finsupp.sum_single f).symm
  have hL : toCFock X f = ∑ α ∈ f.support, toCFock X (Finsupp.single α (f α)) := by
    conv_lhs => rw [hfs]
    rw [map_sum]
  rw [hL, sum_inner]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Submodule.coe_inner, toCFock_coe, toCFock_coe, toLp_single, lp.inner_single_left,
    toLp_apply, RCLike.inner_apply]
  ring

/-- The same formula with the sum extended to any finite set containing the support. -/
lemma inner_toCFock_sum (f g : (X →₀ ℕ) →₀ ℂ) (s : Finset (X →₀ ℕ))
    (hs : f.support ⊆ s) :
    inner ℂ (toCFock X f) (toCFock X g) = ∑ α ∈ s, (starRingEnd ℂ) (f α) * g α := by
  rw [inner_toCFock]
  exact Finset.sum_subset hs fun α _ hα => by
    rw [Finsupp.notMem_support_iff.mp hα, map_zero, zero_mul]

/-- The real part of `⟪f, g⟫` when `g` is real. -/
lemma inner_toCFock_re (f g : (X →₀ ℕ) →₀ ℂ) (s : Finset (X →₀ ℕ)) (hs : f.support ⊆ s)
    (hg : IsRealF g) :
    (inner ℂ (toCFock X f) (toCFock X g)).re = ∑ α ∈ s, (f α).re * (g α).re := by
  rw [inner_toCFock_sum f g s hs, Complex.re_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hgα : g α = (((g α).re : ℝ) : ℂ) := by
    refine Complex.ext rfl ?_
    rw [Complex.ofReal_im]; exact hg α
  rw [hgα, Complex.mul_re, Complex.conj_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]

/-- The imaginary part of `⟪f, g⟫` when `g` is real. -/
lemma inner_toCFock_im (f g : (X →₀ ℕ) →₀ ℂ) (s : Finset (X →₀ ℕ)) (hs : f.support ⊆ s)
    (hg : IsRealF g) :
    (inner ℂ (toCFock X f) (toCFock X g)).im = -∑ α ∈ s, (f α).im * (g α).re := by
  rw [inner_toCFock_sum f g s hs, Complex.im_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hgα : g α = (((g α).re : ℝ) : ℂ) := by
    refine Complex.ext rfl ?_
    rw [Complex.ofReal_im]; exact hg α
  rw [hgα, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- **The squared norm in coordinates**. -/
lemma normSq_toCFock (f : (X →₀ ℕ) →₀ ℂ) :
    ‖toCFock X f‖ ^ 2 = ∑ α ∈ f.support, ((f α).re ^ 2 + (f α).im ^ 2) := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ) (toCFock X f), inner_toCFock]
  change (∑ α ∈ f.support, (starRingEnd ℂ) (f α) * f α).re
    = ∑ α ∈ f.support, ((f α).re ^ 2 + (f α).im ^ 2)
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The same formula with the sum extended to any finite set containing the support. -/
lemma normSq_toCFock_sum (f : (X →₀ ℕ) →₀ ℂ) (s : Finset (X →₀ ℕ)) (hs : f.support ⊆ s) :
    ‖toCFock X f‖ ^ 2 = ∑ α ∈ s, ((f α).re ^ 2 + (f α).im ^ 2) := by
  rw [normSq_toCFock]
  exact Finset.sum_subset hs fun α _ hα => by
    rw [Finsupp.notMem_support_iff.mp hα]; norm_num

/-! ## 5. Columns of a linear map, and the quadratic form in coordinates -/

/-- The `β`-th column of `A` in the Fock basis: the coordinates of `A e_β`,
`e_β = toCFock X (single β 1)`. -/
noncomputable def colOp (A : cfock X →ₗ[ℂ] cfock X) (β : X →₀ ℕ) : (X →₀ ℕ) →₀ ℂ :=
  (toCFock X).symm (A (toCFock X (Finsupp.single β (1 : ℂ))))

lemma colOp_apply (A : cfock X →ₗ[ℂ] cfock X) (β : X →₀ ℕ) :
    colOp A β = (toCFock X).symm (A (toCFock X (Finsupp.single β (1 : ℂ)))) := rfl

lemma IsRealF.colOp {A : cfock X →ₗ[ℂ] cfock X} (hA : IsRealMap A) (β : X →₀ ℕ) :
    IsRealF (colOp A β) :=
  hA _ (IsRealC.basis β)

/-- `A (toCFock X f) = Σ_β f β • A e_β` (the sum extended to any `s ⊇ support f`). -/
lemma apply_eq_sum_col (A : cfock X →ₗ[ℂ] cfock X) (f : (X →₀ ℕ) →₀ ℂ)
    (s : Finset (X →₀ ℕ)) (hs : f.support ⊆ s) :
    A (toCFock X f) = ∑ β ∈ s, f β • A (toCFock X (Finsupp.single β (1 : ℂ))) := by
  have hdec : f = ∑ β ∈ s, f β • Finsupp.single β (1 : ℂ) := by
    conv_lhs => rw [show f = ∑ β ∈ f.support, Finsupp.single β (f β)
      from (Finsupp.sum_single f).symm]
    rw [← Finset.sum_subset hs]
    · refine Finset.sum_congr rfl fun β _ => ?_
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    · intro β _ hβf
      rw [Finsupp.smul_single, Finsupp.notMem_support_iff.mp hβf, smul_eq_mul, zero_mul,
        Finsupp.single_zero]
  conv_lhs => rw [hdec]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul, map_smul]

/-- **The quadratic form of a real map in coordinates.**  For a real map `A` (real
matrix entries `colOp A β α`) the real part of `⟪f, A f⟫` is the real quadratic form
of the matrix `colOp A` in the real and imaginary parts of the coordinates of `f`. -/
theorem quadForm_re_expansion (A : cfock X →ₗ[ℂ] cfock X) (hA : IsRealMap A)
    (f : (X →₀ ℕ) →₀ ℂ) (s : Finset (X →₀ ℕ)) (hs : f.support ⊆ s) :
    (inner ℂ (toCFock X f) (A (toCFock X f))).re
      = ∑ β ∈ s, ∑ α ∈ s,
          (colOp A β α).re * ((f α).re * (f β).re + (f α).im * (f β).im) := by
  have hcol : ∀ β, IsRealF (colOp A β) := fun β => IsRealF.colOp hA β
  have hAe : A (toCFock X f) = ∑ β ∈ s, f β • toCFock X (colOp A β) := by
    rw [apply_eq_sum_col A f s hs]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [show A (toCFock X (Finsupp.single β (1 : ℂ))) = toCFock X (colOp A β) from
      (LinearEquiv.apply_symm_apply _ _).symm]
  rw [hAe, inner_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [inner_smul_right (toCFock X f) (toCFock X (colOp A β)) (f β)]
  rw [Complex.mul_re, inner_toCFock_re f (colOp A β) s hs (hcol β),
    inner_toCFock_im f (colOp A β) s hs (hcol β), mul_neg, sub_neg_eq_add,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  ring

/-! ## 6. Realness of the spectator operators of `KzOpC` -/

section Excited

variable {m : ℕ} [NeZero m]

lemma isRealMap_annOfE (φ : Fin m → ℝ) : IsRealMap (annOfE φ) := by
  have h : annOfE φ = ∑ l : Excited m, (((φ l.1 : ℝ)) : ℂ) • annC (Excited m) l := rfl
  rw [h]
  refine IsRealMap.sum (Finset.univ : Finset (Excited m)) _ fun l _ => ?_
  exact IsRealMap.smul_real (by simp) (IsRealMap.annC l)

lemma isRealMap_creOfE (φ : Fin m → ℝ) : IsRealMap (creOfE φ) := by
  have h : creOfE φ = ∑ l : Excited m, (((φ l.1 : ℝ)) : ℂ) • creC (Excited m) l := rfl
  rw [h]
  refine IsRealMap.sum (Finset.univ : Finset (Excited m)) _ fun l _ => ?_
  exact IsRealMap.smul_real (by simp) (IsRealMap.creC l)

lemma isRealMap_nOpC (φ : Fin m → ℝ) : IsRealMap (nOpC φ) := by
  have h : nOpC φ = (creOfE φ).comp (annOfE φ) := rfl
  rw [h]
  exact IsRealMap.comp (isRealMap_creOfE φ) (isRealMap_annOfE φ)

lemma isRealMap_nPlusC : IsRealMap (nPlusC (m := m)) := by
  have h : nPlusC (m := m) = ∑ l : Excited m, (1 : ℂ) •
      ((creC (Excited m) l).comp (annC (Excited m) l)) := rfl
  rw [h]
  refine IsRealMap.sum (Finset.univ : Finset (Excited m)) _ fun l _ => ?_
  refine IsRealMap.smul_real (by simp) ?_
  exact IsRealMap.comp (IsRealMap.creC l) (IsRealMap.annC l)

end Excited

end Work.BoseBoxFock

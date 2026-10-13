import Mathlib
import Submission.Work.DSCOH.ChartFree
import Submission.Work.DSCOH.shift_finite_indep
import Submission.Work.DSCOH.chartCech_shift_vanishing
import Submission.Work.DSCOH.exists_graded_cover
import Submission.Work.DSCOH.exists_graded_quotient
import Submission.Work.DSCOH.freeGraded_homology_finite
import Submission.Work.DSCOH.homology_finite_of_graded_shortExact
import Submission.Work.DSCOH.cechHomology_of_graded_linearEquiv

/-!
# Area DSCOH — Serre finiteness for the chart Čech complex

**The theorem of the area.**  For `A` Noetherian and `M` a finitely generated graded
`A[X₀,…,X_{n-1}]`-module, every cohomology group of the chart Čech complex `chartCech ℳ` is a
finitely generated `A`-module, and it vanishes in degrees `> n` (the complex has no terms in
degrees `≥ n`, since there are no `(q+1)`-element subsets of `Fin n` for `q ≥ n`).

The proof is the classical one, organised as a *descending induction on the cohomological degree*
`q`:

* for `n ≤ q` the complex vanishes in degree `q`, so `H^q = 0`;
* for `q < n`, cover `M` by the graded free module `F = ⊕_{j} S(-d_j)` on a finite family of
  homogeneous generators of `M` (`exists_graded_cover`), with kernel `K` (finitely generated, as
  `S` is Noetherian).  The short exact sequence `0 → K → F → M → 0` of graded modules gives a
  short exact sequence of chart Čech complexes (`cechMap_exact`), and hence a long exact sequence
  `H^q(F) → H^q(M) → H^{q+1}(K) → …`.  Therefore `H^q(M)` is finite as soon as `H^q(F)` and
  `H^{q+1}(K)` are, and these are provided by the free case
  (`freeGraded_homology_finite` + the single-shift case `chartCech_shift_homology_finite`) and by
  the induction hypothesis applied to the graded module `K`.

The single-shift case itself is Serre's computation of `H^q(ℙ^{n-1}, O(-d))`: vanishing for
`0 < q < n-1`, and `H⁰ = S_{-d}`, `H^{n-1} ≅ (S_{d-n})^*` (proved in the sibling files
`chartCech_shift_vanishing` and `chartCech_shift_finite`).
-/

open MvPolynomial CategoryTheory

set_option maxHeartbeats 1600000

namespace Work.DSCOH

universe u

variable {A : Type*} [CommRing A] {n : ℕ}

/-- A module isomorphic to zero is finitely generated. -/
theorem moduleFinite_of_isZero {X : ModuleCat A} (h : CategoryTheory.Limits.IsZero X) :
    Module.Finite A X := by
  haveI : Subsingleton X := (ModuleCat.isZero_iff_subsingleton (M := X)).mp h
  exact Module.Finite.of_surjective (0 : PUnit →ₗ[A] X)
    (fun x => ⟨PUnit.unit, by simp [Subsingleton.elim x 0]⟩)

/-- **The single-shift case.**  For the graded module `S(-d)` (`M = S = A[X₀,…,X_{n-1}]` with the
shifted grading `shift d`), every chart Čech cohomology group is a finitely generated
`A`-module: it is zero for `0 < q < n - 1` (and for `q ≥ n`), and the two remaining degrees are
`H⁰ = S_{-d}` and `H^{n-1} ≅ (S_{d-n})^*`, both finite. -/
theorem chartCech_shift_homology_finite (d q : ℕ) :
    Module.Finite A ((chartCech (A := A) (n := n) (M := Poly A n)
      (shift (A := A) (n := n) d)).homology q) := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    exact (SFI.chartCech_shift_finite_indep (A := A) (n := n) d).1
  · by_cases h1 : q + 1 < n
    · exact moduleFinite_of_isZero (chartCech_shift_vanishing (A := A) (n := n) d q hq h1)
    · by_cases h2 : q = n - 1
      · subst h2
        exact (SFI.chartCech_shift_finite_indep (A := A) (n := n) d).2
      · exact moduleFinite_of_isZero (chartCech_homology_isZero_of_le (A := A) (n := n)
          (M := Poly A n) (shift (A := A) (n := n) d) (by omega))

/-- In a direct sum, the `e`-th coordinate of a sum of `of`'s indexed by `s ∋ e` is the `e`-th
term: if `of e x` is such a sum, then `x` is the `e`-th term. -/
theorem of_eq_sum_of {ι : Type*} [DecidableEq ι] {N : ι → Type*} [∀ i, AddCommMonoid (N i)]
    {s : Finset ι} (v : (i : ι) → N i) {e : ι} (he : e ∈ s) {x : N e}
    (h : DirectSum.of N e x = ∑ i ∈ s, DirectSum.of N i (v i)) : x = v e := by
  have h1 := congrArg (fun z : DirectSum ι N => z e) h
  rw [DFinsupp.finsetSum_apply, Finset.sum_eq_single_of_mem e he] at h1
  · simpa using h1
  · intro b _ hb
    exact DirectSum.of_eq_of_ne b e (v b) (Ne.symm hb)

section Cover

variable {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
  [IsScalarTower A (Poly A n) M]

/-- **A surjective graded map of graded modules maps onto each graded piece.**  If `φ : N → M` is
surjective with `φ (𝒩 e) ⊆ ℳ e`, and both gradings are internal, then `φ (𝒩 e) = ℳ e`: an element
`m ∈ ℳ e` is the image of some `x`, and reading the decomposition of `x` in the pieces `𝒩 j`
shows that its `e`-th component already maps onto `m`. -/
theorem map_eq_of_surjective_graded {N : Type*} [AddCommGroup N] [Module A N]
    (ℳ : ℕ → Submodule A M) (hℳ : DirectSum.IsInternal ℳ)
    (𝒩 : ℕ → Submodule A N) (h𝒩 : DirectSum.IsInternal 𝒩)
    (φ : N →ₗ[A] M) (hsurj : Function.Surjective φ)
    (hgr : ∀ e, Submodule.map φ (𝒩 e) ≤ ℳ e) (e : ℕ) :
    Submodule.map φ (𝒩 e) = ℳ e := by
  classical
  haveI hdecM : DirectSum.Decomposition ℳ := hℳ.chooseDecomposition
  haveI hdecN : DirectSum.Decomposition 𝒩 := h𝒩.chooseDecomposition
  refine le_antisymm (hgr e) ?_
  rintro m hm
  obtain ⟨x, hx⟩ := hsurj m
  -- the decomposition of `x` in the pieces of `𝒩`
  set s : Finset ℕ := (DirectSum.decompose 𝒩 x).support with hs
  set v : (j : ℕ) → ↥(𝒩 j) := fun j => DirectSum.decompose 𝒩 x j with hv
  have hsum : (∑ j ∈ s, (v j : N)) = x := DirectSum.sum_support_decompose 𝒩 x
  have hmem : ∀ j, φ (v j : N) ∈ ℳ j :=
    fun j => hgr j (Submodule.mem_map_of_mem (v j).2)
  -- `m = φ x` is the sum of the images of the components
  have hπ : m = ∑ j ∈ s, φ (v j : N) := by
    rw [← hx, ← hsum, map_sum]
  -- the `ℳ`-decomposition of `m ∈ ℳ e` is concentrated in degree `e`
  have hof : DirectSum.of (fun j => ↥(ℳ j)) e ⟨m, hm⟩ =
      ∑ j ∈ s, DirectSum.of (fun j => ↥(ℳ j)) j ⟨φ (v j : N), hmem j⟩ := by
    apply (DirectSum.Decomposition.isInternal ℳ).1
    simp only [map_sum, DirectSum.coeAddMonoidHom_of, ← hπ]
  -- hence `m` itself is the `e`-th component of that sum (or `m = 0`)
  have he : e ∈ s ∨ m = 0 := by
    by_cases h : e ∈ s
    · exact Or.inl h
    · right
      have h1 := congrArg (fun z : DirectSum ℕ (fun j => ↥(ℳ j)) => z e) hof
      rw [DFinsupp.finsetSum_apply, Finset.sum_eq_zero] at h1
      · simpa using congrArg Subtype.val h1
      · intro b hb
        exact DirectSum.of_eq_of_ne b e _ (by rintro rfl; exact h hb)
  rcases he with he | hzero
  · have h1 : (⟨m, hm⟩ : ↥(ℳ e)) = ⟨φ (v e : N), hmem e⟩ :=
      of_eq_sum_of (fun j => (⟨φ (v j : N), hmem j⟩ : ↥(ℳ j))) he hof
    exact Submodule.mem_map.mpr ⟨(v e : N), (v e).2, (congrArg Subtype.val h1).symm⟩
  · refine Submodule.mem_map.mpr ⟨0, (𝒩 e).zero_mem, ?_⟩
    rw [map_zero, hzero]

end Cover

section SameUniverse

variable {A : Type u} [CommRing A] {n : ℕ}

/-- **Finiteness of chart Čech cohomology, by descending induction on the degree.**  The
auxiliary statement, with the "remaining descent length" `m` as an explicit induction variable so
that the induction can be polymorphic in the graded module.  All modules live in the universe of
`A`, as the long exact sequence argument requires. -/
private theorem chartCech_homology_finite_aux : ∀ (m : ℕ) (q : ℕ) (M : Type u)
    [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    [IsNoetherianRing A] (ℳ : ℕ → Submodule A M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (homSub A n) ℳ] [Module.Finite (Poly A n) M], n - q ≤ m →
    Module.Finite A ((chartCech (A := A) (n := n) (M := M) ℳ).homology q) := by
  intro m
  induction m with
  | zero =>
    intro q M _ _ _ _ _ ℳ _ _ _ hq
    exact moduleFinite_of_isZero
      (chartCech_homology_isZero_of_le (A := A) (n := n) (M := M) ℳ (by omega))
  | succ m ih =>
    intro q M _ _ _ _ _ ℳ hdec hgsm hfin hq
    by_cases hqn : n ≤ q
    · exact moduleFinite_of_isZero
        (chartCech_homology_isZero_of_le (A := A) (n := n) (M := M) ℳ hqn)
    · -- the graded cover of `M` by a free module
      obtain ⟨r, δ, π, hsurj, hgr, hKfin, hKIsInt⟩ := exists_graded_cover (A := A) (n := n) ℳ
      have hφsurj : Function.Surjective (π.restrictScalars A) := by
        intro y
        obtain ⟨x, hx⟩ := hsurj y
        exact ⟨x, by simpa using hx⟩
      haveI : SetLike.GradedSMul (homSub A n) (kerGraded (A := A) (n := n) δ π) :=
        kerGraded_gradedSMul (A := A) (n := n) δ π
      haveI : DirectSum.Decomposition (kerGraded (A := A) (n := n) δ π) :=
        hKIsInt.chooseDecomposition
      have hgr1 : ∀ e, Submodule.map ((LinearMap.ker π).subtype.restrictScalars A)
          (kerGraded (A := A) (n := n) δ π e) ≤ freeGraded (A := A) (n := n) δ e := by
        intro e x hx
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
        simpa using mem_kerGraded.mp hy
      have hker' : ∀ e, freeGraded (A := A) (n := n) δ e ⊓
          LinearMap.ker (π.restrictScalars A) ≤
          Submodule.map ((LinearMap.ker π).subtype.restrictScalars A)
            (kerGraded (A := A) (n := n) δ π e) := by
        intro e x hx
        obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
        exact Submodule.mem_map.mpr ⟨⟨x, hx2⟩, mem_kerGraded.mpr hx1, rfl⟩
      have hgr2 : ∀ e, Submodule.map (π.restrictScalars A)
          (freeGraded (A := A) (n := n) δ e) = ℳ e :=
        fun e => map_eq_of_surjective_graded ℳ hdec.isInternal
          (freeGraded (A := A) (n := n) δ) (freeGraded_isInternal (A := A) (n := n) δ)
          (π.restrictScalars A) hφsurj hgr e
      have hex : Function.Exact (LinearMap.ker π).subtype π := LinearMap.exact_subtype_ker_map π
      have hinj : Function.Injective (LinearMap.ker π).subtype := Subtype.val_injective
      have hF : Module.Finite A ((chartCech (A := A) (n := n) (M := Fin r → Poly A n)
          (freeGraded (A := A) (n := n) δ)).homology q) :=
        freeGraded_homology_finite (A := A) (n := n)
          (fun d q => chartCech_shift_homology_finite (A := A) (n := n) d q) r δ q
      have hK : Module.Finite A ((chartCech (A := A) (n := n) (M := LinearMap.ker π)
          (kerGraded (A := A) (n := n) δ π)).homology (q + 1)) :=
        ih (q + 1) (LinearMap.ker π) (kerGraded (A := A) (n := n) δ π) (by omega)
      exact (homology_finite_of_graded_shortExact (A := A) (n := n)
        (M := LinearMap.ker π) (M' := Fin r → Poly A n) (M'' := M)
        (ℳ := kerGraded (A := A) (n := n) δ π) (ℳ' := freeGraded (A := A) (n := n) δ)
        (ℳ'' := ℳ) (LinearMap.ker π).subtype π hinj hex hgr1 hgr2 hker' q).2 hF hK

/-- **Finiteness half of the area's theorem**: for `A` Noetherian and `M` a finitely generated
graded `A[X₀,…,X_{n-1}]`-module, all chart Čech cohomology groups are finitely generated
`A`-modules. -/
theorem chartCech_homology_finite_of_decomposition {A : Type u} [CommRing A] [IsNoetherianRing A]
    {n : ℕ} {M : Type u} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M] (ℳ : ℕ → Submodule A M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (homSub A n) ℳ] [Module.Finite (Poly A n) M] (q : ℕ) :
    Module.Finite A ((chartCech (A := A) (n := n) (M := M) ℳ).homology q) :=
  chartCech_homology_finite_aux (n - q) q M ℳ le_rfl

end SameUniverse

theorem chartCech_finite_vanishing {A : Type*} [CommRing A] [IsNoetherianRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    (ℳ : ℕ → Submodule A M) [DirectSum.Decomposition ℳ] [SetLike.GradedSMul (homSub A n) ℳ]
    [Module.Finite (Poly A n) M] :
    (∀ q : ℕ, Module.Finite A ((chartCech (A := A) (n := n) (M := M) ℳ).homology q)) ∧
      (∀ q : ℕ, n < q → CategoryTheory.Limits.IsZero
        ((chartCech (A := A) (n := n) (M := M) ℳ).homology q)) := by
  constructor
  · intro q
    -- replace `M` by the graded quotient `F ⧸ ker π`, which lives in the universe of `A`
    obtain ⟨r, δ, π, hsurj, hgr, 𝒬, h𝒬gsm, h𝒬int, hQfin, φ, hφ⟩ :=
      exists_graded_quotient (A := A) (n := n) ℳ
    haveI : SetLike.GradedSMul (homSub A n) 𝒬 := h𝒬gsm
    haveI : DirectSum.Decomposition 𝒬 := h𝒬int.chooseDecomposition
    exact (cechHomology_of_graded_linearEquiv (A := A) (n := n) ℳ 𝒬 φ hφ q).1.2
      (chartCech_homology_finite_of_decomposition 𝒬 q)
  · intro q hq
    exact chartCech_homology_isZero_of_le (A := A) (n := n) (M := M) ℳ (by omega)

end Work.DSCOH

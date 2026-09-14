import Mathlib
import Submission.Subspace.ElimInt
import Submission.Subspace.NonVanish
import Submission.Commons.Algebra.MvPolynomial.pderivIter_rename
import Submission.Commons.Algebra.MvPolynomial.coeff_indexTay_mul_factorial

/-!
# The non-vanishing lemma (Evertse's Lemma 24)

Let `F ∈ ℤ[X (h,j)]` (`h : Fin m`, `j : Fin N`, `N ≥ 2`) be a nonzero polynomial, homogeneous
of degree `e h` in the block `h`.  Let `l_h = ∑_j b h j · X (h,j)` be hyperplane forms with
`b h 0 ≠ 0`, and let `V = ∏_h Z(l_h)`.

**Non-vanishing.**  If the hyperplanes are tall enough, there are a point `x ∈ V` and a
multi-index `α` of weighted size `(α/d) < m Θ` with `(∂_α F)(x) ≠ 0`.

This is Evertse's Lemma 24 (`/tmp/sswork/evertse.txt`, §7), the sharp form of Schmidt's
specialisation theorem.  The proof proceeds by *eliminating* all the variables `X (h,j)` with
`j ≥ 2` (Schmidt's specialisation, implemented in `Submission.Subspace.elimF`), which turns `F`
into a polynomial in two variables per block; the resulting polynomial is still nonzero,
homogeneous of the same (or smaller) block degrees, and has no larger height.  Its index at
the special point is `≥ m Θ` (by the elimination invariant `elim_invariant`), while the
*projective Roth lemma* `Submission.Subspace.roth_proj` bounds it from above by `4 m η < m Θ`.

The statement below is the "substitution form" of the non-vanishing: instead of a point of
`V`, we conclude that some derivative of `F` does not vanish on the whole of `V`, expressed as
the non-vanishing of the substitution `pivotSubst b` applied to it.
-/

open scoped BigOperators
open MvPolynomial

namespace Submission.Subspace

variable {m N : ℕ} [NeZero N]

/-! ## A general evaluation point for the chart substitution -/

/-- If the composed substitution `chartSubst b q` kills `f`, then so does the evaluation at any
point `y` with `y (h,0) = -(b h 0)⁻¹ b h q · y (h,q)` and `y (h,j) = 0` for `j ∉ {0,q}`. -/
theorem aeval_chartSubst_eq_zero_of {K : Type*} [Field K]
    (b : Fin m → Fin N → K) {q : Fin N} (hq0 : q ≠ 0) (y : Fin m × Fin N → K)
    (h1 : ∀ h, y (h, 0) = -(b h 0)⁻¹ * b h q * y (h, q))
    (h2 : ∀ h j, j ≠ 0 → j ≠ q → y (h, j) = 0)
    (f : MvPolynomial (Fin m × Fin N) K) (hf : chartSubst b q f = 0) :
    MvPolynomial.aeval y f = 0 := by
  have hcomp : (MvPolynomial.aeval y).comp (chartSubst b q) = MvPolynomial.aeval y := by
    rw [chartSubst, aeval_comp_aeval]
    congr 1
    funext z
    obtain ⟨h, j⟩ := z
    by_cases hj0 : j = 0
    · subst hj0
      rw [if_pos rfl, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, h1 h]
      simp
    · rw [if_neg hj0]
      by_cases hjq : j = q
      · subst hjq
        rw [if_pos rfl, MvPolynomial.aeval_X]
      · rw [if_neg hjq]
        simp only [map_zero]
        exact (h2 h j hj0 hjq).symm
  rw [← hcomp, AlgHom.comp_apply, hf, map_zero]

/-! ## The compressed (two variables per block) polynomial -/

/-- The inclusion of the two kept coordinates into the `N` coordinates of a block. -/
noncomputable def keepMap (q : Fin N) : Fin m × Fin 2 → Fin m × Fin N :=
  fun z => (z.1, if (z.2 : ℕ) = 0 then 0 else q)

/-- The projection forgetting the eliminated coordinates. -/
noncomputable def dropMap (m N : ℕ) [NeZero N] : Fin m × Fin N → Fin m × Fin 2 :=
  fun z => (z.1, if (z.2 : ℕ) = 0 then 0 else 1)

lemma keepMap_zero (q : Fin N) (h : Fin m) :
    keepMap (m := m) q (h, 0) = (h, 0) := by
  simp [keepMap]

lemma keepMap_one (q : Fin N) (h : Fin m) :
    keepMap (m := m) q (h, 1) = (h, q) := by
  simp [keepMap]

lemma keepMap_injective {q : Fin N} (hq : q ≠ 0) : Function.Injective (keepMap (m := m) q) := by
  intro a b hab
  simp only [keepMap, Prod.mk.injEq] at hab
  obtain ⟨ha, hb⟩ := hab
  refine Prod.ext ha ?_
  by_cases ha0 : (a.2 : ℕ) = 0
  · have hb0 : (b.2 : ℕ) = 0 := by
      by_contra hb0
      rw [if_pos ha0, if_neg hb0] at hb
      exact hq hb.symm
    exact Fin.ext (by simp [ha0, hb0])
  · have hb0 : (b.2 : ℕ) ≠ 0 := by
      by_contra hb0
      rw [if_pos hb0, if_neg ha0] at hb
      exact hq hb
    rw [if_neg ha0, if_neg hb0] at hb
    exact Fin.ext (by
      have h1 : (a.2 : ℕ) < 2 := a.2.isLt
      have h2 : (b.2 : ℕ) < 2 := b.2.isLt
      omega)

/-- A `rename` fixes a polynomial all of whose monomials avoid a finite set `S`, provided the
renaming map fixes every variable outside `S`. -/
theorem rename_eq_self_of_freeOf_local {σ : Type*} [DecidableEq σ] {K : Type*} [CommSemiring K]
    (f : σ → σ) (S : Finset σ) (P : MvPolynomial σ K)
    (hP : ∀ u ∈ P.support, ∀ z ∈ S, u z = 0) (hf : ∀ z, z ∉ S → f z = z) :
    MvPolynomial.rename f P = P := by
  conv_rhs => rw [MvPolynomial.as_sum P]
  conv_lhs => rw [MvPolynomial.as_sum P]
  rw [map_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [MvPolynomial.rename_monomial]
  have hcong : Finsupp.mapDomain f u = u := by
    have h := Finsupp.mapDomain_congr (v := u) (f := f) (g := id) fun z hz =>
      hf z fun hmem => (Finsupp.mem_support_iff.mp hz) (hP u hu z hmem)
    simpa using h
  rw [hcong]

/-- The composed projection/inclusion map fixes every kept coordinate. -/
lemma keepMap_dropMap_apply {q : Fin N} (hq : (q : ℕ) = 1) :
    ∀ z : Fin m × Fin N, z ∉ (elimList m N).toFinset →
      (keepMap (m := m) q ∘ dropMap m N) z = z := by
  intro z hz
  obtain ⟨h, j⟩ := z
  have hj2 : ¬ (2 ≤ (j : ℕ)) := fun hc => hz (mem_elimList_toFinset.mpr hc)
  have hjle : (j : ℕ) ≤ 1 := by omega
  by_cases hj0 : (j : ℕ) = 0
  · have hjz : j = (0 : Fin N) := Fin.ext (by simpa using hj0)
    subst hjz
    simp [Function.comp, keepMap, dropMap]
  · have hj1 : (j : ℕ) = 1 := by omega
    have hjq : j = q := Fin.ext (by rw [hj1, hq])
    subst hjq
    simp [Function.comp, keepMap, dropMap, hq]

/-- The compression: a polynomial free of the eliminated coordinates is recovered from its
image in the two-kept-coordinates ring. -/
theorem rename_keepMap_dropMap_eq_of_free {K : Type*} [Field K] {q : Fin N}
    (hq : (q : ℕ) = 1) (Q : MvPolynomial (Fin m × Fin N) K)
    (hfree : FreeOf (K := K) (elimList m N).toFinset Q) :
    MvPolynomial.rename (keepMap (m := m) q) (MvPolynomial.rename (dropMap m N) Q) = Q := by
  rw [MvPolynomial.rename_rename]
  exact rename_eq_self_of_freeOf_local _ _ _ hfree (fun z => keepMap_dropMap_apply hq z)

/-! ## The block sum of a compressed multi-index -/

/-- The sum over a block of the `keepMap`-image of a two-variable multi-index is the sum over
the two kept coordinates. -/
lemma sum_keepMap_apply (q : Fin N) (hq : (q : ℕ) = 1) (u : (Fin m × Fin 2) →₀ ℕ)
    (h : Fin m) :
    ∑ j : Fin N, (Finsupp.mapDomain (keepMap q) u) (h, j) = u (h, 0) + u (h, 1) := by
  classical
  have hq0 : q ≠ 0 := by intro hh; rw [hh] at hq; simp at hq
  have hinj : Function.Injective (keepMap (m := m) q) := keepMap_injective hq0
  have e0 : (Finsupp.mapDomain (keepMap q) u) (h, 0) = u (h, 0) := by
    have hh := Finsupp.mapDomain_apply (x := u) hinj (a := (h, 0))
    simpa [keepMap_zero] using hh
  have eq : (Finsupp.mapDomain (keepMap q) u) (h, q) = u (h, 1) := by
    have hh := Finsupp.mapDomain_apply (x := u) hinj (a := (h, 1))
    simpa [keepMap_one] using hh
  have h0q : (0 : Fin N) ≠ q := fun hh => hq0 hh.symm
  have hside : ∀ j ∈ (Finset.univ : Finset (Fin N)), j ∉ ({0, q} : Finset (Fin N)) →
      (Finsupp.mapDomain (keepMap q) u) (h, j) = 0 := by
    intro j _ hj
    rw [Finsupp.mapDomain_of_notMem_range]
    intro hmem
    obtain ⟨z, hz⟩ := hmem
    have hzj : j = (keepMap (m := m) q z).2 := (congrArg Prod.snd hz).symm
    have hz' : (j : ℕ) = 0 ∨ (j : ℕ) = (q : ℕ) := by
      rw [hzj]
      by_cases hz0 : (z.2 : ℕ) = 0
      · left; simp [keepMap, hz0]
      · right; simp [keepMap, hz0]
    have hj' : j ≠ 0 ∧ j ≠ q := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hj
    rcases hz' with hz' | hz'
    · exact hj'.1 (Fin.ext (by simp [hz']))
    · exact hj'.2 (Fin.ext (by simp [hz']))
  rw [← Finset.sum_subset (Finset.subset_univ ({0, q} : Finset (Fin N))) hside]
  rw [Finset.sum_insert (by simpa using h0q), Finset.sum_singleton, e0, eq]

/-! ## The index bound from the vanishing hypothesis -/

/-- If every derivative of `G` (in two variables per block) of weighted size `< m Θ` vanishes
at the chart point, then the index of `G` there is at least `m Θ`. -/
lemma index_ge_of_vanishing [NeZero m] (G : MvPolynomial (Fin m × Fin 2) ℚ) (hG : G ≠ 0)
    (c : Fin m → Fin 2) (β : Fin m → ℚ) (d : Fin m → ℕ) (Θ : ℝ)
    (hvan : ∀ α : (Fin m × Fin 2) →₀ ℕ,
      Commons.Algebra.MvPolynomial.indexWt (fun hi : Fin m × Fin 2 => d hi.1) α < m * Θ →
      MvPolynomial.aeval (chartPoint c β)
        (Commons.Algebra.MvPolynomial.pderivIter α G) = 0) :
    m * Θ ≤ index (chartPoint c β) (fun hi : Fin m × Fin 2 => d hi.1) G := by
  classical
  rw [index_def]
  refine le_csInf ?_ ?_
  · rw [Commons.Algebra.MvPolynomial.indexSet_eq_image]
    exact Finset.image_nonempty.mpr (MvPolynomial.support_nonempty.mpr
      ((Commons.Algebra.MvPolynomial.indexTay_injective (chartPoint c β)).ne hG))
  · intro t ht
    rw [Commons.Algebra.MvPolynomial.indexSet_eq_image, Finset.mem_coe, Finset.mem_image] at ht
    obtain ⟨mm, hmm, rfl⟩ := ht
    by_contra hlt
    rw [not_le] at hlt
    have hz := hvan mm hlt
    have hcoeff : (Commons.Algebra.MvPolynomial.indexTay (chartPoint c β) G).coeff mm ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hmm
    have hfact := Commons.Algebra.MvPolynomial.coeff_indexTay_mul_factorial (chartPoint c β) mm G
    rw [eval_eq_aeval', hz] at hfact
    have hfac : (∏ i : Fin m × Fin 2, ((mm i).factorial : ℚ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    exact (mul_ne_zero hfac hcoeff) hfact

/-! ## The elimination invariant in chart form -/

/-- If every derivative of `F` of weighted size `< m Θ` vanishes on the product of the
hyperplanes (tested by the pivot substitution), then so does the corresponding derivative of
the eliminated polynomial, dehomogenised at the chart. -/
theorem chartSubst_elimF_vanishing {K : Type*} [Field K]
    (F : MvPolynomial (Fin m × Fin N) K) (hF : F ≠ 0)
    (b : Fin m → Fin N → K) (hb : ∀ h, b h 0 ≠ 0)
    (q : Fin N) (hq : (q : ℕ) = 1) (d : Fin m → ℕ) (Θ : ℝ)
    (hvan : ∀ α : (Fin m × Fin 2) →₀ ℕ,
      Commons.Algebra.MvPolynomial.indexWt (fun hi : Fin m × Fin 2 => d hi.1) α < m * Θ →
      pivotSubst b (Commons.Algebra.MvPolynomial.pderivIter (α.mapDomain (keepMap q)) F) = 0) :
    ∀ α : (Fin m × Fin 2) →₀ ℕ,
      Commons.Algebra.MvPolynomial.indexWt (fun hi : Fin m × Fin 2 => d hi.1) α < m * Θ →
      chartSubst b q (Commons.Algebra.MvPolynomial.pderivIter (α.mapDomain (keepMap q))
        (elimF (elimList m N) F)) = 0 := by
  intro α hα
  have hq0 : q ≠ 0 := by intro hh; rw [hh] at hq; simp at hq
  have hnd : (elimList m N).Nodup := Finset.nodup_toList _
  have hz2 : ∀ z ∈ elimList m N, 2 ≤ (z.2 : ℕ) := fun z hz =>
    mem_elimList_toFinset.mp (List.mem_toFinset.mpr hz)
  have hfix : ∀ z ∈ elimList m N, pivotSubst b (MvPolynomial.X z) = MvPolynomial.X z := by
    intro z hz
    exact pivotSubst_X_of_ne b z.1 (fun hh => by
      have h := hz2 z hz
      rw [hh] at h
      simp at h)
  have hα0 : ∀ z ∈ elimList m N, (α.mapDomain (keepMap q)) z = 0 := by
    intro z hz
    have h2 := hz2 z hz
    rw [Finsupp.mapDomain_of_notMem_range]
    intro hmem
    obtain ⟨w, hw⟩ := hmem
    have hz' : (z.2 : ℕ) = 0 ∨ (z.2 : ℕ) = (q : ℕ) := by
      rw [← hw]
      by_cases hw0 : (w.2 : ℕ) = 0
      · left; simp [keepMap, hw0]
      · right; simp [keepMap, hw0]
    omega
  have hinv := (elim_invariant (elimList m N) (α.mapDomain (keepMap q)) F (pivotSubst b)
    hF hnd hfix hα0 (hvan α hα)).2
  rwa [elimRho_pivotSubst b hb hq] at hinv

/-! ## The main non-vanishing theorem -/

/-- **The non-vanishing lemma** (Evertse's Lemma 24, substitution form).

Let `F ∈ ℤ[X (h,j)]` (`h : Fin m`, `j : Fin N`, `N ≥ 2`) be nonzero and homogeneous of degree
`e h ≤ d h` in the block `h`, let `l_h = ∑_j b h j · X (h,j)` with `b h 0 ≠ 0`, and let
`Θ, η > 0` with `4 η < Θ` and the height condition
`η^{2^{m-1}} · ⨅_h (d h · logHeight₁ (b h q / b h 0)) ≥ hZ F + 100 m ∑ d h`.
Then some derivative of `F` of weighted size `< m Θ` does not vanish on the product of the
hyperplanes `Z(l_h)`; equivalently, the pivot substitution applied to it does not vanish. -/
theorem nonvanish_core {m N : ℕ} [NeZero m] [NeZero N] (hN : 2 ≤ N)
    (F : MvPolynomial (Fin m × Fin N) ℤ) (hF : F ≠ 0)
    (e : Fin m → ℕ) (hhom : IsBlockHom e (F.map (Int.castRingHom ℚ)))
    (d : Fin m → ℕ) (hd : ∀ h, 1 ≤ d h) (hle : ∀ h, e h ≤ d h)
    (b : Fin m → Fin N → ℚ) (hb : ∀ h, b h 0 ≠ 0)
    (q : Fin N) (hq : (q : ℕ) = 1)
    (Θ η : ℝ) (hΘ : 0 < Θ) (hη0 : 0 < η) (hη : η ≤ 1 / 2) (hηΘ : 4 * η < Θ)
    (hratio : ∀ i j : Fin m, i ≤ j →
      (d i : ℝ) ≤ η ^ (2 ^ (m - 1) * ((j : ℕ) - (i : ℕ))) * (d j : ℝ))
    (hcond : η ^ (2 ^ (m - 1)) *
        (⨅ h : Fin m, (d h : ℝ) * Height.logHeight₁ (-(b h q) / (b h 0))) ≥
        hZ F + 100 * (m : ℝ) * (∑ h : Fin m, (d h : ℝ))) :
    ∃ α : (Fin m × Fin 2) →₀ ℕ,
      Commons.Algebra.MvPolynomial.indexWt (fun hi : Fin m × Fin 2 => d hi.1) α < m * Θ ∧
      pivotSubst b (Commons.Algebra.MvPolynomial.pderivIter (α.mapDomain (keepMap q))
        (F.map (Int.castRingHom ℚ))) ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hq0 : q ≠ 0 := by intro hh; rw [hh] at hq; simp at hq
  -- ### The elimination over `ℚ` and its integral companion
  have hFq_ne : F.map (Int.castRingHom ℚ) ≠ 0 := fun hh =>
    hF (MvPolynomial.map_injective _ intCast_injective' hh)
  have hnd : (elimList m N).Nodup := Finset.nodup_toList _
  have hfreeFq : FreeOf (K := ℚ) (∅ : Finset (Fin m × Fin N)) (F.map (Int.castRingHom ℚ)) :=
    fun u _ z hz => absurd hz (Finset.notMem_empty z)
  have hfree := (freeOf_elimF (elimList m N) (F.map (Int.castRingHom ℚ)) ∅ hnd
    (by simp) hfreeFq).2
  have hGq_ne : elimF (elimList m N) (F.map (Int.castRingHom ℚ)) ≠ 0 :=
    elimF_ne_zero _ _ hFq_ne
  have hcomp : MvPolynomial.rename (keepMap q) (MvPolynomial.rename (dropMap m N)
      (elimF (elimList m N) (F.map (Int.castRingHom ℚ)))) =
      elimF (elimList m N) (F.map (Int.castRingHom ℚ)) :=
    rename_keepMap_dropMap_eq_of_free (K := ℚ) hq _ hfree
  have hGq2_ne : MvPolynomial.rename (dropMap m N)
      (elimF (elimList m N) (F.map (Int.castRingHom ℚ))) ≠ 0 := by
    intro hh
    exact hGq_ne (by rw [← hcomp, hh, map_zero])
  have hGzGq : elimF (elimList m N) (F.map (Int.castRingHom ℚ)) =
      (elimFZ (elimList m N) F).map (Int.castRingHom ℚ) := elimFZ_map_intCast _ _
  have hGz2_map : MvPolynomial.rename (dropMap m N)
      (elimF (elimList m N) (F.map (Int.castRingHom ℚ))) =
      (MvPolynomial.rename (dropMap m N) (elimFZ (elimList m N) F)).map
        (Int.castRingHom ℚ) := by
    rw [hGzGq, ← MvPolynomial.map_rename]
  have hGz2_ne : MvPolynomial.rename (dropMap m N) (elimFZ (elimList m N) F) ≠ 0 := by
    intro hh
    exact hGq2_ne (by rw [hGz2_map, hh, map_zero])
  have hkeep_eq : MvPolynomial.rename (keepMap q) (MvPolynomial.rename (dropMap m N)
      (elimFZ (elimList m N) F)) = elimFZ (elimList m N) F := by
    apply MvPolynomial.map_injective (Int.castRingHom ℚ) intCast_injective'
    rw [MvPolynomial.map_rename, MvPolynomial.map_rename, ← hGzGq, hcomp]
  -- ### Block homogeneity of the compressed polynomial
  obtain ⟨e', he', hle'⟩ := exists_isBlockHom_elimF (K := ℚ) (elimList m N)
    (F.map (Int.castRingHom ℚ)) e hhom
  have hhom2 : ∀ u ∈ (MvPolynomial.rename (dropMap m N)
      (elimF (elimList m N) (F.map (Int.castRingHom ℚ)))).support, ∀ h : Fin m,
      u (h, 0) + u (h, 1) = e' h := by
    intro u hu h
    have hmem : Finsupp.mapDomain (keepMap q) u ∈
        (elimF (elimList m N) (F.map (Int.castRingHom ℚ))).support := by
      rw [← hcomp, MvPolynomial.support_rename_of_injective (keepMap_injective hq0),
        Finset.mem_image]
      exact ⟨u, hu, rfl⟩
    have hsum := he' _ hmem h
    rwa [sum_keepMap_apply q hq u h] at hsum
  -- ### The vanishing at the chart point
  have hvan' : ∀ α : (Fin m × Fin 2) →₀ ℕ,
      Commons.Algebra.MvPolynomial.indexWt (fun hi : Fin m × Fin 2 => d hi.1) α < m * Θ →
      chartSubst b q (Commons.Algebra.MvPolynomial.pderivIter (α.mapDomain (keepMap q))
        (elimF (elimList m N) (F.map (Int.castRingHom ℚ)))) = 0 :=
    chartSubst_elimF_vanishing (F.map (Int.castRingHom ℚ)) hFq_ne b hb q hq d Θ
      (fun α hα => hcon α hα)
  have hchartVanish : ∀ α : (Fin m × Fin 2) →₀ ℕ,
      Commons.Algebra.MvPolynomial.indexWt (fun hi : Fin m × Fin 2 => d hi.1) α < m * Θ →
      MvPolynomial.aeval (chartPoint (fun _ : Fin m => (1 : Fin 2)) (fun h => -(b h q) / (b h 0)))
        (Commons.Algebra.MvPolynomial.pderivIter α (MvPolynomial.rename (dropMap m N)
          (elimF (elimList m N) (F.map (Int.castRingHom ℚ))))) = 0 := by
    intro α hα
    have h1 := hvan' α hα
    set y : Fin m × Fin N → ℚ := fun z =>
      if z.2 = 0 then -(b z.1 0)⁻¹ * b z.1 q else if z.2 = q then 1 else 0 with hy
    have hx1 : ∀ h, y (h, 0) = -(b h 0)⁻¹ * b h q * y (h, q) := by
      intro h
      have hx0 : y (h, 0) = -(b h 0)⁻¹ * b h q := by rw [hy]; simp
      have hxq : y (h, q) = 1 := by rw [hy]; simp [hq0]
      rw [hx0, hxq, mul_one]
    have hx2 : ∀ h j, j ≠ 0 → j ≠ q → y (h, j) = 0 := by
      intro h j hj0 hjq
      rw [hy]; simp [hj0, hjq]
    have h2 := aeval_chartSubst_eq_zero_of b hq0 y hx1 hx2
      (Commons.Algebra.MvPolynomial.pderivIter (α.mapDomain (keepMap q))
        (elimF (elimList m N) (F.map (Int.castRingHom ℚ)))) h1
    rw [← hcomp, Commons.Algebra.MvPolynomial.pderivIter_rename (keepMap q)
      (keepMap_injective hq0) α
      (MvPolynomial.rename (dropMap m N) (elimF (elimList m N) (F.map (Int.castRingHom ℚ)))),
      MvPolynomial.aeval_rename] at h2
    have hpt : y ∘ keepMap q =
        chartPoint (fun _ : Fin m => (1 : Fin 2)) (fun h => -(b h q) / (b h 0)) := by
      funext z
      obtain ⟨h, i⟩ := z
      rcases fin2_eq_zero_or_one i with rfl | rfl
      · have hy0 : y (h, (0 : Fin N)) = -(b h 0)⁻¹ * b h q := by rw [hy]; simp
        have hc0 : chartPoint (fun _ : Fin m => (1 : Fin 2)) (fun h => -(b h q) / (b h 0))
            (h, (0 : Fin 2)) = -(b h q) / (b h 0) := by simp [chartPoint]
        rw [Function.comp_apply, keepMap_zero, hy0, hc0, div_eq_inv_mul]
        ring
      · have hyq : y (h, q) = 1 := by rw [hy]; simp [hq0]
        have hc1 : chartPoint (fun _ : Fin m => (1 : Fin 2)) (fun h => -(b h q) / (b h 0))
            (h, (1 : Fin 2)) = 1 := by simp [chartPoint]
        rw [Function.comp_apply, keepMap_one, hyq, hc1]
    rwa [hpt] at h2
  -- ### The index bound
  have hindex : m * Θ ≤ index (chartPoint (fun _ : Fin m => (1 : Fin 2))
      (fun h => -(b h q) / (b h 0))) (fun hi : Fin m × Fin 2 => d hi.1)
      (MvPolynomial.rename (dropMap m N) (elimF (elimList m N) (F.map (Int.castRingHom ℚ)))) :=
    index_ge_of_vanishing _ hGq2_ne _ _ d Θ hchartVanish
  have hindex2 : m * Θ ≤ index (chartPoint (fun _ : Fin m => (1 : Fin 2))
      (fun h => -(b h q) / (b h 0))) (fun hi : Fin m × Fin 2 => d hi.1)
      ((MvPolynomial.rename (dropMap m N) (elimFZ (elimList m N) F)).map (Int.castRingHom ℚ)) := by
    rw [← hGz2_map]
    exact hindex
  -- ### The projective Roth lemma
  have hhZle : hZ (MvPolynomial.rename (dropMap m N) (elimFZ (elimList m N) F)) ≤ hZ F := by
    have h1 : hZ (MvPolynomial.rename (dropMap m N) (elimFZ (elimList m N) F)) ≤
        hZ (MvPolynomial.rename (keepMap q) (MvPolynomial.rename (dropMap m N)
          (elimFZ (elimList m N) F))) := by
      simp only [hZ, Height.logHeight_eq_log_mulHeight]
      refine Real.log_le_log ?_ ?_
      · rw [Commons.NumberTheory.Height.MvPolynomial.mulHeight_gP_eq]
        exact Height.mulHeight_pos _
      · apply mulHeight_gP_le_of_coeff_map _ _ (fun t => Finsupp.mapDomain (keepMap q) t)
        intro t _
        rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map,
          MvPolynomial.coeff_rename_mapDomain (keepMap q) (keepMap_injective hq0)]
    rw [hkeep_eq] at h1
    exact le_trans h1 (hZ_elimFZ_le _ _)
  have hcond' : η ^ (2 ^ (m - 1)) *
      (⨅ h : Fin m, (d h : ℝ) * Height.logHeight₁ (-(b h q) / (b h 0))) ≥
      hZ (MvPolynomial.rename (dropMap m N) (elimFZ (elimList m N) F)) +
        100 * (m : ℝ) * (∑ h : Fin m, (d h : ℝ)) := by
    linarith
  have hhomZ : ∀ u ∈ (MvPolynomial.rename (dropMap m N) (elimFZ (elimList m N) F)).support,
      ∀ h : Fin m, u (h, 0) + u (h, 1) = e' h := by
    intro u hu h
    refine hhom2 u ?_ h
    rw [hGz2_map, MvPolynomial.support_map_of_injective _ intCast_injective']
    exact hu
  have hroth := roth_proj (MvPolynomial.rename (dropMap m N) (elimFZ (elimList m N) F)) d e'
    hd (fun h => le_trans (hle' h) (hle h)) hGz2_ne hhomZ (fun _ : Fin m => (1 : Fin 2))
    (fun h => -(b h q) / (b h 0)) η hη0 hη hratio hcond'
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hcontra : 4 * (m : ℝ) * η < m * Θ := by nlinarith [hηΘ]
  linarith

end Submission.Subspace

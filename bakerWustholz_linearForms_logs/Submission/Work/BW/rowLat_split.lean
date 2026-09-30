import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Module

section Purity

variable {ι : Type*} [Fintype ι] {n : ℕ} {K : Submodule ℤ (ι → ℤ)}

omit [Fintype ι] in
/-- **Saturation gives the SNF basis vectors.** If `K ≤ ℤ^ι` is saturated (pure), then for a
Smith-normal-form pair of bases `bM` of `ℤ^ι` and `bN` of `K` with `bN i = a i • bM (f i)`, the
vectors `bM (f i)` themselves already lie in `K`. -/
private lemma snf_bM_mem (snf : Module.Basis.SmithNormalForm K ι n)
    (hpure : ∀ (x : ι → ℤ) (m : ℤ), m ≠ 0 → m • x ∈ K → x ∈ K) (i : Fin n) :
    snf.bM (snf.f i) ∈ K := by
  have hne : snf.bN i ≠ 0 := Module.Basis.ne_zero snf.bN i
  have ha : snf.a i ≠ 0 := by
    intro hai
    apply hne
    apply Subtype.ext
    show (snf.bN i : ι → ℤ) = 0
    rw [snf.snf i, hai, zero_smul]
  have hmem : snf.a i • snf.bM (snf.f i) ∈ K := by
    rw [← snf.snf i]
    exact (snf.bN i).2
  exact hpure _ _ ha hmem

/-- Every element of `K` is the corresponding combination of the `bM (f i)`: its `bM`-coordinates
vanish outside `Set.range snf.f`. -/
private lemma snf_expansion (snf : Module.Basis.SmithNormalForm K ι n) (y : K) :
    (y : ι → ℤ) = ∑ i : Fin n, (snf.bM.repr (y : ι → ℤ) (snf.f i)) • snf.bM (snf.f i) := by
  classical
  let g : ι → ι → ℤ := fun j => (snf.bM.repr (y : ι → ℤ) j) • snf.bM j
  have hrepr : ∑ j : ι, g j = (y : ι → ℤ) := snf.bM.sum_repr (y : ι → ℤ)
  have h1 : ∑ j ∈ (Finset.univ.image snf.f : Finset ι), g j = ∑ j : ι, g j := by
    rw [Finset.sum_subset (Finset.subset_univ _)]
    intro j _ hj
    have hj' : j ∉ Set.range snf.f := by simpa [Finset.mem_image, Set.mem_range] using hj
    simp [g, snf.repr_eq_zero_of_notMem_range y hj']
  have h2 : ∑ j ∈ (Finset.univ.image snf.f : Finset ι), g j
      = ∑ i : Fin n, g (snf.f i) := by
    rw [Finset.sum_image]
    exact snf.f.injective.injOn
  exact hrepr.symm.trans (h1.symm.trans h2)

end Purity

/-- The rows of a `ℚ`-linearly independent integer matrix are `ℤ`-linearly independent. -/
private lemma rows_linearIndependent {N ρ : ℕ} (M : Matrix (Fin ρ) (Fin N) ℤ)
    (hM : LinearIndependent ℚ (fun j i => (M j i : ℚ))) :
    LinearIndependent ℤ (fun j : Fin ρ => M j) := by
  rw [Fintype.linearIndependent_iff] at hM ⊢
  intro g hg j
  have hg' : (∑ j, (g j : ℚ) • (fun i => (M j i : ℚ))) = 0 := by
    funext i
    have h := congr_fun hg i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h ⊢
    have h2 := congrArg (fun z : ℤ => (z : ℚ)) h
    push_cast at h2
    simpa using h2
  have h0 := hM (fun j => (g j : ℚ)) hg' j
  exact_mod_cast h0

/-- **Splitting of a primitive system of integer linear forms.** If the rows of `M` are
`ℚ`-linearly independent and their `ℤ`-span is saturated in `ℤ^N` (equivalently: the maximal
minors of `M` are coprime), then `M` admits an integral right inverse `S`: `M * S = 1`.

The proof uses the Smith normal form of the row lattice `𝒵 = span ℤ (range M)`: saturation
forces `𝒵` to be spanned by basis vectors of `ℤ^N`, hence to be a direct summand of `ℤ^N`. The
projection onto `𝒵` composed with the inverse of the row basis of `𝒵` gives the required `S`. -/
theorem rowLat_split {N ρ : ℕ} (M : Matrix (Fin ρ) (Fin N) ℤ) (hρ : ρ ≤ N) (hM : PrimSys M) :
    ∃ S : Matrix (Fin N) (Fin ρ) ℤ, M * S = 1 := by
  classical
  -- the rows of `M`, as a family of integer vectors
  let rM : Fin ρ → Fin N → ℤ := M
  have hli : LinearIndependent ℤ (fun j : Fin ρ => rM j) := rows_linearIndependent M hM.1
  set K : Submodule ℤ (Fin N → ℤ) := Submodule.span ℤ (Set.range rM) with hK
  have hpure : ∀ (x : Fin N → ℤ) (m : ℤ), m ≠ 0 → m • x ∈ K → x ∈ K := by
    intro x m hm hx
    exact hM.2 x m hm hx
  obtain ⟨n, snf⟩ := K.smithNormalForm (Pi.basisFun ℤ (Fin N))
  have hmem : ∀ i : Fin n, snf.bM (snf.f i) ∈ K := fun i => snf_bM_mem snf hpure i
  -- the Smith-normal-form projection of `ℤ^N` onto `K`
  let proj : (Fin N → ℤ) →ₗ[ℤ] (Fin N → ℤ) :=
    snf.bM.constr ℤ (fun t : Fin N => if ht : t ∈ Set.range snf.f then snf.bM t else 0)
  have hproj_basis : ∀ t : Fin N, proj (snf.bM t)
      = (if ht : t ∈ Set.range snf.f then snf.bM t else 0) := by
    intro t
    simp only [proj, Module.Basis.constr_basis]
  have hproj : ∀ x : Fin N → ℤ, proj x ∈ K := by
    intro x
    have h1 : proj x = ∑ t : Fin N, (snf.bM.repr x t) • proj (snf.bM t) := by
      conv_lhs => rw [← snf.bM.sum_repr x]
      rw [map_sum]
      exact Finset.sum_congr rfl (fun t _ => by rw [map_smul])
    rw [h1]
    refine Submodule.sum_mem _ (fun t _ => Submodule.smul_mem _ _ ?_)
    rw [hproj_basis t]
    by_cases ht : t ∈ Set.range snf.f
    · rw [dite_eq_left ht]
      obtain ⟨i, hi⟩ := ht
      rw [← hi]
      exact hmem i
    · rw [dite_eq_right ht]
      exact K.zero_mem
  let π : (Fin N → ℤ) →ₗ[ℤ] K := proj.codRestrict K hproj
  have hretract : ∀ y : K, π (y : Fin N → ℤ) = y := by
    intro y
    apply Subtype.ext
    show proj (y : Fin N → ℤ) = (y : Fin N → ℤ)
    rw [snf_expansion snf y]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, hproj_basis (snf.f i), dite_eq_left ⟨i, rfl⟩]
  -- the basis of `K` given by the rows of `M`
  have hsp : ⊤ ≤ Submodule.span ℤ
      (Set.range (fun j : Fin ρ => (⟨rM j, Submodule.subset_span (Set.mem_range_self j)⟩ : K))) := by
    rintro x -
    rw [Submodule.mem_span_range_iff_exists_fun ℤ]
    have hx : (x : Fin N → ℤ) ∈ Submodule.span ℤ (Set.range rM) := x.2
    rw [Submodule.mem_span_range_iff_exists_fun ℤ] at hx
    obtain ⟨c, hc⟩ := hx
    refine ⟨c, ?_⟩
    apply Subtype.ext
    have hcoe : (K.subtype : K →ₗ[ℤ] (Fin N → ℤ))
        (∑ i : Fin ρ, c i • (⟨rM i, Submodule.subset_span (Set.mem_range_self i)⟩ : K))
        = ∑ i : Fin ρ, c i • rM i := by
      rw [map_sum]
      simp only [map_smul, Submodule.subtype_apply]
    exact hcoe.trans hc
  have hliK : LinearIndependent ℤ (fun j : Fin ρ =>
      (⟨rM j, Submodule.subset_span (Set.mem_range_self j)⟩ : K)) :=
    linearIndependent_span hli
  let bK : Basis (Fin ρ) ℤ K :=
    Basis.mk (v := fun j : Fin ρ =>
      (⟨rM j, Submodule.subset_span (Set.mem_range_self j)⟩ : K)) hliK hsp
  let ψ : K →ₗ[ℤ] (Fin ρ → ℤ) := bK.constr ℤ (fun j => Pi.single j 1)
  have hψ : ∀ j : Fin ρ, ψ (bK j) = Pi.single j 1 := by
    intro j
    simp only [ψ, Module.Basis.constr_basis]
  have hψv : ∀ j : Fin ρ,
      ψ (⟨rM j, Submodule.subset_span (Set.mem_range_self j)⟩ : K) = Pi.single j 1 := by
    intro j
    have h1 : (⟨rM j, Submodule.subset_span (Set.mem_range_self j)⟩ : K) = bK j := by
      rw [show bK j = (⟨rM j, Submodule.subset_span (Set.mem_range_self j)⟩ : K) from
        Basis.mk_apply hliK hsp j]
    rw [h1]
    exact hψ j
  let T : (Fin N → ℤ) →ₗ[ℤ] (Fin ρ → ℤ) := ψ.comp π
  have hrow : ∀ j : Fin ρ, T (rM j) = Pi.single j 1 := by
    intro j
    have h1 : π (rM j) = (⟨rM j, Submodule.subset_span (Set.mem_range_self j)⟩ : K) :=
      hretract ⟨rM j, Submodule.subset_span (Set.mem_range_self j)⟩
    calc T (rM j) = ψ (π (rM j)) := rfl
      _ = ψ (⟨rM j, Submodule.subset_span (Set.mem_range_self j)⟩ : K) := by rw [h1]
      _ = Pi.single j 1 := hψv j
  refine ⟨(fun i k => T (Pi.single i 1) k : Matrix (Fin N) (Fin ρ) ℤ), ?_⟩
  ext j k
  have key : (∑ i : Fin N, rM j i * T (Pi.single i 1) k) = (if j = k then 1 else 0) := by
    have hsum : (∑ i : Fin N, rM j i • (Pi.single i (1 : ℤ) : Fin N → ℤ)) = rM j := by
      simpa using (Pi.basisFun ℤ (Fin N)).sum_repr (rM j)
    calc (∑ i : Fin N, rM j i * T (Pi.single i 1) k)
        = (∑ i : Fin N, rM j i • T (Pi.single i 1)) k := by
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      _ = (T (∑ i : Fin N, rM j i • (Pi.single i (1 : ℤ) : Fin N → ℤ))) k := by
          rw [map_sum]
          simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      _ = (T (rM j)) k := by rw [hsum]
      _ = (Pi.single j (1 : ℤ) : Fin ρ → ℤ) k := by rw [hrow j]
      _ = (if j = k then 1 else 0) := by
          rw [Pi.single_apply]
          by_cases h : j = k
          · simp [h]
          · simp [h, Ne.symm h]
  exact key

end Work.BW

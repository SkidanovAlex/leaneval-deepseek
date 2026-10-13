import Mathlib

/-!
# Coordinate projections onto a submodule of an affine coordinate space

We prove that for any linear map `A : (Fin M → ℝ) →ₗ[ℝ] (Fin n → ℝ)` and any
`m ≤ finrank ℝ A.range` there is an embedding `e : Fin m ↪ Fin n` of coordinates such
that the coordinate projection `v ↦ (A v) ∘ e` is surjective.

The mathematical content is the standard linear-algebra fact that a subspace `W ≤ ℝⁿ` of
dimension `r` admits `r` coordinates whose coordinate projection restricts to an isomorphism
`W ≅ ℝʳ`.  We prove it through duality: the coordinate functionals restricted to `W` span the
dual `W*`, one selects `m` of them that are linearly independent (a linear map to `ℝᵐ` whose
dual is injective is surjective), and linear independence of the restrictions is exactly the
statement that the coordinate projection is surjective.
-/

namespace Work.WilE7.DimAPI

/-- From a spanning family `v : ι → V` of a finite-dimensional real vector space one can select
`k` members (`k ≤ finrank ℝ V`) that are linearly independent. -/
theorem exists_linearIndependent_comp_of_span_eq_top {V : Type*} [AddCommGroup V] [Module ℝ V]
    {ι : Type*} [Fintype ι] (v : ι → V) (hspan : Submodule.span ℝ (Set.range v) = ⊤)
    (k : ℕ) (hk : k ≤ Module.finrank ℝ V) :
    ∃ a : Fin k ↪ ι, LinearIndependent ℝ (v ∘ a) := by
  obtain ⟨κ, a, ha, hspan', hli⟩ := exists_linearIndependent' ℝ v
  have : Fintype κ := Fintype.ofInjective a ha
  have hcard : Module.finrank ℝ V = Fintype.card κ := by
    have h1 := finrank_span_eq_card hli
    rw [hspan', hspan, finrank_top] at h1
    exact h1
  have hk' : k ≤ Fintype.card κ := by rw [← hcard]; exact hk
  let e : Fin k ↪ κ := (Fin.castLEEmb hk').trans (Fintype.equivFin κ).symm.toEmbedding
  refine ⟨e.trans ⟨a, ha⟩, ?_⟩
  have := hli.comp e e.injective
  simpa [Function.comp_assoc, Function.Embedding.trans_apply] using this

/-- The coordinate projections `x ↦ x i` span the dual of `Fin k → ℝ`. -/
theorem span_range_coordProj_eq_top (k : ℕ) :
    Submodule.span ℝ (Set.range (fun i : Fin k => (LinearMap.proj i : (Fin k → ℝ) →ₗ[ℝ] ℝ))) = ⊤ := by
  apply le_antisymm le_top
  intro lam _
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun i => lam (Pi.single i 1), ?_⟩
  apply LinearMap.ext
  intro x
  have hx : x = ∑ i, x i • Pi.single i 1 := by
    rw [← Finset.univ_sum_single x]
    exact Finset.sum_congr rfl (fun i _ => by
      funext j; by_cases h : j = i <;> simp [Pi.single_apply, h])
  have hL : (∑ i, lam (Pi.single i 1) • (LinearMap.proj i : (Fin k → ℝ) →ₗ[ℝ] ℝ)) x
      = ∑ i, lam (Pi.single i 1) * x i := by
    rw [LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  have hR : lam x = ∑ i, lam (Pi.single i 1) * x i := by
    conv_lhs => rw [hx]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, smul_eq_mul, mul_comm]
  rw [hL, hR]

/-- If the composites of `ψ` with the coordinate projections of `Fin m → ℝ` are linearly
independent, then `ψ` is surjective. -/
theorem surjective_of_linearIndependent_coordProj_comp {W : Type*} [AddCommGroup W] [Module ℝ W]
    {m : ℕ} (ψ : W →ₗ[ℝ] (Fin m → ℝ))
    (h : LinearIndependent ℝ (fun j : Fin m => (LinearMap.proj j).comp ψ)) :
    Function.Surjective ψ := by
  have hle : Submodule.span ℝ (Set.range (fun j : Fin m => (LinearMap.proj j).comp ψ))
      ≤ ψ.dualMap.range := by
    rw [Submodule.span_le]
    rintro x ⟨j, rfl⟩
    exact ⟨LinearMap.proj j, by ext w; simp [LinearMap.dualMap_apply, LinearMap.comp_apply]⟩
  have : Module.Finite ℝ ↥ψ.dualMap.range :=
    Module.Finite.of_surjective ψ.dualMap.rangeRestrict (LinearMap.surjective_rangeRestrict ψ.dualMap)
  have h1' : Module.finrank ℝ (Submodule.span ℝ (Set.range (fun j : Fin m => (LinearMap.proj j).comp ψ)))
      ≤ Module.finrank ℝ ψ.dualMap.range := Submodule.finrank_mono hle
  have hcard : Module.finrank ℝ
      (Submodule.span ℝ (Set.range (fun j : Fin m => (LinearMap.proj j).comp ψ))) = m := by
    rw [finrank_span_eq_card h, Fintype.card_fin]
  have h1 : m ≤ Module.finrank ℝ ψ.range :=
    (le_of_eq hcard.symm).trans (h1'.trans_eq (LinearMap.finrank_range_dualMap_eq_finrank_range ψ))
  have h2 : Module.finrank ℝ ψ.range ≤ m := by
    calc Module.finrank ℝ ψ.range ≤ Module.finrank ℝ (Fin m → ℝ) := Submodule.finrank_le _
      _ = m := Module.finrank_fin_fun ℝ
  have hfin : Module.finrank ℝ ψ.range = Module.finrank ℝ (Fin m → ℝ) := by
    rw [Module.finrank_fin_fun]; exact le_antisymm h2 h1
  exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq hfin)

/-- For a submodule `W ≤ (Fin n → ℝ)` and `m ≤ finrank ℝ W` there is an embedding of
coordinates `e : Fin m ↪ Fin n` such that the coordinate projection onto `e` is surjective
on `W`. -/
theorem exists_coordProj_surj_submodule {n : ℕ} (W : Submodule ℝ (Fin n → ℝ)) (m : ℕ)
    (h : m ≤ Module.finrank ℝ W) :
    ∃ e : Fin m ↪ Fin n, Function.Surjective
      ((LinearMap.pi (fun j : Fin m => (LinearMap.proj (e j) : (Fin n → ℝ) →ₗ[ℝ] ℝ))).comp W.subtype) := by
  have hspanproj : Submodule.span ℝ
      (Set.range (fun i : Fin n => (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ))) = ⊤ :=
    span_range_coordProj_eq_top n
  have hspan : Submodule.span ℝ (Set.range (fun i : Fin n => W.dualRestrict (LinearMap.proj i))) = ⊤ := by
    have heq : (fun i : Fin n => W.dualRestrict (LinearMap.proj i))
        = W.dualRestrict ∘ (fun i : Fin n => (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ)) := rfl
    rw [heq, Set.range_comp, Submodule.span_image, hspanproj, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (Subspace.dualRestrict_surjective (W := W))
  obtain ⟨e, hli⟩ := exists_linearIndependent_comp_of_span_eq_top
      (fun i : Fin n => W.dualRestrict (LinearMap.proj i)) hspan m
      (by simpa [Subspace.dual_finrank_eq] using h)
  refine ⟨e, ?_⟩
  set ψ : W →ₗ[ℝ] (Fin m → ℝ) :=
    (LinearMap.pi (fun j : Fin m => (LinearMap.proj (e j) : (Fin n → ℝ) →ₗ[ℝ] ℝ))).comp W.subtype with hψ
  have hfun : (fun j : Fin m => (LinearMap.proj j).comp ψ)
      = (fun i : Fin n => W.dualRestrict (LinearMap.proj i)) ∘ e := by
    funext j
    ext w
    simp [hψ, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.dualRestrict_apply]
  exact surjective_of_linearIndependent_coordProj_comp ψ (by rw [hfun]; exact hli)

theorem exists_coordProj_surj_of_le_finrank {M n m : ℕ}
    (A : (Fin M → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (h : m ≤ Module.finrank ℝ A.range) :
    ∃ e : Fin m ↪ Fin n, Function.Surjective (fun v : Fin M → ℝ => (A v) ∘ e) := by
  obtain ⟨e, he⟩ := exists_coordProj_surj_submodule A.range m h
  refine ⟨e, ?_⟩
  intro y
  obtain ⟨w, hw⟩ := he y
  obtain ⟨v, hv⟩ := LinearMap.mem_range.mp w.2
  refine ⟨v, ?_⟩
  show (A v) ∘ (e : Fin m → Fin n) = y
  have hcomp : (A v) ∘ (e : Fin m → Fin n)
      = (LinearMap.pi (fun j : Fin m => (LinearMap.proj (e j) : (Fin n → ℝ) →ₗ[ℝ] ℝ))) (A v) := by
    funext j; simp [LinearMap.pi_apply, LinearMap.proj_apply]
  rw [hcomp, hv]
  simpa using hw

end Work.WilE7.DimAPI

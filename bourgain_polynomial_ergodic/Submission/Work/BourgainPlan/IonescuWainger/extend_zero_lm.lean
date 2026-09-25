import Mathlib

/-!
# Extending a function on a finite subset of `ℤ` by zero

`extendZeroLM S : (↥S → ℂ) →ₗ[ℂ] (ℤ →₀ ℂ)` is the linear map that views a function on a finite
set `S : Finset ℤ` as a finitely supported function on `ℤ`, extended by zero outside `S`.

It is the tool that lets a statement about *finitely supported* `f : ℤ →₀ ℂ` be reduced, for every
finite `F ⊆ ℤ`, to a statement about the *finite* index type `↥f.support`.
-/

namespace Work.BourgainPlan.IonescuWainger

open scoped BigOperators

noncomputable section

/-- Extend a function on a finset `S : Finset ℤ` by zero to a finitely supported function on `ℤ`. -/
noncomputable def extendZeroLM (S : Finset ℤ) : (↥S → ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) where
  toFun g := Finsupp.embDomain (Function.Embedding.subtype (fun n : ℤ => n ∈ S))
    ((Finsupp.linearEquivFunOnFinite ℂ ℂ ↥S).symm g)
  map_add' g h := by
    simp only [map_add, Finsupp.embDomain_add]
  map_smul' c g := by
    simp only [map_smul, Finsupp.embDomain_eq_mapDomain, Finsupp.mapDomain_smul,
      RingHom.id_apply]

lemma extendZeroLM_apply (S : Finset ℤ) (g : ↥S → ℂ) (n : ℤ) :
    extendZeroLM S g n = if h : n ∈ S then g ⟨n, h⟩ else 0 := by
  change Finsupp.embDomain (Function.Embedding.subtype (fun m : ℤ => m ∈ S))
    ((Finsupp.linearEquivFunOnFinite ℂ ℂ ↥S).symm g) n
      = if h : n ∈ S then g ⟨n, h⟩ else 0
  rw [Finsupp.embDomain_apply]
  by_cases hn : n ∈ S
  · have hcho : (⟨⟨n, hn⟩, rfl⟩ : ∃ a : ↥S,
        (Function.Embedding.subtype (fun m : ℤ => m ∈ S)) a = n).choose = ⟨n, hn⟩ :=
      Subtype.ext (Exists.choose_spec (⟨⟨n, hn⟩, rfl⟩ : ∃ a : ↥S,
        (Function.Embedding.subtype (fun m : ℤ => m ∈ S)) a = n))
    rw [dif_pos ⟨⟨n, hn⟩, rfl⟩, dif_pos hn, hcho]
    exact congrFun (Finsupp.linearEquivFunOnFinite_symm_apply ℂ ℂ ↥S g) ⟨n, hn⟩
  · have hno : ¬ ∃ a : ↥S, (Function.Embedding.subtype (fun m : ℤ => m ∈ S)) a = n := by
      rintro ⟨a, ha⟩
      exact hn (ha ▸ a.2)
    rw [dif_neg hno, dif_neg hn]

lemma extendZeroLM_self (f : ℤ →₀ ℂ) : extendZeroLM f.support (fun a => f a) = f := by
  ext n
  simp only [extendZeroLM_apply]
  by_cases hn : n ∈ f.support
  · rw [dif_pos hn]
  · rw [dif_neg hn]; exact (Finsupp.notMem_support_iff.mp hn).symm

lemma tsum_norm_extendZeroLM (S : Finset ℤ) (g : ↥S → ℂ) {q : ℝ} (hq : 0 < q) :
    (∑' n : ℤ, ‖extendZeroLM S g n‖ ^ q) = ∑ a : ↥S, ‖g a‖ ^ q := by
  rw [tsum_eq_sum (s := S) (f := fun n : ℤ => ‖extendZeroLM S g n‖ ^ q)]
  · rw [Finset.sum_subtype S (fun x => Iff.rfl) (fun n => ‖extendZeroLM S g n‖ ^ q)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [extendZeroLM_apply, dif_pos a.2]
  · intro n hn
    rw [extendZeroLM_apply, dif_neg hn, norm_zero, Real.zero_rpow (ne_of_gt hq)]

end

end Work.BourgainPlan.IonescuWainger

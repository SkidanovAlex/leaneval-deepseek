import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Ring.IsFormallyReal
import Submission.Commons.LinearAlgebra.Orthogonal.odd_dim_det_one_fixed_vector

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.LinearAlgebra.Orthogonal

open LinearMap

/-- **Synge's linear-algebra input.**  An orthogonal map of a finite-dimensional real inner product
space of *even* dimension that fixes a nonzero vector `e` and has determinant `1` fixes some
nonzero vector orthogonal to `e`.  (Equivalently: the restriction to `e^⊥`, an odd-dimensional
space, is orthogonal with determinant `1`, hence has the eigenvalue `1`.) -/
theorem fixed_vector_compl_of_det_one
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {f : V →ₗ[ℝ] V} (hf : ∀ x y : V, inner ℝ (f x) (f y) = inner ℝ x y)
    (hfdim : Even (Module.finrank ℝ V)) {e : V} (he : e ≠ 0) (hfe : f e = e)
    (hdet : f.det = 1) :
    ∃ v : V, v ≠ 0 ∧ inner ℝ e v = 0 ∧ f v = v := by
  classical
  set U : Submodule ℝ V := Submodule.span ℝ {e} with hUdef
  -- `f` fixes `U = ℝ ∙ e` pointwise, hence preserves it.
  have hfUid : ∀ u ∈ U, f u = u := by
    intro u hu
    rw [hUdef] at hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [map_smul, hfe]
  have hfU : ∀ x ∈ U, f x ∈ U := fun x hx => by
    rw [hfUid x hx]; exact hx
  -- `f` preserves the orthogonal complement `Uᗮ = e^⊥`.
  have hfW : ∀ x ∈ Uᗮ, f x ∈ Uᗮ := by
    intro x hx
    rw [Submodule.mem_orthogonal] at hx ⊢
    intro u hu
    calc inner ℝ u (f x) = inner ℝ (f u) (f x) := by rw [hfUid u hu]
      _ = inner ℝ u x := hf u x
      _ = 0 := hx u hu
  -- The restriction `g` of `f` to `Uᗮ` is orthogonal.
  let g : (Uᗮ) →ₗ[ℝ] (Uᗮ) := f.restrict hfW
  have hg : ∀ x y : Uᗮ, inner ℝ (g x) (g y) = inner ℝ x y := by
    intro x y
    show inner ℝ (g x : V) (g y : V) = inner ℝ (x : V) (y : V)
    rw [show (g x : V) = f x from rfl, show (g y : V) = f y from rfl]
    exact hf x y
  -- An orthogonal endomorphism is injective, hence bijective in finite dimension.
  have hker : ∀ x : Uᗮ, g x = 0 → x = 0 := by
    intro x hx
    have h0 : inner ℝ (x : V) (x : V) = 0 := by
      have h := hg x x
      rw [hx] at h
      simpa using h.symm
    exact Subtype.ext (inner_self_eq_zero.mp h0)
  have hinj : Function.Injective g := by
    intro x y hxy
    have h : x - y = 0 := hker (x - y) (by rw [map_sub, hxy, sub_self])
    exact sub_eq_zero.mp h
  have hsurj : Function.Surjective g := LinearMap.injective_iff_surjective.mp hinj
  -- Promote `g` to an isometry equivalence of `Uᗮ`.
  let G : (Uᗮ) ≃ₗᵢ[ℝ] (Uᗮ) := (LinearEquiv.ofBijective g ⟨hinj, hsurj⟩).isometryOfInner hg
  have hGcoe : ((G : (Uᗮ) ≃ₗ[ℝ] (Uᗮ)) : (Uᗮ) →ₗ[ℝ] (Uᗮ)) = g := by
    rw [show (G : (Uᗮ) ≃ₗ[ℝ] (Uᗮ)) = LinearEquiv.ofBijective g ⟨hinj, hsurj⟩ from rfl]
    rfl
  -- `Uᗮ` is odd-dimensional.
  have hfr : Module.finrank ℝ (Uᗮ) = Module.finrank ℝ V - 1 := by
    have hU1 : Module.finrank ℝ U = 1 := by
      rw [hUdef]; exact finrank_span_singleton he
    have h := Submodule.finrank_add_finrank_orthogonal U
    rw [hU1] at h
    omega
  have hodd : Odd (Module.finrank ℝ (Uᗮ)) := by
    obtain ⟨k, hk⟩ := hfdim
    have h1 : 1 ≤ Module.finrank ℝ V := by
      have : 0 < Module.finrank ℝ V :=
        Module.finrank_pos_iff.mpr (nontrivial_of_ne e 0 he)
      omega
    rw [hfr]
    exact ⟨k - 1, by omega⟩
  -- The determinant of the restriction is `1`, by decomposing `V = U ⊕ Uᗮ`.
  have hdetg : LinearMap.det g = 1 := by
    set PE : (U × (Uᗮ)) ≃ₗ[ℝ] V :=
      Submodule.prodEquivOfIsCompl U (Uᗮ) U.isCompl_orthogonal with hPEdef
    have hconj : PE.symm.conj f = (f.restrict hfU).prodMap (f.restrict hfW) := by
      apply LinearMap.ext
      intro x
      apply PE.injective
      simp only [hPEdef, LinearEquiv.conj_apply_apply, LinearEquiv.apply_symm_apply,
        LinearEquiv.symm_symm, Submodule.coe_prodEquivOfIsCompl', LinearMap.prodMap_apply,
        coe_restrict_apply, map_add]
    have hd1 : (PE.symm.conj f).det = f.det := by
      have h := LinearMap.det_conj f PE.symm
      rw [LinearEquiv.symm_symm] at h
      rw [LinearEquiv.symm_conj_apply, LinearMap.comp_assoc]
      exact h
    have hd2 : (PE.symm.conj f).det =
        (f.restrict hfU).det * (f.restrict hfW).det := by
      rw [hconj, LinearMap.det_prodMap]
    have hone : f.restrict hfU = 1 := by
      apply LinearMap.ext
      intro x
      exact Subtype.ext (hfUid (x : V) x.2)
    have hdetU : (f.restrict hfU).det = 1 := by
      rw [hone, map_one LinearMap.det]
    show LinearMap.det (f.restrict hfW) = 1
    have h := hdet
    rw [← hd1, hd2, hdetU, one_mul] at h
    exact h
  -- Apply the odd-dimensional case to `g`.
  obtain ⟨w, hwne, hwfix⟩ := odd_dim_det_one_fixed_vector G hodd (by rw [hGcoe]; exact hdetg)
  refine ⟨(w : V), ?_, ?_, ?_⟩
  · intro h
    exact hwne (Subtype.ext h)
  · exact (Submodule.mem_orthogonal U (w : V)).mp w.2 e
      (Submodule.subset_span (Set.mem_singleton e))
  · have h2 : (G w : Uᗮ) = g w :=
      congrArg (fun φ : (Uᗮ) →ₗ[ℝ] (Uᗮ) => φ w) hGcoe
    have h1 : ((G w : Uᗮ) : V) = f (w : V) := by
      rw [h2]
      rfl
    rw [hwfix] at h1
    exact h1.symm

end Commons.LinearAlgebra.Orthogonal
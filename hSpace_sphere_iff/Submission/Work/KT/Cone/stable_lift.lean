import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Cone.RadialDefs
import Submission.Work.KT.Cone.continuous_comp_radialMap
import Submission.Work.KT.Cone.slice_one_inv_const
import Submission.Work.KT.Cone.mulProd_eq_one

namespace Work.KT.Cone

open Work.KT Matrix

noncomputable section

open Classical

/-- Given `GLStablyTrivial T` (`T` compact Hausdorff), every invertible matrix over `C(T, ℂ)`
lifts, after adding an identity block, to an invertible matrix over the mapping-cone algebra
`coneAlg f = C(T) ×_{C(S_V)} C(D_V)`.

Route.  GLStablyTrivial supplies `k` and an invertible `H : Matrix (Fin (n+k)) (Fin (n+k)) C(T × I, ℂ)`
whose slice at `0` is `u ⊕ 1` and whose slice at `1` is a constant matrix `c`.  The lift is the
matrix `v : Matrix (Fin (n+k)) (Fin (n+k)) (coneAlg f)` whose first component is `u ⊕ 1` and whose
second component `N : Matrix (Fin (n+k)) (Fin (n+k)) C(Ball V, ℂ)` is the "radial" extension
`N x = H (1 - ‖x‖, f (x/‖x‖))` for `x ≠ 0`, `N 0 = c`; it is continuous because the slice at `1`
of `H` is constant, it restricts to `(u ⊕ 1) ∘ f` on the boundary sphere, and it is
invertible-valued because `H` is. -/
theorem stable_lift (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : Type) [TopologicalSpace T] [CompactSpace T] [T2Space T] [Nonempty T]
    (f : C(Sph V, T)) (hgl : GLStablyTrivial T) :
    ∀ (n : ℕ) (u : Matrix (Fin n) (Fin n) C(T, ℂ)), IsUnit u →
      ∃ (k : ℕ) (v : Matrix (Fin (n + k)) (Fin (n + k)) (coneAlg f)), IsUnit v ∧
        v.map (coneToT f) = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks u 0 0 1) := by
  intro n u hu
  obtain ⟨k, H, hHunit, hH0, c₀, hH1⟩ := hgl n u hu
  let t₀ : T := Classical.choice ‹Nonempty T›
  obtain ⟨Hu, hHu⟩ := hHunit
  set H' : Matrix (Fin (n + k)) (Fin (n + k)) C(T × unitInterval, ℂ) := ↑(Hu⁻¹) with hH'def
  have hH'1 : H * H' = 1 := by
    rw [hH'def, ← hHu, ← Units.val_mul]
    simp
  have hH'2 : H' * H = 1 := by
    rw [hH'def, ← hHu, ← Units.val_mul]
    simp
  have hcH : ∀ (i j : Fin (n + k)) (t : T), H i j (t, 1) = c₀ i j := by
    intro i j t
    have h := congrArg (fun M : Matrix (Fin (n + k)) (Fin (n + k)) C(T, ℂ) => M i j) hH1
    simp only [Matrix.map_apply] at h
    have h2 := congrArg (fun φ : C(T, ℂ) => φ t) h
    simpa [sliceAt, pullAlg] using h2
  obtain ⟨c', hH'1'⟩ := slice_one_inv_const H H' hH'1 hH'2 ⟨c₀, hH1⟩
  have hcH' : ∀ (i j : Fin (n + k)) (t : T), H' i j (t, 1) = c' i j := by
    intro i j t
    have h := congrArg (fun M : Matrix (Fin (n + k)) (Fin (n + k)) C(T, ℂ) => M i j) hH'1'
    simp only [Matrix.map_apply] at h
    have h2 := congrArg (fun φ : C(T, ℂ) => φ t) h
    simpa [sliceAt, pullAlg] using h2
  let N : Matrix (Fin (n + k)) (Fin (n + k)) C(Ball V, ℂ) := fun i j =>
    ⟨fun x => H i j (radialMapAll f t₀ x),
      continuous_comp_radialMap f t₀ (H i j) (c₀ i j) (hcH i j)⟩
  let N' : Matrix (Fin (n + k)) (Fin (n + k)) C(Ball V, ℂ) := fun i j =>
    ⟨fun x => H' i j (radialMapAll f t₀ x),
      continuous_comp_radialMap f t₀ (H' i j) (c' i j) (hcH' i j)⟩
  let g : Matrix (Fin (n + k)) (Fin (n + k)) C(T, ℂ) := H.map (sliceAt (0 : unitInterval))
  let g' : Matrix (Fin (n + k)) (Fin (n + k)) C(T, ℂ) := H'.map (sliceAt (0 : unitInterval))
  have hgg' : g * g' = 1 := by
    have h := congrArg (fun M : Matrix (Fin (n + k)) (Fin (n + k)) C(T × unitInterval, ℂ) =>
      M.map (sliceAt (0 : unitInterval))) hH'1
    rw [Matrix.map_mul (f := sliceAt (0 : unitInterval)),
      Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact h
  have hg'g : g' * g = 1 := by
    have h := congrArg (fun M : Matrix (Fin (n + k)) (Fin (n + k)) C(T × unitInterval, ℂ) =>
      M.map (sliceAt (0 : unitInterval))) hH'2
    rw [Matrix.map_mul (f := sliceAt (0 : unitInterval)),
      Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact h
  have hmem : ∀ (i j : Fin (n + k)) (y : Ball V) (hy : ‖(y : V)‖ = 1),
      (N i j) y = (g i j) (f ⟨(y : V), mem_sphere_zero_iff_norm.mpr hy⟩) := by
    intro i j y hy
    have hy0 : (y : V) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hy; exact one_ne_zero hy.symm
    have hsphv : (sphProj y hy0 : V) = (y : V) := by
      rw [sphProj_coe, hy, inv_one, one_smul]
    have hsph : sphProj y hy0 = ⟨(y : V), mem_sphere_zero_iff_norm.mpr hy⟩ :=
      Subtype.ext hsphv
    have hrad : radialCoord y = 0 := by
      apply Subtype.ext
      simp [hy]
    show H i j (radialMapAll f t₀ y) = g i j (f ⟨(y : V), mem_sphere_zero_iff_norm.mpr hy⟩)
    rw [radialMapAll_of_ne f t₀ y hy0, hsph, hrad]
    show H i j (f ⟨(y : V), mem_sphere_zero_iff_norm.mpr hy⟩, (0 : unitInterval)) =
      g i j (f ⟨(y : V), mem_sphere_zero_iff_norm.mpr hy⟩)
    simp only [g, Matrix.map_apply, sliceAt, pullAlg]
    rfl
  have hmem' : ∀ (i j : Fin (n + k)) (y : Ball V) (hy : ‖(y : V)‖ = 1),
      (N' i j) y = (g' i j) (f ⟨(y : V), mem_sphere_zero_iff_norm.mpr hy⟩) := by
    intro i j y hy
    have hy0 : (y : V) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hy; exact one_ne_zero hy.symm
    have hsphv : (sphProj y hy0 : V) = (y : V) := by
      rw [sphProj_coe, hy, inv_one, one_smul]
    have hsph : sphProj y hy0 = ⟨(y : V), mem_sphere_zero_iff_norm.mpr hy⟩ :=
      Subtype.ext hsphv
    have hrad : radialCoord y = 0 := by
      apply Subtype.ext
      simp [hy]
    show H' i j (radialMapAll f t₀ y) = g' i j (f ⟨(y : V), mem_sphere_zero_iff_norm.mpr hy⟩)
    rw [radialMapAll_of_ne f t₀ y hy0, hsph, hrad]
    show H' i j (f ⟨(y : V), mem_sphere_zero_iff_norm.mpr hy⟩, (0 : unitInterval)) =
      g' i j (f ⟨(y : V), mem_sphere_zero_iff_norm.mpr hy⟩)
    simp only [g', Matrix.map_apply, sliceAt, pullAlg]
    rfl
  let v : Matrix (Fin (n + k)) (Fin (n + k)) (coneAlg f) := fun i j =>
    ⟨(g i j, N i j), hmem i j⟩
  let v' : Matrix (Fin (n + k)) (Fin (n + k)) (coneAlg f) := fun i j =>
    ⟨(g' i j, N' i j), hmem' i j⟩
  have hNN' : N * N' = 1 := by
    ext i j y
    have hpt : ∀ y : Ball V, (N * N').map (⇑(evalC y)) = 1 := by
      intro y
      set y' : T × unitInterval := radialMapAll f t₀ y with hy'
      have hN : N.map (⇑(evalC y)) = H.map (⇑(evalC y')) := by ext a b; rfl
      have hN' : N'.map (⇑(evalC y)) = H'.map (⇑(evalC y')) := by ext a b; rfl
      rw [Matrix.map_mul (f := evalC y), hN, hN', ← Matrix.map_mul (f := evalC y'),
        hH'1, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 := congrArg (fun M : Matrix (Fin (n + k)) (Fin (n + k)) ℂ => M i j) (hpt y)
    have h2' : ((N * N') i j) y = (if i = j then (1 : ℂ) else 0) := by
      simpa [Matrix.map_apply, Matrix.one_apply] using h2
    rw [h2', Matrix.one_apply]
    by_cases hij : i = j <;>
      simp [hij, ContinuousMap.one_apply, ContinuousMap.zero_apply]
  have hN'N : N' * N = 1 := by
    ext i j y
    have hpt : ∀ y : Ball V, (N' * N).map (⇑(evalC y)) = 1 := by
      intro y
      set y' : T × unitInterval := radialMapAll f t₀ y with hy'
      have hN : N.map (⇑(evalC y)) = H.map (⇑(evalC y')) := by ext a b; rfl
      have hN' : N'.map (⇑(evalC y)) = H'.map (⇑(evalC y')) := by ext a b; rfl
      rw [Matrix.map_mul (f := evalC y), hN', hN, ← Matrix.map_mul (f := evalC y'),
        hH'2, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 := congrArg (fun M : Matrix (Fin (n + k)) (Fin (n + k)) ℂ => M i j) (hpt y)
    have h2' : ((N' * N) i j) y = (if i = j then (1 : ℂ) else 0) := by
      simpa [Matrix.map_apply, Matrix.one_apply] using h2
    rw [h2', Matrix.one_apply]
    by_cases hij : i = j <;>
      simp [hij, ContinuousMap.one_apply, ContinuousMap.zero_apply]
  let X : Matrix (Fin (n + k)) (Fin (n + k)) (C(T, ℂ) × C(Ball V, ℂ)) := fun i j => (g i j, N i j)
  let Y : Matrix (Fin (n + k)) (Fin (n + k)) (C(T, ℂ) × C(Ball V, ℂ)) := fun i j => (g' i j, N' i j)
  have hXmap : X.map (Prod.fst : C(T, ℂ) × C(Ball V, ℂ) → C(T, ℂ)) = g := rfl
  have hYmap : Y.map (Prod.fst : C(T, ℂ) × C(Ball V, ℂ) → C(T, ℂ)) = g' := rfl
  have hXmap2 : X.map (Prod.snd : C(T, ℂ) × C(Ball V, ℂ) → C(Ball V, ℂ)) = N := rfl
  have hYmap2 : Y.map (Prod.snd : C(T, ℂ) × C(Ball V, ℂ) → C(Ball V, ℂ)) = N' := rfl
  have hXY : X * Y = 1 := by
    apply mulProd_eq_one
    · rw [hXmap, hYmap, hgg']
    · rw [hXmap2, hYmap2, hNN']
  have hYX : Y * X = 1 := by
    apply mulProd_eq_one
    · rw [hYmap, hXmap, hg'g]
    · rw [hYmap2, hXmap2, hN'N]
  have hinj : Function.Injective
      (fun M : Matrix (Fin (n + k)) (Fin (n + k)) (coneAlg f) => M.map (⇑(coneAlg f).val)) := by
    have hval : (⇑(coneAlg f).val : coneAlg f → C(T, ℂ) × C(Ball V, ℂ)) = Subtype.val :=
      Subalgebra.coe_val _
    rw [hval]
    exact Matrix.map_injective Subtype.val_injective
  have hvv' : v * v' = 1 := by
    refine hinj ?_
    show (v * v').map (⇑(coneAlg f).val) =
      (1 : Matrix (Fin (n + k)) (Fin (n + k)) (coneAlg f)).map (⇑(coneAlg f).val)
    rw [Matrix.map_mul (f := (coneAlg f).val), Matrix.map_one _ (map_zero _) (map_one _)]
    change X * Y = 1
    exact hXY
  have hv'v : v' * v = 1 := by
    refine hinj ?_
    show (v' * v).map (⇑(coneAlg f).val) =
      (1 : Matrix (Fin (n + k)) (Fin (n + k)) (coneAlg f)).map (⇑(coneAlg f).val)
    rw [Matrix.map_mul (f := (coneAlg f).val), Matrix.map_one _ (map_zero _) (map_one _)]
    change Y * X = 1
    exact hYX
  refine ⟨k, v, ⟨Units.mk v v' hvv' hv'v, rfl⟩, ?_⟩
  have hproj : v.map (coneToT f) = g := rfl
  rw [hproj]
  exact hH0

end

end Work.KT.Cone

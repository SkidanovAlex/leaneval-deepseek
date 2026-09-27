import Mathlib
import Submission.Work.KT.HopfK.Interface
import Submission.Work.KT.HopfK.Disk

namespace Work.KT.HopfK

/-- On the boundary sphere of the ball, the cell evaluation `evalD` coincides with the base
evaluation `evalT` at the image point under the attaching map: both amount to the relation
`g ∘ f = h` defining the mapping cone. -/
private lemma evalD_eq_evalT_of_norm_eq_one (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (w : Ball (Eu m × Eu m)) (hw : ‖(w : Eu m × Eu m)‖ = 1) :
    evalD m f w = evalT m f (f ⟨(w : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hw⟩) := by
  ext x
  have hx := x.2 w hw
  show (x : C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ)).2 w = _
  rw [show (evalT m f (f ⟨(w : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hw⟩)) x
      = ((x : C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ)).1)
        (f ⟨(w : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hw⟩) from rfl]
  exact hx

/-- The diagonal idempotent `diag(1_r, 0)` is preserved by entrywise image under a ring map. -/
private lemma diagMat_map {R S : Type} [Ring R] [Ring S] (φ : R →+* S) (r n : ℕ) :
    (diagMat R r n).map φ = diagMat S r n := by
  unfold diagMat Mat.map
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
  ext i j
  simp only [Matrix.map_apply, Matrix.diagonal_apply]
  by_cases h : i = j <;> simp [h]

theorem hk_sliceSnd (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m))) (n r : ℕ)
    (e₀ : Sph (Eu m)) (y0E : Ball (Eu m)) (hy0E : y0E ∈ bdry (Eu m))
    (p : Matrix (Fin n) (Fin n) (coneAlg (hopfKMap m μ))) (hp : p * p = p)
    (hpb : ∀ t : Tgt m, t ∈ capTplus m → p.map (evalT m (hopfKMap m μ) t) = diagIdemMat r n) :
    ∃ u : Matrix (Fin n) (Fin n) (Kpair (Eu m)),
      Mat.IsIdem (⟨n, u⟩ : Mat (Kpair (Eu m))) ∧
      (∀ i j, (u i j : C(Ball (Eu m), ℂ))
        = ⟨fun y : Ball (Eu m) => coneCell (hopfKMap m μ) p i j (ptSnd m e₀ y),
           (coneCell (hopfKMap m μ) p i j).continuous.comp (continuous_ptSnd m e₀)⟩) ∧
      (coneCell (hopfKMap m μ) p).map (pullAlg (shiftSnd m e₀ 1)).toRingHom
        = (fun i j => ((pullSnd (Eu m) (Eu m) (u i j) : prodAlg (Eu m) (Eu m)) :
            C(Ball (Eu m × Eu m), ℂ))) ∧
      K0.mapA (augPair (Eu m) y0E)
        (cls (⟨n, u⟩ : Mat (Kpair (Eu m))) - cls (diagMat (Kpair (Eu m)) r n)) = 0 := by
  have hcell : coneCell (hopfKMap m μ) p * coneCell (hopfKMap m μ) p
      = coneCell (hopfKMap m μ) p := by
    rw [← coneCell_mul (hopfKMap m μ) p p, hp]
  -- On the boundary sphere of `Ball (Eu m)` the slice agrees with the constant `diag(1_r,0)`:
  -- the point `(e₀, y)` lies on the boundary sphere of `Ball (Eu m × Eu m)`, where the cell part
  -- of an element of the mapping cone is its base part at the image under the attaching map, and
  -- that image has height `0`, hence lies in the upper cap `capTplus`.
  have hbdry : ∀ (i j : Fin n) (y : Ball (Eu m)), y ∈ bdry (Eu m) →
      coneCell (hopfKMap m μ) p i j (ptSnd m e₀ y) = diagIdemMat r n i j := by
    intro i j y hy
    have he0 : ‖(e₀ : Eu m)‖ = 1 := by
      have h := Metric.mem_sphere.mp e₀.2
      rwa [dist_eq_norm, sub_zero] at h
    have hz : ‖((ptSnd m e₀ y : Ball (Eu m × Eu m)) : Eu m × Eu m)‖ = 1 := by
      rw [show ((ptSnd m e₀ y : Ball (Eu m × Eu m)) : Eu m × Eu m) = ((e₀ : Eu m), (y : Eu m))
        from rfl, Prod.norm_def, he0, hy, max_self]
    have hxs : ‖(⟨(ptSnd m e₀ y : Eu m × Eu m),
        mem_sphere_zero_iff_norm.mpr hz⟩ : Sph (Eu m × Eu m)).1.1‖ = 1 := he0
    have hys : ‖(⟨(ptSnd m e₀ y : Eu m × Eu m),
        mem_sphere_zero_iff_norm.mpr hz⟩ : Sph (Eu m × Eu m)).1.2‖ = 1 := hy
    have hcap : hopfKMap m μ ⟨(ptSnd m e₀ y : Eu m × Eu m),
        mem_sphere_zero_iff_norm.mpr hz⟩ ∈ capTplus m := by
      show tgtHeight m (hopfKMap m μ _) ≥ -(1 / 2)
      rw [tgtHeight_eq_of_norm_fst_eq_one m μ _ hxs, hys, one_pow, sub_self, Real.sqrt_zero,
        neg_zero]
      norm_num
    have h3 : p.map (evalT m (hopfKMap m μ)
        (hopfKMap m μ ⟨(ptSnd m e₀ y : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩))
        = diagIdemMat r n := hpb _ hcap
    have h1 : coneCell (hopfKMap m μ) p i j (ptSnd m e₀ y)
        = evalD m (hopfKMap m μ) (ptSnd m e₀ y) (p i j) := rfl
    rw [h1, evalD_eq_evalT_of_norm_eq_one m (hopfKMap m μ) (ptSnd m e₀ y) hz]
    have := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) h3
    simp only [Matrix.map_apply] at this
    exact this
  -- hence each slice entry lies in `Kpair (Eu m)`.
  have hmem : ∀ i j : Fin n,
      (⟨fun y : Ball (Eu m) => coneCell (hopfKMap m μ) p i j (ptSnd m e₀ y),
        (coneCell (hopfKMap m μ) p i j).continuous.comp (continuous_ptSnd m e₀)⟩ :
          C(Ball (Eu m), ℂ)) ∈ Kpair (Eu m) := by
    intro i j a ha a' ha'
    show coneCell (hopfKMap m μ) p i j (ptSnd m e₀ a)
      = coneCell (hopfKMap m μ) p i j (ptSnd m e₀ a')
    rw [hbdry i j a ha, hbdry i j a' ha']
  let u : Matrix (Fin n) (Fin n) (Kpair (Eu m)) :=
    sliceSnd m n e₀ (coneCell (hopfKMap m μ) p) hmem
  have hslice : ∀ i j, (u i j : C(Ball (Eu m), ℂ))
        = ⟨fun y : Ball (Eu m) => coneCell (hopfKMap m μ) p i j (ptSnd m e₀ y),
           (coneCell (hopfKMap m μ) p i j).continuous.comp (continuous_ptSnd m e₀)⟩ :=
    fun i j => rfl
  -- idempotence: the slice of the idempotent `coneCell p` is idempotent.
  have hidem : Mat.IsIdem (⟨n, u⟩ : Mat (Kpair (Eu m))) := by
    show u * u = u
    let φ : Kpair (Eu m) →+* C(Ball (Eu m), ℂ) := (Kpair (Eu m)).val.toRingHom
    have hφinj : Function.Injective φ := fun a b hab => Subtype.ext hab
    have hV : u.map φ
        = (coneCell (hopfKMap m μ) p).map
            (pullAlg ⟨ptSnd m e₀, continuous_ptSnd m e₀⟩).toRingHom := by
      ext i j
      rfl
    have hVmul : u.map φ * u.map φ = u.map φ := by
      rw [hV, ← Matrix.map_mul, hcell]
    have hfin : (u * u).map φ = u.map φ := by
      rw [Matrix.map_mul, hVmul]
    exact Matrix.map_injective hφinj hfin
  refine ⟨u, hidem, hslice, ?_, ?_⟩
  · -- the slice relation `p^cell ∘ shiftSnd = pullSnd u`.
    ext i j z
    have hsh : (shiftSnd m e₀ (1 : unitInterval)) z
        = ptSnd m e₀ (prSnd (Eu m) (Eu m) z) := by
      apply Subtype.ext
      show (((1 - ((1 : unitInterval) : ℝ)) • (z : Eu m × Eu m).1
            + ((1 : unitInterval) : ℝ) • (e₀ : Eu m), (z : Eu m × Eu m).2) : Eu m × Eu m)
          = ((e₀ : Eu m), ((prSnd (Eu m) (Eu m) z : Ball (Eu m)) : Eu m))
      rw [show ((1 : unitInterval) : ℝ) = 1 from rfl]
      simp only [sub_self, zero_smul, zero_add, one_smul]
      rfl
    rw [show ((coneCell (hopfKMap m μ) p).map (pullAlg (shiftSnd m e₀ 1)).toRingHom) i j z
        = coneCell (hopfKMap m μ) p i j ((shiftSnd m e₀ (1 : unitInterval)) z) from rfl]
    rw [show (((pullSnd (Eu m) (Eu m) (u i j) : prodAlg (Eu m) (Eu m))
          : C(Ball (Eu m × Eu m), ℂ)) z)
        = (u i j : C(Ball (Eu m), ℂ)) (prSnd (Eu m) (Eu m) z) from rfl]
    rw [hslice i j, hsh]
    rfl
  · -- reducedness of the slice class at the boundary point `y0E`.
    let φ : Kpair (Eu m) →+* ℂ := (augPair (Eu m) y0E).toRingHom
    have hφapply : ∀ g : Kpair (Eu m), φ g = (g : C(Ball (Eu m), ℂ)) y0E := fun g => rfl
    have humap : u.map φ = diagIdemMat r n := by
      ext i j
      rw [Matrix.map_apply, hφapply]
      exact hbdry i j y0E hy0E
    have e1 : Mat.map φ (⟨n, u⟩ : Mat (Kpair (Eu m))) = ⟨n, u.map φ⟩ := rfl
    have e2 : Mat.map φ (diagMat (Kpair (Eu m)) r n) = diagMat ℂ r n := diagMat_map φ r n
    show K0.map φ (cls (⟨n, u⟩ : Mat (Kpair (Eu m)))
        - cls (diagMat (Kpair (Eu m)) r n)) = 0
    rw [map_sub, K0.map_cls φ hidem, K0.map_cls φ (diagMat_isIdem (Kpair (Eu m)) r n)]
    rw [e1, e2, humap, sub_eq_zero]
    rfl

end Work.KT.HopfK

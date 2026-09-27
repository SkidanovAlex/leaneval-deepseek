import Mathlib
import Submission.Work.Surf.defs
import Submission.Work.Surf.rayMeetFaceAux
import Submission.Work.Surf.zeroSet_persist_one_dim

namespace Work.Surf

open Set Filter

open scoped Topology

open Work.Surf.RayMeetAux

namespace RmpAux

/-- `faceOf i 0` is a corner of the square. -/
lemma faceOf_zero_corner (i : Fin 4) :
    (((faceOf i 0 : EuclideanSpace ℝ (Fin 2)) 0 = 0 ∨ (faceOf i 0) 0 = 1) ∧
      ((faceOf i 0) 1 = 0 ∨ (faceOf i 0) 1 = 1)) := by
  fin_cases i <;> simp [faceOf, faceBot, faceTop, faceLft, faceRgt, e0, e1]

/-- `faceOf i 1` is a corner of the square. -/
lemma faceOf_one_corner (i : Fin 4) :
    (((faceOf i 1 : EuclideanSpace ℝ (Fin 2)) 0 = 0 ∨ (faceOf i 1) 0 = 1) ∧
      ((faceOf i 1) 1 = 0 ∨ (faceOf i 1) 1 = 1)) := by
  fin_cases i <;> simp [faceOf, faceBot, faceTop, faceLft, faceRgt, e0, e1]

/-- The parametrisation of a face of the square is `C¹`. -/
lemma contDiff_faceOf (i : Fin 4) : ContDiff ℝ 1 (faceOf i) := by
  have h0 : ContDiff ℝ 1 (faceBot : ℝ → EuclideanSpace ℝ (Fin 2)) := by
    unfold faceBot; fun_prop
  have h1 : ContDiff ℝ 1 (faceTop : ℝ → EuclideanSpace ℝ (Fin 2)) := by
    unfold faceTop; fun_prop
  have h2 : ContDiff ℝ 1 (faceLft : ℝ → EuclideanSpace ℝ (Fin 2)) := by
    unfold faceLft; fun_prop
  have h3 : ContDiff ℝ 1 (faceRgt : ℝ → EuclideanSpace ℝ (Fin 2)) := by
    unfold faceRgt; fun_prop
  fin_cases i
  · show ContDiff ℝ 1 faceBot; exact h0
  · show ContDiff ℝ 1 faceTop; exact h1
  · show ContDiff ℝ 1 faceLft; exact h2
  · show ContDiff ℝ 1 faceRgt; exact h3

/-- The determinant is additive in its first argument. -/
lemma det2_sub_left (u w v : EuclideanSpace ℝ (Fin 2)) :
    Work.Drive.det2 (u - w) v = Work.Drive.det2 u v - Work.Drive.det2 w v := by
  simp only [Work.Drive.det2, PiLp.sub_apply]; ring

/-- The determinant is bounded by an absolute constant times the norm of its first argument. -/
lemma abs_det2_le_C (u v : EuclideanSpace ℝ (Fin 2)) :
    |Work.Drive.det2 u v| ≤ (|v 0| + |v 1| + ‖v‖ + 1) * ‖u‖ := by
  refine (abs_det2_le u v).trans ?_
  have h1 : (|v 0| + |v 1|) ≤ |v 0| + |v 1| + ‖v‖ + 1 := by linarith [norm_nonneg v]
  exact mul_le_mul_of_nonneg_right h1 (norm_nonneg u)

lemma abs_det2_sub_le_C (u w v : EuclideanSpace ℝ (Fin 2)) :
    |Work.Drive.det2 u v - Work.Drive.det2 w v| ≤ (|v 0| + |v 1| + ‖v‖ + 1) * ‖u - w‖ := by
  rw [← det2_sub_left]
  exact abs_det2_le_C _ _

/-- The inner product with a fixed vector is Lipschitz with the same constant. -/
lemma abs_inner_sub_le_C (u w v : EuclideanSpace ℝ (Fin 2)) :
    |inner ℝ u v - inner ℝ w v| ≤ (|v 0| + |v 1| + ‖v‖ + 1) * ‖u - w‖ := by
  rw [← inner_sub_left]
  refine (abs_real_inner_le_norm (u - w) v).trans ?_
  have h1 : ‖v‖ ≤ |v 0| + |v 1| + ‖v‖ + 1 := by linarith [abs_nonneg (v 0), abs_nonneg (v 1)]
  calc ‖u - w‖ * ‖v‖ ≤ ‖u - w‖ * (|v 0| + |v 1| + ‖v‖ + 1) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = (|v 0| + |v 1| + ‖v‖ + 1) * ‖u - w‖ := by ring

/-- On a face the direction of the parametrisation has norm one. -/
lemma norm_faceDir (i : Fin 4) : ‖faceDir i‖ = 1 := by
  fin_cases i <;> simp [faceDir, norm_e0, norm_e1]

end RmpAux

/-- **Persistence of the number of boundary ray-meeting points under a small `C¹` perturbation.**
Let `F : 𝔼² → 𝔼²` be `C¹`, nonzero on the boundary of the unit square, and let `v ≠ 0` be such that
`‖F x‖ < ‖v‖` on the boundary, the boundary ray-meeting set `rayMeet F v ∩ sqBdry` is finite, avoids
the corners, and is *transverse*: at each of its points the derivative of `F` along the containing
face is not parallel to `v`.  Then there is `δ > 0` such that every `C¹` map `G` with
`‖G x - F x‖ < δ` **and** `‖fderiv ℝ G x - fderiv ℝ F x‖ < δ` on the square has a *finite* boundary
ray-meeting set with the same number of points:

`(rayMeet G v ∩ sqBdry).Finite ∧ (rayMeet G v ∩ sqBdry).ncard = (rayMeet F v ∩ sqBdry).ncard`.

This is the "boundary ray-meetings" half of `Work.Surf.smooth_reduction`.

Proof.  Write `∂□` as the union of its four closed edges (compact intervals), and on each edge let
`ψ x = det2 (F x, v)` and `φ x = ⟪F x, v⟫`; the ray-meeting set of `F` is contained in
`{ψ = 0, φ > 0}`, and the whole zero set of `ψ` on `sqBdry` splits into `{φ > 0}` (the ray-meetings)
and `{φ ≤ 0}` (the "anti-ray" zeros, possibly infinitely many).  Two compactness facts:

* the ray-meeting points are finitely many (`hfin`) and at each of them `φ > 0`, so
  `φ ≥ m₁ > 0` on the (finite) ray-meeting set; also, by `htrans_bdry`, the derivative of `ψ` along
  the containing edge is non-zero there, with a uniform positive lower bound `m₂ > 0` on the finite
  set (the finitely many ray-meeting points lie in the interiors of edges by `hcorner`);
* on the *closed* set `Z = {x ∈ sqBdry | ψ x = 0 ∧ φ x ≤ 0}` we have `φ < 0` everywhere (a point with
  `φ = 0` would be a zero of `F` on the boundary, excluded by `hbdry`), so by compactness
  `φ ≤ -m₃ < 0` on `Z`.

Take `δ` smaller than a suitable fraction of `min (m₁, m₂, m₃, ‖v‖)` divided by `‖v‖` and by the
norms of the projection maps.  Then for `G` with `‖G - F‖ < δ`, `‖fderiv ℝ G - fderiv ℝ F‖ < δ`:

* near each ray-meeting point the function `ψ_G x = det2 (G x, v)` is still transverse (its edge
  derivative is within `δ‖v‖` of the non-zero derivative of `ψ`, whose modulus is `≥ m₂`), so `ψ_G`
  has exactly one zero near it, and there `φ_G > 0` (since `φ ≥ m₁` at the old point and the
  perturbation is `≤ δ‖v‖`), so it is a ray-meeting point of `G`;
* on the part of the edge away from the old ray-meeting points (which is a finite union of compact
  intervals) either `|ψ| ≥ m₄ > 0` (so `ψ_G ≠ 0` there for small `δ`), or the point lies near `Z`,
  where `φ ≤ -m₃ < 0` and hence `φ_G < 0`, so the zeros of `ψ_G` that may appear there (possibly a
  splitting of a non-transversal zero of `ψ`) are *not* ray-meeting points of `G`.

Hence the ray-meeting points of `G` are in bijection with those of `F`, giving the equality of
cardinalities and the finiteness of the ray-meeting set of `G`. -/
theorem ncard_rayMeet_persist
    (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hF : ContDiff ℝ 1 F)
    (hbdry : ∀ x ∈ Work.Surf.sqBdry, F x ≠ 0)
    {v : EuclideanSpace ℝ (Fin 2)} (hv : v ≠ 0)
    (hbig : ∀ x ∈ Work.Surf.sqBdry, ‖F x‖ < ‖v‖)
    (hcorner : ∀ x ∈ Work.Surf.sqBdry, (∃ r : ℝ, 0 < r ∧ F x = r • v) →
      ¬ ((x 0 = 0 ∨ x 0 = 1) ∧ (x 1 = 0 ∨ x 1 = 1)))
    (htrans_bdry : ∀ x ∈ Work.Surf.sqBdry, (∃ r : ℝ, 0 < r ∧ F x = r • v) →
      ((x 1 = 0 ∨ x 1 = 1) →
        Work.Drive.det2 (fderiv ℝ F x (EuclideanSpace.single 0 1)) v ≠ 0) ∧
      ((x 0 = 0 ∨ x 0 = 1) →
        Work.Drive.det2 (fderiv ℝ F x (EuclideanSpace.single 1 1)) v ≠ 0))
    (hfin : (Work.Surf.rayMeet F v ∩ Work.Surf.sqBdry).Finite) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      ContDiff ℝ 1 G → (∀ x ∈ Work.Surf.sqBox, ‖G x - F x‖ < δ) →
      (∀ x ∈ Work.Surf.sqBox, ‖fderiv ℝ G x - fderiv ℝ F x‖ < δ) →
      (Work.Surf.rayMeet G v ∩ Work.Surf.sqBdry : Set (EuclideanSpace ℝ (Fin 2))).Finite ∧
        (Work.Surf.rayMeet G v ∩ Work.Surf.sqBdry : Set (EuclideanSpace ℝ (Fin 2))).ncard =
          (Work.Surf.rayMeet F v ∩ Work.Surf.sqBdry : Set (EuclideanSpace ℝ (Fin 2))).ncard := by
  classical
  set c : ℝ := |v 0| + |v 1| + ‖v‖ + 1 with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    have h1 := abs_nonneg (v 0)
    have h2 := abs_nonneg (v 1)
    have h3 := norm_nonneg v
    linarith
  -- Step 1: the boundary ray-meeting points of `F` on each face.
  have hFfin : ∀ i : Fin 4, (faceRaySet F v i).Finite := by
    intro i
    refine Set.Finite.of_finite_image ?_ (faceOf_injective i).injOn
    exact hfin.subset (faceOf_image_faceRaySet_subset hv i)
  have hFvar : ∀ i : Fin 4, faceRaySet F v i ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro i t ht
    obtain ⟨htIcc, hgt, hht⟩ := ht
    have hx : faceOf i t ∈ sqBdry := faceOf_mem_sqBdry i t htIcc
    have hray : ∃ r : ℝ, 0 < r ∧ F (faceOf i t) = r • v := (isPosRay_iff hv).mp ⟨hgt, hht⟩
    have hn0 : t ≠ 0 := by
      intro h0
      exact hcorner (faceOf i t) hx hray (by rw [h0]; exact RmpAux.faceOf_zero_corner i)
    have hn1 : t ≠ 1 := by
      intro h1
      exact hcorner (faceOf i t) hx hray (by rw [h1]; exact RmpAux.faceOf_one_corner i)
    exact ⟨lt_of_le_of_ne htIcc.1 (Ne.symm hn0), lt_of_le_of_ne htIcc.2 hn1⟩
  -- Step 2: the "anti-ray" boundary zeros of `F` keep a strictly negative `⟨·,v⟩`.
  obtain ⟨m₃, hm₃pos, hm₃⟩ : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ sqBdry,
      Work.Drive.det2 (F x) v = 0 → inner ℝ (F x) v ≤ 0 → inner ℝ (F x) v ≤ -m := by
    set Z : Set (EuclideanSpace ℝ (Fin 2)) :=
      {x | x ∈ sqBdry ∧ Work.Drive.det2 (F x) v = 0 ∧ inner ℝ (F x) v ≤ 0} with hZdef
    have hZclosed : IsClosed Z := by
      have h1 : IsClosed {x : EuclideanSpace ℝ (Fin 2) | Work.Drive.det2 (F x) v = 0} :=
        isClosed_eq (by simp only [Work.Drive.det2]; fun_prop) continuous_const
      have h2 : IsClosed {x : EuclideanSpace ℝ (Fin 2) | inner ℝ (F x) v ≤ 0} :=
        isClosed_le (continuous_inner.comp (hF.continuous.prodMk continuous_const)) continuous_const
      rw [hZdef]
      convert (isCompact_sqBdry.isClosed.inter h1).inter h2 using 1
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
      tauto
    have hZcompact : IsCompact Z :=
      IsCompact.of_isClosed_subset isCompact_sqBdry hZclosed (fun x hx => hx.1)
    rcases Z.eq_empty_or_nonempty with hem | hne
    · refine ⟨1, one_pos, fun x hx h1 h2 => ?_⟩
      have hmem : x ∈ Z := ⟨hx, h1, h2⟩
      rw [hem] at hmem
      exact absurd hmem (by simp)
    · have hpos : ∀ x ∈ Z, 0 < -inner ℝ (F x) v := by
        rintro x ⟨hxs, hxψ, hxφ⟩
        rw [neg_pos]
        rcases lt_or_eq_of_le hxφ with hlt | heq
        · exact hlt
        · exfalso
          obtain ⟨cc, hcc⟩ := exists_smul_of_det2_eq_zero hv hxψ
          have h1 : inner ℝ (F x) v = cc * inner ℝ v v := by rw [hcc, inner_smul_left]; simp
          have h2 : inner ℝ v v ≠ 0 := ne_of_gt (real_inner_self_pos.mpr hv)
          have hcc0 : cc = 0 := by
            rcases mul_eq_zero.mp (by rw [← h1]; exact heq) with h | h
            · exact h
            · exact absurd h h2
          exact hbdry x hxs (by rw [hcc, hcc0, zero_smul])
      obtain ⟨m, hmpos, hm⟩ := exists_pos_le_of_isCompact_of_pos
        (f := fun x : EuclideanSpace ℝ (Fin 2) => -inner ℝ (F x) v) (by fun_prop) hZcompact hpos
      exact ⟨m, hmpos, fun x hx h1 h2 => by have := hm x ⟨hx, h1, h2⟩; linarith⟩
  -- Step 3: the one-dimensional persistence lemma on each face.
  have hFace : ∀ i : Fin 4, ∃ d : ℝ, 0 < d ∧
      ∀ G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2), ContDiff ℝ 1 G →
        (∀ x ∈ sqBox, ‖G x - F x‖ < d) →
        (∀ x ∈ sqBox, ‖fderiv ℝ G x - fderiv ℝ F x‖ < d) →
        (faceRaySet G v i).Finite ∧ (faceRaySet G v i).ncard = (faceRaySet F v i).ncard ∧
          (faceRaySet G v i) ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro i
    have htrans_i : ∀ t ∈ Set.Icc (0 : ℝ) 1, Work.Drive.det2 (F (faceOf i t)) v = 0 →
        0 < inner ℝ (F (faceOf i t)) v →
        deriv (fun s => Work.Drive.det2 (F (faceOf i s)) v) t ≠ 0 := by
      intro t ht hgt hht
      have htint : t ∈ Set.Ioo (0 : ℝ) 1 := hFvar i ⟨ht, hgt, hht⟩
      have hx : faceOf i t ∈ sqBdry := faceOf_mem_sqBdry i t ht
      have hray : ∃ r : ℝ, 0 < r ∧ F (faceOf i t) = r • v := (isPosRay_iff hv).mp ⟨hgt, hht⟩
      obtain ⟨hb1, hb2⟩ := htrans_bdry (faceOf i t) hx hray
      rw [deriv_det2_faceOf F hF v i t]
      by_cases h1 : (faceOf i t) 1 = 0 ∨ (faceOf i t) 1 = 1
      · rw [faceDir_eq_e0_of_coord_one htint h1, e0]
        exact hb1 h1
      · push Not at h1
        have hx0 : (faceOf i t) 0 = 0 ∨ (faceOf i t) 0 = 1 := by
          rcases hx.2 with h | h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd h h1.1
          · exact absurd h h1.2
        rw [faceDir_eq_e1_of_coord_zero htint hx0, e1]
        exact hb2 hx0
    have hanti_i : ∃ m : ℝ, 0 < m ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Work.Drive.det2 (F (faceOf i t)) v = 0 → inner ℝ (F (faceOf i t)) v ≤ 0 →
        inner ℝ (F (faceOf i t)) v ≤ -m :=
      ⟨m₃, hm₃pos, fun t ht h1 h2 => hm₃ (faceOf i t) (faceOf_mem_sqBdry i t ht) h1 h2⟩
    have hgF : ContDiff ℝ 1 (fun t : ℝ => Work.Drive.det2 (F (faceOf i t)) v) := by
      have h1 : ContDiff ℝ 1 (fun t : ℝ => det2CLM v (F (faceOf i t))) :=
        (det2CLM v).contDiff.comp (hF.comp (RmpAux.contDiff_faceOf i))
      simpa only [det2CLM_apply] using h1
    have hhF : Continuous (fun t : ℝ => inner ℝ (F (faceOf i t)) v) :=
      continuous_inner.comp ((hF.continuous.comp (continuous_faceOf i)).prodMk continuous_const)
    obtain ⟨δi, hδipos, hδi⟩ := zeroSet_persist_one_dim
      (g := fun t : ℝ => Work.Drive.det2 (F (faceOf i t)) v)
      (h := fun t : ℝ => inner ℝ (F (faceOf i t)) v) hgF hhF (hFfin i) (hFvar i) htrans_i hanti_i
    refine ⟨δi / c, by positivity, ?_⟩
    intro G hG hcl1 hcl2
    have hgG : ContDiff ℝ 1 (fun t : ℝ => Work.Drive.det2 (G (faceOf i t)) v) := by
      have h1 : ContDiff ℝ 1 (fun t : ℝ => det2CLM v (G (faceOf i t))) :=
        (det2CLM v).contDiff.comp (hG.comp (RmpAux.contDiff_faceOf i))
      simpa only [det2CLM_apply] using h1
    have hhG : Continuous (fun t : ℝ => inner ℝ (G (faceOf i t)) v) :=
      continuous_inner.comp ((hG.continuous.comp (continuous_faceOf i)).prodMk continuous_const)
    refine hδi _ _ hgG hhG ?_ ?_ ?_
    · intro t ht
      have hx : faceOf i t ∈ sqBox := (faceOf_mem_sqBox i t).mpr ht
      have h1 : ‖G (faceOf i t) - F (faceOf i t)‖ < δi / c := hcl1 _ hx
      calc |Work.Drive.det2 (G (faceOf i t)) v - Work.Drive.det2 (F (faceOf i t)) v|
          ≤ c * ‖G (faceOf i t) - F (faceOf i t)‖ := by
            rw [hcdef]; exact RmpAux.abs_det2_sub_le_C _ _ _
        _ ≤ c * (δi / c) := le_of_lt (mul_lt_mul_of_pos_left h1 hcpos)
        _ = δi := by field_simp
    · intro t ht
      have hx : faceOf i t ∈ sqBox := (faceOf_mem_sqBox i t).mpr ht
      have h1 : ‖fderiv ℝ G (faceOf i t) - fderiv ℝ F (faceOf i t)‖ < δi / c := hcl2 _ hx
      rw [deriv_det2_faceOf G hG v i t, deriv_det2_faceOf F hF v i t]
      have h2 : ‖(fderiv ℝ G (faceOf i t) - fderiv ℝ F (faceOf i t)) (faceDir i)‖
          ≤ ‖fderiv ℝ G (faceOf i t) - fderiv ℝ F (faceOf i t)‖ := by
        have h3 := ContinuousLinearMap.le_opNorm
          (fderiv ℝ G (faceOf i t) - fderiv ℝ F (faceOf i t)) (faceDir i)
        rwa [RmpAux.norm_faceDir, mul_one] at h3
      calc |Work.Drive.det2 ((fderiv ℝ G (faceOf i t)) (faceDir i)) v
            - Work.Drive.det2 ((fderiv ℝ F (faceOf i t)) (faceDir i)) v|
          = |Work.Drive.det2 ((fderiv ℝ G (faceOf i t) - fderiv ℝ F (faceOf i t))
              (faceDir i)) v| := by
            rw [ContinuousLinearMap.sub_apply, RmpAux.det2_sub_left]
        _ ≤ c * ‖(fderiv ℝ G (faceOf i t) - fderiv ℝ F (faceOf i t)) (faceDir i)‖ := by
            rw [hcdef]; exact RmpAux.abs_det2_le_C _ _
        _ ≤ c * ‖fderiv ℝ G (faceOf i t) - fderiv ℝ F (faceOf i t)‖ :=
            mul_le_mul_of_nonneg_left h2 hcpos.le
        _ ≤ c * (δi / c) := le_of_lt (mul_lt_mul_of_pos_left h1 hcpos)
        _ = δi := by field_simp
    · intro t ht
      have hx : faceOf i t ∈ sqBox := (faceOf_mem_sqBox i t).mpr ht
      have h1 : ‖G (faceOf i t) - F (faceOf i t)‖ < δi / c := hcl1 _ hx
      calc |inner ℝ (G (faceOf i t)) v - inner ℝ (F (faceOf i t)) v|
          ≤ c * ‖G (faceOf i t) - F (faceOf i t)‖ := by
            rw [hcdef]; exact RmpAux.abs_inner_sub_le_C _ _ _
        _ ≤ c * (δi / c) := le_of_lt (mul_lt_mul_of_pos_left h1 hcpos)
        _ = δi := by field_simp
  -- Step 4: a single `δ` works for all four faces.
  choose dfun hdfun using hFace
  set δ : ℝ := (Finset.univ : Finset (Fin 4)).inf' ⟨0, Finset.mem_univ 0⟩ dfun with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact (Finset.lt_inf'_iff (⟨0, Finset.mem_univ 0⟩ :
      (Finset.univ : Finset (Fin 4)).Nonempty)).mpr (fun i _ => (hdfun i).1)
  have hδle : ∀ i : Fin 4, δ ≤ dfun i := by
    intro i
    rw [hδdef]
    exact Finset.inf'_le dfun (Finset.mem_univ i)
  refine ⟨δ, hδpos, ?_⟩
  intro G hG hcl1 hcl2
  have hGface : ∀ i : Fin 4, (faceRaySet G v i).Finite ∧
      (faceRaySet G v i).ncard = (faceRaySet F v i).ncard ∧
      (faceRaySet G v i) ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro i
    exact (hdfun i).2 G hG (fun x hx => lt_of_lt_of_le (hcl1 x hx) (hδle i))
      (fun x hx => lt_of_lt_of_le (hcl2 x hx) (hδle i))
  have hGfin : ∀ i : Fin 4, (faceRaySet G v i).Finite := fun i => (hGface i).1
  have hGvar : ∀ i : Fin 4, faceRaySet G v i ⊆ Set.Ioo (0 : ℝ) 1 := fun i => (hGface i).2.2
  refine ⟨?_, ?_⟩
  · rw [rayMeet_inter_sqBdry_eq_iUnion hv]
    exact finite_iUnion fun i => (hGfin i).image (faceOf i)
  · rw [ncard_rayMeet_inter_sqBdry hv hGvar hGfin, ncard_rayMeet_inter_sqBdry hv hFvar hFfin]
    exact Finset.sum_congr rfl fun i _ => (hGface i).2.1


end Work.Surf

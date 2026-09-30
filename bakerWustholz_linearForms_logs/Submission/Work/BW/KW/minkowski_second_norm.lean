import Mathlib
import Submission.Work.BW.basisRed_defs
import Submission.Work.BW.Minkowski2.exists_minimizers_flag
import Submission.Work.BW.Minkowski2.exists_zbasis_adapted
import Submission.Work.BW.KWM.basic
import Submission.Work.BW.KWM.coord_defs
import Submission.Work.BW.KWM.coord
import Submission.Work.BW.KWM.coord_case

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Minkowski's second theorem for a lattice norm

`Work.BW.KW.minkowski_second_norm`: for a lattice norm `F` on `ℝⁿ` the product of the successive
minima of `F` with respect to `ℤⁿ` times the volume of the unit ball `{F ≤ 1}` is at most `2ⁿ`.
-/

namespace Work.BW.KW

open MeasureTheory
open scoped Pointwise
open scoped ENNReal

variable {n : ℕ}

/-- The successive minima are invariant under a linear equivalence preserving `ℤⁿ`. -/
theorem succMinL_comp_linearEquiv (F : (Fin n → ℝ) → ℝ) (j : ℕ)
    (e : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (hZ : ∀ x : Fin n → ℝ, (∃ t : Fin n → ℤ, x = fun i => (t i : ℝ)) ↔
      (∃ t : Fin n → ℤ, e x = fun i => (t i : ℝ))) :
    Work.BW.succMinL (fun x => F (e x)) j = Work.BW.succMinL F j := by
  have hset : ∀ t : ℝ, {x : Fin n → ℝ |
        (∃ v : Fin n → ℤ, x = fun i => (v i : ℝ)) ∧ F (e x) ≤ t}
      = e ⁻¹' {x : Fin n → ℝ | (∃ v : Fin n → ℤ, x = fun i => (v i : ℝ)) ∧ F x ≤ t} := by
    intro t
    ext x
    exact ⟨fun h => ⟨(hZ x).mp h.1, h.2⟩, fun h => ⟨(hZ x).mpr h.1, h.2⟩⟩
  rw [Work.BW.basisRed_succMinL_eq_sInf, Work.BW.basisRed_succMinL_eq_sInf]
  congr 1
  ext t
  rw [Work.BW.basisRed_succSetL, Work.BW.basisRed_succSetL, Set.mem_ofPred_eq, Set.mem_ofPred_eq,
    Work.BW.basisRed_succSpanL, Work.BW.basisRed_succSpanL]
  have hfr : Module.finrank ℝ (Submodule.span ℝ {x : Fin n → ℝ |
        (∃ v : Fin n → ℤ, x = fun i => (v i : ℝ)) ∧ F (e x) ≤ t})
      = Module.finrank ℝ (Submodule.span ℝ {x : Fin n → ℝ |
        (∃ v : Fin n → ℤ, x = fun i => (v i : ℝ)) ∧ F x ≤ t}) := by
    rw [hset t]
    have hmap : Submodule.map (e : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
        (Submodule.span ℝ (e ⁻¹' {x : Fin n → ℝ |
          (∃ v : Fin n → ℤ, x = fun i => (v i : ℝ)) ∧ F x ≤ t}))
        = Submodule.span ℝ {x : Fin n → ℝ |
          (∃ v : Fin n → ℤ, x = fun i => (v i : ℝ)) ∧ F x ≤ t} := by
      rw [Submodule.map_span]
      congr 1
      ext y
      constructor
      · rintro ⟨x, hx, hxy⟩
        rwa [← hxy]
      · intro hy
        exact ⟨e.symm y, by simpa using hy, e.apply_symm_apply y⟩
    rw [← hmap, LinearEquiv.finrank_map_eq e]
  rw [hfr]

/-- The Lebesgue measure is invariant under a determinant-one linear equivalence. -/
theorem volume_real_preimage_linearEquiv (e : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (hdet : |LinearMap.det (e : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))| = 1)
    (S : Set (Fin n → ℝ)) : volume.real (e ⁻¹' S) = volume.real S := by
  have himg : e ⁻¹' S = (e.symm : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) '' S := by
    ext x
    constructor
    · intro hx; exact ⟨e x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩; simpa using hy
  have hdet' : |LinearMap.det (e.symm : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))| = 1 := by
    have h2 : LinearMap.det (e.symm : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
        * LinearMap.det (e : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) = 1 := by
      have h1 := LinearMap.det_comp (e.symm : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
        (e : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
      rw [show (e.symm : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ∘ₗ
          (e : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) = LinearMap.id from by
        ext x; simp, LinearMap.det_id] at h1
      exact h1.symm
    have h3 : |LinearMap.det (e.symm : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))|
        * |LinearMap.det (e : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))| = 1 := by
      rw [← abs_mul, h2, abs_one]
    rw [hdet, mul_one] at h3
    exact h3
  rw [himg, MeasureTheory.Measure.real_def volume
      ((e.symm : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) '' S),
    MeasureTheory.Measure.real_def volume S,
    MeasureTheory.Measure.addHaar_image_linearMap volume
      (e.symm : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) S, hdet']
  simp

/-- **Minkowski's second theorem for a lattice norm.** -/
theorem minkowski_second_norm {n : ℕ} (F : (Fin n → ℝ) → ℝ) (hF : Work.BW.IsLatticeNorm F) :
    (∏ j : Fin n, Work.BW.succMinL F (j.1 + 1)) *
        MeasureTheory.volume.real {x : Fin n → ℝ | F x ≤ 1} ≤ (2 : ℝ) ^ n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h1 : (∏ j : Fin 0, Work.BW.succMinL F (j.1 + 1)) = 1 := by simp
    rw [h1, one_mul, show (2 : ℝ) ^ (0 : ℕ) = 1 by norm_num]
    have h3 : volume.real {x : Fin 0 → ℝ | F x ≤ 1}
        ≤ volume.real (Set.univ : Set (Fin 0 → ℝ)) :=
      MeasureTheory.measureReal_mono (Set.subset_univ _) (by
        rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_empty_univ]
        exact ENNReal.one_ne_top)
    have h4 : volume.real (Set.univ : Set (Fin 0 → ℝ)) = 1 := by
      rw [MeasureTheory.Measure.real_def volume (Set.univ : Set (Fin 0 → ℝ)),
        MeasureTheory.volume_pi, MeasureTheory.Measure.pi_empty_univ]
      simp
    rwa [h4] at h3
  · obtain ⟨z, hzind, hzval, hzflag⟩ := Work.BW.Minkowski2.exists_minimizers_flag (d := n) hF
    obtain ⟨b, hunit, hbflag⟩ := Work.BW.Minkowski2.exists_zbasis_adapted z hzind
    set Mi : Matrix (Fin n) (Fin n) ℤ := Matrix.of (fun i k => b k i) with hMi
    set M : Matrix (Fin n) (Fin n) ℝ := Mi.map (Int.castRingHom ℝ) with hM
    have hMdet : M.det = ((Mi.det : ℤ) : ℝ) := by
      rw [hM]
      exact (RingHom.map_det (Int.castRingHom ℝ) Mi).symm
    have hdetM : M.det ≠ 0 := by
      rw [hMdet]
      exact_mod_cast (IsUnit.ne_zero hunit)
    have hMinj : Function.Injective M.mulVecLin := by
      intro x y h
      exact Matrix.mulVec_injective_of_det_ne_zero hdetM
        (by simpa only [Matrix.mulVecLin_apply] using h)
    have hMsurj : Function.Surjective M.mulVecLin :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (show Module.finrank ℝ (Fin n → ℝ) = Module.finrank ℝ (Fin n → ℝ) from rfl)).mp hMinj
    have hbij : Function.Bijective M.mulVecLin :=
      ⟨hMinj, hMsurj⟩
    set e : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
      LinearEquiv.ofBijective M.mulVecLin hbij with he_def
    have he_apply : ∀ x : Fin n → ℝ, e x = M.mulVec x := by
      intro x
      rw [he_def, LinearEquiv.ofBijective_apply, Matrix.mulVecLin_apply]
    have hMz : ∀ t : Fin n → ℤ, M.mulVec (fun i => (t i : ℝ))
        = fun i => ((Mi.mulVec t) i : ℝ) := by
      intro t
      rw [hM]
      ext i
      simp only [Matrix.mulVec, Matrix.map_apply, dotProduct]
      push_cast
      rfl
    have hMe : ∀ k : Fin n, M.mulVec (Pi.single k (1 : ℝ)) = fun i => ((b k) i : ℝ) := by
      intro k
      rw [hM, hMi]
      ext i
      simp [Matrix.mulVec, Matrix.of_apply, Matrix.map_apply, dotProduct, Pi.single_apply]
    -- the lattice `ℤⁿ` is preserved by `e`
    have heZ : ∀ x : Fin n → ℝ, (∃ t : Fin n → ℤ, x = fun i => (t i : ℝ)) ↔
        (∃ t : Fin n → ℤ, e x = fun i => (t i : ℝ)) := by
      intro x
      obtain ⟨N, hN⟩ := ((Matrix.isUnit_iff_isUnit_det Mi).mpr hunit).exists_right_inv
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨Mi.mulVec t, by rw [he_apply, hMz]⟩
      · rintro ⟨t, ht⟩
        refine ⟨N.mulVec t, ?_⟩
        apply e.injective
        rw [ht, he_apply, hMz, Matrix.mulVec_mulVec, hN, Matrix.one_mulVec]
    have heq : ∀ j : ℕ, Work.BW.succMinL (fun x => F (e x)) j = Work.BW.succMinL F j :=
      fun j => succMinL_comp_linearEquiv F j e heZ
    -- the transferred norm
    have hF' : Work.BW.IsLatticeNorm (fun x => F (e x)) := by
      refine ⟨fun x => hF.nonneg _, ?_, ?_, ?_, ?_⟩
      · intro x
        rw [hF.eq_zero (e x)]
        exact ⟨fun h => e.injective (by rw [h, map_zero]),
          fun h => by rw [h, map_zero]⟩
      · intro t x
        rw [map_smul, hF.smul]
      · intro x y
        rw [map_add]
        exact hF.add_le _ _
      · intro t
        have hsetT : {v : Fin n → ℤ | (fun x => F (e x)) (fun i => (v i : ℝ)) ≤ t}
            = Mi.mulVec ⁻¹' {v : Fin n → ℤ | F (fun i => (v i : ℝ)) ≤ t} := by
          ext v
          simp only [Set.mem_ofPred_eq, Set.mem_preimage, he_apply, hMz]
        rw [hsetT]
        exact Set.Finite.preimage (Matrix.mulVec_injective_of_det_ne_zero
          (R := ℤ) (IsUnit.ne_zero hunit)).injOn (hF.finite t)
    -- the flag property in the standard coordinates
    have hspan_e : ∀ m : ℕ, m ≤ n →
        Submodule.span ℝ (Set.range (fun k : {k : Fin n // (k : ℕ) < m} =>
          (Pi.single (k : Fin n) (1 : ℝ) : Fin n → ℝ))) = Work.BW.KWM.cflag n m := by
      intro m hm
      refine le_antisymm ?_ ?_
      · rw [Submodule.span_le]
        rintro x ⟨k, rfl⟩
        change (Pi.single (k : Fin n) (1 : ℝ) : Fin n → ℝ) ∈ Work.BW.KWM.cflag n m
        refine (Work.BW.KWM.mem_cflag).mpr ?_
        intro j hj
        rw [Pi.single_eq_of_ne]
        intro hkjeq
        have hkj : (j : ℕ) = (k : ℕ) := by rw [← hkjeq]
        rw [hkj] at hj
        exact absurd hj (not_le.mpr k.2)
      · intro x hx
        have hx' : ∀ j : Fin n, m ≤ (j : ℕ) → x j = 0 := (Work.BW.KWM.mem_cflag).mp hx
        have hxsum : x = ∑ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < m),
            x k • (Pi.single k (1 : ℝ) : Fin n → ℝ) := by
          ext j
          rw [Finset.sum_apply]
          rw [Finset.sum_eq_single j]
          · simp [Pi.single_eq_same]
          · intro b _ hb
            rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
          · intro hj
            rw [Finset.mem_filter] at hj
            rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
            exact hx' j (not_lt.mp (fun h => hj ⟨Finset.mem_univ j, h⟩))
        rw [hxsum]
        exact Submodule.sum_mem _ (fun k hk => Submodule.smul_mem _ _
          (Submodule.subset_span ⟨⟨k, (Finset.mem_filter.mp hk).2⟩, rfl⟩))
    have hspan_bz : ∀ m : ℕ, m ≤ n →
        Submodule.span ℝ (Set.range (fun k : {k : Fin n // (k : ℕ) < m} =>
          fun i => ((b k) i : ℝ)))
        = Submodule.span ℝ (Set.range (fun k : {k : Fin n // (k : ℕ) < m} =>
          fun i => ((z k) i : ℝ))) := by
      intro m hm
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · subst h0
        have hempty : ∀ (w : Fin n → Fin n → ℤ),
            Submodule.span ℝ (Set.range (fun k : {k : Fin n // (k : ℕ) < 0} =>
              fun i => ((w k) i : ℝ))) = ⊥ := by
          intro w
          rw [Submodule.span_eq_bot]
          rintro y ⟨k, rfl⟩
          exact absurd k.2 (by omega)
        rw [hempty b, hempty z]
      · have hsetb : {x : Fin n → ℝ | ∃ k : Fin n, (k : ℕ) < m ∧ x = fun i => ((b k) i : ℝ)}
            = {x : Fin n → ℝ | ∃ k : Fin n, k.1 ≤ m - 1 ∧ x = fun i => ((b k) i : ℝ)} := by
          ext x; constructor <;> rintro ⟨k, hk, rfl⟩ <;> exact ⟨k, by omega, rfl⟩
        have hsetz : {x : Fin n → ℝ | ∃ k : Fin n, (k : ℕ) < m ∧ x = fun i => ((z k) i : ℝ)}
            = {x : Fin n → ℝ | ∃ k : Fin n, k.1 ≤ m - 1 ∧ x = fun i => ((z k) i : ℝ)} := by
          ext x; constructor <;> rintro ⟨k, hk, rfl⟩ <;> exact ⟨k, by omega, rfl⟩
        have hrb : Set.range (fun k : {k : Fin n // (k : ℕ) < m} => fun i => ((b k) i : ℝ))
            = {x : Fin n → ℝ | ∃ k : Fin n, (k : ℕ) < m ∧ x = fun i => ((b k) i : ℝ)} := by
          ext x; constructor
          · rintro ⟨k, rfl⟩; exact ⟨k.1, k.2, rfl⟩
          · rintro ⟨k, hk, rfl⟩; exact ⟨⟨k, hk⟩, rfl⟩
        have hrz : Set.range (fun k : {k : Fin n // (k : ℕ) < m} => fun i => ((z k) i : ℝ))
            = {x : Fin n → ℝ | ∃ k : Fin n, (k : ℕ) < m ∧ x = fun i => ((z k) i : ℝ)} := by
          ext x; constructor
          · rintro ⟨k, rfl⟩; exact ⟨k.1, k.2, rfl⟩
          · rintro ⟨k, hk, rfl⟩; exact ⟨⟨k, hk⟩, rfl⟩
        rw [hrb, hrz, hsetb, hsetz, hbflag (m - 1) (by omega)]
    have he_symm_b : ∀ k : Fin n, e.symm (fun i => ((b k) i : ℝ)) = Pi.single k (1 : ℝ) := by
      intro k
      apply e.injective
      rw [LinearEquiv.apply_symm_apply, he_apply, hMe k]
    have hflag' : ∀ (j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n) (x : Fin n → ℤ),
        (fun x => F (e x)) (fun i => (x i : ℝ)) < Work.BW.succMinL (fun x => F (e x)) j →
        (fun i => (x i : ℝ)) ∈ Work.BW.KWM.cflag n (j - 1) := by
      intro j hj1 hjn x hx
      have he_x : e (fun i => (x i : ℝ)) = fun i => ((Mi.mulVec x) i : ℝ) := by
        rw [he_apply, hMz]
      have hx0 : F (e (fun i => (x i : ℝ))) < Work.BW.succMinL (fun x => F (e x)) j := hx
      have hkmem : (fun i => ((Mi.mulVec x) i : ℝ)) ∈ Submodule.span ℝ
          (Set.range (fun k : {k : Fin n // (k : ℕ) < j - 1} => fun i => ((z k) i : ℝ))) := by
        refine hzflag ⟨j - 1, by omega⟩ (Mi.mulVec x) ?_
        rw [← he_x, show (⟨j - 1, by omega⟩ : Fin n).1 = j - 1 by simp,
          Nat.sub_add_cancel hj1, ← heq j]
        exact hx0
      have hmem2 : (fun i => ((Mi.mulVec x) i : ℝ)) ∈ Submodule.span ℝ
          (Set.range (fun k : {k : Fin n // (k : ℕ) < j - 1} => fun i => ((b k) i : ℝ))) := by
        rw [hspan_bz (j - 1) (by omega)]
        exact hkmem
      have hsub : (Submodule.span ℝ (Set.range (fun k : {k : Fin n // (k : ℕ) < j - 1} =>
            fun i => ((b k) i : ℝ)))).map (e.symm : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
          ≤ Submodule.span ℝ (Set.range (fun k : {k : Fin n // (k : ℕ) < j - 1} =>
            (Pi.single (k : Fin n) (1 : ℝ) : Fin n → ℝ))) := by
        rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
        rintro y ⟨k, rfl⟩
        exact (Submodule.mem_comap).mpr (Submodule.subset_span ⟨k, (he_symm_b k).symm⟩)
      have hcx : (fun i => (x i : ℝ)) = e.symm (fun i => ((Mi.mulVec x) i : ℝ)) := by
        rw [← he_x, LinearEquiv.symm_apply_apply]
      rw [hcx, ← hspan_e (j - 1) (by omega)]
      exact hsub (Submodule.mem_map.mpr ⟨_, hmem2, rfl⟩)
    have hmain := Work.BW.KWM.coord_case hn (fun x => F (e x)) hF' hflag'
    have hvol : volume.real (Work.BW.KWM.uBall (fun x => F (e x)))
        = volume.real (Work.BW.KWM.uBall F) := by
      have h1 : Work.BW.KWM.uBall (fun x => F (e x)) = e ⁻¹' Work.BW.KWM.uBall F := rfl
      rw [h1]
      refine volume_real_preimage_linearEquiv e ?_ _
      have hLM : (e : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) = M.mulVecLin := by
        apply LinearMap.ext
        intro x
        exact he_apply x
      rw [hLM, show M.mulVecLin = Matrix.toLin' M from rfl, LinearMap.det_toLin', hMdet]
      rcases Int.isUnit_iff.mp hunit with h | h <;> rw [h] <;> norm_num
    have hprod : (∏ j : Fin n, Work.BW.succMinL (fun x => F (e x)) (j.1 + 1))
        = ∏ j : Fin n, Work.BW.succMinL F (j.1 + 1) :=
      Finset.prod_congr rfl (fun j _ => heq (j.1 + 1))
    rw [hprod, hvol] at hmain
    exact hmain

end Work.BW.KW

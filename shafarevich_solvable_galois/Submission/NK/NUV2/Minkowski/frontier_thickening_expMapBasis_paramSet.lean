import Mathlib
import Submission.NK.NUV2.Geom.volume_cthickening_frontier_normLeOne
import Submission.NK.NUV2.Minkowski.volume_thickening_unitBox_image_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.NUV2.Minkowski

open scoped Classical Pointwise
open MeasureTheory NumberField
open NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone
open NumberField.InfinitePlace
open NumberField.Units.dirichletUnitTheorem

section Aux

variable {K : Type*} [Field K] [NumberField K]

/-- The face of `closure (paramSet K)` in which the coordinate `j` is fixed to `v`. -/
noncomputable def faceSet (j : InfinitePlace K) (v : ℝ) : Set (realSpace K) :=
  Set.univ.pi fun i => if i = j then {v} else if i = w₀ then Set.Iic 0 else Set.Icc 0 1

/-- The parametrization of the "cap" face `faceSet w₀ v`: the `w₀`-coordinate is `v` and the
remaining coordinates are read off from `u`. -/
noncomputable def capP (v : ℝ) : ({i : InfinitePlace K // i ≠ w₀} → ℝ) → realSpace K :=
  fun u i => if hi : i = w₀ then v else u ⟨i, hi⟩

/-- The "unit part" of a lateral face: `w₀`-coordinate `0`, `j`-coordinate `v`, and the
remaining coordinates read off from `p`. -/
noncomputable def latU (j : InfinitePlace K) (v : ℝ)
    (p : {i : InfinitePlace K // i ≠ w₀} → ℝ) : realSpace K :=
  fun i => if hi : i = w₀ then 0 else if i = j then v else p ⟨i, hi⟩

/-- The parametrization of a lateral face `faceSet j v` (`j ≠ w₀`) as a "cone": the coordinate
of `p` at `j` plays the role of the scaling factor `Real.exp (x w₀)`. -/
noncomputable def latG (j : InfinitePlace K) (v : ℝ) (hj : j ≠ w₀) :
    ({i : InfinitePlace K // i ≠ w₀} → ℝ) → realSpace K :=
  fun p => p ⟨j, hj⟩ • expMapBasis (latU j v p)

/-- The unit cube in `{i : InfinitePlace K // i ≠ w₀} → ℝ`. -/
abbrev cubeJ : Set ({i : InfinitePlace K // i ≠ w₀} → ℝ) :=
  Set.univ.pi fun _ => Set.Icc (0:ℝ) 1

lemma cardJ_add_one :
    Fintype.card {i : InfinitePlace K // i ≠ w₀} + 1 = Fintype.card (InfinitePlace K) := by
  have h1 : Fintype.card {i : InfinitePlace K // i ≠ w₀} = Units.rank K := by
    have h := Units.finrank_eq_rank (K := K)
    rwa [Module.finrank_fintype_fun_eq_card] at h
  rw [h1, Units.rank]
  have h2 : 1 ≤ Fintype.card (InfinitePlace K) := Fintype.card_pos_iff.mpr ⟨w₀⟩
  omega

lemma closure_subset_faceSet (j : InfinitePlace K) (v : ℝ) :
    {x : realSpace K | x ∈ closure (paramSet K) ∧ x j = v} ⊆ faceSet j v := by
  intro x hx
  obtain ⟨hcl, hj⟩ := hx
  rw [closure_paramSet, Set.mem_univ_pi] at hcl
  rw [faceSet, Set.mem_univ_pi]
  intro i
  by_cases hi : i = j
  · subst hi; simpa using hj
  · by_cases hiw : i = w₀
    · subst hiw; rw [if_neg hi]; simpa using hcl w₀
    · have := hcl i
      rw [if_neg hiw] at this
      rw [if_neg hi, if_neg hiw]
      exact this

lemma capP_image (v : ℝ) :
    capP (K := K) v '' cubeJ (K := K) = faceSet w₀ v := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨u, hu, rfl⟩
    rw [faceSet, Set.mem_univ_pi]
    intro i
    by_cases hi : i = w₀
    · subst hi; simp [capP]
    · have h1 : (capP (K := K) v u) i = u ⟨i, hi⟩ := by simp [capP, hi]
      rw [h1, if_neg hi, if_neg hi]
      exact Set.mem_univ_pi.mp hu ⟨i, hi⟩
  · intro x hx
    rw [faceSet, Set.mem_univ_pi] at hx
    refine ⟨fun i' => x i'.1, ?_, ?_⟩
    · rw [Set.mem_univ_pi]
      intro i'
      have h := hx i'
      rw [if_neg i'.2, if_neg i'.2] at h
      exact h
    · funext i
      by_cases hi : i = w₀
      · subst hi
        rw [show capP (K := K) v (fun i' => x i'.1) w₀ = v by simp [capP]]
        have h := hx w₀
        rw [if_pos rfl] at h
        exact h.symm
      · simp [capP, hi]

lemma latG_image (j : InfinitePlace K) (v : ℝ) (hj : j ≠ w₀) :
    expMapBasis '' faceSet j v ⊆ latG j v hj '' cubeJ (K := K) := by
  rintro y ⟨x, hx, rfl⟩
  rw [faceSet, Set.mem_univ_pi] at hx
  have hxj : x j = v := by
    have h := hx j; rw [if_pos rfl] at h; exact h
  have hxw : x w₀ ≤ 0 := by
    have h := hx w₀
    rw [if_neg (Ne.symm hj), if_pos rfl] at h
    exact h
  have hxi : ∀ i, i ≠ j → i ≠ w₀ → x i ∈ Set.Icc (0:ℝ) 1 := by
    intro i hij hiw
    have h := hx i
    rw [if_neg hij, if_neg hiw] at h
    exact h
  have hz : latU j v (fun i' => if (i' : InfinitePlace K) = j then Real.exp (x w₀) else x i') =
      (fun i => if i = w₀ then 0 else x i) := by
    funext i
    by_cases hi : i = w₀
    · subst hi; simp [latU]
    · by_cases hij : i = j
      · subst hij; simp [latU, hi, hxj]
      · simp [latU, hi, hij]
  refine ⟨fun i' => if (i' : InfinitePlace K) = j then Real.exp (x w₀) else x i', ?_, ?_⟩
  · rw [Set.mem_univ_pi]
    intro i'
    by_cases h : (i' : InfinitePlace K) = j
    · rw [if_pos h]; exact ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr hxw⟩
    · rw [if_neg h]; exact hxi i'.1 h i'.2
  · show latG j v hj (fun i' => if (i' : InfinitePlace K) = j then Real.exp (x w₀) else x i')
      = expMapBasis x
    rw [latG]
    simp only [if_pos rfl]
    rw [hz]
    exact (expMapBasis_apply'' x).symm

lemma contDiff_expMapBasis : ContDiff ℝ 1 (expMapBasis : realSpace K → realSpace K) := by
  have h1 : ContDiff ℝ 1 (expMap : realSpace K → realSpace K) := by
    rw [contDiff_pi]
    intro w
    show ContDiff ℝ 1 (fun x : realSpace K => Real.exp ((w.mult : ℝ)⁻¹ * x w))
    fun_prop
  have hfun : (expMapBasis : realSpace K → realSpace K) =
      fun x => expMap ((completeBasis K).equivFunL.symm x) := by
    funext x; rw [expMapBasis_apply]; rfl
  rw [hfun]
  exact h1.comp (by fun_prop)

lemma lipschitz_capP (v : ℝ) : ∃ L : NNReal,
    LipschitzOnWith L (fun u => expMapBasis (capP (K := K) v u)) (cubeJ (K := K)) := by
  have hc : ContDiff ℝ 1 (fun u => expMapBasis (capP (K := K) v u)) :=
    (contDiff_expMapBasis (K := K)).comp (by
      rw [contDiff_pi]; intro i
      by_cases hi : i = w₀
      · simp only [capP, hi, dif_pos]; fun_prop
      · simp only [capP, hi, dif_neg, not_false_eq_true]
        exact (ContinuousLinearMap.contDiff
          (ContinuousLinearMap.proj ⟨i, hi⟩ : ({i // i ≠ w₀} → ℝ) →L[ℝ] ℝ)))
  refine ContDiffOn.exists_lipschitzOnWith hc.contDiffOn (by norm_num)
    (convex_pi fun _ _ => convex_Icc _ _) (isCompact_univ_pi fun _ => isCompact_Icc)

lemma lipschitz_latG (j : InfinitePlace K) (v : ℝ) (hj : j ≠ w₀) :
    ∃ L : NNReal, LipschitzOnWith L (latG j v hj) (cubeJ (K := K)) := by
  have hc : ContDiff ℝ 1 (latG j v hj) := by
    have hA : ContDiff ℝ 1 (fun p : {i : InfinitePlace K // i ≠ w₀} → ℝ => p ⟨j, hj⟩) := by
      fun_prop
    have hB : ContDiff ℝ 1 (fun p : {i : InfinitePlace K // i ≠ w₀} → ℝ =>
        expMapBasis (latU j v p)) :=
      (contDiff_expMapBasis (K := K)).comp (by
        rw [contDiff_pi]; intro i
        by_cases hi : i = w₀
        · have heq : (fun p : {i : InfinitePlace K // i ≠ w₀} → ℝ => latU j v p i)
              = fun _ => (0:ℝ) := by
            funext p; simp only [latU, dif_pos hi]
          rw [heq]; fun_prop
        · by_cases hij : i = j
          · have heq : (fun p : {i : InfinitePlace K // i ≠ w₀} → ℝ => latU j v p i)
                = fun _ => v := by
              funext p; simp only [latU, dif_neg hi, if_pos hij]
            rw [heq]; fun_prop
          · have heq : (fun p : {i : InfinitePlace K // i ≠ w₀} → ℝ => latU j v p i)
                = fun p => p ⟨i, hi⟩ := by
              funext p; simp only [latU, dif_neg hi, if_neg hij]
            rw [heq]
            exact (ContinuousLinearMap.contDiff
              (ContinuousLinearMap.proj ⟨i, hi⟩ : ({i // i ≠ w₀} → ℝ) →L[ℝ] ℝ)))
    exact hA.smul hB
  refine ContDiffOn.exists_lipschitzOnWith hc.contDiffOn (by norm_num)
    (convex_pi fun _ _ => convex_Icc _ _) (isCompact_univ_pi fun _ => isCompact_Icc)

/-- The `ε`-neighbourhood of a single face image has volume `O ε`. -/
lemma face_thickening_bound (j : InfinitePlace K) (v : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      volume {y : realSpace K | ∃ q ∈ expMapBasis '' (faceSet j v), ‖y - q‖ ≤ ε}
        ≤ ENNReal.ofReal (C * ε) := by
  by_cases hj : j = w₀
  · subst hj
    obtain ⟨L, hL⟩ := lipschitz_capP (K := K) v
    obtain ⟨C, hCpos, hC⟩ :=
      volume_thickening_unitBox_image_le (ι := {i : InfinitePlace K // i ≠ w₀})
        (η := InfinitePlace K) (k := 1) (cardJ_add_one (K := K))
        (fun u => expMapBasis (capP (K := K) v u)) L hL
    refine ⟨C, hCpos, fun ε hε hε1 => ?_⟩
    have hS : {y : realSpace K | ∃ q ∈ expMapBasis '' (faceSet w₀ v), ‖y - q‖ ≤ ε}
        = {y : realSpace K | ∃ q ∈ cubeJ (K := K),
            ‖y - expMapBasis (capP (K := K) v q)‖ ≤ ε} := by
      ext y
      constructor
      · rintro ⟨q, hq, hqy⟩
        obtain ⟨x, hx, rfl⟩ := hq
        rw [← capP_image (K := K) v] at hx
        obtain ⟨u, hu, rfl⟩ := hx
        exact ⟨u, hu, hqy⟩
      · rintro ⟨u, hu, hy⟩
        exact ⟨expMapBasis (capP (K := K) v u),
          ⟨capP (K := K) v u, by rw [← capP_image (K := K) v]; exact ⟨u, hu, rfl⟩, rfl⟩, hy⟩
    rw [hS]
    simpa [pow_one] using hC ε hε hε1
  · obtain ⟨L, hL⟩ := lipschitz_latG (K := K) j v hj
    obtain ⟨C, hCpos, hC⟩ :=
      volume_thickening_unitBox_image_le (ι := {i : InfinitePlace K // i ≠ w₀})
        (η := InfinitePlace K) (k := 1) (cardJ_add_one (K := K)) (latG j v hj) L hL
    refine ⟨C, hCpos, fun ε hε hε1 => ?_⟩
    have hsub2 : {y : realSpace K | ∃ q ∈ expMapBasis '' (faceSet j v), ‖y - q‖ ≤ ε} ⊆
        {y : realSpace K | ∃ q ∈ cubeJ (K := K), ‖y - latG j v hj q‖ ≤ ε} := by
      rintro y ⟨q, hq, hqy⟩
      obtain ⟨x, hx, rfl⟩ := hq
      obtain ⟨p, hp, hpv⟩ := latG_image j v hj ⟨x, hx, rfl⟩
      exact ⟨p, hp, by rw [hpv]; exact hqy⟩
    refine le_trans (measure_mono hsub2) ?_
    simpa [pow_one] using hC ε hε hε1

/-- The apex `{0}`: the `ε`-ball around the origin has volume `≤ 2 ^ card · ε` for `ε ≤ 1`. -/
lemma volume_closedBall_zero_le (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    volume {y : realSpace K | ‖y‖ ≤ ε}
      ≤ ENNReal.ofReal ((2:ℝ) ^ Fintype.card (InfinitePlace K) * ε) := by
  have hsub : {y : realSpace K | ‖y‖ ≤ ε} ⊆
      Set.univ.pi (fun _ : InfinitePlace K => Set.Icc (-ε) ε) := by
    intro y hy
    rw [Set.mem_univ_pi]
    intro w
    have hy' : ‖y‖ ≤ ε := hy
    have h := norm_le_pi_norm y w
    rw [Real.norm_eq_abs, abs_le] at h
    exact ⟨by linarith [h.1, hy'], by linarith [h.2, hy']⟩
  have hprod : (∏ _ : InfinitePlace K, volume (Set.Icc (-ε) ε))
      = ENNReal.ofReal ((2 * ε) ^ Fintype.card (InfinitePlace K)) := by
    simp only [Real.volume_Icc]
    rw [Finset.prod_const, Finset.card_univ]
    rw [show ε - -ε = 2 * ε by ring]
    rw [← ENNReal.ofReal_pow (show (0:ℝ) ≤ 2 * ε by linarith)]
  refine (measure_mono hsub).trans ?_
  rw [volume_pi, Measure.pi_pi, hprod]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_pow]
  have hn : 1 ≤ Fintype.card (InfinitePlace K) := Fintype.card_pos_iff.mpr ⟨w₀⟩
  have h1 : ε ^ Fintype.card (InfinitePlace K) ≤ ε := by
    calc ε ^ Fintype.card (InfinitePlace K) ≤ ε ^ 1 :=
          pow_le_pow_of_le_one hε.le hε1 hn
      _ = ε := pow_one ε
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

end Aux

/-- **Minkowski content of the frontier of `expMapBasis '' paramSet K` (the unfolded region).**
In the real space `realSpace K = InfinitePlace K → ℝ`, the `ε`-neighbourhood of the frontier of
`expMapBasis '' paramSet K` has volume `≤ C · ε` for `0 < ε ≤ 1`.

Structure: `paramSet K = ∏ w, (if w = w₀ then Iic 0 else Ico 0 1)` is a half-open box, unbounded
only in the `w₀` direction; `expMapBasis` is an open partial homeomorphism with source `univ`, so
it is an open embedding, and `expMapBasis x = Real.exp (x w₀) • expMapBasis (unit part)`
(`expMapBasis_apply'`). Hence `expMapBasis '' paramSet K = (0,1] • B` with
`B = expMapBasis '' ({x w₀ = 0} ∩ box)` compact, and
`frontier (expMapBasis '' paramSet K) = expMapBasis '' (frontier (paramSet K)) ∪ {0}`. The frontier
of `paramSet K` is a finite union of coordinate faces, i.e. `(rank K - 1)`-dimensional boxes;
`expMapBasis` is Lipschitz on each (bounded) face with an explicit constant, so
`volume_thickening_box_image_le` in
`Submission/Work/NUV2/Minkowski/volume_thickening_box_image_le.lean` gives volume `O ε` for each
face-image, while the apex `{0}` contributes `O(ε^n) ≤ O(ε)` for `ε ≤ 1`. -/
theorem frontier_thickening_expMapBasis_paramSet (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (volume {y : realSpace K | ∃ q ∈ frontier (expMapBasis '' (paramSet K)), ‖y - q‖ ≤ ε}).toReal
        ≤ C * ε := by
  classical
  choose cf hcf using fun p : InfinitePlace K × Fin 2 =>
    face_thickening_bound (K := K) p.1 (((p.2 : ℕ) : ℝ))
  set Cs : ℝ := ∑ p : InfinitePlace K × Fin 2, cf p with hCs
  have hCspos : 0 < Cs := by
    obtain ⟨p₀⟩ := (inferInstance : Nonempty (InfinitePlace K × Fin 2))
    exact Finset.sum_pos (fun p _ => (hcf p).1) ⟨p₀, Finset.mem_univ p₀⟩
  set Ctot : ℝ := Cs + 2 ^ Fintype.card (InfinitePlace K) with hCtot
  have hCtotpos : 0 < Ctot := by
    have h2 : (0:ℝ) < 2 ^ Fintype.card (InfinitePlace K) := by positivity
    rw [hCtot]; linarith
  refine ⟨Ctot, hCtotpos, fun ε hε hε1 => ?_⟩
  set S : Set (realSpace K) :=
    {y : realSpace K | ∃ q ∈ frontier (expMapBasis '' (paramSet K)), ‖y - q‖ ≤ ε} with hS
  have hsub : S ⊆ ({y : realSpace K | ‖y‖ ≤ ε} ∪
      ⋃ p ∈ (Finset.univ : Finset (InfinitePlace K × Fin 2)),
        {y : realSpace K | ∃ q ∈ expMapBasis '' (faceSet p.1 (((p.2 : ℕ) : ℝ))),
          ‖y - q‖ ≤ ε}) := by
    intro y hy
    obtain ⟨q, hq, hqy⟩ := hy
    rcases (NK.NUV2.Geom.frontier_expMapBasis_paramSet_subset (K := K)) hq with hq1 | hq0
    · right
      rw [Set.mem_iUnion] at hq1
      obtain ⟨j, hj⟩ := hq1
      rcases hj with hj | hj
      · obtain ⟨x, hx, hxf⟩ := hj
        refine Set.mem_iUnion.mpr ⟨(j, 0), Set.mem_iUnion.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        refine ⟨expMapBasis x, ⟨x, ?_, rfl⟩, ?_⟩
        · simpa using closure_subset_faceSet j 0 hx
        · rw [hxf]; exact hqy
      · obtain ⟨x, hx, hxf⟩ := hj
        refine Set.mem_iUnion.mpr ⟨(j, 1), Set.mem_iUnion.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        refine ⟨expMapBasis x, ⟨x, ?_, rfl⟩, ?_⟩
        · simpa using closure_subset_faceSet j 1 hx
        · rw [hxf]; exact hqy
    · left
      have hq0' : q = 0 := by simpa using hq0
      rw [hq0', sub_zero] at hqy
      exact hqy
  have hbound : volume S ≤ ENNReal.ofReal (Ctot * ε) := by
    have h1 : volume S ≤ volume {y : realSpace K | ‖y‖ ≤ ε} +
        volume (⋃ p ∈ (Finset.univ : Finset (InfinitePlace K × Fin 2)),
          {y : realSpace K | ∃ q ∈ expMapBasis '' (faceSet p.1 (((p.2 : ℕ) : ℝ))),
            ‖y - q‖ ≤ ε}) :=
      (measure_mono hsub).trans (measure_union_le _ _)
    have h2 : volume (⋃ p ∈ (Finset.univ : Finset (InfinitePlace K × Fin 2)),
          {y : realSpace K | ∃ q ∈ expMapBasis '' (faceSet p.1 (((p.2 : ℕ) : ℝ))),
            ‖y - q‖ ≤ ε})
        ≤ ∑ p ∈ (Finset.univ : Finset (InfinitePlace K × Fin 2)),
            ENNReal.ofReal (cf p * ε) :=
      (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun p _ => (hcf p).2 ε hε hε1)
    calc volume S
        ≤ volume {y : realSpace K | ‖y‖ ≤ ε} +
            ∑ p ∈ (Finset.univ : Finset (InfinitePlace K × Fin 2)),
              ENNReal.ofReal (cf p * ε) := h1.trans (add_le_add le_rfl h2)
      _ ≤ ENNReal.ofReal ((2:ℝ) ^ Fintype.card (InfinitePlace K) * ε) +
            ENNReal.ofReal (∑ p : InfinitePlace K × Fin 2, cf p * ε) := by
          refine add_le_add (volume_closedBall_zero_le (K := K) ε hε hε1) ?_
          rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => mul_nonneg (hcf p).1.le hε.le)]
      _ = ENNReal.ofReal ((2:ℝ) ^ Fintype.card (InfinitePlace K) * ε +
            ∑ p : InfinitePlace K × Fin 2, cf p * ε) := by
          rw [ENNReal.ofReal_add (by positivity)
            (Finset.sum_nonneg fun p _ => mul_nonneg (hcf p).1.le hε.le)]
      _ = ENNReal.ofReal (Ctot * ε) := by
          congr 1
          rw [hCtot, hCs, ← Finset.sum_mul]
          ring
  rw [hS] at hbound
  calc (volume S).toReal ≤ (ENNReal.ofReal (Ctot * ε)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    _ = Ctot * ε := ENNReal.toReal_ofReal (by positivity)

end NK.NUV2.Minkowski

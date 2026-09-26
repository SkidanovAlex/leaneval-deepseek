import Mathlib
import Submission.Work.Drive.Final.Trough.Defs
import Submission.Work.Drive.Mono.FiberModel.pair_facts

namespace Work.Drive.Final.Trough

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

/-! ## Helper lemmas: the pair, its kernel, the fibre direction and the section -/

/-- `pair v ℓ` is the pair `(⟪v,·⟫, ℓ)` of continuous linear functionals. -/
theorem pair_eq_levPairCLM (v : R3) (ℓ : R3 →L[ℝ] ℝ) :
    pair v ℓ = Work.Drive.Mono.FiberModel.levPairCLM v ℓ := rfl

/-- The pair `(⟪v,·⟫, ℓ)` is surjective. -/
theorem pair_surjective {v : R3} {ℓ : R3 →L[ℝ] ℝ} (hv : v ≠ 0) (hℓv : ℓ v = 0)
    (hℓne : ℓ ≠ 0) : Function.Surjective (pair v ℓ) := by
  rw [pair_eq_levPairCLM]
  exact Work.Drive.Mono.FiberModel.levPairCLM_surjective hv hℓv hℓne

/-- The pair `(⟪v,·⟫, ℓ)` is an open map. -/
theorem pair_isOpenMap {v : R3} {ℓ : R3 →L[ℝ] ℝ} (hv : v ≠ 0) (hℓv : ℓ v = 0)
    (hℓne : ℓ ≠ 0) : IsOpenMap (pair v ℓ) := by
  rw [pair_eq_levPairCLM]
  exact Work.Drive.Mono.FiberModel.levPairCLM_isOpenMap hv hℓv hℓne

/-- The kernel of the pair is one-dimensional. -/
theorem finrank_ker_pair {v : R3} {ℓ : R3 →L[ℝ] ℝ} (hv : v ≠ 0) (hℓv : ℓ v = 0)
    (hℓne : ℓ ≠ 0) : Module.finrank ℝ (pairLM v ℓ).ker = 1 := by
  have hsurj := pair_surjective hv hℓv hℓne
  have hrange : (pairLM v ℓ).range = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    obtain ⟨y, hy⟩ := hsurj x
    exact ⟨y, hy⟩
  have hfin : Module.finrank ℝ (pairLM v ℓ).range = 2 := by
    have h2 : Module.finrank ℝ (ℝ × ℝ) = 2 := by
      simp [Module.finrank_prod, Module.finrank_self]
    rw [hrange]
    exact (Submodule.topEquiv (R := ℝ) (M := ℝ × ℝ)).finrank_eq.trans h2
  have h := LinearMap.finrank_range_add_finrank_ker (pairLM v ℓ)
  rw [hfin, finrank_euclideanSpace_fin] at h
  omega

/-- There is a non-zero vector in the kernel of the pair. -/
theorem exists_kernel_pair {v : R3} {ℓ : R3 →L[ℝ] ℝ} (hv : v ≠ 0) (hℓv : ℓ v = 0)
    (hℓne : ℓ ≠ 0) : ∃ w : R3, w ≠ 0 ∧ pair v ℓ w = 0 := by
  have hker : (pairLM v ℓ).ker ≠ ⊥ := by
    intro h
    have h0 : Module.finrank ℝ (pairLM v ℓ).ker = 0 := (Submodule.finrank_eq_zero).mpr h
    rw [finrank_ker_pair hv hℓv hℓne] at h0
    exact one_ne_zero h0
  obtain ⟨w, hw, hwne⟩ := (Submodule.ne_bot_iff (pairLM v ℓ).ker).mp hker
  exact ⟨w, hwne, hw⟩

/-- The fibre direction is non-zero. -/
theorem fibreDir_ne_zero {v : R3} {ℓ : R3 →L[ℝ] ℝ} (hv : v ≠ 0) (hℓv : ℓ v = 0)
    (hℓne : ℓ ≠ 0) : fibreDir v ℓ ≠ 0 := by
  obtain ⟨w, hwne, hw0⟩ := exists_kernel_pair hv hℓv hℓne
  have h : ∃ w : R3, w ≠ 0 ∧ pair v ℓ w = 0 := ⟨w, hwne, hw0⟩
  unfold fibreDir
  rw [dif_pos h]
  exact (Classical.choose_spec h).1

/-- The fibre direction lies in the kernel of the pair. -/
theorem pair_fibreDir {v : R3} {ℓ : R3 →L[ℝ] ℝ} (hv : v ≠ 0) (hℓv : ℓ v = 0)
    (hℓne : ℓ ≠ 0) : pair v ℓ (fibreDir v ℓ) = 0 := by
  obtain ⟨w, hwne, hw0⟩ := exists_kernel_pair hv hℓv hℓne
  have h : ∃ w : R3, w ≠ 0 ∧ pair v ℓ w = 0 := ⟨w, hwne, hw0⟩
  unfold fibreDir
  rw [dif_pos h]
  exact (Classical.choose_spec h).2

/-- The kernel of the pair is spanned by the fibre direction. -/
theorem span_fibreDir_eq_ker {v : R3} {ℓ : R3 →L[ℝ] ℝ} (hv : v ≠ 0) (hℓv : ℓ v = 0)
    (hℓne : ℓ ≠ 0) :
    Submodule.span ℝ ({fibreDir v ℓ} : Set R3) = (pairLM v ℓ).ker := by
  refine Submodule.eq_of_le_of_finrank_le ?_ ?_
  · rw [Submodule.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact pair_fibreDir hv hℓv hℓne
  · rw [finrank_span_singleton (fibreDir_ne_zero hv hℓv hℓne), finrank_ker_pair hv hℓv hℓne]

/-- A linear section of the pair. -/
theorem sectionL_spec {v : R3} {ℓ : R3 →L[ℝ] ℝ} (hv : v ≠ 0) (hℓv : ℓ v = 0)
    (hℓne : ℓ ≠ 0) (x : ℝ × ℝ) : pair v ℓ (sectionL v ℓ x) = x := by
  obtain ⟨g, hg⟩ := (pairLM v ℓ).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 (pair_surjective hv hℓv hℓne))
  have h : ∃ g : (ℝ × ℝ) →ₗ[ℝ] R3, ∀ x, pair v ℓ (g x) = x :=
    ⟨g, fun x => by have := congrFun (congrArg DFunLike.coe hg) x; simpa using this⟩
  unfold sectionL
  rw [dif_pos h]
  exact (Classical.choose_spec h) x

/-- The section property, for the linear map form of the pair. -/
theorem sectionL_spec' {v : R3} {ℓ : R3 →L[ℝ] ℝ} (hv : v ≠ 0) (hℓv : ℓ v = 0)
    (hℓne : ℓ ≠ 0) (x : ℝ × ℝ) : pairLM v ℓ (sectionL v ℓ x) = x :=
  sectionL_spec hv hℓv hℓne x

/-- The two ways of writing the pair agree. -/
theorem pairLM_eq_pair (v : R3) (ℓ : R3 →L[ℝ] ℝ) (y : R3) : pairLM v ℓ y = pair v ℓ y := rfl

/-- Every vector is a point of the section over its shadow, plus a multiple of the fibre
direction. -/
theorem exists_fibre_coord {v : R3} {ℓ : R3 →L[ℝ] ℝ} (hv : v ≠ 0) (hℓv : ℓ v = 0)
    (hℓne : ℓ ≠ 0) (y : R3) :
    ∃ t : ℝ, y = sectionL v ℓ (pair v ℓ y) + t • fibreDir v ℓ := by
  have hker : y - sectionL v ℓ (pair v ℓ y) ∈ (pairLM v ℓ).ker := by
    rw [LinearMap.mem_ker, map_sub, sectionL_spec' hv hℓv hℓne, pairLM_eq_pair, sub_self]
  have hspan : y - sectionL v ℓ (pair v ℓ y) ∈
      Submodule.span ℝ ({fibreDir v ℓ} : Set R3) := by
    rw [span_fibreDir_eq_ker hv hℓv hℓne]
    exact hker
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hspan
  refine ⟨t, ?_⟩
  rw [ht]
  abel


section Helpers

/-! ## The box constraints along a fibre -/

/-- The half side length of the box is positive. -/
theorem halfLen_pos (s : ℝ) (σ : Equiv.Perm (Fin 3)) (hs : 0 < s) (i : Fin 3) :
    0 < halfLen s σ i :=
  mul_pos (Submission.boxSide_pos i) hs

/-- Coordinates along a fibre. -/
theorem pt_coord (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3) (ℓ : R3 →L[ℝ] ℝ)
    (x : ℝ × ℝ) (t : ℝ) (i : Fin 3) :
    (sectionL v ℓ x + t • fibreDir v ℓ) (σ i) - c (σ i)
      = baseCoord s c σ v ℓ i x + t * kernCoef v ℓ σ i := by
  simp only [baseCoord, kernCoef, PiLp.add_apply, PiLp.smul_apply]
  ring

/-- Membership in the closed box, in fibre coordinates. -/
theorem mem_cbox_iff (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3) (ℓ : R3 →L[ℝ] ℝ)
    (x : ℝ × ℝ) (t : ℝ) :
    sectionL v ℓ x + t • fibreDir v ℓ ∈ cbox s c σ ↔
      ∀ i : Fin 3, |baseCoord s c σ v ℓ i x + t * kernCoef v ℓ σ i| ≤ halfLen s σ i := by
  simp only [cbox, halfLen]
  constructor
  · intro h i
    rw [← pt_coord s c σ v ℓ x t i]
    exact h i
  · intro h i
    rw [pt_coord s c σ v ℓ x t i]
    exact h i

/-- The index set of the box constraints involving the fibre parameter. -/
theorem mem_nzIdx {σ : Equiv.Perm (Fin 3)} {v : R3} {ℓ : R3 →L[ℝ] ℝ} (i : Fin 3) :
    i ∈ nzIdx v ℓ σ ↔ kernCoef v ℓ σ i ≠ 0 := by
  simp [nzIdx]

/-- The constraints involving the fibre parameter are non-empty. -/
theorem nzIdx_nonempty {σ : Equiv.Perm (Fin 3)} {v : R3} {ℓ : R3 →L[ℝ] ℝ} (hv : v ≠ 0)
    (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0) : (nzIdx v ℓ σ).Nonempty := by
  have hfd := fibreDir_ne_zero hv hℓv hℓne
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, fibreDir v ℓ (σ i) ≠ 0 := by
    by_contra h
    push Not at h
    apply hfd
    ext j
    simpa using h (σ.symm j)
  exact ⟨i, (mem_nzIdx i).mpr (by simpa [kernCoef] using hi)⟩

/-- The remaining constraints do not involve the fibre parameter. -/
theorem constraint_zero (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) {i : Fin 3} (hk : kernCoef v ℓ σ i = 0) (x : ℝ × ℝ) (t : ℝ) :
    |baseCoord s c σ v ℓ i x + t * kernCoef v ℓ σ i| ≤ halfLen s σ i ↔
      |baseCoord s c σ v ℓ i x| ≤ halfLen s σ i := by
  rw [hk, mul_zero, add_zero]

/-- Solving the `i`-th box constraint for the fibre parameter. -/
theorem constraint_iff (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) {i : Fin 3} (hk : kernCoef v ℓ σ i ≠ 0) (x : ℝ × ℝ) (t : ℝ) :
    |baseCoord s c σ v ℓ i x + t * kernCoef v ℓ σ i| ≤ halfLen s σ i ↔
      loB s c σ v ℓ i x ≤ t ∧ t ≤ hiB s c σ v ℓ i x := by
  set k := kernCoef v ℓ σ i with hkdef
  set b := baseCoord s c σ v ℓ i x with hbdef
  set h : ℝ := halfLen s σ i with hhdef
  rw [loB, hiB]
  by_cases hk' : 0 < k
  · rw [if_pos hk', if_pos hk']
    rw [abs_le, div_le_iff₀ hk', le_div_iff₀ hk']
    constructor <;> intro hh <;> exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  · have hkneg : k < 0 := lt_of_le_of_ne (not_lt.mp hk') hk
    rw [if_neg hk', if_neg hk']
    rw [abs_le, div_le_iff_of_neg hkneg, le_div_iff_of_neg hkneg]
    constructor <;> intro hh <;> exact ⟨by linarith [hh.2], by linarith [hh.1]⟩

/-- Membership in the shadow, in fibre coordinates. -/
theorem mem_shadow_iff (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) {v : R3}
    {ℓ : R3 →L[ℝ] ℝ} (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0) (x : ℝ × ℝ) :
    x ∈ shadow s c σ v ℓ ↔ ∃ t : ℝ, ∀ i : Fin 3,
      |baseCoord s c σ v ℓ i x + t * kernCoef v ℓ σ i| ≤ halfLen s σ i := by
  rw [mem_shadow]
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨t, ht⟩ := exists_fibre_coord hv hℓv hℓne y
    exact ⟨t, (mem_cbox_iff s c σ v ℓ x t).mp (by rw [← hxy, ← ht]; exact hy)⟩
  · rintro ⟨t, ht⟩
    refine ⟨sectionL v ℓ x + t • fibreDir v ℓ, (mem_cbox_iff s c σ v ℓ x t).mpr ht, ?_⟩
    rw [map_add, map_smul, sectionL_spec hv hℓv hℓne, pair_fibreDir hv hℓv hℓne, smul_zero,
      add_zero]


/-! ## The supremum and infimum of the box constraints -/

/-- Unfolding `htl` when the index set is non-empty. -/
theorem htl_eq (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3) (ℓ : R3 →L[ℝ] ℝ)
    (h : (nzIdx v ℓ σ).Nonempty) (x : ℝ × ℝ) :
    htl s c σ v ℓ x = (nzIdx v ℓ σ).sup' h (fun i => loB s c σ v ℓ i x) := by
  unfold htl
  rw [dif_pos h]

/-- Unfolding `hth` when the index set is non-empty. -/
theorem hth_eq (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3) (ℓ : R3 →L[ℝ] ℝ)
    (h : (nzIdx v ℓ σ).Nonempty) (x : ℝ × ℝ) :
    hth s c σ v ℓ x = (nzIdx v ℓ σ).inf' h (fun i => hiB s c σ v ℓ i x) := by
  unfold hth
  rw [dif_pos h]

/-- On the shadow, the lower fibre end never exceeds the upper one. -/
theorem htl_le_hth_of_mem_shadow (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0) {x : ℝ × ℝ}
    (hx : x ∈ shadow s c σ v ℓ) : htl s c σ v ℓ x ≤ hth s c σ v ℓ x := by
  obtain ⟨t0, ht0⟩ := (mem_shadow_iff s c σ hv hℓv hℓne x).mp hx
  have hnz : (nzIdx v ℓ σ).Nonempty := nzIdx_nonempty hv hℓv hℓne
  rw [htl_eq s c σ v ℓ hnz x, hth_eq s c σ v ℓ hnz x]
  apply Finset.sup'_le hnz
  intro i hi
  apply Finset.le_inf' hnz
  intro j hj
  have hi' : kernCoef v ℓ σ i ≠ 0 := (mem_nzIdx i).mp hi
  have hj' : kernCoef v ℓ σ j ≠ 0 := (mem_nzIdx j).mp hj
  have c1 := (constraint_iff s c σ v ℓ hi' x t0).mp (ht0 i)
  have c2 := (constraint_iff s c σ v ℓ hj' x t0).mp (ht0 j)
  linarith [c1.1, c2.2]

/-- Over the shadow, the whole interval between the two fibre ends lies in the box. -/
theorem mem_cbox_of_mem_shadow_of_between (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (v : R3) (ℓ : R3 →L[ℝ] ℝ) (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    {x : ℝ × ℝ} (hx : x ∈ shadow s c σ v ℓ) {t : ℝ}
    (htl_le : htl s c σ v ℓ x ≤ t) (ht_le : t ≤ hth s c σ v ℓ x) :
    sectionL v ℓ x + t • fibreDir v ℓ ∈ cbox s c σ := by
  obtain ⟨t0, ht0⟩ := (mem_shadow_iff s c σ hv hℓv hℓne x).mp hx
  have hnz : (nzIdx v ℓ σ).Nonempty := nzIdx_nonempty hv hℓv hℓne
  rw [mem_cbox_iff s c σ v ℓ x t]
  intro i
  by_cases hk : kernCoef v ℓ σ i = 0
  · rw [constraint_zero s c σ v ℓ hk x t]
    exact (constraint_zero s c σ v ℓ hk x t0).mp (ht0 i)
  · rw [constraint_iff s c σ v ℓ hk x t]
    have hmem : i ∈ nzIdx v ℓ σ := (mem_nzIdx i).mpr hk
    refine ⟨?_, ?_⟩
    · calc loB s c σ v ℓ i x
          ≤ (nzIdx v ℓ σ).sup' hnz (fun j => loB s c σ v ℓ j x) :=
            Finset.le_sup'_of_le (f := fun j => loB s c σ v ℓ j x) hmem le_rfl
        _ = htl s c σ v ℓ x := (htl_eq s c σ v ℓ hnz x).symm
        _ ≤ t := htl_le
    · calc t ≤ hth s c σ v ℓ x := ht_le
        _ = (nzIdx v ℓ σ).inf' hnz (fun j => hiB s c σ v ℓ j x) := hth_eq s c σ v ℓ hnz x
        _ ≤ hiB s c σ v ℓ i x := Finset.inf'_le_of_le (f := fun j => hiB s c σ v ℓ j x) hmem le_rfl

/-! ## Continuity -/

/-- The base coordinate is continuous. -/
theorem continuous_baseCoord (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) (i : Fin 3) : Continuous (baseCoord s c σ v ℓ i) := by
  have h1 : Continuous (fun x : ℝ × ℝ => (sectionL v ℓ) x (σ i)) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ i)).comp
      (sectionL v ℓ).continuous_of_finiteDimensional
  unfold baseCoord
  exact h1.sub continuous_const

/-- The lower bound from one constraint is continuous. -/
theorem continuous_loB (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) (i : Fin 3) : Continuous (loB s c σ v ℓ i) := by
  have hb := continuous_baseCoord s c σ v ℓ i
  unfold loB
  by_cases hpos : 0 < kernCoef v ℓ σ i
  · simp only [if_pos hpos]
    exact (continuous_const.sub hb).div_const _
  · simp only [if_neg hpos]
    exact (continuous_const.sub hb).div_const _

/-- The upper bound from one constraint is continuous. -/
theorem continuous_hiB (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) (i : Fin 3) : Continuous (hiB s c σ v ℓ i) := by
  have hb := continuous_baseCoord s c σ v ℓ i
  unfold hiB
  by_cases hpos : 0 < kernCoef v ℓ σ i
  · simp only [if_pos hpos]
    exact (continuous_const.sub hb).div_const _
  · simp only [if_neg hpos]
    exact (continuous_const.sub hb).div_const _

/-- The lower fibre end is continuous. -/
theorem continuous_htl (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0) :
    Continuous (htl s c σ v ℓ) := by
  have hnz : (nzIdx v ℓ σ).Nonempty := nzIdx_nonempty hv hℓv hℓne
  have hfun : htl s c σ v ℓ
      = fun x => (nzIdx v ℓ σ).sup' hnz (fun i => loB s c σ v ℓ i x) := by
    funext x; exact htl_eq s c σ v ℓ hnz x
  rw [hfun]
  exact Continuous.finset_sup'_apply hnz (fun i _ => continuous_loB s c σ v ℓ i)

/-- The upper fibre end is continuous. -/
theorem continuous_hth (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0) :
    Continuous (hth s c σ v ℓ) := by
  have hnz : (nzIdx v ℓ σ).Nonempty := nzIdx_nonempty hv hℓv hℓne
  have hfun : hth s c σ v ℓ
      = fun x => (nzIdx v ℓ σ).inf' hnz (fun i => hiB s c σ v ℓ i x) := by
    funext x; exact hth_eq s c σ v ℓ hnz x
  rw [hfun]
  exact Continuous.finset_inf'_apply hnz (fun i _ => continuous_hiB s c σ v ℓ i)

/-! ## Convexity -/

/-- The base coordinate is affine. -/
theorem baseCoord_affine (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) (i : Fin 3) (a b : ℝ) (hab : a + b = 1) (x y : ℝ × ℝ) :
    baseCoord s c σ v ℓ i (a • x + b • y)
      = a * baseCoord s c σ v ℓ i x + b * baseCoord s c σ v ℓ i y := by
  simp only [baseCoord, map_add, map_smul]
  rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  linear_combination (c (σ i)) * hab

/-- The lower bound from one constraint is affine. -/
theorem loB_affine (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3) (ℓ : R3 →L[ℝ] ℝ)
    (i : Fin 3) (a b : ℝ) (hab : a + b = 1) (x y : ℝ × ℝ) :
    loB s c σ v ℓ i (a • x + b • y)
      = a * loB s c σ v ℓ i x + b * loB s c σ v ℓ i y := by
  have hbase := baseCoord_affine s c σ v ℓ i a b hab x y
  unfold loB
  by_cases hpos : 0 < kernCoef v ℓ σ i
  · rw [if_pos hpos, if_pos hpos, if_pos hpos, hbase]
    have hk : kernCoef v ℓ σ i ≠ 0 := ne_of_gt hpos
    have hsum : halfLen s σ i * a + halfLen s σ i * b = halfLen s σ i := by
      rw [← mul_add, hab, mul_one]
    field_simp
    linarith [hsum]
  · rw [if_neg hpos, if_neg hpos, if_neg hpos, hbase]
    by_cases hk0 : kernCoef v ℓ σ i = 0
    · simp [hk0]
    · have hsum : halfLen s σ i * a + halfLen s σ i * b = halfLen s σ i := by
        rw [← mul_add, hab, mul_one]
      field_simp
      linarith [hsum]

/-- The upper bound from one constraint is affine. -/
theorem hiB_affine (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3) (ℓ : R3 →L[ℝ] ℝ)
    (i : Fin 3) (a b : ℝ) (hab : a + b = 1) (x y : ℝ × ℝ) :
    hiB s c σ v ℓ i (a • x + b • y)
      = a * hiB s c σ v ℓ i x + b * hiB s c σ v ℓ i y := by
  have hbase := baseCoord_affine s c σ v ℓ i a b hab x y
  unfold hiB
  by_cases hpos : 0 < kernCoef v ℓ σ i
  · rw [if_pos hpos, if_pos hpos, if_pos hpos, hbase]
    have hk : kernCoef v ℓ σ i ≠ 0 := ne_of_gt hpos
    have hsum : halfLen s σ i * a + halfLen s σ i * b = halfLen s σ i := by
      rw [← mul_add, hab, mul_one]
    field_simp
    linarith [hsum]
  · rw [if_neg hpos, if_neg hpos, if_neg hpos, hbase]
    by_cases hk0 : kernCoef v ℓ σ i = 0
    · simp [hk0]
    · have hsum : halfLen s σ i * a + halfLen s σ i * b = halfLen s σ i := by
        rw [← mul_add, hab, mul_one]
      field_simp
      linarith [hsum]

/-- The closed box is convex. -/
theorem convex_cbox (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) : Convex ℝ (cbox s c σ) := by
  rintro x hx y hy a b ha hb hab i
  have h1 := hx i
  have h2 := hy i
  have hcoord : (a • x + b • y) (σ i) - c (σ i)
      = a * (x (σ i) - c (σ i)) + b * (y (σ i) - c (σ i)) := by
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    linear_combination (c (σ i)) * hab
  rw [hcoord]
  calc |a * (x (σ i) - c (σ i)) + b * (y (σ i) - c (σ i))|
      ≤ |a * (x (σ i) - c (σ i))| + |b * (y (σ i) - c (σ i))| := abs_add_le _ _
    _ = a * |x (σ i) - c (σ i)| + b * |y (σ i) - c (σ i)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * (Submission.boxSide i * s) + b * (Submission.boxSide i * s) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
    _ = Submission.boxSide i * s := by
          have hfac : a * (Submission.boxSide i * s) + b * (Submission.boxSide i * s)
              = (a + b) * (Submission.boxSide i * s) := by ring
          rw [hfac, hab, one_mul]

/-- The shadow of the closed box is convex. -/
theorem convex_shadow (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) : Convex ℝ (shadow s c σ v ℓ) := by
  rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ a b ha hb hab
  exact ⟨a • y + b • y', convex_cbox s c σ hy hy' ha hb hab, by simp [map_add, map_smul]⟩

/-- The lower fibre end is convex over the shadow. -/
theorem convexOn_htl (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0) :
    ConvexOn ℝ (shadow s c σ v ℓ) (htl s c σ v ℓ) := by
  have hnz : (nzIdx v ℓ σ).Nonempty := nzIdx_nonempty hv hℓv hℓne
  refine ⟨convex_shadow s c σ v ℓ, ?_⟩
  rintro x hx y hy a b ha hb hab
  rw [htl_eq s c σ v ℓ hnz (a • x + b • y), smul_eq_mul, smul_eq_mul]
  apply Finset.sup'_le hnz
  intro i hi
  have h1 : loB s c σ v ℓ i x ≤ htl s c σ v ℓ x := by
    rw [htl_eq s c σ v ℓ hnz x]; exact Finset.le_sup'_of_le (f := fun j => loB s c σ v ℓ j x) hi le_rfl
  have h2 : loB s c σ v ℓ i y ≤ htl s c σ v ℓ y := by
    rw [htl_eq s c σ v ℓ hnz y]; exact Finset.le_sup'_of_le (f := fun j => loB s c σ v ℓ j y) hi le_rfl
  have haff := loB_affine s c σ v ℓ i a b hab x y
  rw [haff]
  nlinarith [h1, h2, ha, hb]

/-- The upper fibre end is concave over the shadow. -/
theorem concaveOn_hth (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0) :
    ConcaveOn ℝ (shadow s c σ v ℓ) (hth s c σ v ℓ) := by
  have hnz : (nzIdx v ℓ σ).Nonempty := nzIdx_nonempty hv hℓv hℓne
  refine ⟨convex_shadow s c σ v ℓ, ?_⟩
  rintro x hx y hy a b ha hb hab
  rw [hth_eq s c σ v ℓ hnz (a • x + b • y), smul_eq_mul, smul_eq_mul]
  apply Finset.le_inf' hnz
  intro i hi
  have h1 : hth s c σ v ℓ x ≤ hiB s c σ v ℓ i x := by
    rw [hth_eq s c σ v ℓ hnz x]; exact Finset.inf'_le_of_le (f := fun j => hiB s c σ v ℓ j x) hi le_rfl
  have h2 : hth s c σ v ℓ y ≤ hiB s c σ v ℓ i y := by
    rw [hth_eq s c σ v ℓ hnz y]; exact Finset.inf'_le_of_le (f := fun j => hiB s c σ v ℓ j y) hi le_rfl
  have haff := hiB_affine s c σ v ℓ i a b hab x y
  rw [haff]
  nlinarith [h1, h2, ha, hb]



/-! ## The parametrisation `Phi` of the box over its shadow -/

/-- The parametrisation is the section plus a convex combination of the two fibre ends. -/
theorem Phi_eq (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3) (ℓ : R3 →L[ℝ] ℝ)
    (x : ℝ × ℝ) (τ : ℝ) :
    Phi s c σ v ℓ x τ
      = sectionL v ℓ x + ((1 - τ) * htl s c σ v ℓ x + τ * hth s c σ v ℓ x) • fibreDir v ℓ :=
  rfl

/-- The pair of a parametrised point is the point of the shadow. -/
theorem pair_Phi (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3) (ℓ : R3 →L[ℝ] ℝ)
    (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0) (x : ℝ × ℝ) (τ : ℝ) :
    pair v ℓ (Phi s c σ v ℓ x τ) = x := by
  rw [Phi_eq, map_add, map_smul, sectionL_spec hv hℓv hℓne, pair_fibreDir hv hℓv hℓne,
    smul_zero, add_zero]

/-- The lower end is the value at `τ = 0`. -/
theorem Phi_zero (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3) (ℓ : R3 →L[ℝ] ℝ)
    (x : ℝ × ℝ) : Phi s c σ v ℓ x 0 = sectionL v ℓ x + htl s c σ v ℓ x • fibreDir v ℓ := by
  rw [Phi_eq]; norm_num

/-- The upper end is the value at `τ = 1`. -/
theorem Phi_one (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3) (ℓ : R3 →L[ℝ] ℝ)
    (x : ℝ × ℝ) : Phi s c σ v ℓ x 1 = sectionL v ℓ x + hth s c σ v ℓ x • fibreDir v ℓ := by
  rw [Phi_eq]; norm_num

/-- A point of the box over `x` has fibre parameter at least `htl x`. -/
theorem htl_le_of_mem_cbox (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) {v : R3}
    {ℓ : R3 →L[ℝ] ℝ} (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0) {x : ℝ × ℝ} {t : ℝ}
    (h : sectionL v ℓ x + t • fibreDir v ℓ ∈ cbox s c σ) : htl s c σ v ℓ x ≤ t := by
  have hnz : (nzIdx v ℓ σ).Nonempty := nzIdx_nonempty hv hℓv hℓne
  have hc := (mem_cbox_iff s c σ v ℓ x t).mp h
  rw [htl_eq s c σ v ℓ hnz x]
  apply Finset.sup'_le hnz
  intro i hi
  exact ((constraint_iff s c σ v ℓ ((mem_nzIdx i).mp hi) x t).mp (hc i)).1

/-- A point of the box over `x` has fibre parameter at most `hth x`. -/
theorem le_hth_of_mem_cbox (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) {v : R3}
    {ℓ : R3 →L[ℝ] ℝ} (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0) {x : ℝ × ℝ} {t : ℝ}
    (h : sectionL v ℓ x + t • fibreDir v ℓ ∈ cbox s c σ) : t ≤ hth s c σ v ℓ x := by
  have hnz : (nzIdx v ℓ σ).Nonempty := nzIdx_nonempty hv hℓv hℓne
  have hc := (mem_cbox_iff s c σ v ℓ x t).mp h
  rw [hth_eq s c σ v ℓ hnz x]
  apply Finset.le_inf' hnz
  intro i hi
  exact ((constraint_iff s c σ v ℓ ((mem_nzIdx i).mp hi) x t).mp (hc i)).2

/-- Any number between two reals is a convex combination of them. -/
theorem exists_tau_of_between {a b t : ℝ} (hat : a ≤ t) (htb : t ≤ b) :
    ∃ τ : ℝ, τ ∈ Set.Icc (0:ℝ) 1 ∧ (1 - τ) * a + τ * b = t := by
  rcases eq_or_lt_of_le hat with h | h
  · exact ⟨0, by norm_num, by rw [← h]; ring⟩
  · have hba : 0 < b - a := by linarith
    refine ⟨(t - a) / (b - a), ⟨div_nonneg (by linarith) (le_of_lt hba), ?_⟩, ?_⟩
    · rw [div_le_one hba]; linarith
    · field_simp
      ring

/-- Every point of the box over a point of the shadow is parametrised. -/
theorem exists_tau_Phi (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0) {x : ℝ × ℝ}
    (hx : x ∈ shadow s c σ v ℓ) {y : R3} (hy : y ∈ cbox s c σ) (hxy : pair v ℓ y = x) :
    ∃ τ ∈ Set.Icc (0:ℝ) 1, Phi s c σ v ℓ x τ = y := by
  obtain ⟨t, ht⟩ := exists_fibre_coord hv hℓv hℓne y
  have hmem : sectionL v ℓ x + t • fibreDir v ℓ ∈ cbox s c σ := by
    rw [← hxy, ← ht]; exact hy
  have h1 : htl s c σ v ℓ x ≤ t := htl_le_of_mem_cbox s c σ hv hℓv hℓne hmem
  have h2 : t ≤ hth s c σ v ℓ x := le_hth_of_mem_cbox s c σ hv hℓv hℓne hmem
  obtain ⟨τ, hτ, hτeq⟩ := exists_tau_of_between h1 h2
  refine ⟨τ, hτ, ?_⟩
  rw [Phi_eq, hτeq, ht, hxy]

/-- The parametrisation is injective in the planar variable. -/
theorem Phi_inj (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3) (ℓ : R3 →L[ℝ] ℝ)
    (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0) {x x' : ℝ × ℝ} {τ τ' : ℝ}
    (h : Phi s c σ v ℓ x τ = Phi s c σ v ℓ x' τ') : x = x' := by
  calc x = pair v ℓ (Phi s c σ v ℓ x τ) := (pair_Phi s c σ v ℓ hv hℓv hℓne x τ).symm
    _ = pair v ℓ (Phi s c σ v ℓ x' τ') := by rw [h]
    _ = x' := pair_Phi s c σ v ℓ hv hℓv hℓne x' τ'

/-- The parametrisation is injective in the fibre parameter, over a non-degenerate fibre. -/
theorem Phi_tau_inj (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3) (ℓ : R3 →L[ℝ] ℝ)
    (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0) {x : ℝ × ℝ}
    (hlt : htl s c σ v ℓ x < hth s c σ v ℓ x) {τ τ' : ℝ}
    (h : Phi s c σ v ℓ x τ = Phi s c σ v ℓ x τ') : τ = τ' := by
  have hfd := fibreDir_ne_zero hv hℓv hℓne
  rw [Phi_eq, Phi_eq] at h
  have h2 : ((1 - τ) * htl s c σ v ℓ x + τ * hth s c σ v ℓ x) • fibreDir v ℓ
      = ((1 - τ') * htl s c σ v ℓ x + τ' * hth s c σ v ℓ x) • fibreDir v ℓ :=
    add_left_cancel h
  have h3 : (((1 - τ) * htl s c σ v ℓ x + τ * hth s c σ v ℓ x)
      - ((1 - τ') * htl s c σ v ℓ x + τ' * hth s c σ v ℓ x)) • fibreDir v ℓ = 0 := by
    rw [sub_smul, h2, sub_self]
  have hAB : ((1 - τ) * htl s c σ v ℓ x + τ * hth s c σ v ℓ x)
      - ((1 - τ') * htl s c σ v ℓ x + τ' * hth s c σ v ℓ x) = 0 := by
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact h4
    · exact absurd h4 hfd
  have hprod : (τ - τ') * (hth s c σ v ℓ x - htl s c σ v ℓ x) = 0 := by
    have key : ((1 - τ) * htl s c σ v ℓ x + τ * hth s c σ v ℓ x)
        - ((1 - τ') * htl s c σ v ℓ x + τ' * hth s c σ v ℓ x)
        = (τ - τ') * (hth s c σ v ℓ x - htl s c σ v ℓ x) := by ring
    rw [← key]; exact hAB
  rcases mul_eq_zero.mp hprod with h5 | h5
  · linarith
  · linarith

/-- The parametrised points fill the box over the shadow. -/
theorem mem_cbox_Phi (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0) {x : ℝ × ℝ}
    (hx : x ∈ shadow s c σ v ℓ) {τ : ℝ} (hτ : τ ∈ Set.Icc (0:ℝ) 1) :
    Phi s c σ v ℓ x τ ∈ cbox s c σ := by
  have hle := htl_le_hth_of_mem_shadow s c σ v ℓ hv hℓv hℓne hx
  rw [Phi_eq]
  exact mem_cbox_of_mem_shadow_of_between s c σ v ℓ hv hℓv hℓne hx
    (by nlinarith [hτ.1, hle]) (by nlinarith [hτ.2, hle])



/-! ## The fibre ends lie on the boundary of the box -/

/-- At the lower end of a constraint the constraint is tight. -/
theorem abs_coord_loB (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) (hs : 0 < s) {i : Fin 3} (hk : kernCoef v ℓ σ i ≠ 0) (x : ℝ × ℝ) :
    |baseCoord s c σ v ℓ i x + loB s c σ v ℓ i x * kernCoef v ℓ σ i| = halfLen s σ i := by
  have hH : 0 < halfLen s σ i := halfLen_pos s σ hs i
  unfold loB
  by_cases hpos : 0 < kernCoef v ℓ σ i
  · rw [if_pos hpos, div_mul_cancel₀ _ (ne_of_gt hpos)]
    have hkey : baseCoord s c σ v ℓ i x + (-(halfLen s σ i) - baseCoord s c σ v ℓ i x)
        = -(halfLen s σ i) := by ring
    rw [hkey, abs_neg, abs_of_pos hH]
  · rw [if_neg hpos, div_mul_cancel₀ _ hk]
    have hkey : baseCoord s c σ v ℓ i x + (halfLen s σ i - baseCoord s c σ v ℓ i x)
        = halfLen s σ i := by ring
    rw [hkey, abs_of_pos hH]

/-- At the upper end of a constraint the constraint is tight. -/
theorem abs_coord_hiB (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) (hs : 0 < s) {i : Fin 3} (hk : kernCoef v ℓ σ i ≠ 0) (x : ℝ × ℝ) :
    |baseCoord s c σ v ℓ i x + hiB s c σ v ℓ i x * kernCoef v ℓ σ i| = halfLen s σ i := by
  have hH : 0 < halfLen s σ i := halfLen_pos s σ hs i
  unfold hiB
  by_cases hpos : 0 < kernCoef v ℓ σ i
  · rw [if_pos hpos, div_mul_cancel₀ _ (ne_of_gt hpos)]
    have hkey : baseCoord s c σ v ℓ i x + (halfLen s σ i - baseCoord s c σ v ℓ i x)
        = halfLen s σ i := by ring
    rw [hkey, abs_of_pos hH]
  · rw [if_neg hpos, div_mul_cancel₀ _ hk]
    have hkey : baseCoord s c σ v ℓ i x + (-(halfLen s σ i) - baseCoord s c σ v ℓ i x)
        = -(halfLen s σ i) := by ring
    rw [hkey, abs_neg, abs_of_pos hH]

/-- A point on a face of the box is not in the interior. -/
theorem not_mem_interior_cbox_of_tight (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (hs : 0 < s) {i : Fin 3} {y : R3}
    (ht : |y (σ i) - c (σ i)| = halfLen s σ i) : y ∉ interior (cbox s c σ) := by
  intro hy
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior y hy
  have hH : 0 < halfLen s σ i := halfLen_pos s σ hs i
  set e : R3 := EuclideanSpace.single (σ i) 1 with he
  have he_norm : ‖e‖ = 1 := by
    rw [he, EuclideanSpace.single, PiLp.norm_single]
    norm_num
  rcases lt_trichotomy (y (σ i) - c (σ i)) 0 with hsign | hsign | hsign
  · have hyi : y (σ i) - c (σ i) = -halfLen s σ i := by
      rw [abs_of_neg hsign] at ht; linarith
    have hδpos : 0 < ε / 2 := by linarith
    have hδlt : ε / 2 < ε := by linarith
    have hmem : y - (ε / 2) • e ∈ Metric.ball y ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hsub : y - (ε / 2) • e - y = -((ε / 2) • e) := by abel
      rw [hsub, norm_neg, norm_smul, he_norm, mul_one, Real.norm_eq_abs, abs_of_pos hδpos]
      exact hδlt
    have hcoord : (y - (ε / 2) • e) (σ i) - c (σ i) = -halfLen s σ i - ε / 2 := by
      rw [PiLp.sub_apply, PiLp.smul_apply, he, EuclideanSpace.single_apply, if_pos rfl,
        smul_eq_mul, mul_one]
      linarith [hyi]
    have hle := (interior_subset (hball hmem)) i
    rw [hcoord, abs_of_neg (by linarith : -halfLen s σ i - ε / 2 < 0)] at hle
    have hlen : halfLen s σ i = Submission.boxSide i * s := rfl
    linarith [hlen]
  · exfalso
    rw [hsign, abs_zero] at ht
    linarith [hH]
  · have hyi : y (σ i) - c (σ i) = halfLen s σ i := by
      rw [abs_of_pos hsign] at ht; exact ht
    have hδpos : 0 < ε / 2 := by linarith
    have hδlt : ε / 2 < ε := by linarith
    have hmem : y + (ε / 2) • e ∈ Metric.ball y ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hsub : y + (ε / 2) • e - y = (ε / 2) • e := by abel
      rw [hsub, norm_smul, he_norm, mul_one, Real.norm_eq_abs, abs_of_pos hδpos]
      exact hδlt
    have hcoord : (y + (ε / 2) • e) (σ i) - c (σ i) = halfLen s σ i + ε / 2 := by
      rw [PiLp.add_apply, PiLp.smul_apply, he, EuclideanSpace.single_apply, if_pos rfl,
        smul_eq_mul, mul_one]
      linarith [hyi]
    have hle := (interior_subset (hball hmem)) i
    rw [hcoord, abs_of_pos (by linarith : (0:ℝ) < halfLen s σ i + ε / 2)] at hle
    have hlen : halfLen s σ i = Submission.boxSide i * s := rfl
    linarith [hlen]

/-- The two ends of every fibre lie on the boundary of the box. -/
theorem Phi_mem_frontier_cbox (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) (hs : 0 < s) (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    {x : ℝ × ℝ} (hx : x ∈ shadow s c σ v ℓ) :
    Phi s c σ v ℓ x 0 ∈ frontier (cbox s c σ) ∧
      Phi s c σ v ℓ x 1 ∈ frontier (cbox s c σ) := by
  have hnz : (nzIdx v ℓ σ).Nonempty := nzIdx_nonempty hv hℓv hℓne
  have hmem0 := mem_cbox_Phi s c σ v ℓ hv hℓv hℓne hx (Set.left_mem_Icc.mpr zero_le_one)
  have hmem1 := mem_cbox_Phi s c σ v ℓ hv hℓv hℓne hx (Set.right_mem_Icc.mpr zero_le_one)
  constructor
  · obtain ⟨i0, hi0, hi0eq⟩ := Finset.exists_mem_eq_sup' hnz (fun i => loB s c σ v ℓ i x)
    have hk0 : kernCoef v ℓ σ i0 ≠ 0 := (mem_nzIdx i0).mp hi0
    have hlo : loB s c σ v ℓ i0 x = htl s c σ v ℓ x := by
      rw [htl_eq s c σ v ℓ hnz x]; exact hi0eq.symm
    have htight : |(Phi s c σ v ℓ x 0) (σ i0) - c (σ i0)| = halfLen s σ i0 := by
      rw [Phi_zero, ← hlo, pt_coord s c σ v ℓ x (loB s c σ v ℓ i0 x) i0]
      exact abs_coord_loB s c σ v ℓ hs hk0 x
    exact (mem_frontier_iff_notMem_interior hmem0).mpr
      (not_mem_interior_cbox_of_tight s c σ hs htight)
  · obtain ⟨j0, hj0, hj0eq⟩ := Finset.exists_mem_eq_inf' hnz (fun i => hiB s c σ v ℓ i x)
    have hk0 : kernCoef v ℓ σ j0 ≠ 0 := (mem_nzIdx j0).mp hj0
    have hhi : hiB s c σ v ℓ j0 x = hth s c σ v ℓ x := by
      rw [hth_eq s c σ v ℓ hnz x]; exact hj0eq.symm
    have htight : |(Phi s c σ v ℓ x 1) (σ j0) - c (σ j0)| = halfLen s σ j0 := by
      rw [Phi_one, ← hhi, pt_coord s c σ v ℓ x (hiB s c σ v ℓ j0 x) j0]
      exact abs_coord_hiB s c σ v ℓ hs hk0 x
    exact (mem_frontier_iff_notMem_interior hmem1).mpr
      (not_mem_interior_cbox_of_tight s c σ hs htight)

/-- The parametrisation sends the frontier of the shadow into the frontier of the box. -/
theorem Phi_frontier_shadow (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    {x : ℝ × ℝ} (hx : x ∈ frontier (shadow s c σ v ℓ)) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0:ℝ) 1) :
    Phi s c σ v ℓ x τ ∈ frontier (cbox s c σ) := by
  have hnz : (nzIdx v ℓ σ).Nonempty := nzIdx_nonempty hv hℓv hℓne
  have hcl : x ∈ closure (shadow s c σ v ℓ) := by
    have h := hx; rw [frontier, Set.mem_sdiff] at h; exact h.1
  have hnint : x ∉ interior (shadow s c σ v ℓ) := by
    have h := hx; rw [frontier, Set.mem_sdiff] at h; exact h.2
  have hle : htl s c σ v ℓ x ≤ hth s c σ v ℓ x :=
    closure_minimal (fun x' hx' => htl_le_hth_of_mem_shadow s c σ v ℓ hv hℓv hℓne hx')
      (isClosed_le (continuous_htl s c σ v ℓ hv hℓv hℓne)
        (continuous_hth s c σ v ℓ hv hℓv hℓne)) hcl
  have hmem : Phi s c σ v ℓ x τ ∈ cbox s c σ := by
    rw [Phi_eq, mem_cbox_iff]
    intro i
    by_cases hk : kernCoef v ℓ σ i = 0
    · rw [constraint_zero s c σ v ℓ hk]
      have hclosed : IsClosed {x : ℝ × ℝ | |baseCoord s c σ v ℓ i x| ≤ halfLen s σ i} :=
        isClosed_le (continuous_baseCoord s c σ v ℓ i).abs continuous_const
      have hsub : shadow s c σ v ℓ ⊆ {x : ℝ × ℝ | |baseCoord s c σ v ℓ i x| ≤ halfLen s σ i} := by
        intro x' hx'
        obtain ⟨t', ht'⟩ := (mem_shadow_iff s c σ hv hℓv hℓne x').mp hx'
        exact (constraint_zero s c σ v ℓ hk x' t').mp (ht' i)
      exact closure_minimal hsub hclosed hcl
    · rw [constraint_iff s c σ v ℓ hk]
      have h1 : loB s c σ v ℓ i x ≤ htl s c σ v ℓ x := by
        rw [htl_eq s c σ v ℓ hnz x]
        exact Finset.le_sup'_of_le (f := fun j => loB s c σ v ℓ j x)
          ((mem_nzIdx i).mpr hk) le_rfl
      have h2 : hth s c σ v ℓ x ≤ hiB s c σ v ℓ i x := by
        rw [hth_eq s c σ v ℓ hnz x]
        exact Finset.inf'_le_of_le (f := fun j => hiB s c σ v ℓ j x)
          ((mem_nzIdx i).mpr hk) le_rfl
      exact ⟨by nlinarith [h1, hle, hτ.1], by nlinarith [h2, hle, hτ.2]⟩
  have hnot : Phi s c σ v ℓ x τ ∉ interior (cbox s c σ) := by
    intro hint
    have hopen : IsOpen (pair v ℓ '' interior (cbox s c σ)) :=
      pair_isOpenMap hv hℓv hℓne _ isOpen_interior
    have hsub : pair v ℓ '' interior (cbox s c σ) ⊆ shadow s c σ v ℓ := by
      rintro y ⟨z, hz, rfl⟩
      exact ⟨z, interior_subset hz, rfl⟩
    have : x ∈ interior (shadow s c σ v ℓ) :=
      interior_maximal hsub hopen ⟨Phi s c σ v ℓ x τ, hint, pair_Phi s c σ v ℓ hv hℓv hℓne x τ⟩
    exact hnint this
  exact (mem_frontier_iff_notMem_interior hmem).mpr hnot



/-! ## Positive combinators on affine functions -/

/-- An affine function with a local maximum at an interior point is constant. -/
theorem affine_eq_zero_of_le_on_ball {G : ℝ × ℝ → ℝ}
    (haff : ∀ (a b : ℝ) (x y : ℝ × ℝ), a + b = 1 → G (a • x + b • y) = a * G x + b * G y)
    {x : ℝ × ℝ} (hxG : G x = 0) {ε : ℝ} (hε : 0 < ε)
    (hle : ∀ x' ∈ Metric.ball x ε, G x' ≤ 0) : ∀ d : ℝ × ℝ, G (x + d) = 0 := by
  intro d
  by_contra hne
  have hshift : ∀ t : ℝ, G (x + t • d) = t * G (x + d) := by
    intro t
    have h1 : x + t • d = (1 - t) • x + t • (x + d) := by
      have : (1 - t) • x + t • (x + d) = x + t • d := by
        rw [smul_add, ← add_assoc, ← add_smul, show (1 - t) + t = 1 by ring, one_smul]
      exact this.symm
    rw [h1, haff (1 - t) t x (x + d) (by ring), hxG]
    ring
  set δ : ℝ := min (1 / 2) (ε / (2 * (‖d‖ + 1))) with hδ
  have hδpos : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδle : δ ≤ ε / (2 * (‖d‖ + 1)) := min_le_right _ _
  have hdist : δ * ‖d‖ < ε := by
    have hden : 0 < 2 * (‖d‖ + 1) := by positivity
    calc δ * ‖d‖ ≤ (ε / (2 * (‖d‖ + 1))) * ‖d‖ :=
          mul_le_mul_of_nonneg_right hδle (norm_nonneg d)
      _ = ε * (‖d‖ / (2 * (‖d‖ + 1))) := by ring
      _ < ε * 1 := by
          refine mul_lt_mul_of_pos_left ?_ hε
          rw [div_lt_one hden]; linarith [norm_nonneg d]
      _ = ε := mul_one ε
  set t : ℝ := (if 0 < G (x + d) then 1 else -1) * δ with ht
  have htabs : |t| = δ := by
    rw [ht]
    have hsgn : (if 0 < G (x + d) then (1:ℝ) else -1) = 1 ∨
        (if 0 < G (x + d) then (1:ℝ) else -1) = -1 := by
      by_cases h : 0 < G (x + d) <;> simp [h]
    rcases hsgn with h | h <;> rw [h] <;> simp [abs_of_pos hδpos]
  have htpos : 0 < t * G (x + d) := by
    rw [ht]
    by_cases h : 0 < G (x + d)
    · rw [if_pos h, one_mul]; exact mul_pos hδpos h
    · rw [if_neg h]
      have hneg : G (x + d) < 0 := lt_of_le_of_ne (not_lt.mp h) hne
      nlinarith [hδpos, hneg]
  have hmem : x + t • d ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : x + t • d - x = t • d := by abel
    rw [hsub, norm_smul, Real.norm_eq_abs, htabs]
    exact hdist
  have hcontra := hle (x + t • d) hmem
  rw [hshift t] at hcontra
  linarith [htpos, hcontra]

/-- The same, in pointwise form. -/
theorem affine_const_of_le_on_ball {G : ℝ × ℝ → ℝ}
    (haff : ∀ (a b : ℝ) (x y : ℝ × ℝ), a + b = 1 → G (a • x + b • y) = a * G x + b * G y)
    {x : ℝ × ℝ} (hxG : G x = 0) {ε : ℝ} (hε : 0 < ε)
    (hle : ∀ x' ∈ Metric.ball x ε, G x' ≤ 0) (x' : ℝ × ℝ) : G x' = 0 := by
  have h := affine_eq_zero_of_le_on_ball haff hxG hε hle (x' - x)
  rwa [show x + (x' - x) = x' by abel] at h

/-- If a base coordinate is constant along the fibre directions, its value is zero. -/
theorem baseCoord_const_value_zero (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) {v : R3}
    {ℓ : R3 →L[ℝ] ℝ} (hs : 0 < s) (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    {i : Fin 3} (hk : kernCoef v ℓ σ i = 0) {β : ℝ}
    (hconst : ∀ x' : ℝ × ℝ, baseCoord s c σ v ℓ i x' = β) : β = 0 := by
  have hb0 : baseCoord s c σ v ℓ i (0 : ℝ × ℝ) = -c (σ i) := by simp [baseCoord]
  have hβ : β = -c (σ i) := by rw [← hconst 0, hb0]
  have hcbox : c ∈ cbox s c σ := by
    intro j
    rw [sub_self, abs_zero]
    exact mul_nonneg (le_of_lt (Submission.boxSide_pos j)) (le_of_lt hs)
  have hzero : ∀ y ∈ cbox s c σ, y (σ i) = 0 := by
    intro y hy
    obtain ⟨t, ht⟩ := exists_fibre_coord hv hℓv hℓne y
    have hsec : (sectionL v ℓ) (pair v ℓ y) (σ i) = 0 := by
      have h1 : baseCoord s c σ v ℓ i (pair v ℓ y)
          = (sectionL v ℓ) (pair v ℓ y) (σ i) - c (σ i) := rfl
      rw [hconst (pair v ℓ y), hβ] at h1
      linarith
    have hfd : fibreDir v ℓ (σ i) = 0 := hk
    rw [ht, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hsec, hfd, mul_zero, zero_add]
  rw [hβ, hzero c hcbox, neg_zero]

/-- A constraint that does not involve the fibre parameter is strict in the interior. -/
theorem strict_of_nzIdx_eq_zero (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) {v : R3}
    {ℓ : R3 →L[ℝ] ℝ} (hs : 0 < s) (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    {x : ℝ × ℝ} (hx : x ∈ interior (shadow s c σ v ℓ)) {i : Fin 3}
    (hk : kernCoef v ℓ σ i = 0) : |baseCoord s c σ v ℓ i x| < halfLen s σ i := by
  have hH : 0 < halfLen s σ i := halfLen_pos s σ hs i
  have hxsh : x ∈ shadow s c σ v ℓ := interior_subset hx
  obtain ⟨t0, ht0⟩ := (mem_shadow_iff s c σ hv hℓv hℓne x).mp hxsh
  have hble : |baseCoord s c σ v ℓ i x| ≤ halfLen s σ i :=
    (constraint_zero s c σ v ℓ hk x t0).mp (ht0 i)
  rcases lt_or_eq_of_le hble with h | h
  · exact h
  · exfalso
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
    have hball' : ∀ x' ∈ Metric.ball x ε, |baseCoord s c σ v ℓ i x'| ≤ halfLen s σ i := by
      intro x' hx'
      obtain ⟨t', ht'⟩ :=
        (mem_shadow_iff s c σ hv hℓv hℓne x').mp (interior_subset (hball hx'))
      exact (constraint_zero s c σ v ℓ hk x' t').mp (ht' i)
    rcases lt_trichotomy (baseCoord s c σ v ℓ i x) 0 with hneg | hzero | hpos
    · have hbx : baseCoord s c σ v ℓ i x = -halfLen s σ i := by
        rw [abs_of_neg hneg] at h; linarith
      have hconst : ∀ x' : ℝ × ℝ, baseCoord s c σ v ℓ i x' = -halfLen s σ i := by
        intro x'
        have haff : ∀ (a b : ℝ) (x₀ y₀ : ℝ × ℝ), a + b = 1 →
            (fun z => -baseCoord s c σ v ℓ i z - halfLen s σ i) (a • x₀ + b • y₀)
              = a * ((fun z => -baseCoord s c σ v ℓ i z - halfLen s σ i) x₀)
                + b * ((fun z => -baseCoord s c σ v ℓ i z - halfLen s σ i) y₀) := by
          intro a b x₀ y₀ hab
          simp only
          rw [baseCoord_affine s c σ v ℓ i a b hab x₀ y₀]
          linear_combination (halfLen s σ i) * hab
        have hle : ∀ z ∈ Metric.ball x ε,
            (fun z => -baseCoord s c σ v ℓ i z - halfLen s σ i) z ≤ 0 := by
          intro z hz
          have hz' := hball' z hz
          rw [abs_le] at hz'
          simp only
          linarith [hz'.1]
        have hxG : (fun z => -baseCoord s c σ v ℓ i z - halfLen s σ i) x = 0 := by
          simp only
          rw [hbx]; ring
        have hgoal := affine_const_of_le_on_ball haff hxG hε hle x'
        linarith
      have hz := baseCoord_const_value_zero s c σ hs hv hℓv hℓne hk hconst
      linarith [hH, hz]
    · rw [hzero, abs_zero] at h; linarith [hH]
    · have hbx : baseCoord s c σ v ℓ i x = halfLen s σ i := by
        rw [abs_of_pos hpos] at h; exact h
      have hconst : ∀ x' : ℝ × ℝ, baseCoord s c σ v ℓ i x' = halfLen s σ i := by
        intro x'
        have haff : ∀ (a b : ℝ) (x₀ y₀ : ℝ × ℝ), a + b = 1 →
            (fun z => baseCoord s c σ v ℓ i z - halfLen s σ i) (a • x₀ + b • y₀)
              = a * ((fun z => baseCoord s c σ v ℓ i z - halfLen s σ i) x₀)
                + b * ((fun z => baseCoord s c σ v ℓ i z - halfLen s σ i) y₀) := by
          intro a b x₀ y₀ hab
          simp only
          rw [baseCoord_affine s c σ v ℓ i a b hab x₀ y₀]
          linear_combination (halfLen s σ i) * hab
        have hle : ∀ z ∈ Metric.ball x ε,
            (fun z => baseCoord s c σ v ℓ i z - halfLen s σ i) z ≤ 0 := by
          intro z hz
          have hz' := hball' z hz
          rw [abs_le] at hz'
          simp only
          linarith [hz'.2]
        have hxG : (fun z => baseCoord s c σ v ℓ i z - halfLen s σ i) x = 0 := by
          simp only
          rw [hbx]; ring
        have hgoal := affine_const_of_le_on_ball haff hxG hε hle x'
        linarith
      have hz := baseCoord_const_value_zero s c σ hs hv hℓv hℓne hk hconst
      linarith [hH, hz]

/-- The interior of the box is cut out by the strict inequalities. -/
theorem interior_cbox_eq (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (hs : 0 < s) :
    interior (cbox s c σ) = {y : R3 | ∀ i, |y (σ i) - c (σ i)| < halfLen s σ i} := by
  refine Subset.antisymm ?_ ?_
  · intro y hy i
    have hyc : y ∈ cbox s c σ := interior_subset hy
    have hle : |y (σ i) - c (σ i)| ≤ halfLen s σ i := hyc i
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd hy (not_mem_interior_cbox_of_tight s c σ hs h)
  · have hopen : IsOpen {y : R3 | ∀ i, |y (σ i) - c (σ i)| < halfLen s σ i} := by
      rw [show {y : R3 | ∀ i, |y (σ i) - c (σ i)| < halfLen s σ i}
          = ⋂ i, {y : R3 | |y (σ i) - c (σ i)| < halfLen s σ i} by ext y; simp]
      refine isOpen_iInter_of_finite fun i => ?_
      have hcont : Continuous (fun y : R3 => y (σ i) - c (σ i)) :=
        (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ i)).sub continuous_const
      rw [show {y : R3 | |y (σ i) - c (σ i)| < halfLen s σ i}
          = (fun y : R3 => y (σ i) - c (σ i)) ⁻¹'
              Set.Ioo (-(halfLen s σ i)) (halfLen s σ i) by
        ext y; rw [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioo, abs_lt]]
      exact isOpen_Ioo.preimage hcont
    have hsub : {y : R3 | ∀ i, |y (σ i) - c (σ i)| < halfLen s σ i} ⊆ cbox s c σ := by
      intro z hz
      have hz' : ∀ i, |z (σ i) - c (σ i)| < halfLen s σ i := hz
      intro i
      exact le_of_lt (hz' i)
    exact fun y hy => interior_maximal hsub hopen hy

/-- The fibre of a box over any point of the shadow of the interior is non-degenerate. -/
theorem htl_lt_hth_of_mem_interior (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) {v : R3}
    {ℓ : R3 →L[ℝ] ℝ} (hs : 0 < s) (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    {x : ℝ × ℝ} (hx : x ∈ interior (shadow s c σ v ℓ)) :
    htl s c σ v ℓ x < hth s c σ v ℓ x := by
  have hxsh : x ∈ shadow s c σ v ℓ := interior_subset hx
  rcases lt_or_eq_of_le (htl_le_hth_of_mem_shadow s c σ v ℓ hv hℓv hℓne hxsh) with h | h
  · exact h
  · exfalso
    have hnz : (nzIdx v ℓ σ).Nonempty := nzIdx_nonempty hv hℓv hℓne
    obtain ⟨i0, hi0, hi0eq⟩ := Finset.exists_mem_eq_sup' hnz (fun i => loB s c σ v ℓ i x)
    obtain ⟨j0, hj0, hj0eq⟩ := Finset.exists_mem_eq_inf' hnz (fun i => hiB s c σ v ℓ i x)
    have hk0 : kernCoef v ℓ σ i0 ≠ 0 := (mem_nzIdx i0).mp hi0
    have hl0 : kernCoef v ℓ σ j0 ≠ 0 := (mem_nzIdx j0).mp hj0
    have hlo : loB s c σ v ℓ i0 x = htl s c σ v ℓ x := by
      rw [htl_eq s c σ v ℓ hnz x]; exact hi0eq.symm
    have hhi : hiB s c σ v ℓ j0 x = hth s c σ v ℓ x := by
      rw [hth_eq s c σ v ℓ hnz x]; exact hj0eq.symm
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
    have haff : ∀ (a b : ℝ) (x₀ y₀ : ℝ × ℝ), a + b = 1 →
        (loB s c σ v ℓ i0 - hiB s c σ v ℓ j0) (a • x₀ + b • y₀)
          = a * ((loB s c σ v ℓ i0 - hiB s c σ v ℓ j0) x₀)
            + b * ((loB s c σ v ℓ i0 - hiB s c σ v ℓ j0) y₀) := by
      intro a b x₀ y₀ hab
      simp only [Pi.sub_apply]
      rw [loB_affine s c σ v ℓ i0 a b hab x₀ y₀, hiB_affine s c σ v ℓ j0 a b hab x₀ y₀]
      ring
    have hxG : (loB s c σ v ℓ i0 - hiB s c σ v ℓ j0) x = 0 := by
      simp only [Pi.sub_apply]
      rw [hlo, hhi, h, sub_self]
    have hle : ∀ x' ∈ Metric.ball x ε, (loB s c σ v ℓ i0 - hiB s c σ v ℓ j0) x' ≤ 0 := by
      intro x' hx'
      obtain ⟨t', ht'⟩ :=
        (mem_shadow_iff s c σ hv hℓv hℓne x').mp (interior_subset (hball hx'))
      have c1 := (constraint_iff s c σ v ℓ hk0 x' t').mp (ht' i0)
      have c2 := (constraint_iff s c σ v ℓ hl0 x' t').mp (ht' j0)
      simp only [Pi.sub_apply]
      linarith [c1.1, c2.2]
    have hGzero : ∀ x' : ℝ × ℝ, loB s c σ v ℓ i0 x' = hiB s c σ v ℓ j0 x' := by
      intro x'
      have hgoal := affine_const_of_le_on_ball haff hxG hε hle x'
      simp only [Pi.sub_apply] at hgoal
      linarith
    have hcbox : c ∈ cbox s c σ := by
      intro j
      rw [sub_self, abs_zero]
      exact mul_nonneg (le_of_lt (Submission.boxSide_pos j)) (le_of_lt hs)
    have hcint : c ∈ interior (cbox s c σ) := by
      rw [interior_cbox_eq s c σ hs]
      intro j
      rw [sub_self, abs_zero]
      exact halfLen_pos s σ hs j
    have htight : |(sectionL v ℓ (pair v ℓ c)
        + loB s c σ v ℓ i0 (pair v ℓ c) • fibreDir v ℓ) (σ i0) - c (σ i0)| = halfLen s σ i0 := by
      rw [pt_coord s c σ v ℓ (pair v ℓ c) (loB s c σ v ℓ i0 (pair v ℓ c)) i0]
      exact abs_coord_loB s c σ v ℓ hs hk0 (pair v ℓ c)
    have hceq : c = sectionL v ℓ (pair v ℓ c)
        + loB s c σ v ℓ i0 (pair v ℓ c) • fibreDir v ℓ := by
      obtain ⟨tc, htc⟩ := exists_fibre_coord hv hℓv hℓne c
      have hcmem : sectionL v ℓ (pair v ℓ c) + tc • fibreDir v ℓ ∈ cbox s c σ := by
        rw [← htc]; exact hcbox
      have hcc := (mem_cbox_iff s c σ v ℓ (pair v ℓ c) tc).mp hcmem
      have c1 := (constraint_iff s c σ v ℓ hk0 (pair v ℓ c) tc).mp (hcc i0)
      have c2 := (constraint_iff s c σ v ℓ hl0 (pair v ℓ c) tc).mp (hcc j0)
      have hge := hGzero (pair v ℓ c)
      have htceq : tc = loB s c σ v ℓ i0 (pair v ℓ c) := by linarith [c1.1, c2.2, hge]
      have hfinal : sectionL v ℓ (pair v ℓ c) + tc • fibreDir v ℓ
          = sectionL v ℓ (pair v ℓ c) + loB s c σ v ℓ i0 (pair v ℓ c) • fibreDir v ℓ := by
        rw [htceq]
      exact htc.trans hfinal
    have hmem_eq : sectionL v ℓ (pair v ℓ c) + loB s c σ v ℓ i0 (pair v ℓ c) • fibreDir v ℓ = c :=
      hceq.symm
    have hint : sectionL v ℓ (pair v ℓ c)
        + loB s c σ v ℓ i0 (pair v ℓ c) • fibreDir v ℓ ∈ interior (cbox s c σ) := by
      rw [hmem_eq]
      exact hcint
    exact not_mem_interior_cbox_of_tight s c σ hs htight hint

/-- The strict form of a box constraint involving the fibre parameter. -/
theorem constraint_iff_lt (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) {i : Fin 3} (hk : kernCoef v ℓ σ i ≠ 0) (x : ℝ × ℝ) (t : ℝ) :
    |baseCoord s c σ v ℓ i x + t * kernCoef v ℓ σ i| < halfLen s σ i ↔
      loB s c σ v ℓ i x < t ∧ t < hiB s c σ v ℓ i x := by
  rw [loB, hiB]
  by_cases hk' : 0 < kernCoef v ℓ σ i
  · rw [if_pos hk', if_pos hk', abs_lt, div_lt_iff₀ hk', lt_div_iff₀ hk']
    constructor <;> intro hh <;> exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  · have hkneg : kernCoef v ℓ σ i < 0 := lt_of_le_of_ne (not_lt.mp hk') hk
    rw [if_neg hk', if_neg hk', abs_lt, div_lt_iff_of_neg hkneg, lt_div_iff_of_neg hkneg]
    constructor <;> intro hh <;> exact ⟨by linarith [hh.2], by linarith [hh.1]⟩

/-- The parametrisation sends the interior of the shadow into the interior of the box. -/
theorem Phi_interior (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) (hs : 0 < s) (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    {x : ℝ × ℝ} (hx : x ∈ interior (shadow s c σ v ℓ)) {τ : ℝ}
    (hτ : τ ∈ Set.Ioo (0:ℝ) 1) : Phi s c σ v ℓ x τ ∈ interior (cbox s c σ) := by
  have hlt := htl_lt_hth_of_mem_interior s c σ hs hv hℓv hℓne hx
  have hnz : (nzIdx v ℓ σ).Nonempty := nzIdx_nonempty hv hℓv hℓne
  rw [interior_cbox_eq s c σ hs]
  intro i
  rw [Phi_eq, pt_coord s c σ v ℓ x
    ((1 - τ) * htl s c σ v ℓ x + τ * hth s c σ v ℓ x) i]
  by_cases hk : kernCoef v ℓ σ i = 0
  · rw [hk, mul_zero, add_zero]
    exact strict_of_nzIdx_eq_zero s c σ hs hv hℓv hℓne hx hk
  · rw [constraint_iff_lt s c σ v ℓ hk]
    have h1 : loB s c σ v ℓ i x ≤ htl s c σ v ℓ x := by
      rw [htl_eq s c σ v ℓ hnz x]
      exact Finset.le_sup'_of_le (f := fun j => loB s c σ v ℓ j x)
        ((mem_nzIdx i).mpr hk) le_rfl
    have h2 : hth s c σ v ℓ x ≤ hiB s c σ v ℓ i x := by
      rw [hth_eq s c σ v ℓ hnz x]
      exact Finset.inf'_le_of_le (f := fun j => hiB s c σ v ℓ j x)
        ((mem_nzIdx i).mpr hk) le_rfl
    exact ⟨by nlinarith [h1, hlt, hτ.1], by nlinarith [h2, hlt, hτ.2]⟩


end Helpers

theorem fibre_model (s : ℝ) (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (v : LeanEval.KnotTheory.PardonDistortion.R3) (ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ)
    (hs : 0 < s) (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0) :
    Work.Drive.Final.Trough.fibreDir v ℓ ≠ 0 ∧ Work.Drive.Final.Trough.pair v ℓ (Work.Drive.Final.Trough.fibreDir v ℓ) = 0 ∧
      (∀ x : ℝ × ℝ, Work.Drive.Final.Trough.pair v ℓ (Work.Drive.Final.Trough.sectionL v ℓ x) = x) ∧
      Continuous (Work.Drive.Final.Trough.htl s c σ v ℓ) ∧ Continuous (Work.Drive.Final.Trough.hth s c σ v ℓ) ∧
      ConvexOn ℝ (Work.Drive.Final.Trough.shadow s c σ v ℓ) (Work.Drive.Final.Trough.htl s c σ v ℓ) ∧
      ConcaveOn ℝ (Work.Drive.Final.Trough.shadow s c σ v ℓ) (Work.Drive.Final.Trough.hth s c σ v ℓ) ∧
      (∀ x ∈ Work.Drive.Final.Trough.shadow s c σ v ℓ, Work.Drive.Final.Trough.htl s c σ v ℓ x ≤ Work.Drive.Final.Trough.hth s c σ v ℓ x) ∧
      (∀ y ∈ Work.Drive.Final.Trough.cbox s c σ, Work.Drive.Final.Trough.pair v ℓ y ∈ Work.Drive.Final.Trough.shadow s c σ v ℓ) ∧
      (∀ x ∈ Work.Drive.Final.Trough.shadow s c σ v ℓ, ∀ τ ∈ Set.Icc (0:ℝ) 1, Work.Drive.Final.Trough.Phi s c σ v ℓ x τ ∈ Work.Drive.Final.Trough.cbox s c σ) ∧
      (∀ x ∈ Work.Drive.Final.Trough.shadow s c σ v ℓ, ∀ y ∈ Work.Drive.Final.Trough.cbox s c σ, Work.Drive.Final.Trough.pair v ℓ y = x →
        ∃ τ ∈ Set.Icc (0:ℝ) 1, Work.Drive.Final.Trough.Phi s c σ v ℓ x τ = y) ∧
      (∀ x ∈ Work.Drive.Final.Trough.shadow s c σ v ℓ, ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ x' ∈ Work.Drive.Final.Trough.shadow s c σ v ℓ,
        ∀ τ' ∈ Set.Icc (0:ℝ) 1, Work.Drive.Final.Trough.Phi s c σ v ℓ x τ = Work.Drive.Final.Trough.Phi s c σ v ℓ x' τ' → x = x') ∧
      (∀ x ∈ Work.Drive.Final.Trough.shadow s c σ v ℓ, Work.Drive.Final.Trough.htl s c σ v ℓ x < Work.Drive.Final.Trough.hth s c σ v ℓ x →
        ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ τ' ∈ Set.Icc (0:ℝ) 1,
          Work.Drive.Final.Trough.Phi s c σ v ℓ x τ = Work.Drive.Final.Trough.Phi s c σ v ℓ x τ' → τ = τ') ∧
      (∀ x ∈ Work.Drive.Final.Trough.shadow s c σ v ℓ,
        Work.Drive.Final.Trough.Phi s c σ v ℓ x 0 ∈ frontier (Work.Drive.Final.Trough.cbox s c σ) ∧ Work.Drive.Final.Trough.Phi s c σ v ℓ x 1 ∈ frontier (Work.Drive.Final.Trough.cbox s c σ)) ∧
      (∀ x ∈ frontier (Work.Drive.Final.Trough.shadow s c σ v ℓ), ∀ τ ∈ Set.Icc (0:ℝ) 1,
        Work.Drive.Final.Trough.Phi s c σ v ℓ x τ ∈ frontier (Work.Drive.Final.Trough.cbox s c σ)) ∧
      (∀ x ∈ interior (Work.Drive.Final.Trough.shadow s c σ v ℓ), ∀ τ ∈ Set.Ioo (0:ℝ) 1,
        Work.Drive.Final.Trough.Phi s c σ v ℓ x τ ∈ interior (Work.Drive.Final.Trough.cbox s c σ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fibreDir_ne_zero hv hℓv hℓne
  · exact pair_fibreDir hv hℓv hℓne
  · intro x; exact sectionL_spec hv hℓv hℓne x
  · exact continuous_htl s c σ v ℓ hv hℓv hℓne
  · exact continuous_hth s c σ v ℓ hv hℓv hℓne
  · exact convexOn_htl s c σ v ℓ hv hℓv hℓne
  · exact concaveOn_hth s c σ v ℓ hv hℓv hℓne
  · intro x hx; exact htl_le_hth_of_mem_shadow s c σ v ℓ hv hℓv hℓne hx
  · intro y hy; exact ⟨y, hy, rfl⟩
  · intro x hx τ hτ; exact mem_cbox_Phi s c σ v ℓ hv hℓv hℓne hx hτ
  · intro x hx y hy hxy; exact exists_tau_Phi s c σ v ℓ hv hℓv hℓne hx hy hxy
  · intro x hx τ hτ x' hx' τ' hτ' h; exact Phi_inj s c σ v ℓ hv hℓv hℓne h
  · intro x hx hlt τ hτ τ' hτ' h; exact Phi_tau_inj s c σ v ℓ hv hℓv hℓne hlt h
  · intro x hx; exact Phi_mem_frontier_cbox s c σ v ℓ hs hv hℓv hℓne hx
  · intro x hx τ hτ; exact Phi_frontier_shadow s c σ v ℓ hv hℓv hℓne hx hτ
  · intro x hx τ hτ; exact Phi_interior s c σ v ℓ hs hv hℓv hℓne hx hτ



end

end Work.Drive.Final.Trough

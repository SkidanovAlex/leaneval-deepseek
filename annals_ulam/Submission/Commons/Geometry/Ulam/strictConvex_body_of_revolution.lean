import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped Pointwise RealInnerProductSpace BigOperators Topology

set_option autoImplicit false

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Commons.Geometry.Ulam

namespace strictConvexBodyOfRevolution

/-- The radial part of a vector in `ℝᵈ`, obtained by forgetting the first coordinate. -/
noncomputable def radialPart {d : ℕ} [NeZero d] (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ {i : Fin d // 0 < i} :=
  WithLp.toLp 2 (fun i : {i : Fin d // 0 < i} => x i.1)

/-- The squared Euclidean norm of the radial part. -/
noncomputable def radialSumSq {d : ℕ} [NeZero d] (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i ∈ Finset.Ioi (0 : Fin d), (x i)^2

lemma radialSumSq_eq_norm_sq [NeZero d] (x : ℝᵈ) :
    radialSumSq x = ‖radialPart x‖^2 := by
  unfold radialSumSq radialPart
  rw [EuclideanSpace.real_norm_sq_eq]
  symm
  rw [Finset.sum_subtype (s := Finset.Ioi (0 : Fin d)) (p := fun i : Fin d => 0 < i)]
  · simp

lemma radialPart_smul_add [NeZero d] (x y : ℝᵈ) (a b : ℝ) :
    radialPart (a • x + b • y) = a • radialPart x + b • radialPart y := by
  apply PiLp.ext
  intro i
  simp [radialPart]

lemma eq_of_coord0_and_radialPart_eq [NeZero d] {x y : ℝᵈ}
    (h0 : x 0 = y 0) (hr : radialPart x = radialPart y) : x = y := by
  apply PiLp.ext
  intro i
  by_cases hi : 0 < i
  · have h := congrArg (fun v : EuclideanSpace ℝ {i : Fin d // 0 < i} => v ⟨i, hi⟩) hr
    simpa [radialPart] using h
  · have hle : i ≤ 0 := not_lt.mp hi
    have hi0 : i = 0 := (nonpos_iff_eq_zero).mp hle
    rw [hi0]
    exact h0

lemma eq_of_coord0_and_sum_sq_zero [NeZero d] {x y : ℝᵈ}
    (h0 : x 0 = y 0)
    (hx : radialSumSq x = 0)
    (hy : radialSumSq y = 0) : x = y := by
  have hx_zero : ∀ i : Fin d, 0 < i → x i = 0 := by
    intro i hi
    have hx' := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.Ioi (0 : Fin d))
      (f := fun i : Fin d => (x i)^2) (by intro j hj; exact sq_nonneg _)).1
      (by simpa [radialSumSq] using hx)
    exact sq_eq_zero_iff.mp (hx' i (by simpa [Finset.mem_Ioi] using hi))
  have hy_zero : ∀ i : Fin d, 0 < i → y i = 0 := by
    intro i hi
    have hy' := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.Ioi (0 : Fin d))
      (f := fun i : Fin d => (y i)^2) (by intro j hj; exact sq_nonneg _)).1
      (by simpa [radialSumSq] using hy)
    exact sq_eq_zero_iff.mp (hy' i (by simpa [Finset.mem_Ioi] using hi))
  apply PiLp.ext
  intro i
  by_cases hi : 0 < i
  · rw [hx_zero i hi, hy_zero i hi]
  · have hle : i ≤ 0 := not_lt.mp hi
    have hi0 : i = 0 := (nonpos_iff_eq_zero).mp hle
    rw [hi0]
    exact h0

lemma combo_mem_Ioo_of_mem_Icc_of_lt {a b t s α β : ℝ}
    (ha : 0 < α) (hb : 0 < β) (hαβ : α + β = 1)
    (ht : t ∈ Set.Icc a b) (hs : s ∈ Set.Icc a b) (h : t < s) :
    α * t + β * s ∈ Set.Ioo a b := by
  have hβ' : 1 - β = α := by linarith
  have hgt : t < α * t + β * s := by
    have h1 : α * t + β * s - t = β * (s - t) := by
      calc α * t + β * s - t = β * (s - t) + (α + β - 1) * t := by ring
        _ = β * (s - t) := by rw [hαβ]; ring
    have hpos : 0 < β * (s - t) := mul_pos hb (sub_pos.mpr h)
    rw [← h1] at hpos
    linarith
  have hlt : α * t + β * s < s := by
    have h2 : s - (α * t + β * s) = α * (s - t) := by
      calc s - (α * t + β * s) = (1 - β) * s - α * t := by ring
        _ = α * s - α * t := by rw [hβ']
        _ = α * (s - t) := by ring
    have hpos : 0 < α * (s - t) := mul_pos ha (sub_pos.mpr h)
    rw [← h2] at hpos
    linarith
  exact ⟨lt_of_le_of_lt ht.1 hgt, lt_of_lt_of_le hlt hs.2⟩

lemma combo_mem_Ioo_of_mem_Icc_of_ne {a b t s α β : ℝ}
    (ha : 0 < α) (hb : 0 < β) (hαβ : α + β = 1)
    (ht : t ∈ Set.Icc a b) (hs : s ∈ Set.Icc a b) (h : t ≠ s) :
    α * t + β * s ∈ Set.Ioo a b := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact combo_mem_Ioo_of_mem_Icc_of_lt ha hb hαβ ht hs hlt
  · rw [add_comm]
    exact combo_mem_Ioo_of_mem_Icc_of_lt hb ha (by linarith) hs ht hgt

lemma eq_endpoints_of_mem_Icc_not_mem_Ioo {a b t : ℝ}
    (ht : t ∈ Set.Icc a b) (h : t ∉ Set.Ioo a b) : t = a ∨ t = b := by
  rw [Set.mem_Icc] at ht
  rw [Set.mem_Ioo] at h
  by_cases hta : t = a
  · exact Or.inl hta
  · have ha_lt : a < t := lt_of_le_of_ne ht.1 (Ne.symm hta)
    have htb : t = b := by
      by_contra hne
      have hlt : t < b := lt_of_le_of_ne ht.2 hne
      exact h ⟨ha_lt, hlt⟩
    exact Or.inr htb

lemma eq_of_body_endpoint [NeZero d] {R₁ R₂ : ℝ} {f : ℝ → ℝ}
    (hf_left : f (-R₁) = 0) (hf_right : f R₂ = 0)
    {x y : ℝᵈ} {t : ℝ}
    (hx0 : x 0 = t) (hy0 : y 0 = t)
    (hx : x 0 ∈ Set.Icc (-R₁) R₂ ∧ radialSumSq x ≤ (f (x 0))^2)
    (hy : y 0 ∈ Set.Icc (-R₁) R₂ ∧ radialSumSq y ≤ (f (y 0))^2)
    (ht : t = -R₁ ∨ t = R₂) : x = y := by
  rcases ht with rfl | rfl
  · have hSx0 : radialSumSq x = 0 := by
      have hnonneg : 0 ≤ radialSumSq x := by
        unfold radialSumSq
        exact Finset.sum_nonneg (by intro i hi; exact sq_nonneg _)
      have hle : radialSumSq x ≤ 0 := by
        have h := hx.2
        rw [hx0, hf_left] at h
        simpa using h
      exact le_antisymm hle hnonneg
    have hSy0 : radialSumSq y = 0 := by
      have hnonneg : 0 ≤ radialSumSq y := by
        unfold radialSumSq
        exact Finset.sum_nonneg (by intro i hi; exact sq_nonneg _)
      have hle : radialSumSq y ≤ 0 := by
        have h := hy.2
        rw [hy0, hf_left] at h
        simpa using h
      exact le_antisymm hle hnonneg
    exact eq_of_coord0_and_sum_sq_zero (by rw [hx0, hy0]) hSx0 hSy0
  · have hSx0 : radialSumSq x = 0 := by
      have hnonneg : 0 ≤ radialSumSq x := by
        unfold radialSumSq
        exact Finset.sum_nonneg (by intro i hi; exact sq_nonneg _)
      have hle : radialSumSq x ≤ 0 := by
        have h := hx.2
        rw [hx0, hf_right] at h
        simpa using h
      exact le_antisymm hle hnonneg
    have hSy0 : radialSumSq y = 0 := by
      have hnonneg : 0 ≤ radialSumSq y := by
        unfold radialSumSq
        exact Finset.sum_nonneg (by intro i hi; exact sq_nonneg _)
      have hle : radialSumSq y ≤ 0 := by
        have h := hy.2
        rw [hy0, hf_right] at h
        simpa using h
      exact le_antisymm hle hnonneg
    exact eq_of_coord0_and_sum_sq_zero (by rw [hx0, hy0]) hSx0 hSy0

lemma mem_interior_body_of_revolution [NeZero d] {R₁ R₂ : ℝ} {f : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Set.Icc (-R₁) R₂))
    {x : ℝᵈ}
    (hx0 : x 0 ∈ Set.Ioo (-R₁) R₂)
    (hrad : radialSumSq x < (f (x 0))^2) :
    x ∈ interior {x : ℝᵈ | x 0 ∈ Set.Icc (-R₁) R₂ ∧
      radialSumSq x ≤ (f (x 0))^2} := by
  let g : ℝᵈ → ℝ := fun w => radialSumSq w - (f (w 0))^2
  have hf_at : ContinuousAt f (x 0) := by
    exact hf_cont.continuousAt (Icc_mem_nhds hx0.1 hx0.2)
  have hg_cont : ContinuousAt g x := by
    unfold g radialSumSq
    fun_prop
  have hg_neg : g x < 0 := by
    unfold g
    linarith
  have h1 : {w : ℝᵈ | w 0 ∈ Set.Ioo (-R₁) R₂} ∈ 𝓝 x := by
    have hcoeff : ContinuousAt (fun w : ℝᵈ => w 0) x := by fun_prop
    exact hcoeff.preimage_mem_nhds (Ioo_mem_nhds hx0.1 hx0.2)
  have h2 : {w : ℝᵈ | g w < 0} ∈ 𝓝 x := by
    exact hg_cont.preimage_mem_nhds (isOpen_Iio.mem_nhds hg_neg)
  have hneigh : ({w : ℝᵈ | w 0 ∈ Set.Ioo (-R₁) R₂} ∩ {w : ℝᵈ | g w < 0}) ∈ 𝓝 x :=
    Filter.inter_mem h1 h2
  have hsub : ({w : ℝᵈ | w 0 ∈ Set.Ioo (-R₁) R₂} ∩ {w : ℝᵈ | g w < 0}) ⊆
      {x : ℝᵈ | x 0 ∈ Set.Icc (-R₁) R₂ ∧ radialSumSq x ≤ (f (x 0))^2} := by
    intro w hw
    have hw1 : w 0 ∈ Set.Ioo (-R₁) R₂ := hw.1
    have hw2 : g w < 0 := hw.2
    refine ⟨Set.Ioo_subset_Icc_self hw1, ?_⟩
    unfold g at hw2
    linarith
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset hneigh hsub)

end strictConvexBodyOfRevolution

open strictConvexBodyOfRevolution

lemma strictConvex_body_of_revolution [NeZero d] {R₁ R₂ : ℝ} {f : ℝ → ℝ}
    (hf_nonneg : ∀ t ∈ Set.Icc (-R₁) R₂, 0 ≤ f t)
    (hf_conc : StrictConcaveOn ℝ (Set.Icc (-R₁) R₂) f)
    (hf_cont : ContinuousOn f (Set.Icc (-R₁) R₂))
    (hf_left : f (-R₁) = 0) (hf_right : f R₂ = 0)
    (hf_pos : ∀ t ∈ Set.Ioo (-R₁) R₂, 0 < f t) :
    StrictConvex ℝ {x : ℝᵈ | x 0 ∈ Set.Icc (-R₁) R₂ ∧
      ∑ i > 0, (x i)^2 ≤ (f (x 0))^2} := by
  have _ := hf_pos
  change StrictConvex ℝ {x : ℝᵈ | x 0 ∈ Set.Icc (-R₁) R₂ ∧
      radialSumSq x ≤ (f (x 0))^2}
  intro x hx y hy hxy a b ha hb hab
  let z : ℝᵈ := a • x + b • y
  let t : ℝ := x 0
  let s : ℝ := y 0
  have htIcc : t ∈ Set.Icc (-R₁) R₂ := by simpa [t] using hx.1
  have hsIcc : s ∈ Set.Icc (-R₁) R₂ := by simpa [s] using hy.1
  have hx_norm_le : ‖radialPart x‖ ≤ f t := by
    have hnonneg : 0 ≤ f t := hf_nonneg t htIcc
    have hsq : ‖radialPart x‖^2 ≤ (f t)^2 := by
      simpa [t, radialSumSq_eq_norm_sq x] using hx.2
    exact (sq_le_sq₀ (norm_nonneg _) hnonneg).1 hsq
  have hy_norm_le : ‖radialPart y‖ ≤ f s := by
    have hnonneg : 0 ≤ f s := hf_nonneg s hsIcc
    have hsq : ‖radialPart y‖^2 ≤ (f s)^2 := by
      simpa [s, radialSumSq_eq_norm_sq y] using hy.2
    exact (sq_le_sq₀ (norm_nonneg _) hnonneg).1 hsq
  have hz0_eq : z 0 = a * t + b * s := by
    simp [z, t, s, smul_eq_mul]
  have hz0_Ioo : z 0 ∈ Set.Ioo (-R₁) R₂ := by
    by_cases hts : t = s
    · have hz0_t : z 0 = t := by
        calc z 0 = a * t + b * s := by simp [z, t, s, smul_eq_mul]
          _ = a * t + b * t := by rw [hts]
          _ = (a + b) * t := by ring
          _ = t := by rw [hab, one_mul]
      have ht_Ioo : t ∈ Set.Ioo (-R₁) R₂ := by
        by_contra hnot
        have h_endpoint : t = -R₁ ∨ t = R₂ :=
          eq_endpoints_of_mem_Icc_not_mem_Ioo htIcc hnot
        have hxy_eq : x = y := by
          exact eq_of_body_endpoint hf_left hf_right (by simp [t])
            (by simpa [s] using hts.symm) hx hy h_endpoint
        exact hxy hxy_eq
      simpa [hz0_t] using ht_Ioo
    · exact combo_mem_Ioo_of_mem_Icc_of_ne ha hb hab htIcc hsIcc hts
  have hz_rad_strict : radialSumSq z < (f (z 0))^2 := by
    by_cases hts : t = s
    · have hz0_t : z 0 = t := by
        calc z 0 = a * t + b * s := by simp [z, t, s, smul_eq_mul]
          _ = a * t + b * t := by rw [hts]
          _ = (a + b) * t := by ring
          _ = t := by rw [hab, one_mul]
      have hrad_ne : radialPart x ≠ radialPart y := by
        intro hrad_eq
        have hxy_eq : x = y := by
          exact eq_of_coord0_and_radialPart_eq (by simpa [t, s] using hts) hrad_eq
        exact hxy hxy_eq
      have hy_norm_le_t : ‖radialPart y‖ ≤ f t := by simpa [hts] using hy_norm_le
      have hnorm_lt : ‖radialPart z‖ < f t := by
        have hcombo := norm_combo_lt_of_ne (E := EuclideanSpace ℝ {i : Fin d // 0 < i})
          hx_norm_le hy_norm_le_t hrad_ne ha hb hab
        simpa [z, t, s, hts, radialPart_smul_add] using hcombo
      have hsq_lt : ‖radialPart z‖^2 < (f t)^2 := by
        exact (sq_lt_sq₀ (norm_nonneg _) (hf_nonneg t htIcc)).2 hnorm_lt
      simpa [z, hz0_t, radialSumSq_eq_norm_sq z] using hsq_lt
    · have hconc : a * f t + b * f s < f (a * t + b * s) := by
        simpa [smul_eq_mul] using hf_conc.2 htIcc hsIcc hts ha hb hab
      have hnonneg_combo : 0 ≤ a * f t + b * f s := by
        exact add_nonneg (mul_nonneg ha.le (hf_nonneg t htIcc))
          (mul_nonneg hb.le (hf_nonneg s hsIcc))
      have hfz_nonneg : 0 ≤ f (z 0) := by
        rw [hz0_eq]
        exact hf_nonneg (a * t + b * s) (by
          have := combo_mem_Ioo_of_mem_Icc_of_ne ha hb hab htIcc hsIcc hts
          exact Set.Ioo_subset_Icc_self this)
      have hz_norm_le : ‖radialPart z‖ ≤ a * f t + b * f s := by
        have hrad : radialPart z = a • radialPart x + b • radialPart y := by
          simp [z, radialPart_smul_add]
        calc
          ‖radialPart z‖ = ‖a • radialPart x + b • radialPart y‖ := by rw [hrad]
          _ ≤ ‖a • radialPart x‖ + ‖b • radialPart y‖ := norm_add_le _ _
          _ = a * ‖radialPart x‖ + b * ‖radialPart y‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg ha.le, Real.norm_of_nonneg hb.le]
          _ ≤ a * f t + b * f s := by
            exact add_le_add (mul_le_mul_of_nonneg_left hx_norm_le ha.le)
              (mul_le_mul_of_nonneg_left hy_norm_le hb.le)
      have hz_norm_sq_le : ‖radialPart z‖^2 ≤ (a * f t + b * f s)^2 := by
        exact (sq_le_sq₀ (norm_nonneg _) hnonneg_combo).2 hz_norm_le
      have hcombo_sq_lt : (a * f t + b * f s)^2 < (f (z 0))^2 := by
        rw [hz0_eq]
        exact (sq_lt_sq₀ hnonneg_combo hfz_nonneg).2 (by simpa [hz0_eq] using hconc)
      have hlt : ‖radialPart z‖^2 < (f (z 0))^2 := hz_norm_sq_le.trans_lt hcombo_sq_lt
      simpa [z, radialSumSq_eq_norm_sq z] using hlt
  exact mem_interior_body_of_revolution hf_cont hz0_Ioo hz_rad_strict

end Commons.Geometry.Ulam
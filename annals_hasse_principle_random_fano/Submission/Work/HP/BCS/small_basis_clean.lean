import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.lam_basic
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.MDEstimates.rk_projScale
import Submission.Work.HP.BCS.Setup
import Submission.Work.HP.BCS.close_span
import Submission.Work.HP.BCS.min_norm_sub
import Submission.Work.HP.BCS.shortest_vec

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

noncomputable section

namespace Work.HP.BCS

open Work.HP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Orthogonal projection onto the orthogonal complement of a line -/

/-- Orthogonal projection onto the orthogonal complement of `ℝ x`, as a linear map. -/
def projL {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : E) : E →ₗ[ℝ] E :=
  LinearMap.id - (‖x‖ ^ 2)⁻¹ • LinearMap.smulRight ((innerSL ℝ x).toLinearMap) x

lemma projL_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) : projL x y = y - ((‖x‖ ^ 2)⁻¹ * inner ℝ y x) • x := by
  simp [projL, LinearMap.smulRight_apply, smul_smul, real_inner_comm]

lemma inner_projL_left {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) : inner ℝ (projL x y) x = 0 := by
  rw [projL_apply, inner_sub_left]
  have h : inner ℝ (((‖x‖ ^ 2)⁻¹ * inner ℝ y x) • x) x
      = ((‖x‖ ^ 2)⁻¹ * inner ℝ y x) * (‖x‖ ^ 2 : ℝ) := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
  rw [h]
  by_cases hx : ‖x‖ = 0
  · rw [norm_eq_zero.mp hx]; simp
  · rw [show (‖x‖ ^ 2)⁻¹ * inner ℝ y x * (‖x‖ ^ 2 : ℝ) = inner ℝ y x by
      rw [mul_comm ((‖x‖ ^ 2)⁻¹) (inner ℝ y x), mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero 2 hx), mul_one]
    , sub_self]

lemma projL_self_eq_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x : E} (hx : x ≠ 0) : projL x x = 0 := by
  rw [projL_apply, real_inner_self_eq_norm_sq]
  rw [show (‖x‖ ^ 2)⁻¹ * ‖x‖ ^ 2 = 1 by
    rw [inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))], one_smul, sub_self]

lemma projL_add_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : E) (c : ℝ) (y : E) : projL x (y + c • x) = projL x y := by
  rw [map_add, map_smul]
  have : projL x x = 0 := by
    by_cases hx : x = 0
    · subst hx; simp
    · exact projL_self_eq_zero hx
  rw [this, smul_zero, add_zero]

lemma norm_sq_add_smulL {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : E) (c : ℝ) (y : E) :
    ‖projL x y + c • x‖ ^ 2 = ‖projL x y‖ ^ 2 + (c * ‖x‖) ^ 2 := by
  have horth : inner ℝ (projL x y) (c • x) = 0 := by
    rw [real_inner_smul_right, inner_projL_left, mul_zero]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (projL x y) (c • x) horth
  have h2 : ‖projL x y + c • x‖ ^ 2 = ‖projL x y‖ ^ 2 + ‖c • x‖ ^ 2 := by
    rw [sq, sq, sq, h]
  rw [h2, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, mul_pow]

lemma norm_projL_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) : ‖projL x y‖ ≤ ‖y‖ := by
  have hx : y = projL x y + ((‖x‖ ^ 2)⁻¹ * inner ℝ y x) • x := by
    rw [projL_apply]; abel
  have h := norm_sq_add_smulL x ((‖x‖ ^ 2)⁻¹ * inner ℝ y x) y
  rw [← hx] at h
  have h2 : ‖projL x y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg ((‖x‖ ^ 2)⁻¹ * inner ℝ y x * ‖x‖), h]
  simpa [abs_of_nonneg (norm_nonneg y), abs_of_nonneg (norm_nonneg (projL x y))]
    using sq_le_sq.mp h2

lemma projL_add_decomp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) : projL x y + ((‖x‖ ^ 2)⁻¹ * inner ℝ y x) • x = y := by
  rw [projL_apply]; abel

/-! ## The embedding `ℤ^ι → ℝ^ι` and `projScale` -/

lemma toEr_add (x y : ι → ℤ) : toEr (x + y) = toEr x + toEr y := by
  show toErLin (x + y) = toErLin x + toErLin y; rw [map_add]

lemma toEr_sub (x y : ι → ℤ) : toEr (x - y) = toEr x - toEr y := by
  show toErLin (x - y) = toErLin x - toErLin y; rw [map_sub]

lemma toEr_zsmul (m : ℤ) (x : ι → ℤ) : toEr (m • x) = m • toEr x := by
  show toErLin (m • x) = m • toErLin x; rw [map_smul]

private lemma inner_toEr_toEr (u y : ι → ℤ) : inner ℝ (toEr u) (toEr y) = (dotZ u y : ℝ) := by
  have h := Work.HP.BCS.inner_toE_toEr (toR u) y
  have h1 : toE (toR u) = toEr u := rfl
  rw [h1] at h
  rw [h, dotR]
  simp only [toR, dotZ_apply]
  push_cast
  rfl

lemma norm_sq_toEr (u : ι → ℤ) : ‖toEr u‖ ^ 2 = ((dotZ u u : ℤ) : ℝ) := by
  rw [norm_toEr u, eNorm_sq_eq]

lemma toEr_projScale (u y : ι → ℤ) (hu : u ≠ 0) :
    toEr (projScale u y) = ‖toEr u‖ ^ 2 • projL (toEr u) (toEr y) := by
  rw [projScale_apply, toEr_sub, toEr_zsmul, toEr_zsmul]
  rw [← Int.cast_smul_eq_zsmul ℝ (dotZ u u) (toEr y),
      ← Int.cast_smul_eq_zsmul ℝ (dotZ y u) (toEr u)]
  rw [projL_apply, inner_toEr_toEr y u, norm_sq_toEr]
  rw [smul_sub, smul_smul]
  have hD : ((dotZ u u : ℤ):ℝ) ≠ 0 := by
    rw [← eNorm_sq_eq u]; exact pow_ne_zero 2 (ne_of_gt (eNorm_pos_of_ne_zero hu))
  rw [show ((dotZ u u : ℤ):ℝ) * (((dotZ u u : ℤ):ℝ)⁻¹ * (dotZ y u : ℝ)) = (dotZ y u : ℝ) from by
    field_simp]

/-- `projScale u` is nonexpansive up to the factor `‖u‖²`. -/
lemma eNorm_projScale_le (u x : ι → ℤ) (hu : u ≠ 0) :
    eNorm (projScale u x) ≤ eNorm u ^ 2 * eNorm x := by
  have hDnn : (0:ℝ) ≤ ((dotZ u u : ℤ):ℝ) := by exact_mod_cast dotZ_self_nonneg u
  have h := norm_projL_le (toEr u) (toEr x)
  rw [norm_toEr x] at h
  rw [← norm_toEr (projScale u x), toEr_projScale u x hu, norm_smul, norm_sq_toEr u,
    Real.norm_of_nonneg hDnn, ← norm_toEr u, norm_sq_toEr u]
  exact mul_le_mul_of_nonneg_left h hDnn

lemma norm_projL_eq (u y : ι → ℤ) (hu : u ≠ 0) :
    ‖projL (toEr u) (toEr y)‖ = eNorm (projScale u y) / (eNorm u) ^ 2 := by
  have h := toEr_projScale u y hu
  have h2 : eNorm (projScale u y) = (eNorm u) ^ 2 * ‖projL (toEr u) (toEr y)‖ := by
    rw [← norm_toEr (projScale u y), h, norm_smul, norm_toEr u,
      Real.norm_of_nonneg (sq_nonneg _)]
  have hU : (eNorm u) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (eNorm_pos_of_ne_zero hu))
  rw [h2, eq_div_iff hU]
  ring

/-- Lifting bound: shifting `y` by the nearest integer multiple of `u` costs at most `‖u‖/2`
beyond the component orthogonal to `u`. -/
private lemma lift_bound (u y : ι → ℤ) (hu : u ≠ 0) (m : ℤ)
    (hm : |inner ℝ (toEr y) (toEr u) / ‖toEr u‖ ^ 2 - (m : ℝ)| ≤ 1 / 2) :
    eNorm (y - m • u) ≤ eNorm (projScale u y) / (eNorm u) ^ 2 + eNorm u / 2 := by
  set c : ℝ := (‖toEr u‖ ^ 2)⁻¹ * inner ℝ (toEr y) (toEr u) with hc
  have hc' : c = inner ℝ (toEr y) (toEr u) / ‖toEr u‖ ^ 2 := by
    rw [hc, div_eq_inv_mul]
  have hdec : toEr y = projL (toEr u) (toEr y) + c • toEr u :=
    (projL_add_decomp (toEr u) (toEr y)).symm
  have step : toEr y - (m : ℝ) • toEr u
      = projL (toEr u) (toEr y) + (c - (m : ℝ)) • toEr u := by
    conv_lhs => rw [hdec]
    rw [sub_eq_add_neg, add_assoc, ← neg_smul, ← add_smul, sub_eq_add_neg]
  have h1 : toEr (y - m • u) = projL (toEr u) (toEr y) + (c - (m : ℝ)) • toEr u := by
    rw [toEr_sub, toEr_zsmul, ← Int.cast_smul_eq_zsmul ℝ m (toEr u)]
    exact step
  have hmn : |c - (m : ℝ)| ≤ 1 / 2 := by rw [hc']; exact hm
  calc eNorm (y - m • u) = ‖toEr (y - m • u)‖ := (norm_toEr _).symm
    _ = ‖projL (toEr u) (toEr y) + (c - (m : ℝ)) • toEr u‖ := by rw [h1]
    _ ≤ ‖projL (toEr u) (toEr y)‖ + ‖(c - (m : ℝ)) • toEr u‖ := norm_add_le _ _
    _ = ‖projL (toEr u) (toEr y)‖ + |c - (m : ℝ)| * ‖toEr u‖ := by
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖projL (toEr u) (toEr y)‖ + (1 / 2) * ‖toEr u‖ := by
        gcongr
    _ = eNorm (projScale u y) / (eNorm u) ^ 2 + eNorm u / 2 := by
        rw [norm_projL_eq u y hu, norm_toEr u]
        ring


/-! ## `projScale u u = 0` -/

lemma projScale_self (u : ι → ℤ) : projScale u u = 0 := by
  rw [projScale_apply, sub_self]

/-! ## The real span of `L` equals the real span of `rk L` independent vectors -/

lemma spanE_eq_span_f (L : Submodule ℤ (ι → ℤ)) (f : Fin (rk L) → ι → ℤ)
    (hfL : ∀ j, f j ∈ L) (hfind : LinearIndependent ℤ f) :
    spanE L = Submodule.span ℝ (Set.range (fun j => toEr (f j))) := by
  have hle : Submodule.span ℝ (Set.range (fun j => toEr (f j))) ≤ spanE L := by
    rw [Submodule.span_le]
    rintro y ⟨j, rfl⟩
    exact Submodule.subset_span ⟨f j, hfL j, rfl⟩
  have hfli : LinearIndependent ℝ (fun j => toEr (f j)) := linearIndependent_toEr_cast hfind
  have h1 : Module.finrank ℝ ↥(Submodule.span ℝ (Set.range (fun j => toEr (f j)))) = rk L := by
    rw [finrank_span_eq_card hfli]; simp
  have h2 : Module.finrank ℝ ↥(spanE L) = rk L := by
    have h := finrank_spanE L (Module.finBasis ℤ L)
    rw [show Module.finrank ℤ ↥L = rk L from rfl] at h
    exact h
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [h1, h2])).symm

/-! ## The predicate "generated by its short vectors" -/

/-- `GenBy L N` says that `L` is generated as a `ℤ`-module by its elements of norm `≤ N`. -/
def GenBy (L : Submodule ℤ (ι → ℤ)) (N : ℝ) : Prop :=
  ∀ x ∈ L, x ∈ Submodule.span ℤ ((L : Set (ι → ℤ)) ∩ {v | eNorm v ≤ N})

/-- Every lattice of rank `≥ 1` is generated by its elements of norm `≤ 2 (rk L) λ_{rk L}`. -/
lemma genBy_of_lam (L : Submodule ℤ (ι → ℤ)) (hL : 1 ≤ rk L) :
    ∃ N : ℝ, 0 < N ∧ N ≤ 2 * (rk L : ℝ) * lam L (rk L) ∧ GenBy L N := by
  have hk : (0:ℝ) < lam L (rk L) := lam_pos L hL le_rfl
  obtain ⟨f, hfL, hfind, hfρ⟩ :=
    lam_witness L (le_refl (rk L)) (by linarith : lam L (rk L) < 2 * lam L (rk L))
  have hspan := spanE_eq_span_f L f hfL hfind
  set N : ℝ := ∑ j : Fin (rk L), eNorm (f j) with hN
  have hNpos : 0 < N := by
    rw [hN]
    refine Finset.sum_pos' (fun j _ => eNorm_nonneg _) ⟨⟨0, hL⟩, Finset.mem_univ _, ?_⟩
    exact eNorm_pos_of_ne_zero (hfind.ne_zero ⟨0, hL⟩)
  have hNle : N ≤ 2 * (rk L : ℝ) * lam L (rk L) := by
    rw [hN]
    calc ∑ j : Fin (rk L), eNorm (f j) ≤ ∑ j : Fin (rk L), 2 * lam L (rk L) :=
          Finset.sum_le_sum (fun j _ => hfρ j)
      _ = (rk L : ℝ) * (2 * lam L (rk L)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = 2 * (rk L : ℝ) * lam L (rk L) := by ring
  refine ⟨N, hNpos, hNle, ?_⟩
  intro x hxL
  by_contra hxnot
  obtain ⟨x₀, hx₀, hmin⟩ := min_norm_sub L
      (S := {v | v ∈ L ∧ v ∉ Submodule.span ℤ ((L : Set (ι → ℤ)) ∩ {v | eNorm v ≤ N})})
      ⟨x, hxL, hxnot⟩ (fun s hs => hs.1)
  have hx₀L : x₀ ∈ L := hx₀.1
  have hx₀not : x₀ ∉ Submodule.span ℤ ((L : Set (ι → ℤ)) ∩ {v | eNorm v ≤ N}) := hx₀.2
  have hmin' : ∀ t ∈ L, t ∉ Submodule.span ℤ
      ((L : Set (ι → ℤ)) ∩ {v | eNorm v ≤ N}) → eNorm x₀ ≤ eNorm t :=
    fun t htL ht => hmin t ⟨htL, ht⟩
  have hNlt : N < eNorm x₀ := by
    by_contra hle
    push Not at hle
    exact hx₀not (Submodule.subset_span ⟨hx₀L, hle⟩)
  have hx₀span : toEr x₀ ∈ spanE L := Submodule.subset_span ⟨x₀, hx₀L, rfl⟩
  have hcover : ∀ y ∈ spanE L, ∃ a ∈ L, ‖y - toEr a‖ ≤ (1 / 2) * N := by
    intro y hy
    have h := close_span L f hfL hspan y hy
    rw [hN]; exact h
  obtain ⟨a, haL, ha_close⟩ := hcover ((2:ℝ)⁻¹ • toEr x₀) (Submodule.smul_mem _ _ hx₀span)
  have hy_toEr : toEr (x₀ - (2:ℤ) • a) = (2:ℝ) • ((2:ℝ)⁻¹ • toEr x₀ - toEr a) := by
    rw [toEr_sub, toEr_zsmul, ← Int.cast_smul_eq_zsmul ℝ (2:ℤ) (toEr a)]
    rw [smul_sub, smul_smul, mul_inv_cancel₀ (by norm_num : (2:ℝ) ≠ 0), one_smul]
    simp
  have hy_norm_le : eNorm (x₀ - (2:ℤ) • a) ≤ N := by
    rw [← norm_toEr (x₀ - (2:ℤ) • a), hy_toEr, norm_smul,
      Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    nlinarith [ha_close, norm_nonneg ((2:ℝ)⁻¹ • toEr x₀ - toEr a)]
  have ha_lt : eNorm a < eNorm x₀ := by
    have hNlt' : N < ‖toEr x₀‖ := by rw [norm_toEr x₀]; exact hNlt
    have ha_norm : ‖toEr a‖ ≤ (1 / 2) * N + (1 / 2) * ‖toEr x₀‖ := by
      calc ‖toEr a‖ = ‖(toEr a - (2:ℝ)⁻¹ • toEr x₀) + (2:ℝ)⁻¹ • toEr x₀‖ := by
            congr 1; abel
        _ ≤ ‖toEr a - (2:ℝ)⁻¹ • toEr x₀‖ + ‖(2:ℝ)⁻¹ • toEr x₀‖ := norm_add_le _ _
        _ = ‖(2:ℝ)⁻¹ • toEr x₀ - toEr a‖ + (2:ℝ)⁻¹ * ‖toEr x₀‖ := by
            rw [norm_sub_rev, norm_smul,
              Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)]
        _ ≤ (1 / 2) * N + (1 / 2) * ‖toEr x₀‖ := by
            have h2 : (2:ℝ)⁻¹ = 1 / 2 := by norm_num
            linarith [ha_close, h2]
    rw [← norm_toEr a, ← norm_toEr x₀]
    nlinarith [ha_norm, hNlt', norm_nonneg (toEr x₀)]
  have ha_span : a ∈ Submodule.span ℤ ((L : Set (ι → ℤ)) ∩ {v | eNorm v ≤ N}) := by
    by_contra ha_not
    exact absurd (hmin' a haL ha_not) (not_le.mpr ha_lt)
  have hyL : x₀ - (2:ℤ) • a ∈ L :=
    Submodule.sub_mem L hx₀L (Submodule.smul_mem L (2:ℤ) haL)
  have hy_span : x₀ - (2:ℤ) • a ∈
      Submodule.span ℤ ((L : Set (ι → ℤ)) ∩ {v | eNorm v ≤ N}) := by
    by_contra hy_not
    exact absurd (hmin' (x₀ - (2:ℤ) • a) hyL hy_not)
      (not_le.mpr (lt_of_le_of_lt hy_norm_le hNlt))
  exact hx₀not (by
    have hxx : x₀ = (2:ℤ) • a + (x₀ - (2:ℤ) • a) := by abel
    rw [hxx]
    exact Submodule.add_mem
      (Submodule.span ℤ ((L : Set (ι → ℤ)) ∩ {v | eNorm v ≤ N}))
      (Submodule.smul_mem (Submodule.span ℤ ((L : Set (ι → ℤ)) ∩ {v | eNorm v ≤ N}))
        (2:ℤ) ha_span)
      hy_span)

/-- The projection `projScale u` maps `GenBy L N` to `GenBy (L.projScale) (‖u‖² N)`. -/
lemma genBy_projScale (L : Submodule ℤ (ι → ℤ)) (N : ℝ) (u : ι → ℤ) (huL : u ∈ L)
    (hu0 : u ≠ 0) (hN : 0 < N) (hgen : GenBy L N) :
    GenBy (Submodule.map (projScale u) L) (eNorm u ^ 2 * N) := by
  intro w hw
  rw [Submodule.mem_map] at hw
  obtain ⟨x, hxL, rfl⟩ := hw
  have hx' : projScale u x ∈ Submodule.map (projScale u)
      (Submodule.span ℤ ((L : Set (ι → ℤ)) ∩ {v | eNorm v ≤ N})) :=
    ⟨x, hgen x hxL, rfl⟩
  rw [Submodule.map_span] at hx'
  have hsub : projScale u '' ((L : Set (ι → ℤ)) ∩ {v | eNorm v ≤ N}) ⊆
      ((Submodule.map (projScale u) L : Submodule ℤ (ι → ℤ)) : Set (ι → ℤ)) ∩
        {v | eNorm v ≤ eNorm u ^ 2 * N} := by
    rintro y ⟨g, hg, rfl⟩
    refine ⟨Submodule.mem_map_of_mem (f := projScale u) hg.1, ?_⟩
    calc eNorm (projScale u g) ≤ eNorm u ^ 2 * eNorm g := eNorm_projScale_le u g hu0
      _ ≤ eNorm u ^ 2 * N :=
          mul_le_mul_of_nonneg_left hg.2 (by positivity)
  exact Submodule.span_mono hsub hx'

/-! ## Bases from short generating sets (induction on the rank) -/

/-- A rank-`k` lattice generated by its elements of norm `≤ N` has a `ℤ`-basis whose norms sum
to at most `4^k N`. -/
theorem exists_basis_genBy (k : ℕ) (L : Submodule ℤ (ι → ℤ)) (N : ℝ) (hN : 0 < N)
    (hk : rk L = k) (hgen : GenBy L N) :
    ∃ b : Module.Basis (Fin k) ℤ L,
      (∑ i, eNorm ((b i : L) : ι → ℤ)) ≤ (4:ℝ)^k * N := by
  induction k generalizing L N with
  | zero =>
    refine ⟨(Module.finBasis ℤ L).reindex (finCongr hk), ?_⟩
    have hsum0 : (∑ i : Fin 0,
        eNorm (((((Module.finBasis ℤ L).reindex (finCongr hk)) i : L) : ι → ℤ))) = 0 := by simp
    rw [hsum0, pow_zero, one_mul]
    exact le_of_lt hN
  | succ k ih =>
    have hLne : L ≠ ⊥ := by
      obtain ⟨gg, hggL, hggLI⟩ := exists_linIndep_card L (i := 1) (by omega : 1 ≤ rk L)
      exact (Submodule.ne_bot_iff L).mpr ⟨gg 0, hggL 0, hggLI.ne_zero 0⟩
    obtain ⟨u, huL, hu0, hshort⟩ := shortest_vec L hLne
    have huN : eNorm u ≤ N := by
      have hex : ∃ g ∈ (L : Set (ι → ℤ)) ∩ {v | eNorm v ≤ N}, g ≠ 0 := by
        by_contra h
        push Not at h
        have hbot : Submodule.span ℤ ((L : Set (ι → ℤ)) ∩ {v | eNorm v ≤ N}) ≤ ⊥ := by
          rw [Submodule.span_le]
          intro g hg
          rw [h g hg]
          exact (Submodule.mem_bot ℤ).mpr rfl
        exact hu0 ((Submodule.mem_bot ℤ).mp (hbot (hgen u huL)))
      obtain ⟨g, hg, hgne⟩ := hex
      exact le_trans (hshort g hg.1 hgne) hg.2
    set L' := Submodule.map (projScale u) L with hL'
    have hrk' : rk L' = k := by
      rw [hL', Work.HP.MDEstimates.rk_projScale L u huL hu0 hshort, hk]
      omega
    have hN' : 0 < eNorm u ^ 2 * N := by
      have := eNorm_pos_of_ne_zero hu0; positivity
    have hgen' : GenBy L' (eNorm u ^ 2 * N) := by
      rw [hL']; exact genBy_projScale L N u huL hu0 hN hgen
    obtain ⟨w, hwsum⟩ := ih L' (eNorm u ^ 2 * N) hN' hrk' hgen'
    have hlift : ∀ i : Fin k, ∃ x ∈ L, projScale u x = (w i : ι → ℤ) := fun i => by
      have hmem : (w i : ι → ℤ) ∈ Submodule.map (projScale u) L := by
        rw [← hL']; exact (w i).2
      rw [Submodule.mem_map] at hmem
      exact hmem
    choose x' hx'L hx'proj using hlift
    set m : Fin k → ℤ := fun i => round (inner ℝ (toEr (x' i)) (toEr u) / ‖toEr u‖ ^ 2) with hm
    set x : Fin k → ι → ℤ := fun i => x' i - m i • u with hxdef
    have hxL : ∀ i, x i ∈ L := fun i =>
      Submodule.sub_mem L (hx'L i) (Submodule.smul_mem L (m i) huL)
    have hxproj : ∀ i, projScale u (x i) = (w i : ι → ℤ) := by
      intro i
      show projScale u (x' i - m i • u) = (w i : ι → ℤ)
      rw [map_sub, map_smul, projScale_self, smul_zero, sub_zero, hx'proj i]
    have hxbound : ∀ i, eNorm (x i) ≤
        eNorm ((w i : L') : ι → ℤ) / (eNorm u) ^ 2 + eNorm u / 2 := by
      intro i
      have hmr : |inner ℝ (toEr (x' i)) (toEr u) / ‖toEr u‖ ^ 2 - ((m i : ℤ) : ℝ)| ≤ 1 / 2 :=
        abs_sub_round _
      have h := lift_bound u (x' i) hu0 (m i) hmr
      rwa [hx'proj i] at h
    set g : Fin (k+1) → L := Fin.cons ⟨u, huL⟩ (fun i => ⟨x i, hxL i⟩) with hg
    have hli : LinearIndependent ℤ g := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hcproj : ∑ i : Fin k, c i.succ • (w i : ι → ℤ) = 0 := by
        have happly : projScale u (∑ j : Fin (k+1), c j • (g j : ι → ℤ)) = 0 := by
          have h := congrArg (Submodule.subtype L) hc
          simp only [map_zero, map_sum, map_smul] at h
          have hgoal : (∑ j : Fin (k+1), c j • (g j : ι → ℤ)) = 0 := h
          rw [hgoal, map_zero]
        rw [map_sum, Fin.sum_univ_succ] at happly
        simp only [map_smul] at happly
        dsimp only [g] at happly
        simp only [Fin.cons_zero, Fin.cons_succ, Subtype.coe_mk, projScale_self, smul_zero,
          hxproj, zero_add] at happly
        simpa using happly
      have hwli := w.linearIndependent.map' (Submodule.subtype L')
        (Submodule.ker_subtype L')
      have hcsucc : ∀ i : Fin k, c i.succ = 0 :=
        Fintype.linearIndependent_iff.mp hwli (fun i => c i.succ) hcproj
      have hc0 : c 0 = 0 := by
        have h0 : c 0 • u = 0 := by
          have h1 : c 0 • (⟨u, huL⟩ : L) + ∑ i : Fin k, c i.succ • (⟨x i, hxL i⟩ : L) = 0 := by
            have h := hc
            rw [Fin.sum_univ_succ] at h
            simpa only [g, Fin.cons_zero, Fin.cons_succ] using h
          have h2 : c 0 • (⟨u, huL⟩ : L) = 0 := by
            rw [Finset.sum_eq_zero (fun i _ => by rw [hcsucc i, zero_smul]), add_zero] at h1
            exact h1
          have := congrArg (Submodule.subtype L) h2
          simpa using this
        rcases smul_eq_zero.mp h0 with h | h
        · exact h
        · exact absurd h hu0
      intro j
      rcases Fin.eq_zero_or_eq_succ j with h | ⟨i, rfl⟩
      · rw [h]; exact hc0
      · exact hcsucc i
    have hspan_top : Submodule.span ℤ (Set.range g) = ⊤ := by
      rw [Submodule.eq_top_iff']
      intro y
      have hyL : (y : ι → ℤ) ∈ L := y.2
      have hproj_mem : projScale u (y : ι → ℤ) ∈ L' :=
        Submodule.mem_map_of_mem (f := projScale u) hyL
      obtain ⟨z, hzeq⟩ : ∃ z : L', (z : ι → ℤ) = projScale u (y : ι → ℤ) :=
        ⟨⟨projScale u (y : ι → ℤ), hproj_mem⟩, rfl⟩
      have hzm : z ∈ Submodule.span ℤ (Set.range w) := by
        rw [w.span_eq]; exact Submodule.mem_top
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hzm
      have hceq : ∑ i, c i • (w i : ι → ℤ) = projScale u (y : ι → ℤ) := by
        have h1 : ((∑ i, c i • w i : L') : ι → ℤ) = projScale u (y : ι → ℤ) := by rw [hc, hzeq]
        simpa only [Submodule.coe_sum, Submodule.coe_smul] using h1
      have hzL : (y : ι → ℤ) - ∑ i, c i • x i ∈ L :=
        Submodule.sub_mem L hyL
          (Submodule.sum_mem L (fun i _ => Submodule.smul_mem L (c i) (hxL i)))
      have hzproj : projScale u ((y : ι → ℤ) - ∑ i, c i • x i) = 0 := by
        rw [map_sub, map_sum]
        rw [show (∑ i, projScale u (c i • x i)) = ∑ i, c i • (w i : ι → ℤ) from
          Finset.sum_congr rfl (fun i _ => by rw [map_smul, hxproj i])]
        rw [← hceq, sub_self]
      obtain ⟨m', hm'⟩ :=
        Work.HP.MDEstimates.projScale_eq_zero_imp L huL hu0 hshort hzL hzproj
      have hyeq : y = m' • g 0 + ∑ i, c i • g i.succ := by
        apply Subtype.ext
        show (y : ι → ℤ) = (Submodule.subtype L) (m' • g 0 + ∑ i, c i • g i.succ)
        rw [map_add, map_sum]
        have h1 : (Submodule.subtype L) (m' • g 0) = m' • u := by
          rw [map_smul, hg, Fin.cons_zero]; rfl
        have h2 : ∀ i : Fin k, (Submodule.subtype L) (c i • g i.succ) = c i • x i := fun i => by
          rw [map_smul, hg, Fin.cons_succ]; rfl
        rw [h1, Finset.sum_congr rfl (fun i _ => h2 i), ← hm']
        abel
      rw [hyeq]
      refine Submodule.add_mem (Submodule.span ℤ (Set.range g))
        (Submodule.smul_mem (Submodule.span ℤ (Set.range g)) m'
          (Submodule.subset_span (show g 0 ∈ Set.range g from ⟨0, rfl⟩))) ?_
      exact Submodule.sum_mem (Submodule.span ℤ (Set.range g))
        (fun i _ => Submodule.smul_mem (Submodule.span ℤ (Set.range g)) (c i)
          (Submodule.subset_span (show g i.succ ∈ Set.range g from ⟨i.succ, rfl⟩)))
    refine ⟨Module.Basis.mk hli (by rw [hspan_top]), ?_⟩
    have hbsum : (∑ i : Fin (k+1),
        eNorm ((((Module.Basis.mk hli (by rw [hspan_top])) i : L) : ι → ℤ)))
        = ∑ j : Fin (k+1), eNorm ((g j : L) : ι → ℤ) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Module.Basis.coe_mk]
    rw [hbsum, Fin.sum_univ_succ]
    dsimp only [g]
    simp only [Fin.cons_zero, Fin.cons_succ, Subtype.coe_mk]
    have hsum_x : ∑ i : Fin k, eNorm (x i) ≤ (4:ℝ)^k * N + (k:ℝ) * (N/2) := by
      calc ∑ i : Fin k, eNorm (x i)
          ≤ ∑ i : Fin k, (eNorm ((w i : L') : ι → ℤ) / (eNorm u)^2 + eNorm u/2) :=
            Finset.sum_le_sum (fun i _ => hxbound i)
        _ = (∑ i : Fin k, eNorm ((w i : L') : ι → ℤ)) / (eNorm u)^2 + (k:ℝ) * (eNorm u/2) := by
            rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul]
        _ ≤ ((4:ℝ)^k * (eNorm u^2 * N)) / (eNorm u)^2 + (k:ℝ) * (N/2) := by
            apply add_le_add
            · exact div_le_div_of_nonneg_right hwsum (by positivity)
            · exact mul_le_mul_of_nonneg_left (by linarith [huN]) (by positivity)
        _ = (4:ℝ)^k * N + (k:ℝ) * (N/2) := by
            rw [show (4:ℝ)^k * (eNorm u^2 * N) = ((4:ℝ)^k * N) * (eNorm u)^2 by ring,
              mul_div_cancel_right₀ _ (pow_ne_zero 2 (ne_of_gt (eNorm_pos_of_ne_zero hu0)))]
    have harith : (1:ℝ) + (4:ℝ)^k + (k:ℝ)/2 ≤ (4:ℝ)^(k+1) := by
      have hP1 : (1:ℝ) ≤ (4:ℝ)^k := one_le_pow₀ (by norm_num)
      have hkP : (k:ℝ) ≤ (4:ℝ)^k := by
        have h1 : (k:ℝ) < (2:ℝ)^k := by exact_mod_cast Nat.lt_two_pow_self (n := k)
        have h2 : (2:ℝ)^k ≤ (4:ℝ)^k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
        linarith
      rw [pow_succ]
      nlinarith [hP1, hkP]
    calc eNorm u + ∑ i : Fin k, eNorm (x i)
        ≤ N + ((4:ℝ)^k * N + (k:ℝ) * (N/2)) := by linarith [huN, hsum_x]
      _ = (1 + (4:ℝ)^k + (k:ℝ)/2) * N := by ring
      _ ≤ (4:ℝ)^(k+1) * N := mul_le_mul_of_nonneg_right harith (le_of_lt hN)

theorem small_basis_clean {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : Submodule ℤ (ι → ℤ)), 1 ≤ rk L →
      ∃ b : Module.Basis (Fin (rk L)) ℤ L,
        (∑ i, eNorm ((b i : ι → ℤ))) ≤ C * lam L (rk L) := by
  refine ⟨2 * ((Fintype.card ι : ℝ) + 1) * 4 ^ (Fintype.card ι), ?_, ?_⟩
  · positivity
  · intro L hL
    obtain ⟨N, hNpos, hNle, hgen⟩ := genBy_of_lam L hL
    obtain ⟨b, hb⟩ := exists_basis_genBy (rk L) L N hNpos rfl hgen
    refine ⟨b, ?_⟩
    have hlam_nn : 0 ≤ lam L (rk L) := lam_nonneg L (rk L)
    have hrk_le : rk L ≤ Fintype.card ι := by
      have h := Submodule.finrank_le L
      rwa [Module.finrank_fintype_fun_eq_card ℤ] at h
    calc ∑ i, eNorm ((b i : ι → ℤ)) ≤ (4:ℝ)^(rk L) * N := hb
      _ ≤ (4:ℝ)^(rk L) * (2 * (rk L : ℝ) * lam L (rk L)) :=
          mul_le_mul_of_nonneg_left hNle (by positivity)
      _ ≤ (4:ℝ)^(Fintype.card ι) * (2 * ((Fintype.card ι : ℝ) + 1) * lam L (rk L)) := by
          apply mul_le_mul
          · exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 4) hrk_le
          · apply mul_le_mul_of_nonneg_right _ hlam_nn
            exact mul_le_mul_of_nonneg_left
              (by exact_mod_cast (show rk L ≤ Fintype.card ι + 1 by omega))
              (by norm_num : (0:ℝ) ≤ 2)
          · exact mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hlam_nn
          · positivity
      _ = (2 * ((Fintype.card ι : ℝ) + 1) * 4 ^ (Fintype.card ι)) * lam L (rk L) := by ring

end Work.HP.BCS

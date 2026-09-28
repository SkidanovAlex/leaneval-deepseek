import Mathlib
import Submission.Work.HP.lam_basic
import Submission.Work.HP.Q44Child.lam_attained
import Submission.Work.HP.Q44Child.basis_ext
import Submission.Work.HP.BCS.lat_span_u_zsmul
import Submission.Work.HP.BCS.shortest_vec
import Submission.Work.Q44Geom.exists_completion_of_shortest
import Submission.Work.Q44Geom.projU_le_lam_two

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Work.Q44Geom

open Work.HP

/-! ## helper lemmas -/

lemma exists_int_close_rev (t : ℝ) : ∃ k : ℤ, |t - (k : ℝ)| ≤ 1 / 2 := by
  refine ⟨⌊t + 1/2⌋, ?_⟩
  have h1 : ((⌊t + 1/2⌋ : ℤ) : ℝ) ≤ t + 1/2 := Int.floor_le _
  have h2 : t + 1/2 < ((⌊t + 1/2⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  rw [abs_le]; constructor <;> linarith

/-- Pythagoras decomposition for the orthogonal projection onto `u^⊥`. -/
lemma norm_sq_eq_projU_sq_add {u v : EuclideanSpace ℝ (Fin 5)} (hu : u ≠ 0) :
    ‖v‖ ^ 2 = ‖Work.HP.projU u v‖ ^ 2 + (inner ℝ v u / ‖u‖) ^ 2 := by
  have h : v = Work.HP.projU u v + (inner ℝ v u / ‖u‖ ^ 2) • u := by
    rw [Work.HP.projU_apply, div_eq_inv_mul]; abel
  conv_lhs => rw [h]
  rw [Work.HP.norm_sq_add_smul' u (inner ℝ v u / ‖u‖ ^ 2) v]
  have hnorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  congr 1
  rw [div_mul_eq_mul_div]
  field_simp


theorem exists_gen_pair_lam :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : Submodule ℤ (Fin 5 → ℤ)), Work.HP.rk N = 2 →
      ∃ x y : Fin 5 → ℤ, x ∈ N ∧ y ∈ N ∧ N = Submodule.span ℤ {x, y} ∧
        Work.HP.eNorm x ≤ C * Work.HP.lam N 1 ∧ Work.HP.eNorm y ≤ C * Work.HP.lam N 2 := by
  refine ⟨2, by norm_num, fun N hN => ?_⟩
  have hbot : N ≠ ⊥ := by
    rintro rfl
    simp [Work.HP.rk] at hN
  obtain ⟨x, hxN, hx0, hxmin⟩ := Work.HP.BCS.shortest_vec N hbot
  have hx_le₁ : Work.HP.eNorm x ≤ Work.HP.lam N 1 := by
    obtain ⟨f, hfN, hfI, hfρ⟩ := Work.HP.Q44Child.lam_attained N 1 (by norm_num) (by omega)
    exact (hxmin (f 0) (hfN 0) (hfI.ne_zero 0)).trans (by simpa using hfρ 0)
  obtain ⟨w, hwN, hspan⟩ := exists_completion_of_shortest N hN x hxN hx0 hxmin
  have hperp : ‖Work.HP.projU (Work.HP.Q44Child.toE x) (Work.HP.Q44Child.toE w)‖ ≤
      Work.HP.lam N 2 := projU_le_lam_two N hN x w hxN hwN hx0 hspan
  have hX0 : Work.HP.Q44Child.toE x ≠ 0 := fun h =>
    hx0 (Work.HP.Q44Child.toE_injective (by simpa using h))
  have hXpos : 0 < ‖Work.HP.Q44Child.toE x‖ := norm_pos_iff.mpr hX0
  have hX2pos : 0 < ‖Work.HP.Q44Child.toE x‖ ^ 2 := by positivity
  obtain ⟨k, hk⟩ := exists_int_close_rev
    (inner ℝ (Work.HP.Q44Child.toE x) (Work.HP.Q44Child.toE w) / ‖Work.HP.Q44Child.toE x‖ ^ 2)
  set n : ℤ := -k with hn
  have hto : Work.HP.Q44Child.toE (w + n • x)
      = Work.HP.Q44Child.toE w + (n : ℝ) • Work.HP.Q44Child.toE x := by
    rw [map_add, map_smul, Int.cast_smul_eq_zsmul]
  have hinner : inner ℝ (Work.HP.Q44Child.toE x) (Work.HP.Q44Child.toE (w + n • x))
      = inner ℝ (Work.HP.Q44Child.toE x) (Work.HP.Q44Child.toE w)
        + (n : ℝ) * ‖Work.HP.Q44Child.toE x‖ ^ 2 := by
    rw [hto, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hq : inner ℝ (Work.HP.Q44Child.toE x) (Work.HP.Q44Child.toE (w + n • x))
      = ‖Work.HP.Q44Child.toE x‖ ^ 2 * (inner ℝ (Work.HP.Q44Child.toE x) (Work.HP.Q44Child.toE w)
          / ‖Work.HP.Q44Child.toE x‖ ^ 2 - (k : ℝ)) := by
    rw [hinner, hn]
    push_cast
    rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt hX2pos)]
    ring
  have hbd : |inner ℝ (Work.HP.Q44Child.toE x) (Work.HP.Q44Child.toE (w + n • x))|
      ≤ ‖Work.HP.Q44Child.toE x‖ ^ 2 / 2 := by
    rw [hq, abs_mul, abs_of_nonneg (sq_nonneg _)]
    calc ‖Work.HP.Q44Child.toE x‖ ^ 2
          * |inner ℝ (Work.HP.Q44Child.toE x) (Work.HP.Q44Child.toE w)
              / ‖Work.HP.Q44Child.toE x‖ ^ 2 - (k : ℝ)|
        ≤ ‖Work.HP.Q44Child.toE x‖ ^ 2 * (1 / 2) :=
          mul_le_mul_of_nonneg_left hk (sq_nonneg _)
      _ = ‖Work.HP.Q44Child.toE x‖ ^ 2 / 2 := by ring
  have hperp' : ‖Work.HP.projU (Work.HP.Q44Child.toE x) (Work.HP.Q44Child.toE (w + n • x))‖
      ≤ Work.HP.lam N 2 := by
    rw [hto, Work.HP.projU_add_smul]
    exact hperp
  have hx_le₂ : Work.HP.eNorm x ≤ Work.HP.lam N 2 :=
    hx_le₁.trans (Work.HP.lam_mono N (by norm_num) (by omega))
  have hlam2 : 0 ≤ Work.HP.lam N 2 := Work.HP.lam_nonneg N 2
  have hY : ‖Work.HP.Q44Child.toE (w + n • x)‖ ≤ 2 * Work.HP.lam N 2 := by
    have hpyth := norm_sq_eq_projU_sq_add (u := Work.HP.Q44Child.toE x)
      (v := Work.HP.Q44Child.toE (w + n • x)) hX0
    have hpar : (inner ℝ (Work.HP.Q44Child.toE (w + n • x)) (Work.HP.Q44Child.toE x)
        / ‖Work.HP.Q44Child.toE x‖) ^ 2 ≤ (Work.HP.lam N 2) ^ 2 / 4 := by
      have hkey : |inner ℝ (Work.HP.Q44Child.toE (w + n • x)) (Work.HP.Q44Child.toE x)
          / ‖Work.HP.Q44Child.toE x‖| ≤ Work.HP.lam N 2 / 2 := by
        rw [abs_div, abs_of_nonneg (norm_nonneg _)]
        rw [div_le_iff₀ hXpos]
        calc |inner ℝ (Work.HP.Q44Child.toE (w + n • x)) (Work.HP.Q44Child.toE x)|
            = |inner ℝ (Work.HP.Q44Child.toE x) (Work.HP.Q44Child.toE (w + n • x))| := by
              rw [real_inner_comm]
          _ ≤ ‖Work.HP.Q44Child.toE x‖ ^ 2 / 2 := hbd
          _ = ‖Work.HP.Q44Child.toE x‖ * (‖Work.HP.Q44Child.toE x‖ / 2) := by ring
          _ ≤ ‖Work.HP.Q44Child.toE x‖ * (Work.HP.lam N 2 / 2) := by
              refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
              rw [Work.HP.Q44Child.norm_toE]
              linarith
          _ = Work.HP.lam N 2 / 2 * ‖Work.HP.Q44Child.toE x‖ := by ring
      rw [show (inner ℝ (Work.HP.Q44Child.toE (w + n • x)) (Work.HP.Q44Child.toE x)
          / ‖Work.HP.Q44Child.toE x‖) ^ 2
          = |inner ℝ (Work.HP.Q44Child.toE (w + n • x)) (Work.HP.Q44Child.toE x)
              / ‖Work.HP.Q44Child.toE x‖| ^ 2 from (sq_abs _).symm]
      calc |inner ℝ (Work.HP.Q44Child.toE (w + n • x)) (Work.HP.Q44Child.toE x)
            / ‖Work.HP.Q44Child.toE x‖| ^ 2
          ≤ (Work.HP.lam N 2 / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hkey 2
        _ = (Work.HP.lam N 2) ^ 2 / 4 := by ring
    have h1 : ‖Work.HP.projU (Work.HP.Q44Child.toE x) (Work.HP.Q44Child.toE (w + n • x))‖ ^ 2
        ≤ (Work.HP.lam N 2) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hperp' 2
    have hsq : ‖Work.HP.Q44Child.toE (w + n • x)‖ ^ 2 ≤ (2 * Work.HP.lam N 2) ^ 2 := by
      rw [hpyth]; nlinarith [hlam2]
    have h2l : 0 ≤ 2 * Work.HP.lam N 2 := by linarith
    have hs := (sq_le_sq).mp hsq
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg h2l] at hs
  have hspan_y : N = Submodule.span ℤ ({x, w + n • x} : Set (Fin 5 → ℤ)) := by
    rw [hspan]
    apply le_antisymm
    · rw [Submodule.span_le]
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with hv | hv
      · rw [hv]
        exact Submodule.subset_span (by simp)
      · rw [hv]
        have hrepr : w = (w + n • x) + (-n) • x := by
          rw [add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]
        rw [hrepr]
        exact Submodule.add_mem _ (Submodule.subset_span (by simp))
          (Submodule.smul_mem _ (-n) (Submodule.subset_span (by simp)))
    · rw [Submodule.span_le]
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with hv | hv
      · rw [hv]
        exact Submodule.subset_span (by simp)
      · rw [hv]
        exact Submodule.add_mem _ (Submodule.subset_span (by simp))
          (Submodule.smul_mem _ n (Submodule.subset_span (by simp)))
  refine ⟨x, w + n • x, hxN, Submodule.add_mem _ hwN (Submodule.smul_mem _ _ hxN),
    hspan_y, ?_, ?_⟩
  · have h1 : 0 < Work.HP.lam N 1 := Work.HP.lam_pos N (i := 1) (by norm_num) (by omega)
    linarith
  · have := Work.HP.Q44Child.norm_toE (w + n • x)
    linarith

end Work.Q44Geom

import Mathlib
import Submission.Work.HP.BCSDefs

/-!
# `Work.HP.BCS.sMin_succ_le_two_mul_sMin_proj`

The comparison of successive minima under the orthogonal projection onto `u^⊥`:
if `u ≠ 0` is a shortest vector of the lattice `Λ ⊆ ℝ^ι` and `projU u` is the orthogonal
projection onto `u^⊥`, then for every `j ≥ 1` for which the projected lattice has `j`
independent elements,

`λ_{j+1}(Λ) ≤ 2 · λ_j(Λ.map (projU u))`.

The factor `2` comes from two places: (i) the shortest vector has `‖u‖ ≤ 2 λ_j(π Λ)` because
lifting a projected vector `y` to `Λ` and reducing modulo `ℤu` produces a nonzero lattice vector
of norm at most `‖y‖ + ‖u‖/2`; (ii) the same reduction produces a lift of norm at most
`‖y‖ + ‖u‖/2`, and `j` such lifts together with `u` are linearly independent.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP.BCS

open Work.HP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every real number is within `1/2` of an integer. -/
private lemma bcs_round_half (x : ℝ) : ∃ k : ℤ, |x - (k : ℝ)| ≤ 1 / 2 := by
  refine ⟨⌊x + 1 / 2⌋, ?_⟩
  have h1 : ((⌊x + 1 / 2⌋ : ℤ) : ℝ) ≤ x + 1 / 2 := Int.floor_le _
  have h2 : x + 1 / 2 < ((⌊x + 1 / 2⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  rw [abs_le]
  constructor <;> linarith

/-- The orthogonal projection onto `u^⊥` is idempotent. -/
private lemma bcs_projU_idem (u x : EuclideanSpace ℝ ι) :
    projU u (projU u x) = projU u x := by
  rw [projU_apply u (projU u x), inner_projU_left u x, mul_zero, zero_smul, sub_zero]

/-- **Lifting a projected vector.**  Every `y` in the projected lattice `Λ.map (projUZ u)`
has a lift `y' ∈ Λ` with the same projection and with `‖y'‖ ≤ ‖y‖ + ‖u‖/2`: reduce any
preimage modulo a nearest integer multiple of `u`. -/
private lemma bcs_exists_lift_projU (Λ : Submodule ℤ (EuclideanSpace ℝ ι))
    {u : EuclideanSpace ℝ ι} (hu : u ∈ Λ) (hu0 : u ≠ 0) {y : EuclideanSpace ℝ ι}
    (hy : y ∈ Λ.map (projUZ u)) :
    ∃ y' ∈ Λ, projU u y' = y ∧ ‖y'‖ ≤ ‖y‖ + ‖u‖ / 2 := by
  obtain ⟨x, hxΛ, hx⟩ := Submodule.mem_map.mp hy
  have hxu : projU u x = y := hx
  have hyproj : projU u y = y := by
    rw [← hxu, projU_apply u (projU u x), inner_projU_left u x, mul_zero, zero_smul, sub_zero]
  have hzero : projU u (x - y) = 0 := by rw [map_sub, hxu, hyproj, sub_self]
  have hmem : x - y ∈ Submodule.span ℝ {u} := (projU_eq_zero_iff u hu0 (x - y)).mp hzero
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c • u = x - y := Submodule.mem_span_singleton.mp hmem
  obtain ⟨m, hm⟩ := bcs_round_half c
  refine ⟨x - (m : ℤ) • u, ?_, ?_, ?_⟩
  · exact Submodule.sub_mem _ hxΛ (Submodule.smul_mem _ (m : ℤ) hu)
  · rw [map_sub, hxu]
    have hm' : (m : ℤ) • u = (m : ℝ) • u := by rw [← Int.cast_smul_eq_zsmul ℝ m u]
    rw [hm', map_smul, projU_self_eq_zero u hu0, smul_zero, sub_zero]
  · have hyx : x - y = c • u := hc.symm
    have hx' : x = y + c • u := by rw [← hyx]; abel
    have hxy : x - (m : ℤ) • u = y + (c - (m : ℝ)) • u := by
      rw [hx']
      have hm' : (m : ℤ) • u = (m : ℝ) • u := by rw [← Int.cast_smul_eq_zsmul ℝ m u]
      rw [hm']
      module
    rw [hxy]
    calc ‖y + (c - (m : ℝ)) • u‖ ≤ ‖y‖ + ‖(c - (m : ℝ)) • u‖ := norm_add_le _ _
      _ = ‖y‖ + |c - (m : ℝ)| * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖y‖ + (1 / 2) * ‖u‖ := by
          have := mul_le_mul_of_nonneg_right hm (norm_nonneg u); linarith
      _ = ‖y‖ + ‖u‖ / 2 := by ring

/-- If `u` is a shortest nonzero vector of `Λ`, then the `j`-th successive minimum of the
projected lattice is at least `‖u‖/2`, hence `‖u‖ ≤ 2 λ_j(π Λ)`. -/
private lemma bcs_norm_u_le_two_mul_sMin_map (Λ : Submodule ℤ (EuclideanSpace ℝ ι))
    {u : EuclideanSpace ℝ ι} (hu : u ∈ Λ) (hu0 : u ≠ 0)
    (hmin : ∀ x ∈ Λ, x ≠ 0 → ‖u‖ ≤ ‖x‖) {j : ℕ} (hj : 1 ≤ j)
    (hne : (sMinSet (Λ.map (projUZ u)) j).Nonempty) :
    ‖u‖ ≤ 2 * sMin (Λ.map (projUZ u)) j := by
  have hne1 : ∃ f : Fin j → EuclideanSpace ℝ ι,
      (∀ k, f k ∈ Λ.map (projUZ u)) ∧ LinearIndependent ℤ f := by
    obtain ⟨s, -, f, hfM, hfind, -⟩ := hne
    exact ⟨f, hfM, hfind⟩
  have hkey : ‖u‖ / 2 ≤ sMin (Λ.map (projUZ u)) j := by
    refine le_sMin_of_forall hne1 ?_
    intro r hr0 hr
    obtain ⟨f, hfM, hfind, hfr⟩ := hr
    have hf0 : f ⟨0, by omega⟩ ≠ 0 := hfind.ne_zero ⟨0, by omega⟩
    obtain ⟨y', hy'Λ, hy'proj, hy'norm⟩ :=
      bcs_exists_lift_projU Λ hu hu0 (hfM ⟨0, by omega⟩)
    have hy'ne : y' ≠ 0 := by
      intro h0; rw [h0, map_zero] at hy'proj; exact hf0 hy'proj.symm
    have h1 : ‖u‖ ≤ ‖y'‖ := hmin y' hy'Λ hy'ne
    have h3 : ‖f ⟨0, by omega⟩‖ ≤ r := hfr ⟨0, by omega⟩
    linarith
  linarith

theorem sMin_succ_le_two_mul_sMin_proj (ι : Type) [Fintype ι] [DecidableEq ι] (Λ : Submodule ℤ (EuclideanSpace ℝ ι))
    {u : EuclideanSpace ℝ ι} (hu : u ∈ Λ) (hu0 : u ≠ 0)
    (hmin : ∀ x ∈ Λ, x ≠ 0 → ‖u‖ ≤ ‖x‖) {j : ℕ} (hj : 1 ≤ j)
    (hne : (sMinSet (Λ.map (projUZ u)) j).Nonempty) :
    sMin Λ (j + 1) ≤ 2 * sMin (Λ.map (projUZ u)) j := by
  have hu_le : ‖u‖ ≤ 2 * sMin (Λ.map (projUZ u)) j :=
    bcs_norm_u_le_two_mul_sMin_map Λ hu hu0 hmin hj hne
  have hkey : ‖u‖ / 2 ≤ sMin (Λ.map (projUZ u)) j := by linarith
  have ha : (0 : ℝ) ≤ 2 * sMin (Λ.map (projUZ u)) j := by
    have := sMin_nonneg (Λ := Λ.map (projUZ u)) j; linarith
  refine sMin_le_of_forall_eps ha ?_
  intro ε hε
  have hlt : sInf (sMinSet (Λ.map (projUZ u)) j) < sMin (Λ.map (projUZ u)) j + ε :=
    lt_add_of_pos_right _ hε
  obtain ⟨s, ⟨hs0, f, hfM, hfind, hfs⟩, hslt⟩ := exists_lt_of_csInf_lt hne hlt
  have hlift : ∀ k : Fin j, ∃ y' ∈ Λ, projU u y' = f k ∧ ‖y'‖ ≤ ‖f k‖ + ‖u‖ / 2 :=
    fun k => bcs_exists_lift_projU Λ hu hu0 (hfM k)
  choose y hyΛ hyproj hynorm using hlift
  let g : Fin (j + 1) → EuclideanSpace ℝ ι := Fin.cons u y
  have hg0 : g 0 = u := rfl
  have hgs : ∀ i : Fin j, g i.succ = y i := fun i => rfl
  have hgΛ : ∀ m, g m ∈ Λ := by
    intro m
    rcases Fin.eq_zero_or_eq_succ m with h | ⟨i, rfl⟩
    · rw [h, hg0]; exact hu
    · rw [hgs i]; exact hyΛ i
  have hgind : LinearIndependent ℤ g := by
    rw [Fintype.linearIndependent_iff]
    intro a ha2
    have h1 : ∑ m : Fin (j + 1), a m • projU u (g m) = 0 := by
      have h := congrArg (projUZ u) ha2
      simp only [map_sum, map_smul, projUZ_apply, map_zero] at h
      exact h
    rw [Fin.sum_univ_succ] at h1
    have h2 : ∑ i : Fin j, a i.succ • f i = 0 := by
      have hz : projU u (g 0) = 0 := by rw [hg0, projU_self_eq_zero u hu0]
      have hs : ∀ i : Fin j, projU u (g i.succ) = f i := fun i => by rw [hgs i, hyproj i]
      rw [hz, smul_zero, zero_add] at h1
      simpa only [hs] using h1
    have hasucc : ∀ i : Fin j, a i.succ = 0 :=
      Fintype.linearIndependent_iff.mp hfind (fun i => a i.succ) h2
    have ha0 : a 0 = 0 := by
      rw [Fin.sum_univ_succ] at ha2
      have hsum0 : ∑ i : Fin j, a i.succ • g i.succ = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [hasucc i, zero_smul]
      rw [hsum0, add_zero, hg0] at ha2
      have hcast : ((a 0 : ℤ) : ℝ) • u = 0 := by
        rw [Int.cast_smul_eq_zsmul ℝ (a 0) u]; exact ha2
      rcases smul_eq_zero.mp hcast with h | h
      · exact Int.cast_eq_zero.mp h
      · exact absurd h hu0
    intro m
    rcases Fin.eq_zero_or_eq_succ m with h | ⟨i, rfl⟩
    · rw [h]; exact ha0
    · exact hasucc i
  have hgnorm : ∀ m, ‖g m‖ ≤ 2 * sMin (Λ.map (projUZ u)) j + ε := by
    intro m
    rcases Fin.eq_zero_or_eq_succ m with h | ⟨i, rfl⟩
    · rw [h, hg0]
      exact le_trans hu_le (le_add_of_nonneg_right hε.le)
    · rw [hgs i]
      have h1 : ‖f i‖ ≤ sMin (Λ.map (projUZ u)) j + ε := le_trans (hfs i) hslt.le
      have h2 : ‖y i‖ ≤ ‖f i‖ + ‖u‖ / 2 := hynorm i
      linarith
  exact ⟨g, hgΛ, hgind, hgnorm⟩

end Work.HP.BCS

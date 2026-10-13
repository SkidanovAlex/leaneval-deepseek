import Mathlib

namespace Work.WilE4.CAD

set_option linter.unusedVariables false

/-- A simple root of a polynomial is isolated: there is a disk around it whose
only root of the (complexified) polynomial is the root itself, and whose boundary
circle carries no root. -/
theorem exists_disk_roots_eq_singleton {q : Polynomial ℝ} (hq : q ≠ 0) {t₀ : ℝ}
    (hroot : q.IsRoot t₀) (hsimple : ¬ q.derivative.IsRoot t₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < ε ∧
      ((q.map (algebraMap ℝ ℂ)).roots.filter (fun z : ℂ => dist z (t₀ : ℂ) < ρ)) = {(t₀ : ℂ)} ∧
      (∀ z : ℂ, dist z (t₀ : ℂ) = ρ → ((q.map (algebraMap ℝ ℂ)).eval z) ≠ 0) := by
  -- Factor `q = (X - C t₀) * q₁` with `q₁ t₀ ≠ 0` (simplicity of the root).
  obtain ⟨q₁, hq₁, hq₁eval⟩ :
      ∃ q₁ : Polynomial ℝ, q = (Polynomial.X - Polynomial.C t₀) * q₁ ∧ q₁.eval t₀ ≠ 0 := by
    obtain ⟨q₁, hq₁⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
    refine ⟨q₁, hq₁, ?_⟩
    have hdq : q.derivative.eval t₀ = q₁.eval t₀ := by
      have hd : q.derivative = q₁ + (Polynomial.X - Polynomial.C t₀) * q₁.derivative := by
        rw [hq₁, Polynomial.derivative_mul, Polynomial.derivative_sub,
            Polynomial.derivative_X, Polynomial.derivative_C]
        simp
      rw [hd, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C]
      ring
    have hd0 : q.derivative.eval t₀ ≠ 0 := fun h => hsimple (Polynomial.IsRoot.def.mpr h)
    intro h
    exact hd0 (hdq.trans h)
  let p : Polynomial ℂ := q.map (algebraMap ℝ ℂ)
  let r : Polynomial ℂ := q₁.map (algebraMap ℝ ℂ)
  let c : ℂ := (t₀ : ℂ)
  -- The complexified factorization `p = (X - C c) * r` with `r c ≠ 0`.
  have hp_eq : p = (Polynomial.X - Polynomial.C c) * r := by
    simp only [p, r, c, hq₁, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C]
    rw [Complex.coe_algebraMap]
  have hr_eval : r.eval c ≠ 0 := by
    have h1 : r.eval c = algebraMap ℝ ℂ (q₁.eval t₀) := by
      simp only [r, c]
      rw [Polynomial.eval_map]
      rw [show (↑t₀ : ℂ) = (algebraMap ℝ ℂ) t₀ by simp [Complex.coe_algebraMap]]
      rw [Polynomial.eval₂_at_apply]
    rw [h1]
    intro h
    exact hq₁eval (Complex.ofReal_injective (by simpa using h))
  have hr_ne : r ≠ 0 := by
    intro h; rw [h] at hr_eval; simp at hr_eval
  have hp_ne : p ≠ 0 := by
    rw [hp_eq]
    exact mul_ne_zero (Polynomial.X_sub_C_ne_zero c) hr_ne
  have hroots : p.roots = (Polynomial.X - Polynomial.C c).roots + r.roots := by
    rw [hp_eq, Polynomial.roots_mul (mul_ne_zero (Polynomial.X_sub_C_ne_zero c) hr_ne)]
  -- A positive lower bound `d` for the distances from `c` to the other roots.
  let D : Finset ℝ := (r.roots.toFinset).image (fun z => dist z c)
  let d : ℝ := (insert 1 D).min' (Finset.insert_nonempty 1 D)
  have hd_pos : 0 < d := by
    rw [Finset.lt_min'_iff]
    intro y hy
    rw [Finset.mem_insert] at hy
    rcases hy with hy1 | hyD
    · rw [hy1]; norm_num
    · rw [Finset.mem_image] at hyD
      obtain ⟨z, hz, rfl⟩ := hyD
      rw [dist_pos]
      intro hzc
      have hroot_z : r.IsRoot z := (Polynomial.mem_roots'.mp (Multiset.mem_toFinset.mp hz)).2
      rw [hzc] at hroot_z
      exact hr_eval (Polynomial.IsRoot.def.mp hroot_z)
  have hd_le : ∀ z ∈ r.roots.toFinset, d ≤ dist z c := by
    intro z hz
    exact Finset.min'_le _ _ (Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨z, hz, rfl⟩)))
  set m : ℝ := min d ε with hm
  have hm_pos : 0 < m := by rw [hm]; exact lt_min hd_pos hε
  have hm_le_d : m ≤ d := by rw [hm]; exact min_le_left _ _
  have hm_le_eps : m ≤ ε := by rw [hm]; exact min_le_right _ _
  refine ⟨m / 2, by linarith, by linarith, ?_, ?_⟩
  · -- The only root inside the open disk of radius `m / 2` is `c`.
    show Multiset.filter (fun z : ℂ => dist z c < m / 2) p.roots = {c}
    rw [hroots, Multiset.filter_add]
    have h1 : Multiset.filter (fun z : ℂ => dist z c < m / 2)
        (Polynomial.X - Polynomial.C c).roots = {c} := by
      rw [Polynomial.roots_X_sub_C, Multiset.filter_singleton]
      split_ifs with h
      · rfl
      · exfalso; rw [dist_self] at h; linarith
    have h2 : Multiset.filter (fun z : ℂ => dist z c < m / 2) r.roots = 0 := by
      rw [Multiset.filter_eq_nil]
      intro z hz hlt
      have := hd_le z (Multiset.mem_toFinset.mpr hz)
      linarith
    rw [h1, h2, add_zero]
  · -- No root on the boundary circle.
    show ∀ z : ℂ, dist z c = m / 2 → p.eval z ≠ 0
    intro z hz hev
    have hzroot : z ∈ p.roots :=
      (Polynomial.mem_roots').mpr ⟨hp_ne, Polynomial.IsRoot.def.mpr hev⟩
    rw [hroots, Polynomial.roots_X_sub_C, Multiset.mem_add, Multiset.mem_singleton] at hzroot
    rcases hzroot with hzc | hzr
    · rw [hzc, dist_self] at hz; linarith
    · have := hd_le z (Multiset.mem_toFinset.mpr hzr)
      rw [hz] at this; linarith

end Work.WilE4.CAD

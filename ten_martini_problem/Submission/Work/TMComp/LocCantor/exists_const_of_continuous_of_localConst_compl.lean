import Mathlib

open Set
open scoped Topology

set_option linter.style.haveILetI false

namespace Work.TMComp.LocCantor

/-- If `f` is locally constant on a set `U` (in the epsilon form), then it is constant
on any interval `Ioo a b` contained in `U`. -/
theorem const_on_Ioo_of_locConstOn {U : Set ℝ} {f : ℝ → ℂ}
    (hloc : ∀ x ∈ U, ∃ ε > 0, ∀ y ∈ U, |y - x| < ε → f y = f x)
    {a b : ℝ} (hab : Ioo a b ⊆ U) :
    ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, f x = f y := by
  haveI : PreconnectedSpace (Ioo a b) := Subtype.preconnectedSpace isPreconnected_Ioo
  have hlc : IsLocallyConstant (fun t : Ioo a b => f t.1) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro t
    obtain ⟨ε, hε, hε'⟩ := hloc t.1 (hab t.2)
    refine ⟨Subtype.val ⁻¹' Metric.ball (t : ℝ) ε,
      Metric.isOpen_ball.preimage continuous_subtype_val, ?_, ?_⟩
    · show dist (t : ℝ) (t : ℝ) < ε
      rw [dist_self]
      exact hε
    · intro s hs
      rw [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hs
      exact hε' s.1 (hab s.2) hs
  intro x hx y hy
  exact hlc.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩

/-- If `f` is continuous and takes the value `v` on the open interval `(a,b)`, with `a < b`,
then it takes the value `v` on the closed interval `[a,b]`. -/
theorem eq_of_continuous_of_constOn_Ioo {f : ℝ → ℂ} (hf : Continuous f) {a b : ℝ} (hab : a < b)
    {v : ℂ} (hv : ∀ t ∈ Ioo a b, f t = v) :
    ∀ t ∈ Icc a b, f t = v := by
  have hclosed : IsClosed (f ⁻¹' {v}) := IsClosed.preimage hf isClosed_singleton
  have hsub : Ioo a b ⊆ f ⁻¹' {v} := fun t ht => hv t ht
  have hcl : Icc a b ⊆ f ⁻¹' {v} := by
    rw [← closure_Ioo (ne_of_lt hab)]
    exact closure_minimal hsub hclosed
  exact fun t ht => hcl ht

theorem exists_const_of_continuous_of_localConst_compl {Z : Set ℝ} (hZc : IsClosed Z)
    (hZd : ∀ z ∈ Z, ∃ ε > 0, ∀ y ∈ Z, |y - z| < ε → y = z)
    {f : ℝ → ℂ} (hf : Continuous f)
    (hloc : ∀ x ∉ Z, ∃ ε > 0, ∀ y ∉ Z, |y - x| < ε → f y = f x) :
    ∃ c : ℂ, ∀ x, f x = c := by
  have hLC : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ Z
    · obtain ⟨ε, hεpos, hiso⟩ := hZd x hx
      refine ⟨Ioo (x - ε) (x + ε), isOpen_Ioo, ⟨by linarith, by linarith⟩, ?_⟩
      have hLU : Ioo (x - ε) x ⊆ (Zᶜ : Set ℝ) := by
        intro t ht
        simp only [mem_compl_iff]
        intro htZ
        have hlt : |t - x| < ε := by
          rw [abs_lt]
          exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
        have := hiso t htZ hlt
        linarith [ht.2, this]
      have hRU : Ioo x (x + ε) ⊆ (Zᶜ : Set ℝ) := by
        intro t ht
        simp only [mem_compl_iff]
        intro htZ
        have hlt : |t - x| < ε := by
          rw [abs_lt]
          exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
        have := hiso t htZ hlt
        linarith [ht.1, this]
      have hLc : ∀ t ∈ Ioo (x - ε) x, f t = f (x - ε / 2) :=
        fun t ht => const_on_Ioo_of_locConstOn hloc hLU t ht (x - ε / 2)
          (by constructor <;> linarith)
      have hRc : ∀ t ∈ Ioo x (x + ε), f t = f (x + ε / 2) :=
        fun t ht => const_on_Ioo_of_locConstOn hloc hRU t ht (x + ε / 2)
          (by constructor <;> linarith)
      have hxL : f x = f (x - ε / 2) :=
        eq_of_continuous_of_constOn_Ioo hf (by linarith) hLc x (by constructor <;> linarith)
      have hxR : f x = f (x + ε / 2) :=
        eq_of_continuous_of_constOn_Ioo hf (by linarith) hRc x (by constructor <;> linarith)
      intro t ht
      rcases lt_trichotomy t x with hlt | heq | hgt
      · rw [hLc t ⟨by linarith [ht.1], hlt⟩, ← hxL]
      · subst heq; rfl
      · rw [hRc t ⟨hgt, by linarith [ht.2]⟩, ← hxR]
    · obtain ⟨ε, hεpos, hε⟩ := hloc x hx
      have hUnhds : (Zᶜ : Set ℝ) ∈ 𝓝 x := hZc.isOpen_compl.mem_nhds hx
      obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.1 hUnhds
      refine ⟨Ioo (x - min ε δ) (x + min ε δ), isOpen_Ioo,
        ⟨by linarith [lt_min hεpos hδpos], by linarith [lt_min hεpos hδpos]⟩, ?_⟩
      intro t ht
      have htmin : |t - x| < min ε δ := by
        rw [abs_lt]
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have htx : |t - x| < ε := lt_of_lt_of_le htmin (min_le_left ε δ)
      have htU : t ∉ Z := by
        have : t ∈ Metric.ball x δ := by
          rw [Metric.mem_ball, Real.dist_eq]
          exact lt_of_lt_of_le htmin (min_le_right ε δ)
        exact hδ this
      exact hε t htU htx
  obtain ⟨c, hc⟩ := hLC.exists_eq_const
  exact ⟨c, fun x => by simpa using congrFun hc x⟩

end Work.TMComp.LocCantor

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Submission.Work.FTS.StrongEps.LocUnif.rho_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

/-- A continuous real function on the closed rectangle `[a,b] × [c,d]` (`a < b`, `c < d`) is
bounded above. -/
lemma exists_upper_bound_of_continuousOn {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {ρ : ℝ → ℝ → ℝ}
    (hρc : ContinuousOn (Function.uncurry ρ) (Set.Icc a b ×ˢ Set.Icc c d)) :
    ∃ M : ℝ, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, ρ z θ ≤ M := by
  have hK : IsCompact (Set.Icc a b ×ˢ Set.Icc c d) :=
    (isCompact_Icc (a := a) (b := b)).prod (isCompact_Icc (a := c) (b := d))
  have hne : (Set.Icc a b ×ˢ Set.Icc c d).Nonempty :=
    ⟨(a, c), by rw [Set.mem_prod]; exact ⟨⟨le_rfl, hab.le⟩, ⟨le_rfl, hcd.le⟩⟩⟩
  obtain ⟨p, _hp, hmax⟩ := hK.exists_isMaxOn hne hρc
  exact ⟨ρ p.1 p.2, fun z hz θ hθ => (isMaxOn_iff.mp hmax) (z, θ) ⟨hz, hθ⟩⟩

theorem exists_scaling_const_seq {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {ι : Type*} [Fintype ι] (hne : Nonempty ι) {ρ : ι → ℝ → ℝ → ℝ}
    (hρc : ∀ k, ContinuousOn (Function.uncurry (ρ k)) (Set.Icc a b ×ˢ Set.Icc c d))
    (hρp : ∀ k, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, 0 < ρ k z θ) :
    ∃ C : ℕ → ℝ, (∀ j, 1 ≤ C j) ∧
      (∀ (j : ℕ) (k : ι) (z y θ : ℝ), z ∈ Set.Icc a b → y ∈ Set.Icc a b → θ ∈ Set.Icc c d →
        |z - y| ≤ 1 / ((j : ℝ) + 1) → (ρ k z θ) ^ 2 ≤ C j * (ρ k y θ) ^ 2) ∧
      Filter.Tendsto C Filter.atTop (nhds 1) := by
  -- per-`k` positive lower bound and uniform continuity on the box
  choose m hm using fun k => (rho_bounds hab hcd (hρc k) (hρp k)).1
  -- per-`k` upper bound on the box
  choose M hM using fun k => exists_upper_bound_of_continuousOn hab hcd (hρc k)
  have hmpos : ∀ k, 0 < m k := fun k => (hm k).1
  have hmle : ∀ k, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, m k ≤ ρ k z θ := fun k => (hm k).2
  -- a global upper bound for all the ratios
  have huniv : (Finset.univ : Finset ι).Nonempty := ⟨Classical.choice hne, Finset.mem_univ _⟩
  set B : ℝ := Finset.univ.sup' huniv (fun k => (M k) ^ 2 / (m k) ^ 2) with hBdef
  -- the set of ratios admissible at scale `j`
  let T : ℕ → Set ℝ := fun j => {v : ℝ | ∃ k : ι, ∃ z ∈ Set.Icc a b, ∃ y ∈ Set.Icc a b,
      ∃ θ ∈ Set.Icc c d, |z - y| ≤ 1 / ((j : ℝ) + 1) ∧ v = (ρ k z θ) ^ 2 / (ρ k y θ) ^ 2}
  have ha_mem : a ∈ Set.Icc a b := ⟨le_rfl, hab.le⟩
  have hc_mem : c ∈ Set.Icc c d := ⟨le_rfl, hcd.le⟩
  have hone : ∀ j, (1 : ℝ) ∈ T j := by
    intro j
    refine ⟨Classical.choice hne, a, ha_mem, a, ha_mem, c, hc_mem, ?_, ?_⟩
    · rw [sub_self, abs_zero]
      exact le_of_lt (one_div_pos.mpr (by positivity))
    · rw [div_self]
      exact pow_ne_zero 2 (ne_of_gt (hρp _ a ha_mem c hc_mem))
  have hTne : ∀ j, (T j).Nonempty := fun j => ⟨1, hone j⟩
  have hTbdd : ∀ j, BddAbove (T j) := by
    intro j
    refine ⟨B, ?_⟩
    intro v hv
    obtain ⟨k, z, hz, y, hy, θ, hθ, _, hv⟩ := hv
    rw [hv]
    have hzpos : 0 < ρ k z θ := hρp k z hz θ hθ
    have hypos : 0 < ρ k y θ := hρp k y hy θ hθ
    have h1 : (ρ k z θ) ^ 2 ≤ (M k) ^ 2 :=
      pow_le_pow_left₀ hzpos.le (hM k z hz θ hθ) 2
    have h2 : (m k) ^ 2 ≤ (ρ k y θ) ^ 2 :=
      pow_le_pow_left₀ (hmpos k).le (hmle k y hy θ hθ) 2
    have h3 : (ρ k z θ) ^ 2 / (ρ k y θ) ^ 2 ≤ (M k) ^ 2 / (m k) ^ 2 :=
      div_le_div₀ (sq_nonneg _) h1 (pow_pos (hmpos k) 2) h2
    exact le_trans h3 (Finset.le_sup' (fun k => (M k) ^ 2 / (m k) ^ 2) (Finset.mem_univ k))
  have h1j : ∀ j, 1 ≤ sSup (T j) := fun j => le_csSup (hTbdd j) (hone j)
  refine ⟨fun j => sSup (T j), h1j, ?_, ?_⟩
  · intro j k z y θ hz hy hθ hzy
    have hypos : 0 < ρ k y θ := hρp k y hy θ hθ
    have hv : (ρ k z θ) ^ 2 / (ρ k y θ) ^ 2 ∈ T j := ⟨k, z, hz, y, hy, θ, hθ, hzy, rfl⟩
    have hle : (ρ k z θ) ^ 2 / (ρ k y θ) ^ 2 ≤ sSup (T j) := le_csSup (hTbdd j) hv
    rw [div_le_iff₀ (pow_pos hypos 2)] at hle
    exact hle
  · rw [tendsto_order]
    constructor
    · intro a' ha'
      exact Filter.Eventually.of_forall (fun j => lt_of_lt_of_le ha' (h1j j))
    · intro b hb
      have hb1 : 0 < b - 1 := by linarith
      set e : ℝ := min ((b - 1) / 4) (1 / 2) with hedef
      have hepos : 0 < e := by rw [hedef]; exact lt_min (by linarith) (by norm_num)
      have he1 : e ≤ 1 / 2 := by rw [hedef]; exact min_le_right _ _
      have he2 : e ≤ (b - 1) / 4 := by rw [hedef]; exact min_le_left _ _
      have hkey : (1 + e) ^ 2 < b := by
        have h1 : e ^ 2 ≤ e * (1 / 2) := by
          calc e ^ 2 = e * e := by ring
            _ ≤ e * (1 / 2) := mul_le_mul_of_nonneg_left he1 hepos.le
        nlinarith [h1, he1, he2, hepos]
      choose δ hδ using fun k =>
        (rho_bounds hab hcd (hρc k) (hρp k)).2 (e * m k) (mul_pos hepos (hmpos k))
      have hEv : ∀ᶠ j : ℕ in Filter.atTop, ∀ k : ι, 1 / ((j : ℝ) + 1) < δ k := by
        refine Filter.eventually_all.mpr ?_
        intro k
        exact (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
          (Iio_mem_nhds (hδ k).1)
      filter_upwards [hEv] with j hj
      have hsup : sSup (T j) ≤ (1 + e) ^ 2 := by
        refine csSup_le (hTne j) ?_
        intro v hv
        obtain ⟨k, z, hz, y, hy, θ, hθ, hzy, hv⟩ := hv
        rw [hv]
        have hypos : 0 < ρ k y θ := hρp k y hy θ hθ
        have hzpos : 0 < ρ k z θ := hρp k z hz θ hθ
        have hδk : |z - y| < δ k := lt_of_le_of_lt hzy (hj k)
        have hdiff : |ρ k z θ - ρ k y θ| < e * m k := (hδ k).2 z hz y hy θ hθ hδk
        have hstep : ρ k z θ < (1 + e) * ρ k y θ := by
          have hlt : ρ k z θ - ρ k y θ < e * m k := (abs_sub_lt_iff.mp hdiff).1
          have hme : e * m k ≤ e * ρ k y θ :=
            mul_le_mul_of_nonneg_left (hmle k y hy θ hθ) hepos.le
          nlinarith
        rw [div_le_iff₀ (pow_pos hypos 2)]
        calc (ρ k z θ) ^ 2 ≤ ((1 + e) * ρ k y θ) ^ 2 :=
              le_of_lt (pow_lt_pow_left₀ hstep hzpos.le (by norm_num))
          _ = (1 + e) ^ 2 * (ρ k y θ) ^ 2 := by ring
      linarith

end Work.FTS.StrongEps.LocUnif

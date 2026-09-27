import Mathlib
import Submission.Work.EQ.EquiLocalDefs
import Submission.Work.EQ.root_near_of_limit_root
import Submission.Work.Analysis.Complex.punctured_ball_connected

namespace Work.EQ

open Filter _root_.Topology

set_option linter.unusedVariables false

/-- The punctured disc `Metric.ball c r \ {c}` is preconnected (for `r > 0`). -/
theorem punctured_ball_isPreconnected {c : ℂ} {r : ℝ} (hr : 0 < r) :
    IsPreconnected (Metric.ball c r \ {c}) := by
  have hset : Metric.ball c r \ {c} = {z : ℂ | 0 < ‖z - c‖ ∧ ‖z - c‖ < r} := by
    ext z
    rw [Set.mem_sdiff, Metric.mem_ball, Set.mem_singleton_iff, Set.mem_setOf_eq, dist_eq_norm,
      norm_pos_iff, sub_ne_zero]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [hset]
  exact (Work.Analysis.Complex.isConnected_punctured_ball_at c hr).isPreconnected

/-- **A value of the leg on a local section propagates along the whole leg.**
If some point `E ζ₀` of the leg (`ζ₀ ≠ 0` in the unit punctured disc) is a value of the local
section `f` through a point `q` with `q.2.1 = u₁`, then over a suitable small punctured disc
every point of the leg is a value of that same section.  The proof is the usual "clopen in a
punctured disc": agreement propagates by local injectivity of `ψ₁`, and the domain is the
connected punctured disc. -/
theorem leg_value_propagates {a : ℝ} {h : ℂ → ℂ} {E : ℂ → ChainData} {u₁ κ : ℂ} {k : ℕ}
    (hE : IsChartData a h E u₁ κ k) (hLI : LocalInj a h)
    {q : ChainData} {ρ' : ℝ} {f : ℂ → ChainData} (hf : IsSection a h f q ρ')
    (hqψ : q.2.1 = u₁) {ζ₀ : ℂ} (hζ₀mem : ζ₀ ∈ Metric.ball (0 : ℂ) 1 \ {0})
    (hval : E ζ₀ ∈ f '' Metric.ball q.2.1 ρ') :
    ∃ r : ℝ, 0 < r ∧ ∀ ζ ∈ Metric.ball (0 : ℂ) r \ {0}, E ζ ∈ f '' Metric.ball q.2.1 ρ' := by
  obtain ⟨hk, hκ, hEmem, hEinj, hEcont⟩ := hE
  have hρ'pos : 0 < ρ' := hf.1
  have hfq : f q.2.1 = q := hf.2.1
  have hfmem : ∀ u ∈ Metric.ball q.2.1 ρ', f u ∈ H0 a h ∧ (f u).2.1 = u := hf.2.2.1
  have hfan := hf.2.2.2.1
  have hfan2 := hf.2.2.2.2
  obtain ⟨u₀, hu₀mem, hfu₀⟩ := hval
  have hζ₀ne : ζ₀ ≠ 0 := hζ₀mem.2
  have hζ₀lt1 : ‖ζ₀‖ < 1 := by
    have h := hζ₀mem.1
    rwa [Metric.mem_ball, dist_zero_right] at h
  -- the base value of the covered point is `u₁ + κ ζ₀ ^ k`
  have hu₀eq : u₀ = u₁ + κ * ζ₀ ^ k := by
    have h1 : u₀ = (f u₀).2.1 := ((hfmem u₀ hu₀mem).2).symm
    have h2 : (f u₀).2.1 = (E ζ₀).2.1 := by rw [hfu₀]
    have h3 : (E ζ₀).2.1 = u₁ + κ * ζ₀ ^ k := (hEmem ζ₀ hζ₀mem).2
    exact h1.trans (h2.trans h3)
  have hnorm_lt : ‖κ‖ * ‖ζ₀‖ ^ k < ρ' := by
    have hb : ‖u₀ - q.2.1‖ < ρ' := by
      have h := Metric.mem_ball.mp hu₀mem
      rwa [dist_eq_norm] at h
    have heq : ‖u₀ - q.2.1‖ = ‖κ‖ * ‖ζ₀‖ ^ k := by
      rw [hu₀eq, hqψ, add_sub_cancel_left, norm_mul, norm_pow]
    rw [heq] at hb
    exact hb
  -- choose the radius `r` so that the whole leg over `ball 0 r` lands in the section's ball
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_lt (f := fun t : ℝ => ‖κ‖ * t ^ k) (g := fun _ : ℝ => ρ')
      (by fun_prop) continuous_const).mem_nhds hnorm_lt)
  set r : ℝ := min 1 (‖ζ₀‖ + δ / 2) with hrdef
  have hr_gt : ‖ζ₀‖ < r := by
    rw [hrdef]
    exact lt_min hζ₀lt1 (by linarith)
  have hr_le : r ≤ 1 := by rw [hrdef]; exact min_le_left _ _
  have hr_pos : 0 < r := lt_of_le_of_lt (norm_nonneg _) hr_gt
  have hr_mem : r ∈ Metric.ball (‖ζ₀‖) δ := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hr_gt)]
    have h2 : r ≤ ‖ζ₀‖ + δ / 2 := by rw [hrdef]; exact min_le_right _ _
    linarith
  have hkr : ‖κ‖ * r ^ k < ρ' := hδsub hr_mem
  have hDconn : IsPreconnected (Metric.ball (0 : ℂ) r \ {0}) :=
    punctured_ball_isPreconnected hr_pos
  set D : Set ℂ := Metric.ball (0 : ℂ) r \ {0} with hDdef
  set g : ℂ → ChainData := fun w => f (u₁ + κ * w ^ k) with hgdef
  have hDmem : ∀ z : ℂ, z ∈ D ↔ ‖z‖ < r ∧ z ≠ 0 := by
    intro z
    simp only [hDdef, Metric.mem_ball, Set.mem_sdiff, Set.mem_singleton_iff, dist_eq_norm, sub_zero]
  have hDconn' : IsPreconnected D := by rw [hDdef]; exact hDconn
  have hDsub1 : ∀ w ∈ D, w ∈ Metric.ball (0 : ℂ) 1 \ {0} := by
    intro w hwD
    obtain ⟨hwn, hwne⟩ := (hDmem w).mp hwD
    rw [Set.mem_sdiff, Metric.mem_ball, Set.mem_singleton_iff, dist_eq_norm, sub_zero]
    exact ⟨lt_of_lt_of_le hwn hr_le, hwne⟩
  -- every point of `D` maps into the section's ball
  have hφmem : ∀ ζ ∈ D, u₁ + κ * ζ ^ k ∈ Metric.ball q.2.1 ρ' := by
    intro ζ hζD
    have hζn : ‖ζ‖ < r := ((hDmem ζ).mp hζD).1
    rw [Metric.mem_ball, hqψ, dist_eq_norm, add_sub_cancel_left]
    calc ‖κ * ζ ^ k‖ = ‖κ‖ * ‖ζ‖ ^ k := by rw [norm_mul, norm_pow]
      _ ≤ ‖κ‖ * r ^ k := mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg ζ) (le_of_lt hζn) k) (norm_nonneg κ)
      _ < ρ' := hkr
  -- `g` is continuous at every point of `D`
  have hg_cont : ∀ ζ ∈ D, ContinuousAt g ζ := by
    intro ζ hζD
    have hφmemζ : u₁ + κ * ζ ^ k ∈ Metric.ball q.2.1 ρ' := hφmem ζ hζD
    have hφcont : ContinuousAt (fun w : ℂ => u₁ + κ * w ^ k) ζ := by fun_prop
    have hfat : ContinuousAt f (u₁ + κ * ζ ^ k) :=
      (IsSection.continuousOn hf).continuousAt (Metric.isOpen_ball.mem_nhds hφmemζ)
    have hfund : ContinuousAt (f ∘ fun w : ℂ => u₁ + κ * w ^ k) ζ :=
      hfat.comp (f := fun w : ℂ => u₁ + κ * w ^ k) (x := ζ) hφcont
    have h2 : ContinuousAt (fun w : ℂ => f (u₁ + κ * w ^ k)) ζ := by
      simpa only [Function.comp_def] using hfund
    simpa only [hgdef] using h2
  -- agreement propagates
  have agree : ∀ ζ ∈ D, E ζ = g ζ →
      ∃ ε > 0, ∀ w, dist w ζ < ε → (w ∈ D → E w = g w) := by
    intro ζ hζD hζg
    have hEζ : ContinuousAt E ζ :=
      hEcont.continuousAt ((Metric.isOpen_ball.sdiff isClosed_singleton).mem_nhds (hDsub1 ζ hζD))
    have hgζ : ContinuousAt g ζ := hg_cont ζ hζD
    have hxH : E ζ ∈ H0 a h := (hEmem ζ (hDsub1 ζ hζD)).1
    obtain ⟨U, hUo, hxU, hinj⟩ := hLI (E ζ) hxH
    have hpre1 : E ⁻¹' U ∈ 𝓝 ζ := hEζ.preimage_mem_nhds (hUo.mem_nhds hxU)
    have hpre2 : g ⁻¹' U ∈ 𝓝 ζ :=
      hgζ.preimage_mem_nhds (hUo.mem_nhds (by rw [← hζg]; exact hxU))
    obtain ⟨ε₁, hε₁, hs₁⟩ := Metric.mem_nhds_iff.mp hpre1
    obtain ⟨ε₂, hε₂, hs₂⟩ := Metric.mem_nhds_iff.mp hpre2
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun w hw hwD => ?_⟩
    have hw1 : E w ∈ U := hs₁ (by rw [Metric.mem_ball]; exact lt_of_lt_of_le hw (min_le_left _ _))
    have hw2 : g w ∈ U := hs₂ (by rw [Metric.mem_ball]; exact lt_of_lt_of_le hw (min_le_right _ _))
    have hwH : E w ∈ H0 a h := (hEmem w (hDsub1 w hwD)).1
    have hgwH : g w ∈ H0 a h := (hfmem (u₁ + κ * w ^ k) (hφmem w hwD)).1
    have hpsi : (E w).2.1 = (g w).2.1 := by
      have h1 : (E w).2.1 = u₁ + κ * w ^ k := (hEmem w (hDsub1 w hwD)).2
      have h2 : (g w).2.1 = u₁ + κ * w ^ k := by
        rw [hgdef]
        exact (hfmem (u₁ + κ * w ^ k) (hφmem w hwD)).2
      rw [h1, h2]
    exact hinj (E w) hw1 hwH (g w) hw2 hgwH hpsi
  -- disagreement propagates (the diagonal of `ChainData` is closed)
  have disagree : ∀ ζ ∈ D, E ζ ≠ g ζ →
      ∃ ε > 0, ∀ w, dist w ζ < ε → (w ∈ D → E w ≠ g w) := by
    intro ζ hζD hζne
    have hEζ : ContinuousAt E ζ :=
      hEcont.continuousAt ((Metric.isOpen_ball.sdiff isClosed_singleton).mem_nhds (hDsub1 ζ hζD))
    have hgζ : ContinuousAt g ζ := hg_cont ζ hζD
    have hcont : ContinuousAt (fun w : ℂ => (E w, g w)) ζ := hEζ.prodMk hgζ
    have hmem : (E ζ, g ζ) ∈ (Set.diagonal ChainData)ᶜ := by
      rw [Set.mem_compl_iff, Set.mem_diagonal_iff]
      exact hζne
    have hpre : (fun w : ℂ => (E w, g w)) ⁻¹' (Set.diagonal ChainData)ᶜ ∈ 𝓝 ζ :=
      hcont.preimage_mem_nhds (isClosed_diagonal.isOpen_compl.mem_nhds hmem)
    obtain ⟨ε, hε, hs⟩ := Metric.mem_nhds_iff.mp hpre
    refine ⟨ε, hε, fun w hw _ => ?_⟩
    have hw' : w ∈ Metric.ball ζ ε := Metric.mem_ball.mpr hw
    have h2 := hs hw'
    rw [Set.mem_preimage, Set.mem_compl_iff, Set.mem_diagonal_iff] at h2
    exact h2
  set u : Set ℂ := {ζ : ℂ | ∃ ε > 0, ∀ w, dist w ζ < ε → (w ∈ D → E w = g w)} with hudef
  set v : Set ℂ := {ζ : ℂ | ∃ ε > 0, ∀ w, dist w ζ < ε → (w ∈ D → E w ≠ g w)} with hvdef
  have huo : IsOpen u := by
    rw [hudef]
    refine isOpen_iff_mem_nhds.mpr (fun ζ hζ => ?_)
    obtain ⟨ε, hε, hεp⟩ := hζ
    refine Filter.mem_of_superset (Metric.ball_mem_nhds ζ hε) ?_
    intro w hw
    refine ⟨ε - dist w ζ, sub_pos.mpr (Metric.mem_ball.mp hw), fun x hx => ?_⟩
    exact hεp x (by
      have h1 : dist x ζ ≤ dist x w + dist w ζ := dist_triangle x w ζ
      have h2 : dist x w < ε - dist w ζ := hx
      linarith)
  have hvo : IsOpen v := by
    rw [hvdef]
    refine isOpen_iff_mem_nhds.mpr (fun ζ hζ => ?_)
    obtain ⟨ε, hε, hεp⟩ := hζ
    refine Filter.mem_of_superset (Metric.ball_mem_nhds ζ hε) ?_
    intro w hw
    refine ⟨ε - dist w ζ, sub_pos.mpr (Metric.mem_ball.mp hw), fun x hx => ?_⟩
    exact hεp x (by
      have h1 : dist x ζ ≤ dist x w + dist w ζ := dist_triangle x w ζ
      have h2 : dist x w < ε - dist w ζ := hx
      linarith)
  have hsubuv : D ⊆ u ∪ v := by
    intro ζ hζD
    by_cases hζ : E ζ = g ζ
    · left; rw [hudef]; exact agree ζ hζD hζ
    · right; rw [hvdef]; exact disagree ζ hζD hζ
  have hdisj : D ∩ (u ∩ v) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro ζ hζ
    obtain ⟨hζD, hζu, hζv⟩ := hζ
    rw [hudef] at hζu
    rw [hvdef] at hζv
    obtain ⟨ε₁, hε₁, h₁⟩ := hζu
    obtain ⟨ε₂, hε₂, h₂⟩ := hζv
    have hmin : (0 : ℝ) < min ε₁ ε₂ := lt_min hε₁ hε₂
    have h1 := h₁ ζ (by rw [dist_self]; exact lt_of_lt_of_le hmin (min_le_left _ _)) hζD
    have h2 := h₂ ζ (by rw [dist_self]; exact lt_of_lt_of_le hmin (min_le_right _ _)) hζD
    exact h2 h1
  have hζ₀D : ζ₀ ∈ D := by
    rw [hDmem]
    exact ⟨hr_gt, hζ₀ne⟩
  have hgζ₀ : g ζ₀ = E ζ₀ := by
    rw [hgdef]
    show f (u₁ + κ * ζ₀ ^ k) = E ζ₀
    rw [← hu₀eq, hfu₀]
  have hζ₀u : ζ₀ ∈ u := by
    rw [hudef]
    exact agree ζ₀ hζ₀D hgζ₀.symm
  have hDu : D ⊆ u := by
    rcases (isPreconnected_iff_subset_of_disjoint.mp hDconn') u v huo hvo hsubuv hdisj with h | h
    · exact h
    · exfalso
      have hmem : ζ₀ ∈ D ∩ (u ∩ v) := ⟨hζ₀D, hζ₀u, h hζ₀D⟩
      rw [hdisj] at hmem
      exact hmem
  refine ⟨r, hr_pos, ?_⟩
  intro ζ hζD
  have hζu : ζ ∈ u := hDu hζD
  rw [hudef] at hζu
  obtain ⟨ε, hε, hεp⟩ := hζu
  have hEζg : E ζ = g ζ := hεp ζ (by rw [dist_self]; exact hε) hζD
  have hgval : g ζ = f (u₁ + κ * ζ ^ k) := by rw [hgdef]
  exact ⟨u₁ + κ * ζ ^ k, hφmem ζ hζD, by rw [hEζg, hgval]⟩

/-- **Dichotomy for a leg centred at `u₁`.**  Either every point of the leg (over a small
punctured disc around `ζ = 0`) lies on one single local section through a point of the fibre
`S ∩ ψ₁⁻¹ u₁` — the leg is *redundant*, it does not parametrise a puncture — or no point of the
leg is a value of any local section through a point of that fibre — the leg is *genuine*.  Here
"`x` is a value of the section `f`" means `x ∈ f '' Metric.ball f.2.1 ρ`, i.e. `x` is a value at a
base point inside the section's ball. -/
theorem chart_centre_section_values {a : ℝ} {h : ℂ → ℂ} {r : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hh : IsStableGerm a h r) {p : ChainData} (hp : p ∈ H0 a h) {u₁ : ℂ} (hu₁ : u₁ ≠ 0)
    {E : ℂ → ChainData} {κ : ℂ} {k : ℕ} (hE : IsChartData a h E u₁ κ k)
    (hES : E '' (Metric.ball (0 : ℂ) (1 / 2) \ {0}) ⊆ connectedComponentIn (H0 a h) p) :
    ∃ r : ℝ, 0 < r ∧
      ((∃ (q : ChainData) (ρ' : ℝ) (f : ℂ → ChainData),
          q ∈ connectedComponentIn (H0 a h) p ∧ q.2.1 = u₁ ∧ 0 < ρ' ∧
          IsSection a h f q ρ' ∧
          ∀ ζ ∈ Metric.ball (0 : ℂ) r \ {0}, E ζ ∈ f '' Metric.ball q.2.1 ρ') ∨
       (∀ ζ ∈ Metric.ball (0 : ℂ) r \ {0}, ∀ (q : ChainData) (ρ' : ℝ) (f : ℂ → ChainData),
          q ∈ connectedComponentIn (H0 a h) p → q.2.1 = u₁ →
          IsSection a h f q ρ' → E ζ ∉ f '' Metric.ball q.2.1 ρ')) := by
  have hLI : LocalInj a h := localInj_of_localHomeomorph (H0_structure ha0 ha1 hh).1
  by_cases hcase : ∃ ζ ∈ Metric.ball (0 : ℂ) (1 / 2) \ {0},
      ∃ (q : ChainData) (ρ' : ℝ) (f : ℂ → ChainData),
        q ∈ connectedComponentIn (H0 a h) p ∧ q.2.1 = u₁ ∧
        IsSection a h f q ρ' ∧ E ζ ∈ f '' Metric.ball q.2.1 ρ'
  · obtain ⟨ζ₀, hζ₀mem, q, ρ', f, hqS, hqψ, hf, hval⟩ := hcase
    have hζ₀mem1 : ζ₀ ∈ Metric.ball (0 : ℂ) 1 \ {0} := by
      obtain ⟨h1, h2⟩ := hζ₀mem
      refine ⟨?_, h2⟩
      rw [Metric.mem_ball] at h1 ⊢
      linarith
    obtain ⟨r', hr'pos, hr'prop⟩ := leg_value_propagates hE hLI hf hqψ hζ₀mem1 hval
    exact ⟨r', hr'pos, Or.inl ⟨q, ρ', f, hqS, hqψ, hf.1, hf, hr'prop⟩⟩
  · refine ⟨1 / 2, by norm_num, Or.inr ?_⟩
    intro ζ hζ q ρ' f hqS hqψ hf hval
    exact hcase ⟨ζ, hζ, q, ρ', f, hqS, hqψ, hf, hval⟩

end Work.EQ

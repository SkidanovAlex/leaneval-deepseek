import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.H0_regular
import Submission.Work.EQ.H0_path_limit
import Submission.Work.EQ.H0_structure
import Submission.Work.EQ.isPreconnected_ball_diff_countable
import Submission.Work.EQ.Refl.path_lift_component
import Submission.Work.EQ.meromorphicAt_onePoint_limit

/-!
# The `ψ₁`-projection of a regular component of `⁰H` is co-countable

Rychlik's structural theorem for the connection surface `⁰H` says that (over the unbranched
locus) `ψ₁` parametrises every component, so the only `ψ₁`-values it misses are the values of
genuine punctures of `⁰H` — and those are countable (`Work.EQ.countable_puncture_psi1_limits`).

The proof here avoids the analytic analysis of punctures altogether and works purely topologically:
a continuous path in `ℂ*` which avoids the `ψ₁`-values of the genuine punctures lifts to `H0`
(`Work.EQ.Refl.path_lift_component`), so every `z ∈ ℂ*` which can be joined to the component's own
`ψ₁`-value by such a path is hit.  Since `ℂ` minus a countable set is path-connected, the missed
set is exactly contained in the countable set of genuine-puncture values.
-/

namespace Work.EQ.Refl

open Filter _root_.Topology Set Metric

noncomputable section

/-- The set of `ψ₁`-values of *genuine* punctured charts of `H0 a h` (those having no limit in
`H0 a h`), together with a finite `ψ₂`-limit.  This is the set whose countability is
`Work.EQ.countable_puncture_psi1_limits`. -/
def GenuinePunctureValues (a : ℝ) (h : ℂ → ℂ) : Set ℂ :=
  {u : ℂ | ∃ (e : ℂ → ChainData) (v₀ : ℂ) (k : ℕ),
    IsPuncturedChart a h e u k ∧
      (¬ ∃ q ∈ H0 a h, Tendsto e (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds q)) ∧
      Tendsto (fun ζ : ℂ => (e ζ).2.2) (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds v₀)}

/-- **Every punctured chart has a finite `ψ₂`-limit.**  The chart is continuous on the punctured
unit disc, so its image is preconnected and lies in a single component of `H0`, on which `ψ₁ψ₂` is
constant (`Work.EQ.H0_regular`); hence `ψ₂ = c/ψ₁` extends across the puncture. -/
theorem tendsto_psi2_of_isPuncturedChart {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {e : ℂ → ChainData} {u : ℂ} {k : ℕ}
    (he : IsPuncturedChart a h e u k) :
    ∃ v : ℂ, Tendsto (fun ζ : ℂ => (e ζ).2.2) (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ))
      (nhds v) := by
  obtain ⟨hk, hu, κ, hκ, himg, hinj, hcont, hmer, -⟩ := he
  -- a base point of the punctured disc
  obtain ⟨ζ₀, hζ₀⟩ : ∃ ζ : ℂ, ζ ∈ Metric.ball (0 : ℂ) 1 \ {0} :=
    ⟨(1 / 2 : ℂ), by
      rw [Set.mem_sdiff, Metric.mem_ball, dist_zero_right, Set.mem_singleton_iff]
      exact ⟨by norm_num, by norm_num⟩⟩
  have hx₀ : e ζ₀ ∈ H0 a h := (himg ζ₀ hζ₀).1
  obtain ⟨c, hc⟩ := H0_regular ha0 ha1 hh (e ζ₀) hx₀
  refine ⟨c / u, ?_⟩
  -- the image of the chart is preconnected and contained in the component of `e ζ₀`
  have hball : IsPreconnected (Metric.ball (0 : ℂ) 1 \ ({0} : Set ℂ)) :=
    isPreconnected_ball_diff_countable one_pos (Set.countable_singleton 0)
  have hpre : IsPreconnected (e '' (Metric.ball (0 : ℂ) 1 \ ({0} : Set ℂ))) :=
    hball.image e hcont
  have hsub : e '' (Metric.ball (0 : ℂ) 1 \ ({0} : Set ℂ)) ⊆ connectedComponentIn (H0 a h) (e ζ₀) :=
    hpre.subset_connectedComponentIn ⟨ζ₀, hζ₀, rfl⟩
      (by rintro _ ⟨ζ, hζ, rfl⟩; exact (himg ζ hζ).1)
  -- hence `ψ₂ (e ζ) = c / (u + κ ζ^k)` on the punctured disc
  have heq : ∀ ζ ∈ Metric.ball (0 : ℂ) 1 \ ({0} : Set ℂ),
      (e ζ).2.2 = c / (u + κ * ζ ^ k) := by
    intro ζ hζ
    have hval := hc (e ζ) (hsub ⟨ζ, hζ, rfl⟩)
    have hpsi : (e ζ).2.1 = u + κ * ζ ^ k := (himg ζ hζ).2
    have hne : (e ζ).2.1 ≠ 0 := (isChain_of_mem_H0 (himg ζ hζ).1).2.1
    rw [hpsi] at hval hne
    rw [eq_div_iff hne, mul_comm]
    exact hval
  -- the model limit `c / (u + κ ζ^k) → c / u`
  have hcont : Continuous fun ζ : ℂ => u + κ * ζ ^ k := by fun_prop
  have hden : Tendsto (fun ζ : ℂ => u + κ * ζ ^ k) (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ))
      (nhds u) := by
    have h : Tendsto (fun ζ : ℂ => u + κ * ζ ^ k) (nhds (0 : ℂ))
        (nhds (u + κ * (0 : ℂ) ^ k)) := hcont.continuousAt
    have h' := h.mono_left (nhdsWithin_le_nhds : nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)
      ≤ nhds (0 : ℂ))
    simpa [zero_pow (Nat.pos_iff_ne_zero.mp hk)] using h'
  have hmodel : Tendsto (fun ζ : ℂ => c / (u + κ * ζ ^ k))
      (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds (c / u)) :=
    Filter.Tendsto.div tendsto_const_nhds hden hu
  -- the two functions agree near the puncture
  have hev : (fun ζ : ℂ => c / (u + κ * ζ ^ k))
      =ᶠ[nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)] (fun ζ : ℂ => (e ζ).2.2) := by
    refine (Filter.eventuallyEq_iff_exists_mem).mpr
      ⟨Metric.ball (0 : ℂ) 1 \ ({0} : Set ℂ), ?_, fun ζ hζ => (heq ζ hζ).symm⟩
    exact Metric.mem_nhdsWithin_iff.mpr ⟨1, one_pos, fun z hz => ⟨hz.1, hz.2⟩⟩
  exact Tendsto.congr' hev hmodel


/-- A countable subset of `ℂ` cannot cover an open ball. -/
lemma exists_mem_ball_notMem {x : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {D : Set ℂ} (hD : D.Countable) :
    ∃ u ∈ Metric.ball x ρ, u ∉ D := by
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective (fun t : ℝ => x + (t : ℂ)) := by
    intro s t hst
    have h : ((s : ℂ)) = ((t : ℂ)) := by simpa using hst
    exact_mod_cast h
  have hcount : (Set.Ioo (0 : ℝ) ρ).Countable :=
    (hD.preimage hinj).mono (fun t ht => by
      rw [Set.mem_preimage]
      exact hcon _ (Metric.mem_ball.mpr (by
        rw [dist_eq_norm, show x + (t : ℂ) - x = (t : ℂ) by ring, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos ht.1]
        exact ht.2)))
  rw [Cardinal.Real.Ioo_countable_iff] at hcount
  linarith

/-- **The `ψ₁`-projection of a regular component of `⁰H` is co-countable.** -/
theorem component_projection_cocountable {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r)
    (hcount : (GenuinePunctureValues a h).Countable)
    {S : Set ChainData} {c : ℂ} (hS : IsRegComp a h S c) :
    ∃ E : Set ℂ, E.Countable ∧ ∀ z : ℂ, z ≠ 0 → z ∉ E → ∃ x ∈ S, x.2.1 = z := by
  classical
  obtain ⟨hSsub, ⟨p, hp, hSp⟩, hSval⟩ := hS
  refine ⟨GenuinePunctureValues a h, hcount, ?_⟩
  intro z hz0 hzE
  -- the analytic local section at `p`
  obtain ⟨-, hsect, -, -⟩ := H0_structure ha0 ha1 hh
  obtain ⟨ρ, hρpos, f, hf0, hfmem, hfan, hfan2, -⟩ := hsect p hp
  have hcontf : ContinuousOn f (Metric.ball p.2.1 ρ) :=
    ContinuousOn.prodMk (continuousOn_pi' fun n => (hfan n).continuousOn)
      (ContinuousOn.prodMk (continuousOn_id.congr (fun u hu => (hfmem u hu).2))
        (hfan2).continuousOn)
  -- the image of the section is contained in the component of `p`
  have himgS : f '' Metric.ball p.2.1 ρ ⊆ S := by
    have hpre : IsPreconnected (f '' Metric.ball p.2.1 ρ) :=
      (Metric.isPreconnected_ball (x := p.2.1) (r := ρ)).image f hcontf
    have hsub : f '' Metric.ball p.2.1 ρ ⊆ connectedComponentIn (H0 a h) p :=
      hpre.subset_connectedComponentIn ⟨p.2.1, Metric.mem_ball_self hρpos, hf0⟩
        (by rintro _ ⟨u, hu, rfl⟩; exact (hfmem u hu).1)
    rw [hSp]
    exact hsub
  -- a starting parameter outside the countable obstruction set
  obtain ⟨u₁, hu₁ball, hu₁notE, hu₁ne⟩ : ∃ u₁ : ℂ, u₁ ∈ Metric.ball p.2.1 ρ ∧
      u₁ ∉ GenuinePunctureValues a h ∧ u₁ ≠ 0 := by
    obtain ⟨u, hu⟩ := exists_mem_ball_notMem (x := p.2.1) hρpos
      (hcount.union (Set.countable_singleton 0))
    exact ⟨u, hu.1, fun hc => hu.2 (Or.inl hc), fun hc => hu.2 (Or.inr (by simpa using hc))⟩
  set p' : ChainData := f u₁ with hp'def
  have hp'psi : p'.2.1 = u₁ := (hfmem u₁ hu₁ball).2
  have hp'H0 : p' ∈ H0 a h := (hfmem u₁ hu₁ball).1
  have hp'S : p' ∈ S := himgS ⟨u₁, hu₁ball, rfl⟩
  have hpp' : p' ∈ connectedComponentIn (H0 a h) p := hSp ▸ hp'S
  have hcc : connectedComponentIn (H0 a h) p' = S :=
    (connectedComponentIn_eq hpp').symm.trans hSp.symm
  have hval : ∀ x ∈ connectedComponentIn (H0 a h) p', x.2.1 * x.2.2 = c := by
    intro x hx
    rw [hcc] at hx
    exact hSval x hx
  -- a path from `u₁` to `z` avoiding the obstruction set
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    have h2 : Module.rank ℝ ℂ = (2 : Cardinal) := by
      rw [← Module.finrank_eq_rank ℝ ℂ, Complex.finrank_real_complex]
      norm_num
    rw [h2]
    norm_num
  have hTpc : IsPathConnected ((GenuinePunctureValues a h ∪ {0} : Set ℂ)ᶜ) :=
    Set.Countable.isPathConnected_compl_of_one_lt_rank hrank
      (hcount.union (Set.countable_singleton 0))
  have hu₁T : u₁ ∈ (GenuinePunctureValues a h ∪ {0} : Set ℂ)ᶜ := by
    rw [Set.mem_compl_iff, Set.mem_union]
    exact fun h => h.elim hu₁notE (fun h' => hu₁ne (by simpa using h'))
  have hzT : z ∈ (GenuinePunctureValues a h ∪ {0} : Set ℂ)ᶜ := by
    rw [Set.mem_compl_iff, Set.mem_union]
    exact fun h => h.elim hzE (fun h' => hz0 (by simpa using h'))
  obtain ⟨x₀, hx₀T, hjoin⟩ := hTpc
  have hjoin' : JoinedIn ((GenuinePunctureValues a h ∪ {0} : Set ℂ)ᶜ) u₁ z :=
    (hjoin hu₁T).symm.trans (hjoin hzT)
  obtain ⟨γ, hγ⟩ := hjoin'
  -- read `γ` as a function on `[0,1]`
  set g : ℝ → ℂ := fun t => γ (Set.projIcc 0 1 (by norm_num : (0 : ℝ) ≤ 1) t) with hgdef
  have hg_mem : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t ∈ (GenuinePunctureValues a h ∪ {0} : Set ℂ)ᶜ :=
    fun t ht => hγ (Set.projIcc 0 1 (by norm_num : (0 : ℝ) ≤ 1) t)
  have hg_ne : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t ≠ 0 := by
    intro t ht h0
    have h := hg_mem t ht
    rw [Set.mem_compl_iff, Set.mem_union, h0] at h
    exact h (Or.inr rfl)
  have hg_notE : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t ∉ GenuinePunctureValues a h := by
    intro t ht h
    have h' := hg_mem t ht
    rw [Set.mem_compl_iff, Set.mem_union] at h'
    exact h' (Or.inl h)
  have hg_cont : ContinuousOn g (Set.Icc (0 : ℝ) 1) :=
    γ.continuous.comp_continuousOn continuous_projIcc.continuousOn
  have hg0 : g 0 = p'.2.1 := by
    rw [hgdef]
    simp only
    rw [Set.projIcc_left]
    rw [hp'psi]
    exact γ.source
  have hg1 : g 1 = z := by
    rw [hgdef]
    simp only
    rw [Set.projIcc_right]
    exact γ.target
  -- the obstruction set is exactly the set of genuine-puncture values
  have hgen : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ (e : ℂ → ChainData) (k : ℕ),
      IsPuncturedChart a h e (g t) k →
        ∃ q ∈ H0 a h, Tendsto e (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds q) := by
    intro t ht e k he
    by_contra hno
    obtain ⟨v, hv⟩ := tendsto_psi2_of_isPuncturedChart ha0 ha1 hh he
    exact hg_notE t ht ⟨e, v, k, he, hno, hv⟩
  -- lift the path
  obtain ⟨G, hGcont, hG0, hGm⟩ :=
    path_lift_component ha0 ha1 hh hp'H0 hval hg0 hg_cont hg_ne hgen
  refine ⟨G 1, ?_, ?_⟩
  · have hmem : G '' Set.Icc (0 : ℝ) 1 ⊆ connectedComponentIn (H0 a h) p' :=
      (isPreconnected_Icc.image G hGcont).subset_connectedComponentIn
        ⟨0, ⟨le_rfl, zero_le_one⟩, hG0⟩
        (by rintro _ ⟨t, ht, rfl⟩; exact (hGm t ht).1)
    rw [hcc.symm]
    exact hmem ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
  · rw [(hGm 1 ⟨zero_le_one, le_rfl⟩).2, hg1]

end

end Work.EQ.Refl

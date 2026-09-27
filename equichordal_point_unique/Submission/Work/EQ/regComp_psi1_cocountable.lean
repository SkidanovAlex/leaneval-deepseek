import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.H0_path_limit
import Submission.Work.EQ.H0_structure
import Submission.Work.EQ.countable_puncture_psi1_limits
import Submission.Work.EQ.tail_uniform_of_isPreconnected
import Submission.Work.EQ.H0_tail_bounded
import Submission.Work.EQ.Refl.component_projection_cocountable

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/EQ/DESIGN_LA.md (the lead's closing route for exists_compact_regular_cycle's limit_analysis; the fan-rigidity chain and la_witness route are retired).

# regComp_psi1_cocountable (0.5–1k)

**Claim.** For every regular component `S`, `ψ₁(S) ⊇ ℂ* ∖ P`, with `P` countable and independent
of `S`.

**Imports:** as for `regComp_lift_over_annulus`.

**Route.** The lifting of step 2 in `regComp_lift_over_annulus.md`, run in `ℂ* ∖ P` (connected)
instead of the annulus. You can prove this lemma first and derive the annulus lemma from the same
lifting helper.

**Used by:** the new proof of `regComp_finite`. Every regular component of value `c` meets
`Ann r₁ r₂`, which replaces the periodicity hypothesis that made `la_regular_periodic` and the
limit analysis circular.

## Proof implemented here

The countable obstruction set is Rychlik's set of `ψ₁`-limits of *genuine* punctures with a finite
`ψ₂`-limit,

`P := Work.EQ.Refl.GenuinePunctureValues a h`,

countable by `Work.EQ.countable_puncture_psi1_limits`.  Fix a regular component `S = cCI (H0) p`
of value `c` and `z ∈ ℂ* ∖ P`.  Let `f` be the analytic local section of `ψ₁` at `p` given by
`H0_structure`; its image lies in `S`, so `p' := f u₁ ∈ S` for a parameter `u₁` close to `ψ₁ p`
chosen outside `P ∪ {0}`.  Since `ℂ ∖ (P ∪ {0})` is path-connected, a path `g` joins `u₁` to `z`
inside it; every genuine punctured chart whose `ψ₁`-value is hit by `g` fails to be genuine
(otherwise `g` would meet `P`), so `Work.EQ.Refl.path_lift_component` lifts `g` to a continuous
path in `H0` starting at `p'`.  The endpoint of the lift lies in the component of `p'`, which is
`S`, and has `ψ₁`-value `z`. -/

namespace Work.EQ

open Filter _root_.Topology

/-- **The obstruction set is countable.**  The set of `ψ₁`-limits of genuine punctured charts of
`⁰H` with a finite `ψ₂`-limit is countable (`Work.EQ.countable_puncture_psi1_limits`); it is the
set `Work.EQ.Refl.GenuinePunctureValues a h` of the path-lifting argument. -/
theorem countable_genuinePunctureValues {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {r : ℝ} (hh : IsStableGerm a h r) : (Refl.GenuinePunctureValues a h).Countable :=
  countable_puncture_psi1_limits ha0 ha1 hh

/-- **A regular component lies over `ℂ*` minus the genuine-puncture values.**  This is the
statement of `regComp_psi1_cocountable` with the countable set fixed to
`Refl.GenuinePunctureValues a h`, which is what the path-lifting argument delivers. -/
theorem regComp_psi1_cocountable_aux {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {r : ℝ} (hh : IsStableGerm a h r) {S : Set ChainData} {c : ℂ} (hS : IsRegComp a h S c) :
    ∀ z : ℂ, z ≠ 0 → z ∉ Refl.GenuinePunctureValues a h → ∃ q ∈ S, q.2.1 = z := by
  classical
  have hcount : (Refl.GenuinePunctureValues a h).Countable :=
    countable_genuinePunctureValues ha0 ha1 hh
  obtain ⟨_, ⟨p, hp, hSp⟩, hSval⟩ := hS
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
      u₁ ∉ Refl.GenuinePunctureValues a h ∧ u₁ ≠ 0 := by
    obtain ⟨u, hu⟩ := Refl.exists_mem_ball_notMem (x := p.2.1) hρpos
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
  have hTpc : IsPathConnected ((Refl.GenuinePunctureValues a h ∪ {0} : Set ℂ)ᶜ) :=
    Set.Countable.isPathConnected_compl_of_one_lt_rank hrank
      (hcount.union (Set.countable_singleton 0))
  have hu₁T : u₁ ∈ (Refl.GenuinePunctureValues a h ∪ {0} : Set ℂ)ᶜ := by
    rw [Set.mem_compl_iff, Set.mem_union]
    exact fun h => h.elim hu₁notE (fun h' => hu₁ne (by simpa using h'))
  have hzT : z ∈ (Refl.GenuinePunctureValues a h ∪ {0} : Set ℂ)ᶜ := by
    rw [Set.mem_compl_iff, Set.mem_union]
    exact fun h => h.elim hzE (fun h' => hz0 (by simpa using h'))
  obtain ⟨x₀, hx₀T, hjoin⟩ := hTpc
  have hjoin' : JoinedIn ((Refl.GenuinePunctureValues a h ∪ {0} : Set ℂ)ᶜ) u₁ z :=
    (hjoin hu₁T).symm.trans (hjoin hzT)
  obtain ⟨γ, hγ⟩ := hjoin'
  -- read `γ` as a function on `[0,1]`
  set g : ℝ → ℂ := fun t => γ (Set.projIcc 0 1 (by norm_num : (0 : ℝ) ≤ 1) t) with hgdef
  have hg_mem : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      g t ∈ (Refl.GenuinePunctureValues a h ∪ {0} : Set ℂ)ᶜ :=
    fun t ht => hγ (Set.projIcc 0 1 (by norm_num : (0 : ℝ) ≤ 1) t)
  have hg_ne : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t ≠ 0 := by
    intro t ht h0
    have h := hg_mem t ht
    rw [Set.mem_compl_iff, Set.mem_union, h0] at h
    exact h (Or.inr rfl)
  have hg_notE : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t ∉ Refl.GenuinePunctureValues a h := by
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
    obtain ⟨v, hv⟩ := Refl.tendsto_psi2_of_isPuncturedChart ha0 ha1 hh he
    exact hg_notE t ht ⟨e, v, k, he, hno, hv⟩
  -- lift the path
  obtain ⟨G, hGcont, hG0, hGm⟩ :=
    Refl.path_lift_component ha0 ha1 hh hp'H0 hval hg0 hg_cont hg_ne hgen
  refine ⟨G 1, ?_, ?_⟩
  · have hmem : G '' Set.Icc (0 : ℝ) 1 ⊆ connectedComponentIn (H0 a h) p' :=
      (isPreconnected_Icc.image G hGcont).subset_connectedComponentIn
        ⟨0, ⟨le_rfl, zero_le_one⟩, hG0⟩
        (by rintro _ ⟨t, ht, rfl⟩; exact (hGm t ht).1)
    rw [hcc.symm]
    exact hmem ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
  · rw [(hGm 1 ⟨zero_le_one, le_rfl⟩).2, hg1]

/-- **A regular component lies over all of `ℂ*` except a countable set.** There is a countable
set `P` (the `ψ₁`-limits of genuine punctures) such that every regular component contains a
chain over every `z ≠ 0` outside `P`. The proof is path lifting in `ℂ* ∖ P`: a maximal lift
converges by `H0_path_limit`, because `ψ₂ = c/ψ₁` converges along it. -/
theorem regComp_psi1_cocountable {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ P : Set ℂ, P.Countable ∧ ∀ {S : Set ChainData} {c : ℂ}, IsRegComp a h S c →
      ∀ z : ℂ, z ≠ 0 → z ∉ P → ∃ q ∈ S, q.2.1 = z := by
  refine ⟨Refl.GenuinePunctureValues a h, countable_genuinePunctureValues ha0 ha1 hh, ?_⟩
  intro S c hS z hz0 hz
  exact regComp_psi1_cocountable_aux ha0 ha1 hh hS z hz0 hz

end Work.EQ

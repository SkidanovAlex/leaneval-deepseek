import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.Defs
import Submission.Work.HornSC.CellBoundaryJordan.GridCycleAux
import Submission.Work.HornSC.CellBoundaryJordan.exists_injective_circle_map_of_grid_cycle
import Submission.Work.HornSC.CellBoundaryJordan.RayDefs
import Submission.Work.HornSC.CellBoundaryJordan.ray_crossing_parity
import Submission.Work.PlanarSC.lens_subset_of_crosscut
import Submission.Lib.Unif2.Commons.Topology.Jordan.plane_separation
import Submission.Lib.Unif2.Commons.Topology.Connected.frontier_component_compl_range

/-!
# Parity of the crossings of a generic ray with a grid cycle

Given a *vertex-simple* closed walk in the unit grid (`u i`, `i < k`, consecutive vertices
unit-adjacent, period `k`, `k ≥ 3`) and a point `a` off the polygonal cycle it spans, the number of
crossings of the ray `t ↦ a + t (1 + εI)` (`t > 0`, `ε > 0`) with the cycle is odd exactly when `a`
lies in the *bounded* connected component of the complement of the cycle.

The proof has three ingredients.

* `local_chord_of_finite_unit_segments` — locally around a point of a finite union of unit grid
  segments which is not a lattice point, the union is a straight chord.
* `flip_of_linear_chord` — if the complement of a closed set is the disjoint union of two open sets
  `U`, `V`, and near `p` the set is a straight chord (a level set of a linear functional `L`), then
  two points of a small ball on opposite sides of the chord lie in different pieces: the one with
  larger `L`-value is in `U` iff the other is not.
* the counting lemma `even_card_iff_parity` (from `ray_crossing_parity`), applied to the predicate
  `t ↦ rayPt a ε t ∈ U` on `[0, T]`: it is locally constant away from the crossings and flips at
  every crossing, while it is true at `0` exactly when `a ∈ U` and false at a far away time `T`.
-/

namespace Work.PlanarSC.JC

open Set Metric
open Work.HornSC.CellBoundaryJordan

noncomputable section

/-- **Flip across a linear chord.**  Let `U`, `V` be disjoint open sets covering the complement of
`γ`, both accumulating at `p` (`p ∈ closure U ∩ closure V`), and suppose that inside the ball
`Metric.ball p r` the curve `γ` is exactly the level set `L = L p` of a linear functional `L`.  Then
two points of the ball on opposite sides of that level set are in different pieces of the
complement: the one with the larger value of `L` lies in `U` iff the other one does not. -/
theorem flip_of_linear_chord {γ : C(Circle, ℂ)}
    {U V : Set ℂ} (hUo : IsOpen U) (hVo : IsOpen V) (hdisj : Disjoint U V)
    (hcover : U ∪ V = (Set.range γ)ᶜ)
    {p : ℂ} (hpU : p ∈ closure U) (hpV : p ∈ closure V)
    {r : ℝ} (hr : 0 < r) (L : ℂ →ₗ[ℝ] ℝ)
    (hseg : ∀ z : ℂ, z ∈ Metric.ball p r → (z ∈ Set.range γ ↔ L z = L p))
    {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ Metric.ball p r) (hz₂ : z₂ ∈ Metric.ball p r)
    (h₁ : L p < L z₁) (h₂ : L z₂ < L p) :
    (z₁ ∈ U ↔ z₂ ∉ U) := by
  classical
  set H₁ : Set ℂ := {z : ℂ | z ∈ Metric.ball p r ∧ L p < L z}
  set H₂ : Set ℂ := {z : ℂ | z ∈ Metric.ball p r ∧ L z < L p}
  have hball₁ : Convex ℝ (Metric.ball p r) := convex_ball p r
  have hH₁conv : Convex ℝ H₁ := by
    rw [show H₁ = Metric.ball p r ∩ L ⁻¹' Set.Ioi (L p) from rfl]
    exact hball₁.inter ((convex_Ioi _).linear_preimage L)
  have hH₂conv : Convex ℝ H₂ := by
    rw [show H₂ = Metric.ball p r ∩ L ⁻¹' Set.Iio (L p) from rfl]
    exact hball₁.inter ((convex_Iio _).linear_preimage L)
  have hH₁pre : IsPreconnected H₁ := hH₁conv.isPreconnected
  have hH₂pre : IsPreconnected H₂ := hH₂conv.isPreconnected
  have hz₁H : z₁ ∈ H₁ := ⟨hz₁, h₁⟩
  have hz₂H : z₂ ∈ H₂ := ⟨hz₂, h₂⟩
  have hH₁Γ : ∀ z ∈ H₁, z ∉ Set.range γ := by
    rintro z ⟨hzb, hzL⟩ hzΓ
    exact (ne_of_gt hzL) ((hseg z hzb).mp hzΓ)
  have hH₂Γ : ∀ z ∈ H₂, z ∉ Set.range γ := by
    rintro z ⟨hzb, hzL⟩ hzΓ
    exact (ne_of_lt hzL) ((hseg z hzb).mp hzΓ)
  have hH₁sub : H₁ ⊆ U ∪ V := by
    intro z hz
    rw [hcover]
    exact hH₁Γ z hz
  have hH₂sub : H₂ ⊆ U ∪ V := by
    intro z hz
    rw [hcover]
    exact hH₂Γ z hz
  have h1or : H₁ ⊆ U ∨ H₁ ⊆ V := hH₁pre.subset_or_subset hUo hVo hdisj hH₁sub
  have h2or : H₂ ⊆ U ∨ H₂ ⊆ V := hH₂pre.subset_or_subset hUo hVo hdisj hH₂sub
  obtain ⟨u, huU, hud⟩ := Metric.mem_closure_iff.mp hpU r hr
  have huB : u ∈ Metric.ball p r := by rw [Metric.mem_ball, dist_comm]; exact hud
  have huUc : u ∈ (Set.range γ)ᶜ := by rw [← hcover]; exact Or.inl huU
  have huH : u ∈ H₁ ∪ H₂ := by
    have hne : L u ≠ L p := fun h => huUc ((hseg u huB).mpr h)
    rcases lt_trichotomy (L u) (L p) with h | h | h
    · exact Or.inr ⟨huB, h⟩
    · exact absurd h hne
    · exact Or.inl ⟨huB, h⟩
  obtain ⟨v, hvV, hvd⟩ := Metric.mem_closure_iff.mp hpV r hr
  have hvB : v ∈ Metric.ball p r := by rw [Metric.mem_ball, dist_comm]; exact hvd
  have hvVc : v ∈ (Set.range γ)ᶜ := by rw [← hcover]; exact Or.inr hvV
  have hvH : v ∈ H₁ ∪ H₂ := by
    have hne : L v ≠ L p := fun h => hvVc ((hseg v hvB).mpr h)
    rcases lt_trichotomy (L v) (L p) with h | h | h
    · exact Or.inr ⟨hvB, h⟩
    · exact absurd h hne
    · exact Or.inl ⟨hvB, h⟩
  have hUhalf : H₁ ⊆ U ∨ H₂ ⊆ U := by
    rcases huH with hu1 | hu2
    · rcases h1or with h | h
      · exact Or.inl h
      · exact absurd (h hu1) (Set.disjoint_left.mp hdisj huU)
    · rcases h2or with h | h
      · exact Or.inr h
      · exact absurd (h hu2) (Set.disjoint_left.mp hdisj huU)
  have hVhalf : H₁ ⊆ V ∨ H₂ ⊆ V := by
    rcases hvH with hv1 | hv2
    · rcases h1or with h | h
      · exact absurd (h hv1) (Set.disjoint_right.mp hdisj hvV)
      · exact Or.inl h
    · rcases h2or with h | h
      · exact absurd (h hv2) (Set.disjoint_right.mp hdisj hvV)
      · exact Or.inr h
  have key : (H₁ ⊆ U ∧ H₂ ⊆ V) ∨ (H₁ ⊆ V ∧ H₂ ⊆ U) := by
    rcases hUhalf with h1 | h2
    · refine Or.inl ⟨h1, ?_⟩
      rcases hVhalf with h | h
      · exact absurd (h hz₁H) (Set.disjoint_left.mp hdisj (h1 hz₁H))
      · exact h
    · refine Or.inr ⟨?_, h2⟩
      rcases hVhalf with h | h
      · exact h
      · exact absurd (h hz₂H) (Set.disjoint_left.mp hdisj (h2 hz₂H))
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨fun _ hz2U => (Set.disjoint_left.mp hdisj hz2U) (h2 hz₂H), fun _ => h1 hz₁H⟩
  · exact ⟨fun hz1U _ => (Set.disjoint_left.mp hdisj hz1U) (h1 hz₁H),
      fun hz2U => (hz2U (h2 hz₂H)).elim⟩

/-- Inside a ball around a non-lattice point `p` of a unit grid segment `hSeg w`, membership in the
segment is equivalent to being on its supporting line. -/
private lemma ball_hSeg_eq {w : ℤ × ℤ} {p : ℂ} (hp : p ∈ hSeg w)
    (hnl : ∀ v : ℤ × ℤ, p ≠ Work.HornSC.CellBoundaryJordan.lpt v) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, z ∈ Metric.ball p r → (z ∈ hSeg w ↔ z.im = p.im) := by
  obtain ⟨him, h1, h2⟩ := hp
  have hpne1 : p.re ≠ (w.1 : ℝ) := by
    intro h
    refine hnl w ?_
    apply Complex.ext
    · simpa [Work.HornSC.CellBoundaryJordan.lpt] using h
    · simpa [Work.HornSC.CellBoundaryJordan.lpt] using him
  have hpne2 : p.re ≠ (w.1 : ℝ) + 1 := by
    intro h
    refine hnl (w.1 + 1, w.2) ?_
    apply Complex.ext
    · simpa [Work.HornSC.CellBoundaryJordan.lpt] using h
    · simpa [Work.HornSC.CellBoundaryJordan.lpt] using him
  have hlt1 : (w.1 : ℝ) < p.re := lt_of_le_of_ne h1 (Ne.symm hpne1)
  have hlt2 : p.re < (w.1 : ℝ) + 1 := lt_of_le_of_ne h2 hpne2
  refine ⟨min (p.re - (w.1 : ℝ)) ((w.1 : ℝ) + 1 - p.re) / 2, ?_, ?_⟩
  · have : 0 < min (p.re - (w.1 : ℝ)) ((w.1 : ℝ) + 1 - p.re) :=
      lt_min (by linarith) (by linarith)
    linarith
  · intro z hz
    constructor
    · intro hz'
      simpa [Work.HornSC.CellBoundaryJordan.lpt] using hz'.1.trans him.symm
    · intro hzim
      have hd : ‖z - p‖ < min (p.re - (w.1 : ℝ)) ((w.1 : ℝ) + 1 - p.re) / 2 := by
        rw [Metric.mem_ball, dist_eq_norm] at hz; exact hz
      have hre : |z.re - p.re| ≤ ‖z - p‖ := by
        have h := Complex.abs_re_le_norm (z - p)
        simpa using h
      have hm1 : min (p.re - (w.1 : ℝ)) ((w.1 : ℝ) + 1 - p.re) / 2 ≤ p.re - (w.1 : ℝ) := by
        linarith [min_le_left (p.re - (w.1 : ℝ)) ((w.1 : ℝ) + 1 - p.re)]
      have hm2 : min (p.re - (w.1 : ℝ)) ((w.1 : ℝ) + 1 - p.re) / 2 ≤ (w.1 : ℝ) + 1 - p.re := by
        linarith [min_le_right (p.re - (w.1 : ℝ)) ((w.1 : ℝ) + 1 - p.re)]
      have hz1 : (w.1 : ℝ) ≤ z.re := by
        have := abs_le.mp hre
        linarith [this.1]
      have hz2 : z.re ≤ (w.1 : ℝ) + 1 := by
        have := abs_le.mp hre
        linarith [this.2]
      exact ⟨by rw [hzim]; exact him, hz1, hz2⟩

/-- Inside a ball around a non-lattice point `p` of a unit grid segment `vSeg w`, membership in the
segment is equivalent to being on its supporting line. -/
private lemma ball_vSeg_eq {w : ℤ × ℤ} {p : ℂ} (hp : p ∈ vSeg w)
    (hnl : ∀ v : ℤ × ℤ, p ≠ Work.HornSC.CellBoundaryJordan.lpt v) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, z ∈ Metric.ball p r → (z ∈ vSeg w ↔ z.re = p.re) := by
  obtain ⟨hre, h1, h2⟩ := hp
  have hpne1 : p.im ≠ (w.2 : ℝ) := by
    intro h
    refine hnl w ?_
    apply Complex.ext
    · simpa [Work.HornSC.CellBoundaryJordan.lpt] using hre
    · simpa [Work.HornSC.CellBoundaryJordan.lpt] using h
  have hpne2 : p.im ≠ (w.2 : ℝ) + 1 := by
    intro h
    refine hnl (w.1, w.2 + 1) ?_
    apply Complex.ext
    · simpa [Work.HornSC.CellBoundaryJordan.lpt] using hre
    · simpa [Work.HornSC.CellBoundaryJordan.lpt] using h
  have hlt1 : (w.2 : ℝ) < p.im := lt_of_le_of_ne h1 (Ne.symm hpne1)
  have hlt2 : p.im < (w.2 : ℝ) + 1 := lt_of_le_of_ne h2 hpne2
  refine ⟨min (p.im - (w.2 : ℝ)) ((w.2 : ℝ) + 1 - p.im) / 2, ?_, ?_⟩
  · have : 0 < min (p.im - (w.2 : ℝ)) ((w.2 : ℝ) + 1 - p.im) :=
      lt_min (by linarith) (by linarith)
    linarith
  · intro z hz
    constructor
    · intro hz'
      simpa [Work.HornSC.CellBoundaryJordan.lpt] using hz'.1.trans hre.symm
    · intro hzim
      have hd : ‖z - p‖ < min (p.im - (w.2 : ℝ)) ((w.2 : ℝ) + 1 - p.im) / 2 := by
        rw [Metric.mem_ball, dist_eq_norm] at hz; exact hz
      have him' : |z.im - p.im| ≤ ‖z - p‖ := by
        have h := Complex.abs_im_le_norm (z - p)
        simpa using h
      have hm1 : min (p.im - (w.2 : ℝ)) ((w.2 : ℝ) + 1 - p.im) / 2 ≤ p.im - (w.2 : ℝ) := by
        linarith [min_le_left (p.im - (w.2 : ℝ)) ((w.2 : ℝ) + 1 - p.im)]
      have hm2 : min (p.im - (w.2 : ℝ)) ((w.2 : ℝ) + 1 - p.im) / 2 ≤ (w.2 : ℝ) + 1 - p.im := by
        linarith [min_le_right (p.im - (w.2 : ℝ)) ((w.2 : ℝ) + 1 - p.im)]
      have hz1 : (w.2 : ℝ) ≤ z.im := by
        have := abs_le.mp him'
        linarith [this.1]
      have hz2 : z.im ≤ (w.2 : ℝ) + 1 := by
        have := abs_le.mp him'
        linarith [this.2]
      exact ⟨by rw [hzim]; exact hre, hz1, hz2⟩

/-- **Local structure of a finite union of unit grid segments.**  Near a point `p` of a finite union
of unit grid segments which is not a lattice point, the union coincides with a single straight
chord: either a horizontal one (described by the imaginary part) or a vertical one (described by the
real part). -/
theorem local_chord_of_finite_unit_segments {ι : Type*} [Fintype ι] (a b : ι → ℤ × ℤ)
    (hadj : ∀ i, Work.HornSC.CellBoundaryJordan.IsUnitAdj (a i) (b i))
    {p : ℂ} (hp : p ∈ ⋃ i, Work.HornSC.CellBoundaryJordan.adjSeg (a i) (b i))
    (hnl : Work.HornSC.CellBoundaryJordan.NonLattice p) :
    ∃ r : ℝ, 0 < r ∧
      ((∀ z : ℂ, z ∈ Metric.ball p r →
          (z ∈ ⋃ i, Work.HornSC.CellBoundaryJordan.adjSeg (a i) (b i) ↔ z.im = p.im)) ∨
       (∀ z : ℂ, z ∈ Metric.ball p r →
          (z ∈ ⋃ i, Work.HornSC.CellBoundaryJordan.adjSeg (a i) (b i) ↔ z.re = p.re))) := by
  classical
  obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.mp hp
  have hnl' : ∀ v : ℤ × ℤ, p ≠ Work.HornSC.CellBoundaryJordan.lpt v := fun v => hnl.notMem_lpt v
  have hcpt : ∀ i, IsCompact (adjSeg (a i) (b i)) := by
    intro i
    rw [adjSeg, segment_eq_image_lineMap]
    exact isCompact_Icc.image (by fun_prop)
  have hedge : ∀ i, p ∈ adjSeg (a i) (b i) → adjSeg (a i) (b i) = adjSeg (a i₀) (b i₀) :=
    fun i hi => adjSeg_eq_of_mem_of_not_lattice (hadj i) (hadj i₀) hi hi₀ hnl'
  set ρ : ℝ := Finset.univ.inf' (Finset.univ_nonempty_iff.mpr ⟨i₀⟩)
      (fun i => if adjSeg (a i) (b i) = adjSeg (a i₀) (b i₀) then 1
        else Metric.infDist p (adjSeg (a i) (b i))) with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef, Finset.lt_inf'_iff]
    intro i _
    by_cases h : adjSeg (a i) (b i) = adjSeg (a i₀) (b i₀)
    · rw [if_pos h]; norm_num
    · rw [if_neg h]
      have hpos : 0 < Metric.infDist p (adjSeg (a i) (b i)) := by
        rw [← Metric.infDist_pos_iff_notMem_closure]
        · rw [(hcpt i).isClosed.closure_eq]
          intro hp'
          exact h (hedge i hp')
        · exact ⟨Work.HornSC.CellBoundaryJordan.lpt (a i), by rw [adjSeg]; exact left_mem_segment ℝ _ _⟩
      exact hpos
  have hρle : ∀ i, ρ ≤ (if adjSeg (a i) (b i) = adjSeg (a i₀) (b i₀) then 1
      else Metric.infDist p (adjSeg (a i) (b i))) := by
    intro i; rw [hρdef]; exact Finset.inf'_le _ (Finset.mem_univ i)
  have hρdist : ∀ i, adjSeg (a i) (b i) ≠ adjSeg (a i₀) (b i₀) →
      ρ ≤ Metric.infDist p (adjSeg (a i) (b i)) := by
    intro i hi; have := hρle i; rwa [if_neg hi] at this
  have key_h : ∀ w : ℤ × ℤ, adjSeg (a i₀) (b i₀) = hSeg w →
      ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, z ∈ Metric.ball p r →
        (z ∈ ⋃ i, adjSeg (a i) (b i) ↔ z.im = p.im) := by
    intro w hw
    have hpw : p ∈ hSeg w := by rw [← hw]; exact hi₀
    obtain ⟨ρ', hρ'pos, hρ'⟩ := ball_hSeg_eq hpw hnl'
    refine ⟨min ρ ρ', lt_min hρpos hρ'pos, fun z hz => ?_⟩
    have hzρ : z ∈ Metric.ball p ρ := Metric.ball_subset_ball (min_le_left _ _) hz
    have hzρ' : z ∈ Metric.ball p ρ' := Metric.ball_subset_ball (min_le_right _ _) hz
    constructor
    · intro hzU
      obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hzU
      have hpi : p ∈ adjSeg (a i) (b i) := by
        by_contra hpi
        have hne : adjSeg (a i) (b i) ≠ adjSeg (a i₀) (b i₀) := fun heq => hpi (heq ▸ hi₀)
        have h1 : ρ ≤ Metric.infDist p (adjSeg (a i) (b i)) := hρdist i hne
        have h2 : Metric.infDist p (adjSeg (a i) (b i)) ≤ dist p z :=
          Metric.infDist_le_dist_of_mem hzi
        have h3 : dist p z < ρ := by rw [Metric.mem_ball] at hzρ; rwa [dist_comm]
        linarith
      rw [hedge i hpi, hw] at hzi
      exact (hρ' z hzρ').mp hzi
    · intro hzim
      exact Set.mem_iUnion.mpr ⟨i₀, by rw [hw]; exact (hρ' z hzρ').mpr hzim⟩
  have key_v : ∀ w : ℤ × ℤ, adjSeg (a i₀) (b i₀) = vSeg w →
      ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, z ∈ Metric.ball p r →
        (z ∈ ⋃ i, adjSeg (a i) (b i) ↔ z.re = p.re) := by
    intro w hw
    have hpw : p ∈ vSeg w := by rw [← hw]; exact hi₀
    obtain ⟨ρ', hρ'pos, hρ'⟩ := ball_vSeg_eq hpw hnl'
    refine ⟨min ρ ρ', lt_min hρpos hρ'pos, fun z hz => ?_⟩
    have hzρ : z ∈ Metric.ball p ρ := Metric.ball_subset_ball (min_le_left _ _) hz
    have hzρ' : z ∈ Metric.ball p ρ' := Metric.ball_subset_ball (min_le_right _ _) hz
    constructor
    · intro hzU
      obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hzU
      have hpi : p ∈ adjSeg (a i) (b i) := by
        by_contra hpi
        have hne : adjSeg (a i) (b i) ≠ adjSeg (a i₀) (b i₀) := fun heq => hpi (heq ▸ hi₀)
        have h1 : ρ ≤ Metric.infDist p (adjSeg (a i) (b i)) := hρdist i hne
        have h2 : Metric.infDist p (adjSeg (a i) (b i)) ≤ dist p z :=
          Metric.infDist_le_dist_of_mem hzi
        have h3 : dist p z < ρ := by rw [Metric.mem_ball] at hzρ; rwa [dist_comm]
        linarith
      rw [hedge i hpi, hw] at hzi
      exact (hρ' z hzρ').mp hzi
    · intro hzim
      exact Set.mem_iUnion.mpr ⟨i₀, by rw [hw]; exact (hρ' z hzρ').mpr hzim⟩
  rcases hadj i₀ with hb | hb | hb | hb
  · obtain ⟨r, hr, h⟩ := key_h (a i₀) (by rw [hb, adjSeg_east])
    exact ⟨r, hr, Or.inl h⟩
  · obtain ⟨r, hr, h⟩ := key_h (b i₀) (by rw [hb, adjSeg_west])
    exact ⟨r, hr, Or.inl h⟩
  · obtain ⟨r, hr, h⟩ := key_v (a i₀) (by rw [hb, adjSeg_north])
    exact ⟨r, hr, Or.inr h⟩
  · obtain ⟨r, hr, h⟩ := key_v (b i₀) (by rw [hb, adjSeg_south])
    exact ⟨r, hr, Or.inr h⟩

theorem grid_cycle_crossing_parity {k : ℕ} (hk : 3 ≤ k) (u : ℕ → ℤ × ℤ)
    (hper : ∀ i, u (i + k) = u i)
    (hinj : ∀ i j, i < k → j < k → u i = u j → i = j)
    (hstep : ∀ i, i < k → Work.HornSC.CellBoundaryJordan.IsUnitAdj (u i) (u (i + 1)))
    {a : ℂ} {ε : ℝ} (hε : 0 < ε)
    (ha : a ∉ ⋃ i ∈ {i : ℕ | i < k}, Work.HornSC.CellBoundaryJordan.adjSeg (u i) (u (i + 1)))
    (hgen : ∀ t : ℝ, 0 < t → ∀ m n : ℤ,
      a + (t : ℂ) * (⟨1, ε⟩ : ℂ) ≠ (m : ℂ) + (n : ℂ) * Complex.I)
    (hfin : {t : ℝ | 0 < t ∧ a + (t : ℂ) * (⟨1, ε⟩ : ℂ) ∈
      ⋃ i ∈ {i : ℕ | i < k}, Work.HornSC.CellBoundaryJordan.adjSeg (u i) (u (i + 1))}.Finite) :
    (Odd hfin.toFinset.card ↔
      Bornology.IsBounded (connectedComponentIn
        ((⋃ i ∈ {i : ℕ | i < k},
          Work.HornSC.CellBoundaryJordan.adjSeg (u i) (u (i + 1)))ᶜ) a)) := by
  classical
  obtain ⟨γ, hγinj, hγrange⟩ :=
    Work.HornSC.CellBoundaryJordan.exists_injective_circle_map_of_grid_cycle hk u hper hinj hstep
  -- the union of the edges, in the two indexings
  have hEc : (⋃ i ∈ {i : ℕ | i < k}, Work.HornSC.CellBoundaryJordan.adjSeg (u i) (u (i + 1)))
      = Set.range γ := hγrange.symm
  have hedges : Set.range γ =
      ⋃ i : Fin k, Work.HornSC.CellBoundaryJordan.adjSeg (u i.1) (u (i.1 + 1)) := by
    rw [hγrange]
    ext z
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, hi, hz⟩; exact ⟨⟨i, hi⟩, hz⟩
    · rintro ⟨⟨i, hi⟩, hz⟩; exact ⟨i, hi, hz⟩
  -- the hypotheses transferred to `Set.range γ`
  have haΓ : a ∉ Set.range γ := by rw [← hEc]; exact ha
  have hfinΓ : {t : ℝ | 0 < t ∧ Work.HornSC.CellBoundaryJordan.rayPt a ε t ∈ Set.range γ}.Finite := by
    have heq : {t : ℝ | 0 < t ∧ Work.HornSC.CellBoundaryJordan.rayPt a ε t ∈ Set.range γ} =
        {t : ℝ | 0 < t ∧ a + (t : ℂ) * (⟨1, ε⟩ : ℂ) ∈
          ⋃ i ∈ {i : ℕ | i < k}, Work.HornSC.CellBoundaryJordan.adjSeg (u i) (u (i + 1))} := by
      ext t
      rw [← hEc]
      simp only [Work.HornSC.CellBoundaryJordan.rayPt,
        Work.HornSC.CellBoundaryJordan.rayDir]
    rw [heq]; exact hfin
  have hcard : hfin.toFinset.card = hfinΓ.toFinset.card := by
    congr 1
    apply Finset.ext
    intro t
    rw [Set.Finite.mem_toFinset hfin, Set.Finite.mem_toFinset hfinΓ]
    rw [← hEc]
    simp only [Work.HornSC.CellBoundaryJordan.rayPt,
      Work.HornSC.CellBoundaryJordan.rayDir]
  rw [hcard, hEc]
  -- the two complementary pieces of the cycle
  obtain ⟨U, V, hUo, hVo, hUc, hVc, hdisj, hUb, hVunb, hcover⟩ :=
    Commons.Topology.Jordan.plane_separation γ hγinj
  have hpre : ¬ IsPreconnected (Set.range γ)ᶜ :=
    Work.PlanarSC.not_isPreconnected_compl_of_cover hUo hVo hdisj hUc hVc hcover
  have hUsub : U ⊆ (Set.range γ)ᶜ := by rw [← hcover]; exact subset_union_left
  have hVsub : V ⊆ (Set.range γ)ᶜ := by rw [← hcover]; exact subset_union_right
  obtain ⟨u₀, hu₀⟩ := hUc.nonempty
  have hfrontU : frontier U = Set.range γ := by
    have h := Commons.Topology.Connected.frontier_component_compl_range γ hγinj hpre u₀
      (hUsub hu₀)
    rwa [Work.PlanarSC.connectedComponentIn_eq_left_of_cover hUo hVo hdisj hUc hcover hu₀] at h
  have hfrontV : frontier V = Set.range γ := by
    obtain ⟨v₀, hv₀⟩ := hVc.nonempty
    have h := Commons.Topology.Connected.frontier_component_compl_range γ hγinj hpre v₀
      (hVsub hv₀)
    rwa [Work.PlanarSC.connectedComponentIn_eq_right_of_cover hUo hVo hdisj hVc hcover hv₀] at h
  have hcompU : ∀ z ∈ U, connectedComponentIn (Set.range γ)ᶜ z = U :=
    fun z hz => Work.PlanarSC.connectedComponentIn_eq_left_of_cover hUo hVo hdisj hUc hcover hz
  have hcompV : ∀ z ∈ V, connectedComponentIn (Set.range γ)ᶜ z = V :=
    fun z hz => Work.PlanarSC.connectedComponentIn_eq_right_of_cover hUo hVo hdisj hVc hcover hz
  -- boundedness radii and the far away time `T`
  obtain ⟨RΓ, hRΓ⟩ : ∃ R : ℝ, ∀ z ∈ Set.range γ, ‖z‖ ≤ R := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp
      (isCompact_range γ.continuous).isBounded
    exact ⟨R, fun z hz => by simpa [Metric.mem_closedBall, dist_zero_right] using hR hz⟩
  obtain ⟨RU, hRU⟩ : ∃ R : ℝ, ∀ z ∈ U, ‖z‖ ≤ R := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hUb
    exact ⟨R, fun z hz => by simpa [Metric.mem_closedBall, dist_zero_right] using hR hz⟩
  have hRU0 : 0 ≤ RU := le_trans (norm_nonneg u₀) (hRU _ hu₀)
  set T : ℝ := max RΓ RU + ‖a‖ + 1 with hTdef
  have hTpos : 0 < T := by
    rw [hTdef]; linarith [le_max_right RΓ RU, hRU0, norm_nonneg a]
  have hrayDir_ge : 1 ≤ ‖rayDir ε‖ := by
    have h := Complex.abs_re_le_norm (rayDir ε)
    simpa [rayDir] using h
  have hle_norm : ∀ t : ℝ, 0 ≤ t → t ≤ ‖rayPt a ε t‖ + ‖a‖ := by
    intro t ht
    have hsub : rayPt a ε t - a = (t : ℂ) * rayDir ε := by simp only [rayPt]; ring
    have hnorm : ‖(t : ℂ) * rayDir ε‖ = t * ‖rayDir ε‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
    calc t = t * 1 := (mul_one t).symm
      _ ≤ t * ‖rayDir ε‖ := by nlinarith
      _ = ‖rayPt a ε t - a‖ := by rw [hsub, hnorm]
      _ ≤ ‖rayPt a ε t‖ + ‖a‖ := norm_sub_le _ _
  have hescU : rayPt a ε T ∉ U := by
    intro hmem
    have h1 : ‖rayPt a ε T‖ ≤ RU := hRU _ hmem
    have h2 : T ≤ ‖rayPt a ε T‖ + ‖a‖ := hle_norm T (le_of_lt hTpos)
    rw [hTdef] at h2
    linarith [le_max_right RΓ RU]
  have hescΓ : ∀ t : ℝ, T ≤ t → rayPt a ε t ∉ Set.range γ := by
    intro t ht hmem
    have h1 : ‖rayPt a ε t‖ ≤ RΓ := hRΓ _ hmem
    have h2 : t ≤ ‖rayPt a ε t‖ + ‖a‖ := hle_norm t (le_trans hTpos.le ht)
    rw [hTdef] at ht
    linarith [le_max_left RΓ RU]
  -- the three hypotheses of the counting lemma
  have hS : ∀ t ∈ hfinΓ.toFinset, 0 < t ∧ t < T := by
    intro t ht
    obtain ⟨ht0, hmem⟩ := (Set.Finite.mem_toFinset hfinΓ).mp ht
    refine ⟨ht0, ?_⟩
    have h1 : ‖rayPt a ε t‖ ≤ RΓ := hRΓ _ hmem
    have h2 : t ≤ ‖rayPt a ε t‖ + ‖a‖ := hle_norm t ht0.le
    have h3 : RΓ ≤ max RΓ RU := le_max_left _ _
    rw [hTdef]
    linarith
  have hloc : ∀ t ∈ Set.Icc (0 : ℝ) T, t ∉ hfinΓ.toFinset →
      ∃ δ > 0, ∀ s, |s - t| < δ → ((rayPt a ε s ∈ U) ↔ (rayPt a ε t ∈ U)) := by
    intro t ht htS
    have htΓ : rayPt a ε t ∉ Set.range γ := by
      intro hmem
      have hne0 : t ≠ 0 := by
        intro h0
        rw [h0, rayPt_zero] at hmem
        exact haΓ hmem
      have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hne0)
      exact htS ((Set.Finite.mem_toFinset hfinΓ).mpr ⟨ht0, hmem⟩)
    have hUV : rayPt a ε t ∈ U ∪ V := by rw [hcover]; exact htΓ
    have hcont : ContinuousAt (fun s : ℝ => rayPt a ε s) t := by
      apply Continuous.continuousAt
      simp only [rayPt]; fun_prop
    rcases hUV with hU | hV
    · obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hUo (rayPt a ε t) hU
      obtain ⟨δ', hδ'pos, hδ'⟩ := Metric.continuousAt_iff.mp hcont δ hδ
      refine ⟨δ', hδ'pos, fun s hs => ?_⟩
      have hsU : rayPt a ε s ∈ U :=
        hδsub (Metric.mem_ball.mpr (hδ' (by rw [Real.dist_eq]; exact hs)))
      exact ⟨fun _ => hU, fun _ => hsU⟩
    · obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hVo (rayPt a ε t) hV
      obtain ⟨δ', hδ'pos, hδ'⟩ := Metric.continuousAt_iff.mp hcont δ hδ
      refine ⟨δ', hδ'pos, fun s hs => ?_⟩
      have hsV : rayPt a ε s ∈ V :=
        hδsub (Metric.mem_ball.mpr (hδ' (by rw [Real.dist_eq]; exact hs)))
      have hnU : rayPt a ε t ∉ U := fun h => Set.disjoint_left.mp hdisj h hV
      have hs_nU : rayPt a ε s ∉ U := fun h => Set.disjoint_left.mp hdisj h hsV
      exact ⟨fun hsU => (hs_nU hsU).elim, fun htU => (hnU htU).elim⟩
  have hflip : ∀ t ∈ hfinΓ.toFinset, ∃ δ > 0, ∀ s, 0 < s → s < δ →
      ((rayPt a ε (t + s) ∈ U) ↔ ¬ (rayPt a ε (t - s) ∈ U)) := by
    intro t htS
    obtain ⟨ht0, hmem⟩ := (Set.Finite.mem_toFinset hfinΓ).mp htS
    have hmemE : rayPt a ε t ∈
        ⋃ i : Fin k, Work.HornSC.CellBoundaryJordan.adjSeg (u i.1) (u (i.1 + 1)) := by
      rw [← hedges]; exact hmem
    have hnl : NonLattice (rayPt a ε t) := fun m n => hgen t ht0 m n
    have hmemF : rayPt a ε t ∈ Set.range γ := hmem
    obtain ⟨r, hr, hchord⟩ :=
      local_chord_of_finite_unit_segments (fun i : Fin k => u i.1) (fun i : Fin k => u (i.1 + 1))
        (fun i => hstep i.1 i.2) hmemE hnl
    have hpU : rayPt a ε t ∈ closure U :=
      frontier_subset_closure (by rw [hfrontU]; exact hmemF)
    have hpV : rayPt a ε t ∈ closure V :=
      frontier_subset_closure (by rw [hfrontV]; exact hmemF)
    rcases hchord with hchord | hchord
    · -- horizontal chord: use the imaginary part
      have hseg : ∀ z : ℂ, z ∈ Metric.ball (rayPt a ε t) r →
          (z ∈ Set.range γ ↔ (Complex.imCLM : ℂ →ₗ[ℝ] ℝ) z
            = (Complex.imCLM : ℂ →ₗ[ℝ] ℝ) (rayPt a ε t)) := by
        intro z hz
        rw [hedges]
        exact hchord z hz
      refine ⟨r / (‖rayDir ε‖ + 1), by positivity, fun s hs0 hsδ => ?_⟩
      have hδ' : s * ‖rayDir ε‖ < r := by
        have h1 : s * (‖rayDir ε‖ + 1) < r :=
          (lt_div_iff₀ (by positivity : (0 : ℝ) < ‖rayDir ε‖ + 1)).mp hsδ
        nlinarith [norm_nonneg (rayDir ε)]
      have hz₁ : rayPt a ε (t + s) ∈ Metric.ball (rayPt a ε t) r := by
        rw [Metric.mem_ball, dist_eq_norm]
        have hsub : rayPt a ε (t + s) - rayPt a ε t = (s : ℂ) * rayDir ε := by
          simp only [rayPt]; push_cast; ring
        rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
        exact hδ'
      have hz₂ : rayPt a ε (t - s) ∈ Metric.ball (rayPt a ε t) r := by
        rw [Metric.mem_ball, dist_eq_norm]
        have hsub : rayPt a ε (t - s) - rayPt a ε t = (-s : ℂ) * rayDir ε := by
          simp only [rayPt]; push_cast; ring
        rw [hsub, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
        exact hδ'
      refine flip_of_linear_chord hUo hVo hdisj hcover hpU hpV hr
        (Complex.imCLM : ℂ →ₗ[ℝ] ℝ) hseg hz₁ hz₂ ?_ ?_
      · show (rayPt a ε t).im < (rayPt a ε (t + s)).im
        rw [rayPt_im, rayPt_im]; nlinarith [hε, hs0]
      · show (rayPt a ε (t - s)).im < (rayPt a ε t).im
        rw [rayPt_im, rayPt_im]; nlinarith [hε, hs0]
    · -- vertical chord: use the real part
      have hseg : ∀ z : ℂ, z ∈ Metric.ball (rayPt a ε t) r →
          (z ∈ Set.range γ ↔ (Complex.reCLM : ℂ →ₗ[ℝ] ℝ) z
            = (Complex.reCLM : ℂ →ₗ[ℝ] ℝ) (rayPt a ε t)) := by
        intro z hz
        rw [hedges]
        exact hchord z hz
      refine ⟨r / (‖rayDir ε‖ + 1), by positivity, fun s hs0 hsδ => ?_⟩
      have hδ' : s * ‖rayDir ε‖ < r := by
        have h1 : s * (‖rayDir ε‖ + 1) < r :=
          (lt_div_iff₀ (by positivity : (0 : ℝ) < ‖rayDir ε‖ + 1)).mp hsδ
        nlinarith [norm_nonneg (rayDir ε)]
      have hz₁ : rayPt a ε (t + s) ∈ Metric.ball (rayPt a ε t) r := by
        rw [Metric.mem_ball, dist_eq_norm]
        have hsub : rayPt a ε (t + s) - rayPt a ε t = (s : ℂ) * rayDir ε := by
          simp only [rayPt]; push_cast; ring
        rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
        exact hδ'
      have hz₂ : rayPt a ε (t - s) ∈ Metric.ball (rayPt a ε t) r := by
        rw [Metric.mem_ball, dist_eq_norm]
        have hsub : rayPt a ε (t - s) - rayPt a ε t = (-s : ℂ) * rayDir ε := by
          simp only [rayPt]; push_cast; ring
        rw [hsub, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
        exact hδ'
      refine flip_of_linear_chord hUo hVo hdisj hcover hpU hpV hr
        (Complex.reCLM : ℂ →ₗ[ℝ] ℝ) hseg hz₁ hz₂ ?_ ?_
      · show (rayPt a ε t).re < (rayPt a ε (t + s)).re
        rw [rayPt_re, rayPt_re]; nlinarith [hs0]
      · show (rayPt a ε (t - s)).re < (rayPt a ε t).re
        rw [rayPt_re, rayPt_re]; nlinarith [hs0]
  -- parity of the number of crossings
  have hpar : ¬ (a ∈ U) ↔ Even hfinΓ.toFinset.card := by
    have h := even_card_iff_parity (S := hfinΓ.toFinset) (a := 0) (b := T) hTpos hS hloc hflip
    rw [rayPt_zero] at h
    have hiff : (a ∈ U ↔ rayPt a ε T ∈ U) ↔ ¬ (a ∈ U) := by
      constructor
      · intro hh ha
        exact hescU (hh.mp ha)
      · intro hna
        exact ⟨fun ha => absurd ha hna, fun hT => (hescU hT).elim⟩
    rwa [hiff] at h
  have hUiff : (a ∈ U) ↔ Odd hfinΓ.toFinset.card := by
    constructor
    · intro haU
      rw [← Nat.not_even_iff_odd]
      intro he
      exact hpar.mpr he haU
    · intro ho
      by_contra hna
      exact (Nat.not_even_iff_odd.mpr ho) (hpar.mp hna)
  have hcomp : (a ∈ U) ↔
      Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ a) := by
    constructor
    · intro haU
      rw [hcompU a haU]
      exact hUb
    · intro hb
      by_contra hna
      have haV : a ∈ V := by
        have hmem : a ∈ U ∪ V := by rw [hcover]; exact haΓ
        exact hmem.resolve_left hna
      have hVeq : connectedComponentIn (Set.range γ)ᶜ a = V := hcompV a haV
      rw [hVeq] at hb
      exact hVunb hb
  exact ⟨fun ho => hcomp.mp (hUiff.mpr ho), fun hb => hUiff.mp (hcomp.mpr hb)⟩

end

end Work.PlanarSC.JC

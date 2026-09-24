import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Complex.Harmonic.eq_zero_on_sphere_of_circleAverage_eq_zero

open Metric Set Filter
open scoped Topology Real

namespace Commons.Analysis.Complex.Harmonic

/-- **Maximum principle for functions with a local circle sub-mean-value
inequality on a bounded connected open set.**  Let `Ω ⊆ ℂ` be open,
preconnected and bounded, let `w` be continuous on `closure Ω`, suppose that at
every interior point `p` there is a neighbourhood `ball p ε ⊆ Ω` on which the
circle mean-value inequality `w p ≤ Real.circleAverage w p r` holds for all
radii `r < ε`, and suppose `w z ≤ 0` at every boundary point `z ∈ closure Ω \ Ω`.
Then `w ≤ 0` on `Ω`.

Proof: `closure Ω` is compact, so `w` attains a maximum `M` there; if `M > 0`
the maximizer `p` lies in `Ω` (boundary values are ≤ 0).  The set `S` of points
of `Ω` where `w = M` is nonempty, closed in `Ω` (continuity) and open in `Ω`:
at such a point `q`, take the minimum `ε` of the openness neighborhood and the
neighborhood supplied by the local hypothesis; for any circle around `q` of
radius `r < ε` the mean-value inequality gives `M = w q ≤ average ≤ M`, so the
whole circle has value `M`.  Since `Ω` is preconnected, `w ≡ M > 0` on `Ω`,
contradicting the boundary bound by continuity on `closure Ω`. -/
theorem max_principle_localSubMeanValue {Ω : Set ℂ} (hΩopen : IsOpen Ω)
    (hΩconn : IsPreconnected Ω) (hbdd : Bornology.IsBounded Ω) {w : ℂ → ℝ}
    (hcont : ContinuousOn w (closure Ω))
    (hloc : ∀ p ∈ Ω, ∃ ε : ℝ, 0 < ε ∧ Metric.ball p ε ⊆ Ω ∧
      ∀ r : ℝ, 0 < r → Metric.closedBall p r ⊆ Metric.ball p ε →
        w p ≤ Real.circleAverage w p r)
    (hbd : ∀ z ∈ closure Ω, z ∉ Ω → w z ≤ 0) :
    ∀ z ∈ Ω, w z ≤ 0 := by
  classical
  by_cases hΩne : Ω.Nonempty
  · /- `closure Ω` is compact, so `w` attains a maximum `M = w p` there. -/
    obtain ⟨p, hpcl, hpMax⟩ :=
      hbdd.isCompact_closure.exists_isMaxOn (Set.Nonempty.mono subset_closure hΩne) hcont
    set M : ℝ := w p with hMdef
    have hMmax : ∀ y ∈ closure Ω, w y ≤ M := fun y hy => by
      simpa [hMdef] using hpMax hy
    have hMle : M ≤ 0 := by
      by_contra hMnot
      /- The maximizer is interior, since boundary values are `≤ 0 < M`. -/
      have hpΩ : p ∈ Ω := by
        by_contra hpn
        have h1 : w p ≤ 0 := hbd p hpcl hpn
        have h2 : w p = M := hMdef.symm
        linarith
      let S : Set ℂ := {z : ℂ | z ∈ Ω ∧ w z = M}
      /- **Local strong maximum principle.**  Near a point `q` of `Ω` where
      `w q = M`, a whole ball lies in `{w = M}`: on any circle around `q`
      inside `Ω` (and inside the local neighborhood where the mean-value
      inequality is available) the function `M - w ≥ 0` has nonnegative circle
      average (local sub-mean-value inequality) and nonpositive circle average
      (`w ≤ M`), hence is identically zero on that circle. -/
      have hlocal : ∀ q ∈ Ω, w q = M → ∃ R : ℝ, 0 < R ∧ Metric.closedBall q R ⊆ Ω
          ∧ ∀ z : ℂ, ‖z - q‖ < R → w z = M := by
        intro q hqΩ hqM
        rcases Metric.isOpen_iff.mp hΩopen q hqΩ with ⟨ε₀, hε₀pos, hε₀sub⟩
        rcases hloc q hqΩ with ⟨ε₁, hε₁pos, hε₁sub, hε₁ineq⟩
        let ε : ℝ := min ε₀ ε₁
        have hεpos : 0 < ε := lt_min hε₀pos hε₁pos
        have hεle₀ : ε ≤ ε₀ := min_le_left _ _
        have hεle₁ : ε ≤ ε₁ := min_le_right _ _
        have hεsub : Metric.ball q ε ⊆ Ω :=
          subset_trans (Metric.ball_subset_ball hεle₀) hε₀sub
        refine ⟨ε / 2, by linarith, ?_, ?_⟩
        · intro y hy
          have hy' : dist y q ≤ ε / 2 := Metric.mem_closedBall.mp hy
          apply hεsub
          rw [Metric.mem_ball]
          linarith
        · intro z hz
          by_cases hzq : z = q
          · rw [hzq]
            exact hqM
          · set r : ℝ := ‖z - q‖ with hrdef
            have hrpos : 0 < r := by
              rw [hrdef]
              exact norm_pos_iff.mpr (sub_ne_zero.mpr hzq)
            have hrlt : r < ε := by
              rw [hrdef] at hz
              linarith
            have hclsub : Metric.closedBall q r ⊆ Ω := by
              intro y hy
              apply hεsub
              rw [Metric.mem_ball]
              have hy' : dist y q ≤ r := Metric.mem_closedBall.mp hy
              linarith
            have hclball : Metric.closedBall q r ⊆ Metric.ball q ε₁ := by
              intro y hy
              rw [Metric.mem_ball]
              have hy' : dist y q ≤ r := Metric.mem_closedBall.mp hy
              linarith
            have hsph_sub : Metric.sphere q |r| ⊆ closure Ω := by
              intro y hy
              apply subset_closure
              apply hclsub
              rw [Metric.mem_closedBall]
              have hy' : dist y q = |r| := Metric.mem_sphere.mp hy
              rw [hy', abs_of_pos hrpos]
            have hcontSph : ContinuousOn w (Metric.sphere q |r|) := hcont.mono hsph_sub
            have hwint : CircleIntegrable w q r := ContinuousOn.circleIntegrable' hcontSph
            have hcint : CircleIntegrable (fun _ : ℂ => M) q r :=
              circleIntegrable_const M q r
            have havg_le : Real.circleAverage w q r ≤ M :=
              Real.circleAverage_mono_on_of_le_circle hwint
                (fun y hy => hMmax y (hsph_sub hy))
            have havg_ge : M ≤ Real.circleAverage w q r := by
              rw [← hqM]
              exact hε₁ineq r hrpos hclball
            have havg_eq : Real.circleAverage w q r = M := le_antisymm havg_le havg_ge
            have hgavg : Real.circleAverage (fun y : ℂ => M - w y) q r = 0 := by
              have h := Real.circleAverage_fun_sub (f₁ := fun _ : ℂ => M) (f₂ := w) hcint hwint
              rw [havg_eq, Real.circleAverage_const] at h
              simpa using h
            have hgnonneg : ∀ y ∈ Metric.sphere q |r|, 0 ≤ M - w y :=
              fun y hy => sub_nonneg.mpr (hMmax y (hsph_sub hy))
            have hgz := eq_zero_on_sphere_of_circleAverage_eq_zero
              (f := fun y : ℂ => M - w y) (c := q) (R := r)
              (continuousOn_const.sub hcontSph) hgnonneg hgavg
            have hzmem : z ∈ Metric.sphere q |r| := by
              rw [Metric.mem_sphere]
              rw [dist_eq_norm]
              rw [hrdef]
              exact (abs_of_nonneg (norm_nonneg _)).symm
            have h0 : M - w z = 0 := hgz z hzmem
            linarith
      /- `S` is open, by `hlocal`. -/
      have hS_open : IsOpen S := by
        rw [Metric.isOpen_iff]
        intro q hqS
        obtain ⟨hqΩ, hqM⟩ := hqS
        obtain ⟨R, hRpos, hclsub, hball⟩ := hlocal q hqΩ hqM
        refine ⟨R, hRpos, ?_⟩
        intro y hy
        have hyR : dist y q < R := Metric.mem_ball.mp hy
        refine ⟨hclsub (Metric.mem_closedBall.mpr (le_of_lt hyR)), ?_⟩
        exact hball y (by rw [← dist_eq_norm]; exact hyR)
      /- `Ω \ S` is open: at a point of `Ω` where `w < M`, continuity keeps
      `w < M` on a neighbourhood contained in `Ω`. -/
      have hV_open : IsOpen (Ω \ S) := by
        rw [Metric.isOpen_iff]
        intro q hqV
        obtain ⟨hqΩ, hqnotS⟩ := hqV
        have hqM : w q ≠ M := fun heq => hqnotS ⟨hqΩ, heq⟩
        have hqlt : w q < M := lt_of_le_of_ne (hMmax q (subset_closure hqΩ)) hqM
        have hclnhds : closure Ω ∈ 𝓝 q :=
          Filter.mem_of_superset (hΩopen.mem_nhds hqΩ) subset_closure
        have hev : ∀ᶠ y in 𝓝 q, w y < M :=
          (hcont.continuousAt hclnhds).eventually_lt continuousAt_const hqlt
        rcases Metric.mem_nhds_iff.mp (hΩopen.mem_nhds hqΩ) with ⟨ε₁, hε₁, hsub₁⟩
        rcases Metric.eventually_nhds_iff.mp hev with ⟨ε₂, hε₂, hsub₂⟩
        refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
        intro y hy
        have hyΩ : y ∈ Ω := hsub₁ (Metric.ball_subset_ball (min_le_left _ _) hy)
        have hyM : w y < M := hsub₂ (Metric.ball_subset_ball (min_le_right _ _) hy)
        exact ⟨hyΩ, fun hyS => (ne_of_lt hyM) hyS.2⟩
      /- `Ω` is the union of the disjoint open sets `S` and `Ω \ S`, so by
      preconnectedness and nonemptiness of `S` we get `Ω ⊆ S`. -/
      have hΩsubS : Ω ⊆ S :=
        hΩconn.subset_left_of_subset_union hS_open hV_open
          (by rw [Set.disjoint_left]; intro y hyS hyV; exact hyV.2 hyS)
          (by intro y hy
              by_cases h : y ∈ S
              · exact Or.inl h
              · exact Or.inr ⟨hy, h⟩)
          ⟨p, mem_inter hpΩ (by show p ∈ Ω ∧ w p = M; exact ⟨hpΩ, hMdef.symm⟩)⟩
      have hwS : ∀ z ∈ Ω, w z = M := fun z hz => (hΩsubS hz).2
      /- `Ω` has a boundary point: otherwise `Ω` is clopen and nonempty in the
      preconnected space `ℂ`, hence all of `ℂ`, contradicting boundedness. -/
      have hnotclosed : ¬ IsClosed Ω := by
        intro hcl
        have hΩuniv : Ω = univ := by
          apply Set.eq_univ_of_univ_subset
          exact IsPreconnected.subset_left_of_subset_union hΩopen hcl.isOpen_compl
            (by rw [Set.disjoint_left]; intro y hy hyc; exact hyc hy)
            (by intro y _
                by_cases hy : y ∈ Ω
                · exact Or.inl hy
                · exact Or.inr (by simpa using hy))
            (Set.Nonempty.mono (fun y hy => ⟨trivial, hy⟩) hΩne)
            isPreconnected_univ
        have hbu : Bornology.IsBounded (univ : Set ℂ) := hbdd.subset (by rw [hΩuniv])
        exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℂ))
          (Metric.compactSpace_iff_isBounded_univ.mpr hbu)
      have hbdy : ∃ z ∈ closure Ω, z ∉ Ω := by
        by_contra h
        have hsub : closure Ω ⊆ Ω := by
          intro z hz
          by_contra hzn
          exact h ⟨z, hz, hzn⟩
        exact hnotclosed (closure_subset_iff_isClosed.mp hsub)
      obtain ⟨z₀, hz₀cl, hz₀not⟩ := hbdy
      /- `w ≡ M` on `Ω`, hence `w ≡ M` on `closure Ω` by continuity, in
      particular `w z₀ = M > 0`, contradicting the boundary bound. -/
      have hEqOnCl : Set.EqOn w (fun _ : ℂ => M) (closure Ω) :=
        Set.EqOn.of_subset_closure (s := Ω) (t := closure Ω)
          (fun z hz => hwS z hz) hcont continuousOn_const subset_closure
          (fun x hx => hx)
      have hwz₀ : w z₀ = M := hEqOnCl hz₀cl
      have hbdz : w z₀ ≤ 0 := hbd z₀ hz₀cl hz₀not
      linarith
    intro z hz
    exact le_trans (hMmax z (subset_closure hz)) hMle
  · intro z hz
    exact (hΩne ⟨z, hz⟩).elim

end Commons.Analysis.Complex.Harmonic
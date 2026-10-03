import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.model_deep_branch_lower

/-!
# L62 — the deep inverse branch of an asymptotically translating map

**Self-contained proof of the deep-inverse-branch lemma used by
`Submission.Work.L62.section_Bl`** (the same statement is requested/proved under the name
`Work.L62.deep_preimage`; this module is a self-contained alternative, kept so that
`section_Bl` does not depend on the other module).  Let `g` be holomorphic on an open `D`
containing the half plane `{w | w.im < Y}`, with `g w → 0` as `w.im → -∞` (uniformly), and let
`0 < cl.im`.  Then for `z` deep enough the fixed point equation `u + cl + g u = z` — i.e.
`u = z - cl - g u` — has a unique solution `u z` in a deep half plane `{u | u.im < L}`, and
`z ↦ u z` is holomorphic with `u z - z + cl → 0` at the lower end.

The proof is the elementary contraction argument: `g` is bounded by `1/4` on a deep half plane
(by `hlim`) and, by Cauchy's estimate on the ball of radius `1`
(`Work.L62.deep_psi_deriv_bound`), its derivative is bounded by `1/4` on a deeper one; hence
`Φ_z(u) = z - cl - g u` is a `1/4`-contraction (`Convex.norm_image_sub_le_of_norm_deriv_le`) of
the deep half plane, so its Picard iterates `Φ_z^n (z - cl)` converge geometrically.  The limit
is a fixed point, and the iterates are holomorphic in `z`; the limit `u` is holomorphic by
`Complex.differentiableOn_tsum_of_summable_norm` applied to the telescoped series
`u = (z - cl) + ∑' n, (Φ_z^{n+1}(z-cl) - Φ_z^n(z-cl))`.
-/

namespace Work.L62

open MandelDim Filter Topology Complex Set
open scoped Topology

noncomputable section

/-- Backup proof of the deep inverse branch (same statement as `Work.L62.deep_preimage`). -/
theorem deep_preimage_aux {g : ℂ → ℂ} {D : Set ℂ} {cl : ℂ} {Y : ℝ}
    (hD : IsOpen D) (hYsub : {w : ℂ | w.im < Y} ⊆ D) (hg : DifferentiableOn ℂ g D)
    (hlim : Filter.Tendsto g (Filter.comap Complex.im Filter.atBot) (nhds 0))
    (hcl : 0 < cl.im) :
    ∃ L Lz : ℝ, L < Y ∧ ∃ u : ℂ → ℂ,
      DifferentiableOn ℂ u {z : ℂ | z.im < Lz} ∧
      (∀ z : ℂ, z.im < Lz → (u z).im < L ∧ u z + cl + g (u z) = z) ∧
      (∀ z : ℂ, z.im < Lz → ∀ v : ℂ, v.im < L → v + cl + g v = z → v = u z) ∧
      Filter.Tendsto (fun z => u z - z + cl) (Filter.comap Complex.im Filter.atBot) (nhds 0) := by
  -- (1) a deep half plane on which `‖g‖ < 1/4`
  have hquarter : {w : ℂ | ‖g w‖ < 1/4} ∈ MandelDim.lowerEnd := by
    have h1 : {w : ℂ | g w ∈ Metric.ball (0 : ℂ) (1/4)} ∈ Filter.comap Complex.im Filter.atBot :=
      hlim.eventually (Metric.ball_mem_nhds 0 (by norm_num))
    refine Filter.mem_of_superset h1 ?_
    intro w hw
    simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hw
  obtain ⟨Yb, hYb⟩ := lowerEnd_eventually hquarter
  -- (2) Cauchy estimate for the derivative on a deeper half plane
  set Y0 : ℝ := max (-Y) Yb with hY0def
  have hY0le : -Y0 ≤ Y := by
    rw [hY0def]; linarith [le_max_left (-Y) Yb]
  have hY0leb : -Y0 ≤ -Yb := by
    rw [hY0def]; linarith [le_max_right (-Y) Yb]
  have hgd : DifferentiableOn ℂ g {v : ℂ | v.im < -Y0} :=
    hg.mono (fun v hv => hYsub (lt_of_lt_of_le hv hY0le))
  obtain ⟨Yd, hYd1, hYd2⟩ := deep_psi_deriv_bound (ψ := g) (Y0 := Y0) (ε := 1/4) hgd hlim
    (by norm_num : (0:ℝ) < 1/4)
  -- (3) the two half planes `{im < L}` (solutions) and `{im < Lz}` (parameters)
  set L : ℝ := -Yd - 1 with hLdef
  have hL_lt_Y : L < Y := by rw [hLdef]; linarith
  have hL_lt_Y0 : L < -Y0 := by rw [hLdef]; linarith
  have hsubD : {v : ℂ | v.im < L} ⊆ D :=
    fun v hv => hYsub (lt_of_lt_of_le hv (le_of_lt hL_lt_Y))
  have hgbd : ∀ v : ℂ, v.im < L → ‖g v‖ < 1/4 := fun v hv => hYb v (by linarith)
  have hderiv : ∀ v : ℂ, v.im < L → ‖deriv g v‖ ≤ 1/4 := fun v hv => hYd2 v (by linarith)
  set Lz : ℝ := L + cl.im - 1/2 with hLzdef
  have hLz_lt : Lz < L + cl.im := by rw [hLzdef]; linarith
  -- (4) the `1/4`-Lipschitz bound and uniqueness on `{im < L}`
  have hlip : ∀ a b : ℂ, a.im < L → b.im < L → ‖g b - g a‖ ≤ (1/4) * ‖b - a‖ := by
    intro a b ha hb
    refine Convex.norm_image_sub_le_of_norm_deriv_le (s := {v : ℂ | v.im < L}) ?_ ?_
      (convex_halfSpace_im_lt L) ha hb
    · intro x hx
      exact hg.differentiableAt (hD.mem_nhds (hsubD hx))
    · intro x hx
      exact hderiv x hx
  have huniq : ∀ z v v' : ℂ, v.im < L → v'.im < L → v + cl + g v = z → v' + cl + g v' = z →
      v = v' := by
    intro z v v' hv hv' he he'
    have hkey : v' - v = g v - g v' := by linear_combination he' - he
    have hb := hlip v' v hv' hv
    have h1 : ‖v' - v‖ ≤ (1/4) * ‖v - v'‖ := by
      calc ‖v' - v‖ = ‖g v - g v'‖ := by rw [hkey]
        _ ≤ (1/4) * ‖v - v'‖ := hb
    rw [norm_sub_rev] at h1
    have h2 : ‖v - v'‖ = 0 := by linarith [norm_nonneg (v - v')]
    exact sub_eq_zero.mp (norm_eq_zero.mp h2)
  -- (5) the Picard iteration
  let Mf : ℂ → ℂ := fun z => z - cl
  let step : (ℂ → ℂ) → (ℂ → ℂ) := fun F z => Mf z - g (F z)
  let Hseq : ℕ → ℂ → ℂ := fun n => Nat.rec Mf (fun _ F => step F) n
  have hH0 : Hseq 0 = Mf := rfl
  have hHval : ∀ n z, Hseq (n + 1) z = Mf z - g (Hseq n z) := fun n z => rfl
  have hMf_im : ∀ z : ℂ, (Mf z).im = z.im - cl.im := by
    intro z
    show (z - cl).im = z.im - cl.im
    rw [Complex.sub_im]
  have hmem : ∀ n : ℕ, ∀ z : ℂ, z.im < Lz → (Hseq n z).im < L := by
    intro n
    induction n with
    | zero =>
        intro z hz
        rw [hH0]
        rw [hMf_im]
        have : z.im < L + cl.im := lt_trans hz hLz_lt
        linarith
    | succ n ih =>
        intro z hz
        rw [hHval n z, Complex.sub_im, hMf_im]
        have h1 : (Hseq n z).im < L := ih z hz
        have h2 : ‖g (Hseq n z)‖ < 1/4 := hgbd _ h1
        have h3 : -((g (Hseq n z)).im) ≤ ‖g (Hseq n z)‖ := by
          have ha := Complex.abs_im_le_norm (g (Hseq n z))
          have hb : -((g (Hseq n z)).im) ≤ |(g (Hseq n z)).im| := neg_le_abs _
          linarith
        have h4 : z.im < L + cl.im := lt_trans hz hLz_lt
        linarith
  have hmem1 : ∀ n : ℕ, ∀ z : ℂ, z.im < Lz → (Hseq (n + 1) z).im < L - 1/4 := by
    intro n z hz
    rw [hHval n z, Complex.sub_im, hMf_im]
    have h1 : (Hseq n z).im < L := hmem n z hz
    have h2 : ‖g (Hseq n z)‖ < 1/4 := hgbd _ h1
    have h3 : -((g (Hseq n z)).im) ≤ ‖g (Hseq n z)‖ := by
      have ha := Complex.abs_im_le_norm (g (Hseq n z))
      have hb : -((g (Hseq n z)).im) ≤ |(g (Hseq n z)).im| := neg_le_abs _
      linarith
    have h4 : z.im < L + cl.im := lt_trans hz hLz_lt
    linarith
  have hbdseq : ∀ n : ℕ, ∀ z : ℂ, z.im < Lz →
      ‖Hseq (n + 1) z - Hseq n z‖ ≤ (1/4) * (1/4) ^ n := by
    intro n
    induction n with
    | zero =>
        intro z hz
        have hMw : (Mf z).im < L := by rw [hMf_im]; have := lt_trans hz hLz_lt; linarith
        have hb : ‖g (Mf z)‖ < 1/4 := hgbd _ hMw
        have he : Hseq (0 + 1) z - Hseq 0 z = -(g (Mf z)) := by
          rw [hHval 0 z, hH0]
          show (Mf z - g (Mf z)) - Mf z = -(g (Mf z))
          ring
        rw [he, norm_neg, pow_zero, mul_one]
        exact le_of_lt hb
    | succ n ih =>
        intro z hz
        have h1 : (Hseq (n + 1) z).im < L := hmem (n + 1) z hz
        have h2 : (Hseq n z).im < L := hmem n z hz
        have hc := hlip (Hseq (n + 1) z) (Hseq n z) h1 h2
        have he : Hseq (n + 1 + 1) z - Hseq (n + 1) z
            = g (Hseq n z) - g (Hseq (n + 1) z) := by
          rw [hHval (n + 1) z, hHval n z]
          show (Mf z - g (Hseq (n + 1) z)) - (Mf z - g (Hseq n z))
              = g (Hseq n z) - g (Hseq (n + 1) z)
          ring
        rw [he]
        calc ‖g (Hseq n z) - g (Hseq (n + 1) z)‖
            ≤ (1/4) * ‖Hseq n z - Hseq (n + 1) z‖ := hc
          _ = (1/4) * ‖Hseq (n + 1) z - Hseq n z‖ := by rw [norm_sub_rev]
          _ ≤ (1/4) * ((1/4) * (1/4) ^ n) := mul_le_mul_of_nonneg_left (ih z hz) (by norm_num)
          _ = (1/4) * (1/4) ^ (n + 1) := by rw [pow_succ]; ring
  have hdiffseq : ∀ n : ℕ, DifferentiableOn ℂ (Hseq n) {z : ℂ | z.im < Lz} := by
    intro n
    induction n with
    | zero =>
        rw [hH0]
        show DifferentiableOn ℂ (fun z : ℂ => z - cl) {z : ℂ | z.im < Lz}
        exact differentiableOn_id.sub (differentiableOn_const cl)
    | succ n ih =>
        show DifferentiableOn ℂ (step (Hseq n)) {z : ℂ | z.im < Lz}
        show DifferentiableOn ℂ (fun z : ℂ => Mf z - g (Hseq n z)) {z : ℂ | z.im < Lz}
        refine (differentiableOn_id.sub (differentiableOn_const cl)).sub ?_
        exact hg.comp ih (fun z hz => hsubD (hmem n z hz))
  -- (6) the locally uniform limit and its holomorphy
  have hsum_u : Summable (fun n : ℕ => (1/4 : ℝ) * (1/4) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num)).mul_left (1/4)
  let G : ℂ → ℂ := fun z => ∑' n : ℕ, (Hseq (n + 1) z - Hseq n z)
  have hGdiff : DifferentiableOn ℂ G {z : ℂ | z.im < Lz} := by
    show DifferentiableOn ℂ (fun z => ∑' n : ℕ, (Hseq (n + 1) z - Hseq n z)) _
    exact Complex.differentiableOn_tsum_of_summable_norm
      (F := fun n z => Hseq (n + 1) z - Hseq n z)
      (u := fun n => (1/4 : ℝ) * (1/4) ^ n) hsum_u
      (fun n => (hdiffseq (n + 1)).sub (hdiffseq n))
      (isOpen_lt (f := Complex.im) (g := fun _ : ℂ => Lz) Complex.continuous_im continuous_const)
      (fun n z hz => hbdseq n z hz)
  let u : ℂ → ℂ := fun z => Mf z + G z
  have hudiff : DifferentiableOn ℂ u {z : ℂ | z.im < Lz} := by
    show DifferentiableOn ℂ (fun z : ℂ => Mf z + G z) _
    exact (differentiableOn_id.sub (differentiableOn_const cl)).add hGdiff
  have htend : ∀ z : ℂ, z.im < Lz → Filter.Tendsto (fun N : ℕ => Hseq N z) atTop (nhds (u z)) := by
    intro z hz
    have hsummable : Summable (fun n : ℕ => Hseq (n + 1) z - Hseq n z) :=
      Summable.of_norm_bounded hsum_u (fun n => hbdseq n z hz)
    have hsum : HasSum (fun n : ℕ => Hseq (n + 1) z - Hseq n z) (G z) := hsummable.hasSum
    have htel : ∀ N : ℕ, ∑ n ∈ Finset.range N, (Hseq (n + 1) z - Hseq n z) = Hseq N z - Mf z := by
      intro N
      induction N with
      | zero => rw [Finset.sum_range_zero, hH0]; ring
      | succ N ih =>
          rw [Finset.sum_range_succ, ih, hHval N z]
          ring
    have h1 : Filter.Tendsto (fun N : ℕ => Hseq N z - Mf z) atTop (nhds (G z)) := by
      have h := hsum.tendsto_sum_nat
      simpa only [htel] using h
    have h2 : Filter.Tendsto (fun N : ℕ => Mf z + (Hseq N z - Mf z)) atTop (nhds (u z)) := by
      show Filter.Tendsto (fun N : ℕ => Mf z + (Hseq N z - Mf z)) atTop (nhds (Mf z + G z))
      exact h1.const_add (Mf z)
    exact Filter.Tendsto.congr (fun N => by ring) h2
  -- (7) the limit solves the equation; uniqueness; strict depth
  have hmem_le : ∀ z : ℂ, z.im < Lz → (u z).im ≤ L - 1/4 := by
    intro z hz
    have hlim : Filter.Tendsto (fun N : ℕ => (Hseq (N + 1) z).im) atTop (nhds ((u z).im)) := by
      have h1 : Filter.Tendsto (fun N : ℕ => Hseq (N + 1) z) atTop (nhds (u z)) :=
        (htend z hz).comp (tendsto_add_atTop_nat 1)
      exact (Complex.continuous_im.tendsto (u z)).comp h1
    exact le_of_tendsto hlim (Filter.Eventually.of_forall (fun N => le_of_lt (hmem1 N z hz)))
  have hu_sec : ∀ z : ℂ, z.im < Lz → u z + cl + g (u z) = z := by
    intro z hz
    have h1 : Filter.Tendsto (fun N : ℕ => Hseq (N + 1) z) atTop (nhds (u z)) :=
      (htend z hz).comp (tendsto_add_atTop_nat 1)
    have huD : u z ∈ D := by
      refine hsubD ?_
      exact lt_of_le_of_lt (hmem_le z hz) (by linarith)
    have hcont : ContinuousAt g (u z) :=
      hg.continuousOn.continuousAt (hD.mem_nhds huD)
    have h2 : Filter.Tendsto (fun N : ℕ => Hseq (N + 1) z) atTop (nhds (Mf z - g (u z))) := by
      have hg2 : Filter.Tendsto (fun N : ℕ => g (Hseq N z)) atTop (nhds (g (u z))) :=
        hcont.tendsto.comp (htend z hz)
      have h3 : Filter.Tendsto (fun N : ℕ => Mf z - g (Hseq N z)) atTop (nhds (Mf z - g (u z))) :=
        hg2.const_sub (Mf z)
      refine Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun N => ?_)) h3
      exact hHval N z
    have heq : u z = Mf z - g (u z) := tendsto_nhds_unique h1 h2
    nth_rewrite 1 [heq]
    show (z - cl - g (u z)) + cl + g (u z) = z
    ring
  -- (8) the asymptotics
  have hu_deep : Filter.Tendsto (fun z => u z - z + cl) MandelDim.lowerEnd (nhds 0) := by
    refine tendsto_lowerEnd_of_deep (fun ε hε => ?_)
    have hge : {w : ℂ | ‖g w‖ < ε} ∈ MandelDim.lowerEnd := by
      have h1 : {w : ℂ | g w ∈ Metric.ball (0 : ℂ) ε} ∈ Filter.comap Complex.im Filter.atBot :=
        hlim.eventually (Metric.ball_mem_nhds 0 hε)
      refine Filter.mem_of_superset h1 ?_
      intro w hw
      simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hw
    obtain ⟨T, hT⟩ := lowerEnd_eventually hge
    refine ⟨-(min Lz (-T + cl.im - 1/4)), fun z hz => ?_⟩
    have hz' : z.im < min Lz (-T + cl.im - 1/4) := by simpa using hz
    have hzLz : z.im < Lz := lt_of_lt_of_le hz' (min_le_left _ _)
    have hzT : z.im < -T + cl.im - 1/4 := lt_of_lt_of_le hz' (min_le_right _ _)
    have hsec := hu_sec z hzLz
    have hle := hmem_le z hzLz
    have him : (u z).im < -T := by
      have him_eq : (u z).im = z.im - cl.im - (g (u z)).im := by
        have := congrArg Complex.im hsec
        simp only [Complex.add_im, Complex.sub_im] at this
        linarith
      have hbd : ‖g (u z)‖ < 1/4 := hgbd _ (lt_of_le_of_lt hle (by linarith))
      have h3 : -((g (u z)).im) ≤ ‖g (u z)‖ := by
        have ha := Complex.abs_im_le_norm (g (u z))
        have hb : -((g (u z)).im) ≤ |(g (u z)).im| := neg_le_abs _
        linarith
      linarith [him_eq, h3, hbd, hzT]
    have hkey : u z - z + cl = -g (u z) := by linear_combination hsec
    rw [hkey]
    simpa using hT (u z) him
  exact ⟨L, Lz, hL_lt_Y, u, hudiff,
    (fun z hz => ⟨lt_of_le_of_lt (hmem_le z hz) (by linarith), hu_sec z hz⟩),
    (fun z hz v hv hvz => huniq z v (u z) hv (lt_of_le_of_lt (hmem_le z hz) (by linarith)) hvz
      (hu_sec z hz)),
    hu_deep⟩

end

end Work.L62

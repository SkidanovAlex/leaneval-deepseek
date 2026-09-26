/-
Montel's theorem for locally bounded families of holomorphic functions on a domain `U ⊆ ℂ`:
every sequence `F n` of holomorphic functions on `U` with `‖F n z‖ ≤ 1` for all `z ∈ U`
has a subsequence converging locally uniformly on `U` to a holomorphic function `g`.

The proof follows the classical route: a locally bounded family of holomorphic functions is
locally uniformly Lipschitz (Cauchy estimates for the derivative + the mean value inequality),
hence equicontinuous on compact subsets; a diagonal (product space) argument extracts a
subsequence which converges pointwise on a countable dense subset of `U`; equicontinuity
upgrades this to uniform convergence on every compact subset of `U`; finally a locally uniform
limit of holomorphic functions is holomorphic.
-/
import Mathlib

open Metric Filter Set Topology

namespace Work.Smooth.SphereJordan

set_option linter.style.haveILetI false

/-- Cauchy's estimate for the derivative of a holomorphic function bounded by `1`, at the centre
of a closed ball contained in the domain. -/
lemma norm_deriv_le_one {U : Set ℂ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hbf : ∀ z, z ∈ U → ‖f z‖ ≤ 1)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : Metric.closedBall z r ⊆ U) :
    ‖deriv f z‖ ≤ 1 / r := by
  have hcl : closure (Metric.ball z r) = Metric.closedBall z r := closure_ball z hr.ne'
  have hdc : DiffContOnCl ℂ f (Metric.ball z r) :=
    DifferentiableOn.diffContOnCl (hcl.symm ▸ hf.mono hz)
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdc (C := 1)
    (fun w hw => hbf w (hz (Metric.sphere_subset_closedBall hw)))
  simpa using h

/-- A locally bounded family of holomorphic functions on a domain is uniformly Lipschitz on every
compact subset: there is a modulus of uniform equicontinuity, i.e. for every `ε > 0` there is
`δ > 0` such that `‖F n w - F n z‖ ≤ ε` whenever `z` lies in `K` and `‖w - z‖ ≤ δ`. -/
lemma equicont {U : Set ℂ} (hU : IsOpen U) (F : ℕ → ℂ → ℂ)
    (hF : ∀ n, DifferentiableOn ℂ (F n) U) (hb : ∀ n z, z ∈ U → ‖F n z‖ ≤ 1)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∀ ε > 0, ∃ δ > 0, ∀ n z w, z ∈ K → ‖w - z‖ ≤ δ → ‖F n w - F n z‖ ≤ ε := by
  intro ε hε
  obtain ⟨ρ, hρpos, hρ⟩ := hK.exists_cthickening_subset_open hU hKU
  have hr : (0:ℝ) < ρ / 2 := by linarith
  have hKsub : ∀ z ∈ K, Metric.closedBall z ρ ⊆ U := fun z hz =>
    (Metric.closedBall_subset_cthickening hz ρ).trans hρ
  refine ⟨min (ρ/2) (ε * ρ / 2), lt_min hr (by nlinarith), ?_⟩
  intro n z w hzK hwz
  have hzw : w ∈ Metric.closedBall z (ρ/2) :=
    Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using le_trans hwz (min_le_left _ _))
  have hballU : Metric.closedBall z (ρ/2) ⊆ U :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans (hKsub z hzK)
  have hder : ∀ a ∈ Metric.closedBall z (ρ/2), ‖deriv (F n) a‖ ≤ 2/ρ := by
    intro a ha
    have haU : Metric.closedBall a (ρ/2) ⊆ U := by
      have hsub : Metric.closedBall a (ρ/2) ⊆ Metric.closedBall z ρ := by
        intro x hx
        rw [Metric.mem_closedBall] at hx ⊢
        calc dist x z ≤ dist x a + dist a z := dist_triangle _ _ _
          _ ≤ ρ/2 + ρ/2 := add_le_add hx (Metric.mem_closedBall.mp ha)
          _ = ρ := by ring
      exact hsub.trans (hKsub z hzK)
    have h1 := norm_deriv_le_one (hF n) (hb n) hr haU
    have h2 : (1:ℝ)/(ρ/2) = 2/ρ := by field_simp
    linarith [h1, h2]
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (f := F n)
    (s := Metric.closedBall z (ρ/2)) (x := z) (y := w) (C := 2/ρ)
    (fun a ha => (hF n).differentiableAt (hU.mem_nhds (hballU ha)))
    hder (convex_closedBall z (ρ/2)) (Metric.mem_closedBall.mpr (by rw [dist_self]; linarith)) hzw
  calc ‖F n w - F n z‖ ≤ (2/ρ) * ‖w - z‖ := hmv
    _ ≤ (2/ρ) * (min (ρ/2) (ε * ρ / 2)) := mul_le_mul_of_nonneg_left hwz (by positivity)
    _ ≤ (2/ρ) * (ε * ρ / 2) := mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
    _ = ε := by field_simp

/-- Diagonal extraction: for a pointwise bounded sequence of functions indexed by a countable set
`D ⊆ ℂ`, there is a subsequence converging at every point of `D`. This is proved by viewing the
sequence as a sequence in the compact product space `∏_{d ∈ D} closedBall 0 1`, which is
sequentially compact (first-countable compact space), so that convergence in the product topology
gives convergence in every coordinate simultaneously. -/
lemma exists_subseq_of_countable {D : Set ℂ} (hD : D.Countable) (F : ℕ → ℂ → ℂ)
    (hb : ∀ n z, z ∈ D → ‖F n z‖ ≤ 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ L : ℂ → ℂ,
      ∀ d ∈ D, Tendsto (fun n => F (φ n) d) Filter.atTop (𝓝 (L d)) := by
  classical
  haveI : Countable D := hD
  have hA : IsCompact (Set.pi univ (fun _ : D => Metric.closedBall (0:ℂ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_closedBall _ _)
  obtain ⟨a, ha, φ, hφ, hφa⟩ := hA.isCountablyCompact.isSeqCompact
    (x := fun n : ℕ => fun d : D => F n d) (fun n => by
      rw [Set.mem_pi]
      intro d _
      simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact hb n d d.2)
  refine ⟨φ, hφ, fun z => if hz : z ∈ D then a ⟨z, hz⟩ else 0, ?_⟩
  intro d hd
  have hd' : (fun z => if hz : z ∈ D then a ⟨z, hz⟩ else 0) d = a ⟨d, hd⟩ := by simp [hd]
  rw [hd']
  have hcont : Tendsto (fun u : D → ℂ => u ⟨d, hd⟩) (𝓝 a) (𝓝 (a ⟨d, hd⟩)) :=
    (continuous_apply (⟨d, hd⟩ : D)).tendsto a
  have := hcont.comp hφa
  simpa [Function.comp_def] using this

/-- **Montel's theorem.** A locally uniformly bounded sequence of holomorphic functions on an open
set `U ⊆ ℂ` admits a subsequence converging locally uniformly on `U` to a holomorphic limit. -/
theorem montel {U : Set ℂ} (hU : IsOpen U) (F : ℕ → ℂ → ℂ)
    (hF : ∀ n, DifferentiableOn ℂ (F n) U) (hb : ∀ n z, z ∈ U → ‖F n z‖ ≤ 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧
      TendstoLocallyUniformlyOn (fun n => F (φ n)) g Filter.atTop U := by
  classical
  -- a countable dense subset of `U`
  obtain ⟨C, hCcount, hCdense⟩ := TopologicalSpace.exists_countable_dense ℂ
  let D : Set ℂ := C ∩ U
  have hDcount : D.Countable := Set.Countable.mono Set.inter_subset_left hCcount
  have hDsubU : D ⊆ U := Set.inter_subset_right
  have hDclose : ∀ z ∈ U, ∀ ε > 0, ∃ d ∈ D, dist d z < ε := by
    intro z hz ε hε
    obtain ⟨r, hrpos, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
    have hzc : z ∈ closure C := by rw [hCdense.closure_eq]; exact mem_univ z
    obtain ⟨c, hcC, hcz⟩ := Metric.mem_closure_iff.mp hzc (min ε r) (lt_min hε hrpos)
    have hcz' : dist c z < min ε r := by rwa [dist_comm] at hcz
    refine ⟨c, ⟨hcC, ?_⟩, hcz'.trans_le (min_le_left _ _)⟩
    exact hrU (Metric.mem_ball.mpr (hcz'.trans_le (min_le_right _ _)))
  -- extract a subsequence converging on `D`
  obtain ⟨φ, hφ, L, hL⟩ := exists_subseq_of_countable hDcount F (fun n z hz => hb n z (hDsubU hz))
  have heqc : ∀ K : Set ℂ, IsCompact K → K ⊆ U → ∀ ε > 0, ∃ δ > 0,
      ∀ n z w, z ∈ K → ‖w - z‖ ≤ δ → ‖F (φ n) w - F (φ n) z‖ ≤ ε :=
    fun K hK hKU => equicont hU (fun n => F (φ n)) (fun n => hF (φ n))
      (fun n z hz => hb (φ n) z hz) hK hKU
  -- the extracted subsequence is pointwise Cauchy on `U`
  have hCauchy : ∀ x ∈ U, CauchySeq (fun n => F (φ n) x) := by
    intro x hx
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨r, hrpos, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
    have hK : IsCompact (Metric.closedBall x (r/2)) := isCompact_closedBall _ _
    have hKU : Metric.closedBall x (r/2) ⊆ U :=
      (Metric.closedBall_subset_ball (by linarith)).trans hrU
    obtain ⟨δ, hδpos, hδ⟩ := heqc _ hK hKU (ε/4) (by linarith)
    obtain ⟨a, haD, had⟩ := hDclose x hx (min δ (r/2)) (lt_min hδpos (by linarith))
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hL a haD).cauchySeq (ε/4) (by linarith)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hxK : x ∈ Metric.closedBall x (r/2) := by
      rw [Metric.mem_closedBall, dist_self]; linarith
    have hax : ‖a - x‖ ≤ δ := by
      have h' := had
      rw [dist_eq_norm] at h'
      exact le_trans (le_of_lt h') (min_le_left _ _)
    have h1 : ‖F (φ m) a - F (φ m) x‖ ≤ ε/4 := hδ m x a hxK hax
    have h2 : ‖F (φ m) a - F (φ n) a‖ < ε/4 := by
      simpa [dist_eq_norm] using hN m hm n hn
    have h3 : ‖F (φ n) a - F (φ n) x‖ ≤ ε/4 := hδ n x a hxK hax
    have htri : ‖F (φ m) x - F (φ n) x‖ ≤
        ‖F (φ m) x - F (φ m) a‖ + ‖F (φ m) a - F (φ n) a‖ + ‖F (φ n) a - F (φ n) x‖ := by
      have hs : F (φ m) x - F (φ n) x =
          (F (φ m) x - F (φ m) a) + (F (φ m) a - F (φ n) a) + (F (φ n) a - F (φ n) x) := by ring
      rw [hs]
      calc ‖(F (φ m) x - F (φ m) a) + (F (φ m) a - F (φ n) a) + (F (φ n) a - F (φ n) x)‖
          ≤ ‖(F (φ m) x - F (φ m) a) + (F (φ m) a - F (φ n) a)‖ + ‖F (φ n) a - F (φ n) x‖ :=
            norm_add_le _ _
        _ ≤ (‖F (φ m) x - F (φ m) a‖ + ‖F (φ m) a - F (φ n) a‖) + ‖F (φ n) a - F (φ n) x‖ := by
            gcongr
            exact norm_add_le _ _
    rw [dist_eq_norm]
    have h1' : ‖F (φ m) x - F (φ m) a‖ ≤ ε/4 := by rw [norm_sub_rev]; exact h1
    linarith
  -- define the limit function on `U`, extended by `0` outside
  have hlim : ∀ x ∈ U, ∃ y : ℂ, Tendsto (fun n => F (φ n) x) Filter.atTop (𝓝 y) :=
    fun x hx => cauchySeq_tendsto_of_complete (hCauchy x hx)
  choose g hg using hlim
  let G : ℂ → ℂ := fun x => if hx : x ∈ U then g x hx else 0
  have hG : ∀ x ∈ U, Tendsto (fun n => F (φ n) x) Filter.atTop (𝓝 (G x)) := by
    intro x hx
    have hGx : G x = g x hx := by simp [G, hx]
    rw [hGx]
    exact hg x hx
  -- uniform convergence on every compact subset of `U`
  have hUnif : ∀ K : Set ℂ, K ⊆ U → IsCompact K →
      TendstoUniformlyOn (fun n => F (φ n)) G Filter.atTop K := by
    intro K hKU hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := heqc K hK hKU (ε/4) (by linarith)
    -- a finite δ-net in `K` consisting of points of `D`
    obtain ⟨b', hb'sub, hb'fin, hb'cov⟩ := hK.elim_finite_subcover_image (b := D)
      (c := fun a => Metric.ball a δ) (fun a _ => Metric.isOpen_ball) (fun z hz => by
        obtain ⟨a, haD, haz⟩ := hDclose z (hKU hz) δ hδpos
        exact Set.mem_biUnion haD (Metric.mem_ball.mpr (by simpa [dist_comm] using haz)))
    have hev : ∀ a ∈ b', ∀ᶠ n in Filter.atTop, dist (F (φ n) a) (G a) < ε/4 := by
      intro a ha
      have h1 : ∀ᶠ n in Filter.atTop, F (φ n) a ∈ Metric.ball (G a) (ε/4) :=
        (hG a (hDsubU (hb'sub ha))).eventually (Metric.ball_mem_nhds (G a) (by linarith))
      filter_upwards [h1] with n hn
      simpa [Metric.mem_ball, dist_comm] using hn
    have hall : ∀ᶠ n in Filter.atTop, ∀ a ∈ b', dist (F (φ n) a) (G a) < ε/4 :=
      (Set.Finite.eventually_all hb'fin).mpr hev
    filter_upwards [hall] with n hn
    intro z hz
    have hz' := hb'cov hz
    simp only [Set.mem_iUnion] at hz'
    obtain ⟨a, ha, hza⟩ := hz'
    have hzaδ : dist z a < δ := Metric.mem_ball.mp hza
    have hzaδ' : ‖a - z‖ ≤ δ := by
      simpa [dist_eq_norm, norm_sub_rev] using le_of_lt hzaδ
    have hlim2 : ‖G z - G a‖ ≤ ε/4 := by
      have htend : Tendsto (fun n => ‖F (φ n) z - F (φ n) a‖) Filter.atTop (𝓝 ‖G z - G a‖) :=
        ((hG z (hKU hz)).sub (hG a (hDsubU (hb'sub ha)))).norm
      refine le_of_tendsto_of_tendsto' htend tendsto_const_nhds (fun n => ?_)
      rw [norm_sub_rev]
      exact hδ n z a hz hzaδ'
    have hn' : ‖F (φ n) a - G a‖ < ε/4 := by
      simpa [dist_eq_norm] using hn a ha
    have hGA : ‖G a - F (φ n) a‖ < ε/4 := by rw [norm_sub_rev]; exact hn'
    have htri : ‖G z - F (φ n) z‖ ≤
        ‖G z - G a‖ + ‖G a - F (φ n) a‖ + ‖F (φ n) a - F (φ n) z‖ := by
      have hs : G z - F (φ n) z =
          (G z - G a) + (G a - F (φ n) a) + (F (φ n) a - F (φ n) z) := by ring
      rw [hs]
      calc ‖(G z - G a) + (G a - F (φ n) a) + (F (φ n) a - F (φ n) z)‖
          ≤ ‖(G z - G a) + (G a - F (φ n) a)‖ + ‖F (φ n) a - F (φ n) z‖ := norm_add_le _ _
        _ ≤ (‖G z - G a‖ + ‖G a - F (φ n) a‖) + ‖F (φ n) a - F (φ n) z‖ := by
            gcongr
            exact norm_add_le _ _
    calc dist (G z) (F (φ n) z) = ‖G z - F (φ n) z‖ := dist_eq_norm _ _
      _ ≤ ε/4 + ε/4 + ε/4 := by linarith [htri, hlim2, hGA, hδ n z a hz hzaδ']
      _ < ε := by linarith
  have hTLU : TendstoLocallyUniformlyOn (fun n => F (φ n)) G Filter.atTop U :=
    ((tendstoLocallyUniformlyOn_TFAE (fun n => F (φ n)) G Filter.atTop hU).out 1 2).mpr hUnif
  exact ⟨φ, hφ, G, TendstoLocallyUniformlyOn.differentiableOn hTLU
    (Filter.Eventually.of_forall fun n => hF (φ n)) hU, hTLU⟩

end Work.Smooth.SphereJordan

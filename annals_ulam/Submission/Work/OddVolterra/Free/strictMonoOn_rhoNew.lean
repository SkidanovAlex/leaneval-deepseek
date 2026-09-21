import Mathlib
import Submission.Work.OddCurve.LowSlope.CurveDefs
import Submission.Work.OddCurve.LowSlope.GlueDefs

/-!
# Strict monotonicity of `u ↦ ρNew R r u * u`

`Work.OddCurve.LowSlope.rhoNew R r u` is the radial function of the reconstructed body:
`R (arccos u)` on the right half and `r (arccos (-u))` on the left half.  We show that
`G u = ρNew R r u * u` is strictly increasing on `(-1,1)`, given

* that `G` agrees with the anchor's `ρa u * u` on the cap `|u| ≤ 4/5`, which is strictly
  increasing there, and
* that the reparametrised functions `σ ↦ R (arctan σ) cos (arctan σ)` and
  `σ ↦ r (arctan σ) cos (arctan σ)` are strictly decreasing on `(0, 3/4)`, which controls `G`
  on `(4/5, 1)` and `(-1, -4/5)` respectively (the change of variable `u = cos (arctan σ)`
  maps `(4/5,1)` antitonically onto `(0,3/4)`).

The three pieces are glued at the junction points `±4/5` using continuity of `G` there.
-/

namespace Work.OddVolterra.Free

open Set Filter
open scoped Topology

noncomputable section

private lemma strictAntiOn_neg_univ : StrictAntiOn (fun x : ℝ => -x) Set.univ :=
  fun a _ b _ hab => by simpa using neg_lt_neg hab

/-- **Gluing lemma.**  If `f` is strictly increasing on `(a,c)` and on `(c,b)` and is continuous
at the junction point `c`, then `f` is strictly increasing on `(a,b)`.

The only content is the strictness of the comparison across `c`: both one-sided limits of `f` at
`c` equal `f c`, and the strict monotonicity on either side gives `f x < f t ≤ f c ≤ f s < f y`
for `x < t < c < s < y`. -/
private lemma strictMonoOn_Ioo_of_strictMonoOn_Ioo_of_continuousAt {f : ℝ → ℝ} {a c b : ℝ}
    (h1 : StrictMonoOn f (Set.Ioo a c)) (h2 : StrictMonoOn f (Set.Ioo c b))
    (hc : ContinuousAt f c) : StrictMonoOn f (Set.Ioo a b) := by
  have hliml : Tendsto f (𝓝[<] c) (𝓝 (f c)) := hc.tendsto.mono_left nhdsWithin_le_nhds
  have hlimr : Tendsto f (𝓝[>] c) (𝓝 (f c)) := hc.tendsto.mono_left nhdsWithin_le_nhds
  have hL : ∀ t ∈ Set.Ioo a c, f t ≤ f c := by
    intro t ht
    refine ge_of_tendsto hliml ?_
    have hmem : Set.Ioo t c ∈ 𝓝[<] c := by
      rw [nhdsWithin, Filter.mem_inf_iff]
      exact ⟨Set.Ioi t, Ioi_mem_nhds ht.2, Set.Iio c, Filter.mem_principal_self _,
        (by ext x; simp [Set.mem_Ioo, Set.mem_Ioi, Set.mem_Iio])⟩
    filter_upwards [hmem] with s hs
    exact le_of_lt (h1 ht ⟨lt_trans ht.1 hs.1, hs.2⟩ hs.1)
  have hR : ∀ t ∈ Set.Ioo c b, f c ≤ f t := by
    intro t ht
    refine le_of_tendsto hlimr ?_
    have hmem : Set.Ioo c t ∈ 𝓝[>] c := by
      rw [nhdsWithin, Filter.mem_inf_iff]
      exact ⟨Set.Iio t, Iio_mem_nhds ht.1, Set.Ioi c, Filter.mem_principal_self _,
        (by ext x; simp [Set.mem_Ioo, Set.mem_Ioi, Set.mem_Iio, and_comm])⟩
    filter_upwards [hmem] with s hs
    exact le_of_lt (h2 ⟨hs.1, lt_trans hs.2 ht.2⟩ ht hs.2)
  intro x hx y hy hxy
  rcases lt_or_ge x c with hxc | hxc
  · rcases lt_or_ge y c with hyc | hyc
    · exact h1 ⟨hx.1, hxc⟩ ⟨hy.1, hyc⟩ hxy
    · obtain ⟨t, hxt, htc⟩ := exists_between hxc
      have ht : t ∈ Set.Ioo a c := ⟨lt_trans hx.1 hxt, htc⟩
      have hxfc : f x < f c := lt_of_lt_of_le (h1 ⟨hx.1, hxc⟩ ht hxt) (hL t ht)
      rcases eq_or_lt_of_le hyc with h | h
      · rw [← h]; exact hxfc
      · obtain ⟨s, hcs, hsy⟩ := exists_between h
        have hs : s ∈ Set.Ioo c b := ⟨hcs, lt_trans hsy hy.2⟩
        exact lt_trans hxfc (lt_of_le_of_lt (hR s hs) (h2 hs ⟨h, hy.2⟩ hsy))
  · rcases lt_or_eq_of_le hxc with h | h
    · have hxc' : x ∈ Set.Ioo c b := ⟨h, hx.2⟩
      exact h2 hxc' ⟨lt_trans h hxy, hy.2⟩ hxy
    · rw [← h]
      have hcy : c < y := by rw [h]; exact hxy
      obtain ⟨s, hcs, hsy⟩ := exists_between hcy
      have hs : s ∈ Set.Ioo c b := ⟨hcs, lt_trans hsy hy.2⟩
      have hyc : y ∈ Set.Ioo c b := ⟨hcy, hy.2⟩
      exact lt_of_le_of_lt (hR s hs) (h2 hs hyc hsy)

/-- `cos (arctan (3/4)) = 4/5`. -/
private lemma cos_arctan_three_quarters : Real.cos (Real.arctan (3 / 4)) = 4 / 5 := by
  have hsq : (1 : ℝ) + (3 / 4) ^ 2 = (5 / 4) ^ 2 := by norm_num
  rw [Real.cos_arctan, hsq, Real.sqrt_sq (by norm_num)]
  norm_num

/-- `arccos (4/5) = arctan (3/4)`. -/
private lemma arccos_four_fifths : Real.arccos (4 / 5 : ℝ) = Real.arctan (3 / 4) := by
  rw [← cos_arctan_three_quarters,
    Real.arccos_cos (Real.arctan_nonneg.mpr (by norm_num)) (by
      linarith [Real.arctan_lt_pi_div_two (3 / 4), Real.pi_pos])]

/-- **The right half, reparametrised.**  If `σ ↦ A (arctan σ) cos (arctan σ)` is continuous on
`(0, 3/4)` with strictly negative derivative there, then `u ↦ A (arccos u) * u` is strictly
increasing on `(4/5, 1)`.

Indeed, `u ↦ tan (arccos u)` maps `(4/5,1)` antitonically onto `(0,3/4)`, `cos (arctan σ) = u`
inverts it, and the composition of two antitone maps is increasing. -/
private lemma strictMonoOn_arccos_mul {A : ℝ → ℝ}
    (hcont : ContinuousOn (fun σ : ℝ => A (Real.arctan σ) * Real.cos (Real.arctan σ))
      (Set.Ioo 0 (3 / 4)))
    (hderiv : ∀ σ ∈ Set.Ioo (0 : ℝ) (3 / 4),
      deriv (fun τ : ℝ => A (Real.arctan τ) * Real.cos (Real.arctan τ)) σ < 0) :
    StrictMonoOn (fun u : ℝ => A (Real.arccos u) * u) (Set.Ioo (4 / 5) 1) := by
  have hFanti : StrictAntiOn (fun σ : ℝ => A (Real.arctan σ) * Real.cos (Real.arctan σ))
      (Set.Ioo 0 (3 / 4)) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioo 0 (3 / 4)) hcont ?_
    intro σ hσ
    rw [interior_Ioo] at hσ
    exact hderiv σ hσ
  -- the reparametrisation `u ↦ tan (arccos u)`
  have hψanti : StrictAntiOn (fun u : ℝ => Real.tan (Real.arccos u)) (Set.Ioo (4 / 5) 1) := by
    have h1 : StrictAntiOn Real.arccos (Set.Ioo (4 / 5 : ℝ) 1) :=
      Real.strictAntiOn_arccos.mono fun x hx => ⟨by linarith [hx.1], le_of_lt hx.2⟩
    have h2 : Set.MapsTo Real.arccos (Set.Ioo (4 / 5 : ℝ) 1)
        (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
      intro u hu
      exact ⟨by linarith [Real.arccos_nonneg u, Real.pi_pos],
        Real.arccos_lt_pi_div_two.mpr (by linarith [hu.1])⟩
    exact Real.strictMonoOn_tan.comp_strictAntiOn h1 h2
  have hψmaps : Set.MapsTo (fun u : ℝ => Real.tan (Real.arccos u))
      (Set.Ioo (4 / 5) 1) (Set.Ioo 0 (3 / 4)) := by
    intro u hu
    have harccos_pos : 0 < Real.arccos u := Real.arccos_pos.mpr hu.2
    have harccos_lt : Real.arccos u < Real.arctan (3 / 4) := by
      rw [← arccos_four_fifths]
      exact Real.strictAntiOn_arccos
        (show (4 / 5 : ℝ) ∈ Set.Icc (-1) 1 from ⟨by norm_num, by norm_num⟩)
        (show u ∈ Set.Icc (-1) 1 from ⟨by linarith [hu.1], le_of_lt hu.2⟩) hu.1
    constructor
    · exact Real.tan_pos_of_pos_of_lt_pi_div_two harccos_pos
        (Real.arccos_lt_pi_div_two.mpr (by linarith [hu.1]))
    · have h := Real.tan_lt_tan_of_lt_of_lt_pi_div_two
        (by linarith [Real.arccos_nonneg u, Real.pi_pos])
        (Real.arctan_lt_pi_div_two _) harccos_lt
      rwa [Real.tan_arctan] at h
  have hEq : Set.EqOn (fun u : ℝ => A (Real.arccos u) * u)
      ((fun σ : ℝ => A (Real.arctan σ) * Real.cos (Real.arctan σ)) ∘
        (fun u : ℝ => Real.tan (Real.arccos u))) (Set.Ioo (4 / 5) 1) := by
    intro u hu
    have hσ := hψmaps hu
    have harccos_pos : 0 < Real.arccos u := Real.arccos_pos.mpr hu.2
    have harctan_eq : Real.arctan (Real.tan (Real.arccos u)) = Real.arccos u :=
      Real.arctan_tan (by linarith [Real.arccos_nonneg u, Real.pi_pos])
        (Real.arccos_lt_pi_div_two.mpr (by linarith [hu.1]))
    simp only [Function.comp_apply]
    rw [harctan_eq, Real.cos_arccos (by linarith [hu.1]) (le_of_lt hu.2)]
  have hcomp : StrictMonoOn ((fun σ : ℝ => A (Real.arctan σ) * Real.cos (Real.arctan σ)) ∘
      (fun u : ℝ => Real.tan (Real.arccos u))) (Set.Ioo (4 / 5) 1) :=
    StrictAntiOn.comp hFanti hψanti hψmaps
  intro x hx y hy hxy
  rw [hEq hx, hEq hy]
  exact hcomp hx hy hxy

theorem strictMonoOn_rhoNew {R r ρa : ℝ → ℝ}
    (hRsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hrsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r (Set.Icc 0 (Real.pi / 2)))
    (hRpos : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), 0 < R α)
    (hrpos : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), 0 < r α)
    (hRm : ∀ σ : ℝ, 0 < σ → σ < 3 / 4 →
      deriv (fun τ : ℝ => R (Real.arctan τ) * Real.cos (Real.arctan τ)) σ < 0)
    (hrm : ∀ σ : ℝ, 0 < σ → σ < 3 / 4 →
      deriv (fun τ : ℝ => r (Real.arctan τ) * Real.cos (Real.arctan τ)) σ < 0)
    (hρapos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρa u)
    (hρamono : StrictMonoOn (fun u : ℝ => ρa u * u) (Set.Ioo (-1 : ℝ) 1))
    (hcap : ∀ u : ℝ, |u| ≤ 4 / 5 → Work.OddCurve.LowSlope.rhoNew R r u = ρa u) :
    StrictMonoOn (fun u : ℝ => Work.OddCurve.LowSlope.rhoNew R r u * u) (Set.Ioo (-1 : ℝ) 1) := by
  set G : ℝ → ℝ := fun u => Work.OddCurve.LowSlope.rhoNew R r u * u with hG
  have hRcontOn : ContinuousOn R (Set.Icc 0 (Real.pi / 2)) := hRsm.continuousOn
  have hrcontOn : ContinuousOn r (Set.Icc 0 (Real.pi / 2)) := hrsm.continuousOn
  have harctan_maps : Set.MapsTo Real.arctan (Set.Ioo (0 : ℝ) (3 / 4))
      (Set.Icc 0 (Real.pi / 2)) := fun σ hσ =>
    ⟨le_of_lt (Real.arctan_pos.mpr hσ.1), le_of_lt (Real.arctan_lt_pi_div_two σ)⟩
  have hcontF : ContinuousOn (fun σ : ℝ => R (Real.arctan σ) * Real.cos (Real.arctan σ))
      (Set.Ioo 0 (3 / 4)) :=
    (hRcontOn.comp Real.continuous_arctan.continuousOn harctan_maps).mul
      (Real.continuous_cos.continuousOn.comp Real.continuous_arctan.continuousOn
        (fun σ _ => Set.mem_univ _))
  have hcontr : ContinuousOn (fun σ : ℝ => r (Real.arctan σ) * Real.cos (Real.arctan σ))
      (Set.Ioo 0 (3 / 4)) :=
    (hrcontOn.comp Real.continuous_arctan.continuousOn harctan_maps).mul
      (Real.continuous_cos.continuousOn.comp Real.continuous_arctan.continuousOn
        (fun σ _ => Set.mem_univ _))
  -- the right piece `(4/5, 1)`
  have hright : StrictMonoOn G (Set.Ioo (4 / 5) 1) := by
    have hbase : StrictMonoOn (fun u : ℝ => R (Real.arccos u) * u) (Set.Ioo (4 / 5) 1) :=
      strictMonoOn_arccos_mul hcontF (fun σ hσ => hRm σ hσ.1 hσ.2)
    intro x hx y hy hxy
    have hx0 : (0 : ℝ) < x := by linarith [hx.1]
    have hy0 : (0 : ℝ) < y := by linarith [hy.1]
    have ex : G x = R (Real.arccos x) * x := by
      rw [hG]; simp only [Work.OddCurve.LowSlope.rhoNew_of_nonneg (le_of_lt hx0)]
    have ey : G y = R (Real.arccos y) * y := by
      rw [hG]; simp only [Work.OddCurve.LowSlope.rhoNew_of_nonneg (le_of_lt hy0)]
    rw [ex, ey]
    exact hbase hx hy hxy
  -- the left piece `(-1, -4/5)`
  have hleft : StrictMonoOn G (Set.Ioo (-1) (-4 / 5)) := by
    have hbase : StrictMonoOn (fun v : ℝ => r (Real.arccos v) * v) (Set.Ioo (4 / 5) 1) :=
      strictMonoOn_arccos_mul hcontr (fun σ hσ => hrm σ hσ.1 hσ.2)
    intro x hx y hy hxy
    have hx' : -x ∈ Set.Ioo (4 / 5 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hy' : -y ∈ Set.Ioo (4 / 5 : ℝ) 1 := ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have h := hbase hy' hx' (by linarith : -y < -x)
    have ex : G x = -(r (Real.arccos (-x)) * (-x)) := by
      rw [hG]
      simp only [Work.OddCurve.LowSlope.rhoNew_of_neg (by linarith [hx.2] : x < 0)]
      ring
    have ey : G y = -(r (Real.arccos (-y)) * (-y)) := by
      rw [hG]
      simp only [Work.OddCurve.LowSlope.rhoNew_of_neg (by linarith [hy.2] : y < 0)]
      ring
    rw [ex, ey]
    linarith
  -- the middle piece `(-4/5, 4/5)`, where `G` is the anchor's `ρa u * u`
  have hmid : StrictMonoOn G (Set.Ioo (-4 / 5) (4 / 5)) := by
    intro x hx y hy hxy
    have hxabs : |x| ≤ 4 / 5 := le_of_lt (abs_lt.mpr ⟨by linarith [hx.1], hx.2⟩)
    have hyabs : |y| ≤ 4 / 5 := le_of_lt (abs_lt.mpr ⟨by linarith [hy.1], hy.2⟩)
    have ex : G x = ρa x * x := by rw [hG]; simp only [hcap x hxabs]
    have ey : G y = ρa y * y := by rw [hG]; simp only [hcap y hyabs]
    rw [ex, ey]
    exact hρamono ⟨by linarith [hx.1], by linarith [hx.2]⟩
      ⟨by linarith [hy.1], by linarith [hy.2]⟩ hxy
  -- continuity of `G` at the junction points
  have hmiddle : Set.Icc (0 : ℝ) (Real.pi / 2) ∈ 𝓝 (Real.arccos (4 / 5)) :=
    Filter.mem_of_superset
      (isOpen_Ioo.mem_nhds (show Real.arccos (4 / 5) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) from
        ⟨by rw [arccos_four_fifths]; exact Real.arctan_pos.mpr (by norm_num),
         Real.arccos_lt_pi_div_two.mpr (by norm_num)⟩))
      Set.Ioo_subset_Icc_self
  have hc_right : ContinuousAt G (4 / 5) := by
    have h1 : ContinuousAt (fun u : ℝ => R (Real.arccos u) * u) (4 / 5) :=
      ((hRcontOn.continuousAt hmiddle).comp Real.continuous_arccos.continuousAt).mul
        continuousAt_id
    refine ContinuousAt.congr h1 ?_
    filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 4 / 5)] with u hu
    rw [hG]
    simp only [Work.OddCurve.LowSlope.rhoNew_of_nonneg (le_of_lt hu)]
  have hc_left : ContinuousAt G (-4 / 5) := by
    have hmem' : Set.Icc (0 : ℝ) (Real.pi / 2) ∈ 𝓝 (Real.arccos (-(-4 / 5))) := by
      rw [show -(-4 / 5 : ℝ) = 4 / 5 from by norm_num]
      exact hmiddle
    have h2 : ContinuousAt (fun u : ℝ => r (Real.arccos (-u)) * u) (-4 / 5) := by
      have h3 : ContinuousAt (fun u : ℝ => Real.arccos (-u)) (-4 / 5) := by
        simpa [Function.comp_def] using
          (Real.continuous_arccos.continuousAt.comp continuousAt_neg)
      have h4 : ContinuousAt (fun u : ℝ => r (Real.arccos (-u))) (-4 / 5) :=
        ContinuousAt.comp (x := -4 / 5) (f := fun u : ℝ => Real.arccos (-u)) (g := r)
          (hrcontOn.continuousAt hmem') h3
      exact h4.mul continuousAt_id
    refine ContinuousAt.congr h2 ?_
    filter_upwards [Iio_mem_nhds (by norm_num : (-4 / 5 : ℝ) < 0)] with u hu
    rw [hG]
    simp only [Work.OddCurve.LowSlope.rhoNew_of_neg hu]
  have hA : StrictMonoOn G (Set.Ioo (-4 / 5) 1) :=
    strictMonoOn_Ioo_of_strictMonoOn_Ioo_of_continuousAt hmid hright hc_right
  exact strictMonoOn_Ioo_of_strictMonoOn_Ioo_of_continuousAt hleft hA hc_left

end

end Work.OddVolterra.Free

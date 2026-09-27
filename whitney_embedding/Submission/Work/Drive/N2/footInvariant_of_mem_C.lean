import Mathlib
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2.saddleScaled
import Submission.Work.Drive.N2.saddlePack
import Submission.Work.Drive.N2.swlLanding
import Submission.Work.Drive.N2.levelBoundsOfJourney
import Submission.Work.Drive.N2.saddleWindow_legality

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Filter

/-- **The outer sub-case of the foot invariant of the saddle window.**  For a saddle window datum,
with the canonical scaled coordinate `Z` and anchor level `a = f p - (D.ρ D.j / 8)² * η`, a point `y`
of the window band `(a, a + 2 lam0² η)` which is outside the model region
`{y ∈ source | |Im (Z y)²| < c₀}` and whose *foot* (the transport of `y` to the anchor level along the
model-adapted flow `D.Φ`) lies in the ODE region `D.C D.j`, has foot invariant at least `c₀`. -/
theorem footInvariant_of_mem_C {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    (hsgn : D.s₁ D.j = - D.s₂ D.j)
    {η δ c₀ : ℝ} (hη : 0 < η) (hη' : η < 1 / 10) (hδ : 0 < δ) (hδ' : δ < 1 / 10)
    (hc₀ : 2 - 2 * δ < c₀) (hc₀' : c₀ < 2)
    (hsep : (D.ρ D.j / 8) ^ 2 * η < 2 * D.ηd) :
    ∃ (Z : M → ℂ) (lam0 a : ℝ), 0 < lam0 ∧ lam0 = D.ρ D.j / 8 ∧ a = f p - lam0 ^ 2 * η ∧
      (∀ y ∈ (D.φ D.j).source, f y = f p + lam0 ^ 2 * ((Z y) ^ 2).re) ∧
      (∀ y : M, y ∉ Work.Drive.N2.saddleRegion (D.φ D.j).source Z c₀ →
        f y ∈ Set.Ioo a (a + 2 * lam0 ^ 2 * η) →
        Work.Drive.N2.footMap D.Φ f a y ∈ D.C D.j →
        c₀ ≤ |((Z (Work.Drive.N2.footMap D.Φ f a y)) ^ 2).im|) := by
  classical
  obtain ⟨φ', Zs, Z, lam0, hlam0pos, hlam0, hsrc, hball, hZs, hZrel, hZsm, hZinj, hZimm,
    hlevZ, hlevZs, hODE, him⟩ := saddlePack (D := D) hsgn
  refine ⟨Z, lam0, f p - lam0 ^ 2 * η, hlam0pos, hlam0, rfl, hlevZ, ?_⟩
  intro y hy hband hfootC
  have hband_lo : f p - lam0 ^ 2 * η < f y := hband.1
  have hband_hi : f y < f p + lam0 ^ 2 * η := by
    have h : (f p - lam0 ^ 2 * η) + 2 * lam0 ^ 2 * η = f p + lam0 ^ 2 * η := by ring
    rw [← h]
    exact hband.2
  set τ : ℝ := f p - lam0 ^ 2 * η - f y with hτdef
  have hτneg : τ < 0 := by rw [hτdef]; linarith
  have hfootτ : footMap D.Φ f (f p - lam0 ^ 2 * η) y = D.Φ (τ, y) := by
    rw [footMap, hτdef]
  have hγ : Continuous fun t : ℝ => D.Φ (t, y) :=
    D.hΦsm.continuous.comp (continuous_id.prodMk continuous_const)
  have hCclosed : IsClosed (D.C D.j) := D.hCclosed D.j
  set S : Set ℝ := {t : ℝ | t ∈ Set.Icc τ 0 ∧ D.Φ (t, y) ∉ D.C D.j} with hSdef
  have hSmem : ∀ t : ℝ, t ∈ S ↔ (t ∈ Set.Icc τ 0 ∧ D.Φ (t, y) ∉ D.C D.j) := by
    intro t
    rw [hSdef, Set.mem_ofPred_eq]
  have hτnotS : τ ∉ S := fun h => h.2 (hfootτ ▸ hfootC)
  by_cases hSne : S.Nonempty
  · -- ===== The trace leaves the ODE region: the first exit point has chart norm `≥ ρ j` =====
    set t₁ : ℝ := sInf S with ht₁def
    have hSbdd : BddBelow S := ⟨τ, fun t ht => ((hSmem t).mp ht).1.1⟩
    have ht₁ge : τ ≤ t₁ := le_csInf hSne (fun t ht => ((hSmem t).mp ht).1.1)
    have ht₁le : t₁ ≤ 0 := by
      obtain ⟨s, hs⟩ := hSne
      exact le_trans (csInf_le hSbdd hs) ((hSmem s).mp hs).1.2
    have ht₁clS : t₁ ∈ closure S := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨s, hsS, hslt⟩ : ∃ s ∈ S, s < t₁ + ε := by
        by_contra hcon
        push Not at hcon
        have hle : t₁ + ε ≤ t₁ := le_csInf hSne hcon
        linarith
      refine ⟨s, hsS, ?_⟩
      rw [Real.dist_eq, abs_lt]
      have hle : t₁ ≤ s := csInf_le hSbdd hsS
      constructor <;> linarith
    -- the infimum is not itself an exit time
    have ht₁notS : t₁ ∉ S := by
      intro htS
      have hzC : D.Φ (t₁, y) ∈ D.C D.j := by
        rcases eq_or_lt_of_le ht₁ge with heq | hlt
        · exact absurd (heq ▸ htS) hτnotS
        · have hzlim : D.Φ (t₁, y) ∈ closure (D.C D.j) := by
            rw [mem_closure_iff]
            intro U hU hzU
            have hnh : (fun t : ℝ => D.Φ (t, y)) ⁻¹' U ∈ 𝓝 t₁ :=
              hγ.continuousAt.preimage_mem_nhds (hU.mem_nhds hzU)
            obtain ⟨ε₀, hε₀pos, hε₀⟩ := Metric.mem_nhds_iff.mp hnh
            have hu_lt : max τ (t₁ - ε₀ / 2) < t₁ := max_lt hlt (by linarith)
            have hu_ge : τ ≤ max τ (t₁ - ε₀ / 2) := le_max_left _ _
            have huball : max τ (t₁ - ε₀ / 2) ∈ Metric.ball t₁ ε₀ := by
              rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith)]
              have h2 : t₁ - ε₀ / 2 ≤ max τ (t₁ - ε₀ / 2) := le_max_right _ _
              linarith
            have huC : D.Φ (max τ (t₁ - ε₀ / 2), y) ∈ D.C D.j := by
              by_contra hbad
              have huS : max τ (t₁ - ε₀ / 2) ∈ S :=
                (hSmem _).mpr ⟨⟨hu_ge, le_trans hu_lt.le ht₁le⟩, hbad⟩
              exact absurd (csInf_le hSbdd huS) (not_le.mpr hu_lt)
            exact ⟨D.Φ (max τ (t₁ - ε₀ / 2), y), hε₀ huball, huC⟩
          rwa [hCclosed.closure_eq] at hzlim
      exact htS.2 hzC
    have ht₁C : D.Φ (t₁, y) ∈ D.C D.j := by
      by_contra hbad
      exact ht₁notS ((hSmem t₁).mpr ⟨⟨ht₁ge, ht₁le⟩, hbad⟩)
    -- the trace stays in the ODE region up to `t₁`
    have hconf : ∀ u ∈ Set.Icc τ t₁, D.Φ (u, y) ∈ D.C D.j := by
      intro u hu
      rcases eq_or_lt_of_le hu.2 with h | h
      · rw [h]; exact ht₁C
      · by_contra hbad
        have huS : u ∈ S := (hSmem u).mpr ⟨⟨hu.1, le_trans h.le ht₁le⟩, hbad⟩
        exact absurd (csInf_le hSbdd huS) (not_le.mpr h)
    -- the invariant is transported from the foot to `t₁`
    have htrans : ((Zs (D.Φ (t₁, y))) ^ 2).im = ((Zs (D.Φ (τ, y))) ^ 2).im :=
      swlL_im_eq D Zs him ht₁ge hconf
    -- the exit point is a frontier point of `C j`
    have hzcl : D.Φ (t₁, y) ∈ closure ((D.C D.j)ᶜ) := by
      have himg : D.Φ (t₁, y) ∈ closure ((fun t : ℝ => D.Φ (t, y)) '' S) :=
        image_closure_subset_closure_image hγ ⟨t₁, ht₁clS, rfl⟩
      refine closure_mono ?_ himg
      rintro z ⟨s, hs, rfl⟩
      exact ((hSmem s).mp hs).2
    have hznorm : D.ρ D.j ≤ ‖φ' (D.Φ (t₁, y))‖ :=
      swlL_norm_ge_rho_of_closure_compl D φ' hsrc hball ht₁C hzcl
    have hzsrc : D.Φ (t₁, y) ∈ (D.φ D.j).source := D.hCsub D.j ht₁C
    -- the level of the exit point is still in the window
    have hzlev : |f (D.Φ (t₁, y)) - f p| ≤ lam0 ^ 2 * η := by
      have hb := levelBoundsOfJourney D (x := y) (τ := t₁) ht₁le
      have h1 : f p - lam0 ^ 2 * η ≤ f (D.Φ (t₁, y)) := by
        have h2 : f y + τ = f p - lam0 ^ 2 * η := by rw [hτdef]; ring
        linarith [hb.1, ht₁ge, h2]
      have h3 : f (D.Φ (t₁, y)) < f p + lam0 ^ 2 * η := lt_of_le_of_lt hb.2 hband_hi
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    have hrez : ((Zs (D.Φ (t₁, y))) ^ 2).re = f (D.Φ (t₁, y)) - f p := by
      have h := hlevZs (D.Φ (t₁, y)) hzsrc
      linarith
    -- the fourth-power identity and the norm bound at the exit point
    have hfour : ‖φ' (D.Φ (t₁, y))‖ ^ 4 = ((Zs (D.Φ (t₁, y))) ^ 2).re ^ 2
        + ((Zs (D.Φ (t₁, y))) ^ 2).im ^ 2 := swlL_Zs_fourth φ' Zs hZs _
    have hρ8 : D.ρ D.j = 8 * lam0 := by rw [hlam0]; ring
    have hzn8 : 8 * lam0 ≤ ‖φ' (D.Φ (t₁, y))‖ := by rw [← hρ8]; exact hznorm
    have hkey : lam0 ^ 4 * 4095 ≤ ((Zs (D.Φ (t₁, y))) ^ 2).im ^ 2 := by
      have h1 : (8 * lam0) ^ 4 ≤ ((Zs (D.Φ (t₁, y))) ^ 2).re ^ 2
          + ((Zs (D.Φ (t₁, y))) ^ 2).im ^ 2 := by
        rw [← hfour]
        exact pow_le_pow_left₀ (by positivity) hzn8 4
      have h2 : ((Zs (D.Φ (t₁, y))) ^ 2).re ^ 2 ≤ (lam0 ^ 2 * η) ^ 2 := by
        rw [hrez, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hzlev 2
      have h3 : (8 * lam0) ^ 4 - (lam0 ^ 2 * η) ^ 2 = lam0 ^ 4 * (4096 - η ^ 2) := by ring
      have h4 : η ^ 2 ≤ 1 := by nlinarith [hη, hη']
      have h6 : lam0 ^ 4 * 4095 ≤ lam0 ^ 4 * (4096 - η ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith [h1, h2, h3, h6]
    have hIm2 : 4095 ≤ ((Z (D.Φ (t₁, y))) ^ 2).im ^ 2 := by
      have h1 : ((Zs (D.Φ (t₁, y))) ^ 2).im = lam0 ^ 2 * ((Z (D.Φ (t₁, y))) ^ 2).im :=
        swl_im_sq_eq_div (hZrel (D.Φ (t₁, y)))
      have h2 : lam0 ^ 4 * ((Z (D.Φ (t₁, y))) ^ 2).im ^ 2
          = ((Zs (D.Φ (t₁, y))) ^ 2).im ^ 2 := by
        rw [h1]; ring
      have h3 : lam0 ^ 4 * 4095 ≤ lam0 ^ 4 * ((Z (D.Φ (t₁, y))) ^ 2).im ^ 2 := by
        rw [h2]; exact hkey
      exact le_of_mul_le_mul_left h3 (by positivity : (0 : ℝ) < lam0 ^ 4)
    have hgoal : c₀ ≤ |((Z (D.Φ (t₁, y))) ^ 2).im| := by
      have hc0pos : 0 ≤ c₀ := by linarith [hc₀, hδ]
      have h3 : c₀ ^ 2 ≤ ((Z (D.Φ (t₁, y))) ^ 2).im ^ 2 := by
        have h4 : c₀ ^ 2 < 4 := by nlinarith [hc₀', hc0pos]
        linarith
      have h4 := sq_le_sq.mp h3
      rwa [abs_of_nonneg hc0pos] at h4
    have hZim : ((Z (D.Φ (t₁, y))) ^ 2).im = ((Z (D.Φ (τ, y))) ^ 2).im := by
      have h1 : lam0 ^ 2 * ((Z (D.Φ (t₁, y))) ^ 2).im
          = lam0 ^ 2 * ((Z (D.Φ (τ, y))) ^ 2).im := by
        rw [← swl_im_sq_eq_div (hZrel (D.Φ (t₁, y))),
          ← swl_im_sq_eq_div (hZrel (D.Φ (τ, y))), htrans]
      exact mul_left_cancel₀ (ne_of_gt (pow_pos hlam0pos 2)) h1
    rw [hfootτ, ← hZim]
    exact hgoal
  · -- ===== The trace stays in the ODE region: the invariant is transported all the way =====
    have hconf : ∀ u ∈ Set.Icc τ 0, D.Φ (u, y) ∈ D.C D.j := by
      intro u hu
      by_contra hbad
      exact hSne ⟨u, (hSmem u).mpr ⟨hu, hbad⟩⟩
    have htrans : ((Zs (D.Φ (0, y))) ^ 2).im = ((Zs (D.Φ (τ, y))) ^ 2).im :=
      swlL_im_eq D Zs him hτneg.le hconf
    have htrans' : ((Zs y) ^ 2).im = ((Zs (D.Φ (τ, y))) ^ 2).im := by
      rwa [D.hΦ0 y] at htrans
    have hyC : y ∈ D.C D.j := by
      have h := hconf 0 ⟨hτneg.le, le_rfl⟩
      rwa [D.hΦ0 y] at h
    have hysrc : y ∈ (D.φ D.j).source := D.hCsub D.j hyC
    have hyge : c₀ ≤ |((Z y) ^ 2).im| := by
      by_contra hlt
      exact hy ⟨hysrc, not_le.mp hlt⟩
    have hZim : ((Z y) ^ 2).im = ((Z (D.Φ (τ, y))) ^ 2).im := by
      have h1 : lam0 ^ 2 * ((Z y) ^ 2).im = lam0 ^ 2 * ((Z (D.Φ (τ, y))) ^ 2).im := by
        rw [← swl_im_sq_eq_div (hZrel y), ← swl_im_sq_eq_div (hZrel (D.Φ (τ, y))), htrans']
      exact mul_left_cancel₀ (ne_of_gt (pow_pos hlam0pos 2)) h1
    rw [hfootτ, ← hZim]
    exact hyge

end Work.Drive.N2

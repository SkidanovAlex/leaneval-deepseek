import Mathlib
import Submission.Work.WilE4.CAD.seq_geom
import Submission.Work.WilE4.CAD.seq_bounded
import Submission.Work.WilE4.CAD.seq_mult
import Submission.Work.WilE4.CAD.disk_roots_card_eventually_const
import Submission.Work.WilE4.CAD.common_root_unique
import Submission.Work.WilE4.CAD.gcd_spec_natDegree_const_on_C
import Submission.Work.WilE4.CAD.gcd_spec_psc

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open Classical Filter
open scoped Topology

namespace Work.WilE4.CAD

open MvPolynomial Polynomial
open Work.WilE4 (spec)

variable {m k : ℕ}

/-- **The geometric data needed by `seq_closed_bounded`**, produced from the Sylvester/gcd data.

There is a single cluster point `hz n → t₀` such that every member of the family that does not
vanish identically on `C` and does vanish at `(x₀,t₀)` has `hz n` as its only root (with the
multiplicity of the limit root) in the disk of radius `ρ` about `t₀`. -/
theorem cluster_data {m k : ℕ} (P : Fin k → MvPolynomial (Fin (m + 1)) ℝ) (D : ℕ)
    (hD : ∀ i : Fin k, (P i).degreeOf (Fin.last m) ≤ D)
    (hclosed : ∀ i : Fin k, ∃ j : Fin k, P j = MvPolynomial.pderiv (Fin.last m) (P i))
    (C : Set (Fin m → ℝ))
    (hcoeff : ∀ i : Fin k, ∀ j : ℕ, j ≤ D → ∀ x ∈ C, ∀ x' ∈ C,
      SignType.sign ((spec (P i) x).coeff j) = SignType.sign ((spec (P i) x').coeff j))
    (hmin : PscSignConst P C)
    (v' : Fin k → SignType) (x : ℕ → Fin m → ℝ) (hxC : ∀ n, x n ∈ C) {x₀ : Fin m → ℝ}
    (hx₀ : x₀ ∈ C) (hlim : Filter.Tendsto x Filter.atTop (nhds x₀))
    (t : ℕ → ℝ) (ht : ∀ n, ∀ i : Fin k,
      SignType.sign ((spec (P i) (x n)).eval (t n)) = v' i)
    {t₀ : ℝ} (htlim : Filter.Tendsto t Filter.atTop (nhds t₀)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ hz : ℕ → ℝ,
      Filter.Tendsto hz Filter.atTop (nhds t₀) ∧
      (∀ᶠ n in Filter.atTop, |hz n - t₀| < ρ) ∧
      (∀ᶠ n in Filter.atTop, ∀ i : Fin k, (spec (P i) x₀) ≠ 0 →
        (spec (P i) x₀).eval t₀ = 0 → (spec (P i) (x n)).eval (hz n) = 0) ∧
      (∀ᶠ n in Filter.atTop, ∀ i : Fin k, (spec (P i) x₀) ≠ 0 →
        (spec (P i) x₀).eval t₀ = 0 →
        ∀ w : ℝ, (spec (P i) (x n)).eval w = 0 → |w - t₀| < ρ → w = hz n) ∧
      (∀ᶠ n in Filter.atTop, ∀ i : Fin k, (spec (P i) x₀) ≠ 0 →
        (spec (P i) x₀).eval t₀ = 0 →
        (spec (P i) (x n)).rootMultiplicity (hz n) = (spec (P i) x₀).rootMultiplicity t₀) ∧
      (∃ ε : ℝ, 0 < ε ∧ ε < ρ ∧ ∀ i : Fin k, (spec (P i) x₀) ≠ 0 →
        ∀ w : ℝ, (spec (P i) x₀).eval w = 0 → |w - t₀| ≤ ε → w = t₀) := by
  classical
  by_cases hGood : ∃ i : Fin k, (spec (P i) x₀) ≠ 0 ∧ (spec (P i) x₀).eval t₀ = 0
  · obtain ⟨i₁, hi₁ne, hi₁root⟩ := hGood
    -- the `ℂ`-valued family, obtained by embedding the real specialisations
    set F : Fin k → (Fin m → ℝ) → Polynomial ℂ :=
      fun i y => (spec (P i) y).map (algebraMap ℝ ℂ) with hFdef
    have hFcont : ∀ i : Fin k, ∀ j : ℕ, Continuous fun y : Fin m → ℝ => (F i y).coeff j := by
      intro i j
      have h1 : Continuous fun y : Fin m → ℝ => (((spec (P i) y).coeff j : ℝ) : ℂ) :=
        Complex.continuous_ofReal.comp (continuous_spec_coeff (P i) j)
      refine h1.congr fun y => ?_
      simp only [hFdef, Polynomial.coeff_map]
      simp
    have hFdeg : ∀ (i : Fin k) (y : Fin m → ℝ), (F i y).natDegree ≤ D := by
      intro i y
      rw [hFdef, Polynomial.natDegree_map]
      exact spec_natDegree_le_of_degreeOf (P i) D (hD i) y
    have hFne : ∀ (i : Fin k) (y : Fin m → ℝ), spec (P i) y ≠ 0 → F i y ≠ 0 := by
      intro i y hi
      rw [hFdef]
      exact map_ofReal_ne_zero hi
    have hspecne_n : ∀ (i : Fin k), spec (P i) x₀ ≠ 0 → ∀ n, spec (P i) (x n) ≠ 0 :=
      fun i hi n h => hi ((spec_eq_zero_iff_on_C hD hcoeff (hxC n) hx₀).mp h)
    -- a uniform isolating radius for the limit fibre
    obtain ⟨δ, hδpos, hδfar⟩ := exists_pos_lt_dist_roots_family
      (ι := {i : Fin k // spec (P i) x₀ ≠ 0})
      (f := fun i : {i : Fin k // spec (P i) x₀ ≠ 0} => spec (P i.val) x₀) t₀
      (fun i => i.2)
    have hfar : ∀ (i : Fin k), spec (P i) x₀ ≠ 0 → ∀ z : ℂ,
        ((spec (P i) x₀).map (algebraMap ℝ ℂ)).IsRoot z → z ≠ (t₀ : ℂ) →
        δ < dist z (t₀ : ℂ) :=
      fun i hi z hz hzt => hδfar ⟨i, hi⟩ z hz hzt
    -- the common cluster point of the reference member and any member vanishing at `(x₀,t₀)`
    have hcu : ∀ i : Fin k, spec (P i) x₀ ≠ 0 → (spec (P i) x₀).eval t₀ = 0 →
        ∀ᶠ n in Filter.atTop, ∃ z : ℂ, dist z (t₀ : ℂ) < δ ∧
          (F i₁ (x n)).IsRoot z ∧ (F i (x n)).IsRoot z ∧
          (∀ w : ℂ, (F i₁ (x n)).IsRoot w → dist w (t₀ : ℂ) < δ → w = z) ∧
          (∀ w : ℂ, (F i (x n)).IsRoot w → dist w (t₀ : ℂ) < δ → w = z) := by
      intro i hine hi0
      refine common_root_unique (F i₁) (F i) D (hFcont i₁) (hFcont i)
        (hFdeg i₁) (hFdeg i) x hlim (hFne i₁ x₀ hi₁ne) (hFne i x₀ hine) ?_ ?_ ?_
        hδpos (isRoot_map_ofReal hi₁root) (isRoot_map_ofReal hi0) ?_ ?_
      · intro n
        exact rootsCard_spec_const_on_C P D hD hclosed C hcoeff hmin i₁ (hxC n) hx₀
      · intro n
        exact rootsCard_spec_const_on_C P D hD hclosed C hcoeff hmin i (hxC n) hx₀
      · intro n
        rw [gcd_map_ofReal_natDegree, gcd_map_ofReal_natDegree]
        exact gcd_spec_natDegree_const_on_C_psc P D hD C hcoeff hmin i₁ i (x n) x₀ (hxC n) hx₀
      · exact fun z hz hzt => hfar i₁ hi₁ne z hz hzt
      · exact fun z hz hzt => hfar i hine z hz hzt
    -- the reference cluster function
    have hz₀ : ∀ᶠ n in Filter.atTop, ∃ z : ℂ, dist z (t₀ : ℂ) < δ ∧
        (F i₁ (x n)).IsRoot z ∧
        (∀ w : ℂ, (F i₁ (x n)).IsRoot w → dist w (t₀ : ℂ) < δ → w = z) :=
      (hcu i₁ hi₁ne hi₁root).mono fun n hn =>
        ⟨Classical.choose hn, (Classical.choose_spec hn).1, (Classical.choose_spec hn).2.1,
          (Classical.choose_spec hn).2.2.2.1⟩
    let zf : ℕ → ℂ := fun n => if h : ∃ z : ℂ, dist z (t₀ : ℂ) < δ ∧
        (F i₁ (x n)).IsRoot z ∧
        (∀ w : ℂ, (F i₁ (x n)).IsRoot w → dist w (t₀ : ℂ) < δ → w = z)
      then Classical.choose h else (t₀ : ℂ)
    have hzf : ∀ᶠ n in Filter.atTop, dist (zf n) (t₀ : ℂ) < δ ∧
        (F i₁ (x n)).IsRoot (zf n) ∧
        (∀ w : ℂ, (F i₁ (x n)).IsRoot w → dist w (t₀ : ℂ) < δ → w = zf n) := by
      filter_upwards [hz₀] with n hn
      have h1 : zf n = Classical.choose hn := by simp only [zf, dif_pos hn]
      rw [h1]
      exact Classical.choose_spec hn
    -- the cluster point is real
    have hzf_real : ∀ᶠ n in Filter.atTop, starRingEnd ℂ (zf n) = zf n := by
      filter_upwards [hzf] with n hn
      obtain ⟨hd, hr, hu⟩ := hn
      have hroot' : (F i₁ (x n)).IsRoot (starRingEnd ℂ (zf n)) :=
        isRoot_conj_of_isRoot hr
      have hdisk' : dist (starRingEnd ℂ (zf n)) (t₀ : ℂ) < δ := by
        have h1 : dist (starRingEnd ℂ (zf n)) (starRingEnd ℂ (t₀ : ℂ)) = dist (zf n) (t₀ : ℂ) :=
          dist_conj _ _
        rw [show starRingEnd ℂ (t₀ : ℂ) = (t₀ : ℂ) from Complex.conj_ofReal t₀] at h1
        rw [h1]
        exact hd
      exact hu _ hroot' hdisk'
    -- per-member data
    have hQi : ∀ i : Fin k, spec (P i) x₀ ≠ 0 → (spec (P i) x₀).eval t₀ = 0 →
        ∀ᶠ n in Filter.atTop, (F i (x n)).IsRoot (zf n) ∧
          (∀ w : ℂ, (F i (x n)).IsRoot w → dist w (t₀ : ℂ) < δ → w = zf n) ∧
          (F i (x n)).rootMultiplicity (zf n) = (spec (P i) x₀).rootMultiplicity t₀ := by
      intro i hine hi0
      have hrootuniq : ∀ᶠ n in Filter.atTop, (F i (x n)).IsRoot (zf n) ∧
          (∀ w : ℂ, (F i (x n)).IsRoot w → dist w (t₀ : ℂ) < δ → w = zf n) := by
        filter_upwards [hcu i hine hi0, hzf] with n hn hzn
        obtain ⟨z, hzd, hz1, hz2, hu1, hu2⟩ := hn
        obtain ⟨-, -, hfu⟩ := hzn
        have hz_eq : z = zf n := hfu z hz1 hzd
        subst hz_eq
        exact ⟨hz2, hu2⟩
      have hmult : ∀ᶠ n in Filter.atTop,
          (F i (x n)).rootMultiplicity (zf n) = (spec (P i) x₀).rootMultiplicity t₀ := by
        have hno : ∀ z : ℂ, dist z (t₀ : ℂ) = δ → (F i x₀).eval z ≠ 0 := by
          intro z hz h0
          have hzroot : (F i x₀).IsRoot z := h0
          have hzne : z ≠ (t₀ : ℂ) := by
            intro h; rw [h, dist_self] at hz; linarith
          have := hfar i hine z hzroot hzne
          linarith
        have hcount : ∀ᶠ n in Filter.atTop,
            ((F i (x n)).roots.filter (fun z : ℂ => dist z (t₀ : ℂ) < δ)).card
              = ((F i x₀).roots.filter (fun z : ℂ => dist z (t₀ : ℂ) < δ)).card :=
          hlim.eventually (disk_roots_card_eventually_const (F i) D (hFcont i) x₀
            (Filter.Eventually.of_forall (hFdeg i)) hδpos hno)
        have hiso : ∀ w : ℂ, (F i x₀).IsRoot w → dist w (t₀ : ℂ) < δ → w = (t₀ : ℂ) := by
          intro w hw hwd
          by_contra hne
          have := hfar i hine w hw hne
          linarith
        have hcount₀ : ((F i x₀).roots.filter (fun z : ℂ => dist z (t₀ : ℂ) < δ)).card
            = (F i x₀).rootMultiplicity (t₀ : ℂ) :=
          (rootMultiplicity_eq_of_filter_card (p := F i x₀) (z := (t₀ : ℂ)) (t₀ := (t₀ : ℂ))
            (isRoot_map_ofReal hi0) (by rw [dist_self]; exact hδpos) hiso rfl).symm
        filter_upwards [hcount, hrootuniq, hzf] with n hc hr hzn
        have hzd : dist (zf n) (t₀ : ℂ) < δ := hzn.1
        have h2 := rootMultiplicity_eq_of_filter_card (p := F i (x n)) (z := zf n)
          (t₀ := (t₀ : ℂ)) (ρ := δ)
          (μ := ((F i (x n)).roots.filter (fun z : ℂ => dist z (t₀ : ℂ) < δ)).card)
          hr.1 hzd hr.2 rfl
        rw [h2, hc, hcount₀, rootMultiplicity_map_ofReal]
      filter_upwards [hrootuniq, hmult] with n h1 h2
      exact ⟨h1.1, h1.2, h2⟩
    have hQall : ∀ᶠ n in Filter.atTop, ∀ i ∈ Finset.univ.filter
        (fun i : Fin k => (spec (P i) x₀) ≠ 0 ∧ (spec (P i) x₀).eval t₀ = 0),
        (F i (x n)).IsRoot (zf n) ∧
        (∀ w : ℂ, (F i (x n)).IsRoot w → dist w (t₀ : ℂ) < δ → w = zf n) ∧
        (F i (x n)).rootMultiplicity (zf n) = (spec (P i) x₀).rootMultiplicity t₀ := by
      have hall : ∀ᶠ n in Filter.atTop,
          ∀ i : ↥(Finset.univ.filter (fun i : Fin k =>
            (spec (P i) x₀) ≠ 0 ∧ (spec (P i) x₀).eval t₀ = 0)),
          (F i.1 (x n)).IsRoot (zf n) ∧
          (∀ w : ℂ, (F i.1 (x n)).IsRoot w → dist w (t₀ : ℂ) < δ → w = zf n) ∧
          (F i.1 (x n)).rootMultiplicity (zf n) = (spec (P i.1) x₀).rootMultiplicity t₀ :=
        (Filter.eventually_all).mpr fun i =>
          hQi i.1 (Finset.mem_filter.mp i.2).2.1 (Finset.mem_filter.mp i.2).2.2
      exact hall.mono fun n hn i hi => hn ⟨i, hi⟩
    -- the cluster point converges to `t₀`
    have hzlim : Filter.Tendsto (fun n => (zf n).re) Filter.atTop (nhds t₀) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      set ρ' : ℝ := min ε (δ / 2) with hρ'def
      have hρ'pos : 0 < ρ' := lt_min hε (by linarith)
      have hρ'le : ρ' ≤ ε := min_le_left _ _
      have hρ'δ : ρ' < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have hno : ∀ z : ℂ, dist z (t₀ : ℂ) = ρ' → (F i₁ x₀).eval z ≠ 0 := by
        intro z hz h0
        have hzroot : (F i₁ x₀).IsRoot z := h0
        have hzne : z ≠ (t₀ : ℂ) := by
          intro h; rw [h, dist_self] at hz; linarith
        have := hfar i₁ hi₁ne z hzroot hzne
        linarith
      have hcount := hlim.eventually (disk_roots_card_eventually_const (F i₁) D (hFcont i₁) x₀
        (Filter.Eventually.of_forall (hFdeg i₁)) hρ'pos hno)
      have hcount₀ : 0 < ((F i₁ x₀).roots.filter (fun z : ℂ => dist z (t₀ : ℂ) < ρ')).card := by
        apply Multiset.card_pos_iff_exists_mem.mpr
        exact ⟨(t₀ : ℂ), Multiset.mem_filter.mpr
          ⟨(Polynomial.mem_roots (hFne i₁ x₀ hi₁ne)).mpr (isRoot_map_ofReal hi₁root),
            by rw [dist_self]; exact hρ'pos⟩⟩
      have hmain : ∀ᶠ n in Filter.atTop, dist (zf n) (t₀ : ℂ) < ε := by
        filter_upwards [hcount, hzf] with n hc hzn
        have hpos : 0 < ((F i₁ (x n)).roots.filter
            (fun z : ℂ => dist z (t₀ : ℂ) < ρ')).card := by
          rw [hc]; exact hcount₀
        obtain ⟨w, hw⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
        obtain ⟨hwr, hwd⟩ := Multiset.mem_filter.mp hw
        have hwroot : (F i₁ (x n)).IsRoot w :=
          (Polynomial.mem_roots (hFne i₁ (x n) (hspecne_n i₁ hi₁ne n))).mp hwr
        have hwzf : w = zf n := hzn.2.2 w hwroot (lt_trans hwd hρ'δ)
        rw [← hwzf]
        exact lt_of_lt_of_le hwd hρ'le
      have hfin : ∀ᶠ n in Filter.atTop, dist ((zf n).re) t₀ < ε := by
        filter_upwards [hmain, hzf_real] with n hn hr
        rw [show zf n = (((zf n).re : ℝ) : ℂ) from (ofReal_re_of_conj_eq (zf n) hr).symm,
          dist_ofReal_eq] at hn
        exact hn
      exact Filter.eventually_atTop.mp hfin
    refine ⟨δ, hδpos, fun n => (zf n).re, hzlim, ?_, ?_, ?_, ?_, ?_⟩
    · filter_upwards [hzf, hzf_real] with n hn hr
      have hd := hn.1
      rw [show zf n = (((zf n).re : ℝ) : ℂ) from (ofReal_re_of_conj_eq (zf n) hr).symm,
        dist_ofReal_eq] at hd
      exact hd
    · filter_upwards [hQall, hzf_real] with n hQ hr
      intro i hine hi0
      obtain ⟨hroot, -, -⟩ := hQ i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hine, hi0⟩)
      rw [show zf n = (((zf n).re : ℝ) : ℂ) from (ofReal_re_of_conj_eq (zf n) hr).symm]
        at hroot
      exact isRoot_of_map_ofReal hroot
    · filter_upwards [hQall, hzf_real] with n hQ hr
      intro i hine hi0 w hw hwδ
      obtain ⟨-, huniq, -⟩ := hQ i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hine, hi0⟩)
      have hwroot : ((spec (P i) (x n)).map (algebraMap ℝ ℂ)).IsRoot (w : ℂ) :=
        isRoot_map_ofReal hw
      have h1 : (w : ℂ) = zf n := huniq (w : ℂ) hwroot (by rw [dist_ofReal_eq]; exact hwδ)
      have h2 : (w : ℂ) = (((zf n).re : ℝ) : ℂ) := by
        rw [h1, ofReal_re_of_conj_eq (zf n) hr]
      exact Complex.ofReal_inj.mp h2
    · filter_upwards [hQall, hzf_real] with n hQ hr
      intro i hine hi0
      obtain ⟨-, -, hmult⟩ := hQ i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hine, hi0⟩)
      rw [← rootMultiplicity_map_ofReal (spec (P i) (x n)) ((zf n).re),
        show (((zf n).re : ℝ) : ℂ) = zf n from ofReal_re_of_conj_eq (zf n) hr]
      exact hmult
    · refine ⟨δ / 2, by linarith, by linarith, fun i hine w hw hwd => ?_⟩
      by_contra hne
      have hroot : ((spec (P i) x₀).map (algebraMap ℝ ℂ)).IsRoot (w : ℂ) := isRoot_map_ofReal hw
      have hwne : (w : ℂ) ≠ (t₀ : ℂ) := fun h => hne (Complex.ofReal_inj.mp h)
      have hfar_i := hfar i hine (w : ℂ) hroot hwne
      rw [dist_ofReal_eq] at hfar_i
      linarith
  · -- no member of the family that does not vanish on `C` vanishes at `t₀`
    have hEv_i : ∀ i : Fin k, ∀ᶠ ε in nhds (0 : ℝ),
        (spec (P i) x₀ ≠ 0 → ∀ w : ℝ, |w - t₀| < ε → (spec (P i) x₀).eval w ≠ 0) := by
      intro i
      by_cases hi : spec (P i) x₀ = 0
      · exact Filter.Eventually.of_forall fun ε hne w hw => absurd hi hne
      · have hne : (spec (P i) x₀).eval t₀ ≠ 0 := fun h0 => hGood ⟨i, hi, h0⟩
        have hc : ContinuousAt (fun w : ℝ => (spec (P i) x₀).eval w) t₀ :=
          (Polynomial.continuous (spec (P i) x₀)).continuousAt
        have hnb : {y : ℝ | y ≠ 0} ∈ nhds ((spec (P i) x₀).eval t₀) :=
          isOpen_ne.mem_nhds hne
        obtain ⟨g₁, hg₁pos, hg₁sub⟩ := Metric.mem_nhds_iff.mp (hc.eventually hnb)
        show ({ε : ℝ | spec (P i) x₀ ≠ 0 → ∀ w : ℝ, |w - t₀| < ε →
          (spec (P i) x₀).eval w ≠ 0} : Set ℝ) ∈ nhds (0 : ℝ)
        refine Metric.mem_nhds_iff.mpr ⟨g₁, hg₁pos, fun ε hε _ w hw => ?_⟩
        have hε' : |ε| < g₁ := by
          rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hε
          exact hε
        exact hg₁sub (by
          rw [Metric.mem_ball, Real.dist_eq]
          exact lt_of_lt_of_le (lt_of_lt_of_le hw (le_abs_self ε)) (le_of_lt hε'))
    have hEv : ∀ᶠ ε in nhds (0 : ℝ),
        (∀ i : Fin k, spec (P i) x₀ ≠ 0 → ∀ w : ℝ,
          |w - t₀| < ε → (spec (P i) x₀).eval w ≠ 0) :=
      (Filter.eventually_all).mpr hEv_i
    obtain ⟨g, hgpos, hgsub⟩ := Metric.mem_nhds_iff.mp hEv
    have hball : 3 * g / 4 ∈ Metric.ball (0 : ℝ) g := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero,
        abs_of_pos (by linarith : (0 : ℝ) < 3 * g / 4)]
      linarith
    have hprop : ∀ i : Fin k, spec (P i) x₀ ≠ 0 → ∀ w : ℝ, (spec (P i) x₀).eval w = 0 →
        |w - t₀| ≤ g / 2 → w = t₀ := by
      intro i hi w hw hwd
      exact absurd hw (hgsub hball i hi w (by linarith))
    refine ⟨1 / 2, by norm_num, fun _ => t₀, tendsto_const_nhds, ?_, ?_, ?_, ?_, ?_⟩
    · exact Filter.Eventually.of_forall fun n => by rw [sub_self, abs_zero]; norm_num
    · exact Filter.Eventually.of_forall fun n i hi h0 => absurd ⟨i, hi, h0⟩ hGood
    · exact Filter.Eventually.of_forall fun n i hi h0 w _ _ => absurd ⟨i, hi, h0⟩ hGood
    · exact Filter.Eventually.of_forall fun n i hi h0 => absurd ⟨i, hi, h0⟩ hGood
    · refine ⟨min (g / 2) (1 / 4), lt_min (by linarith) (by norm_num),
        lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
      intro i hi w hw hwd
      exact hprop i hi w hw (le_trans hwd (min_le_left _ _))

end Work.WilE4.CAD

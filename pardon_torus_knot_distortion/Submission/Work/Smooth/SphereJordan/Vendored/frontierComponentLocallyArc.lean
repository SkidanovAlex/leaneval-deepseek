import Mathlib
import Submission.Work.Smooth.SphereJordan.localComplementBasic
import Submission.Work.Smooth.SphereJordan.localComplementPreconnected
import Submission.Work.Smooth.SphereJordan.Vendored.localArcHgen
import Submission.Work.Smooth.SphereJordan.Vendored.localArcTangency
import Submission.Work.Smooth.SphereJordan.Vendored.tangencyPair
import Submission.Work.Smooth.SphereJordan.tangencyCuspSeparation

/-!
# The frontier of a complementary component of a finite union of equal discs is locally an arc

`frontierComponentLocallyArc`: for `S = ⋃ w ∈ Q, closedBall w r` a finite union of equal closed
discs whose *open* balls are preconnected
(`hB : IsPreconnected (⋃ w ∈ Q, Metric.ball w r)`), the frontier of any connected component of the
complement `Sᶜ` is, at each of its points `x`, an arc through `x`.

The proof splits on whether there is a *free* unit direction at `x` (a direction strictly behind
every active centre).  If there is, the local complement is a single sector
(`localComplementPreconnected`) and `frontierLocallyArc_of_freeDirection` gives the arc.  If there
is not, `tangencyPair_of_not_generic` produces two antipodal active centres `a`, `b` and a
direction `u₀ = I * (a - x) / r`; the local behaviour is then described by the cusp machinery of
`localArcTangency` (the profile is `r * |z.im|`) and, when the active set is exactly `{a, b}`, the
two cusps are separated by `tangency_cusps_separated` (the loop through `x` built from the
preconnectedness of the open balls).
-/

namespace Work.Smooth.SphereJordan

open Set Metric

noncomputable section

open scoped Classical

theorem frontierComponentLocallyArc (Q : Finset ℂ) {r : ℝ} (hr : 0 < r)
    (hB : IsPreconnected (⋃ w ∈ Q, Metric.ball w r)) (q : ℂ) :
    ∀ x ∈ frontier (connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q),
      ∃ ε > 0, ∃ γ : ℝ → ℂ, Continuous γ ∧ Function.Injective γ ∧ γ 0 = x ∧
        γ '' Set.Ioo (-1) 1 =
          frontier (connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q) ∩ Metric.ball x ε := by
  intro x hxq
  classical
  have hSclosed : IsClosed (⋃ w ∈ Q, Metric.closedBall w r) := isClosed_ballUAux Q r
  have hx : x ∈ frontier (⋃ w ∈ Q, Metric.closedBall w r) := frontier_componentIn_subset hSclosed hxq
  have hxS : x ∈ ⋃ w ∈ Q, Metric.closedBall w r := hSclosed.closure_eq ▸ hx.1
  by_cases hgen : ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ w ∈ Q, dist x w = r → (star u * (w - x)).re < 0
  · obtain ⟨εp, hεp, hpre⟩ := localComplementPreconnected hr hx hgen
    have hU : ∃ ε' > 0, ∀ y ∈ (⋃ w ∈ Q, Metric.closedBall w r)ᶜ,
        y ∈ Metric.ball x ε' → y ∈ connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q := by
      refine ⟨εp, hεp, fun y hyS hyb => ?_⟩
      obtain ⟨y', hy'c, hy'd⟩ := Metric.mem_closure_iff.mp hxq.1 εp hεp
      have hy's : y' ∈ (⋃ w ∈ Q, Metric.closedBall w r)ᶜ ∩ Metric.ball x εp :=
        ⟨connectedComponentIn_subset _ q hy'c, by rw [Metric.mem_ball]; rwa [dist_comm]⟩
      have h1 : y ∈ connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) y' :=
        (hpre.subset_connectedComponentIn hy's inter_subset_left) ⟨hyS, hyb⟩
      have h2 : connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) y' =
          connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q :=
        (connectedComponentIn_eq hy'c).symm
      rwa [h2] at h1
    obtain ⟨ε, γ, hε, hcont, hinj, hγ0, hγ⟩ := frontierLocallyArc_of_freeDirection hr hxq hgen hU
    exact ⟨ε, hε, γ, hcont, hinj, hγ0, hγ⟩
  · obtain ⟨a, b, u₀, haQ, hbQ, har, hbr, hab, hu₀, hdir, hu₀a, hotherQ⟩ :=
      tangencyPair_of_not_generic hr hx hgen
    have hact : a ∈ actC Q r x := mem_actC.mpr ⟨haQ, har⟩
    have hbact : b ∈ actC Q r x := mem_actC.mpr ⟨hbQ, hbr⟩
    have hother : ∀ w ∈ actC Q r x, w ≠ a → w ≠ b → (star u₀ * (w - x)).re < 0 :=
      fun w hw hwa hwb => hotherQ w (mem_actC.mp hw).1 (mem_actC.mp hw).2 hwa hwb
    obtain ⟨ε₁, hε₁, hmodel₁⟩ := exists_model_mC hr hx
    have hε0 : 0 < min ε₁ (2 * r) := lt_min hε₁ (by linarith)
    have hmod : ∀ (u' : ℂ) (ρ : ℝ), ‖u'‖ = 1 → 0 < ρ → ρ < min ε₁ (2 * r) →
        (x + ρ * u' ∈ ⋃ w ∈ Q, Metric.closedBall w r ↔
          ρ ≤ 2 * mC Q r x (actC_nonempty hr hx) u') :=
      fun u' ρ hu' hρ hρlt => hmodel₁ u' ρ hu' hρ (lt_of_lt_of_le hρlt (min_le_left _ _))
    by_cases hmore : ∃ w ∈ actC Q r x, w ≠ a ∧ w ≠ b
    · obtain ⟨w₀, hw₀, hw₀a, hw₀b⟩ := hmore
      have hw₀neg : (star u₀ * (w₀ - x)).re < 0 := hother w₀ hw₀ hw₀a hw₀b
      obtain ⟨ε₂, hε₂, hε₂le, hexcl⟩ := cusp_excludes hr hact hbact hab hu₀ hu₀a hxS
        hw₀ hw₀neg hε0 (min_le_right ε₁ (2 * r)) hmod
      have hε₂2r : ε₂ ≤ 2 * r := le_trans hε₂le (min_le_right _ _)
      have hmod₂ : ∀ (u' : ℂ) (ρ : ℝ), ‖u'‖ = 1 → 0 < ρ → ρ < ε₂ →
          (x + ρ * u' ∈ ⋃ w ∈ Q, Metric.closedBall w r ↔
            ρ ≤ 2 * mC Q r x (actC_nonempty hr hx) u') :=
        fun u' ρ hu' hρ hρlt => hmod u' ρ hu' hρ (lt_of_lt_of_le hρlt hε₂le)
      have hmeet : ∃ y ∈ (⋃ w ∈ Q, Metric.closedBall w r)ᶜ, dist y x < ε₂ ∧
          0 < (star u₀ * (y - x)).re ∧
          y ∈ connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q := by
        obtain ⟨y', hy'c, hy'd⟩ := Metric.mem_closure_iff.mp hxq.1 (ε₂ / 2) (by linarith)
        have hy'S : y' ∈ (⋃ w ∈ Q, Metric.closedBall w r)ᶜ := connectedComponentIn_subset _ q hy'c
        have hy'd2 : dist y' x < ε₂ := by rw [dist_comm]; linarith
        exact ⟨y', hy'S, hy'd2, hexcl y' hy'S hy'd2, hy'c⟩
      have hdisj : ∀ y ∈ (⋃ w ∈ Q, Metric.closedBall w r)ᶜ, dist y x < ε₂ →
          (star u₀ * (y - x)).re < 0 →
          y ∉ connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q :=
        fun y hyS hyd hneg => absurd (hexcl y hyS hyd) (not_lt.mpr hneg.le)
      obtain ⟨γ, hcont, hinj, hγ0, hγ⟩ := frontierLocallyArc_of_cusp hr hε₂ hε₂2r hxq hact hbact
        hab hu₀ hu₀a hother hmod₂ hmeet hdisj
      exact ⟨ε₂, hε₂, γ, hcont, hinj, hγ0, hγ⟩
    · have hnoother : ∀ w ∈ actC Q r x, w = a ∨ w = b := by
        intro w hw
        by_contra hcon
        push_neg at hcon
        exact hmore ⟨w, hw, hcon⟩
      set ε : ℝ := min ε₁ (2 * r) / 2 with hεdef
      have hεpos : 0 < ε := by rw [hεdef]; exact div_pos hε0 (by norm_num)
      have hε2r : ε ≤ 2 * r := by rw [hεdef]; linarith [min_le_right ε₁ (2 * r)]
      have hεε₀ : ε ≤ min ε₁ (2 * r) := by rw [hεdef]; linarith [hε0.le]
      have hmodε : ∀ (u' : ℂ) (ρ : ℝ), ‖u'‖ = 1 → 0 < ρ → ρ < ε →
          (x + ρ * u' ∈ ⋃ w ∈ Q, Metric.closedBall w r ↔
            ρ ≤ 2 * mC Q r x (actC_nonempty hr hx) u') :=
        fun u' ρ hu' hρ hρlt => hmod u' ρ hu' hρ (lt_of_lt_of_le hρlt hεε₀)
      have hua' : (star (-u₀) * (a - x)).re = 0 := by
        rw [star_neg, neg_mul, Complex.neg_re, hu₀a, neg_zero]
      have hother' : ∀ w ∈ actC Q r x, w ≠ a → w ≠ b → (star (-u₀) * (w - x)).re < 0 := by
        intro w hw hwa hwb
        rcases hnoother w hw with h | h
        · exact absurd h hwa
        · exact absurd h hwb
      have hCpre : IsPreconnected (cuspSet Q r x u₀ ε) :=
        cuspSet_preconnected hr hε2r hact hbact hab hu₀ hu₀a hother hmodε
      have hC'pre : IsPreconnected (cuspSet Q r x (-u₀) ε) :=
        cuspSet_preconnected hr hε2r hact hbact hab (by rw [norm_neg, hu₀]) hua' hother' hmodε
      have hMu₀ : mC Q r x (actC_nonempty hr hx) u₀ = 0 := by
        have h1 := mC_eq_abs_im (hA := actC_nonempty hr hx) hact hbact hab hu₀ hu₀a hother
          (by norm_num : ‖(1 : ℂ)‖ = 1) (by norm_num : 0 ≤ (1 : ℂ).re)
        simpa using h1
      have hMu₀' : mC Q r x (actC_nonempty hr hx) (-u₀) = 0 := by
        have h1 := mC_eq_abs_im (hA := actC_nonempty hr hx) hact hbact hab
          (by rw [norm_neg, hu₀]) hua' hother' (by norm_num : ‖(1 : ℂ)‖ = 1)
          (by norm_num : 0 ≤ (1 : ℂ).re)
        simpa using h1
      have hray1 : ∀ t ∈ Set.Ioo (0 : ℝ) ε, x + (t : ℂ) * u₀ ∈ cuspSet Q r x u₀ ε := by
        intro t ht
        have hS : x + (t : ℂ) * u₀ ∉ ⋃ w ∈ Q, Metric.closedBall w r := by
          intro hmem
          have h2 : t ≤ 2 * mC Q r x (actC_nonempty hr hx) u₀ :=
            (hmodε u₀ t hu₀ ht.1 ht.2).mp hmem
          rw [hMu₀] at h2
          linarith [ht.1]
        refine ⟨hS, ?_, ?_⟩
        · rw [dist_eq_norm]
          have h1 : x + (t : ℂ) * u₀ - x = (t : ℂ) * u₀ := by ring
          rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1, hu₀, mul_one]
          exact ht.2
        · have h1 : star u₀ * (x + (t : ℂ) * u₀ - x) = (t : ℂ) * (star u₀ * u₀) := by ring
          have h2 : star u₀ * u₀ = 1 := star_mul_self hu₀
          rw [h1, h2]
          have h3 : (t : ℂ) * 1 = (t : ℂ) := by ring
          rw [h3, Complex.ofReal_re]
          exact ht.1
      have hray2 : ∀ t ∈ Set.Ioo (0 : ℝ) ε, x - (t : ℂ) * u₀ ∈ cuspSet Q r x (-u₀) ε := by
        intro t ht
        have hS : x - (t : ℂ) * u₀ ∉ ⋃ w ∈ Q, Metric.closedBall w r := by
          intro hmem
          have hpt : x - (t : ℂ) * u₀ = x + (t : ℂ) * (-u₀) := by ring
          rw [hpt] at hmem
          have h2 : t ≤ 2 * mC Q r x (actC_nonempty hr hx) (-u₀) :=
            (hmodε (-u₀) t (by rw [norm_neg, hu₀]) ht.1 ht.2).mp hmem
          rw [hMu₀'] at h2
          linarith [ht.1]
        refine ⟨hS, ?_, ?_⟩
        · rw [dist_eq_norm]
          have h1 : x - (t : ℂ) * u₀ - x = -((t : ℂ) * u₀) := by ring
          rw [h1, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1,
            hu₀, mul_one]
          exact ht.2
        · have h1 : star (-u₀) * (x - (t : ℂ) * u₀ - x)
              = -((t : ℂ) * (star (-u₀) * u₀)) := by ring
          have h2 : star (-u₀) * u₀ = -1 := by
            rw [star_neg, neg_mul, star_mul_self hu₀]
          rw [h1, h2]
          have h3 : -((t : ℂ) * (-1)) = (t : ℂ) := by ring
          rw [h3, Complex.ofReal_re]
          exact ht.1
      have hsep_aux : ∀ t ∈ Set.Ioo (0 : ℝ) ε, ¬ (x + (t : ℂ) * u₀ ∈
            connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q ∧
          x - (t : ℂ) * u₀ ∈ connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q) := by
        intro t ht
        have hseg : ∀ c : ℝ, c ≠ 0 → |c| ≤ t →
            x + (c : ℂ) * (Complex.I * ((a - x) / (r : ℂ))) ∉
              ⋃ w ∈ Q, Metric.closedBall w r := by
          intro c hc0 hcabs
          rw [← hdir]
          have hcpos : 0 < |c| := abs_pos.mpr hc0
          have hclt : |c| < ε := lt_of_le_of_lt hcabs ht.2
          rcases lt_or_gt_of_ne hc0 with h3 | h3
          · have h4 : x + (c : ℂ) * u₀ = x + ((|c| : ℝ) : ℂ) * (-u₀) := by
              rw [abs_of_neg h3]
              push_cast
              ring
            rw [h4]
            intro hmem
            have h5 := (hmodε (-u₀) |c| (by rw [norm_neg, hu₀]) hcpos hclt).mp hmem
            rw [hMu₀'] at h5
            linarith
          · have h4 : x + (c : ℂ) * u₀ = x + ((|c| : ℝ) : ℂ) * u₀ := by
              rw [abs_of_pos h3]
            rw [h4]
            intro hmem
            have h5 := (hmodε u₀ |c| hu₀ hcpos hclt).mp hmem
            rw [hMu₀] at h5
            linarith
        have h := tangency_cusps_separated (ρ := t) hr ht.1 hB haQ hbQ
          (by linear_combination hab : a + b = 2 * x) har (dist_ge_of_frontier hx) hseg q
        simpa [hdir] using h
      have hy₀dec : ∀ y ∈ (⋃ w ∈ Q, Metric.closedBall w r)ᶜ, dist y x < ε →
          y ∈ cuspSet Q r x u₀ ε ∨ y ∈ cuspSet Q r x (-u₀) ε := by
        intro y hyS hyd
        by_cases hyx : y = x
        · exact absurd (hyx ▸ hyS) (fun h => h hxS)
        · have hρ0 : 0 < dist y x := dist_pos.mpr hyx
          set ρ : ℝ := dist y x with hρdef
          have hρ0' : 0 < ρ := hρ0
          have hρlt : ρ < ε := hyd
          have hhy : ‖y - x‖ = ρ := by rw [hρdef, dist_eq_norm]
          set w : ℂ := (y - x) / (ρ : ℂ) with hwdef
          have hwnorm : ‖w‖ = 1 := by
            rw [hwdef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0', hhy]
            exact div_self (ne_of_gt hρ0')
          have hyw : y = x + ρ * w := by
            have hρne : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hρ0')
            rw [hwdef, mul_comm (ρ : ℂ), div_mul_cancel₀ (y - x) hρne]
            ring
          have hnotS : x + ρ * w ∉ ⋃ w ∈ Q, Metric.closedBall w r := by rw [← hyw]; exact hyS
          have hmC : 2 * mC Q r x (actC_nonempty hr hx) w < ρ := by
            by_contra hcon
            push_neg at hcon
            exact hnotS ((hmodε w ρ hwnorm hρ0' hρlt).mpr hcon)
          set z : ℂ := star u₀ * w with hzdef
          have hznorm : ‖z‖ = 1 := by rw [hzdef, norm_mul, norm_star, hu₀, one_mul, hwnorm]
          have hwuz : w = u₀ * z := by rw [hzdef, ← mul_assoc, mul_star_self hu₀, one_mul]
          have hle : r * |z.im| ≤ mC Q r x (actC_nonempty hr hx) w := by
            rw [hwuz]
            exact mC_ge_abs_im (hA := actC_nonempty hr hx) hact hbact hab hu₀ hu₀a hznorm
          have him1 : |z.im| < 1 := by
            have h2 : |z.im| < ρ / (2 * r) := by rw [lt_div_iff₀ (by linarith)]; linarith
            have h3 : ρ / (2 * r) < 1 := by rw [div_lt_one (by linarith)]; linarith
            linarith
          have hzre_ne : z.re ≠ 0 := by
            intro h0
            have h1 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
              rw [Complex.sq_norm, Complex.normSq_apply]; ring
            rw [hznorm, h0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add] at h1
            have h2 : (|z.im|) ^ 2 = (1 : ℝ) ^ 2 := by rw [sq_abs, one_pow]; linarith [h1]
            have h3 : |z.im| = 1 := by
              simpa using (sq_eq_sq_iff_abs_eq_abs (|z.im|) (1 : ℝ)).mp h2
            linarith [him1, h3]
          have hz : (star u₀ * (y - x)).re = ρ * z.re := by
            have h2 : star u₀ * (x + ρ * w - x) = (ρ : ℂ) * z := by rw [hzdef]; ring
            rw [hyw, h2, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
              mul_comm]
          rcases lt_or_gt_of_ne hzre_ne with h | h
          · right
            refine ⟨hyS, hyd, ?_⟩
            have h4 : (star (-u₀) * (y - x)).re = -((star u₀ * (y - x)).re) := by
              rw [star_neg, neg_mul, Complex.neg_re]
            rw [h4, hz]
            nlinarith [hρ0', h]
          · left
            exact ⟨hyS, hyd, by rw [hz]; exact mul_pos hρ0' h⟩
      obtain ⟨y₀, hy₀c, hy₀d⟩ := Metric.mem_closure_iff.mp hxq.1 (ε / 2) (by linarith)
      have hy₀S : y₀ ∈ (⋃ w ∈ Q, Metric.closedBall w r)ᶜ := connectedComponentIn_subset _ q hy₀c
      have hy₀d' : dist y₀ x < ε := by rw [dist_comm]; linarith
      have hdec : y₀ ∈ cuspSet Q r x u₀ ε ∨ y₀ ∈ cuspSet Q r x (-u₀) ε := hy₀dec y₀ hy₀S hy₀d'
      have htmid : (ε / 2) ∈ Set.Ioo (0 : ℝ) ε := ⟨by linarith, by linarith⟩
      have hCcompOf : ∀ y ∈ cuspSet Q r x u₀ ε,
          y ∈ connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q →
          cuspSet Q r x u₀ ε ⊆ connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q := by
        intro y hy hyc
        have h1 : cuspSet Q r x u₀ ε ⊆
            connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) y :=
          hCpre.subset_connectedComponentIn hy (fun z hz => hz.1)
        have h2 : connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) y =
            connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q :=
          (connectedComponentIn_eq hyc).symm
        rwa [h2] at h1
      have hC'compOf : ∀ y ∈ cuspSet Q r x (-u₀) ε,
          y ∈ connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q →
          cuspSet Q r x (-u₀) ε ⊆ connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q := by
        intro y hy hyc
        have h1 : cuspSet Q r x (-u₀) ε ⊆
            connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) y :=
          hC'pre.subset_connectedComponentIn hy (fun z hz => hz.1)
        have h2 : connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) y =
            connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q :=
          (connectedComponentIn_eq hyc).symm
        rwa [h2] at h1
      rcases hdec with hdec | hdec
      · have hC'not : ∀ y ∈ cuspSet Q r x (-u₀) ε,
            y ∉ connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q := by
          intro y hy hycomp
          have h1 : cuspSet Q r x (-u₀) ε ⊆
              connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) y :=
            hC'pre.subset_connectedComponentIn hy (fun z hz => hz.1)
          have h2 : connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) y =
              connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q :=
            (connectedComponentIn_eq hycomp).symm
          rw [h2] at h1
          exact (hsep_aux (ε / 2) htmid)
            ⟨hCcompOf y₀ hdec hy₀c (hray1 (ε / 2) htmid), h1 (hray2 (ε / 2) htmid)⟩
        have hmeet : ∃ y ∈ (⋃ w ∈ Q, Metric.closedBall w r)ᶜ, dist y x < ε ∧
            0 < (star u₀ * (y - x)).re ∧
            y ∈ connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q :=
          ⟨y₀, hy₀S, hy₀d', hdec.2.2, hy₀c⟩
        have hdisj : ∀ y ∈ (⋃ w ∈ Q, Metric.closedBall w r)ᶜ, dist y x < ε →
            (star u₀ * (y - x)).re < 0 →
            y ∉ connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q := by
          intro y hyS hyd hneg
          refine hC'not y ⟨hyS, hyd, ?_⟩
          rw [star_neg, neg_mul, Complex.neg_re]
          linarith
        obtain ⟨γ, hcont, hinj, hγ0, hγ⟩ := frontierLocallyArc_of_cusp hr hεpos hε2r hxq hact
          hbact hab hu₀ hu₀a hother hmodε hmeet hdisj
        exact ⟨ε, hεpos, γ, hcont, hinj, hγ0, hγ⟩
      · have hCnot : ∀ y ∈ cuspSet Q r x u₀ ε,
            y ∉ connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q := by
          intro y hy hycomp
          have h1 : cuspSet Q r x u₀ ε ⊆
              connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) y :=
            hCpre.subset_connectedComponentIn hy (fun z hz => hz.1)
          have h2 : connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) y =
              connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q :=
            (connectedComponentIn_eq hycomp).symm
          rw [h2] at h1
          have h5 : cuspSet Q r x (-u₀) ε ⊆
              connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) y₀ :=
            hC'pre.subset_connectedComponentIn hdec (fun z hz => hz.1)
          have h6 : connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) y₀ =
              connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q :=
            (connectedComponentIn_eq hy₀c).symm
          rw [h6] at h5
          exact (hsep_aux (ε / 2) htmid)
            ⟨h1 (hray1 (ε / 2) htmid), h5 (hray2 (ε / 2) htmid)⟩
        have hmeet : ∃ y ∈ (⋃ w ∈ Q, Metric.closedBall w r)ᶜ, dist y x < ε ∧
            0 < (star (-u₀) * (y - x)).re ∧
            y ∈ connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q :=
          ⟨y₀, hy₀S, hy₀d', hdec.2.2, hy₀c⟩
        have hdisj : ∀ y ∈ (⋃ w ∈ Q, Metric.closedBall w r)ᶜ, dist y x < ε →
            (star (-u₀) * (y - x)).re < 0 →
            y ∉ connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q := by
          intro y hyS hyd hneg
          refine hCnot y ⟨hyS, hyd, ?_⟩
          rw [star_neg, neg_mul, Complex.neg_re] at hneg
          linarith
        obtain ⟨γ, hcont, hinj, hγ0, hγ⟩ := frontierLocallyArc_of_cusp hr hεpos hε2r hxq hact
          hbact hab (by rw [norm_neg, hu₀]) hua' hother' hmodε hmeet hdisj
        exact ⟨ε, hεpos, γ, hcont, hinj, hγ0, hγ⟩

end

end Work.Smooth.SphereJordan

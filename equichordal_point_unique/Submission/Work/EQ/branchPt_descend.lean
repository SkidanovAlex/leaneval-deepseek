import Mathlib
import Submission.Work.EQ.bp_aux
import Submission.Work.EQ.backward_puiseux
import Submission.Work.EQ.branchPt_meromorphic
import Submission.Work.EQ.meromorphicAt_punctured_bounded
import Submission.Work.Topology.exists_factor_of_root_invariant

namespace Work.EQ

open Filter _root_.Topology
open Complex Metric

/-- **Meromorphy of a pair.**  A pair-valued function both of whose components are meromorphic at
`x` is meromorphic at `x`.  (Mathlib has `MeromorphicAt.prod` only for the multiplicative structure
of the codomain, so we read off the definition `∃ n, AnalyticAt (z ↦ (z-x)^n • f z) x` and take the
sum of the two exponents.) -/
lemma meromorphicAt_pair {f g : ℂ → ℂ} {x : ℂ} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (fun z => (f z, g z)) x := by
  obtain ⟨m, hm⟩ := hf
  obtain ⟨n, hn⟩ := hg
  refine ⟨m + n, ?_⟩
  have h1 : AnalyticAt ℂ (fun z => (z - x) ^ n • ((z - x) ^ m • f z)) x :=
    ((analyticAt_id.sub analyticAt_const).pow n).smul hm
  have h2 : AnalyticAt ℂ (fun z => (z - x) ^ m • ((z - x) ^ n • g z)) x :=
    ((analyticAt_id.sub analyticAt_const).pow m).smul hn
  refine (h1.prod h2).congr ?_
  filter_upwards with z
  ext <;> simp [smul_eq_mul, pow_add] <;> ring

/-- **Meromorphic descent of an invariant function.**

Let `f` be meromorphic at `0` and analytic on the punctured disc `0 < ‖t‖ < ρ`, and suppose that
`f (ω * t) = f t` on that punctured disc for a primitive `d`-th root of unity `ω`.  Then `f`
descends along `t ↦ t ^ d`: there is `g`, analytic on the punctured disc of radius `ρ ^ d` and
meromorphic at `0`, with `f t = g (t ^ d)`.

Proof: pick `M` with `A z = z ^ M * f z` analytic at `0` (definition of `MeromorphicAt`).  Then
`F t = t ^ (M * d) * f t = t ^ (M * (d-1)) * A t` is analytic on the punctured disc *and* at `0`;
`F` is invariant because `ω ^ (M * d) = (ω ^ d) ^ M = 1`.  Hence
`Work.Topology.exists_factor_of_root_invariant` gives `G` analytic on the punctured disc of radius
`ρ ^ d` with `F t = G (t ^ d)`.  `G` is bounded near `0` (as `F` is continuous at `0` and
`t ↦ t ^ d` is surjective onto the punctured disc), so `G` is meromorphic at `0` by
`Work.EQ.meromorphicAt_punctured_bounded`; finally `g s = G s / s ^ M` is the descent of `f`. -/
theorem descend_coord {ρ : ℝ} (hρ : 0 < ρ) {d : ℕ} (hd : 0 < d) {ω : ℂ}
    (hω : ω ^ d = 1) (hprim : ∀ m : ℕ, 0 < m → m < d → ω ^ m ≠ 1)
    {f : ℂ → ℂ}
    (hf_an : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) ρ \ {0}))
    (hf_m : MeromorphicAt f 0)
    (hinv : ∀ t : ℂ, t ∈ Metric.ball (0 : ℂ) ρ \ {0} → f (ω * t) = f t) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) (ρ ^ d) \ {0}) ∧
      MeromorphicAt g 0 ∧
      ∀ t : ℂ, t ∈ Metric.ball (0 : ℂ) ρ \ {0} → f t = g (t ^ d) := by
  obtain ⟨M, hM⟩ := hf_m
  have hM' : AnalyticAt ℂ (fun z : ℂ => z ^ M * f z) 0 := by
    simpa [sub_zero, smul_eq_mul] using hM
  have hωnorm : ‖ω‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hω hd.ne'
  have hωne : ω ≠ 0 := fun h => by rw [h, norm_zero] at hωnorm; exact one_ne_zero hωnorm.symm
  set F : ℂ → ℂ := fun t => t ^ (M * d) * f t with hFdef
  have hF_an : AnalyticOnNhd ℂ F (Metric.ball (0 : ℂ) ρ \ {0}) := by
    intro t ht
    rw [hFdef]
    exact (analyticAt_pow_id (M * d)).mul (hf_an t ht)
  have hF_inv : ∀ t : ℂ, t ∈ Metric.ball (0 : ℂ) ρ \ {0} → F (ω * t) = F t := by
    intro t ht
    have hmem : ω * t ∈ Metric.ball (0 : ℂ) ρ \ {0} := by
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, dist_zero_right, norm_mul, hωnorm, one_mul]
        have ht1 := Metric.mem_ball.mp ht.1
        rwa [dist_zero_right] at ht1
      · simp only [Set.mem_singleton_iff]; exact mul_ne_zero hωne (by simpa using ht.2)
    rw [hFdef]
    change (ω * t) ^ (M * d) * f (ω * t) = t ^ (M * d) * f t
    rw [mul_pow, hinv t ht]
    have hωMd : ω ^ (M * d) = 1 := by
      rw [Nat.mul_comm, pow_mul, hω, one_pow]
    rw [hωMd, one_mul]
  obtain ⟨G, hGan, hFG⟩ :=
    Work.Topology.exists_factor_of_root_invariant hρ hF_an hd hω hprim hF_inv
  have hFa : AnalyticAt ℂ F 0 := by
    have hMid : M * (d - 1) + M = M * d := by
      cases d with
      | zero => omega
      | succ k => simp [Nat.mul_succ]
    refine AnalyticAt.congr ((analyticAt_pow_id (M * (d - 1))).mul hM') ?_
    filter_upwards with z
    rw [hFdef]
    simp only [Pi.mul_apply]
    rw [← mul_assoc, ← pow_add, hMid]
  have hFbdd : ∃ r0 : ℝ, 0 < r0 ∧ ∀ z ∈ Metric.ball (0 : ℂ) r0, ‖F z‖ ≤ ‖F 0‖ + 1 := by
    have hcont := hFa.continuousAt
    have hev : ∀ᶠ z in 𝓝 (0 : ℂ), ‖F z‖ ≤ ‖F 0‖ + 1 := by
      have hb : ∀ᶠ z in 𝓝 (0 : ℂ), F z ∈ Metric.ball (F 0) 1 :=
        hcont.tendsto.eventually (Metric.ball_mem_nhds (F 0) one_pos)
      filter_upwards [hb] with z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have h2 : ‖F z‖ ≤ ‖F z - F 0‖ + ‖F 0‖ := by
        have := norm_add_le (F z - F 0) (F 0); rwa [sub_add_cancel] at this
      linarith [norm_nonneg (F 0)]
    rw [Filter.eventually_iff, Metric.mem_nhds_iff] at hev
    obtain ⟨r0, hr0, hsub⟩ := hev
    exact ⟨r0, hr0, fun z hz => hsub hz⟩
  obtain ⟨r0, hr0pos, hr0bdd⟩ := hFbdd
  set r : ℝ := min r0 ρ with hrdef
  have hrmem : 0 < r := lt_min hr0pos hρ
  have hrρ : r ≤ ρ := min_le_right _ _
  have hrr0 : r ≤ r0 := min_le_left _ _
  have hGan_r : AnalyticOnNhd ℂ G (Metric.ball (0 : ℂ) (r ^ d) \ {0}) := by
    refine hGan.mono (fun z hz => ⟨?_, hz.2⟩)
    have hz1 := Metric.mem_ball.mp hz.1
    rw [dist_zero_right] at hz1
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_lt_of_le hz1 (pow_le_pow_left₀ (le_of_lt hrmem) hrρ d)
  have hGbdd : ∀ s ∈ Metric.ball (0 : ℂ) (r ^ d) \ {0}, ‖G s‖ ≤ ‖F 0‖ + 1 := by
    intro s hs
    have hsne : s ≠ 0 := by simpa using hs.2
    have hsl : ‖s‖ < r ^ d := by
      have := Metric.mem_ball.mp hs.1
      rwa [dist_zero_right] at this
    obtain ⟨t, ht, ht0, htlt⟩ := bp_root_aux (w := s) (ρ := r) (k := d) hd hrmem hsne hsl
    have htmem : t ∈ Metric.ball (0 : ℂ) ρ \ {0} := by
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, dist_zero_right]
        exact lt_of_lt_of_le htlt hrρ
      · simp only [Set.mem_singleton_iff]
        exact norm_ne_zero_iff.mp (ne_of_gt ht0)
    have hFt := hFG t htmem
    rw [ht] at hFt
    rw [← hFt]
    exact hr0bdd t (by rw [Metric.mem_ball, dist_zero_right]; exact lt_of_lt_of_le htlt hrr0)
  have hGmer : MeromorphicAt G 0 :=
    meromorphicAt_punctured_bounded (pow_pos hrmem d) hGan_r hGbdd
  refine ⟨fun s => G s / s ^ M, ?_, ?_, ?_⟩
  · intro s hs
    have hsne : s ≠ 0 := by simpa using hs.2
    exact (hGan s hs).div (analyticAt_pow_id M) (pow_ne_zero M hsne)
  · exact hGmer.div (analyticAt_pow_id M).meromorphicAt
  · intro t ht
    have ht0 : t ≠ 0 := by simpa using ht.2
    have hFt := hFG t ht
    rw [hFdef] at hFt
    show f t = G (t ^ d) / (t ^ d) ^ M
    rw [← hFt]
    rw [show (t ^ d) ^ M = t ^ (M * d) from by rw [← pow_mul, Nat.mul_comm]]
    rw [mul_div_cancel_left₀ (f t) (pow_ne_zero (M * d) ht0)]

/-- **Primitive reduction of a backward-Puiseux branch.**

If a rotation `ω` (a primitive `d`-th root of unity, `d ∣ 2 ^ N`) leaves the branch
`t ↦ branchPt a c u₀ R σ t` invariant on the punctured disc, then the branch descends: there is a
family `β` on the punctured disc of radius `(rhoFin') ^ d` with `β (t ^ d) = branchPt σ t`, whose
coordinates are analytic there and meromorphic at `0`, whose steps are regular pairs, and whose
last entry is `c (u₀ + s ^ (2 ^ N / d))`.

Route: each of the finitely many coordinates `t ↦ (branchPt σ t j).i` is analytic on the punctured
disc (`Work.EQ.branchPt_analytic`) and meromorphic at `0` (`Work.EQ.branchPt_meromorphic`); for a
function `f` meromorphic at `0` and invariant under the primitive root `ω`, the function
`F t = t ^ (m * d) * f t` (where `m` makes `t ^ m * f t` analytic at `0`) is invariant, so
`Work.Topology.exists_factor_of_root_invariant` applies to `F`, and `G` yields
`g s = G s / s ^ m` with `f t = g (t ^ d)`; this is the meromorphic descent, applied coordinatewise
with the common exponent `d`. -/
theorem branchPt_descend {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ}
    (hR : 0 < R) (hc : AnalyticOnNhd ℂ c (Metric.ball u₀ R)) {σ : Fin N → Bool}
    (hσ : Work.EQ.Adm a c u₀ R σ)
    {d : ℕ} (hd : 0 < d) (hdvd : d ∣ 2 ^ N) {ω : ℂ} (hω : ω ^ d = 1)
    (hprim : ∀ m : ℕ, 0 < m → m < d → ω ^ m ≠ 1)
    (hinv : ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < Work.EQ.rhoFin' a c u₀ R N →
      Work.EQ.branchPt a c u₀ R σ (ω * t) = Work.EQ.branchPt a c u₀ R σ t) :
    ∃ β : ℂ → Fin (N + 1) → ℂ × ℂ,
      (∀ j, AnalyticOnNhd ℂ (fun s => β s j)
        (Metric.ball (0 : ℂ) ((Work.EQ.rhoFin' a c u₀ R N) ^ d) \ {0})) ∧
      (∀ j, MeromorphicAt (fun s => β s j) 0) ∧
      (∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < Work.EQ.rhoFin' a c u₀ R N →
        β (t ^ d) = Work.EQ.branchPt a c u₀ R σ t) ∧
      (∀ s : ℂ, 0 < ‖s‖ → ‖s‖ < (Work.EQ.rhoFin' a c u₀ R N) ^ d → ∀ j : Fin N,
        Work.EQ.RegPair a (β s (Fin.castSucc j)) (β s (Fin.succ j))) ∧
      (∀ s : ℂ, 0 < ‖s‖ → ‖s‖ < (Work.EQ.rhoFin' a c u₀ R N) ^ d →
        β s (Fin.last N) = c (u₀ + s ^ (2 ^ N / d))) := by
  classical
  have hP : 0 < rhoFin' a c u₀ R N := rhoFin'_pos hR hc
  have hf1_an : ∀ j : Fin (N + 1), AnalyticOnNhd ℂ (fun t => (branchPt a c u₀ R σ t j).1)
      (Metric.ball (0 : ℂ) (rhoFin' a c u₀ R N) \ {0}) :=
    fun j => (branchPt_analytic hR hc hσ j).1
  have hf2_an : ∀ j : Fin (N + 1), AnalyticOnNhd ℂ (fun t => (branchPt a c u₀ R σ t j).2)
      (Metric.ball (0 : ℂ) (rhoFin' a c u₀ R N) \ {0}) :=
    fun j => (branchPt_analytic hR hc hσ j).2
  have hf1_m : ∀ j : Fin (N + 1), MeromorphicAt (fun t => (branchPt a c u₀ R σ t j).1) 0 :=
    fun j => (branchPt_meromorphic hR hc hσ j).1
  have hf2_m : ∀ j : Fin (N + 1), MeromorphicAt (fun t => (branchPt a c u₀ R σ t j).2) 0 :=
    fun j => (branchPt_meromorphic hR hc hσ j).2
  have hf1_inv : ∀ j : Fin (N + 1), ∀ t : ℂ,
      t ∈ Metric.ball (0 : ℂ) (rhoFin' a c u₀ R N) \ {0} →
      (fun t => (branchPt a c u₀ R σ t j).1) (ω * t)
        = (fun t => (branchPt a c u₀ R σ t j).1) t := by
    intro j t ht
    have ht1 : 0 < ‖t‖ := norm_pos_iff.mpr (by simpa using ht.2)
    have ht2 : ‖t‖ < rhoFin' a c u₀ R N := by
      have := Metric.mem_ball.mp ht.1; rwa [dist_zero_right] at this
    show (branchPt a c u₀ R σ (ω * t) j).1 = (branchPt a c u₀ R σ t j).1
    rw [hinv t ht1 ht2]
  have hf2_inv : ∀ j : Fin (N + 1), ∀ t : ℂ,
      t ∈ Metric.ball (0 : ℂ) (rhoFin' a c u₀ R N) \ {0} →
      (fun t => (branchPt a c u₀ R σ t j).2) (ω * t)
        = (fun t => (branchPt a c u₀ R σ t j).2) t := by
    intro j t ht
    have ht1 : 0 < ‖t‖ := norm_pos_iff.mpr (by simpa using ht.2)
    have ht2 : ‖t‖ < rhoFin' a c u₀ R N := by
      have := Metric.mem_ball.mp ht.1; rwa [dist_zero_right] at this
    show (branchPt a c u₀ R σ (ω * t) j).2 = (branchPt a c u₀ R σ t j).2
    rw [hinv t ht1 ht2]
  have hdec1 : ∀ j : Fin (N + 1), ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) ((rhoFin' a c u₀ R N) ^ d) \ {0}) ∧
      MeromorphicAt g 0 ∧
      ∀ t : ℂ, t ∈ Metric.ball (0 : ℂ) (rhoFin' a c u₀ R N) \ {0} →
        (branchPt a c u₀ R σ t j).1 = g (t ^ d) :=
    fun j => descend_coord hP hd hω hprim (hf1_an j) (hf1_m j) (hf1_inv j)
  have hdec2 : ∀ j : Fin (N + 1), ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) ((rhoFin' a c u₀ R N) ^ d) \ {0}) ∧
      MeromorphicAt g 0 ∧
      ∀ t : ℂ, t ∈ Metric.ball (0 : ℂ) (rhoFin' a c u₀ R N) \ {0} →
        (branchPt a c u₀ R σ t j).2 = g (t ^ d) :=
    fun j => descend_coord hP hd hω hprim (hf2_an j) (hf2_m j) (hf2_inv j)
  let g1 : Fin (N + 1) → ℂ → ℂ := fun j => Classical.choose (hdec1 j)
  let g2 : Fin (N + 1) → ℂ → ℂ := fun j => Classical.choose (hdec2 j)
  have g1_an : ∀ j, AnalyticOnNhd ℂ (g1 j)
      (Metric.ball (0 : ℂ) ((rhoFin' a c u₀ R N) ^ d) \ {0}) :=
    fun j => (Classical.choose_spec (hdec1 j)).1
  have g2_an : ∀ j, AnalyticOnNhd ℂ (g2 j)
      (Metric.ball (0 : ℂ) ((rhoFin' a c u₀ R N) ^ d) \ {0}) :=
    fun j => (Classical.choose_spec (hdec2 j)).1
  have g1_m : ∀ j, MeromorphicAt (g1 j) 0 := fun j => (Classical.choose_spec (hdec1 j)).2.1
  have g2_m : ∀ j, MeromorphicAt (g2 j) 0 := fun j => (Classical.choose_spec (hdec2 j)).2.1
  have g1_eq : ∀ (j : Fin (N + 1)) (t : ℂ),
      t ∈ Metric.ball (0 : ℂ) (rhoFin' a c u₀ R N) \ {0} →
      (branchPt a c u₀ R σ t j).1 = g1 j (t ^ d) :=
    fun j => (Classical.choose_spec (hdec1 j)).2.2
  have g2_eq : ∀ (j : Fin (N + 1)) (t : ℂ),
      t ∈ Metric.ball (0 : ℂ) (rhoFin' a c u₀ R N) \ {0} →
      (branchPt a c u₀ R σ t j).2 = g2 j (t ^ d) :=
    fun j => (Classical.choose_spec (hdec2 j)).2.2
  let β : ℂ → Fin (N + 1) → ℂ × ℂ := fun s j => (g1 j s, g2 j s)
  refine ⟨β, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact (g1_an j).prod (g2_an j)
  · intro j
    exact meromorphicAt_pair (g1_m j) (g2_m j)
  · intro t ht1 ht2
    funext j
    have htmem : t ∈ Metric.ball (0 : ℂ) (rhoFin' a c u₀ R N) \ {0} :=
      ⟨by rw [Metric.mem_ball, dist_zero_right]; exact ht2,
        by simpa using norm_ne_zero_iff.mp (ne_of_gt ht1)⟩
    exact Prod.ext (g1_eq j t htmem).symm (g2_eq j t htmem).symm
  · intro s hs1 hs2 j
    have hsne : s ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hs1)
    obtain ⟨t, ht, ht0, htlt⟩ :=
      bp_root_aux (w := s) (ρ := rhoFin' a c u₀ R N) (k := d) hd hP hsne hs2
    have htne : t ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt ht0)
    have htmem : t ∈ Metric.ball (0 : ℂ) (rhoFin' a c u₀ R N) \ {0} :=
      ⟨by rw [Metric.mem_ball, dist_zero_right]; exact htlt, by simpa using htne⟩
    have hβs : β s = branchPt a c u₀ R σ t := by
      funext k
      show (g1 k s, g2 k s) = branchPt a c u₀ R σ t k
      rw [← ht]
      exact Prod.ext (g1_eq k t htmem).symm (g2_eq k t htmem).symm
    rw [hβs]
    exact branchPt_reg hR hc hσ htlt htne j
  · intro s hs1 hs2
    have hsne : s ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hs1)
    obtain ⟨t, ht, ht0, htlt⟩ :=
      bp_root_aux (w := s) (ρ := rhoFin' a c u₀ R N) (k := d) hd hP hsne hs2
    have htne : t ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt ht0)
    have htmem : t ∈ Metric.ball (0 : ℂ) (rhoFin' a c u₀ R N) \ {0} :=
      ⟨by rw [Metric.mem_ball, dist_zero_right]; exact htlt, by simpa using htne⟩
    have hβs : β s = branchPt a c u₀ R σ t := by
      funext k
      show (g1 k s, g2 k s) = branchPt a c u₀ R σ t k
      rw [← ht]
      exact Prod.ext (g1_eq k t htmem).symm (g2_eq k t htmem).symm
    rw [hβs, branchPt_last]
    congr 1
    rw [← ht]
    rw [show (t ^ d) ^ (2 ^ N / d) = t ^ (2 ^ N) from by
      rw [← pow_mul, Nat.mul_div_cancel' hdvd]]

end Work.EQ

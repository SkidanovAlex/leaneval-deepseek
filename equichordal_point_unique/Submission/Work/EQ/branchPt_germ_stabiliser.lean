import Mathlib
import Submission.Work.EQ.bp_aux
import Submission.Work.EQ.backward_puiseux
import Submission.Work.EQ.branchPt_meromorphic
import Submission.Work.EQ.germInv_defs

namespace Work.EQ

open Filter _root_.Topology
open Complex Metric

noncomputable section

/-- **A small parameter with small `2 ^ N`-th powers.**  For any `δ, δi > 0` and any `τ` there is a
nonzero `t` with `‖t‖ < δ` whose `2 ^ N`-th power *and* the `2 ^ N`-th power of `τ t` both have
norm `< δi`.  Explicitly one may take a small positive real. -/
lemma germSmallPoint (N : ℕ) {τ : ℂ} {δ δi : ℝ} (hδ : 0 < δ) (hδi : 0 < δi) :
    ∃ t : ℂ, 0 < ‖t‖ ∧ ‖t‖ < δ ∧ ‖t ^ (2 ^ N)‖ < δi ∧ ‖(τ * t) ^ (2 ^ N)‖ < δi := by
  have h1le : 1 ≤ 2 ^ N := Nat.one_le_two_pow
  set e : ℝ := min δ (min 1 (δi / (2 * (1 + ‖τ‖) ^ (2 ^ N)))) / 2 with he
  have hW : 0 < δi / (2 * (1 + ‖τ‖) ^ (2 ^ N)) := by positivity
  have hinner : 0 < min δ (min 1 (δi / (2 * (1 + ‖τ‖) ^ (2 ^ N)))) :=
    lt_min hδ (lt_min one_pos hW)
  have he0 : 0 < e := by rw [he]; exact div_pos hinner two_pos
  have heδ : e < δ := by
    rw [he]
    have h := min_le_left δ (min 1 (δi / (2 * (1 + ‖τ‖) ^ (2 ^ N))))
    linarith
  have he1 : e ≤ 1 := by
    rw [he]
    have h : min δ (min 1 (δi / (2 * (1 + ‖τ‖) ^ (2 ^ N)))) ≤ 1 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have heW : e < δi / (2 * (1 + ‖τ‖) ^ (2 ^ N)) := by
    rw [he]
    have h : min δ (min 1 (δi / (2 * (1 + ‖τ‖) ^ (2 ^ N)))) ≤
        δi / (2 * (1 + ‖τ‖) ^ (2 ^ N)) := le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  have hen : ‖(e : ℂ)‖ = e := by
    rw [Complex.norm_real, Real.norm_of_nonneg he0.le]
  have hApos : 0 < 1 + ‖τ‖ := by positivity
  have hWle : δi / (2 * (1 + ‖τ‖) ^ (2 ^ N)) ≤ δi := by
    rw [div_le_iff₀ (by positivity)]
    have h2 : (1 : ℝ) ≤ 2 * (1 + ‖τ‖) ^ (2 ^ N) := by
      have h1 : (1 : ℝ) ≤ (1 + ‖τ‖) ^ (2 ^ N) :=
        one_le_pow₀ (by linarith [norm_nonneg τ] : (1 : ℝ) ≤ 1 + ‖τ‖)
      linarith
    nlinarith [hδi]
  refine ⟨(e : ℂ), ?_, ?_, ?_, ?_⟩
  · rw [hen]; exact he0
  · rw [hen]; exact heδ
  · rw [norm_pow, hen]
    have h := pow_le_pow_of_le_one he0.le he1 h1le
    simp only [pow_one] at h
    exact lt_of_lt_of_le (lt_of_le_of_lt h heW) hWle
  · rw [norm_pow, norm_mul, hen, mul_pow]
    have hepow : e ^ (2 ^ N) ≤ e := by
      have h := pow_le_pow_of_le_one he0.le he1 h1le
      simpa using h
    have hTpow : ‖τ‖ ^ (2 ^ N) ≤ (1 + ‖τ‖) ^ (2 ^ N) :=
      pow_le_pow_left₀ (norm_nonneg τ) (le_add_of_nonneg_left (by norm_num)) _
    have hmul : ‖τ‖ ^ (2 ^ N) * e ^ (2 ^ N) ≤ (1 + ‖τ‖) ^ (2 ^ N) * e :=
      mul_le_mul hTpow hepow (pow_nonneg he0.le _) (pow_nonneg hApos.le _)
    refine lt_of_le_of_lt hmul ?_
    have h2 : (1 + ‖τ‖) ^ (2 ^ N) * e < (1 + ‖τ‖) ^ (2 ^ N) *
        (δi / (2 * (1 + ‖τ‖) ^ (2 ^ N))) :=
      mul_lt_mul_of_pos_left heW (pow_pos hApos _)
    refine lt_of_lt_of_le h2 ?_
    have hs : (1 + ‖τ‖) ^ (2 ^ N) * (δi / (2 * (1 + ‖τ‖) ^ (2 ^ N))) = δi / 2 := by
      have hne : (1 + ‖τ‖) ^ (2 ^ N) ≠ 0 := pow_ne_zero _ hApos.ne'
      field_simp
    rw [hs]
    linarith

/-- **Germ-preserving rotations are `2 ^ N`-th roots of unity.**  The last coordinate of the branch
is `c (u₀ + t ^ (2 ^ N))`; germ equality therefore gives
`c (u₀ + (τ t) ^ (2 ^ N)) = c (u₀ + t ^ (2 ^ N))`, and for a suitable small `t`
(`Work.EQ.germSmallPoint`) both arguments lie in the ball where the second coordinate of `c` is
injective.  Hence `(τ t) ^ (2 ^ N) = t ^ (2 ^ N)` and, since `t ≠ 0`, `τ ^ (2 ^ N) = 1`. -/
lemma germInv_pow_eq_one {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ} {σ : Fin N → Bool}
    (hinj : ∃ δ : ℝ, 0 < δ ∧ Set.InjOn (fun u : ℂ => (c u).2) (Metric.ball u₀ δ))
    {τ : ℂ} (hτ : GermInv a c u₀ R σ τ) : τ ^ (2 ^ N) = 1 := by
  obtain ⟨δ, hδ0, -, hδeq⟩ := hτ
  obtain ⟨δi, hδi0, hinjOn⟩ := hinj
  obtain ⟨t, ht0, htδ, htpow, hτtpow⟩ := germSmallPoint N hδ0 hδi0
  have hlast : branchPt a c u₀ R σ (τ * t) (Fin.last N)
      = branchPt a c u₀ R σ t (Fin.last N) := by
    rw [hδeq t ht0 htδ]
  rw [branchPt_last, branchPt_last] at hlast
  have hm1 : u₀ + (τ * t) ^ (2 ^ N) ∈ Metric.ball u₀ δi := by
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using hτtpow
  have hm2 : u₀ + t ^ (2 ^ N) ∈ Metric.ball u₀ δi := by
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using htpow
  have huu := hinjOn hm1 hm2 (congrArg Prod.snd hlast)
  have huu' : (τ * t) ^ (2 ^ N) = t ^ (2 ^ N) := by simpa using huu
  have hmul : τ ^ (2 ^ N) * t ^ (2 ^ N) = t ^ (2 ^ N) := by
    rw [← mul_pow]; exact huu'
  have htne : t ^ (2 ^ N) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mp ht0.ne')
  have hfin : τ ^ (2 ^ N) * t ^ (2 ^ N) = 1 * t ^ (2 ^ N) := by rw [one_mul]; exact hmul
  exact mul_right_cancel₀ htne hfin

/-- A germ-preserving rotation has norm `1`: it satisfies `τ ^ (2 ^ N) = 1`
(`Work.EQ.germInv_pow_two_pow_eq_one`) and a nonzero power of `τ` is `1`. -/
lemma germInv_norm_one {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ} {σ : Fin N → Bool}
    (hinj : ∃ δ : ℝ, 0 < δ ∧ Set.InjOn (fun u : ℂ => (c u).2) (Metric.ball u₀ δ))
    {τ : ℂ} (hτ : GermInv a c u₀ R σ τ) : ‖τ‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one (germInv_pow_eq_one hinj hτ) (by positivity)

/-- **Germ equality upgrades to equality on the whole punctured disc.**  If the rotation `τ` has
`‖τ‖ = 1` and preserves the branch germ, then it preserves the branch on the *whole* punctured disc
of radius `rhoFin' a c u₀ R N`.  Indeed, for every level `j`, the coordinate difference
`z ↦ branchPt (τ z) j - branchPt z j` is analytic on that punctured disc (the condition `‖τ‖ = 1` is
exactly what keeps `τ z` inside it) and vanishes on a punctured neighbourhood of `0`; the punctured
disc is connected, so the difference vanishes everywhere. -/
lemma germInv_full {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ} {σ : Fin N → Bool}
    (hR : 0 < R) (hc : AnalyticOnNhd ℂ c (Metric.ball u₀ R)) (hσ : Adm a c u₀ R σ)
    {τ : ℂ} (hnorm : ‖τ‖ = 1) (hτ : GermInv a c u₀ R σ τ) :
    ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < rhoFin' a c u₀ R N →
      branchPt a c u₀ R σ (τ * t) = branchPt a c u₀ R σ t := by
  obtain ⟨δ, hδ0, -, hδeq⟩ := hτ
  have hρ : 0 < rhoFin' a c u₀ R N := rhoFin'_pos hR hc
  have hτne : τ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    exact one_ne_zero hnorm.symm
  have hball : Metric.ball (0 : ℂ) δ ∈ 𝓝[≠] (0 : ℂ) :=
    nhdsWithin_le_nhds (α := ℂ) (a := 0) (s := {0}ᶜ) (Metric.ball_mem_nhds (0 : ℂ) hδ0)
  -- the fundamental case: one level `j`, one parameter `t`
  have key : ∀ (j : Fin (N + 1)), ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < rhoFin' a c u₀ R N →
      branchPt a c u₀ R σ (τ * t) j = branchPt a c u₀ R σ t j := by
    intro j t ht0 htρ
    have hmem : τ * t ∈ Metric.ball 0 (rhoFin' a c u₀ R N) \ {0} := by
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, dist_zero_right, norm_mul, hnorm, one_mul]
        exact htρ
      · simp only [Set.mem_singleton_iff]
        exact mul_ne_zero hτne (norm_ne_zero_iff.mp ht0.ne')
    -- analyticity of the two coordinate differences on the punctured disc
    have hfst : AnalyticOnNhd ℂ (fun z : ℂ =>
        (branchPt a c u₀ R σ (τ * z) j).1 - (branchPt a c u₀ R σ z j).1)
        (Metric.ball 0 (rhoFin' a c u₀ R N) \ {0}) := by
      intro z hz
      have hzball : ‖z‖ < rhoFin' a c u₀ R N := by
        have h := hz.1; rwa [Metric.mem_ball, dist_zero_right] at h
      have hzne : z ≠ 0 := by simpa using hz.2
      have htz : τ * z ∈ Metric.ball 0 (rhoFin' a c u₀ R N) \ {0} := by
        refine ⟨?_, ?_⟩
        · rw [Metric.mem_ball, dist_zero_right, norm_mul, hnorm, one_mul]; exact hzball
        · simp only [Set.mem_singleton_iff]; exact mul_ne_zero hτne hzne
      have hb := branchPt_analytic hR hc hσ j
      exact ((hb.1 (τ * z) htz).comp (f := fun w : ℂ => τ * w)
          (analyticAt_const.mul analyticAt_id)).sub (hb.1 z hz)
    have hsnd : AnalyticOnNhd ℂ (fun z : ℂ =>
        (branchPt a c u₀ R σ (τ * z) j).2 - (branchPt a c u₀ R σ z j).2)
        (Metric.ball 0 (rhoFin' a c u₀ R N) \ {0}) := by
      intro z hz
      have hzball : ‖z‖ < rhoFin' a c u₀ R N := by
        have h := hz.1; rwa [Metric.mem_ball, dist_zero_right] at h
      have hzne : z ≠ 0 := by simpa using hz.2
      have htz : τ * z ∈ Metric.ball 0 (rhoFin' a c u₀ R N) \ {0} := by
        refine ⟨?_, ?_⟩
        · rw [Metric.mem_ball, dist_zero_right, norm_mul, hnorm, one_mul]; exact hzball
        · simp only [Set.mem_singleton_iff]; exact mul_ne_zero hτne hzne
      have hb := branchPt_analytic hR hc hσ j
      exact ((hb.2 (τ * z) htz).comp (f := fun w : ℂ => τ * w)
          (analyticAt_const.mul analyticAt_id)).sub (hb.2 z hz)
    -- the differences vanish on a punctured neighbourhood of `0`
    have hev1 : (fun z : ℂ =>
        (branchPt a c u₀ R σ (τ * z) j).1 - (branchPt a c u₀ R σ z j).1)
        =ᶠ[𝓝[≠] (0 : ℂ)] 0 := by
      filter_upwards [hball, self_mem_nhdsWithin] with z hz hzne
      have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr (by simpa using hzne)
      have hzδ : ‖z‖ < δ := by
        have h := hz; rwa [Metric.mem_ball, dist_zero_right] at h
      rw [hδeq z hz0 hzδ, sub_self]
      rfl
    have hev2 : (fun z : ℂ =>
        (branchPt a c u₀ R σ (τ * z) j).2 - (branchPt a c u₀ R σ z j).2)
        =ᶠ[𝓝[≠] (0 : ℂ)] 0 := by
      filter_upwards [hball, self_mem_nhdsWithin] with z hz hzne
      have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr (by simpa using hzne)
      have hzδ : ‖z‖ < δ := by
        have h := hz; rwa [Metric.mem_ball, dist_zero_right] at h
      rw [hδeq z hz0 hzδ, sub_self]
      rfl
    have hz1 := eqOn_zero_of_eventually_zero hρ hfst hev1
    have hz2 := eqOn_zero_of_eventually_zero hρ hsnd hev2
    have htmem : t ∈ Metric.ball 0 (rhoFin' a c u₀ R N) \ {0} :=
      ⟨by rw [Metric.mem_ball, dist_zero_right]; exact htρ,
        by simpa using ht0.ne'⟩
    exact Prod.ext (sub_eq_zero.mp (hz1 t htmem)) (sub_eq_zero.mp (hz2 t htmem))
  intro t ht0 htρ
  funext j
  exact key j t ht0 htρ

/-- **The germ rotational stabiliser of an `F3` branch.**

`Work.EQ.branchPt a c u₀ R σ t j` parametrises the backward `EqRelC`-chains of length `N` ending at
`c (u₀ + t ^ (2^N))` with sign sequence `σ`; its coordinates are meromorphic at `0`
(`Work.EQ.branchPt_meromorphic`).

Claim: the group `G` of rotations `τ` that preserve the *germ* of the branch at `0` (i.e.
`branchPt … (τ t) = branchPt … t` for all `t` in some punctured disc `0 < ‖t‖ < δ`), is the cyclic
group `μ_d` of `d`-th roots of unity for some `d ∣ 2 ^ N`.  Formally: there is a primitive `d`-th
root of unity `ω` such that

* `ω` preserves the branch on the *whole* punctured disc of radius `rhoFin' a c u₀ R N` (analytic
  continuation on the connected punctured disc upgrades the germ equality);
* conversely every `τ` preserving the germ satisfies `τ ^ d = 1`.

`τ` is *not* assumed in advance to be a root of unity.  The hypothesis `hinj` (injectivity of the
second coordinate of `c` near `u₀`, as `Work.EQ.germC_facts` provides for `germC`) is what makes the
last component of the branch, `c (u₀ + t ^ (2^N))`, separate rotations: from germ-equality one gets
`c (u₀ + t ^ (2^N)) = c (u₀ + (τ t) ^ (2^N))` and hence `τ ^ (2^N) = 1`; the subgroup of the cyclic
group `μ_{2^N}` consisting of the germ-preserving rotations is then `μ_d`. -/
theorem branchPt_germ_stabiliser {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ} (hR : 0 < R)
    (hc : AnalyticOnNhd ℂ c (Metric.ball u₀ R))
    (hinj : ∃ δ : ℝ, 0 < δ ∧ Set.InjOn (fun u : ℂ => (c u).2) (Metric.ball u₀ δ))
    {σ : Fin N → Bool} (hσ : Work.EQ.Adm a c u₀ R σ) :
    ∃ (d : ℕ) (_ : 0 < d) (_ : d ∣ 2 ^ N) (ω : ℂ) (_ : ω ^ d = 1)
      (_ : ∀ m : ℕ, 0 < m → m < d → ω ^ m ≠ 1),
      (∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < Work.EQ.rhoFin' a c u₀ R N →
        Work.EQ.branchPt a c u₀ R σ (ω * t) = Work.EQ.branchPt a c u₀ R σ t) ∧
      (∀ τ : ℂ,
        (∃ δ : ℝ, 0 < δ ∧ δ ≤ Work.EQ.rhoFin' a c u₀ R N ∧
          ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < δ →
            Work.EQ.branchPt a c u₀ R σ (τ * t) = Work.EQ.branchPt a c u₀ R σ t) →
        τ ^ d = 1) := by
  classical
  -- Every germ-preserving rotation is a `2 ^ N`-th root of unity
  -- (`Work.EQ.germInv_pow_eq_one`), so the germ-preserving rotations are parametrised by
  -- the exponent `i` in `orderOf τ = 2 ^ i`, `i ≤ N`.  Take `i` maximal; the corresponding
  -- rotation `ω` is the desired primitive generator.
  let P : ℕ → Prop := fun i => ∃ τ : ℂ, GermInv a c u₀ R σ τ ∧ orderOf τ = 2 ^ i
  have hP0 : P 0 := ⟨1, germInv_one hR hc, by simp⟩
  obtain ⟨ω, hωgerm, hωord⟩ := Nat.findGreatest_spec (P := P) (Nat.zero_le N) hP0
  have hjN : Nat.findGreatest P N ≤ N := Nat.findGreatest_le N
  refine ⟨2 ^ Nat.findGreatest P N, by positivity, pow_dvd_pow 2 hjN, ω, ?_, ?_, ?_, ?_⟩
  · rw [← hωord]
    exact pow_orderOf_eq_one ω
  · intro m hm0 hmlt
    exact pow_ne_one_of_lt_orderOf (Nat.ne_of_gt hm0) (by rwa [hωord])
  · exact germInv_full hR hc hσ (germInv_norm_one hinj hωgerm) hωgerm
  · intro τ hτ
    have hτg : GermInv a c u₀ R σ τ := hτ
    have hdvdpow : orderOf τ ∣ 2 ^ N :=
      orderOf_dvd_iff_pow_eq_one.mpr (germInv_pow_eq_one hinj hτg)
    obtain ⟨i, hiN, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvdpow
    have hile : i ≤ Nat.findGreatest P N := Nat.le_findGreatest hiN ⟨τ, hτg, hi⟩
    have hdvd : orderOf τ ∣ 2 ^ Nat.findGreatest P N := by
      have h2 : (2 : ℕ) ^ i ∣ 2 ^ Nat.findGreatest P N := pow_dvd_pow 2 hile
      rwa [hi]
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd

end

end Work.EQ

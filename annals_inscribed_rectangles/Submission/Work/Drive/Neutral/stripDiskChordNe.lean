import Mathlib
import Submission.Work.Drive.Neutral.StripDiskAux
import Submission.Work.Drive.Neutral.dataChord_spec

namespace Work.Drive.Neutral

open Manifold
open scoped Manifold ContDiff Topology
open Filter

/-!
# Non-vanishing of the strip chord data and of its halving

The clamped opening `sClamp` keeps the two endpoints of the chord at parameter `s ≠ 0` distinct for
*every* opening: `sClamp` is odd and positive on the positive axis, and `|sClamp s| ≤ π - 1 < π`, so
`sClamp s` is never a nonzero multiple of `π`.  Since the endpoints of the chord at `x ≠ 0` are the
curve points at `θ ± sClamp s` (where `Circle.exp θ = x/‖x‖`) and `γ` is injective while a point of
`Circle` has period `2π`, the chord vector `dataChord γ x s` never vanishes for `s ≠ 0`.

The halving `dchW γ` does not vanish for *any* `s` (including `s = 0`, where it is the tangent
direction): for `s ≠ 0` this follows from `dataChord γ x s = s • dchW γ (x, s)`, while for `s = 0`
one uses the chord identity through the divided difference,
`dataChord γ x s' = 2 * sClamp s' * symmC (secantW (curve γ) (θ + sClamp s', θ - sClamp s'))`,
which near `0` (where `sClamp = id`) exhibits `dchW γ (x, ·)` as the continuous function
`s ↦ 2 * symmC (secantW (curve γ) (θ + s, θ - s))` on a punctured neighbourhood of `0`; its value at
`0` is `2 * symmC (deriv (curve γ) θ) ≠ 0` (`secantW_self`, `curve_deriv_ne_zero`), so
`dchW γ (x, 0) ≠ 0` by uniqueness of limits.
-/

/-- The clamped opening is positive for positive openings. -/
lemma sClamp_pos_of_pos {s : ℝ} (h : 0 < s) : 0 < sClamp s := by
  have hσ : 0 < sSig s := by rw [sSig]; positivity
  have hπ1 : 0 < Real.pi - 1 := by linarith [Real.pi_gt_three]
  have hkey : sClamp s = sKappa s * s + (1 - sKappa s) * ((Real.pi - 1) * sSig s) := by
    rw [sClamp]; ring
  rw [hkey]
  rcases lt_or_eq_of_le (sKappa_nonneg s) with hκ | hκ
  · have h1 : 0 < sKappa s * s := mul_pos hκ h
    have h2 : 0 ≤ (1 - sKappa s) * ((Real.pi - 1) * sSig s) :=
      mul_nonneg (by linarith [sKappa_le_one s]) (mul_pos hπ1 hσ).le
    linarith
  · rw [← hκ]; simp only [zero_mul, sub_zero, one_mul]
    simpa using mul_pos hπ1 hσ

/-- The clamped opening vanishes only at `s = 0`. -/
lemma sClamp_ne_zero_aux {s : ℝ} (hs : s ≠ 0) : sClamp s ≠ 0 := by
  rcases lt_trichotomy s 0 with h | h | h
  · have h2 : 0 < sClamp (-s) := sClamp_pos_of_pos (by linarith)
    have hodd : sClamp s = -sClamp (-s) := by
      simpa using sClamp_odd (-s)
    rw [hodd]; linarith
  · exact absurd h hs
  · exact ne_of_gt (sClamp_pos_of_pos h)

theorem stripDiskChordNe (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    (∀ x : ℂ, x ≠ 0 → ∀ s : ℝ, s ≠ 0 → Work.Drive.Neutral.dataChord γ x s ≠ 0) ∧
      (∀ x : ℂ, x ≠ 0 → ∀ s : ℝ, Work.Drive.Neutral.dchW γ (x, s) ≠ 0) := by
  have hbase : ∀ x : ℂ, x ≠ 0 → ∀ s : ℝ, s ≠ 0 → dataChord γ x s ≠ 0 := by
    intro x hx s hs hzero
    -- the chord in terms of a local argument `θ = arg x`
    have hθ : (Circle.exp (Complex.arg x) : ℂ) = x / (‖x‖ : ℂ) := by
      rw [← toCirc_eq_exp_arg x hx]
      exact toCirc_coe x hx
    have hform := dataChord_eq_exp γ x hx hθ s
    have hsymm : symmC (curve γ (Complex.arg x + sClamp s)
        - curve γ (Complex.arg x - sClamp s)) = 0 := by
      rw [← hform]; exact hzero
    have hdiff : curve γ (Complex.arg x + sClamp s) - curve γ (Complex.arg x - sClamp s) = 0 :=
      symmC_eq_zero_iff.mp hsymm
    have hcab : curve γ (Complex.arg x + sClamp s) = curve γ (Complex.arg x - sClamp s) :=
      sub_eq_zero.mp hdiff
    -- injectivity of `γ` on the circle makes the two parameters congruent mod `2π`
    have hinj : Function.Injective γ := hγ.isEmbedding.injective
    have hexp : Circle.exp (Complex.arg x + sClamp s) = Circle.exp (Complex.arg x - sClamp s) :=
      hinj hcab
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp hexp
    have hk3 : sClamp s = Real.pi * (k : ℝ) := by nlinarith [hk]
    have hkabs : |sClamp s| = Real.pi * |(k : ℝ)| := by
      rw [hk3, abs_mul, abs_of_pos Real.pi_pos]
    -- `|sClamp s| ≤ π - 1` forces `k = 0`, whence `sClamp s = 0`, i.e. `s = 0`
    have hle : Real.pi * |(k : ℝ)| ≤ Real.pi - 1 := by rw [← hkabs]; exact abs_sClamp_le
    have hk0 : k = 0 := by
      by_contra hkne
      have hge : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hkne
      have hge2 : Real.pi ≤ Real.pi * |(k : ℝ)| := by
        simpa using mul_le_mul_of_nonneg_left hge Real.pi_pos.le
      linarith [Real.pi_pos]
    have hsz : sClamp s = 0 := by rw [hk3, hk0]; simp
    exact sClamp_ne_zero_aux hs hsz
  refine ⟨hbase, ?_⟩
  intro x hx s
  rcases eq_or_ne s 0 with rfl | hs
  · -- the diagonal: `dchW γ (x, 0)` is the (non-zero) tangent direction
    set θ : ℝ := Complex.arg x with hθdef
    have hθ : (Circle.exp θ : ℂ) = x / (‖x‖ : ℂ) := by
      rw [hθdef, ← toCirc_eq_exp_arg x hx]; exact toCirc_coe x hx
    -- the chord through the divided difference
    have hident : ∀ s' : ℝ, dataChord γ x s' =
        2 * (sClamp s' : ℂ) * symmC (secantW (curve γ) (θ + sClamp s', θ - sClamp s')) := by
      intro s'
      rw [dataChord_eq_exp γ x hx hθ s']
      have hsub : curve γ (θ + sClamp s') - curve γ (θ - sClamp s')
          = (2 * sClamp s') • secantW (curve γ) (θ + sClamp s', θ - sClamp s') := by
        have h' := sub_eq_smul_secantW (contDiff_curve γ hγ) (θ + sClamp s') (θ - sClamp s')
        rwa [show θ + sClamp s' - (θ - sClamp s') = 2 * sClamp s' by ring] at h'
      rw [hsub, symmC_smul]
      push_cast
      ring
    -- away from `0` the clamped opening is the opening, so `dchW` is the unclamped expression
    have hU1 : {s : ℝ | s ≠ 0} ∈ 𝓝[≠] (0:ℝ) := self_mem_nhdsWithin
    have hball : Metric.ball (0:ℝ) (Real.pi / 2) ∈ 𝓝[≠] (0:ℝ) :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0:ℝ) (ε := Real.pi / 2)
        (by linarith [Real.pi_gt_three]))
    have hU2 : {s : ℝ | |s| < Real.pi / 2} ∈ 𝓝[≠] (0:ℝ) := by
      refine Filter.mem_of_superset hball ?_
      intro s hs
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs
      exact hs
    have hU : {s : ℝ | s ≠ 0 ∧ |s| < Real.pi / 2} ∈ 𝓝[≠] (0:ℝ) := Filter.inter_mem hU1 hU2
    have heq : (fun s : ℝ => dchW γ (x, s)) =ᶠ[𝓝[≠] (0:ℝ)]
        (fun s : ℝ => 2 * symmC (secantW (curve γ) (θ + s, θ - s))) := by
      refine Filter.eventually_of_mem hU (fun s hs => ?_)
      obtain ⟨hsne, hslt⟩ := hs
      have hsc : sClamp s = s := sClamp_eq_self hslt.le
      have hsmul := dchW_smul γ hγ hx s
      rw [hident s, hsc] at hsmul
      simp only [Complex.real_smul] at hsmul
      refine mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hsne) ?_
      rw [hsmul]; ring
    -- the unclamped expression is continuous and its value at `0` is the tangent direction
    let Ψ : ℝ → ℂ := fun s => 2 * symmC (secantW (curve γ) (θ + s, θ - s))
    have heqΨ : (fun s : ℝ => dchW γ (x, s)) =ᶠ[𝓝[≠] (0:ℝ)] Ψ := heq
    have hcontΦ : ContinuousAt (fun s : ℝ => dchW γ (x, s)) 0 := by
      have hmem : {p : ℂ × ℝ | p.1 ≠ 0} ∈ 𝓝 (x, 0) :=
        (isOpen_ne.preimage continuous_fst).mem_nhds (show (x, 0).1 ≠ 0 from hx)
      have hcd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dchW γ) (x, 0) :=
        (contDiffOn_dchW γ hγ).contDiffAt hmem
      exact hcd.continuousAt.comp (continuousAt_const.prodMk continuousAt_id)
    have hΨcont : Continuous Ψ := by
      have hsec : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (secantW (curve γ)) :=
        contDiff_secantW (contDiff_curve_top hγ)
      have hpair : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => (θ + s, θ - s)) := by
        fun_prop
      exact (contDiff_const.mul (contDiff_symmC.comp (hsec.comp hpair))).continuous
    have hΨ0 : Ψ 0 = 2 * symmC (deriv (curve γ) θ) := by
      show 2 * symmC (secantW (curve γ) (θ + 0, θ - 0)) = 2 * symmC (deriv (curve γ) θ)
      rw [add_zero, sub_zero, secantW_self]
    have t1 : Tendsto (fun s : ℝ => dchW γ (x, s)) (𝓝[≠] (0:ℝ)) (𝓝 (dchW γ (x, 0))) :=
      hcontΦ.tendsto.mono_left inf_le_left
    have t2 : Tendsto Ψ (𝓝[≠] (0:ℝ)) (𝓝 (Ψ 0)) :=
      hΨcont.continuousAt.tendsto.mono_left inf_le_left
    have t2' : Tendsto Ψ (𝓝[≠] (0:ℝ)) (𝓝 (2 * symmC (deriv (curve γ) θ))) := by
      rw [← hΨ0]; exact t2
    have t2'' : Tendsto (fun s : ℝ => dchW γ (x, s)) (𝓝[≠] (0:ℝ))
        (𝓝 (2 * symmC (deriv (curve γ) θ))) := Tendsto.congr' heqΨ.symm t2'
    have hval : dchW γ (x, 0) = 2 * symmC (deriv (curve γ) θ) := tendsto_nhds_unique t1 t2''
    rw [hval]
    intro h
    rcases mul_eq_zero.mp h with h2 | h2
    · norm_num at h2
    · exact curve_deriv_ne_zero γ hγ θ (symmC_eq_zero_iff.mp h2)
  · -- away from the diagonal the chord does not vanish and `dataChord = s • dchW`
    intro hW
    have hsmul := dchW_smul γ hγ hx s
    rw [hW, smul_zero] at hsmul
    exact hbase x hx s hs hsmul.symm

end Work.Drive.Neutral

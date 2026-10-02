import Mathlib
import Submission.Work.ParamRays.Basic
import Submission.Work.ParamRays.Green
import Submission.Work.ParamRays.Bottcher
import Submission.Work.ParamRays.MbDefs
import Submission.Work.ParamRaysCrit.CritDomain
import Submission.Work.ParamRaysCrit.CritBottcher.IsCritBottcher_modulus
import Submission.Work.ParamRays.IsDynBottcher_modulus
import Submission.Work.ParamRays.greenFun_orbit
import Submission.Work.ParamRays.greenFun_pos_of_lt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Continuity of the potential of the mandelbar

The potential `potential c = log ‖Φ c‖` off the mandelbar and `0` on it is continuous on `ℂ`.

Since `Real.log 0 = 0` and `Φ` is zero on the mandelbar, `potential` *is* the function
`c ↦ log ‖Φ c‖` on the whole plane; the work is to see that this function is continuous at
the points of the mandelbar.

The proof uses the three structural inputs bundled in `NakaneInput`:

* `BottcherExists` gives, through the Green function bounds of `greenFun_pos_of_lt`, the
  **a priori bound** `‖Φ c‖ ≤ (2 (‖c‖ + 1))²` outside the mandelbar — so the values of `Φ`
  are bounded on bounded sets, which rules out `Φ c → ∞` for `c` near a finite parameter;
* `NakaneHomeo` identifies `Φ` on the exterior of the mandelbar with a *homeomorphism* onto
  `‖w‖ > 1`, which rules out `‖Φ c‖ → r > 1` along a bounded sequence;
* together these give `‖Φ c‖ → 1` as `c` approaches the mandelbar, i.e. `potential → 0`
  there, and the potential is glued from its continuous exterior part and its vanishing
  part by the pasting lemma `ContinuousOn.union_continuousAt`.

## Main results

* `Work.ParamRays.norm_Phi_le` : `‖Φ c‖ ≤ (2 (‖c‖ + 1))²` outside the mandelbar.
* `Work.ParamRays.exists_norm_Phi_lt` : `‖Φ c‖ → 1` at the mandelbar.
* `Work.ParamRays.continuousOn_log_Phi` : continuity of `log ‖Φ ·‖` off the mandelbar.
* `Work.ParamRays.continuous_potential` : the potential is continuous.
-/

open Filter
open scoped Real Topology ComplexConjugate

namespace Work.ParamRays

open LeanEval.ComplexAnalysis (Tantibar)

/-! Auxiliary facts about the parameter Böttcher map: the critical value of `T_c` escapes
for `c` outside the mandelbar, and the modulus of `Φ` is the exponential of `2` times the
parameter potential. -/
namespace CP

/-- If a tail of the orbit of `w` escapes, then the orbit of `w` escapes. -/
theorem escOrbit {c w : ℂ} (n : ℕ) (h : Escaping c (orbit c w n)) : Escaping c w := by
  simp only [Escaping] at h ⊢
  rw [← tendsto_add_atTop_iff_nat n]
  have h' : (fun a : ℕ => ‖orbit c w (a + n)‖) = fun a : ℕ => ‖orbit c (orbit c w n) a‖ := by
    funext a
    rw [Nat.add_comm a n]
    exact congrArg Norm.norm (orbit_add c w n a)
  rw [h']
  exact h

/-- `orbit c 0 1 = c`: the critical value is the first point of the critical orbit. -/
theorem orbit_zero_one (c : ℂ) : orbit c 0 1 = c := by
  simp [orbit_succ, Tantibar]

/-- Outside the mandelbar the critical value escapes. -/
theorem criticalValue_escapes {c : ℂ} (hc : c ∉ Mb) : Escaping c c := by
  have hnb : ¬ BoundedOrbit c 0 := hc
  rw [BoundedOrbit] at hnb
  push Not at hnb
  obtain ⟨N, hN⟩ := hnb (max 2 ‖c‖)
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h
    · exfalso
      rw [h0] at hN
      simp only [orbit, Function.iterate_zero, id_eq, norm_zero,
        max_lt_iff] at hN
      linarith [hN.1]
    · exact h
  have hesc : Escaping c (critOrbit c N) := escaping_of_lt_norm c _ hN
  obtain ⟨m, hm⟩ : ∃ m : ℕ, N = m + 1 := ⟨N - 1, by omega⟩
  have hcrit : critOrbit c N = orbit c c m := by
    rw [hm, critOrbit]
    rw [show m + 1 = 1 + m from Nat.add_comm m 1, orbit_add, orbit_zero_one]
  rw [hcrit] at hesc
  exact escOrbit m hesc

/-- Outside the mandelbar the parameter potential is positive. -/
theorem paramPotential_pos {c : ℂ} (hc : c ∉ Mb) : 0 < paramPotential c := by
  have hnb : ¬ BoundedOrbit c 0 := hc
  rw [BoundedOrbit] at hnb
  push Not at hnb
  obtain ⟨N, hN⟩ := hnb (max 2 ‖c‖)
  have hpos : 0 < greenFun c (orbit c 0 N) := greenFun_pos_of_lt c _ hN
  rw [greenFun_orbit] at hpos
  have h2 : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have : 0 < greenFun c 0 := by nlinarith
  simpa [paramPotential] using this

/-- The modulus of the parameter Böttcher map is the exponential of `2` times the potential
of the critical point. -/
theorem norm_Phi_eq_exp (h : NakaneInput) {c : ℂ} (hc : c ∉ Mb) :
    ‖Phi c‖ = Real.exp (2 * paramPotential c) := by
  have hφ : ∃ φ : ℂ → ℂ, IsCritBottcher c φ := h.bottcher c hc
  have hmod := Work.ParamRaysCrit.CritBottcher.IsCritBottcher_modulus
    (Classical.choose_spec hφ) (self_mem_critDomain hc)
  rw [Phi_eq_choose hc hφ, hmod]
  have hshift : greenFun c c = 2 * paramPotential c := by
    have h2 := greenFun_orbit c 0 1
    rw [orbit_zero_one] at h2
    simpa [paramPotential] using h2
  rw [hshift]

/-- Outside the mandelbar the parameter Böttcher map has modulus bigger than `1`. -/
theorem one_lt_norm_Phi (h : NakaneInput) {c : ℂ} (hc : c ∉ Mb) : 1 < ‖Phi c‖ := by
  rw [norm_Phi_eq_exp h hc, ← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by linarith [paramPotential_pos hc])

end CP

/-- **A priori bound for the parameter Böttcher map.**  Outside the mandelbar, `‖Φ c‖` is
bounded by an explicit function of `‖c‖`: the Green function of the critical value is at
most `log (2 (‖c‖ + 1))` (`GreenGrowth.greenSeq_le_log`) and `‖Φ c‖ = exp (2 G_c c)`
(`Work.ParamRays.CP.norm_Phi_eq_exp`).

In particular `Φ` is bounded on every bounded subset of the exterior of the mandelbar; this
is what rules out the second alternative in the boundary argument. -/
lemma norm_Phi_le (h : NakaneInput) {c : ℂ} (hc : c ∉ Mb) :
    ‖Phi c‖ ≤ (2 * (‖c‖ + 1)) ^ 2 := by
  rw [CP.norm_Phi_eq_exp h hc]
  have hle : greenFun c 0 ≤ Real.log (2 * (‖c‖ + 1)) := by
    apply greenFun_le_of_eventually
    filter_upwards with n
    simpa using GreenGrowth.greenSeq_le_log c 0 n
  have h2 : 2 * paramPotential c ≤ 2 * Real.log (2 * (‖c‖ + 1)) := by
    have hp : paramPotential c = greenFun c 0 := rfl
    rw [hp]; linarith
  calc Real.exp (2 * paramPotential c)
      ≤ Real.exp (2 * Real.log (2 * (‖c‖ + 1))) := Real.exp_le_exp.mpr h2
    _ = (2 * (‖c‖ + 1)) ^ 2 := by
        rw [show (2:ℝ) * Real.log (2 * (‖c‖ + 1))
              = ((2:ℕ):ℝ) * Real.log (2 * (‖c‖ + 1)) by norm_num,
          Real.exp_nat_mul, Real.exp_log (by positivity)]

/-- **The modulus of `Φ` tends to `1` at the mandelbar.**  For `c₀` in the mandelbar and
`ε > 0` there is `δ > 0` with `‖Φ c‖ < 1 + ε` for all `c` at distance `< δ` from `c₀`
outside the mandelbar.

Indeed, a sequence of counterexamples `cₙ → c₀` has `‖Φ cₙ‖ ∈ [1 + ε, B]` with
`B = (2 (‖c₀‖ + 2))²` by `norm_Phi_le`; passing to a convergent subsequence `Φ cₙ → w` with
`1 < ‖w‖`, the inverse of Nakane's homeomorphism is continuous at `w` and sends `Φ cₙ`
back to `cₙ`, so `c₀` would lie outside the mandelbar — a contradiction. -/
lemma exists_norm_Phi_lt (h : NakaneInput) {c₀ : ℂ} (hc₀ : c₀ ∈ Mb) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ c : ℂ, dist c c₀ < δ → c ∉ Mb → ‖Phi c‖ < 1 + ε := by
  by_contra hcon
  push Not at hcon
  choose u hu using fun n : ℕ => hcon (1 / (n + 1)) (by positivity)
  have hu_dist : ∀ n, dist (u n) c₀ < 1 / (n + 1) := fun n => (hu n).1
  have hu_notmem : ∀ n, u n ∉ Mb := fun n => (hu n).2.1
  have hu_ge : ∀ n, 1 + ε ≤ ‖Phi (u n)‖ := fun n => (hu n).2.2
  have h0 : Tendsto (fun n : ℕ => (1:ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hd : Tendsto (fun n => dist (u n) c₀) atTop (𝓝 0) :=
    squeeze_zero (fun n => dist_nonneg) (fun n => le_of_lt (hu_dist n)) h0
  have hutend : Tendsto u atTop (𝓝 c₀) :=
    (tendsto_iff_dist_tendsto_zero (f := u) (a := c₀)).mpr hd
  -- the uniform upper bound for the `Φ`-values of the counterexamples
  set B : ℝ := (2 * (‖c₀‖ + 2)) ^ 2 with hBdef
  have hu_bound : ∀ n, ‖Phi (u n)‖ ≤ B := by
    intro n
    have hn : ‖u n‖ ≤ ‖c₀‖ + 1 := by
      have h1 : 1 / (n + 1 : ℝ) ≤ 1 := by
        rw [div_le_one (by positivity)]; exact_mod_cast Nat.le_add_left 1 n
      have h3 : dist (u n) c₀ < 1 := lt_of_lt_of_le (hu_dist n) h1
      have h4 : ‖u n‖ ≤ dist (u n) c₀ + ‖c₀‖ := by
        calc ‖u n‖ = dist (u n) 0 := by rw [dist_zero_right]
          _ ≤ dist (u n) c₀ + dist c₀ 0 := dist_triangle _ _ _
          _ = dist (u n) c₀ + ‖c₀‖ := by rw [dist_zero_right]
      linarith
    calc ‖Phi (u n)‖ ≤ (2 * (‖u n‖ + 1)) ^ 2 := norm_Phi_le h (hu_notmem n)
      _ ≤ B := by
          rw [hBdef]
          apply pow_le_pow_left₀ (by positivity)
          linarith
  -- the `Φ`-values lie in a compact annulus, so a subsequence converges
  let K : Set ℂ := {w : ℂ | 1 + ε ≤ ‖w‖ ∧ ‖w‖ ≤ B}
  have hK : IsCompact K := by
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0:ℂ) B) ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    · intro w hw; rw [Metric.mem_closedBall, dist_zero_right]; exact hw.2
  have hmem : ∀ n, Phi (u n) ∈ K := fun n => ⟨hu_ge n, hu_bound n⟩
  obtain ⟨w, hwK, φ, hφmono, hφlim⟩ := hK.tendsto_subseq hmem
  have hw1 : 1 < ‖w‖ := by linarith [hwK.1, hε]
  -- the inverse of Nakane's homeomorphism
  obtain ⟨e, he⟩ := h.homeo
  let G : ↥{w : ℂ | 1 < ‖w‖} → ℂ := fun w => ((e.symm w : ↥Mbᶜ) : ℂ)
  have hGcont : Continuous G := continuous_subtype_val.comp e.symm.continuous
  have hGPhi : ∀ (c : ℂ) (hc : c ∉ Mb),
      G ⟨Phi c, by rw [← he ⟨c, hc⟩]; exact (e ⟨c, hc⟩).2⟩ = c := by
    intro c hc
    have hsym : e.symm (⟨Phi c, by rw [← he ⟨c, hc⟩]; exact (e ⟨c, hc⟩).2⟩
        : ↥{w : ℂ | 1 < ‖w‖}) = ⟨c, hc⟩ := by
      rw [Homeomorph.symm_apply_eq]
      exact Subtype.ext (he ⟨c, hc⟩).symm
    simp only [G, hsym]
  have hp : ∀ n, 1 < ‖Phi (u (φ n))‖ := fun n => by
    have := hu_ge (φ n); linarith
  have hPhitend : Tendsto (fun n => Phi (u (φ n))) atTop (𝓝 w) := hφlim
  have hsub : Tendsto (fun n => (⟨Phi (u (φ n)), hp n⟩ : ↥{w : ℂ | 1 < ‖w‖})) atTop
      (𝓝 (⟨w, hw1⟩ : ↥{w : ℂ | 1 < ‖w‖})) := tendsto_subtype_rng.mpr hPhitend
  have hcomp : Tendsto (fun n => G ⟨Phi (u (φ n)), hp n⟩) atTop (𝓝 (G ⟨w, hw1⟩)) :=
    hGcont.continuousAt.tendsto.comp hsub
  have hcomp' : Tendsto (fun n => u (φ n)) atTop (𝓝 (G ⟨w, hw1⟩)) :=
    hcomp.congr' (Eventually.of_forall fun n => hGPhi (u (φ n)) (hu_notmem (φ n)))
  have hphi : Tendsto (fun n => u (φ n)) atTop (𝓝 c₀) := hutend.comp hφmono.tendsto_atTop
  have hc0eq : c₀ = G ⟨w, hw1⟩ := tendsto_nhds_unique hphi hcomp'
  have hbad : ((e.symm (⟨w, hw1⟩ : ↥{w : ℂ | 1 < ‖w‖}) : ↥Mbᶜ) : ℂ) ∉ Mb :=
    (e.symm ⟨w, hw1⟩ : ↥Mbᶜ).2
  simp only [G] at hc0eq
  rw [← hc0eq] at hbad
  exact hbad hc₀

/-- **Continuity of `log ‖Φ ·‖` on the exterior of the mandelbar.**  There `Φ` agrees with
Nakane's homeomorphism `e : Mbᶜ ≃ₜ {w | 1 < ‖w‖}`, and `log ‖·‖` is continuous (and nowhere
zero) on the exterior disc. -/
lemma continuousOn_log_Phi (h : NakaneInput) :
    ContinuousOn (fun c : ℂ => Real.log ‖Phi c‖) Mbᶜ := by
  obtain ⟨e, he⟩ := h.homeo
  rw [continuousOn_iff_continuous_domRestrict]
  have hfun : Mbᶜ.domRestrict (fun c : ℂ => Real.log ‖Phi c‖) =
      (fun w : ↥{w : ℂ | 1 < ‖w‖} => Real.log ‖(w : ℂ)‖) ∘ e := by
    funext c
    simp only [Set.domRestrict, Function.comp_apply]
    rw [he c]
  rw [hfun]
  refine Continuous.log ?_ ?_
  · exact continuous_subtype_val.norm.comp e.continuous
  · intro w
    exact ne_of_gt (lt_trans zero_lt_one (e w).2)

/-- **The potential is continuous on `ℂ`.**  It vanishes on the interior of the mandelbar and
equals `log ‖Φ c‖` outside it; only the boundary `∂Mb` needs an argument.  For `cₙ ∉ Mb` with
`cₙ → c₀ ∈ Mb` one shows `‖Φ cₙ‖ → 1`: if `‖Φ cₙₖ‖` stays bounded, pass to
`Φ cₙₖ → w` with `‖w‖ = r > 1`, and `cₙₖ = e⁻¹ (Φ cₙₖ) → e⁻¹ w ∈ Mbᶜ`, contradicting
`cₙₖ → c₀ ∈ Mb`; while if `‖Φ cₙₖ‖ → ∞` then `Φ c / c → 1` at infinity forces
`‖cₙₖ‖ → ∞`, again contradicting convergence to a finite point.
(`Work.ParamRays.Phi_isBigO_atTop` is available for the second case.) -/
theorem continuous_potential (h : Work.ParamRays.NakaneInput) :
    Continuous Work.ParamRays.potential := by
  -- off the mandelbar `potential` is `log ‖Φ ·‖`, and on it both sides vanish
  have hfun : potential = fun c : ℂ => Real.log ‖Phi c‖ := by
    funext c
    rcases Classical.em (c ∈ Mb) with hc | hc
    · rw [potential_eq_zero_of_mem hc, Phi_eq_zero_of_mem hc, norm_zero, Real.log_zero]
    · rw [potential, dite_eq_right hc]
  rw [hfun]
  have h1 : ContinuousOn (fun c : ℂ => Real.log ‖Phi c‖) Mbᶜ := continuousOn_log_Phi h
  -- the potential tends to `0` at every point of the mandelbar
  have h2 : ∀ c ∈ Mb, ContinuousAt (fun c : ℂ => Real.log ‖Phi c‖) c := by
    intro c₀ hc₀
    rw [Metric.continuousAt_iff]
    intro ε hε
    have hε' : 0 < Real.exp ε - 1 := by
      have : 1 < Real.exp ε := Real.one_lt_exp_iff.mpr hε
      linarith
    obtain ⟨δ, hδpos, hδ⟩ := exists_norm_Phi_lt h hc₀ hε'
    refine ⟨δ, hδpos, fun c hc => ?_⟩
    have hc0 : Real.log ‖Phi c₀‖ = 0 := by
      rw [Phi_eq_zero_of_mem hc₀, norm_zero, Real.log_zero]
    rw [hc0]
    rcases Classical.em (c ∈ Mb) with hcm | hcm
    · rw [Phi_eq_zero_of_mem hcm, norm_zero, Real.log_zero, dist_self]
      exact hε
    · have hlt : ‖Phi c‖ < Real.exp ε := by
        have h5 := hδ c hc hcm
        linarith
      have hpos : 0 < ‖Phi c‖ := lt_trans zero_lt_one (CP.one_lt_norm_Phi h hcm)
      have hlog : Real.log ‖Phi c‖ < ε := by
        rw [← Real.log_exp ε]
        exact Real.log_lt_log hpos hlt
      have hnonneg : 0 ≤ Real.log ‖Phi c‖ :=
        Real.log_nonneg (le_of_lt (CP.one_lt_norm_Phi h hcm))
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
      exact hlog
  -- paste the exterior part and the boundary values
  have h3 : ContinuousOn (fun c : ℂ => Real.log ‖Phi c‖) (Mbᶜ ∪ Mb) :=
    h1.union_continuousAt isClosed_mandelbar.isOpen_compl h2
  rwa [Set.compl_union_self, continuousOn_univ] at h3

end Work.ParamRays

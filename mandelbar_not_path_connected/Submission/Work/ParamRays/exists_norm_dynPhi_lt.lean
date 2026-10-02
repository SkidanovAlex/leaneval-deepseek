import Mathlib
import Submission.Work.ParamRays.DynBottcher
import Submission.Work.ParamRays.IsDynBottcher_modulus
import Submission.Work.ParamRays.greenFun_pos_of_lt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ParamRays

open Filter
open scoped Real Topology ComplexConjugate

/-! ## An a priori bound for the dynamical Böttcher coordinate

Outside the filled Julia set the modulus of `dynPhi c` is controlled by `‖z‖`: the Green
function is at most `log (2 (‖z‖ + ‖c‖ + 1))` (`GreenGrowth.greenSeq_le_log`) and
`‖dynPhiOf c z‖ = exp (greenFun c z)` (`IsDynBottcher_modulus`).  This is what rules out
the second alternative in the boundary argument below. -/

/-- **A priori bound for the dynamical Böttcher coordinate.**  Outside the filled Julia set,
`‖dynPhi c z‖` is bounded by an explicit function of `‖z‖`. -/
lemma norm_dynPhi_le {c : ℂ} (h : DynBottcherHomeo c) {z : ℂ} (hz : z ∉ filledJulia c) :
    ‖dynPhi c z‖ ≤ (2 * (‖z‖ + ‖c‖ + 1)) ^ 2 := by
  have hesc : Escaping c z := (escaping_iff_not_bounded c z).mpr hz
  rw [dynPhi_of_not_mem hz,
    IsDynBottcher_modulus (isDynBottcher_dynPhiOf h.exists) hesc]
  have hle : greenFun c z ≤ Real.log (2 * (‖z‖ + (‖c‖ + 1))) := by
    apply greenFun_le_of_eventually
    filter_upwards with n
    simpa using GreenGrowth.greenSeq_le_log c z n
  have hX : 0 < 2 * (‖z‖ + (‖c‖ + 1)) := by positivity
  calc Real.exp (greenFun c z)
      ≤ Real.exp (Real.log (2 * (‖z‖ + (‖c‖ + 1)))) := Real.exp_le_exp.mpr hle
    _ = 2 * (‖z‖ + ‖c‖ + 1) := by rw [Real.exp_log hX]; ring
    _ ≤ (2 * (‖z‖ + ‖c‖ + 1)) ^ 2 := by
        have h1 : (1 : ℝ) ≤ 2 * (‖z‖ + ‖c‖ + 1) := by
          have hz0 := norm_nonneg z
          have hc0 := norm_nonneg c
          linarith
        calc 2 * (‖z‖ + ‖c‖ + 1) = (2 * (‖z‖ + ‖c‖ + 1)) ^ 1 := by ring
          _ ≤ (2 * (‖z‖ + ‖c‖ + 1)) ^ 2 := pow_le_pow_right₀ h1 (by norm_num)

/-- **The modulus of the dynamical Böttcher coordinate tends to `1` at the filled Julia set.**

For `z₀` in the filled Julia set of `T_c` and `ε > 0` there is `δ > 0` such that
`‖dynPhi c z‖ < 1 + ε` for every `z` with `dist z z₀ < δ` that is outside the filled Julia set.

Route (a verbatim adaptation of `Work.ParamRays.exists_norm_Phi_lt` in
`Submission/Work/ParamRays/continuous_potential.lean`, with `Mb ↦ filledJulia c`,
`Phi ↦ dynPhi c`, `NakaneInput.homeo ↦ DynBottcherHomeo.homeo`):

* the a priori bound `‖dynPhi c z‖ ≤ (2 * (‖z‖ + ‖c‖ + 1)) ^ 2` for `z ∉ filledJulia c`,
  obtained from `dynPhi_of_not_mem`, `compl_filledJulia`, `IsDynBottcher_modulus`
  (`‖dynPhiOf c z‖ = exp (greenFun c z)`) and `greenFun_le_of_eventually` together with
  `GreenGrowth.greenSeq_le_log`;
* a sequence of counterexamples `u n` with `dist (u n) z₀ < 1/(n+1)`, `u n ∉ filledJulia c` and
  `1 + ε ≤ ‖dynPhi c (u n)‖` satisfies `u n → z₀` and `‖dynPhi c (u n)‖ ∈ [1+ε, B]` with
  `B = (2 * (‖z₀‖ + ‖c‖ + 2)) ^ 2`; a convergent subsequence `dynPhi c (u (φ n)) → w` with
  `1 < ‖w‖` then gives, through the inverse homeomorphism `e.symm` of `DynBottcherHomeo.homeo`,
  `u (φ n) → e.symm w ∉ filledJulia c`, contradicting `u (φ n) → z₀ ∈ filledJulia c`. -/
theorem exists_norm_dynPhi_lt {c : ℂ} (h : Work.ParamRays.DynBottcherHomeo c) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Work.ParamRays.filledJulia c) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z : ℂ, dist z z₀ < δ → z ∉ Work.ParamRays.filledJulia c →
      ‖Work.ParamRays.dynPhi c z‖ < 1 + ε := by
  by_contra hcon
  push Not at hcon
  choose u hu using fun n : ℕ => hcon (1 / (n + 1)) (by positivity)
  have hu_dist : ∀ n, dist (u n) z₀ < 1 / (n + 1) := fun n => (hu n).1
  have hu_notmem : ∀ n, u n ∉ filledJulia c := fun n => (hu n).2.1
  have hu_ge : ∀ n, 1 + ε ≤ ‖dynPhi c (u n)‖ := fun n => (hu n).2.2
  have h0 : Tendsto (fun n : ℕ => (1:ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hd : Tendsto (fun n => dist (u n) z₀) atTop (𝓝 0) :=
    squeeze_zero (fun n => dist_nonneg) (fun n => le_of_lt (hu_dist n)) h0
  have hutend : Tendsto u atTop (𝓝 z₀) :=
    (tendsto_iff_dist_tendsto_zero (f := u) (a := z₀)).mpr hd
  -- the uniform upper bound for the `dynPhi`-values of the counterexamples
  set B : ℝ := (2 * (‖z₀‖ + ‖c‖ + 2)) ^ 2 with hBdef
  have hu_bound : ∀ n, ‖dynPhi c (u n)‖ ≤ B := by
    intro n
    have hn : ‖u n‖ ≤ ‖z₀‖ + 1 := by
      have h1 : 1 / (n + 1 : ℝ) ≤ 1 := by
        rw [div_le_one (by positivity)]; exact_mod_cast Nat.le_add_left 1 n
      have h3 : dist (u n) z₀ < 1 := lt_of_lt_of_le (hu_dist n) h1
      have h4 : ‖u n‖ ≤ dist (u n) z₀ + ‖z₀‖ := by
        calc ‖u n‖ = dist (u n) 0 := by rw [dist_zero_right]
          _ ≤ dist (u n) z₀ + dist z₀ 0 := dist_triangle _ _ _
          _ = dist (u n) z₀ + ‖z₀‖ := by rw [dist_zero_right]
      linarith
    calc ‖dynPhi c (u n)‖ ≤ (2 * (‖u n‖ + ‖c‖ + 1)) ^ 2 := norm_dynPhi_le h (hu_notmem n)
      _ ≤ B := by
          rw [hBdef]
          apply pow_le_pow_left₀ (by positivity)
          linarith
  -- the `dynPhi`-values lie in a compact annulus, so a subsequence converges
  let K : Set ℂ := {w : ℂ | 1 + ε ≤ ‖w‖ ∧ ‖w‖ ≤ B}
  have hK : IsCompact K := by
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0:ℂ) B) ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    · intro w hw; rw [Metric.mem_closedBall, dist_zero_right]; exact hw.2
  have hmem : ∀ n, dynPhi c (u n) ∈ K := fun n => ⟨hu_ge n, hu_bound n⟩
  obtain ⟨w, hwK, φ, hφmono, hφlim⟩ := hK.tendsto_subseq hmem
  have hw1 : 1 < ‖w‖ := by linarith [hwK.1, hε]
  -- the inverse of the Böttcher homeomorphism
  obtain ⟨e, he⟩ := h.homeo
  let G : ↥(Work.Top.exteriorDisc) → ℂ := fun w => ((e.symm w : ↥(filledJulia c)ᶜ) : ℂ)
  have hGcont : Continuous G := continuous_subtype_val.comp e.symm.continuous
  have hmemE : ∀ (z : ℂ) (hz : z ∉ filledJulia c),
      dynPhi c z ∈ Work.Top.exteriorDisc := by
    intro z hz
    have hsub : dynPhi c z = ((e ⟨z, hz⟩ : ↥(Work.Top.exteriorDisc)) : ℂ) := by
      simpa using he ⟨z, hz⟩
    rw [hsub]
    exact (e ⟨z, hz⟩).2
  have hGPhi : ∀ (z : ℂ) (hz : z ∉ filledJulia c),
      G ⟨dynPhi c z, hmemE z hz⟩ = z := by
    intro z hz
    have hsym : e.symm (⟨dynPhi c z, hmemE z hz⟩ : ↥(Work.Top.exteriorDisc)) = ⟨z, hz⟩ := by
      rw [Homeomorph.symm_apply_eq]
      exact Subtype.ext (by simpa using he ⟨z, hz⟩)
    simp only [G, hsym, Subtype.coe_mk]
  have hp : ∀ n, 1 < ‖dynPhi c (u (φ n))‖ := fun n => by
    have := hu_ge (φ n); linarith
  have hPhitend : Tendsto (fun n => dynPhi c (u (φ n))) atTop (𝓝 w) := hφlim
  have hsub : Tendsto (fun n => (⟨dynPhi c (u (φ n)), hp n⟩ : ↥{w : ℂ | 1 < ‖w‖})) atTop
      (𝓝 (⟨w, hw1⟩ : ↥{w : ℂ | 1 < ‖w‖})) := tendsto_subtype_rng.mpr hPhitend
  have hcomp : Tendsto (fun n => G ⟨dynPhi c (u (φ n)), hp n⟩) atTop (𝓝 (G ⟨w, hw1⟩)) :=
    hGcont.continuousAt.tendsto.comp hsub
  have hcomp' : Tendsto (fun n => u (φ n)) atTop (𝓝 (G ⟨w, hw1⟩)) :=
    hcomp.congr' (Eventually.of_forall fun n => hGPhi (u (φ n)) (hu_notmem (φ n)))
  have hphi : Tendsto (fun n => u (φ n)) atTop (𝓝 z₀) := hutend.comp hφmono.tendsto_atTop
  have hz0eq : z₀ = G ⟨w, hw1⟩ := tendsto_nhds_unique hphi hcomp'
  have hbad : ((e.symm (⟨w, hw1⟩ : ↥(Work.Top.exteriorDisc)) : ↥(filledJulia c)ᶜ) : ℂ)
      ∉ filledJulia c := (e.symm ⟨w, hw1⟩ : ↥(filledJulia c)ᶜ).2
  simp only [G] at hz0eq
  rw [← hz0eq] at hbad
  exact hbad hz₀

end Work.ParamRays

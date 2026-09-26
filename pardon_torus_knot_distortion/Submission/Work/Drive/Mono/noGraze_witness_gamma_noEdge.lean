import Mathlib
import Submission.Work.Drive.Mono.noGraze_witness_robust
import Submission.Work.Drive.Mono.gammaArcs_exist
import Submission.Work.Drive.Mono.BoxGenE
import Submission.Work.Drive.Mono.arcHeightKernel

/-!
# The no-grazing witness, with the clauses on the box-trace arcs

This file proves `Work.Drive.Mono.noGraze_witness_gamma_noEdge`, the version of the no-grazing
witness whose last clause controls the derivative of an arbitrary `C³` family of box-trace arcs
parametrised by height near the cutting plane (with `Set.Ioo` in place of `Set.Icc`, so that the
junk value of `deriv` at the endpoints plays no role).

The proof copies `Work.Drive.Mono.noGraze_witness_robust` (the same caps `X1 … X12`, the same
construction of `n₀`, `ng`, `n`, `v`, `τ`, `h`, `ρ`) with three changes:

* the avoidance direction `Ñ₀` avoids, besides the vertical velocities of the knot at the crossings,
  also the finitely many horizontal velocities `γ'(0) - e_{σ 2}` of the box-trace arcs
  (`Work.Drive.Mono.exists_unitOrthAvoid_both`);
* six new caps (`Y1 … Y7` collected in `Yc`) force `τ`, and hence `h`, to be small relative to the
  intrinsic data of the arcs supplied by `Work.Drive.Mono.arcHeightKernel`;
* the robustness radius `ρ` gains a third branch `τ / (144 * (arcM + 2))`, which makes the
  perturbation of `n` harmless compared with the tilt `inner ℝ n e`.

The final clause then follows from `arcHeightKernel`: the arcs' horizontal velocity is
`φ'(t) • e_{σ j}` with `φ'(0)` one of the finitely many avoided values; at a non-vertical crossing
the margin is `cA / 8`, at a vertical one (`FaceNoBend`) the quadratic bound `arcQ * t ^ 2` leaves
the tilt `inner ℝ n e ≥ η / 3` intact.
-/

set_option maxHeartbeats 1000000

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal _root_.Topology RealInnerProductSpace
open Work.Drive.Mono.Band

noncomputable section

private lemma mg_mul_le_of_le_div {a b c : ℝ} (hb : 0 < b) (h : a ≤ c / b) : a * b ≤ c := by
  rwa [le_div_iff₀ hb] at h

/-- The reverse triangle inequality in the form needed below. -/
private lemma mg_le_abs_add (a b : ℝ) : |a| - |b| ≤ |a + b| := by
  have h := abs_sub_abs_le_abs_sub a (-b)
  simpa [abs_neg, sub_neg_eq_add] using h

/-- For a unit vector `n`, the absolute value of `⟪n, w⟫` is at most `‖w‖`. -/
private lemma mg_abs_inner_unit_le {n w : R3} (hn : ‖n‖ = 1) : |inner ℝ n w| ≤ ‖w‖ := by
  have h := abs_real_inner_le_norm n w
  rwa [hn, one_mul] at h

/-- From `a ≤ c / b / 4` with `b > 0` conclude `a * (4 * b) ≤ c`. -/
private lemma mg_mul_le_of_le_quarter {a b c : ℝ} (hb : 0 < b) (h : a ≤ c / b / 4) :
    a * (4 * b) ≤ c := by
  rw [le_div_iff₀ (show (0 : ℝ) < 4 by norm_num)] at h
  rw [le_div_iff₀ hb] at h
  nlinarith only [h]

/-- `|a| - |b| - |c| ≤ |a + b + c|`. -/
private lemma mg_abs_add_three (a b c : ℝ) : |a| - |b| - |c| ≤ |a + b + c| := by
  have h1 : |a + b| - |c| ≤ |a + b + c| := mg_le_abs_add (a + b) c
  have h2 : |a| - |b| ≤ |a + b| := mg_le_abs_add a b
  linarith only [h1, h2]

/-- From `a ≤ c / b` with `b > 0` conclude `a * b ≤ c`. -/

theorem exists_unitOrthAvoid_both (K : Knot) (e e₂ : R3) (he : ‖e‖ = 1)
    (he₂ : ‖e₂‖ = 1) (horth : inner ℝ e₂ e = 0) {c : R3} {σ : Equiv.Perm (Fin 3)} {s u : ℝ}
    (hcut : Work.Drive.Mono.CutTransverse K s c σ u) (D : Finset R3)
    (hDperp : ∀ d ∈ D, inner ℝ e d = 0) :
    ∃ Ñ : R3, ‖Ñ‖ = 1 ∧ inner ℝ Ñ e = 0 ∧
      (∀ t ∈ Work.Drive.Mono.crossingSet K c σ s u hcut, Work.Drive.Mono.vertVel K e t ≠ 0 →
        inner ℝ Ñ (Work.Drive.Mono.vertVel K e t) ≠ 0) ∧
      (∀ d ∈ D, d ≠ 0 → inner ℝ Ñ d ≠ 0) := by
  classical
  set F' : Finset R3 := ((Work.Drive.Mono.crossingSet K c σ s u hcut).filter
      (fun t => Work.Drive.Mono.vertVel K e t ≠ 0)).image
      (fun t => Work.Drive.Mono.vertVel K e t) ∪ D.filter (fun d => d ≠ 0) with hF'
  have hF'ne : ∀ w ∈ F', w ≠ 0 := by
    intro w hw
    rw [hF'] at hw
    rcases Finset.mem_union.mp hw with h | h
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp ht).2
    · exact (Finset.mem_filter.mp h).2
  have hF'orth : ∀ w ∈ F', inner ℝ e w = 0 := by
    intro w hw
    rw [hF'] at hw
    rcases Finset.mem_union.mp hw with h | h
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
      exact Work.Drive.Mono.inner_e_vertVel K e he t
    · exact hDperp w (Finset.mem_of_mem_filter w h)
  by_cases hF'empty : F' = ∅
  · refine ⟨e₂, he₂, horth, ?_, ?_⟩
    · intro t ht hv
      exfalso
      have : Work.Drive.Mono.vertVel K e t ∈ F' := by
        rw [hF']
        exact Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, hv⟩, rfl⟩)
      rw [hF'empty] at this
      simpa using this
    · intro d hd hd0
      exfalso
      have : d ∈ F' := by
        rw [hF']
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hd, hd0⟩)
      rw [hF'empty] at this
      simpa using this
  · have hF'nonempty : F'.Nonempty := Finset.nonempty_iff_ne_empty.mpr hF'empty
    set P : R3 → Submodule ℝ R3 := fun w => LinearMap.ker ((innerSL ℝ w : R3 →ₗ[ℝ] ℝ)) with hP
    have hne : ∀ w : {w // w ∈ F'}, P w.1 ≠ ⊤ := by
      rintro ⟨w, hw⟩ htop
      have hw0 : w ≠ 0 := hF'ne w hw
      have hmem : w ∈ P w := by rw [htop]; trivial
      rw [hP, LinearMap.mem_ker] at hmem
      have hval : ((innerSL ℝ w : R3 →ₗ[ℝ] ℝ)) w = inner ℝ w w := rfl
      rw [hval, real_inner_self_eq_norm_sq] at hmem
      exact hw0 (norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hmem))
    have hsub := Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt (K := ℝ) (M := R3)
      F'.attach (fun w : {w // w ∈ F'} => P w.1) hne
      (by rw [ENat.card_eq_top_of_infinite (α := ℝ)]; exact ENat.natCast_lt_top _)
    obtain ⟨x, hx⟩ : ∃ x : R3, x ∉ ⋃ i ∈ F'.attach, (P i.1 : Set R3) := by
      by_contra hcon
      push Not at hcon
      exact (Set.ssubset_univ_iff.mp hsub) (Set.eq_univ_of_forall hcon)
    have hxavoid : ∀ w ∈ F', inner ℝ x w ≠ 0 := by
      intro w hw hzero
      have hnotmem : x ∉ P w := fun hcon =>
        hx (Set.mem_iUnion.mpr ⟨⟨w, hw⟩,
          Set.mem_iUnion.mpr ⟨Finset.mem_attach _ _, hcon⟩⟩)
      apply hnotmem
      simp only [hP]
      rw [LinearMap.mem_ker]
      rw [show ((innerSL ℝ w : R3 →ₗ[ℝ] ℝ)) x = inner ℝ w x from rfl, real_inner_comm, hzero]
    set x' : R3 := x - inner ℝ x e • e with hx'
    have hx'avoid : ∀ w ∈ F', inner ℝ x' w ≠ 0 := by
      intro w hw
      have hwperp : inner ℝ e w = 0 := hF'orth w hw
      have hval : inner ℝ x' w = inner ℝ x w := by
        rw [hx', inner_sub_left, real_inner_smul_left, hwperp, mul_zero, sub_zero]
      rw [hval]
      exact hxavoid w hw
    have hx'ne : x' ≠ 0 := by
      intro h0
      obtain ⟨w, hw⟩ := hF'nonempty
      have := hx'avoid w hw
      rw [h0, inner_zero_left] at this
      exact this rfl
    have hx'orth : inner ℝ x' e = 0 := by
      rw [hx', inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he, one_pow,
        mul_one, sub_self]
    refine ⟨unitDir x', unitDir_norm x' hx'ne, ?_, ?_, ?_⟩
    · rw [inner_unitDir, hx'orth, mul_zero]
    · intro t ht hv
      have hmem : Work.Drive.Mono.vertVel K e t ∈ F' := by
        rw [hF']
        exact Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, hv⟩, rfl⟩)
      rw [inner_unitDir]
      exact mul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hx'ne)) (hx'avoid _ hmem)
    · intro d hd hd0
      have hmem : d ∈ F' := by
        rw [hF']
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hd, hd0⟩)
      rw [inner_unitDir]
      exact mul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hx'ne)) (hx'avoid _ hmem)

theorem noGraze_witness_arcs_noEdge
    (ψ : Submission.Diffeo) (K : LeanEval.KnotTheory.PardonDistortion.Knot) {r s u : ℝ}
    (hr : 0 < r) (hrs : r < s) (hu : |u| < Submission.eps * r)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3))
    (hcut : Work.Drive.Mono.CutTransverse K s c σ u)
    {εg δg θ' : ℝ} (hεg : 0 < εg) (hδg : 0 < δg) (hθ' : 0 < θ')
    (hnograz : ∀ v : LeanEval.KnotTheory.PardonDistortion.R3, ‖v‖ = 1 →
        ‖v - Work.BoxShrink.shiftVσ σ 1‖ < εg →
        ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
          deriv (fun r : ℝ => inner ℝ v (K.curve r)) t = 0 →
          δg ≤ |inner ℝ v (K.curve t) - (inner ℝ v c + u)|)
    (hnobend : ∀ t : ℝ, K.curve t ∈ closure (Submission.PBox s c σ) →
        (K.curve t) (σ 2) = c (σ 2) + u →
        Work.Drive.Mono.vertVel K (Work.BoxShrink.shiftVσ σ 1) t = 0 →
        Work.Drive.Mono.vertAcc K (Work.BoxShrink.shiftVσ σ 1) t = 0)
    (hX : Work.Drive.Mono.FaceCrossReg ψ c σ s u)
    (hFB : Work.Drive.Mono.FaceNoBend ψ c σ s u)
    (hedge : ∃ mE : ℝ, 0 < mE ∧ ∀ z : LeanEval.KnotTheory.PardonDistortion.R3,
        z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
        |z (σ 0) - c (σ 0)| = Submission.boxSide 0 * s →
        |z (σ 1) - c (σ 1)| = Submission.boxSide 1 * s →
        mE ≤ |z (σ 2) - (c (σ 2) + u)|)
    (D : Finset LeanEval.KnotTheory.PardonDistortion.R3) (arcE arcM arcL arcQ : ℝ)
    (hDperp : ∀ d ∈ D, inner ℝ (Work.BoxShrink.shiftVσ σ 1) d = 0)
    (harcE : 0 < arcE) (harcM : 0 < arcM) (harcL : 0 < arcL) (harcQ : 0 < arcQ)
    (harc : ∀ (γ : ℝ → LeanEval.KnotTheory.PardonDistortion.R3) (η : ℝ) (i : Fin 3) (ev : ℝ)
        (β : ℝ → ℝ × ℝ),
        0 < η → i ≠ 2 → (ev = 1 ∨ ev = -1) →
        ContDiffOn ℝ 3 γ (Set.Icc (-η) η) →
        (∀ t ∈ Set.Icc (-η) η, (γ t) (σ 2) = c (σ 2) + u + t) →
        ContDiffOn ℝ 3 β (Set.Icc (-η) η) →
        (∀ t ∈ Set.Icc (-η) η, Work.BoxShrink.Pinch.par ψ (β t) = γ t ∧
          (γ t) (σ i) = c (σ i) + ev * Submission.boxSide i * s) →
        (∃ d ∈ D, deriv γ 0 - Work.BoxShrink.shiftVσ σ 1 = d) ∧
        (∀ t : ℝ, t ∈ Set.Ioo (-η) η → |t| ≤ arcE →
          ‖deriv γ t‖ ≤ arcM ∧ ‖deriv γ t - deriv γ 0‖ ≤ arcL * |t| ∧
          (deriv γ 0 = Work.BoxShrink.shiftVσ σ 1 →
            ‖deriv γ t - deriv γ 0‖ ≤ arcQ * t ^ 2))) :
    ∃ (v n : LeanEval.KnotTheory.PardonDistortion.R3) (h ρ : ℝ),
      ‖v‖ = 1 ∧ ‖n‖ = 1 ∧ inner ℝ v n = 0 ∧ Work.Drive.Mono.Band.HeightGood ψ n ∧
      ‖v - Work.BoxShrink.shiftVσ σ 1‖ ≤ θ' ∧
      ‖v - Work.BoxShrink.shiftVσ σ 1‖ ≤ εg / 4 ∧
      0 < h ∧ 0 < ρ ∧
      2 * (‖v - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s)) < h ∧
      (∀ t : ℝ, Submission.boxNorm c σ (K.curve t) = s →
          h ≤ |inner ℝ v (K.curve t) - (inner ℝ v c + u)|) ∧
      (∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
          deriv (fun r : ℝ => inner ℝ v (K.curve r)) t = 0 →
          h ≤ |inner ℝ v (K.curve t) - (inner ℝ v c + u)|) ∧
      (∀ nn : LeanEval.KnotTheory.PardonDistortion.R3, ‖nn‖ = 1 → ‖nn - n‖ < ρ → ∀ t : ℝ,
          K.curve t ∈ Submission.PBox s c σ →
          |inner ℝ v (K.curve t) - (inner ℝ v c + u)| ≤ h →
          deriv (fun r : ℝ => inner ℝ nn (K.curve r)) t ≠ 0) ∧
      (∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
          |inner ℝ v (K.curve t) - (inner ℝ v c + u)| = h →
          deriv (fun r : ℝ => inner ℝ v (K.curve r)) t ≠ 0) ∧
      (∀ (N : ℕ) (γ : Fin N → ℝ → LeanEval.KnotTheory.PardonDistortion.R3) (η m : ℝ),
        0 < η → 0 < m →
        (∀ k, ContDiffOn ℝ 3 (γ k) (Set.Icc (-η) η)) →
        (∀ k, ∀ t ∈ Set.Icc (-η) η, (γ k t) (σ 2) = c (σ 2) + u + t) →
        (∀ k, ∃ i : Fin 3, i ≠ 2 ∧ ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∃ β : ℝ → ℝ × ℝ,
          ContDiffOn ℝ 3 β (Set.Icc (-η) η) ∧ ∀ t ∈ Set.Icc (-η) η,
            Work.BoxShrink.Pinch.par ψ (β t) = γ k t ∧
            (γ k t) (σ i) = c (σ i) + ε * Submission.boxSide i * s) →
        (∀ z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier, Submission.boxNorm c σ z = s →
          |z (σ 2) - (c (σ 2) + u)| < m → (∀ j : Fin 3, j ≠ 2 → ∀ j' : Fin 3, j' ≠ 2 → j ≠ j' →
            ¬ (|z (σ j) - c (σ j)| = Submission.boxSide j * s ∧
               |z (σ j') - c (σ j')| = Submission.boxSide j' * s)) →
          ∃ k, ∃ t ∈ Set.Ioo (-η) η, z = γ k t) →
        (∀ k, ∀ t : ℝ, t ∈ Set.Ioo (-η) η → |t| ≤ 2 * h → ∀ nn : LeanEval.KnotTheory.PardonDistortion.R3,
          ‖nn‖ = 1 → ‖nn - n‖ < ρ → inner ℝ nn (deriv (γ k) t) ≠ 0) ∧
        (∀ k, ∀ t : ℝ, t ∈ Set.Ioo (-η) η → |t| ≤ 2 * h →
          (1 / 2 : ℝ) ≤ inner ℝ v (deriv (γ k) t))) := by
  classical
  -- ## 0. Basic data
  have hs : 0 < s := lt_trans hr hrs
  have hs0 : 0 ≤ s := le_of_lt hs
  set e : R3 := Work.BoxShrink.shiftVσ σ 1 with hedef
  have he1 : ‖e‖ = 1 := by rw [hedef]; exact norm_shiftVσ_one σ
  obtain ⟨lam, m, ρc, hlam0, hm0, hρc0, hlam, hmargin, hcover⟩ := noGraze_cover K c σ hcut
  obtain ⟨M1, hM10, hM1⟩ := exists_bound_deriv_curve K
  obtain ⟨M2, hM20, hM2⟩ := exists_bound_deriv2_curve K
  obtain ⟨Cv, dv, hCv0, hdv0, hCv⟩ := exists_uniform_sq_bound_vertVel K e he1
  obtain ⟨R2, hR20, hR2⟩ := exists_bound_boxNorm_eq s c σ
  obtain ⟨mbox, hmbox0, hmbox⟩ := exists_margin_boxSphere K c σ hs hcut
  set R1 : ℝ := 5 / 2 * s with hR1def
  have hR1b : ∀ y ∈ Submission.PBox s c σ, ‖y - c‖ ≤ R1 := by
    intro y hy
    rw [hR1def]
    exact norm_sub_le_of_mem_PBox hs0 hy
  -- a unit vector orthogonal to `e`
  set e₂ : R3 := unitCoord σ 0 with he₂def
  have he₂1 : ‖e₂‖ = 1 := by rw [he₂def]; exact norm_unitCoord σ 0
  have he₂orth : inner ℝ e₂ e = 0 := by
    rw [hedef, he₂def, inner_unitCoord, Work.BoxShrink.shiftVσ_apply]
    have h : σ 0 ≠ σ 2 := fun hc => absurd (σ.injective hc) (by decide)
    simp [h]
  -- ## 1. the crossing set and the avoidance direction
  obtain ⟨Ñ₀, hÑ₀1, hÑ₀orth, hÑ₀avoid, hFD⟩ := exists_unitOrthAvoid_both K e e₂ he1 he₂1 he₂orth hcut D hDperp
  have hÑ₀orth' : inner ℝ e Ñ₀ = 0 := by rw [real_inner_comm, hÑ₀orth]
  have hc00 : ∃ c00 : ℝ, 0 < c00 ∧ ∀ t ∈ crossingSet K c σ s u hcut,
      vertVel K e t ≠ 0 → c00 ≤ |inner ℝ Ñ₀ (vertVel K e t)| := by
    classical
    by_cases hne : (crossingSet K c σ s u hcut).filter (fun t => vertVel K e t ≠ 0) |>.Nonempty
    · obtain ⟨t₁, ht₁, hmin⟩ := Finset.exists_min_image
        ((crossingSet K c σ s u hcut).filter (fun t => vertVel K e t ≠ 0))
        (fun t => |inner ℝ Ñ₀ (vertVel K e t)|) hne
      refine ⟨|inner ℝ Ñ₀ (vertVel K e t₁)|, ?_, ?_⟩
      · rcases Finset.mem_filter.mp ht₁ with ⟨htT, hvn⟩
        exact abs_pos.mpr (hÑ₀avoid t₁ htT hvn)
      · intro t htT hvn
        exact hmin t (Finset.mem_filter.mpr ⟨htT, hvn⟩)
    · refine ⟨1, one_pos, ?_⟩
      intro t htT hvn
      exact absurd ⟨t, Finset.mem_filter.mpr ⟨htT, hvn⟩⟩ hne
  obtain ⟨c00, hc000, hc00le⟩ := hc00
  -- ## 1b. the arc directions
  set cA : ℝ := if h : (D.filter (fun d => d ≠ 0)).Nonempty then
      (D.filter (fun d => d ≠ 0)).inf' h (fun d => |inner ℝ Ñ₀ d|) else 1 with hcA
  have hcApos : 0 < cA := by
    rw [hcA]
    by_cases h : (D.filter (fun d => d ≠ 0)).Nonempty
    · rw [dif_pos h]
      exact (Finset.lt_inf'_iff h).mpr fun d hd =>
        abs_pos.mpr (hFD d (Finset.mem_of_mem_filter d hd) (Finset.mem_filter.mp hd).2)
    · rw [dif_neg h]; norm_num
  have hcAle : ∀ d ∈ D, d ≠ 0 → cA ≤ |inner ℝ Ñ₀ d| := by
    intro d hd hd0
    have hmem : d ∈ D.filter (fun d => d ≠ 0) := Finset.mem_filter.mpr ⟨hd, hd0⟩
    have h : (D.filter (fun d => d ≠ 0)).Nonempty := ⟨d, hmem⟩
    rw [hcA, dif_pos h]
    exact Finset.inf'_le _ hmem
  set Md : ℝ := if h : D.Nonempty then max 1 (D.sup' h (fun d => ‖d‖)) else 1 with hMd
  have hMdpos : 0 < Md := by
    rw [hMd]
    by_cases h : D.Nonempty
    · rw [dif_pos h]; exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    · rw [dif_neg h]; norm_num
  have hMdge : ∀ d ∈ D, ‖d‖ ≤ Md := by
    intro d hd
    have h : D.Nonempty := ⟨d, hd⟩
    rw [hMd, dif_pos h]
    exact le_trans (Finset.le_sup' _ hd) (le_max_right _ _)
  -- the new smallness parameters
  set Y1 : ℝ := cA / 96 with hY1def
  set Y2 : ℝ := arcE / (96 * s) with hY2def
  set Y3 : ℝ := 1 / (8 * (arcM + 2)) with hY3def
  set Y4 : ℝ := cA / (96 * s * arcL) with hY4def
  set Y5 : ℝ := cA / (96 * Md) with hY5def
  set Y6 : ℝ := cA / (96 * arcM) with hY6def
  set Y7 : ℝ := 1 / (64800 * s ^ 2 * arcQ) with hY7def
  set Yc : ℝ := min Y1 (min Y2 (min Y3 (min Y4 (min Y5 (min Y6 Y7))))) with hYcdef
  have hYcpos : 0 < Yc := by
    rw [hYcdef]
    refine lt_min ?_ (lt_min ?_ (lt_min ?_ (lt_min ?_ (lt_min ?_ (lt_min ?_ ?_)))))
    · rw [hY1def]; exact div_pos hcApos (by norm_num)
    · rw [hY2def]; exact div_pos harcE (by positivity)
    · rw [hY3def]; exact div_pos one_pos (by positivity)
    · rw [hY4def]; exact div_pos hcApos (by positivity)
    · rw [hY5def]; exact div_pos hcApos (by positivity)
    · rw [hY6def]; exact div_pos hcApos (by positivity)
    · rw [hY7def]; exact div_pos one_pos (by positivity)
  have hYc1 : Yc ≤ Y1 := by rw [hYcdef]; exact min_le_left _ _
  have hYc2 : Yc ≤ Y2 := by
    rw [hYcdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hYc3 : Yc ≤ Y3 := by
    rw [hYcdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hYc4 : Yc ≤ Y4 := by
    rw [hYcdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hYc5 : Yc ≤ Y5 := by
    rw [hYcdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hYc6 : Yc ≤ Y6 := by
    rw [hYcdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))))
  have hYc7 : Yc ≤ Y7 := by
    rw [hYcdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))))

  -- ## 2. the smallness parameters
  set X1 : ℝ := εg with hX1
  set X2 : ℝ := δg / (6 * s + 1) with hX2
  set X3 : ℝ := mbox / (6 * s + R2 + 2) with hX3
  set X4 : ℝ := m / (6 * s + R1 + 2) with hX4
  set X5 : ℝ := dv * lam / (2 * (6 * s + R1 + 2)) with hX5
  set X6 : ℝ := lam ^ 2 / (8 * M2 * (6 * s + R1) + 8) with hX6
  set X7 : ℝ := lam ^ 3 / (24 * Cv * (6 * s + R1) ^ 2 + 1) with hX7
  set X8 : ℝ := c00 * lam / (16 * M2 * (6 * s + R1) + 16) with hX8
  set X9 : ℝ := c00 / (16 * (M1 + 1)) with hX9
  set X10 : ℝ := 1 with hX10
  set X11 : ℝ := c00 / (4 * (M1 + 1)) with hX11
  set X12 : ℝ := 1 / 4 with hX12
  set caps : Finset ℝ := {X1, X2, X3, X4, X5, X6, X7, X8, X9, X10, X11, X12, θ', Yc} with hcaps
  have hcapsne : caps.Nonempty := ⟨X1, by rw [hcaps]; simp⟩
  obtain ⟨I, hImem, hIle⟩ := Finset.exists_min_image caps (fun x : ℝ => x) hcapsne
  have hIpos : 0 < I := by
    rw [hcaps] at hImem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hImem
    rcases hImem with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · rw [h, hX1]; exact hεg
    · rw [h, hX2]; exact div_pos hδg (by linarith [hs])
    · rw [h, hX3]; exact div_pos hmbox0 (by linarith [hs, hR20])
    · rw [h, hX4]; exact div_pos hm0 (by linarith [hs, hR1def])
    · rw [h, hX5]; exact div_pos (mul_pos hdv0 hlam0) (by linarith [hs, hR1def])
    · rw [h, hX6]; exact div_pos (pow_pos hlam0 2) (by nlinarith [hs, hR1def, hM20])
    · rw [h, hX7]; exact div_pos (pow_pos hlam0 3)
        (by nlinarith [hCv0, hs, hR1def, sq_nonneg (6 * s + R1)])
    · rw [h, hX8]; exact div_pos (mul_pos hc000 hlam0) (by nlinarith [hs, hR1def, hM20])
    · rw [h, hX9]; exact div_pos hc000 (by linarith [hM10])
    · rw [h, hX10]; norm_num
    · rw [h, hX11]; exact div_pos hc000 (by linarith [hM10])
    · rw [h, hX12]; norm_num
    · rw [h]; exact hθ'
    · rw [h]; exact hYcpos
  have hI_le_Yc : I ≤ Yc := hIle Yc (by rw [hcaps]; simp)
  have hIY1 : I ≤ Y1 := le_trans hI_le_Yc hYc1
  have hIY2 : I ≤ Y2 := le_trans hI_le_Yc hYc2
  have hIY3 : I ≤ Y3 := le_trans hI_le_Yc hYc3
  have hIY4 : I ≤ Y4 := le_trans hI_le_Yc hYc4
  have hIY5 : I ≤ Y5 := le_trans hI_le_Yc hYc5
  have hIY6 : I ≤ Y6 := le_trans hI_le_Yc hYc6
  have hIY7 : I ≤ Y7 := le_trans hI_le_Yc hYc7
  set η : ℝ := I / 24 with hη
  set ζ : ℝ := I / 48 with hζ
  have hη0 : 0 < η := by rw [hη]; exact div_pos hIpos (by norm_num)
  have hζ0 : 0 < ζ := by rw [hζ]; exact div_pos hIpos (by norm_num)
  have hζ_eq : ζ = η / 2 := by rw [hη, hζ]; ring
  have hη_le : η ≤ 1 / 24 := by
    have h := hIle X10 (by rw [hcaps]; simp)
    rw [hX10] at h
    rw [hη]; linarith
  -- ## 3. the base direction `n₀` and the admissible ball
  set n₀ : R3 := η • e + Real.sqrt (1 - η ^ 2) • Ñ₀ with hn₀def
  have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he1]; norm_num
  have hÑÑ : inner ℝ Ñ₀ Ñ₀ = 1 := by rw [real_inner_self_eq_norm_sq, hÑ₀1]; norm_num
  have hn₀_sq : inner ℝ n₀ n₀ = 1 := by
    have hsq : Real.sqrt (1 - η ^ 2) ^ 2 = 1 - η ^ 2 :=
      Real.sq_sqrt (by nlinarith only [hη_le, hη0])
    simp only [hn₀def, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hee, hÑÑ, hÑ₀orth, hÑ₀orth', mul_one, mul_zero, add_zero]
    ring_nf
    linarith only [hsq]
  have hn₀_norm : ‖n₀‖ = 1 := by
    have h : ‖n₀‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, hn₀_sq]
    calc ‖n₀‖ = Real.sqrt (‖n₀‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt 1 := by rw [h]
      _ = 1 := Real.sqrt_one
  have he_n₀ : inner ℝ e n₀ = η := by
    simp only [hn₀def, inner_add_right, real_inner_smul_right, hee, hÑ₀orth',
      mul_one, mul_zero, add_zero]
  set U : Set R3 := Metric.ball n₀ ζ with hU
  have hUopen : IsOpen U := by rw [hU]; exact Metric.isOpen_ball
  have hUne : U.Nonempty := ⟨n₀, by rw [hU, Metric.mem_ball, dist_self]; exact hζ0⟩
  obtain ⟨ng, hngU, hngGood⟩ := heightGood_exists_in ψ hUopen hUne
  have hngbd : ‖ng - n₀‖ < ζ := by
    rw [hU, Metric.mem_ball, dist_eq_norm] at hngU
    exact hngU
  have hζ_le : ζ ≤ 1 / 4 := by
    have h := hIle X12 (by rw [hcaps]; simp)
    rw [hX12] at h
    rw [hζ]; linarith
  have hng_low : 1 - ζ ≤ ‖ng‖ := by
    have h1 : ‖n₀‖ - ‖ng‖ ≤ ‖n₀ - ng‖ := (abs_le.mp (abs_norm_sub_norm_le n₀ ng)).2
    rw [hn₀_norm, norm_sub_rev] at h1
    linarith only [h1, hngbd]
  have hng_high : ‖ng‖ ≤ 1 + ζ := by
    have h1 : ‖ng‖ - ‖n₀‖ ≤ ‖ng - n₀‖ := (abs_le.mp (abs_norm_sub_norm_le ng n₀)).2
    rw [hn₀_norm] at h1
    linarith only [h1, hngbd]
  have hng_ne : ng ≠ 0 := by
    intro h0
    have h1 : ‖ng‖ = 0 := by rw [h0, norm_zero]
    linarith [hng_low, hζ_le]
  have he_ng : |inner ℝ e ng - η| < ζ := by
    have h1 : inner ℝ e ng - η = inner ℝ e (ng - n₀) := by
      rw [inner_sub_right, he_n₀]
    rw [h1]
    calc |inner ℝ e (ng - n₀)| ≤ ‖e‖ * ‖ng - n₀‖ := abs_real_inner_le_norm _ _
      _ = ‖ng - n₀‖ := by rw [he1, one_mul]
      _ < ζ := hngbd
  -- ## 4. the witness
  set n : R3 := unitDir ng with hndef
  have hn1 : ‖n‖ = 1 := by rw [hndef]; exact unitDir_norm ng hng_ne
  set v : R3 := orthDir e n with hvdef
  set τ : ℝ := ‖v - e‖ with hτdef
  have hκ_eq : inner ℝ e n = (‖ng‖)⁻¹ * inner ℝ e ng := by
    rw [hndef, real_inner_comm, inner_unitDir, real_inner_comm]
  have hκ_pos : η / 3 ≤ inner ℝ e n := by
    rw [hκ_eq]
    have h1 : η / 2 ≤ inner ℝ e ng := by
      have hh := (abs_lt.mp he_ng).1
      have h2 : ζ = η / 2 := hζ_eq
      linarith only [hh, h2]
    have h2 : (‖ng‖)⁻¹ ≥ 2 / 3 := by
      have h3 : (1 : ℝ) + ζ ≤ 5 / 4 := by linarith only [hζ_le]
      have h4 : (‖ng‖)⁻¹ ≥ ((1 : ℝ) + ζ)⁻¹ := by
        have hpos : 0 < ‖ng‖ := by linarith only [hng_low, hζ_le]
        have hh := one_div_le_one_div_of_le hpos hng_high
        simpa [one_div] using hh
      have h5 : ((1 : ℝ) + ζ)⁻¹ ≥ 2 / 3 := by
        rw [ge_iff_le, ← one_div, le_div_iff₀ (by linarith only [hζ0] : (0:ℝ) < 1 + ζ)]
        linarith only [h3]
      linarith only [h4, h5]
    calc η / 3 = (2 / 3) * (η / 2) := by ring
      _ ≤ (‖ng‖)⁻¹ * inner ℝ e ng :=
          mul_le_mul h2 h1 (by linarith only [hη0]) (inv_nonneg.mpr (norm_nonneg _))
  have hκ_le : inner ℝ e n ≤ 3 * η := by
    rw [hκ_eq]
    have h1 : inner ℝ e ng ≤ 3 * η / 2 := by
      have hh := (abs_lt.mp he_ng).2
      linarith only [hh, hζ_eq]
    have h2 : (‖ng‖)⁻¹ ≤ 2 := by
      have h3 : (3 : ℝ) / 4 ≤ ‖ng‖ := by linarith only [hng_low, hζ_le]
      have h4 : (‖ng‖)⁻¹ ≤ 4 / 3 := by
        have hh := one_div_le_one_div_of_le (show (0 : ℝ) < (3:ℝ)/4 by norm_num) h3
        simpa [one_div] using hh
      linarith only [h4]
    have h4 : 0 < inner ℝ e ng := by
      have hh := (abs_lt.mp he_ng).1
      linarith only [hh, hζ_eq, hη0]
    calc (‖ng‖)⁻¹ * inner ℝ e ng ≤ 2 * (3 * η / 2) :=
          mul_le_mul h2 h1 (le_of_lt h4) (by linarith only [hη0])
      _ = 3 * η := by ring
  have hκ_half : |inner ℝ e n| ≤ 1 / 2 := by
    rw [abs_of_nonneg (by linarith only [hκ_pos, hη0])]
    have h := hIle X10 (by rw [hcaps]; simp)
    rw [hX10] at h
    nlinarith only [hκ_le, hη, h]
  obtain ⟨hv1, hvn, hev, hτ_up, hτ_low⟩ :=
    orthDir_spec (e := e) (m := n) he1 hn1 (s := inner ℝ e n) rfl hκ_half
  have hτ_pos : 0 < τ := by
    have h : |inner ℝ e n| ≤ τ := by rw [hτdef]; exact hτ_low
    have h2 : 0 < |inner ℝ e n| := abs_pos.mpr (by
      intro h0
      have h3 := hκ_pos
      rw [h0] at h3
      linarith only [h3, hη0])
    linarith only [h, h2]
  have hτ_I : τ ≤ I / 4 := by
    have h1 : τ ≤ Real.sqrt 2 * (3 * η) := by
      calc τ ≤ Real.sqrt 2 * |inner ℝ e n| := hτ_up
        _ ≤ Real.sqrt 2 * (3 * η) := by
            apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg 2)
            rw [abs_of_nonneg (by linarith only [hκ_pos, hη0])]
            exact hκ_le
    have h2 : Real.sqrt 2 ≤ 2 := by
      nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have h5 : 0 ≤ 3 * η := by linarith only [hη0]
    calc τ ≤ Real.sqrt 2 * (3 * η) := h1
      _ ≤ 2 * (3 * η) := mul_le_mul_of_nonneg_right h2 h5
      _ = I / 4 := by rw [hη]; ring
  set h : ℝ := 6 * s * τ with hhdef
  have hh_pos : 0 < h := by rw [hhdef]; exact mul_pos (mul_pos (by norm_num) hs) hτ_pos
  -- the robustness radius
  set ρ : ℝ := min (τ / 12) (min (c00 / (96 * (M1 + 1))) (τ / (144 * (arcM + 2)))) with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]
    exact lt_min (by linarith only [hτ_pos])
      (lt_min (div_pos hc000 (by linarith only [hM10])) (div_pos hτ_pos (by positivity)))
  have hρ_le_tau : ρ ≤ τ / 12 := by rw [hρdef]; exact min_le_left _ _
  have hρM1 : ρ * M1 ≤ c00 / 96 := by
    have h1 : ρ ≤ c00 / (96 * (M1 + 1)) := by
      rw [hρdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    have h2 : ρ * M1 ≤ c00 / (96 * (M1 + 1)) * M1 := mul_le_mul_of_nonneg_right h1 hM10
    have h3 : c00 / (96 * (M1 + 1)) * M1 ≤ c00 / 96 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by linarith only [hM10]) (by norm_num : (0:ℝ) < 96)]
      nlinarith only [hc000, hM10]
    linarith only [h2, h3]
  -- ## 5. the constraints
  have hI2 : I ≤ δg / (6 * s + 1) := by
    have h := hIle X2 (by rw [hcaps]; simp); rwa [hX2] at h
  have hI3 : I ≤ mbox / (6 * s + R2 + 2) := by
    have h := hIle X3 (by rw [hcaps]; simp); rwa [hX3] at h
  have hI4 : I ≤ m / (6 * s + R1 + 2) := by
    have h := hIle X4 (by rw [hcaps]; simp); rwa [hX4] at h
  have hI5 : I ≤ dv * lam / (2 * (6 * s + R1 + 2)) := by
    have h := hIle X5 (by rw [hcaps]; simp); rwa [hX5] at h
  have hI6 : I ≤ lam ^ 2 / (8 * M2 * (6 * s + R1) + 8) := by
    have h := hIle X6 (by rw [hcaps]; simp); rwa [hX6] at h
  have hI7 : I ≤ lam ^ 3 / (24 * Cv * (6 * s + R1) ^ 2 + 1) := by
    have h := hIle X7 (by rw [hcaps]; simp); rwa [hX7] at h
  have hI8 : I ≤ c00 * lam / (16 * M2 * (6 * s + R1) + 16) := by
    have h := hIle X8 (by rw [hcaps]; simp); rwa [hX8] at h
  have hI9 : I ≤ c00 / (16 * (M1 + 1)) := by
    have h := hIle X9 (by rw [hcaps]; simp); rwa [hX9] at h
  have hI11 : I ≤ c00 / (4 * (M1 + 1)) := by
    have h := hIle X11 (by rw [hcaps]; simp); rwa [hX11] at h
  have hτ_theta : τ ≤ θ' := by
    have h : I ≤ θ' := hIle θ' (by rw [hcaps]; simp)
    linarith only [hτ_I, h, hθ']
  have hτ_eps : τ ≤ εg / 4 := by
    have h : I ≤ εg := by
      have h := hIle X1 (by rw [hcaps]; simp); rwa [hX1] at h
    linarith only [hτ_I, h]
  -- (c1) the tilt is small enough for the no-grazing hypothesis
  have hc1 : τ < εg := by linarith only [hτ_eps, hεg]
  -- (c2) `h < δg`
  have hc2 : h < δg := by
    have h : τ * (4 * (6 * s + 1)) ≤ δg :=
      mg_mul_le_of_le_quarter (by linarith only [hs]) (by linarith only [hτ_I, hI2])
    have hh : 6 * s * τ ≤ δg / 4 := by nlinarith only [h, hs, hτ_pos]
    rw [hhdef]
    linarith only [hh, hδg]
  -- (c3) the bound on the box sphere
  have hc3 : τ * (6 * s + R2) ≤ mbox := by
    have h : τ * (4 * (6 * s + R2 + 2)) ≤ mbox :=
      mg_mul_le_of_le_quarter (by linarith only [hs, hR20])
        (by linarith only [hτ_I, hI3])
    nlinarith only [h, hs, hR20, hτ_pos]
  -- (c4) the covering constraint
  have hc4 : τ * (6 * s + R1) < m := by
    have h : τ * (4 * (6 * s + R1 + 2)) ≤ m :=
      mg_mul_le_of_le_quarter (by linarith only [hs, hR1def])
        (by linarith only [hτ_I, hI4])
    nlinarith only [h, hs, hR1def, hτ_pos, hm0]
  -- (c5a) `2H/lam ≤ dv`
  have hc5a : 2 * (τ * (6 * s + R1)) ≤ dv * lam := by
    have h : τ * (4 * (2 * (6 * s + R1 + 2))) ≤ dv * lam :=
      mg_mul_le_of_le_quarter (by linarith only [hs, hR1def])
        (by linarith only [hτ_I, hI5])
    nlinarith only [h, hs, hR1def, hτ_pos]
  -- (c5b) `M2 * (2H/lam) ≤ lam/2`
  have hc5b : 2 * M2 * (τ * (6 * s + R1)) ≤ lam ^ 2 / 2 := by
    have h : τ * (4 * (8 * M2 * (6 * s + R1) + 8)) ≤ lam ^ 2 :=
      mg_mul_le_of_le_quarter (by nlinarith only [hs, hR1def, hM20])
        (by linarith only [hτ_I, hI6])
    nlinarith only [h, hs, hR1def, hM20, hτ_pos, hlam0]
  -- (c5c) the vertical-crossing positivity
  have hc5c : 4 * Cv * τ ^ 2 * (6 * s + R1) ^ 2 / lam ^ 2 < τ * lam / 6 := by
    have h : τ * (4 * (24 * Cv * (6 * s + R1) ^ 2 + 1)) ≤ lam ^ 3 :=
      mg_mul_le_of_le_quarter
        (by nlinarith only [hCv0, hs, hR1def, sq_nonneg (6 * s + R1)])
        (by linarith only [hτ_I, hI7])
    have h2 : 24 * Cv * (6 * s + R1) ^ 2 * τ ≤ lam ^ 3 / 4 := by
      nlinarith only [h, hτ_pos, hCv0, hs, hR1def]
    have h3 : 4 * Cv * (6 * s + R1) ^ 2 * τ ≤ lam ^ 3 / 24 := by linarith only [h2]
    have h4 : 4 * Cv * (6 * s + R1) ^ 2 * τ * τ ≤ (lam ^ 3 / 24) * τ :=
      mul_le_mul_of_nonneg_right h3 (le_of_lt hτ_pos)
    have hX : 0 < τ * lam ^ 3 := mul_pos hτ_pos (pow_pos hlam0 3)
    have h5 : τ * lam ^ 3 / 24 < τ * lam ^ 3 / 6 := by linarith only [hX]
    have h6 : 4 * Cv * τ ^ 2 * (6 * s + R1) ^ 2 ≤ τ * lam ^ 3 / 24 := by
      nlinarith only [h4]
    rw [div_lt_iff₀ (pow_pos hlam0 2)]
    linarith only [h5, h6]
  -- (c6a) the non-vertical-crossing bound
  have hc6a : 2 * M2 * (τ * (6 * s + R1)) ≤ c00 * lam / 16 := by
    have h : τ * (4 * (16 * M2 * (6 * s + R1) + 16)) ≤ c00 * lam :=
      mg_mul_le_of_le_quarter (by nlinarith only [hs, hR1def, hM20])
        (by linarith only [hτ_I, hI8])
    nlinarith only [h, hs, hR1def, hM20, hτ_pos, hlam0, hc000]
  -- (c6b) the other non-vertical-crossing bound
  have hc6b : inner ℝ e n * M1 ≤ c00 / 16 := by
    have h2 : 3 * η ≤ I / 8 := by rw [hη]; linarith only []
    have h3 : inner ℝ e n ≤ (c00 / (16 * (M1 + 1))) / 8 := by
      linarith only [hκ_le, h2, hI9]
    have h4 : inner ℝ e n * M1 ≤ ((c00 / (16 * (M1 + 1))) / 8) * M1 :=
      mul_le_mul_of_nonneg_right h3 hM10
    have h5 : ((c00 / (16 * (M1 + 1))) / 8) * M1 ≤ c00 / 16 := by
      have h6 : (c00 / (16 * (M1 + 1))) / 8 = c00 / (128 * (M1 + 1)) := by
        rw [div_div, show (16 * (M1 + 1)) * 8 = 128 * (M1 + 1) by ring]
      rw [h6, div_mul_eq_mul_div,
        div_le_div_iff₀ (by linarith only [hM10]) (by norm_num : (0:ℝ) < 16)]
      nlinarith only [hM10, hc000]
    linarith only [h4, h5]
  -- (c7) the ball radius constraints
  have hc7a : ζ ≤ 1 / 2 := by linarith only [hζ_le]
  have hc7b : ζ * M1 ≤ c00 / 4 := by
    have h1 : ζ * (192 * (M1 + 1)) ≤ c00 := by
      have h3 : (c00 / (4 * (M1 + 1))) / 48 = c00 / (192 * (M1 + 1)) := by
        rw [div_div, show (4 * (M1 + 1)) * 48 = 192 * (M1 + 1) by ring]
      have h4 : ζ ≤ c00 / (192 * (M1 + 1)) := by
        calc ζ = I / 48 := hζ
          _ ≤ (c00 / (4 * (M1 + 1))) / 48 := div_le_div_of_nonneg_right hI11 (by norm_num)
          _ = c00 / (192 * (M1 + 1)) := h3
      exact mg_mul_le_of_le_div (by linarith only [hM10]) h4
    have hden : 0 < 192 * (M1 + 1) := by linarith only [hM10]
    have h1' : ζ * (192 * (M1 + 1)) * M1 ≤ c00 * M1 := mul_le_mul_of_nonneg_right h1 hM10
    have h6 : ζ * M1 ≤ (c00 * M1) / (192 * (M1 + 1)) := by
      rw [le_div_iff₀ hden]; nlinarith only [h1']
    have h7 : (c00 * M1) / (192 * (M1 + 1)) ≤ c00 / 4 := by
      rw [div_le_div_iff₀ hden (by norm_num : (0:ℝ) < 4)]
      nlinarith only [hM10, hc000]
    linarith only [h6, h7]
  -- ## 6. the witness
  have hv1' : ‖v‖ = 1 := by rw [hvdef]; exact hv1
  have hvn' : inner ℝ v n = 0 := by rw [hvdef]; exact hvn
  have hgood : HeightGood ψ n := by
    rw [hndef, unitDir]
    exact (heightGood_smul_iff ψ (inv_ne_zero (norm_ne_zero_iff.mpr hng_ne)) ng).mpr hngGood
  refine ⟨v, n, h, ρ, hv1', hn1, hvn', hgood, ?_, ?_, hh_pos, hρpos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `‖v - e‖ ≤ θ'`
    have hτeq : ‖v - Work.BoxShrink.shiftVσ σ 1‖ = τ := by rw [← hedef]
    rw [hτeq]
    exact hτ_theta
  · -- `‖v - e‖ ≤ εg / 4`
    have hτeq : ‖v - Work.BoxShrink.shiftVσ σ 1‖ = τ := by rw [← hedef]
    rw [hτeq]
    exact hτ_eps
  · -- the size condition
    have hτeq : ‖v - Work.BoxShrink.shiftVσ σ 1‖ = τ := by rw [← hedef]
    rw [hτeq, hhdef]
    have h5 : 0 < s * τ := mul_pos hs hτ_pos
    have h6 : 2 * (τ * R1) = 5 * (s * τ) := by rw [hR1def]; ring
    linarith only [h5, h6]
  · -- clause 1: on the box sphere
    intro t ht
    have hsb : slabHeight K c u v t = inner ℝ v (K.curve t) - (inner ℝ v c + u) := rfl
    rw [← hsb]
    have hR2b : ‖K.curve t - c‖ ≤ R2 := hR2 _ ht
    have hmb : mbox ≤ |flatHeight K c σ u t| := by
      rw [flatHeight_apply]; exact hmbox t ht
    have hdiff : |slabHeight K c u v t - flatHeight K c σ u t| ≤ τ * R2 := by
      rw [slabHeight_sub_flatHeight]
      calc |inner ℝ (v - e) (K.curve t - c)| ≤ ‖v - e‖ * ‖K.curve t - c‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ τ * R2 := by rw [hτdef]; exact mul_le_mul_of_nonneg_left hR2b (norm_nonneg _)
    have hkey : mbox - τ * R2 ≤ |slabHeight K c u v t| := by
      have h1 := abs_sub_abs_le_abs_sub (flatHeight K c σ u t) (slabHeight K c u v t)
      rw [abs_sub_comm (flatHeight K c σ u t) (slabHeight K c u v t)] at h1
      linarith only [h1, hmb, hdiff]
    rw [hhdef]
    linarith only [hkey, hc3]
  · -- clause 2: at the critical points of the tilted height
    intro t htbox hderiv
    have hve : ‖v - Work.BoxShrink.shiftVσ σ 1‖ < εg := by
      rw [← hedef, show ‖v - e‖ = τ from rfl]
      linarith only [hτ_eps, hεg]
    have := hnograz v hv1' hve t htbox hderiv
    rw [hhdef]
    linarith only [this, hc2]
  · -- clause 3: the slab region, robustly in the normal direction
    intro nn hnn1 hnnnear t htbox hslab
    obtain ⟨t', ht'Icc, hct', hdt'⟩ := exists_period_reduce K t
    have ht'box : K.curve t' ∈ Submission.PBox s c σ := by rw [hct']; exact htbox
    have ht'cl : K.curve t' ∈ closure (Submission.PBox s c σ) := subset_closure ht'box
    have hslab' : |slabHeight K c u v t'| ≤ h := by
      rw [slabHeight_apply, hct']
      exact hslab
    have hdiff' : |slabHeight K c u v t' - flatHeight K c σ u t'| ≤ τ * R1 := by
      rw [slabHeight_sub_flatHeight]
      calc |inner ℝ (v - e) (K.curve t' - c)| ≤ ‖v - e‖ * ‖K.curve t' - c‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ τ * R1 := by
            rw [hτdef]
            exact mul_le_mul_of_nonneg_left (hR1b _ ht'box) (norm_nonneg _)
    have hφ : |flatHeight K c σ u t'| ≤ τ * (6 * s + R1) := by
      have h1 := abs_sub_abs_le_abs_sub (flatHeight K c σ u t') (slabHeight K c u v t')
      rw [abs_sub_comm (flatHeight K c σ u t') (slabHeight K c u v t')] at h1
      linarith only [h1, hslab', hdiff']
    have hderiv_eq : deriv (fun r : ℝ => inner ℝ nn (K.curve r)) t
        = deriv (fun r : ℝ => inner ℝ nn (K.curve r)) t' := by
      rw [deriv_inner_curve_const, deriv_inner_curve_const, hdt']
    rw [hderiv_eq, deriv_inner_eq_mul_add_vertVel K he1 t', inner_shiftVσ_one,
      show inner ℝ nn e = inner ℝ e nn from real_inner_comm e nn,
      mul_comm (inner ℝ e nn) ((deriv K.curve t') (σ 2))]
    by_cases hfar : |flatHeight K c σ u t'| < m
    · obtain ⟨ts, htsT, hbt⟩ := hcover t' ht'Icc ht'cl hfar
      have htsIcc : ts ∈ Set.Icc 0 (2 * Real.pi) := (mem_crossingSet.mp htsT).1
      have htscl : K.curve ts ∈ closure (Submission.PBox s c σ) := (mem_crossingSet.mp htsT).2.1
      have htslv : (K.curve ts) (σ 2) = c (σ 2) + u := (mem_crossingSet.mp htsT).2.2
      have hspd : lam ≤ |deriv (flatHeight K c σ u) ts| := hlam ts htsT
      have hspd' : lam ≤ |(deriv K.curve ts) (σ 2)| := by
        rw [← deriv_flatHeight]; exact hspd
      have hdist : |t' - ts| ≤ 2 * (τ * (6 * s + R1)) / lam := by
        have h1 : lam * |t' - ts| ≤ 2 * (τ * (6 * s + R1)) :=
          le_trans hbt (by linarith only [hφ])
        rw [le_div_iff₀ hlam0]
        linarith only [h1]
      by_cases hv : vertVel K e ts = 0
      · -- the crossing is vertical
        have hacc : vertAcc K e ts = 0 := hnobend ts htscl htslv hv
        have hquad : ‖vertVel K e t'‖ ≤ Cv * (t' - ts) ^ 2 := by
          refine hCv ts hv hacc t' ?_
          have h2H : 2 * (τ * (6 * s + R1)) / lam ≤ dv := by
            rw [div_le_iff₀ hlam0]; nlinarith only [hc5a]
          linarith only [hdist, h2H]
        have hα_low : lam / 2 ≤ |(deriv K.curve t') (σ 2)| := by
          have hmvt := noGraze_mvt_coord (K := K) hM2 σ t' ts
          have h3 : M2 * |t' - ts| ≤ lam / 2 := by
            have h4 : M2 * (2 * (τ * (6 * s + R1))) ≤ lam ^ 2 / 2 := by
              linarith only [hc5b]
            have h5 : M2 * (2 * (τ * (6 * s + R1))) / lam ≤ lam / 2 := by
              rw [div_le_iff₀ hlam0]
              nlinarith only [h4, hlam0]
            have h6 : M2 * (2 * (τ * (6 * s + R1)) / lam)
                = M2 * (2 * (τ * (6 * s + R1))) / lam := by ring
            calc M2 * |t' - ts| ≤ M2 * (2 * (τ * (6 * s + R1)) / lam) :=
                  mul_le_mul_of_nonneg_left hdist hM20
              _ = M2 * (2 * (τ * (6 * s + R1))) / lam := h6
              _ ≤ lam / 2 := h5
          have h7 : |(deriv K.curve ts) (σ 2)| - |(deriv K.curve t') (σ 2)| ≤ M2 * |t' - ts| := by
            have h8 := abs_sub_abs_le_abs_sub ((deriv K.curve ts) (σ 2)) ((deriv K.curve t') (σ 2))
            rw [abs_sub_comm ((deriv K.curve ts) (σ 2)) ((deriv K.curve t') (σ 2))] at h8
            linarith only [h8, hmvt]
          linarith only [h7, h3, hspd']
        have hκge : τ / 2 ≤ |inner ℝ e n| := by
          have h1 : τ ≤ Real.sqrt 2 * |inner ℝ e n| := hτ_up
          have h2 : Real.sqrt 2 ≤ 2 := by
            nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
              Real.sqrt_nonneg 2]
          nlinarith only [h1, h2, abs_nonneg (inner ℝ e n)]
        have hκge_nn : τ / 2 - ρ ≤ |inner ℝ e nn| := by
          have h1 : |inner ℝ e n| - |inner ℝ e nn| ≤ |inner ℝ e n - inner ℝ e nn| :=
            abs_sub_abs_le_abs_sub _ _
          have h2 : |inner ℝ e n - inner ℝ e nn| ≤ ‖nn - n‖ := by
            rw [← inner_sub_right]
            calc |inner ℝ e (n - nn)| ≤ ‖e‖ * ‖n - nn‖ := abs_real_inner_le_norm _ _
              _ = ‖nn - n‖ := by rw [he1, one_mul, norm_sub_rev]
          linarith only [h1, h2, hnnnear, hκge]
        have hA : lam / 2 * (τ / 2 - ρ) - Cv * (t' - ts) ^ 2
            ≤ |(deriv K.curve t') (σ 2) * inner ℝ e nn + inner ℝ nn (vertVel K e t')| := by
          have h1 : lam / 2 * (τ / 2 - ρ) ≤ |(deriv K.curve t') (σ 2)| * |inner ℝ e nn| :=
            mul_le_mul hα_low hκge_nn (by linarith only [hτ_pos, hρ_le_tau]) (abs_nonneg _)
          have h2 : |inner ℝ nn (vertVel K e t')| ≤ ‖vertVel K e t'‖ :=
            mg_abs_inner_unit_le hnn1
          have h3 := mg_le_abs_add ((deriv K.curve t') (σ 2) * inner ℝ e nn)
            (inner ℝ nn (vertVel K e t'))
          have h4 : |(deriv K.curve t') (σ 2) * inner ℝ e nn|
              = |(deriv K.curve t') (σ 2)| * |inner ℝ e nn| := abs_mul _ _
          linarith only [h1, h2, h3, h4, hquad]
        have hfinal : 0 < lam / 2 * (τ / 2 - ρ) - Cv * (t' - ts) ^ 2 := by
          have hsq : (t' - ts) ^ 2 ≤ (2 * (τ * (6 * s + R1)) / lam) ^ 2 := by
            have h2 := abs_le.mp hdist
            have hh0 : 0 ≤ 2 * (τ * (6 * s + R1)) / lam :=
              div_nonneg (by nlinarith only [hτ_pos, hs, hR1def]) (le_of_lt hlam0)
            nlinarith only [h2.1, h2.2, hh0]
          have h1 : Cv * (t' - ts) ^ 2 ≤ Cv * (2 * (τ * (6 * s + R1)) / lam) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (le_of_lt hCv0)
          have h2 : Cv * (2 * (τ * (6 * s + R1)) / lam) ^ 2 < τ * lam / 6 := by
            have h3 : (2 * (τ * (6 * s + R1)) / lam) ^ 2
                = 4 * τ ^ 2 * (6 * s + R1) ^ 2 / lam ^ 2 := by
              rw [div_pow, mul_pow]
              ring
            rw [h3]
            have h4 : Cv * (4 * τ ^ 2 * (6 * s + R1) ^ 2 / lam ^ 2) < τ * lam / 6 := by
              have h4b : Cv * (4 * τ ^ 2 * (6 * s + R1) ^ 2 / lam ^ 2)
                  = 4 * Cv * τ ^ 2 * (6 * s + R1) ^ 2 / lam ^ 2 := by ring
              rw [h4b]; exact hc5c
            linarith only [h4]
          have hρb : lam / 2 * ρ ≤ lam * τ / 24 := by
            have h := mul_le_mul_of_nonneg_left hρ_le_tau
              (by linarith only [hlam0] : (0 : ℝ) ≤ lam / 2)
            nlinarith only [h]
          nlinarith only [h1, h2, hρb, hτ_pos, hlam0]
        exact abs_pos.mp (by linarith only [hA, hfinal])
      · -- the crossing is not vertical
        have hc00t : c00 ≤ |inner ℝ Ñ₀ (vertVel K e ts)| := hc00le ts htsT hv
        have hng_le : ‖ng‖ ≤ 3 / 2 := by linarith only [hng_high, hζ_le]
        have hng_ge : (1 : ℝ) / 2 ≤ ‖ng‖ := by linarith only [hng_low, hζ_le]
        have hw0 : inner ℝ e (vertVel K e ts) = 0 := by
          rw [real_inner_comm (vertVel K e ts) e]
          exact inner_vertVel_eq_zero K he1 ts
        have hn₀w : inner ℝ n₀ (vertVel K e ts)
            = Real.sqrt (1 - η ^ 2) * inner ℝ Ñ₀ (vertVel K e ts) := by
          rw [hn₀def, inner_add_left, real_inner_smul_left, real_inner_smul_left, hw0,
            mul_zero, zero_add]
        have h1 : c00 / 2 ≤ |inner ℝ n₀ (vertVel K e ts)| := by
          rw [hn₀w, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
          have h2 : (1 : ℝ) / 2 ≤ Real.sqrt (1 - η ^ 2) := by
            rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
            apply Real.sqrt_le_sqrt
            nlinarith only [hη_le, hη0]
          calc c00 / 2 = (1 / 2) * c00 := by ring
            _ ≤ Real.sqrt (1 - η ^ 2) * |inner ℝ Ñ₀ (vertVel K e ts)| :=
                mul_le_mul h2 hc00t (le_of_lt hc000) (Real.sqrt_nonneg _)
        have h2 : c00 / 4 ≤ |inner ℝ ng (vertVel K e ts)| := by
          have h3 : |inner ℝ ng (vertVel K e ts) - inner ℝ n₀ (vertVel K e ts)|
              ≤ ‖ng - n₀‖ * ‖vertVel K e ts‖ := by
            rw [← inner_sub_left]
            exact abs_real_inner_le_norm _ _
          have hwM1 : ‖vertVel K e ts‖ ≤ M1 :=
            le_trans (norm_perpProj_le (e := e) (x := deriv K.curve ts) he1) (hM1 ts)
          have h4 : ‖ng - n₀‖ * ‖vertVel K e ts‖ ≤ ζ * M1 :=
            mul_le_mul (le_of_lt hngbd) hwM1 (norm_nonneg _) (le_of_lt hζ0)
          have h5 : |inner ℝ n₀ (vertVel K e ts)| - ζ * M1
              ≤ |inner ℝ ng (vertVel K e ts)| := by
            have hh := abs_sub_abs_le_abs_sub (inner ℝ n₀ (vertVel K e ts))
              (inner ℝ ng (vertVel K e ts))
            rw [abs_sub_comm (inner ℝ n₀ (vertVel K e ts)) (inner ℝ ng (vertVel K e ts))] at hh
            linarith only [hh, h3, h4]
          linarith only [h1, h5, hc7b]
        have h3 : c00 / 6 ≤ |inner ℝ n (vertVel K e ts)| := by
          have hunit : inner ℝ n (vertVel K e ts)
              = (‖ng‖)⁻¹ * inner ℝ ng (vertVel K e ts) := by
            rw [hndef, inner_unitDir]
          rw [hunit, abs_mul, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
          have h4 : (3 / 2 : ℝ)⁻¹ ≤ (‖ng‖)⁻¹ := by
            have hh := one_div_le_one_div_of_le (by linarith only [hng_ge]) hng_le
            simpa [one_div] using hh
          calc c00 / 6 = (3 / 2 : ℝ)⁻¹ * (c00 / 4) := by ring
            _ ≤ (‖ng‖)⁻¹ * |inner ℝ ng (vertVel K e ts)| :=
                mul_le_mul h4 h2 (by linarith only [hc000]) (inv_nonneg.mpr (norm_nonneg _))
        have h4 : c00 / 6 - c00 / 16 ≤ |inner ℝ n (vertVel K e t')| := by
          have h5 : |inner ℝ n (vertVel K e t') - inner ℝ n (vertVel K e ts)|
              ≤ ‖vertVel K e t' - vertVel K e ts‖ := by
            rw [← inner_sub_right]
            exact mg_abs_inner_unit_le (n := n) (w := vertVel K e t' - vertVel K e ts) hn1
          have h6 := noGraze_mvt_vertVel (K := K) he1 hM2 t' ts
          have h7 : M2 * |t' - ts| ≤ 2 * M2 * (τ * (6 * s + R1)) / lam := by
            have h7b : M2 * (2 * (τ * (6 * s + R1)) / lam)
                = M2 * (2 * (τ * (6 * s + R1))) / lam := by ring
            calc M2 * |t' - ts| ≤ M2 * (2 * (τ * (6 * s + R1)) / lam) :=
                  mul_le_mul_of_nonneg_left hdist hM20
              _ = M2 * (2 * (τ * (6 * s + R1))) / lam := h7b
              _ = 2 * M2 * (τ * (6 * s + R1)) / lam := by ring
          have h8 : 2 * M2 * (τ * (6 * s + R1)) / lam ≤ c00 / 16 := by
            rw [div_le_iff₀ hlam0]; nlinarith only [hc6a, hlam0]
          have h9 : |inner ℝ n (vertVel K e ts)| - |inner ℝ n (vertVel K e t')|
              ≤ |inner ℝ n (vertVel K e t') - inner ℝ n (vertVel K e ts)| := by
            have hh := abs_sub_abs_le_abs_sub (inner ℝ n (vertVel K e ts))
              (inner ℝ n (vertVel K e t'))
            rw [abs_sub_comm (inner ℝ n (vertVel K e ts)) (inner ℝ n (vertVel K e t'))] at hh
            exact hh
          linarith only [h3, h5, h6, h7, h8, h9]
        have h4nn : c00 / 6 - c00 / 16 - ρ * M1 ≤ |inner ℝ nn (vertVel K e t')| := by
          have h5 : |inner ℝ nn (vertVel K e t') - inner ℝ n (vertVel K e t')|
              ≤ ‖nn - n‖ * ‖vertVel K e t'‖ := by
            rw [← inner_sub_left]
            exact abs_real_inner_le_norm _ _
          have hwM1 : ‖vertVel K e t'‖ ≤ M1 :=
            le_trans (norm_perpProj_le (e := e) (x := deriv K.curve t') he1) (hM1 t')
          have h6 : ‖nn - n‖ * ‖vertVel K e t'‖ ≤ ρ * M1 :=
            mul_le_mul (le_of_lt hnnnear) hwM1 (norm_nonneg _) (le_of_lt hρpos)
          have h7 : |inner ℝ n (vertVel K e t')| - |inner ℝ nn (vertVel K e t')| ≤ ρ * M1 := by
            have hh := abs_sub_abs_le_abs_sub (inner ℝ n (vertVel K e t'))
              (inner ℝ nn (vertVel K e t'))
            rw [abs_sub_comm (inner ℝ n (vertVel K e t')) (inner ℝ nn (vertVel K e t'))] at hh
            linarith only [hh, h5, h6]
          linarith only [h4, h7]
        have hx_up : |(deriv K.curve t') (σ 2) * inner ℝ e nn| ≤ c00 / 16 + M1 * ρ := by
          have hα_le : |(deriv K.curve t') (σ 2)| ≤ M1 := by
            have h10 := abs_real_inner_le_norm e (deriv K.curve t')
            rw [he1, one_mul, inner_shiftVσ_one] at h10
            exact le_trans h10 (hM1 t')
          have hκnn : |inner ℝ e nn| ≤ inner ℝ e n + ρ := by
            have hκen : |inner ℝ e n| = inner ℝ e n :=
              abs_of_nonneg (by linarith only [hκ_pos, hη0])
            have h2 : |inner ℝ e (nn - n)| ≤ ‖nn - n‖ := by
              calc |inner ℝ e (nn - n)| ≤ ‖e‖ * ‖nn - n‖ := abs_real_inner_le_norm _ _
                _ = ‖nn - n‖ := by rw [he1, one_mul]
            have hsplit : inner ℝ e nn = inner ℝ e n + inner ℝ e (nn - n) := by
              rw [← inner_add_right]; congr 1; abel
            calc |inner ℝ e nn| = |inner ℝ e n + inner ℝ e (nn - n)| := by rw [hsplit]
              _ ≤ |inner ℝ e n| + |inner ℝ e (nn - n)| := abs_add_le _ _
              _ ≤ inner ℝ e n + ρ := by rw [hκen]; linarith only [h2, hnnnear]
          rw [abs_mul]
          calc |(deriv K.curve t') (σ 2)| * |inner ℝ e nn| ≤ M1 * (inner ℝ e n + ρ) :=
                mul_le_mul hα_le hκnn (abs_nonneg _) hM10
            _ = M1 * inner ℝ e n + M1 * ρ := by ring
            _ ≤ c00 / 16 + M1 * ρ := by
                have hb : M1 * inner ℝ e n ≤ c00 / 16 := by
                  rw [mul_comm]; exact hc6b
                linarith only [hb]
        have hA : c00 / 6 - c00 / 16 - ρ * M1 - (c00 / 16 + M1 * ρ)
            ≤ |(deriv K.curve t') (σ 2) * inner ℝ e nn + inner ℝ nn (vertVel K e t')| := by
          have h1 := mg_le_abs_add (inner ℝ nn (vertVel K e t'))
            ((deriv K.curve t') (σ 2) * inner ℝ e nn)
          rw [add_comm] at h1
          linarith only [h1, h4nn, hx_up]
        have hfrac : 0 < c00 / 6 - c00 / 16 - ρ * M1 - (c00 / 16 + M1 * ρ) := by
          nlinarith only [hc000, hρM1]
        exact abs_pos.mp (by linarith only [hA, hfrac])
    · -- far from every crossing: the slab misses the knot
      exfalso
      push Not at hfar
      have h1 := abs_sub_abs_le_abs_sub (flatHeight K c σ u t') (slabHeight K c u v t')
      rw [abs_sub_comm (flatHeight K c σ u t') (slabHeight K c u v t')] at h1
      linarith only [h1, hdiff', hfar, hslab', hc4]
  · -- clause 4: the slab boundary
    intro t htbox hEq hderiv
    exfalso
    have hve : ‖v - Work.BoxShrink.shiftVσ σ 1‖ < εg := by
      rw [← hedef, show ‖v - e‖ = τ from rfl]
      linarith only [hτ_eps, hεg]
    have := hnograz v hv1' hve t htbox hderiv
    rw [hEq] at this
    linarith only [this, hc2]

  · -- clause 5: the box-trace arcs near the cutting plane
    intro N γa ηa ma hηapos hmapos hγaC hγaH hγaβ hcover
    have hκ_pos' : η / 3 ≤ inner ℝ n e := by rw [real_inner_comm]; exact hκ_pos
    have h2harcE : 2 * h ≤ arcE := by
      rw [hhdef]
      have h1 : τ ≤ arcE / (384 * s) := by
        have hY : I ≤ arcE / (96 * s) := by rw [← hY2def]; exact hIY2
        have h4 : (arcE / (96 * s)) / 4 = arcE / (384 * s) := by
          field_simp [ne_of_gt hs, ne_of_gt harcE] <;> ring
        have h5 : τ ≤ (arcE / (96 * s)) / 4 := by linarith only [hτ_I, hY]
        rw [h4] at h5
        exact h5
      have h3 : 12 * s * τ ≤ arcE / 32 := by
        have h := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 12 * s)
        have h4 : arcE / (384 * s) * (12 * s) = arcE / 32 := by
          field_simp [ne_of_gt hs, ne_of_gt harcE] <;> ring
        rw [h4] at h
        linarith only [h]
      linarith only [h3, harcE]
    have hcommon : ∀ k : Fin N, (∃ d ∈ D,
        deriv (γa k) 0 - Work.BoxShrink.shiftVσ σ 1 = d) ∧
        (∀ t : ℝ, t ∈ Set.Ioo (-ηa) ηa → |t| ≤ arcE →
          ‖deriv (γa k) t‖ ≤ arcM ∧ ‖deriv (γa k) t - deriv (γa k) 0‖ ≤ arcL * |t| ∧
          (deriv (γa k) 0 = Work.BoxShrink.shiftVσ σ 1 →
            ‖deriv (γa k) t - deriv (γa k) 0‖ ≤ arcQ * t ^ 2)) := by
      intro k
      obtain ⟨i, hi2, ev, hev, β, hβC, hβspec⟩ := hγaβ k
      exact harc (γa k) ηa i ev β hηapos hi2 hev (hγaC k) (hγaH k) hβC hβspec
    refine ⟨?_, ?_⟩
    · intro k t htIoo ht2h nn hnn1 hnnnear
      obtain ⟨⟨d, hdDmem, hdval⟩, hbd⟩ := hcommon k
      have htarcE : |t| ≤ arcE := le_trans ht2h h2harcE
      obtain ⟨hbdM, hbdL, hbdQ⟩ := hbd t htIoo htarcE
      have hdecomp : inner ℝ nn (deriv (γa k) t)
          = inner ℝ n (deriv (γa k) 0) + inner ℝ n (deriv (γa k) t - deriv (γa k) 0)
            + inner ℝ (nn - n) (deriv (γa k) t) := by
        rw [inner_sub_left, inner_sub_right]
        ring
      have hpertt : |inner ℝ (nn - n) (deriv (γa k) t)| ≤ ρ * ‖deriv (γa k) t‖ := by
        calc |inner ℝ (nn - n) (deriv (γa k) t)| ≤ ‖nn - n‖ * ‖deriv (γa k) t‖ :=
              abs_real_inner_le_norm _ _
          _ ≤ ρ * ‖deriv (γa k) t‖ :=
              mul_le_mul_of_nonneg_right (le_of_lt hnnnear) (norm_nonneg _)
      have hρbd : ρ * ‖deriv (γa k) t‖ ≤ η / 24 := by
        have hρ3 : ρ ≤ τ / (144 * (arcM + 2)) := by
          rw [hρdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
        have hτ6 : τ ≤ 6 * η := by rw [hη]; linarith only [hτ_I]
        have h5 : arcM / (144 * (arcM + 2)) ≤ 1 / 144 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith only [harcM]
        calc ρ * ‖deriv (γa k) t‖ ≤ (τ / (144 * (arcM + 2))) * arcM :=
              mul_le_mul hρ3 hbdM (norm_nonneg _) (by positivity)
          _ = τ * (arcM / (144 * (arcM + 2))) := by ring
          _ ≤ (6 * η) * (1 / 144) := mul_le_mul hτ6 h5 (by positivity) (by positivity)
          _ = η / 24 := by ring
      have hcAlow : 96 * I ≤ cA := by
        have h3 : I ≤ cA / 96 := by rw [← hY1def]; exact hIY1
        linarith only [h3]
      have hρbd' : ρ * ‖deriv (γa k) t‖ ≤ cA / 32 := by
        have h3 : η / 24 ≤ cA / 32 := by rw [hη]; nlinarith only [hcAlow, hIpos, hcApos]
        linarith only [hρbd, h3]
      by_cases hd0 : d = 0
      · -- the trace is vertical at the crossing: the quadratic bound of `FaceNoBend` applies
        have hder0 : deriv (γa k) 0 = e := by
          have h2 : deriv (γa k) 0 = Work.BoxShrink.shiftVσ σ 1 :=
            sub_eq_zero.mp (hdval.trans hd0)
          rw [hedef]
          exact h2
        have hquad : ‖deriv (γa k) t - deriv (γa k) 0‖ ≤ arcQ * t ^ 2 := hbdQ hder0
        have hinner0 : inner ℝ n (deriv (γa k) 0) = inner ℝ n e := by rw [hder0]
        have hmarg : inner ℝ n e - arcQ * t ^ 2 - ρ * ‖deriv (γa k) t‖
            ≤ |inner ℝ nn (deriv (γa k) t)| := by
          rw [hdecomp, hinner0]
          have h1 : |inner ℝ n (deriv (γa k) t - deriv (γa k) 0)| ≤ arcQ * t ^ 2 := by
            calc |inner ℝ n (deriv (γa k) t - deriv (γa k) 0)|
                  ≤ ‖n‖ * ‖deriv (γa k) t - deriv (γa k) 0‖ := abs_real_inner_le_norm _ _
              _ = ‖deriv (γa k) t - deriv (γa k) 0‖ := by rw [hn1, one_mul]
              _ ≤ arcQ * t ^ 2 := hquad
          have h4 := mg_abs_add_three (inner ℝ n e)
            (inner ℝ n (deriv (γa k) t - deriv (γa k) 0))
            (inner ℝ (nn - n) (deriv (γa k) t))
          have h5 : |inner ℝ n e| = inner ℝ n e :=
            abs_of_nonneg (by linarith only [hκ_pos', hη0])
          linarith only [h4, h5, h1, hpertt]
        have hA2 : arcQ * t ^ 2 ≤ η / 24 := by
          have ht2 : t ^ 2 ≤ (2 * h) ^ 2 := by
            have h1 := abs_le.mp ht2h
            have e1 : 0 ≤ 2 * h - t := by linarith only [h1.2]
            have e2 : 0 ≤ 2 * h + t := by linarith only [h1.1]
            nlinarith only [e1, e2]
          have h2h6 : (2 * h) ^ 2 = 144 * s ^ 2 * τ ^ 2 := by rw [hhdef]; ring
          rw [h2h6] at ht2
          have hsq : 144 * s ^ 2 * τ ^ 2 ≤ 9 * s ^ 2 * I ^ 2 := by
            have h1 : 4 * τ ≤ I := by linarith only [hτ_I]
            have h2 : (4 * τ) ^ 2 ≤ I ^ 2 := by nlinarith only [h1, hτ_pos, hIpos]
            nlinarith only [h2, hτ_pos, hs, hIpos]
          have hY7' : I ≤ 1 / (64800 * s ^ 2 * arcQ) := by rw [← hY7def]; exact hIY7
          have hmain : 9 * s ^ 2 * arcQ * I ^ 2 ≤ I / 7200 := by
            have hb : 9 * s ^ 2 * arcQ * I ≤ 9 * s ^ 2 * arcQ * (1 / (64800 * s ^ 2 * arcQ)) :=
              mul_le_mul_of_nonneg_left hY7' (by positivity)
            have hb2 : 9 * s ^ 2 * arcQ * (1 / (64800 * s ^ 2 * arcQ)) = 1 / 7200 := by
              field_simp [ne_of_gt hs, ne_of_gt harcQ] <;> ring
            rw [hb2] at hb
            calc 9 * s ^ 2 * arcQ * I ^ 2 = (9 * s ^ 2 * arcQ * I) * I := by ring
              _ ≤ (1 / 7200) * I := mul_le_mul_of_nonneg_right hb (le_of_lt hIpos)
              _ = I / 7200 := by ring
          have hη24 : η / 24 = I / 576 := by rw [hη]; ring
          have hstep1 : arcQ * t ^ 2 ≤ arcQ * (144 * s ^ 2 * τ ^ 2) :=
            mul_le_mul_of_nonneg_left ht2 (le_of_lt harcQ)
          have hstep2 : arcQ * (144 * s ^ 2 * τ ^ 2) ≤ arcQ * (9 * s ^ 2 * I ^ 2) :=
            mul_le_mul_of_nonneg_left hsq (le_of_lt harcQ)
          have hstep3 : arcQ * (9 * s ^ 2 * I ^ 2) = 9 * s ^ 2 * arcQ * I ^ 2 := by ring
          have hstep5 : I / 7200 ≤ η / 24 := by rw [hη24]; linarith only [hIpos]
          linarith only [hstep1, hstep2, hstep3, hmain, hstep5]
        have hpos : 0 < |inner ℝ nn (deriv (γa k) t)| := by
          have hA1 : η / 3 ≤ inner ℝ n e := hκ_pos'
          linarith only [hmarg, hA1, hA2, hρbd, hη0]
        exact abs_pos.mp hpos
      · -- the trace is not vertical at the crossing: the avoided direction gives the margin
        have hng_le : ‖ng‖ ≤ 3 / 2 := by linarith only [hng_high, hζ_le]
        have hng_ge : (1 : ℝ) / 2 ≤ ‖ng‖ := by linarith only [hng_low, hζ_le]
        have hcAm : cA ≤ |inner ℝ Ñ₀ d| := hcAle d hdDmem hd0
        have hMd0 : ‖d‖ ≤ Md := hMdge d hdDmem
        have hder0 : deriv (γa k) 0 = e + d := by
          have h2 : deriv (γa k) 0 = Work.BoxShrink.shiftVσ σ 1 + d :=
            sub_eq_iff_eq_add'.mp hdval
          rw [hedef]
          exact h2
        have hed0 : inner ℝ e d = 0 := by rw [hedef]; exact hDperp d hdDmem
        have hn0d : inner ℝ n₀ d = Real.sqrt (1 - η ^ 2) * inner ℝ Ñ₀ d := by
          rw [hn₀def, inner_add_left, real_inner_smul_left, real_inner_smul_left,
            hed0, mul_zero, zero_add]
        have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt (1 - η ^ 2) := by
          rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
          apply Real.sqrt_le_sqrt
          nlinarith only [hη_le, hη0]
        have hA : cA / 2 ≤ |inner ℝ n₀ d| := by
          rw [hn0d, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
          calc cA / 2 = (1 / 2) * cA := by ring
            _ ≤ Real.sqrt (1 - η ^ 2) * |inner ℝ Ñ₀ d| :=
                mul_le_mul hsqrt hcAm (le_of_lt hcApos) (Real.sqrt_nonneg _)
        have hB : |inner ℝ n₀ d| - ζ * Md ≤ |inner ℝ ng d| := by
          have h3 : |inner ℝ ng d - inner ℝ n₀ d| ≤ ‖ng - n₀‖ * ‖d‖ := by
            rw [← inner_sub_left]
            exact abs_real_inner_le_norm _ _
          have h4 : ‖ng - n₀‖ * ‖d‖ ≤ ζ * Md :=
            mul_le_mul (le_of_lt hngbd) hMd0 (norm_nonneg _) (le_of_lt hζ0)
          have hh := abs_sub_abs_le_abs_sub (inner ℝ n₀ d) (inner ℝ ng d)
          rw [abs_sub_comm (inner ℝ n₀ d) (inner ℝ ng d)] at hh
          linarith only [hh, h3, h4]
        have hζMd : ζ * Md ≤ cA / 8 := by
          have h1 : I ≤ cA / (96 * Md) := by rw [← hY5def]; exact hIY5
          have h2 : I * Md ≤ cA / 96 := by
            have h := mul_le_mul_of_nonneg_right h1 (le_of_lt hMdpos)
            have h3 : cA / (96 * Md) * Md = cA / 96 := by
              field_simp [ne_of_gt hMdpos] <;> ring
            rwa [h3] at h
          have h4 : ζ * Md = I * Md / 48 := by rw [hζ]; ring
          have h5 : I * Md / 48 ≤ cA / (96 * 48) := by linarith only [h2]
          have h6 : cA / (96 * 48) ≤ cA / 8 := by
            rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 96 * 48) (by norm_num : (0 : ℝ) < 8)]
            nlinarith only [hcApos]
          linarith only [h4, h5, h6]
        have hC : cA / 4 ≤ |inner ℝ ng d| := by linarith only [hA, hB, hζMd, hcApos]
        have hD4 : cA / 6 ≤ |inner ℝ n d| := by
          have hunit : inner ℝ n d = (‖ng‖)⁻¹ * inner ℝ ng d := by rw [hndef, inner_unitDir]
          rw [hunit, abs_mul, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
          have h4 : (3 / 2 : ℝ)⁻¹ ≤ (‖ng‖)⁻¹ := by
            have hh := one_div_le_one_div_of_le (by linarith only [hng_ge]) hng_le
            simpa [one_div] using hh
          calc cA / 6 = (3 / 2 : ℝ)⁻¹ * (cA / 4) := by
                rw [show (3 / 2 : ℝ)⁻¹ = 2 / 3 by norm_num]; ring
            _ ≤ (‖ng‖)⁻¹ * |inner ℝ ng d| :=
                mul_le_mul h4 hC (by positivity) (inv_nonneg.mpr (norm_nonneg _))
        have hE : cA / 8 ≤ |inner ℝ n (e + d)| := by
          have h1 : |inner ℝ n e| ≤ 3 * η := by
            rw [abs_of_nonneg (by linarith only [hκ_pos', hη0]), real_inner_comm]
            exact hκ_le
          have h2 : 3 * η ≤ cA / 768 := by
            have h3 : I ≤ cA / 96 := by rw [← hY1def]; exact hIY1
            rw [hη]; linarith only [h3]
          have h3 : |inner ℝ n d| - |inner ℝ n e| ≤ |inner ℝ n (e + d)| := by
            have hh : inner ℝ n (e + d) = inner ℝ n d + inner ℝ n e := by
              rw [inner_add_right]; ring
            rw [hh]
            exact mg_le_abs_add (inner ℝ n d) (inner ℝ n e)
          linarith only [h3, hD4, h1, h2, hcApos]
        have hinner0 : inner ℝ n (deriv (γa k) 0) = inner ℝ n (e + d) := by rw [hder0]
        have hmarg : cA / 8 - arcL * |t| - ρ * ‖deriv (γa k) t‖
            ≤ |inner ℝ nn (deriv (γa k) t)| := by
          rw [hdecomp, hinner0]
          have h1 : |inner ℝ n (deriv (γa k) t - deriv (γa k) 0)| ≤ arcL * |t| := by
            calc |inner ℝ n (deriv (γa k) t - deriv (γa k) 0)|
                  ≤ ‖n‖ * ‖deriv (γa k) t - deriv (γa k) 0‖ := abs_real_inner_le_norm _ _
              _ = ‖deriv (γa k) t - deriv (γa k) 0‖ := by rw [hn1, one_mul]
              _ ≤ arcL * |t| := hbdL
          have h4 := mg_abs_add_three (inner ℝ n (e + d))
            (inner ℝ n (deriv (γa k) t - deriv (γa k) 0))
            (inner ℝ (nn - n) (deriv (γa k) t))
          linarith only [h4, hE, h1, hpertt]
        have hA1 : arcL * |t| ≤ cA / 32 := by
          have hτs : τ ≤ cA / (384 * s * arcL) := by
            have h3 : I ≤ cA / (96 * s * arcL) := by rw [← hY4def]; exact hIY4
            have h4 : cA / (96 * s * arcL) / 4 = cA / (384 * s * arcL) := by
              field_simp [ne_of_gt hs, ne_of_gt harcL, ne_of_gt hcApos] <;> ring
            linarith only [hτ_I, h3, h4]
          have h1 : arcL * (12 * s * τ) ≤ arcL * (12 * s * (cA / (384 * s * arcL))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hτs (by positivity)) (le_of_lt harcL)
          have h2 : arcL * (12 * s * (cA / (384 * s * arcL))) = cA / 32 := by
            field_simp [ne_of_gt hs, ne_of_gt harcL, ne_of_gt hcApos] <;> ring
          have h3 : arcL * |t| ≤ arcL * (2 * h) := mul_le_mul_of_nonneg_left ht2h (le_of_lt harcL)
          have h4 : arcL * (2 * h) = arcL * (12 * s * τ) := by rw [hhdef]; ring
          linarith only [h1, h2, h3, h4]
        have hpos : 0 < |inner ℝ nn (deriv (γa k) t)| := by
          linarith only [hmarg, hA1, hρbd', hcApos]
        exact abs_pos.mp hpos
    · intro k t htIoo ht2h
      obtain ⟨⟨d, hdDmem, hdval⟩, hbd⟩ := hcommon k
      have htarcE : |t| ≤ arcE := le_trans ht2h h2harcE
      obtain ⟨hbdM, hbdL, hbdQ⟩ := hbd t htIoo htarcE
      obtain ⟨i, hi2, ev, hev, β, hβC, hβspec⟩ := hγaβ k
      have hdiff : DifferentiableAt ℝ (γa k) t := by
        have hIcc : Set.Icc (-ηa) ηa ∈ 𝓝 t :=
          Filter.mem_of_superset (isOpen_Ioo.mem_nhds htIoo)
            (fun r hr => ⟨le_of_lt hr.1, le_of_lt hr.2⟩)
        exact ((hγaC k).contDiffAt hIcc).differentiableAt (by norm_num)
      have hcoord : (deriv (γa k) t) (σ 2) = 1 := by
        have h1 : deriv (fun r : ℝ => (γa k r) (σ 2)) t = (deriv (γa k) t) (σ 2) := by
          have h2 : (fun r : ℝ => (γa k r) (σ 2))
              = fun r : ℝ => inner ℝ (unitCoord σ 2) (γa k r) := by
            funext r; rw [inner_unitCoord]
          rw [h2, deriv_inner_apply ℝ (differentiableAt_const _) hdiff, inner_unitCoord]
          simp
        rw [← h1]
        have hEv : (fun r : ℝ => (γa k r) (σ 2)) =ᶠ[𝓝 t] fun r : ℝ => c (σ 2) + u + r := by
          filter_upwards [isOpen_Ioo.mem_nhds htIoo] with r hr
          exact hγaH k r ⟨le_of_lt hr.1, le_of_lt hr.2⟩
        rw [Filter.EventuallyEq.deriv_eq hEv]
        simp
      have hinner_e : inner ℝ e (deriv (γa k) t) = 1 := by
        rw [hedef, inner_shiftVσ_one]
        exact hcoord
      have hee : inner ℝ e e = 1 := by
        rw [real_inner_self_eq_norm_sq, he1, one_pow]
      have hw : inner ℝ e (deriv (γa k) t - e) = 0 := by
        rw [inner_sub_right, hinner_e, hee, sub_self]
      have hve : 1 - τ ≤ inner ℝ v e := by
        have h2 : inner ℝ v e - 1 = inner ℝ (v - e) e := by
          rw [inner_sub_left, hee] <;> ring
        have h3 : |inner ℝ (v - e) e| ≤ τ := by
          calc |inner ℝ (v - e) e| ≤ ‖v - e‖ * ‖e‖ := abs_real_inner_le_norm _ _
            _ = τ := by rw [he1, mul_one, hτdef]
        have h4 : |inner ℝ v e - 1| ≤ τ := by rw [h2]; exact h3
        linarith only [(abs_le.mp h4).1]
      have hvρ : |inner ℝ v (deriv (γa k) t - e)| ≤ τ * ‖deriv (γa k) t - e‖ := by
        have hsplit : inner ℝ v (deriv (γa k) t - e)
            = inner ℝ e (deriv (γa k) t - e)
              + inner ℝ (v - e) (deriv (γa k) t - e) := by
          conv_lhs => rw [show v = e + (v - e) by abel]
          rw [inner_add_left]
        rw [hsplit, hw, zero_add]
        calc |inner ℝ (v - e) (deriv (γa k) t - e)|
              ≤ ‖v - e‖ * ‖deriv (γa k) t - e‖ := abs_real_inner_le_norm _ _
          _ = τ * ‖deriv (γa k) t - e‖ := by rw [hτdef]
      have hbdw : ‖deriv (γa k) t - e‖ ≤ arcM + 1 := by
        calc ‖deriv (γa k) t - e‖ ≤ ‖deriv (γa k) t‖ + ‖e‖ := norm_sub_le _ _
          _ ≤ arcM + 1 := by rw [he1]; linarith only [hbdM]
      have hτ3 : τ * (arcM + 2) ≤ 1 / 32 := by
        have hY : I ≤ 1 / (8 * (arcM + 2)) := by rw [← hY3def]; exact hIY3
        have h2 : τ ≤ 1 / (32 * (arcM + 2)) := by
          have h3 : (1 / (8 * (arcM + 2))) / 4 = 1 / (32 * (arcM + 2)) := by
            field_simp <;> ring
          linarith only [hτ_I, hY, h3]
        have h4 : τ * (arcM + 2) ≤ (1 / (32 * (arcM + 2))) * (arcM + 2) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
        have h5 : (1 / (32 * (arcM + 2))) * (arcM + 2) = 1 / 32 := by
          field_simp <;> ring
        linarith only [h4, h5]
      have hfinal : inner ℝ v (deriv (γa k) t) ≥ 1 - τ * (arcM + 2) := by
        have h4 : inner ℝ v (deriv (γa k) t - e) ≥ -(τ * ‖deriv (γa k) t - e‖) := by
          have hh := neg_abs_le (inner ℝ v (deriv (γa k) t - e))
          linarith only [hh, hvρ]
        have h5 : τ * ‖deriv (γa k) t - e‖ ≤ τ * (arcM + 1) :=
          mul_le_mul_of_nonneg_left hbdw (le_of_lt hτ_pos)
        have h6 : inner ℝ v (deriv (γa k) t)
            = inner ℝ v e + inner ℝ v (deriv (γa k) t - e) := by
          conv_lhs => rw [show deriv (γa k) t = e + (deriv (γa k) t - e) by abel]
          rw [inner_add_right]
        rw [h6]
        linarith only [hve, h4, h5]
      linarith only [hfinal, hτ3]


/-- **The requested lemma.** -/
theorem noGraze_witness_gamma_noEdge
    (ψ : Submission.Diffeo) (K : LeanEval.KnotTheory.PardonDistortion.Knot) {r s u : ℝ}
    (hr : 0 < r) (hrs : r < s) (hu : |u| < Submission.eps * r)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3))
    (hcut : Work.Drive.Mono.CutTransverse K s c σ u)
    {εg δg θ' : ℝ} (hεg : 0 < εg) (hδg : 0 < δg) (hθ' : 0 < θ')
    (hnograz : ∀ v : LeanEval.KnotTheory.PardonDistortion.R3, ‖v‖ = 1 →
        ‖v - Work.BoxShrink.shiftVσ σ 1‖ < εg →
        ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
          deriv (fun r : ℝ => inner ℝ v (K.curve r)) t = 0 →
          δg ≤ |inner ℝ v (K.curve t) - (inner ℝ v c + u)|)
    (hnobend : ∀ t : ℝ, K.curve t ∈ closure (Submission.PBox s c σ) →
        (K.curve t) (σ 2) = c (σ 2) + u →
        Work.Drive.Mono.vertVel K (Work.BoxShrink.shiftVσ σ 1) t = 0 →
        Work.Drive.Mono.vertAcc K (Work.BoxShrink.shiftVσ σ 1) t = 0)
    (hX : Work.Drive.Mono.FaceCrossReg ψ c σ s u)
    (hFB : Work.Drive.Mono.FaceNoBend ψ c σ s u)
    (hedge : ∃ mE : ℝ, 0 < mE ∧ ∀ z : LeanEval.KnotTheory.PardonDistortion.R3,
        z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
        |z (σ 0) - c (σ 0)| = Submission.boxSide 0 * s →
        |z (σ 1) - c (σ 1)| = Submission.boxSide 1 * s →
        mE ≤ |z (σ 2) - (c (σ 2) + u)|) :
    ∃ (v n : LeanEval.KnotTheory.PardonDistortion.R3) (h ρ : ℝ),
      ‖v‖ = 1 ∧ ‖n‖ = 1 ∧ inner ℝ v n = 0 ∧ Work.Drive.Mono.Band.HeightGood ψ n ∧
      ‖v - Work.BoxShrink.shiftVσ σ 1‖ ≤ θ' ∧
      ‖v - Work.BoxShrink.shiftVσ σ 1‖ ≤ εg / 4 ∧
      0 < h ∧ 0 < ρ ∧
      2 * (‖v - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s)) < h ∧
      (∀ t : ℝ, Submission.boxNorm c σ (K.curve t) = s →
          h ≤ |inner ℝ v (K.curve t) - (inner ℝ v c + u)|) ∧
      (∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
          deriv (fun r : ℝ => inner ℝ v (K.curve r)) t = 0 →
          h ≤ |inner ℝ v (K.curve t) - (inner ℝ v c + u)|) ∧
      (∀ nn : LeanEval.KnotTheory.PardonDistortion.R3, ‖nn‖ = 1 → ‖nn - n‖ < ρ → ∀ t : ℝ,
          K.curve t ∈ Submission.PBox s c σ →
          |inner ℝ v (K.curve t) - (inner ℝ v c + u)| ≤ h →
          deriv (fun r : ℝ => inner ℝ nn (K.curve r)) t ≠ 0) ∧
      (∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
          |inner ℝ v (K.curve t) - (inner ℝ v c + u)| = h →
          deriv (fun r : ℝ => inner ℝ v (K.curve r)) t ≠ 0) ∧
      (∀ (N : ℕ) (γ : Fin N → ℝ → LeanEval.KnotTheory.PardonDistortion.R3) (η m : ℝ),
        0 < η → 0 < m →
        (∀ k, ContDiffOn ℝ 3 (γ k) (Set.Icc (-η) η)) →
        (∀ k, ∀ t ∈ Set.Icc (-η) η, (γ k t) (σ 2) = c (σ 2) + u + t) →
        (∀ k, ∃ i : Fin 3, i ≠ 2 ∧ ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∃ β : ℝ → ℝ × ℝ,
          ContDiffOn ℝ 3 β (Set.Icc (-η) η) ∧ ∀ t ∈ Set.Icc (-η) η,
            Work.BoxShrink.Pinch.par ψ (β t) = γ k t ∧
            (γ k t) (σ i) = c (σ i) + ε * Submission.boxSide i * s) →
        (∀ z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier, Submission.boxNorm c σ z = s →
          |z (σ 2) - (c (σ 2) + u)| < m → (∀ j : Fin 3, j ≠ 2 → ∀ j' : Fin 3, j' ≠ 2 → j ≠ j' →
            ¬ (|z (σ j) - c (σ j)| = Submission.boxSide j * s ∧
               |z (σ j') - c (σ j')| = Submission.boxSide j' * s)) →
          ∃ k, ∃ t ∈ Set.Ioo (-η) η, z = γ k t) →
        (∀ k, ∀ t : ℝ, t ∈ Set.Ioo (-η) η → |t| ≤ 2 * h → ∀ nn : LeanEval.KnotTheory.PardonDistortion.R3,
          ‖nn‖ = 1 → ‖nn - n‖ < ρ → inner ℝ nn (deriv (γ k) t) ≠ 0) ∧
        (∀ k, ∀ t : ℝ, t ∈ Set.Ioo (-η) η → |t| ≤ 2 * h →
          (1 / 2 : ℝ) ≤ inner ℝ v (deriv (γ k) t))) := by
  have hs : 0 < s := lt_trans hr hrs
  obtain ⟨D, arcE, arcM, arcL, arcQ, hDperp, harcE, harcM, harcL, harcQ, harc⟩ :=
    Work.Drive.Mono.arcHeightKernel ψ hs c σ hX hFB
  exact noGraze_witness_arcs_noEdge ψ K hr hrs hu c σ hcut hεg hδg hθ' hnograz hnobend hX hFB hedge
    D arcE arcM arcL arcQ hDperp harcE harcM harcL harcQ harc

end

end Work.Drive.Mono

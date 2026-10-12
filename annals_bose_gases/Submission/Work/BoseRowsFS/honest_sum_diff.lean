import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowsFS.Defs
import Submission.Work.BoseRowsFS.honest_lattice_sum_diff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.honest_sum_diff`

FS §11's `IntKernel.sum_diff` row at the honest model, in the form the area's
`FINDING_session3.md` §2a prescribes: the lattice half of the row
(`Work.BoseRowsFS.honest_lattice_sum_diff`, the sharp `(R/ℓ)⁴` comparison for the *uncut*
difference kernel `W₁ − g₀` over an arbitrary finite set of nonzero integer labels) on the
part of the cube where the UV cut `ζ` is inactive, plus the explicit cut-tail hypothesis
`htail` on the part where `ζ` is active.

## Route

With `ℓ = ellH v μ`, `Λ = uvRad ℓ N`, `ζ k = uvCut fu Λ (kmom k)`, `W₁ = chat (W1fun v h ℓ)`,
`ĝ = chat (g₀ v h)`, the honest `W1 k = ζ k · W₁(k)` (`Hon.lean`'s `honE_W1_apply`), so

* `(ĝ k − W1 k)² ≤ 2(ĝ k − W₁ k)² + 2(1 − ζ k)²W₁(k)²`  (`sq_sub_mul_div_le`, the elementary
  two-square bound applied to `ĝ − ζW₁ = (ĝ − W₁) + (1 − ζ)W₁`);
* for the first summand: `honest_lattice_sum_diff` applied to the transfer of `PHset` along
  the injection `labVec N : Lab N → ℤ³` (`kmom k = kvec ℓ (labVec N k)`), giving
  `ℓ⁻³Σ ≤ Chl·a·(R/ℓ)⁴` — no cut enters, so the sharp `(R/ℓ)⁴` survives;
* for the second summand: `1 − ζ k` vanishes whenever `‖kmom k‖ ≤ Λ` (`LowCut.one`, via
  `uvCut_eq_one_of_norm_le`), so this sum runs over `{k ∈ PHset : Λ < ‖kmom k‖} ⊆` the cut
  tail of `htail`, where `(1 − ζ)²W₁² ≤ ĝ² + W₁²`.

`R ≤ ℓ` (needed by `honest_lattice_sum_diff`) follows from the régime row `R ≤ ℓ·chiR0`
because `chiR0 ≤ 1` (`Work.BoseFixR.Rb5Lin.chiR0_le_one`).

No `sorry`, no `axiom`.
-/

namespace Work.BoseRowsFS

open scoped Real BigOperators Topology
open MeasureTheory Metric

noncomputable section

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. Elementary pieces -/

/-- The two-square bound. -/
lemma two_sq_le (x y : ℝ) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  nlinarith [sq_nonneg (x - y)]

/-- `(a − ζb)² ≤ 2(a − b)² + 2(1 − ζ)²b²`. -/
lemma sq_sub_mul_le (a b ζ : ℝ) :
    (a - ζ * b) ^ 2 ≤ 2 * (a - b) ^ 2 + 2 * ((1 - ζ) ^ 2 * b ^ 2) := by
  have h := two_sq_le (a - b) ((1 - ζ) * b)
  have e2 : ((1 - ζ) * b) ^ 2 = (1 - ζ) ^ 2 * b ^ 2 := by ring
  rw [e2] at h
  calc (a - ζ * b) ^ 2 = ((a - b) + (1 - ζ) * b) ^ 2 := by ring
    _ ≤ 2 * (a - b) ^ 2 + 2 * ((1 - ζ) ^ 2 * b ^ 2) := h

/-- `(a − ζb)²/w ≤ 2(a − b)²/w + 2(1 − ζ)²b²/w` for `0 ≤ w`. -/
lemma sq_sub_mul_div_le (a b ζ w : ℝ) (hw : 0 ≤ w) :
    (a - ζ * b) ^ 2 / w ≤ 2 * ((a - b) ^ 2 / w) + 2 * ((1 - ζ) ^ 2 * b ^ 2 / w) := by
  have h := sq_sub_mul_le a b ζ
  calc (a - ζ * b) ^ 2 / w ≤ (2 * (a - b) ^ 2 + 2 * ((1 - ζ) ^ 2 * b ^ 2)) / w :=
        div_le_div_of_nonneg_right h hw
    _ = 2 * ((a - b) ^ 2 / w) + 2 * ((1 - ζ) ^ 2 * b ^ 2 / w) := by ring

/-- The UV cut is `1` on the ball of radius `Λ` (for every `Λ`, including `Λ ≤ 0`). -/
lemma uvCut_eq_one_of_norm_le {fu : Work.BoseBoxFix.LowCut} {Λ : ℝ}
    {p : EuclideanSpace ℝ (Fin 3)} (h : ‖p‖ ≤ Λ) :
    Work.BoseBoxFock.uvCut fu Λ p = 1 := by
  rw [Work.BoseBoxFock.uvCut]
  refine fu.one _ ?_
  rcases lt_trichotomy Λ 0 with hΛ | hΛ | hΛ
  · have hp0 : ‖p‖ = 0 := le_antisymm (le_trans h hΛ.le) (norm_nonneg _)
    rw [hp0, zero_div]
    norm_num
  · rw [hΛ, div_zero]
    norm_num
  · rw [div_le_one hΛ]
    exact h

/-! ## 2. The row -/

theorem honest_sum_diff {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hdecayW : ∀ ℓ : ℝ, 1 ≤ ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 →
      ∀ p : EuclideanSpace ℝ (Fin 3),
        |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p| * (1 + ‖p‖) ^ 2
          ≤ Cw * _root_.BoseGases.a v)
    (hdecayg : ∀ ℓ : ℝ, 1 ≤ ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 →
      ∀ p : EuclideanSpace ℝ (Fin 3),
        |Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p| * (1 + ‖p‖) ^ 2
          ≤ Cw * _root_.BoseGases.a v)
    (Ng : ℝ → ℕ) (εg : ℝ) (hεg : 0 < εg)
    (hrég : ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ εg →
      1 ≤ Work.BoseBoxFock.ellH v μ
        ∧ R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0)
    (htail : ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ),
      (∀ μ, Ng μ ≤ (HM μ).N) → ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ εg →
        (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
            ∑ k ∈ (Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
                (fun k => Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N
                  < ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖),
              (Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
                  ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k) ^ 2
                + Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
                    ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k) ^ 2)
                / ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ ^ 2
          ≤ Cw ^ 2 * _root_.BoseGases.a v
              * (R / Work.BoseBoxFock.ellH v μ) ^ 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ),
      (∀ μ, Ng μ ≤ (HM μ).N) → ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ εg →
      (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
          ∑ k ∈ (Work.BoseRowsFS.honF v h fc fu HM μ).PHset
              (Work.BoseRowsFS.honE v h fc fu HM μ),
            (Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
                ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k)
              - (Work.BoseRowsFS.honE v h fc fu HM μ).W1 k) ^ 2
              / ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ ^ 2
        ≤ C * (Work.BoseRowsFS.honE v h fc fu HM μ).aScat
            * (R / (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ 4 := by
  obtain ⟨Chl, _hChlnn, hhl⟩ :=
    honest_lattice_sum_diff (h := h) R hR hav hv_nonneg hvrad hv_supp
  refine ⟨2 * Chl + 2 * Cw ^ 2, by positivity, ?_⟩
  intro HM hN μ hμ hε
  obtain ⟨hℓ1, hRℓchi⟩ := hrég μ hμ hε
  have hRℓH : R ≤ Work.BoseBoxFock.ellH v μ :=
    calc R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0 := hRℓchi
      _ ≤ Work.BoseBoxFock.ellH v μ * 1 :=
          mul_le_mul_of_nonneg_left Work.BoseFixR.Rb5Lin.chiR0_le_one
            (Work.BoseBoxFock.ellH_pos v μ).le
      _ = Work.BoseBoxFock.ellH v μ := mul_one _
  have hell : (Work.BoseRowsFS.honE v h fc fu HM μ).ell = Work.BoseBoxFock.ellH v μ :=
    honE_ell v h fc fu HM μ hμ hav
  have haS : (Work.BoseRowsFS.honE v h fc fu HM μ).aScat = _root_.BoseGases.a v := rfl
  -- ### the vocabulary
  set ℓ : ℝ := Work.BoseBoxFock.ellH v μ with hℓdef
  set Λ : ℝ := Work.BoseBoxFock.uvRad ℓ (HM μ).N with hΛdef
  set KM : Work.BoseBoxFock.Lab (HM μ).N → EuclideanSpace ℝ (Fin 3) :=
    (Work.BoseRowsFS.honF v h fc fu HM μ).kmom with hKMdef
  set G : EuclideanSpace ℝ (Fin 3) → ℝ :=
    Work.BoseFixR.chat (Submission.BoseGases.g0 v h) with hGdef
  set W : EuclideanSpace ℝ (Fin 3) → ℝ :=
    Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) with hWdef
  set P : Finset (Work.BoseBoxFock.Lab (HM μ).N) :=
    (Work.BoseRowsFS.honF v h fc fu HM μ).PHset (Work.BoseRowsFS.honE v h fc fu HM μ)
    with hPdef
  have hℓpos : 0 < ℓ := by rw [hℓdef]; exact Work.BoseBoxFock.ellH_pos v μ
  -- ### the honest `W1` is the cut times the uncut transform
  have hW1app : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
      (Work.BoseRowsFS.honE v h fc fu HM μ).W1 k
        = Work.BoseBoxFock.uvCut fu Λ (KM k) * W (KM k) := by
    intro k
    rw [hΛdef, hℓdef, hKMdef, hWdef]
    exact honE_W1_apply v h fc fu HM μ hμ hav k
  -- ### the elementary split
  have hsplit : (∑ k ∈ P, (G (KM k)
        - (Work.BoseRowsFS.honE v h fc fu HM μ).W1 k) ^ 2 / ‖KM k‖ ^ 2)
      ≤ 2 * (∑ k ∈ P, (G (KM k) - W (KM k)) ^ 2 / ‖KM k‖ ^ 2)
        + 2 * (∑ k ∈ P, (1 - Work.BoseBoxFock.uvCut fu Λ (KM k)) ^ 2
            * (W (KM k)) ^ 2 / ‖KM k‖ ^ 2) := by
    have hpt : ∀ k ∈ P, (G (KM k)
          - (Work.BoseRowsFS.honE v h fc fu HM μ).W1 k) ^ 2 / ‖KM k‖ ^ 2
        ≤ 2 * ((G (KM k) - W (KM k)) ^ 2 / ‖KM k‖ ^ 2)
          + 2 * ((1 - Work.BoseBoxFock.uvCut fu Λ (KM k)) ^ 2
              * (W (KM k)) ^ 2 / ‖KM k‖ ^ 2) := by
      intro k _
      rw [hW1app k]
      exact sq_sub_mul_div_le _ _ _ _ (sq_nonneg _)
    calc (∑ k ∈ P, (G (KM k)
          - (Work.BoseRowsFS.honE v h fc fu HM μ).W1 k) ^ 2 / ‖KM k‖ ^ 2)
        ≤ ∑ k ∈ P, (2 * ((G (KM k) - W (KM k)) ^ 2 / ‖KM k‖ ^ 2)
            + 2 * ((1 - Work.BoseBoxFock.uvCut fu Λ (KM k)) ^ 2
                * (W (KM k)) ^ 2 / ‖KM k‖ ^ 2)) := Finset.sum_le_sum hpt
      _ = 2 * (∑ k ∈ P, (G (KM k) - W (KM k)) ^ 2 / ‖KM k‖ ^ 2)
            + 2 * (∑ k ∈ P, (1 - Work.BoseBoxFock.uvCut fu Λ (KM k)) ^ 2
                * (W (KM k)) ^ 2 / ‖KM k‖ ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- ### the uncut part, by the lattice comparison
  have hB : ℓ ^ (-(3 : ℝ)) * (∑ k ∈ P, (G (KM k) - W (KM k)) ^ 2 / ‖KM k‖ ^ 2)
      ≤ Chl * _root_.BoseGases.a v * (R / ℓ) ^ 4 := by
    set S : Finset (Fin 3 → ℤ) := P.image (Work.BoseBoxFock.labVec (HM μ).N) with hSdef
    have hSne : ∀ m ∈ S, m ≠ 0 := by
      intro m hm
      rw [hSdef] at hm
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
      have hkexc : k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N) := by
        rw [hPdef] at hk
        exact (Finset.mem_filter.mp
          (by simpa only [Work.BoseB7.FockData.PHset] using hk)).1
      have hk0 : k ≠ 0 := (Finset.mem_erase.mp hkexc).1
      intro hcon
      exact hk0 (Work.BoseFixR.labVec_injective (HM μ).N
        (by rw [hcon, Work.BoseRowsFS.labVec_zero]))
    have hkvec : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        KM k = kvec ℓ (Work.BoseBoxFock.labVec (HM μ).N k) := by
      intro k
      rw [hKMdef, hℓdef]
      have h1 : (Work.BoseRowsFS.honF v h fc fu HM μ).kmom k
          = Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N k := rfl
      rw [h1, Work.BoseRowsFS.kmomLab_eq]
      rfl
    have hsum : (∑ k ∈ P, (G (KM k) - W (KM k)) ^ 2 / ‖KM k‖ ^ 2)
        = ∑ m ∈ S, (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (kvec ℓ m)
            - Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (kvec ℓ m)) ^ 2
            / ‖kvec ℓ m‖ ^ 2 := by
      rw [hSdef,
        Finset.sum_image (s := P) (g := Work.BoseBoxFock.labVec (HM μ).N)
          (f := fun m => (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (kvec ℓ m)
            - Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (kvec ℓ m)) ^ 2
            / ‖kvec ℓ m‖ ^ 2)
          (Work.BoseFixR.labVec_injective (HM μ).N).injOn]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hkvec k, hGdef, hWdef]
      ring
    rw [hsum]
    exact hhl ℓ hℓ1 hRℓH hRℓchi S hSne
  -- ### the cut tail
  have hC1 : ℓ ^ (-(3 : ℝ)) * (∑ k ∈ P, (1 - Work.BoseBoxFock.uvCut fu Λ (KM k)) ^ 2
        * (W (KM k)) ^ 2 / ‖KM k‖ ^ 2)
      ≤ Cw ^ 2 * _root_.BoseGases.a v * (R / ℓ) ^ 4 := by
    have htail' : (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
        ∑ k ∈ (Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
            (fun k => Λ < ‖KM k‖),
          (G (KM k) ^ 2 + W (KM k) ^ 2) / ‖KM k‖ ^ 2
        ≤ Cw ^ 2 * _root_.BoseGases.a v * (R / ℓ) ^ 4 := by
      simpa only [← hℓdef, ← hΛdef, ← hKMdef, ← hGdef, ← hWdef]
        using htail HM hN μ hμ hε
    rw [hell] at htail'
    have hle : (∑ k ∈ P, (1 - Work.BoseBoxFock.uvCut fu Λ (KM k)) ^ 2
          * (W (KM k)) ^ 2 / ‖KM k‖ ^ 2)
        ≤ ∑ k ∈ (Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
            (fun k => Λ < ‖KM k‖),
          (G (KM k) ^ 2 + W (KM k) ^ 2) / ‖KM k‖ ^ 2 := by
      have hsub : P.filter (fun k => Λ < ‖KM k‖)
          ⊆ (Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
              (fun k => Λ < ‖KM k‖) := by
        intro k hk
        rw [Finset.mem_filter] at hk ⊢
        refine ⟨?_, hk.2⟩
        have hkP : k ∈ P := hk.1
        rw [hPdef] at hkP
        exact (Finset.mem_filter.mp
          (by simpa only [Work.BoseB7.FockData.PHset] using hkP)).1
      have hpt : ∀ k ∈ P, (1 - Work.BoseBoxFock.uvCut fu Λ (KM k)) ^ 2
            * (W (KM k)) ^ 2 / ‖KM k‖ ^ 2
          ≤ (if Λ < ‖KM k‖ then (G (KM k) ^ 2 + W (KM k) ^ 2) / ‖KM k‖ ^ 2
              else 0) := by
        intro k _
        by_cases hk : Λ < ‖KM k‖
        · rw [if_pos hk]
          have hζ0 : 0 ≤ Work.BoseBoxFock.uvCut fu Λ (KM k) := fu.nonneg _
          have hζ1 : Work.BoseBoxFock.uvCut fu Λ (KM k) ≤ 1 := fu.le_one _
          have h2 : (1 - Work.BoseBoxFock.uvCut fu Λ (KM k)) ^ 2 ≤ 1 := by nlinarith
          have h3 : (1 - Work.BoseBoxFock.uvCut fu Λ (KM k)) ^ 2 * (W (KM k)) ^ 2
              ≤ G (KM k) ^ 2 + W (KM k) ^ 2 := by
            calc (1 - Work.BoseBoxFock.uvCut fu Λ (KM k)) ^ 2 * (W (KM k)) ^ 2
                ≤ 1 * (W (KM k)) ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
              _ = (W (KM k)) ^ 2 := one_mul _
              _ ≤ G (KM k) ^ 2 + W (KM k) ^ 2 := by linarith [sq_nonneg (G (KM k))]
          exact div_le_div_of_nonneg_right h3 (sq_nonneg _)
        · rw [if_neg hk]
          have hζ : Work.BoseBoxFock.uvCut fu Λ (KM k) = 1 :=
            uvCut_eq_one_of_norm_le (not_lt.mp hk)
          rw [hζ]
          simp
      calc (∑ k ∈ P, (1 - Work.BoseBoxFock.uvCut fu Λ (KM k)) ^ 2
            * (W (KM k)) ^ 2 / ‖KM k‖ ^ 2)
          ≤ ∑ k ∈ P, (if Λ < ‖KM k‖ then
              (G (KM k) ^ 2 + W (KM k) ^ 2) / ‖KM k‖ ^ 2 else 0) :=
            Finset.sum_le_sum hpt
        _ = ∑ k ∈ P.filter (fun k => Λ < ‖KM k‖),
              (G (KM k) ^ 2 + W (KM k) ^ 2) / ‖KM k‖ ^ 2 :=
            (Finset.sum_filter (fun k => Λ < ‖KM k‖)
              (fun k => (G (KM k) ^ 2 + W (KM k) ^ 2) / ‖KM k‖ ^ 2)).symm
        _ ≤ ∑ k ∈ (Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
              (fun k => Λ < ‖KM k‖),
              (G (KM k) ^ 2 + W (KM k) ^ 2) / ‖KM k‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
    calc ℓ ^ (-(3 : ℝ)) * (∑ k ∈ P, (1 - Work.BoseBoxFock.uvCut fu Λ (KM k)) ^ 2
          * (W (KM k)) ^ 2 / ‖KM k‖ ^ 2)
        ≤ ℓ ^ (-(3 : ℝ)) *
            ∑ k ∈ (Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
              (fun k => Λ < ‖KM k‖),
              (G (KM k) ^ 2 + W (KM k) ^ 2) / ‖KM k‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hℓpos.le _)
      _ ≤ Cw ^ 2 * _root_.BoseGases.a v * (R / ℓ) ^ 4 := htail'
  -- ### assembly
  have key : ℓ ^ (-(3 : ℝ)) * (∑ k ∈ P, (G (KM k)
        - (Work.BoseRowsFS.honE v h fc fu HM μ).W1 k) ^ 2 / ‖KM k‖ ^ 2)
      ≤ (2 * Chl + 2 * Cw ^ 2) * _root_.BoseGases.a v * (R / ℓ) ^ 4 := by
    calc ℓ ^ (-(3 : ℝ)) * (∑ k ∈ P, (G (KM k)
            - (Work.BoseRowsFS.honE v h fc fu HM μ).W1 k) ^ 2 / ‖KM k‖ ^ 2)
        ≤ ℓ ^ (-(3 : ℝ)) * (2 * (∑ k ∈ P, (G (KM k) - W (KM k)) ^ 2 / ‖KM k‖ ^ 2)
            + 2 * (∑ k ∈ P, (1 - Work.BoseBoxFock.uvCut fu Λ (KM k)) ^ 2
                * (W (KM k)) ^ 2 / ‖KM k‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hsplit (Real.rpow_nonneg hℓpos.le _)
      _ = 2 * (ℓ ^ (-(3 : ℝ)) * (∑ k ∈ P, (G (KM k) - W (KM k)) ^ 2 / ‖KM k‖ ^ 2))
            + 2 * (ℓ ^ (-(3 : ℝ)) * (∑ k ∈ P,
                (1 - Work.BoseBoxFock.uvCut fu Λ (KM k)) ^ 2
                  * (W (KM k)) ^ 2 / ‖KM k‖ ^ 2)) := by ring
      _ ≤ 2 * (Chl * _root_.BoseGases.a v * (R / ℓ) ^ 4)
            + 2 * (Cw ^ 2 * _root_.BoseGases.a v * (R / ℓ) ^ 4) := by
          linarith [hB, hC1]
      _ = (2 * Chl + 2 * Cw ^ 2) * _root_.BoseGases.a v * (R / ℓ) ^ 4 := by ring
  rw [hell, haS]
  exact key

end

end Work.BoseRowsFS

import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowsFS.honest_sum_diff
import Submission.Work.BoseRowsL.Exists
import Submission.Work.BoseRowsL.Glue.honTailL_to_excitedTail
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.Glue.sumDiff_of_interfaceL`

The `IntKernel.sum_diff` row (FS §11) at the **decay-free** interface `HonestInterfaceL`.

The row is the `ℓ⁻³`-normalised comparison of the honest `W1` (the UV-cut `Ŵ₁`) with the
unprojected `ĝ` over the set `PHset` of modes admitted by the pseudopotential condition, and it
is the same statement as `Work.BoseRowsFS.honest_sum_diff` — but `honest_sum_diff` asks for FS's
two *decay* rows `|Ŵ₁(p)|(1+‖p‖)² ≤ Cw·a v`, which are **false** for a merely `L¹` compactly
supported `v` (`FINDING_omega_lattice_honest_ng.md`; the decay-free replacement is the sup row
`bndW` of `HonestInterfaceL`).  In fact the proof of `honest_sum_diff` never uses them: the row
rests on

* the lattice comparison `Work.BoseRowsFS.honest_lattice_sum_diff` (decay-free, for the
  difference kernel `W₁ − g₀` over an arbitrary finite set of nonzero lattice labels);
* the UV-cut tail row `tailL` of `HonestInterfaceL` (the lattice tail beyond `uvRad`), and
* the régime rows of `GateThresholds` (`1 ≤ ℓ`, `R ≤ ℓ·chiR0`);

so the same argument applies verbatim at `HonestInterfaceL`.  Route:

* `ĝ k − W1 k = (ĝ k − Ŵ₁ k) + (1 − ζ k)·Ŵ₁ k`, hence
  `(ĝ k − W1 k)²/‖k‖² ≤ 2(ĝ k − Ŵ₁ k)²/‖k‖² + 2(1 − ζ k)²Ŵ₁(k)²/‖k‖²`;
* first summand: reindex `PHset` along the injection `labVec N : Lab N → ℤ³`
  (`kmom k = ℓ⁻¹ • vec (labVec N k)`) and apply `honest_lattice_sum_diff`;
* second summand: `1 − ζ` vanishes for `‖k‖ ≤ Λ`, so the sum lives on the cut tail, where
  `(1 − ζ)²Ŵ₁² ≤ ĝ² + Ŵ₁²`, and `tailL` bounds it.

No `sorry`, no `axiom`.
-/

namespace Work.BoseRowsL.Glue

open scoped Real BigOperators Topology

noncomputable section

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem sumDiff_of_interfaceL {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hR : 0 < R) (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hthr : Work.BoseGateFS.GateThresholds v h fc fu R)
    (H : Work.BoseRowsL.HonestInterfaceL R hthr) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ),
      (∀ μ, H.Ng' μ ≤ (HM μ).N) →
      ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
      (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
          ∑ k ∈ (Work.BoseRowsFS.honF v h fc fu HM μ).PHset
              (Work.BoseRowsFS.honE v h fc fu HM μ),
            (Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
                ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k)
              - (Work.BoseRowsFS.honE v h fc fu HM μ).W1 k) ^ 2
              / ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ ^ 2
        ≤ C * (Work.BoseRowsFS.honE v h fc fu HM μ).aScat
            * (R / (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ 4 := by
  obtain ⟨Chl, hChlnn, hhl⟩ :=
    Work.BoseRowsFS.honest_lattice_sum_diff (h := h) R hR hav hv_nonneg hvrad hv_supp
  refine ⟨2 * Chl + 2 * H.Cw ^ 2, by nlinarith [hChlnn, sq_nonneg H.Cw], ?_⟩
  intro HM hN μ hμ hε
  -- ### the régime rows of `GateThresholds`
  obtain ⟨hℓ1, -, hRℓchi, -, -, -⟩ :=
    hthr.dil HM (fun ν => le_trans (H.Ng'_ge ν) (hN ν)) μ hμ hε
  have hRℓH : R ≤ Work.BoseBoxFock.ellH v μ :=
    calc R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0 := hRℓchi
      _ ≤ Work.BoseBoxFock.ellH v μ * 1 :=
          mul_le_mul_of_nonneg_left Work.BoseFixR.Rb5Lin.chiR0_le_one
            (Work.BoseBoxFock.ellH_pos v μ).le
      _ = Work.BoseBoxFock.ellH v μ := mul_one _
  have hell : (Work.BoseRowsFS.honE v h fc fu HM μ).ell = Work.BoseBoxFock.ellH v μ :=
    Work.BoseRowsFS.honE_ell v h fc fu HM μ hμ hav
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
    exact Work.BoseRowsFS.honE_W1_apply v h fc fu HM μ hμ hav k
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
      exact Work.BoseRowsFS.sq_sub_mul_div_le _ _ _ _ (sq_nonneg _)
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
        KM k = Work.BoseRowsFS.kvec ℓ (Work.BoseBoxFock.labVec (HM μ).N k) := by
      intro k
      rw [hKMdef, hℓdef]
      have h1 : (Work.BoseRowsFS.honF v h fc fu HM μ).kmom k
          = Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N k := rfl
      rw [h1, Work.BoseRowsFS.kmomLab_eq]
      rfl
    have hsum : (∑ k ∈ P, (G (KM k) - W (KM k)) ^ 2 / ‖KM k‖ ^ 2)
        = ∑ m ∈ S, (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (Work.BoseRowsFS.kvec ℓ m)
            - Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (Work.BoseRowsFS.kvec ℓ m)) ^ 2
            / ‖Work.BoseRowsFS.kvec ℓ m‖ ^ 2 := by
      rw [hSdef,
        Finset.sum_image (s := P) (g := Work.BoseBoxFock.labVec (HM μ).N)
          (f := fun m => (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)
              (Work.BoseRowsFS.kvec ℓ m)
            - Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (Work.BoseRowsFS.kvec ℓ m)) ^ 2
            / ‖Work.BoseRowsFS.kvec ℓ m‖ ^ 2)
          (Work.BoseFixR.labVec_injective (HM μ).N).injOn]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hkvec k, hGdef, hWdef]
      ring
    rw [hsum]
    exact hhl ℓ hℓ1 hRℓH hRℓchi S hSne
  -- ### the cut tail
  have hC1 : ℓ ^ (-(3 : ℝ)) * (∑ k ∈ P, (1 - Work.BoseBoxFock.uvCut fu Λ (KM k)) ^ 2
        * (W (KM k)) ^ 2 / ‖KM k‖ ^ 2)
      ≤ H.Cw ^ 2 * _root_.BoseGases.a v * (R / ℓ) ^ 4 := by
    have htail' : ℓ ^ (-(3 : ℝ)) *
        ∑ k ∈ (Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
            (fun k => Λ < ‖KM k‖),
          (G (KM k) ^ 2 + W (KM k) ^ 2) / ‖KM k‖ ^ 2
        ≤ H.Cw ^ 2 * _root_.BoseGases.a v * (R / ℓ) ^ 4 := by
      simpa only [← hℓdef, ← hΛdef, ← hKMdef, ← hGdef, ← hWdef]
        using honTailL_to_excitedTail H HM hN μ hμ hε
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
            Work.BoseRowsFS.uvCut_eq_one_of_norm_le (not_lt.mp hk)
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
      _ ≤ H.Cw ^ 2 * _root_.BoseGases.a v * (R / ℓ) ^ 4 := htail'
  -- ### assembly
  have key : ℓ ^ (-(3 : ℝ)) * (∑ k ∈ P, (G (KM k)
        - (Work.BoseRowsFS.honE v h fc fu HM μ).W1 k) ^ 2 / ‖KM k‖ ^ 2)
      ≤ (2 * Chl + 2 * H.Cw ^ 2) * _root_.BoseGases.a v * (R / ℓ) ^ 4 := by
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
            + 2 * (H.Cw ^ 2 * _root_.BoseGases.a v * (R / ℓ) ^ 4) := by
          linarith [hB, hC1]
      _ = (2 * Chl + 2 * H.Cw ^ 2) * _root_.BoseGases.a v * (R / ℓ) ^ 4 := by ring
  rw [hell, haS]
  exact key

end

end Work.BoseRowsL.Glue

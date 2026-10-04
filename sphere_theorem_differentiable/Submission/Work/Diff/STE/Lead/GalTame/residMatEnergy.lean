import Mathlib
import Submission.Work.Diff.STE.Lead.GalTame.GalCenter
import Submission.Work.Diff.STE.B3.Data
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.B3.mat_ENormSq_le_clean
import Submission.Work.Diff.STE.B3.mat_ENormSq_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `residMatEnergy`: the `Hᵐ` energy of the localised chart matrix over the centred cube

The target of this file is the estimate which the tame `L²` transport residual needs: the `Hᵐ`
energy `CENormSq m (φ · mat j h a b)` of the chart matrix of a section, cut off by a bump `φ`
supported in a compact set `Kc` inside the flat chart target, is controlled by the `Hᵐ` energies of
the periodised localised components `D.Rper i h c d`.

The proof (all ingredients are already in the workspace, and axiom-clean) runs as follows.

* The pointwise reconstruction identity `Work.Diff.STE.B3.mat_eq_sum_of_partition` writes
  `φ z · mat j h a b z = Σ_{i,c,d} (φ z · G (a,b) i c d z) · Rper i h c d (Tt i z)` for *every* `z`,
  where `ψ`, `Tt`, `G`, `Ctr` come from the smooth-data construction
  `Work.Diff.STE.B3.exists_smooth_data` (subordinated to the compact set `Kc`).
* Cauchy–Schwarz over the finite triple index turns the energy of the sum into the sum of the
  energies of the summands (with the cardinality of the index as the constant), and
  `∫_{cubeC} ≤ ∫_{ℝⁿ}` drops the restriction to the centred cube.
* Each summand has the form `(↑φ) · Z t` with `Z t = ↑(G t) · (Rper ∘ Tt)`; the pointwise
  Leibniz bound `resid_mulJet_pointwise` (the sharp cut-off bound of `mulJet_le_sharp`, in
  pointwise form) bounds `‖∂^β ((↑φ) · Z t)‖²` by `4^m Kφ²` times the full jet weight of `Z t`,
  and `resid_Rn_pdVec_mul_le` integrates this over `ℝⁿ`.
* For `Z t` itself, the change-of-variables estimate carried by `exists_smooth_data` (the `hGb`
  conjunct, proved from `Work.Diff.STE.B3.integral_pd_comp_le_compact`) bounds every jet integral
  over `ℝⁿ` by the unit-cube jet integrals of `Rper`, uniformly in the periodic factor.
* The counting of the `(j,γ,k,l')` quadruples contributes the factor `Call · Nt · Nt`, and the
  Sobolev conversion `∫_{unitCube} ‖∂^{l'} Rper‖² ≤ Cenv · ENormSq m Rper` (for `l' ≤ m`) finishes.

The two closed-form lemmas at the top (`resid_mulJet_pointwise`, `resid_Rn_pdVec_mul_le`) are
domain independent; only the first one is the (already proved) pointwise core of
`Work.Diff.STE.B3.mulJet_le_sharp`.
-/

namespace Work.Diff.STE.Lead.GalTame

section Helpers

open MeasureTheory BigOperators

/-- The `Hᵐ` energy over the unit cube is nonnegative: it is a sum of integrals of squares. -/
lemma resid_ENormSq_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ)
    (f : (ι → ℝ) → ℂ) : 0 ≤ Work.Diff.STE.ENormSq m f := by
  rw [Work.Diff.STE.ENormSq]
  exact Finset.sum_nonneg fun l _ => MeasureTheory.integral_nonneg fun x => sq_nonneg _

/-- **Pointwise sharp Leibniz bound for a cut-off.**  If all iterated derivatives of `φ` of order
`≤ m` are bounded by `Kφ`, then the squared norm of the `β`-th partial derivative of `φ · W` is
bounded by `4^m Kφ²` times the full jet weight `Σ_{j ≤ m} Σ_γ ‖∂^γ W‖²`.

This is the pointwise content of `Work.Diff.STE.B3.mulJet_le_sharp` (which integrates it over the
unit cube); stated pointwise it is available on every domain, which is what the centred-cube
energy needs. -/
lemma resid_mulJet_pointwise {n m : ℕ} (φ : (Fin n → ℝ) → ℝ) (W : (Fin n → ℝ) → ℂ) (Kφ : ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hφb : ∀ r : ℕ, r ≤ m → ∀ (γ : Fin r → Fin n) (z : Fin n → ℝ),
      |Work.Diff.STE.pdRVec r γ φ z| ≤ Kφ)
    (β : Fin m → Fin n) (z : Fin n → ℝ) :
    ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * W z) z‖ ^ 2
      ≤ (4 : ℝ) ^ m * Kφ ^ 2 * ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
          ‖Work.Diff.STE.pdVec j γ W z‖ ^ 2 := by
  classical
  set F : (Fin n → ℝ) → ℂ := fun y => ((φ y : ℝ) : ℂ) with hF
  set l : List (Fin n) := List.ofFn β with hl
  have hl_len : l.length = m := by rw [hl]; exact List.length_ofFn
  set S : List (List (Fin n) × List (Fin n)) := Work.Diff.STE.splits l with hS
  have hS_len : (S.length : ℝ) = (2 : ℝ) ^ m := by
    rw [hS, Work.Diff.STE.cm_splits_length_count, hl_len]; push_cast; ring
  set B : (Fin n → ℝ) → ℝ := fun z => ∑ j ∈ Finset.range (m + 1),
    ∑ γ : Fin j → Fin n, ‖Work.Diff.STE.pdVec j γ W z‖ ^ 2 with hB
  have hSsq : (S.length : ℝ) ^ 2 = (4 : ℝ) ^ m := by
    rw [hS_len]
    calc ((2 : ℝ) ^ m) ^ 2 = 2 ^ (m * 2) := by rw [pow_mul]
      _ = 2 ^ (2 * m) := by rw [Nat.mul_comm]
      _ = (2 ^ 2) ^ m := by rw [pow_mul]
      _ = 4 ^ m := by norm_num
  have hBnn : ∀ z : Fin n → ℝ, 0 ≤ B z := by
    intro z; rw [hB]
    exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun γ _ => sq_nonneg _
  have hFdiff : ∀ q : List (Fin n), q.Sublist l → q.length < l.length →
      Differentiable ℝ (Work.Diff.STE.pdList q F) := by
    intro q _ _
    rw [hF]
    exact Work.Diff.STE.cm_diff_pdList_ofReal φ hφ q
  have hWdiff : ∀ q : List (Fin n), q.Sublist l → q.length < l.length →
      Differentiable ℝ (Work.Diff.STE.pdList q W) := by
    intro q _ _
    refine (Work.Diff.STE.cm_contDiff_pdList q 1 W ?_).differentiable (by norm_num)
    exact hW.of_le (Work.Diff.STE.B3.contDiff_level_le (q.length + 1))
  have hterm : ∀ (z : Fin n → ℝ) (p : List (Fin n) × List (Fin n)), p ∈ S →
      ‖Work.Diff.STE.pdList p.1 F z * Work.Diff.STE.pdList p.2 W z‖
        ≤ Kφ * ‖Work.Diff.STE.pdList p.2 W z‖ := by
    intro z p hp
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have hp' : p ∈ Work.Diff.STE.splits l := by rw [hS] at hp; exact hp
    have hlen := Work.Diff.STE.cm_splits_mem_length l p hp'
    have hlen' : p.1.length ≤ m := by rw [hl_len] at hlen; omega
    rw [hF]
    exact Work.Diff.STE.B3.pdList_ofReal_norm_le_b3 hφb hlen' z
  have h1 : ∀ z : Fin n → ℝ, ‖Work.Diff.STE.pdList l (fun z => F z * W z) z‖
      ≤ Kφ * (S.map (fun p => ‖Work.Diff.STE.pdList p.2 W z‖)).sum := by
    intro z
    rw [Work.Diff.STE.B3.pdList_mul_unfiltered_b3 l F W hFdiff hWdiff z]
    calc ‖(S.map (fun p => Work.Diff.STE.pdList p.1 F z * Work.Diff.STE.pdList p.2 W z)).sum‖
        ≤ (S.map (fun p => ‖Work.Diff.STE.pdList p.1 F z * Work.Diff.STE.pdList p.2 W z‖)).sum :=
          Work.Diff.STE.B3.norm_list_sum_le_b3 S _
      _ ≤ (S.map (fun p => Kφ * ‖Work.Diff.STE.pdList p.2 W z‖)).sum :=
          Work.Diff.STE.B3.list_sum_le_sum_b3 S (fun p hp => hterm z p hp)
      _ = Kφ * (S.map (fun p => ‖Work.Diff.STE.pdList p.2 W z‖)).sum :=
          Work.Diff.STE.B3.list_sum_map_mul_left_b3 S Kφ _
  have h2 : ∀ z : Fin n → ℝ, (S.map (fun p => ‖Work.Diff.STE.pdList p.2 W z‖)).sum
      ≤ (S.length : ℝ) * Real.sqrt (B z) := by
    intro z
    refine Work.Diff.STE.B3.list_sum_le_card_mul_b3 S
      (fun p => ‖Work.Diff.STE.pdList p.2 W z‖) (Real.sqrt (B z)) ?_
    intro p hp
    refine Real.le_sqrt_of_sq_le ?_
    have hp' : p ∈ Work.Diff.STE.splits l := by rw [hS] at hp; exact hp
    have hlen := Work.Diff.STE.cm_splits_mem_length l p hp'
    have hlen' : p.2.length ≤ m := by rw [hl_len] at hlen; omega
    have hpd' : Work.Diff.STE.pdList p.2 W
        = Work.Diff.STE.pdVec p.2.length (fun i : Fin p.2.length => p.2.get i) W := by
      rw [Work.Diff.STE.pdVec]
      congr 1
      exact (List.ofFn_get p.2).symm
    rw [hpd']
    refine (Finset.single_le_sum
      (f := fun γ : Fin p.2.length → Fin n => ‖Work.Diff.STE.pdVec p.2.length γ W z‖ ^ 2)
      (fun γ _ => sq_nonneg _) (Finset.mem_univ (fun i => p.2.get i))).trans ?_
    rw [hB]
    exact Finset.single_le_sum
      (f := fun j => ∑ γ : Fin j → Fin n, ‖Work.Diff.STE.pdVec j γ W z‖ ^ 2)
      (fun j _ => Finset.sum_nonneg fun γ _ => sq_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hlen'))
  have h3 : ∀ z : Fin n → ℝ, 0 ≤ (S.map (fun p => ‖Work.Diff.STE.pdList p.2 W z‖)).sum := by
    intro z
    exact List.sum_nonneg fun a ha => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      exact norm_nonneg _
  have hpd : Work.Diff.STE.pdVec m β (fun z => F z * W z)
      = Work.Diff.STE.pdList l (fun z => F z * W z) := by rw [hl]; rfl
  calc ‖Work.Diff.STE.pdVec m β (fun z => F z * W z) z‖ ^ 2
      = ‖Work.Diff.STE.pdList l (fun z => F z * W z) z‖ ^ 2 := by rw [hpd]
    _ ≤ (Kφ * (S.map (fun p => ‖Work.Diff.STE.pdList p.2 W z‖)).sum) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (h1 z) 2
    _ = Kφ ^ 2 * ((S.map (fun p => ‖Work.Diff.STE.pdList p.2 W z‖)).sum) ^ 2 := by ring
    _ ≤ Kφ ^ 2 * ((S.length : ℝ) * Real.sqrt (B z)) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (h3 z) (h2 z) 2) (sq_nonneg Kφ)
    _ = Kφ ^ 2 * (S.length : ℝ) ^ 2 * B z := by
        rw [mul_pow, Real.sq_sqrt (hBnn z)]; ring
    _ = (4 : ℝ) ^ m * Kφ ^ 2 * B z := by rw [hSsq]; ring

/-- **Integral form of the sharp Leibniz bound.**  Under the same hypotheses, plus the compactness
of the support of `W` (which makes every integrand integrable), the integral over `ℝ^n` of the
squared `β`-th derivative of `φ · W` is bounded by `4^m Kφ²` times the total jet energy of `W`. -/
lemma resid_Rn_pdVec_mul_le {n m : ℕ} (φ : (Fin n → ℝ) → ℝ) (W : (Fin n → ℝ) → ℂ) (Kφ : ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hWc : HasCompactSupport W)
    (hφb : ∀ r : ℕ, r ≤ m → ∀ (γ : Fin r → Fin n) (z : Fin n → ℝ),
      |Work.Diff.STE.pdRVec r γ φ z| ≤ Kφ)
    (β : Fin m → Fin n) :
    ∫ z : Fin n → ℝ, ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * W z) z‖ ^ 2
      ≤ (4 : ℝ) ^ m * Kφ ^ 2 * ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
          ∫ z : Fin n → ℝ, ‖Work.Diff.STE.pdVec j γ W z‖ ^ 2 := by
  classical
  set B : (Fin n → ℝ) → ℝ := fun z => ∑ j ∈ Finset.range (m + 1),
    ∑ γ : Fin j → Fin n, ‖Work.Diff.STE.pdVec j γ W z‖ ^ 2 with hB
  have hcpt1 : HasCompactSupport (fun z : Fin n → ℝ => ((φ z : ℝ) : ℂ) * W z) :=
    hWc.mono (Function.support_mul_subset_right (fun z : Fin n → ℝ => ((φ z : ℝ) : ℂ)) W)
  have hIntSummand : ∀ (j : ℕ) (γ : Fin j → Fin n),
      Integrable (fun z : Fin n → ℝ => ‖Work.Diff.STE.pdVec j γ W z‖ ^ 2) := by
    intro j γ
    refine Continuous.integrable_of_hasCompactSupport
      (((Work.Diff.STE.B3.continuous_pdVec_of_smooth hW j γ).norm).pow 2) ?_
    refine IsCompact.of_isClosed_subset hWc (isClosed_tsupport _) ?_
    have h2 : Function.support (Work.Diff.STE.pdVec j γ W) ⊆ closure (Function.support W) :=
      Work.Diff.STE.csqp_support_pdList_subset_closure (List.ofFn γ) W
    calc tsupport (fun z : Fin n → ℝ => ‖Work.Diff.STE.pdVec j γ W z‖ ^ 2)
        = closure (Function.support (fun z : Fin n → ℝ => ‖Work.Diff.STE.pdVec j γ W z‖ ^ 2)) := rfl
      _ ⊆ closure (Function.support (Work.Diff.STE.pdVec j γ W)) := by
          refine closure_mono ?_
          intro z hz
          rw [Function.mem_support] at hz ⊢
          intro h0; exact hz (by rw [h0]; simp)
      _ ⊆ closure (closure (Function.support W)) := closure_mono h2
      _ = closure (Function.support W) := closure_closure
      _ = tsupport W := rfl
  have hIntB : Integrable B := by
    rw [hB]
    refine MeasureTheory.integrable_finsetSum _ (fun j _ => ?_)
    exact MeasureTheory.integrable_finsetSum _ (fun γ _ => hIntSummand j γ)
  have hIntg : Integrable (fun z : Fin n → ℝ => ((4 : ℝ) ^ m * Kφ ^ 2) * B z) :=
    hIntB.const_mul _
  have hle : ∀ z : Fin n → ℝ, ‖Work.Diff.STE.pdVec m β
      (fun z => ((φ z : ℝ) : ℂ) * W z) z‖ ^ 2 ≤ ((4 : ℝ) ^ m * Kφ ^ 2) * B z := by
    intro z
    rw [hB]
    exact resid_mulJet_pointwise φ W Kφ hφ hW hφb β z
  have hintB : ∫ z : Fin n → ℝ, B z = ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
      ∫ z : Fin n → ℝ, ‖Work.Diff.STE.pdVec j γ W z‖ ^ 2 := by
    rw [hB]
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [MeasureTheory.integral_finsetSum]
      intro γ _; exact hIntSummand j γ
    · intro j _; exact MeasureTheory.integrable_finsetSum _ (fun γ _ => hIntSummand j γ)
  calc ∫ z : Fin n → ℝ, ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * W z) z‖ ^ 2
      ≤ ∫ z : Fin n → ℝ, ((4 : ℝ) ^ m * Kφ ^ 2) * B z :=
        MeasureTheory.integral_mono
          (Continuous.integrable_of_hasCompactSupport
            (by
              have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => ((φ z : ℝ) : ℂ) * W z) :=
                (Complex.ofRealCLM.contDiff (n := (⊤ : ℕ∞))).comp hφ |>.mul hW
              have h := (Work.Diff.STE.B3.continuous_pdVec_of_smooth hsm m β).norm
              convert h.mul h using 1
              ext z; simp only [Pi.mul_apply, pow_two])
            (IsCompact.of_isClosed_subset hcpt1 (isClosed_tsupport _) (by
              have h1 : Function.support (fun z : Fin n → ℝ => ‖Work.Diff.STE.pdVec m β
                  (fun z => ((φ z : ℝ) : ℂ) * W z) z‖ ^ 2)
                  ⊆ Function.support (Work.Diff.STE.pdVec m β
                    (fun z => ((φ z : ℝ) : ℂ) * W z)) := by
                intro z hz
                rw [Function.mem_support] at hz ⊢
                intro h0; exact hz (by rw [h0]; simp)
              have h2 : Function.support (Work.Diff.STE.pdVec m β
                    (fun z => ((φ z : ℝ) : ℂ) * W z))
                  ⊆ closure (Function.support (fun z : Fin n → ℝ => ((φ z : ℝ) : ℂ) * W z)) :=
                Work.Diff.STE.csqp_support_pdList_subset_closure (List.ofFn β) _
              calc tsupport (fun z : Fin n → ℝ => ‖Work.Diff.STE.pdVec m β
                      (fun z => ((φ z : ℝ) : ℂ) * W z) z‖ ^ 2)
                  = closure (Function.support (fun z : Fin n → ℝ => ‖Work.Diff.STE.pdVec m β
                      (fun z => ((φ z : ℝ) : ℂ) * W z) z‖ ^ 2)) := rfl
                _ ⊆ closure (Function.support (Work.Diff.STE.pdVec m β
                      (fun z => ((φ z : ℝ) : ℂ) * W z))) := closure_mono h1
                _ ⊆ closure (closure (Function.support
                      (fun z : Fin n → ℝ => ((φ z : ℝ) : ℂ) * W z))) := closure_mono h2
                _ = closure (Function.support (fun z : Fin n → ℝ => ((φ z : ℝ) : ℂ) * W z)) :=
                    closure_closure
                _ = tsupport (fun z : Fin n → ℝ => ((φ z : ℝ) : ℂ) * W z) := rfl)))
          hIntg hle
    _ = ((4 : ℝ) ^ m * Kφ ^ 2) * ∫ z : Fin n → ℝ, B z := MeasureTheory.integral_const_mul _ _
    _ = (4 : ℝ) ^ m * Kφ ^ 2 * ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
          ∫ z : Fin n → ℝ, ‖Work.Diff.STE.pdVec j γ W z‖ ^ 2 := by rw [hintB]

end Helpers

/-- **The `Hᵐ` energy of the localised chart matrix over the centred cube**, controlled by the `Hᵐ`
energies of the periodised components. -/
theorem residMatEnergy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) (m : ℕ)
    (Kc : Set (Fin (Module.finrank ℝ E) → ℝ)) (hKc : IsCompact Kc) (Kφ : ℝ) (hKφ : 0 ≤ Kφ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
        (φ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hφ : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) φ)
        (hφb : ∀ (r : ℕ), r ≤ m → ∀ (γ : Fin r → Fin (Module.finrank ℝ E))
          (z : Fin (Module.finrank ℝ E) → ℝ), |Work.Diff.STE.pdRVec r γ φ z| ≤ Kφ)
        (hφs : tsupport φ ⊆ Kc)
        (hφt : Kc ⊆ {z : Fin (Module.finrank ℝ E) → ℝ |
          Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target}),
        ∀ (a b : Fin (Module.finrank ℝ E)),
        Work.Diff.STE.Lead.GalTame.CENormSq m
            (fun z => ((φ z * D.mat j h a b z : ℝ) : ℂ))
          ≤ C * (1 + ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
              ∑ d : Fin (Module.finrank ℝ E), Work.Diff.STE.ENormSq m (D.Rper i h c d)) := by
  classical
  by_cases hn : Module.finrank ℝ E = 0
  · refine ⟨0, le_refl 0, ?_⟩
    intro h hsm φ hφ hφb hφs hφt a b
    exact Fin.elim0 (hn ▸ a)
  have hn1 : 1 ≤ Module.finrank ℝ E := Nat.pos_of_ne_zero hn
  haveI : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, hn1⟩⟩
  by_cases hKO : Kc ⊆ Work.Diff.STE.B3.flatTarget (I := I) (M := M) D j
  · obtain ⟨ψ, Tt, U, G, Ctr, hψsm, hψsupp, hψcpt, hψsum, hUopen, hTtsm, hUsub, hTinj, hTdet,
      hTeqU, hTtone, hGsm, hGcpt, hGgood, hGone, hGzero, hCtrnn, hGb⟩ :=
      Work.Diff.STE.B3.exists_smooth_data (I := I) (M := M) D j m Kc hKc hKO
    -- ## the constants of the estimate (all independent of `h`, `φ`, `a`, `b`)
    set nR : ℝ := ((Module.finrank ℝ E : ℕ) : ℝ) with hnR
    have hnR1 : (1 : ℝ) ≤ nR := by rw [hnR]; exact_mod_cast hn1
    have hnRnn : (0 : ℝ) ≤ nR := le_trans zero_le_one hnR1
    set Nt : ℝ := ∑ j' ∈ Finset.range (m + 1), nR ^ j' with hNt
    have hNtnn : 0 ≤ Nt := by rw [hNt]; exact Finset.sum_nonneg fun j' _ => pow_nonneg hnRnn j'
    set N1 : ℝ := (Fintype.card (ι₀ × (Fin (Module.finrank ℝ E) ×
      Fin (Module.finrank ℝ E))) : ℝ) with hN1
    have hN1nn : 0 ≤ N1 := by rw [hN1]; positivity
    -- the Sobolev conversion constant
    have hconv : ∃ C : ℝ, 0 ≤ C ∧ ∀ (R P : (Fin (Module.finrank ℝ E) → ℝ) → ℂ),
        ContDiff ℝ (⊤ : ℕ∞) R →
        Function.support R ⊆ Set.pi Set.univ
          (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2)) →
        ContDiff ℝ (⊤ : ℕ∞) P → Work.Diff.STE.Periodic1 P →
        (∀ z, P z = ∑' k : Fin (Module.finrank ℝ E) → ℤ, R (z + Work.Diff.STE.iVec k)) →
        ∀ (j' : ℕ) (l' : Fin j' → Fin (Module.finrank ℝ E)), j' ≤ m →
          ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec j' l' P x‖ ^ 2
            ≤ C * Work.Diff.STE.ENormSq m P := by
      by_cases hm0 : m = 0
      · subst hm0
        refine ⟨1, zero_le_one, ?_⟩
        intro R P hR hRs hP hPp hPrepr j' l' hj'
        have hj'0 : j' = 0 := Nat.le_zero.mp hj'
        subst hj'0
        rw [one_mul]
        have h1 : Work.Diff.STE.pdVec 0 l' P = P := by
          simp [Work.Diff.STE.pdVec, Work.Diff.STE.pdList]
        rw [h1]
        have h2 : Work.Diff.STE.ENormSq 0 P
            = ∫ x in Work.Diff.STE.unitCube, ‖P x‖ ^ 2 := by
          simp [Work.Diff.STE.ENormSq, Work.Diff.STE.pdVec, Work.Diff.STE.pdList]
        rw [h2]
      · exact Work.Diff.STE.B3.pdVec_integral_le_ENormSq_per_local
          (ι := Fin (Module.finrank ℝ E)) m (Nat.pos_of_ne_zero hm0)
    obtain ⟨Cenv, hCenvnn, hCenvb⟩ := hconv
    set Call : ℝ := ∑ ab : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      (Ctr ab + 1) with hCall
    have hCallnn : 0 ≤ Call := by
      rw [hCall]; exact Finset.sum_nonneg fun ab _ => by linarith [hCtrnn ab]
    have hCtrle : ∀ ab : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        Ctr ab ≤ Call := by
      intro ab
      have h2 := Finset.single_le_sum (f := fun ab : Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E) => Ctr ab + 1) (fun ab _ => by linarith [hCtrnn ab])
        (Finset.mem_univ ab)
      rw [hCall]; linarith
    set Dc : ℝ := (4 : ℝ) ^ m * Kφ ^ 2 * (Call * Nt * (Nt * Cenv)) with hDc
    have hDcnn : 0 ≤ Dc := by
      rw [hDc]
      refine mul_nonneg (mul_nonneg (by positivity) (sq_nonneg Kφ)) ?_
      exact mul_nonneg (mul_nonneg hCallnn hNtnn) (mul_nonneg hNtnn hCenvnn)
    set Cnst : ℝ := (Fintype.card (Fin m → Fin (Module.finrank ℝ E)) : ℝ) * N1 * Dc
      with hCnst
    have hCnstnn : 0 ≤ Cnst := by
      rw [hCnst]; exact mul_nonneg (mul_nonneg (by positivity) hN1nn) hDcnn
    refine ⟨max 1 Cnst, le_trans zero_le_one (le_max_left _ _), ?_⟩
    intro h hsm φ hφ hφb hφs hφt a b
    -- ## the reconstruction identity
    have hψζ : ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ψ i z ≠ 0 →
        D.ζ i (D.pt j z) ≠ 0 :=
      fun i z hz => (hψsupp i (subset_closure (Function.mem_support.mpr hz))).2
    set F : (Fin (Module.finrank ℝ E) → ℝ) → ℂ :=
      fun z => ((φ z * D.mat j h a b z : ℝ) : ℂ) with hF
    have hident : F
        = fun z => ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
            ∑ d : Fin (Module.finrank ℝ E),
              ((φ z * G (a, b) i c d z : ℝ) : ℂ) * D.Rper i h c d (Tt i z) := by
      funext z
      rw [hF]
      exact Work.Diff.STE.B3.mat_eq_sum_of_partition (I := I) (M := M) D h j a b Kc ψ
        (fun i c d => G (a, b) i c d) Tt hψsum hψζ hTtone
        (fun i c d z hz => hGone (a, b) i c d z hz)
        (fun i c d z hz => hGzero (a, b) i c d z hz) φ hφs z
    set Z : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) →
        (Fin (Module.finrank ℝ E) → ℝ) → ℂ :=
      fun t z => ((G (a, b) t.1 t.2.1 t.2.2 z : ℝ) : ℂ) *
        D.Rper t.1 h t.2.1 t.2.2 (Tt t.1 z) with hZ
    have hZsm : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (Z t) := by
      intro t
      have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun z => ((G (a, b) t.1 t.2.1 t.2.2 z : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp (hGsm (a, b) t.1 t.2.1 t.2.2)
      have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun z => D.Rper t.1 h t.2.1 t.2.2 (Tt t.1 z)) :=
        (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff (I := I) (M := M) D t.1 h t.2.1
          t.2.2 (Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D h hsm t.1 t.2.1
            t.2.2)).1.comp (hTtsm t.1)
      simpa only [hZ, Pi.mul_apply] using h1.mul h2
    have hZcpt : ∀ t, HasCompactSupport (Z t) := by
      intro t
      have h1 : HasCompactSupport (fun z => ((G (a, b) t.1 t.2.1 t.2.2 z : ℝ) : ℂ)) := by
        refine (hGcpt (a, b) t.1 t.2.1 t.2.2).mono ?_
        intro z hz
        rw [Function.mem_support] at hz ⊢
        exact fun h0 => hz (by rw [h0]; simp)
      refine h1.mono ?_
      intro z hz
      rw [Function.mem_support] at hz ⊢
      intro h0
      exact hz (by rw [hZ]; simp [h0])
    have hRper : ∀ t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
        ContDiff ℝ (⊤ : ℕ∞) (D.Rper t.1 h t.2.1 t.2.2) ∧
        Work.Diff.STE.Periodic1 (D.Rper t.1 h t.2.1 t.2.2) :=
      fun t => Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff (I := I) (M := M) D t.1 h
        t.2.1 t.2.2 (Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D h hsm t.1
          t.2.1 t.2.2)
    have hident' : F = fun z => ∑ t : ι₀ × (Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E)), ((φ z : ℝ) : ℂ) * Z t z := by
      rw [hident]
      funext z
      rw [show (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
            ∑ d : Fin (Module.finrank ℝ E),
              ((φ z * G (a, b) i c d z : ℝ) : ℂ) * D.Rper i h c d (Tt i z))
          = ∑ t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
              ((φ z * G (a, b) t.1 t.2.1 t.2.2 z : ℝ) : ℂ) *
                D.Rper t.1 h t.2.1 t.2.2 (Tt t.1 z)
          from Work.Diff.STE.B3.sum3_eq_sum_prod _]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [hZ]
      rw [Complex.ofReal_mul]; ring
    have hFsm : ContDiff ℝ (⊤ : ℕ∞) F := by
      rw [hident']
      exact ContDiff.sum fun t _ =>
        (Complex.ofRealCLM.contDiff (n := (⊤ : ℕ∞))).comp hφ |>.mul (hZsm t)
    have hφcpt : HasCompactSupport φ :=
      IsCompact.of_isClosed_subset hKc (isClosed_tsupport φ) hφs
    have hFcpt_sub : Function.support F ⊆ Function.support φ := by
      intro z hz
      rw [Function.mem_support] at hz ⊢
      intro h0
      exact hz (by rw [hF]; simp [h0])
    set St : ℝ := ∑ t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
      Work.Diff.STE.ENormSq m (D.Rper t.1 h t.2.1 t.2.2) with hSt
    have hStnn : 0 ≤ St := by
      rw [hSt]
      exact Finset.sum_nonneg fun t _ => resid_ENormSq_nonneg m _
    -- ## the counting of the `(j,γ,k,l')` quadruples
    have hcount : ∀ (Gc : (k : ℕ) → (Fin k → Fin (Module.finrank ℝ E)) → ℝ),
        (∀ k l', 0 ≤ Gc k l') →
        (∑ j' ∈ Finset.range (m + 1), ∑ γ : Fin j' → Fin (Module.finrank ℝ E),
            Ctr (a, b) * ∑ k ∈ Finset.range (j' + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E), Gc k l')
          ≤ Ctr (a, b) * Nt * (∑ k ∈ Finset.range (m + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E), Gc k l') := by
      intro Gc hGnn
      have hinner : ∀ j' ∈ Finset.range (m + 1),
          (∑ γ : Fin j' → Fin (Module.finrank ℝ E),
              Ctr (a, b) * ∑ k ∈ Finset.range (j' + 1),
                ∑ l' : Fin k → Fin (Module.finrank ℝ E), Gc k l')
            ≤ Ctr (a, b) * nR ^ j' * (∑ k ∈ Finset.range (m + 1),
                ∑ l' : Fin k → Fin (Module.finrank ℝ E), Gc k l') := by
        intro j' hj'
        have hjle : j' ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj')
        have hsub : (∑ k ∈ Finset.range (j' + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E), Gc k l')
            ≤ ∑ k ∈ Finset.range (m + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E), Gc k l' := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro k hk
            exact Finset.mem_range.mpr
              (lt_of_lt_of_le (Finset.mem_range.mp hk) (Nat.succ_le_succ hjle))
          · intro k _ _
            exact Finset.sum_nonneg fun l' _ => hGnn k l'
        have h1 : (∑ γ : Fin j' → Fin (Module.finrank ℝ E),
              Ctr (a, b) * ∑ k ∈ Finset.range (j' + 1),
                ∑ l' : Fin k → Fin (Module.finrank ℝ E), Gc k l')
            = nR ^ j' * (Ctr (a, b) * (∑ k ∈ Finset.range (j' + 1),
                ∑ l' : Fin k → Fin (Module.finrank ℝ E), Gc k l')) := by
          rw [Work.Diff.STE.B3.sum_fun_const, ← hnR]
        calc (∑ γ : Fin j' → Fin (Module.finrank ℝ E),
              Ctr (a, b) * ∑ k ∈ Finset.range (j' + 1),
                ∑ l' : Fin k → Fin (Module.finrank ℝ E), Gc k l')
            = nR ^ j' * (Ctr (a, b) * (∑ k ∈ Finset.range (j' + 1),
                ∑ l' : Fin k → Fin (Module.finrank ℝ E), Gc k l')) := h1
          _ ≤ nR ^ j' * (Ctr (a, b) * (∑ k ∈ Finset.range (m + 1),
                ∑ l' : Fin k → Fin (Module.finrank ℝ E), Gc k l')) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hsub (hCtrnn (a, b))) (pow_nonneg hnRnn j')
          _ = Ctr (a, b) * nR ^ j' * (∑ k ∈ Finset.range (m + 1),
                ∑ l' : Fin k → Fin (Module.finrank ℝ E), Gc k l') := by ring
      calc (∑ j' ∈ Finset.range (m + 1), ∑ γ : Fin j' → Fin (Module.finrank ℝ E),
              Ctr (a, b) * ∑ k ∈ Finset.range (j' + 1),
                ∑ l' : Fin k → Fin (Module.finrank ℝ E), Gc k l')
          ≤ ∑ j' ∈ Finset.range (m + 1), Ctr (a, b) * nR ^ j' *
              (∑ k ∈ Finset.range (m + 1),
                ∑ l' : Fin k → Fin (Module.finrank ℝ E), Gc k l') :=
            Finset.sum_le_sum hinner
        _ = Ctr (a, b) * (∑ j' ∈ Finset.range (m + 1), nR ^ j') *
              (∑ k ∈ Finset.range (m + 1),
                ∑ l' : Fin k → Fin (Module.finrank ℝ E), Gc k l') := by
            have hfac : ∀ Y : ℝ,
                (∑ j' ∈ Finset.range (m + 1), Ctr (a, b) * nR ^ j' * Y)
                  = Ctr (a, b) * (∑ j' ∈ Finset.range (m + 1), nR ^ j') * Y := by
              intro Y
              simp only [Finset.mul_sum, Finset.sum_mul]
            rw [hfac]
        _ = Ctr (a, b) * Nt * (∑ k ∈ Finset.range (m + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E), Gc k l') := by rw [hNt]
    -- ## the per-`β` bound
    have hbound : ∀ β : Fin m → Fin (Module.finrank ℝ E),
        ∫ z in Work.Diff.STE.Lead.GalTame.cubeC (Fin (Module.finrank ℝ E)),
            ‖Work.Diff.STE.pdVec m β F z‖ ^ 2 ≤ N1 * Dc * St := by
      intro β
      have hlin : Work.Diff.STE.pdVec m β F
          = fun z : Fin (Module.finrank ℝ E) → ℝ => ∑ t : ι₀ × (Fin (Module.finrank ℝ E) ×
              Fin (Module.finrank ℝ E)),
              Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z t z) z := by
        rw [hident']
        simpa using
          (Work.Diff.STE.flat.pdVec_finset_sum (Finset.univ) β
            (fun t (z : Fin (Module.finrank ℝ E) → ℝ) => ((φ z : ℝ) : ℂ) * Z t z)
            (fun t => (Complex.ofRealCLM.contDiff (n := (⊤ : ℕ∞))).comp hφ |>.mul (hZsm t)))
      have hptA : ∀ z : Fin (Module.finrank ℝ E) → ℝ,
          ‖Work.Diff.STE.pdVec m β F z‖ ^ 2
            ≤ N1 * ∑ t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
                ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z t z) z‖ ^ 2 := by
        intro z
        rw [hlin]
        calc ‖∑ t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
              Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z t z) z‖ ^ 2
            ≤ (∑ t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
                ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z t z) z‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
          _ ≤ (Fintype.card (ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))) : ℝ) *
                ∑ t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
                  ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z t z) z‖ ^ 2 := by
              simpa using (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (ι₀ ×
                (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)))))
                (f := fun t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) =>
                  ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z t z) z‖))
          _ = N1 * ∑ t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
                  ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z t z) z‖ ^ 2 := by
              rw [hN1]
      have hTerm_int : ∀ t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
          MeasureTheory.Integrable (fun z : Fin (Module.finrank ℝ E) → ℝ =>
            ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z t z) z‖ ^ 2) := by
        intro t
        refine Continuous.integrable_of_hasCompactSupport ?_ ?_
        · have h := (Work.Diff.STE.B3.continuous_pdVec_of_smooth
            ((Complex.ofRealCLM.contDiff (n := (⊤ : ℕ∞))).comp hφ |>.mul (hZsm t)) m β).norm
          convert h.mul h using 1
          ext z; simp only [Pi.mul_apply, pow_two, Function.comp_apply, Complex.ofRealCLM_apply]
        · refine IsCompact.of_isClosed_subset hφcpt (isClosed_tsupport _) ?_
          have h2 : Function.support (Work.Diff.STE.pdVec m β
                (fun z => ((φ z : ℝ) : ℂ) * Z t z))
              ⊆ closure (Function.support (fun z : Fin (Module.finrank ℝ E) → ℝ =>
                ((φ z : ℝ) : ℂ) * Z t z)) :=
            Work.Diff.STE.csqp_support_pdList_subset_closure (List.ofFn β) _
          calc tsupport (fun z : Fin (Module.finrank ℝ E) → ℝ =>
                ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z t z) z‖ ^ 2)
              = closure (Function.support (fun z : Fin (Module.finrank ℝ E) → ℝ =>
                  ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z t z) z‖ ^ 2)) := rfl
            _ ⊆ closure (Function.support (Work.Diff.STE.pdVec m β
                  (fun z => ((φ z : ℝ) : ℂ) * Z t z))) := by
                refine closure_mono ?_
                intro z hz
                rw [Function.mem_support] at hz ⊢
                intro h0; exact hz (by rw [h0]; simp)
            _ ⊆ closure (closure (Function.support (fun z : Fin (Module.finrank ℝ E) → ℝ =>
                  ((φ z : ℝ) : ℂ) * Z t z))) := closure_mono h2
            _ = closure (Function.support (fun z : Fin (Module.finrank ℝ E) → ℝ =>
                  ((φ z : ℝ) : ℂ) * Z t z)) := closure_closure
            _ ⊆ tsupport φ := by
                have hts : tsupport φ = closure (Function.support φ) := rfl
                rw [hts]
                exact closure_mono (fun z hz => by
                  rw [Function.mem_support] at hz ⊢
                  intro h0; exact hz (by simp [h0]))
      have hFintβ : MeasureTheory.Integrable (fun z : Fin (Module.finrank ℝ E) → ℝ =>
          ‖Work.Diff.STE.pdVec m β F z‖ ^ 2) := by
        refine Continuous.integrable_of_hasCompactSupport ?_ ?_
        · have h := (Work.Diff.STE.B3.continuous_pdVec_of_smooth hFsm m β).norm
          convert h.mul h using 1
          ext z; simp only [Pi.mul_apply, pow_two]
        · refine IsCompact.of_isClosed_subset hφcpt (isClosed_tsupport _) ?_
          have h2 : Function.support (Work.Diff.STE.pdVec m β F)
              ⊆ closure (Function.support F) :=
            Work.Diff.STE.csqp_support_pdList_subset_closure (List.ofFn β) F
          calc tsupport (fun z : Fin (Module.finrank ℝ E) → ℝ =>
                ‖Work.Diff.STE.pdVec m β F z‖ ^ 2)
              = closure (Function.support (fun z : Fin (Module.finrank ℝ E) → ℝ =>
                  ‖Work.Diff.STE.pdVec m β F z‖ ^ 2)) := rfl
            _ ⊆ closure (Function.support (Work.Diff.STE.pdVec m β F)) := by
                refine closure_mono ?_
                intro z hz
                rw [Function.mem_support] at hz ⊢
                intro h0; exact hz (by rw [h0]; simp)
            _ ⊆ closure (closure (Function.support F)) := closure_mono h2
            _ = closure (Function.support F) := closure_closure
            _ ⊆ tsupport φ := closure_mono hFcpt_sub
      have hRint : MeasureTheory.Integrable (fun z : Fin (Module.finrank ℝ E) → ℝ =>
          N1 * ∑ t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
            ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z t z) z‖ ^ 2) :=
        (MeasureTheory.integrable_finsetSum _ (fun t _ => hTerm_int t)).const_mul N1
      have hA : ∫ z in Work.Diff.STE.Lead.GalTame.cubeC (Fin (Module.finrank ℝ E)),
            ‖Work.Diff.STE.pdVec m β F z‖ ^ 2
          ≤ N1 * ∑ t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
              ∫ z : Fin (Module.finrank ℝ E) → ℝ,
                ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z t z) z‖ ^ 2 := by
        calc ∫ z in Work.Diff.STE.Lead.GalTame.cubeC (Fin (Module.finrank ℝ E)),
              ‖Work.Diff.STE.pdVec m β F z‖ ^ 2
            ≤ ∫ z : Fin (Module.finrank ℝ E) → ℝ, ‖Work.Diff.STE.pdVec m β F z‖ ^ 2 :=
              MeasureTheory.setIntegral_le_integral hFintβ
                (Filter.Eventually.of_forall fun z => sq_nonneg _)
          _ ≤ ∫ z : Fin (Module.finrank ℝ E) → ℝ,
                N1 * ∑ t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
                  ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z t z) z‖ ^ 2 :=
              MeasureTheory.integral_mono hFintβ hRint hptA
          _ = N1 * ∫ z : Fin (Module.finrank ℝ E) → ℝ,
                ∑ t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
                  ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z t z) z‖ ^ 2 :=
              MeasureTheory.integral_const_mul _ _
          _ = N1 * ∑ t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
                ∫ z : Fin (Module.finrank ℝ E) → ℝ,
                  ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z t z) z‖ ^ 2 := by
              rw [MeasureTheory.integral_finsetSum]
              intro t _
              exact hTerm_int t
      -- the per-summand bound
      have ht : ∀ t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
          ∫ z : Fin (Module.finrank ℝ E) → ℝ,
              ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z t z) z‖ ^ 2
            ≤ Dc * Work.Diff.STE.ENormSq m (D.Rper t.1 h t.2.1 t.2.2) := by
        intro t
        have hstep1 : ∫ z : Fin (Module.finrank ℝ E) → ℝ,
              ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z t z) z‖ ^ 2
            ≤ (4 : ℝ) ^ m * Kφ ^ 2 *
                ∑ j' ∈ Finset.range (m + 1), ∑ γ : Fin j' → Fin (Module.finrank ℝ E),
                  ∫ z : Fin (Module.finrank ℝ E) → ℝ,
                    ‖Work.Diff.STE.pdVec j' γ (Z t) z‖ ^ 2 :=
          resid_Rn_pdVec_mul_le φ (Z t) Kφ hφ (hZsm t) (hZcpt t) hφb β
        have hGb' : ∀ (j' : ℕ) (γ : Fin j' → Fin (Module.finrank ℝ E)), j' ≤ m →
            ∫ z : Fin (Module.finrank ℝ E) → ℝ,
                ‖Work.Diff.STE.pdVec j' γ (Z t) z‖ ^ 2
              ≤ Ctr (a, b) * ∑ k ∈ Finset.range (j' + 1),
                  ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                    ∫ x in Work.Diff.STE.unitCube,
                      ‖Work.Diff.STE.pdVec k l' (D.Rper t.1 h t.2.1 t.2.2) x‖ ^ 2 :=
          fun j' γ hj' => hGb (a, b) t.1 t.2.1 t.2.2 j' γ hj'
            (D.Rper t.1 h t.2.1 t.2.2) (hRper t).1 (hRper t).2
        have hstep2 : (∑ j' ∈ Finset.range (m + 1),
              ∑ γ : Fin j' → Fin (Module.finrank ℝ E),
                ∫ z : Fin (Module.finrank ℝ E) → ℝ,
                  ‖Work.Diff.STE.pdVec j' γ (Z t) z‖ ^ 2)
            ≤ Call * Nt * (∑ k ∈ Finset.range (m + 1),
                ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                  ∫ x in Work.Diff.STE.unitCube,
                    ‖Work.Diff.STE.pdVec k l' (D.Rper t.1 h t.2.1 t.2.2) x‖ ^ 2) := by
          have hcnt := hcount (fun k (l' : Fin k → Fin (Module.finrank ℝ E)) =>
              ∫ x in Work.Diff.STE.unitCube,
                ‖Work.Diff.STE.pdVec k l' (D.Rper t.1 h t.2.1 t.2.2) x‖ ^ 2)
            (fun k l' => MeasureTheory.integral_nonneg fun x => sq_nonneg _)
          refine (Finset.sum_le_sum fun j' hj' => Finset.sum_le_sum fun γ _ =>
            hGb' j' γ (Nat.le_of_lt_succ (Finset.mem_range.mp hj'))).trans ?_
          refine hcnt.trans ?_
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hCtrle (a, b)) hNtnn) ?_
          exact Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l' _ =>
            MeasureTheory.integral_nonneg fun x => sq_nonneg _
        have hstep3 : (∑ k ∈ Finset.range (m + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper t.1 h t.2.1 t.2.2) x‖ ^ 2)
            ≤ Nt * (Cenv * Work.Diff.STE.ENormSq m (D.Rper t.1 h t.2.1 t.2.2)) := by
          have hb : ∀ k ∈ Finset.range (m + 1), ∀ l' : Fin k → Fin (Module.finrank ℝ E),
              ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper t.1 h t.2.1 t.2.2) x‖ ^ 2
                ≤ Cenv * Work.Diff.STE.ENormSq m (D.Rper t.1 h t.2.1 t.2.2) := by
            intro k hk l'
            exact hCenvb (fun z => ((D.R t.1 h t.2.1 t.2.2 z : ℝ) : ℂ))
              (D.Rper t.1 h t.2.1 t.2.2)
              (Complex.ofRealCLM.contDiff.comp (Work.Diff.STE.B3.R_contDiff_of_chartData
                (I := I) (M := M) D h hsm t.1 t.2.1 t.2.2))
              (fun z hz => Work.Diff.STE.B3Data.R_support (I := I) (M := M) D t.1 h t.2.1 t.2.2
                (by
                  intro h0
                  exact (Function.mem_support.mp hz) (by simp [h0])))
              (hRper t).1 (hRper t).2 (fun z => rfl) k l'
              (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
          calc (∑ k ∈ Finset.range (m + 1),
                ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                  ∫ x in Work.Diff.STE.unitCube,
                    ‖Work.Diff.STE.pdVec k l' (D.Rper t.1 h t.2.1 t.2.2) x‖ ^ 2)
              ≤ ∑ k ∈ Finset.range (m + 1),
                  nR ^ k * (Cenv * Work.Diff.STE.ENormSq m (D.Rper t.1 h t.2.1 t.2.2)) := by
                refine Finset.sum_le_sum fun k hk => ?_
                have hsum : (∑ l' : Fin k → Fin (Module.finrank ℝ E),
                    ∫ x in Work.Diff.STE.unitCube,
                      ‖Work.Diff.STE.pdVec k l' (D.Rper t.1 h t.2.1 t.2.2) x‖ ^ 2)
                    ≤ ∑ _l' : Fin k → Fin (Module.finrank ℝ E),
                      (Cenv * Work.Diff.STE.ENormSq m (D.Rper t.1 h t.2.1 t.2.2)) :=
                  Finset.sum_le_sum fun l' _ => hb k hk l'
                rw [Work.Diff.STE.B3.sum_fun_const, ← hnR] at hsum
                exact hsum
            _ = Nt * (Cenv * Work.Diff.STE.ENormSq m (D.Rper t.1 h t.2.1 t.2.2)) := by
                rw [← Finset.sum_mul, ← hNt]
        calc ∫ z : Fin (Module.finrank ℝ E) → ℝ,
              ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z t z) z‖ ^ 2
            ≤ (4 : ℝ) ^ m * Kφ ^ 2 *
                ∑ j' ∈ Finset.range (m + 1), ∑ γ : Fin j' → Fin (Module.finrank ℝ E),
                  ∫ z : Fin (Module.finrank ℝ E) → ℝ,
                    ‖Work.Diff.STE.pdVec j' γ (Z t) z‖ ^ 2 := hstep1
          _ ≤ (4 : ℝ) ^ m * Kφ ^ 2 *
                (Call * Nt * (∑ k ∈ Finset.range (m + 1),
                  ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                    ∫ x in Work.Diff.STE.unitCube,
                      ‖Work.Diff.STE.pdVec k l' (D.Rper t.1 h t.2.1 t.2.2) x‖ ^ 2)) :=
              mul_le_mul_of_nonneg_left hstep2 (by positivity)
          _ ≤ (4 : ℝ) ^ m * Kφ ^ 2 *
                (Call * Nt * (Nt * (Cenv * Work.Diff.STE.ENormSq m (D.Rper t.1 h t.2.1 t.2.2)))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hstep3 (mul_nonneg hCallnn hNtnn)) (by positivity)
          _ = Dc * Work.Diff.STE.ENormSq m (D.Rper t.1 h t.2.1 t.2.2) := by
              rw [hDc]; ring
      calc ∫ z in Work.Diff.STE.Lead.GalTame.cubeC (Fin (Module.finrank ℝ E)),
            ‖Work.Diff.STE.pdVec m β F z‖ ^ 2
          ≤ N1 * ∑ t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
              ∫ z : Fin (Module.finrank ℝ E) → ℝ,
                ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z t z) z‖ ^ 2 := hA
        _ ≤ N1 * ∑ t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
              Dc * Work.Diff.STE.ENormSq m (D.Rper t.1 h t.2.1 t.2.2) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ => ht t) hN1nn
        _ = N1 * Dc * St := by
            have hfac2 : ∀ Y : (ι₀ × (Fin (Module.finrank ℝ E) ×
                Fin (Module.finrank ℝ E))) → ℝ,
                N1 * (∑ t, Dc * Y t) = N1 * Dc * (∑ t, Y t) := by
              intro Y
              simp only [Finset.mul_sum]
              exact Finset.sum_congr rfl fun t _ => by ring
            rw [hSt]
            exact hfac2 _
    -- ## summing over `β`
    have hCEN : Work.Diff.STE.Lead.GalTame.CENormSq m F
        = ∑ β : Fin m → Fin (Module.finrank ℝ E),
            ∫ z in Work.Diff.STE.Lead.GalTame.cubeC (Fin (Module.finrank ℝ E)),
              ‖Work.Diff.STE.pdVec m β F z‖ ^ 2 := rfl
    have hmain : Work.Diff.STE.Lead.GalTame.CENormSq m F ≤ Cnst * St := by
      rw [hCEN]
      calc ∑ β : Fin m → Fin (Module.finrank ℝ E),
            ∫ z in Work.Diff.STE.Lead.GalTame.cubeC (Fin (Module.finrank ℝ E)),
              ‖Work.Diff.STE.pdVec m β F z‖ ^ 2
          ≤ ∑ _β : Fin m → Fin (Module.finrank ℝ E), N1 * Dc * St :=
            Finset.sum_le_sum fun β _ => hbound β
        _ = (Fintype.card (Fin m → Fin (Module.finrank ℝ E)) : ℝ) * (N1 * Dc * St) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = Cnst * St := by rw [hCnst]; ring
    -- ## the triple sum in the statement
    have hSz : St = ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
        ∑ d : Fin (Module.finrank ℝ E), Work.Diff.STE.ENormSq m (D.Rper i h c d) := by
      rw [hSt]
      exact (Work.Diff.STE.B3.sum3_eq_sum_prod
        (f := fun (i : ι₀) (c d : Fin (Module.finrank ℝ E)) =>
          Work.Diff.STE.ENormSq m (D.Rper i h c d))).symm
    rw [hSz] at hmain
    refine hmain.trans ?_
    calc Cnst * (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
          ∑ d : Fin (Module.finrank ℝ E), Work.Diff.STE.ENormSq m (D.Rper i h c d))
        ≤ max 1 Cnst * (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
          ∑ d : Fin (Module.finrank ℝ E), Work.Diff.STE.ENormSq m (D.Rper i h c d)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by rw [← hSz]; exact hStnn)
      _ ≤ max 1 Cnst * (1 + ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
          ∑ d : Fin (Module.finrank ℝ E), Work.Diff.STE.ENormSq m (D.Rper i h c d)) :=
          mul_le_mul_of_nonneg_left (by linarith [hStnn]) (le_trans zero_le_one (le_max_left _ _))
  · refine ⟨0, le_refl 0, ?_⟩
    intro h hsm φ hφ hφb hφs hφt a b
    exact absurd (fun z hz => hφt hz) hKO

end Work.Diff.STE.Lead.GalTame

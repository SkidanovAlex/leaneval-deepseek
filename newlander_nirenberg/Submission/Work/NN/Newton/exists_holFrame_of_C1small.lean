import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Final.Defs
import Submission.Work.NN.Assemble.Setup
import Submission.Work.CR.Flat.Holder
import Submission.Work.NN.Newton.newton_step
import Submission.Work.NN.Newton.C1smallSetup
import Submission.Work.NN.Newton.C1smallRadBounds
import Submission.Work.NN.Newton.C1smallSumBounds
import Submission.Work.NN.Newton.C1smallProdBounds
import Submission.Work.NN.Newton.NNsmoothFork
import Submission.Work.NN.Core.bijective_add_of_norm_comp_lt_one

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/NN/Newton/DESIGN.md first. Your inputs are the sibling lemmas in depends_on (being proved in parallel; build against their statements). Do NOT use Work.NN.Core.dbar_regularity (rests on sorryAx).

# exists_holFrame_of_C1small — guidance

This **replaces** `exists_holFrame_of_small_integrable_aux` in
`Submission/Work/NN/Final/dbarSolvable_of_perturb.lean`. The plug-in is machine-checked: see
`assembly_check.lean.txt`, where `dbarSolvable_of_perturb_C1` compiles from this statement plus
`exists_rescale_C1small`.

## Iteration

1. Get `K, N` from `newton_step`, and `ε₀` from `Work.NN.Final.dbarCn_smooth_local_flex` with
   `ρ = fun _ => 1`, `ρ' = fun _ => 1/2`.
   * Set `ε := min (2^{-5N}/K) (ε₀)` (also `≤ 1`).
   * Note `pd n (fun _ => 1) 4 = polydisc 0 (fun _ => 4)` (by `simp [pd]`).
2. **Radii.** `δ_m = 2^{-(m+3)}`, `r_0 = 4`, `r_{m+1} = r_m(1 − 2δ_m)`.
   * `r_m ≥ 4 ∏(1 − 2^{-(m+2)}) ≥ 4(1 − Σ 2^{-(m+2)}) = 2`. Use Weierstrass, or the elementary
     `∏(1 − x_i) ≥ 1 − Σ x_i`.
3. **Recursion** (`Nat.rec`, or `choose` on `newton_step` packaged as a function of
   `(r, δ, A, a)`).
   * The data at stage `m` are `(A_m, a_m)` with `a_m := a_0 2^{-2Nm}`.
   * Invariant: `A_m` is smooth, almost complex and integrable on `P_{r_m}`, with `C^{1,α}`-size
     `≤ a_m`.
   * Smallness check: `a_m ≤ δ_m^N/K ⇐ a_0 ≤ 2^{-3N}/K`.
   * Next size: `K δ_m^{-N} a_m² ≤ a_{m+1} ⇐ K 2^{5N} a_0 2^{-Nm} ≤ 1`.
   * Corrections: `‖Φ_m − id‖, ‖dΦ_m − 1‖ ≤ K δ_m^{-N} a_m = K 2^{3N} a_0 2^{-Nm} =: β_m`, with
     `Σβ_m ≤ 2K2^{3N}a_0 ≤ 1/8`.
4. **Composites** on `P_1`: `G_{-1} = id`, `G_m = Φ_m ∘ G_{m−1}`.
   * `G_{m−1}(P_1) ⊆ P_{1 + Σβ} ⊆ P_{r_m(1−δ_m)}` (radius `≥ 1.75`), so `Φ_m` is defined there.
   * Intertwining by induction and the chain rule:
     `dG_m z ∘ J z = (Jstd + A_{m+1})(G_m z) ∘ dG_m z`, which needs `G_m z ∈ P_{r_{m+1}}`.
5. **`C¹` convergence.** `‖G_m − G_{m−1}‖ ≤ β_m`, and
   `‖dG_m − dG_{m−1}‖ ≤ β_m ∏_{i<m}(1+β_i) ≤ 2β_m`.
   * So `G_m → G` and `dG_m → L` uniformly on `P_1`.
   * Mathlib `hasFDerivAt_of_tendstoUniformlyOn` (open convex set) gives `fderiv G = L`, and `L`
     is continuous. So each `G_l` is `C¹`.
6. **Holomorphy.** `‖A_{m+1}(G_m z)‖ ≤ a_{m+1} → 0`, so `L z ∘ J z = Jstd ∘ L z`.
   * Hence `fderiv G_l z (J z h) = i · fderiv G_l z h`, so `dbarCn J (G_l) z = 0` (unfold
     `dbarCn_apply`).
   * `‖L − 1‖ ≤ ∏(1+β_i) − 1 < 1`, so `L` is bijective
     (`Work.NN.Core.bijective_add_of_norm_comp_lt_one`).
7. **Smoothness.** `dbarCn_smooth_local_flex` with `f = 0` and `h = G_l` (`C¹` on `P_1`) gives
   `C^k` on `P_{1/2}` for all `k`, hence `ContDiffOn ∞` (`contDiffOn_infty`).
8. Conclude with `V := P_{1/2}` and `u := fun l z => G z l`.
   * `IsHolFrame` (`NN/Assemble/Setup.lean`) wants `ContDiffOn ∞`, `dbarCn J (u j) y = 0`, and the
     bijective `fderiv` of the tuple, which is `L`.

## Traps

* Do not use `Work.NN.Core.dbar_regularity` for smoothness: it depends on `sorryAx`.
* `A 0 = 0` is not needed and not assumed.
* The ranges `r ∈ [1,4]`, `δ ≤ 1/8` of `newton_step` are respected: `r_m ∈ [2,4]`,
  `δ_m ≤ 1/8`.
-/

namespace Work.NN.Newton

open scoped ContDiff
open Set Filter Topology

noncomputable section

/-- The telescoped ``position'' bound `S_m = ∑_{i<m} β_i`. -/
def Ssum (C ε : ℝ) (N : ℕ) (m : ℕ) : ℝ := ∑ i ∈ Finset.range m, bsize C N ε i

/-- The telescoped ``derivative'' bound `Π_m = ∏_{i<m} (1 + β_i)`. -/
def Pprod (C ε : ℝ) (N : ℕ) (m : ℕ) : ℝ := ∏ i ∈ Finset.range m, (1 + bsize C N ε i)

@[simp] lemma Ssum_zero (C ε : ℝ) (N : ℕ) : Ssum C ε N 0 = 0 := by simp [Ssum]

lemma Ssum_succ (C ε : ℝ) (N : ℕ) (m : ℕ) :
    Ssum C ε N (m + 1) = Ssum C ε N m + bsize C N ε m := by
  simp [Ssum, Finset.sum_range_succ]

@[simp] lemma Pprod_zero (C ε : ℝ) (N : ℕ) : Pprod C ε N 0 = 1 := by simp [Pprod]

lemma Pprod_succ (C ε : ℝ) (N : ℕ) (m : ℕ) :
    Pprod C ε N (m + 1) = Pprod C ε N m * (1 + bsize C N ε m) := by
  simp [Pprod, Finset.prod_range_succ]

theorem exists_holFrame_of_C1small {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n,
        (∀ m : ℕ, ContDiffOn ℝ m A (Work.NN.Final.pd n (fun _ => 1) 4)) →
        (∀ z, z ∈ Work.NN.Final.pd n (fun _ => 1) 4 → ∀ v : Work.NN.Core.Cn n,
          (Work.NN.Core.JstdCn n + A) z ((Work.NN.Core.JstdCn n + A) z v) = -v) →
        (∀ u : Work.NN.Core.Cn n → ℂ, (∀ k : ℕ, ContDiff ℝ k u) →
          ∀ z, z ∈ Work.NN.Final.pd n (fun _ => 1) 4 → ∀ V W : Work.NN.Core.Cn n,
            Work.NN.Final.proj02 (Work.NN.Core.JstdCn n + A)
              (fun z' => Work.NN.Final.dOne
                (fun z'' => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z'') z') z V W = 0) →
        (∀ w : Work.NN.Core.Cn n, ‖w‖ ≤ 1 → ∀ j : Fin n,
          Work.CR.Flat.holderNorm 1 α (fun z => A z w j) (Work.NN.Final.pd n (fun _ => 1) 4)
            ≤ ENNReal.ofReal ε) →
        ∃ V : Set (Work.NN.Core.Cn n), IsOpen V ∧ (0 : Work.NN.Core.Cn n) ∈ V ∧
          V ⊆ Work.NN.Final.pd n (fun _ => 1) 4 ∧
          ∃ u : Fin n → Work.NN.Core.Cn n → ℂ,
            Work.NN.Assemble.IsHolFrame (Work.NN.Core.JstdCn n + A) V u := by
  classical
  obtain ⟨C₀, hC₀pos, N₀, hstep₀⟩ := newton_step hn hα0 hα1
  obtain ⟨ε₁, hε₁pos, hsmooth⟩ :=
    Work.NN.Final.dbarCn_smooth_local_flex (n := n) hn hα0 hα1 (ρ := fun _ => 1)
      (ρ' := fun _ => 1 / 2) (fun _ => one_pos) (fun _ => by norm_num) (fun _ => by norm_num)
  set N : ℕ := N₀ + 3 with hNdef
  have hN3 : 3 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hN0le : N₀ ≤ N := by omega
  set ε : ℝ := min (min (1 / ((2 : ℝ) ^ (5 * N) * C₀)) ε₁) 1 with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact lt_min (lt_min (by positivity) hε₁pos) (by norm_num)
  have hεnonneg : 0 ≤ ε := le_of_lt hεpos
  have hεexp : ε ≤ 1 / ((2 : ℝ) ^ (5 * N) * C₀) := by
    rw [hεdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hε1 : ε ≤ 1 := by rw [hεdef]; exact min_le_right _ _
  have hεε₁ : ε ≤ ε₁ := by
    rw [hεdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hεC : C₀ * ε * (2 : ℝ) ^ (5 * N) ≤ 1 := by
    have hpos : 0 < (2 : ℝ) ^ (5 * N) * C₀ := by positivity
    calc C₀ * ε * (2 : ℝ) ^ (5 * N) = ε * ((2 : ℝ) ^ (5 * N) * C₀) := by ring
      _ ≤ (1 / ((2 : ℝ) ^ (5 * N) * C₀)) * ((2 : ℝ) ^ (5 * N) * C₀) :=
            mul_le_mul_of_nonneg_right hεexp (le_of_lt hpos)
      _ = 1 := by field_simp
  refine ⟨ε, hεpos, ?_⟩
  intro A hAsm hJac hint hsmall
  -- ## the arithmetic inputs
  have hradm : ∀ m : ℕ, (0:ℝ) < delta m ∧ delta m ≤ 1/8 ∧ (1:ℝ) ≤ rad m ∧ rad m ≤ 4 ∧
      (1:ℝ) < rad m * (1 - delta m) ∧ (2:ℝ) ≤ rad m * (1 - 2 * delta m) :=
    C1smallRadBounds
  obtain ⟨hasize0, hasizele, hbsize0, hbsizele, hsumle, hIcole⟩ :=
    C1smallSumBounds (C := C₀) (ε := ε) (N := N) hC₀pos hN3 hεnonneg hεC
  obtain ⟨hprodle, hnext, hsmallsize⟩ :=
    C1smallProdBounds (C := C₀) (ε := ε) (N := N) hC₀pos hN3 hεnonneg hεC
  have hrad2 : ∀ m : ℕ, (2:ℝ) ≤ rad m := by
    intro m
    cases m with
    | zero => rw [rad_zero]; norm_num
    | succ k => simpa using (hradm k).2.2.2.2.2
  have hrad_32 : ∀ m : ℕ, (3/2:ℝ) ≤ rad m := fun m => le_trans (by norm_num) (hrad2 m)
  have hrad_32' : ∀ m : ℕ, (3/2:ℝ) ≤ rad m * (1 - delta m) := by
    intro m
    obtain ⟨hδ0, hδ8, -, -, -, -⟩ := hradm m
    have h2 := hrad2 m
    nlinarith [hδ8, h2]
  have hrad_next : ∀ m : ℕ, (3/2:ℝ) ≤ rad m * (1 - 2 * delta m) := by
    intro m
    have h := hrad_32 (m+1)
    rwa [rad_succ] at h
  -- ## the invariant at stage `0`
  have h0 : NNInv n α N ε 0 A := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k
      have h := hAsm k
      rwa [rad_zero, P_eq_pd]
    · intro z hz v
      rw [rad_zero, P_eq_pd] at hz
      exact hJac z hz v
    · intro u hu z hz V W
      rw [rad_zero, P_eq_pd] at hz
      exact hint u hu z hz V W
    · intro w hw j
      rw [rad_zero, P_eq_pd]
      simpa [asize] using hsmall w hw j
  -- ## one Newton step
  have H : ∀ (m : ℕ) (B : Cn n → Cn n →L[ℝ] Cn n), NNInv n α N ε m B →
      ∃ p : (Cn n → Cn n) × (Cn n → Cn n →L[ℝ] Cn n),
        NNStep n α C₀ N ε m B p.1 p.2 := by
    intro m B hInv
    obtain ⟨hBsm, hBac, hBint, hBsz⟩ := hInv
    obtain ⟨hδ0, hδ8, hr1, hr4, -, -⟩ := hradm m
    have ha0 : (0:ℝ) ≤ asize ε N m := hasize0 m
    have hδle1 : delta m ≤ 1 := by linarith
    have hpow : delta m ^ N ≤ delta m ^ N₀ :=
      pow_le_pow_of_le_one (le_of_lt hδ0) hδle1 hN0le
    have hbmono : C₀ / delta m ^ N₀ ≤ C₀ / delta m ^ N :=
      div_le_div_of_nonneg_left (le_of_lt hC₀pos) (pow_pos hδ0 N) hpow
    have ha_le : asize ε N m ≤ delta m ^ N₀ / C₀ :=
      (hsmallsize m).trans (div_le_div_of_nonneg_right hpow (le_of_lt hC₀pos))
    obtain ⟨Φ, hΦ⟩ := hstep₀ (rad m) (delta m) hr1 hr4 hδ0 hδ8 B hBsm hBac hBint
      (asize ε N m) ha0 ha_le hBsz
    obtain ⟨hΦsm, -, -, hΦn, hΦd, B', hB'sm, hintw, hB'ac, hB'int, hB'sz⟩ := hΦ
    refine ⟨(Φ, B'), ?_⟩
    refine ⟨hΦsm, ?_, ?_, hB'sm, hintw, hB'ac, hB'int, ?_⟩
    · intro z hz
      simp only [bsize]
      exact (hΦn z hz).trans (mul_le_mul_of_nonneg_right hbmono ha0)
    · intro z hz
      simp only [bsize]
      exact (hΦd z hz).trans (mul_le_mul_of_nonneg_right hbmono ha0)
    · intro w hw j
      refine (hB'sz w hw j).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right hbmono (sq_nonneg _)
  -- ## the iteration
  set bld : (m : ℕ) → Stage n α C₀ N ε m := build n α C₀ N ε A h0 hnext H with hbldeq
  set G : ℕ → Cn n → Cn n := Gseq bld with hGeq
  have hG0 : G 0 = id := by rw [hGeq]; rfl
  have hGsucc : ∀ m, G (m + 1) = (bld m).Φ ∘ G m := fun m => by
    rw [hGeq]; exact Gseq_succ m
  have hbldAs : ∀ m, (bld (m + 1)).A = (bld m).A' := fun m => by
    rw [hbldeq]
    exact build_succ (n := n) (α := α) (C := C₀) (N := N) (ε := ε) (A₀ := A)
      (h0 := h0) (hnext := hnext) (H := H) m
  have hbldA0 : (bld 0).A = A := by
    rw [hbldeq]
    exact build_zero (n := n) (α := α) (C := C₀) (N := N) (ε := ε) (A₀ := A)
      (h0 := h0) (hnext := hnext) (H := H)
  -- ## the induction
  have hmain : ∀ m : ℕ,
      (∀ z, z ∈ P n 1 → ‖G m z - z‖ ≤ Ssum C₀ ε N m) ∧
      (∀ z, z ∈ P n 1 → G m z ∈ P n (3/2)) ∧
      (∀ z, z ∈ P n 1 → DifferentiableAt ℝ (G m) z) ∧
      (∀ z, z ∈ P n 1 → ‖fderiv ℝ (G m) z‖ ≤ Pprod C₀ ε N m) ∧
      (∀ z, z ∈ P n 1 → fderiv ℝ (G m) z ∘SL ((Work.NN.Core.JstdCn n + A) z)
          = (Work.NN.Core.JstdCn n + (bld m).A) (G m z) ∘SL fderiv ℝ (G m) z) := by
    intro m
    induction m with
    | zero =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro z hz
        have hz' : G 0 z = z := by rw [hG0]; rfl
        rw [hz', sub_self]
        simp
      · intro z hz
        rw [mem_P]
        intro j
        have h1 : ‖z j‖ < 1 := (mem_P.mp hz) j
        have hz' : G 0 z = z := by rw [hG0]; rfl
        rw [hz']
        linarith
      · intro z hz
        rw [hG0]
        exact differentiableAt_id
      · intro z hz
        rw [hG0]
        have := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := Cn n)
        simpa [Pprod_zero] using this
      · intro z hz
        rw [hG0, hbldA0, fderiv_id]
        apply ContinuousLinearMap.ext
        intro v
        simp
    | succ m ih =>
      obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ := ih
      have hstep := (bld m).hStep
      have hmem : ∀ z ∈ P n 1, G m z ∈ P n (rad m * (1 - delta m)) :=
        fun z hz => P_mono (hrad_32' m) (ih2 z hz)
      have hPhiDiff : ∀ y ∈ P n (rad m * (1 - delta m)), DifferentiableAt ℝ (bld m).Φ y := by
        intro y hy
        exact ((hstep.1 1).contDiffAt ((isOpen_P n _).mem_nhds hy)).differentiableAt
          (by norm_num)
      have hball3 : ∀ z ∈ P n 1, ‖G (m + 1) z - z‖ ≤ Ssum C₀ ε N (m+1) := by
        intro z hz
        have hb := hstep.2.1 (G m z) (hmem z hz)
        have hid : G (m + 1) z - z = ((bld m).Φ (G m z) - G m z) + (G m z - z) := by
          rw [hGsucc]; simp only [Function.comp_apply]; abel
        rw [hid]
        refine (norm_add_le _ _).trans ?_
        rw [Ssum_succ]
        linarith [hb, ih1 z hz]
      have hc3 : ∀ z ∈ P n 1, G (m + 1) z ∈ P n (3/2) := by
        intro z hz
        rw [mem_P]
        have h1 : ‖z‖ < 1 := (pi_norm_lt_iff one_pos).mpr fun j => (mem_P.mp hz) j
        have hS : Ssum C₀ ε N (m+1) ≤ 1/32 := hsumle (m+1)
        have h2 : ‖G (m + 1) z‖ < 1 + 1/32 := by
          calc ‖G (m + 1) z‖ = ‖z + (G (m + 1) z - z)‖ := by congr 1; abel
            _ ≤ ‖z‖ + ‖G (m + 1) z - z‖ := norm_add_le _ _
            _ < 1 + 1/32 := by linarith [hball3 z hz, hS]
        intro j
        calc ‖G (m + 1) z j‖ ≤ ‖G (m + 1) z‖ := norm_le_pi_norm _ j
          _ < 3/2 := by linarith
      have hΦmem : ∀ z ∈ P n 1, (bld m).Φ (G m z) ∈ P n (rad m * (1 - 2 * delta m)) := by
        intro z hz
        have h1 : G (m + 1) z ∈ P n (3/2) := hc3 z hz
        have h2 : G (m + 1) z = (bld m).Φ (G m z) := by rw [hGsucc]; rfl
        rw [← h2]
        exact P_mono (hrad_next m) h1
      refine ⟨hball3, hc3, ?_, ?_, ?_⟩
      · intro z hz
        rw [hGsucc]
        exact (hPhiDiff (G m z) (hmem z hz)).comp z (ih3 z hz)
      · intro z hz
        have h1 : DifferentiableAt ℝ (bld m).Φ (G m z) := hPhiDiff (G m z) (hmem z hz)
        have h2 : DifferentiableAt ℝ (G m) z := ih3 z hz
        have hchain : fderiv ℝ (G (m + 1)) z
            = fderiv ℝ (bld m).Φ (G m z) ∘SL fderiv ℝ (G m) z := by
          rw [hGsucc, fderiv_comp z h1 h2]
        rw [hchain]
        have hb := hstep.2.2.1 (G m z) (hmem z hz)
        have h3 : ‖fderiv ℝ (bld m).Φ (G m z)‖ ≤ 1 + bsize C₀ N ε m := by
          have hone : ‖(1 : Cn n →L[ℝ] Cn n)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
          calc ‖fderiv ℝ (bld m).Φ (G m z)‖
              = ‖(fderiv ℝ (bld m).Φ (G m z) - 1) + 1‖ := by rw [sub_add_cancel]
            _ ≤ ‖fderiv ℝ (bld m).Φ (G m z) - 1‖ + ‖(1 : Cn n →L[ℝ] Cn n)‖ :=
                  norm_add_le _ _
            _ ≤ bsize C₀ N ε m + 1 := add_le_add hb hone
            _ = 1 + bsize C₀ N ε m := by ring
        rw [Pprod_succ]
        calc ‖fderiv ℝ (bld m).Φ (G m z) ∘SL fderiv ℝ (G m) z‖
            ≤ ‖fderiv ℝ (bld m).Φ (G m z)‖ * ‖fderiv ℝ (G m) z‖ :=
                ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ (1 + bsize C₀ N ε m) * Pprod C₀ ε N m :=
                mul_le_mul h3 (ih4 z hz) (norm_nonneg _) (by linarith [hbsize0 m])
          _ = Pprod C₀ ε N m * (1 + bsize C₀ N ε m) := by ring
      · intro z hz
        have h1 : DifferentiableAt ℝ (bld m).Φ (G m z) := hPhiDiff (G m z) (hmem z hz)
        have h2 : DifferentiableAt ℝ (G m) z := ih3 z hz
        have hchain : fderiv ℝ (G (m + 1)) z
            = fderiv ℝ (bld m).Φ (G m z) ∘SL fderiv ℝ (G m) z := by
          rw [hGsucc, fderiv_comp z h1 h2]
        have hint : fderiv ℝ (bld m).Φ (G m z) ∘SL (Work.NN.Core.JstdCn n + (bld m).A) (G m z)
            = (Work.NN.Core.JstdCn n + (bld (m + 1)).A) ((bld m).Φ (G m z))
              ∘SL fderiv ℝ (bld m).Φ (G m z) := by
          apply ContinuousLinearMap.ext
          intro v
          have hh := hstep.2.2.2.2.1 (G m z) (hmem z hz) (hΦmem z hz) v
          rw [hbldAs m]
          simpa only [ContinuousLinearMap.comp_apply] using hh
        have hGm : (bld m).Φ (G m z) = G (m + 1) z := by rw [hGsucc]; rfl
        calc fderiv ℝ (G (m + 1)) z ∘SL ((Work.NN.Core.JstdCn n + A) z)
            = (fderiv ℝ (bld m).Φ (G m z) ∘SL fderiv ℝ (G m) z)
                ∘SL ((Work.NN.Core.JstdCn n + A) z) := by rw [hchain]
          _ = fderiv ℝ (bld m).Φ (G m z)
                ∘SL (fderiv ℝ (G m) z ∘SL ((Work.NN.Core.JstdCn n + A) z)) := by
                rw [ContinuousLinearMap.comp_assoc]
          _ = fderiv ℝ (bld m).Φ (G m z)
                ∘SL ((Work.NN.Core.JstdCn n + (bld m).A) (G m z)
                  ∘SL fderiv ℝ (G m) z) := by rw [ih5 z hz]
          _ = (fderiv ℝ (bld m).Φ (G m z) ∘SL (Work.NN.Core.JstdCn n + (bld m).A) (G m z))
                ∘SL fderiv ℝ (G m) z := by rw [ContinuousLinearMap.comp_assoc]
          _ = ((Work.NN.Core.JstdCn n + (bld (m + 1)).A) ((bld m).Φ (G m z))
                ∘SL fderiv ℝ (bld m).Φ (G m z)) ∘SL fderiv ℝ (G m) z := by rw [hint]
          _ = (Work.NN.Core.JstdCn n + (bld (m + 1)).A) (G (m + 1) z)
                ∘SL fderiv ℝ (G (m + 1)) z := by
                rw [ContinuousLinearMap.comp_assoc, ← hchain, hGm]
  --------------------------------------------------------------------------------
  -- ## increments and telescoping
  --------------------------------------------------------------------------------
  have hincr : ∀ m z, z ∈ P n 1 → ‖G (m + 1) z - G m z‖ ≤ bsize C₀ N ε m := by
    intro m z hz
    have hmem : G m z ∈ P n (rad m * (1 - delta m)) :=
      P_mono (hrad_32' m) ((hmain m).2.1 z hz)
    have hb := (bld m).hStep.2.1 (G m z) hmem
    have h1 : G (m + 1) z = (bld m).Φ (G m z) := by rw [hGsucc]; rfl
    rwa [h1]
  have htel : ∀ k m, k ≤ m → ∀ z ∈ P n 1,
      ‖G m z - G k z‖ ≤ ∑ i ∈ Finset.Ico k m, bsize C₀ N ε i := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base => intro z hz; simp
    | succ m hkm ih =>
        intro z hz
        have h1 : G (m + 1) z - G k z = (G (m + 1) z - G m z) + (G m z - G k z) := by abel
        rw [h1]
        calc ‖(G (m + 1) z - G m z) + (G m z - G k z)‖
            ≤ ‖G (m + 1) z - G m z‖ + ‖G m z - G k z‖ := norm_add_le _ _
          _ ≤ bsize C₀ N ε m + ∑ i ∈ Finset.Ico k m, bsize C₀ N ε i :=
              add_le_add (hincr m z hz) (ih z hz)
          _ = ∑ i ∈ Finset.Ico k (m + 1), bsize C₀ N ε i := by
              rw [Finset.sum_Ico_succ_top hkm]; ring
  --------------------------------------------------------------------------------
  -- ## geometric majorants
  --------------------------------------------------------------------------------
  have hgeo : Tendsto (fun k : ℕ => ((1 / 2 : ℝ) ^ N) ^ k) atTop (𝓝 0) := by
    refine tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ?_
    calc (1 / 2 : ℝ) ^ N ≤ (1 / 2 : ℝ) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hN1
      _ = 1 / 2 := by norm_num
      _ < 1 := by norm_num
  have hDtend : Tendsto (fun k : ℕ => (2 * C₀ * ε * (2 : ℝ) ^ (3 * N)) * (1 / 2 : ℝ) ^ (N * k))
      atTop (𝓝 0) := by
    have h : Tendsto (fun k : ℕ => (2 * C₀ * ε * (2 : ℝ) ^ (3 * N)) * ((1 / 2 : ℝ) ^ N) ^ k)
        atTop (𝓝 0) := by
      simpa using hgeo.const_mul (2 * C₀ * ε * (2 : ℝ) ^ (3 * N))
    simpa only [pow_mul] using h
  have hDnn : (0 : ℝ) ≤ 2 * C₀ * ε * (2 : ℝ) ^ (3 * N) := by positivity
  have hgeo2 : Tendsto (fun k : ℕ => ((1 / 2 : ℝ) ^ (2 * N)) ^ k) atTop (𝓝 0) := by
    refine tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ?_
    calc (1 / 2 : ℝ) ^ (2 * N) ≤ (1 / 2 : ℝ) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 2 := by norm_num
      _ < 1 := by norm_num
  have hasize_tend : Tendsto (fun m : ℕ => asize ε N m) atTop (𝓝 0) := by
    have h : Tendsto (fun k : ℕ => ε * ((1 / 2 : ℝ) ^ (2 * N)) ^ k) atTop (𝓝 0) := by
      simpa using hgeo2.const_mul ε
    simpa [asize, pow_mul] using h
  --------------------------------------------------------------------------------
  -- ## the position limit
  --------------------------------------------------------------------------------
  have hGcauchy : ∀ z ∈ P n 1, CauchySeq (fun m => G m z) := by
    intro z hz
    rw [Metric.cauchySeq_iff]
    intro e he
    obtain ⟨k, hk⟩ := (Metric.tendsto_atTop.mp hDtend) (e / 2) (by linarith)
    refine ⟨k, fun m hm q hq => ?_⟩
    have hDk : (2 * C₀ * ε * (2 : ℝ) ^ (3 * N)) * (1 / 2 : ℝ) ^ (N * k) < e / 2 := by
      have hh : ‖(2 * C₀ * ε * (2 : ℝ) ^ (3 * N)) * (1 / 2 : ℝ) ^ (N * k)‖ < e / 2 := by
        simpa using hk k le_rfl
      rwa [Real.norm_of_nonneg (mul_nonneg hDnn (by positivity))] at hh
    have hmk : ‖G m z - G k z‖ ≤ (2 * C₀ * ε * (2 : ℝ) ^ (3 * N)) * (1 / 2 : ℝ) ^ (N * k) :=
      (htel k m hm z hz).trans (hIcole k m)
    have hqk : ‖G q z - G k z‖ ≤ (2 * C₀ * ε * (2 : ℝ) ^ (3 * N)) * (1 / 2 : ℝ) ^ (N * k) :=
      (htel k q hq z hz).trans (hIcole k q)
    calc dist (G m z) (G q z) = ‖G m z - G q z‖ := dist_eq_norm _ _
      _ ≤ ‖G m z - G k z‖ + ‖G q z - G k z‖ := by
            have h2 : G m z - G q z = (G m z - G k z) - (G q z - G k z) := by abel
            rw [h2]; exact norm_sub_le _ _
      _ ≤ 2 * ((2 * C₀ * ε * (2 : ℝ) ^ (3 * N)) * (1 / 2 : ℝ) ^ (N * k)) := by linarith
      _ < e := by linarith
  have hGlim_ex : ∀ z ∈ P n 1, ∃ w : Cn n, Tendsto (fun m => G m z) atTop (𝓝 w) :=
    fun z hz => cauchySeq_tendsto_of_complete (hGcauchy z hz)
  set Glim : Cn n → Cn n :=
    fun z => if h : z ∈ P n 1 then Classical.choose (hGlim_ex z h) else 0 with hGlimdef
  have hGlim_tend : ∀ z (hz : z ∈ P n 1), Tendsto (fun m => G m z) atTop (𝓝 (Glim z)) := by
    intro z hz
    rw [hGlimdef]
    simp only [dif_pos hz]
    exact Classical.choose_spec (hGlim_ex z hz)
  have hGlim_bound : ∀ m z, z ∈ P n 1 →
      ‖Glim z - G m z‖ ≤ (2 * C₀ * ε * (2 : ℝ) ^ (3 * N)) * (1 / 2 : ℝ) ^ (N * m) := by
    intro m z hz
    have htend : Tendsto (fun p : ℕ => ‖G p z - G m z‖) atTop (𝓝 (‖Glim z - G m z‖)) :=
      ((hGlim_tend z hz).sub_const (G m z)).norm
    refine le_of_tendsto htend ?_
    filter_upwards [Filter.eventually_ge_atTop m] with p hp
    exact (htel m p hp z hz).trans (hIcole m p)
  have hGunif : TendstoUniformlyOn (fun m => G m) Glim atTop (P n 1) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro e he
    obtain ⟨k, hk⟩ := (Metric.tendsto_atTop.mp hDtend) (e / 2) (by linarith)
    rw [Filter.eventually_atTop]
    refine ⟨k, fun m hm z hz => ?_⟩
    have hDk : (2 * C₀ * ε * (2 : ℝ) ^ (3 * N)) * (1 / 2 : ℝ) ^ (N * m) < e / 2 := by
      have hh : ‖(2 * C₀ * ε * (2 : ℝ) ^ (3 * N)) * (1 / 2 : ℝ) ^ (N * k)‖ < e / 2 := by
        simpa using hk k le_rfl
      rw [Real.norm_of_nonneg (mul_nonneg hDnn (by positivity))] at hh
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.mul_le_mul_left N hm)) hDnn) hh
    calc dist (Glim z) (G m z) = ‖Glim z - G m z‖ := dist_eq_norm _ _
      _ ≤ (2 * C₀ * ε * (2 : ℝ) ^ (3 * N)) * (1 / 2 : ℝ) ^ (N * m) := hGlim_bound m z hz
      _ < e := by linarith
  --------------------------------------------------------------------------------
  -- ## the perturbation is uniformly small in the operator norm
  --------------------------------------------------------------------------------
  have hAbound : ∀ m (z' : Cn n), z' ∈ P n (rad m) → ∀ u : Cn n,
      ‖(bld m).A z' u‖ ≤ asize ε N m * ‖u‖ := by
    intro m z' hz' u
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg (hasize0 m) (norm_nonneg u))]
    intro j
    rcases eq_or_ne ‖u‖ 0 with hu | hu
    · have huz : u = 0 := norm_eq_zero.mp hu
      rw [huz, map_zero]
      simp
    · have hpos : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg u) (Ne.symm hu)
      have hw : ‖(‖u‖⁻¹ : ℝ) • u‖ ≤ 1 := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg u)),
          inv_mul_cancel₀ (ne_of_gt hpos)]
      have h1 : ‖(bld m).A z' ((‖u‖⁻¹ : ℝ) • u) j‖ ≤ asize ε N m := by
        have h2 := (bld m).hInv.2.2.2 ((‖u‖⁻¹ : ℝ) • u) hw j
        have h3 := Work.CR.Flat.norm_apply_le_holderNorm 1 α
          (fun z => (bld m).A z ((‖u‖⁻¹ : ℝ) • u) j) (P n (rad m)) hz'
        exact (ENNReal.ofReal_le_ofReal_iff (hasize0 m)).mp (h3.trans h2)
      have h4 : (bld m).A z' u = ‖u‖ • ((bld m).A z' ((‖u‖⁻¹ : ℝ) • u)) := by
        rw [map_smul, smul_smul, mul_inv_cancel₀ (ne_of_gt hpos), one_smul]
      rw [h4, Pi.smul_apply, norm_smul, Real.norm_of_nonneg (norm_nonneg u)]
      calc ‖u‖ * ‖(bld m).A z' ((‖u‖⁻¹ : ℝ) • u) j‖ ≤ ‖u‖ * asize ε N m :=
            mul_le_mul_of_nonneg_left h1 (norm_nonneg u)
        _ = asize ε N m * ‖u‖ := by ring
  --------------------------------------------------------------------------------
  -- ## the derivative increments and telescoping
  --------------------------------------------------------------------------------
  have hdin : ∀ m z, z ∈ P n 1 →
      ‖fderiv ℝ (G (m + 1)) z - fderiv ℝ (G m) z‖ ≤ bsize C₀ N ε m * (32 / 31) := by
    intro m z hz
    have hmem : G m z ∈ P n (rad m * (1 - delta m)) :=
      P_mono (hrad_32' m) ((hmain m).2.1 z hz)
    have h1 : DifferentiableAt ℝ (bld m).Φ (G m z) :=
      (((bld m).hStep.1 1).contDiffAt ((isOpen_P n _).mem_nhds hmem)).differentiableAt (by norm_num)
    have h2 : DifferentiableAt ℝ (G m) z := (hmain m).2.2.1 z hz
    have hchain : fderiv ℝ (G (m + 1)) z
        = fderiv ℝ (bld m).Φ (G m z) ∘SL fderiv ℝ (G m) z := by
      rw [hGsucc, fderiv_comp z h1 h2]
    have hsub : fderiv ℝ (G (m + 1)) z - fderiv ℝ (G m) z
        = (fderiv ℝ (bld m).Φ (G m z) - 1) ∘SL fderiv ℝ (G m) z := by
      rw [hchain]
      apply ContinuousLinearMap.ext
      intro v
      simp
    rw [hsub]
    calc ‖(fderiv ℝ (bld m).Φ (G m z) - 1) ∘SL fderiv ℝ (G m) z‖
        ≤ ‖fderiv ℝ (bld m).Φ (G m z) - 1‖ * ‖fderiv ℝ (G m) z‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ bsize C₀ N ε m * (32 / 31) :=
            mul_le_mul ((bld m).hStep.2.2.1 (G m z) hmem)
              (((hmain m).2.2.2.1 z hz).trans (hprodle m)) (norm_nonneg _) (hbsize0 m)
  have hdtel : ∀ k m, k ≤ m → ∀ z ∈ P n 1,
      ‖fderiv ℝ (G m) z - fderiv ℝ (G k) z‖
        ≤ (32 / 31) * ∑ i ∈ Finset.Ico k m, bsize C₀ N ε i := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base => intro z hz; simp
    | succ m hkm ih =>
        intro z hz
        have h1 : fderiv ℝ (G (m + 1)) z - fderiv ℝ (G k) z
            = (fderiv ℝ (G (m + 1)) z - fderiv ℝ (G m) z)
              + (fderiv ℝ (G m) z - fderiv ℝ (G k) z) := by abel
        rw [h1]
        refine (norm_add_le _ _).trans ?_
        rw [Finset.sum_Ico_succ_top hkm]
        calc ‖fderiv ℝ (G (m + 1)) z - fderiv ℝ (G m) z‖
              + ‖fderiv ℝ (G m) z - fderiv ℝ (G k) z‖
            ≤ bsize C₀ N ε m * (32 / 31) + (32 / 31) * ∑ i ∈ Finset.Ico k m, bsize C₀ N ε i :=
              add_le_add (hdin m z hz) (ih z hz)
          _ = (32 / 31) * (∑ i ∈ Finset.Ico k m, bsize C₀ N ε i + bsize C₀ N ε m) := by ring
  have hD2tend : Tendsto
      (fun k : ℕ => (32 / 31) * ((2 * C₀ * ε * (2 : ℝ) ^ (3 * N)) * (1 / 2 : ℝ) ^ (N * k)))
      atTop (𝓝 0) := by
    simpa using hDtend.const_mul (32 / 31)
  have hLcauchy : ∀ z ∈ P n 1, CauchySeq (fun m => fderiv ℝ (G m) z) := by
    intro z hz
    rw [Metric.cauchySeq_iff]
    intro e he
    obtain ⟨k, hk⟩ := (Metric.tendsto_atTop.mp hD2tend) (e / 2) (by linarith)
    refine ⟨k, fun m hm q hq => ?_⟩
    have hDk : (32 / 31) * ((2 * C₀ * ε * (2 : ℝ) ^ (3 * N)) * (1 / 2 : ℝ) ^ (N * k)) < e / 2 := by
      have hh : ‖(32 / 31) * ((2 * C₀ * ε * (2 : ℝ) ^ (3 * N)) * (1 / 2 : ℝ) ^ (N * k))‖ < e / 2 := by
        simpa using hk k le_rfl
      rwa [Real.norm_of_nonneg (mul_nonneg (by norm_num) (mul_nonneg hDnn (by positivity)))] at hh
    have hmk : ‖fderiv ℝ (G m) z - fderiv ℝ (G k) z‖
        ≤ (32 / 31) * ((2 * C₀ * ε * (2 : ℝ) ^ (3 * N)) * (1 / 2 : ℝ) ^ (N * k)) :=
      (hdtel k m hm z hz).trans (mul_le_mul_of_nonneg_left (hIcole k m) (by norm_num))
    have hqk : ‖fderiv ℝ (G q) z - fderiv ℝ (G k) z‖
        ≤ (32 / 31) * ((2 * C₀ * ε * (2 : ℝ) ^ (3 * N)) * (1 / 2 : ℝ) ^ (N * k)) :=
      (hdtel k q hq z hz).trans (mul_le_mul_of_nonneg_left (hIcole k q) (by norm_num))
    calc dist (fderiv ℝ (G m) z) (fderiv ℝ (G q) z)
        = ‖fderiv ℝ (G m) z - fderiv ℝ (G q) z‖ := dist_eq_norm _ _
      _ ≤ ‖fderiv ℝ (G m) z - fderiv ℝ (G k) z‖
            + ‖fderiv ℝ (G q) z - fderiv ℝ (G k) z‖ := by
            have h2 : fderiv ℝ (G m) z - fderiv ℝ (G q) z
                = (fderiv ℝ (G m) z - fderiv ℝ (G k) z)
                  - (fderiv ℝ (G q) z - fderiv ℝ (G k) z) := by abel
            rw [h2]; exact norm_sub_le _ _
      _ ≤ 2 * ((32 / 31) * ((2 * C₀ * ε * (2 : ℝ) ^ (3 * N)) * (1 / 2 : ℝ) ^ (N * k))) := by
            linarith
      _ < e := by linarith
  have hLlim_ex : ∀ z ∈ P n 1, ∃ L : Cn n →L[ℝ] Cn n, Tendsto (fun m => fderiv ℝ (G m) z) atTop (𝓝 L) :=
    fun z hz => cauchySeq_tendsto_of_complete (hLcauchy z hz)
  set Llim : Cn n → Cn n →L[ℝ] Cn n :=
    fun z => if h : z ∈ P n 1 then Classical.choose (hLlim_ex z h) else 0 with hLlimdef
  have hLlim_tend : ∀ z (hz : z ∈ P n 1),
      Tendsto (fun m => fderiv ℝ (G m) z) atTop (𝓝 (Llim z)) := by
    intro z hz
    rw [hLlimdef]
    simp only [dif_pos hz]
    exact Classical.choose_spec (hLlim_ex z hz)
  have hLlim_bound : ∀ m z, z ∈ P n 1 →
      ‖fderiv ℝ (G m) z - Llim z‖
        ≤ (32 / 31) * ((2 * C₀ * ε * (2 : ℝ) ^ (3 * N)) * (1 / 2 : ℝ) ^ (N * m)) := by
    intro m z hz
    have htend : Tendsto (fun p : ℕ => ‖fderiv ℝ (G p) z - fderiv ℝ (G m) z‖) atTop
        (𝓝 (‖Llim z - fderiv ℝ (G m) z‖)) :=
      (((hLlim_tend z hz).sub_const (fderiv ℝ (G m) z)).norm)
    have hb : ‖Llim z - fderiv ℝ (G m) z‖
        ≤ (32 / 31) * ((2 * C₀ * ε * (2 : ℝ) ^ (3 * N)) * (1 / 2 : ℝ) ^ (N * m)) := by
      refine le_of_tendsto htend ?_
      filter_upwards [Filter.eventually_ge_atTop m] with p hp
      exact (hdtel m p hp z hz).trans (mul_le_mul_of_nonneg_left (hIcole m p) (by norm_num))
    rwa [norm_sub_rev] at hb
  have hLunif : TendstoUniformlyOn (fun m => fderiv ℝ (G m)) Llim atTop (P n 1) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro e he
    obtain ⟨k, hk⟩ := (Metric.tendsto_atTop.mp hD2tend) (e / 2) (by linarith)
    rw [Filter.eventually_atTop]
    refine ⟨k, fun m hm z hz => ?_⟩
    have hDk : (32 / 31) * ((2 * C₀ * ε * (2 : ℝ) ^ (3 * N)) * (1 / 2 : ℝ) ^ (N * m)) < e / 2 := by
      have hh : ‖(32 / 31) * ((2 * C₀ * ε * (2 : ℝ) ^ (3 * N)) * (1 / 2 : ℝ) ^ (N * k))‖ < e / 2 := by
        simpa using hk k le_rfl
      rw [Real.norm_of_nonneg (mul_nonneg (by norm_num) (mul_nonneg hDnn (by positivity)))] at hh
      refine lt_of_le_of_lt ?_ hh
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.mul_le_mul_left N hm)) hDnn
    calc dist (Llim z) (fderiv ℝ (G m) z) = ‖Llim z - fderiv ℝ (G m) z‖ := dist_eq_norm _ _
      _ = ‖fderiv ℝ (G m) z - Llim z‖ := norm_sub_rev _ _
      _ ≤ (32 / 31) * ((2 * C₀ * ε * (2 : ℝ) ^ (3 * N)) * (1 / 2 : ℝ) ^ (N * m)) :=
            hLlim_bound m z hz
      _ < e := by linarith
  --------------------------------------------------------------------------------
  -- ## the limit is differentiable with derivative `Llim`
  --------------------------------------------------------------------------------
  have hfd : ∀ z ∈ P n 1, HasFDerivAt Glim (Llim z) z := by
    intro z hz
    refine hasFDerivAt_of_tendstoUniformlyOn (s := P n 1) (f := fun m => G m)
      (isOpen_P n 1) hLunif ?_ ?_ hz
    · intro m x hx
      exact ((hmain m).2.2.1 x hx).hasFDerivAt
    · intro x hx
      exact hGlim_tend x hx
  have hfderivG : ∀ z ∈ P n 1, fderiv ℝ Glim z = Llim z := fun z hz => (hfd z hz).fderiv
  have hGlimDiff : ∀ z ∈ P n 1, DifferentiableAt ℝ Glim z := fun z hz => (hfd z hz).differentiableAt
  --------------------------------------------------------------------------------
  -- ## the limit intertwines `J` and `Jstd`
  --------------------------------------------------------------------------------
  have hGlimInter : ∀ z ∈ P n 1,
      fderiv ℝ Glim z ∘SL ((Work.NN.Core.JstdCn n + A) z)
        = Work.NN.Core.JstdCn n (Glim z) ∘SL fderiv ℝ Glim z := by
    intro z hz
    have hLm_tend := hLlim_tend z hz
    apply ContinuousLinearMap.ext
    intro v
    have hLv : Tendsto (fun m : ℕ => fderiv ℝ (G m) z v) atTop (𝓝 (Llim z v)) :=
      ((ContinuousLinearMap.apply ℝ (Cn n) v).continuous.tendsto (Llim z)).comp hLm_tend
    have hev1 : Tendsto (fun m : ℕ => fderiv ℝ (G m) z ((Work.NN.Core.JstdCn n + A) z v))
        atTop (𝓝 (Llim z ((Work.NN.Core.JstdCn n + A) z v))) :=
      ((ContinuousLinearMap.apply ℝ (Cn n) ((Work.NN.Core.JstdCn n + A) z v)).continuous.tendsto
        (Llim z)).comp hLm_tend
    have hbd : ∀ m, ‖(bld m).A (G m z) (fderiv ℝ (G m) z v)‖ ≤
        (2 * ‖v‖) * asize ε N m := by
      intro m
      have hmem : G m z ∈ P n (rad m) :=
        P_mono (by linarith [hrad_32 m]) ((hmain m).2.1 z hz)
      refine (hAbound m (G m z) hmem (fderiv ℝ (G m) z v)).trans ?_
      have h1 : ‖fderiv ℝ (G m) z v‖ ≤ 2 * ‖v‖ := by
        calc ‖fderiv ℝ (G m) z v‖ ≤ ‖fderiv ℝ (G m) z‖ * ‖v‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ (32 / 31) * ‖v‖ :=
              mul_le_mul_of_nonneg_right (((hmain m).2.2.2.1 z hz).trans (hprodle m))
                (norm_nonneg _)
          _ ≤ 2 * ‖v‖ := mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _)
      calc asize ε N m * ‖fderiv ℝ (G m) z v‖ ≤ asize ε N m * (2 * ‖v‖) :=
            mul_le_mul_of_nonneg_left h1 (hasize0 m)
        _ = (2 * ‖v‖) * asize ε N m := by ring
    have h2 : Tendsto (fun m : ℕ => (bld m).A (G m z) (fderiv ℝ (G m) z v)) atTop (𝓝 0) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simp only [sub_zero]
      exact squeeze_zero' (Eventually.of_forall fun m => norm_nonneg _)
        (Eventually.of_forall hbd)
        (by simpa using hasize_tend.const_mul (2 * ‖v‖))
    have h1 : Tendsto (fun m : ℕ => (Work.NN.Core.JstdCn n (G m z)) (fderiv ℝ (G m) z v)) atTop
        (𝓝 ((Work.NN.Core.JstdCn n (Glim z)) (Llim z v))) := by
      have hJm : (fun m : ℕ => (Work.NN.Core.JstdCn n (G m z)) (fderiv ℝ (G m) z v))
          = fun m : ℕ => Complex.I • (fderiv ℝ (G m) z v) := by
        funext m
        rw [Work.NN.Core.JstdCn_apply]
      have hJl : (Work.NN.Core.JstdCn n (Glim z)) (Llim z v) = Complex.I • (Llim z v) := by
        rw [Work.NN.Core.JstdCn_apply]
      rw [hJm, hJl]
      exact hLv.const_smul Complex.I
    have hev2 : Tendsto (fun m : ℕ => (Work.NN.Core.JstdCn n (G m z)) (fderiv ℝ (G m) z v)
        + (bld m).A (G m z) (fderiv ℝ (G m) z v)) atTop
        (𝓝 ((Work.NN.Core.JstdCn n (Glim z)) (Llim z v))) := by
      simpa using h1.add h2
    have heq : (fun m : ℕ => fderiv ℝ (G m) z ((Work.NN.Core.JstdCn n + A) z v))
        = fun m : ℕ => (Work.NN.Core.JstdCn n (G m z)) (fderiv ℝ (G m) z v)
            + (bld m).A (G m z) (fderiv ℝ (G m) z v) := by
      funext m
      have h := congrArg (fun T : Cn n →L[ℝ] Cn n => T v) ((hmain m).2.2.2.2 z hz)
      simpa only [ContinuousLinearMap.comp_apply, Pi.add_apply, ContinuousLinearMap.add_apply]
        using h
    have hlim := tendsto_nhds_unique hev1 (heq ▸ hev2)
    rw [hfderivG z hz]
    simpa only [ContinuousLinearMap.comp_apply] using hlim

  --------------------------------------------------------------------------------
  -- ## smoothness of the composites; continuity of the limit derivative
  --------------------------------------------------------------------------------
  have hGsm : ∀ m (k : ℕ), ContDiffOn ℝ k (G m) (P n 1) := by
    intro m
    induction m with
    | zero =>
        intro k
        rw [hG0]
        exact contDiffOn_id
    | succ m ih =>
        intro k
        have hmap : MapsTo (G m) (P n 1) (P n (rad m * (1 - delta m))) :=
          fun z hz => P_mono (hrad_32' m) ((hmain m).2.1 z hz)
        have h1 := (bld m).hStep.1 k
        have h := h1.comp (ih k) hmap
        rw [hGsucc]
        exact h
  have hG1 : ∀ m, ContinuousOn (fderiv ℝ (G m)) (P n 1) := by
    intro m
    have h1 : ContinuousOn (fderivWithin ℝ (G m) (P n 1)) (P n 1) :=
      (hGsm m 2).continuousOn_fderivWithin (isOpen_P n 1).uniqueDiffOn (by norm_num)
    refine h1.congr fun x hx => ?_
    rw [fderivWithin_of_isOpen (isOpen_P n 1) hx]
  have hLlim_cont : ContinuousOn Llim (P n 1) :=
    hLunif.continuousOn (Eventually.of_forall hG1).frequently
  have hproj : ∀ (l : Fin n) (z : Cn n), z ∈ P n 1 →
      fderiv ℝ (fun w => Glim w l) z
        = (ContinuousLinearMap.proj (R := ℝ) l).comp (fderiv ℝ Glim z) := by
    intro l z hz
    have h1 : (fun w : Cn n => Glim w l) = (ContinuousLinearMap.proj (R := ℝ) l) ∘ Glim := by
      funext w; rfl
    rw [h1, fderiv_comp z (ContinuousLinearMap.proj (R := ℝ) l).differentiableAt
      (hfd z hz).differentiableAt, ContinuousLinearMap.fderiv]
  have hprojcont : ∀ l : Fin n,
      ContinuousOn (fun w => (ContinuousLinearMap.proj (R := ℝ) l).comp (Llim w)) (P n 1) := by
    intro l
    have hc := hLlim_cont
    rw [continuousOn_iff_continuous_restrict] at hc
    rw [continuousOn_iff_continuous_restrict]
    exact hc.const_clm_comp (ContinuousLinearMap.proj (R := ℝ) l)
  have hcomp_fd : ∀ (l : Fin n) (x : Cn n), x ∈ P n 1 →
      HasFDerivAt (fun w => Glim w l)
        ((ContinuousLinearMap.proj (R := ℝ) l).comp (Llim x)) x := by
    intro l x hx
    have h1 : (fun w : Cn n => Glim w l) = (ContinuousLinearMap.proj (R := ℝ) l) ∘ Glim := by
      funext w; rfl
    rw [h1]
    exact (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.proj (R := ℝ) l)).comp x
      (hfd x hx)
  have hC1 : ∀ (l : Fin n),
      ContDiffOn ℝ 1 (fun w => Glim w l) (Work.CR.Flat.polydisc 0 (fun _ => (1 : ℝ))) := by
    intro l x hx
    rw [contDiffWithinAt_iff_contDiffAt
        ((Work.CR.Flat.isOpen_polydisc 0 (fun _ => (1 : ℝ))).mem_nhds hx),
      contDiffAt_one_iff]
    exact ⟨fun w => (ContinuousLinearMap.proj (R := ℝ) l).comp (Llim w),
      ⟨P n 1, (isOpen_P n 1).mem_nhds hx, hprojcont l, fun y hy => hcomp_fd l y hy⟩⟩
  --------------------------------------------------------------------------------
  -- ## the limit is `J`-holomorphic
  --------------------------------------------------------------------------------
  have hunit2 : ∀ k : Fin n, ‖(Pi.single k (1 : ℂ) : Cn n)‖ ≤ 1 := by
    intro k
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
    by_cases h : j = k
    · subst h; simp
    · rw [Pi.single_eq_of_ne h]; simp
  have hol : ∀ (l : Fin n) (z : Cn n), z ∈ P n 1 →
      Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) (fun w => Glim w l) z = 0 := by
    intro l z hz
    ext v
    rw [Work.NN.Core.dbarCn_apply, ContinuousLinearMap.zero_apply]
    have h1 : fderiv ℝ (fun w => Glim w l) z v = (fderiv ℝ Glim z v) l := by
      rw [hproj l z hz]
      rfl
    have h2 : fderiv ℝ (fun w => Glim w l) z ((Work.NN.Core.JstdCn n + A) z v)
        = Complex.I * (fderiv ℝ Glim z v) l := by
      rw [hproj l z hz]
      have hh := congrArg (fun T : Cn n →L[ℝ] Cn n => T v) (hGlimInter z hz)
      simp only [ContinuousLinearMap.comp_apply] at hh
      rw [ContinuousLinearMap.comp_apply, hh, Work.NN.Core.JstdCn_apply,
        ContinuousLinearMap.proj_apply, Pi.smul_apply, smul_eq_mul]
    rw [h1, h2]
    have h3 : Complex.I * (Complex.I * (fderiv ℝ Glim z v) l) = -((fderiv ℝ Glim z v) l) := by
      rw [← mul_assoc, Complex.I_mul_I]; ring
    rw [h3]; ring
  have hPsub : ∀ {r : ℝ}, r ≤ 4 → P n r ⊆ Work.NN.Final.pd n (fun _ => 1) 4 := by
    intro r hr z hz
    rw [Work.NN.Final.mem_pd]
    intro j
    have h := (mem_P.mp hz) j
    linarith
  --------------------------------------------------------------------------------
  -- ## smoothness of the frame
  --------------------------------------------------------------------------------
  have hsmall0 : ∀ i j : Fin n, Work.CR.Flat.holderNorm 0 α
      (fun z => A z (Pi.single i 1) j) (Work.CR.Flat.polydisc 0 (fun _ => (1 : ℝ)))
      ≤ ENNReal.ofReal ε := by
    intro i j
    have h1 : Work.CR.Flat.holderNorm 0 α (fun z => A z (Pi.single i 1) j) (P n 1)
        ≤ Work.CR.Flat.holderNorm 1 α (fun z => A z (Pi.single i 1) j) (P n 1) :=
      Work.CR.Flat.holderNorm_mono_k (by norm_num) α _ _
    have h2 : Work.CR.Flat.holderNorm 1 α (fun z => A z (Pi.single i 1) j) (P n 1)
        ≤ Work.CR.Flat.holderNorm 1 α (fun z => A z (Pi.single i 1) j) (P n 4) :=
      Work.CR.Flat.holderNorm_mono_set (isOpen_P n 4) (isOpen_P n 1) (P_mono (by norm_num)) 1 α _
    have h3 : Work.CR.Flat.holderNorm 1 α (fun z => A z (Pi.single i 1) j) (P n 4)
        ≤ ENNReal.ofReal ε := by
      rw [P_eq_pd]
      exact hsmall (Pi.single i 1) (hunit2 i) j
    exact h1.trans (h2.trans h3)
  have hsmoothk : ∀ (l : Fin n) (k : ℕ),
      ContDiffOn ℝ k (fun w => Glim w l) (Work.CR.Flat.polydisc 0 (fun _ => (1 / 2 : ℝ))) := by
    intro l k
    refine hsmooth (A := A) ?_ (ε := ε) hεε₁ ?_ ?_ (fun _ => (0 : Cn n →L[ℝ] ℂ)) ?_
      (fun w => Glim w l) (hC1 l) ?_ k
    · intro m
      exact (hAsm m).mono (hPsub (by norm_num))
    · exact hsmall0
    · intro z hz v
      refine hJac z ?_ v
      rw [← P_eq_pd]
      exact P_mono (by norm_num) hz
    · intro m
      exact contDiffOn_const
    · intro z hz V
      have hz' : z ∈ P n 1 := P_mono (by norm_num) hz
      rw [hol l z hz']
  --------------------------------------------------------------------------------
  -- ## the differential of the limit is invertible
  --------------------------------------------------------------------------------
  have hderiv1 : ∀ z ∈ P n 1, ‖fderiv ℝ Glim z - 1‖ < 1 := by
    intro z hz
    have h0 : fderiv ℝ (G 0) z = 1 := by
      rw [hG0]; exact fderiv_id
    have h1 : ∀ m, ‖fderiv ℝ (G m) z - 1‖ ≤ (32 / 31) * (1 / 32) := by
      intro m
      have h2 : ‖fderiv ℝ (G m) z - fderiv ℝ (G 0) z‖
          ≤ (32 / 31) * ∑ i ∈ Finset.Ico 0 m, bsize C₀ N ε i :=
        hdtel 0 m (Nat.zero_le m) z hz
      have h3 : ∑ i ∈ Finset.Ico 0 m, bsize C₀ N ε i ≤ 1 / 32 := by
        rw [← Finset.range_eq_Ico]
        exact hsumle m
      rw [h0] at h2
      calc ‖fderiv ℝ (G m) z - 1‖ ≤ (32 / 31) * ∑ i ∈ Finset.Ico 0 m, bsize C₀ N ε i := h2
        _ ≤ (32 / 31) * (1 / 32) := mul_le_mul_of_nonneg_left h3 (by norm_num)
    have htend : Tendsto (fun m => ‖fderiv ℝ (G m) z - 1‖) atTop (𝓝 (‖Llim z - 1‖)) :=
      ((hLlim_tend z hz).sub_const (1 : Cn n →L[ℝ] Cn n)).norm
    have h4 : ‖Llim z - 1‖ ≤ (32 / 31) * (1 / 32) := le_of_tendsto' htend h1
    rw [hfderivG z hz]
    have : (32 / 31 : ℝ) * (1 / 32) < 1 := by norm_num
    linarith
  --------------------------------------------------------------------------------
  -- ## conclusion
  --------------------------------------------------------------------------------
  refine ⟨P n (1 / 2), isOpen_P n (1 / 2), ?_, ?_, ?_⟩
  · rw [mem_P]
    intro j
    norm_num
  · exact hPsub (by norm_num)
  · refine ⟨fun l z => Glim z l, ?_, ?_, ?_⟩
    · intro l
      exact contDiffOn_infty.mpr fun k => hsmoothk l k
    · intro l y hy
      exact hol l y (P_mono (by norm_num) hy)
    · intro y hy
      have hy' : y ∈ P n 1 := P_mono (by norm_num) hy
      have hbij : Function.Bijective (fderiv ℝ Glim y) := by
        have h1 : ‖(ContinuousLinearMap.id ℝ (Cn n)).comp (fderiv ℝ Glim y - 1)‖ < 1 := by
          rw [ContinuousLinearMap.id_comp]
          exact hderiv1 y hy'
        have h2 := Work.NN.Core.bijective_add_of_norm_comp_lt_one
          (T₀ := ContinuousLinearMap.id ℝ (Cn n)) (T₀inv := ContinuousLinearMap.id ℝ (Cn n))
          (by ext v; simp) (by ext v; simp)
          (S := fderiv ℝ Glim y - 1) h1
        have h3 : (ContinuousLinearMap.id ℝ (Cn n)) + (fderiv ℝ Glim y - 1)
            = fderiv ℝ Glim y := by ext v; simp
        rwa [h3] at h2
      simpa using hbij

end

end Work.NN.Newton

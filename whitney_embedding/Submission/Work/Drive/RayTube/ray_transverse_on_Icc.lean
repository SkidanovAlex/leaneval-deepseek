import Mathlib
import Submission.Work.Drive.RayTube.RaySetup

/-!
# A transverse coordinate on a compact interval of a properly embedded ray

This file ports the compact-interval part of `Submission/Work/Noncompact/CompressionTube/ctc/`
from a properly embedded *line* to the *ray* `Work.Drive.RayTube.RayData`:

* `ray_extension_step`   (port of `Work.Noncompact.CompressionTube.extension_step`),
* `ray_piece_on_chain`   (port of `Work.Noncompact.CompressionTube.exists_piece_on_chain`),
* `ray_finite_piece_cover` (port of `Work.Noncompact.CompressionTube.exists_finite_piece_cover`),
* `ray_transverse_on_Icc` (port of `Work.Noncompact.CompressionTube.exists_transverse_on_Icc`).

The greedy-chain lemmas (`rightEnds`, `chainIdx`, `rightEnds_card_eq_b`, ...) of
`ctc/exists_transverse_on_Icc.lean` are statements about real numbers only and are reused verbatim;
the ray versions of the local piece, of the openness of transversality, of the linear gauge and of
the blend live in `RaySetup.lean`.
-/

namespace Work.Drive.RayTube

open scoped Manifold ContDiff
open Topology Set Function
open Work.Noncompact.CompressionTube

noncomputable section

/-! ## The extension step -/

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- **The extension step (ray version).**  If `Ψ` is transverse on `[a,c]` (with `c ∈ [a,b]`) and
`ψ` is a fresh piece transverse on the interval `|t - s| < ρ` with `|c - s| < ρ/2`, then there is a
piece `Ψ'`, vanishing on the ray, which is transverse on `[a, min (s + ρ/2) b]`. -/
theorem ray_extension_step {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M] (D : RayData n M)
    {a b c : ℝ} (ha : 0 ≤ a) (hc : c ∈ Set.Icc a b)
    {Ψ : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hΨsm : ContMDiff (MC n) (MC (n - 1)) smoothOrder Ψ)
    (hΨ0 : ∀ t : ℝ, 0 ≤ t → Ψ (D.ρ t) = 0)
    (hΨT : ∀ t : ℝ, 0 ≤ t → t ∈ Set.Icc a c → Transverse D.ρ D.g Ψ t)
    {ψ : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hψsm : ContMDiff (MC n) (MC (n - 1)) smoothOrder ψ)
    (hψ0 : ∀ t : ℝ, 0 ≤ t → ψ (D.ρ t) = 0)
    {s ρ : ℝ} (hρ : 0 < ρ) (hψT : ∀ t : ℝ, 0 ≤ t → |t - s| < ρ → Transverse D.ρ D.g ψ t)
    (hcU : |c - s| < ρ / 2) :
    ∃ Ψ' : M → EuclideanSpace ℝ (Fin (n - 1)),
      ContMDiff (MC n) (MC (n - 1)) smoothOrder Ψ' ∧
        (∀ t : ℝ, 0 ≤ t → Ψ' (D.ρ t) = 0) ∧
        ∀ t : ℝ, 0 ≤ t → t ∈ Set.Icc a (min (s + ρ / 2) b) → Transverse D.ρ D.g Ψ' t := by
  classical
  have hc0 : (0:ℝ) ≤ c := le_trans ha hc.1
  have hcT : Transverse D.ρ D.g Ψ c := hΨT c hc0 ⟨hc.1, le_refl c⟩
  have hcψ : Transverse D.ρ D.g ψ c :=
    hψT c hc0 (by rw [abs_lt] at hcU ⊢; constructor <;> linarith)
  -- the gauge aligning the fresh piece to the current one
  obtain ⟨A, hAinj, hAeq⟩ := ray_gauge hn D hΨsm hψsm hΨ0 hψ0 hc0 hcT hcψ
  have hGsm : ContMDiff (MC n) (MC (n - 1)) smoothOrder (fun x : M => A (ψ x)) :=
    A.contMDiff.comp hψsm
  have hG0 : ∀ t : ℝ, 0 ≤ t → (fun x : M => A (ψ x)) (D.ρ t) = 0 := by
    intro t ht
    simp [hψ0 t ht]
  have hGder : mfderiv (MC n) (MC (n - 1)) (fun x : M => A (ψ x)) (D.ρ c) =
      mfderiv (MC n) (MC (n - 1)) Ψ (D.ρ c) := by
    ext v : 1
    rw [mfderiv_clm_comp_apply hψsm A (D.ρ c) v]
    exact hAeq v
  -- the blend window
  obtain ⟨ρb, hρb, hblend⟩ := ray_blend hn D hΨsm hGsm hΨ0 hG0 hc0 hGder.symm hcT
  -- the step function
  obtain ⟨χ, hχsm, hχ01, hχ1, hχ0⟩ := exists_smoothStep c (ρb / 4) (by linarith)
  -- the fresh piece is transverse wherever `ψ` is
  have hGtrans' : ∀ t : ℝ, Transverse D.ρ D.g ψ t → Transverse D.ρ D.g (fun x : M => A (ψ x)) t := by
    intro t ht v hv1 hv2
    rw [mfderiv_clm_comp_apply hψsm A (D.ρ t) v] at hv1
    exact ht v (hAinj (by simpa using hv1)) hv2
  refine ⟨fun x : M => χ (D.g x) • Ψ x + (1 - χ (D.g x)) • A (ψ x), ?_, ?_, ?_⟩
  · -- smoothness
    have h1 : ContMDiff (MC n) MCreal smoothOrder (fun x : M => χ (D.g x)) :=
      (contMDiff_iff_contDiff.mpr hχsm).comp D.hg
    have h2 : ContMDiff (MC n) MCreal smoothOrder (fun x : M => 1 - χ (D.g x)) :=
      contMDiff_const.sub h1
    exact (h1.smul hΨsm).add (h2.smul hGsm)
  · -- vanishing on the ray
    intro t ht
    simp [D.hgc t ht, hΨ0 t ht, hψ0 t ht]
  · -- transversality
    intro t ht0 ht
    have hts : t ≤ s + ρ / 2 := le_trans ht.2 (min_le_left _ _)
    by_cases h1 : t < c - ρb / 4
    · -- to the left of the window: `Ψ' = Ψ`
      have htc : t ∈ Set.Icc a c := ⟨ht.1, by linarith⟩
      have heq : (fun x : M => χ (D.g x) • Ψ x + (1 - χ (D.g x)) • A (ψ x))
          =ᶠ[𝓝 (D.ρ t)] Ψ := by
        have hop : {x : M | D.g x < c - ρb / 4} ∈ 𝓝 (D.ρ t) :=
          D.hg.continuous.continuousAt.preimage_mem_nhds
            (by rw [D.hgc t ht0]; exact isOpen_Iio.mem_nhds h1)
        filter_upwards [hop] with x hx
        rw [hχ1 (D.g x) (le_of_lt hx)]
        simp
      exact (transverse_congr heq).mpr (hΨT t ht0 htc)
    · by_cases h2 : c + ρb / 4 < t
      · -- to the right of the window: `Ψ' = A ∘ ψ`
        have heq : (fun x : M => χ (D.g x) • Ψ x + (1 - χ (D.g x)) • A (ψ x))
            =ᶠ[𝓝 (D.ρ t)] (fun x : M => A (ψ x)) := by
          have hop : {x : M | c + ρb / 4 < D.g x} ∈ 𝓝 (D.ρ t) :=
            D.hg.continuous.continuousAt.preimage_mem_nhds
              (by rw [D.hgc t ht0]; exact isOpen_Ioi.mem_nhds h2)
          filter_upwards [hop] with x hx
          rw [hχ0 (D.g x) (le_of_lt hx)]
          simp
        refine (transverse_congr heq).mpr (hGtrans' t (hψT t ht0 ?_))
        rw [abs_lt] at hcU ⊢
        constructor <;> linarith [hcU.1, hcU.2, hts, hρb, hρ, h2]
      · -- inside the window: the blend lemma
        have hmid : |t - c| < ρb := by
          rw [abs_lt]
          constructor <;> linarith
        exact hblend χ hχsm hχ01 t ht0 hmid

/-! ## The induction along the chain -/

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- **The induction along the chain (ray version).**  For every `k` there is a piece, vanishing on
the ray, transverse on `[a, c k]` where `c k` is the `k`-th right end of the greedy chain. -/
theorem ray_piece_on_chain {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M] (D : RayData n M)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {F : Finset ℝ} {rr : ℝ → ℝ}
    {psi : ℝ → M → EuclideanSpace ℝ (Fin (n - 1))}
    (hpieces : ∀ t ∈ F, 0 < rr t ∧
      ContMDiff (MC n) (MC (n - 1)) smoothOrder (psi t) ∧
      (∀ s : ℝ, 0 ≤ s → psi t (D.ρ s) = 0) ∧
      ∀ s : ℝ, 0 ≤ s → |s - t| < rr t → Transverse D.ρ D.g (psi t) s)
    (hcover : Set.Icc a b ⊆ ⋃ t ∈ F, Set.Ioo (t - rr t / 2) (t + rr t / 2)) (k : ℕ) :
    ∃ Ψ : M → EuclideanSpace ℝ (Fin (n - 1)),
      ContMDiff (MC n) (MC (n - 1)) smoothOrder Ψ ∧
      (∀ s : ℝ, 0 ≤ s → Ψ (D.ρ s) = 0) ∧
      ∀ s : ℝ, 0 ≤ s → s ∈ Set.Icc a (rightEnds hcover hab k).val → Transverse D.ρ D.g Ψ s := by
  classical
  induction k with
  | zero =>
      obtain ⟨hrr, hpsm, hp0, hpT⟩ := hpieces _ (chainIdx_mem hcover hab 0)
      refine ⟨psi (chainIdx hcover hab 0), hpsm, hp0, ?_⟩
      intro s hs0 hs
      have hsa : s = a := le_antisymm (by rw [rightEnds_zero] at hs; exact hs.2) hs.1
      rw [hsa]
      refine hpT a ha ?_
      have hspec : a ∈ Set.Ioo (chainIdx hcover hab 0 - rr (chainIdx hcover hab 0) / 2)
          (chainIdx hcover hab 0 + rr (chainIdx hcover hab 0) / 2) := by
        simpa [rightEnds_zero] using chainIdx_spec hcover hab 0
      rw [Set.mem_Ioo] at hspec
      rw [abs_lt]
      constructor <;> linarith
  | succ k ih =>
      obtain ⟨Ψ, hΨsm, hΨ0, hΨT⟩ := ih
      by_cases hkb : (rightEnds hcover hab k).val = b
      · refine ⟨Ψ, hΨsm, hΨ0, ?_⟩
        intro s hs0 hs
        rw [rightEnds_succ, if_pos hkb, ← hkb] at hs
        exact hΨT s hs0 hs
      · obtain ⟨hrr, hpsm, hp0, hpT⟩ := hpieces _ (chainIdx_mem hcover hab k)
        have hc : (rightEnds hcover hab k).val ∈ Set.Icc a b := (rightEnds hcover hab k).property
        have hmid : |(rightEnds hcover hab k).val - chainIdx hcover hab k| <
            rr (chainIdx hcover hab k) / 2 := by
          have hspec : (rightEnds hcover hab k).val ∈
              Set.Ioo (chainIdx hcover hab k - rr (chainIdx hcover hab k) / 2)
                (chainIdx hcover hab k + rr (chainIdx hcover hab k) / 2) :=
            chainIdx_spec hcover hab k
          rw [Set.mem_Ioo] at hspec
          rw [abs_lt]
          constructor <;> linarith
        obtain ⟨Ψ', hΨ'sm, hΨ'0, hΨ'T⟩ := ray_extension_step hn D ha hc hΨsm hΨ0 hΨT hpsm hp0
          hrr hpT hmid
        refine ⟨Ψ', hΨ'sm, hΨ'0, ?_⟩
        rw [rightEnds_succ, if_neg hkb]
        exact hΨ'T

/-! ## A finite cover of a compact parameter interval by transverse pieces -/

set_option backward.isDefEq.respectTransparency false in
/-- **A finite family of pieces covering a compact interval (ray version).** -/
theorem ray_finite_piece_cover {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M] (D : RayData n M)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∃ (F : Finset ℝ) (psi : ℝ → M → EuclideanSpace ℝ (Fin (n - 1))) (rr : ℝ → ℝ),
      (∀ t ∈ F, 0 < rr t ∧
        ContMDiff (MC n) (MC (n - 1)) smoothOrder (psi t) ∧
        (∀ s : ℝ, 0 ≤ s → psi t (D.ρ s) = 0) ∧
        ∀ s : ℝ, 0 ≤ s → |s - t| < rr t → Transverse D.ρ D.g (psi t) s) ∧
      Set.Icc a b ⊆ ⋃ t ∈ F, Set.Ioo (t - rr t / 2) (t + rr t / 2) := by
  classical
  -- Step 1: at every real parameter there is a piece together with a transversality radius,
  -- valid at all parameters `s ≥ 0`.
  have hkey : ∀ t : ℝ, ∃ (psi : M → EuclideanSpace ℝ (Fin (n - 1))) (rr : ℝ),
      0 < rr ∧ ContMDiff (MC n) (MC (n - 1)) smoothOrder psi ∧
        (∀ s : ℝ, 0 ≤ s → psi (D.ρ s) = 0) ∧
        ∀ s : ℝ, 0 ≤ s → |s - t| < rr → Transverse D.ρ D.g psi s := by
    intro t
    by_cases ht : 0 ≤ t
    · obtain ⟨psi, hpsm, hp0, htr⟩ := ray_local_transverse_piece hn D ht
      obtain ⟨r, hrpos, hr⟩ := ray_transverse_open hn D hpsm hp0 ht htr
      exact ⟨psi, r, hrpos, hpsm, hp0, hr⟩
    · -- `t < 0`: use the piece centred at the parameter `0`
      obtain ⟨psi, hpsm, hp0, htr⟩ := ray_local_transverse_piece hn D (le_refl (0:ℝ))
      obtain ⟨r, hrpos, hr⟩ := ray_transverse_open hn D hpsm hp0 (le_refl (0:ℝ)) htr
      refine ⟨psi, r - t, by linarith, hpsm, hp0, ?_⟩
      intro s hs0 hs
      refine hr s hs0 ?_
      rw [sub_zero, abs_of_nonneg hs0]
      have h1 : |s - t| = s - t := abs_of_nonneg (by linarith)
      rw [h1] at hs
      linarith
  choose psi rr hspec using hkey
  -- Step 2: the half-radius intervals cover `[a,b]`
  have hcov : Set.Icc a b ⊆ ⋃ t : ℝ, Set.Ioo (t - rr t / 2) (t + rr t / 2) := by
    intro s _
    refine mem_iUnion.mpr ⟨s, ?_⟩
    have hpos : 0 < rr s := (hspec s).1
    rw [Set.mem_Ioo]
    constructor <;> linarith
  -- Step 3: compactness of `[a,b]` extracts a finite subcover
  obtain ⟨F, hF⟩ := IsCompact.elim_finite_subcover isCompact_Icc
    (fun t : ℝ => Set.Ioo (t - rr t / 2) (t + rr t / 2)) (fun _ => isOpen_Ioo) hcov
  exact ⟨F, psi, rr, fun t ht => hspec t, hF⟩

/-! ## The transverse coordinate on a compact interval -/

set_option backward.isDefEq.respectTransparency false in
/-- **A transverse coordinate on a compact interval of the ray.** -/
theorem ray_transverse_on_Icc {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M] (D : RayData n M)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∃ Ψ : M → EuclideanSpace ℝ (Fin (n - 1)),
      ContMDiff (MC n) (MC (n - 1)) smoothOrder Ψ ∧
      (∀ t : ℝ, 0 ≤ t → Ψ (D.ρ t) = 0) ∧
      ∀ s : ℝ, 0 ≤ s → s ∈ Set.Icc a b → Transverse D.ρ D.g Ψ s := by
  obtain ⟨F, psi, rr, hpieces, hcover⟩ := ray_finite_piece_cover hn D ha hab
  obtain ⟨Ψ, hΨsm, hΨ0, hΨT⟩ := ray_piece_on_chain hn D ha hab hpieces hcover F.card
  refine ⟨Ψ, hΨsm, hΨ0, ?_⟩
  intro s hs0 hs
  refine hΨT s hs0 ?_
  rw [rightEnds_card_eq_b hcover hab]
  exact hs

end

end Work.Drive.RayTube

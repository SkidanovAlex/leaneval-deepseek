import Mathlib
import Submission.Work.Drive.transverse_inter_boundary_parity
import Submission.Work.Drive.loopFamMeet_boxHavoid
import Submission.Work.Drive.t5FaceAvoid
import Submission.Work.Drive.diamCoreParity

/-!
# The T5 chain (and the `(2,3)` parity engine) with the transversality hypothesis **box-restricted**

The project lead's decision of 2026-09-26: `Work.Drive.DiamFamReg`'s two *transversality* clauses
quantify over the **unbounded** meet set `{(u,x) : diamFam Q θ u = clampedSweep c (1-·) P x}`, which is
neither open nor producible (`DIAMFAMREG_STATUS.md`, `NOTE_DiamFamReg_not_open.md`).  Every consumer
(`odd_ncard_diamMeet_iff_coreSideCount`, the T5 engines, `loopTransHyp_of_on_box`) uses them only at
**box** meets (`u ∈ unitBox 1`, `x ∈ unitBox 2`).  The box-restricted pair is open in the design
parameter and is what the producer `exists_diamFamRegBox_of_small_shift` supplies.

This file carries the whole chain with `htrans` box-restricted:

* `transverse_inter_boundary_parity_box` — the mod-2 boundary parity of two transverse chains, with the
  transversality required only at box pairs (the `ManifoldParity` chapter below it is *already* stated
  with box-restricted `htrans`, so the only change is at its top wrapper);
* `odd_ncard_loopFamMeet_iff_boxH` — the loop-deformation engine with box-restricted `htrans`;
* `odd_ncard_diamMeet_iff_arcMeet_boxH`, `odd_ncard_arcMeet_iff_core_boxH` — the two halves of T5;
* `odd_ncard_diamMeet_iff_arcMeet_clampedSweepBox`, `odd_ncard_arcMeet_iff_core_clampedSweepBox` — the
  same with the analytic hypotheses discharged for a clamped sweep.

The proofs are transcriptions of the on-disk proofs with the weaker hypothesis (which is only ever
applied at box points).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

noncomputable section

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

private lemma loop_seamInv_seamInv (x : EuclideanSpace ℝ (Fin 3)) : seamInv (seamInv x) = x := by
  ext i
  fin_cases i <;> simp [seamInv_apply_zero, seamInv_apply_one, seamInv_apply_two]

private lemma loop_mk2_eta (u : EuclideanSpace ℝ (Fin 2)) : u = mk2 (u 0) (u 1) := by
  ext i
  fin_cases i <;> simp

private lemma loop_onSeam_seamInv (x : EuclideanSpace ℝ (Fin 3)) :
    onSeam (seamInv x) ↔ onSeam x := by
  have h0 : (1 - x 0 = 0) ↔ (x 0 = 1) := by constructor <;> intro h <;> linarith
  have h0' : (1 - x 0 = 1) ↔ (x 0 = 0) := by constructor <;> intro h <;> linarith
  have h1 : (1 - x 1 = 0) ↔ (x 1 = 1) := by constructor <;> intro h <;> linarith
  have h1' : (1 - x 1 = 1) ↔ (x 1 = 0) := by constructor <;> intro h <;> linarith
  simp only [onSeam, seamInv_apply_zero, seamInv_apply_one]
  rw [h0, h0', h1, h1']
  tauto

private lemma loop_seamInv_mem_unitBox_iff (y : EuclideanSpace ℝ (Fin 3)) :
    seamInv y ∈ Submission.Drive.unitBox 2 ↔ y ∈ Submission.Drive.unitBox 2 := by
  simp only [Submission.Drive.unitBox, Set.mem_ofPred_eq, Set.mem_Icc]
  constructor <;> intro h i <;> have hi := h i <;>
    fin_cases i <;> simp [seamInv_apply_zero, seamInv_apply_one, seamInv_apply_two] at hi ⊢ <;>
    constructor <;> linarith

private lemma loop_seamInv_mem_unitBoxBdry (y : EuclideanSpace ℝ (Fin 3))
    (hy : y ∈ Submission.Drive.unitBox 2) (h : onSeam y) :
    seamInv y ∈ Submission.Drive.unitBoxBdry 2 := by
  refine ⟨(loop_seamInv_mem_unitBox_iff y).mpr hy, ?_⟩
  rcases h with h | h | h | h
  · exact ⟨0, by simp [seamInv_apply_zero, h]⟩
  · exact ⟨0, by simp [seamInv_apply_zero, h]⟩
  · exact ⟨1, by simp [seamInv_apply_one, h]⟩
  · exact ⟨1, by simp [seamInv_apply_one, h]⟩

private lemma loop_seamInv_ne_self_of_onSeam (x : EuclideanSpace ℝ (Fin 3)) (h : onSeam x) :
    seamInv x ≠ x := by
  intro heq
  rcases h with h | h | h | h
  · have hc := congrArg (fun y : EuclideanSpace ℝ (Fin 3) => y 0) heq
    simp [seamInv_apply_zero] at hc; linarith
  · have hc := congrArg (fun y : EuclideanSpace ℝ (Fin 3) => y 0) heq
    simp [seamInv_apply_zero] at hc; linarith
  · have hc := congrArg (fun y : EuclideanSpace ℝ (Fin 3) => y 1) heq
    simp [seamInv_apply_one] at hc; linarith
  · have hc := congrArg (fun y : EuclideanSpace ℝ (Fin 3) => y 1) heq
    simp [seamInv_apply_one] at hc; linarith

private lemma loop_mk2_mem_unitBox {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) : mk2 a b ∈ Submission.Drive.unitBox 1 := by
  intro i
  fin_cases i
  · simpa using ha
  · simpa using hb

private lemma loop_zero_mem_Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num

private lemma loop_one_mem_Icc : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num


theorem transverse_inter_boundary_parity_box (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M)
    (hD : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) D)
    (hN : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) N)
    (htrans : ∀ (s : EuclideanSpace ℝ (Fin 2)) (t : EuclideanSpace ℝ (Fin 3)), D s = N t →
      s ∈ Submission.Drive.unitBox 1 → t ∈ Submission.Drive.unitBox 2 →
      LinearMap.range (mfderiv (𝓡 2) (𝓡 4) D s).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) N t).toLinearMap = ⊤)
    (hface : ∀ (s : EuclideanSpace ℝ (Fin 2)) (t : EuclideanSpace ℝ (Fin 3)), D s = N t →
      s ∈ Submission.Drive.unitBox 1 → t ∈ Submission.Drive.unitBox 2 →
      (s ∈ Submission.Drive.unitBoxBdry 1 ∨ t ∈ Submission.Drive.unitBoxBdry 2) →
      (∃ i : Fin 2, (s i = 0 ∨ s i = 1) ∧ (∀ j : Fin 2, j ≠ i → s j ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ j : Fin 3, t j ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) D s σ = mfderiv (𝓡 3) (𝓡 4) N t τ ∧ σ i ≠ 0)
      ∨ (∃ j : Fin 3, (t j = 0 ∨ t j = 1) ∧ (∀ k : Fin 3, k ≠ j → t k ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ i : Fin 2, s i ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) D s σ = mfderiv (𝓡 3) (𝓡 4) N t τ ∧ τ j ≠ 0)) :
    ({p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3) |
        D p.1 = N p.2 ∧ p.1 ∈ Submission.Drive.unitBox 1 ∧ p.2 ∈ Submission.Drive.unitBox 2 ∧
        (p.1 ∈ Submission.Drive.unitBoxBdry 1 ∨ p.2 ∈ Submission.Drive.unitBoxBdry 2)}).Finite ∧
      Even ({p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3) |
        D p.1 = N p.2 ∧ p.1 ∈ Submission.Drive.unitBox 1 ∧ p.2 ∈ Submission.Drive.unitBox 2 ∧
        (p.1 ∈ Submission.Drive.unitBoxBdry 1 ∨
          p.2 ∈ Submission.Drive.unitBoxBdry 2)}).ncard := by
  -- the two hypotheses of the target theorem, in the `ℝ⁵` coordinates of the mod-2 chapter
  have htrans' : ∀ x : Work.Drive.Amb 4, x ∈ Submission.Drive.unitBox 4 →
      D (Work.Drive.sqPart x) = N (Work.Drive.cbPart x) →
      LinearMap.range (mfderiv (𝓡 2) (𝓡 4) D (Work.Drive.sqPart x)).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) N (Work.Drive.cbPart x)).toLinearMap = ⊤ :=
    fun x hxbox hx =>
      htrans (Work.Drive.sqPart x) (Work.Drive.cbPart x) hx
        ((Work.Drive.mem_unitBox_iff_prod x).mp hxbox).1
        ((Work.Drive.mem_unitBox_iff_prod x).mp hxbox).2
  have hface' : ∀ x : Work.Drive.Amb 4, x ∈ Submission.Drive.unitBox 4 →
      D (Work.Drive.sqPart x) = N (Work.Drive.cbPart x) →
      x ∈ Submission.Drive.unitBoxBdry 4 →
      (∃ i : Fin 2, (Work.Drive.sqPart x i = 0 ∨ Work.Drive.sqPart x i = 1) ∧
          (∀ j : Fin 2, j ≠ i → Work.Drive.sqPart x j ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ j : Fin 3, Work.Drive.cbPart x j ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) D (Work.Drive.sqPart x) σ =
              mfderiv (𝓡 3) (𝓡 4) N (Work.Drive.cbPart x) τ ∧ σ i ≠ 0)
      ∨ (∃ j : Fin 3, (Work.Drive.cbPart x j = 0 ∨ Work.Drive.cbPart x j = 1) ∧
          (∀ k : Fin 3, k ≠ j → Work.Drive.cbPart x k ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ i : Fin 2, Work.Drive.sqPart x i ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) D (Work.Drive.sqPart x) σ =
              mfderiv (𝓡 3) (𝓡 4) N (Work.Drive.cbPart x) τ ∧ τ j ≠ 0) := by
    intro x hxbox hDx hxbdy
    have hb := (Work.Drive.mem_unitBox_iff_prod x).mp hxbox
    rcases (Work.Drive.mem_unitBoxBdry_iff_prod x hxbox).mp hxbdy with h | h
    · exact hface (Work.Drive.sqPart x) (Work.Drive.cbPart x) hDx hb.1 hb.2 (Or.inl h)
    · exact hface (Work.Drive.sqPart x) (Work.Drive.cbPart x) hDx hb.1 hb.2 (Or.inr h)
  -- a non-zero smooth compactly supported field tangent to the intersection set
  obtain ⟨V, hV, hVsupp, hVne, hVtan⟩ :=
    Work.Drive.ManifoldParity.exists_tangential_field D N hD hN htrans'
  -- the flow of that field pairs the boundary intersections up
  have hmain := Work.Drive.ManifoldParity.even_ncard_bInterSet_of_tangential_field
    D N hD hN htrans' hface' V hV hVsupp hVne hVtan
  refine ⟨?_, ?_⟩
  · exact (Work.Drive.prodBInterSet_finite_iff D N).mpr hmain.1
  · exact (Work.Drive.prodBInterSet_ncard D N).symm ▸ hmain.2

theorem odd_ncard_loopFamMeet_iff_boxH (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (L : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M)
    (hL : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) L)
    (hN : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) N)
    (hloop : ∀ t ∈ Set.Icc (0 : ℝ) 1, L (mk2 t 0) = L (mk2 t 1))
    (hseam : ∀ x : EuclideanSpace ℝ (Fin 3), onSeam x → N (seamInv x) = N x)
    (havoid : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      L u = N x → u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
        (x 2 = 0 ∨ x 2 = 1) → False)
    (htrans : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)), L u = N x →
      u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
      LinearMap.range (mfderiv (𝓡 2) (𝓡 4) L u).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) N x).toLinearMap = ⊤)
    (hface : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)), L u = N x →
      u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
      (u ∈ Submission.Drive.unitBoxBdry 1 ∨ x ∈ Submission.Drive.unitBoxBdry 2) →
      (∃ i : Fin 2, (u i = 0 ∨ u i = 1) ∧ (∀ j : Fin 2, j ≠ i → u j ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ j : Fin 3, x j ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) L u σ = mfderiv (𝓡 3) (𝓡 4) N x τ ∧ σ i ≠ 0)
        ∨ (∃ j : Fin 3, (x j = 0 ∨ x j = 1) ∧ (∀ k : Fin 3, k ≠ j → x k ∈ Set.Ioo (0 : ℝ) 1) ∧
            (∀ i : Fin 2, u i ∈ Set.Ioo (0 : ℝ) 1) ∧
            ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
              mfderiv (𝓡 2) (𝓡 4) L u σ = mfderiv (𝓡 3) (𝓡 4) N x τ ∧ τ j ≠ 0)) :
    Odd ((loopFamMeet L N 0).ncard) ↔ Odd ((loopFamMeet L N 1).ncard) := by
  classical
  -- the boundary intersection set of the engine
  set B : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3)) :=
    {p | L p.1 = N p.2 ∧ p.1 ∈ Submission.Drive.unitBox 1 ∧ p.2 ∈ Submission.Drive.unitBox 2 ∧
      (p.1 ∈ Submission.Drive.unitBoxBdry 1 ∨ p.2 ∈ Submission.Drive.unitBoxBdry 2)} with hB
  have hBpar := transverse_inter_boundary_parity_box M L N hL hN htrans hface
  have hBfin : B.Finite := by rw [hB]; exact hBpar.1
  have hBeven : Even B.ncard := by rw [hB]; exact hBpar.2
  -- the five pieces of `B`: the `p.1 0`-face, the `p.1 1`-face, and the seam part of `p.2`
  let A : ℝ → Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3)) :=
    fun t => {p | p ∈ B ∧ p.1 0 = t}
  let Q : ℝ → Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3)) :=
    fun c => {p | p ∈ B ∧ p.1 1 = c}
  let E : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3)) :=
    {p | p ∈ B ∧ onSeam p.2}
  have hAfin : ∀ t : ℝ, (A t).Finite := fun t => hBfin.subset (fun p hp => hp.1)
  have hQfin : ∀ c : ℝ, (Q c).Finite := fun c => hBfin.subset (fun p hp => hp.1)
  have hEfin : E.Finite := hBfin.subset (fun p hp => hp.1)
  -- ## the face normal form of a boundary meet
  have hnf : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      L u = N x → u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
      (u ∈ Submission.Drive.unitBoxBdry 1 ∨ x ∈ Submission.Drive.unitBoxBdry 2) →
      ((u 0 = 0 ∨ u 0 = 1) ∧ u 1 ∈ Set.Ioo (0 : ℝ) 1 ∧ (∀ j : Fin 3, x j ∈ Set.Ioo (0 : ℝ) 1)) ∨
      ((u 1 = 0 ∨ u 1 = 1) ∧ u 0 ∈ Set.Ioo (0 : ℝ) 1 ∧ (∀ j : Fin 3, x j ∈ Set.Ioo (0 : ℝ) 1)) ∨
      (onSeam x ∧ u 0 ∈ Set.Ioo (0 : ℝ) 1 ∧ u 1 ∈ Set.Ioo (0 : ℝ) 1) := by
    intro u x hmeet hu hx hb
    rcases hface u x hmeet hu hx hb with ⟨i, hi, hio, hxi, -⟩ | ⟨j, hj, hjo, hui, -⟩
    · fin_cases i
      · exact Or.inl ⟨hi, hio 1 (by decide), hxi⟩
      · exact Or.inr (Or.inl ⟨hi, hio 0 (by decide), hxi⟩)
    · have hj2 : j ≠ 2 := by
        intro h
        exact havoid u x hmeet hu hx (by simpa [h] using hj)
      fin_cases j
      · rcases hj with h | h
        · exact Or.inr (Or.inr ⟨Or.inl h, hui 0, hui 1⟩)
        · exact Or.inr (Or.inr ⟨Or.inr (Or.inl h), hui 0, hui 1⟩)
      · rcases hj with h | h
        · exact Or.inr (Or.inr ⟨Or.inr (Or.inr (Or.inl h)), hui 0, hui 1⟩)
        · exact Or.inr (Or.inr ⟨Or.inr (Or.inr (Or.inr h)), hui 0, hui 1⟩)
      · exact absurd rfl hj2
  have hnfp : ∀ p ∈ B,
      ((p.1 0 = 0 ∨ p.1 0 = 1) ∧ p.1 1 ∈ Set.Ioo (0 : ℝ) 1 ∧
        (∀ j : Fin 3, p.2 j ∈ Set.Ioo (0 : ℝ) 1)) ∨
      ((p.1 1 = 0 ∨ p.1 1 = 1) ∧ p.1 0 ∈ Set.Ioo (0 : ℝ) 1 ∧
        (∀ j : Fin 3, p.2 j ∈ Set.Ioo (0 : ℝ) 1)) ∨
      (onSeam p.2 ∧ p.1 0 ∈ Set.Ioo (0 : ℝ) 1 ∧ p.1 1 ∈ Set.Ioo (0 : ℝ) 1) := by
    intro p hp
    exact hnf p.1 p.2 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
  have onSeam_not_allIoo : ∀ x : EuclideanSpace ℝ (Fin 3),
      (∀ j : Fin 3, x j ∈ Set.Ioo (0 : ℝ) 1) → ¬ onSeam x := by
    intro x hx hs
    rcases hs with h | h | h | h
    · have := (hx 0).1; linarith
    · have := (hx 0).2; linarith
    · have := (hx 1).1; linarith
    · have := (hx 1).2; linarith
  -- ## pairwise disjointness of the five pieces
  have hdisj_A01 : Disjoint (A 0) (A 1) := by
    rw [Set.disjoint_left]
    rintro p ⟨-, h0⟩ ⟨-, h1⟩
    linarith
  have hdisj_Q01 : Disjoint (Q 0) (Q 1) := by
    rw [Set.disjoint_left]
    rintro p ⟨-, h0⟩ ⟨-, h1⟩
    linarith
  have hdisj_AQ : ∀ {t c : ℝ}, (t = 0 ∨ t = 1) → (c = 0 ∨ c = 1) →
      Disjoint (A t) (Q c) := by
    intro t c ht hc
    rw [Set.disjoint_left]
    rintro p ⟨hpb, hpt⟩ ⟨-, hpc⟩
    rcases hnfp p hpb with ⟨-, hl1, -⟩ | ⟨-, hl0, -⟩ | ⟨-, hl0', -⟩
    · rcases hc with hc | hc <;> linarith [hl1.1, hl1.2, hpc, hc]
    · rcases ht with ht | ht <;> linarith [hl0.1, hl0.2, hpt, ht]
    · rcases ht with ht | ht <;> linarith [hl0'.1, hl0'.2, hpt, ht]
  have hdisj_AE : ∀ {t : ℝ}, (t = 0 ∨ t = 1) → Disjoint (A t) E := by
    intro t ht
    rw [Set.disjoint_left]
    rintro p ⟨hpb, hpt⟩ ⟨-, hs⟩
    rcases hnfp p hpb with ⟨-, -, hx⟩ | ⟨-, -, hx⟩ | ⟨-, h0, -⟩
    · exact onSeam_not_allIoo p.2 hx hs
    · exact onSeam_not_allIoo p.2 hx hs
    · rcases ht with ht | ht <;> linarith [h0.1, h0.2, hpt, ht]
  have hdisj_QE : ∀ {c : ℝ}, (c = 0 ∨ c = 1) → Disjoint (Q c) E := by
    intro c hc
    rw [Set.disjoint_left]
    rintro p ⟨hpb, hpc⟩ ⟨-, hs⟩
    rcases hnfp p hpb with ⟨-, -, hx⟩ | ⟨-, -, hx⟩ | ⟨-, -, h1⟩
    · exact onSeam_not_allIoo p.2 hx hs
    · exact onSeam_not_allIoo p.2 hx hs
    · rcases hc with hc | hc <;> linarith [h1.1, h1.2, hpc, hc]
  -- ## the five pieces cover `B`
  have hcoverOr : ∀ p, p ∈ B ↔ p ∈ A 0 ∨ p ∈ A 1 ∨ p ∈ Q 0 ∨ p ∈ Q 1 ∨ p ∈ E := by
    intro p
    constructor
    · intro hp
      rcases hnfp p hp with ⟨h0, -, -⟩ | ⟨h1, -, -⟩ | ⟨hs, -, -⟩
      · rcases h0 with h0 | h0
        · exact Or.inl ⟨hp, h0⟩
        · exact Or.inr (Or.inl ⟨hp, h0⟩)
      · rcases h1 with h1 | h1
        · exact Or.inr (Or.inr (Or.inl ⟨hp, h1⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, h1⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hp, hs⟩)))
    · intro hp
      rcases hp with h | h | h | h | h
      · exact h.1
      · exact h.1
      · exact h.1
      · exact h.1
      · exact h.1
  have hcover : B = A 0 ∪ A 1 ∪ Q 0 ∪ Q 1 ∪ E := by
    ext p
    rw [hcoverOr p]
    simp only [Set.mem_union]
    tauto
  -- ## the seam part `E` is even: the seam involution of `p.2`
  have hEeven : Even E.ncard := by
    refine even_ncard_of_involution hEfin
      (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3) => (p.1, seamInv p.2)) ?_ ?_ ?_
    · intro p hp
      obtain ⟨u, x⟩ := p
      obtain ⟨hpb, hx⟩ := hp
      exact ⟨⟨hpb.1.trans (hseam x hx).symm, hpb.2.1,
              (loop_seamInv_mem_unitBox_iff x).mpr hpb.2.2.1,
              Or.inr (loop_seamInv_mem_unitBoxBdry x hpb.2.2.1 hx)⟩,
             (loop_onSeam_seamInv x).mpr hx⟩
    · intro p _
      obtain ⟨u, x⟩ := p
      exact Prod.ext rfl (loop_seamInv_seamInv x)
    · intro p hp
      obtain ⟨u, x⟩ := p
      obtain ⟨-, hx⟩ := hp
      intro h
      exact loop_seamInv_ne_self_of_onSeam x hx (congrArg Prod.snd h)
  -- ## the two `p.1 1`-faces are swapped by `hloop`
  have hQeq : (Q 0).ncard = (Q 1).ncard := by
    have hsQ1 : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
        (u, x) ∈ Q 0 → (mk2 (u 0) (1 - u 1), x) ∈ Q 1 := by
      rintro u x ⟨hpb, hu1⟩
      have hu : u = mk2 (u 0) 0 := by
        ext i
        fin_cases i
        · simp
        · simpa using hu1
      have h1 : (1 : ℝ) - u 1 = 1 := by rw [hu1]; norm_num
      have hmeet : L (mk2 (u 0) (1 - u 1)) = N x := by
        rw [h1]
        exact ((hloop (u 0) (hpb.2.1 0)).symm.trans (by rw [hu.symm])).trans hpb.1
      have hbox : mk2 (u 0) (1 - u 1) ∈ Submission.Drive.unitBox 1 := by
        rw [h1]
        exact loop_mk2_mem_unitBox (hpb.2.1 0) loop_one_mem_Icc
      have hsec : (mk2 (u 0) (1 - u 1)) 1 = 1 := by rw [h1]; simp
      exact ⟨⟨hmeet, hbox, hpb.2.2.1, Or.inl ⟨hbox, ⟨1, Or.inr hsec⟩⟩⟩, hsec⟩
    have hsQ0 : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
        (u, x) ∈ Q 1 → (mk2 (u 0) (1 - u 1), x) ∈ Q 0 := by
      rintro u x ⟨hpb, hu1⟩
      have hu : u = mk2 (u 0) 1 := by
        ext i
        fin_cases i
        · simp
        · simpa using hu1
      have h0 : (1 : ℝ) - u 1 = 0 := by rw [hu1]; norm_num
      have hmeet : L (mk2 (u 0) (1 - u 1)) = N x := by
        rw [h0]
        exact ((hloop (u 0) (hpb.2.1 0)).trans (by rw [hu.symm])).trans hpb.1
      have hbox : mk2 (u 0) (1 - u 1) ∈ Submission.Drive.unitBox 1 := by
        rw [h0]
        exact loop_mk2_mem_unitBox (hpb.2.1 0) loop_zero_mem_Icc
      have hsec : (mk2 (u 0) (1 - u 1)) 1 = 0 := by rw [h0]; simp
      exact ⟨⟨hmeet, hbox, hpb.2.2.1, Or.inl ⟨hbox, ⟨1, Or.inl hsec⟩⟩⟩, hsec⟩
    refine ncard_eq_of_involution_swap ((hQfin 0).union (hQfin 1))
      (fun p => (mk2 (p.1 0) (1 - p.1 1), p.2)) ?_ ?_ hdisj_Q01 rfl ?_ ?_
    · intro p hp
      obtain ⟨u, x⟩ := p
      simp only [Set.mem_union] at hp
      rcases hp with hp | hp
      · exact Or.inr (hsQ1 u x hp)
      · exact Or.inl (hsQ0 u x hp)
    · intro p _
      obtain ⟨u, x⟩ := p
      refine Prod.ext ?_ rfl
      ext i
      fin_cases i <;> simp
    · intro p hp
      obtain ⟨u, x⟩ := p
      exact hsQ1 u x hp
    · intro p hp
      obtain ⟨u, x⟩ := p
      exact hsQ0 u x hp
  have hQeven : Even ((Q 0).ncard + (Q 1).ncard) := by
    rw [hQeq]
    exact ⟨(Q 1).ncard, rfl⟩
  -- ## the cardinality bookkeeping
  have hd_A0E : Disjoint (A 0) E := hdisj_AE (Or.inl rfl)
  have hd_A1E : Disjoint (A 1) E := hdisj_AE (Or.inr rfl)
  have hd_Q0E : Disjoint (Q 0) E := hdisj_QE (Or.inl rfl)
  have hd_Q1E : Disjoint (Q 1) E := hdisj_QE (Or.inr rfl)
  have hd_A0Q0 : Disjoint (A 0) (Q 0) := hdisj_AQ (Or.inl rfl) (Or.inl rfl)
  have hd_A0Q1 : Disjoint (A 0) (Q 1) := hdisj_AQ (Or.inl rfl) (Or.inr rfl)
  have hd_A1Q0 : Disjoint (A 1) (Q 0) := hdisj_AQ (Or.inr rfl) (Or.inl rfl)
  have hd_A1Q1 : Disjoint (A 1) (Q 1) := hdisj_AQ (Or.inr rfl) (Or.inr rfl)
  have hd1 : Disjoint (A 0 ∪ A 1) (Q 0) := hd_A0Q0.union_left hd_A1Q0
  have hd2 : Disjoint (A 0 ∪ A 1) (Q 1) := hd_A0Q1.union_left hd_A1Q1
  have hd3 : Disjoint (A 0 ∪ A 1 ∪ Q 0) (Q 1) := hd2.union_left hdisj_Q01
  have hd4 : Disjoint (A 0 ∪ A 1) E := hd_A0E.union_left hd_A1E
  have hd5 : Disjoint (A 0 ∪ A 1 ∪ Q 0) E := hd4.union_left hd_Q0E
  have hd6 : Disjoint (A 0 ∪ A 1 ∪ Q 0 ∪ Q 1) E := hd5.union_left hd_Q1E
  have hsum1 : (A 0 ∪ A 1 ∪ Q 0 ∪ Q 1 ∪ E).ncard =
      (A 0 ∪ A 1 ∪ Q 0 ∪ Q 1).ncard + E.ncard :=
    Set.ncard_union_eq hd6 ((((hAfin 0).union (hAfin 1)).union (hQfin 0)).union (hQfin 1)) hEfin
  have hsum2 : (A 0 ∪ A 1 ∪ Q 0 ∪ Q 1).ncard = (A 0 ∪ A 1 ∪ Q 0).ncard + (Q 1).ncard :=
    Set.ncard_union_eq hd3 (((hAfin 0).union (hAfin 1)).union (hQfin 0)) (hQfin 1)
  have hsum3 : (A 0 ∪ A 1 ∪ Q 0).ncard = (A 0 ∪ A 1).ncard + (Q 0).ncard :=
    Set.ncard_union_eq hd1 ((hAfin 0).union (hAfin 1)) (hQfin 0)
  have hsum4 : (A 0 ∪ A 1).ncard = (A 0).ncard + (A 1).ncard :=
    Set.ncard_union_eq hdisj_A01 (hAfin 0) (hAfin 1)
  have hBsum : B.ncard = (A 0).ncard + (A 1).ncard + (Q 0).ncard + (Q 1).ncard + E.ncard := by
    rw [hcover, hsum1, hsum2, hsum3, hsum4]
  -- ## parity arithmetic
  have hsumEven : Even ((A 0).ncard + (A 1).ncard + (Q 0).ncard + (Q 1).ncard + E.ncard) := by
    rw [← hBsum]; exact hBeven
  have hmain : Even (((A 0).ncard + (A 1).ncard) + (((Q 0).ncard + (Q 1).ncard) + E.ncard)) := by
    rw [show ((A 0).ncard + (A 1).ncard) + (((Q 0).ncard + (Q 1).ncard) + E.ncard)
        = (A 0).ncard + (A 1).ncard + (Q 0).ncard + (Q 1).ncard + E.ncard from by ring]
    exact hsumEven
  have hAeven : Even ((A 0).ncard + (A 1).ncard) := by
    have hy : Even (((Q 0).ncard + (Q 1).ncard) + E.ncard) := hQeven.add hEeven
    rw [Nat.even_add] at hmain
    exact hmain.mpr hy
  have hgoal : Odd ((A 0).ncard) ↔ Odd ((A 1).ncard) := Nat.even_add'.mp hAeven
  -- ## the two `p.1 0`-faces are the two loop meets
  have hA0 : A 0 = loopFamMeet L N 0 := by
    ext p
    constructor
    · rintro ⟨hpb, h0⟩
      exact ⟨hpb.2.1, h0, hpb.2.2.1, hpb.1⟩
    · rintro ⟨h1, h0, h2, hmeet⟩
      exact ⟨⟨hmeet, h1, h2, Or.inl ⟨h1, ⟨0, Or.inl h0⟩⟩⟩, h0⟩
  have hA1 : A 1 = loopFamMeet L N 1 := by
    ext p
    constructor
    · rintro ⟨hpb, h0⟩
      exact ⟨hpb.2.1, h0, hpb.2.2.1, hpb.1⟩
    · rintro ⟨h1, h0, h2, hmeet⟩
      exact ⟨⟨hmeet, h1, h2, Or.inl ⟨h1, ⟨0, Or.inr h0⟩⟩⟩, h0⟩
  rw [← hA0, ← hA1]
  exact hgoal

theorem odd_ncard_diamMeet_iff_arcMeet_boxH (Q : ℂ → CappingSpace) (t : ℝ)
    (W : EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    (hL : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (diamFam Q t))
    (hN : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hseam : ∀ x : EuclideanSpace ℝ (Fin 3), onSeam x → W (seamInv x) = W x)
    (havoid : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      diamFam Q t u = W x → u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
        (x 2 = 0 ∨ x 2 = 1) → False)
    (htrans : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      diamFam Q t u = W x → u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
      LinearMap.range (mfderiv (𝓡 2) (𝓡 4) (diamFam Q t) u).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) W x).toLinearMap = ⊤)
    (hface : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      diamFam Q t u = W x →
      u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
      (u ∈ Submission.Drive.unitBoxBdry 1 ∨ x ∈ Submission.Drive.unitBoxBdry 2) →
      (∃ i : Fin 2, (u i = 0 ∨ u i = 1) ∧ (∀ j : Fin 2, j ≠ i → u j ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ j : Fin 3, x j ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) (diamFam Q t) u σ = mfderiv (𝓡 3) (𝓡 4) W x τ ∧ σ i ≠ 0)
        ∨ (∃ j : Fin 3, (x j = 0 ∨ x j = 1) ∧ (∀ k : Fin 3, k ≠ j → x k ∈ Set.Ioo (0 : ℝ) 1) ∧
            (∀ i : Fin 2, u i ∈ Set.Ioo (0 : ℝ) 1) ∧
            ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
              mfderiv (𝓡 2) (𝓡 4) (diamFam Q t) u σ = mfderiv (𝓡 3) (𝓡 4) W x τ ∧ τ j ≠ 0)) :
    Odd (diamMeet Q t W).ncard ↔ Odd (arcMeet Q t W).ncard := by
  have hloop : ∀ a ∈ Set.Icc (0 : ℝ) 1, diamFam Q t (mk2 a 0) = diamFam Q t (mk2 a 1) := by
    intro a _
    show diamInterp Q t a 0 = diamInterp Q t a 1
    exact (diamInterp_loop hQseam t a).symm
  have he := odd_ncard_loopFamMeet_iff_boxH CappingSpace (diamFam Q t) W hL hN hloop hseam
    havoid htrans hface
  rw [diamMeet_ncard_eq_loopFamMeet_zero Q t W, ← loopFamMeet_one_eq_arcMeet Q t W]
  exact he

theorem odd_ncard_arcMeet_iff_core_boxH (Q : ℂ → CappingSpace) (t c : ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    (hL : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (arcFam Q t))
    (hN : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (clampedSweep c (fun s => 1 - s) P))
    (hseam : ∀ x : EuclideanSpace ℝ (Fin 3), onSeam x →
      clampedSweep c (fun s => 1 - s) P (seamInv x) = clampedSweep c (fun s => 1 - s) P x)
    (havoid : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      arcFam Q t u = clampedSweep c (fun s => 1 - s) P x → u ∈ Submission.Drive.unitBox 1 →
        x ∈ Submission.Drive.unitBox 2 → (x 2 = 0 ∨ x 2 = 1) → False)
    (htrans : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      arcFam Q t u = clampedSweep c (fun s => 1 - s) P x →
      u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
      LinearMap.range (mfderiv (𝓡 2) (𝓡 4) (arcFam Q t) u).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) (clampedSweep c (fun s => 1 - s) P) x).toLinearMap = ⊤)
    (hface : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      arcFam Q t u = clampedSweep c (fun s => 1 - s) P x →
      u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
      (u ∈ Submission.Drive.unitBoxBdry 1 ∨ x ∈ Submission.Drive.unitBoxBdry 2) →
      (∃ i : Fin 2, (u i = 0 ∨ u i = 1) ∧ (∀ j : Fin 2, j ≠ i → u j ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ j : Fin 3, x j ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) (arcFam Q t) u σ
              = mfderiv (𝓡 3) (𝓡 4) (clampedSweep c (fun s => 1 - s) P) x τ ∧ σ i ≠ 0)
        ∨ (∃ j : Fin 3, (x j = 0 ∨ x j = 1) ∧ (∀ k : Fin 3, k ≠ j → x k ∈ Set.Ioo (0 : ℝ) 1) ∧
            (∀ i : Fin 2, u i ∈ Set.Ioo (0 : ℝ) 1) ∧
            ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
              mfderiv (𝓡 2) (𝓡 4) (arcFam Q t) u σ
                = mfderiv (𝓡 3) (𝓡 4) (clampedSweep c (fun s => 1 - s) P) x τ ∧ τ j ≠ 0)) :
    Odd (arcMeet Q t (clampedSweep c (fun s => 1 - s) P)).ncard
      ↔ Odd (coreSideCount Q c P) := by
  have hloop : ∀ a ∈ Set.Icc (0 : ℝ) 1, arcFam Q t (mk2 a 0) = arcFam Q t (mk2 a 1) := by
    intro a _
    show arcRot Q t a 0 = arcRot Q t a 1
    exact (arcRot_loop hQseam t a).symm
  have he := odd_ncard_loopFamMeet_iff_boxH CappingSpace (arcFam Q t)
    (clampedSweep c (fun s => 1 - s) P) hL hN hloop hseam havoid htrans hface
  change Odd (arcMeet Q t (clampedSweep c (fun s => 1 - s) P)).ncard
      ↔ Odd ((coreMeet Q c P).ncard)
  rw [arcMeet_ncard_eq_loopFamMeet_zero, ← arcMeet_zero_eq_coreMeet,
    ← loopFamMeet_one_eq_arcMeet_zero]
  exact he

theorem odd_ncard_diamMeet_iff_arcMeet_clampedSweepBox (Q : ℂ → CappingSpace) (t c : ℝ)
    (ψ : ℝ → ℝ) (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hQ : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) Q)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hP : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P)
    (hPseam : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → P y = P (seamInv2 y))
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0) (hc : 0 < c)
    (hdisj : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ ≤ 1 → Q z ≠ P y)
    (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≠ c)
    (htrans : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      diamFam Q t u = clampedSweep c ψ P x → u ∈ Submission.Drive.unitBox 1 →
      x ∈ Submission.Drive.unitBox 2 →
      LinearMap.range (mfderiv (𝓡 2) (𝓡 4) (diamFam Q t) u).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) (clampedSweep c ψ P) x).toLinearMap = ⊤)
    (hface : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      diamFam Q t u = clampedSweep c ψ P x →
      u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
      (u ∈ Submission.Drive.unitBoxBdry 1 ∨ x ∈ Submission.Drive.unitBoxBdry 2) →
      (∃ i : Fin 2, (u i = 0 ∨ u i = 1) ∧ (∀ j : Fin 2, j ≠ i → u j ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ j : Fin 3, x j ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) (diamFam Q t) u σ
              = mfderiv (𝓡 3) (𝓡 4) (clampedSweep c ψ P) x τ ∧ σ i ≠ 0)
        ∨ (∃ j : Fin 3, (x j = 0 ∨ x j = 1) ∧ (∀ k : Fin 3, k ≠ j → x k ∈ Set.Ioo (0 : ℝ) 1) ∧
            (∀ i : Fin 2, u i ∈ Set.Ioo (0 : ℝ) 1) ∧
            ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
              mfderiv (𝓡 2) (𝓡 4) (diamFam Q t) u σ
                = mfderiv (𝓡 3) (𝓡 4) (clampedSweep c ψ P) x τ ∧ τ j ≠ 0)) :
    Odd (diamMeet Q t (clampedSweep c ψ P)).ncard
      ↔ Odd (arcMeet Q t (clampedSweep c ψ P)).ncard :=
  odd_ncard_diamMeet_iff_arcMeet_boxH Q t (clampedSweep c ψ P) hQseam
    (contMDiff_diamFam hQ t) (contMDiff_clampedSweep c ψ P hψ hP)
    (fun x hx => (clampedSweep_seamInv c ψ P hPseam x hx).symm)
    (havoid_diamFam hc hψ0 hψ1 hdisj hlev t) htrans hface

theorem odd_ncard_arcMeet_iff_core_clampedSweepBox (Q : ℂ → CappingSpace) (t c : ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hQ : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) Q)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    (hP : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P)
    (hPseam : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → P y = P (seamInv2 y))
    (hc : 0 < c)
    (hdisj : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ = 1 → Q z ≠ P y)
    (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≠ c)
    (htrans : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      arcFam Q t u = clampedSweep c (fun s => 1 - s) P x →
      u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
      LinearMap.range (mfderiv (𝓡 2) (𝓡 4) (arcFam Q t) u).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) (clampedSweep c (fun s => 1 - s) P) x).toLinearMap = ⊤)
    (hface : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      arcFam Q t u = clampedSweep c (fun s => 1 - s) P x →
      u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
      (u ∈ Submission.Drive.unitBoxBdry 1 ∨ x ∈ Submission.Drive.unitBoxBdry 2) →
      (∃ i : Fin 2, (u i = 0 ∨ u i = 1) ∧ (∀ j : Fin 2, j ≠ i → u j ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ j : Fin 3, x j ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) (arcFam Q t) u σ
              = mfderiv (𝓡 3) (𝓡 4) (clampedSweep c (fun s => 1 - s) P) x τ ∧ σ i ≠ 0)
        ∨ (∃ j : Fin 3, (x j = 0 ∨ x j = 1) ∧ (∀ k : Fin 3, k ≠ j → x k ∈ Set.Ioo (0 : ℝ) 1) ∧
            (∀ i : Fin 2, u i ∈ Set.Ioo (0 : ℝ) 1) ∧
            ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
              mfderiv (𝓡 2) (𝓡 4) (arcFam Q t) u σ
                = mfderiv (𝓡 3) (𝓡 4) (clampedSweep c (fun s => 1 - s) P) x τ ∧ τ j ≠ 0)) :
    Odd (arcMeet Q t (clampedSweep c (fun s => 1 - s) P)).ncard
      ↔ Odd (coreSideCount Q c P) :=
  odd_ncard_arcMeet_iff_core_boxH Q t c P hQseam (contMDiff_arcFam hQ t)
    (contMDiff_clampedSweep c (fun s => 1 - s) P (by fun_prop) hP)
    (fun x hx => (clampedSweep_seamInv c (fun s => 1 - s) P hPseam x hx).symm)
    (havoid_arcFam hc (by norm_num) (by norm_num) hdisj hlev t) htrans hface

end

end Work.Drive

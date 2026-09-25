import Mathlib
import Submission.Work.LT.Defs
import Submission.Work.LT.lr_local_defs
import Submission.Work.LT.lr_spectral_M0
import Submission.Work.LT.lr_spectral_class_A
import Submission.Work.LT.lr_spectral_class_B
import Submission.Work.LT.lr_incidence_A
import Submission.Work.LT.lr_incidence_B
import Submission.Work.LT.lr_claim410_A
import Submission.Work.LT.lr_claim410_B
import Submission.Work.LT.lr_claim411
import Submission.Work.LT.lr_far_edge_count
import Submission.Work.LT.lr_M_case
import Submission.Work.LT.lr_Mpar_case

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/LT/DESIGN.md first (the orchestrator's design; your lemma is one node of its DAG). Shared definitions: Submission/Work/LT/Defs.lean (namespace Work.LT) — do NOT edit it; if you need a new shared definition, put it in your own file. Siblings are being proved in parallel; import them when they land.

# lr_local_opt_far — guidance

**This is the heart of the whole project.** Follow DELLM §4.2, proof of Proposition 4.8
(arXiv 2111.04808 v1, pp. 18–22), transcribed to the quadripartite complex of `Defs.lean`.
Notation: vertices `(α,β,g)`; edges: A-edges `(β,g,i)` between `(0,β,g)` and `(1,β,A i * g)`,
B-edges `(α,g,j)` between `(α,0,g)` and `(α,1,g * B j)`; `4|G|Δ` edges. `R` = disputed edges,
`c = κ0 δ0/(8+κ0)`, `γ = κ0/(8+κ0)`.

The file below implements the following route (a slight sharpening of the guidance's step 4, in
which the "parallel" branch and the "M" branch are combined exactly as in DELLM's Lemma 4.13):

1. `Claim 4.10` (local distance, delegated to `lr_claim410_A/B`): a disputed edge forces
   `δ0 Δ` disputes among its square-neighbours.
2. `Claim 4.11` (local agreement, delegated to `lr_claim411`) plus the far-edge count
   (`lr_far_edge_count`) give the per-vertex bound `κ0 * Sfun u ≤ 4Δ * Qfun u`.
3. The pointwise bound `γ δ0 ≤ γ * parA p + (1-γ) * MstepA p` for every disputed edge `p`.
4. Summing gives `γ ⟨1_R, M‖ 1_R⟩ + (1-γ) ⟨1_R, M 1_R⟩ ≥ γ δ0 |R|`.
5. Dichotomy + the spectral bounds (`lr_spectral_M0`, `lr_M_case`, `lr_spectral_class_A/B`,
   `lr_Mpar_case`) + the incidence identities (`lr_incidence_A/B`) finish the proof.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Classical
open scoped BigOperators

namespace Work.LT

variable {G : Type} [Group G] [Fintype G] {Δ : ℕ}

/-- The A-part of the parallel-move quadratic form. -/
noncomputable def MparA (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) : ℝ :=
  ∑ p : EIdx G Δ, if disputeA A W p.1 p.2.1 p.2.2 then parA A B W p else 0

/-- The B-part of the parallel-move quadratic form. -/
noncomputable def MparB (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) : ℝ :=
  ∑ p : EIdx G Δ, if disputeB B W p.1 p.2.1 p.2.2 then parB A B W p else 0

/-- The A-part of the `M`-move quadratic form. -/
noncomputable def MmoveA (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) : ℝ :=
  ∑ p : EIdx G Δ, if disputeA A W p.1 p.2.1 p.2.2 then MstepA A B W p else 0

/-- The B-part of the `M`-move quadratic form. -/
noncomputable def MmoveB (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) : ℝ :=
  ∑ p : EIdx G Δ, if disputeB B W p.1 p.2.1 p.2.2 then MstepB A B W p else 0

/-! ### Counting helpers -/

lemma mem_tensorCode_iff {CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)}
    {w : Fin Δ × Fin Δ → ZMod 2} :
    w ∈ tensorCode CA CB ↔
      (∀ i, (fun j => w (i, j)) ∈ CB) ∧ (∀ j, (fun i => w (i, j)) ∈ CA) := by
  unfold tensorCode
  simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => h1 i, fun j => h2 j⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => h1 i, fun j => h2 j⟩

/-- `dispCount` is the number of disputed A-edges plus disputed B-edges. -/
lemma dispCount_eq_card (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) :
    dispCount A B W
      = (Finset.univ.filter (fun p : EIdx G Δ => disputeA A W p.1 p.2.1 p.2.2)).card
        + (Finset.univ.filter (fun p : EIdx G Δ => disputeB B W p.1 p.2.1 p.2.2)).card :=
  rfl

/-- The sum of the indicator of `disputeA` over all A-edges, as a real number. -/
lemma sum_disputeA (A : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) :
    (∑ p : EIdx G Δ, (if disputeA A W p.1 p.2.1 p.2.2 then (1 : ℝ) else 0))
      = ((Finset.univ.filter (fun p : EIdx G Δ =>
          disputeA A W p.1 p.2.1 p.2.2)).card : ℝ) := by
  rw [Finset.card_filter]
  push_cast
  exact Finset.sum_congr rfl (fun x _ => rfl)

lemma sum_disputeB (B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) :
    (∑ p : EIdx G Δ, (if disputeB B W p.1 p.2.1 p.2.2 then (1 : ℝ) else 0))
      = ((Finset.univ.filter (fun p : EIdx G Δ =>
          disputeB B W p.1 p.2.1 p.2.2)).card : ℝ) := by
  rw [Finset.card_filter]
  push_cast
  exact Finset.sum_congr rfl (fun x _ => rfl)

lemma MparForm_eq (A B : Fin Δ → G) (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) :
    MparForm A B W = MparA A B W + MparB A B W := rfl

/-! ### Pure algebra helpers -/

/-- The dichotomy step: a convex combination dominating `c |R|` has one term dominating it. -/
lemma mix_dichotomy {γ c Rc Mpar M : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (_ : 0 < Rc)
    (hmix : c * Rc ≤ γ * Mpar + (1 - γ) * M) :
    c * Rc ≤ Mpar ∨ c * Rc ≤ M := by
  by_cases h : c * Rc ≤ Mpar
  · exact Or.inl h
  · right
    have h' : Mpar < c * Rc := not_le.mp h
    nlinarith [hmix, hγ0, hγ1]

/-- The algebra of the `M` branch: if `c ≤ p + μ(1-p)` with `p = |R|/|E|`, `|E| = 4Δ|G|` and
`Δ ≥ 1`, then `(c-μ)|G| ≤ |R|`. -/
lemma M_algebra {c μ p Rc N D : ℝ} (hD : 1 ≤ D) (hN : 0 ≤ N) (hp0 : 0 ≤ p) (hμ : 0 ≤ μ)
    (hRc : 0 < Rc) (hE : Rc = p * (4 * D * N)) (hc : c ≤ p + μ * (1 - p)) :
    (c - μ) * N ≤ Rc := by
  rcases le_or_gt c μ with h | h
  · have : (c - μ) * N ≤ 0 := by nlinarith
    linarith
  · have hcm : 0 < c - μ := by linarith
    have hppos : 0 < p := by
      by_contra hle
      have hpz : p = 0 := le_antisymm (not_lt.mp hle) hp0
      rw [hpz] at hE
      simp at hE
      linarith [hE ▸ hRc]
    have h1μ : 0 < 1 - μ := by
      by_contra hle
      have : 1 - μ ≤ 0 := not_lt.mp hle
      have hp' : p * (1 - μ) ≥ c - μ := by nlinarith
      nlinarith
    have hp' : p * (1 - μ) ≥ c - μ := by nlinarith
    have hmm : (1 - μ) ≤ 1 := by linarith
    have hpc : c - μ ≤ p := by
      have : p * (1 - μ) ≤ p * 1 := mul_le_mul_of_nonneg_left hmm hp0
      linarith
    have hNpos : 0 < N := by
      rcases lt_or_ge N 0 with hlt | hge
      · rw [hE] at hRc
        nlinarith
      · rcases eq_or_lt_of_le hge with h0 | h0
        · rw [← h0] at hE
          simp at hE
          linarith [hE ▸ hRc]
        · exact h0
    have h4 : N ≤ 4 * D * N := by
      have h1 : (1 : ℝ) ≤ 4 * D := by linarith
      calc N = 1 * N := by ring
        _ ≤ (4 * D) * N := mul_le_mul_of_nonneg_right h1 (by linarith : (0:ℝ) ≤ N)
    have hcm' : 0 ≤ c - μ := le_of_lt hcm
    have h4N : 0 ≤ 4 * D * N := by nlinarith
    calc (c - μ) * N ≤ (c - μ) * (4 * D * N) := mul_le_mul_of_nonneg_left h4 hcm'
      _ ≤ p * (4 * D * N) := mul_le_mul_of_nonneg_right hpc h4N
      _ = Rc := hE.symm

end Work.LT

namespace Work.LT

variable {G : Type} [Group G] [Fintype G] {Δ : ℕ}

/-! ### The pointwise bound for a disputed edge -/

/-- The pointwise bound of DELLM Lemma 4.13 for a disputed A-edge: with probability `γ` we jump to
a random parallel A-edge, and with probability `1-γ` we perform the `M`-move from a random
endpoint. Claim 4.10 and the per-vertex bound give `γ δ0`. -/
private lemma pointwise_A (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (δ0 κ0 γ : ℝ)
    (hΔR : (0 : ℝ) < (Δ : ℝ)) (hγ : γ = κ0 / (8 + κ0)) (hκ0 : 0 < κ0)
    (hQ : ∀ u : Vtx G, κ0 * Sfun A B W u ≤ 4 * (Δ : ℝ) * Qfun A B W u)
    (h410 : ∀ p : EIdx G Δ, disputeA A W p.1 p.2.1 p.2.2 →
      δ0 * (Δ : ℝ) ≤ parA A B W p * (Δ : ℝ) + (rB B W (0, p.1, p.2.1) : ℝ)
        + (rB B W (1, p.1, A p.2.2 * p.2.1) : ℝ))
    (p : EIdx G Δ) (hp : disputeA A W p.1 p.2.1 p.2.2) :
    γ * δ0 ≤ γ * parA A B W p + (1 - γ) * MstepA A B W p := by
  have hΔne : (Δ : ℝ) ≠ 0 := ne_of_gt hΔR
  have h8 : (0 : ℝ) < 8 + κ0 := by linarith
  have hγpos : 0 < γ := by rw [hγ]; exact div_pos hκ0 h8
  have hκγ : (1 - γ) * κ0 / 8 = γ := by rw [hγ]; field_simp; ring
  have hpar : parA A B W p * (Δ : ℝ) = ((Finset.univ.filter (fun j : Fin Δ =>
      dispAE A W (nB B (0, p.1, p.2.1) j) p.2.2)).card : ℝ) := by
    simp only [parA]
    rw [div_mul_cancel₀ _ hΔne]
  have h410' : δ0 * (Δ : ℝ) ≤ ((Finset.univ.filter (fun j : Fin Δ =>
      dispAE A W (nB B (0, p.1, p.2.1) j) p.2.2)).card : ℝ)
      + (rB B W (0, p.1, p.2.1) : ℝ) + (rB B W (1, p.1, A p.2.2 * p.2.1) : ℝ) := by
    have h := h410 p hp
    rw [hpar] at h
    exact h
  have hstep : MstepA A B W p * (Δ : ℝ) ≥ κ0 * ((rB B W (0, p.1, p.2.1) : ℝ)
      + (rB B W (1, p.1, A p.2.2 * p.2.1) : ℝ)) / 8 := by
    have hQv := hQ (0, p.1, p.2.1)
    have hQw := hQ (1, p.1, A p.2.2 * p.2.1)
    have hrv : (rB B W (0, p.1, p.2.1) : ℝ) ≤ Sfun A B W (0, p.1, p.2.1) := by
      simp only [Sfun]; linarith [(Nat.cast_nonneg (rA A W (0, p.1, p.2.1)) : (0:ℝ) ≤ (rA A W (0, p.1, p.2.1) : ℝ))]
    have hrw : (rB B W (1, p.1, A p.2.2 * p.2.1) : ℝ)
        ≤ Sfun A B W (1, p.1, A p.2.2 * p.2.1) := by
      simp only [Sfun]; linarith [(Nat.cast_nonneg (rA A W (1, p.1, A p.2.2 * p.2.1)) : (0:ℝ) ≤ (rA A W (1, p.1, A p.2.2 * p.2.1) : ℝ))]
    have e1 := mul_le_mul_of_nonneg_left hrv hκ0.le
    have e2 := mul_le_mul_of_nonneg_left hrw hκ0.le
    simp only [MstepA]
    nlinarith [hQv, hQw, e1, e2]
  have h2 : γ * ((rB B W (0, p.1, p.2.1) : ℝ) + (rB B W (1, p.1, A p.2.2 * p.2.1) : ℝ))
      ≤ (1 - γ) * (MstepA A B W p * (Δ : ℝ)) := by
    have hγle1 : γ ≤ 1 := by rw [hγ]; rw [div_le_iff₀ h8]; linarith
    have h3 := mul_le_mul_of_nonneg_left hstep (by linarith : (0 : ℝ) ≤ 1 - γ)
    have h4 : (1 - γ) * (κ0 * ((rB B W (0, p.1, p.2.1) : ℝ)
        + (rB B W (1, p.1, A p.2.2 * p.2.1) : ℝ)) / 8)
        = γ * ((rB B W (0, p.1, p.2.1) : ℝ) + (rB B W (1, p.1, A p.2.2 * p.2.1) : ℝ)) := by
      calc (1 - γ) * (κ0 * ((rB B W (0, p.1, p.2.1) : ℝ)
            + (rB B W (1, p.1, A p.2.2 * p.2.1) : ℝ)) / 8)
          = ((1 - γ) * κ0 / 8) * ((rB B W (0, p.1, p.2.1) : ℝ)
            + (rB B W (1, p.1, A p.2.2 * p.2.1) : ℝ)) := by ring
        _ = γ * ((rB B W (0, p.1, p.2.1) : ℝ) + (rB B W (1, p.1, A p.2.2 * p.2.1) : ℝ)) := by
            rw [hκγ]
    linarith
  have key : γ * δ0 * (Δ : ℝ) ≤ (γ * parA A B W p + (1 - γ) * MstepA A B W p) * (Δ : ℝ) := by
    have hexp : (γ * parA A B W p + (1 - γ) * MstepA A B W p) * (Δ : ℝ)
        = γ * (parA A B W p * (Δ : ℝ)) + (1 - γ) * (MstepA A B W p * (Δ : ℝ)) := by ring
    have h1 : γ * (δ0 * (Δ : ℝ)) ≤ γ * (((Finset.univ.filter (fun j : Fin Δ =>
        dispAE A W (nB B (0, p.1, p.2.1) j) p.2.2)).card : ℝ)
        + (rB B W (0, p.1, p.2.1) : ℝ) + (rB B W (1, p.1, A p.2.2 * p.2.1) : ℝ)) :=
      mul_le_mul_of_nonneg_left h410' hγpos.le
    rw [hexp, hpar]
    nlinarith [h1, h2]
  exact le_of_mul_le_mul_right key hΔR

/-- The pointwise bound for a disputed B-edge (transpose of `pointwise_A`). -/
private lemma pointwise_B (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (δ0 κ0 γ : ℝ)
    (hΔR : (0 : ℝ) < (Δ : ℝ)) (hγ : γ = κ0 / (8 + κ0)) (hκ0 : 0 < κ0)
    (hQ : ∀ u : Vtx G, κ0 * Sfun A B W u ≤ 4 * (Δ : ℝ) * Qfun A B W u)
    (h410 : ∀ p : EIdx G Δ, disputeB B W p.1 p.2.1 p.2.2 →
      δ0 * (Δ : ℝ) ≤ parB A B W p * (Δ : ℝ) + (rA A W (p.1, 0, p.2.1) : ℝ)
        + (rA A W (p.1, 1, p.2.1 * B p.2.2) : ℝ))
    (p : EIdx G Δ) (hp : disputeB B W p.1 p.2.1 p.2.2) :
    γ * δ0 ≤ γ * parB A B W p + (1 - γ) * MstepB A B W p := by
  have hΔne : (Δ : ℝ) ≠ 0 := ne_of_gt hΔR
  have h8 : (0 : ℝ) < 8 + κ0 := by linarith
  have hγpos : 0 < γ := by rw [hγ]; exact div_pos hκ0 h8
  have hκγ : (1 - γ) * κ0 / 8 = γ := by rw [hγ]; field_simp; ring
  have hpar : parB A B W p * (Δ : ℝ) = ((Finset.univ.filter (fun i : Fin Δ =>
      dispBE B W (nA A (p.1, 0, p.2.1) i) p.2.2)).card : ℝ) := by
    simp only [parB]
    rw [div_mul_cancel₀ _ hΔne]
  have h410' : δ0 * (Δ : ℝ) ≤ ((Finset.univ.filter (fun i : Fin Δ =>
      dispBE B W (nA A (p.1, 0, p.2.1) i) p.2.2)).card : ℝ)
      + (rA A W (p.1, 0, p.2.1) : ℝ) + (rA A W (p.1, 1, p.2.1 * B p.2.2) : ℝ) := by
    have h := h410 p hp
    rw [hpar] at h
    exact h
  have hstep : MstepB A B W p * (Δ : ℝ) ≥ κ0 * ((rA A W (p.1, 0, p.2.1) : ℝ)
      + (rA A W (p.1, 1, p.2.1 * B p.2.2) : ℝ)) / 8 := by
    have hQv := hQ (p.1, 0, p.2.1)
    have hQw := hQ (p.1, 1, p.2.1 * B p.2.2)
    have hrv : (rA A W (p.1, 0, p.2.1) : ℝ) ≤ Sfun A B W (p.1, 0, p.2.1) := by
      simp only [Sfun]; linarith [(Nat.cast_nonneg (rB B W (p.1, 0, p.2.1)) : (0:ℝ) ≤ (rB B W (p.1, 0, p.2.1) : ℝ))]
    have hrw : (rA A W (p.1, 1, p.2.1 * B p.2.2) : ℝ)
        ≤ Sfun A B W (p.1, 1, p.2.1 * B p.2.2) := by
      simp only [Sfun]; linarith [(Nat.cast_nonneg (rB B W (p.1, 1, p.2.1 * B p.2.2)) : (0:ℝ) ≤ (rB B W (p.1, 1, p.2.1 * B p.2.2) : ℝ))]
    have e1 := mul_le_mul_of_nonneg_left hrv hκ0.le
    have e2 := mul_le_mul_of_nonneg_left hrw hκ0.le
    simp only [MstepB]
    nlinarith [hQv, hQw, e1, e2]
  have h2 : γ * ((rA A W (p.1, 0, p.2.1) : ℝ) + (rA A W (p.1, 1, p.2.1 * B p.2.2) : ℝ))
      ≤ (1 - γ) * (MstepB A B W p * (Δ : ℝ)) := by
    have hγle1 : γ ≤ 1 := by rw [hγ]; rw [div_le_iff₀ h8]; linarith
    have h3 := mul_le_mul_of_nonneg_left hstep (by linarith : (0 : ℝ) ≤ 1 - γ)
    have h4 : (1 - γ) * (κ0 * ((rA A W (p.1, 0, p.2.1) : ℝ)
        + (rA A W (p.1, 1, p.2.1 * B p.2.2) : ℝ)) / 8)
        = γ * ((rA A W (p.1, 0, p.2.1) : ℝ) + (rA A W (p.1, 1, p.2.1 * B p.2.2) : ℝ)) := by
      calc (1 - γ) * (κ0 * ((rA A W (p.1, 0, p.2.1) : ℝ)
            + (rA A W (p.1, 1, p.2.1 * B p.2.2) : ℝ)) / 8)
          = ((1 - γ) * κ0 / 8) * ((rA A W (p.1, 0, p.2.1) : ℝ)
            + (rA A W (p.1, 1, p.2.1 * B p.2.2) : ℝ)) := by ring
        _ = γ * ((rA A W (p.1, 0, p.2.1) : ℝ) + (rA A W (p.1, 1, p.2.1 * B p.2.2) : ℝ)) := by
            rw [hκγ]
    linarith
  have key : γ * δ0 * (Δ : ℝ) ≤ (γ * parB A B W p + (1 - γ) * MstepB A B W p) * (Δ : ℝ) := by
    have hexp : (γ * parB A B W p + (1 - γ) * MstepB A B W p) * (Δ : ℝ)
        = γ * (parB A B W p * (Δ : ℝ)) + (1 - γ) * (MstepB A B W p * (Δ : ℝ)) := by ring
    have h1 : γ * (δ0 * (Δ : ℝ)) ≤ γ * (((Finset.univ.filter (fun i : Fin Δ =>
        dispBE B W (nA A (p.1, 0, p.2.1) i) p.2.2)).card : ℝ)
        + (rA A W (p.1, 0, p.2.1) : ℝ) + (rA A W (p.1, 1, p.2.1 * B p.2.2) : ℝ)) :=
      mul_le_mul_of_nonneg_left h410' hγpos.le
    rw [hexp, hpar]
    nlinarith [h1, h2]
  exact le_of_mul_le_mul_right key hΔR

end Work.LT

namespace Work.LT

variable {G : Type} [Group G] [Fintype G] {Δ : ℕ}

lemma two_sum_disputeA (A : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) :
    (∑ p : EIdx G Δ, (if disputeA A W p.1 p.2.1 p.2.2 then (2 : ℝ) else 0))
      = 2 * ((Finset.univ.filter (fun p : EIdx G Δ =>
          disputeA A W p.1 p.2.1 p.2.2)).card : ℝ) := by
  rw [← sum_disputeA A W, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases h : disputeA A W p.1 p.2.1 p.2.2 <;> simp [h]

lemma two_sum_disputeB (B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) :
    (∑ p : EIdx G Δ, (if disputeB B W p.1 p.2.1 p.2.2 then (2 : ℝ) else 0))
      = 2 * ((Finset.univ.filter (fun p : EIdx G Δ =>
          disputeB B W p.1 p.2.1 p.2.2)).card : ℝ) := by
  rw [← sum_disputeB B W, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases h : disputeB B W p.1 p.2.1 p.2.2 <;> simp [h]

/-! ### The `M`-move sums -/

private lemma MmoveA_eq (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2))
    (hinc : (∑ p : EIdx G Δ, if disputeA A W p.1 p.2.1 p.2.2 then
        Qfun A B W (0, p.1, p.2.1) + Qfun A B W (1, p.1, A p.2.2 * p.2.1) else 0)
      = ∑ v : Vtx G, (rA A W v : ℝ) * Qfun A B W v) :
    MmoveA A B W = (1 / 2) * ∑ v : Vtx G, (rA A W v : ℝ) * Qfun A B W v := by
  simp only [MmoveA]
  rw [← hinc, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases hp : disputeA A W p.1 p.2.1 p.2.2
  · simp only [hp, if_true, MstepA]; ring
  · simp [hp]

private lemma MmoveB_eq (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2))
    (hinc : (∑ p : EIdx G Δ, if disputeB B W p.1 p.2.1 p.2.2 then
        Qfun A B W (p.1, 0, p.2.1) + Qfun A B W (p.1, 1, p.2.1 * B p.2.2) else 0)
      = ∑ v : Vtx G, (rB B W v : ℝ) * Qfun A B W v) :
    MmoveB A B W = (1 / 2) * ∑ v : Vtx G, (rB B W v : ℝ) * Qfun A B W v := by
  simp only [MmoveB]
  rw [← hinc, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases hp : disputeB B W p.1 p.2.1 p.2.2
  · simp only [hp, if_true, MstepB]; ring
  · simp [hp]

private lemma MForm_eq (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2))
    (hA : MmoveA A B W = (1 / 2) * ∑ v : Vtx G, (rA A W v : ℝ) * Qfun A B W v)
    (hB : MmoveB A B W = (1 / 2) * ∑ v : Vtx G, (rB B W v : ℝ) * Qfun A B W v) :
    MForm A B W = MmoveA A B W + MmoveB A B W := by
  simp only [MForm, Sfun]
  have hsum : (∑ v : Vtx G, ((rA A W v : ℝ) + (rB B W v : ℝ)) * Qfun A B W v)
      = (∑ v : Vtx G, (rA A W v : ℝ) * Qfun A B W v)
        + (∑ v : Vtx G, (rB B W v : ℝ) * Qfun A B W v) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v _ => by ring)
  rw [hsum, hA, hB]
  ring

/-! ### The mixture inequality -/

/-- Summing the pointwise bound over all disputed edges: the two operators together detect `γ δ0`
of the disputed edges. -/
private lemma mix_bound (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (δ0 κ0 γ : ℝ)
    (hΔR : (0 : ℝ) < (Δ : ℝ)) (hγ : γ = κ0 / (8 + κ0)) (hκ0 : 0 < κ0)
    (hQ : ∀ u : Vtx G, κ0 * Sfun A B W u ≤ 4 * (Δ : ℝ) * Qfun A B W u)
    (h410A : ∀ p : EIdx G Δ, disputeA A W p.1 p.2.1 p.2.2 →
      δ0 * (Δ : ℝ) ≤ parA A B W p * (Δ : ℝ) + (rB B W (0, p.1, p.2.1) : ℝ)
        + (rB B W (1, p.1, A p.2.2 * p.2.1) : ℝ))
    (h410B : ∀ p : EIdx G Δ, disputeB B W p.1 p.2.1 p.2.2 →
      δ0 * (Δ : ℝ) ≤ parB A B W p * (Δ : ℝ) + (rA A W (p.1, 0, p.2.1) : ℝ)
        + (rA A W (p.1, 1, p.2.1 * B p.2.2) : ℝ))
    (hincA : ∀ F : Vtx G → ℝ,
      (∑ p : EIdx G Δ, if disputeA A W p.1 p.2.1 p.2.2
        then F (0, p.1, p.2.1) + F (1, p.1, A p.2.2 * p.2.1) else 0)
      = ∑ v : Vtx G, (rA A W v : ℝ) * F v)
    (hincB : ∀ F : Vtx G → ℝ,
      (∑ p : EIdx G Δ, if disputeB B W p.1 p.2.1 p.2.2
        then F (p.1, 0, p.2.1) + F (p.1, 1, p.2.1 * B p.2.2) else 0)
      = ∑ v : Vtx G, (rB B W v : ℝ) * F v) :
    γ * MparForm A B W + (1 - γ) * MForm A B W ≥ γ * δ0 * (dispCount A B W : ℝ) := by
  have hptA : ∀ p : EIdx G Δ, (if disputeA A W p.1 p.2.1 p.2.2 then γ * δ0 else 0)
      ≤ (if disputeA A W p.1 p.2.1 p.2.2 then
          γ * parA A B W p + (1 - γ) * MstepA A B W p else 0) := by
    intro p
    by_cases hp : disputeA A W p.1 p.2.1 p.2.2
    · simpa [hp] using pointwise_A A B W δ0 κ0 γ hΔR hγ hκ0 hQ h410A p hp
    · simp [hp]
  have hptB : ∀ p : EIdx G Δ, (if disputeB B W p.1 p.2.1 p.2.2 then γ * δ0 else 0)
      ≤ (if disputeB B W p.1 p.2.1 p.2.2 then
          γ * parB A B W p + (1 - γ) * MstepB A B W p else 0) := by
    intro p
    by_cases hp : disputeB B W p.1 p.2.1 p.2.2
    · simpa [hp] using pointwise_B A B W δ0 κ0 γ hΔR hγ hκ0 hQ h410B p hp
    · simp [hp]
  have hsA := Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) => hptA p)
  have hsB := Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) => hptB p)
  have e1A : (∑ p : EIdx G Δ, (if disputeA A W p.1 p.2.1 p.2.2 then γ * δ0 else 0))
      = γ * δ0 * (∑ p : EIdx G Δ, (if disputeA A W p.1 p.2.1 p.2.2 then (1 : ℝ) else 0)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases hp : disputeA A W p.1 p.2.1 p.2.2 <;> simp [hp]
  have e1B : (∑ p : EIdx G Δ, (if disputeB B W p.1 p.2.1 p.2.2 then γ * δ0 else 0))
      = γ * δ0 * (∑ p : EIdx G Δ, (if disputeB B W p.1 p.2.1 p.2.2 then (1 : ℝ) else 0)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases hp : disputeB B W p.1 p.2.1 p.2.2 <;> simp [hp]
  have e2A : (∑ p : EIdx G Δ, (if disputeA A W p.1 p.2.1 p.2.2 then
        γ * parA A B W p + (1 - γ) * MstepA A B W p else 0))
      = γ * MparA A B W + (1 - γ) * MmoveA A B W := by
    simp only [MparA, MmoveA]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases hp : disputeA A W p.1 p.2.1 p.2.2 <;> simp [hp]
  have e2B : (∑ p : EIdx G Δ, (if disputeB B W p.1 p.2.1 p.2.2 then
        γ * parB A B W p + (1 - γ) * MstepB A B W p else 0))
      = γ * MparB A B W + (1 - γ) * MmoveB A B W := by
    simp only [MparB, MmoveB]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases hp : disputeB B W p.1 p.2.1 p.2.2 <;> simp [hp]
  have hA : γ * MparA A B W + (1 - γ) * MmoveA A B W ≥ γ * δ0 *
      (∑ p : EIdx G Δ, (if disputeA A W p.1 p.2.1 p.2.2 then (1 : ℝ) else 0)) := by
    rw [← e2A, ← e1A]
    exact hsA
  have hB : γ * MparB A B W + (1 - γ) * MmoveB A B W ≥ γ * δ0 *
      (∑ p : EIdx G Δ, (if disputeB B W p.1 p.2.1 p.2.2 then (1 : ℝ) else 0)) := by
    rw [← e2B, ← e1B]
    exact hsB
  have hdc : (dispCount A B W : ℝ)
      = (∑ p : EIdx G Δ, (if disputeA A W p.1 p.2.1 p.2.2 then (1 : ℝ) else 0))
        + (∑ p : EIdx G Δ, (if disputeB B W p.1 p.2.1 p.2.2 then (1 : ℝ) else 0)) := by
    rw [sum_disputeA, sum_disputeB, dispCount_eq_card]
    push_cast
    ring
  have hMF : MForm A B W = MmoveA A B W + MmoveB A B W :=
    MForm_eq A B W (MmoveA_eq A B W (hincA (Qfun A B W)))
      (MmoveB_eq A B W (hincB (Qfun A B W)))
  rw [MparForm_eq, hMF, hdc]
  linarith [hA, hB]

end Work.LT

namespace Work.LT

variable {G : Type} [Group G] [Fintype G] {Δ : ℕ}

/-- The assembly: given the local claims (4.10, 4.11 + far-edge count, the incidence identities)
and the two spectral consequences (`lr_M_case`, `lr_Mpar_case`), DELLM Proposition 4.8 follows. -/
private theorem aux (A B : Fin Δ → G)
    (δ0 κ0 μ : ℝ) (hκ0 : 0 < κ0) (hδ1 : δ0 ≤ 1) (hμ : 0 ≤ μ)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2))
    (hQ : ∀ u : Vtx G, κ0 * Sfun A B W u ≤ 4 * (Δ : ℝ) * Qfun A B W u)
    (h410A : ∀ p : EIdx G Δ, disputeA A W p.1 p.2.1 p.2.2 →
      δ0 * (Δ : ℝ) ≤ parA A B W p * (Δ : ℝ) + (rB B W (0, p.1, p.2.1) : ℝ)
        + (rB B W (1, p.1, A p.2.2 * p.2.1) : ℝ))
    (h410B : ∀ p : EIdx G Δ, disputeB B W p.1 p.2.1 p.2.2 →
      δ0 * (Δ : ℝ) ≤ parB A B W p * (Δ : ℝ) + (rA A W (p.1, 0, p.2.1) : ℝ)
        + (rA A W (p.1, 1, p.2.1 * B p.2.2) : ℝ))
    (hincA : ∀ F : Vtx G → ℝ,
      (∑ p : EIdx G Δ, if disputeA A W p.1 p.2.1 p.2.2
        then F (0, p.1, p.2.1) + F (1, p.1, A p.2.2 * p.2.1) else 0)
      = ∑ v : Vtx G, (rA A W v : ℝ) * F v)
    (hincB : ∀ F : Vtx G → ℝ,
      (∑ p : EIdx G Δ, if disputeB B W p.1 p.2.1 p.2.2
        then F (p.1, 0, p.2.1) + F (p.1, 1, p.2.1 * B p.2.2) else 0)
      = ∑ v : Vtx G, (rB B W v : ℝ) * F v)
    (hMcase : MForm A B W ≤ (dispCount A B W : ℝ) *
      ((dispCount A B W : ℝ) / (4 * Δ * Fintype.card G)
        + μ * (1 - (dispCount A B W : ℝ) / (4 * Δ * Fintype.card G))))
    (hMpar : (κ0 * δ0 / (8 + κ0)) * (dispCount A B W : ℝ) ≤ MparForm A B W →
      (κ0 * δ0 / (8 + κ0) - μ) * (Fintype.card G : ℝ) ≤ (dispCount A B W : ℝ)) :
    dispCount A B W = 0 ∨
      (κ0 * δ0 / (8 + κ0) - μ) * Fintype.card G ≤ dispCount A B W := by
  by_cases h0 : dispCount A B W = 0
  · exact Or.inl h0
  · right
    have hpos : 0 < (dispCount A B W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
    have hΔ : 0 < Δ := by
      by_contra h
      have hz : Δ = 0 := Nat.eq_zero_of_not_pos h
      exact h0 (by subst hz; simp [dispCount])
    have hΔR : (0 : ℝ) < (Δ : ℝ) := by exact_mod_cast hΔ
    set γ : ℝ := κ0 / (8 + κ0) with hγ
    have h8 : (0 : ℝ) < 8 + κ0 := by linarith
    have hγpos : 0 < γ := by rw [hγ]; exact div_pos hκ0 h8
    have hγlt1 : γ < 1 := by rw [hγ, div_lt_one h8]; linarith
    have hcγ : κ0 * δ0 / (8 + κ0) = γ * δ0 := by rw [hγ]; ring
    have hmix : γ * δ0 * (dispCount A B W : ℝ)
        ≤ γ * MparForm A B W + (1 - γ) * MForm A B W := by
      have h := mix_bound A B W δ0 κ0 γ hΔR hγ hκ0 hQ h410A h410B hincA hincB
      linarith
    rcases mix_dichotomy hγpos hγlt1 hpos hmix with hcase | hcase
    · exact hMpar (by rw [hcγ]; exact hcase)
    · set N : ℝ := (Fintype.card G : ℝ) with hN
      set Rc : ℝ := (dispCount A B W : ℝ) with hRc
      set p : ℝ := Rc / (4 * (Δ : ℝ) * N) with hp
      have hNpos : 0 < N := by
        rw [hN]; exact_mod_cast (Fintype.card_pos_iff.mpr ⟨1⟩)
      have hp0 : 0 ≤ p := by rw [hp]; positivity
      have hRcpos : 0 < Rc := by rw [hRc]; exact hpos
      have hE : Rc = p * (4 * (Δ : ℝ) * N) := by
        rw [hp]; field_simp
      have hD : (1 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ
      have hMc' : MForm A B W ≤ Rc * (p + μ * (1 - p)) := hMcase
      have hcp : γ * δ0 ≤ p + μ * (1 - p) := by
        have h2 : γ * δ0 * Rc ≤ (p + μ * (1 - p)) * Rc := by
          rw [hRc] at hcase
          linarith
        exact le_of_mul_le_mul_right h2 hRcpos
      have hgoal : (γ * δ0 - μ) * N ≤ Rc :=
        M_algebra hD hNpos.le hp0 hμ hRcpos hE hcp
      rw [hcγ]
      exact hgoal



/-- **Heart of local testability** (DELLM Proposition 4.8, quadripartite form). Let `W` assign to
each vertex a tensor codeword and be a local minimum of the number of disputed edges. Then either
no edge is disputed, or at least `(c - μ) |G|` are, where `c = κ0 δ0 / (8 + κ0)`. -/
theorem lr_local_opt_far {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)) (δ0 κ0 μ : ℝ) (hκ0 : 0 < κ0)
    (hδ1 : δ0 ≤ 1) (hμ : 0 ≤ μ)
    (hdA : ∀ x ∈ CA, x ≠ 0 → δ0 * Δ ≤ hammingNorm x)
    (hdB : ∀ x ∈ CB, x ≠ 0 → δ0 * Δ ≤ hammingNorm x)
    (hagr : agreementTestable κ0 CA CB) (hA : leftExpander A μ) (hB : rightExpander B μ)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2))
    (hW : ∀ α β g, W α β g ∈ tensorCode CA CB) (hopt : IsLocalOpt A B CA CB W) :
    dispCount A B W = 0 ∨
      (κ0 * δ0 / (8 + κ0) - μ) * Fintype.card G ≤ dispCount A B W := by
  by_cases h0 : dispCount A B W = 0
  · exact Or.inl h0
  · right
    have hΔ : 0 < Δ := by
      by_contra h
      have hz : Δ = 0 := Nat.eq_zero_of_not_pos h
      exact h0 (by subst hz; simp [dispCount])
    have hΔR : (0 : ℝ) < (Δ : ℝ) := by exact_mod_cast hΔ
    have hposNat : 0 < dispCount A B W := Nat.pos_of_ne_zero h0
    have hrowB : ∀ v : Vtx G, ∀ i : Fin Δ, (fun j => view W v (i, j)) ∈ CB := by
      intro v i
      exact (mem_tensorCode_iff.mp (hW v.1 v.2.1 v.2.2)).1 i
    have hrowA : ∀ v : Vtx G, ∀ j : Fin Δ, (fun i => view W v (i, j)) ∈ CA := by
      intro v j
      exact (mem_tensorCode_iff.mp (hW v.1 v.2.1 v.2.2)).2 j
    -- Per-vertex bound: Claim 4.11 plus the far-edge count.
    have hQ : ∀ u : Vtx G, κ0 * Sfun A B W u ≤ 4 * (Δ : ℝ) * Qfun A B W u := by
      intro u
      have h411 := lr_claim411 A B CA CB κ0 hκ0 hagr W hW hopt u
      have hfar := lr_far_edge_count A B W u
      have h1 : κ0 * (Δ : ℝ) * Sfun A B W u ≤
          (∑ i, (rB B W (nA A u i) : ℝ)) + (∑ j, (rA A W (nB B u j) : ℝ)) := by
        simp only [Sfun]
        linarith
      have h2 : (∑ i, (rB B W (nA A u i) : ℝ)) + (∑ j, (rA A W (nB B u j) : ℝ))
          ≤ (∑ i, Sfun A B W (nA A u i)) + (∑ j, Sfun A B W (nB B u j)) := by
        have e1 : (∑ i : Fin Δ, (rB B W (nA A u i) : ℝ)) ≤ ∑ i, Sfun A B W (nA A u i) :=
          Finset.sum_le_sum (fun i _ => by
            simp only [Sfun]
            linarith [(Nat.cast_nonneg (rA A W (nA A u i)) : (0 : ℝ) ≤
              (rA A W (nA A u i) : ℝ))])
        have e2 : (∑ j : Fin Δ, (rA A W (nB B u j) : ℝ)) ≤ ∑ j, Sfun A B W (nB B u j) :=
          Finset.sum_le_sum (fun j _ => by
            simp only [Sfun]
            linarith [(Nat.cast_nonneg (rB B W (nB B u j)) : (0 : ℝ) ≤
              (rB B W (nB B u j) : ℝ))])
        linarith
      have h3 : (∑ i : Fin Δ, Sfun A B W (nA A u i)) + (∑ j : Fin Δ, Sfun A B W (nB B u j))
          = 4 * (Δ : ℝ) ^ 2 * Qfun A B W u := by
        have hne : (Δ : ℝ) ≠ 0 := ne_of_gt hΔR
        simp only [Qfun, M0, gfun]
        rw [← Finset.sum_div, ← Finset.sum_div]
        field_simp
        ring
      have h4 : κ0 * Sfun A B W u * (Δ : ℝ) ≤ (4 * (Δ : ℝ) * Qfun A B W u) * (Δ : ℝ) := by
        nlinarith [h1, h2, h3]
      exact le_of_mul_le_mul_right h4 hΔR
    -- Claim 4.10 in the form used by `pointwise_A`.
    have h410A : ∀ p : EIdx G Δ, disputeA A W p.1 p.2.1 p.2.2 →
        δ0 * (Δ : ℝ) ≤ parA A B W p * (Δ : ℝ) + (rB B W (0, p.1, p.2.1) : ℝ)
          + (rB B W (1, p.1, A p.2.2 * p.2.1) : ℝ) := by
      intro p hp
      have hdisp : dispAE A W (0, p.1, p.2.1) p.2.2 := by
        refine (disputeA_aIdx A W (0, p.1, p.2.1) p.2.2).mp ?_
        simpa [aIdx] using hp
      have h := lr_claim410_A A B CB δ0 W hrowB hdB (0, p.1, p.2.1) p.2.2 hdisp
      have hnA : nA A (0, p.1, p.2.1) p.2.2 = (1, p.1, A p.2.2 * p.2.1) := by simp [nA]
      have hpar : parA A B W p * (Δ : ℝ) = ((Finset.univ.filter (fun j : Fin Δ =>
          dispAE A W (nB B (0, p.1, p.2.1) j) p.2.2)).card : ℝ) := by
        simp only [parA]
        rw [div_mul_cancel₀ _ (ne_of_gt hΔR)]
      rw [hnA, ← hpar] at h
      exact h
    -- Claim 4.10 in the form used by `pointwise_B`.
    have h410B : ∀ p : EIdx G Δ, disputeB B W p.1 p.2.1 p.2.2 →
        δ0 * (Δ : ℝ) ≤ parB A B W p * (Δ : ℝ) + (rA A W (p.1, 0, p.2.1) : ℝ)
          + (rA A W (p.1, 1, p.2.1 * B p.2.2) : ℝ) := by
      intro p hp
      have hdisp : dispBE B W (p.1, 0, p.2.1) p.2.2 := by
        refine (disputeB_bIdx B W (p.1, 0, p.2.1) p.2.2).mp ?_
        simpa [bIdx] using hp
      have h := lr_claim410_B A B CA δ0 W hrowA hdA (p.1, 0, p.2.1) p.2.2 hdisp
      have hnB : nB B (p.1, 0, p.2.1) p.2.2 = (p.1, 1, p.2.1 * B p.2.2) := by simp [nB]
      have hpar : parB A B W p * (Δ : ℝ) = ((Finset.univ.filter (fun i : Fin Δ =>
          dispBE B W (nA A (p.1, 0, p.2.1) i) p.2.2)).card : ℝ) := by
        simp only [parB]
        rw [div_mul_cancel₀ _ (ne_of_gt hΔR)]
      rw [hnB, ← hpar] at h
      exact h
    have hincA : ∀ F : Vtx G → ℝ,
        (∑ p : EIdx G Δ, if disputeA A W p.1 p.2.1 p.2.2
          then F (0, p.1, p.2.1) + F (1, p.1, A p.2.2 * p.2.1) else 0)
        = ∑ v : Vtx G, (rA A W v : ℝ) * F v := fun F => lr_incidence_A A W F
    have hincB : ∀ F : Vtx G → ℝ,
        (∑ p : EIdx G Δ, if disputeB B W p.1 p.2.1 p.2.2
          then F (p.1, 0, p.2.1) + F (p.1, 1, p.2.1 * B p.2.2) else 0)
        = ∑ v : Vtx G, (rB B W v : ℝ) * F v := fun F => lr_incidence_B B W F
    have hsum : (∑ v : Vtx G, Sfun A B W v) = 2 * (dispCount A B W : ℝ) := by
      have h1 := hincA (fun _ : Vtx G => (1 : ℝ))
      have h2 := hincB (fun _ : Vtx G => (1 : ℝ))
      simp only [Pi.one_apply, mul_one] at h1 h2
      have e1 : (∑ v : Vtx G, (rA A W v : ℝ)) = 2 * ((Finset.univ.filter (fun p : EIdx G Δ =>
          disputeA A W p.1 p.2.1 p.2.2)).card : ℝ) := by
        rw [← two_sum_disputeA A W, h1.symm]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        by_cases hp : disputeA A W p.1 p.2.1 p.2.2
        · simp only [hp, if_true]; norm_num
        · simp [hp]
      have e2 : (∑ v : Vtx G, (rB B W v : ℝ)) = 2 * ((Finset.univ.filter (fun p : EIdx G Δ =>
          disputeB B W p.1 p.2.1 p.2.2)).card : ℝ) := by
        rw [← two_sum_disputeB B W, h2.symm]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        by_cases hp : disputeB B W p.1 p.2.1 p.2.2
        · simp only [hp, if_true]; norm_num
        · simp [hp]
      simp only [Sfun]
      rw [Finset.sum_add_distrib, e1, e2, dispCount_eq_card]
      push_cast
      ring
    have hMcase : MForm A B W ≤ (dispCount A B W : ℝ) *
        ((dispCount A B W : ℝ) / (4 * Δ * Fintype.card G)
          + μ * (1 - (dispCount A B W : ℝ) / (4 * Δ * Fintype.card G))) :=
      lr_M_case A B W μ hΔ hμ (lr_spectral_M0 A B μ hA hB hμ) hsum
    have hMpar : (κ0 * δ0 / (8 + κ0)) * (dispCount A B W : ℝ) ≤ MparForm A B W →
        (κ0 * δ0 / (8 + κ0) - μ) * (Fintype.card G : ℝ) ≤ (dispCount A B W : ℝ) :=
      fun hlarge => lr_Mpar_case A B W μ (κ0 * δ0 / (8 + κ0)) hΔ hμ
        (lr_spectral_class_B A μ hA hμ) (lr_spectral_class_A B μ hB hμ) hposNat hlarge
    exact (aux A B δ0 κ0 μ hκ0 hδ1 hμ W hQ h410A h410B hincA hincB hMcase hMpar).resolve_left h0

end Work.LT

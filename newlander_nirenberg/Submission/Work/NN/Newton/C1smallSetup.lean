import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Final.Defs
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc

/-!
# Definitions for the `C^{1,α}`-small Newlander–Nirenberg iteration

This module fixes the vocabulary of the Newton iteration of
`Work.NN.Newton.exists_holFrame_of_C1small`.

* `delta m = 2^{-(m+3)}` — the logarithmic gap;
* `rad m` — the radii `r_0 = 4`, `r_{m+1} = r_m (1 - 2 δ_m)`;
* `asize ε N m = ε 2^{-2Nm}` — the size `a_m` of the perturbation at stage `m`;
* `bsize C N ε m = (C / δ_m^N) a_m` — the size `β_m` of the `m`-th correction;
* `P n r` — the polydisc of radius `r` about `0` in `Cn n`;
* `NNInv n α N ε m A` — the hypotheses on the perturbation `A` at stage `m`;
* `NNStep n α C N ε m A Φ A'` — the conclusion of one Newton step at stage `m`;
* `Stage`/`build` — the recursion that produces the sequence of perturbations and corrections.
-/

namespace Work.NN.Newton

open scoped ContDiff
open Set Filter

noncomputable section

abbrev Cn (n : ℕ) := Work.NN.Core.Cn n

/-- `δ_m = 2^{-(m+3)}`. -/
def delta (m : ℕ) : ℝ := (1 / 2 : ℝ) ^ (m + 3)

/-- The radii `r_0 = 4`, `r_{m+1} = r_m (1 - 2 δ_m)`. -/
def rad : ℕ → ℝ := Nat.rec 4 (fun m r => r * (1 - 2 * delta m))

@[simp] lemma rad_zero : rad 0 = 4 := rfl
@[simp] lemma rad_succ (m : ℕ) : rad (m + 1) = rad m * (1 - 2 * delta m) := rfl

/-- `a_m = ε 2^{-2Nm}`. -/
def asize (ε : ℝ) (N : ℕ) (m : ℕ) : ℝ := ε * (1 / 2 : ℝ) ^ (2 * N * m)

/-- `β_m = (C/δ_m^N) a_m`. -/
def bsize (C : ℝ) (N : ℕ) (ε : ℝ) (m : ℕ) : ℝ := C / delta m ^ N * asize ε N m

/-- The polydisc of radius `r` centred at the origin in `Cn n`. -/
def P (n : ℕ) (r : ℝ) : Set (Cn n) := Work.CR.Flat.polydisc 0 (fun _ => r)

lemma mem_P {n : ℕ} {r : ℝ} {z : Cn n} : z ∈ P n r ↔ ∀ j, ‖z j‖ < r := by
  simp [P, Work.CR.Flat.mem_polydisc]

lemma isOpen_P (n : ℕ) (r : ℝ) : IsOpen (P n r) := Work.CR.Flat.isOpen_polydisc 0 _

lemma P_mono {n : ℕ} {r r' : ℝ} (h : r ≤ r') : P n r ⊆ P n r' :=
  Work.CR.Flat.polydisc_mono (fun _ => h)

lemma P_eq_pd (n : ℕ) : P n 4 = Work.NN.Final.pd n (fun _ => 1) 4 := by
  ext z
  simp [P, Work.NN.Final.pd, Work.CR.Flat.mem_polydisc]

/-- **The hypotheses on the perturbation at stage `m`.** -/
def NNInv (n : ℕ) (α : ℝ) (N : ℕ) (ε : ℝ) (m : ℕ)
    (A : Cn n → Cn n →L[ℝ] Cn n) : Prop :=
  (∀ k : ℕ, ContDiffOn ℝ k A (P n (rad m))) ∧
  (∀ z, z ∈ P n (rad m) → ∀ v : Cn n,
    (Work.NN.Core.JstdCn n + A) z ((Work.NN.Core.JstdCn n + A) z v) = -v) ∧
  (∀ u : Cn n → ℂ, (∀ k : ℕ, ContDiff ℝ k u) →
    ∀ z, z ∈ P n (rad m) → ∀ V W : Cn n,
      Work.NN.Final.proj02 (Work.NN.Core.JstdCn n + A)
        (fun z' => Work.NN.Final.dOne
          (fun z'' => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z'') z') z V W = 0) ∧
  (∀ w : Cn n, ‖w‖ ≤ 1 → ∀ j : Fin n,
    Work.CR.Flat.holderNorm 1 α (fun z => A z w j) (P n (rad m))
      ≤ ENNReal.ofReal (asize ε N m))

/-- **The conclusion of one Newton step at stage `m`.** -/
def NNStep (n : ℕ) (α : ℝ) (C : ℝ) (N : ℕ) (ε : ℝ) (m : ℕ)
    (A : Cn n → Cn n →L[ℝ] Cn n) (Φ : Cn n → Cn n) (A' : Cn n → Cn n →L[ℝ] Cn n) : Prop :=
  (∀ k : ℕ, ContDiffOn ℝ k Φ (P n (rad m * (1 - delta m)))) ∧
  (∀ z, z ∈ P n (rad m * (1 - delta m)) → ‖Φ z - z‖ ≤ bsize C N ε m) ∧
  (∀ z, z ∈ P n (rad m * (1 - delta m)) →
    ‖fderiv ℝ Φ z - ContinuousLinearMap.id ℝ (Cn n)‖ ≤ bsize C N ε m) ∧
  (∀ k : ℕ, ContDiffOn ℝ k A' (P n (rad m * (1 - 2 * delta m)))) ∧
  (∀ z, z ∈ P n (rad m * (1 - delta m)) → Φ z ∈ P n (rad m * (1 - 2 * delta m)) →
    ∀ h : Cn n,
      fderiv ℝ Φ z ((Work.NN.Core.JstdCn n + A) z h)
        = (Work.NN.Core.JstdCn n + A') (Φ z) (fderiv ℝ Φ z h)) ∧
  (∀ ζ, ζ ∈ P n (rad m * (1 - 2 * delta m)) → ∀ w : Cn n,
    (Work.NN.Core.JstdCn n + A') ζ ((Work.NN.Core.JstdCn n + A') ζ w) = -w) ∧
  (∀ u : Cn n → ℂ, (∀ k : ℕ, ContDiff ℝ k u) →
    ∀ ζ, ζ ∈ P n (rad m * (1 - 2 * delta m)) → ∀ V W : Cn n,
      Work.NN.Final.proj02 (Work.NN.Core.JstdCn n + A')
        (fun z' => Work.NN.Final.dOne
          (fun z'' => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A') u z'') z') ζ V W = 0) ∧
  (∀ w : Cn n, ‖w‖ ≤ 1 → ∀ j : Fin n,
    Work.CR.Flat.holderNorm 1 α (fun ζ => A' ζ w j) (P n (rad m * (1 - 2 * delta m)))
      ≤ ENNReal.ofReal (C / delta m ^ N * (asize ε N m) ^ 2))

/-- **The size estimate of one Newton step implies the hypotheses at the next stage.** -/
lemma NNInv_of_NNStep {n : ℕ} {α C ε : ℝ} {N m : ℕ} {A : Cn n → Cn n →L[ℝ] Cn n}
    {Φ : Cn n → Cn n} {A' : Cn n → Cn n →L[ℝ] Cn n}
    (hnext : C / delta m ^ N * (asize ε N m) ^ 2 ≤ asize ε N (m + 1))
    (h : NNStep n α C N ε m A Φ A') : NNInv n α N ε (m + 1) A' := by
  obtain ⟨-, -, -, hsm, -, hac, hint, hsz⟩ := h
  exact ⟨fun k => hsm k, fun ζ hζ => hac ζ hζ, fun u hu ζ hζ => hint u hu ζ hζ,
    fun w hw j => (hsz w hw j).trans (ENNReal.ofReal_le_ofReal hnext)⟩

/-- One stage of the iteration: the perturbation, the correction, the next perturbation. -/
structure Stage (n : ℕ) (α : ℝ) (C : ℝ) (N : ℕ) (ε : ℝ) (m : ℕ) where
  A : Cn n → Cn n →L[ℝ] Cn n
  Φ : Cn n → Cn n
  A' : Cn n → Cn n →L[ℝ] Cn n
  hInv : NNInv n α N ε m A
  hStep : NNStep n α C N ε m A Φ A'

/-- **The Newton iteration.** -/
noncomputable def build (n : ℕ) (α : ℝ) (C : ℝ) (N : ℕ) (ε : ℝ)
    (A₀ : Cn n → Cn n →L[ℝ] Cn n) (h0 : NNInv n α N ε 0 A₀)
    (hnext : ∀ m, C / delta m ^ N * (asize ε N m) ^ 2 ≤ asize ε N (m + 1))
    (H : ∀ (m : ℕ) (A : Cn n → Cn n →L[ℝ] Cn n), NNInv n α N ε m A →
      ∃ p : (Cn n → Cn n) × (Cn n → Cn n →L[ℝ] Cn n),
        NNStep n α C N ε m A p.1 p.2) :
    (m : ℕ) → Stage n α C N ε m :=
  fun m => Nat.rec
    (let o := Classical.choose (H 0 A₀ h0)
     { A := A₀, Φ := o.1, A' := o.2, hInv := h0
       hStep := Classical.choose_spec (H 0 A₀ h0) })
    (fun m (p : Stage n α C N ε m) =>
      let h' := NNInv_of_NNStep (hnext m) p.hStep
      let o := Classical.choose (H (m + 1) p.A' h')
      { A := p.A', Φ := o.1, A' := o.2, hInv := h'
        hStep := Classical.choose_spec (H (m + 1) p.A' h') })
    m

@[simp] lemma build_zero {n : ℕ} {α C ε : ℝ} {N : ℕ} {A₀ : Cn n → Cn n →L[ℝ] Cn n}
    {h0 hnext H} : (build n α C N ε A₀ h0 hnext H 0).A = A₀ := rfl

lemma build_succ {n : ℕ} {α C ε : ℝ} {N : ℕ} {A₀ : Cn n → Cn n →L[ℝ] Cn n}
    {h0 hnext H} (m : ℕ) :
    (build n α C N ε A₀ h0 hnext H (m + 1)).A
      = (build n α C N ε A₀ h0 hnext H m).A' := by
  simp only [build]

/-- The composite maps `G_m = Φ_{m-1} ∘ ⋯ ∘ Φ_0`. -/
noncomputable def Gseq {n : ℕ} {α C ε : ℝ} {N : ℕ} (bld : (m : ℕ) → Stage n α C N ε m) :
    ℕ → Cn n → Cn n :=
  fun m => Nat.rec id (fun m g => (bld m).Φ ∘ g) m

@[simp] lemma Gseq_zero {n : ℕ} {α C ε : ℝ} {N : ℕ} {bld : (m : ℕ) → Stage n α C N ε m} :
    Gseq bld 0 = id := rfl

@[simp] lemma Gseq_succ {n : ℕ} {α C ε : ℝ} {N : ℕ} {bld : (m : ℕ) → Stage n α C N ε m}
    (m : ℕ) : Gseq bld (m + 1) = (bld m).Φ ∘ Gseq bld m := rfl

end

end Work.NN.Newton

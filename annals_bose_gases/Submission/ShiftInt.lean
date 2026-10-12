import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Neumann
import Submission.Shift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Interaction translation isometry and the Neumann quotient comparison

The mirror of `Submission.Shift` for the interaction energy, and its
consequence for the Neumann ground state.  The interaction `v(x_i − x_l)` is
invariant under shifting *every* particle by the *same* vector `c : ℝ³`
(`constShift N c : X N`), so the interaction energy is translation-isometric
exactly like the kinetic one:

  * `constShift` — the common particle shift by `c`;
  * `intPairSum` — `Σ_{i<l} v(x_i − x_l)`, pointwise translation invariant
    (`intPairSum_shift`);
  * `intWs_constShift` — the whole-space interaction energy
    `∫ f²·intPairSum` is invariant under `constShift`;
  * `intWs_eq_intNeu` — for a function `f` supported in `box N L`, its
    whole-space interaction energy equals `intNeu N L v (f as a CNeu state)`;
  * `kinWs_eq_kinNeu` — the kinetic mirror (whole-space gradient energy equals
    `kinNeu` for a function supported in the box);
  * `CNeu.ofFun` — build a `CNeu` state from a smooth nonzero function with
    positive box norm;
  * `kinWs_eq_box` / `intWs_eq_box` — for a function supported in the box the
    whole-space energies equal the box ones (matching `kinNeu`/`intNeu`);
  * `eNeu_le_quot_ofFun` — the Neumann energy is a lower bound for the
    quotient of any admissible state (the per-cell bracket ingredient).

Template: `Submission.Shift` (proved by hand).  All the measure-preserving
change-of-variables and support plumbing is already there; this file is the
`v`-dependent half plus the Neumann-quotient corollary.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

local notation "⟪" f ", " g "⟫_["N "," L"]" => ∫ x in box N L, f x * g x

/-- The common particle shift by the vector `c`. -/
noncomputable def constShift (N : ℕ) (c : ℝ³) : X N :=
  fun _ : Fin N => c

/-- The pair-interaction density `Σ_{i<l} v(x_i − x_l)`. -/
noncomputable def intPairSum (N : ℕ) (v : ℝ³ → ℝ) (x : X N) : ℝ :=
  ∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)), v (x p.1 - x p.2)

/-- The pair interaction is pointwise invariant under the common shift. -/
lemma intPairSum_shift (N : ℕ) (c : ℝ³) (v : ℝ³ → ℝ) (x : X N) :
    intPairSum N v (x + constShift N c) = intPairSum N v x := by
  unfold intPairSum
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  simp [constShift, Pi.add_apply]

/-- A function with support contained in a set vanishes outside that set. -/
lemma zero_of_not_mem_support {N : ℕ} (f : X N → ℝ) {x : X N}
    (hx : x ∉ Function.support f) : f x = 0 := by
  by_contra h
  exact hx ((Function.mem_support).mpr h)

/-- The whole-space interaction energy is invariant under the common shift. -/
lemma intWs_constShift {N : ℕ} (c : ℝ³) (v : ℝ³ → ℝ) {f : X N → ℝ}
    (hf : ContDiff ℝ 1 f) :
    (∫ x : X N, (f (x + constShift N c)) ^ 2 * intPairSum N v (x + constShift N c)) =
      (∫ x : X N, (f x) ^ 2 * intPairSum N v x) := by
  let T : X N → X N := fun x => x + constShift N c
  let g : X N → ℝ := fun x => (f x) ^ 2 * intPairSum N v x
  have hmp : MeasurePreserving T volume volume := by
    dsimp [T]
    simpa [add_comm] using (measurePreserving_add_left volume (constShift N c))
  have hme : MeasurableEmbedding T := by
    dsimp [T]
    simpa using ((Homeomorph.addRight (constShift N c)).measurableEmbedding)
  calc
    (∫ x : X N, (f (x + constShift N c)) ^ 2 * intPairSum N v (x + constShift N c))
        = ∫ x : X N, g (T x) := by rfl
    _ = ∫ y : X N, g y := (MeasurePreserving.integral_comp hmp hme g)
    _ = (∫ x : X N, (f x) ^ 2 * intPairSum N v x) := by rfl

/-- For `f` supported in the (open) box, the whole-space interaction energy is
the box one. -/
lemma intWs_eq_intNeu_box {N : ℕ} {L : ℝ} (v : ℝ³ → ℝ) {f : X N → ℝ}
    (hf : ContDiff ℝ 1 f) (hsup : Function.support f ⊆ box N L) :
    (∫ x : X N, (f x) ^ 2 * intPairSum N v x) =
      ∫ x in box N L, (f x) ^ 2 * intPairSum N v x := by
  have hzero : ∀ x : X N, x ∉ box N L → (f x) ^ 2 * intPairSum N v x = 0 := by
    intro x hx
    have hfx : f x = 0 := zero_of_not_mem_support f (by
      intro hs
      exact hx (hsup hs))
    simp [hfx]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (s := box N L)
    (f := fun x : X N => (f x) ^ 2 * intPairSum N v x) hzero).symm

/-- Build a `CNeu` state from a smooth nonzero function with positive box
norm. -/
noncomputable def CNeu.ofFun {N : ℕ} {L : ℝ} {f : X N → ℝ} (hf : ContDiff ℝ ∞ f)
    (hne : f ≠ 0) (hpos : 0 < ∫ x in box N L, (f x) ^ 2) : CNeu N L :=
  ⟨f, hf, hne, hpos⟩

/-- For `f` supported in the box, the whole-space kinetic energy equals the box
one (i.e. `kinNeu` of the induced state). -/
lemma kinWs_eq_box {N : ℕ} {L : ℝ} {f : X N → ℝ} (hf : ContDiff ℝ 1 f)
    (hsup : Function.support f ⊆ box N L) :
    (∫ x : X N, ∑ i : Fin N, ∑ k : Fin 3, (fderiv ℝ f x (kcDir N i k)) ^ 2) =
      (∫ x in box N L, ∑ i : Fin N, ∑ k : Fin 3,
        (fderiv ℝ f x (kcDir N i k)) ^ 2) := by
  let K : X N → ℝ := fun x => ∑ i : Fin N, ∑ k : Fin 3, (fderiv ℝ f x (kcDir N i k)) ^ 2
  have hKzero : ∀ x : X N, x ∉ box N L → K x = 0 := by
    intro x hx
    have hfzero_nhds : f =ᶠ[𝓝 x] (fun _ : X N => 0) := by
      have hopen : (box N L)ᶜ ∈ 𝓝 x := (box_closed L).isOpen_compl.mem_nhds hx
      filter_upwards [hopen] with y hy
      have hyns : y ∉ Function.support f := by
        intro hs
        exact hy (hsup hs)
      exact zero_of_not_mem_support f hyns
    have hfd : fderiv ℝ f x = 0 := by
      have hd0 : HasFDerivAt f (0 : X N →L[ℝ] ℝ) x := by
        exact (hasFDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq hfzero_nhds
      exact hd0.fderiv
    dsimp [K]
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro k hk
    rw [hfd]
    simp
  calc
    (∫ x : X N, ∑ i : Fin N, ∑ k : Fin 3, (fderiv ℝ f x (kcDir N i k)) ^ 2)
        = ∫ x : X N, K x := by rfl
    _ = ∫ x in box N L, K x := by
          exact (setIntegral_eq_integral_of_forall_compl_eq_zero (s := box N L) (f := K) hKzero).symm
    _ = ∫ x in box N L, ∑ i : Fin N, ∑ k : Fin 3,
        (fderiv ℝ f x (kcDir N i k)) ^ 2 := by rfl

/-- **The Neumann energy is a lower bound for the quotient of any admissible
state** (the per-cell bracket ingredient): `eNeu` is the infimum of the
quotients over `CNeu`. -/
lemma eNeu_le_quot_ofFun {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hv : 0 ≤ v)
    {f : X N → ℝ} (hf : ContDiff ℝ ∞ f) (hne : f ≠ 0)
    (hpos : 0 < ∫ x in box N L, (f x) ^ 2) :
    eNeu N L v ≤
      (kinNeu N L (CNeu.ofFun hf hne hpos) + intNeu N L v (CNeu.ofFun hf hne hpos)) /
        (∫ x in box N L, (f x) ^ 2) := by
  have hbdd : BddBelow (Set.range (fun Φ : CNeu N L =>
      (kinNeu N L Φ + intNeu N L v Φ) / (∫ x in box N L, ((Φ : X N → ℝ) x) ^ 2))) := by
    exact eNeu_quot_bddBelow (N := N) (L := L) (v := v) hv
  let Φ₀ : CNeu N L := CNeu.ofFun hf hne hpos
  have hle := ciInf_le hbdd Φ₀
  unfold eNeu
  simpa [Φ₀, CNeu.ofFun] using hle


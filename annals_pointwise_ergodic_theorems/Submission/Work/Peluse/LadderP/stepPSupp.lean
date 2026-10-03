import Mathlib
import Submission.Work.Peluse.LadderP.stepPState

/-!
# The one-step lemma of the power-loss ladder: small support

The iterated differences of a function supported in `symIcc N` are supported in some *translate* of
`symIcc N` (`SuppSmall`), and the box norm is invariant under translation
(`BoxNorm.boxNormPow_shift`), so every box norm of such a difference is at most `1`.  This is what
makes the box average `boxAvgA` an average of numbers in `[0,1]`, which powers the Markov step of
the ladder.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.LadderP

noncomputable section

open Work.Peluse

/-- Membership in the symmetric interval `[-N,N]` is the size condition `|x| ≤ N`. -/
lemma mem_symIcc_iff {N : ℕ} {x : ℤ} : x ∈ symIcc N ↔ x.natAbs ≤ N := by
  rw [symIcc, Finset.mem_Icc, ← abs_le, ← Int.natCast_natAbs]
  exact_mod_cast Iff.rfl

lemma boxNormPow_nonneg' {t : ℕ} {Q : Fin t → Finset ℤ} {S : Finset ℤ} {f : ℤ → ℂ} :
    0 ≤ boxNormPow t Q S f := norm_nonneg _

/-- A function whose support is contained in some translate of `symIcc N`. -/
def SuppSmall (N : ℕ) (g : ℤ → ℂ) : Prop := ∃ s : ℤ, SupportIn (fun x => g (x + s)) N

lemma SuppSmall.of_supportIn {N : ℕ} {g : ℤ → ℂ} (h : SupportIn g N) : SuppSmall N g := by
  refine ⟨0, fun x hx => ?_⟩
  simpa using h x hx

lemma SuppSmall.finSuppZ {N : ℕ} {g : ℤ → ℂ} (h : SuppSmall N g) : FinSuppZ g := by
  obtain ⟨s, hs⟩ := h
  refine ⟨N + s.natAbs, fun x hx => ?_⟩
  have h2 : g ((x - s) + s) = 0 := hs (x - s) (by
    have h3 : (x - s).natAbs ≤ x.natAbs + s.natAbs := by
      have h4 := Int.natAbs_add_le x (-s)
      rw [Int.natAbs_neg] at h4
      simpa [sub_eq_add_neg] using h4
    omega)
  simpa [sub_add_cancel] using h2

lemma SuppSmall.iterDeltaStep {N : ℕ} {F : ℤ → ℂ} (h : SuppSmall N F) (a b : ℤ) :
    SuppSmall N (Ulower.iterDeltaStep (a, b) F) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s - a, fun x hx => ?_⟩
  have h1 : F (x + (s - a) + a) = 0 := by
    rw [show x + (s - a) + a = x + s by ring]
    exact hs x hx
  simp only [Ulower.iterDeltaStep]
  rw [h1, zero_mul]

lemma SuppSmall.iterDelta {N : ℕ} : ∀ (k : ℕ) (sh : Fin k → ℤ × ℤ) {F : ℤ → ℂ},
    SuppSmall N F → SuppSmall N (Ulower.iterDelta k sh F) := by
  intro k
  induction k with
  | zero => intro sh F h; simpa [Ulower.iterDelta_zero] using h
  | succ k ih =>
      intro sh F h
      rw [Ulower.iterDelta_succ]
      have hthis := ih (fun i => sh i.succ) (h.iterDeltaStep (sh 0).1 (sh 0).2)
      rwa [Concat.iterDeltaStep_iterDelta_comm] at hthis

/-- A box-norm power of a `1`-bounded function with small support is at most `1`. -/
lemma boxNormPow_le_one_of_suppSmall {t : ℕ} {Q : Fin t → Finset ℤ} {N : ℕ} {g : ℤ → ℂ}
    (hbd : ∀ x : ℤ, ‖g x‖ ≤ 1) (h : SuppSmall N g) :
    boxNormPow t Q (symIcc N) g ≤ 1 := by
  obtain ⟨s, hs⟩ := h
  have hfin : FinSuppZ g := ⟨N + s.natAbs, fun x hx => by
    have h3 : (x - s).natAbs ≤ x.natAbs + s.natAbs := by
      have h4 := Int.natAbs_add_le x (-s)
      rw [Int.natAbs_neg] at h4
      simpa [sub_eq_add_neg] using h4
    have h2 : g ((x - s) + s) = 0 := hs (x - s) (by omega)
    simpa [sub_add_cancel] using h2⟩
  rw [← BoxNorm.boxNormPow_shift t Q (symIcc N) g s hfin]
  exact BoxNorm.boxNormPow_le_one (fun x => hbd (x + s)) (fun x hx => hs x (by
    simp only [mem_symIcc_iff, not_le] at hx
    exact hx))

lemma boxNormPow_le_boxNorm_of_suppSmall {t : ℕ} {Q : Fin t → Finset ℤ} {N : ℕ} {g : ℤ → ℂ}
    (hbd : ∀ x : ℤ, ‖g x‖ ≤ 1) (h : SuppSmall N g) :
    boxNormPow t Q (symIcc N) g ≤ boxNorm t Q (symIcc N) g := by
  rw [boxNorm]
  exact Real.self_le_rpow_of_le_one boxNormPow_nonneg'
    (boxNormPow_le_one_of_suppSmall hbd h) (by
      rw [div_le_one (by positivity)]
      exact one_le_pow₀ (by norm_num))

/-- A box norm of a `1`-bounded function with small support is at most `1`. -/
lemma boxNorm_le_one_of_suppSmall {t : ℕ} {Q : Fin t → Finset ℤ} {N : ℕ} {g : ℤ → ℂ}
    (hbd : ∀ x : ℤ, ‖g x‖ ≤ 1) (h : SuppSmall N g) :
    boxNorm t Q (symIcc N) g ≤ 1 := by
  rw [boxNorm]
  exact Real.rpow_le_one boxNormPow_nonneg' (boxNormPow_le_one_of_suppSmall hbd h)
    (by positivity)

lemma Gwt_nonneg (j n M₁ : ℕ) (c : ℤ) (L D : ℕ) (h₁ h₁' : Fin j → Fin M₁) :
    0 ≤ Gwt j n M₁ c L D h₁ h₁' :=
  mul_nonneg (Finset.prod_nonneg (fun i _ => by positivity))
    (Finset.prod_nonneg (fun i _ => by positivity))

end

end Work.Peluse.LadderP

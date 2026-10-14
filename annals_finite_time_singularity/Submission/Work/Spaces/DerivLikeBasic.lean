import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Submission.Work.Spaces.scoef_sum_shift

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.Spaces

variable {X : Type*} {s : Set X} {P : (X → ℝ) → Prop} {D : (X → ℝ) → (X → ℝ)}

theorem eqOn_refl (f : X → ℝ) : Set.EqOn f f s := fun _ _ => rfl

theorem eqOn_add {f g f' g' : X → ℝ} (hf : Set.EqOn f f' s) (hg : Set.EqOn g g' s) :
    Set.EqOn (fun p => f p + g p) (fun p => f' p + g' p) s := fun p hp => by
  show f p + g p = f' p + g' p
  rw [hf hp, hg hp]

theorem eqOn_const_mul (c : ℝ) {f g : X → ℝ} (h : Set.EqOn f g s) :
    Set.EqOn (fun p => c * f p) (fun p => c * g p) s := fun p hp => by
  show c * f p = c * g p
  rw [h hp]

/-- `D^[k]` preserves the class `P`. -/
theorem DerivLike.preserve_iterate (hD : DerivLike s P D) (k : ℕ) {A : X → ℝ} (hA : P A) :
    P (D^[k] A) := by
  induction k with
  | zero => simpa using hA
  | succ n ih => rw [Function.iterate_succ_apply']; exact hD.preserve _ ih

/-- Iterates respect `EqOn`. -/
theorem DerivLike.iterate_congr (hD : DerivLike s P D) (k : ℕ) {A B : X → ℝ}
    (h : Set.EqOn A B s) : Set.EqOn (D^[k] A) (D^[k] B) s := by
  induction k with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact hD.congr _ _ ih

/-- Iterates are additive on `P`-functions. -/
theorem DerivLike.iterate_add (hD : DerivLike s P D) (k : ℕ) {A B : X → ℝ}
    (hA : P A) (hB : P B) :
    Set.EqOn (D^[k] (A + B)) (D^[k] A + D^[k] B) s := by
  induction k with
  | zero => intro p hp; simp
  | succ n ih =>
    have h1 : Set.EqOn (D^[n + 1] (A + B)) (D (D^[n] A + D^[n] B)) s := by
      have hc := hD.congr (D^[n] (A + B)) (D^[n] A + D^[n] B) ih
      simpa only [Function.iterate_succ_apply'] using hc
    have h2 := hD.add (D^[n] A) (D^[n] B)
      (hD.preserve_iterate n hA) (hD.preserve_iterate n hB)
    refine h1.trans (h2.trans ?_)
    intro p hp
    show D (D^[n] A) p + D (D^[n] B) p = (D^[n + 1] A + D^[n + 1] B) p
    simp only [Pi.add_apply, Function.iterate_succ_apply']

/-- Iterates commute with multiplication by a constant on `P`-functions. -/
theorem DerivLike.iterate_smul (hD : DerivLike s P D) (k : ℕ) (c : ℝ) {A : X → ℝ}
    (hA : P A) :
    Set.EqOn (D^[k] (fun p => c * A p)) (fun p => c * D^[k] A p) s := by
  induction k with
  | zero => intro p hp; simp
  | succ n ih =>
    have h1 : Set.EqOn (D^[n + 1] (fun p => c * A p)) (D (fun p => c * D^[n] A p)) s := by
      have hc := hD.congr (D^[n] (fun p => c * A p)) (fun p => c * D^[n] A p) ih
      simpa only [Function.iterate_succ_apply'] using hc
    have h2 := hD.smul c (D^[n] A) (hD.preserve_iterate n hA)
    refine h1.trans (h2.trans ?_)
    intro p hp
    show c * D (D^[n] A) p = c * D^[n + 1] A p
    simp only [Function.iterate_succ_apply']

/-- `P` is closed under `Finset.range` sums. -/
theorem FunClass.sum_range (hP : FunClass P) (N : ℕ) {A : ℕ → X → ℝ}
    (hA : ∀ i ≤ N, P (A i)) : P (fun p => ∑ i ∈ Finset.range (N + 1), A i p) := by
  induction N with
  | zero =>
    have h0 : (fun p => ∑ i ∈ Finset.range (0 + 1), A i p) = A 0 := by
      funext p; simp
    rw [h0]; exact hA 0 le_rfl
  | succ N ih =>
    have hsum : (fun p => ∑ i ∈ Finset.range (N + 1 + 1), A i p)
        = (fun p => ∑ i ∈ Finset.range (N + 1), A i p) + A (N + 1) := by
      funext p; rw [Finset.sum_range_succ]; rfl
    rw [hsum]
    exact hP.add _ _ (ih (fun i hi => hA i (le_trans hi (Nat.le_succ N))))
      (hA (N + 1) le_rfl)

/-- Iterates are linear over `Finset.range` sums of `P`-functions. -/
theorem DerivLike.iterate_sum_range (hD : DerivLike s P D) (hP : FunClass P) (k N : ℕ)
    {A : ℕ → X → ℝ} (hA : ∀ i ≤ N, P (A i)) :
    Set.EqOn (D^[k] (fun p => ∑ i ∈ Finset.range (N + 1), A i p))
      (fun p => ∑ i ∈ Finset.range (N + 1), D^[k] (A i) p) s := by
  induction N with
  | zero =>
    have h0 : (fun p => ∑ i ∈ Finset.range (0 + 1), A i p) = A 0 := by funext p; simp
    have h1 : (fun p => ∑ i ∈ Finset.range (0 + 1), D^[k] (A i) p) = D^[k] (A 0) := by
      funext p; simp
    rw [h0, h1]
    exact eqOn_refl _
  | succ N ih =>
    have hsum : (fun p => ∑ i ∈ Finset.range (N + 1 + 1), A i p)
        = (fun p => ∑ i ∈ Finset.range (N + 1), A i p) + A (N + 1) := by
      funext p; rw [Finset.sum_range_succ]; rfl
    have hsum' : (fun p => ∑ i ∈ Finset.range (N + 1 + 1), D^[k] (A i) p)
        = (fun p => ∑ i ∈ Finset.range (N + 1), D^[k] (A i) p) + D^[k] (A (N + 1)) := by
      funext p; rw [Finset.sum_range_succ]; rfl
    rw [hsum, hsum']
    have hPT : P (fun p => ∑ i ∈ Finset.range (N + 1), A i p) :=
      FunClass.sum_range hP N (fun i hi => hA i (le_trans hi (Nat.le_succ N)))
    have hIH := ih (fun i hi => hA i (le_trans hi (Nat.le_succ N)))
    refine (hD.iterate_add k hPT (hA (N + 1) le_rfl)).trans
      ((eqOn_add hIH (eqOn_refl _)).trans ?_)
    intro p hp
    rfl

/-- Level-one linearity of `D` over `Finset.range` sums of `P`-functions. -/
theorem DerivLike.sum_range (hD : DerivLike s P D) (hP : FunClass P) (N : ℕ)
    {A : ℕ → X → ℝ} (hA : ∀ i ≤ N, P (A i)) :
    Set.EqOn (D (fun p => ∑ i ∈ Finset.range (N + 1), A i p))
      (fun p => ∑ i ∈ Finset.range (N + 1), D (A i) p) s := by
  have h := hD.iterate_sum_range hP 1 N hA
  simpa only [Function.iterate_one] using h

/-- The single-operator iterated Leibniz rule. -/
theorem DerivLike.iterate_mul (hD : DerivLike s P D) (hP : FunClass P) (k : ℕ) {F G : X → ℝ}
    (hF : P F) (hG : P G) :
    Set.EqOn (D^[k] (F * G))
      (fun p => ∑ a ∈ Finset.range (k + 1),
        (k.choose a : ℝ) * (D^[a] F p * D^[k - a] G p)) s := by
  induction k with
  | zero => intro p hp; simp
  | succ k ih =>
    have hA : ∀ a ≤ k, P (fun p => (k.choose a : ℝ) * (D^[a] F p * D^[k - a] G p)) :=
      fun a _ => hP.smul (k.choose a) (D^[a] F * D^[k - a] G)
        (hP.mul (D^[a] F) (D^[k - a] G) (hD.preserve_iterate a hF) (hD.preserve_iterate (k - a) hG))
    have step1 : Set.EqOn (D^[k + 1] (F * G))
        (D (fun p => ∑ a ∈ Finset.range (k + 1),
          (k.choose a : ℝ) * (D^[a] F p * D^[k - a] G p))) s := by
      have hc := hD.congr (D^[k] (F * G))
        (fun p => ∑ a ∈ Finset.range (k + 1),
          (k.choose a : ℝ) * (D^[a] F p * D^[k - a] G p)) ih
      simpa only [Function.iterate_succ_apply'] using hc
    have step2 := hD.sum_range hP k hA
    have step3 : ∀ a ≤ k, Set.EqOn
        (D (fun p => (k.choose a : ℝ) * (D^[a] F p * D^[k - a] G p)))
        (fun p => (k.choose a : ℝ) *
          (D^[a + 1] F p * D^[k - a] G p + D^[a] F p * D^[k - a + 1] G p)) s := by
      intro a ha
      have hPA : P (D^[a] F * D^[k - a] G) :=
        hP.mul (D^[a] F) (D^[k - a] G) (hD.preserve_iterate a hF) (hD.preserve_iterate (k - a) hG)
      have hsm := hD.smul (k.choose a) (D^[a] F * D^[k - a] G) hPA
      have hmul := hD.mul (D^[a] F) (D^[k - a] G)
        (hD.preserve_iterate a hF) (hD.preserve_iterate (k - a) hG)
      refine hsm.trans ((eqOn_const_mul _ hmul).trans ?_)
      intro p hp
      show (k.choose a : ℝ) *
          (D (D^[a] F) p * D^[k - a] G p + D^[a] F p * D (D^[k - a] G) p)
        = (k.choose a : ℝ) *
          (D^[a + 1] F p * D^[k - a] G p + D^[a] F p * D^[k - a + 1] G p)
      simp only [Function.iterate_succ_apply']
    have step4 : Set.EqOn
        (fun p => ∑ a ∈ Finset.range (k + 1),
          D (fun p => (k.choose a : ℝ) * (D^[a] F p * D^[k - a] G p)) p)
        (fun p => ∑ a ∈ Finset.range (k + 1),
          (k.choose a : ℝ) *
            (D^[a + 1] F p * D^[k - a] G p + D^[a] F p * D^[k - a + 1] G p)) s :=
      eqOn_sum _ (fun a ha => step3 a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)))
    have step5 : Set.EqOn
        (fun p => ∑ a ∈ Finset.range (k + 1),
          (k.choose a : ℝ) *
            (D^[a + 1] F p * D^[k - a] G p + D^[a] F p * D^[k - a + 1] G p))
        (fun p => ∑ b ∈ Finset.range (k + 1 + 1),
          ((k + 1).choose b : ℝ) * (D^[b] F p * D^[k + 1 - b] G p)) s := by
      intro p hp
      exact leibniz_step k (fun i => D^[i] F p) (fun i => D^[i] G p)
    exact step1.trans (step2.trans (step4.trans step5))

end Work.Spaces

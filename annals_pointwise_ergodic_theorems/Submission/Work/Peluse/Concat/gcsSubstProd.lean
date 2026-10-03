import Mathlib
import Submission.Work.Peluse.Concat.GowersDefs

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Work.Peluse.Concat

noncomputable section

variable {X : Type} [Fintype X]

/-! ## Iterated `star` -/

lemma starIter_sum {ι : Type*} (s : Finset ι) (k : ℕ) (f : ι → ℂ) :
    (star^[k]) (∑ i ∈ s, f i) = ∑ i ∈ s, (star^[k]) (f i) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, star_sum]
      exact Finset.sum_congr rfl fun i _ => (Function.iterate_succ_apply' star k (f i)).symm

lemma starIter_prod {ι : Type*} (s : Finset ι) (k : ℕ) (f : ι → ℂ) :
    (star^[k]) (∏ i ∈ s, f i) = ∏ i ∈ s, (star^[k]) (f i) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, star_prod]
      exact Finset.prod_congr rfl fun i _ => (Function.iterate_succ_apply' star k (f i)).symm

lemma norm_starIter (k : ℕ) (z : ℂ) : ‖(star^[k]) z‖ = ‖z‖ := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', norm_star, ih]

lemma star_iterate_comm (a b : ℕ) (z : ℂ) :
    (star^[a]) ((star^[b]) z) = (star^[b]) ((star^[a]) z) := by
  rw [← Function.iterate_add_apply star a b z, ← Function.iterate_add_apply star b a z,
    Nat.add_comm a b]

/-! ## The iterated `star` as a ring endomorphism, and `cubeSum` -/

lemma starPowRingHom_apply (k : ℕ) (z : ℂ) : ((starRingEnd ℂ) ^ k) z = (star^[k]) z := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', pow_succ']
      simp only [RingHom.mul_def, RingHom.comp_apply]
      rw [ih, starRingEnd_apply]

lemma starPow_comm (a b : ℕ) (z : ℂ) :
    ((starRingEnd ℂ) ^ a) (((starRingEnd ℂ) ^ b) z)
      = ((starRingEnd ℂ) ^ b) (((starRingEnd ℂ) ^ a) z) := by
  rw [starPowRingHom_apply, starPowRingHom_apply, starPowRingHom_apply, starPowRingHom_apply]
  exact star_iterate_comm a b z

lemma cubeSum_starPow_comp {t : ℕ} (k : ℕ) (h : (Fin t → X) → ℂ) :
    cubeSum (fun (_ : Fin t → Bool) => fun x => ((starRingEnd ℂ)^k) (h x))
      = ((starRingEnd ℂ)^k) (cubeSum (fun (_ : Fin t → Bool) => h)) := by
  simp only [cubeSum, cubeProd, starPowRingHom_apply, map_sum, map_prod]
  exact Finset.sum_congr rfl fun x0 _ => Finset.sum_congr rfl fun x1 _ =>
    Finset.prod_congr rfl fun ω _ => starPow_comm _ _ _

lemma NPow_starIter_comp {t : ℕ} (k : ℕ) (h : (Fin t → X) → ℂ) :
    NPow t (fun x => (star^[k]) (h x)) = NPow t h := by
  unfold NPow
  have h1 : cubeSum (fun (_ : Fin t → Bool) => fun x => (star^[k]) (h x))
      = (star^[k]) (cubeSum (fun (_ : Fin t → Bool) => h)) := by
    simpa only [starPowRingHom_apply] using cubeSum_starPow_comp (X := X) k h
  rw [h1]
  exact norm_starIter k _

/-! ## `substG` and `substF` -/

lemma weight_allTrue_prod (s : ℕ) : Work.Peluse.weight (fun _ : Fin s => true) = s := by
  simp [Work.Peluse.weight]

lemma substG_allTrue_prod {s : ℕ} (f : (Fin s → X) → ℂ) (g : Fin s → (Fin s → X) → ℂ)
    (x : Fin s → X) : substG f g (fun _ : Fin s => true) x = f x := by
  simp only [substG]
  exact dif_pos (fun _ => trivial)

lemma norm_substF_le_one {s : ℕ} (f : (Fin s → X) → ℂ)
    (g : Fin s → (Fin s → X) → ℂ) (hg : ∀ (i : Fin s) (x : Fin s → X), ‖g i x‖ ≤ 1)
    {ω : Fin s → Bool} (hω : ¬ ∀ i, ω i) (x : Fin s → X) :
    ‖substF f g ω x‖ ≤ 1 := by
  show ‖(star^[Work.Peluse.weight ω]) (substG f g ω x)‖ ≤ 1
  rw [norm_starIter]
  simp only [substG]
  rw [dif_neg hω]
  by_cases h2 : ∃ i, ω i = false ∧ ∀ j, j ≠ i → ω j
  · rw [dif_pos h2]; exact hg _ _
  · rw [dif_neg h2]; simp

lemma NPow_substF_allTrue {s : ℕ} (f : (Fin s → X) → ℂ)
    (g : Fin s → (Fin s → X) → ℂ) :
    NPow s (substF f g (fun _ : Fin s => true)) = NPow s f := by
  have h : substF f g (fun _ : Fin s => true) = fun x => (star^[s]) (f x) := by
    funext x
    show (star^[Work.Peluse.weight (fun _ : Fin s => true)])
      (substG f g (fun _ : Fin s => true) x) = _
    rw [weight_allTrue_prod, substG_allTrue_prod]
  rw [h, NPow_starIter_comp]

/-! ## The trivial bound for `NPow` -/

lemma NPow_le_card_pow (t : ℕ) (h : (Fin t → X) → ℂ) (h1 : ∀ x, ‖h x‖ ≤ 1) :
    NPow t h ≤ (Fintype.card X : ℝ) ^ (2 * t) := by
  unfold NPow cubeSum cubeProd
  calc ‖∑ x0 : Fin t → X, ∑ x1 : Fin t → X, ∏ ω : Fin t → Bool,
            (star^[Work.Peluse.weight ω]) (h (mix ω x0 x1))‖
      ≤ ∑ x0 : Fin t → X, ‖∑ x1 : Fin t → X, ∏ ω : Fin t → Bool,
            (star^[Work.Peluse.weight ω]) (h (mix ω x0 x1))‖ := norm_sum_le _ _
    _ ≤ ∑ x0 : Fin t → X, ∑ x1 : Fin t → X, ‖∏ ω : Fin t → Bool,
            (star^[Work.Peluse.weight ω]) (h (mix ω x0 x1))‖ :=
        Finset.sum_le_sum fun x0 _ => norm_sum_le _ _
    _ ≤ ∑ _x0 : Fin t → X, ∑ _x1 : Fin t → X, (1 : ℝ) := by
        refine Finset.sum_le_sum fun x0 _ => Finset.sum_le_sum fun x1 _ => ?_
        rw [norm_prod]
        refine Finset.prod_le_one₀ (fun ω _ => norm_nonneg _) fun ω _ => ?_
        rw [norm_starIter]
        exact h1 _
    _ = (Fintype.card X : ℝ) ^ (2 * t) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        rw [Fintype.card_fun (α := Fin t) (β := X), Fintype.card_fin, Nat.cast_pow,
          ← pow_add]
        congr 1
        omega

/-! ## The main product estimate -/

theorem gcsSubstProd :
    ∀ (X : Type) [Fintype X] (s : ℕ), 1 ≤ s →
      ∀ (f : (Fin s → X) → ℂ) (g : Fin s → (Fin s → X) → ℂ),
      (∀ (i : Fin s) (x : Fin s → X), ‖g i x‖ ≤ 1) →
      (∀ (i : Fin s) (x x' : Fin s → X), (∀ j, j ≠ i → x j = x' j) → g i x = g i x') →
      (∏ ω : Fin s → Bool, Work.Peluse.Concat.NPow s (Work.Peluse.Concat.substF f g ω))
        ≤ Work.Peluse.Concat.NPow s f
            * (((Fintype.card X : ℝ)) ^ (2*s)) ^ (2^s - 1) := by
  intro X _ s hs f g hg _
  have hcard : (Finset.univ.erase (fun _ : Fin s => true)).card = 2 ^ s - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fun (α := Fin s) (β := Bool), Fintype.card_bool, Fintype.card_fin]
  calc ∏ ω : Fin s → Bool, NPow s (substF f g ω)
      = NPow s f * ∏ ω ∈ Finset.univ.erase (fun _ : Fin s => true), NPow s (substF f g ω) := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (fun _ : Fin s => true)),
          NPow_substF_allTrue]
    _ ≤ NPow s f * ∏ _ω ∈ Finset.univ.erase (fun _ : Fin s => true),
          ((Fintype.card X : ℝ) ^ (2 * s)) := by
        refine mul_le_mul_of_nonneg_left ?_ (NPow_nonneg s f)
        refine Finset.prod_le_prod₀ (fun ω _ => NPow_nonneg s _) fun ω hω => ?_
        have hne : ¬ ∀ i, ω i := by
          intro hall
          exact (Finset.mem_erase.mp hω).1 (funext fun i => by simpa using hall i)
        exact NPow_le_card_pow s _ (fun x => norm_substF_le_one f g hg hne x)
    _ = NPow s f * (((Fintype.card X : ℝ) ^ (2 * s)) ^ (2 ^ s - 1)) := by
        rw [Finset.prod_const, hcard]

end

end Work.Peluse.Concat

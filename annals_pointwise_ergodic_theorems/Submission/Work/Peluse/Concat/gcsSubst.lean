/-
The *substitution* step of the Gowers--Cauchy--Schwarz inequality for the flat cube: Peluse's
Lemma 2.2 in the "one function per omitted coordinate" form (her Lemma 5.1 / Lemma 5.6 input).

Three facts are proved:

* `Work.Peluse.Concat.substF f g ω` is bounded by `1` whenever `f`, `g i` are (clause 1);
* the flat cube sum of the substituted family *collapses*:
  `cubeSum (substF f g) = |X|^s · ∑_x f x ∏_i g i x` whenever `g i` does not depend on the `i`-th
  coordinate (clause 2);
* the product over all sign patterns of the box-norm powers of the substituted family is dominated
  by the box-norm power of `f` times the trivial bound `|X|^{2s}` for each of the `2^s - 1`
  remaining patterns (clause 3).

The three together are exactly the "substitution" reduction of Gowers--Cauchy--Schwarz: clause 2
turns the multilinear average into the Gowers inner product of the `substF f g ω`, whose modulus
is bounded by `∏_ω NPow s (substF f g ω)^{1/2^s}` — and clause 3 bounds that product by
`NPow s f · (|X|^{2s})^{2^s-1}`, which is the bound needed in `gowersCS`.
-/
import Mathlib
import Submission.Work.Peluse.Concat.GowersDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Peluse.Concat

noncomputable section

variable {X : Type} [Fintype X]

/-! ## Iterates of `star` -/

/-- The complex conjugation is an isometry, hence so is each of its iterates. -/
lemma norm_star_iterate (k : ℕ) (z : ℂ) : ‖(star^[k]) z‖ = ‖z‖ := by
  induction k with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', norm_star, ih]

/-- Each iterate of `star` is additive. -/
lemma star_iterate_add (k : ℕ) (z w : ℂ) :
    (star^[k]) (z + w) = (star^[k]) z + (star^[k]) w := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, star_add, Function.iterate_succ_apply',
      Function.iterate_succ_apply']

/-- Each iterate of `star` commutes with finite sums. -/
lemma star_iterate_sum {ι : Type*} (k : ℕ) (s : Finset ι) (f : ι → ℂ) :
    (star^[k]) (∑ i ∈ s, f i) = ∑ i ∈ s, (star^[k]) (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, star_iterate_add, ih, Finset.sum_insert ha]

/-- Each iterate of `star` commutes with finite products. -/
lemma star_iterate_prod {ι : Type*} (k : ℕ) (s : Finset ι) (f : ι → ℂ) :
    (star^[k]) (∏ i ∈ s, f i) = ∏ i ∈ s, (star^[k]) (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, star_iterate_mul, ih, Finset.prod_insert ha]

/-- Two equal iterates of `star` cancel. -/
lemma star_iterate_iterate (k : ℕ) (z : ℂ) : (star^[k]) ((star^[k]) z) = z := by
  rw [← Function.iterate_add_apply]
  have h2 : star^[2] = (id : ℂ → ℂ) := by funext w; simp [Function.iterate_succ_apply]
  rw [show k + k = 2 * k by ring, Function.iterate_mul, h2, Function.iterate_id]
  rfl

/-- Conjugating a single function by `star^[k]` conjugates its flat cube sum. -/
lemma cubeSum_star_iterate (t k : ℕ) (h : (Fin t → X) → ℂ) :
    cubeSum (fun (_ : Fin t → Bool) => fun y => (star^[k]) (h y))
      = (star^[k]) (cubeSum (fun (_ : Fin t → Bool) => h)) := by
  unfold cubeSum cubeProd
  rw [star_iterate_sum]
  refine Finset.sum_congr rfl (fun x0 _ => ?_)
  rw [star_iterate_sum]
  refine Finset.sum_congr rfl (fun x1 _ => ?_)
  rw [star_iterate_prod]
  refine Finset.prod_congr rfl (fun ω _ => ?_)
  simp only
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]
  exact congrArg (fun m => (star^[m]) (h (mix ω x0 x1))) (Nat.add_comm _ _)

/-- The box-norm power is invariant under conjugating the function by `star^[k]`. -/
lemma NPow_star_iterate (t k : ℕ) (h : (Fin t → X) → ℂ) :
    NPow t (fun y => (star^[k]) (h y)) = NPow t h := by
  unfold NPow
  rw [cubeSum_star_iterate, norm_star_iterate]

/-! ## Elementary bounds for the cube sum and the box-norm power -/

/-- The norm of a cube product is the product of the norms. -/
lemma norm_cubeProd (t : ℕ) (F : (Fin t → Bool) → (Fin t → X) → ℂ) (x0 x1 : Fin t → X) :
    ‖cubeProd F x0 x1‖ = ∏ ω : Fin t → Bool, ‖F ω (mix ω x0 x1)‖ := by
  unfold cubeProd
  rw [norm_prod]
  exact Finset.prod_congr rfl (fun ω _ => norm_star_iterate _ _)

/-- The trivial bound for the box-norm power: a function bounded by `1` has `NPow` at most the
number of corners `|X|^{2t}`. -/
lemma NPow_le_card (t : ℕ) (h : (Fin t → X) → ℂ) (hh : ∀ y, ‖h y‖ ≤ 1) :
    NPow t h ≤ ((Fintype.card X : ℝ)) ^ (2 * t) := by
  unfold NPow
  have hcube : ‖cubeSum (fun (_ : Fin t → Bool) => h)‖
      ≤ ∑ _x0 : Fin t → X, ∑ _x1 : Fin t → X, (1 : ℝ) := by
    rw [cubeSum]
    calc ‖∑ x0 : Fin t → X, ∑ x1 : Fin t → X, cubeProd (fun _ : Fin t → Bool => h) x0 x1‖
        ≤ ∑ x0 : Fin t → X,
            ‖∑ x1 : Fin t → X, cubeProd (fun _ : Fin t → Bool => h) x0 x1‖ :=
          norm_sum_le _ _
      _ ≤ ∑ x0 : Fin t → X, ∑ x1 : Fin t → X,
            ‖cubeProd (fun _ : Fin t → Bool => h) x0 x1‖ := by
          gcongr with x0
          exact norm_sum_le _ _
      _ ≤ ∑ _x0 : Fin t → X, ∑ _x1 : Fin t → X, (1 : ℝ) := by
          gcongr with x0 x1
          rw [norm_cubeProd]
          exact Finset.prod_le_one₀ (fun ω _ => norm_nonneg _) (fun ω _ => hh _)
  calc ‖cubeSum (fun (_ : Fin t → Bool) => h)‖
      ≤ ∑ _x0 : Fin t → X, ∑ _x1 : Fin t → X, (1 : ℝ) := hcube
    _ = (Fintype.card (Fin t → X) : ℝ) * (Fintype.card (Fin t → X) : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ = ((Fintype.card X : ℝ)) ^ (2 * t) := by
        have hcard : (Fintype.card (Fin t → X) : ℝ) = (Fintype.card X : ℝ) ^ t := by
          rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
        rw [hcard, ← pow_add, two_mul]

/-! ## The two distinguished sign patterns -/

/-- The sign pattern with every coordinate `true`. -/
def allTrue (s : ℕ) : Fin s → Bool := fun _ => true

/-- The sign pattern which is `false` at `i` and `true` everywhere else. -/
def onlyFalse {s : ℕ} (i : Fin s) : Fin s → Bool := fun j => if j = i then false else true

@[simp] lemma allTrue_apply (s : ℕ) (i : Fin s) : allTrue s i = true := rfl

@[simp] lemma onlyFalse_self {s : ℕ} (i : Fin s) : onlyFalse i i = false := by
  simp [onlyFalse]

lemma onlyFalse_apply_ne {s : ℕ} {i j : Fin s} (h : ¬ (j = i)) : onlyFalse i j = true := by
  simp [onlyFalse, h]

lemma eq_allTrue_iff {s : ℕ} (ω : Fin s → Bool) : ω = allTrue s ↔ ∀ i, ω i := by
  constructor
  · intro h i; rw [h]; rfl
  · intro h; funext i; exact h i

lemma onlyFalse_injective {s : ℕ} : Function.Injective (@onlyFalse s) := by
  intro i j h
  by_contra hne
  have h1 : onlyFalse j i = true := onlyFalse_apply_ne (s := s) (i := j) (j := i) hne
  have h2 : onlyFalse j i = false := by rw [← h]; exact onlyFalse_self i
  rw [h1] at h2
  exact Bool.noConfusion h2

lemma allTrue_not_mem_image {s : ℕ} :
    allTrue s ∉ Finset.univ.image (fun i : Fin s => onlyFalse i) := by
  intro h
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
  have h2 : onlyFalse i i = allTrue s i := congrFun hi i
  rw [onlyFalse_self, allTrue_apply] at h2
  exact Bool.noConfusion h2

/-- A sign pattern which is `false` at a unique coordinate is one of the `onlyFalse`. -/
lemma eq_onlyFalse_of_unique_false {s : ℕ} {ω : Fin s → Bool} {i : Fin s}
    (hi : ω i = false) (h : ∀ j, j ≠ i → ω j) : ω = onlyFalse i := by
  funext j
  by_cases hj : j = i
  · subst hj; rw [hi, onlyFalse_self]
  · rw [h j hj, onlyFalse_apply_ne (s := s) (i := i) (j := j) hj]

lemma weight_allTrue (s : ℕ) : Work.Peluse.weight (allTrue s) = s := by
  simp [Work.Peluse.weight, allTrue]

/-! ## Evaluating the substitution family -/

/-- The substituted family at the all-`true` pattern is `f`. -/
lemma substG_allTrue {s : ℕ} (f : (Fin s → X) → ℂ) (g : Fin s → (Fin s → X) → ℂ)
    (x : Fin s → X) : substG f g (allTrue s) x = f x := by
  have h : (∀ i, allTrue s i) := fun i => rfl
  simp only [substG]
  rw [dif_pos h]

/-- The substituted family at the pattern which is `false` only at `i` is `g i`. -/
lemma substG_onlyFalse {s : ℕ} (f : (Fin s → X) → ℂ) (g : Fin s → (Fin s → X) → ℂ)
    (i : Fin s) (x : Fin s → X) : substG f g (onlyFalse i) x = g i x := by
  have h1 : ¬ (∀ j, onlyFalse i j) := by
    intro h; have := h i; rw [onlyFalse_self] at this; exact Bool.noConfusion this
  have h2 : ∃ j, onlyFalse i j = false ∧ ∀ k, k ≠ j → onlyFalse i k :=
    ⟨i, onlyFalse_self i, fun k hk => onlyFalse_apply_ne (s := s) (i := i) (j := k) hk⟩
  simp only [substG]
  rw [dif_neg h1, dif_pos h2]
  have hc := (Classical.choose_spec h2).1
  have hci : Classical.choose h2 = i := by
    by_contra hne
    have hthis : onlyFalse i (Classical.choose h2) = true :=
      onlyFalse_apply_ne (s := s) (i := i) (j := Classical.choose h2) hne
    rw [hthis] at hc
    exact Bool.noConfusion hc
  rw [hci]

/-- **Clause 1.** The substituted family is bounded by `1`. -/
lemma norm_substF_le {s : ℕ} (f : (Fin s → X) → ℂ) (g : Fin s → (Fin s → X) → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ i x, ‖g i x‖ ≤ 1) (ω : Fin s → Bool) (x : Fin s → X) :
    ‖substF f g ω x‖ ≤ 1 := by
  rw [substF, norm_star_iterate]
  unfold substG
  split_ifs with h1 h2
  · exact hf x
  · exact hg _ _
  · simp

/-- **The pointwise product identity.** At every pair of corners, the product over all sign patterns
of the substituted family collapses to `f x1 · ∏_i g i x1`. -/
lemma prod_substG {s : ℕ} (f : (Fin s → X) → ℂ) (g : Fin s → (Fin s → X) → ℂ)
    (hgind : ∀ (i : Fin s) (x x' : Fin s → X), (∀ j, j ≠ i → x j = x' j) → g i x = g i x')
    (x0 x1 : Fin s → X) :
    ∏ ω : Fin s → Bool, substG f g ω (mix ω x0 x1) = f x1 * ∏ i : Fin s, g i x1 := by
  classical
  have ha_all : substG f g (allTrue s) (mix (allTrue s) x0 x1) = f x1 := by
    have h2 : mix (allTrue s) x0 x1 = x1 := by funext i; simp [mix]
    rw [h2]
    exact substG_allTrue (s := s) f g x1
  have ha_of : ∀ i : Fin s, substG f g (onlyFalse i) (mix (onlyFalse i) x0 x1) = g i x1 := by
    intro i
    rw [substG_onlyFalse]
    apply hgind
    intro j hj
    simp [mix, onlyFalse, hj]
  have ha_other : ∀ ω : Fin s → Bool,
      ω ∉ insert (allTrue s) (Finset.univ.image (fun i : Fin s => onlyFalse i)) →
      substG f g ω (mix ω x0 x1) = 1 := by
    intro ω hω
    have hne : ¬ (∀ i, ω i) := by
      intro h
      exact hω (by rw [(eq_allTrue_iff ω).mpr h]; exact Finset.mem_insert_self _ _)
    have hnu : ¬ (∃ i, ω i = false ∧ ∀ j, j ≠ i → ω j) := by
      rintro ⟨i, hi, h'⟩
      refine hω (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, ?_⟩))
      exact (eq_onlyFalse_of_unique_false hi h').symm
    simp only [substG]
    rw [dif_neg hne, dif_neg hnu]
  have hmain : ∏ ω : Fin s → Bool, substG f g ω (mix ω x0 x1)
      = ∏ ω ∈ (insert (allTrue s) (Finset.univ.image (fun i : Fin s => onlyFalse i))),
          substG f g ω (mix ω x0 x1) :=
    (Finset.prod_subset (Finset.subset_univ _) (fun x _ hx => ha_other x hx)).symm
  have hprod : (∏ i ∈ Finset.univ, substG f g (onlyFalse i) (mix (onlyFalse i) x0 x1))
      = ∏ i : Fin s, g i x1 := Finset.prod_congr rfl (fun i _ => ha_of i)
  rw [hmain, Finset.prod_insert allTrue_not_mem_image,
    Finset.prod_image (f := fun ω => substG f g ω (mix ω x0 x1))
      (fun i _ j _ hij => onlyFalse_injective hij), ha_all, hprod]

/-! ## The theorem -/

theorem gcsSubst :
    (∀ (X : Type) [Fintype X] (s : ℕ) (f : (Fin s → X) → ℂ) (g : Fin s → (Fin s → X) → ℂ),
        (∀ x, ‖f x‖ ≤ 1) → (∀ i x, ‖g i x‖ ≤ 1) →
        ∀ (ω : Fin s → Bool) (x : Fin s → X), ‖Work.Peluse.Concat.substF f g ω x‖ ≤ 1)
    ∧ (∀ (X : Type) [Fintype X] (s : ℕ), 1 ≤ s →
        ∀ (f : (Fin s → X) → ℂ) (g : Fin s → (Fin s → X) → ℂ),
        (∀ (i : Fin s) (x x' : Fin s → X), (∀ j, j ≠ i → x j = x' j) → g i x = g i x') →
        Work.Peluse.Concat.cubeSum (Work.Peluse.Concat.substF f g)
          = ((Fintype.card X : ℂ)) ^ s * ∑ x : Fin s → X, f x * ∏ i : Fin s, g i x)
    ∧ (∀ (X : Type) [Fintype X] (s : ℕ), 1 ≤ s →
        ∀ (f : (Fin s → X) → ℂ) (g : Fin s → (Fin s → X) → ℂ),
        (∀ x, ‖f x‖ ≤ 1) → (∀ i x, ‖g i x‖ ≤ 1) →
        (∀ (i : Fin s) (x x' : Fin s → X), (∀ j, j ≠ i → x j = x' j) → g i x = g i x') →
        (∏ ω : Fin s → Bool, Work.Peluse.Concat.NPow s (Work.Peluse.Concat.substF f g ω))
          ≤ Work.Peluse.Concat.NPow s f * (((Fintype.card X : ℝ)) ^ (2*s)) ^ (2^s - 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X _ s f g hf hg ω x
    exact norm_substF_le f g hf hg ω x
  · intro X _ s _ f g hgind
    have hcube : cubeSum (substF f g)
        = ∑ x0 : Fin s → X, ∑ x1 : Fin s → X, f x1 * ∏ i : Fin s, g i x1 := by
      unfold cubeSum cubeProd
      refine Finset.sum_congr rfl (fun x0 _ => Finset.sum_congr rfl (fun x1 _ => ?_))
      have hterm : ∀ ω : Fin s → Bool,
          (star^[Work.Peluse.weight ω]) (substF f g ω (mix ω x0 x1))
            = substG f g ω (mix ω x0 x1) := by
        intro ω
        simp only [substF]
        exact star_iterate_iterate _ _
      rw [Finset.prod_congr rfl (fun ω _ => hterm ω)]
      exact prod_substG f g hgind x0 x1
    rw [hcube]
    have hsum : ∑ x0 : Fin s → X, ∑ x1 : Fin s → X, f x1 * ∏ i : Fin s, g i x1
        = (Fintype.card (Fin s → X) : ℂ) * ∑ x : Fin s → X, f x * ∏ i : Fin s, g i x := by
      rw [Finset.sum_comm]
      have h1 : ∀ x1 : Fin s → X, (∑ _x0 : Fin s → X, f x1 * ∏ i : Fin s, g i x1)
          = (Fintype.card (Fin s → X) : ℂ) * (f x1 * ∏ i : Fin s, g i x1) := by
        intro x1
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp only [h1]
      rw [← Finset.mul_sum]
    rw [hsum]
    congr 1
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  · intro X _ s _ f g hf hg hgind
    classical
    have hcard : (Finset.univ.erase (allTrue s)).card = 2 ^ s - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_bool]
    have hall : NPow s (substF f g (allTrue s)) = NPow s f := by
      have h1 : substF f g (allTrue s) = fun x => (star^[s]) (f x) := by
        funext x
        simp only [substF]
        rw [weight_allTrue, substG_allTrue]
      rw [h1, NPow_star_iterate]
    have hle : ∀ ω : Fin s → Bool, ω ≠ allTrue s →
        NPow s (substF f g ω) ≤ ((Fintype.card X : ℝ)) ^ (2*s) := by
      intro ω _
      exact NPow_le_card s _ (fun x => norm_substF_le f g hf hg ω x)
    have hsplit : ∏ ω : Fin s → Bool, NPow s (substF f g ω)
        = NPow s (substF f g (allTrue s))
          * ∏ ω ∈ (Finset.univ.erase (allTrue s)), NPow s (substF f g ω) := by
      conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ (allTrue s))]
      rw [Finset.prod_insert (Finset.notMem_erase _ _)]
    calc ∏ ω : Fin s → Bool, NPow s (substF f g ω)
        = NPow s (substF f g (allTrue s))
          * ∏ ω ∈ (Finset.univ.erase (allTrue s)), NPow s (substF f g ω) := hsplit
      _ = NPow s f * ∏ ω ∈ (Finset.univ.erase (allTrue s)), NPow s (substF f g ω) := by
          rw [hall]
      _ ≤ NPow s f * ∏ _ω ∈ (Finset.univ.erase (allTrue s)),
            ((Fintype.card X : ℝ)) ^ (2*s) := by
          apply mul_le_mul_of_nonneg_left _ (by unfold NPow; positivity)
          apply Finset.prod_le_prod₀
          · intro ω _; unfold NPow; positivity
          · intro ω hω; exact hle ω (Finset.ne_of_mem_erase hω)
      _ = NPow s f * (((Fintype.card X : ℝ)) ^ (2*s)) ^ (2^s - 1) := by
          rw [Finset.prod_const, hcard]

end

end Work.Peluse.Concat

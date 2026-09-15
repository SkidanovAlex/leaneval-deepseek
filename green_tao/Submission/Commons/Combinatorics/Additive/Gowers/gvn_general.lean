import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Submission.Commons.Combinatorics.Additive.AP.sum_weighted_coordinates
import Submission.Commons.Combinatorics.Additive.Gowers.cube_one_sum

open scoped BigOperators

namespace GVNgen

/-! ## Averages over finite types -/

/-- Average of a real-valued function over a finite type. -/
noncomputable def av {α : Type*} [Fintype α] (g : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ)⁻¹ * ∑ x, g x

lemma av_congr {α : Type*} [Fintype α] {g g' : α → ℝ} (h : ∀ x, g x = g' x) :
    av g = av g' := by
  unfold av
  rw [Finset.sum_congr rfl fun x _ => h x]

lemma av_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) : av (fun _ : α => c) = c := by
  rw [av, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

lemma av_nonneg {α : Type*} [Fintype α] (g : α → ℝ) (hg : ∀ x, 0 ≤ g x) : 0 ≤ av g := by
  unfold av
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun x _ => hg x)

/-- Reindexing of an average along an equivalence. -/
lemma av_comp {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (g : β → ℝ) :
    av (fun a => g (e a)) = av g := by
  unfold av
  rw [Fintype.card_congr e, Equiv.sum_comp e g]

/-- Cauchy–Schwarz for averages. -/
lemma av_mul_sq_le {α : Type*} [Fintype α] (A B : α → ℝ) :
    (av fun x => A x * B x)^2 ≤ (av fun x => A x^2) * (av fun x => B x^2) := by
  unfold av
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α) A B
  calc ((Fintype.card α : ℝ)⁻¹ * ∑ x, A x * B x)^2
      = (Fintype.card α : ℝ)⁻¹^2 * (∑ x, A x * B x)^2 := by ring
    _ ≤ (Fintype.card α : ℝ)⁻¹^2 * ((∑ x, A x^2) * (∑ x, B x^2)) :=
        mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
    _ = ((Fintype.card α : ℝ)⁻¹ * ∑ x, A x^2) * ((Fintype.card α : ℝ)⁻¹ * ∑ x, B x^2) := by
        ring

/-- `Fin (m+1)`-tuples as `(last element, initial segment)`. -/
def snocEquiv (m : ℕ) (X : Type*) : X × (Fin m → X) ≃ (Fin (m+1) → X) where
  toFun p := Fin.snoc p.2 p.1
  invFun u := (u (Fin.last m), Fin.init u)
  left_inv p := by obtain ⟨z, u⟩ := p; simp [Fin.init_snoc]
  right_inv u := Fin.snoc_init_self u

/-- Splitting an average over `Fin (m+1)` along the last coordinate. -/
lemma av_snoc {X : Type*} [Fintype X] (m : ℕ) (F : (Fin (m+1) → X) → ℝ) :
    av (fun u : Fin (m+1) → X => F u)
      = av (fun p : X × (Fin m → X) => F (Fin.snoc p.2 p.1)) := by
  have hsum : (∑ u : Fin (m+1) → X, F u)
      = ∑ p : X × (Fin m → X), F (Fin.snoc p.2 p.1) :=
    (Equiv.sum_comp (snocEquiv m X) F).symm
  have hcard : (Fintype.card (Fin (m+1) → X) : ℝ)
      = (Fintype.card (X × (Fin m → X)) : ℝ) := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin]
    push_cast
    ring
  unfold av
  rw [hsum, hcard]

lemma av_prod {α β : Type*} [Fintype α] [Fintype β] (g : α → β → ℝ) :
    av (fun a : α => av (fun b : β => g a b)) = av (fun p : α × β => g p.1 p.2) := by
  have hsum : (∑ a : α, ∑ b : β, g a b) = ∑ p : α × β, g p.1 p.2 :=
    (Fintype.sum_prod_type (f := fun p : α × β => g p.1 p.2)).symm
  dsimp only [av]
  rw [← Finset.mul_sum, hsum, Fintype.card_prod]
  push_cast
  rw [mul_inv]
  ring

/-- `Fin (n+1)`-tuples as `(first element, tail)`. -/

lemma av_prod' {α β : Type*} [Fintype α] [Fintype β] (F : α × β → ℝ) :
    av F = av (fun b : β => av (fun a : α => F (a, b))) := by
  rw [av_prod (fun b a => F (a, b))]
  rw [show (fun q : β × α => F (q.2, q.1)) = (fun q : β × α => F ((Equiv.prodComm α β).symm q)) from rfl]
  exact (av_comp (Equiv.prodComm α β).symm F).symm

lemma av_swap {α β : Type*} [Fintype α] [Fintype β] (F : α → β → ℝ) :
    av (fun a : α => av (fun b : β => F a b)) = av (fun b : β => av (fun a : α => F a b)) := by
  rw [av_prod (g := F)]
  exact av_prod' (F := fun p : α × β => F p.1 p.2)

lemma av_le {α : Type*} [Fintype α] {g h : α → ℝ} (hh : ∀ x, g x ≤ h x) : av g ≤ av h := by
  unfold av
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hh x)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

lemma av_sq {α : Type*} [Fintype α] (g : α → ℝ) :
    (av g)^2 = av (fun p : α × α => g p.1 * g p.2) := by
  have hsum : (∑ x : α, g x)^2 = ∑ p : α × α, g p.1 * g p.2 := by
    rw [pow_two, Finset.sum_mul_sum]
    exact (Fintype.sum_prod_type (f := fun p : α × α => g p.1 * g p.2)).symm
  have hcard : ((Fintype.card (α × α) : ℕ) : ℝ)
      = (Fintype.card α : ℝ) * (Fintype.card α : ℝ) := by
    rw [Fintype.card_prod]
    push_cast
    ring
  dsimp only [av]
  rw [mul_pow, hsum, hcard]
  rw [mul_inv]
  ring

lemma av_mul_const {α : Type*} [Fintype α] (g : α → ℝ) (c : ℝ) :
    av (fun x => g x * c) = av g * c := by
  dsimp only [av]
  rw [← Finset.sum_mul]
  ring

def consEquiv (n : ℕ) (X : Type*) : X × (Fin n → X) ≃ (Fin (n+1) → X) where
  toFun p := Fin.cons p.1 p.2
  invFun u := (u 0, Fin.tail u)
  left_inv p := by obtain ⟨z, u⟩ := p; simp [Fin.tail_cons]
  right_inv u := Fin.cons_self_tail u

/-! ## The iterated Cauchy–Schwarz quantities of Green–Tao §5

The stage is parametrised by the number `m` of coordinates in the *fixed prefix*: stage `m`
sums over a `(m+1)`-tuple of functions and a cube of dimension `k-1-m`.  Stage `k-1`
(empty prefix) is the arithmetic-progression sum and stage `0` (empty cube) is the
`(k-1)`-dimensional cube sum of `f 0`. -/

/-- Concatenate a prefix of length `m` with a suffix of length `k-1-m`. -/
def app {X : Type*} (k m : ℕ) (hm : m + 1 ≤ k) (u : Fin m → X) (w : Fin (k-1-m) → X) :
    Fin (k-1) → X :=
  fun j => if h : j.val < m then u ⟨j.val, h⟩ else w ⟨j.val - m, by omega⟩

lemma app_apply {X : Type*} (k m : ℕ) (hm : m + 1 ≤ k) (u : Fin m → X)
    (w : Fin (k-1-m) → X) (j : Fin (k-1)) :
    app k m hm u w j
      = if h : j.val < m then u ⟨j.val, h⟩ else w ⟨j.val - m, by omega⟩ := rfl

lemma app_prefix {X : Type*} (k m : ℕ) (hm : m + 1 ≤ k) (u : Fin m → X)
    (w : Fin (k-1-m) → X) (i : Fin m) : app k m hm u w ⟨i.val, by omega⟩ = u i := by
  rw [app_apply, dif_pos i.isLt]

lemma app_suffix {X : Type*} (k m : ℕ) (hm : m + 1 ≤ k) (u : Fin m → X)
    (w : Fin (k-1-m) → X) (i : Fin (k-1-m)) :
    app k m hm u w ⟨m + i.val, by omega⟩ = w i := by
  rw [app_apply, dif_neg (by omega : ¬ m + i.val < m)]
  congr 1
  exact Fin.ext (by simp)

/-- The integrand of the `m`-th Green–Tao quantity: the product over the cube of the first
`m+1` functions. -/
noncomputable def Tfin (X : Type*) [Fintype X] (k : ℕ)
    (φ : Fin k → (Fin (k-1) → X) → X) (f : Fin k → X → ℝ)
    (m : ℕ) (hm : m + 1 ≤ k) (u : Fin m → X) (v y' : Fin (k-1-m) → X) : ℝ :=
  ∏ ω : Fin (k-1-m) → Bool, ∏ i : Fin (m+1),
    f ⟨i.val, by omega⟩ (φ ⟨i.val, by omega⟩
      (app k m hm u (fun j => if ω j then y' j else v j)))

/-- The `m`-th quantity `J` of the iterated Cauchy–Schwarz argument of Green–Tao §5. -/
noncomputable def Jf (X : Type*) [Fintype X] (k : ℕ)
    (φ : Fin k → (Fin (k-1) → X) → X) (f : Fin k → X → ℝ) (m : ℕ) (hm : m + 1 ≤ k) : ℝ :=
  av (fun u : Fin m → X =>
    av (fun v : Fin (k-1-m) → X =>
      av (fun y' : Fin (k-1-m) → X => Tfin X k φ f m hm u v y')))

/-- Append a new element at the *front* of a suffix vector of length `k-1-(m+1)`. -/
def consK {X : Type*} {k m : ℕ} (hm : m + 2 ≤ k) (z : X) (v : Fin (k-1-(m+1)) → X) :
    Fin (k-1-m) → X :=
  fun j => if hj : j.val = 0 then z else v ⟨j.val - 1, by omega⟩

lemma consK_zero {X : Type*} {k m : ℕ} (hm : m + 2 ≤ k) (z : X)
    (v : Fin (k-1-(m+1)) → X) : consK hm z v ⟨0, by omega⟩ = z := by
  rw [consK]
  exact dif_pos rfl

lemma consK_succ {X : Type*} {k m : ℕ} (hm : m + 2 ≤ k) (z : X)
    (v : Fin (k-1-(m+1)) → X) (i : Fin (k-1-(m+1))) :
    consK hm z v ⟨i.val + 1, by omega⟩ = v i := by
  rw [consK, dif_neg (by omega : ¬ (i.val + 1 : ℕ) = 0)]
  congr 1

lemma consK_apply_zero {X : Type*} {k m : ℕ} (hm : m + 2 ≤ k) (z : X)
    (v : Fin (k-1-(m+1)) → X) (j : Fin (k-1-m)) (hj : j.val = 0) :
    consK hm z v j = z := dif_pos hj

lemma consK_apply_ne {X : Type*} {k m : ℕ} (hm : m + 2 ≤ k) (z : X)
    (v : Fin (k-1-(m+1)) → X) (j : Fin (k-1-m)) (hj : ¬ j.val = 0) :
    consK hm z v j = v ⟨j.val - 1, by omega⟩ := dif_neg hj

/-- `consK` as an equivalence. -/
def consKEquiv {X : Type*} (k m : ℕ) (hm : m + 2 ≤ k) :
    X × (Fin (k-1-(m+1)) → X) ≃ (Fin (k-1-m) → X) where
  toFun p := consK hm p.1 p.2
  invFun u := (u ⟨0, by omega⟩, fun i => u ⟨i.val + 1, by omega⟩)
  left_inv p := by
    obtain ⟨z, v⟩ := p
    refine Prod.ext ?_ ?_
    · exact (consK_zero hm z v).symm
    · funext i; exact consK_succ hm z v i
  right_inv u := by
    funext j
    show consK hm (u ⟨0, by omega⟩) (fun i => u ⟨i.val + 1, by omega⟩) j = u j
    rcases eq_or_ne j.val 0 with hj | hj
    · have hj0 : j = ⟨0, by omega⟩ := Fin.ext hj
      rw [hj0, consK_apply_zero (k := k) (m := m) hm (u ⟨0, by omega⟩)
          (fun i => u ⟨i.val + 1, by omega⟩) ⟨0, by omega⟩ rfl]
    · have hjn : j = ⟨j.val - 1 + 1, by omega⟩ := Fin.ext (by simp only [Fin.val_mk]; omega)
      rw [hjn, consK_succ (k := k) (m := m) hm (u ⟨0, by omega⟩)
          (fun i => u ⟨i.val + 1, by omega⟩) ⟨j.val - 1, by omega⟩]

lemma av_consK {X : Type*} [Fintype X] {k m : ℕ} (hm : m + 2 ≤ k)
    (F : (Fin (k-1-m) → X) → ℝ) :
    av (fun p : X × (Fin (k-1-(m+1)) → X) => F (consK hm p.1 p.2)) = av F :=
  av_comp (consKEquiv k m hm) F

/-- The shuffle `((A × B) × (C × D)) ≃ ((C × A) × (D × B))`. -/
def shuf (A B C D : Type*) : ((A × B) × (C × D)) ≃ ((C × A) × (D × B)) where
  toFun p := ((p.2.1, p.1.1), (p.2.2, p.1.2))
  invFun p := ((p.1.2, p.2.2), (p.1.1, p.2.1))
  left_inv p := by obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := p; rfl
  right_inv p := by obtain ⟨⟨c, a⟩, ⟨d, b⟩⟩ := p; rfl

/-- Append a new Boolean at the *front* of a cube vertex of dimension `k-1-(m+1)`. -/
def boolK {k m : ℕ} (hm : m + 2 ≤ k) (b : Bool) (ω : Fin (k-1-(m+1)) → Bool) :
    Fin (k-1-m) → Bool :=
  fun j => if hj : j.val = 0 then b else ω ⟨j.val - 1, by omega⟩

lemma boolK_zero {k m : ℕ} (hm : m + 2 ≤ k) (b : Bool) (ω : Fin (k-1-(m+1)) → Bool) :
    boolK hm b ω ⟨0, by omega⟩ = b := by
  rw [boolK]
  exact dif_pos rfl

lemma boolK_succ {k m : ℕ} (hm : m + 2 ≤ k) (b : Bool) (ω : Fin (k-1-(m+1)) → Bool)
    (i : Fin (k-1-(m+1))) : boolK hm b ω ⟨i.val + 1, by omega⟩ = ω i := by
  rw [boolK, dif_neg (by omega : ¬ (i.val + 1 : ℕ) = 0)]
  congr 1

lemma boolK_apply_zero {k m : ℕ} (hm : m + 2 ≤ k) (b : Bool) (ω : Fin (k-1-(m+1)) → Bool)
    (j : Fin (k-1-m)) (hj : j.val = 0) : boolK hm b ω j = b := dif_pos hj

lemma boolK_apply_ne {k m : ℕ} (hm : m + 2 ≤ k) (b : Bool) (ω : Fin (k-1-(m+1)) → Bool)
    (j : Fin (k-1-m)) (hj : ¬ j.val = 0) :
    boolK hm b ω j = ω ⟨j.val - 1, by omega⟩ := dif_neg hj

/-- `boolK` as an equivalence. -/
def boolKEquiv (k m : ℕ) (hm : m + 2 ≤ k) :
    Bool × (Fin (k-1-(m+1)) → Bool) ≃ (Fin (k-1-m) → Bool) where
  toFun p := boolK hm p.1 p.2
  invFun ω := (ω ⟨0, by omega⟩, fun i => ω ⟨i.val + 1, by omega⟩)
  left_inv p := by
    obtain ⟨b, ω⟩ := p
    refine Prod.ext ?_ ?_
    · exact (boolK_zero hm b ω).symm
    · funext i; exact boolK_succ hm b ω i
  right_inv ω := by
    funext j
    show boolK hm (ω ⟨0, by omega⟩) (fun i => ω ⟨i.val + 1, by omega⟩) j = ω j
    rcases eq_or_ne j.val 0 with hj | hj
    · have hj0 : j = ⟨0, by omega⟩ := Fin.ext hj
      rw [hj0, boolK_apply_zero (k := k) (m := m) hm (ω ⟨0, by omega⟩)
          (fun i => ω ⟨i.val + 1, by omega⟩) ⟨0, by omega⟩ rfl]
    · have hjn : j = ⟨j.val - 1 + 1, by omega⟩ := Fin.ext (by simp only [Fin.val_mk]; omega)
      rw [hjn, boolK_succ (k := k) (m := m) hm (ω ⟨0, by omega⟩)
          (fun i => ω ⟨i.val + 1, by omega⟩) ⟨j.val - 1, by omega⟩]

/-- The `z`-dependent part of the integrand after splitting off the last remaining function:
the product of the first `m+1` functions over the cube. -/
noncomputable def HHf (X : Type*) [Fintype X] (k : ℕ)
    (φ : Fin k → (Fin (k-1) → X) → X) (f : Fin k → X → ℝ)
    (m : ℕ) (hm : m + 2 ≤ k) (u : Fin (m+1) → X) (v y' : Fin (k-1-(m+1)) → X) : ℝ :=
  ∏ ω : Fin (k-1-(m+1)) → Bool, ∏ i : Fin (m+1),
    f ⟨i.val, by omega⟩ (φ ⟨i.val, by omega⟩
      (app k (m+1) (by omega) u (fun j => if ω j then y' j else v j)))

/-- The `z`-independent part of the integrand after splitting off the last remaining function:
the last function `f_{m+1}` evaluated on the cube. -/
noncomputable def GGf (X : Type*) [Fintype X] (k : ℕ)
    (φ : Fin k → (Fin (k-1) → X) → X) (f : Fin k → X → ℝ)
    (m : ℕ) (hm : m + 2 ≤ k) (u : Fin (m+1) → X) (v y' : Fin (k-1-(m+1)) → X) : ℝ :=
  ∏ ω : Fin (k-1-(m+1)) → Bool,
    f ⟨m+1, by omega⟩ (φ ⟨m+1, by omega⟩
      (app k (m+1) (by omega) u (fun j => if ω j then y' j else v j)))

/-- The product at stage `m+1` splits as the product of the first `m+1` functions times the
last one. -/
lemma Tfin_split (X : Type*) [Fintype X] (k : ℕ)
    (φ : Fin k → (Fin (k-1) → X) → X) (f : Fin k → X → ℝ)
    (m : ℕ) (hm : m + 2 ≤ k) (u : Fin (m+1) → X) (v y' : Fin (k-1-(m+1)) → X) :
    Tfin X k φ f (m+1) (by omega) u v y'
      = HHf X k φ f m hm u v y' * GGf X k φ f m hm u v y' := by
  rw [Tfin, HHf, GGf]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro ω _
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]

/-- `GGf` does not depend on the last coordinate of the prefix. -/
lemma GGf_congr {X : Type*} [Fintype X] {k : ℕ}
    (φ : Fin k → (Fin (k-1) → X) → X) (f : Fin k → X → ℝ)
    (hφ : ∀ (m : ℕ) (hm : m + 2 ≤ k) (u : Fin m → X) (z z' : X)
        (w : Fin (k-1-(m+1)) → X),
      φ ⟨m+1, by omega⟩ (app k (m+1) (by omega) (Fin.snoc u z) w)
        = φ ⟨m+1, by omega⟩ (app k (m+1) (by omega) (Fin.snoc u z') w))
    (m : ℕ) (hm : m + 2 ≤ k) (u : Fin m → X) (z z' : X)
    (v y' : Fin (k-1-(m+1)) → X) :
    GGf X k φ f m hm (Fin.snoc u z) v y' = GGf X k φ f m hm (Fin.snoc u z') v y' := by
  rw [GGf, GGf]
  apply Finset.prod_congr rfl
  intro ω _
  rw [hφ m hm u z z' (fun j => if ω j then y' j else v j)]

/-- The vertex identity relating stage `m+1` and stage `m`. -/
lemma app_cons {X : Type*} {k m : ℕ} (hm : m + 2 ≤ k) (u : Fin m → X) (z z' : X)
    (v y' : Fin (k-1-(m+1)) → X) (b : Bool) (ω : Fin (k-1-(m+1)) → Bool)
    (j : Fin (k-1)) :
    app k (m+1) (by omega) (Fin.snoc u (if b then z' else z))
        (fun j => if ω j then y' j else v j) j
      = app k m (by omega) u
        (fun j => if boolK hm b ω j then (consK hm z' y') j else (consK hm z v) j) j := by
  simp only [app_apply]
  by_cases h1 : j.val < m
  · simp only [dif_pos h1, dif_pos (Nat.lt_succ_of_lt h1)]
    have hcast : (⟨j.val, Nat.lt_succ_of_lt h1⟩ : Fin (m+1)) = (⟨j.val, h1⟩ : Fin m).castSucc :=
      Fin.ext rfl
    rw [hcast, Fin.snoc_castSucc]
  · simp only [dif_neg h1]
    by_cases h2 : j.val = m
    · have e1 : (⟨j.val, by omega⟩ : Fin (m+1)) = Fin.last m := Fin.ext (by simp [h2])
      have e2 : (⟨j.val - m, by omega⟩ : Fin (k-1-m)) = ⟨0, by omega⟩ := Fin.ext (by simp [h2])
      simp only [dif_pos (show j.val < m + 1 by omega), e1, Fin.snoc_last, e2,
        boolK_zero hm, consK_zero hm]
    · have h3 : m < j.val := by omega
      have h4 : ¬ j.val < m + 1 := by omega
      simp only [dif_neg h4]
      have hne : ¬ (⟨j.val - m, by omega⟩ : Fin (k-1-m)).val = 0 := by
        simp only [Fin.val_mk]; omega
      simp only [boolK_apply_ne (k := k) (m := m) hm b ω ⟨j.val - m, by omega⟩ hne,
        consK_apply_ne (k := k) (m := m) hm z' y' ⟨j.val - m, by omega⟩ hne,
        consK_apply_ne (k := k) (m := m) hm z v ⟨j.val - m, by omega⟩ hne]
      exact congrArg (fun i : Fin (k-1-(m+1)) => if ω i then y' i else v i)
        (Fin.ext (by simp only [Fin.val_mk]; rw [Nat.sub_sub]))

/-- The vertex identity, as an equality of functions. -/
lemma app_cons_fun {X : Type*} {k m : ℕ} (hm : m + 2 ≤ k) (u : Fin m → X) (z z' : X)
    (v y' : Fin (k-1-(m+1)) → X) (b : Bool) (ω : Fin (k-1-(m+1)) → Bool) :
    app k (m+1) (by omega) (Fin.snoc u (if b then z' else z))
        (fun j => if ω j then y' j else v j)
      = app k m (by omega) u
        (fun j => if boolK hm b ω j then (consK hm z' y') j else (consK hm z v) j) := by
  funext j
  exact app_cons hm u z z' v y' b ω j

/-- The square expansion at the transition `m → m+1`: the two products over the stage-`m+1`
cube equal the single product over the stage-`m` cube with the doubled variables. -/
lemma Tfin_cons {X : Type*} [Fintype X] {k : ℕ}
    (φ : Fin k → (Fin (k-1) → X) → X) (f : Fin k → X → ℝ)
    (m : ℕ) (hm : m + 2 ≤ k) (u : Fin m → X) (z z' : X)
    (v y' : Fin (k-1-(m+1)) → X) :
    Tfin X k φ f m (by omega) u (consK hm z v) (consK hm z' y')
      = HHf X k φ f m hm (Fin.snoc u z) v y'
          * HHf X k φ f m hm (Fin.snoc u z') v y' := by
  have key : ∀ (b : Bool) (ω : Fin (k-1-(m+1)) → Bool) (i : Fin (m+1)),
      f ⟨i.val, by omega⟩ (φ ⟨i.val, by omega⟩
          (app k m (by omega) u (fun j => if boolK hm b ω j then (consK hm z' y') j
            else (consK hm z v) j)))
        = f ⟨i.val, by omega⟩ (φ ⟨i.val, by omega⟩
          (app k (m+1) (by omega) (Fin.snoc u (if b then z' else z))
            (fun j => if ω j then y' j else v j))) := by
    intro b ω i
    rw [app_cons_fun (k := k) (m := m) hm u z z' v y' b ω]
  rw [Tfin, HHf, HHf]
  rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_equiv (boolKEquiv k m hm)
    (fun p : Bool × (Fin (k-1-(m+1)) → Bool) => ∏ i : Fin (m+1),
      f ⟨i.val, by omega⟩ (φ ⟨i.val, by omega⟩
        (app k m (by omega) u (fun j => if boolK hm p.1 p.2 j then (consK hm z' y') j
          else (consK hm z v) j))))
    (fun ω'' : Fin (k-1-m) → Bool => ∏ i : Fin (m+1),
      f ⟨i.val, by omega⟩ (φ ⟨i.val, by omega⟩
        (app k m (by omega) u (fun j => if ω'' j then (consK hm z' y') j
          else (consK hm z v) j))))
    (fun p => rfl)]
  rw [Fintype.prod_prod_type]
  rw [Fintype.prod_bool]
  dsimp only
  rw [Finset.prod_mul_distrib]
  rw [mul_comm]
  congr 1
  · apply Finset.prod_congr rfl; intro y _
    apply Finset.prod_congr rfl; intro i _
    simpa using congrArg (fun w => f ⟨i.val, by omega⟩ (φ ⟨i.val, by omega⟩ w))
      (app_cons_fun (k := k) (m := m) hm u z z' v y' false y).symm
  · apply Finset.prod_congr rfl; intro y _
    apply Finset.prod_congr rfl; intro i _
    simpa using congrArg (fun w => f ⟨i.val, by omega⟩ (φ ⟨i.val, by omega⟩ w))
      (app_cons_fun (k := k) (m := m) hm u z z' v y' true y).symm

section Reindex

variable {X : Type*} [Fintype X] [Nonempty X]

/-- The reindexing identity behind the recursion: the square of the average over the peeled
coordinate equals the stage-`m` quantity with doubled cube variables. -/
lemma av_HH_sq {k : ℕ} (φ : Fin k → (Fin (k-1) → X) → X) (f : Fin k → X → ℝ)
    (m : ℕ) (hm : m + 2 ≤ k) (u : Fin m → X) :
    av (fun q : (Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X) =>
        (av (fun z : X => HHf X k φ f m hm (Fin.snoc u z) q.1 q.2))^2)
      = av (fun v : Fin (k-1-m) → X => av (fun y' : Fin (k-1-m) → X =>
          Tfin X k φ f m (by omega) u v y')) := by
  have step1 : av (fun q : (Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X) =>
        (av (fun z : X => HHf X k φ f m hm (Fin.snoc u z) q.1 q.2))^2)
      = av (fun q : (Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X) =>
          av (fun p : X × X => HHf X k φ f m hm (Fin.snoc u p.1) q.1 q.2
            * HHf X k φ f m hm (Fin.snoc u p.2) q.1 q.2)) := by
    apply av_congr
    intro q
    rw [av_sq]
  rw [step1, av_prod]
  have step2 : av (fun r : ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) × (X × X) =>
          HHf X k φ f m hm (Fin.snoc u r.2.1) r.1.1 r.1.2
            * HHf X k φ f m hm (Fin.snoc u r.2.2) r.1.1 r.1.2)
      = av (fun r : ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) × (X × X) =>
          Tfin X k φ f m (by omega) u (consK hm r.2.1 r.1.1) (consK hm r.2.2 r.1.2)) := by
    apply av_congr
    intro r
    exact (Tfin_cons φ f m hm u r.2.1 r.2.2 r.1.1 r.1.2).symm
  rw [step2]
  -- reindex: `((V × V) × (X × X))` ↦ `((X × V) × (X × V))` ↦ `(Fin (k-1-m) → X)²`
  rw [show av (fun r : ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) × (X × X) =>
          Tfin X k φ f m (by omega) u (consK hm r.2.1 r.1.1) (consK hm r.2.2 r.1.2))
      = av (fun r : (X × (Fin (k-1-(m+1)) → X)) × (X × (Fin (k-1-(m+1)) → X)) =>
          Tfin X k φ f m (by omega) u (consK hm r.1.1 r.1.2) (consK hm r.2.1 r.2.2)) from by
    exact av_comp (shuf (Fin (k-1-(m+1)) → X) (Fin (k-1-(m+1)) → X) X X)
      (fun s : (X × (Fin (k-1-(m+1)) → X)) × (X × (Fin (k-1-(m+1)) → X)) =>
        Tfin X k φ f m (by omega) u (consK hm s.1.1 s.1.2) (consK hm s.2.1 s.2.2))]
  rw [show av (fun r : (X × (Fin (k-1-(m+1)) → X)) × (X × (Fin (k-1-(m+1)) → X)) =>
          Tfin X k φ f m (by omega) u (consK hm r.1.1 r.1.2) (consK hm r.2.1 r.2.2))
      = av (fun s : (Fin (k-1-m) → X) × (Fin (k-1-m) → X) =>
          Tfin X k φ f m (by omega) u s.1 s.2) from
    av_comp (Equiv.prodCongr (consKEquiv k m hm) (consKEquiv k m hm))
      (fun s : (Fin (k-1-m) → X) × (Fin (k-1-m) → X) => Tfin X k φ f m (by omega) u s.1 s.2)]
  rw [av_prod (g := fun v : Fin (k-1-m) → X => fun y' : Fin (k-1-m) → X =>
      Tfin X k φ f m (by omega) u v y')]


/-- The Cauchy–Schwarz recursion of the Green–Tao §5 argument: passing from stage `m`
to stage `m+1` squares the quantity but does not increase it. -/
lemma Jf_sq_le {k : ℕ} (φ : Fin k → (Fin (k-1) → X) → X) (f : Fin k → X → ℝ)
    (hf : ∀ i : Fin k, (i : ℕ) ≠ 0 → ∀ x, |f i x| ≤ 1)
    (hφ : ∀ (m : ℕ) (hm : m + 2 ≤ k) (u : Fin m → X) (z z' : X)
        (w : Fin (k-1-(m+1)) → X),
      φ ⟨m+1, by omega⟩ (app k (m+1) (by omega) (Fin.snoc u z) w)
        = φ ⟨m+1, by omega⟩ (app k (m+1) (by omega) (Fin.snoc u z') w))
    (m : ℕ) (hm : m + 2 ≤ k) :
    (Jf X k φ f (m+1) (by omega))^2 ≤ Jf X k φ f m (by omega) := by
  set z0 : X := Classical.arbitrary X with hz0
  have key1 : Jf X k φ f (m+1) (by omega)
      = av (fun r : (Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
          (av (fun z : X => HHf X k φ f m hm (Fin.snoc r.1 z) r.2.1 r.2.2))
            * GGf X k φ f m hm (Fin.snoc r.1 z0) r.2.1 r.2.2) := by
    have hJf : Jf X k φ f (m+1) (by omega)
        = av (fun u : Fin (m+1) → X => av (fun v : Fin (k-1-(m+1)) → X =>
            av (fun y' : Fin (k-1-(m+1)) → X =>
              Tfin X k φ f (m+1) (by omega) u v y'))) := rfl
    rw [hJf]
    have h1 : av (fun u : Fin (m+1) → X => av (fun v : Fin (k-1-(m+1)) → X =>
            av (fun y' : Fin (k-1-(m+1)) → X =>
              Tfin X k φ f (m+1) (by omega) u v y')))
        = av (fun p : X × (Fin m → X) => av (fun v : Fin (k-1-(m+1)) → X =>
            av (fun y' : Fin (k-1-(m+1)) → X =>
              Tfin X k φ f (m+1) (by omega) (Fin.snoc p.2 p.1) v y'))) := by
      rw [av_snoc m (fun u : Fin (m+1) → X => av (fun v : Fin (k-1-(m+1)) → X =>
            av (fun y' : Fin (k-1-(m+1)) → X =>
              Tfin X k φ f (m+1) (by omega) u v y')))]
    rw [h1]
    have h2 : av (fun p : X × (Fin m → X) => av (fun v : Fin (k-1-(m+1)) → X =>
            av (fun y' : Fin (k-1-(m+1)) → X =>
              Tfin X k φ f (m+1) (by omega) (Fin.snoc p.2 p.1) v y')))
        = av (fun p : X × (Fin m → X) =>
            av (fun s : (Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X) =>
              Tfin X k φ f (m+1) (by omega) (Fin.snoc p.2 p.1) s.1 s.2)) := by
      apply av_congr; intro p
      exact av_prod (g := fun v y' =>
        Tfin X k φ f (m+1) (by omega) (Fin.snoc p.2 p.1) v y')
    rw [h2]
    have h3 : av (fun p : X × (Fin m → X) =>
            av (fun s : (Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X) =>
              Tfin X k φ f (m+1) (by omega) (Fin.snoc p.2 p.1) s.1 s.2))
        = av (fun p : X × (Fin m → X) =>
            av (fun s : (Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X) =>
              HHf X k φ f m hm (Fin.snoc p.2 p.1) s.1 s.2
                * GGf X k φ f m hm (Fin.snoc p.2 z0) s.1 s.2)) := by
      apply av_congr; intro p
      apply av_congr; intro s
      rw [Tfin_split]
      rw [GGf_congr φ f hφ m hm p.2 p.1 z0 s.1 s.2]
    rw [h3]
    have h4 : av (fun p : X × (Fin m → X) =>
            av (fun s : (Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X) =>
              HHf X k φ f m hm (Fin.snoc p.2 p.1) s.1 s.2
                * GGf X k φ f m hm (Fin.snoc p.2 z0) s.1 s.2))
        = av (fun u : Fin m → X =>
            av (fun s : (Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X) =>
              (av (fun z : X => HHf X k φ f m hm (Fin.snoc u z) s.1 s.2))
                * GGf X k φ f m hm (Fin.snoc u z0) s.1 s.2)) := by
      rw [av_prod' (F := fun p : X × (Fin m → X) =>
            av (fun s : (Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X) =>
              HHf X k φ f m hm (Fin.snoc p.2 p.1) s.1 s.2
                * GGf X k φ f m hm (Fin.snoc p.2 z0) s.1 s.2))]
      apply av_congr; intro u
      rw [av_swap (F := fun z : X =>
        fun s : (Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X) =>
          HHf X k φ f m hm (Fin.snoc u z) s.1 s.2
            * GGf X k φ f m hm (Fin.snoc u z0) s.1 s.2)]
      apply av_congr; intro s
      rw [av_mul_const]
    rw [h4]
    exact av_prod (g := fun u (s : (Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
      (av (fun z : X => HHf X k φ f m hm (Fin.snoc u z) s.1 s.2))
        * GGf X k φ f m hm (Fin.snoc u z0) s.1 s.2)
  have hA2 : av (fun r : (Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
        (av (fun z : X => HHf X k φ f m hm (Fin.snoc r.1 z) r.2.1 r.2.2))^2)
      = Jf X k φ f m (by omega) := by
    rw [← (av_prod (g := fun u (s : (Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
      (av (fun z : X => HHf X k φ f m hm (Fin.snoc u z) s.1 s.2))^2))]
    have hJf2 : Jf X k φ f m (by omega)
        = av (fun u : Fin m → X => av (fun v : Fin (k-1-m) → X =>
            av (fun y' : Fin (k-1-m) → X =>
              Tfin X k φ f m (by omega) u v y'))) := rfl
    rw [hJf2]
    apply av_congr; intro u
    rw [av_HH_sq φ f m hm u]
  have hB2 : av (fun r : (Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
        (GGf X k φ f m hm (Fin.snoc r.1 z0) r.2.1 r.2.2)^2) ≤ 1 := by
    have hle : ∀ r : (Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)),
        (GGf X k φ f m hm (Fin.snoc r.1 z0) r.2.1 r.2.2)^2 ≤ 1 := by
      intro r
      have h1 : |GGf X k φ f m hm (Fin.snoc r.1 z0) r.2.1 r.2.2| ≤ 1 := by
        dsimp only [GGf]
        rw [Finset.abs_prod]
        apply Finset.prod_le_one (fun x _ => abs_nonneg _)
        intro ω _
        exact hf ⟨m+1, by omega⟩ (by simp) _
      exact (sq_le_one_iff_abs_le_one _).mpr h1
    calc av (fun r : (Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
          (GGf X k φ f m hm (Fin.snoc r.1 z0) r.2.1 r.2.2)^2)
        ≤ av (fun _ : (Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
            (1:ℝ)) := av_le hle
      _ = 1 := av_const 1
  rw [key1]
  refine le_trans (av_mul_sq_le
      (fun r : (Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
        av (fun z : X => HHf X k φ f m hm (Fin.snoc r.1 z) r.2.1 r.2.2))
      (fun r : (Fin m → X) × ((Fin (k-1-(m+1)) → X) × (Fin (k-1-(m+1)) → X)) =>
        GGf X k φ f m hm (Fin.snoc r.1 z0) r.2.1 r.2.2)) ?_
  refine le_trans (mul_le_mul_of_nonneg_left hB2 (av_nonneg _ (fun r => sq_nonneg _))) ?_
  rw [hA2, mul_one]


/-- Iterating the Cauchy–Schwarz recursion of `Jf_sq_le`: the `2^m`-th power of the stage-`m`
quantity is controlled by the stage-`0` quantity. -/
lemma Jf_pow_le {k : ℕ} (hk : 1 ≤ k)
    (φ : Fin k → (Fin (k-1) → X) → X) (f : Fin k → X → ℝ)
    (hf : ∀ i : Fin k, (i : ℕ) ≠ 0 → ∀ x, |f i x| ≤ 1)
    (hφ : ∀ (m : ℕ) (hm : m + 2 ≤ k) (u : Fin m → X) (z z' : X)
        (w : Fin (k-1-(m+1)) → X),
      φ ⟨m+1, by omega⟩ (app k (m+1) (by omega) (Fin.snoc u z) w)
        = φ ⟨m+1, by omega⟩ (app k (m+1) (by omega) (Fin.snoc u z') w)) :
    ∀ (m : ℕ) (hm : m + 1 ≤ k),
      (Jf X k φ f m hm)^(2^m) ≤ Jf X k φ f 0 (by omega) := by
  intro m
  induction m with
  | zero =>
    intro hm
    rw [show (2:ℕ)^0 = 1 from rfl, pow_one]
  | succ n ih =>
    intro hm
    have hstep : (Jf X k φ f (n+1) (by omega))^2 ≤ Jf X k φ f n (by omega) :=
      Jf_sq_le (X := X) φ f hf hφ n (by omega)
    rw [show Jf X k φ f (n+1) hm = Jf X k φ f (n+1) (by omega) from
      congrArg (Jf X k φ f (n+1)) (Subsingleton.elim _ _)]
    rw [pow_succ', pow_mul]
    exact le_trans (pow_le_pow_left₀ (sq_nonneg _) hstep _) (ih (by omega))


/-- At the last stage (`m = k-1`) the Green–Tao quantity is the average of the product of all
the `f_i` evaluated at the `φ_i`. -/
lemma Jf_last {k : ℕ} (hk : 1 ≤ k) (φ : Fin k → (Fin (k-1) → X) → X) (f : Fin k → X → ℝ)
    (hm : k - 1 + 1 ≤ k) :
    Jf X k φ f (k-1) hm = av (fun u : Fin (k-1) → X => ∏ i : Fin k, f i (φ i u)) := by
  have happ : ∀ (u : Fin (k-1) → X) (w : Fin (k-1-(k-1)) → X),
      app k (k-1) hm u w = fun j : Fin (k-1) => u ⟨j.val, j.isLt⟩ := by
    intro u w
    funext j
    rw [app_apply, dif_pos j.isLt]
  have hT : ∀ (u : Fin (k-1) → X) (v y' : Fin (k-1-(k-1)) → X),
      Tfin X k φ f (k-1) hm u v y'
        = ∏ ω : Fin (k-1-(k-1)) → Bool, ∏ i : Fin (k-1+1),
            f ⟨i.val, by omega⟩ (φ ⟨i.val, by omega⟩ (fun j : Fin (k-1) => u ⟨j.val, j.isLt⟩)) := by
    intro u v y'
    simp only [Tfin]
    apply Finset.prod_congr rfl; intro ω _
    apply Finset.prod_congr rfl; intro i _
    rw [happ u (fun j => if ω j then y' j else v j)]
  rw [Jf]
  apply av_congr; intro u
  rw [show (fun v : Fin (k-1-(k-1)) → X => av (fun y' : Fin (k-1-(k-1)) → X =>
        Tfin X k φ f (k-1) hm u v y'))
      = (fun _ : Fin (k-1-(k-1)) → X => ∏ ω : Fin (k-1-(k-1)) → Bool, ∏ i : Fin (k-1+1),
            f ⟨i.val, by omega⟩ (φ ⟨i.val, by omega⟩ (fun j : Fin (k-1) => u ⟨j.val, j.isLt⟩)))
      from by
    funext v
    rw [av_congr (fun y' => hT u v y')]
    exact av_const _]
  rw [av_const]
  have hE : IsEmpty (Fin (k-1-(k-1))) := by
    rw [show k-1-(k-1) = 0 from Nat.sub_self _]
    infer_instance
  haveI : Unique (Fin (k-1-(k-1)) → Bool) :=
    ⟨⟨fun i => (hE.false i).elim⟩, fun a => funext (fun i => (hE.false i).elim)⟩
  rw [Fintype.prod_unique]
  refine Fintype.prod_equiv (finCongr (Nat.sub_add_cancel hk)) _ _ (fun i => ?_)
  have he : finCongr (Nat.sub_add_cancel hk) i = (⟨i.val, by omega⟩ : Fin k) :=
    Fin.ext (by simp [finCongr])
  rw [he]

/-- At stage `0` the Green–Tao quantity is the average over the (full) cube of `f_0`. -/
lemma Jf_zero {k : ℕ} (hk : 1 ≤ k) (φ : Fin k → (Fin (k-1) → X) → X) (f : Fin k → X → ℝ)
    (hm : 0 + 1 ≤ k) :
    Jf X k φ f 0 hm
      = av (fun v : Fin (k-1) → X => av (fun y' : Fin (k-1) → X =>
          ∏ ω : Fin (k-1) → Bool, ∏ i : Fin 1,
            f ⟨i.val, by omega⟩ (φ ⟨i.val, by omega⟩
              (fun j => if ω j then y' j else v j)))) := by
  have happ : ∀ (u : Fin 0 → X) (w : Fin (k-1-0) → X), app k 0 hm u w = w := by
    intro u w
    funext j
    rw [app_apply, dif_neg (by omega : ¬ j.val < 0)]
    congr 1
  have hT : ∀ (u : Fin 0 → X) (v y' : Fin (k-1-0) → X),
      Tfin X k φ f 0 hm u v y'
        = ∏ ω : Fin (k-1-0) → Bool, ∏ i : Fin (0+1),
            f ⟨i.val, by omega⟩ (φ ⟨i.val, by omega⟩
              (fun j => if ω j then y' j else v j)) := by
    intro u v y'
    simp only [Tfin]
    apply Finset.prod_congr rfl; intro ω _
    apply Finset.prod_congr rfl; intro i _
    show f ⟨i.val, by omega⟩ (φ ⟨i.val, by omega⟩ (app k 0 hm u (fun j => if ω j then y' j else v j))) = _
    rw [happ u (fun j => if ω j then y' j else v j)]
    rfl
  rw [Jf]
  rw [show (fun u : Fin 0 → X => av (fun v : Fin (k-1-0) → X => av (fun y' : Fin (k-1-0) → X =>
        Tfin X k φ f 0 hm u v y')))
      = (fun _ : Fin 0 → X => av (fun v : Fin (k-1-0) → X => av (fun y' : Fin (k-1-0) → X =>
          ∏ ω : Fin (k-1-0) → Bool, ∏ i : Fin (0+1),
            f ⟨i.val, by omega⟩ (φ ⟨i.val, by omega⟩
              (fun j => if ω j then y' j else v j))))) from by
    funext u
    exact av_congr (fun v => av_congr (fun y' => hT u v y'))]
  rw [av_const]
  rfl
end Reindex




section ZModReparam

variable {p : ℕ} [Fact p.Prime]

/-- Green–Tao's reparametrisation of arithmetic progressions: for `y : (Fin (k-1) → ZMod p)`
the value `φ_i(y) = x + i r` where `x = ∑ y_t` and `r = -∑ y_t/(t+1)`.  The point is that
`φ_i` does not depend on the `(i-1)`-th coordinate of `y`, which is what the iterated
Cauchy–Schwarz argument needs. -/
noncomputable def phiZ (k : ℕ) : Fin k → (Fin (k-1) → ZMod p) → ZMod p :=
  fun i y => (∑ t : Fin (k-1), y t)
    - (i : ZMod p) * (∑ t : Fin (k-1), y t / ((t : ZMod p) + 1))

lemma phiZ_apply (k : ℕ) (i : Fin k) (y : Fin (k-1) → ZMod p) :
    phiZ (p := p) k i y = (∑ t : Fin (k-1), y t)
      - (i : ZMod p) * (∑ t : Fin (k-1), y t / ((t : ZMod p) + 1)) := rfl

/-- The sum of a `Pi.single` function. -/
lemma sum_pi_single {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι) (v : ZMod p) :
    (∑ t : ι, (Pi.single j v : ι → ZMod p) t) = v := by
  rw [Finset.sum_eq_single j]
  · exact Pi.single_eq_same (M := fun _ : ι => ZMod p) j v
  · intro t _ ht
    exact Pi.single_eq_of_ne (M := fun _ : ι => ZMod p) ht v
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- Updating one coordinate is adding a suitable `Pi.single`. -/
lemma update_eq_add_single {ι : Type*} [DecidableEq ι] (j : ι) (y : ι → ZMod p) (c : ZMod p) :
    Function.update y j c = y + Pi.single j (c - y j) := by
  funext t
  by_cases h : t = j
  · subst h
    rw [Function.update_self, Pi.add_apply, Pi.single_eq_same]
    ring
  · rw [Function.update_of_ne h, Pi.add_apply, Pi.single_eq_of_ne h, add_zero]

/-- `φ_{m+1}` does not depend on the `m`-th coordinate. -/
lemma phiZ_update {k : ℕ} (hkp : k ≤ p) (m : ℕ) (hm : m + 2 ≤ k)
    (y : Fin (k-1) → ZMod p) (c : ZMod p) :
    phiZ (p := p) k ⟨m+1, by omega⟩ (Function.update y ⟨m, by omega⟩ c)
      = phiZ (p := p) k ⟨m+1, by omega⟩ y := by
  have hmk : m < k - 1 := by omega
  set j : Fin (k-1) := ⟨m, hmk⟩ with hj
  have h1 : (∑ t : Fin (k-1), Function.update y j c t) = (∑ t, y t) + (c - y j) := by
    rw [update_eq_add_single]
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib, sum_pi_single]
  have h2 : (∑ t : Fin (k-1), Function.update y j c t / ((t : ZMod p) + 1))
      = (∑ t, y t / ((t : ZMod p) + 1)) + (c - y j) / ((j : ZMod p) + 1) := by
    have hpt : ∀ t : Fin (k-1),
        Function.update y j c t / ((t : ZMod p) + 1)
          = y t / ((t : ZMod p) + 1)
            + (Pi.single j (c - y j) : Fin (k-1) → ZMod p) t / ((t : ZMod p) + 1) := by
      intro t
      rw [update_eq_add_single, Pi.add_apply, add_div]
    rw [Finset.sum_congr rfl (fun t _ => hpt t), Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same]
    · intro t _ ht
      rw [Pi.single_eq_of_ne (M := fun _ : Fin (k-1) => ZMod p) ht, zero_div]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hne : ((m : ZMod p) + 1) ≠ 0 := by
    have h0 : ((m + 1 : ℕ) : ZMod p) ≠ 0 := by
      intro h
      have hd : p ∣ m + 1 := (ZMod.natCast_eq_zero_iff (m + 1) p).mp h
      have := Nat.le_of_dvd (by omega : 0 < m + 1) hd
      omega
    simpa using h0
  have hjv : ((j : ZMod p) + 1) ≠ 0 := by
    rw [hj]; exact hne
  have hi : (((⟨m+1, by omega⟩ : Fin k)) : ZMod p) = (j : ZMod p) + 1 := by
    have hA : (((⟨m+1, by omega⟩ : Fin k)) : ℕ) = m + 1 := rfl
    have hB : (j : ℕ) = m := by rw [hj]
    rw [hA, hB]
    push_cast
    ring
  rw [phiZ_apply, phiZ_apply, h1, h2, hi]
  have hdiv : ((j : ZMod p) + 1) * ((c - y j) / ((j : ZMod p) + 1)) = (c - y j) :=
    mul_div_cancel₀ (c - y j) hjv
  rw [mul_add, hdiv]
  ring


/-- `φ_{m+1}` is independent of the `m`-th coordinate of the vector, in the precise form
required by the Green–Tao iteration. -/
lemma phiZ_app_cons {k : ℕ} (hkp : k ≤ p) (m : ℕ) (hm : m + 2 ≤ k)
    (u : Fin m → ZMod p) (z z' : ZMod p) (w : Fin (k-1-(m+1)) → ZMod p) :
    phiZ (p := p) k ⟨m+1, by omega⟩ (app k (m+1) (by omega) (Fin.snoc u z) w)
      = phiZ (p := p) k ⟨m+1, by omega⟩ (app k (m+1) (by omega) (Fin.snoc u z') w) := by
  have hmk : m < k - 1 := by omega
  have hy : app k (m+1) (by omega) (Fin.snoc u z) w
      = Function.update (app k (m+1) (by omega) (Fin.snoc u z') w) ⟨m, hmk⟩ z := by
    funext j
    by_cases hj : j = ⟨m, hmk⟩
    · subst hj
      rw [Function.update_self, app_apply, dif_pos (show m < m + 1 by omega)]
      rw [show (⟨m, by omega⟩ : Fin (m+1)) = Fin.last m from Fin.ext rfl]
      exact Fin.snoc_last (α := fun _ : Fin (m+1) => ZMod p) z u
    · rw [Function.update_of_ne hj]
      by_cases hlt : j.val < m + 1
      · rw [app_apply, app_apply, dif_pos hlt, dif_pos hlt]
        have hjm : j.val < m := by
          rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with h | h
          · exact h
          · exact absurd (Fin.ext h) hj
        rw [show (⟨j.val, hlt⟩ : Fin (m+1)) = Fin.castSucc ⟨j.val, hjm⟩ from Fin.ext rfl,
          Fin.snoc_castSucc (α := fun _ : Fin (m+1) => ZMod p),
          Fin.snoc_castSucc (α := fun _ : Fin (m+1) => ZMod p)]
      · rw [app_apply, app_apply, dif_neg hlt, dif_neg hlt]
  rw [hy]
  exact phiZ_update hkp m hm _ z

end ZModReparam


section Cover
variable {p : ℕ} [Fact p.Prime]

private lemma two_ne_zero_zmod (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
  · exact (Fact.out : p.Prime).one_lt.ne' h1
  · exact hp2 h1

private def consZ (n : ℕ) : ZMod p × (Fin n → ZMod p) ≃ (Fin (n+1) → ZMod p) where
  toFun q := Fin.cons q.1 q.2
  invFun u := (u 0, Fin.tail u)
  left_inv q := by obtain ⟨a,b⟩ := q; simp
  right_inv u := Fin.cons_self_tail u

@[simp] private lemma consZ_apply (n : ℕ) (q : ZMod p × (Fin n → ZMod p)) :
    consZ (p:=p) n q = Fin.cons q.1 q.2 := rfl

private lemma sum_cover_aux (m : ℕ) (hp2 : p ≠ 2) (G0 : ZMod p → ZMod p → ℝ) :
    (∑ u : Fin (m+2) → ZMod p, G0 (∑ t, u t) (∑ t, u t / ((t : ZMod p) + 1)))
      = (p : ℝ)^m * ∑ q : ZMod p × ZMod p, G0 q.1 q.2 := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod p hp2
  rw [← Equiv.sum_comp (consZ (p:=p) (m+1))
        (fun u : Fin (m+2) → ZMod p => G0 (∑ t, u t) (∑ t, u t / ((t : ZMod p) + 1)))]
  simp only [consZ_apply]
  have hA : ∀ q : ZMod p × (Fin (m+1) → ZMod p),
      (∑ t : Fin (m+2), Fin.cons q.1 q.2 t) = q.1 + ∑ t : Fin (m+1), q.2 t :=
    fun q => Fin.sum_cons q.1 q.2
  have hB : ∀ q : ZMod p × (Fin (m+1) → ZMod p),
      (∑ t : Fin (m+2), (Fin.cons q.1 q.2 : Fin (m+2) → ZMod p) t / ((t : ZMod p) + 1))
        = q.1 + ∑ t : Fin (m+1), q.2 t / ((t : ZMod p) + 2) := by
    intro q
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.val_zero, Nat.cast_zero, zero_add, div_one]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    rw [Fin.cons_succ, Fin.val_succ]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun q _ => by rw [hA q, hB q])]
  set S : (Fin (m+1) → ZMod p) → ZMod p := fun w => ∑ t, w t with hS
  set T : (Fin (m+1) → ZMod p) → ZMod p := fun w => ∑ t, w t / ((t : ZMod p) + 2) with hT
  set d : Fin (m+1) → ZMod p := fun t => 1 / ((t : ZMod p) + 2) - 1 with hd
  have hTS : ∀ q2 : Fin (m+1) → ZMod p, T q2 - S q2 = ∑ t : Fin (m+1), d t * q2 t := by
    intro q2
    simp only [hS, hT, hd]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  let e : ZMod p × (Fin (m+1) → ZMod p) ≃ ZMod p × (Fin (m+1) → ZMod p) :=
    { toFun q := (q.1 - S q.2, q.2)
      invFun q := (q.1 + S q.2, q.2)
      left_inv := by intro q; simp
      right_inv := by intro q; simp }
  have e_apply : ∀ q : ZMod p × (Fin (m+1) → ZMod p), e q = (q.1 - S q.2, q.2) := fun q => rfl
  rw [← Equiv.sum_comp e (fun q : ZMod p × (Fin (m+1) → ZMod p) =>
        G0 (q.1 + S q.2) (q.1 + T q.2))]
  simp only [e_apply]
  have hpoint : ∀ q : ZMod p × (Fin (m+1) → ZMod p),
      G0 ((q.1 - S q.2) + S q.2) ((q.1 - S q.2) + T q.2)
        = G0 q.1 (q.1 + ∑ t : Fin (m+1), d t * q.2 t) := by
    intro q
    rw [sub_add_cancel]
    congr 1
    rw [← hTS q.2]
    ring
  rw [Finset.sum_congr rfl (fun q _ => hpoint q)]
  rw [Fintype.sum_prod_type]
  have hd0 : d ⟨0, by omega⟩ ≠ 0 := by
    have hval : d ⟨0, by omega⟩ = -((2 : ZMod p)⁻¹) := by
      simp only [hd, Fin.val_zero, Nat.cast_zero, zero_add]
      field_simp
      ring
    rw [hval]
    exact neg_ne_zero.mpr (inv_ne_zero h2)
  have hSWC : ∀ w : ZMod p,
      (∑ q2 : Fin (m+1) → ZMod p, G0 w (w + ∑ t : Fin (m+1), d t * q2 t))
        = (p : ℝ)^m * ∑ v : ZMod p, G0 w (w + v) := by
    intro w
    exact Commons.Combinatorics.Additive.AP.sum_weighted_coordinates (p := p) (n := m+1)
      (by omega) d ⟨⟨0, by omega⟩, hd0⟩ (fun v => G0 w (w + v))
  rw [Finset.sum_congr rfl (fun w _ => hSWC w)]
  rw [← Finset.mul_sum]
  congr 1
  rw [Fintype.sum_prod_type (f := fun q : ZMod p × ZMod p => G0 q.1 q.2)]
  apply Finset.sum_congr rfl
  intro w _
  exact Equiv.sum_comp (Equiv.addLeft w) (fun b => G0 w b)


/-- The cover identity in the `k`-indexed form used by the Green–Tao reparametrisation. -/
lemma sum_cover {k : ℕ} (hk : 3 ≤ k) (hkp : k ≤ p) (G0 : ZMod p → ZMod p → ℝ) :
    (∑ u : Fin (k-1) → ZMod p, G0 (∑ t, u t) (∑ t, u t / ((t : ZMod p) + 1)))
      = (p : ℝ)^(k-3) * ∑ q : ZMod p × ZMod p, G0 q.1 q.2 := by
  have hk3 : k - 1 = (k - 3) + 2 := by omega
  have hp2 : p ≠ 2 := by omega
  rw [hk3]
  exact sum_cover_aux (p := p) (k - 3) hp2 G0

end Cover

section Assembly
variable {p : ℕ} [Fact p.Prime]

private lemma card_arrow (n : ℕ) :
    (Fintype.card (Fin n → ZMod p) : ℝ) = (p : ℝ)^n := by
  rw [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow]

private lemma inv_mul_cancel_zmod_pow (k : ℕ) (hk : 3 ≤ k) :
    (p : ℝ)^2 * ((p : ℝ)^(k-1))⁻¹ * (p : ℝ)^(k-3) = 1 := by
  have hpk : (2 : ℕ) + (k - 3) = k - 1 := by omega
  have hpow : (p : ℝ)^2 * (p : ℝ)^(k-3) = (p : ℝ)^(k-1) := by
    rw [← pow_add, hpk]
  have hpne : (p : ℝ)^(k-1) ≠ 0 := by
    apply pow_ne_zero
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  calc (p : ℝ)^2 * ((p : ℝ)^(k-1))⁻¹ * (p : ℝ)^(k-3)
      = ((p : ℝ)^(k-1))⁻¹ * ((p : ℝ)^2 * (p : ℝ)^(k-3)) := by ring
    _ = ((p : ℝ)^(k-1))⁻¹ * (p : ℝ)^(k-1) := by rw [hpow]
    _ = 1 := inv_mul_cancel₀ hpne

/-- The Green–Tao reparametrisation: the arithmetic-progression sum equals `p²` times the
last stage quantity. -/
lemma Jf_last_eq {k : ℕ} (hk : 3 ≤ k) (hkp : k ≤ p) (f : Fin k → ZMod p → ℝ) :
    (∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, f i (x + ((i : ℕ) : ZMod p) * r))
      = (p : ℝ)^2 * Jf (ZMod p) k (phiZ (p := p) k) f (k-1) (by omega) := by
  have hcard : (Fintype.card (Fin (k-1) → ZMod p) : ℝ) = (p : ℝ)^(k-1) := card_arrow _
  have hsum : (∑ u : Fin (k-1) → ZMod p, ∏ i : Fin k, f i (phiZ (p:=p) k i u))
      = (p : ℝ)^(k-3) * (∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k,
          f i (x + ((i:ℕ):ZMod p) * r)) := by
    have hcov := sum_cover (p:=p) hk hkp (fun a b => ∏ i : Fin k, f i (a - (i : ZMod p) * b))
    have hL : (∑ u : Fin (k-1) → ZMod p, ∏ i : Fin k, f i (phiZ (p:=p) k i u))
        = (∑ u : Fin (k-1) → ZMod p, ∏ i : Fin k, f i ((∑ t, u t)
            - (i : ZMod p) * (∑ t, u t / ((t : ZMod p) + 1)))) := by
      apply Finset.sum_congr rfl; intro u _
      apply Finset.prod_congr rfl; intro i _
      rw [phiZ_apply]
    rw [hL, hcov]
    congr 1
    rw [Fintype.sum_prod_type (f := fun q : ZMod p × ZMod p =>
      ∏ i : Fin k, f i (q.1 - (i : ZMod p) * q.2))]
    apply Finset.sum_congr rfl; intro x _
    rw [← Equiv.sum_comp (Equiv.neg (ZMod p))
      (fun r : ZMod p => ∏ i : Fin k, f i (x + (i:ZMod p) * r))]
    apply Finset.sum_congr rfl; intro b _
    apply Finset.prod_congr rfl; intro i _
    congr 1
    rw [show (Equiv.neg (ZMod p)) b = -b from rfl]
    ring
  rw [Jf_last (k := k) (by omega) (phiZ (p := p) k) f (by omega)]
  unfold av
  rw [hcard, hsum]
  have hkey := inv_mul_cancel_zmod_pow (p := p) k hk
  have hassoc : (p:ℝ)^2 * ((p:ℝ)^(k-1))⁻¹ * (p:ℝ)^(k-3)
        * (∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, f i (x + ((i:ℕ):ZMod p) * r))
      = (p:ℝ)^2 * (((p:ℝ)^(k-1))⁻¹ * ((p:ℝ)^(k-3)
        * (∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, f i (x + ((i:ℕ):ZMod p) * r)))) := by ring
  rw [← hassoc, hkey, one_mul]

end Assembly

section Assembly2
variable {p : ℕ} [Fact p.Prime]

private lemma coeff_eq_one (k : ℕ) (hk : 3 ≤ k) :
    (p : ℝ)^k * ((p : ℝ)^(k-1))⁻¹ * ((p : ℝ)^(k-1))⁻¹ * (p : ℝ)^(k-2) = 1 := by
  have hpne : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hAne : (p : ℝ)^(k-1) ≠ 0 := pow_ne_zero _ hpne
  have hk1 : k = (k-1)+1 := by omega
  have hpowk : (p : ℝ)^k = (p : ℝ)^(k-1) * p := by
    conv_lhs => rw [hk1]
    rw [pow_succ]
  have hk2 : k - 1 = (k - 2) + 1 := by omega
  have hpk2 : (p : ℝ)^(k-1) = (p : ℝ)^(k-2) * p := by rw [hk2, pow_succ]
  have hval : (p : ℝ)^(k-2) = (p : ℝ)^(k-1) * (p : ℝ)⁻¹ := by
    rw [hpk2, mul_assoc, mul_inv_cancel₀ hpne, mul_one]
  rw [hpowk, hval]
  field_simp

/-- The cube-sum endpoint: the cube sum of `f 0` equals `p^k` times the stage-`0` quantity. -/
lemma Jf_zero_eq {k : ℕ} (hk : 3 ≤ k) (hkp : k ≤ p) (f : Fin k → ZMod p → ℝ) :
    (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
        ∏ ω : Fin (k-1) → Bool, f ⟨0, by omega⟩ (x + ∑ i : Fin (k-1), if ω i then h i else 0))
      = (p : ℝ)^k * Jf (ZMod p) k (phiZ (p := p) k) f 0 (by omega) := by
  have hcard : (Fintype.card (Fin (k-1) → ZMod p) : ℝ) = (p : ℝ)^(k-1) := card_arrow _
  have hSin : ∀ (v y' : Fin (k-1) → ZMod p),
      (∏ ω : Fin (k-1) → Bool, ∏ i : Fin 1, f ⟨i.val, by omega⟩
          (phiZ (p:=p) k ⟨i.val, by omega⟩ (fun j => if ω j then y' j else v j)))
        = (∏ ω : Fin (k-1) → Bool, f ⟨0, by omega⟩ (∑ j, if ω j then y' j else v j)) := by
    intro v y'
    apply Finset.prod_congr rfl; intro ω _
    rw [Fin.prod_univ_one]
    congr 1
    rw [phiZ_apply]
    simp
  have hmain : (∑ v : Fin (k-1) → ZMod p, ∑ y' : Fin (k-1) → ZMod p,
        ∏ ω : Fin (k-1) → Bool, f ⟨0, by omega⟩ (∑ j, if ω j then y' j else v j))
      = (p:ℝ)^(k-2) * (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
          ∏ ω : Fin (k-1) → Bool, f ⟨0, by omega⟩ (x + ∑ j, if ω j then h j else 0)) := by
    have hstep1 : (∑ v : Fin (k-1) → ZMod p, ∑ y' : Fin (k-1) → ZMod p,
          ∏ ω : Fin (k-1) → Bool, f ⟨0, by omega⟩ (∑ j, if ω j then y' j else v j))
        = (∑ v : Fin (k-1) → ZMod p, ∑ h : Fin (k-1) → ZMod p,
          ∏ ω : Fin (k-1) → Bool, f ⟨0, by omega⟩
            ((∑ j, v j) + ∑ j, if ω j then h j else 0)) := by
      apply Finset.sum_congr rfl; intro v _
      rw [← Equiv.sum_comp (Equiv.addLeft v) (fun y' : Fin (k-1) → ZMod p =>
        ∏ ω : Fin (k-1) → Bool, f ⟨0, by omega⟩ (∑ j, if ω j then y' j else v j))]
      apply Finset.sum_congr rfl; intro h _
      apply Finset.prod_congr rfl; intro ω _
      congr 1
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j _
      by_cases hj : ω j <;> simp [hj, Pi.add_apply]
    have hswc : ∀ h : Fin (k-1) → ZMod p,
        (∑ v : Fin (k-1) → ZMod p, ∏ ω : Fin (k-1) → Bool,
            f ⟨0, by omega⟩ ((∑ j, v j) + ∑ j, if ω j then h j else 0))
          = (p:ℝ)^(k-2) * (∑ x : ZMod p, ∏ ω : Fin (k-1) → Bool,
              f ⟨0, by omega⟩ (x + ∑ j, if ω j then h j else 0)) := by
      intro h
      have h' := Commons.Combinatorics.Additive.AP.sum_weighted_coordinates (p:=p) (n:=k-1)
        (by omega) (fun _ : Fin (k-1) => (1 : ZMod p)) ⟨⟨0, by omega⟩, by simp⟩
        (fun x : ZMod p => ∏ ω : Fin (k-1) → Bool,
          f ⟨0, by omega⟩ (x + ∑ j, if ω j then h j else 0))
      simp only [one_mul] at h'
      rw [show k - 1 - 1 = k - 2 from by omega] at h'
      exact h'
    rw [hstep1, Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun h _ => hswc h)]
    rw [← Finset.mul_sum]
  rw [Jf_zero (k := k) (by omega) (phiZ (p := p) k) f (by omega)]
  simp only [av]
  rw [hcard]
  rw [show (∑ v : Fin (k-1) → ZMod p, ((p:ℝ)^(k-1))⁻¹ * (∑ y' : Fin (k-1) → ZMod p,
        ∏ ω : Fin (k-1) → Bool, ∏ i : Fin 1, f ⟨i.val, by omega⟩
          (phiZ (p:=p) k ⟨i.val, by omega⟩ (fun j => if ω j then y' j else v j))))
      = ((p:ℝ)^(k-1))⁻¹ * ((p:ℝ)^(k-2) * (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
        ∏ ω : Fin (k-1) → Bool, f ⟨0, by omega⟩ (x + ∑ i : Fin (k-1),
          if ω i then h i else 0))) from by
      rw [← Finset.mul_sum]
      congr 1
      rw [show (∑ v : Fin (k-1) → ZMod p, ∑ y' : Fin (k-1) → ZMod p,
          ∏ ω : Fin (k-1) → Bool, ∏ i : Fin 1, f ⟨i.val, by omega⟩
            (phiZ (p:=p) k ⟨i.val, by omega⟩ (fun j => if ω j then y' j else v j)))
          = (∑ v : Fin (k-1) → ZMod p, ∑ y' : Fin (k-1) → ZMod p,
            ∏ ω : Fin (k-1) → Bool, f ⟨0, by omega⟩ (∑ j, if ω j then y' j else v j)) from by
        apply Finset.sum_congr rfl; intro v _
        apply Finset.sum_congr rfl; intro y' _
        exact hSin v y']
      exact hmain]
  have hcoeff : (p : ℝ)^k * ((p : ℝ)^(k-1))⁻¹ * ((p : ℝ)^(k-1))⁻¹ * (p : ℝ)^(k-2) = 1 :=
    coeff_eq_one k hk
  have hassoc : (p : ℝ)^k * ((p : ℝ)^(k-1))⁻¹ * ((p : ℝ)^(k-1))⁻¹ * (p : ℝ)^(k-2)
        * (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, ∏ ω : Fin (k-1) → Bool,
            f ⟨0, by omega⟩ (x + ∑ i : Fin (k-1), if ω i then h i else 0))
      = (p : ℝ)^k * (((p : ℝ)^(k-1))⁻¹ * (((p : ℝ)^(k-1))⁻¹ * ((p : ℝ)^(k-2)
        * (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, ∏ ω : Fin (k-1) → Bool,
            f ⟨0, by omega⟩ (x + ∑ i : Fin (k-1), if ω i then h i else 0))))) := by ring
  rw [← hassoc, hcoeff, one_mul]

end Assembly2
end GVNgen

namespace Commons.Combinatorics.Additive.Gowers

open scoped BigOperators

private def fin1Equiv (α : Type*) : (Fin 1 → α) ≃ α where
  toFun f := f 0
  invFun a := fun _ => a
  left_inv f := by funext i; rw [show i = 0 from Subsingleton.elim i 0]
  right_inv a := rfl

@[simp] private lemma fin1Equiv_apply (α : Type*) (f : Fin 1 → α) : fin1Equiv α f = f 0 := rfl

/-- **Generalised von Neumann inequality (Green–Tao, §5).**  For a prime `p`, `2 ≤ k ≤ p`, and
functions `f 0, …, f (k-1) : ZMod p → ℝ` whose values away from index `0` are bounded by `1`,

  `(∑_x ∑_r ∏_i f i (x + i·r))^(2^(k-1)) ≤ p^(2^k - k) · (cube sum of f 0)`,

where the cube sum is `∑_h ∑_x ∏_{ω : Fin (k-1) → Bool} f 0 (x + ω·h)`. -/
theorem gvn_general (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 2 ≤ k) (hkp : k ≤ p)
    (f : Fin k → ZMod p → ℝ)
    (hf : ∀ i : Fin k, (i : ℕ) ≠ 0 → ∀ x : ZMod p, |f i x| ≤ 1) :
    (∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, f i (x + ((i : ℕ) : ZMod p) * r)) ^ (2 ^ (k - 1))
      ≤ (p : ℝ) ^ (2 ^ k - k) *
        (∑ h : Fin (k - 1) → ZMod p, ∑ x : ZMod p,
          ∏ ω : Fin (k - 1) → Bool,
            f ⟨0, by omega⟩ (x + ∑ i : Fin (k - 1), if ω i then h i else 0)) := by
  rcases eq_or_lt_of_le hk with hk2 | hklt
  · -- k = 2
    subst hk2
    have hL : (∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin 2, f i (x + ((i : ℕ) : ZMod p) * r))
        = (∑ x : ZMod p, f ⟨0, by omega⟩ x) * (∑ r : ZMod p, f ⟨1, by omega⟩ r) := by
      calc (∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin 2, f i (x + ((i : ℕ) : ZMod p) * r))
          = ∑ x : ZMod p, ∑ r : ZMod p,
              f ⟨0, by omega⟩ x * f ⟨1, by omega⟩ (x + r) := by
              apply Finset.sum_congr rfl; intro x _
              apply Finset.sum_congr rfl; intro r _
              rw [Fin.prod_univ_two]; simp
        _ = ∑ x : ZMod p, f ⟨0, by omega⟩ x * (∑ y : ZMod p, f ⟨1, by omega⟩ y) := by
              apply Finset.sum_congr rfl; intro x _
              rw [Finset.mul_sum]
              exact Equiv.sum_comp (Equiv.addLeft x)
                (fun y : ZMod p => f ⟨0, by omega⟩ x * f ⟨1, by omega⟩ y)
        _ = (∑ x : ZMod p, f ⟨0, by omega⟩ x) * (∑ y : ZMod p, f ⟨1, by omega⟩ y) := by
              rw [Finset.sum_mul]
    have hinner : ∀ (x : ZMod p) (h : Fin 1 → ZMod p),
        (∏ ω : Fin 1 → Bool, f ⟨0, by omega⟩ (x + ∑ i : Fin 1, if ω i then h i else 0))
          = f ⟨0, by omega⟩ x * f ⟨0, by omega⟩ (x + h 0) := by
      intro x h
      rw [show (∏ ω : Fin 1 → Bool,
            f ⟨0, by omega⟩ (x + ∑ i : Fin 1, if ω i then h i else 0))
          = ∏ b : Bool, f ⟨0, by omega⟩ (x + (if b then h 0 else 0)) from by
        rw [Fintype.prod_equiv (fin1Equiv Bool)
          (fun ω : Fin 1 → Bool => f ⟨0, by omega⟩ (x + ∑ i : Fin 1, if ω i then h i else 0))
          (fun b : Bool => f ⟨0, by omega⟩ (x + (if b then h 0 else 0)))
          (fun ω => by rw [fin1Equiv_apply]; congr 1; rw [Fin.sum_univ_one])]]
      rw [Fintype.prod_bool]; simp [mul_comm]
    have hR : (∑ h : Fin (2-1) → ZMod p, ∑ x : ZMod p,
          ∏ ω : Fin (2-1) → Bool,
            f ⟨0, by omega⟩ (x + ∑ i : Fin (2-1), if ω i then h i else 0))
        = (∑ x : ZMod p, f ⟨0, by omega⟩ x)^2 := by
      have h1 : (∑ h : Fin 1 → ZMod p, ∑ x : ZMod p, ∏ ω : Fin 1 → Bool,
            f ⟨0, by omega⟩ (x + ∑ i : Fin 1, if ω i then h i else 0))
          = ∑ h : Fin 1 → ZMod p, ∑ x : ZMod p,
              f ⟨0, by omega⟩ x * f ⟨0, by omega⟩ (x + h 0) := by
        apply Finset.sum_congr rfl; intro h _
        apply Finset.sum_congr rfl; intro x _
        exact hinner x h
      rw [h1]
      rw [Fintype.sum_equiv (fin1Equiv (ZMod p))
            (fun h : Fin 1 → ZMod p => ∑ x : ZMod p,
              f ⟨0, by omega⟩ x * f ⟨0, by omega⟩ (x + h 0))
            (fun y : ZMod p => ∑ x : ZMod p,
              f ⟨0, by omega⟩ x * f ⟨0, by omega⟩ (x + y))
            (fun h => by rw [fin1Equiv_apply])]
      rw [Finset.sum_comm]
      exact Commons.Combinatorics.Additive.Gowers.cube_one_sum (f ⟨0, by omega⟩)
    have hS1 : (∑ r : ZMod p, f ⟨1, by omega⟩ r)^2 ≤ (p : ℝ)^2 := by
      have h1 : |∑ r : ZMod p, f ⟨1, by omega⟩ r| ≤ ∑ r, |f ⟨1, by omega⟩ r| :=
        Finset.abs_sum_le_sum_abs _ _
      have h2 : (∑ r : ZMod p, |f ⟨1, by omega⟩ r|) ≤ (p : ℝ) := by
        calc ∑ r, |f ⟨1, by omega⟩ r| ≤ ∑ _r : ZMod p, (1 : ℝ) :=
              Finset.sum_le_sum (fun r _ => hf ⟨1, by omega⟩ (by simp) r)
          _ = (p : ℝ) := by
              rw [Finset.sum_const, Finset.card_univ, ZMod.card p, nsmul_eq_mul, mul_one]
      rw [← sq_abs (∑ r : ZMod p, f ⟨1, by omega⟩ r)]
      exact pow_le_pow_left₀ (abs_nonneg _) (h1.trans h2) 2
    rw [show 2 ^ (2 - 1) = 2 from by norm_num, show 2 ^ 2 - 2 = 2 from by norm_num]
    rw [hL, hR]
    calc ((∑ x : ZMod p, f ⟨0, by omega⟩ x) * (∑ r : ZMod p, f ⟨1, by omega⟩ r))^2
        = (∑ x : ZMod p, f ⟨0, by omega⟩ x)^2 * (∑ r : ZMod p, f ⟨1, by omega⟩ r)^2 := by ring
      _ ≤ (∑ x : ZMod p, f ⟨0, by omega⟩ x)^2 * (p : ℝ)^2 :=
          mul_le_mul_of_nonneg_left hS1 (sq_nonneg _)
      _ = (p : ℝ)^2 * (∑ x : ZMod p, f ⟨0, by omega⟩ x)^2 := by ring
  · -- 3 ≤ k
    have hk3 : 3 ≤ k := hklt
    have hmain := GVNgen.Jf_pow_le (X := ZMod p) (k := k) (by omega) (GVNgen.phiZ (p := p) k) f hf
        (fun m hm u z z' w => GVNgen.phiZ_app_cons hkp m hm u z z' w) (k-1) (by omega)
    have hlast := GVNgen.Jf_last_eq (p := p) hk3 hkp f
    have hzero := GVNgen.Jf_zero_eq (p := p) hk3 hkp f
    rw [hlast, hzero]
    set Jk : ℝ := GVNgen.Jf (ZMod p) k (GVNgen.phiZ (p := p) k) f (k-1) (by omega) with hJk
    set J0 : ℝ := GVNgen.Jf (ZMod p) k (GVNgen.phiZ (p := p) k) f 0 (by omega) with hJ0
    have hp0 : (0 : ℝ) ≤ p := by positivity
    have h2k : 2 * 2^(k-1) = 2^k := by
      rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
    have hpow : (p : ℝ)^(2^k) = (p : ℝ)^(2^k - k) * (p : ℝ)^k := by
      conv_lhs => rw [← Nat.sub_add_cancel (le_of_lt (Nat.lt_two_pow_self (n := k)))]
      rw [pow_add]
    calc ((p : ℝ)^2 * Jk) ^ (2 ^ (k - 1))
        = (p : ℝ)^(2^k) * Jk ^ (2 ^ (k - 1)) := by
          rw [mul_pow, ← pow_mul, h2k]
      _ ≤ (p : ℝ)^(2^k) * J0 :=
          mul_le_mul_of_nonneg_left hmain (pow_nonneg hp0 _)
      _ = (p : ℝ)^(2^k - k) * ((p : ℝ)^k * J0) := by rw [hpow]; ring

end Commons.Combinatorics.Additive.Gowers
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.Combinatorics.Additive.Gowers.bilinear_sum_decouple

open scoped BigOperators

/-!
# One-digit Gowers–Cauchy–Schwarz at an arbitrary coordinate

This file proves `gcs_digit_step_at`: the single-digit step of the
Gowers–Cauchy–Schwarz inequality (Green–Tao 2008, §5, inequality (gcz)),
splitting the `d`-dimensional Gowers cube sum of a family of functions along an
arbitrary coordinate `ℓ : Fin d` and applying Cauchy–Schwarz in the shift
variable at that coordinate.

The proof splits the cube sum at the **last** coordinate (where the
`Fin.snoc`/`Fin.init` API is available), then transports the result to an
arbitrary `ℓ` by reindexing the cube sum along the permutation
`Equiv.swap ℓ (Fin.last _)`.  All the auxiliary material lives in the namespace
`GCSDigitAux`; only the requested theorem is added to
`Commons.Combinatorics.Additive.Gowers`.
-/

namespace GCSDigitAux

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-! ## Cube sums over a general finite index type (used for reindexing) -/

/-- Cone point of a cube over an arbitrary finite index type. -/
def cpt {I : Type*} [Fintype I] (x : G) (h : I → G) (ω : I → Bool) : G :=
  x + ∑ i, (if ω i then h i else 0)

/-- Gowers cube sum of a family over an arbitrary finite index type. -/
def cubeSumI (I : Type*) [Fintype I] [DecidableEq I] (F : (I → Bool) → G → ℝ) : ℝ :=
  ∑ h : I → G, ∑ x : G, ∏ ω : I → Bool, F ω (cpt x h ω)

section
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Reindexing `(J → Bool)` along an equivalence by precomposition. -/
def arrowCompEquiv (e : I ≃ J) : (J → Bool) ≃ (I → Bool) where
  toFun ω := ω ∘ e
  invFun ω := ω ∘ e.symm
  left_inv := by intro ω; funext j; simp
  right_inv := by intro ω; funext i; simp

@[simp] lemma arrowCompEquiv_apply (e : I ≃ J) (ω : J → Bool) :
    arrowCompEquiv e ω = ω ∘ e := rfl

/-- Reindexing `(I → G)` along an equivalence by precomposition. -/
def arrowGEquiv (e : I ≃ J) : (I → G) ≃ (J → G) where
  toFun h := h ∘ e.symm
  invFun h := h ∘ e
  left_inv := by intro h; funext i; simp
  right_inv := by intro h; funext j; simp

@[simp] lemma arrowGEquiv_apply (e : I ≃ J) (h : I → G) :
    arrowGEquiv e h = h ∘ e.symm := rfl

/-- Reindexing the summation over `I → G` along an equivalence. -/
lemma sum_arrow_reindex (e : I ≃ J) (f : (I → G) → ℝ) :
    (∑ h : I → G, f h) = ∑ h' : J → G, f (h' ∘ e) := by
  refine Fintype.sum_equiv (arrowGEquiv e) f (fun h' => f (h' ∘ e)) ?_
  intro h
  congr 1
  funext i
  simp

/-- Reindexing the product over `I → Bool` along an equivalence. -/
lemma prod_arrow_reindex (e : I ≃ J) (f : (I → Bool) → ℝ) :
    (∏ ω' : J → Bool, f (ω' ∘ e)) = ∏ ω : I → Bool, f ω := by
  refine Fintype.prod_equiv (arrowCompEquiv e) (fun ω' : J → Bool => f (ω' ∘ e)) f ?_
  intro ω'
  simp

/-- **Reindexing invariance of the cube sum** (general finite index type). -/
lemma cubeSumI_reindex (e : I ≃ J) (F : (I → Bool) → G → ℝ) :
    cubeSumI J (fun ω' : J → Bool => F (ω' ∘ e)) = cubeSumI I F := by
  unfold cubeSumI cpt
  dsimp only
  have h1 : (∑ h' : J → G, ∑ x : G, ∏ ω' : J → Bool,
        F (ω' ∘ e) (x + ∑ j : J, (if ω' j then h' j else 0)))
      = ∑ h : I → G, ∑ x : G, ∏ ω' : J → Bool,
        F (ω' ∘ e) (x + ∑ j : J, (if ω' j then h (e.symm j) else 0)) :=
    sum_arrow_reindex e.symm (f := fun h' : J → G => ∑ x : G, ∏ ω' : J → Bool,
      F (ω' ∘ e) (x + ∑ j : J, (if ω' j then h' j else 0)))
  rw [h1]
  apply Finset.sum_congr rfl; intro h _
  apply Finset.sum_congr rfl; intro x _
  refine Fintype.prod_equiv (arrowCompEquiv e)
    (fun ω' : J → Bool => F (ω' ∘ e) (x + ∑ j : J, (if ω' j then h (e.symm j) else 0)))
    (fun ω : I → Bool => F ω (x + ∑ i : I, (if ω i then h i else 0))) ?_
  intro ω'
  have harg : (arrowCompEquiv e) ω' = ω' ∘ e := rfl
  rw [harg]
  have hsum : (∑ j : J, (if ω' j then h (e.symm j) else 0))
      = (∑ i : I, (if (ω' ∘ e) i then h i else 0)) := by
    have h2 := Equiv.sum_comp e.symm (fun i : I => (if (ω' ∘ e) i then h i else 0))
    rw [← h2]
    apply Finset.sum_congr rfl; intro j _
    simp
  rw [hsum]

end

/-! ## Cube sums indexed by `Fin d` -/

/-- Cube point of the `d`-dimensional cube: `x + ∑ i, ω i • h i`. -/
def cubePt (d : ℕ) (x : G) (h : Fin d → G) (ω : Fin d → Bool) : G :=
  x + ∑ i : Fin d, (if ω i then h i else 0)

/-- The `d`-dimensional Gowers cube sum of a family of functions. -/
def cubeSum (d : ℕ) (F : (Fin d → Bool) → G → ℝ) : ℝ :=
  ∑ h : Fin d → G, ∑ x : G, ∏ ω : Fin d → Bool, F ω (cubePt d x h ω)

/-- The general-index cube sum at `Fin d` agrees with the `Fin`-indexed one. -/
lemma gen_cubeSum_fin (d : ℕ) (F : (Fin d → Bool) → G → ℝ) :
    cubeSumI (Fin d) F = cubeSum d F := rfl

/-- Reindexing invariance of the cube sum, in the `Fin`-indexed form. -/
lemma cubeSum_reindex_fin (d : ℕ) (π : Fin d ≃ Fin d) (F : (Fin d → Bool) → G → ℝ) :
    cubeSum d (fun ω' => F (ω' ∘ π)) = cubeSum d F := by
  have h := cubeSumI_reindex π F
  rwa [gen_cubeSum_fin, gen_cubeSum_fin] at h

/-! ## Splitting off the last coordinate -/

/-- Splitting the cube point along the last coordinate. -/
lemma cubePt_snoc (n : ℕ) (x : G) (h : Fin n → G) (hl : G) (ω : Fin n → Bool) (b : Bool) :
    cubePt (n+1) x (Fin.snoc h hl) (Fin.snoc ω b)
      = cubePt n (x + (if b then hl else 0)) h ω := by
  simp only [cubePt, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  abel

/-- Splitting `Fin (n+1) → α` into its last coordinate and the rest. -/
def snocEquiv (n : ℕ) (α : Type*) : (Fin n → α) × α ≃ (Fin (n+1) → α) where
  toFun p := Fin.snoc p.1 p.2
  invFun f := (Fin.init f, f (Fin.last n))
  left_inv := fun p => by simp [Fin.init_snoc, Fin.snoc_last]
  right_inv := fun f => Fin.snoc_init_self f

/-- Casting a last-coordinate split: `α × (Fin n → α) ≃ (Fin (n+1) → α)` by `snoc`. -/
def snocBoolEquiv (n : ℕ) (α : Type*) : α × (Fin n → α) ≃ (Fin (n+1) → α) where
  toFun p := Fin.snoc p.2 p.1
  invFun f := (f (Fin.last n), Fin.init f)
  left_inv := fun p => by simp [Fin.init_snoc, Fin.snoc_last]
  right_inv := fun f => Fin.snoc_init_self f

/-- Product over `Fin (n+1) → Bool` split by the last coordinate. -/
lemma prod_snoc_bool (n : ℕ) (F : (Fin (n+1) → Bool) → ℝ) :
    (∏ ω : Fin (n+1) → Bool, F ω) = ∏ b : Bool, ∏ σ : Fin n → Bool, F (Fin.snoc σ b) := by
  calc (∏ ω : Fin (n+1) → Bool, F ω)
      = ∏ p : Bool × (Fin n → Bool), F (Fin.snoc p.2 p.1) :=
        (Fintype.prod_equiv (snocBoolEquiv n Bool) _ _ (fun p => rfl)).symm
    _ = ∏ b : Bool, ∏ σ : Fin n → Bool, F (Fin.snoc σ b) := Fintype.prod_prod_type _

/-- Sum over `Fin (n+1) → G` split by the last coordinate. -/
lemma sum_snoc (n : ℕ) (F : (Fin (n+1) → G) → ℝ) :
    (∑ h : Fin (n+1) → G, F h) = ∑ hl : G, ∑ h : Fin n → G, F (Fin.snoc h hl) := by
  calc (∑ h : Fin (n+1) → G, F h)
      = ∑ p : (Fin n → G) × G, F (Fin.snoc p.1 p.2) :=
        (Fintype.sum_equiv (snocEquiv n G) _ _ (fun p => rfl)).symm
    _ = ∑ hl : G, ∑ h : Fin n → G, F (Fin.snoc h hl) := by
        rw [Fintype.sum_prod_type]
        exact Finset.sum_comm

/-- Splitting the product over the vertices of the `(n+1)`-cube into the
`ω (last) = true` and `ω (last) = false` faces. -/
lemma prod_cubePt_snoc (n : ℕ) (F : (Fin (n+1) → Bool) → G → ℝ) (x : G)
    (h : Fin n → G) (hl : G) :
    (∏ ω : Fin (n+1) → Bool, F ω (cubePt (n+1) x (Fin.snoc h hl) ω))
      = (∏ σ : Fin n → Bool, F (Fin.snoc σ true) (cubePt n (x + hl) h σ))
        * (∏ σ : Fin n → Bool, F (Fin.snoc σ false) (cubePt n x h σ)) := by
  rw [prod_snoc_bool, Fintype.prod_bool]
  congr 1
  · apply Finset.prod_congr rfl; intro σ _
    rw [cubePt_snoc]; simp
  · apply Finset.prod_congr rfl; intro σ _
    rw [cubePt_snoc]; simp

/-- **Family cube identity.** A family that is constant in the last vertex
coordinate has cube sum equal to a sum of squares of `n`-dimensional cube sums. -/
lemma cubeSum_extend (n : ℕ) (g : (Fin n → Bool) → G → ℝ) :
    cubeSum (n+1) (fun ω => g (Fin.init ω))
      = ∑ h : Fin n → G,
          (∑ x : G, ∏ σ : Fin n → Bool, g σ (cubePt n x h σ))^2 := by
  rw [cubeSum, sum_snoc, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro h _
  have key : ∀ hl : G, ∀ x : G,
      (∏ ω : Fin (n+1) → Bool, g (Fin.init ω) (cubePt (n+1) x (Fin.snoc h hl) ω))
        = (∏ σ : Fin n → Bool, g σ (cubePt n (x + hl) h σ))
          * (∏ σ : Fin n → Bool, g σ (cubePt n x h σ)) := by
    intro hl x
    rw [prod_cubePt_snoc]
    simp
  rw [Finset.sum_congr rfl (fun hl _ => Finset.sum_congr rfl (fun x _ => key hl x))]
  rw [Finset.sum_comm, pow_two]
  have hdec := Commons.Combinatorics.Additive.Gowers.bilinear_sum_decouple
    (f := fun z : G => ∏ σ : Fin n → Bool, g σ (cubePt n z h σ))
    (g := fun z : G => ∏ σ : Fin n → Bool, g σ (cubePt n z h σ))
  rw [← hdec]
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro hl _
  ring

/-- **One-digit Gowers–Cauchy–Schwarz** at the last coordinate. -/
lemma gcs_digit_step (n : ℕ) (F : (Fin (n+1) → Bool) → G → ℝ) :
    (cubeSum (n+1) F)^2
      ≤ (cubeSum (n+1) (fun ω => F (Fin.snoc (Fin.init ω) false)))
        * (cubeSum (n+1) (fun ω => F (Fin.snoc (Fin.init ω) true))) := by
  have h1 : cubeSum (n+1) F
      = ∑ h : Fin n → G,
          (∑ x : G, ∏ σ : Fin n → Bool, F (Fin.snoc σ false) (cubePt n x h σ))
          * (∑ x : G, ∏ σ : Fin n → Bool, F (Fin.snoc σ true) (cubePt n x h σ)) := by
    rw [cubeSum, sum_snoc, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro h _
    have key : ∀ hl : G, ∀ x : G,
        (∏ ω : Fin (n+1) → Bool, F ω (cubePt (n+1) x (Fin.snoc h hl) ω))
          = (∏ σ : Fin n → Bool, F (Fin.snoc σ true) (cubePt n (x + hl) h σ))
            * (∏ σ : Fin n → Bool, F (Fin.snoc σ false) (cubePt n x h σ)) :=
      fun hl x => prod_cubePt_snoc n F x h hl
    rw [Finset.sum_congr rfl (fun hl _ => Finset.sum_congr rfl (fun x _ => key hl x))]
    rw [Finset.sum_comm]
    have hdec := Commons.Combinatorics.Additive.Gowers.bilinear_sum_decouple
      (f := fun z : G => ∏ σ : Fin n → Bool, F (Fin.snoc σ false) (cubePt n z h σ))
      (g := fun z : G => ∏ σ : Fin n → Bool, F (Fin.snoc σ true) (cubePt n z h σ))
    rw [← hdec]
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro hl _
    ring
  rw [h1]
  refine le_trans (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun h : Fin n → G => ∑ x : G, ∏ σ : Fin n → Bool, F (Fin.snoc σ false) (cubePt n x h σ))
    (fun h : Fin n → G => ∑ x : G, ∏ σ : Fin n → Bool, F (Fin.snoc σ true) (cubePt n x h σ))) ?_
  rw [← cubeSum_extend n (fun σ : Fin n → Bool => F (Fin.snoc σ false)),
      ← cubeSum_extend n (fun σ : Fin n → Bool => F (Fin.snoc σ true))]

/-! ## Transporting the step to an arbitrary coordinate -/

/-- `setCoord ℓ b ω` is `ω` with the coordinate `ℓ` replaced by `b`. -/
def setCoord {n : ℕ} (ℓ : Fin n) (b : Bool) (ω : Fin n → Bool) : Fin n → Bool :=
  fun i => if i = ℓ then b else ω i

@[simp] lemma setCoord_apply {n : ℕ} (ℓ : Fin n) (b : Bool) (ω : Fin n → Bool) (i : Fin n) :
    setCoord ℓ b ω i = if i = ℓ then b else ω i := rfl

lemma setCoord_self {n : ℕ} (ℓ : Fin n) (b : Bool) (ω : Fin n → Bool) :
    setCoord ℓ b ω ℓ = b := by simp

lemma setCoord_of_ne {n : ℕ} {ℓ i : Fin n} (b : Bool) (ω : Fin n → Bool) (h : i ≠ ℓ) :
    setCoord ℓ b ω i = ω i := by simp [setCoord_apply, h]

/-- The key combinatorial identity behind the digit step at an arbitrary coordinate:
composing `Fin.snoc` at the last coordinate with the swap that moves `ℓ` to the last
position gives "set the coordinate `ℓ`". -/
lemma snoc_init_comp_swap {e : ℕ} (ℓ : Fin (e+1)) (b : Bool) (ω : Fin (e+1) → Bool) :
    Fin.snoc (Fin.init (ω ∘ Equiv.swap ℓ (Fin.last e))) b
      = setCoord ℓ b ω ∘ Equiv.swap ℓ (Fin.last e) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp only [Function.comp_apply]
    rw [Fin.snoc_last, Equiv.swap_apply_right, setCoord_self]
  · intro j
    have h1 : (Equiv.swap ℓ (Fin.last e)) (Fin.castSucc j) ≠ ℓ := by
      intro hc
      have h2 : Fin.castSucc j = Fin.last e := by
        have := congrArg (Equiv.swap ℓ (Fin.last e)) hc
        rwa [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
      have h3 : (Fin.castSucc j).val = (Fin.last e).val := by rw [h2]
      simp at h3
      omega
    simp only [Function.comp_apply]
    rw [Fin.snoc_castSucc]
    exact (setCoord_of_ne b ω h1).symm

lemma setCoord_eq_fun {n : ℕ} (ℓ : Fin n) (b : Bool) (ω : Fin n → Bool) :
    setCoord ℓ b ω = (fun i => if i = ℓ then b else ω i) := rfl

/-- The coordinate-overwrite form of the digit step. -/
theorem digit_step_at_sc (d : ℕ) (F : (Fin d → Bool) → G → ℝ) (ℓ : Fin d) :
    (cubeSum d F)^2
      ≤ cubeSum d (fun ω => F (setCoord ℓ false ω))
        * cubeSum d (fun ω => F (setCoord ℓ true ω)) := by
  cases d with
  | zero => exact Fin.elim0 ℓ
  | succ e =>
    let π : Fin (e+1) ≃ Fin (e+1) := Equiv.swap ℓ (Fin.last e)
    let F' : (Fin (e+1) → Bool) → G → ℝ := fun ψ => F (ψ ∘ π.symm)
    have hF' : cubeSum (e+1) F' = cubeSum (e+1) F := by
      rw [← cubeSum_reindex_fin (e+1) π F']
      congr 1
      funext ω
      show F ((ω ∘ π) ∘ π.symm) = F ω
      congr 1
      funext i
      rw [Function.comp_apply, Function.comp_apply, Equiv.apply_symm_apply]
    have hchild : ∀ b : Bool,
        cubeSum (e+1) (fun ω => F' (Fin.snoc (Fin.init ω) b))
          = cubeSum (e+1) (fun ω => F (setCoord ℓ b ω)) := by
      intro b
      rw [← cubeSum_reindex_fin (e+1) π (fun ω => F' (Fin.snoc (Fin.init ω) b))]
      congr 1
      funext ω
      rw [show F' (Fin.snoc (Fin.init (ω ∘ π)) b)
            = F ((Fin.snoc (Fin.init (ω ∘ π)) b) ∘ π.symm) from rfl]
      rw [snoc_init_comp_swap ℓ b ω]
      congr 1
      funext i
      rw [Function.comp_apply, Function.comp_apply, Equiv.apply_symm_apply]
    have hstep := gcs_digit_step e F'
    rw [← hF', ← hchild false, ← hchild true]
    exact hstep

/-- **One-digit Gowers–Cauchy–Schwarz at an arbitrary coordinate** (in terms of
the explicit coordinate-overwrite lambda). -/
theorem digit_step_at (d : ℕ) (F : (Fin d → Bool) → G → ℝ) (ℓ : Fin d) :
    (cubeSum d F)^2
      ≤ cubeSum d (fun ω => F (fun i => if i = ℓ then false else ω i))
        * cubeSum d (fun ω => F (fun i => if i = ℓ then true else ω i)) := by
  have h := digit_step_at_sc d F ℓ
  rw [show (fun ω : Fin d → Bool => F (setCoord ℓ false ω))
        = (fun ω => F (fun i => if i = ℓ then false else ω i)) from by
        funext ω; rw [setCoord_eq_fun],
      show (fun ω : Fin d → Bool => F (setCoord ℓ true ω))
        = (fun ω => F (fun i => if i = ℓ then true else ω i)) from by
        funext ω; rw [setCoord_eq_fun]] at h
  exact h

end GCSDigitAux

namespace Commons.Combinatorics.Additive.Gowers

/-- **One-digit Gowers–Cauchy–Schwarz at an arbitrary coordinate.**  Splitting the
`d`-dimensional Gowers cube sum of a family `F` along the coordinate `ℓ` and applying
Cauchy–Schwarz in the corresponding shift variable.  Specialised to the last coordinate
this is the basic step of the Gowers–Cauchy–Schwarz inequality. -/
theorem gcs_digit_step_at {G : Type*} [AddCommGroup G] [Fintype G]
    (d : ℕ) (F : (Fin d → Bool) → G → ℝ) (ℓ : Fin d) :
    (∑ h : Fin d → G, ∑ x : G, ∏ ω : Fin d → Bool,
        F ω (x + ∑ i : Fin d, (if ω i then h i else 0)))^2
      ≤ (∑ h : Fin d → G, ∑ x : G, ∏ ω : Fin d → Bool,
            F (fun i => if i = ℓ then false else ω i)
              (x + ∑ i : Fin d, (if ω i then h i else 0)))
        * (∑ h : Fin d → G, ∑ x : G, ∏ ω : Fin d → Bool,
            F (fun i => if i = ℓ then true else ω i)
              (x + ∑ i : Fin d, (if ω i then h i else 0))) := by
  exact GCSDigitAux.digit_step_at d F ℓ

end Commons.Combinatorics.Additive.Gowers
/-
The flat Gowers cube of Peluse's Lemma 2.2 (the "Gowers--Cauchy--Schwarz" inequality for the
box norms on a product of finite sets), in the exact form needed by `Work.Peluse.Concat.gowersCS`.
-/
import Mathlib
import Submission.Work.Peluse.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Work.Peluse.Concat

noncomputable section

variable {X : Type} [Fintype X]

/-- The `ω`-corner of the flat cube: coordinate `i` taken from `x1` if `ω i`, else from `x0`. -/
def mix {t : ℕ} (ω : Fin t → Bool) (x0 x1 : Fin t → X) : Fin t → X :=
  fun i => if ω i then x1 i else x0 i

/-- The `ω`-weighted product of the flat cube. -/
def cubeProd {t : ℕ} (F : (Fin t → Bool) → (Fin t → X) → ℂ) (x0 x1 : Fin t → X) : ℂ :=
  ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω]) (F ω (mix ω x0 x1))

/-- The (unnormalised) flat cube sum. -/
def cubeSum {t : ℕ} (F : (Fin t → Bool) → (Fin t → X) → ℂ) : ℂ :=
  ∑ x0 : Fin t → X, ∑ x1 : Fin t → X, cubeProd F x0 x1

/-- The `2^t`-th power of the box norm, up to the normalising factor `N ^ (2t)`. -/
def NPow (t : ℕ) (g : (Fin t → X) → ℂ) : ℝ :=
  ‖cubeSum (fun (_ : Fin t → Bool) => g)‖

/-! ## Elementary lemmas about `star`, `weight` and the cube product -/

lemma star_iterate_mul (n : ℕ) (z w : ℂ) :
    (star^[n]) (z * w) = (star^[n] z) * (star^[n] w) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih, star_mul, mul_comm]

lemma star_iterate_succ (n : ℕ) (z : ℂ) : (star^[n+1]) z = star ((star^[n]) z) := by
  rw [Function.iterate_succ_apply']

lemma star_iterate_succ' (n : ℕ) (z : ℂ) : (star^[n+1]) z = (star^[n]) (star z) := by
  rw [Function.iterate_succ_apply]

lemma star_star_iterate (n : ℕ) (z : ℂ) : (star^[n]) (star z) = star ((star^[n]) z) := by
  rw [← Function.iterate_succ_apply star n z, Function.iterate_succ_apply']

lemma star_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    star (∑ i ∈ s, f i) = ∑ i ∈ s, star (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, star_add, ih]

lemma star_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    star (∏ i ∈ s, f i) = ∏ i ∈ s, star (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, star_mul, ih, mul_comm]

lemma star_prod_univ {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    star (∏ i, f i) = ∏ i, star (f i) := star_prod Finset.univ f

lemma prod_star_pair {ι : Type*} [Fintype ι] (a b : ι → ℂ) (k : ι → ℕ) :
    (∏ i, (star^[k i]) (a i * star (b i)))
      = (∏ i, (star^[k i]) (a i)) * star (∏ i, (star^[k i]) (b i)) := by
  have h1 : ∀ i, (star^[k i]) (a i * star (b i))
      = (star^[k i]) (a i) * (star^[k i]) (star (b i)) := fun i => star_iterate_mul _ _ _
  have h2 : (∏ i, (star^[k i]) (star (b i))) = star (∏ i, (star^[k i]) (b i)) := by
    rw [star_prod_univ]
    exact Finset.prod_congr rfl (fun i _ => star_star_iterate (k i) (b i))
  simp only [h1]
  rw [Finset.prod_mul_distrib, h2]

lemma weight_eq_sum (t : ℕ) (ω : Fin t → Bool) :
    Work.Peluse.weight ω = ∑ i : Fin t, (if ω i then (1:ℕ) else 0) := by
  rw [Work.Peluse.weight, Finset.card_filter]

lemma weight_cons (t : ℕ) (b : Bool) (ω' : Fin t → Bool) :
    Work.Peluse.weight (Fin.cons b ω') = Work.Peluse.weight ω' + (if b then 1 else 0) := by
  rw [weight_eq_sum (t+1) (Fin.cons b ω'), weight_eq_sum t ω', Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  exact add_comm _ _

lemma weight_cons_false (t : ℕ) (ω' : Fin t → Bool) :
    Work.Peluse.weight (Fin.cons false ω') = Work.Peluse.weight ω' := by
  rw [weight_cons]; simp

lemma weight_cons_true (t : ℕ) (ω' : Fin t → Bool) :
    Work.Peluse.weight (Fin.cons true ω') = Work.Peluse.weight ω' + 1 := by
  rw [weight_cons]; simp

lemma mix_cons (t : ℕ) (b : Bool) (ω' : Fin t → Bool) (u0 u1 : X) (y0 y1 : Fin t → X) :
    mix (Fin.cons b ω') (Fin.cons u0 y0) (Fin.cons u1 y1)
      = Fin.cons (if b then u1 else u0) (mix ω' y0 y1) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [mix, Fin.cons_zero]
  · intro j
    simp [mix, Fin.cons_succ]

lemma mix_cons_false (t : ℕ) (ω' : Fin t → Bool) (u0 u1 : X) (y0 y1 : Fin t → X) :
    mix (Fin.cons false ω') (Fin.cons u0 y0) (Fin.cons u1 y1)
      = Fin.cons u0 (mix ω' y0 y1) := by
  rw [mix_cons]; rfl

lemma mix_cons_true (t : ℕ) (ω' : Fin t → Bool) (u0 u1 : X) (y0 y1 : Fin t → X) :
    mix (Fin.cons true ω') (Fin.cons u0 y0) (Fin.cons u1 y1)
      = Fin.cons u1 (mix ω' y0 y1) := by
  rw [mix_cons]; rfl

lemma consEquiv_apply_fun (t : ℕ) (Y : Type) (p : Y × (Fin t → Y)) :
    (Fin.consEquiv (fun _ : Fin (t+1) => Y)) p = Fin.cons p.1 p.2 := by
  funext i
  exact Fin.consEquiv_apply (fun _ : Fin (t+1) => Y) p i

lemma prod_fin_succ_bool {M : Type*} [CommMonoid M] (t : ℕ) (G : (Fin (t+1) → Bool) → M) :
    (∏ ω : Fin (t+1) → Bool, G ω)
      = (∏ ω' : Fin t → Bool, G (Fin.cons false ω'))
        * (∏ ω' : Fin t → Bool, G (Fin.cons true ω')) := by
  classical
  have h := Fintype.prod_equiv (Fin.consEquiv (fun _ : Fin (t+1) => Bool))
    (fun p : Bool × (Fin t → Bool) => G (Fin.cons p.1 p.2)) G
    (fun p => by rw [consEquiv_apply_fun])
  rw [← h, Fintype.prod_prod_type, Fintype.prod_bool, mul_comm]

lemma cubeProd_split (t : ℕ) (F : (Fin (t+1) → Bool) → (Fin (t+1) → X) → ℂ)
    (u0 u1 : X) (y0 y1 : Fin t → X) :
    cubeProd F (Fin.cons u0 y0) (Fin.cons u1 y1)
      = ∏ ω' : Fin t → Bool,
          (star^[Work.Peluse.weight ω'])
            (F (Fin.cons false ω') (Fin.cons u0 (mix ω' y0 y1))
              * star (F (Fin.cons true ω') (Fin.cons u1 (mix ω' y0 y1)))) := by
  unfold cubeProd
  rw [prod_fin_succ_bool t
    (fun ω => (star^[Work.Peluse.weight ω]) (F ω (mix ω (Fin.cons u0 y0) (Fin.cons u1 y1))))]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun ω' _ => ?_)
  rw [weight_cons_false, weight_cons_true, mix_cons_false, mix_cons_true]
  rw [star_iterate_succ', ← star_iterate_mul]

/-- The reindexing of a pair of `Fin (t+1)`-tuples as `(u0,u1,(y0,y1))`. -/
def consPairEquiv (t : ℕ) :
    ((Fin (t+1) → X) × (Fin (t+1) → X)) ≃ X × X × ((Fin t → X) × (Fin t → X)) where
  toFun p := (p.1 0, p.2 0, (Fin.tail p.1, Fin.tail p.2))
  invFun q := (Fin.cons q.1 q.2.2.1, Fin.cons q.2.1 q.2.2.2)
  left_inv := by
    rintro ⟨v, w⟩
    simp only [Fin.cons_self_tail]
  right_inv := by
    rintro ⟨a, b, y0, y1⟩
    simp only [Fin.cons_zero, Fin.tail_cons]

lemma cubeSum_split (t : ℕ) (F : (Fin (t+1) → Bool) → (Fin (t+1) → X) → ℂ) :
    cubeSum F = ∑ q : X × X × ((Fin t → X) × (Fin t → X)),
      cubeProd F (Fin.cons q.1 q.2.2.1) (Fin.cons q.2.1 q.2.2.2) := by
  unfold cubeSum
  rw [← Fintype.sum_prod_type
    (f := fun p : (Fin (t+1) → X) × (Fin (t+1) → X) => cubeProd F p.1 p.2)]
  exact Fintype.sum_equiv (consPairEquiv (X := X) t) (fun p => cubeProd F p.1 p.2)
    (fun q => cubeProd F (Fin.cons q.1 q.2.2.1) (Fin.cons q.2.1 q.2.2.2))
    (fun p => by
      show cubeProd F p.1 p.2
        = cubeProd F (Fin.cons (p.1 0) (Fin.tail p.1)) (Fin.cons (p.2 0) (Fin.tail p.2))
      rw [Fin.cons_self_tail, Fin.cons_self_tail])

lemma cubeSum_const_succ (t : ℕ) (g : (Fin (t+1) → X) → ℂ) :
    cubeSum (fun (_ : Fin (t+1) → Bool) => g)
      = ∑ u0 : X, ∑ u1 : X,
          cubeSum (fun (_ : Fin t → Bool) =>
            (fun y : Fin t → X => g (Fin.cons u0 y) * star (g (Fin.cons u1 y)))) := by
  calc cubeSum (fun (_ : Fin (t+1) → Bool) => g)
      = ∑ q : X × X × ((Fin t → X) × (Fin t → X)),
          cubeProd (fun (_ : Fin (t+1) → Bool) => g)
            (Fin.cons q.1 q.2.2.1) (Fin.cons q.2.1 q.2.2.2) := cubeSum_split t _
    _ = ∑ u0 : X, ∑ u1 : X, ∑ y0 : Fin t → X, ∑ y1 : Fin t → X,
          cubeProd (fun (_ : Fin (t+1) → Bool) => g)
            (Fin.cons u0 y0) (Fin.cons u1 y1) := by
        simp only [Fintype.sum_prod_type]
    _ = ∑ u0 : X, ∑ u1 : X, cubeSum (fun (_ : Fin t → Bool) =>
          (fun y : Fin t → X => g (Fin.cons u0 y) * star (g (Fin.cons u1 y)))) := by
        refine Finset.sum_congr rfl (fun u0 _ => Finset.sum_congr rfl (fun u1 _ => ?_))
        simp only [cubeSum]
        refine Finset.sum_congr rfl (fun y0 _ => Finset.sum_congr rfl (fun y1 _ => ?_))
        rw [cubeProd_split]
        simp only [cubeProd]

/-- The canonical equivalence `(Fin 1 → Y) ≃ Y`. -/
def fin1ArrowEquiv (Y : Type) : (Fin 1 → Y) ≃ Y where
  toFun v := v 0
  invFun y := fun _ => y
  left_inv v := by funext i; fin_cases i <;> rfl
  right_inv y := rfl

lemma sum_fin1 {Y : Type} [Fintype Y] (G : (Fin 1 → Y) → ℂ) :
    (∑ v : Fin 1 → Y, G v) = ∑ y : Y, G (fun _ => y) := by
  refine Fintype.sum_equiv (fin1ArrowEquiv Y) G (fun y : Y => G (fun _ => y)) (fun v => ?_)
  congr 1
  funext i
  fin_cases i <;> rfl

lemma prod_fin_one_bool {M : Type*} [CommMonoid M] (G : (Fin 1 → Bool) → M) :
    (∏ ω : Fin 1 → Bool, G ω) = G (fun _ => true) * G (fun _ => false) := by
  rw [show (∏ ω : Fin 1 → Bool, G ω) = ∏ b : Bool, G (fun _ : Fin 1 => b) from
    Fintype.prod_equiv (fin1ArrowEquiv Bool) G (fun b : Bool => G (fun _ => b))
      (fun ω => by congr 1; funext i; fin_cases i; rfl)]
  rw [Fintype.prod_bool]

lemma weight_fin_one_true : Work.Peluse.weight (fun _ : Fin 1 => true) = 1 := by
  rw [weight_eq_sum, Fin.sum_univ_one]; simp

lemma weight_fin_one_false : Work.Peluse.weight (fun _ : Fin 1 => false) = 0 := by
  rw [weight_eq_sum, Fin.sum_univ_one]; simp

lemma mix_fin_one_true {X : Type} (x0 x1 : Fin 1 → X) :
    mix (fun _ : Fin 1 => true) x0 x1 = x1 := by
  funext i; fin_cases i; simp [mix]

lemma mix_fin_one_false {X : Type} (x0 x1 : Fin 1 → X) :
    mix (fun _ : Fin 1 => false) x0 x1 = x0 := by
  funext i; fin_cases i; simp [mix]

lemma NPow_nonneg (t : ℕ) (g : (Fin t → X) → ℂ) : 0 ≤ NPow t g := norm_nonneg _

/-- The set of indices at which `ω` is `false`. -/
def zeroSet {s : ℕ} (ω : Fin s → Bool) : Finset (Fin s) :=
  Finset.univ.filter (fun i => !ω i)

/-- The "one function per omitted coordinate" family of Peluse's Lemma 2.2 as an abstract family:
`ω ↦ f` if `ω` is identically true, `ω ↦ g i` if `i` is the unique index with `ω i = false`, and
`ω ↦ 1` otherwise. -/
def substG {s : ℕ} (f : (Fin s → X) → ℂ) (g : Fin s → (Fin s → X) → ℂ) :
    (Fin s → Bool) → (Fin s → X) → ℂ :=
  fun ω x =>
    if _h : (∀ i, ω i) then f x
    else if h2 : (∃ i, ω i = false ∧ ∀ j, j ≠ i → ω j)
      then g (Classical.choose h2) x
    else 1

/-- The family used in the substitution step of Lemma 2.2: `substF ω = star^|ω| ∘ substG ω`. -/
def substF {s : ℕ} (f : (Fin s → X) → ℂ) (g : Fin s → (Fin s → X) → ℂ) :
    (Fin s → Bool) → (Fin s → X) → ℂ :=
  fun ω x => (star^[Work.Peluse.weight ω]) (substG f g ω x)

end

end Work.Peluse.Concat

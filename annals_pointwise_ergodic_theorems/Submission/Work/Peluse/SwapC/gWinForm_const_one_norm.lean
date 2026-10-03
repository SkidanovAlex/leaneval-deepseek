/-
The `d = 1` evaluation of the box form `Work.Peluse.SwapC.gWinForm` of a single function `g`.

At `d = 1` the cube has the two sign patterns `false`, `true`, contributing the two corners
`z'` and `z` of the unique coordinate, so the `ω`-product of the box form collapses to
`g (x + β 0 (z' 0)) * conj (g (x + β 0 (z 0)))`.  Summing over the two index coordinates
(identified with `Y 0`) gives the square of the modulus of the shifted sum `∑ a, g (x + β 0 a)`,
and then summing over the window `W` gives

  `gWinForm 1 Y β W (fun _ => g) = ↑(∑ x ∈ W, ‖∑ a : Y 0, g (x + β 0 a)‖ ^ 2)`,

hence `‖gWinForm 1 Y β W (fun _ => g)‖ = ∑ x ∈ W, ‖∑ a : Y 0, g (x + β 0 a)‖ ^ 2`.

This is the `SwapC` counterpart of `Work.Peluse.BoxNorm.winForm_const_one_norm`; the difference is
that there the coordinate range is a *set* `Q 0 ⊆ ℤ`, whereas here it is an arbitrary finite type
`Y 0` together with a shift map `β 0 : Y 0 → ℤ`, so coincidences of the shifts are counted with
multiplicity.
-/
import Mathlib
import Submission.Work.Peluse.SwapC.GDefs
import Submission.Work.Peluse.BoxNorm.WinAux

open scoped BigOperators

namespace Work.Peluse.SwapC

noncomputable section

open Work.Peluse

/-! ## Evaluation of the `ω`-product at `d = 1` -/

/-- The product over the two sign patterns `Fin 1 → Bool`, in the order `false`, `true`. -/
private lemma prod_finOneBool (F : (Fin 1 → Bool) → ℂ) :
    ∏ ω : Fin 1 → Bool, F ω = F (fun _ => false) * F (fun _ => true) := by
  have h1 : ∏ ω : Fin 1 → Bool, F ω
      = ∏ b : Bool, F ((Equiv.piUnique (fun _ : Fin 1 => Bool)).symm b) :=
    Fintype.prod_equiv (Equiv.piUnique (fun _ : Fin 1 => Bool)) F
      (fun b => F ((Equiv.piUnique (fun _ : Fin 1 => Bool)).symm b))
      (fun ω => by rw [Equiv.symm_apply_apply])
  have ht : (Equiv.piUnique (fun _ : Fin 1 => Bool)).symm true = (fun _ : Fin 1 => true) := by
    funext i; fin_cases i; rfl
  have hf : (Equiv.piUnique (fun _ : Fin 1 => Bool)).symm false = (fun _ : Fin 1 => false) := by
    funext i; fin_cases i; rfl
  rw [h1, Fintype.prod_bool, ht, hf, mul_comm]

private lemma weight_finOneBool_true : weight (fun _ : Fin 1 => true) = 1 := by decide

private lemma weight_finOneBool_false : weight (fun _ : Fin 1 => false) = 0 := by decide

/-- The total shift of the `ω`-corner at `d = 1`, for a constant sign pattern. -/
private lemma gtotal_gcorner_finOneBool {Y : Fin 1 → Type*} [∀ i, Fintype (Y i)]
    (β : (i : Fin 1) → Y i → ℤ) (z z' : GIdx 1 Y) (b : Bool) :
    gtotal β (gcorner z z' (fun _ => b)) = β 0 (if b then z 0 else z' 0) := by
  simp only [gtotal, gcorner, Fin.sum_univ_one]

/-- The `ω`-product of the `d = 1` box form of an arbitrary family `φ`. -/
private lemma gWinForm_prod_term {Y : Fin 1 → Type*} [∀ i, Fintype (Y i)]
    (β : (i : Fin 1) → Y i → ℤ) (z z' : GIdx 1 Y) (x : ℤ)
    (φ : (Fin 1 → Bool) → ℤ → ℂ) :
    (∏ ω : Fin 1 → Bool, (star^[weight ω]) (φ ω (x + gtotal β (gcorner z z' ω))))
      = φ (fun _ => false) (x + β 0 (z' 0)) * star (φ (fun _ => true) (x + β 0 (z 0))) := by
  rw [prod_finOneBool]
  have hT : (star^[weight (fun _ : Fin 1 => true)])
        (φ (fun _ => true) (x + gtotal β (gcorner z z' (fun _ => true))))
      = star (φ (fun _ => true) (x + β 0 (z 0))) := by
    rw [gtotal_gcorner_finOneBool, weight_finOneBool_true]
    simp
  have hF : (star^[weight (fun _ : Fin 1 => false)])
        (φ (fun _ => false) (x + gtotal β (gcorner z z' (fun _ => false))))
      = φ (fun _ => false) (x + β 0 (z' 0)) := by
    rw [gtotal_gcorner_finOneBool, weight_finOneBool_false]
    simp
  rw [hT, hF]

/-! ## Reindexing the single coordinate `GIdx 1 Y` by `Y 0` -/

/-- The single coordinate of a one-dimensional cube: `GIdx 1 Y ≃ Y 0`, evaluation at `0`. -/
private def gIdxEquiv (Y : Fin 1 → Type*) : GIdx 1 Y ≃ Y 0 where
  toFun z := z 0
  invFun a := Fin.cases a (fun i : Fin 0 => Fin.elim0 i)
  left_inv z := by funext i; fin_cases i; rfl
  right_inv a := rfl

private lemma gIdxEquiv_symm_zero (Y : Fin 1 → Type*) (a : Y 0) :
    ((gIdxEquiv Y).symm a) 0 = a := rfl

/-- Sums over the one-dimensional cube reduce to sums over `Y 0`. -/
private lemma sum_gIdx_eq {Y : Fin 1 → Type*} [∀ i, Fintype (Y i)] {M : Type*}
    [AddCommMonoid M] (f : Y 0 → M) :
    (∑ z : GIdx 1 Y, f (z 0)) = ∑ a : Y 0, f a := by
  rw [(Equiv.sum_comp (gIdxEquiv Y).symm (fun z : GIdx 1 Y => f (z 0))).symm]
  simp only [gIdxEquiv_symm_zero]

/-! ## The term identity -/

/-- The double sum over the two coordinate tuples is the squared modulus of the shifted sum. -/
private lemma gWinForm_doubleSum {Y : Fin 1 → Type*} [∀ i, Fintype (Y i)]
    (β : (i : Fin 1) → Y i → ℤ) (x : ℤ) (g : ℤ → ℂ) :
    (∑ z' : GIdx 1 Y, ∑ z : GIdx 1 Y,
        g (x + β 0 (z' 0)) * star (g (x + β 0 (z 0))))
      = ((‖∑ a : Y 0, g (x + β 0 a)‖ ^ 2 : ℝ) : ℂ) := by
  rw [BoxNorm.pairSum_star (fun z : GIdx 1 Y => g (x + β 0 (z 0)))]
  rw [sum_gIdx_eq (fun a : Y 0 => g (x + β 0 a))]

/-- The `d = 1` box form of a single function as an explicit real number. -/
private lemma gWinForm_const_one' (Y : Fin 1 → Type*) [∀ i, Fintype (Y i)]
    (β : (i : Fin 1) → Y i → ℤ) (W : Finset ℤ) (g : ℤ → ℂ) :
    gWinForm 1 Y β W (fun _ => g)
      = ((∑ x ∈ W, ‖∑ a : Y 0, g (x + β 0 a)‖ ^ 2 : ℝ) : ℂ) := by
  simp only [gWinForm, gWinForm_prod_term]
  rw [BoxNorm.sum_three_comm]
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_comm]
  exact gWinForm_doubleSum β x g

/-- **The `d = 1` evaluation of the box form of a single function**, in norm form. -/
theorem gWinForm_const_one_norm (Y : Fin 1 → Type*) [∀ i, Fintype (Y i)]
    (β : (i : Fin 1) → Y i → ℤ) (W : Finset ℤ) (g : ℤ → ℂ) :
    ‖Work.Peluse.SwapC.gWinForm 1 Y β W (fun _ => g)‖
      = ∑ x ∈ W, ‖∑ a : Y 0, g (x + β 0 a)‖ ^ 2 := by
  rw [gWinForm_const_one']
  exact BoxNorm.norm_ofReal_of_nonneg (Finset.sum_nonneg (fun x _ => sq_nonneg _))

end

end Work.Peluse.SwapC

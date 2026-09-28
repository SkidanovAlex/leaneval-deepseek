import Mathlib
import Submission.Work.HP.Sig2.GamTwoDefs
import Submission.Work.HP.Transf.Basic

namespace Work.HP.Sig2

open Work.HP Work.HP.Transf

/-! ## Auxiliary computations for `perpCompB_mem_orth`

We record the elementary calculus of the explicit Euclidean form `dotR`, the symmetry of the Gram
matrix `gramOf b`, and its identification with `dotR` on the realified basis vectors.  The key
identity is that the transposed inverse Gram matrix is a left inverse of the Gram matrix (it is the
transpose of the assumed right-inverse relation, using symmetry of `gramOf b`). -/

/-- `dotR` is additive in its first argument over a finite sum. -/
lemma dotR_sum_left {ι : Type*} [Fintype ι] {α : Type*} (s : Finset α) (f : α → ι → ℝ)
    (y : ι → ℝ) : dotR (∑ i ∈ s, f i) y = ∑ i ∈ s, dotR (f i) y := by
  classical
  induction s using Finset.induction with
  | empty => simp [dotR]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, dotR_add_left, ih]

/-- The Gram matrix of a `ℤ`-basis is symmetric. -/
lemma gramOf_comm {ι κ : Type*} [Fintype ι] [Fintype κ] {Λ : Submodule ℤ (ι → ℤ)}
    (b : Module.Basis κ ℤ Λ) (i j : κ) : gramOf b i j = gramOf b j i := by
  simp only [gramOf, Matrix.of_apply]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

/-- The entries of the Gram matrix are the pairwise `dotR` products of the realified basis. -/
lemma gramOf_eq_dotR {ι κ : Type*} [Fintype ι] [Fintype κ] {Λ : Submodule ℤ (ι → ℤ)}
    (b : Module.Basis κ ℤ Λ) (i j : κ) :
    gramOf b i j = dotR (intCastPi (((b i : Λ) : ι → ℤ))) (intCastPi (((b j : Λ) : ι → ℤ))) := by
  simp only [gramOf, Matrix.of_apply, dotR, intCastPi_apply]

/-- Given only that `gramOf b` is a *right* inverse of `gramOf b`, transposition and symmetry turn
it into the statement that `(gramOf b)⁻¹` is a left inverse of `gramOf b`, in entry form. -/
lemma gramOf_inv_entry {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {Λ : Submodule ℤ (ι → ℤ)} (b : Module.Basis κ ℤ Λ)
    (hG : gramOf b * (gramOf b)⁻¹ = 1) :
    ∀ j k : κ, (∑ i : κ, (gramOf b)⁻¹ i j * gramOf b i k) = if j = k then (1:ℝ) else 0 := by
  have hsymm : Matrix.transpose (gramOf b) = gramOf b := by
    ext i j; rw [Matrix.transpose_apply]; exact gramOf_comm b j i
  have h := congrArg Matrix.transpose hG
  rw [Matrix.transpose_mul, Matrix.transpose_one, hsymm] at h
  intro j k
  have hjk := congrFun (congrFun h j) k
  rw [Matrix.mul_apply, Matrix.one_apply] at hjk
  simpa only [Matrix.transpose_apply] using hjk

/-- `perpCompB b w` is orthogonal to every realified basis vector `b k`. -/
lemma perpCompB_dot_basis {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {Λ : Submodule ℤ (ι → ℤ)} (b : Module.Basis κ ℤ Λ)
    (hG : gramOf b * (gramOf b)⁻¹ = 1) (w : ι → ℝ) (k : κ) :
    dotR (perpCompB b w) (intCastPi (((b k : Λ) : ι → ℤ))) = 0 := by
  have hkey := gramOf_inv_entry b hG
  -- the coefficient of `b i` in the projection, paired against `b k`
  have hmain : (∑ i : κ, (∑ j : κ,
        (gramOf b)⁻¹ i j * dotR w (intCastPi (((b j : Λ) : ι → ℤ)))) * gramOf b i k)
      = dotR w (intCastPi (((b k : Λ) : ι → ℤ))) := by
    have step1 : (∑ i : κ, (∑ j : κ,
          (gramOf b)⁻¹ i j * dotR w (intCastPi (((b j : Λ) : ι → ℤ)))) * gramOf b i k)
        = ∑ i : κ, ∑ j : κ,
            ((gramOf b)⁻¹ i j * dotR w (intCastPi (((b j : Λ) : ι → ℤ)))) * gramOf b i k :=
      Finset.sum_congr rfl fun i _ => Finset.sum_mul _ _ _
    rw [step1]
    have step2 : (∑ i : κ, ∑ j : κ,
          ((gramOf b)⁻¹ i j * dotR w (intCastPi (((b j : Λ) : ι → ℤ)))) * gramOf b i k)
        = ∑ j : κ, ∑ i : κ,
            ((gramOf b)⁻¹ i j * dotR w (intCastPi (((b j : Λ) : ι → ℤ)))) * gramOf b i k :=
      Finset.sum_comm
    rw [step2]
    have step3 : (∑ j : κ, ∑ i : κ,
          ((gramOf b)⁻¹ i j * dotR w (intCastPi (((b j : Λ) : ι → ℤ)))) * gramOf b i k)
        = ∑ j : κ, (∑ i : κ, (gramOf b)⁻¹ i j * gramOf b i k)
            * dotR w (intCastPi (((b j : Λ) : ι → ℤ))) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [step3]
    have step4 : (∑ j : κ, (∑ i : κ, (gramOf b)⁻¹ i j * gramOf b i k)
          * dotR w (intCastPi (((b j : Λ) : ι → ℤ))))
        = ∑ j : κ, (if j = k then (1:ℝ) else 0)
            * dotR w (intCastPi (((b j : Λ) : ι → ℤ))) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hkey j k]
    rw [step4]
    have step5 : (∑ j : κ, (if j = k then (1:ℝ) else 0)
          * dotR w (intCastPi (((b j : Λ) : ι → ℤ))))
        = ∑ j : κ, (if j = k then dotR w (intCastPi (((b j : Λ) : ι → ℤ))) else 0) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : j = k <;> simp [h]
    rw [step5, Finset.sum_ite_eq']
    simp
  have hstep : (∑ i : κ, dotR ((∑ j : κ,
        (gramOf b)⁻¹ i j * dotR w (intCastPi (((b j : Λ) : ι → ℤ))))
        • intCastPi (((b i : Λ) : ι → ℤ))) (intCastPi (((b k : Λ) : ι → ℤ))))
      = ∑ i : κ, (∑ j : κ,
          (gramOf b)⁻¹ i j * dotR w (intCastPi (((b j : Λ) : ι → ℤ)))) * gramOf b i k := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dotR_smul_left, ← gramOf_eq_dotR b i k]
  rw [perpCompB, dotR_sub_left, dotR_sum_left, hstep, hmain, sub_self]

/-- The vector `w - perpCompB b w` lies in the real span `V` of the realified `ℤ`-basis `b`, and
`perpCompB b w` is orthogonal to all of `V` (dotR is the explicit Euclidean form), assuming the
inverse Gram matrix is a right inverse. -/
theorem perpCompB_mem_orth {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {Λ : Submodule ℤ (ι → ℤ)} (b : Module.Basis κ ℤ Λ)
    (hG : (gramOf b) * (gramOf b)⁻¹ = 1) :
    (∀ w : ι → ℝ,
      w - perpCompB b w ∈
        Submodule.span ℝ (Set.range fun i : κ => intCastPi (((b i : Λ) : ι → ℤ)))) ∧
    (∀ w : ι → ℝ, ∀ z ∈ Submodule.span ℝ (Set.range fun i : κ => intCastPi (((b i : Λ) : ι → ℤ))),
      dotR (perpCompB b w) z = 0) := by
  constructor
  · intro w
    have hmem : w - perpCompB b w =
        ∑ i : κ, (∑ j : κ, (gramOf b)⁻¹ i j * dotR w (intCastPi (((b j : Λ) : ι → ℤ))))
          • intCastPi (((b i : Λ) : ι → ℤ)) := by
      rw [perpCompB]; abel
    rw [hmem]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  · intro w z hz
    refine Submodule.span_induction (p := fun z _ => dotR (perpCompB b w) z = 0)
      (fun x hx => ?_) ?_ (fun x y hx hy ihx ihy => ?_) (fun a x hx ihx => ?_) hz
    · rcases hx with ⟨i, rfl⟩
      exact perpCompB_dot_basis b hG w i
    · simp
    · rw [dotR_add_right, ihx, ihy, add_zero]
    · rw [dotR_smul_right, ihx, mul_zero]

end Work.HP.Sig2

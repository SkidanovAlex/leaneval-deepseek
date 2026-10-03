/-
# The level-one multiset box norm, explicitly

`pbox 1 q₁ q₂ M S f` is the modulus of the `d = 1` multiset box sum

`(1/|S|) M^{-4} ∑_{h,h'} ∑_x ∏_{ω : Fin 1 → Bool} C^{|ω|} f (x + cornerShift …)`,

and the one-dimensional cube term is

`∏_{ω : Fin 1 → Bool} C^{|ω|} f (x + cornerShift u v ω) = f (x + v) · conj (f (x + u))`.

Hence the double sum over `h, h' ∈ Fin M × Fin M` is the Gram matrix of the family
`m ↦ (x ↦ f (x + pdir (q₁ 0) (q₂ 0) m))`, and collapsing it produces the squared `ℓ²`-norm of the
windowed sum `x ↦ ∑_m f (x + pdir (q₁ 0) (q₂ 0) m)`.

## Main results

* `Work.Peluse.SwapCS0.gramShiftC` : the abstract Gram identity
  `∑_{k,k'} ∑_x f (x + σ k') conj (f (x + σ k)) = ↑(∑_x ‖∑_k f (x + σ k)‖²)`
  for a finitely supported `f`;
* `Work.Peluse.SwapCS0.mCubeSumOneGram` : `mCubeSum` at `d = 1`, in Gram form;
* `Work.Peluse.SwapCS0.pboxOneExplicit` : the target identity for `pbox 1`.
-/

import Mathlib
import Submission.Work.Peluse.SwapC.concatGlue

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.SwapCS0

noncomputable section

open Work.Peluse

/-! ## Elementary support bookkeeping -/

/-- An integer outside the symmetric interval `[-m,m]` has `natAbs > m`. -/
private lemma lt_natAbs_of_not_mem_symIcc {m : ℕ} {x : ℤ} (h : x ∉ Work.Peluse.symIcc m) :
    m < x.natAbs := by
  by_contra hc
  rw [not_lt] at hc
  refine h ?_
  simp only [Work.Peluse.symIcc, Finset.mem_Icc]
  have h2 : (x.natAbs : ℤ) ≤ (m : ℤ) := by exact_mod_cast hc
  have h1 : x ≤ (x.natAbs : ℤ) := Int.le_natAbs
  constructor <;> omega

/-! ## The one-dimensional cube term -/

private lemma weight_const_fin1 (b : Bool) :
    Work.Peluse.weight (fun _ : Fin 1 => b) = if b then 1 else 0 := by
  cases b <;> simp [Work.Peluse.weight]

private lemma cornerShift_const_fin1 (b : Bool) (u v : Fin 1 → ℤ) :
    Work.Peluse.cornerShift u v (fun _ : Fin 1 => b) = if b then u 0 else v 0 := by
  cases b <;> simp [Work.Peluse.cornerShift]

/-- The one-dimensional cube term is `f (x + v 0) · conj (f (x + u 0))`. -/
private lemma cubeTerm_fin1_aux (u v : Fin 1 → ℤ) (f : ℤ → ℂ) (x : ℤ) :
    Work.Peluse.cubeTerm u v f x = f (x + v 0) * star (f (x + u 0)) := by
  rw [Work.Peluse.cubeTerm]
  rw [Fintype.prod_equiv (Equiv.funUnique (Fin 1) Bool)
    (fun ω : Fin 1 → Bool =>
      (star^[Work.Peluse.weight ω]) (f (x + Work.Peluse.cornerShift u v ω)))
    (fun b : Bool => if b then star (f (x + u 0)) else f (x + v 0))]
  · rw [Fintype.prod_bool]; simp only [if_true, if_false, Bool.false_eq_true]; ring
  · intro ω
    rw [show (Equiv.funUnique (Fin 1) Bool) ω = ω 0 from rfl]
    have hω : ω = fun _ => ω 0 := by funext i; exact congrArg ω (Subsingleton.elim i 0)
    rw [hω, weight_const_fin1 (ω 0), cornerShift_const_fin1 (ω 0) u v]
    cases h : ω 0 <;> simp

/-! ## The abstract Gram identity -/

/-- **Gram identity.**  For a finitely supported `f` and an arbitrary shift family `σ` over a
finite index type,
`∑_{k,k'} ∑_x f (x + σ k') · conj (f (x + σ k)) = ↑(∑_x ‖∑_k f (x + σ k)‖²)`.
Both sides are finite sums: `f` is finitely supported, so everything lives in a symmetric
interval `[-N-B, N+B]`, and the double sum over `k,k'` commutes with the sum over `x`. -/
theorem gramShiftC {ι : Type*} [Fintype ι] (σ : ι → ℤ) (f : ℤ → ℂ)
    (hf : Work.Peluse.FinSuppZ f) :
    (∑ k : ι, ∑ k' : ι, ∑' x : ℤ, f (x + σ k') * star (f (x + σ k)))
      = ((∑' x : ℤ, ‖∑ k : ι, f (x + σ k)‖ ^ 2 : ℝ) : ℂ) := by
  classical
  obtain ⟨N, hN⟩ := hf
  set B : ℕ := ∑ k : ι, (σ k).natAbs with hB
  have hσB : ∀ k : ι, (σ k).natAbs ≤ B := by
    intro k; rw [hB]
    exact Finset.single_le_sum (s := Finset.univ) (f := fun i : ι => (σ i).natAbs)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ k)
  have hsupp : ∀ (k : ι) (x : ℤ), x ∉ symIcc (N + B) → f (x + σ k) = 0 := by
    intro k x hx
    apply hN
    have hxT : N + B < x.natAbs := lt_natAbs_of_not_mem_symIcc hx
    have hsub : x.natAbs ≤ (x + σ k).natAbs + (σ k).natAbs := by
      have := Int.natAbs_sub_le (x + σ k) (σ k)
      simpa using this
    have : N < (x + σ k).natAbs := by
      have := hσB k
      omega
    exact this
  have hper : ∀ x : ℤ, (∑ k : ι, ∑ k' : ι, f (x + σ k') * star (f (x + σ k)))
      = ((‖∑ k : ι, f (x + σ k)‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    have hz : ((‖∑ k : ι, f (x + σ k)‖ ^ 2 : ℝ) : ℂ)
        = (∑ k : ι, f (x + σ k)) * star (∑ k : ι, f (x + σ k)) := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]; rfl
    have hz2 : (∑ k : ι, f (x + σ k)) * star (∑ k : ι, f (x + σ k))
        = ∑ k : ι, ∑ k' : ι, f (x + σ k') * star (f (x + σ k)) := by
      rw [star_sum]
      simp only [Finset.sum_mul, Finset.mul_sum]
    rw [← hz2, ← hz]
  have htsum1 : ∀ k k' : ι, (∑' x : ℤ, f (x + σ k') * star (f (x + σ k)))
      = ∑ x ∈ symIcc (N + B), f (x + σ k') * star (f (x + σ k)) := by
    intro k k'
    refine tsum_eq_sum (s := symIcc (N + B)) (fun x hx => ?_)
    rw [hsupp k x hx, star_zero, mul_zero]
  have htsum2 : (∑' x : ℤ, ‖∑ k : ι, f (x + σ k)‖ ^ 2)
      = ∑ x ∈ symIcc (N + B), ‖∑ k : ι, f (x + σ k)‖ ^ 2 := by
    refine tsum_eq_sum (s := symIcc (N + B)) (fun x hx => ?_)
    have hW : (∑ k : ι, f (x + σ k)) = 0 := Finset.sum_eq_zero (fun k _ => hsupp k x hx)
    rw [hW, norm_zero]; norm_num
  calc (∑ k : ι, ∑ k' : ι, ∑' x : ℤ, f (x + σ k') * star (f (x + σ k)))
      = ∑ k : ι, ∑ k' : ι, ∑ x ∈ symIcc (N + B),
          f (x + σ k') * star (f (x + σ k)) := by
        refine Finset.sum_congr rfl (fun k _ =>
          Finset.sum_congr rfl (fun k' _ => htsum1 k k'))
    _ = ∑ x ∈ symIcc (N + B), ∑ k : ι, ∑ k' : ι,
          f (x + σ k') * star (f (x + σ k)) := by
        have h1 : (∑ k : ι, ∑ k' : ι, ∑ x ∈ symIcc (N + B),
              f (x + σ k') * star (f (x + σ k)))
            = ∑ k : ι, ∑ x ∈ symIcc (N + B), ∑ k' : ι,
              f (x + σ k') * star (f (x + σ k)) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.sum_comm]
        rw [h1, Finset.sum_comm]
    _ = ∑ x ∈ symIcc (N + B), ((‖∑ k : ι, f (x + σ k)‖ ^ 2 : ℝ) : ℂ) := by
        refine Finset.sum_congr rfl (fun x _ => hper x)
    _ = ((∑ x ∈ symIcc (N + B), ‖∑ k : ι, f (x + σ k)‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]
    _ = ((∑' x : ℤ, ‖∑ k : ι, f (x + σ k)‖ ^ 2 : ℝ) : ℂ) := by rw [htsum2]

/-! ## `mCubeSum` at `d = 1` -/

/-- **`mCubeSum` at `d = 1`.**  The multiset box sum of order one is the Gram average of the
windowed family `m ↦ x ↦ f (x + ν m)`. -/
theorem mCubeSumOneGram {X : Type} [Fintype X] (ν : X → ℤ) (S : Finset ℤ) (f : ℤ → ℂ)
    (hf : Work.Peluse.FinSuppZ f) :
    Work.Peluse.SwapC.mCubeSum 1 X (fun _ : Fin 1 => ν) S (fun _ : Fin 1 → Bool => f)
      = ((S.card : ℂ))⁻¹ * (((Fintype.card X : ℂ))⁻¹) ^ 2 *
        ((∑' x : ℤ, ‖∑ k : X, f (x + ν k)‖ ^ 2 : ℝ) : ℂ) := by
  classical
  have hreindex : ∀ (G : (Fin 1 → X) → ℂ),
      (∑ h : Fin 1 → X, G h) = ∑ m : X, G (fun _ => m) := by
    intro G
    refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) X) G (fun m : X => G (fun _ => m)) ?_
    intro h
    rw [show (Equiv.funUnique (Fin 1) X) h = h 0 from rfl]
    congr 1
    funext i
    exact congrArg h (Subsingleton.elim i 0)
  have hcube : ∀ (h h' : Fin 1 → X) (x : ℤ),
      (∏ ω : Fin 1 → Bool, (star^[weight ω])
        (f (x + cornerShift (fun k => ν (h k)) (fun k => ν (h' k)) ω)))
      = f (x + ν (h' 0)) * star (f (x + ν (h 0))) := by
    intro h h' x
    have h2 := cubeTerm_fin1_aux (fun k => ν (h k)) (fun k => ν (h' k)) f x
    rwa [cubeTerm] at h2
  rw [Work.Peluse.SwapC.mCubeSum]
  simp only [Nat.mul_one]
  congr 1
  have h1 : (∑ h : Fin 1 → X, ∑ h' : Fin 1 → X, ∑' x : ℤ,
        ∏ ω : Fin 1 → Bool, (star^[weight ω])
          (f (x + cornerShift (fun k => ν (h k)) (fun k => ν (h' k)) ω)))
      = ∑ h : Fin 1 → X, ∑ h' : Fin 1 → X, ∑' x : ℤ,
          f (x + ν (h' 0)) * star (f (x + ν (h 0))) := by
    refine Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun h' _ => ?_))
    exact tsum_congr (fun x => hcube h h' x)
  rw [h1]
  rw [hreindex (fun h => ∑ h' : Fin 1 → X, ∑' x : ℤ,
        f (x + ν (h' 0)) * star (f (x + ν (h 0))))]
  trans ∑ m : X, ∑ m' : X, ∑' x : ℤ, f (x + ν m') * star (f (x + ν m))
  · refine Finset.sum_congr rfl (fun m _ => ?_)
    exact hreindex (fun h' => ∑' x : ℤ, f (x + ν (h' 0)) * star (f (x + ν m)))
  · exact gramShiftC ν f hf

/-! ## Norm bookkeeping -/

private lemma cz_norm_natCast_inv (n : ℕ) : ‖(((n : ℂ))⁻¹)‖ = ((n : ℝ))⁻¹ := by
  rw [norm_inv, Complex.norm_natCast]

private lemma cz_norm_ofReal (r : ℝ) : ‖((r : ℂ))‖ = |r| := by simp

private lemma card_prod_fin_inv_sq (M : ℕ) :
    (((Fintype.card (Fin M × Fin M) : ℝ))⁻¹) ^ 2 = ((M : ℝ) ^ 4)⁻¹ := by
  have hcard : (Fintype.card (Fin M × Fin M) : ℝ) = (M : ℝ) ^ 2 := by
    rw [Fintype.card_prod, Fintype.card_fin]; push_cast; ring
  rw [hcard, inv_pow]
  congr 1
  ring

/-! ## The target -/

theorem pboxOneExplicit {M : ℕ} (q₁ q₂ : Fin 1 → ℤ) (S : Finset ℤ) (f : ℤ → ℂ)
    (hf : Work.Peluse.FinSuppZ f) :
    Work.Peluse.LadderP.Swap.pbox 1 q₁ q₂ M S f
      = ((S.card : ℝ))⁻¹ * ((M : ℝ) ^ 4)⁻¹ *
          ∑' x : ℤ, ‖∑ m : Fin M × Fin M,
            f (x + Work.Peluse.LadderP.Swap.pdir (q₁ 0) (q₂ 0) m)‖ ^ 2 := by
  classical
  have hdir : (fun (k : Fin 1) (m : Fin M × Fin M) =>
        Work.Peluse.LadderP.Swap.pdir (q₁ k) (q₂ k) m)
      = fun (_ : Fin 1) => (fun m : Fin M × Fin M =>
        Work.Peluse.LadderP.Swap.pdir (q₁ 0) (q₂ 0) m) := by
    funext k m
    have hk : k = 0 := Subsingleton.elim k 0
    rw [hk]
  rw [Work.Peluse.SwapC.pbox_eq_mCubeSum, hdir,
    mCubeSumOneGram (fun m : Fin M × Fin M =>
      Work.Peluse.LadderP.Swap.pdir (q₁ 0) (q₂ 0) m) S f hf]
  have hnorm : ‖(S.card : ℂ)⁻¹ * (((Fintype.card (Fin M × Fin M) : ℂ))⁻¹) ^ 2 *
        ((∑' x : ℤ, ‖∑ k : Fin M × Fin M,
          f (x + (fun m : Fin M × Fin M =>
            Work.Peluse.LadderP.Swap.pdir (q₁ 0) (q₂ 0) m) k)‖ ^ 2 : ℝ) : ℂ)‖
      = ((S.card : ℝ))⁻¹ * ((M : ℝ) ^ 4)⁻¹ *
        ∑' x : ℤ, ‖∑ k : Fin M × Fin M,
          f (x + (fun m : Fin M × Fin M =>
            Work.Peluse.LadderP.Swap.pdir (q₁ 0) (q₂ 0) m) k)‖ ^ 2 := by
    rw [norm_mul, norm_mul, norm_pow, cz_norm_natCast_inv, cz_norm_natCast_inv,
      cz_norm_ofReal, abs_of_nonneg (tsum_nonneg (fun x => sq_nonneg _)), card_prod_fin_inv_sq]
  rw [hnorm]

end

end Work.Peluse.SwapCS0

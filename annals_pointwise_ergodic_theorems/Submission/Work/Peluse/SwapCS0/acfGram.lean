import Mathlib
import Submission.Work.Peluse.SwapCS0.gramShift

/-!
# The Gram expansion of the `ℓ²`-mass of the bilinear shift sum

`acfGram` expands the squared `ℓ²`-mass
`∑_x (∑_i ∑_c ∑_{c'} f (x + a i (c - c'))) · conj (∑_i ∑_c ∑_{c'} f (x + a i (c - c')))`
as the double sum over pairs of shifts of the (shifted) autocorrelation of `f`.  This is the
elementary "expand the square and swap the order of summation" identity, made legitimate by the
finite support of `f` (every `tsum` below is really a finite sum): the pairs of shifts of the two
factors are regrouped as `(i, c, c')` and `(j, d, d')`, and then relabelled by the bijection
`((i, (c,c')), (j, (d,d'))) ↦ ((i,j), ((c,d),(c',d')))`.

The proof reduces the left-hand side to the squared `ℓ²`-norm of the shifted sum and appeals to
`Work.Peluse.SwapCS0.gramShift`, then reindexes the double sum along the bijection `eSwap`.
-/

namespace Work.Peluse.SwapCS0

open scoped BigOperators

/-- A complex number whose norm square is written as a real number is `z * conj z`. -/
private lemma ofReal_normSq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
  simp [Complex.sq_norm, Complex.mul_conj]

/-- The reindexing bijection of the double shift sum: it swaps the two `I`-coordinates and
transposes the two `Fin M × Fin M`-pairs. -/
private def eSwap (I : Type) (M : ℕ) :
    ((I × (Fin M × Fin M)) × (I × (Fin M × Fin M)))
      ≃ (I × I) × ((Fin M × Fin M) × (Fin M × Fin M)) where
  toFun q := ((q.2.1, q.1.1), ((q.1.2.1, q.2.2.1), (q.1.2.2, q.2.2.2)))
  invFun p := ((p.1.2, (p.2.1.1, p.2.2.1)), (p.1.1, (p.2.1.2, p.2.2.2)))
  left_inv := by rintro ⟨⟨i, ⟨c, c'⟩⟩, ⟨j, ⟨d, d'⟩⟩⟩; rfl
  right_inv := by rintro ⟨⟨i, j⟩, ⟨⟨c, c'⟩, ⟨d, d'⟩⟩⟩; rfl

theorem acfGram {I : Type} [Fintype I] (M : ℕ) (a : I → ℤ) (f : ℤ → ℂ) (S₀ : Finset ℤ)
    (hsup : ∀ x : ℤ, x ∉ S₀ → f x = 0) :
    (∑' x : ℤ, (∑ i : I, ∑ c : Fin M, ∑ c' : Fin M, f (x + a i * ((c : ℤ) - (c' : ℤ))))
        * star (∑ i : I, ∑ c : Fin M, ∑ c' : Fin M, f (x + a i * ((c : ℤ) - (c' : ℤ)))))
      = ∑ i : I, ∑ j : I, ∑ m : Fin M × Fin M, ∑ m' : Fin M × Fin M,
          ∑' x : ℤ, f (x + (a j * ((m.1 : ℤ) - (m'.1 : ℤ))
                - a i * ((m.2 : ℤ) - (m'.2 : ℤ)))) * star (f x) := by
  classical
  -- `f` is finitely supported, so every sum below is finite.
  have hf : Work.Peluse.FinSuppZ f :=
    ⟨S₀.sup (fun x : ℤ => x.natAbs), fun x hx => hsup x (fun hmem => by
      have h := Finset.le_sup (f := fun x : ℤ => x.natAbs) hmem
      omega)⟩
  -- The shift attached to the index `(i, c, c')`.
  set σ : I × (Fin M × Fin M) → ℤ := fun k => a k.1 * ((k.2.1 : ℤ) - (k.2.2 : ℤ)) with hσ
  -- The inner sum of the left-hand side, indexed by the product `I × (Fin M × Fin M)`.
  have hA : ∀ x : ℤ, (∑ k : I × (Fin M × Fin M), f (x + σ k))
      = ∑ i : I, ∑ c : Fin M, ∑ c' : Fin M, f (x + a i * ((c : ℤ) - (c' : ℤ))) := by
    intro x
    rw [hσ, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Fintype.sum_prod_type]
  -- Step 1: the left-hand side is the squared `ℓ²`-norm of the shifted sum.
  have hL : (∑' x : ℤ, (∑ i : I, ∑ c : Fin M, ∑ c' : Fin M,
          f (x + a i * ((c : ℤ) - (c' : ℤ))))
        * star (∑ i : I, ∑ c : Fin M, ∑ c' : Fin M, f (x + a i * ((c : ℤ) - (c' : ℤ)))))
      = ((∑' x : ℤ, ‖∑ k : I × (Fin M × Fin M), f (x + σ k)‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr (fun x => ?_)
    rw [← hA x]
    exact (ofReal_normSq _).symm
  -- The Gram form of the double sum, and the target form of the double sum.
  let FG : (I × (Fin M × Fin M)) × (I × (Fin M × Fin M)) → ℂ :=
    fun q => ∑' x : ℤ, f (x + (σ q.1 - σ q.2)) * star (f x)
  let FT : (I × I) × ((Fin M × Fin M) × (Fin M × Fin M)) → ℂ :=
    fun p => ∑' x : ℤ, f (x + (a p.1.2 * ((p.2.1.1 : ℤ) - (p.2.2.1 : ℤ))
        - a p.1.1 * ((p.2.1.2 : ℤ) - (p.2.2.2 : ℤ)))) * star (f x)
  -- The `gramShift` right-hand side is `∑ q, FG q`.
  have hgram : (∑ k : I × (Fin M × Fin M), ∑ k' : I × (Fin M × Fin M),
        ∑' x : ℤ, f (x + (σ k - σ k')) * star (f x))
      = ∑ q : (I × (Fin M × Fin M)) × (I × (Fin M × Fin M)), FG q := by
    rw [show (∑ q : (I × (Fin M × Fin M)) × (I × (Fin M × Fin M)), FG q)
          = ∑ k : I × (Fin M × Fin M), ∑ k' : I × (Fin M × Fin M), FG (k, k')
        from Fintype.sum_prod_type FG]
  -- The target right-hand side is `∑ p, FT p`.
  have htarget : (∑ i : I, ∑ j : I, ∑ m : Fin M × Fin M, ∑ m' : Fin M × Fin M,
          ∑' x : ℤ, f (x + (a j * ((m.1 : ℤ) - (m'.1 : ℤ))
                - a i * ((m.2 : ℤ) - (m'.2 : ℤ)))) * star (f x))
      = ∑ p : (I × I) × ((Fin M × Fin M) × (Fin M × Fin M)), FT p := by
    rw [show (∑ p : (I × I) × ((Fin M × Fin M) × (Fin M × Fin M)), FT p)
          = ∑ x : I × I, ∑ y : (Fin M × Fin M) × (Fin M × Fin M), FT (x, y)
        from Fintype.sum_prod_type FT]
    rw [show (∑ x : I × I, ∑ y : (Fin M × Fin M) × (Fin M × Fin M), FT (x, y))
          = ∑ i : I, ∑ j : I, ∑ y : (Fin M × Fin M) × (Fin M × Fin M), FT ((i, j), y)
        from Fintype.sum_prod_type (f := fun x : I × I =>
          ∑ y : (Fin M × Fin M) × (Fin M × Fin M), FT (x, y))]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [show (∑ y : (Fin M × Fin M) × (Fin M × Fin M), FT ((i, j), y))
          = ∑ m : Fin M × Fin M, ∑ m' : Fin M × Fin M, FT ((i, j), (m, m'))
        from Fintype.sum_prod_type (f := fun y : (Fin M × Fin M) × (Fin M × Fin M) =>
          FT ((i, j), y))]
  -- Step 3: the two double sums agree, by the bijection `eSwap`.
  have hmid : (∑ q : (I × (Fin M × Fin M)) × (I × (Fin M × Fin M)), FG q)
      = ∑ p : (I × I) × ((Fin M × Fin M) × (Fin M × Fin M)), FT p := by
    rw [← Equiv.sum_comp (eSwap I M) FT]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    show FG q = FT (eSwap I M q)
    refine tsum_congr (fun x => ?_)
    show f (x + (σ q.1 - σ q.2)) * star (f x) =
      f (x + (a (eSwap I M q).1.2 * (((eSwap I M q).2.1.1 : ℤ) - ((eSwap I M q).2.2.1 : ℤ))
        - a (eSwap I M q).1.1 * (((eSwap I M q).2.1.2 : ℤ) - ((eSwap I M q).2.2.2 : ℤ))))
        * star (f x)
    rw [hσ]
    rfl
  -- Step 2: `gramShift` and the assembly.
  rw [hL, gramShift σ f hf]
  exact hgram.trans (hmid.trans htarget.symm)

end Work.Peluse.SwapCS0

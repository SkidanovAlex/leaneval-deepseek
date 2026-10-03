import Mathlib
import Submission.Work.Peluse.SwapC.Basic

namespace Work.Peluse.SwapC

open scoped BigOperators

noncomputable section

open Work.Peluse
open Work.Peluse.LadderP.Swap

/-! ## Auxiliary: the multiset box sum over an arbitrary finite index type

`pboxSum` is the box sum along the multiset slots `q₁ k·[M] − q₂ k·[M]`, i.e. the sum over
`h : Fin d → Fin M × Fin M` of the cube term with directions `pdir (q₁ k) (q₂ k) (h k)`.  The two
ingredients of the "sum of squares" identity behind the box norm do not use anything about the
index set `Fin M × Fin M`, so we state them for a general finite index type `X` and a general
direction map `ν : Fin d → X → ℤ`, and only specialise at the end.
-/

/-- The **raw** (unnormalised) multiset box sum of order `d` over the index type `X` with
directions `ν k : X → ℤ`: `∑_{h,h' ∈ X^d} ∑_x ∏_ω C^{|ω|} f (x + ω·h + (1−ω)·h')`.  It is
`mCubeSum` without the normalising constant. -/
def mRawSum (d : ℕ) (X : Type) [Fintype X] (ν : Fin d → X → ℤ) (f : ℤ → ℂ) : ℂ :=
  ∑ h : Fin d → X, ∑ h' : Fin d → X, ∑' x : ℤ,
    ∏ ω : Fin d → Bool, (star^[weight ω])
      (f (x + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω))

/-- The lower-dimensional cube term obtained after peeling the first slot: the product
`∏_{τ : Fin k → Bool} C^{|τ|} f (u + cornerShift hs hs' τ)` over the *tail* directions
`ν i.succ ∘ hs`. -/
def mRed (k : ℕ) {X : Type} (ν : Fin (k+1) → X → ℤ) (f : ℤ → ℂ)
    (hs hs' : Fin k → X) (u : ℤ) : ℂ :=
  ∏ τ : Fin k → Bool, (star^[weight τ])
    (f (u + cornerShift (fun i => ν i.succ (hs i)) (fun i => ν i.succ (hs' i)) τ))

/-- Splitting a sum over the constant family `Fin (k+1) → X` into its head `a : X` and its
tail `hs : Fin k → X` (the constant-family case of `Work.Peluse.BoxNorm.Aux.sum_cons_equiv`). -/
lemma sum_cons_equiv_gen {k : ℕ} {X : Type} [Fintype X] (F : (Fin (k+1) → X) → ℂ) :
    ∑ h : Fin (k+1) → X, F h = ∑ hs : Fin k → X, ∑ a : X, F (Fin.cons a hs) := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (k+1) => X)) F]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [Work.Peluse.BoxNorm.Aux.consEquiv_eq_cons]

/-- The direction sequence of the head `a` and the tail `hs` of a shift tuple. -/
lemma cons_dir {k : ℕ} {X : Type} (ν : Fin (k+1) → X → ℤ) (a : X) (hs : Fin k → X) :
    (fun i : Fin (k+1) => ν i ((Fin.cons a hs : Fin (k+1) → X) i))
      = Fin.cons (ν 0 a) (fun i : Fin k => ν i.succ (hs i)) := by
  funext i
  refine Fin.cases ?_ ?_ i <;> simp

/-- **Splitting the cube term along the first slot** (the multiset analogue of
`Work.Peluse.BoxNorm.cubeTerm_cons`): the cube term of order `k+1` with shifts
`Fin.cons a hs`, `Fin.cons b hs'` is the product of the lower-dimensional cube term shifted by
`ν 0 b` and the conjugate of the one shifted by `ν 0 a`. -/
theorem mCubeTerm_cons {k : ℕ} {X : Type} (ν : Fin (k+1) → X → ℤ) (f : ℤ → ℂ)
    (a b : X) (hs hs' : Fin k → X) (x : ℤ) :
    (∏ ω : Fin (k+1) → Bool, (star^[weight ω])
        (f (x + cornerShift (fun i => ν i ((Fin.cons a hs : Fin (k+1) → X) i))
                              (fun i => ν i ((Fin.cons b hs' : Fin (k+1) → X) i)) ω)))
      = mRed k ν f hs hs' (x + ν 0 b) * star (mRed k ν f hs hs' (x + ν 0 a)) := by
  rw [cons_dir ν a hs, cons_dir ν b hs']
  exact Work.Peluse.BoxNorm.cubeTerm_cons (ν 0 a) (ν 0 b) (fun i => ν i.succ (hs i))
    (fun i => ν i.succ (hs' i)) f x

/-- The double sum over the head of the two shift tuples is a sum of squares. -/
private theorem mInner {k : ℕ} {X : Type} [Fintype X] (ν : Fin (k+1) → X → ℤ) (f : ℤ → ℂ)
    (hs hs' : Fin k → X) (x : ℤ) :
    (∑ a : X, ∑ b : X, (∏ ω : Fin (k+1) → Bool, (star^[weight ω])
        (f (x + cornerShift (fun i => ν i ((Fin.cons a hs : Fin (k+1) → X) i))
                              (fun i => ν i ((Fin.cons b hs' : Fin (k+1) → X) i)) ω))))
      = ((‖∑ a : X, mRed k ν f hs hs' (x + ν 0 a)‖ ^ 2 : ℝ) : ℂ) := by
  simp only [mCubeTerm_cons ν f]
  exact Work.Peluse.BoxNorm.sum_pairs_star_eq_normSq (fun a : X => mRed k ν f hs hs' (x + ν 0 a))

/-- **The raw multiset box sum is a nonnegative real.**  This is the sum-of-squares identity of
the box norm, run once (the index sets are arbitrary finite types, so multiplicities of the
directions are harmless). -/
theorem mRawSum_real_nonneg (d : ℕ) (hd : 1 ≤ d) (X : Type) [Fintype X]
    (ν : Fin d → X → ℤ) (f : ℤ → ℂ) (hf : FinSuppZ f) :
    ∃ r : ℝ, 0 ≤ r ∧ mRawSum d X ν f = (r : ℂ) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  obtain ⟨N, hN⟩ := hf
  set Q : Fin (k + 1) → Finset ℤ := fun i => Finset.image (ν i) Finset.univ with hQ
  set B : Finset ℤ := Finset.Icc (-(((N + ∑ i, (Q i).sum (fun z => z.natAbs)) : ℕ) : ℤ))
      ((((N + ∑ i, (Q i).sum (fun z => z.natAbs)) : ℕ) : ℤ)) with hB
  have hmem : ∀ h : Fin (k+1) → X, ∀ i, ν i (h i) ∈ Q i := by
    intro h i; rw [hQ]; exact Finset.mem_image.mpr ⟨h i, Finset.mem_univ _, rfl⟩
  have htsum : ∀ h h' : Fin (k+1) → X,
      (∑' x : ℤ, ∏ ω : Fin (k+1) → Bool, (star^[weight ω])
        (f (x + cornerShift (fun i => ν i (h i)) (fun i => ν i (h' i)) ω)))
      = ∑ x ∈ B, ∏ ω : Fin (k+1) → Bool, (star^[weight ω])
        (f (x + cornerShift (fun i => ν i (h i)) (fun i => ν i (h' i)) ω)) := by
    intro h h'
    have h1 := Work.Peluse.BoxNorm.cubeTerm_tsum_finite Q f hN
      (fun i => (⟨ν i (h i), hmem h i⟩ : ↥(Q i)))
      (fun i => (⟨ν i (h' i), hmem h' i⟩ : ↥(Q i)))
    simpa [hB] using h1
  have hmain : mRawSum (k+1) X ν f =
      ((∑ hs : Fin k → X, ∑ hs' : Fin k → X, ∑ x ∈ B,
          ‖∑ a : X, mRed k ν f hs hs' (x + ν 0 a)‖ ^ 2 : ℝ) : ℂ) := by
    rw [mRawSum]
    simp only [htsum]
    simp only [sum_cons_equiv_gen]
    rw [Work.Peluse.BoxNorm.Aux.reorder_pair (A := X) (H := Fin k → X) (X := ℤ) B
      (fun hs a hs' b x => ∏ ω : Fin (k+1) → Bool, (star^[weight ω])
        (f (x + cornerShift (fun i => ν i ((Fin.cons a hs : Fin (k+1) → X) i))
                              (fun i => ν i ((Fin.cons b hs' : Fin (k+1) → X) i)) ω)))]
    refine (Finset.sum_congr rfl (fun hs _ => Finset.sum_congr rfl (fun hs' _ =>
      Finset.sum_congr rfl (fun x _ => mInner ν f hs hs' x)))).trans ?_
    simp only [Complex.ofReal_sum]
  exact ⟨_, by positivity, hmain⟩

/-- **`pboxSum` is a nonnegative real** (for `1 ≤ d`), so that `pbox = ‖pboxSum‖` is the real
number `pboxSum.re`: the analogue for the multiset slots of the workspace's proved
`Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow`.

Proof route (mirror of `BoxNorm/boxSumPow_eq_boxNormPow.lean`): induction on `d`.  At `d = 1` the
summand `∏_{ω : Fin 1 → Bool} C^{|ω|} f (x + cornerShift (d m) (d m') ω)` is
`star (f (x + d m)) * f (x + d m')`, so the double sum over `m, m'` is
`‖∑_m f (x + d m)‖ ^ 2`.  For `d + 1` use `pbox_peel` (or its proof) to write `pboxSum (d+1)` as
`((M:ℂ)^4)⁻¹ * ∑_{m,m'} pboxSum d (tail) (tail) (DeltaP …)`, which is a sum of coerced nonnegative
reals.  `FinSuppZ f` makes the `tsum` over `x` finite (`cubeTerm_tsum_finite`-style argument: the
`ω = false` corner forces `x + ∑_k pdir … (h' k) ∈ supp f`). -/
theorem pboxSum_real_nonneg (d : ℕ) (hd : 1 ≤ d) (q₁ q₂ : Fin d → ℤ) (M : ℕ) (S : Finset ℤ)
    (f : ℤ → ℂ) (hf : Work.Peluse.FinSuppZ f) :
    ∃ r : ℝ, 0 ≤ r ∧ Work.Peluse.LadderP.Swap.pboxSum d q₁ q₂ M S f = (r : ℂ) := by
  obtain ⟨r, hr, hmr⟩ :=
    mRawSum_real_nonneg d hd (Fin M × Fin M) (fun k m => pdir (q₁ k) (q₂ k) m) f hf
  refine ⟨((S.card : ℝ))⁻¹ * (((Fintype.card (Fin M × Fin M) : ℝ))⁻¹) ^ (2 * d) * r, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) hr
  · have hS : ((S.card : ℂ))⁻¹ = Complex.ofReal ((S.card : ℝ)⁻¹) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
    have hC : ((Fintype.card (Fin M × Fin M) : ℂ))⁻¹
        = Complex.ofReal ((Fintype.card (Fin M × Fin M) : ℝ)⁻¹) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
    have hunfold : Work.Peluse.LadderP.Swap.pboxSum d q₁ q₂ M S f
        = ((S.card : ℂ))⁻¹ * ((Fintype.card (Fin M × Fin M) : ℂ)⁻¹) ^ (2 * d)
          * mRawSum d (Fin M × Fin M) (fun k m => pdir (q₁ k) (q₂ k) m) f := by
      rw [pboxSum_eq_mCubeSum]
      rfl
    rw [hunfold, hmr, hS, hC, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul]

end

end Work.Peluse.SwapC

import Mathlib
import Submission.Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow

namespace Work.Peluse.PET

/-!
# Degenerating the last coordinate of the box norm

If the last set `Q (Fin.last n)` is the singleton `{0}`, then the `2^{n+1}`-th power of the
Gowers box norm of order `n+1` collapses to the `2^n`-th power of order `n` taken on the
squared modulus `|f|²`:

`‖f‖^{2^{n+1}}_{□^{n+1}_{Q₁,…,Q_n,{0}}(S)} = ‖|f|²‖^{2^n}_{□^n_{Q₁,…,Q_n}(S)}`.

This is the "degenerate last coordinate" identity of the box-norm calculus: the two faces
`ω (last n) = 0` and `ω (last n) = 1` of the cube contribute a complex number and its conjugate.
-/

open scoped BigOperators

/-! ## Elementary bookkeeping for `weight`, `cornerShift`, `Fin.snoc` -/

private lemma weight_eq_sum {t : ℕ} (ω : Fin t → Bool) :
    Work.Peluse.weight ω = ∑ i : Fin t, if ω i then 1 else 0 := by
  rw [Work.Peluse.weight, Finset.card_filter]

private lemma weight_snoc {n : ℕ} (τ : Fin n → Bool) (c : Bool) :
    Work.Peluse.weight (Fin.snoc τ c)
      = Work.Peluse.weight τ + (if c then 1 else 0) := by
  simp only [weight_eq_sum]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

private lemma cornerShift_snoc {n : ℕ} (hs hs' : Fin n → ℤ) (a b : ℤ)
    (τ : Fin n → Bool) (c : Bool) :
    Work.Peluse.cornerShift (Fin.snoc hs a) (Fin.snoc hs' b) (Fin.snoc τ c)
      = Work.Peluse.cornerShift hs hs' τ + (if c then a else b) := by
  rw [Work.Peluse.cornerShift, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [Work.Peluse.cornerShift]

private lemma prod_univ_snoc_bool {n : ℕ} (F : (Fin (n + 1) → Bool) → ℂ) :
    ∏ ω : Fin (n + 1) → Bool, F ω = ∏ c : Bool, ∏ τ : Fin n → Bool, F (Fin.snoc τ c) := by
  have h : ∀ p : Bool × (Fin n → Bool),
      (Fin.snocEquiv (fun _ : Fin (n + 1) => Bool)) p = Fin.snoc p.2 p.1 := by
    intro p
    funext i
    rw [Fin.snocEquiv_apply]
  calc ∏ ω : Fin (n + 1) → Bool, F ω
      = ∏ p : Bool × (Fin n → Bool),
          F ((Fin.snocEquiv (fun _ : Fin (n + 1) => Bool)) p) := (Equiv.prod_comp _ F).symm
    _ = ∏ p : Bool × (Fin n → Bool), F (Fin.snoc p.2 p.1) := by
          refine Finset.prod_congr rfl (fun p _ => ?_)
          rw [h p]
    _ = ∏ c : Bool, ∏ τ : Fin n → Bool, F (Fin.snoc τ c) :=
          Fintype.prod_prod_type (fun p : Bool × (Fin n → Bool) => F (Fin.snoc p.2 p.1))

private lemma star_iterate_succ' (k : ℕ) (z : ℂ) : (star^[k + 1]) z = star ((star^[k]) z) :=
  Function.iterate_succ_apply' star k z

private lemma norm_star_iterate (k : ℕ) (w : ℂ) : ‖(star^[k]) w‖ = ‖w‖ := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', norm_star, ih]

private lemma star_iterate_of_star_fixed {k : ℕ} {w : ℂ} (hw : star w = w) :
    (star^[k]) w = w := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih, hw]

private lemma mul_star_eq_normSq (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

private lemma star_iterate_ofReal (k : ℕ) (r : ℝ) : (star^[k]) ((r : ℝ) : ℂ) = ((r : ℝ) : ℂ) :=
  star_iterate_of_star_fixed (by simp)


/-! ## The degenerate last coordinate -/

open Work.Peluse.BoxNorm

private def snocEndEquiv {n : ℕ} (Q : Fin (n + 1) → Finset ℤ) (hQ : Q (Fin.last n) = {0}) :
    ((i : Fin n) → {x : ℤ // x ∈ Q i.castSucc}) ≃ ((i : Fin (n + 1)) → {x : ℤ // x ∈ Q i}) where
  toFun hs := Fin.snoc hs ⟨0, by rw [hQ]; exact Finset.mem_singleton_self 0⟩
  invFun h := fun i => h i.castSucc
  left_inv hs := by
    funext i
    exact Fin.snoc_castSucc _ _ i
  right_inv h := by
    funext i
    show Fin.snoc (α := fun i : Fin (n + 1) => {x : ℤ // x ∈ Q i})
      (fun j : Fin n => h j.castSucc)
      ⟨0, by rw [hQ]; exact Finset.mem_singleton_self 0⟩ i = h i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.snoc_last]
      refine Subtype.ext ?_
      have hh : (h (Fin.last n)).1 ∈ ({0} : Finset ℤ) := by
        rw [← hQ]; exact (h (Fin.last n)).2
      exact (Finset.mem_singleton.mp hh).symm
    · exact Fin.snoc_castSucc _ _ j

private lemma snocEndEquiv_apply {n : ℕ} (Q : Fin (n + 1) → Finset ℤ) (hQ : Q (Fin.last n) = {0})
    (hs : (i : Fin n) → {x : ℤ // x ∈ Q i.castSucc}) :
    snocEndEquiv Q hQ hs = Fin.snoc hs ⟨0, by rw [hQ]; exact Finset.mem_singleton_self 0⟩ := rfl

/-- The cube term of order `n+1` whose last set is `{0}` equals the cube term of order `n` of the
squared modulus.  The two faces `ω (last n) = false` and `ω (last n) = true` contribute `z` and
`star z`, and `z * star z = ‖z‖²`. -/
private lemma cubeTerm_snoc_zero {n : ℕ} (hs hs' : Fin n → ℤ) (f : ℤ → ℂ) (x : ℤ) :
    (∏ ω : Fin (n + 1) → Bool,
        (star^[Work.Peluse.weight ω])
          (f (x + Work.Peluse.cornerShift (Fin.snoc hs 0) (Fin.snoc hs' 0) ω)))
      = ∏ τ : Fin n → Bool,
          (star^[Work.Peluse.weight τ])
            ((fun y : ℤ => ((‖f y‖ ^ 2 : ℝ) : ℂ))
              (x + Work.Peluse.cornerShift hs hs' τ)) := by
  classical
  have hpair : ∀ τ : Fin n → Bool,
      (star^[Work.Peluse.weight (Fin.snoc τ true)])
          (f (x + Work.Peluse.cornerShift (Fin.snoc hs 0) (Fin.snoc hs' 0) (Fin.snoc τ true)))
        * (star^[Work.Peluse.weight (Fin.snoc τ false)])
          (f (x + Work.Peluse.cornerShift (Fin.snoc hs 0) (Fin.snoc hs' 0) (Fin.snoc τ false)))
        = ((‖(star^[Work.Peluse.weight τ])
              (f (x + Work.Peluse.cornerShift hs hs' τ))‖ ^ 2 : ℝ) : ℂ) := by
    intro τ
    have htrue : (star^[Work.Peluse.weight (Fin.snoc τ true)])
          (f (x + Work.Peluse.cornerShift (Fin.snoc hs 0) (Fin.snoc hs' 0) (Fin.snoc τ true)))
        = star ((star^[Work.Peluse.weight τ])
            (f (x + Work.Peluse.cornerShift hs hs' τ))) := by
      rw [weight_snoc, cornerShift_snoc]
      simp only [if_true, add_zero]
      rw [star_iterate_succ']
    have hfalse : (star^[Work.Peluse.weight (Fin.snoc τ false)])
          (f (x + Work.Peluse.cornerShift (Fin.snoc hs 0) (Fin.snoc hs' 0) (Fin.snoc τ false)))
        = (star^[Work.Peluse.weight τ]) (f (x + Work.Peluse.cornerShift hs hs' τ)) := by
      rw [weight_snoc, cornerShift_snoc]
      simp
    rw [htrue, hfalse, mul_comm, mul_star_eq_normSq]
  rw [prod_univ_snoc_bool, Fintype.prod_bool, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun τ _ => ?_)
  rw [hpair τ]
  show ((‖(star^[Work.Peluse.weight τ])
        (f (x + Work.Peluse.cornerShift hs hs' τ))‖ ^ 2 : ℝ) : ℂ)
      = (star^[Work.Peluse.weight τ])
        (((‖f (x + Work.Peluse.cornerShift hs hs' τ)‖ ^ 2 : ℝ) : ℂ))
  rw [star_iterate_ofReal, norm_star_iterate]

private lemma rawSum_last_singleton {n : ℕ} (Q : Fin (n + 1) → Finset ℤ)
    (hQ : Q (Fin.last n) = {0}) (f : ℤ → ℂ) :
    rawSum (n + 1) Q f
      = rawSum n (fun i : Fin n => Q i.castSucc) (fun x : ℤ => ((‖f x‖ ^ 2 : ℝ) : ℂ)) := by
  classical
  have hterm : ∀ (hs hs' : (i : Fin n) → {x : ℤ // x ∈ Q i.castSucc}) (x : ℤ),
      cubeTermZ Q f (snocEndEquiv Q hQ hs) (snocEndEquiv Q hQ hs') x
        = cubeTermZ (fun i : Fin n => Q i.castSucc)
            (fun x : ℤ => ((‖f x‖ ^ 2 : ℝ) : ℂ)) hs hs' x := by
    intro hs hs' x
    have h1 : (fun i : Fin (n + 1) => ((snocEndEquiv Q hQ) hs i).1)
        = Fin.snoc (fun i : Fin n => (hs i).1) (0 : ℤ) := by
      funext i
      rw [snocEndEquiv_apply]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last, Fin.snoc_last]
      · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
    have h2 : (fun i : Fin (n + 1) => ((snocEndEquiv Q hQ) hs' i).1)
        = Fin.snoc (fun i : Fin n => (hs' i).1) (0 : ℤ) := by
      funext i
      rw [snocEndEquiv_apply]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last, Fin.snoc_last]
      · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
    show (∏ ω : Fin (n + 1) → Bool,
        (star^[Work.Peluse.weight ω])
          (f (x + Work.Peluse.cornerShift (fun i => ((snocEndEquiv Q hQ) hs i).1)
            (fun i => ((snocEndEquiv Q hQ) hs' i).1) ω)))
      = ∏ τ : Fin n → Bool,
          (star^[Work.Peluse.weight τ])
            ((fun y : ℤ => ((‖f y‖ ^ 2 : ℝ) : ℂ))
              (x + Work.Peluse.cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) τ))
    rw [h1, h2]
    exact cubeTerm_snoc_zero (fun i : Fin n => (hs i).1) (fun i : Fin n => (hs' i).1) f x
  have step1 : (∑ h : (i : Fin (n + 1)) → {x : ℤ // x ∈ Q i},
        ∑ h' : (i : Fin (n + 1)) → {x : ℤ // x ∈ Q i},
          ∑' x : ℤ, cubeTermZ Q f h h' x)
      = ∑ hs : (i : Fin n) → {x : ℤ // x ∈ Q i.castSucc},
          ∑ h' : (i : Fin (n + 1)) → {x : ℤ // x ∈ Q i},
            ∑' x : ℤ, cubeTermZ Q f (snocEndEquiv Q hQ hs) h' x :=
    (Equiv.sum_comp (snocEndEquiv Q hQ)
      (fun h : (i : Fin (n + 1)) → {x : ℤ // x ∈ Q i} =>
        ∑ h' : (i : Fin (n + 1)) → {x : ℤ // x ∈ Q i}, ∑' x : ℤ, cubeTermZ Q f h h' x)).symm
  have step2 : ∀ hs : (i : Fin n) → {x : ℤ // x ∈ Q i.castSucc},
      (∑ h' : (i : Fin (n + 1)) → {x : ℤ // x ∈ Q i},
          ∑' x : ℤ, cubeTermZ Q f (snocEndEquiv Q hQ hs) h' x)
        = ∑ hs' : (i : Fin n) → {x : ℤ // x ∈ Q i.castSucc},
            ∑' x : ℤ, cubeTermZ Q f (snocEndEquiv Q hQ hs) (snocEndEquiv Q hQ hs') x :=
    fun hs => (Equiv.sum_comp (snocEndEquiv Q hQ)
      (fun h' : (i : Fin (n + 1)) → {x : ℤ // x ∈ Q i} =>
        ∑' x : ℤ, cubeTermZ Q f (snocEndEquiv Q hQ hs) h' x)).symm
  rw [rawSum, rawSum]
  refine step1.trans ?_
  refine (Finset.sum_congr rfl (fun hs _ => step2 hs)).trans ?_
  exact Finset.sum_congr rfl (fun hs _ => Finset.sum_congr rfl (fun hs' _ =>
    tsum_congr (fun x => hterm hs hs' x)))

private lemma boxScaling_last_singleton {n : ℕ} (Q : Fin (n + 1) → Finset ℤ) (S : Finset ℤ)
    (hQ : Q (Fin.last n) = {0}) :
    boxScaling (n + 1) Q S = boxScaling n (fun i : Fin n => Q i.castSucc) S := by
  rw [boxScaling, boxScaling, Fin.prod_univ_castSucc]
  have hcard : (Q (Fin.last n)).card = 1 := by rw [hQ]; simp
  rw [hcard]
  simp

/-- **Degenerate last coordinate.**  If the last set `Q (Fin.last n)` is the singleton `{0}`, the
`2^{n+1}`-th box-norm power of `f` of order `n+1` equals the `2^n`-th box-norm power of the
squared modulus `|f|²` of order `n` (with the remaining sets `Q i.castSucc`). -/
theorem boxSumPow_last_singleton {n : ℕ} (Q : Fin (n + 1) → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ)
    (hQ : Q (Fin.last n) = {0}) :
    Work.Peluse.boxSumPow (n + 1) Q S f
      = Work.Peluse.boxSumPow n (fun i : Fin n => Q i.castSucc) S
          (fun x : ℤ => ((‖f x‖ ^ 2 : ℝ) : ℂ)) := by
  rw [boxSumPow_eq_scaling (n + 1) Q S f,
    boxSumPow_eq_scaling n (fun i : Fin n => Q i.castSucc) S
      (fun x : ℤ => ((‖f x‖ ^ 2 : ℝ) : ℂ))]
  rw [boxScaling_last_singleton Q S hQ, rawSum_last_singleton Q hQ f]

end Work.Peluse.PET

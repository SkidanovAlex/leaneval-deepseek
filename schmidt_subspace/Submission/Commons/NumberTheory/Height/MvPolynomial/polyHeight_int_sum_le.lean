import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Int.Star
import Submission.Commons.NumberTheory.Height.Rat.mulHeight_int_le_norm
import Submission.Commons.NumberTheory.Height.mulHeight_finsupp_coe_eq

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Commons.NumberTheory.Height.MvPolynomial

/-!
# The height of a sum of integer polynomials

We prove a sharp `log s.card` bound on the logarithmic height of the coefficient tuple of a sum of
integer polynomials: if each summand has logarithmic height at most `H`, then the sum has
logarithmic height at most `H + log s.card`.

The key input is that for an integer tuple with a coordinate equal to `1`, the multiplicative
height over `ℚ` equals the supremum norm of the tuple: at every finite place the local supremum is
exactly `1` (all entries are integers and one entry is `1`), while over `ℚ` the single infinite
place contributes the ordinary supremum of the absolute values.
-/

/-- The supremum norm of an integer tuple, as a real number (i.e. `sup |x a|`). -/
noncomputable def intTupleAbsSup {α : Type*} (x : α → ℤ) : ℝ := ⨆ a, ((|x a| : ℤ) : ℝ)

/-- Over `ℚ` there is a single infinite place, with multiplicity one, so the archimedean factor
in the height formula collapses to the ordinary supremum of the absolute values. -/
lemma arch_infinitePlace_prod_eq {α : Type*} (x : α → ℚ) :
    (∏ v : NumberField.InfinitePlace ℚ, (⨆ a, v (x a)) ^ v.mult)
      = ⨆ a, ((|x a| : ℚ) : ℝ) := by
  rw [Fintype.prod_unique]
  have hd : ∀ a, (default : NumberField.InfinitePlace ℚ) (x a) = ((|x a| : ℚ) : ℝ) := by
    intro a
    rw [show (default : NumberField.InfinitePlace ℚ) = Rat.infinitePlace from
        Subsingleton.elim _ _, Rat.infinitePlace_apply]
  have hmult : (default : NumberField.InfinitePlace ℚ).mult = 1 := by
    rw [show (default : NumberField.InfinitePlace ℚ) = Rat.infinitePlace from
      Subsingleton.elim _ _]
    exact Rat.isReal_infinitePlace.mult_eq_one
  rw [hmult, pow_one,
    show (⨆ a, (default : NumberField.InfinitePlace ℚ) (x a)) = ⨆ a, ((|x a| : ℚ) : ℝ) from
      iSup_congr (fun a => hd a)]

/-- `intTupleAbsSup` agrees with the supremum of the absolute values after casting to `ℚ`. -/
lemma intTupleAbsSup_cast {α : Type*} (x : α → ℤ) :
    intTupleAbsSup x = ⨆ a, ((|(x a : ℚ)| : ℚ) : ℝ) := by
  unfold intTupleAbsSup
  apply iSup_congr
  intro a
  rw [← Int.cast_abs (R := ℚ)]
  norm_cast

/-- `intTupleAbsSup` dominates each of its entries. -/
lemma intTupleAbsSup_le {α : Type*} [Fintype α] (x : α → ℤ) (a : α) :
    ((|x a| : ℤ) : ℝ) ≤ intTupleAbsSup x := by
  unfold intTupleAbsSup
  exact Finite.le_ciSup (fun a => ((|x a| : ℤ) : ℝ)) a

/-- If an integer tuple has a coordinate equal to `1`, then the finite-place factor of its height
over `ℚ` equals `1`. -/
lemma one_le_finitePlace_finprod_of_eq_one {α : Type*} [Fintype α] [Nonempty α]
    (x : α → ℤ) (a₀ : α) (ha₀ : x a₀ = 1) :
    1 ≤ ∏ᶠ v : NumberField.FinitePlace ℚ, ⨆ a, v ((x a : ℚ)) := by
  apply one_le_finprod
  intro v
  have h1 : v ((x a₀ : ℚ)) = 1 := by rw [ha₀]; simp
  calc (1:ℝ) = v ((x a₀ : ℚ)) := h1.symm
    _ ≤ ⨆ a, v ((x a : ℚ)) := Finite.le_ciSup (fun a => v ((x a : ℚ))) a₀

/-- For an integer tuple with a coordinate equal to `1`, the multiplicative height over `ℚ` is the
supremum norm of the tuple. -/
lemma mulHeight_int_eq_intTupleAbsSup {α : Type*} [Fintype α] [Nonempty α]
    (x : α → ℤ) (a₀ : α) (ha₀ : x a₀ = 1) :
    Height.mulHeight (fun a => (x a : ℚ)) = intTupleAbsSup x := by
  have hxZ : x ≠ 0 := by
    intro h; have := congrFun h a₀; rw [ha₀] at this; exact one_ne_zero this
  have hx : (fun a => (x a : ℚ)) ≠ 0 := by
    intro h
    have := congrFun h a₀
    simp only [Pi.zero_apply] at this
    rw [ha₀] at this
    norm_num at this
  have hno : (∏ᶠ v : NumberField.FinitePlace ℚ, ⨆ a, v ((x a : ℚ))) = 1 :=
    le_antisymm (Commons.NumberTheory.Height.Rat.finitePlace_finprod_iSup_le_one x hxZ)
      (one_le_finitePlace_finprod_of_eq_one x a₀ ha₀)
  rw [NumberField.mulHeight_eq hx, arch_infinitePlace_prod_eq, hno, mul_one, intTupleAbsSup_cast]

/-- **Sharp height bound for a sum of integer tuples.**  Let `γ` be a finite index type with a
distinguished point `c`.  Suppose `g i c = 1` for all `i ∈ s`, that `φ c = 1`, and that away from
`c` the function `φ` is the pointwise sum of the `g i`.  If every `g i` (`i ∈ s`) has logarithmic
height at most `H`, then `φ` has logarithmic height at most `H + log s.card`. -/
lemma logHeight_int_sum_le {γ : Type*} [Fintype γ] {ι : Type*} (s : Finset ι) (c : γ)
    (g : ι → γ → ℤ) (φ : γ → ℤ) (H : ℝ) (hH0 : 0 ≤ H)
    (hg1 : ∀ i ∈ s, g i c = 1) (hφ1 : φ c = 1)
    (hφsum : ∀ a, a ≠ c → φ a = ∑ i ∈ s, g i a)
    (hH : ∀ i ∈ s, Height.logHeight (fun a : γ => (g i a : ℚ)) ≤ H) :
    Height.logHeight (fun a : γ => (φ a : ℚ)) ≤ H + Real.log s.card := by
  classical
  haveI : Nonempty γ := ⟨c⟩
  rcases s.eq_empty_or_nonempty with h0 | hs
  · subst h0
    rw [Height.logHeight_eq_log_mulHeight, mulHeight_int_eq_intTupleAbsSup φ c hφ1]
    have hφ0 : ∀ a, a ≠ c → φ a = 0 := by
      intro a ha; rw [hφsum a ha, Finset.sum_empty]
    have habs : intTupleAbsSup φ = 1 := by
      apply le_antisymm
      · unfold intTupleAbsSup
        refine ciSup_le (fun a => ?_)
        by_cases ha : a = c
        · subst ha; rw [hφ1]; simp
        · rw [hφ0 a ha]; simp
      · have h := intTupleAbsSup_le φ c
        rw [hφ1] at h
        simpa using h
    rw [habs, Real.log_one, Finset.card_empty, Nat.cast_zero, Real.log_zero, add_zero]
    exact hH0
  · have hbound_i : ∀ i ∈ s, intTupleAbsSup (g i) ≤ Real.exp H := by
      intro i hi
      have h1 := hH i hi
      rw [Height.logHeight_eq_log_mulHeight] at h1
      have h2 : Height.mulHeight (fun a : γ => (g i a : ℚ)) ≤ Real.exp H :=
        (Real.log_le_iff_le_exp (Height.mulHeight_pos _)).mp h1
      rwa [mulHeight_int_eq_intTupleAbsSup (g i) c (hg1 i hi)] at h2
    have hcoord : ∀ i ∈ s, ∀ a : γ, ((|g i a| : ℤ) : ℝ) ≤ Real.exp H :=
      fun i hi a => le_trans (intTupleAbsSup_le (g i) a) (hbound_i i hi)
    have hbound : intTupleAbsSup φ ≤ (s.card : ℝ) * Real.exp H := by
      unfold intTupleAbsSup
      refine ciSup_le (fun a => ?_)
      by_cases ha : a = c
      · subst ha
        rw [hφ1]
        have hcard : (1:ℝ) ≤ (s.card : ℝ) := by exact_mod_cast hs.card_pos
        have hexp : (1:ℝ) ≤ Real.exp H := Real.one_le_exp hH0
        simp only [abs_one, Int.cast_one]
        nlinarith
      · rw [hφsum a ha]
        have h1 : ((|(∑ i ∈ s, g i a)| : ℤ) : ℝ) ≤ ∑ i ∈ s, Real.exp H := by
          rw [Int.cast_abs, Int.cast_sum]
          calc |∑ i ∈ s, ((g i a : ℤ) : ℝ)|
              ≤ ∑ i ∈ s, |((g i a : ℤ) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
            _ = ∑ i ∈ s, ((|g i a| : ℤ) : ℝ) := by
                apply Finset.sum_congr rfl; intro i _
                rw [Int.cast_abs]
            _ ≤ ∑ i ∈ s, Real.exp H := Finset.sum_le_sum (fun i hi => hcoord i hi a)
        calc ((|(∑ i ∈ s, g i a)| : ℤ) : ℝ) ≤ ∑ i ∈ s, Real.exp H := h1
          _ = (s.card : ℝ) * Real.exp H := by
              rw [Finset.sum_const, nsmul_eq_mul]
    have hpos : 0 < intTupleAbsSup φ := by
      have h := intTupleAbsSup_le φ c
      rw [hφ1] at h
      simp only [abs_one, Int.cast_one] at h
      exact lt_of_lt_of_le zero_lt_one h
    rw [Height.logHeight_eq_log_mulHeight, mulHeight_int_eq_intTupleAbsSup φ c hφ1]
    calc Real.log (intTupleAbsSup φ) ≤ Real.log ((s.card : ℝ) * Real.exp H) :=
          Real.log_le_log hpos hbound
      _ = H + Real.log (s.card : ℝ) := by
          rw [Real.log_mul (Nat.cast_ne_zero.mpr hs.card_pos.ne') (Real.exp_pos H).ne',
            Real.log_exp]; ring

/-- **Sharp height bound for a sum of integer polynomials.**  If the coefficient tuples of the
polynomials `P i` (for `i ∈ s`) all have logarithmic height at most `H`, then the coefficient tuple
of the sum `∑ i ∈ s, P i` has logarithmic height at most `H + log s.card`. -/
theorem polyHeight_int_sum_le {σ ι : Type*} [Fintype σ] (s : Finset ι)
    (P : ι → MvPolynomial σ ℤ) (H : ℝ) (hH0 : 0 ≤ H)
    (hH : ∀ i ∈ s, Height.logHeight (fun o : Option (σ →₀ ℕ) =>
      o.elim (1 : ℚ) (fun m => MvPolynomial.coeff m ((P i).map (Int.castRingHom ℚ)))) ≤ H) :
    Height.logHeight (fun o : Option (σ →₀ ℕ) =>
      o.elim (1 : ℚ) (fun m => MvPolynomial.coeff m ((∑ i ∈ s, P i).map (Int.castRingHom ℚ))))
      ≤ H + Real.log s.card := by
  classical
  have hPi : ∀ i, (fun o : Option (σ →₀ ℕ) =>
      o.elim (1 : ℚ) (fun m => MvPolynomial.coeff m ((P i).map (Int.castRingHom ℚ))))
      = fun o => ((o.elim (1:ℤ) (fun m => (P i).coeff m) : ℤ) : ℚ) := by
    intro i; funext o; cases o <;> simp [MvPolynomial.coeff_map]
  have hsum : (fun o : Option (σ →₀ ℕ) =>
      o.elim (1 : ℚ) (fun m => MvPolynomial.coeff m ((∑ i ∈ s, P i).map (Int.castRingHom ℚ))))
      = fun o => ((o.elim (1:ℤ) (fun m => (∑ i ∈ s, P i).coeff m) : ℤ) : ℚ) := by
    funext o; cases o <;> simp [MvPolynomial.coeff_map, MvPolynomial.coeff_sum]
  rw [hsum]
  let G : ι → Option (σ →₀ ℕ) → ℤ := fun i o => o.elim (1:ℤ) (fun m => (P i).coeff m)
  let F : Option (σ →₀ ℕ) → ℤ := fun o => o.elim (1:ℤ) (fun m => (∑ i ∈ s, P i).coeff m)
  let T : Finset (Option (σ →₀ ℕ)) :=
    insert none ((s.biUnion (fun i => (P i).support)).image some)
  have hnone_mem : (none : Option (σ →₀ ℕ)) ∈ T := Finset.mem_insert_self _ _
  have hG_out : ∀ i ∈ s, ∀ o, o ∉ T → G i o = 0 := by
    intro i hi o ho
    cases o with
    | none => exact absurd hnone_mem ho
    | some m =>
        have hmU : m ∉ s.biUnion (fun i => (P i).support) := by
          intro hm
          apply ho
          rw [show T = insert none ((s.biUnion (fun i => (P i).support)).image some) from rfl,
            Finset.mem_insert]
          exact Or.inr (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
        have hm : m ∉ (P i).support :=
          fun h => hmU (Finset.mem_biUnion.mpr ⟨i, hi, h⟩)
        show MvPolynomial.coeff m (P i) = 0
        exact MvPolynomial.notMem_support_iff.mp hm
  have hF_out : ∀ o, o ∉ T → F o = 0 := by
    intro o ho
    cases o with
    | none => exact absurd hnone_mem ho
    | some m =>
        have hmU : m ∉ s.biUnion (fun i => (P i).support) := by
          intro hm
          apply ho
          rw [show T = insert none ((s.biUnion (fun i => (P i).support)).image some) from rfl,
            Finset.mem_insert]
          exact Or.inr (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
        have hzero : ∀ i ∈ s, MvPolynomial.coeff m (P i) = 0 := by
          intro i hi
          exact MvPolynomial.notMem_support_iff.mp
            (fun h => hmU (Finset.mem_biUnion.mpr ⟨i, hi, h⟩))
        show MvPolynomial.coeff m (∑ i ∈ s, P i) = 0
        rw [MvPolynomial.coeff_sum, Finset.sum_eq_zero hzero]
  have hredG : ∀ i ∈ s, Height.logHeight (fun o : Option (σ →₀ ℕ) => (G i o : ℚ))
      = Height.logHeight (fun a : T => (G i a.val : ℚ)) := by
    intro i hi
    rw [Height.logHeight_eq_log_mulHeight, Height.logHeight_eq_log_mulHeight,
      Commons.NumberTheory.Height.mulHeight_eq_mulHeight_finset T
        (fun o ho => by rw [hG_out i hi o ho]; rfl)]
  have hredF : Height.logHeight (fun o : Option (σ →₀ ℕ) => (F o : ℚ))
      = Height.logHeight (fun a : T => (F a.val : ℚ)) := by
    rw [Height.logHeight_eq_log_mulHeight, Height.logHeight_eq_log_mulHeight,
      Commons.NumberTheory.Height.mulHeight_eq_mulHeight_finset T
        (fun o ho => by rw [hF_out o ho]; rfl)]
  have hhyp : ∀ i ∈ s, Height.logHeight (fun a : T => (G i a.val : ℚ)) ≤ H := by
    intro i hi
    rw [← hredG i hi]
    rw [← hPi i]
    exact hH i hi
  have key := logHeight_int_sum_le (s := s) (c := (⟨none, hnone_mem⟩ : T))
    (g := fun i (a : T) => G i a.val) (φ := fun (a : T) => F a.val) H hH0 ?_ ?_ ?_ hhyp
  · rw [← hredF] at key
    exact key
  · intro i _
    show G i (⟨none, hnone_mem⟩ : T).val = 1
    rfl
  · show F (⟨none, hnone_mem⟩ : T).val = 1
    rfl
  · intro a ha
    have hav : (a : Option (σ →₀ ℕ)) ≠ none := fun h => ha (Subtype.ext h)
    obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.mp hav
    show F a.val = ∑ i ∈ s, G i a.val
    rw [hm]
    show MvPolynomial.coeff m (∑ i ∈ s, P i) = _
    rw [MvPolynomial.coeff_sum]
    rfl

end Commons.NumberTheory.Height.MvPolynomial
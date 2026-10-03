import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.norm_opMul_le_of_kernel

namespace Work.BourgainPlan.IonescuWainger

/-! ## Reindexing and summability helpers -/

/-- Shifting the index of a summable `ℤ`-family of norms. -/
theorem summable_norm_sub_shift {K : ℤ → ℂ} (hK : Summable fun m : ℤ => ‖K m‖) (n : ℤ) :
    Summable fun k : ℤ => ‖K (n - k)‖ := by
  have h := (Equiv.summable_iff (Equiv.subLeft n)).mpr hK
  rw [show ((fun m : ℤ => ‖K m‖) ∘ ⇑(Equiv.subLeft n)) = (fun k : ℤ => ‖K (n - k)‖) from
    funext (fun k => by rw [Function.comp_apply, Equiv.subLeft_apply])] at h
  exact h

/-- Reindexing a `tsum` of shifted norms over `ℤ` (`k ↦ n - k` is a bijection). -/
theorem tsum_norm_sub_shift {K : ℤ → ℂ} (n : ℤ) :
    ∑' k : ℤ, ‖K (n - k)‖ = ∑' m : ℤ, ‖K m‖ := by
  calc ∑' k : ℤ, ‖K (n - k)‖
      = ∑' k : ℤ, ‖K ((Equiv.subLeft n) k)‖ :=
        tsum_congr (fun k => by rw [Equiv.subLeft_apply])
    _ = ∑' m : ℤ, ‖K m‖ := Equiv.tsum_eq (Equiv.subLeft n) (fun m : ℤ => ‖K m‖)

/-- A finite sum of summable real families is summable. -/
theorem summable_finset_sum_of_summable {ι β : Type*} {s : Finset ι} {g : ι → β → ℝ}
    (h : ∀ i ∈ s, Summable (g i)) : Summable fun b => ∑ i ∈ s, g i b := by
  classical
  refine Finset.induction (motive := fun s => (∀ i ∈ s, Summable (g i)) →
      Summable fun b => ∑ i ∈ s, g i b) ?_ ?_ s h
  · intro _
    simp
  · intro a s has ih hins
    simp only [Finset.sum_insert has]
    exact (hins a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hins i (Finset.mem_insert_of_mem hi))

/-- **The duality step of the `p = ∞` endpoint of Tao's `ortho-apply`(ii).**  If the kernels `K i`
of a finite family of multipliers with symbols `Φ i` have `ℓ¹`-norms whose combination is bounded by
`C` (the `hL1` hypothesis, produced by the weighted Cauchy–Schwarz step), then the `ℓ²`-valued
square function of the family is bounded by `C · ‖f‖_∞` at every point. -/
theorem finset_sup_le_of_kernel_l1 {ι : Type*} [Fintype ι]
    (Φ : ι → MeasureTheory.Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) {K : ι → ℤ → ℂ}
    (hKi : ∀ i, Summable fun m : ℤ => ‖K i m‖)
    (hker : ∀ (i : ι) (m : ℤ), ∫ ξ, (Φ i : Circle → ℂ) ξ * star (fourier m ξ)
        ∂(AddCircle.haarAddCircle (T := 1)) = K i m)
    {C C' : ℝ} (hC : 0 ≤ C)
    (hL1 : ∀ c : ι → ℂ, ∑' n : ℤ, ‖∑ i, c i * K i n‖
        ≤ C * (∑ i, ‖c i‖ ^ 2) ^ ((1 : ℝ) / 2))
    (f : ℤ → ℂ) (hf : Memℓp f 2) (hC' : ∀ m : ℤ, ‖f m‖ ≤ C') (n : ℤ) :
    (∑ i, ‖opMul (Φ i) f hf n‖ ^ 2) ^ ((1 : ℝ) / 2) ≤ C * C' := by
  classical
  -- `C'` is non-negative, being an upper bound for the norms of the values of `f`.
  have hC'0 : 0 ≤ C' := le_trans (norm_nonneg (f 0)) (hC' 0)
  set a : ι → ℂ := fun i => opMul (Φ i) f hf n with hadef
  have ha : ∀ i, a i = opMul (Φ i) f hf n := fun i => by rw [hadef]
  -- ## Step 1: the dual estimate `‖Σ_i c_i a_i‖ ≤ C C' ‖c‖_2`, valid for every `c`
  have key : ∀ c : ι → ℂ, ‖∑ i, c i * a i‖ ≤ (C * C') * (∑ i, ‖c i‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    intro c
    set G : ℤ → ℂ := fun m => ∑ i, c i * K i m with hGdef
    -- each convolved sequence is summable (the kernel is `ℓ¹` and `f` is bounded)
    have hsum_i : ∀ i, Summable fun k : ℤ => f k * K i (n - k) := fun i =>
      Summable.of_norm_bounded ((summable_norm_sub_shift (hKi i) n).mul_left C')
        (fun k => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hC' k) (norm_nonneg _))
    -- the combination `G = Σ_i c_i K_i` is in `ℓ¹`
    have hGsum : Summable fun m : ℤ => ‖G m‖ := by
      refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
        (summable_finset_sum_of_summable (s := Finset.univ)
          (g := fun i m => ‖c i‖ * ‖K i m‖) (fun i _ => (hKi i).mul_left (‖c i‖)))
      rw [hGdef]
      simpa only [norm_mul] using norm_sum_le Finset.univ (fun i : ι => c i * K i m)
    have hGshift : Summable fun k : ℤ => ‖G (n - k)‖ := summable_norm_sub_shift hGsum n
    have hsum_fG : Summable fun k : ℤ => ‖f k‖ * ‖G (n - k)‖ :=
      Summable.of_nonneg_of_le (fun k => mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (fun k => mul_le_mul_of_nonneg_right (hC' k) (norm_nonneg _)) (hGshift.mul_left C')
    have hsum_fGn : Summable fun k : ℤ => ‖f k * G (n - k)‖ :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => by rw [norm_mul]) hsum_fG
    -- the finite family of convolutions exchanges with the sum over `ℤ`
    have h1 : (∑' k : ℤ, ∑ i, c i * (f k * K i (n - k))) = ∑ i, c i * a i := by
      rw [Summable.tsum_finsetSum (s := Finset.univ)
        (f := fun i k => c i * (f k * K i (n - k)))
        (fun i _ => (hsum_i i).mul_left (c i))]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [tsum_mul_left, ha i, ← opMul_eq_tsum_kernel (Φ i) f hf (hker i) n]
    have h2 : ∀ k : ℤ, ∑ i, c i * (f k * K i (n - k)) = f k * G (n - k) := by
      intro k
      rw [hGdef, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have heq : ∑ i, c i * a i = ∑' k : ℤ, f k * G (n - k) := by
      rw [← h1]
      exact tsum_congr h2
    calc ‖∑ i, c i * a i‖
        = ‖∑' k : ℤ, f k * G (n - k)‖ := by rw [heq]
      _ ≤ ∑' k : ℤ, ‖f k * G (n - k)‖ := norm_tsum_le_tsum_norm hsum_fGn
      _ = ∑' k : ℤ, ‖f k‖ * ‖G (n - k)‖ := tsum_congr (fun k => by rw [norm_mul])
      _ ≤ ∑' k : ℤ, C' * ‖G (n - k)‖ :=
          Summable.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_right (hC' k) (norm_nonneg _))
            hsum_fG (hGshift.mul_left C')
      _ = C' * ∑' k : ℤ, ‖G (n - k)‖ := tsum_mul_left
      _ = C' * ∑' m : ℤ, ‖G m‖ := by rw [tsum_norm_sub_shift (K := G) n]
      _ ≤ C' * (C * (∑ i, ‖c i‖ ^ 2) ^ ((1 : ℝ) / 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hC'0
          simpa only [hGdef] using hL1 c
      _ = (C * C') * (∑ i, ‖c i‖ ^ 2) ^ ((1 : ℝ) / 2) := by ring
  -- ## Step 2: finite-dimensional duality
  suffices hfin : (∑ i, ‖a i‖ ^ 2) ^ ((1 : ℝ) / 2) ≤ C * C' by
    simpa [hadef] using hfin
  set A : ℝ := ∑ i, ‖a i‖ ^ 2 with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  rw [← Real.sqrt_eq_rpow]
  have hconj : ∑ i, star (a i) * a i = (A : ℂ) := by
    rw [hAdef, Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq])
  have hnorm : (∑ i, ‖star (a i)‖ ^ 2) = A := by
    rw [hAdef]
    exact Finset.sum_congr rfl (fun i _ => by rw [norm_star])
  have hkey := key (fun i => star (a i))
  rw [hconj, Complex.norm_of_nonneg hA0, hnorm, ← Real.sqrt_eq_rpow] at hkey
  -- `hkey : A ≤ (C * C') * √A`
  by_cases hs : Real.sqrt A = 0
  · rw [hs]
    exact mul_nonneg hC hC'0
  · have hpos : 0 < Real.sqrt A := lt_of_le_of_ne (Real.sqrt_nonneg A) (Ne.symm hs)
    have hsq : Real.sqrt A * Real.sqrt A = A := by
      simpa [pow_two] using Real.sq_sqrt hA0
    refine le_of_mul_le_mul_left ?_ hpos
    calc Real.sqrt A * Real.sqrt A = A := hsq
      _ ≤ (C * C') * Real.sqrt A := hkey
      _ = Real.sqrt A * (C * C') := by ring

end Work.BourgainPlan.IonescuWainger

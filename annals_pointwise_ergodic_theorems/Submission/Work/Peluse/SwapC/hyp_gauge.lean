import Mathlib
import Submission.Work.Peluse.SwapC.concatAssemble
import Submission.Work.Peluse.SwapC.pboxSum_real_nonneg

namespace Work.Peluse.SwapC

set_option autoImplicit false

open scoped BigOperators

noncomputable section

open Work.Peluse

/-! ## Elementary support bookkeeping

`symIcc L` is exactly the set of integers of absolute value `≤ L`, so a function supported in
`[-L,L]` vanishes off it. -/

/-- Membership in `symIcc L`. -/
lemma mem_symIcc_iff {L : ℕ} {y : ℤ} : y ∈ symIcc L ↔ y.natAbs ≤ L := by
  rw [Work.Peluse.symIcc, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    rcases Int.natAbs_eq y with hy | hy <;> omega
  · intro h
    rcases Int.natAbs_eq y with hy | hy <;> omega

/-- A function supported in `[-L,L]` vanishes off `symIcc L`. -/
lemma eq_zero_of_notMem_symIcc {f : ℤ → ℂ} {L : ℕ} (h : SupportIn f L) {y : ℤ}
    (hy : y ∉ symIcc L) : f y = 0 := by
  apply h
  have h' : ¬ (y.natAbs ≤ L) := fun hle => hy ((mem_symIcc_iff).mpr hle)
  omega

/-! ## The asymmetric form of the box sum, with the `Rest`-product

`pboxSum_asym_eq` writes the `(s+1)`-fold box sum as the `tsum` of the asymmetric cube of the
increment tuple.  Factoring out the `ω = 0` corner (`asymCube_eq_mul_Rest`) and truncating the
`tsum` to the support of `f` gives the linear-in-`f` form used by the concatenation step. -/

/-- **The box sum is linear in `f` with the `ω = 0` corner factored out.**  The `tsum` over `ℤ` is
truncated to `S₀`, which is legitimate as soon as `f` vanishes off `S₀` (the summand contains the
factor `f y`). -/
lemma pboxSum_asym_rest (s M : ℕ) (qH : ℤ) (q₁ q₂ : Fin s → ℤ) (S S₀ : Finset ℤ) (f : ℤ → ℂ)
    (hsp : ∀ y : ℤ, y ∉ S₀ → f y = 0) :
    LadderP.Swap.pboxSum (s+1) (Fin.cons qH q₁) (Fin.cons (0:ℤ) q₂) M S f
      = ((S.card : ℂ))⁻¹ * (((M:ℂ)^4)⁻¹)^(s+1) *
        ∑ H : Fin (s+1) → Fin M × Fin M, ∑ H' : Fin (s+1) → Fin M × Fin M,
          ∑ y ∈ S₀, f y * Rest (incr s M qH q₁ q₂ H H') f y := by
  rw [pboxSum_asym_eq]
  congr 1
  refine Finset.sum_congr rfl (fun H _ => Finset.sum_congr rfl (fun H' _ => ?_))
  rw [tsum_eq_sum (s := S₀) (fun y hy => by rw [asymCube_eq_mul_Rest, hsp y hy, zero_mul])]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [asymCube_eq_mul_Rest]
  congr 1

/-- **The `Rest`-sum is the box value.**  Since `pboxSum` is a nonnegative real (`1 ≤ s+1`), the box
number `pbox = ‖pboxSum‖` is its real part, and the identity above inverts to a formula for the
`Rest`-sum: it is `|S| · M^{4(s+1)}` times `pbox`. -/
lemma restSum_re_eq (s M : ℕ) (qH : ℤ) (q₁ q₂ : Fin s → ℤ) (S S₀ : Finset ℤ) (f : ℤ → ℂ)
    (hM : 1 ≤ M) (hScard : S.card ≠ 0) (hfin : FinSuppZ f)
    (hsp : ∀ y : ℤ, y ∉ S₀ → f y = 0) :
    (∑ H : Fin (s+1) → Fin M × Fin M, ∑ H' : Fin (s+1) → Fin M × Fin M,
        ∑ y ∈ S₀, f y * Rest (incr s M qH q₁ q₂ H H') f y).re
      = (S.card : ℝ) * ((M:ℝ)^4)^(s+1) *
        LadderP.Swap.pbox (s+1) (Fin.cons qH q₁) (Fin.cons (0:ℤ) q₂) M S f := by
  obtain ⟨r, hr, hsum⟩ := pboxSum_real_nonneg (s+1) (by omega)
    (Fin.cons qH q₁) (Fin.cons (0:ℤ) q₂) M S f hfin
  have hid := pboxSum_asym_rest s M qH q₁ q₂ S S₀ f hsp
  have hSc : (S.card : ℂ) ≠ 0 := by simpa [Complex.ofReal_natCast] using hScard
  have hM4 : ((M:ℂ)^4) ≠ 0 := by
    have hM0 : (M:ℂ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
    exact pow_ne_zero 4 hM0
  have hMc : ((M:ℂ)^4)^(s+1) ≠ 0 := pow_ne_zero _ hM4
  have hkey : (r:ℂ) = ((S.card:ℂ))⁻¹ * ((((M:ℂ)^4)⁻¹)^(s+1)) *
      ∑ H : Fin (s+1) → Fin M × Fin M, ∑ H' : Fin (s+1) → Fin M × Fin M,
        ∑ y ∈ S₀, f y * Rest (incr s M qH q₁ q₂ H H') f y := by
    rw [← hsum]; exact hid
  have hG : (∑ H : Fin (s+1) → Fin M × Fin M, ∑ H' : Fin (s+1) → Fin M × Fin M,
        ∑ y ∈ S₀, f y * Rest (incr s M qH q₁ q₂ H H') f y)
      = (S.card:ℂ) * ((M:ℂ)^4)^(s+1) * (r:ℂ) := by
    have h1 : (S.card:ℂ) * ((S.card:ℂ))⁻¹ = 1 := mul_inv_cancel₀ hSc
    have h2 : ((M:ℂ)^4)^(s+1) * ((((M:ℂ)^4)⁻¹)^(s+1)) = 1 := by
      rw [show ((((M:ℂ)^4)⁻¹)^(s+1)) = ((((M:ℂ)^4)^(s+1))⁻¹) from inv_pow _ _]
      exact mul_inv_cancel₀ hMc
    calc (∑ H, ∑ H', ∑ y ∈ S₀, f y * Rest (incr s M qH q₁ q₂ H H') f y)
        = 1 * 1 * (∑ H, ∑ H', ∑ y ∈ S₀, f y * Rest (incr s M qH q₁ q₂ H H') f y) := by
          ring
      _ = ((S.card:ℂ) * ((S.card:ℂ))⁻¹) *
            ((((M:ℂ)^4)^(s+1)) * ((((M:ℂ)^4)⁻¹)^(s+1))) *
            (∑ H, ∑ H', ∑ y ∈ S₀, f y * Rest (incr s M qH q₁ q₂ H H') f y) := by
              rw [h1, h2]
      _ = (S.card:ℂ) * ((M:ℂ)^4)^(s+1) *
            (((S.card:ℂ))⁻¹ * ((((M:ℂ)^4)⁻¹)^(s+1)) *
              (∑ H, ∑ H', ∑ y ∈ S₀, f y * Rest (incr s M qH q₁ q₂ H H') f y)) := by ring
      _ = (S.card:ℂ) * ((M:ℂ)^4)^(s+1) * (r:ℂ) := by rw [← hkey]
  rw [hG]
  have hcast : ((S.card:ℂ) * ((M:ℂ)^4)^(s+1) * (r:ℂ))
      = (((S.card:ℝ) * ((M:ℝ)^4)^(s+1) * r : ℝ) : ℂ) := by
    have e1 : (S.card : ℂ) = Complex.ofReal (S.card : ℝ) := Complex.ofReal_natCast _
    have e2 : ((M:ℂ)^4) = Complex.ofReal ((M:ℝ)^4) := by
      rw [show (M:ℂ) = Complex.ofReal (M:ℝ) from Complex.ofReal_natCast M,
        ← Complex.ofReal_pow]
    have e3 : ((M:ℂ)^4)^(s+1) = Complex.ofReal (((M:ℝ)^4)^(s+1)) := by
      rw [e2, ← Complex.ofReal_pow]
    rw [e1, e3, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  rw [hcast, Complex.ofReal_re, LadderP.Swap.pbox, hsum, Complex.norm_of_nonneg hr]

/-! ## The `tsum` form of the gauge

`gauge` is an average over the index `i` and over the pair of shift tuples; the box identity above
is a *double* sum in `f`, while the gauge is a single `tsum`.  The two agree: pushing the scalars
and the factor `f y` into the inner finite sums and commuting them (finite sums over the Fintype
`I` and over the function types) turns the `tsum` of `f · gauge` into
`M^{-4(s+1)} · |I|^{-1} · ∑_i (Rest-sum)_i`. -/

lemma gauge_tsum_eq {I : Type} [Fintype I] (s M : ℕ) (qH : I → ℤ) (q₁ q₂ : I → Fin s → ℤ)
    (f : ℤ → ℂ) (S₀ : Finset ℤ) (hsp : ∀ y : ℤ, y ∉ S₀ → f y = 0) :
    (∑' y : ℤ, f y * gauge s M qH q₁ q₂ f y)
      = ((M:ℂ)^4)⁻¹^(s+1) * ((Fintype.card I : ℂ)⁻¹ *
          ∑ i : I, ∑ H : Fin (s+1) → Fin M × Fin M, ∑ H' : Fin (s+1) → Fin M × Fin M,
            ∑ y ∈ S₀, f y * Rest (incr s M (qH i) (q₁ i) (q₂ i) H H') f y) := by
  rw [tsum_eq_sum (s := S₀) (fun y hy => by rw [hsp y hy, zero_mul])]
  simp only [gauge]
  simp only [Finset.mul_sum]
  have h1 : (∑ y ∈ S₀, ∑ i : I, ∑ H : Fin (s+1) → Fin M × Fin M,
        ∑ H' : Fin (s+1) → Fin M × Fin M,
          f y * (((M:ℂ)^4)⁻¹^(s+1) * ((Fintype.card I : ℂ)⁻¹ *
            Rest (incr s M (qH i) (q₁ i) (q₂ i) H H') f y)))
      = ∑ i : I, ∑ y ∈ S₀, ∑ H : Fin (s+1) → Fin M × Fin M,
        ∑ H' : Fin (s+1) → Fin M × Fin M,
          f y * (((M:ℂ)^4)⁻¹^(s+1) * ((Fintype.card I : ℂ)⁻¹ *
            Rest (incr s M (qH i) (q₁ i) (q₂ i) H H') f y)) := Finset.sum_comm
  have h2 : (∑ i : I, ∑ y ∈ S₀, ∑ H : Fin (s+1) → Fin M × Fin M,
        ∑ H' : Fin (s+1) → Fin M × Fin M,
          f y * (((M:ℂ)^4)⁻¹^(s+1) * ((Fintype.card I : ℂ)⁻¹ *
            Rest (incr s M (qH i) (q₁ i) (q₂ i) H H') f y)))
      = ∑ i : I, ∑ H : Fin (s+1) → Fin M × Fin M, ∑ y ∈ S₀,
        ∑ H' : Fin (s+1) → Fin M × Fin M,
          f y * (((M:ℂ)^4)⁻¹^(s+1) * ((Fintype.card I : ℂ)⁻¹ *
            Rest (incr s M (qH i) (q₁ i) (q₂ i) H H') f y)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_comm
  have h3 : (∑ i : I, ∑ H : Fin (s+1) → Fin M × Fin M, ∑ y ∈ S₀,
        ∑ H' : Fin (s+1) → Fin M × Fin M,
          f y * (((M:ℂ)^4)⁻¹^(s+1) * ((Fintype.card I : ℂ)⁻¹ *
            Rest (incr s M (qH i) (q₁ i) (q₂ i) H H') f y)))
      = ∑ i : I, ∑ H : Fin (s+1) → Fin M × Fin M, ∑ H' : Fin (s+1) → Fin M × Fin M,
        ∑ y ∈ S₀, f y * (((M:ℂ)^4)⁻¹^(s+1) * ((Fintype.card I : ℂ)⁻¹ *
            Rest (incr s M (qH i) (q₁ i) (q₂ i) H H') f y)) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro H _
    exact Finset.sum_comm
  rw [h1, h2, h3]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun H _ =>
    Finset.sum_congr rfl (fun H' _ => Finset.sum_congr rfl (fun y _ => by ring))))

/-- **The hypothesis of `concatStep` in gauge form** (KKL step 1 + the `avg` bookkeeping): the
`pbox (s+1)` lower bound is exactly `δ * |S| ≤ Re ∑'_y f y · Φ y` with the gauge `Φ = gauge s M qH q₁ q₂ f`
of `concatAssemble.lean`, i.e. the level-`(s+1)` box sum is linear in `f` with the `ω = 0` corner
factored out (`pboxSum_asym_eq` + `asymCube_eq_mul_Rest`), and `pboxSum_real_nonneg` identifies
`pbox` with the real part of `pboxSum`. -/
theorem hyp_gauge {I : Type} [Fintype I] [Nonempty I] (s M : ℕ) (qH : I → ℤ)
    (q₁ q₂ : I → Fin s → ℤ) (N : ℕ) (δ : ℝ) (f : ℤ → ℂ) (hM : 1 ≤ M) (hδ : 0 < δ)
    (hbd : ∀ x : ℤ, ‖f x‖ ≤ 1) (hsup : Work.Peluse.FinSuppZ f)
    (h : δ ≤ Work.Peluse.LadderP.Swap.avg (fun i : I =>
        Work.Peluse.LadderP.Swap.pbox (s + 1) (Fin.cons (qH i) (q₁ i)) (Fin.cons 0 (q₂ i)) M
          (Work.Peluse.symIcc N) f)) :
    δ * ((Work.Peluse.symIcc N).card : ℝ)
      ≤ (∑' y : ℤ, f y * Work.Peluse.SwapC.gauge s M qH q₁ q₂ f y).re := by
  obtain ⟨N₀, hN₀⟩ := hsup
  have hfs : FinSuppZ f := ⟨N₀, hN₀⟩
  have hsp : ∀ y : ℤ, y ∉ symIcc N₀ → f y = 0 := fun y hy => eq_zero_of_notMem_symIcc hN₀ hy
  have h0mem : (0:ℤ) ∈ symIcc N := by rw [mem_symIcc_iff]; simp
  have hScard : (symIcc N).card ≠ 0 := Nat.pos_iff_ne_zero.mp (Finset.card_pos.mpr ⟨0, h0mem⟩)
  have hXeq := gauge_tsum_eq s M qH q₁ q₂ f (symIcc N₀) hsp
  have hMℝ : ((M:ℝ)^4) ≠ 0 := by
    have hMR : (0:ℝ) < (M:ℝ) := by
      have : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
      linarith
    exact pow_ne_zero 4 (ne_of_gt hMR)
  have hcM : ((((M:ℝ)^4)⁻¹)^(s+1)) * (((M:ℝ)^4)^(s+1)) = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hMℝ, one_pow]
  have hC : ((M:ℂ)^4)⁻¹^(s+1) = Complex.ofReal ((((M:ℝ)^4)⁻¹)^(s+1)) := by
    have e2 : ((M:ℂ)^4) = Complex.ofReal ((M:ℝ)^4) := by
      rw [show (M:ℂ) = Complex.ofReal (M:ℝ) from Complex.ofReal_natCast M,
        ← Complex.ofReal_pow]
    rw [e2, ← Complex.ofReal_inv, ← Complex.ofReal_pow]
  have hD : (Fintype.card I : ℂ)⁻¹ = Complex.ofReal ((Fintype.card I : ℝ)⁻¹) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  have key : (∑' y : ℤ, f y * gauge s M qH q₁ q₂ f y).re
      = ((symIcc N).card : ℝ) * LadderP.Swap.avg (fun i : I =>
          LadderP.Swap.pbox (s+1) (Fin.cons (qH i) (q₁ i)) (Fin.cons (0:ℤ) (q₂ i)) M
            (symIcc N) f) := by
    rw [hXeq, hC, hD, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    rw [Complex.re_sum]
    have hGi : ∀ i : I,
        (∑ H : Fin (s+1) → Fin M × Fin M, ∑ H' : Fin (s+1) → Fin M × Fin M,
          ∑ y ∈ symIcc N₀, f y * Rest (incr s M (qH i) (q₁ i) (q₂ i) H H') f y).re
        = ((symIcc N).card : ℝ) * ((M:ℝ)^4)^(s+1) *
          LadderP.Swap.pbox (s+1) (Fin.cons (qH i) (q₁ i)) (Fin.cons (0:ℤ) (q₂ i)) M
            (symIcc N) f :=
      fun i => restSum_re_eq s M (qH i) (q₁ i) (q₂ i) (symIcc N) (symIcc N₀) f
        hM hScard hfs hsp
    rw [Finset.sum_congr rfl (fun i _ => hGi i)]
    rw [← Finset.mul_sum]
    rw [LadderP.Swap.avg]
    set S : ℝ := ∑ i : I, LadderP.Swap.pbox (s+1) (Fin.cons (qH i) (q₁ i)) (Fin.cons (0:ℤ) (q₂ i)) M (symIcc N) f with hSdef
    set Sc : ℝ := ((symIcc N).card : ℝ) with hScdef
    calc ((((M:ℝ)^4)⁻¹)^(s+1)) * ((Fintype.card I : ℝ)⁻¹ * (Sc * ((M:ℝ)^4)^(s+1) * S))
        = (((((M:ℝ)^4)⁻¹)^(s+1)) * ((M:ℝ)^4)^(s+1)) *
            ((Fintype.card I : ℝ)⁻¹ * (Sc * S)) := by ring
      _ = 1 * ((Fintype.card I : ℝ)⁻¹ * (Sc * S)) := by rw [hcM]
      _ = Sc * ((Fintype.card I : ℝ)⁻¹ * S) := by ring
  rw [key]
  calc δ * ((symIcc N).card : ℝ)
      ≤ LadderP.Swap.avg (fun i : I => LadderP.Swap.pbox (s+1) (Fin.cons (qH i) (q₁ i))
            (Fin.cons (0:ℤ) (q₂ i)) M (symIcc N) f) * ((symIcc N).card : ℝ) :=
        mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _)
    _ = ((symIcc N).card : ℝ) * LadderP.Swap.avg (fun i : I =>
          LadderP.Swap.pbox (s+1) (Fin.cons (qH i) (q₁ i)) (Fin.cons (0:ℤ) (q₂ i)) M
            (symIcc N) f) := by ring

end

end Work.Peluse.SwapC

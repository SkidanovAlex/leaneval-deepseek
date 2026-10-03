/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.Basic

/-!
# Block decomposition of a long window in terms of short windows

Let `a : ℤ → ℝ` be nonnegative and supported in `[-N,N]`, `c : ℤ` a step, and `1 ≤ L ≤ M`
two window lengths.  The "long" window sum `W_M x = ∑_{y ∈ [1,M]} a (x + c y)` is bounded by a
sum of `K = ⌈M/L⌉` "short" window sums `W_L (x + c q L)`, `q < K`, because the interval `[1,M]`
is covered by the `K` disjoint blocks `L q + [1,L]`.  Cauchy–Schwarz then gives

`∑_x W_M(x)^2 ≤ K^2 ∑_x W_L(x)^2`,

and `K ≤ (M + L)/L` yields the constant `((M+L)/L)^2` of

`Work.Peluse.Peel.windowSum_block_le`.

Applying this with `a x = ‖g x‖` for `g` supported in `[-N,N]` gives the requested statement.

## Main result

* `Work.Peluse.Peel.windowSum_block_le`
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Peel

noncomputable section

/-! ## The elementary covering/blocking lemma for `[1,M]` -/

/-- **Block decomposition of `[1,M]`.**  If `f ≥ 0` is a nonnegative function on `ℕ`, then the
sum of `f` over `[1,M]` is at most the sum over the `K = (M-1)/L + 1 = ⌈M/L⌉` blocks
`L q + [1,L]` (`q = 0, …, K-1`), which cover `[1,M]`.

The map `y ↦ ((y-1)/L, y - L·((y-1)/L))` is an injection of `[1,M]` into
`range K × [1,L]` with `y = L·q + r`, so the left sum is a sub-sum of the right one. -/
private lemma sum_Icc_le_sum_blocks {M L : ℕ} (hL : 1 ≤ L) (f : ℕ → ℝ) (hf : ∀ y, 0 ≤ f y) :
    ∑ y ∈ Finset.Icc 1 M, f y
      ≤ ∑ q ∈ Finset.range ((M - 1) / L + 1), ∑ r ∈ Finset.Icc 1 L, f (L * q + r) := by
  set K := (M - 1) / L + 1 with hK
  set φ : ℕ → ℕ × ℕ := fun y => ((y - 1) / L, y - L * ((y - 1) / L)) with hφ
  have hmem : ∀ y ∈ Finset.Icc 1 M, φ y ∈ (Finset.range K) ×ˢ (Finset.Icc 1 L) := by
    intro y hy
    rw [Finset.mem_product]
    rw [Finset.mem_Icc] at hy
    have h : L * ((y - 1) / L) + (y - 1) % L = y - 1 := Nat.div_add_mod (y - 1) L
    have hmod : (y - 1) % L < L := Nat.mod_lt _ (by omega)
    simp only [hφ]
    constructor
    · rw [Finset.mem_range, hK]
      have h1 : (y - 1) / L ≤ (M - 1) / L := Nat.div_le_div_right (Nat.sub_le_sub_right hy.2 1)
      omega
    · rw [Finset.mem_Icc]
      constructor <;> omega
  have hval : ∀ y ∈ Finset.Icc 1 M, y = L * (φ y).1 + (φ y).2 := by
    intro y hy
    rw [Finset.mem_Icc] at hy
    simp only [hφ]
    have hle : L * ((y - 1) / L) ≤ y := by
      have h : L * ((y - 1) / L) + (y - 1) % L = y - 1 := Nat.div_add_mod (y - 1) L
      omega
    exact (Nat.add_sub_of_le hle).symm
  have hinj : Set.InjOn φ ↑(Finset.Icc 1 M) := by
    intro y1 hy1 y2 hy2 heq
    have h1 := hval y1 hy1
    have h2 := hval y2 hy2
    have hfst : (φ y1).1 = (φ y2).1 := congrArg Prod.fst heq
    have hsnd : (φ y1).2 = (φ y2).2 := congrArg Prod.snd heq
    rw [h1, h2, hfst, hsnd]
  calc ∑ y ∈ Finset.Icc 1 M, f y
      = ∑ y ∈ Finset.Icc 1 M, f (L * (φ y).1 + (φ y).2) := by
        refine Finset.sum_congr rfl (fun y hy => congrArg f (hval y hy))
    _ = ∑ z ∈ (Finset.Icc 1 M).image φ, f (L * z.1 + z.2) :=
        (Finset.sum_image (f := fun z : ℕ × ℕ => f (L * z.1 + z.2)) hinj).symm
    _ ≤ ∑ z ∈ (Finset.range K) ×ˢ (Finset.Icc 1 L), f (L * z.1 + z.2) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hmem)
          (fun z _ _ => hf _)
    _ = ∑ q ∈ Finset.range K, ∑ r ∈ Finset.Icc 1 L, f (L * q + r) :=
        Finset.sum_product _ _ _

/-! ## The window of a finitely supported function -/

/-- **Vanishing of a window off its window.**  If `a` vanishes outside `[-N,N]` and
`N + |c|·T < |x|`, then every term `a (x + c y)`, `y ∈ [1,T]`, vanishes. -/
private lemma sum_Icc_window_eq_zero {N T : ℕ} {a : ℤ → ℝ} {c : ℤ} {x : ℤ}
    (hN : ∀ z : ℤ, (N : ℤ) < |z| → a z = 0) (hx : (N : ℤ) + |c| * (T : ℤ) < |x|) :
    ∑ y ∈ Finset.Icc 1 T, a (x + c * (y : ℤ)) = 0 := by
  refine Finset.sum_eq_zero (fun y hy => ?_)
  apply hN
  rw [Finset.mem_Icc] at hy
  have hyZ : (y : ℤ) ≤ (T : ℤ) := by exact_mod_cast hy.2
  have habs : |c * (y : ℤ)| = |c| * (y : ℤ) := by
    rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg y)]
  have hy_le : |c| * (y : ℤ) ≤ |c| * (T : ℤ) :=
    mul_le_mul_of_nonneg_left hyZ (abs_nonneg c)
  have h1 : |x| ≤ |x + c * (y : ℤ)| + |c * (y : ℤ)| := by
    have := abs_add_le (x + c * (y : ℤ)) (-(c * (y : ℤ)))
    simpa [abs_neg, show x + c * (y : ℤ) + -(c * (y : ℤ)) = x from by ring] using this
  rw [habs] at h1
  linarith

/-- Membership in the symmetric interval `Work.Peluse.symIcc A = [-A,A]` is the bound on
`natAbs`. -/
private lemma mem_symIcc_iff {A : ℕ} {z : ℤ} : z ∈ Work.Peluse.symIcc A ↔ z.natAbs ≤ A := by
  rw [Work.Peluse.symIcc, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    have h : |z| ≤ (A : ℤ) := abs_le.mpr ⟨h1, h2⟩
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  · intro hz
    have h : (z.natAbs : ℤ) ≤ (A : ℤ) := by exact_mod_cast hz
    rw [Int.natCast_natAbs] at h
    exact abs_le.mp h

private lemma notMem_symIcc_iff {A : ℕ} {z : ℤ} : z ∉ Work.Peluse.symIcc A ↔ A < z.natAbs := by
  rw [mem_symIcc_iff]; exact not_le

/-! ## The block inequality for window sums -/

/-- **The long window is bounded by `K = ⌈M/L⌉` short windows.**  Let `a : ℤ → ℝ` be
nonnegative and supported in `[-N,N]`, `c : ℤ`, `1 ≤ L ≤ M`.  Then

`∑_x (∑_{y ∈ [1,M]} a (x + c y))^2 ≤ K^2 ∑_x (∑_{y ∈ [1,L]} a (x + c y))^2`

with `K = (M-1)/L + 1`.

Indeed, the interval `[1,M]` is covered by the `K` blocks `L q + [1,L]`, so for every `x`
`W_M(x) ≤ ∑_{q<K} W_L(x + c L q)`; Cauchy–Schwarz gives `W_M(x)^2 ≤ K ∑_{q<K} W_L(x+cLq)^2`,
and summing over `x` the translation invariance of the `tsum` on `ℤ` produces the factor `K^2`. -/
private lemma windowSum_block_le_aux {N M L : ℕ} (hL : 1 ≤ L) (hLM : L ≤ M) (c : ℤ)
    {a : ℤ → ℝ} (ha0 : ∀ x, 0 ≤ a x) (hN : ∀ x : ℤ, (N : ℤ) < |x| → a x = 0) :
    ∑' x : ℤ, (∑ y ∈ Finset.Icc 1 M, a (x + c * (y : ℤ))) ^ 2
      ≤ ((M : ℝ) + L) ^ 2 / (L : ℝ) ^ 2 *
        ∑' x : ℤ, (∑ y ∈ Finset.Icc 1 L, a (x + c * (y : ℤ))) ^ 2 := by
  have hM1 : 1 ≤ M := le_trans hL hLM
  set K : ℕ := (M - 1) / L + 1 with hK
  set WM : ℤ → ℝ := fun x => ∑ y ∈ Finset.Icc 1 M, a (x + c * (y : ℤ)) with hWM
  set WL : ℤ → ℝ := fun x => ∑ y ∈ Finset.Icc 1 L, a (x + c * (y : ℤ)) with hWL
  have hWMnn : ∀ x, 0 ≤ WM x := fun x => Finset.sum_nonneg (fun y _ => ha0 _)
  have hWLnn : ∀ x, 0 ≤ WL x := fun x => Finset.sum_nonneg (fun y _ => ha0 _)
  have hWLzero : ∀ z : ℤ, (N : ℤ) + |c| * (L : ℤ) < |z| → WL z = 0 := by
    intro z hz
    rw [hWL]
    exact sum_Icc_window_eq_zero (T := L) hN hz
  have hWMzero : ∀ z : ℤ, (N : ℤ) + |c| * (M : ℤ) < |z| → WM z = 0 := by
    intro z hz
    rw [hWM]
    exact sum_Icc_window_eq_zero (T := M) hN hz
  have hblock : ∀ x : ℤ, WM x ≤ ∑ q ∈ Finset.range K, WL (x + c * ((L * q : ℕ) : ℤ)) := by
    intro x
    rw [hWM, hWL]
    have h1 := sum_Icc_le_sum_blocks (M := M) (L := L) hL
      (f := fun y : ℕ => a (x + c * (y : ℤ))) (fun y => ha0 _)
    rw [← hK] at h1
    refine h1.trans (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun q _ => ?_)
    refine Finset.sum_congr rfl (fun r _ => ?_)
    congr 1
    push_cast
    ring
  have hsummL : ∀ t : ℤ, Summable (fun x : ℤ => WL (x + t) ^ 2) := by
    intro t
    refine summable_of_ne_finset_zero (s := Work.Peluse.symIcc (N + c.natAbs * L + t.natAbs))
      (fun x hx => ?_)
    have hxA : ((N + c.natAbs * L + t.natAbs : ℕ) : ℤ) < |x| := by
      have h := notMem_symIcc_iff.mp hx
      have h' : ((N + c.natAbs * L + t.natAbs : ℕ) : ℤ) < (x.natAbs : ℤ) := by exact_mod_cast h
      rwa [Int.natCast_natAbs] at h'
    have hA : ((N + c.natAbs * L + t.natAbs : ℕ) : ℤ) = (N : ℤ) + |c| * (L : ℤ) + |t| := by
      push_cast; ring
    have ht : |x| ≤ |x + t| + |t| := by
      have := abs_add_le (x + t) (-t)
      simpa [abs_neg, show x + t + -t = x from by ring] using this
    rw [hA] at hxA
    have hlt : (N : ℤ) + |c| * (L : ℤ) < |x + t| := by linarith
    rw [hWLzero (x + t) hlt]
    simp
  have hsummM : Summable (fun x : ℤ => WM x ^ 2) := by
    refine summable_of_ne_finset_zero (s := Work.Peluse.symIcc (N + c.natAbs * M))
      (fun x hx => ?_)
    have hxA : (N : ℤ) + |c| * (M : ℤ) < |x| := by
      have h := notMem_symIcc_iff.mp hx
      have h' : ((N + c.natAbs * M : ℕ) : ℤ) < (x.natAbs : ℤ) := by exact_mod_cast h
      rw [Int.natCast_natAbs] at h'
      have hA : ((N + c.natAbs * M : ℕ) : ℤ) = (N : ℤ) + |c| * (M : ℤ) := by
        push_cast; ring
      rwa [hA] at h'
    rw [hWMzero x hxA]
    simp
  have hKle : (K : ℝ) ≤ ((M : ℝ) + L) / (L : ℝ) := by
    have hKL : K * L ≤ M + L - 1 := by
      rw [hK]
      have h : L * ((M - 1) / L) + (M - 1) % L = M - 1 := Nat.div_add_mod (M - 1) L
      have hmod : (M - 1) % L < L := Nat.mod_lt _ (by omega)
      have key : ((M - 1) / L) * L ≤ M - 1 := by rw [mul_comm]; omega
      have hexp : ((M - 1) / L + 1) * L = ((M - 1) / L) * L + L := by ring
      rw [hexp]; omega
    have h2 : ((K * L : ℕ) : ℝ) ≤ ((M + L : ℕ) : ℝ) := by
      have : K * L ≤ M + L := by omega
      exact_mod_cast this
    push_cast at h2
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (L : ℝ))]
    linarith
  have hCS : ∀ x : ℤ,
      WM x ^ 2 ≤ (K : ℝ) * ∑ q ∈ Finset.range K, WL (x + c * ((L * q : ℕ) : ℤ)) ^ 2 := by
    intro x
    have h1 := hblock x
    have h2 : WM x ^ 2
        ≤ (∑ q ∈ Finset.range K, WL (x + c * ((L * q : ℕ) : ℤ))) ^ 2 :=
      pow_le_pow_left₀ (hWMnn x) h1 2
    calc WM x ^ 2
        ≤ (∑ q ∈ Finset.range K, WL (x + c * ((L * q : ℕ) : ℤ))) ^ 2 := h2
      _ ≤ ((Finset.range K).card : ℝ)
            * ∑ q ∈ Finset.range K, WL (x + c * ((L * q : ℕ) : ℤ)) ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ = (K : ℝ) * ∑ q ∈ Finset.range K, WL (x + c * ((L * q : ℕ) : ℤ)) ^ 2 := by
          rw [Finset.card_range]
  have hsummR : Summable (fun x : ℤ =>
      (K : ℝ) * ∑ q ∈ Finset.range K, WL (x + c * ((L * q : ℕ) : ℤ)) ^ 2) :=
    (summable_sum (fun q _ => hsummL _)).mul_left _
  have hstep1 := Summable.tsum_le_tsum hCS hsummM hsummR
  have main : ∑' x : ℤ, WM x ^ 2 ≤ ((M : ℝ) + L) ^ 2 / (L : ℝ) ^ 2 * ∑' x : ℤ, WL x ^ 2 := by
    have hstep2 : ∑' x : ℤ, (K : ℝ) * ∑ q ∈ Finset.range K,
          WL (x + c * ((L * q : ℕ) : ℤ)) ^ 2
        = (K : ℝ) * ∑ q ∈ Finset.range K, ∑' x : ℤ, WL (x + c * ((L * q : ℕ) : ℤ)) ^ 2 := by
      rw [tsum_mul_left]
      congr 1
      exact (hasSum_sum (f := fun q x => WL (x + c * ((L * q : ℕ) : ℤ)) ^ 2)
        (a := fun q => ∑' x : ℤ, WL (x + c * ((L * q : ℕ) : ℤ)) ^ 2)
        (fun q _ => (hsummL _).hasSum)).tsum_eq
    have hstep3 : ∀ q : ℕ, ∑' x : ℤ, WL (x + c * ((L * q : ℕ) : ℤ)) ^ 2 = ∑' x : ℤ, WL x ^ 2 :=
      fun q => Equiv.tsum_eq (Equiv.addRight (c * ((L * q : ℕ) : ℤ))) (fun y : ℤ => WL y ^ 2)
    have hs : 0 ≤ ∑' x : ℤ, WL x ^ 2 := tsum_nonneg (fun x => sq_nonneg _)
    have hK2 : (K : ℝ) ^ 2 ≤ ((M : ℝ) + L) ^ 2 / (L : ℝ) ^ 2 := by
      have hdiv : (((M : ℝ) + L) / (L : ℝ)) ^ 2 = ((M : ℝ) + L) ^ 2 / (L : ℝ) ^ 2 :=
        div_pow _ _ 2
      calc (K : ℝ) ^ 2 ≤ (((M : ℝ) + L) / (L : ℝ)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hKle 2
        _ = ((M : ℝ) + L) ^ 2 / (L : ℝ) ^ 2 := hdiv
    calc ∑' x : ℤ, WM x ^ 2
        ≤ ∑' x : ℤ, (K : ℝ) * ∑ q ∈ Finset.range K, WL (x + c * ((L * q : ℕ) : ℤ)) ^ 2 :=
          hstep1
      _ = (K : ℝ) * ∑ q ∈ Finset.range K, ∑' x : ℤ, WL (x + c * ((L * q : ℕ) : ℤ)) ^ 2 :=
          hstep2
      _ = (K : ℝ) * ∑ q ∈ Finset.range K, ∑' x : ℤ, WL x ^ 2 := by
          congr 1
          exact Finset.sum_congr rfl (fun q _ => hstep3 q)
      _ = (K : ℝ) * ((K : ℝ) * ∑' x : ℤ, WL x ^ 2) := by
          congr 1
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = (K : ℝ) ^ 2 * ∑' x : ℤ, WL x ^ 2 := by ring
      _ ≤ ((M : ℝ) + L) ^ 2 / (L : ℝ) ^ 2 * ∑' x : ℤ, WL x ^ 2 :=
          mul_le_mul_of_nonneg_right hK2 hs
  have hconv1 : (∑' x : ℤ, (∑ y ∈ Finset.Icc 1 M, a (x + c * (y : ℤ))) ^ 2)
      = ∑' x : ℤ, WM x ^ 2 := tsum_congr (fun x => by simp only [hWM])
  have hconv2 : (∑' x : ℤ, (∑ y ∈ Finset.Icc 1 L, a (x + c * (y : ℤ))) ^ 2)
      = ∑' x : ℤ, WL x ^ 2 := tsum_congr (fun x => by simp only [hWL])
  rw [hconv1, hconv2]
  exact main

/-! ## The requested statement -/

/-- **The long window is controlled by the short windows.**  For `g` supported in `[-N,N]`,
`c : ℤ` and `1 ≤ L ≤ M`,

`∑_x (∑_{y ∈ [1,M]} ‖g (x + c y)‖)^2 ≤ ((M+L)/L)^2 ∑_x (∑_{y ∈ [1,L]} ‖g (x + c y)‖)^2`. -/
theorem windowSum_block_le {N M L : ℕ} (hL : 1 ≤ L) (hLM : L ≤ M) (c : ℤ) {g : ℤ → ℂ}
    (hsupp : Work.Peluse.SupportIn g N) :
    ∑' x : ℤ, (∑ y ∈ Finset.Icc 1 M, ‖g (x + c * (y : ℤ))‖) ^ 2
      ≤ ((M : ℝ) + L) ^ 2 / (L : ℝ) ^ 2 *
        ∑' x : ℤ, (∑ y ∈ Finset.Icc 1 L, ‖g (x + c * (y : ℤ))‖) ^ 2 := by
  refine windowSum_block_le_aux (N := N) (M := M) (L := L) hL hLM c
    (a := fun x : ℤ => ‖g x‖) (fun x => norm_nonneg _) ?_
  intro x hx
  have hx' : (N : ℤ) < (x.natAbs : ℤ) := by rwa [← Int.natCast_natAbs] at hx
  have h : N < x.natAbs := by exact_mod_cast hx'
  rw [hsupp x h]
  simp

end

end Work.Peluse.Peel

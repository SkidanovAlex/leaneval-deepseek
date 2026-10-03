/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.SwapCS0.acfGram
import Submission.Work.Peluse.SwapCS0.acfNormSqCS
import Submission.Work.Peluse.SwapCS0.acfShiftSupp

/-!
# The `s = 0` Cauchy–Schwarz of the concatenation step

With `A τ = ∑'_x f (x + τ) · conj (f x)` the autocorrelation of a function `f : ℤ → ℂ` supported in
the finite set `S₀`, this module proves

`(∑_{i,c,c'} A (a i ((c:ℤ) - (c':ℤ))))² ≤ |S₀| · ∑_{i,j,m,m'} A (a j (m₁ - m₁') - a i (m₂ - m₂'))`

(the real parts of the two autocorrelation sums; both are in fact non-negative reals), i.e.
`Work.Peluse.SwapCS0.acfCS`, the `s = 0` case of Kravitz–Kuća–Leng Lemma 6.1.  It is used in
`Work.Peluse.SwapC.concatStepProved`.

## The proof

Write `P := ∑_i S_i^* S_i` where `S_i` is the sum of the shifts `a i · c`, `c ∈ Fin M`, so that
`A = S_i^* S_i f` in the autocorrelation notation.  Both sides of the inequality are then the two
sides of Cauchy–Schwarz:

* the left-hand side is `⟨P f, f⟩²` where `P f (x) = ∑_{i,c,c'} f (x + a i (c - c'))` is the sum
  `h x` (this is `tsum_finset_sum_eq`: a finite sum of `tsum`s, each summand supported in `S₀`);
* the right-hand side's inner complex sum is `‖P f‖² = ∑_x ‖h x‖²` (this is the delegated
  `acfGram`, which is `gramShift` applied to the family of shifts `a i · (c - c')` plus a
  reindexing of the resulting double sum);
* Cauchy–Schwarz `⟨Pf,f⟩² ≤ ‖Pf‖² ‖f‖²` is applied over the finite box `Work.Peluse.symIcc B`
  containing `S₀` and the support of `h` (`acfShiftSupp`), and `‖f‖² ≤ |S₀|` follows from
  `‖f‖ ≤ 1` and the support hypothesis.
-/

set_option maxHeartbeats 800000

open scoped BigOperators

namespace Work.Peluse.SwapCS0

/-! ## Elementary helpers -/

/-- Membership in the symmetric interval `[-L, L]`, in terms of `Int.natAbs`. -/
private lemma mem_symIcc_iff_natAbs {L : ℕ} {x : ℤ} :
    x ∈ Work.Peluse.symIcc L ↔ x.natAbs ≤ L := by
  rw [Work.Peluse.symIcc, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    have h : |x| ≤ (L : ℤ) := abs_le.mpr ⟨h1, h2⟩
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  · intro h
    have h' : (x.natAbs : ℤ) ≤ (L : ℤ) := by exact_mod_cast h
    have h'' : |x| ≤ (L : ℤ) := by rwa [Int.natCast_natAbs] at h'
    exact abs_le.mp h''

/-- A complex `normSq` written through the star ring. -/
private lemma ofReal_normSq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
  simp [Complex.sq_norm, Complex.mul_conj]

/-- Three nested `Finset` sums as one sum indexed by the iterated product. -/
private lemma sum3_eq_sum_prod {ι₁ ι₂ ι₃ : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    {γ : Type} [AddCommMonoid γ] (G : ι₁ → ι₂ → ι₃ → γ) :
    (∑ i, ∑ j, ∑ k, G i j k) = ∑ p : ι₁ × (ι₂ × ι₃), G p.1 p.2.1 p.2.2 := by
  rw [Fintype.sum_prod_type (f := fun p : ι₁ × (ι₂ × ι₃) => G p.1 p.2.1 p.2.2)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type (f := fun p : ι₂ × ι₃ => G i p.1 p.2)]

/-- Interchange a finite sum with a `tsum` over `ℤ` when the common support is finite. -/
private lemma tsum_finset_sum_eq {ι : Type} [Fintype ι] (F : ι → ℤ → ℂ) (C : Finset ℤ)
    (hC : ∀ i, ∀ x ∉ C, F i x = 0) :
    (∑ i : ι, ∑' x : ℤ, F i x) = ∑' x : ℤ, ∑ i : ι, F i x := by
  have h1 : ∀ x : ℤ, x ∉ C → (∑ i : ι, F i x) = 0 :=
    fun x hx => Finset.sum_eq_zero fun i _ => hC i x hx
  calc ∑ i : ι, ∑' x : ℤ, F i x
      = ∑ i : ι, ∑ x ∈ C, F i x := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact tsum_eq_sum (hC i)
    _ = ∑ x ∈ C, ∑ i : ι, F i x := Finset.sum_comm
    _ = ∑' x : ℤ, ∑ i : ι, F i x := (tsum_eq_sum h1).symm

/-! ## The target -/

/-- **Cauchy–Schwarz for the autocorrelation of the level-`1` concatenation**: with
`A τ = ∑'_x f (x + τ) conj (f x)`, the square of the `i, c, c'`-autocorrelation sum is bounded by
`|S₀|` times the `i, j, m, m'`-sum of autocorrelations at the shifts
`a j (m₁ - m₁') - a i (m₂ - m₂')`. -/
theorem acfCS {I : Type} [Fintype I] (M : ℕ) (a : I → ℤ) (f : ℤ → ℂ) (S₀ : Finset ℤ)
    (hsup : ∀ x : ℤ, x ∉ S₀ → f x = 0) (hbd : ∀ x : ℤ, ‖f x‖ ≤ 1) :
    (∑ i : I, ∑ c : Fin M, ∑ c' : Fin M,
        ∑' x : ℤ, f (x + a i * ((c : ℤ) - (c' : ℤ))) * star (f x)).re ^ 2
      ≤ (S₀.card : ℝ) *
        (∑ i : I, ∑ j : I, ∑ m : Fin M × Fin M, ∑ m' : Fin M × Fin M,
          ∑' x : ℤ, f (x + (a j * ((m.1 : ℤ) - (m'.1 : ℤ))
                - a i * ((m.2 : ℤ) - (m'.2 : ℤ)))) * star (f x)).re := by
  classical
  set B : ℕ := S₀.sup (fun x : ℤ => x.natAbs)
      + (Finset.univ.sup (fun i : I => (a i).natAbs)) * M with hB
  set h : ℤ → ℂ := fun x => ∑ i : I, ∑ c : Fin M, ∑ c' : Fin M,
      f (x + a i * ((c : ℤ) - (c' : ℤ))) with hhdef
  set Rc : ℂ := ∑ i : I, ∑ j : I, ∑ m : Fin M × Fin M,
      ∑ m' : Fin M × Fin M,
      ∑' x : ℤ, f (x + (a j * ((m.1 : ℤ) - (m'.1 : ℤ))
            - a i * ((m.2 : ℤ) - (m'.2 : ℤ)))) * star (f x) with hRc
  have hS₀_sub : S₀ ⊆ Work.Peluse.symIcc B := by
    intro x hx
    rw [mem_symIcc_iff_natAbs, hB]
    have h1 : x.natAbs ≤ S₀.sup (fun x : ℤ => x.natAbs) :=
      Finset.le_sup (f := fun x : ℤ => x.natAbs) hx
    have h2 : 0 ≤ (Finset.univ.sup (fun i : I => (a i).natAbs)) * M := Nat.zero_le _
    omega
  have hh_supp : ∀ x : ℤ, x ∉ Work.Peluse.symIcc B → h x = 0 := by
    intro x hx
    change (∑ i : I, ∑ c : Fin M, ∑ c' : Fin M,
        f (x + a i * ((c : ℤ) - (c' : ℤ)))) = 0
    rw [hB] at hx
    exact acfShiftSupp (M := M) (a := a) (f := f) S₀ hsup x hx
  -- Step A: the left-hand side is the square of the real part of `∑'_x h x * conj (f x)`.
  have hh_eq : ∀ x : ℤ, h x = ∑ q : I × (Fin M × Fin M),
      f (x + a q.1 * ((q.2.1 : ℤ) - (q.2.2 : ℤ))) := by
    intro x
    change (∑ i : I, ∑ c : Fin M, ∑ c' : Fin M,
        f (x + a i * ((c : ℤ) - (c' : ℤ)))) = _
    rw [sum3_eq_sum_prod (G := fun (i : I) (c c' : Fin M) =>
      f (x + a i * ((c : ℤ) - (c' : ℤ))))]
  have hLHS : (∑ i : I, ∑ c : Fin M, ∑ c' : Fin M,
      ∑' x : ℤ, f (x + a i * ((c : ℤ) - (c' : ℤ))) * star (f x))
      = ∑' x : ℤ, h x * star (f x) := by
    rw [sum3_eq_sum_prod (G := fun (i : I) (c c' : Fin M) =>
      ∑' x : ℤ, f (x + a i * ((c : ℤ) - (c' : ℤ))) * star (f x))]
    have key : (∑ p : I × (Fin M × Fin M),
        ∑' x : ℤ, f (x + a p.1 * ((p.2.1 : ℤ) - (p.2.2 : ℤ))) * star (f x))
        = ∑' x : ℤ, ∑ p : I × (Fin M × Fin M),
            f (x + a p.1 * ((p.2.1 : ℤ) - (p.2.2 : ℤ))) * star (f x) :=
      tsum_finset_sum_eq
        (fun (p : I × (Fin M × Fin M)) (x : ℤ) =>
          f (x + a p.1 * ((p.2.1 : ℤ) - (p.2.2 : ℤ))) * star (f x)) S₀
        (fun (p : I × (Fin M × Fin M)) (x : ℤ) hx => by
          rw [hsup x hx, star_zero, mul_zero])
    rw [key]
    refine tsum_congr fun x => ?_
    rw [hh_eq x, Finset.sum_mul]
  -- Step B: the right-hand side's inner complex sum is the `L²`-mass of `h`.
  have hgram := acfGram (I := I) (M := M) (a := a) (f := f) S₀ hsup
  have hAh : (∑' x : ℤ, h x * star (h x)) = Rc := by
    rw [hRc, hhdef]
    exact hgram
  have hnorm : Rc = ((∑' x : ℤ, ‖h x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hAh, Complex.ofReal_tsum]
    exact tsum_congr fun x => (ofReal_normSq (h x)).symm
  have hnormHs : Rc.re = ∑' x : ℤ, ‖h x‖ ^ 2 := by
    rw [hnorm, Complex.ofReal_re]
  -- Step C: Cauchy–Schwarz over the box `symIcc B`, which contains `S₀` and the support of `h`.
  have hTbox : (∑' x : ℤ, h x * star (f x)) = ∑ x ∈ Work.Peluse.symIcc B, h x * star (f x) := by
    refine tsum_eq_sum (s := Work.Peluse.symIcc B) fun x hx => ?_
    have hfx : f x = 0 := hsup x fun hmem => hx (hS₀_sub hmem)
    rw [hfx, star_zero, mul_zero]
  have hCs := acfNormSqCS (s := Work.Peluse.symIcc B) (u := h) (v := f)
  have hnormH : (∑ x ∈ Work.Peluse.symIcc B, ‖h x‖ ^ 2) = ∑' x : ℤ, ‖h x‖ ^ 2 := by
    refine (tsum_eq_sum (s := Work.Peluse.symIcc B) (f := fun x => ‖h x‖ ^ 2) ?_).symm
    intro x hx
    rw [hh_supp x hx]
    simp
  have hnormF : (∑ x ∈ Work.Peluse.symIcc B, ‖f x‖ ^ 2) ≤ (S₀.card : ℝ) := by
    have hsub := Finset.sum_subset (s₁ := S₀) (s₂ := Work.Peluse.symIcc B)
      (f := fun x => ‖f x‖ ^ 2) hS₀_sub
      (fun x _ hxs => by rw [hsup x hxs]; simp)
    rw [← hsub]
    calc (∑ x ∈ S₀, ‖f x‖ ^ 2) ≤ ∑ x ∈ S₀, (1 : ℝ) := by
          refine Finset.sum_le_sum fun x _ => ?_
          nlinarith [norm_nonneg (f x), hbd x]
      _ = (S₀.card : ℝ) := by simp
  -- Step D: assembly.
  calc (∑ i : I, ∑ c : Fin M, ∑ c' : Fin M,
        ∑' x : ℤ, f (x + a i * ((c : ℤ) - (c' : ℤ))) * star (f x)).re ^ 2
      = (∑' x : ℤ, h x * star (f x)).re ^ 2 := by rw [hLHS]
    _ ≤ ‖∑' x : ℤ, h x * star (f x)‖ ^ 2 := by
        have h1 := Complex.abs_re_le_norm (∑' x : ℤ, h x * star (f x))
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = ‖∑ x ∈ Work.Peluse.symIcc B, h x * star (f x)‖ ^ 2 := by rw [hTbox]
    _ ≤ (∑ x ∈ Work.Peluse.symIcc B, ‖h x‖ ^ 2)
          * (∑ x ∈ Work.Peluse.symIcc B, ‖f x‖ ^ 2) := hCs
    _ = (∑' x : ℤ, ‖h x‖ ^ 2) * (∑ x ∈ Work.Peluse.symIcc B, ‖f x‖ ^ 2) := by rw [hnormH]
    _ ≤ (∑' x : ℤ, ‖h x‖ ^ 2) * (S₀.card : ℝ) := by
        refine mul_le_mul_of_nonneg_left hnormF ?_
        exact tsum_nonneg fun x => by positivity
    _ = Rc.re * (S₀.card : ℝ) := by rw [hnormHs]
    _ = (S₀.card : ℝ) * Rc.re := by ring

end Work.Peluse.SwapCS0

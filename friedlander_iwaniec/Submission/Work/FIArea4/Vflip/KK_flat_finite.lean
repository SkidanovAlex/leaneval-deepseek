import Mathlib
import Submission.Work.FIArea4.box_defs
import Submission.Work.FIArea4.flat_defs
import Submission.Work.FIArea4.Vflip.KK_eq_tsum_gen

namespace Work.FIArea4.Vflip

open scoped BigOperators FourierTransform
open Finset

noncomputable section

/-!
# The flat part of the local kernel `KK` as a finite sum over the support box

For a flat pair (`Work.FIArea4.flatPair d₁ d₂`, i.e. `d₁' d₂' = □` for the odd parts) the Jacobi
weight `wChar` collapses to the indicator of `Nat.Coprime r (d₁ d₂)`, and Poisson summation turns
the local kernel

`KK F R d₁ d₂ a = (1/q) Σ_k F(k/q) Σ_r χ_r e(k r a / q)`,  `q = [d₁,d₂]`,

— with `F = 𝓕f` for the bump majorant `f` of `Work.FIArea4.BumpData` — into the *finite* sum

`Σ_{r ∈ (R,2R], (r,d₁d₂)=1} Σ_{s ∈ suppBox S, s ≡ r a (mod q)} f s`.

That is exactly the shape on which the flat-part estimate (`flat_part_le`) operates, since the
support of `f` is contained in `[S/2, 5S/2]`.

The three ingredients, each isolated below, are
* `bump_decay_two` : the decay `F =O |ξ|^(-2)` needed for absolute convergence;
* `KK_eq_sum_tsum` : the rearrangement of `KK` (finite `r`-sum outside, `tsum` in `k` inside);
* `bump_poisson` : Poisson summation for the bump, `(1/q) Σ_k F(k/q) e(rka/q) = Σ_m f(ra + mq)`;
* `lattice_sum_eq_suppBox` : the lattice sum over `ra + qℤ` equals the finite sum over the box.
-/

/-- The Fourier transform of the bump of `BumpData` decays at least like `|ξ|^(-2)`: for `|ξ| ≥ 1`
one has `1 + S|ξ| ≥ S|ξ| ≥ |ξ|`, so `(1 + S|ξ|)^{-2} ≤ |ξ|^{-2}`. -/
lemma bump_decay_two (S : ℕ) (hS : 1 ≤ S) (f : ℝ → ℝ) (F : ℝ → ℂ) (C₀ : ℝ)
    (hM : Work.FIArea4.BumpData S f F C₀) :
    F =O[Filter.cocompact ℝ] (fun ξ : ℝ => |ξ| ^ (-2 : ℝ)) := by
  obtain ⟨-, -, -, -, hC0, -, hbound⟩ := hM
  have hS1 : (1:ℝ) ≤ (S:ℝ) := by exact_mod_cast hS
  have hev : ∀ᶠ ξ : ℝ in Filter.cocompact ℝ, (1:ℝ) ≤ |ξ| := by
    refine Filter.mem_of_superset
      (isCompact_Icc (a := (-1:ℝ)) (b := 1)).compl_mem_cocompact ?_
    intro ξ hξ
    change (1:ℝ) ≤ |ξ|
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hξ
    rcases hξ with h | h
    · rw [abs_of_neg (by linarith : ξ < 0)]; linarith
    · exact le_trans (le_of_lt h) (le_abs_self ξ)
  refine Asymptotics.IsBigO.of_bound (C₀ * S) ?_
  filter_upwards [hev] with ξ hξ
  have hpos : (0:ℝ) < |ξ| := by linarith
  have hle : |ξ| ≤ 1 + (S:ℝ) * |ξ| := by
    nlinarith [mul_le_mul_of_nonneg_right hS1 (abs_nonneg ξ)]
  have h2 : (1 + (S:ℝ) * |ξ|) ^ (-(2:ℝ)) ≤ |ξ| ^ (-(2:ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hpos hle (by norm_num)
  calc ‖F ξ‖ ≤ C₀ * (S:ℝ) * (1 + (S:ℝ) * |ξ|) ^ (-(2:ℝ)) := hbound ξ
    _ ≤ C₀ * (S:ℝ) * |ξ| ^ (-(2:ℝ)) := by
        apply mul_le_mul_of_nonneg_left h2
        exact mul_nonneg (le_of_lt hC0) (by positivity)
    _ = (C₀ * (S:ℝ)) * ‖|ξ| ^ (-(2:ℝ))‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg ξ) _)]

/-- Under flatness the Jacobi weight is the coprimality indicator, so the finite `r`-sum and the
`k`-series of `KK` may be exchanged (the decay `F =O |ξ|^(-2)` makes every series summable). -/
theorem KK_eq_sum_tsum (F : ℝ → ℂ)
    (hdec : F =O[Filter.cocompact ℝ] (fun ξ : ℝ => |ξ| ^ (-2 : ℝ)))
    (R d1 d2 a : ℕ) (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2) (hflat : Work.FIArea4.flatPair d1 d2) :
    Work.FIArea4.KK F R d1 d2 a
      = ∑ r ∈ (Finset.Ioc R (2 * R)).filter (fun r => Nat.Coprime r (d1 * d2)),
          (1 / (Nat.lcm d1 d2 : ℝ)) * (∑' k : ℤ, F ((k : ℝ) / (Nat.lcm d1 d2 : ℝ)) *
            Complex.exp (2 * Real.pi * Complex.I * (r : ℝ) * (k : ℝ) * (a : ℝ) /
              (Nat.lcm d1 d2 : ℝ))) := by
  have hqpos : 0 < Nat.lcm d1 d2 := Nat.lcm_pos (by omega) (by omega)
  have hqR : (0:ℝ) < (Nat.lcm d1 d2 : ℝ) := by exact_mod_cast hqpos
  have hsum : Summable (fun k : ℤ => F ((k:ℝ) / (Nat.lcm d1 d2 : ℝ))) :=
    Commons.Analysis.Fourier.summable_of_isBigO_cocompact_rpow (b := 2) one_lt_two hdec hqR
  have hsumE : ∀ r : ℕ, Summable (fun k : ℤ => F ((k:ℝ) / (Nat.lcm d1 d2 : ℝ)) *
      Complex.exp (2 * Real.pi * Complex.I * (r:ℝ) * (k:ℝ) * (a:ℝ) /
        (Nat.lcm d1 d2 : ℝ))) := by
    intro r
    refine Summable.of_norm_bounded hsum.norm (fun k => ?_)
    rw [norm_mul, norm_exp_unit r a (Nat.lcm d1 d2) k, mul_one]
  have hw : ∀ k : ℤ, (∑ r ∈ Finset.Ioc R (2*R), Work.FIArea4.wChar d1 d2 r *
        Complex.exp (2 * Real.pi * Complex.I * (r:ℝ) * (k:ℝ) * (a:ℝ) /
          (Nat.lcm d1 d2 : ℝ)))
      = ∑ r ∈ (Finset.Ioc R (2 * R)).filter (fun r => Nat.Coprime r (d1 * d2)),
          Complex.exp (2 * Real.pi * Complex.I * (r:ℝ) * (k:ℝ) * (a:ℝ) /
            (Nat.lcm d1 d2 : ℝ)) := by
    intro k
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    rw [wChar_eq_ite d1 d2 hflat r]
    by_cases h : Nat.Coprime r (d1 * d2)
    · rw [if_pos h, if_pos h, one_mul]
    · rw [if_neg h, if_neg h, zero_mul]
  unfold Work.FIArea4.KK
  rw [show (∑' k : ℤ, F ((k:ℝ) / (Nat.lcm d1 d2 : ℝ)) *
        (∑ r ∈ Finset.Ioc R (2*R), Work.FIArea4.wChar d1 d2 r *
          Complex.exp (2 * Real.pi * Complex.I * (r:ℝ) * (k:ℝ) * (a:ℝ) /
            (Nat.lcm d1 d2 : ℝ))))
      = ∑' k : ℤ, ∑ r ∈ (Finset.Ioc R (2 * R)).filter (fun r => Nat.Coprime r (d1 * d2)),
          F ((k:ℝ) / (Nat.lcm d1 d2 : ℝ)) *
            Complex.exp (2 * Real.pi * Complex.I * (r:ℝ) * (k:ℝ) * (a:ℝ) /
              (Nat.lcm d1 d2 : ℝ))
      from by
    apply tsum_congr; intro k
    rw [hw k, Finset.mul_sum]]
  rw [Summable.tsum_finsetSum (f := fun (r:ℕ) (k:ℤ) => F ((k:ℝ) / (Nat.lcm d1 d2 : ℝ)) *
      Complex.exp (2 * Real.pi * Complex.I * (r:ℝ) * (k:ℝ) * (a:ℝ) /
        (Nat.lcm d1 d2 : ℝ)))
      (s := (Finset.Ioc R (2 * R)).filter (fun r => Nat.Coprime r (d1 * d2)))
      (fun r _ => hsumE r)]
  rw [Finset.mul_sum]

/-- Poisson summation for the bump: applying `Work.FIArea4.poisson_residue` to the complexified
bump `fun x => (f x : ℂ)` (whose Fourier transform is `F` and which is continuous with compact
support) turns the weighted `k`-series into the lattice sum `Σ_m f(ra + mq)`. -/
theorem bump_poisson (S : ℕ) (hS : 1 ≤ S) (f : ℝ → ℝ) (F : ℝ → ℂ) (C₀ : ℝ)
    (hM : Work.FIArea4.BumpData S f F C₀) (q : ℕ) (hq : 0 < q) (r a : ℕ) :
    (1 / (q : ℝ)) * (∑' k : ℤ, F ((k : ℝ) / (q : ℝ)) *
        Complex.exp (2 * Real.pi * Complex.I * (r : ℝ) * (k : ℝ) * (a : ℝ) / (q : ℝ)))
      = ∑' m : ℤ, ((f (((r * a : ℕ) : ℝ) + (m : ℝ) * (q : ℝ)) : ℝ) : ℂ) := by
  have hsupp := hM.2.2.1
  have hfcont := hM.2.2.2.1
  have hC0 := hM.2.2.2.2.1
  have hFid := hM.2.2.2.2.2.1
  have hbound := hM.2.2.2.2.2.2
  have hdecF := bump_decay_two S hS f F C₀ hM
  have hcont : Continuous (fun x : ℝ => (f x : ℂ)) := Complex.continuous_ofReal.comp hfcont
  have hcs : HasCompactSupport (fun x : ℝ => (f x : ℂ)) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := (S:ℝ)/2) (b := 5*(S:ℝ)/2)) ?_
    intro x hx
    simp only [Function.mem_support] at hx
    exact hsupp x (by simpa using hx)
  have hbig : (fun x : ℝ => (f x : ℂ)) =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-2:ℝ)) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    have hev : (fun x : ℝ => (f x : ℂ)) =ᶠ[Filter.cocompact ℝ] 0 := by
      rw [← Filter.coclosedCompact_eq_cocompact, ← hasCompactSupport_iff_eventuallyEq]
      exact hcs
    filter_upwards [hev] with x hx
    have hx' : (f x : ℂ) = 0 := hx
    rw [hx', norm_zero]; positivity
  have hFf : (FourierTransform.fourier (fun x : ℝ => (f x : ℂ)))
      =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-2:ℝ)) := by
    rw [show FourierTransform.fourier (fun x : ℝ => (f x : ℂ)) = F from
      funext fun ξ => (hFid ξ).symm]
    exact hdecF
  have hp := Work.FIArea4.poisson_residue (fun x : ℝ => (f x : ℂ)) hcont
    (by norm_num : (1:ℝ) < 2) hbig hFf q hq (((r*a : ℕ) : ℝ))
  have hL : (∑' m : ℤ, (fun x : ℝ => (f x : ℂ)) ((((r*a : ℕ) : ℝ)) + ((m * (q:ℤ) : ℤ) : ℝ)))
      = ∑' m : ℤ, ((f (((r * a : ℕ) : ℝ) + (m:ℝ)*(q:ℝ)) : ℝ) : ℂ) := by
    apply tsum_congr; intro m
    have h2 : ((m * (q:ℤ) : ℤ) : ℝ) = (m:ℝ)*(q:ℝ) := by push_cast; ring
    rw [h2]
  have hR : (1 / (q:ℝ)) * (∑' k : ℤ,
        (FourierTransform.fourier (fun x : ℝ => (f x : ℂ))) ((k:ℝ)/(q:ℝ)) *
        Complex.exp (2*Real.pi*Complex.I*(((r*a : ℕ) : ℝ))*(k:ℝ)/(q:ℝ)))
      = (1 / (q:ℝ)) * (∑' k : ℤ, F ((k:ℝ)/(q:ℝ)) *
        Complex.exp (2*Real.pi*Complex.I*(r:ℝ)*(k:ℝ)*(a:ℝ)/(q:ℝ))) := by
    congr 1
    apply tsum_congr; intro k
    rw [show FourierTransform.fourier (fun x : ℝ => (f x : ℂ)) ((k:ℝ)/(q:ℝ))
      = F ((k:ℝ)/(q:ℝ)) from (hFid _).symm]
    congr 1
    push_cast; ring_nf
  rw [← hR, ← hp]
  exact hL

/-- The lattice sum `Σ_{m∈ℤ} f(c + mq)` of a function supported in `[S/2, 5S/2]` is the finite sum
over the box `suppBox S = (S/2-1, 5S/2]` restricted to the residue class of `c`: the map
`m ↦ c + mq` is a bijection from the (finitely many) `m` with `f(c+mq) ≠ 0` onto the elements of
`suppBox S` in that class on which `f` does not vanish. -/
theorem lattice_sum_eq_suppBox (S : ℕ) (hS : 1 ≤ S) (f : ℝ → ℝ) (q c : ℕ) (hq : 0 < q)
    (hsupp : ∀ x : ℝ, f x ≠ 0 → (S : ℝ) / 2 ≤ x ∧ x ≤ 5 * (S : ℝ) / 2) :
    (∑' m : ℤ, ((f ((c : ℝ) + (m : ℝ) * (q : ℝ)) : ℝ) : ℂ))
      = ∑ s ∈ Work.FIArea4.suppBox S,
          (if s % q = c % q then ((f s : ℝ) : ℂ) else 0) := by
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hqZ : (0:ℤ) < (q:ℤ) := by exact_mod_cast hq
  have hqZne : (q:ℤ) ≠ 0 := ne_of_gt hqZ
  have hS1 : (1:ℝ) ≤ (S:ℝ) := by exact_mod_cast hS
  have hzero : ∀ x : ℝ, (x < (S:ℝ)/2 ∨ 5*(S:ℝ)/2 < x) → f x = 0 := by
    intro x hx
    by_contra h
    obtain ⟨h1, h2⟩ := hsupp x h
    rcases hx with hx | hx
    · linarith
    · linarith
  have hlow : ∀ m : ℤ, m < -(c:ℤ) → (c:ℝ) + (m:ℝ)*(q:ℝ) < (S:ℝ)/2 := by
    intro m hm
    have hm' : (m:ℝ) ≤ -((c:ℤ):ℝ) - 1 := by
      have h : m ≤ -(c:ℤ) - 1 := by omega
      exact_mod_cast h
    have hstep : (m:ℝ)*(q:ℝ) ≤ (-((c:ℤ):ℝ)-1)*(q:ℝ) :=
      mul_le_mul_of_nonneg_right hm' (by linarith)
    calc (c:ℝ) + (m:ℝ)*(q:ℝ) ≤ (c:ℝ) + (-((c:ℤ):ℝ)-1)*(q:ℝ) := by linarith
      _ = -(c:ℝ)*((q:ℝ)-1) - (q:ℝ) := by push_cast; ring
      _ ≤ -1 := by
          have hc : (0:ℝ) ≤ ((c:ℤ):ℝ) := by positivity
          nlinarith [hq1]
      _ < (S:ℝ)/2 := by linarith
  have hhigh : ∀ m : ℤ, ((5*S/2:ℕ):ℤ) < m → 5*(S:ℝ)/2 < (c:ℝ) + (m:ℝ)*(q:ℝ) := by
    intro m hm
    have hm' : ((5*S/2:ℕ):ℝ) + 1 ≤ (m:ℝ) := by
      have h1 : (((5*S/2:ℕ):ℤ) + 1 : ℤ) ≤ m := by omega
      have h2 : (((((5*S/2:ℕ):ℤ) + 1 : ℤ)) : ℝ) ≤ ((m:ℤ):ℝ) := by exact_mod_cast h1
      simp only [Int.cast_add, Int.cast_one, Int.cast_natCast] at h2
      exact h2
    have hfl : 5*(S:ℝ)/2 < ((5*S/2:ℕ):ℝ) + 1 := by
      have h : 5*S < 2*(5*S/2 + 1) := by
        have := Nat.div_add_mod (5*S) 2
        omega
      have h2 : (5*S : ℝ) < 2*(((5*S/2:ℕ):ℝ) + 1) := by exact_mod_cast h
      linarith
    have hmpos : (0:ℝ) < (m:ℝ) := by linarith
    have hstep : (m:ℝ) ≤ (m:ℝ)*(q:ℝ) := by nlinarith [hmpos, hq1]
    have hc : (0:ℝ) ≤ (c:ℝ) := by positivity
    linarith
  set s0 : Finset ℤ := (Finset.Icc (-(c:ℤ)) ((5*S/2:ℕ):ℤ)).filter
      (fun m => f ((c:ℝ) + (m:ℝ)*(q:ℝ)) ≠ 0) with hs0
  set t : Finset ℕ := (Work.FIArea4.suppBox S).filter (fun n => n % q = c % q) with ht
  set t0 : Finset ℕ := t.filter (fun n => f (n:ℝ) ≠ 0) with ht0
  have hpos_of : ∀ m : ℤ, f ((c:ℝ) + (m:ℝ)*(q:ℝ)) ≠ 0 → 0 < c + m*(q:ℤ) := by
    intro m hm
    have hx := (hsupp _ hm).1
    have h1 : (0:ℝ) < ((c + m*(q:ℤ) : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast h1
  have hcast_of : ∀ m : ℤ, 0 ≤ c + m*(q:ℤ) →
      (((c + m*(q:ℤ)).toNat : ℕ) : ℝ) = (c:ℝ) + (m:ℝ)*(q:ℝ) := by
    intro m hpos
    have h := Int.toNat_of_nonneg hpos
    calc (((c + m*(q:ℤ)).toNat : ℕ) : ℝ) = (((c + m*(q:ℤ)).toNat : ℤ) : ℝ) := by
          push_cast; ring
      _ = ((c + m*(q:ℤ) : ℤ) : ℝ) := by rw [h]
      _ = (c:ℝ) + (m:ℝ)*(q:ℝ) := by push_cast; ring
  have hmod_of : ∀ m : ℤ, 0 ≤ c + m*(q:ℤ) → (c + m*(q:ℤ)).toNat % q = c % q := by
    intro m hpos
    have h : (((c + m*(q:ℤ)).toNat : ℕ) : ℤ) = (c:ℤ) + (m:ℤ)*(q:ℤ) :=
      Int.toNat_of_nonneg hpos
    have key : ((((c + m*(q:ℤ)).toNat % q : ℕ)) : ℤ) = (((c % q : ℕ)) : ℤ) := by
      rw [Int.natCast_emod, Int.natCast_emod, h, mul_comm (m:ℤ) (q:ℤ),
        Int.add_mul_emod_self_left]
    exact_mod_cast key
  have htsum : (∑' m : ℤ, ((f ((c:ℝ)+(m:ℝ)*(q:ℝ)) : ℝ) : ℂ))
      = ∑ m ∈ s0, ((f ((c:ℝ)+(m:ℝ)*(q:ℝ)) : ℝ) : ℂ) := by
    refine tsum_eq_sum ?_
    intro m hm
    rw [hs0] at hm
    simp only [Finset.mem_filter, not_and_or] at hm
    rcases hm with hm | hm
    · rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hm
      rcases hm with hm | hm
      · rw [hzero _ (Or.inl (hlow m hm)), Complex.ofReal_zero]
      · rw [hzero _ (Or.inr (hhigh m hm)), Complex.ofReal_zero]
    · rw [not_not] at hm
      rw [hm, Complex.ofReal_zero]
  have hbij : ∑ m ∈ s0, ((f ((c:ℝ)+(m:ℝ)*(q:ℝ)) : ℝ) : ℂ)
      = ∑ n ∈ t0, ((f (n:ℝ) : ℝ) : ℂ) := by
    refine Finset.sum_bij (fun (m : ℤ) (_ : m ∈ s0) => (c + m*(q:ℤ)).toNat) ?_ ?_ ?_ ?_
    · -- the image of the source lies in the target
      intro m hm
      rw [hs0, Finset.mem_filter] at hm
      obtain ⟨hmIcc, hmf⟩ := hm
      rw [Finset.mem_Icc] at hmIcc
      obtain ⟨hm1, hm2⟩ := hmIcc
      have hpos := hpos_of m hmf
      have hcast := hcast_of m (le_of_lt hpos)
      have hx := (hsupp _ hmf).1
      have hx2 := (hsupp _ hmf).2
      rw [ht0]
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · rw [ht]
        refine Finset.mem_filter.mpr ⟨?_, hmod_of m (le_of_lt hpos)⟩
        rw [Work.FIArea4.suppBox, Finset.mem_Ioc]
        have hle : (((c + m*(q:ℤ)).toNat : ℕ) : ℝ) ≤ 5*(S:ℝ)/2 := by
          rw [hcast]; exact hx2
        have hS2 : (S/2 : ℕ) ≤ (c + m*(q:ℤ)).toNat := by
          rw [← Nat.cast_le (α := ℝ)]
          exact le_trans (Nat.cast_div_le (m := S) (n := 2)) (by rw [hcast]; exact hx)
        have hge1 : 1 ≤ (c + m*(q:ℤ)).toNat := by omega
        refine ⟨by omega, ?_⟩
        rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
        have h2 : ((((c + m*(q:ℤ)).toNat : ℕ) : ℝ)) * 2 ≤ 5*(S:ℝ) := by linarith
        exact_mod_cast h2
      · rw [hcast]; exact hmf
    · -- injectivity
      intro m1 hm1 m2 hm2 heq
      rw [hs0, Finset.mem_filter] at hm1 hm2
      have h1 := Int.toNat_of_nonneg (le_of_lt (hpos_of m1 hm1.2))
      have h2 := Int.toNat_of_nonneg (le_of_lt (hpos_of m2 hm2.2))
      have h3 : (c + m1*(q:ℤ)) = (c + m2*(q:ℤ)) := by
        have := congrArg (fun n : ℕ => (n:ℤ)) heq
        rw [h1, h2] at this
        exact this
      have h4 : m1*(q:ℤ) = m2*(q:ℤ) := by linarith
      exact mul_right_cancel₀ hqZne h4
    · -- surjectivity
      intro n hn
      rw [ht0, Finset.mem_filter] at hn
      obtain ⟨hnt, hnf⟩ := hn
      rw [ht, Finset.mem_filter] at hnt
      obtain ⟨hnbox, hnmod⟩ := hnt
      rw [Work.FIArea4.suppBox, Finset.mem_Ioc] at hnbox
      obtain ⟨hnlo, hnhi⟩ := hnbox
      have hdvd : (q:ℤ) ∣ (n:ℤ) - (c:ℤ) := by
        have h : ((n:ℤ) % (q:ℤ)) = ((c:ℤ) % (q:ℤ)) := by
          rw [← Int.natCast_emod, ← Int.natCast_emod, hnmod]
        exact Int.dvd_iff_emod_eq_zero.mpr (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp h)
      set m : ℤ := ((n:ℤ) - (c:ℤ)) / (q:ℤ) with hmdef
      have hmq : m * (q:ℤ) = (n:ℤ) - (c:ℤ) := Int.ediv_mul_cancel hdvd
      have harg : (c:ℝ) + (m:ℝ)*(q:ℝ) = (n:ℝ) := by
        calc (c:ℝ) + (m:ℝ)*(q:ℝ) = ((c + m*(q:ℤ) : ℤ) : ℝ) := by push_cast; ring
          _ = ((n:ℤ) : ℝ) := by
              rw [show c + m*(q:ℤ) = (n:ℤ) from by rw [hmq]; ring]
          _ = (n:ℝ) := by push_cast; ring
      refine ⟨m, ?_, ?_⟩
      · rw [hs0]
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · rw [Finset.mem_Icc]
          constructor
          · have hkey : (m + (c:ℤ)) * (q:ℤ) = (n:ℤ) + (c:ℤ)*((q:ℤ)-1) := by
              rw [add_mul, hmq]; ring
            have h0 : 0 ≤ (m + (c:ℤ)) * (q:ℤ) := by
              rw [hkey]
              have h2 : 0 ≤ (c:ℤ)*((q:ℤ)-1) := by
                apply mul_nonneg (Int.natCast_nonneg c); omega
              linarith [Int.natCast_nonneg n]
            have hmc : 0 ≤ m + (c:ℤ) := (mul_nonneg_iff_of_pos_right hqZ).mp h0
            linarith
          · have hmq' : m * (q:ℤ) ≤ ((5*S/2:ℕ):ℤ) := by
              rw [hmq]
              have h3 : (n:ℤ) ≤ ((5*S/2:ℕ):ℤ) := by exact_mod_cast hnhi
              omega
            by_cases h : 0 ≤ m
            · have hle : m ≤ m * (q:ℤ) := by nlinarith [h, hqZ]
              linarith
            · linarith [Int.natCast_nonneg (5*S/2)]
        · rw [harg]; exact hnf
      · have : c + m*(q:ℤ) = (n:ℤ) := by rw [hmq]; ring
        rw [this, Int.toNat_natCast]
    · -- the two summands agree along the bijection
      intro m hm
      rw [hs0, Finset.mem_filter] at hm
      rw [hcast_of m (le_of_lt (hpos_of m hm.2))]
  have hfil : ∑ n ∈ t0, ((f (n:ℝ) : ℝ) : ℂ)
      = ∑ n ∈ t, ((f (n:ℝ) : ℝ) : ℂ) :=
    Finset.sum_filter_of_ne (fun x _ hx => by simpa using hx)
  rw [htsum, hbij, hfil, ← Finset.sum_filter, ← ht]

/-- **The flat part of `KK` is a finite sum over the support box.**  For a flat pair `d₁ d₂` and the
bump majorant `f` of `BumpData S f F C₀` (so `F = 𝓕f` with `f` supported in `[S/2, 5S/2]`), the
local kernel equals the finite sum of `f` over the box `suppBox S`, restricted to the residue class
`r a` mod `[d₁,d₂]`, for the `r ∈ (R,2R]` coprime to `d₁d₂`. -/
theorem KK_flat_finite (S : ℕ) (hS : 1 ≤ S) (f : ℝ → ℝ) (F : ℝ → ℂ) (C₀ : ℝ)
    (hM : Work.FIArea4.BumpData S f F C₀) (R d1 d2 a : ℕ) (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2)
    (hflat : Work.FIArea4.flatPair d1 d2) :
    Work.FIArea4.KK F R d1 d2 a
      = ∑ r ∈ (Finset.Ioc R (2 * R)).filter (fun r => Nat.Coprime r (d1 * d2)),
          ∑ s ∈ Work.FIArea4.suppBox S,
            (if s % Nat.lcm d1 d2 = (r * a) % Nat.lcm d1 d2
              then ((f s : ℝ) : ℂ) else 0) := by
  have hq : 0 < Nat.lcm d1 d2 := Nat.lcm_pos (by omega) (by omega)
  have hsupp := hM.2.2.1
  have hdec := bump_decay_two S hS f F C₀ hM
  rw [KK_eq_sum_tsum F hdec R d1 d2 a hd1 hd2 hflat]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [bump_poisson S hS f F C₀ hM (Nat.lcm d1 d2) hq r a]
  exact lattice_sum_eq_suppBox S hS f (Nat.lcm d1 d2) (r * a) hq hsupp

end

end Work.FIArea4.Vflip

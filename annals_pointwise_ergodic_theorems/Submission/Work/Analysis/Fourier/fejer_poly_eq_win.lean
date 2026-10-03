import Mathlib
import Submission.Work.Analysis.Fourier.dyadic_lp_defs

/-!
# The closed form of the normalised Fejér polynomial

`Work.Analysis.Fourier.fejerPoly N θ` is the trigonometric polynomial with the normalised
Fejér (triangular) coefficients `fejerCoeff N n = (N+1)⁻¹ (1 - |n|/(N+1))` on `|n| ≤ N`,
and `fejerWin N θ` is its classical closed form
`(sin (π(N+1)θ) / ((N+1) sin (πθ)))²`.  Here we prove that the two agree, for every `N` and `θ`.

The proof is the classical computation.  Writing `M = N+1` and `Z = exp (-2πiθ)`,
`fejerPoly N θ = M⁻² ∑_{n} (M - |n|) Z^n`.  Grouping the pairs `(j,k)` with `j,k < M` by the
difference `n = j - k` (the fibre over `n` has exactly `M - |n|` elements) shows

`∑_{n} (M - |n|) Z^n = ∑_{j,k<M} Z^{j-k} = (∑_{j<M} Z^j) (∑_{k<M} Z^{-k})`,

and since `|Z| = 1` the second factor is `conj (∑_{j<M} Z^j)`, so the right hand side is
`normSq (∑_{j<M} Z^j)`.  Finally the telescoping identity `(∑_{j<M} Z^j)(1-Z) = 1 - Z^M`
together with `normSq (1 - exp (iα)) = 4 sin (α/2)²` evaluates the norm square as
`sin²(πMθ)/sin²(πθ)` when `sin(πθ) ≠ 0`, while for `sin(πθ) = 0` (i.e. `θ` an integer) we have
`Z = 1` and the sum is `M`.
-/

namespace Work.Analysis.Fourier
open scoped BigOperators
noncomputable section

/-- The basic exponential `Z θ = exp (-(2πiθ))`; its `n`-th power is the character
`e^{-2πinθ}`. -/
private def ze (θ : ℝ) : ℂ := Complex.exp (-(2 * Real.pi * Complex.I * (θ : ℂ)))

/-- The normalised Fejér coefficient is the tent coefficient on its support. -/
private lemma fejerCoeff_eq {N : ℕ} {n : ℤ} (hn : n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ)) :
    fejerCoeff N n = (((N:ℝ)+1)^2)⁻¹ * (((N:ℝ)+1) - |(n:ℝ)|) := by
  have hle : |(n:ℝ)| ≤ (N:ℝ) := by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have h1' : ((-(N:ℤ) : ℤ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast h1
      push_cast at h1'
      linarith
    · have h2' : (n:ℝ) ≤ (N:ℝ) := by exact_mod_cast h2
      linarith
  have hpos : 0 ≤ 1 - |(n:ℝ)| / ((N:ℝ)+1) := by
    have hMpos : (0:ℝ) < (N:ℝ)+1 := by positivity
    have : |(n:ℝ)| / ((N:ℝ)+1) ≤ 1 := by
      rw [div_le_one hMpos]; linarith
    linarith
  unfold fejerCoeff
  rw [max_eq_right hpos]
  field_simp

/-- Powers of `ze θ` are the characters `e^{-2πinθ}`. -/
private lemma ze_pow_int (θ : ℝ) (n : ℤ) :
    Complex.exp (-(2 * Real.pi * Complex.I * (n : ℂ) * (θ : ℂ))) = ze θ ^ n := by
  rw [show -(2 * Real.pi * Complex.I * (n : ℂ) * (θ : ℂ))
        = (n : ℂ) * (-(2 * Real.pi * Complex.I * (θ : ℂ))) from by ring,
      Complex.exp_int_mul]
  rfl

private lemma ze_eq (θ : ℝ) :
    ze θ = Complex.exp (((-(2 * Real.pi * θ) : ℝ) : ℂ) * Complex.I) := by
  unfold ze
  congr 1
  push_cast
  ring

private lemma normSq_ze (θ : ℝ) : Complex.normSq (ze θ) = 1 := by
  rw [ze_eq, Complex.normSq_eq_norm_sq, Complex.norm_exp]
  have hre : (((-(2 * Real.pi * θ) : ℝ) : ℂ) * Complex.I).re = 0 := by simp [Complex.mul_re]
  rw [hre]
  norm_num

private lemma norm_ze (θ : ℝ) : ‖ze θ‖ = 1 := by
  have h := normSq_ze θ
  rw [Complex.normSq_eq_norm_sq] at h
  have hnn : (0:ℝ) ≤ ‖ze θ‖ := norm_nonneg _
  nlinarith

private lemma ze_ne_zero (θ : ℝ) : ze θ ≠ 0 := by
  intro h
  have := normSq_ze θ
  rw [h, Complex.normSq_zero] at this
  norm_num at this

/-- `normSq (1 - exp (iα)) = 4 sin (α/2)²`. -/
private lemma normSq_one_sub_exp_I (α : ℝ) :
    Complex.normSq (1 - Complex.exp ((α : ℂ) * Complex.I)) = 4 * Real.sin (α / 2) ^ 2 := by
  have hcos : Real.cos (2 * (α / 2)) = Real.cos α := by rw [show 2 * (α/2) = α from by ring]
  rw [Complex.exp_ofReal_mul_I, Real.sin_sq_eq_half_sub, hcos, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_im, Complex.one_im,
    Complex.add_im, Complex.mul_im, mul_one, mul_zero, sub_zero, zero_sub, add_zero, zero_add]
  ring_nf
  rw [Real.sin_sq]
  ring

/-- `normSq (1 - (ze θ)^n) = 4 sin (π n θ)²`. -/
private lemma normSq_one_sub_ze_pow (θ : ℝ) (n : ℕ) :
    Complex.normSq (1 - ze θ ^ n) = 4 * Real.sin (Real.pi * n * θ) ^ 2 := by
  have h : ze θ ^ n = Complex.exp (((-(2 * Real.pi * n * θ) : ℝ) : ℂ) * Complex.I) := by
    rw [ze_eq, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h, normSq_one_sub_exp_I,
    show (-(2 * Real.pi * (n:ℝ) * θ)) / 2 = -(Real.pi * n * θ) from by ring, Real.sin_neg]
  ring

/-- Telescoping: `(∑_{j<M} Z^j) (1 - Z) = 1 - Z^M`. -/
private lemma geom_mul (M : ℕ) (Z : ℂ) :
    (∑ j ∈ Finset.range M, Z ^ j) * (1 - Z) = 1 - Z ^ M := by
  rw [show (1 : ℂ) - Z = -(Z - 1) from by ring, mul_neg, geom_sum_mul Z M]
  ring

/-- The norm square of the geometric sum telescopes. -/
private lemma normSq_geom (M : ℕ) (Z : ℂ) :
    Complex.normSq (∑ j ∈ Finset.range M, Z ^ j) * Complex.normSq (1 - Z)
      = Complex.normSq (1 - Z ^ M) := by
  rw [← Complex.normSq_mul, geom_mul]

/-- The fibre of `(j,k) ↦ j - k` over `n` inside the square `[0,M)²` has `M - |n|` elements. -/
private lemma fiber_card (M : ℕ) (n : ℤ) (hn : n.natAbs < M) :
    ((Finset.range M ×ˢ Finset.range M).filter
      (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = n)).card = M - n.natAbs := by
  rcases le_or_gt 0 n with hn0 | hn0
  · have he : n = (n.toNat : ℤ) := (Int.toNat_of_nonneg hn0).symm
    have hset : (Finset.range M ×ˢ Finset.range M).filter
        (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = n)
        = (Finset.range (M - n.toNat)).image (fun k => (k + n.toNat, k)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨p.2, by omega, Prod.ext (by omega) rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨⟨by omega, by omega⟩, by omega⟩
    have hcard : (Finset.range (M - n.toNat)).card = M - n.natAbs := by
      rw [Finset.card_range]
      have : n.toNat = n.natAbs := Int.toNat_of_nonneg hn0 ▸ rfl
      omega
    rw [hset, Finset.card_image_of_injective _ (fun a b h => by simpa using congrArg Prod.snd h),
      hcard]
  · have he : n = -((n.natAbs : ℕ) : ℤ) := by
      rcases Int.natAbs_eq n with h | h
      · omega
      · exact h
    have hset : (Finset.range M ×ˢ Finset.range M).filter
        (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = n)
        = (Finset.range (M - n.natAbs)).image (fun k => (k, k + n.natAbs)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨p.1, by omega, Prod.ext rfl (by omega)⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨⟨by omega, by omega⟩, by omega⟩
    rw [hset, Finset.card_image_of_injective _ (fun a b h => by simpa using congrArg Prod.fst h),
      Finset.card_range]

/-- `((M - n.natAbs : ℕ) : ℝ) = M - |n|` when `n.natAbs ≤ M`. -/
private lemma natCast_sub_natAbs (M : ℕ) (n : ℤ) (hn : n.natAbs ≤ M) :
    ((M - n.natAbs : ℕ) : ℝ) = (M : ℝ) - |(n : ℝ)| := by
  rw [Nat.cast_sub hn,
    show ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| from by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]]

/-- Casting the tent coefficient to `ℂ`. -/
private lemma ofReal_tent (N : ℕ) (n : ℤ) (hn : n.natAbs ≤ N+1) :
    (((N+1 - n.natAbs : ℕ) : ℂ)) = ((((N:ℝ)+1) - |(n:ℝ)| : ℝ) : ℂ) := by
  rw [← Complex.ofReal_natCast, natCast_sub_natAbs (N+1) n hn]
  push_cast
  ring

/-- **The master identity.**  `fejerPoly N θ` is `M⁻²` times the squared modulus of the
geometric sum `∑_{j<M} exp (-2πijθ)`, where `M = N+1`. -/
private lemma fejerPoly_eq_normSq (N : ℕ) (θ : ℝ) :
    fejerPoly N θ = (((((N:ℝ)+1)^2)⁻¹
      * Complex.normSq (∑ j ∈ Finset.range (N+1), ze θ ^ j) : ℝ) : ℂ) := by
  have hstep1 : fejerPoly N θ
      = ∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), (fejerCoeff N n : ℂ) * ze θ ^ n := by
    unfold fejerPoly
    exact Finset.sum_congr rfl (fun n _ => by rw [ze_pow_int])
  have hstep2 : ∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), (fejerCoeff N n : ℂ) * ze θ ^ n
      = ((((N:ℝ)+1)^2)⁻¹ : ℂ) * ∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
          ((((N:ℝ)+1) - |(n:ℝ)| : ℝ) : ℂ) * ze θ ^ n := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [fejerCoeff_eq hn]
    push_cast
    ring_nf
  have hstep3 : ∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
        ((((N:ℝ)+1) - |(n:ℝ)| : ℝ) : ℂ) * ze θ ^ n
      = ((Complex.normSq (∑ j ∈ Finset.range (N+1), ze θ ^ j) : ℝ) : ℂ) := by
    have hmem : ∀ p ∈ Finset.range (N+1) ×ˢ Finset.range (N+1),
        ((p.1 : ℤ) - (p.2 : ℤ)) ∈ Finset.Icc (-(N:ℤ)) (N:ℤ) := by
      intro p hp
      simp only [Finset.mem_product, Finset.mem_range] at hp
      rw [Finset.mem_Icc]
      omega
    have hfiber := Finset.sum_fiberwise_of_maps_to
      (s := Finset.range (N+1) ×ˢ Finset.range (N+1))
      (t := Finset.Icc (-(N:ℤ)) (N:ℤ)) (g := fun p : ℕ × ℕ => (p.1:ℤ) - (p.2:ℤ))
      (f := fun p : ℕ × ℕ => ze θ ^ ((p.1:ℤ) - (p.2:ℤ))) hmem
    have hinner : ∀ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
        (∑ p ∈ (Finset.range (N+1) ×ˢ Finset.range (N+1)).filter
            (fun p : ℕ × ℕ => (p.1:ℤ) - (p.2:ℤ) = n), ze θ ^ ((p.1:ℤ) - (p.2:ℤ)))
          = ((((N:ℝ)+1) - |(n:ℝ)| : ℝ) : ℂ) * ze θ ^ n := by
      intro n hn
      have hnlt : n.natAbs < N + 1 := by
        rw [Finset.mem_Icc] at hn
        omega
      rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.mp hp).2]),
        Finset.sum_const, nsmul_eq_mul, fiber_card (N+1) n hnlt,
        ofReal_tent N n (by omega)]
    have hprod : (∑ p ∈ Finset.range (N+1) ×ˢ Finset.range (N+1),
          ze θ ^ ((p.1:ℤ) - (p.2:ℤ)))
        = (∑ j ∈ Finset.range (N+1), ze θ ^ j)
          * (starRingEnd ℂ) (∑ j ∈ Finset.range (N+1), ze θ ^ j) := by
      rw [Finset.sum_product, map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
      rw [zpow_sub₀ (ze_ne_zero θ), zpow_natCast, zpow_natCast, div_eq_mul_inv, ← inv_pow,
        Complex.inv_eq_conj (norm_ze θ), ← map_pow]
    have hnormSq : (∑ j ∈ Finset.range (N+1), ze θ ^ j)
          * (starRingEnd ℂ) (∑ j ∈ Finset.range (N+1), ze θ ^ j)
        = ((Complex.normSq (∑ j ∈ Finset.range (N+1), ze θ ^ j) : ℝ) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]
      ring
    calc ∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), ((((N:ℝ)+1) - |(n:ℝ)| : ℝ) : ℂ) * ze θ ^ n
        = ∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
            ∑ p ∈ (Finset.range (N+1) ×ˢ Finset.range (N+1)).filter
              (fun p : ℕ × ℕ => (p.1:ℤ) - (p.2:ℤ) = n),
              ze θ ^ ((p.1:ℤ) - (p.2:ℤ)) := (Finset.sum_congr rfl hinner).symm
      _ = ∑ p ∈ Finset.range (N+1) ×ˢ Finset.range (N+1),
            ze θ ^ ((p.1:ℤ) - (p.2:ℤ)) := hfiber
      _ = (∑ j ∈ Finset.range (N+1), ze θ ^ j)
            * (starRingEnd ℂ) (∑ j ∈ Finset.range (N+1), ze θ ^ j) := hprod
      _ = ((Complex.normSq (∑ j ∈ Finset.range (N+1), ze θ ^ j) : ℝ) : ℂ) := hnormSq
  rw [hstep1, hstep2, hstep3]
  push_cast
  ring

theorem fejer_poly_eq_win (N : ℕ) (θ : ℝ) :
    Work.Analysis.Fourier.fejerPoly N θ = (Work.Analysis.Fourier.fejerWin N θ : ℂ) := by
  rcases eq_or_ne (Real.sin (Real.pi * θ)) 0 with hsin | hsin
  · -- `sin (πθ) = 0`: then `θ` is an integer and `Z = 1`, so the sum is `M`.
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hsin
    have hθ : θ = (k : ℝ) := by
      have h1 : (k:ℝ) * Real.pi = θ * Real.pi := by rw [hk, mul_comm]
      exact (mul_right_cancel₀ Real.pi_ne_zero h1).symm
    have hZ1 : ze θ = 1 := by
      rw [ze_eq, hθ,
        show ((-(2 * Real.pi * (k:ℝ)) : ℝ) : ℂ) * Complex.I
            = ((-k : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I) from by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I (-k)
    have hsum : ∑ j ∈ Finset.range (N+1), ze θ ^ j = ((N+1 : ℕ) : ℂ) := by
      simp [hZ1]
    have hnsq : Complex.normSq (∑ j ∈ Finset.range (N+1), ze θ ^ j) = ((N:ℝ)+1)^2 := by
      rw [hsum, Complex.normSq_natCast]
      push_cast
      ring
    rw [fejerPoly_eq_normSq N θ, hnsq, fejerWin, if_pos hsin,
      inv_mul_cancel₀ (by positivity : (((N:ℝ)+1)^2) ≠ 0)]
  · -- `sin (πθ) ≠ 0`
    have hwin : fejerWin N θ
        = (Real.sin (Real.pi * ((N:ℝ)+1) * θ)
            / (((N:ℝ)+1) * Real.sin (Real.pi * θ)))^2 := by
      unfold fejerWin
      rw [if_neg hsin]
    have hS : Complex.normSq (∑ j ∈ Finset.range (N+1), ze θ ^ j)
        = (Real.sin (Real.pi * ((N:ℝ)+1) * θ))^2 / (Real.sin (Real.pi * θ))^2 := by
      have h1 := normSq_one_sub_ze_pow θ 1
      have h2 := normSq_one_sub_ze_pow θ (N+1)
      have hg := normSq_geom (N+1) (ze θ)
      simp only [pow_one] at h1
      rw [show Real.pi * ((1:ℕ) : ℝ) * θ = Real.pi * θ from by ring] at h1
      rw [h1, h2] at hg
      have hcast : Real.pi * ((N+1 : ℕ) : ℝ) * θ = Real.pi * ((N:ℝ)+1) * θ := by
        push_cast; ring
      rw [hcast] at hg
      rw [eq_div_iff (pow_ne_zero 2 hsin)]
      linarith [hg]
    rw [fejerPoly_eq_normSq N θ, hwin, hS]
    congr 1
    have hMne : ((N:ℝ)+1) ≠ 0 := by positivity
    field_simp

end
end Work.Analysis.Fourier

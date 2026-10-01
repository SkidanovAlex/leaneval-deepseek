import Mathlib
import Submission.Work.LinnikAreas.Density4.Defs
import Submission.Work.LinnikAreas.Density4.support_log_div
import Submission.Work.LinnikAreas.Density4.weighted_cauchy_schwarz
import Submission.Work.LinnikAreas.Density4.hb12_arith

namespace Work.LinnikAreas.Density4

open scoped BigOperators

/-! ## Auxiliary complex / Dirichlet-character identities for HB Lemma 12.1 -/

/-- Conjugation of a character value of a unit is its inverse: `conj (χ a) = (χ a)⁻¹` for a unit
`a` (the values at units are roots of unity). -/
lemma conj_unit_char_eq_inv {q : ℕ} (χ : DirichletCharacter ℂ q) {a : ZMod q} (ha : IsUnit a) :
    (starRingEnd ℂ) (χ a) = (χ a)⁻¹ := by
  have hnorm : ‖χ a‖ = 1 := DirichletCharacter.unit_norm_eq_one χ ha.unit
  have h1 : χ a * (starRingEnd ℂ) (χ a) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; norm_num
  exact eq_inv_of_mul_eq_one_right h1

/-- `χ a · conj (ψ a) = (χ · ψ⁻¹) a` for Dirichlet characters (trivially zero on non-units,
and conjugation is inversion on units). -/
lemma conj_char_mul {q : ℕ} (χ ψ : DirichletCharacter ℂ q) (a : ZMod q) :
    χ a * (starRingEnd ℂ) (ψ a) = (χ * ψ⁻¹) a := by
  by_cases ha : IsUnit a
  · rw [MulChar.mul_apply, MulChar.inv_apply_eq_inv', conj_unit_char_eq_inv ψ ha]
  · rw [MulChar.map_nonunit χ ha, MulChar.map_nonunit ψ ha,
      MulChar.map_nonunit (χ * ψ⁻¹) ha]
    simp

/-- Conjugation and the complex power of a natural number: `conj (n^z) = n^(conj z)`. -/
lemma cpow_conj_natCast (n : ℕ) (z : ℂ) :
    (starRingEnd ℂ) ((n:ℂ)^z) = (n:ℂ)^((starRingEnd ℂ) z) := by
  have hx : (n:ℂ).arg ≠ Real.pi := by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
  have h := Complex.cpow_conj (n:ℂ) ((starRingEnd ℂ) z) hx
  rw [Complex.conj_conj] at h
  rw [Complex.conj_natCast] at h
  have h2 := congrArg (starRingEnd ℂ) h
  simp only [Complex.conj_conj] at h2
  exact h2

/-- `n^z · conj (n^w) = n^(z + conj w)` for a positive natural `n`. -/
lemma cpow_mul_conj' {n : ℕ} (hn : n ≠ 0) (z w : ℂ) :
    (n:ℂ)^z * (starRingEnd ℂ) ((n:ℂ)^w) = (n:ℂ)^(z + (starRingEnd ℂ) w) := by
  rw [cpow_conj_natCast]
  rw [← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]

/-- The phase identity `(χ a · n^{-is}) · conj(ψ a · n^{-it}) = (χ ψ⁻¹) a · n^{-i(s-t)}`. -/
lemma char_phase_mul_conj {q : ℕ} (χ ψ : DirichletCharacter ℂ q) (s t : ℝ) (n : ℕ)
    (hn : n ≠ 0) :
    (χ (n:ZMod q) * (n:ℂ)^(-(s:ℂ)*Complex.I))
        * (starRingEnd ℂ) (ψ (n:ZMod q) * (n:ℂ)^(-(t:ℂ)*Complex.I))
      = (χ * ψ⁻¹) (n:ZMod q) * (n:ℂ)^(-((s-t):ℂ)*Complex.I) := by
  rw [map_mul]
  rw [show (χ (n:ZMod q) * (n:ℂ)^(-(s:ℂ)*Complex.I))
          * ((starRingEnd ℂ) (ψ (n:ZMod q)) * (starRingEnd ℂ) ((n:ℂ)^(-(t:ℂ)*Complex.I)))
        = (χ (n:ZMod q) * (starRingEnd ℂ) (ψ (n:ZMod q)))
          * ((n:ℂ)^(-(s:ℂ)*Complex.I) * (starRingEnd ℂ) ((n:ℂ)^(-(t:ℂ)*Complex.I))) by ring]
  rw [conj_char_mul, cpow_mul_conj' hn]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_neg]
  ring_nf

/-- Factorisation of the `K`-summand: for `n ≠ 0`, the `(β,t,χ)` summand is the `(β,0,1)`
"weight" summand times the real part of the phase `χ a · n^{-it}`. -/
lemma Kgen_summand_re {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (β t : ℝ) (n : ℕ)
    (hn : n ≠ 0) :
    (χ (n:ZMod q) * (n:ℂ)^(-(β:ℂ) - (t:ℂ)*Complex.I)).re
      = ((1 : DirichletCharacter ℂ q) (n:ZMod q) * (n:ℂ)^(-(β:ℂ))).re
        * (χ (n:ZMod q) * (n:ℂ)^(-(t:ℂ)*Complex.I)).re := by
  have hn' : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hsplit : (n:ℂ)^(-(β:ℂ) - (t:ℂ)*Complex.I)
      = (n:ℂ)^(-(β:ℂ)) * (n:ℂ)^(-(t:ℂ)*Complex.I) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hn', neg_mul]
  rw [hsplit]
  have himP : ((n:ℂ)^(-(β:ℂ))).im = 0 := by
    rw [← Complex.ofReal_neg, Complex.cpow_ofReal_im, Complex.natCast_arg]; simp
  by_cases ha : IsUnit (n : ZMod q)
  · rw [MulChar.one_apply ha, one_mul]
    rw [show χ (n:ZMod q) * ((n:ℂ)^(-(β:ℂ)) * (n:ℂ)^(-(t:ℂ)*Complex.I))
        = (n:ℂ)^(-(β:ℂ)) * (χ (n:ZMod q) * (n:ℂ)^(-(t:ℂ)*Complex.I)) by ring]
    rw [Complex.mul_re, himP]
    ring
  · rw [MulChar.map_nonunit χ ha, MulChar.map_nonunit (1:DirichletCharacter ℂ q) ha]
    simp

/-- The full-`K`-summand factorisation, valid for all `n` (for `n = 0` both sides vanish). -/
lemma Kgen_summand_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (β t : ℝ) (f : ℝ → ℝ)
    (L : ℝ) (n : ℕ) :
    (ArithmeticFunction.vonMangoldt n : ℝ)
        * (χ (n:ZMod q) * (n:ℂ)^(-(β:ℂ) - (t:ℂ)*Complex.I)).re * f (Real.log n / L)
      = ((ArithmeticFunction.vonMangoldt n : ℝ)
          * (((1 : DirichletCharacter ℂ q) (n:ZMod q)) * (n:ℂ)^(-(β:ℂ))).re
          * f (Real.log n / L))
        * (χ (n:ZMod q) * (n:ℂ)^(-(t:ℂ)*Complex.I)).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [Kgen_summand_re χ β t n hn]; ring

/-- Expansion of the squared modulus of a finite sum of complex numbers. -/
lemma normSq_sum {N : ℕ} (z : Fin N → ℂ) :
    ‖∑ j, z j‖ ^ 2 = ∑ j, ∑ k, (z j * (starRingEnd ℂ) (z k)).re := by
  have h1 : ‖∑ j, z j‖ ^ 2 = ((starRingEnd ℂ) (∑ j, z j) * (∑ j, z j)).re := by
    have h := Complex.normSq_eq_conj_mul_self (z := ∑ j, z j)
    rw [Complex.normSq_eq_norm_sq] at h
    rw [← h, Complex.ofReal_re]
  rw [h1, map_sum, Finset.sum_mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Complex.mul_re, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-- The `(β,0,1)` weight `Re (1(a) · n^{-β})` is non-negative. -/
lemma one_mul_cpow_re_nonneg {q : ℕ} [NeZero q] (β : ℝ) (n : ℕ) :
    0 ≤ (((1 : DirichletCharacter ℂ q)) (n:ZMod q) * (n:ℂ)^(-(β:ℂ))).re := by
  by_cases ha : IsUnit (n : ZMod q)
  · rw [MulChar.one_apply ha, one_mul, ← Complex.ofReal_neg, Complex.cpow_ofReal_re,
      Complex.natCast_arg]
    simp
    positivity
  · rw [MulChar.map_nonunit (1:DirichletCharacter ℂ q) ha]
    simp

/-- Pointwise identity behind the `Σ₂` bound: for each `n`, the `(β,0,1)` weight times the
squared modulus of the phase-sum equals the double sum of the `K`-summands at the conjugate
characters `χ_j χ_k⁻¹` and shifts `γ_j - γ_k`. -/
lemma S2_summand_eq {q : ℕ} [NeZero q] {N : ℕ} (χ : Fin N → DirichletCharacter ℂ q)
    (γ : Fin N → ℝ) (β : ℝ) (f : ℝ → ℝ) (L : ℝ) (n : ℕ) :
    ((ArithmeticFunction.vonMangoldt n : ℝ)
        * (((1 : DirichletCharacter ℂ q) (n:ZMod q)) * (n:ℂ)^(-(β:ℂ))).re
        * f (Real.log n / L))
      * ‖∑ j, (χ j (n:ZMod q) * (n:ℂ)^(-((γ j:ℝ):ℂ)*Complex.I))‖ ^ 2
      = ∑ j, ∑ k, (ArithmeticFunction.vonMangoldt n : ℝ)
          * (((χ j * (χ k)⁻¹) (n:ZMod q))
              * (n:ℂ)^(-(β:ℂ) - ((γ j - γ k : ℝ):ℂ)*Complex.I)).re
          * f (Real.log n / L) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [normSq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Kgen_summand_eq (χ j * (χ k)⁻¹) β (γ j - γ k) f L n, Complex.ofReal_sub,
      ← char_phase_mul_conj (χ j) (χ k) (γ j) (γ k) n hn]

end Work.LinnikAreas.Density4

namespace Work.LinnikAreas.Density4

open scoped BigOperators

/-- **HB §12: the analytic core of the new zero density estimate (Lemma 12.1).**  Let `f` be a
non-negative test function supported in `[0,x₀]` with Laplace transform
`Lapl x₀ f z = ∫_0^{x₀} e^{-zt}f(t)dt`, let the `N` characters `χ_j` have zeros `β₁ + iγ_j` where
`β₁ = 1 - λ₁/𝓛`, and suppose the `K`-bounds of HB Lemmas 5.2/5.3 hold for
`Kgen q L β t f χ = Σ_n Λ(n) Re(χ(n)n^{-β-it}) f(log n/𝓛)`, namely
`K(β₁+iγ_j,χ_j) ≤ -𝓛F(λ_j-λ₁) + f(0)(1/6+ε)𝓛`,
`K(β₁,χ₀) ≤ 𝓛F(-λ₁) + f(0)ε𝓛` (principal character `1`),
and `K(β₁+i(γ_j-γ_k), χ_jχ̄_k) ≤ f(0)(1/6+ε)𝓛` for `j ≠ k`, with `λ_j ≤ λ` and `F` decreasing.
Then, provided `f(0)(1/6+ε) < F(λ-λ₁)` and
`f(0)(1/6+ε)(F(-λ₁)+f(0)ε) < (F(λ-λ₁)-f(0)(1/6+ε))²`,
`N ≤ (F(-λ₁)+f(0)ε)(F(-λ₁)-f(0)/6) / ((F(λ-λ₁)-f(0)(1/6+ε))² - f(0)(1/6+ε)(F(-λ₁)+f(0)ε))`,
which at `ε = 0` is exactly HB (12.1).  Proof: multiply the first bound by `𝓛N`, note
`-Σ_j K_j ≤ Σ_n Λ(n)n^{-β₁}f(log n/𝓛)|Σ_j χ_j(n)n^{-iγ_j}|`, apply Cauchy–Schwarz with
`Σ₁ = K(β₁,χ₀)` and `Σ₂ = Σ_{j,k} K(β₁+iγ_j-iγ_k,χ_jχ̄_k) ≤ N(𝓛F(-λ₁)+f(0)ε𝓛) + (N²-N)f(0)(1/6+ε)𝓛`
(the `N` diagonal terms are the principal-character bound, the `j ≠ k` terms the third bound), and
divide by `𝓛²N`.

**Corrections after review** (the reviewers found both): the off-diagonal hypothesis is at the
*conjugate* character `χ_j χ_k⁻¹` (that is what `Σ₂` contains), and the `K`-sums are taken at the
shifted point `β₁ = 1 - λ₁/𝓛`, so that the Laplace arguments are `λ_j - λ₁` and `-λ₁`. -/
theorem hb_lemma12_1 {q : ℕ} [NeZero q] (L : ℝ) (hL : 0 < L) {x₀ : ℝ} (hx₀ : 0 < x₀)
    {f : ℝ → ℝ} (hfnn : ∀ t, 0 ≤ f t) (hfs : ∀ t, x₀ ≤ t → f t = 0) (hf0 : 0 < f 0)
    {ε : ℝ} (hε : 0 ≤ ε) {lam₁ lam : ℝ} {N : ℕ} (hN : 0 < N)
    {χ : Fin N → DirichletCharacter ℂ q} {γ lamv : Fin N → ℝ}
    (hK1 : ∀ j, Work.LinnikAreas.Density4.Kgen q L (1 - lam₁/L) (γ j) f (χ j)
        ≤ -(L * Work.LinnikAreas.Density4.Lapl x₀ f (lamv j - lam₁)) + f 0 * (1/6 + ε) * L)
    (hK2 : Work.LinnikAreas.Density4.Kgen q L (1 - lam₁/L) 0 f 1
        ≤ L * Work.LinnikAreas.Density4.Lapl x₀ f (-lam₁) + f 0 * ε * L)
    (hK3 : ∀ j k, j ≠ k → Work.LinnikAreas.Density4.Kgen q L (1 - lam₁/L) (γ j - γ k) f
        (χ j * (χ k)⁻¹) ≤ f 0 * (1/6 + ε) * L)
    (hmono : ∀ j, lamv j ≤ lam)
    (hFanti : ∀ a b : ℝ, a ≤ b →
        Work.LinnikAreas.Density4.Lapl x₀ f b ≤ Work.LinnikAreas.Density4.Lapl x₀ f a)
    (hA : 0 < Work.LinnikAreas.Density4.Lapl x₀ f (-lam₁))
    (hpos : f 0 * (1/6 + ε) < Work.LinnikAreas.Density4.Lapl x₀ f (lam - lam₁))
    (hden : f 0 * (1/6 + ε) * (Work.LinnikAreas.Density4.Lapl x₀ f (-lam₁) + f 0 * ε)
        < (Work.LinnikAreas.Density4.Lapl x₀ f (lam - lam₁) - f 0 * (1/6 + ε))^2) :
    (N : ℝ) ≤ (Work.LinnikAreas.Density4.Lapl x₀ f (-lam₁) + f 0*ε) *
        (Work.LinnikAreas.Density4.Lapl x₀ f (-lam₁) - f 0/6) /
        ((Work.LinnikAreas.Density4.Lapl x₀ f (lam - lam₁) - f 0*(1/6+ε))^2
          - f 0*(1/6+ε)*(Work.LinnikAreas.Density4.Lapl x₀ f (-lam₁) + f 0*ε)) := by
  classical
  -- ### The support cut-off `M > exp (x₀ L)`.
  set M : ℕ := Nat.ceil (Real.exp (x₀ * L)) + 1 with hMdef
  have hMgt : Real.exp (x₀ * L) < (M : ℝ) := by
    rw [hMdef]; push_cast
    have hle : Real.exp (x₀ * L) ≤ (Nat.ceil (Real.exp (x₀ * L)) : ℝ) := Nat.le_ceil _
    linarith
  have hsupp : ∀ n, n ∉ Finset.range M → f (Real.log n / L) = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    exact support_log_div hL hx₀ hfs hMgt hn
  -- ### The weight `u`, the phases `Z`, and the two sums `S1, S2`.
  set u : ℕ → ℝ := (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)
      * (((1 : DirichletCharacter ℂ q) (n:ZMod q)) * (n:ℂ)^(-((1 - lam₁/L : ℝ) : ℂ))).re
      * f (Real.log n / L)) with hudef
  set Z : Fin N → ℕ → ℂ := (fun j n => χ j (n:ZMod q)
      * (n:ℂ)^(-((γ j : ℝ) : ℂ)*Complex.I)) with hZdef
  have hu_nonneg : ∀ n, 0 ≤ u n := by
    intro n
    rw [hudef]
    exact mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (one_mul_cpow_re_nonneg _ n)) (hfnn _)
  set S1 : ℝ := ∑ n ∈ Finset.range M, u n with hS1def
  set S2 : ℝ := ∑ n ∈ Finset.range M, u n * ‖∑ j, Z j n‖ ^ 2 with hS2def
  set A : ℝ := Lapl x₀ f (lam - lam₁) - f 0 * (1/6 + ε) with hAdef
  set B : ℝ := Lapl x₀ f (-lam₁) + f 0 * ε with hBdef
  set C : ℝ := f 0 * (1/6 + ε) with hCdef
  -- ### The three `K`-sum identities.
  have hK1eq : ∀ j, Kgen q L (1 - lam₁/L) (γ j) f (χ j)
      = ∑ n ∈ Finset.range M, u n * (Z j n).re := by
    intro j
    unfold Kgen
    rw [tsum_eq_sum (s := Finset.range M) (fun n hn => by rw [hsupp n hn, mul_zero])]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [Kgen_summand_eq (χ j) (1 - lam₁/L) (γ j) f L n, hudef, hZdef]
  have hK2eq : Kgen q L (1 - lam₁/L) 0 f 1 = S1 := by
    rw [hS1def]
    unfold Kgen
    rw [tsum_eq_sum (s := Finset.range M) (fun n hn => by rw [hsupp n hn, mul_zero])]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [hudef]; simp
  have hK1eq' : (∑ j, Kgen q L (1 - lam₁/L) (γ j) f (χ j))
      = ∑ n ∈ Finset.range M, u n * (∑ j, Z j n).re := by
    have h1 : (∑ j, Kgen q L (1 - lam₁/L) (γ j) f (χ j))
        = ∑ j, ∑ n ∈ Finset.range M, u n * (Z j n).re :=
      Finset.sum_congr rfl (fun j _ => hK1eq j)
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [Complex.re_sum, Finset.mul_sum]
  have hK3eq : (∑ j, ∑ k, Kgen q L (1 - lam₁/L) (γ j - γ k) f (χ j * (χ k)⁻¹)) = S2 := by
    rw [hS2def]
    have h1 : ∀ j k, Kgen q L (1 - lam₁/L) (γ j - γ k) f (χ j * (χ k)⁻¹)
        = ∑ n ∈ Finset.range M, (ArithmeticFunction.vonMangoldt n : ℝ)
            * (((χ j * (χ k)⁻¹) (n:ZMod q))
                * (n:ℂ)^(-((1 - lam₁/L : ℝ) : ℂ) - ((γ j - γ k : ℝ) : ℂ)*Complex.I)).re
            * f (Real.log n / L) := by
      intro j k
      unfold Kgen
      rw [tsum_eq_sum (s := Finset.range M) (fun n hn => by rw [hsupp n hn, mul_zero])]
    rw [Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => h1 j k))]
    rw [Finset.sum_congr rfl (fun j _ => Finset.sum_comm), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [← S2_summand_eq χ γ (1 - lam₁/L) f L n, hudef, hZdef]
  -- ### Summing the first hypothesis.
  have hApos : (0:ℝ) < A := by
    rw [hAdef]; linarith [hpos]
  have hK1sum : (N:ℝ) * L * A ≤ -(∑ j, Kgen q L (1 - lam₁/L) (γ j) f (χ j)) := by
    have h1 : ∑ j, Kgen q L (1 - lam₁/L) (γ j) f (χ j) ≤ -((N:ℝ) * L * A) := by
      calc ∑ j, Kgen q L (1 - lam₁/L) (γ j) f (χ j)
          ≤ ∑ j, (-(L * Lapl x₀ f (lamv j - lam₁)) + f 0 * (1/6+ε) * L) :=
            Finset.sum_le_sum (fun j _ => hK1 j)
        _ = -L * (∑ j, Lapl x₀ f (lamv j - lam₁)) + (N:ℝ) * (f 0 * (1/6+ε)*L) := by
            rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum,
              Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; ring
        _ ≤ -L * ((N:ℝ) * Lapl x₀ f (lam - lam₁)) + (N:ℝ) * (f 0 * (1/6+ε)*L) := by
            have hm : (N:ℝ) * Lapl x₀ f (lam - lam₁)
                ≤ ∑ j, Lapl x₀ f (lamv j - lam₁) := by
              have hfj : ∀ j, Lapl x₀ f (lam - lam₁) ≤ Lapl x₀ f (lamv j - lam₁) :=
                fun j => hFanti _ _ (by linarith [hmono j])
              calc (N:ℝ) * Lapl x₀ f (lam - lam₁) = ∑ j, Lapl x₀ f (lam - lam₁) := by
                    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
                _ ≤ ∑ j, Lapl x₀ f (lamv j - lam₁) := Finset.sum_le_sum (fun j _ => hfj j)
            nlinarith [hm, hL]
        _ = -((N:ℝ) * L * A) := by rw [hAdef]; ring
    linarith [h1]
  -- ### The Cauchy–Schwarz chain.
  have hneg : -(∑ j, Kgen q L (1 - lam₁/L) (γ j) f (χ j))
      ≤ ∑ n ∈ Finset.range M, u n * ‖∑ j, Z j n‖ := by
    rw [hK1eq']
    calc -(∑ n ∈ Finset.range M, u n * (∑ j, Z j n).re)
        ≤ |∑ n ∈ Finset.range M, u n * (∑ j, Z j n).re| := neg_le_abs _
      _ ≤ ∑ n ∈ Finset.range M, |u n * (∑ j, Z j n).re| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.range M, u n * ‖∑ j, Z j n‖ := by
            refine Finset.sum_le_sum (fun n _ => ?_)
            rw [abs_mul, abs_of_nonneg (hu_nonneg n)]
            exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (hu_nonneg n)
  have hCS : (∑ n ∈ Finset.range M, u n * ‖∑ j, Z j n‖)^2 ≤ S1 * S2 := by
    rw [hS1def, hS2def]
    exact weighted_cauchy_schwarz _ u hu_nonneg (fun n => ∑ j, Z j n)
  -- ### Bounds on `S1` and `S2`.
  have hS1nn : 0 ≤ S1 := by
    rw [hS1def]; exact Finset.sum_nonneg (fun n _ => hu_nonneg n)
  have hS2nn : 0 ≤ S2 := by
    rw [hS2def]
    exact Finset.sum_nonneg (fun n _ => mul_nonneg (hu_nonneg n) (sq_nonneg _))
  have hS1ub : S1 ≤ L * B := by
    rw [hBdef, ← hK2eq]
    nlinarith [hK2]
  have hS2ub : S2 ≤ (N:ℝ) * S1 + ((N:ℝ)^2 - (N:ℝ)) * C * L := by
    rw [← hK3eq]
    have hdiag : ∀ j, Kgen q L (1 - lam₁/L) (γ j - γ j) f (χ j * (χ j)⁻¹) = S1 := by
      intro j
      rw [sub_self, mul_inv_cancel]
      exact hK2eq
    have hsplit : (∑ j, ∑ k, Kgen q L (1 - lam₁/L) (γ j - γ k) f (χ j * (χ k)⁻¹))
        = (∑ j, Kgen q L (1 - lam₁/L) (γ j - γ j) f (χ j * (χ j)⁻¹))
          + ∑ j, ∑ k ∈ Finset.univ.erase j,
              Kgen q L (1 - lam₁/L) (γ j - γ k) f (χ j * (χ k)⁻¹) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      exact (Finset.add_sum_erase Finset.univ
        (fun k => Kgen q L (1 - lam₁/L) (γ j - γ k) f (χ j * (χ k)⁻¹))
        (Finset.mem_univ j)).symm
    have hd : (∑ j, Kgen q L (1 - lam₁/L) (γ j - γ j) f (χ j * (χ j)⁻¹)) = (N:ℝ) * S1 := by
      rw [Finset.sum_congr rfl (fun j _ => hdiag j), Finset.sum_const, Finset.card_fin,
        nsmul_eq_mul]
    have hoff : (∑ j, ∑ k ∈ Finset.univ.erase j,
          Kgen q L (1 - lam₁/L) (γ j - γ k) f (χ j * (χ k)⁻¹))
        ≤ ((N:ℝ)^2 - (N:ℝ)) * C * L := by
      have hb : ∀ j, (∑ k ∈ Finset.univ.erase j,
              Kgen q L (1 - lam₁/L) (γ j - γ k) f (χ j * (χ k)⁻¹))
          ≤ ((N:ℝ) - 1) * (f 0 * (1/6+ε) * L) := by
        intro j
        have hcard : ((Finset.univ.erase j).card : ℝ) = (N:ℝ) - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_fin,
            Nat.cast_sub (by omega : 1 ≤ N)]
          norm_num
        calc (∑ k ∈ Finset.univ.erase j,
                Kgen q L (1 - lam₁/L) (γ j - γ k) f (χ j * (χ k)⁻¹))
            ≤ ∑ k ∈ Finset.univ.erase j, f 0 * (1/6+ε) * L := by
              refine Finset.sum_le_sum (fun k hk => ?_)
              exact hK3 j k (by
                intro hjk; rw [← hjk] at hk
                exact Finset.notMem_erase j Finset.univ hk)
          _ = ((Finset.univ.erase j).card : ℝ) * (f 0 * (1/6+ε) * L) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ = ((N:ℝ) - 1) * (f 0 * (1/6+ε) * L) := by rw [hcard]
      calc (∑ j, ∑ k ∈ Finset.univ.erase j,
              Kgen q L (1 - lam₁/L) (γ j - γ k) f (χ j * (χ k)⁻¹))
          ≤ ∑ j, ((N:ℝ) - 1) * (f 0 * (1/6+ε) * L) := Finset.sum_le_sum (fun j _ => hb j)
        _ = ((N:ℝ)^2 - (N:ℝ)) * C * L := by
            rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, hCdef]; ring
    rw [hsplit, hd]
    linarith [hoff]
  -- ### The arithmetic closing.
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    have := mul_nonneg hf0.le hε
    linarith [hA]
  have hNLA : (0:ℝ) ≤ (N:ℝ) * L * A := by positivity
  have hCS2 : ((N:ℝ) * L * A)^2 ≤ S1 * S2 := by
    have h2 := le_trans hK1sum hneg
    nlinarith [hNLA, h2, hCS]
  have hden' : B * C < A ^ 2 := by
    rw [hAdef, hBdef, hCdef]
    rw [mul_comm (Lapl x₀ f (-lam₁) + f 0*ε)]
    exact hden
  have hmain := hb12_arith (A := A) (B := B) (C := C) (S1 := S1) (S2 := S2)
    hN hL hS1nn hS2nn hBnn hCS2 hS1ub hS2ub hden'
  have heq : B * (B - C) / (A^2 - B*C)
      = (Lapl x₀ f (-lam₁) + f 0*ε) * (Lapl x₀ f (-lam₁) - f 0/6) /
        ((Lapl x₀ f (lam - lam₁) - f 0*(1/6+ε))^2
          - f 0*(1/6+ε)*(Lapl x₀ f (-lam₁) + f 0*ε)) := by
    rw [hAdef, hBdef, hCdef]; ring
  rw [heq] at hmain
  exact hmain

end Work.LinnikAreas.Density4

import Submission.ZagierHoffmanProof.Step2Complete
import Submission.ZagierHoffmanProof.AmbField

/-!
# (E3): the rationality of the `f`-row of the rigid analytic trivialisation

Dac's Theorem (linear independence) (§3.3) ends with the statement that the `f`-row
`f_{t;Q} = tmF … t` of the rigid analytic trivialisation evaluates at `θ` to an element of
`K = F_q(θ)`.  The paper derives this from Pap08 §4.1.6 (`L^σ = F_q(t)` for the fraction field `L`
of the Tate algebra), which in turn rests on the divisor theory of the Tate algebra.

This file gives an **elementary** proof, avoiding the divisor theory entirely, of the precise
statement needed:

> if `F ∈ T` (a restricted/super-entire power series), `Q ∈ K[t]` is a nonzero polynomial with
> `Q(θ) ≠ 0`, and `F^{(1)}·Q = F·Q^{(1)}`, then `F(θ) ∈ K`.

The proof is the "potential denominator" argument:

* `M := {H ∈ K[t] : ∃ G ∈ T, F·H = G·Q}` is an ideal of `K[t]`, and it is stable under the
  Frobenius twist `σ = frobTwist 1` because `σ(F)·Q = F·σ(Q)`.
* Hence `M = (b₀)` and `b₀ | σ(b₀)`; comparing `t`-degrees gives `σ(b₀) = c·b₀` with `c ∈ K^×`.
* The witness `G` of `b₀ ∈ M` satisfies `σ(G) = c·G`, so its coefficients satisfy `aₙ^q = c·aₙ`;
  writing `aₙ = a_{n₀}·dₙ` (with `n₀` the first nonzero index) gives `dₙ ∈ F_q` for all `n`, and
  `G ∈ T` (coefficients tending to `0`) forces `dₙ = 0` for `n ≫ 0`.
* Setting `b₁ := b₀/a_{n₀}` and `h := G/a_{n₀}` we get `σ(b₁) = b₁`, `σ(h) = h`, hence `b₁` and `h`
  have coefficients in `F_q`; and `F·b₁ = h·Q`.
* Evaluating at `θ` gives `F(θ)·b₁(θ) = h(θ)·Q(θ)` with `b₁(θ), h(θ), Q(θ) ∈ K` and
  `b₁(θ) ≠ 0` (as `θ` is transcendental over `F_q`), so `F(θ) ∈ K`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
open Polynomial PowerSeries Finset Filter
open scoped WithZero Topology Classical

namespace ZagierHoffmanPositiveChar

variable {F : Type*} [Field F] [Finite F]

/-! ## §1. Polynomials are entire -/

/-- A polynomial, viewed as a power series, is entire. -/
lemma GEntire.polynomial (p : Polynomial (Ambient F)) :
    GEntire (K := Ambient F) ((p : PowerSeries (Ambient F))) := by
  have h : ∀ n, p.natDegree < n → PowerSeries.coeff n ((p : PowerSeries (Ambient F))) = 0 :=
    fun n hn => Polynomial.coeff_coe p n ▸ Polynomial.coeff_eq_zero_of_natDegree_lt hn
  exact GEntire.of_support _ (p.natDegree + 1) fun n hn => h n (by omega)


/-! ## §2. The elementary half of `L^σ = F_q(t)` -/

/-- If a power series is fixed by the Frobenius twist then every coefficient is fixed by the
`q`-th power map. -/
lemma coeff_mem_ambF_of_frobTwist_one_eq {f : PowerSeries (Ambient F)}
    (h : frobTwist (R := Ambient F) (p := Nat.card F) 1 f = f) (n : ℕ) :
    f.coeff n ∈ ambF F := by
  rw [mem_ambF_iff]
  have h1 := congrArg (PowerSeries.coeff n) h
  rwa [frobTwist_coeff, pow_one] at h1

/-- **The elementary half of Pap08's `L^σ = F_q(t)`.**  A restricted (entire) power series fixed by
the Frobenius twist is a polynomial with `F_q`-coefficients. -/
lemma exists_polynomial_of_gEntire_of_frobTwist_one_eq {f : PowerSeries (Ambient F)}
    (hf : GEntire (K := Ambient F) f)
    (h : frobTwist (R := Ambient F) (p := Nat.card F) 1 f = f) :
    ∃ p : Polynomial F,
      ((p.map (ambCoeff F) : Polynomial (Ambient F)) : PowerSeries (Ambient F)) = f := by
  classical
  have hcoeff : ∀ n, f.coeff n ∈ (ambCoeff F).range := fun n =>
    eq_range_ambCoeff_of_mem_ambF F (coeff_mem_ambF_of_frobTwist_one_eq h n)
  have hfin : ∃ N, ∀ n, N ≤ n → f.coeff n = 0 := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hf 1 one_ne_zero)
    refine ⟨N, fun n hn => ?_⟩
    by_contra hne
    obtain ⟨c, hc⟩ := eq_range_ambCoeff_of_mem_ambF F (coeff_mem_ambF_of_frobTwist_one_eq h n)
    have hc0 : c ≠ 0 := fun h0 => hne (by rw [← hc, h0, map_zero])
    have hlt := hN n hn
    rw [← hc, v_ambCoeff F c hc0] at hlt
    exact lt_irrefl 1 hlt
  obtain ⟨N, hN⟩ := hfin
  have hp : ∀ n, (PowerSeries.trunc N f).coeff n ∈ (ambCoeff F).range := by
    intro n
    rw [PowerSeries.coeff_trunc]
    by_cases hn : n < N
    · rw [if_pos hn]; exact hcoeff n
    · rw [if_neg hn]; exact ⟨0, map_zero _⟩
  obtain ⟨p, hp'⟩ := (Polynomial.mem_map_range (ambCoeff F)).mpr hp
  have hp2 : (Polynomial.map (ambCoeff F) p : Polynomial (Ambient F)) = PowerSeries.trunc N f := hp'
  refine ⟨p, ?_⟩
  ext n
  rw [Polynomial.coeff_coe, hp2, PowerSeries.coeff_trunc]
  by_cases hn : n < N
  · rw [if_pos hn]
  · rw [if_neg hn]; exact (hN n (by omega)).symm

/-! ## §3. The potential-denominator ideal -/

/-- A polynomial is a nonzero power series iff it is a nonzero polynomial. -/
lemma polynomial_coe_powerSeries_ne_zero {p : Polynomial (Ambient F)} :
    ((p : PowerSeries (Ambient F))) ≠ 0 ↔ p ≠ 0 := by
  constructor
  · intro h hp; exact h (by rw [hp, Polynomial.coe_zero])
  · intro hp h
    refine hp ?_
    ext n
    have h3 := congrArg (PowerSeries.coeff n) h
    rw [Polynomial.coeff_coe] at h3
    simpa using h3

/-- `x ↦ x ^ q` is injective on the ambient field (it is the Frobenius of a field of
characteristic `p`, and `q` is a power of `p`). -/
lemma frobPowHom_injective (k : ℕ) :
    Function.Injective (frobPowHom (K := Ambient F) (q := Nat.card F) k) := by
  intro x y h
  haveI : FrobPow (Ambient F) (Nat.card F ^ k) :=
    FrobPow.pow (R := Ambient F) (q := Nat.card F) k
  simp only [frobPowHom_apply] at h
  have hsub : (x - y) ^ (Nat.card F ^ k) = 0 := by
    have h2 : (x - y) ^ (Nat.card F ^ k) + y ^ (Nat.card F ^ k) = x ^ (Nat.card F ^ k) := by
      rw [← FrobPow.add_pow (x - y) y, sub_add_cancel]
    rw [h] at h2
    rw [eq_sub_of_add_eq h2, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff
    (pow_ne_zero k (FrobPow.ne_zero (Ambient F) (q := Nat.card F)))).mp hsub)

/-- The Frobenius twist of a polynomial, evaluated on power series, is the Frobenius twist. -/
lemma coe_polyTwist' (k : ℕ) (P : Polynomial (Ambient F)) :
    ((polyTwist (q := Nat.card F) k P : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = frobTwist (R := Ambient F) (p := Nat.card F) k (P : PowerSeries (Ambient F)) := by
  simpa only [coeHom_apply] using coe_polyTwist (q := Nat.card F) k P

/-- The set of "potential denominators" of `F/Q`: the ideal of polynomials `H` with
`F·H ∈ T·Q`. -/
noncomputable def denIdeal (f : PowerSeries (Ambient F)) (Q : Polynomial (Ambient F)) :
    Ideal (Polynomial (Ambient F)) where
  carrier := {H | ∃ G : PowerSeries (Ambient F), GEntire G ∧
    f * (H : PowerSeries (Ambient F)) = G * (Q : PowerSeries (Ambient F))}
  zero_mem' := ⟨0, GEntire.zero, by simp⟩
  add_mem' := by
    rintro H H' ⟨G, hG, hEq⟩ ⟨G', hG', hEq'⟩
    refine ⟨G + G', hG.add hG', ?_⟩
    rw [Polynomial.coe_add, mul_add, hEq, hEq', add_mul]
  smul_mem' := by
    rintro A H ⟨G, hG, hEq⟩
    refine ⟨(A : PowerSeries (Ambient F)) * G, (GEntire.polynomial A).mul hG, ?_⟩
    show f * ((A * H : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((A : PowerSeries (Ambient F)) * G) * (Q : PowerSeries (Ambient F))
    rw [Polynomial.coe_mul]
    calc f * ((A : PowerSeries (Ambient F)) * (H : PowerSeries (Ambient F)))
        = (A : PowerSeries (Ambient F)) * (f * (H : PowerSeries (Ambient F))) := by ring
      _ = (A : PowerSeries (Ambient F)) * (G * (Q : PowerSeries (Ambient F))) := by rw [hEq]
      _ = ((A : PowerSeries (Ambient F)) * G) * (Q : PowerSeries (Ambient F)) := by ring

end ZagierHoffmanPositiveChar

/-! ## §4. The rationality theorem -/

namespace ZagierHoffmanPositiveChar

variable {F : Type*} [Field F] [Finite F]

/-- The `C`-scaling of a polynomial with `σ`-fixed coefficients. -/
lemma eval_mem_ambK_of_map_ambCoeff (p : Polynomial F) :
    (p.map (ambCoeff F)).eval (ambTheta F) ∈ ambK F := by
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
  refine Subfield.sum_mem _ fun i _ => ?_
  exact Subfield.mul_mem _ (ambCoeff_mem_ambK F (p.coeff i))
    (Subfield.pow_mem _ (ambTheta_mem_ambK F) i)

lemma eval_ne_zero_of_map_ambCoeff {p : Polynomial F} (hp : p ≠ 0) :
    (p.map (ambCoeff F)).eval (ambTheta F) ≠ 0 := by
  intro h
  refine hp (ambTheta_transcendental F p ?_)
  have h2 : Polynomial.eval₂ (ambCoeff F) (ambTheta F) p = 0 := by
    rw [← Polynomial.eval_map]; exact h
  exact h2

/-- **The elementary rationality theorem.**  Let `f` be a super-entire power series, `Q ≠ 0` a
polynomial with `Q(θ) = 1`, and suppose that `f/Q` is fixed by the Frobenius twist
(`f^{(1)}·Q = f·Q^{(1)}`).  Then `f(θ) ∈ K = F_q(θ)`.

This is the precise form of Dac's "`f_{t;Q}(θ) ∈ K`" (Theorem `linear independence`, §3.3), and the
elementary replacement of Pap08 §4.1.6. -/
theorem evalSeriesGen_mem_ambK_of_frobInv (harch : GammaArchimedean ℚᵐ⁰) {γ : ℚᵐ⁰}
    (hγ0 : 0 < γ) (hγ : γ < 1)
    {f : PowerSeries (Ambient F)} (hf : GSuperEntire γ f)
    {Q : Polynomial (Ambient F)} (hQ : Q.eval (ambTheta F) = 1) (hQ0 : Q ≠ 0)
    (hrel : frobTwist (R := Ambient F) (p := Nat.card F) 1 f * (Q : PowerSeries (Ambient F))
      = f * ((polyTwist (q := Nat.card F) 1 Q : Polynomial (Ambient F)) :
          PowerSeries (Ambient F))) :
    evalSeriesGen f (ambTheta F) ∈ ambK F := by
  classical
  have hγ1 : γ ≤ 1 := le_of_lt hγ
  have hfe : GEntire (K := Ambient F) f :=
    GSuperEntire.entire hγ1 (fun x hx => harch γ hγ x hx) hf
  have hQps : (Q : PowerSeries (Ambient F)) ≠ 0 := polynomial_coe_powerSeries_ne_zero.mpr hQ0
  have hptQ : (polyTwist (q := Nat.card F) 1 Q : Polynomial (Ambient F)) ≠ 0 := by
    rw [polyTwist, polyTwistHom_apply]
    exact fun h => hQ0 ((Polynomial.map_eq_zero_iff (frobPowHom_injective 1)).mp h)
  have hσQ : frobTwist (R := Ambient F) (p := Nat.card F) 1 (Q : PowerSeries (Ambient F)) ≠ 0 := by
    rw [← coe_polyTwist' 1 Q]
    exact fun h => hptQ (Polynomial.coe_injective (Ambient F) (by rw [h, Polynomial.coe_zero]))
  have hrel' : frobTwist (R := Ambient F) (p := Nat.card F) 1 f * (Q : PowerSeries (Ambient F))
      = f * frobTwist (R := Ambient F) (p := Nat.card F) 1 (Q : PowerSeries (Ambient F)) := by
    rw [hrel, coe_polyTwist' 1 Q]
  -- the potential-denominator ideal
  set M := denIdeal f Q with hM
  obtain ⟨b₀, hb₀⟩ := (IsPrincipalIdealRing.principal M).principal
  have hQmem : Q ∈ M := ⟨f, hfe, rfl⟩
  have hMne : M ≠ ⊥ := by
    intro h
    rw [h, Submodule.mem_bot] at hQmem
    exact hQ0 hQmem
  have hb0ne : b₀ ≠ 0 := by
    intro h0
    apply hMne
    rw [hb₀, h0]
    exact Submodule.span_singleton_eq_bot.mpr rfl
  have hb0mem : b₀ ∈ M := by
    rw [hb₀]; exact Submodule.mem_span_singleton_self b₀
  obtain ⟨G, hG, hGb⟩ := hb0mem
  have hσb₀ : ((polyTwist (q := Nat.card F) 1 b₀ : Polynomial (Ambient F)) :
      PowerSeries (Ambient F)) = frobTwist (R := Ambient F) (p := Nat.card F) 1
        (b₀ : PowerSeries (Ambient F)) := coe_polyTwist' 1 b₀
  -- the twist-stability of `M`
  have hsig' : f * ((polyTwist (q := Nat.card F) 1 b₀ : Polynomial (Ambient F)) :
      PowerSeries (Ambient F)) = frobTwist (R := Ambient F) (p := Nat.card F) 1 G
        * (Q : PowerSeries (Ambient F)) := by
    have h1 : frobTwist (R := Ambient F) (p := Nat.card F) 1
        (f * (b₀ : PowerSeries (Ambient F)))
        = frobTwist (R := Ambient F) (p := Nat.card F) 1
          (G * (Q : PowerSeries (Ambient F))) := by rw [hGb]
    rw [frobTwist_mul, frobTwist_mul] at h1
    rw [hσb₀]
    refine mul_right_cancel₀ hσQ ?_
    calc (f * frobTwist (R := Ambient F) (p := Nat.card F) 1 (b₀ : PowerSeries (Ambient F)))
          * frobTwist (R := Ambient F) (p := Nat.card F) 1 (Q : PowerSeries (Ambient F))
        = (f * frobTwist (R := Ambient F) (p := Nat.card F) 1 (Q : PowerSeries (Ambient F)))
          * frobTwist (R := Ambient F) (p := Nat.card F) 1 (b₀ : PowerSeries (Ambient F)) := by
            ring
      _ = (frobTwist (R := Ambient F) (p := Nat.card F) 1 f * (Q : PowerSeries (Ambient F)))
          * frobTwist (R := Ambient F) (p := Nat.card F) 1 (b₀ : PowerSeries (Ambient F)) := by
            rw [congrArg (· * frobTwist (R := Ambient F) (p := Nat.card F) 1
              (b₀ : PowerSeries (Ambient F))) hrel']
      _ = (frobTwist (R := Ambient F) (p := Nat.card F) 1 f
            * frobTwist (R := Ambient F) (p := Nat.card F) 1 (b₀ : PowerSeries (Ambient F)))
          * (Q : PowerSeries (Ambient F)) := by ring
      _ = (frobTwist (R := Ambient F) (p := Nat.card F) 1 G
            * frobTwist (R := Ambient F) (p := Nat.card F) 1 (Q : PowerSeries (Ambient F)))
          * (Q : PowerSeries (Ambient F)) := by
            rw [congrArg (· * (Q : PowerSeries (Ambient F))) h1]
      _ = (frobTwist (R := Ambient F) (p := Nat.card F) 1 G * (Q : PowerSeries (Ambient F)))
          * frobTwist (R := Ambient F) (p := Nat.card F) 1 (Q : PowerSeries (Ambient F)) := by
            ring
  have hsig : polyTwist (q := Nat.card F) 1 b₀ ∈ M :=
    ⟨frobTwist (R := Ambient F) (p := Nat.card F) 1 G, hG.frobTwist 1, hsig'⟩
  -- `b₀ | σ(b₀)`, and the cofactor is a constant
  obtain ⟨c, hc⟩ : ∃ c, polyTwist (q := Nat.card F) 1 b₀ = b₀ * c := by
    have hmem : polyTwist (q := Nat.card F) 1 b₀
        ∈ Ideal.span ({b₀} : Set (Polynomial (Ambient F))) := by
      rw [show Ideal.span ({b₀} : Set (Polynomial (Ambient F))) = M from hb₀.symm]
      exact hsig
    exact Ideal.mem_span_singleton.mp hmem
  have hpt0 : polyTwist (q := Nat.card F) 1 b₀ ≠ 0 := by
    rw [polyTwist, polyTwistHom_apply]
    exact fun h => hb0ne ((Polynomial.map_eq_zero_iff (frobPowHom_injective 1)).mp h)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact hpt0 hc
  have hdegc : c.natDegree = 0 := by
    have h2 : (polyTwist (q := Nat.card F) 1 b₀).natDegree = b₀.natDegree := by
      rw [polyTwist, polyTwistHom_apply]
      exact Polynomial.natDegree_map_eq_of_injective (frobPowHom_injective 1) b₀
    have h1 : (polyTwist (q := Nat.card F) 1 b₀).natDegree = b₀.natDegree + c.natDegree := by
      rw [hc, Polynomial.natDegree_mul hb0ne hc0]
    omega
  set d : Ambient F := c.coeff 0 with hd
  have hcd : c = Polynomial.C d := by
    rw [hd]; exact Polynomial.eq_C_of_natDegree_eq_zero hdegc
  have hcP : polyTwist (q := Nat.card F) 1 b₀ = b₀ * Polynomial.C d := by
    rw [hc, hcd]
  have hd0 : d ≠ 0 := by
    rintro h0
    exact hc0 (by rw [hcd, h0, Polynomial.C_0])
  have hGb' : f * (b₀ : PowerSeries (Ambient F)) = G * (Q : PowerSeries (Ambient F)) := hGb
  -- the witness satisfies `σ(G) = G·d`
  have hGC : frobTwist (R := Ambient F) (p := Nat.card F) 1 G = G * PowerSeries.C d := by
    have hkey : frobTwist (R := Ambient F) (p := Nat.card F) 1 G * (Q : PowerSeries (Ambient F))
        = (G * PowerSeries.C d) * (Q : PowerSeries (Ambient F)) := by
      rw [← hsig', hcP, Polynomial.coe_mul, Polynomial.coe_C]
      calc f * ((b₀ : PowerSeries (Ambient F)) * PowerSeries.C d)
          = (f * (b₀ : PowerSeries (Ambient F))) * PowerSeries.C d := by ring
        _ = (G * (Q : PowerSeries (Ambient F))) * PowerSeries.C d := by rw [hGb']
        _ = (G * PowerSeries.C d) * (Q : PowerSeries (Ambient F)) := by ring
    exact mul_right_cancel₀ hQps hkey
  by_cases hG0 : G = 0
  · have hf0 : f = 0 := by
      have h : f * (b₀ : PowerSeries (Ambient F)) = 0 := by rw [hGb', hG0, zero_mul]
      rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' (polynomial_coe_powerSeries_ne_zero.mpr hb0ne)
    rw [hf0, evalSeriesGen_zero]
    exact (ambK F).zero_mem
  · obtain ⟨n₀, hn₀⟩ : ∃ n, G.coeff n ≠ 0 := by
      by_contra h
      push Not at h
      exact hG0 (PowerSeries.ext h)
    set a : Ambient F := G.coeff n₀ with ha
    have ha0 : a ≠ 0 := hn₀
    have haq : a ^ Nat.card F = a * d := by
      have h1 := congrArg (PowerSeries.coeff n₀) hGC
      rw [frobTwist_coeff, pow_one, PowerSeries.coeff_mul_C] at h1
      exact h1
    have hainv : (a⁻¹) ^ Nat.card F = a⁻¹ * d⁻¹ := by
      rw [inv_pow, haq, mul_inv, mul_comm]
    set H : PowerSeries (Ambient F) := G * PowerSeries.C (a⁻¹) with hHdef
    set b₁ : Polynomial (Ambient F) := b₀ * Polynomial.C (a⁻¹) with hb₁def
    have hb₁ne : b₁ ≠ 0 := by
      rw [hb₁def]
      refine mul_ne_zero hb0ne (Polynomial.C_ne_zero.mpr (inv_ne_zero ha0))
    have hσb₁ : frobTwist (R := Ambient F) (p := Nat.card F) 1 (b₀ : PowerSeries (Ambient F))
        = (b₀ : PowerSeries (Ambient F)) * PowerSeries.C d := by
      rw [← coe_polyTwist' 1 b₀, hcP, Polynomial.coe_mul, Polynomial.coe_C]
    have hdd : d * (a⁻¹ * d⁻¹) = a⁻¹ := by
      rw [← mul_assoc, mul_comm d a⁻¹, mul_assoc, mul_inv_cancel₀ hd0, mul_one]
    have hb₁σ : frobTwist (R := Ambient F) (p := Nat.card F) 1 (b₁ : PowerSeries (Ambient F))
        = (b₁ : PowerSeries (Ambient F)) := by
      rw [hb₁def, Polynomial.coe_mul, Polynomial.coe_C, frobTwist_mul, hσb₁, frobTwist_C, pow_one,
        hainv, mul_assoc, ← PowerSeries.C.map_mul, hdd]
    have hHinv : frobTwist (R := Ambient F) (p := Nat.card F) 1 H = H := by
      rw [hHdef, frobTwist_mul, hGC, frobTwist_C, pow_one, hainv, mul_assoc,
        ← PowerSeries.C.map_mul, hdd]
    have hHent : GEntire (K := Ambient F) H := by
      rw [hHdef]; exact hG.mul (GEntire.C (a⁻¹))
    obtain ⟨p₀, hp₀⟩ := exists_polynomial_of_gEntire_of_frobTwist_one_eq
      (GEntire.polynomial b₁) hb₁σ
    obtain ⟨p₁, hp₁⟩ := exists_polynomial_of_gEntire_of_frobTwist_one_eq hHent hHinv
    -- the equation `f·b₁ = H·Q`
    have hFb₁ : f * (b₁ : PowerSeries (Ambient F)) = H * (Q : PowerSeries (Ambient F)) := by
      rw [hb₁def, Polynomial.coe_mul, Polynomial.coe_C, hHdef]
      calc f * ((b₀ : PowerSeries (Ambient F)) * PowerSeries.C (a⁻¹))
          = (f * (b₀ : PowerSeries (Ambient F))) * PowerSeries.C (a⁻¹) := by ring
        _ = (G * (Q : PowerSeries (Ambient F))) * PowerSeries.C (a⁻¹) := by rw [hGb']
        _ = (G * PowerSeries.C (a⁻¹)) * (Q : PowerSeries (Ambient F)) := by ring
    -- super-entireness of the pieces
    have hb₁se : GSuperEntire γ (b₁ : PowerSeries (Ambient F)) := by
      rw [← hp₀]; exact GSuperEntire.polynomial hγ0 hγ1 _
    have hHse : GSuperEntire γ H := by
      rw [← hp₁]; exact GSuperEntire.polynomial hγ0 hγ1 _
    have hQse : GSuperEntire γ (Q : PowerSeries (Ambient F)) :=
      GSuperEntire.polynomial hγ0 hγ1 Q
    have hev := congrArg (fun s : PowerSeries (Ambient F) => evalSeriesGen s (ambTheta F)) hFb₁
    rw [evalSeriesGen_mul hγ harch hf hb₁se, evalSeriesGen_mul hγ harch hHse hQse] at hev
    rw [← hp₀, ← hp₁, evalSeriesGen_polynomial, evalSeriesGen_polynomial,
      evalSeriesGen_polynomial] at hev
    simp only [hQ] at hev
    rw [mul_one] at hev
    -- membership and non-vanishing
    have hBmem : (p₀.map (ambCoeff F)).eval (ambTheta F) ∈ ambK F :=
      eval_mem_ambK_of_map_ambCoeff p₀
    have hCmem : (p₁.map (ambCoeff F)).eval (ambTheta F) ∈ ambK F :=
      eval_mem_ambK_of_map_ambCoeff p₁
    have hp₀0 : p₀ ≠ 0 := by
      rintro rfl
      apply polynomial_coe_powerSeries_ne_zero.mpr hb₁ne
      rw [← hp₀]
      simp
    have hBne : (p₀.map (ambCoeff F)).eval (ambTheta F) ≠ 0 :=
      eval_ne_zero_of_map_ambCoeff hp₀0
    have hdiv : evalSeriesGen f (ambTheta F)
        = (p₁.map (ambCoeff F)).eval (ambTheta F) / (p₀.map (ambCoeff F)).eval (ambTheta F) :=
      (eq_div_iff_mul_eq hBne).mpr hev
    rw [hdiv]
    exact Subfield.div_mem (ambK F) hCmem hBmem

end ZagierHoffmanPositiveChar

/-! ## §5. Dac's `f_{t;Q}(θ) ∈ K` for the merged `t`-motive -/

namespace ZagierHoffmanPositiveChar

variable {F : Type*} [Field F] [Finite F]
variable {γ : ℚᵐ⁰} {ω : PowerSeries (Ambient F)}
variable {w : ℕ} {S : Finset (List (ℕ × Polynomial (Ambient F)))}
variable {cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)}

/-- The `L`-series of a tuple all of whose entries come from `S` is super-entire. -/
lemma gSuperEntire_tmL_of_mem (hγ : γ < 1) (harch : GammaArchimedean ℚᵐ⁰)
    (hq : 2 ≤ Nat.card F) (hω : GIsSmall γ ω) (hωse : GSuperEntire γ ω)
    (hsm : ∀ s ∈ S, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries (Ambient F))))
    (hSse : ∀ s ∈ S, ∀ y ∈ s, GSuperEntire γ ((y.2 : PowerSeries (Ambient F))))
    {u : List (ℕ × Polynomial (Ambient F))} (hu : ∀ y ∈ u, ∃ s ∈ S, y ∈ s) :
    GSuperEntire γ (tmL (Nat.card F) ω u) := by
  rw [tmL]
  refine gSuperEntire_atLrPaperGen hγ harch hq hω hωse ?_ ?_
  · intro x hx
    rw [tmCoe, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨s, hs, hys⟩ := hu y hy
    exact hsm s hs y hys
  · intro x hx
    rw [tmCoe, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨s, hs, hys⟩ := hu y hy
    exact hSse s hs y hys

/-- A suffix of a prefix of an element of `S` is entrywise from `S`. -/
lemma mem_of_mem_drop_tmI {t : List (ℕ × Polynomial (Ambient F))} (ht : t ∈ tmI S)
    {y : ℕ × Polynomial (Ambient F)} {k : ℕ} (hy : y ∈ t.drop k) : ∃ s ∈ S, y ∈ s :=
  mem_tmI_entry F ht (List.mem_of_mem_drop hy)

/-- Chang's Lemma 5.3.1 (generic): the `f`-row entries are super-entire. -/
lemma gSuperEntire_tmF (hγ0 : 0 < γ) (hγ : γ < 1) (harch : GammaArchimedean ℚᵐ⁰)
    (hq : 2 ≤ Nat.card F) (hω : GIsSmall γ ω) (hωse : GSuperEntire γ ω)
    (hsm : ∀ s ∈ S, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries (Ambient F))))
    (hSse : ∀ s ∈ S, ∀ y ∈ s, GSuperEntire γ ((y.2 : PowerSeries (Ambient F))))
    (t : ↥(tmI S)) : GSuperEntire γ (tmF (Nat.card F) ω w S cf t.1) := by
  rw [tmF]
  refine GSuperEntire.sum (K := Ambient F) hγ.le S _ (fun s hs => ?_)
  by_cases h : s.take t.1.length = t.1
  · rw [if_pos h]
    refine (GSuperEntire.polynomial hγ0 hγ.le (cf s)).mul hγ.le ?_
    exact gSuperEntire_tmL_of_mem hγ harch hq hω hωse hsm hSse
      (fun y hy => ⟨s, hs, List.mem_of_mem_drop hy⟩)
  · rw [if_neg h]; exact GSuperEntire.zero γ

/-- Chang's Lemma 5.3.1 (generic): the entries `Ψ_{t,t'} = 𝓛(t \ t')·ω^{w-w(t)}` are
super-entire. -/
lemma gSuperEntire_tmPsi (hγ : γ < 1) (harch : GammaArchimedean ℚᵐ⁰)
    (hq : 2 ≤ Nat.card F) (hω : GIsSmall γ ω) (hωse : GSuperEntire γ ω)
    (hsm : ∀ s ∈ S, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries (Ambient F))))
    (hSse : ∀ s ∈ S, ∀ y ∈ s, GSuperEntire γ ((y.2 : PowerSeries (Ambient F))))
    (i j : ↥(tmI S)) : GSuperEntire γ (tmPsi (K := Ambient F) (Nat.card F) ω w i.1 j.1) := by
  rw [tmPsi]
  by_cases h : i.1.take j.1.length = j.1
  · rw [if_pos h]
    refine (gSuperEntire_tmL_of_mem hγ harch hq hω hωse hsm hSse ?_).mul hγ.le
      (hωse.pow hγ.le _)
    intro y hy
    exact mem_of_mem_drop_tmI (S := S) i.2 hy
  · rw [if_neg h]; exact GSuperEntire.zero γ

/-- The entries of the rigid analytic trivialisation are super-entire. -/
lemma gSuperEntire_tmPsiOpt (hγ0 : 0 < γ) (hγ : γ < 1) (harch : GammaArchimedean ℚᵐ⁰)
    (hq : 2 ≤ Nat.card F) (hω : GIsSmall γ ω) (hωse : GSuperEntire γ ω)
    (hsm : ∀ s ∈ S, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries (Ambient F))))
    (hSse : ∀ s ∈ S, ∀ y ∈ s, GSuperEntire γ ((y.2 : PowerSeries (Ambient F))))
    (i : Option ↥(tmI S)) (j : ↥(tmI S)) :
    GSuperEntire γ (tmPsiOpt (K := Ambient F) (Nat.card F) ω w S cf i (some j)) := by
  rcases i with _ | i
  · rw [tmPsiOpt_none_some]
    exact gSuperEntire_tmF hγ0 hγ harch hq hω hωse hsm hSse j
  · rw [tmPsiOpt_some_some]
    exact gSuperEntire_tmPsi hγ harch hq hω hωse hsm hSse i j

/-- Evaluation of a finite sum of `polynomial × super-entire series`. -/
lemma evalSeriesGen_finset_sum_poly_mul (hγ0 : 0 < γ) (hγ : γ < 1)
    (harch : GammaArchimedean ℚᵐ⁰) {ι : Type*} (s : Finset ι)
    (h : ι → Polynomial (Ambient F)) (ψ : ι → PowerSeries (Ambient F))
    (hψ : ∀ i ∈ s, GSuperEntire γ (ψ i)) (c : Ambient F) :
    evalSeriesGen (∑ i ∈ s, coeHom (K := Ambient F) (h i) * ψ i) c
      = ∑ i ∈ s, (h i).eval c * evalSeriesGen (ψ i) c := by
  have hse : ∀ i ∈ s, GSuperEntire γ (coeHom (K := Ambient F) (h i) * ψ i) := fun i hi =>
    (GSuperEntire.polynomial hγ0 hγ.le (h i)).mul hγ.le (hψ i hi)
  rw [evalSeriesGen_finset_sum (K := Ambient F) hγ harch s
    (fun i => coeHom (K := Ambient F) (h i) * ψ i) hse c]
  exact Finset.sum_congr rfl fun i hi => by
    simp only [coeHom_apply]
    rw [evalSeriesGen_mul hγ harch (GSuperEntire.polynomial hγ0 hγ.le (h i)) (hψ i hi) c,
      evalSeriesGen_polynomial]



/-- `coeHom` of a Frobenius twist is the Frobenius twist of `coeHom`. -/
lemma coe_polyTwist'' (k : ℕ) (P : Polynomial (Ambient F)) :
    (coeHom (K := Ambient F) (polyTwist (q := Nat.card F) k P) : PowerSeries (Ambient F))
      = frobTwist (R := Ambient F) (p := Nat.card F) k (coeHom (K := Ambient F) P) := by
  simpa only [coeHom_apply] using coe_polyTwist' k P

/-- **The algebraic core of the `K̄ → K` step.**  If the row `P` satisfies the "cleared second
relation" `frobTwist 1 (P_i)·Q = sQ·∑_k P_k A_{ki}` and `A` is a rigid analytic trivialisation
(`∑_i A_{ki}·frobTwist 1 (Ψ_i) = Ψ_k`), then the row `(P·Ψ)/Q` is Frobenius-invariant. -/
lemma row_frobInv {ι : Type*} [Fintype ι] (Pc : ι → PowerSeries (Ambient F))
    (Ac : ι → ι → PowerSeries (Ambient F)) (Ψ : ι → PowerSeries (Ambient F))
    (Q sQ : PowerSeries (Ambient F))
    (hstep : ∀ i, frobTwist (R := Ambient F) (p := Nat.card F) 1 (Pc i) * Q
      = sQ * ∑ k, Pc k * Ac k i)
    (hFE : ∀ k, (∑ i, Ac k i * frobTwist (R := Ambient F) (p := Nat.card F) 1 (Ψ i)) = Ψ k) :
    frobTwist (R := Ambient F) (p := Nat.card F) 1 (∑ i, Pc i * Ψ i) * Q
      = (∑ i, Pc i * Ψ i) * sQ := by
  have e1 : frobTwist (R := Ambient F) (p := Nat.card F) 1 (∑ i, Pc i * Ψ i) * Q
      = ∑ i, (frobTwist (R := Ambient F) (p := Nat.card F) 1 (Pc i) * Q)
          * frobTwist (R := Ambient F) (p := Nat.card F) 1 (Ψ i) := by
    rw [frobTwist_sum 1 Finset.univ (fun i => Pc i * Ψ i), Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [frobTwist_mul]; ring
  have e2 : (∑ i, (frobTwist (R := Ambient F) (p := Nat.card F) 1 (Pc i) * Q)
          * frobTwist (R := Ambient F) (p := Nat.card F) 1 (Ψ i))
      = ∑ i, (sQ * ∑ k, Pc k * Ac k i)
          * frobTwist (R := Ambient F) (p := Nat.card F) 1 (Ψ i) :=
    Finset.sum_congr rfl fun i _ => by rw [hstep i]
  have e3 : (∑ i, (sQ * ∑ k, Pc k * Ac k i)
          * frobTwist (R := Ambient F) (p := Nat.card F) 1 (Ψ i))
      = sQ * ∑ i, (∑ k, Pc k * Ac k i)
          * frobTwist (R := Ambient F) (p := Nat.card F) 1 (Ψ i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e4 : (∑ i, (∑ k, Pc k * Ac k i)
          * frobTwist (R := Ambient F) (p := Nat.card F) 1 (Ψ i))
      = ∑ k, Pc k * Ψ k := by
    rw [show (∑ i, (∑ k, Pc k * Ac k i)
          * frobTwist (R := Ambient F) (p := Nat.card F) 1 (Ψ i))
        = ∑ k, Pc k * ∑ i, Ac k i
          * frobTwist (R := Ambient F) (p := Nat.card F) 1 (Ψ i) from by
      simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]]
    exact Finset.sum_congr rfl fun k _ => by rw [hFE k]
  rw [e1, e2, e3, e4, mul_comm]

/-- **Dac's Theorem (linear independence), conclusion `f_{t;Q}(θ) ∈ K`, for the merged dual
`t`-motive.**  Given the ABP row `P` (`P·ψ_a = 0`, `P(θ) = tmRho`, `P none ≠ 0`) and the vanishing
of all the coefficients `B̃` of the second relation (`TmApply.tmB`), every entry of the `f`-row
evaluates at `θ` to an element of `K = F_q(θ)`. -/
theorem tmF_eval_mem_ambK (hγ0 : 0 < γ) (hγ : γ < 1) (harch : GammaArchimedean ℚᵐ⁰)
    (hq : 2 ≤ Nat.card F) (hω : GIsSmall γ ω) (hωse : GSuperEntire γ ω)
    (hωfe : (PowerSeries.X - PowerSeries.C ((ambTheta F) ^ Nat.card F))
      * frobTwist (R := Ambient F) (p := Nat.card F) 1 ω = ω)
    (hw : ∀ s ∈ S, tmWeight s = w)
    (hcf : ∀ s ∈ S, frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((cf s : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((cf s : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
    (hsm : ∀ s ∈ S, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries (Ambient F))))
    (hSse : ∀ s ∈ S, ∀ y ∈ s, GSuperEntire γ ((y.2 : PowerSeries (Ambient F))))
    (hne : ∀ s ∈ S, s ≠ [])
    {P : Option ↥(tmI S) → Polynomial (Ambient F)}
    (hB : ∀ t : ↥(tmI S), tmB F w S cf P (some t) = 0)
    (hPθ : ∀ j, (P j).eval (ambTheta F) = tmRho F S j)
    (hP0 : P none ≠ 0) :
    ∀ t' : ↥(tmI S),
      evalSeriesGen (tmF (Nat.card F) ω w S cf t'.1) (ambTheta F) ∈ ambK F := by
  classical
  intro t'
  have hQev : (P none).eval (ambTheta F) = 1 := by rw [hPθ none, tmRho_none]
  have hPse : ∀ t : ↥(tmI S), (P (some t)).eval (ambTheta F) = 0 := by
    intro t; rw [hPθ (some t), tmRho_some]
  -- the functional equation, entrywise
  have hFE : ∀ (k j : Option ↥(tmI S)),
      (∑ i, coeHom (K := Ambient F)
          (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf k i)
        * frobTwist (R := Ambient F) (p := Nat.card F) 1
            (tmPsiOpt (K := Ambient F) (Nat.card F) ω w S cf i j))
        = tmPsiOpt (K := Ambient F) (Nat.card F) ω w S cf k j := by
    intro k j
    have h := tmPsiOpt_functional (S := S) (cf := cf) (K := Ambient F) (Nat.card F) (ambTheta F) w
      hγ harch hq hω hωfe hw hcf hsm hne
    have h2 := congrFun (congrFun h k) j
    rw [Matrix.mul_apply] at h2
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, frobTwistMat_apply] using h2.symm
  -- the second relation, cleared of denominators
  have hkey : ∀ i : Option ↥(tmI S),
      coeHom (K := Ambient F) (polyTwist (q := Nat.card F) 1 (P i))
          * coeHom (K := Ambient F) (P none)
        = coeHom (K := Ambient F) (polyTwist (q := Nat.card F) 1 (P none))
          * ∑ k, coeHom (K := Ambient F) (P k)
              * coeHom (K := Ambient F)
                  (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf k i) := by
    intro i
    have hbase : (P none) * polyTwist (q := Nat.card F) 1 (P i)
        = polyTwist (q := Nat.card F) 1 (P none)
          * ∑ k, P k * tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf k i := by
      rcases i with _ | i
      · rw [sum_mul_tmAOpt_none, mul_comm]
      · have h := hB i
        rw [tmB] at h
        exact sub_eq_zero.mp h
    have h' := congrArg (coeHom (K := Ambient F)) hbase
    simp only [map_mul, map_sum] at h'
    rw [← h', mul_comm]
  -- the Frobenius-invariance of the row `(P·Ψ) / P none`
  set Fj : PowerSeries (Ambient F) := ∑ i, coeHom (K := Ambient F) (P i)
      * tmPsiOpt (K := Ambient F) (Nat.card F) ω w S cf i (some t') with hFj
  have hFj_se : GSuperEntire γ Fj := by
    rw [hFj]
    refine GSuperEntire.sum (K := Ambient F) hγ.le Finset.univ _ (fun i _ => ?_)
    exact (GSuperEntire.polynomial hγ0 hγ.le (P i)).mul hγ.le
      (gSuperEntire_tmPsiOpt hγ0 hγ harch hq hω hωse hsm hSse i t')
  have hstep : ∀ i : Option ↥(tmI S),
      frobTwist (R := Ambient F) (p := Nat.card F) 1 (coeHom (K := Ambient F) (P i))
          * coeHom (K := Ambient F) (P none)
        = coeHom (K := Ambient F) (polyTwist (q := Nat.card F) 1 (P none))
          * ∑ k, coeHom (K := Ambient F) (P k)
              * coeHom (K := Ambient F)
                  (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf k i) := by
    intro i
    rw [← coe_polyTwist'' 1 (P i)]
    exact hkey i
  have hrel : frobTwist (R := Ambient F) (p := Nat.card F) 1 Fj
      * coeHom (K := Ambient F) (P none)
      = Fj * coeHom (K := Ambient F) (polyTwist (q := Nat.card F) 1 (P none)) := by
    have h := row_frobInv (Pc := fun i => coeHom (K := Ambient F) (P i))
      (Ac := fun k i => coeHom (K := Ambient F)
        (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf k i))
      (Ψ := fun i => tmPsiOpt (K := Ambient F) (Nat.card F) ω w S cf i (some t'))
      (Q := coeHom (K := Ambient F) (P none))
      (sQ := coeHom (K := Ambient F) (polyTwist (q := Nat.card F) 1 (P none)))
      (fun i => hstep i) (fun k => hFE k (some t'))
    rw [hFj]
    exact h
  -- the identification of the row with the `f`-row
  have hFj_eval : evalSeriesGen Fj (ambTheta F)
      = evalSeriesGen (tmF (Nat.card F) ω w S cf t'.1) (ambTheta F) := by
    rw [hFj, evalSeriesGen_finset_sum_poly_mul hγ0 hγ harch Finset.univ P
      (fun i => tmPsiOpt (K := Ambient F) (Nat.card F) ω w S cf i (some t'))
      (fun i _ => gSuperEntire_tmPsiOpt hγ0 hγ harch hq hω hωse hsm hSse i t') (ambTheta F)]
    rw [Fintype.sum_option]
    rw [show (∑ t : ↥(tmI S), (P (some t)).eval (ambTheta F)
        * evalSeriesGen (tmPsiOpt (K := Ambient F) (Nat.card F) ω w S cf (some t) (some t'))
            (ambTheta F)) = 0 from
      Finset.sum_eq_zero fun t _ => by rw [hPse t, zero_mul]]
    simp only [tmPsiOpt_none_some, add_zero, hQev, one_mul]
  rw [← hFj_eval]
  exact evalSeriesGen_mem_ambK_of_frobInv harch hγ0 hγ hFj_se hQev hP0
    (by simpa only [coeHom_apply] using hrel)

end ZagierHoffmanPositiveChar

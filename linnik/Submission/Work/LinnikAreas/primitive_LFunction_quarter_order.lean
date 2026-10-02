/-
# The phi = 1/4 Burgess -> L-function chain with an explicit order factor

Heath-Brown, *Zero-free regions for Dirichlet L-functions, and the least prime in an arithmetic
progression*, PLMS 64 (1992), Lemma 2.5, small-order case: for a primitive non-principal
character `χ` of modulus `q` the Burgess bound with `φ = 1/4` reads

`‖L(σ+it,χ)‖ ≪ q^{(1/4)(1-σ)(1+1/k)+ε} (1+|t|)`,   `1 - 1/k ≤ σ ≤ 1`.

The input actually available for *all* moduli, with a uniform constant, is the character-sum
bound of Burgess with an *explicit order factor*:

`‖Σ_{N<n≤N+H} χ(n)‖ ≤ CB · (ord χ)^{3/(2k)} · q^{((k+1)/(4k²))+ε} · H^{1-1/k}`.

(`Commons.NumberTheory.DirichletCharacter.burgess_charSum_order_of_cubefree` produces exactly
this from the cube-free Burgess input.)  The point of this file is that the classical three-range
partial-summation argument of Heath-Brown §2 (as formalised for a *fixed* constant in
`primitive_LFunction_bound_quarter`) is **linear** in the character-sum constant, so it
propagates the order factor `(ord χ)^{3/(2k)}` into the L-function bound.

`primitive_quarter_charConst` below is exactly that: the same chain as
`primitive_LFunction_bound_quarter`, but with the hypothesis `CB` replaced by the
*character-dependent* constant `CB · (ord χ)^{3/(2k)}` and with the same factor appearing in the
conclusion.  The proof is the classical one, re-run with the per-character constant
`CBX = CB · (ord χ)^{3/(2k)}`.
-/
import Mathlib
import Submission.Work.NumberTheory.DirichletCharacter.quarterBurgess

open scoped BigOperators
open Finset MeasureTheory intervalIntegral
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Commons.NumberTheory.DirichletCharacter

/-- **The HB §2 chain with an explicit dependence on `ord χ`.**

Assume that for a primitive non-principal `χ` of modulus `q` the partial sums of `χ` satisfy
`‖Σ_{N<n≤N+H} χ(n)‖ ≤ (CB · (ord χ)^{3/(2k)}) · q^{((k+1)/(4k²))+ε/2} · H^{1-1/k}`.
Then for `1 - 1/k ≤ σ ≤ 1`,
`‖L(σ+it,χ)‖ ≤ C · (ord χ)^{3/(2k)} · q^{(1/4)(1-σ)(1+1/k)+ε-δ} (1+|t|)`
with `C` depending only on `k, ε, δ, CB`.

This is `primitive_LFunction_bound_quarter` strengthened from a constant `CB` that is uniform in
`χ` to a constant that is allowed to carry the factor `(ord χ)^{3/(2k)}`; the conclusion acquires
the same factor.  The analytic content (Pólya-Vinogradov tail, head at `Q = q^{(k+1)/(4k)}`, Abel
summation in the middle range) is unchanged, since it is linear in the input constant. -/
theorem primitive_quarter_charConst (k : ℕ) (hk : 3 ≤ k)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδε : δ ≤ ε/4)
    {CB : ℝ} (hCB : 0 < CB) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 →
      (∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ q →
        ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤
          CB * (orderOf χ : ℝ) ^ ((3:ℝ)/(2*(k:ℝ))) * (q:ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2)
            * (H:ℝ)^((1 - 1/((k:ℝ))))) →
      ∀ σ t : ℝ, 1 - 1/(k:ℝ) ≤ σ → σ ≤ 1 →
        ‖DirichletCharacter.LFunction χ ((σ:ℂ)+(t:ℂ)*Complex.I)‖ ≤
          C * (orderOf χ : ℝ) ^ ((3:ℝ)/(2*(k:ℝ)))
            * (q:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε - δ) * (1 + |t|) := by
  have hkR : (3:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hkpos : (0:ℝ) < (k:ℝ) := by linarith
  have hthnn : (0:ℝ) ≤ 1 - 1/(k:ℝ) := by
    rw [sub_nonneg, div_le_iff₀ (by positivity : (0:ℝ) < (k:ℝ))]
    linarith [hkR]
  obtain ⟨Clog, hClogpos, hClog⟩ :=
    Commons.Analysis.Real.log_pow_le_mul_rpow (show (0:ℝ) < ε/2 by positivity) 1
  obtain ⟨Clog2, hClog2pos, hClog2⟩ :=
    Commons.Analysis.Real.log_pow_le_mul_rpow (show (0:ℝ) < ε/8 by positivity) 1
  obtain ⟨CPV, hCPVpos, hCPV⟩ := Commons.NumberTheory.DirichletCharacter.polya_vinogradov
  have hC1pos : (0:ℝ) < 1 + Clog := by linarith
  have hC2pos : (0:ℝ) < 1 + Clog2 := by linarith
  have hCpos : (0:ℝ) < 3 * (3*(1+Clog) + 4*(1+Clog2)*(CB+1) + 14*CPV*(1+Clog2)) + 1 := by
    have h1 : (0:ℝ) < 1 + Clog := by linarith
    have h2 : (0:ℝ) < 1 + Clog2 := by linarith
    have h3 : (0:ℝ) < CB + 1 := by linarith
    positivity
  refine ⟨3 * (3*(1+Clog) + 4*(1+Clog2)*(CB+1) + 14*CPV*(1+Clog2)) + 1, hCpos, ?_⟩
  intro q _inst χ hprim hχ hB0 σ t hσ1 hσle
  -- the order factor `u = (ord χ)^{3/(2k)} ≥ 1` and the per-character constant `CBX = CB * u`
  set u : ℝ := (orderOf χ : ℝ) ^ ((3 : ℝ) / (2 * (k : ℝ))) with hudef
  have hord1 : (1 : ℝ) ≤ (orderOf χ : ℝ) := by
    have h1 : (1 : ℕ) ≤ orderOf χ := Nat.one_le_iff_ne_zero.mpr (ne_of_gt (orderOf_pos χ))
    exact_mod_cast h1
  have hexpnn : (0 : ℝ) ≤ (3 : ℝ) / (2 * (k : ℝ)) := by positivity
  have hu1 : (1 : ℝ) ≤ u := by rw [hudef]; exact Real.one_le_rpow hord1 hexpnn
  have hunonneg : (0 : ℝ) ≤ u := le_trans zero_le_one hu1
  set CBX : ℝ := CB * u with hCBXdef
  have hCBXpos : 0 < CBX := by rw [hCBXdef]; exact mul_pos hCB (lt_of_lt_of_le one_pos hu1)
  have hB : ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ q →
      ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤
        CBX * (q:ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2) * (H:ℝ)^((1 - 1/((k:ℝ)))) := by
    intro N H hN hH hHq
    rw [hCBXdef]
    exact hB0 hN hH hHq
  have hq2 : 2 ≤ q := by
    by_contra h
    rcases (by omega : q = 0 ∨ q = 1) with h0 | h1
    · exact NeZero.ne q h0
    · exact hχ (DirichletCharacter.level_one' (χ := χ) h1)
  set θ : ℝ := ((k:ℝ)+1)/(4*(k:ℝ)) with hθdef
  have hθpos : 0 < θ := by rw [hθdef]; positivity
  have hθle : θ ≤ 1/2 := by
    rw [hθdef, div_le_iff₀ (by positivity : (0:ℝ) < 4*(k:ℝ))]
    linarith [hkR]
  have hθlt1 : θ ≤ 1 := by linarith
  set μ : ℝ := 1 - σ with hμdef
  have hμ0 : 0 ≤ μ := by rw [hμdef]; linarith
  have h1k : 1/(k:ℝ) ≤ 1/3 := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 3) hkR
  set Q : ℕ := Nat.ceil ((q:ℝ)^θ) with hQdef
  have hqR1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hqRpos : (0:ℝ) < (q:ℝ) := lt_of_lt_of_le one_pos hqR1
  have hQge : (q:ℝ)^θ ≤ (Q:ℝ) := Nat.le_ceil _
  have hqpow1 : (1:ℝ) ≤ (q:ℝ)^θ := Real.one_le_rpow hqR1 (le_of_lt hθpos)
  have hQ1 : 1 ≤ Q := by
    have : (1:ℝ) ≤ (Q:ℝ) := le_trans hqpow1 hQge
    exact_mod_cast this
  have hQq : Q ≤ q := by
    rw [hQdef]
    refine Nat.ceil_le.mpr ?_
    have := Real.rpow_le_rpow_of_exponent_le hqR1 hθlt1
    rwa [Real.rpow_one] at this
  have hQle : (Q:ℝ) ≤ 2*(q:ℝ)^θ := by
    have h := Nat.ceil_lt_add_one (le_of_lt (Real.rpow_pos_of_pos hqRpos θ))
    linarith [h, hqpow1]
  -- prefix bound
  set A : ℝ := (CBX+1) * (q:ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2) with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hPre : ∀ m : ℕ, 1 ≤ m → m ≤ q →
      ‖∑ n ∈ Finset.Icc 1 m, χ n‖ ≤ A * (m:ℝ)^((1 - 1/((k:ℝ)))) := by
    intro m hm1 hmq
    rcases Nat.lt_or_ge 1 m with hm2 | hm2
    · have hmem : Finset.Icc 1 m = insert 1 (Finset.Ioc 1 m) := by
        ext n; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]; omega
      have hnotin : (1:ℕ) ∉ Finset.Ioc 1 m := by simp [Finset.mem_Ioc]
      rw [hmem, Finset.sum_insert hnotin]
      have hb := hB (N:=1) (H:=m-1) le_rfl (by omega) (by omega)
      rw [show (1:ℕ)+(m-1) = m by omega] at hb
      have hmR : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
      have hm23 : (1:ℝ) ≤ (m:ℝ)^((1 - 1/((k:ℝ)))) := Real.one_le_rpow hmR hthnn
      have hχ1 : ‖χ ((1:ℕ):ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
      have hA1 : (1:ℝ) ≤ (q:ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2) * (m:ℝ)^((1 - 1/((k:ℝ)))) := by
        have h1 : (1:ℝ) ≤ (q:ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2) := Real.one_le_rpow hqR1 (by positivity)
        have := mul_le_mul h1 hm23 (by norm_num) (Real.rpow_nonneg (le_of_lt hqRpos) _)
        simpa using this
      have hfin : 1 + CBX * (q:ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2) * (m:ℝ)^((1 - 1/((k:ℝ)))) ≤ A * (m:ℝ)^((1 - 1/((k:ℝ)))) := by
        rw [hAdef]
        have hqnn : (0:ℝ) ≤ (q:ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2) := Real.rpow_nonneg (le_of_lt hqRpos) _
        linarith only [hA1]
      calc ‖χ ((1:ℕ):ZMod q) + ∑ n ∈ Finset.Ioc 1 m, χ n‖
          ≤ 1 + CBX * (q:ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2) * ((m-1:ℕ):ℝ)^((1 - 1/((k:ℝ)))) := by
            refine (norm_add_le _ _).trans ?_
            exact add_le_add hχ1 hb
        _ ≤ 1 + CBX * (q:ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2) * (m:ℝ)^((1 - 1/((k:ℝ)))) := by
            have hHm : ((m-1:ℕ):ℝ)^((1 - 1/((k:ℝ)))) ≤ (m:ℝ)^((1 - 1/((k:ℝ)))) :=
              Real.rpow_le_rpow (by positivity) (by exact_mod_cast (by omega : m-1 ≤ m)) hthnn
            have hh := mul_le_mul_of_nonneg_left hHm (by positivity : (0:ℝ) ≤ CBX * (q:ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2))
            linarith [hh]
        _ ≤ A * (m:ℝ)^((1 - 1/((k:ℝ)))) := hfin
    · have hm1' : m = 1 := by omega
      subst hm1'
      have hmem : Finset.Icc 1 1 = {1} := by ext n; simp only [Finset.mem_Icc, Finset.mem_singleton]; omega
      rw [hmem, Finset.sum_singleton]
      have hχ1 : ‖χ ((1:ℕ):ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
      refine hχ1.trans ?_
      rw [show (((1:ℕ):ℝ))^((1 - 1/((k:ℝ)))) = 1 by simp]
      rw [mul_one, hAdef]
      have h1 : (1:ℝ) ≤ (q:ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2) := Real.one_le_rpow hqR1 (by positivity)
      have h2 : (1:ℝ) ≤ CBX + 1 := by linarith
      linarith only [h1, mul_nonneg hCBXpos.le (le_trans zero_le_one h1)]
  -- s
  set s : ℂ := (σ:ℂ) + (t:ℂ)*Complex.I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hs0 : 0 < s.re := by rw [hsre]; linarith
  have hsnorm : ‖s‖ ≤ 2 + |t| := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [hsre] at h
    have h1 : |s.im| = |t| := by simp [hsdef]
    have h2 : |σ| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; exact hσle
    rw [h1] at h; linarith only [h, h2]
  -- head
  have hQpow : (Q:ℝ)^μ ≤ 2*(q:ℝ)^(θ*μ) := by
    have h1 : (Q:ℝ)^μ ≤ (2*(q:ℝ)^θ)^μ := Real.rpow_le_rpow (by positivity) hQle hμ0
    have h2 : (2*(q:ℝ)^θ)^μ = 2^μ * (q:ℝ)^(θ*μ) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (le_of_lt hqRpos)]
    have h3 : (2:ℝ)^μ ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 2 by norm_num) (show μ ≤ 1 by linarith)
      simpa using this
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg (by positivity) _))
  have hQlog : 1 + Real.log (Q:ℝ) ≤ (1+Clog) * (q:ℝ)^(ε/2) := by
    have h1 : Real.log (Q:ℝ) ≤ Clog * (Q:ℝ)^(ε/2) := by
      simpa using hClog (Q:ℝ) (by exact_mod_cast hQ1)
    have h2 : (Q:ℝ)^(ε/2) ≤ (q:ℝ)^(ε/2) := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hQq) (by positivity)
    have h3 : (1:ℝ) ≤ (q:ℝ)^(ε/2) := Real.one_le_rpow hqR1 (by positivity)
    have h4 : Real.log (Q:ℝ) ≤ Clog * (q:ℝ)^(ε/2) :=
      le_trans h1 (mul_le_mul_of_nonneg_left h2 (le_of_lt hClogpos))
    linarith only [h3, h4]
  have hhead : ∑ n ∈ Finset.Icc 1 Q, (n:ℝ)^(-σ) ≤ (3+2*Clog) * (q:ℝ)^(θ*μ + ε/2) := by
    have h1 := sum_Icc_one_rpow_le hQ1 hμ0
    have hQμ1 : (1:ℝ) ≤ (Q:ℝ)^μ := Real.one_le_rpow (by exact_mod_cast hQ1) hμ0
    have hqexp : (1:ℝ) ≤ (q:ℝ)^(θ*μ + ε/2) := Real.one_le_rpow hqR1 (by positivity)
    have hpw : (q:ℝ)^(θ*μ) * (q:ℝ)^(ε/2) = (q:ℝ)^(θ*μ+ε/2) := (Real.rpow_add hqRpos _ _).symm
    calc ∑ n ∈ Finset.Icc 1 Q, (n:ℝ)^(-σ)
        = ∑ n ∈ Finset.Icc 1 Q, (n:ℝ)^(μ-1) := by
          apply Finset.sum_congr rfl; intro n hn; congr 1; rw [hμdef]; ring
      _ ≤ 1 + (Q:ℝ)^μ * (1 + Real.log (Q:ℝ)) := h1
      _ ≤ 1 + (2*(q:ℝ)^(θ*μ)) * ((1+Clog) * (q:ℝ)^(ε/2)) := by
          apply add_le_add le_rfl
          exact mul_le_mul hQpow hQlog (by positivity) (by positivity)
      _ = 1 + 2*(1+Clog) * ((q:ℝ)^(θ*μ) * (q:ℝ)^(ε/2)) := by ring
      _ = 1 + 2*(1+Clog) * (q:ℝ)^(θ*μ+ε/2) := by rw [hpw]
      _ ≤ (3+2*Clog) * (q:ℝ)^(θ*μ + ε/2) := by
          have hqnn : (0:ℝ) ≤ (q:ℝ)^(θ*μ+ε/2) := Real.rpow_nonneg (le_of_lt hqRpos) _
          have hClognn : (0:ℝ) ≤ Clog := le_of_lt hClogpos
          linarith only [hqexp]
  -- Chead
  have hhead2 : ∑ n ∈ Finset.Icc 1 Q, (n:ℝ)^(-σ) ≤ 3*(1+Clog) * (q:ℝ)^(θ*μ + ε/2) := by
    refine hhead.trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (le_of_lt hqRpos) _)
    linarith [hClogpos]
  have hqn1 : (0:ℝ) ≤ (q:ℝ) := le_of_lt hqRpos
  have hσeq : σ = 1 - μ := by rw [hμdef]; ring
  have hslack1 : θ*μ + ε/2 ≤ μ*(1+1/(k:ℝ))/4 + ε - δ := by
    have hkey : θ*μ = μ*(1+1/(k:ℝ))/4 := by
      rw [hθdef]; field_simp; try ring
    rw [hkey]
    linarith [hδε, hδ, hε]
  have hhead3 : ‖∑ n ∈ Finset.Icc 1 Q, χ n * (n:ℂ)^(-s)‖
      ≤ (3*(1+Clog)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by
    have h1 : ‖∑ n ∈ Finset.Icc 1 Q, χ n * (n:ℂ)^(-s)‖ ≤ ∑ n ∈ Finset.Icc 1 Q, (n:ℝ)^(-σ) := by
      refine le_trans (norm_sum_le _ _) ?_
      apply Finset.sum_le_sum; intro n hn
      rw [norm_mul, norm_natCast_cpow_eq s (by rw [Finset.mem_Icc] at hn; omega), hsre]
      exact mul_le_of_le_one_left (by positivity) (DirichletCharacter.norm_le_one χ _)
    have hqle1 : (q:ℝ)^(θ*μ+ε/2) ≤ (q:ℝ)^(μ*(1+1/(k:ℝ))/4+ε-δ) :=
      Real.rpow_le_rpow_of_exponent_le hqR1 hslack1
    have h2 : (3+2*Clog) * (q:ℝ)^(θ*μ+ε/2) ≤ (3*(1+Clog)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4+ε-δ) := by
      have hx : (0:ℝ) ≤ (q:ℝ)^(θ*μ+ε/2) := Real.rpow_nonneg hqn1 _
      have hcoef : (3+2*Clog) ≤ 3*(1+Clog) := by linarith [hClogpos]
      have hrhs : (0:ℝ) ≤ 3*(1+Clog) := by linarith [hClogpos]
      exact mul_le_mul hcoef hqle1 hx hrhs
    have ht1 : (1:ℝ) ≤ 1+|t| := by have := abs_nonneg t; linarith
    calc ‖∑ n ∈ Finset.Icc 1 Q, χ n * (n:ℂ)^(-s)‖ ≤ ∑ n ∈ Finset.Icc 1 Q, (n:ℝ)^(-σ) := h1
      _ ≤ (3+2*Clog) * (q:ℝ)^(θ*μ + ε/2) := hhead
      _ ≤ (3*(1+Clog)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) := h2
      _ ≤ (3*(1+Clog)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by
          rw [mul_assoc]; exact le_mul_of_one_le_right (by positivity) ht1
  have hσ23 : (1 - 1/((k:ℝ))) ≤ s.re := by rw [hsre]; linarith [hσ1, hkR]
  have hδ' : (0:ℝ) < (ε/8) := by positivity
  -- middle bound
  have hmid : ∀ R : ℕ, Q+1 ≤ R → R ≤ q →
      ‖∑ n ∈ Finset.Icc (Q+1) R, χ n * (n:ℂ)^(-s)‖
        ≤ (4*(1+Clog2)*(CBX+1)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by
    intro R hQR hRq
    have hPreR : ∀ m : ℕ, Q ≤ m → m ≤ R → ‖∑ k ∈ Finset.Icc 1 m, χ k‖ ≤ A * (m:ℝ)^((1 - 1/((k:ℝ)))) :=
      fun m hm1 hm2 => hPre m (by omega) (by omega)
    have hh := abel_exp_log (le_of_lt hApos) (1 - 1/((k:ℝ))) (by linarith [hkR]) hs0
      (by rw [hsre]; exact hσ1) hQ1 hQR
      (a := fun n => χ n) hPreR
    have hQpow : (Q:ℝ)^((1 - 1/((k:ℝ))) - s.re) ≤ (q:ℝ)^(θ*((1 - 1/((k:ℝ))) - σ)) := by
      rw [hsre]
      have hle := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hqRpos θ) hQge
        (show (1 - 1/((k:ℝ))) - σ ≤ 0 by linarith [hσ23])
      rwa [← Real.rpow_mul hqn1] at hle
    have hlogR : (1:ℝ) + Real.log (R:ℝ) ≤ (1+Clog2) * (q:ℝ)^((ε/8)) := by
      have h1 : Real.log (R:ℝ) ≤ Clog2 * (R:ℝ)^((ε/8)) := by
        simpa using hClog2 (R:ℝ) (by exact_mod_cast (by omega : 1 ≤ R))
      have h2 : (R:ℝ)^((ε/8)) ≤ (q:ℝ)^((ε/8)) :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast hRq) (by positivity)
      have h3 : (1:ℝ) ≤ (q:ℝ)^((ε/8)) := Real.one_le_rpow hqR1 (le_of_lt hδ')
      have h4 : Real.log (R:ℝ) ≤ Clog2 * (q:ℝ)^((ε/8)) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 (le_of_lt hClog2pos))
      linarith only [h3, h4]
    have hY1 : (1:ℝ) ≤ (1+Clog2)*(q:ℝ)^((ε/8)) := by
      have h3 : (1:ℝ) ≤ (q:ℝ)^((ε/8)) := Real.one_le_rpow hqR1 (le_of_lt hδ')
      linarith only [h3, mul_nonneg hClog2pos.le (le_trans zero_le_one h3)]
    have hY0 : (0:ℝ) ≤ (1+Clog2)*(q:ℝ)^((ε/8)) := by positivity
    have hsn' : ‖s‖ ≤ 2*(1+|t|) := by linarith only [hsnorm, abs_nonneg t]
    have hYbound : (2:ℝ) + ‖s‖*((1+Clog2)*(q:ℝ)^((ε/8)))
        ≤ 4*(1+Clog2)*(q:ℝ)^((ε/8))*(1+|t|) := by
      have h4 : ‖s‖*((1+Clog2)*(q:ℝ)^((ε/8))) ≤ 2*(1+|t|)*((1+Clog2)*(q:ℝ)^((ε/8))) :=
        mul_le_mul_of_nonneg_right hsn' hY0
      have ht1 : (1:ℝ) ≤ 1+|t| := by have := abs_nonneg t; linarith
      have hY2 : (0:ℝ) ≤ (q:ℝ)^((ε/8)) := Real.rpow_nonneg hqn1 _
      linarith only [h4, mul_le_mul hY1 ht1 zero_le_one hY0]
    have hE : ((((k:ℝ)+1)/(4*((k:ℝ))^2)) + ε/2) + θ*((1 - 1/((k:ℝ))) - σ) + (ε/8)
        ≤ μ*(1+1/(k:ℝ))/4 + ε - δ := by
      have hkey : ((((k:ℝ)+1)/(4*((k:ℝ))^2))) + θ*((1 - 1/((k:ℝ))) - σ) = μ*(1+1/(k:ℝ))/4 := by
        rw [hσeq, hθdef]; field_simp; ring
      linarith [hkey, hδε, hδ, hε]
    have hcomb : A * (q:ℝ)^(θ*((1 - 1/((k:ℝ))) - σ))
        = (CBX+1) * (q:ℝ)^(((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2)+θ*((1 - 1/((k:ℝ)))-σ)) := by
      rw [hAdef, mul_assoc, ← Real.rpow_add hqRpos]
    have hrr : A * (q:ℝ)^(θ*((1 - 1/((k:ℝ))) - σ)) * (4*(1+Clog2)*(q:ℝ)^((ε/8))*(1+|t|))
        = (4*(1+Clog2)*(CBX+1)) * (q:ℝ)^(((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2)+θ*((1 - 1/((k:ℝ))) - σ) + (ε/8)) * (1+|t|) := by
      calc A * (q:ℝ)^(θ*((1 - 1/((k:ℝ))) - σ)) * (4*(1+Clog2)*(q:ℝ)^((ε/8))*(1+|t|))
          = (CBX+1) * (q:ℝ)^(((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2)+θ*((1 - 1/((k:ℝ)))-σ)) * (4*(1+Clog2)*(q:ℝ)^((ε/8))*(1+|t|)) := by
            rw [hcomb]
        _ = (CBX+1) * ((q:ℝ)^(((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2)+θ*((1 - 1/((k:ℝ)))-σ)) * (q:ℝ)^((ε/8))) * (4*(1+Clog2)*(1+|t|)) := by ring
        _ = (CBX+1) * (q:ℝ)^(((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2)+θ*((1 - 1/((k:ℝ)))-σ) + (ε/8)) * (4*(1+Clog2)*(1+|t|)) := by
            rw [← Real.rpow_add hqRpos]
        _ = (4*(1+Clog2)*(CBX+1)) * (q:ℝ)^(((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2)+θ*((1 - 1/((k:ℝ)))-σ) + (ε/8)) * (1+|t|) := by ring
    have hstep : A * (q:ℝ)^(θ*((1 - 1/((k:ℝ))) - σ)) * (2 + ‖s‖*((1+Clog2)*(q:ℝ)^((ε/8))))
        ≤ (4*(1+Clog2)*(CBX+1)) * (q:ℝ)^(((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2)+θ*((1 - 1/((k:ℝ))) - σ) + (ε/8)) * (1+|t|) := by
      calc A * (q:ℝ)^(θ*((1 - 1/((k:ℝ))) - σ)) * (2 + ‖s‖*((1+Clog2)*(q:ℝ)^((ε/8))))
          ≤ A * (q:ℝ)^(θ*((1 - 1/((k:ℝ))) - σ)) * (4*(1+Clog2)*(q:ℝ)^((ε/8))*(1+|t|)) :=
            mul_le_mul le_rfl hYbound (by positivity) (by positivity)
        _ = _ := hrr
    calc ‖∑ n ∈ Finset.Icc (Q+1) R, χ n * (n:ℂ)^(-s)‖
        ≤ A * (Q:ℝ)^((1 - 1/((k:ℝ))) - s.re) * (2 + ‖s‖*(1+Real.log (R:ℝ))) := hh
      _ ≤ A * (q:ℝ)^(θ*((1 - 1/((k:ℝ))) - σ)) * (2 + ‖s‖*((1+Clog2)*(q:ℝ)^((ε/8)))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hQpow (le_of_lt hApos))
            (add_le_add le_rfl (mul_le_mul_of_nonneg_left hlogR (norm_nonneg s))) (by positivity) (by positivity)
      _ ≤ (4*(1+Clog2)*(CBX+1)) * (q:ℝ)^(((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2)+θ*((1 - 1/((k:ℝ))) - σ) + (ε/8)) * (1+|t|) := hstep
      _ ≤ (4*(1+Clog2)*(CBX+1)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by
          have hq2 := Real.rpow_le_rpow_of_exponent_le hqR1 hE
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq2 (by positivity)) (by positivity)
  -- tail bound
  have hPV : ∀ x y : ℕ, x ≤ y → ‖∑ n ∈ Finset.Icc x y, χ n‖ ≤ 2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ) := by
    intro x y hxy
    have h1 : ‖∑ n ∈ Finset.range (y+1), χ n‖ ≤ CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ) := hCPV q hq2 χ hχ y
    have h2 : ‖∑ n ∈ Finset.range x, χ n‖ ≤ CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ) := by
      rcases Nat.eq_zero_or_pos x with hx | hx
      · subst hx; simp; positivity
      · have h := hCPV q hq2 χ hχ (x-1)
        rwa [show x-1+1 = x by omega] at h
    have hsplit : ∑ n ∈ Finset.Icc x y, χ n = (∑ n ∈ Finset.range (y+1), χ n) - ∑ n ∈ Finset.range x, χ n := by
      have hun : Finset.range (y+1) = Finset.range x ∪ Finset.Icc x y := by
        ext n; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Icc]; omega
      have hdisj : Disjoint (Finset.range x) (Finset.Icc x y) := by
        rw [Finset.disjoint_left]; intro n h1 h2
        rw [Finset.mem_range] at h1; rw [Finset.mem_Icc] at h2; omega
      rw [hun, Finset.sum_union hdisj]; ring
    rw [hsplit]
    exact (norm_sub_le _ _).trans (by linarith only [h1, h2])
  have hlogqq : Real.log (q:ℝ) ≤ (1+Clog2)*(q:ℝ)^((ε/8)) := by
    have h1 : Real.log (q:ℝ) ≤ Clog2 * (q:ℝ)^((ε/8)) := by simpa using hClog2 (q:ℝ) hqR1
    linarith only [h1, Real.rpow_nonneg hqn1 ((ε/8))]
  have hσinv : (1:ℝ) + ‖s‖/σ ≤ 4*(1+|t|) := by
    have h2 : ‖s‖/s.re ≤ (2+|t|)/(2/3) :=
      div_le_div₀ (by positivity) hsnorm (by norm_num) (by linarith [hσ23])
    rw [hsre] at h2
    linarith only [h2, abs_nonneg t]
  have htail : ∀ M : ℕ, q < M →
      ‖∑ n ∈ Finset.Icc (q+1) M, χ n * (n:ℂ)^(-s)‖
        ≤ (14*CPV*(1+Clog2)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by
    intro M hqM
    have hh := Commons.Analysis.Asymptotics.abel_tail_bound_finite
      (2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ)) hPV s hs0 (N := q+1) (M := M) (by omega) (by omega)
    have hBnn : (0:ℝ) ≤ 2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ) := by
      have h1 : (0:ℝ) ≤ Real.log (q:ℝ) := Real.log_nonneg hqR1
      positivity
    have hstep0 : (2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ)) * ((q+1:ℕ):ℝ)^(-s.re)
        ≤ (2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ)) * (q:ℝ)^(-s.re) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hqRpos (by exact_mod_cast (by omega : q ≤ q+1)) (by rw [hsre]; linarith [hs0])) hBnn
    have hexp_t : (1:ℝ)/2 - σ + (ε/8) ≤ μ*(1+1/(k:ℝ))/4 + ε - δ := by
      have h1 : (1:ℝ)/2 - σ ≤ -1/6 := by linarith [h1k, hσ1]
      have h3 : (0:ℝ) ≤ μ*(1+1/(k:ℝ))/4 := by positivity
      have h4 : ε/2 ≤ ε - δ := by linarith [hδε]
      linarith [h1, h3, h4, hδ, hε]
    have hq3 : (q:ℝ)^((1:ℝ)/2 - σ + (ε/8)) ≤ (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) :=
      Real.rpow_le_rpow_of_exponent_le hqR1 hexp_t
    have hstep1 : (2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ)) * (q:ℝ)^(-s.re) * (1+‖s‖/s.re)
        ≤ 8*CPV*(1+Clog2)*(q:ℝ)^((1:ℝ)/2 - σ + (ε/8))*(1+|t|) := by
      rw [hsre, Real.sqrt_eq_rpow]
      have hAq : 2*CPV*(q:ℝ)^((1:ℝ)/2)*Real.log (q:ℝ)
          ≤ 2*CPV*(q:ℝ)^((1:ℝ)/2)*((1+Clog2)*(q:ℝ)^((ε/8))) :=
        mul_le_mul_of_nonneg_left hlogqq (by positivity)
      have h5 : 2*CPV*(q:ℝ)^((1:ℝ)/2)*Real.log (q:ℝ)*(q:ℝ)^(-σ)
          ≤ 2*CPV*(q:ℝ)^((1:ℝ)/2)*((1+Clog2)*(q:ℝ)^((ε/8)))*(q:ℝ)^(-σ) :=
        mul_le_mul_of_nonneg_right hAq (Real.rpow_nonneg hqn1 _)
      have h6 : (0:ℝ) ≤ 2*CPV*(q:ℝ)^((1:ℝ)/2)*((1+Clog2)*(q:ℝ)^((ε/8)))*(q:ℝ)^(-σ) := by positivity
      have h7 := mul_le_mul h5 hσinv (by
        have hσpos : (0:ℝ) < σ := by linarith [hσ23]
        positivity) h6
      have hrr : (q:ℝ)^((1:ℝ)/2) * (q:ℝ)^((ε/8)) * (q:ℝ)^(-σ)
          = (q:ℝ)^((1:ℝ)/2 - σ + (ε/8)) := by
        rw [← Real.rpow_add hqRpos, ← Real.rpow_add hqRpos]
        congr 1; ring
      calc 2*CPV*(q:ℝ)^((1:ℝ)/2)*Real.log (q:ℝ)*(q:ℝ)^(-σ)*(1+‖s‖/σ)
          ≤ 2*CPV*(q:ℝ)^((1:ℝ)/2)*((1+Clog2)*(q:ℝ)^((ε/8)))*(q:ℝ)^(-σ)*(4*(1+|t|)) := h7
        _ = 8*CPV*(1+Clog2)*((q:ℝ)^((1:ℝ)/2)*(q:ℝ)^((ε/8))*(q:ℝ)^(-σ))*(1+|t|) := by ring
        _ = 8*CPV*(1+Clog2)*(q:ℝ)^((1:ℝ)/2 - σ + (ε/8))*(1+|t|) := by rw [hrr]
    calc ‖∑ n ∈ Finset.Icc (q+1) M, χ n * (n:ℂ)^(-s)‖
        ≤ (2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ)) * ((q+1:ℕ):ℝ)^(-s.re) * (1+‖s‖/s.re) := hh
      _ ≤ (2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ)) * (q:ℝ)^(-s.re) * (1+‖s‖/s.re) :=
          mul_le_mul_of_nonneg_right hstep0 (by positivity)
      _ ≤ 8*CPV*(1+Clog2)*(q:ℝ)^((1:ℝ)/2 - σ + (ε/8))*(1+|t|) := hstep1
      _ ≤ 8*CPV*(1+Clog2)*(q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ)*(1+|t|) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq3 (by positivity)) (by positivity)
      _ ≤ (14*CPV*(1+Clog2)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by
          have h4 : (0:ℝ) ≤ (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by positivity
          have h5 : (8:ℝ)*CPV*(1+Clog2) ≤ 14*CPV*(1+Clog2) := by
            linarith only [mul_nonneg hCPVpos.le (by linarith only [hClog2pos] : (0:ℝ) ≤ 1 + Clog2)]
          calc 8*CPV*(1+Clog2)*(q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ)*(1+|t|)
              = (8*CPV*(1+Clog2)) * ((q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ)*(1+|t|)) := by ring
            _ ≤ (14*CPV*(1+Clog2)) * ((q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ)*(1+|t|)) :=
                mul_le_mul_of_nonneg_right h5 h4
            _ = (14*CPV*(1+Clog2)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by ring
  -- per-M bound
  have hBig : (3*(1+Clog) + 4*(1+Clog2)*(CBX+1) + 14*CPV*(1+Clog2))
      ≤ 3 * (3*(1+Clog) + 4*(1+Clog2)*(CBX+1) + 14*CPV*(1+Clog2)) + 1 := by
    have h4 : (0:ℝ) ≤ 3*(1+Clog) + 4*(1+Clog2)*(CBX+1) + 14*CPV*(1+Clog2) := by positivity
    linarith only [h4]
  have hPerM : ∀ M : ℕ, ‖∑ n ∈ Finset.Icc 1 M, χ n * (n:ℂ)^(-s)‖
      ≤ (3*(1+Clog) + 4*(1+Clog2)*(CBX+1) + 14*CPV*(1+Clog2))
          * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by
    intro M
    have hTpos : (0:ℝ) ≤ (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by positivity
    by_cases hMQ : M ≤ Q
    · have h1 : ‖∑ n ∈ Finset.Icc 1 M, χ n * (n:ℂ)^(-s)‖ ≤ ∑ n ∈ Finset.Icc 1 Q, (n:ℝ)^(-σ) := by
        refine le_trans (norm_sum_le _ _) ?_
        calc ∑ n ∈ Finset.Icc 1 M, ‖χ n * (n:ℂ)^(-s)‖
            ≤ ∑ n ∈ Finset.Icc 1 M, (n:ℝ)^(-σ) := by
              apply Finset.sum_le_sum; intro n hn
              rw [norm_mul, norm_natCast_cpow_eq s (by rw [Finset.mem_Icc] at hn; omega), hsre]
              exact mul_le_of_le_one_left (by positivity) (DirichletCharacter.norm_le_one χ _)
          _ ≤ ∑ n ∈ Finset.Icc 1 Q, (n:ℝ)^(-σ) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro n hn; rw [Finset.mem_Icc] at hn ⊢; omega
              · intro n hn _; positivity
      have h2 : ∑ n ∈ Finset.Icc 1 Q, (n:ℝ)^(-σ) ≤ (3*(1+Clog)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) := by
        refine hhead2.trans ?_
        have hqle1 : (q:ℝ)^(θ*μ+ε/2) ≤ (q:ℝ)^(μ*(1+1/(k:ℝ))/4+ε-δ) :=
          Real.rpow_le_rpow_of_exponent_le hqR1 hslack1
        exact mul_le_mul_of_nonneg_left hqle1 (by positivity)
      refine (h1.trans h2).trans ?_
      have hk1 : (3*(1+Clog)) ≤ 3*(1+Clog) + 4*(1+Clog2)*(CBX+1) + 14*CPV*(1+Clog2) := by
        have h2 : (0:ℝ) ≤ 4*(1+Clog2)*(CBX+1) + 14*CPV*(1+Clog2) := by positivity
        linarith only [h2]
      calc (3*(1+Clog)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ)
          ≤ (3*(1+Clog) + 4*(1+Clog2)*(CBX+1) + 14*CPV*(1+Clog2)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) :=
            mul_le_mul_of_nonneg_right hk1 (Real.rpow_nonneg hqn1 _)
        _ ≤ (3*(1+Clog) + 4*(1+Clog2)*(CBX+1) + 14*CPV*(1+Clog2))
            * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by
            have ht1 : (1:ℝ) ≤ 1+|t| := by have := abs_nonneg t; linarith
            rw [mul_assoc]; exact le_mul_of_one_le_right (by positivity) ht1
    · have hMQ' : Q ≤ M := le_of_lt (lt_of_not_ge hMQ)
      have hsplit1 : ∑ n ∈ Finset.Icc 1 M, χ n * (n:ℂ)^(-s)
          = ∑ n ∈ Finset.Icc 1 Q, χ n * (n:ℂ)^(-s) + ∑ n ∈ Finset.Ioc Q M, χ n * (n:ℂ)^(-s) :=
        sum_Icc_split hMQ' _
      rw [hsplit1]
      have hQR : Q ≤ min M q := le_min hMQ' hQq
      have hRM : min M q ≤ M := min_le_left _ _
      have hsplit2 : ∑ n ∈ Finset.Ioc Q M, χ n * (n:ℂ)^(-s)
          = ∑ n ∈ Finset.Ioc Q (min M q), χ n * (n:ℂ)^(-s)
            + ∑ n ∈ Finset.Ioc (min M q) M, χ n * (n:ℂ)^(-s) :=
        sum_Ioc_split hQR hRM _
      rw [hsplit2]
      have hmid' : ‖∑ n ∈ Finset.Ioc Q (min M q), χ n * (n:ℂ)^(-s)‖
          ≤ (4*(1+Clog2)*(CBX+1)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by
        rcases lt_or_ge Q (min M q) with hQR' | hQR'
        · have hIcc : Finset.Ioc Q (min M q) = Finset.Icc (Q+1) (min M q) := by
            ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
          rw [hIcc]; exact hmid (min M q) (by omega) (min_le_right _ _)
        · have hz : ∑ n ∈ Finset.Ioc Q (min M q), χ n * (n:ℂ)^(-s) = 0 :=
            Finset.sum_eq_zero (fun n hn => by rw [Finset.mem_Ioc] at hn; omega)
          rw [hz, norm_zero]; positivity
      have htail' : ‖∑ n ∈ Finset.Ioc (min M q) M, χ n * (n:ℂ)^(-s)‖
          ≤ (14*CPV*(1+Clog2)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by
        rcases lt_or_ge (min M q) M with hRM' | hRM'
        · have hRq : min M q = q := by omega
          rw [hRq] at hRM'
          rw [hRq]
          have hIcc : Finset.Ioc q M = Finset.Icc (q+1) M := by
            ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
          rw [hIcc]; exact htail M hRM'
        · have hz : ∑ n ∈ Finset.Ioc (min M q) M, χ n * (n:ℂ)^(-s) = 0 :=
            Finset.sum_eq_zero (fun n hn => by rw [Finset.mem_Ioc] at hn; omega)
          rw [hz, norm_zero]; positivity
      calc ‖(∑ n ∈ Finset.Icc 1 Q, χ n * (n:ℂ)^(-s))
            + ((∑ n ∈ Finset.Ioc Q (min M q), χ n * (n:ℂ)^(-s))
              + ∑ n ∈ Finset.Ioc (min M q) M, χ n * (n:ℂ)^(-s))‖
          ≤ ‖∑ n ∈ Finset.Icc 1 Q, χ n * (n:ℂ)^(-s)‖
            + ‖(∑ n ∈ Finset.Ioc Q (min M q), χ n * (n:ℂ)^(-s))
              + ∑ n ∈ Finset.Ioc (min M q) M, χ n * (n:ℂ)^(-s)‖ := norm_add_le _ _
        _ ≤ ‖∑ n ∈ Finset.Icc 1 Q, χ n * (n:ℂ)^(-s)‖
            + (‖∑ n ∈ Finset.Ioc Q (min M q), χ n * (n:ℂ)^(-s)‖
              + ‖∑ n ∈ Finset.Ioc (min M q) M, χ n * (n:ℂ)^(-s)‖) :=
              add_le_add le_rfl (norm_add_le _ _)
        _ ≤ (3*(1+Clog)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|)
            + ((4*(1+Clog2)*(CBX+1)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|)
              + (14*CPV*(1+Clog2)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|)) :=
              add_le_add hhead3 (add_le_add hmid' htail')
        _ ≤ (3*(1+Clog) + 4*(1+Clog2)*(CBX+1) + 14*CPV*(1+Clog2))
            * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by
              exact le_of_eq (by ring)
  have hlim := LSeries_partial_sums_tendsto χ hχ hs0
  have hnormlim : Filter.Tendsto (fun M : ℕ => ‖∑ n ∈ Finset.Icc 1 M, χ n * (n:ℂ)^(-s)‖)
      Filter.atTop (nhds ‖χ.LFunction s‖) := hlim.norm
  have hfin := le_of_tendsto' hnormlim hPerM
  rw [show ((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε - δ = μ*(1+1/(k:ℝ))/4 + ε - δ by
    rw [hμdef]; ring]
  have hXnn : (0:ℝ) ≤ (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by positivity
  have hstep : ‖χ.LFunction s‖ ≤
      (3 * (3*(1+Clog) + 4*(1+Clog2)*(CBX+1) + 14*CPV*(1+Clog2)) + 1)
        * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by
    linarith only [hfin, mul_le_mul_of_nonneg_right hBig hXnn]
  refine hstep.trans ?_
  -- the per-character constant still carries the order factor `u ≥ 1`; this cancels the growth
  have hspec : 3*(1+Clog) + 4*(1+Clog2)*(CBX+1) + 14*CPV*(1+Clog2)
      ≤ (3*(1+Clog) + 4*(1+Clog2)*(CB+1) + 14*CPV*(1+Clog2)) * u := by
    rw [hCBXdef]
    have h1 : 3*(1+Clog) ≤ 3*(1+Clog) * u := le_mul_of_one_le_right (by positivity) hu1
    have h3 : 14*CPV*(1+Clog2) ≤ 14*CPV*(1+Clog2) * u := le_mul_of_one_le_right (by positivity) hu1
    have h2 : 4*(1+Clog2)*(CB*u+1) ≤ 4*(1+Clog2)*(CB+1) * u := by
      have hA : CB*u + 1 ≤ (CB+1)*u := by linarith only [hu1]
      calc 4*(1+Clog2)*(CB*u+1) ≤ 4*(1+Clog2)*((CB+1)*u) :=
            mul_le_mul_of_nonneg_left hA (by positivity)
        _ = 4*(1+Clog2)*(CB+1) * u := by ring
    linarith only [h1, h2, h3]
  have hK : 3 * (3*(1+Clog) + 4*(1+Clog2)*(CBX+1) + 14*CPV*(1+Clog2)) + 1
      ≤ (3 * (3*(1+Clog) + 4*(1+Clog2)*(CB+1) + 14*CPV*(1+Clog2)) + 1) * u := by
    linarith only [hspec, hu1]
  have hqEnn : (0:ℝ) ≤ (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) := Real.rpow_nonneg (by positivity) _
  have htnn : (0:ℝ) ≤ 1 + |t| := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK hqEnn) htnn

end Commons.NumberTheory.DirichletCharacter

namespace Work.LinnikAreas

/-- **HB Lemma 2.5 with `φ = 1/4`, keeping the order of the character explicit.**

Given the cube-free Burgess input `hB` for a primitive non-principal character of cube-free
modulus, we obtain the `φ = 1/4` bound for the L-function of *every* primitive non-principal
character, with the order factor `(ord χ)^{3/(2k)}` made explicit and no restriction on the
order (in particular no `ord χ ≤ log q` hypothesis).

Two ingredients:

* `burgess_charSum_order_of_cubefree` converts `hB` (cube-free moduli) into the character-sum
  bound `≪ (ord χ)^{3/(2k)} q^{((k+1)/(4k²))+ε/4} H^{1-1/k}` for *all* moduli: the cube-full part
  `v` of `q` is absorbed by `(ord χ)^{3/(2k)}` since `v ≤ (2 ord χ)²`.
* `primitive_quarter_charConst` (above) is Heath-Brown's §2 partial-summation argument run with
  this character-dependent constant, which propagates the order factor into the L-function bound.

For `σ ≥ 1` the crude bound `L(σ+it,χ) ≪ (1+log q)(1+|t|)` combined with
`crude_absorb_quarter` gives the same shape, the (superfluous) order factor being `≥ 1`. -/
theorem primitive_LFunction_quarter_order {ε : ℝ} (hε : 0 < ε) (k : ℕ) (hk : 3 ≤ k)
    {CB : ℝ} (hCB : 0 < CB)
    (hB : ∀ {u : ℕ} [NeZero u] (ψ : DirichletCharacter ℂ u), ψ.IsPrimitive → ψ ≠ 1 →
      (∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ u) →
      ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ u →
        ‖∑ n ∈ Finset.Ioc N (N + H), ψ n‖ ≤
          CB * (u : ℝ) ^ ((((k : ℝ) + 1) / (4 * (k : ℝ) ^ 2)) + ε / 4)
            * (H : ℝ) ^ (1 - 1 / (k : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 →
      ∀ σ t : ℝ, 1 - 1 / (k : ℝ) ≤ σ →
        σ ≤ 1 + Real.log (Real.log (q : ℝ)) / Real.log (q : ℝ) →
        ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C * (orderOf χ : ℝ) ^ ((3 : ℝ) / (2 * (k : ℝ)))
            * (q : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε)
            * (1 + |t|) := by
  have hε4 : (0 : ℝ) < ε / 4 := by positivity
  have hε2 : (0 : ℝ) < ε / 2 := by positivity
  have hε8 : (0 : ℝ) < ε / 8 := by positivity
  -- (1) cube-free Burgess input ⟹ character sums with an order factor, for every modulus
  obtain ⟨C1, hC1pos, hC1⟩ :=
    Commons.NumberTheory.DirichletCharacter.burgess_charSum_order_of_cubefree
      (ε := ε / 4) hε4 k (by omega) hCB hB
  -- (2) the `φ = 1/4` chain in the range `σ ≤ 1`, carrying the order factor
  obtain ⟨C2, hC2pos, hC2⟩ :=
    Commons.NumberTheory.DirichletCharacter.primitive_quarter_charConst
      (ε := ε / 2) (δ := ε / 8) k hk hε2 hε8 (by linarith) hC1pos
  -- (3) crude bounds for `σ ≥ 1`
  obtain ⟨Cc, hCcpos, hCc⟩ := Commons.NumberTheory.DirichletCharacter.LFunction_crude_bound
  obtain ⟨Cf, hCfpos, hCf⟩ :=
    Commons.NumberTheory.DirichletCharacter.crude_absorb_quarter hk hε
  refine ⟨max C2 (Cc * Cf) + 1, by positivity, ?_⟩
  intro q _inst χ hprim hχ σ t hσlo hσhi
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have hqnn : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hnsnn : (0 : ℝ) ≤ (orderOf χ : ℝ) ^ ((3 : ℝ) / (2 * (k : ℝ))) := by positivity
  have hns1 : (1 : ℝ) ≤ (orderOf χ : ℝ) ^ ((3 : ℝ) / (2 * (k : ℝ))) := by
    refine Real.one_le_rpow ?_ (by positivity)
    have h1 : (1 : ℕ) ≤ orderOf χ := Nat.one_le_iff_ne_zero.mpr (ne_of_gt (orderOf_pos χ))
    exact_mod_cast h1
  have hmax1 : C2 ≤ max C2 (Cc * Cf) + 1 := by linarith [le_max_left C2 (Cc * Cf)]
  have hmax2 : Cc * Cf ≤ max C2 (Cc * Cf) + 1 := by linarith [le_max_right C2 (Cc * Cf)]
  by_cases hcase : σ ≤ 1
  · -- `σ ≤ 1`: Heath-Brown's §2 argument (three ranges), with the order factor
    have hcharSum : ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ q →
        ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤
          C1 * (orderOf χ : ℝ) ^ ((3 : ℝ) / (2 * (k : ℝ)))
            * (q : ℝ) ^ (((k : ℝ) + 1) / (4 * (k : ℝ) ^ 2) + ε / 2 / 2)
            * (H : ℝ) ^ (1 - 1 / (k : ℝ)) := by
      intro N H hN hH hHq
      have h := hC1 (q := q) χ hprim hχ hN hH hHq
      rwa [show (ε : ℝ) / 4 = ε / 2 / 2 by ring] at h
    have hb := hC2 q χ hprim hχ hcharSum σ t hσlo hcase
    have hexp : ((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε / 2 - ε / 8
        ≤ ((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε := by linarith
    have hqE : (q : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε / 2 - ε / 8)
        ≤ (q : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε) :=
      Real.rpow_le_rpow_of_exponent_le hq1 hexp
    have hA : C2 * (orderOf χ : ℝ) ^ ((3 : ℝ) / (2 * (k : ℝ)))
          * (q : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε / 2 - ε / 8)
        ≤ (max C2 (Cc * Cf) + 1) * (orderOf χ : ℝ) ^ ((3 : ℝ) / (2 * (k : ℝ)))
          * (q : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε) := by
      have h1 : C2 * (orderOf χ : ℝ) ^ ((3 : ℝ) / (2 * (k : ℝ)))
          ≤ (max C2 (Cc * Cf) + 1) * (orderOf χ : ℝ) ^ ((3 : ℝ) / (2 * (k : ℝ))) :=
        mul_le_mul_of_nonneg_right hmax1 hnsnn
      exact (mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hqnn _)).trans
        (mul_le_mul_of_nonneg_left hqE (by positivity))
    calc ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C2 * (orderOf χ : ℝ) ^ ((3 : ℝ) / (2 * (k : ℝ)))
            * (q : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε / 2 - ε / 8)
            * (1 + |t|) := hb
      _ ≤ (max C2 (Cc * Cf) + 1) * (orderOf χ : ℝ) ^ ((3 : ℝ) / (2 * (k : ℝ)))
            * (q : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε)
            * (1 + |t|) := mul_le_mul_of_nonneg_right hA (by positivity)
  · -- `σ ≥ 1`: the crude bound, cast in the same shape
    have hσge : 1 ≤ σ := le_of_lt (lt_of_not_ge hcase)
    have hcb := hCc q χ hχ σ t hσge
    have hca := hCf q (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) σ hσge hσhi
    have hE2nn : (0 : ℝ) ≤ (q : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε) :=
      Real.rpow_nonneg hqnn _
    have hA : (Cc * Cf) * (q : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε)
        ≤ (max C2 (Cc * Cf) + 1) * (orderOf χ : ℝ) ^ ((3 : ℝ) / (2 * (k : ℝ)))
          * (q : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε) := by
      have h1 : (Cc * Cf) * (q : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε)
          ≤ (max C2 (Cc * Cf) + 1) * (q : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε) :=
        mul_le_mul_of_nonneg_right hmax2 hE2nn
      have h3 : (max C2 (Cc * Cf) + 1)
          ≤ (max C2 (Cc * Cf) + 1) * (orderOf χ : ℝ) ^ ((3 : ℝ) / (2 * (k : ℝ))) :=
        le_mul_of_one_le_right (by positivity) hns1
      have h2 : (max C2 (Cc * Cf) + 1) * (q : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε)
          ≤ (max C2 (Cc * Cf) + 1) * (orderOf χ : ℝ) ^ ((3 : ℝ) / (2 * (k : ℝ)))
            * (q : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε) :=
        mul_le_mul_of_nonneg_right h3 hE2nn
      exact h1.trans h2
    calc ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ Cc * (1 + Real.log (q : ℝ)) * (1 + |t|) := hcb
      _ ≤ Cc * (Cf * (q : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε)) * (1 + |t|) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hca (le_of_lt hCcpos))
            (by positivity)
      _ = (Cc * Cf) * (q : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε)
            * (1 + |t|) := by ring
      _ ≤ (max C2 (Cc * Cf) + 1) * (orderOf χ : ℝ) ^ ((3 : ℝ) / (2 * (k : ℝ)))
            * (q : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε)
            * (1 + |t|) := mul_le_mul_of_nonneg_right hA (by positivity)

end Work.LinnikAreas

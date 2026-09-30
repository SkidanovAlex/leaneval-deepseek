import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.weyl_inverse
import Submission.Work.BMF.discretise
import Submission.Work.BMF.scale_down
import Submission.Work.BMF.quaddata_stage
import Submission.Work.BMF.discretise
import Submission.Work.BMF.scale_down
import Submission.Work.BMF.quaddata_stage

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/BMF/DESIGN.md (the lead's design for MRTTZ; your node's section has exact formulas). Shared definitions: Submission/Work/BMF/Defs.lean (do NOT edit). Owned library assets are being installed now (see Submission/Work/BMF/ASSETS.md once it exists, and DESIGN.md §8); import them instead of re-proving. Sibling nodes you import are proved in parallel; build against their statements.

# N3 `build_quadruples`: discretise, Turán–Kubilius scaling-down, quadruple graph

**Sources.**
- MRT (1812.01224) Lemma 2.1, Prop. 2.5, Props. 3.1–3.2 (sources in `papers/`).
- MRTTZ Props. 3.3–3.6 (large sieve for polynomial phases, scaling down, CRT, building the family).

**Imports.** `Submission.Work.BMF.Defs`, `Submission.Work.BMF.weyl_inverse` (N2).
**Owned assets.** None needed beyond Mathlib. The large-sieve step uses N2 only.

## Route

**0. From the formal integrand.** For `x ≥ 1`, the sum
`Σ_{n ∈ Icc ⌈x⌉ ⌊x+H⌋ ⊆ ℤ} f.intExtension n · e(−P n)` equals `corr f P x H`.

The integrand is a step function of `x`: it depends only on `(⌈x⌉, ⌊x+H⌋)`. It is bounded by
`(H+1)/H ≤ 2`. If it were not integrable, the integral would be `0 < ηX`, so the hypothesis gives
integrability.

**1. Discretise (MRT Lemma 2.1).**
- Pigeonhole a shift `y ∈ [0, H)`.
- Take every 500th block `((500ℓ+v)H + y, (500ℓ+v+1)H + y]`.
- The `sup` over `P` is attained up to a factor 2, so pick `P_I` with `|corr f P_I x_I H| ≥ ηH/2`
  for `≥ ηX/(1000H)` intervals.

This gives an `(X, H)`-family, in the `IsFam` sense, with `pol`.

**2. Large sieve for polynomial phases (MRTTZ Prop. 3.3).** Suppose `K` phases `φ_i` on intervals
`I_i ∼ I` each correlate `≥ η'` with `f`. Then either `K ≤ K(η')`, or two of them satisfy
`φ_i ~_1 φ_j`. Proof:
- Cauchy–Schwarz.
- N2 applied to `P_i − P_j`, expanded around an integer point `n_I`.
- Pigeonhole on the bounded set of `(q, a_{j,l})`.

Corollary (greedy): each interval `I` of length `H` has a list `φ_1..φ_K`, `K = O_{η'}(1)`, such
that every `η'`-correlating `φ` on a subinterval `J ⊆ I` with `|J| ≥ η'|I|` satisfies
`φ ~_1 φ_i` for some `i`.

**3. Turán–Kubilius, dual form in short intervals (MRT Prop. 2.5 / Elliott Lemma 4.7).** Prove it
for `p ∈ [P, Q]` with `Q ≤ H^{1/3}`:
`Σ_{P ≤ p ≤ Q} p |Σ_{m ∈ (x/p, (x+H)/p]} a(pm) − (1/p) Σ_{n ∈ (x, x+H]} a(n)|² ≪ H²`
for `|a| ≤ 1`.

Proof by duality from
`Σ_n |Σ_{p | n} b_p − Σ_p b_p/p|² ≪ H Σ |b_p|²/p`.
Expand the square. The error from `#{n : pp' | n} = H/(pp') + O(1)` is
`≤ (Σ|b_p|)² ≤ Q² Σ|b_p|²/p·(log)`, which is fine since `Q² ≤ H^{2/3}`.

**4. Scaling down (MRTTZ Prop. 3.4; the proof of MRT Prop. 3.1 with Prop. 3.3 in place of MRT
Lemma 2.2).**
- Apply 3 to `a(n) = f(n) e(−P_I(n))`, then use multiplicativity: `f(pm) = f(p) f(m)` unless
  `p | m`, which costs `O(H/(pP))`.
- Mertens and pigeonhole give `P' ∈ [P, Q/2]`.
- Greedy `2H/P'`-separated subfamily.
- The large-sieve list (step 2) on each `I'`.
- Completion of sums to a full-length interval: MRT Lemma 2.4. For polynomials it adds a linear
  term `β t` with `|β| ≤ 1/(η'² H)`, which is allowed because `k ≥ 1`.

Output: a large `(X/P', H/P')`-family with phases `φ'_{I'}`. Each `I'` is hit by `≫ π₀(P')` pairs
`(I, p')` with `(1/p')_* φ_I ~_1 φ'_{I'}`, and `I/p'` within `3H/P'` of `I'`.

**5. Two scalings and CRT (MRTTZ Prop. 3.6).**
- First scaling: `P = X^{ε²}`, `Q = X^{ε}`.
- Second scaling: `P = (X/P')^{ε²}`, `Q = (X/P')^ε`.
- CRT (i) (MRTTZ Appendix B, `papers/mrttz/AppendixB4.tex`): replace `φ''_{I''}` by `φ'' + γ`
  with `γ` integer valued, so that `(1/p'')_* φ'_{I'} ~_{1/p''} φ''_{I''}` holds for **all**
  incident `(I', p'')`. Correlations only depend on values at integers, so they are unchanged.
- Cauchy–Schwarz over `(I, p'')` gives octuplets. Then use `PolyRel` dilation and sparsification
  (helpers R3, R4 in `adi_cycles.md`) to get
  `(1/p'_2)_* φ''_{I''_1} ~_{1/p''} (1/p'_1)_* φ''_{I''_2}`.
- Discard `p'_1 = p'_2`.
- Count quadruples. Each can be completed in `≫ π₀(P'')` ways, which gives the prime set
  `S_e`.

**Constants.** `ε₀` must make `log Q/log P = 1/ε` large depending on `η`. `C` is the constant of
`PolyRel`. With left endpoints, the `EdgeGeom` slack of `100L` covers the `≤ 36L` from the chain
`3H/P' + 3H/(P'P'')` plus the lengths.

## Size and risk

Size 6–12k. Risk medium: bookkeeping of families and greedy selections. The mathematics is
routine once N2 is available.
-/

namespace Work.BMF

open Polynomial BoundedMultiplicativeFunctions

set_option maxHeartbeats 4000000

/-! ### Auxiliary lemmas for the assembly of `build_quadruples` -/

/-- For positive `x`, `y`: `y ≤ x^e` iff `log y ≤ e * log x`. -/
lemma le_rpow_iff_le_mul_log {x y e : ℝ} (hx : 0 < x) (hy : 0 < y) :
    y ≤ x ^ e ↔ Real.log y ≤ e * Real.log x := by
  rw [Real.rpow_def_of_pos hx]
  conv_lhs => rw [show y = Real.exp (Real.log y) from (Real.exp_log hy).symm]
  rw [Real.exp_le_exp, mul_comm]

/-- For positive `x`, `y`: `x^e ≤ y` iff `e * log x ≤ log y`. -/
lemma rpow_le_iff_mul_log_le {x y e : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x ^ e ≤ y ↔ e * Real.log x ≤ Real.log y := by
  rw [Real.rpow_def_of_pos hx]
  conv_lhs => rw [show y = Real.exp (Real.log y) from (Real.exp_log hy).symm]
  rw [Real.exp_le_exp, mul_comm]

/-- `incPairs` only depends on its two scalar parameters `R` (radius) and `L'` (target length),
and on the target polynomial. -/
lemma incPairs_congr' {k : ℕ} {C : ℝ} {src : Finset ℝ} {a b H R R' L' L'' : ℝ}
    {pol : ℝ → ℝ[X]} {pol' pol'' : ℝ[X]} {x' : ℝ} (hR : R = R') (hL : L' = L'')
    (hp : pol' = pol'') :
    incPairs k C src a b H R L' pol pol' x' = incPairs k C src a b H R' L'' pol pol'' x' := by
  subst hR; subst hL; subst hp; rfl

/-- Monotonicity of `x ↦ x^e` in the exponent. -/
lemma rpow_mono_exp {x e e' : ℝ} (hx : 1 ≤ x) (h : e ≤ e') : x ^ e ≤ x ^ e' :=
  Real.rpow_le_rpow_of_exponent_le hx h

/-- `incPairs` is monotone in the relation constant `C`, in cardinality. -/
lemma card_incPairs_mono_of_le {k : ℕ} {C C' : ℝ} (hC : C ≤ C') {src : Finset ℝ}
    {a b H R L' : ℝ} (hH : 0 ≤ H) (hL' : 0 ≤ L') {pol : ℝ → ℝ[X]} {pol' : ℝ[X]} {x' : ℝ} :
    (incPairs k C src a b H R L' pol pol' x').card ≤
      (incPairs k C' src a b H R L' pol pol' x').card := by
  apply Finset.card_le_card
  intro q hq
  simp only [incPairs, Finset.mem_filter, Finset.mem_product] at hq ⊢
  obtain ⟨⟨hqs, hqp⟩, hq1, hq2⟩ := hq
  have hp : (0 : ℝ) < (q.2 : ℝ) := by
    exact_mod_cast (Finset.mem_filter.mp hqp).2.pos
  exact ⟨⟨hqs, hqp⟩, hq1, PolyRel_mono hq2 hC (by positivity) hL'⟩

lemma PhaseFamily.congr_fam {k : ℕ} {f : ℕ → ℂ} {c X L X' L' : ℝ} (hX : X = X') (hL : L = L')
    (F : PhaseFamily k f c X L) : (PhaseFamily.congr hX hL F).fam = F.fam := by
  subst hX; subst hL; rfl

lemma PhaseFamily.congr_pol {k : ℕ} {f : ℕ → ℂ} {c X L X' L' : ℝ} (hX : X = X') (hL : L = L')
    (F : PhaseFamily k f c X L) : (PhaseFamily.congr hX hL F).pol = F.pol := by
  subst hX; subst hL; rfl

/-- The ratio of the logarithms of two powers is `1/ε`. -/
lemma le_log_rpow_div_log_rpow {X ε A : ℝ} (hX : 0 < X) (hlog : Real.log X ≠ 0)
    (hε : 0 < ε) (hA : A ≤ 1 / ε) :
    A ≤ Real.log (X ^ ε) / Real.log (X ^ (ε ^ 2)) := by
  rw [Real.log_rpow hX, Real.log_rpow hX]
  have hne1 : ε ≠ 0 := ne_of_gt hε
  have hne2 : ε ^ 2 * Real.log X ≠ 0 := mul_ne_zero (pow_ne_zero 2 hne1) hlog
  have hval : ε * Real.log X / (ε ^ 2 * Real.log X) = 1 / ε := by
    field_simp
  rw [hval]
  exact hA


/-- **N3. Discretisation, Turán–Kubilius scaling-down, and the quadruple graph**
(MRT §2 (2.1), Props. 3.1–3.2; MRTTZ Props. 3.4–3.6). From `∫_X^{2X} ‖f‖_{u^{k+1}[x,x+H]} ≥ ηX`
one finds scales `P₁ = P'`, `P₂ = P''` in `[X^{ε²/2}, X^ε]` and `QuadData` at scale
`(X/(P₁P₂), H/(P₁P₂))`: a large family of intervals with correlating degree-`≤ k` phases and
`≫ π₀(P₁)² X/H` edges related modulo `1/p''` for `≫ π₀(P₂)` primes `p'' ∈ [P₂/2, P₂]`.
`k ≥ 1` is needed for the completion-of-sums step (a linear correction of the phase). -/
theorem build_quadruples (k : ℕ) (hk : 1 ≤ k) (θ η : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1 / 2)
    (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ c C X₀ : ℝ, 0 < c ∧ ∀ (f : ArithmeticFunction ℂ), f.IsMultiplicative → IsOneBounded f →
        ∀ X H : ℝ, X₀ ≤ X → X ^ θ ≤ H → H ≤ X ^ (1 - θ) →
        ∫ x in X..(2 * X), weakGowersUniformityNorm k x H f.intExtension ≥ η * X →
        ∃ P₁ P₂ : ℝ, X ^ (ε ^ 2 / 2) ≤ P₁ ∧ P₁ ≤ X ^ ε ∧ X ^ (ε ^ 2 / 2) ≤ P₂ ∧ P₂ ≤ X ^ ε ∧
          Nonempty (QuadData k f c C (X / (P₁ * P₂)) (H / (P₁ * P₂)) P₁ P₂) := by

  -- ================= the declared constants =================
  obtain ⟨c₀, hc₀, hdisc⟩ := discretise k θ η hθ₀ hη
  obtain ⟨c₁, C₁, A₁, Pp₁, hc₁, hC₁, hA₁, hPp₁, hle₁, hsd₁⟩ := scale_down k hk c₀ hc₀
  obtain ⟨c₂, C₂, A₂, Pp₂, hc₂, hC₂, hA₂, hPp₂, hle₂, hsd₂⟩ := scale_down k hk c₁ hc₁
  obtain ⟨c₃, C₃, A₃, Pp₃, hc₃, hC₃, hA₃, hPp₃, hle₃, hqs⟩ :=
    quaddata_stage k hk c₂ (max C₁ C₂) hc₂ (lt_of_lt_of_le hC₁ (le_max_left _ _))
  refine ⟨min (min (θ / 8) (1 / (A₁ + 1))) (min (1 / (A₂ + 1)) (1 / (A₃ + 1))), by positivity, ?_⟩
  intro ε hε hεle
  have hεθ : ε ≤ θ / 8 := le_trans hεle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hε8 : 8 * ε ≤ θ := by linarith
  have hεA₁ : A₁ ≤ 1 / ε := by
    have h1 : ε ≤ 1 / (A₁ + 1) := le_trans hεle (le_trans (min_le_left _ _) (min_le_right _ _))
    have h2 : ε * (A₁ + 1) ≤ 1 := (le_div_iff₀ (by linarith : (0 : ℝ) < A₁ + 1)).mp h1
    rw [le_div_iff₀ hε]
    nlinarith
  have hεA₂ : A₂ ≤ 1 / ε := by
    have h1 : ε ≤ 1 / (A₂ + 1) := le_trans hεle (le_trans (min_le_right _ _) (min_le_left _ _))
    have h2 : ε * (A₂ + 1) ≤ 1 := (le_div_iff₀ (by linarith : (0 : ℝ) < A₂ + 1)).mp h1
    rw [le_div_iff₀ hε]
    nlinarith
  have hεA₃ : A₃ ≤ 1 / ε := by
    have h1 : ε ≤ 1 / (A₃ + 1) := le_trans hεle (le_trans (min_le_right _ _) (min_le_right _ _))
    have h2 : ε * (A₃ + 1) ≤ 1 := (le_div_iff₀ (by linarith : (0 : ℝ) < A₃ + 1)).mp h1
    rw [le_div_iff₀ hε]
    nlinarith
  have hε1 : ε ≤ 1 := by linarith
  have hεhalf : ε ≤ 1 / 2 := by linarith
  have hεq : ε ≤ 1 / 4 := by linarith
  have hεpos : 0 < ε := hε
  -- ================= the threshold `X₀` =================
  have hSbig : (2 : ℝ) ≤ Pp₁ + Pp₂ + Pp₃ + 2 := by linarith [hPp₁]
  have hSlog : 0 < Real.log (Pp₁ + Pp₂ + Pp₃ + 2) :=
    Real.log_pos (by linarith [hPp₁] : (1 : ℝ) < Pp₁ + Pp₂ + Pp₃ + 2)
  let B : ℝ := max (max (4 * Real.log (Pp₁ + Pp₂ + Pp₃ + 2) / ε ^ 2) (Real.log 2 / ε ^ 3))
      (4 * Real.log 200 / (3 * θ))
  have hB1 : 4 * Real.log (Pp₁ + Pp₂ + Pp₃ + 2) / ε ^ 2 ≤ B := by
    dsimp only [B]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hB2 : Real.log 2 / ε ^ 3 ≤ B := by
    dsimp only [B]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hB3 : 4 * Real.log 200 / (3 * θ) ≤ B := by
    dsimp only [B]; exact le_max_right _ _
  have hBpos : 0 < B := by
    refine lt_of_lt_of_le ?_ hB1
    exact div_pos (by linarith [hSlog]) (pow_pos hεpos 2)
  refine ⟨c₃, C₃, Real.exp B, hc₃, ?_⟩
  intro f hf hf1 X H hX H_θ H_ge hint
  -- ================= elementary consequences of `X ≥ exp B` =================
  have hXgt1 : 1 < X := by
    have h1 : Real.exp 0 < Real.exp B := Real.exp_lt_exp.mpr hBpos
    rw [Real.exp_zero] at h1
    linarith
  have hX1 : 1 ≤ X := le_of_lt hXgt1
  have hXpos : 0 < X := lt_trans zero_lt_one hXgt1
  have hLpos : 0 < Real.log X := Real.log_pos hXgt1
  have hLnn : 0 ≤ Real.log X := le_of_lt hLpos
  have hLne : Real.log X ≠ 0 := ne_of_gt hLpos
  have hL : B ≤ Real.log X := by
    have h1 := Real.log_le_log (Real.exp_pos B) hX
    rwa [Real.log_exp] at h1
  have hL1 : 4 * Real.log (Pp₁ + Pp₂ + Pp₃ + 2) / ε ^ 2 ≤ Real.log X := le_trans hB1 hL
  have hL2 : Real.log 2 / ε ^ 3 ≤ Real.log X := le_trans hB2 hL
  have hL3 : 4 * Real.log 200 / (3 * θ) ≤ Real.log X := le_trans hB3 hL
  have hε2L : 0 < ε ^ 2 * Real.log X := mul_pos (pow_pos hεpos 2) hLpos
  have hstep4 : ε ^ 2 / 4 * Real.log X ≤ ε ^ 2 * ((3 : ℝ) / 4 * Real.log X) := by
    have h3 : ε ^ 2 * ((3 : ℝ) / 4 * Real.log X) - ε ^ 2 / 4 * Real.log X
        = ε ^ 2 / 2 * Real.log X := by ring
    have h4 : 0 ≤ ε ^ 2 / 2 * Real.log X := le_of_lt (mul_pos (by positivity) hLpos)
    linarith
  have hstep2 : ε ^ 2 / 2 * Real.log X ≤ ε ^ 2 * ((3 : ℝ) / 4 * Real.log X) := by
    have h3 : ε ^ 2 * ((3 : ℝ) / 4 * Real.log X) - ε ^ 2 / 2 * Real.log X
        = ε ^ 2 / 4 * Real.log X := by ring
    have h4 : 0 ≤ ε ^ 2 / 4 * Real.log X := le_of_lt (mul_pos (by positivity) hLpos)
    linarith
  have hlogS : Real.log (Pp₁ + Pp₂ + Pp₃ + 2) ≤ ε ^ 2 / 4 * Real.log X := by
    have h := (div_le_iff₀ (show (0 : ℝ) < ε ^ 2 by positivity)).mp hL1
    nlinarith [h]
  have hlog2 : Real.log 2 ≤ ε ^ 2 / 4 * Real.log X :=
    le_trans (Real.log_le_log (by norm_num) hSbig) hlogS
  have hlogT : Real.log (Pp₁ + Pp₂ + Pp₃ + 1) ≤ ε ^ 2 / 4 * Real.log X :=
    le_trans (Real.log_le_log (by linarith [hPp₁]) (by linarith)) hlogS
  have hlog200 : Real.log 200 ≤ 3 * θ / 4 * Real.log X := by
    have h := (div_le_iff₀ (show (0 : ℝ) < 3 * θ by positivity)).mp hL3
    nlinarith [h]
  have hlog2ε3 : Real.log 2 ≤ ε ^ 3 * Real.log X := by
    have h := (div_le_iff₀ (show (0 : ℝ) < ε ^ 3 by positivity)).mp hL2
    nlinarith [h]
  -- ================= rpow consequences at scale `X` =================
  have hX2half : (2 : ℝ) ≤ X ^ (ε ^ 2 / 2) := by
    rw [le_rpow_iff_le_mul_log hXpos (by norm_num)]
    nlinarith [hlog2, hε2L]
  have hTX : (Pp₁ + Pp₂ + Pp₃ + 1) ≤ X ^ (ε ^ 2 / 2) := by
    rw [le_rpow_iff_le_mul_log hXpos (by linarith [hPp₁])]
    nlinarith [hlogT, hε2L]
  have hXeps : (2 : ℝ) ≤ X ^ (ε ^ 2) :=
    le_trans hX2half (rpow_mono_exp hX1 (by nlinarith [hεpos]))
  have hXeps3 : (2 : ℝ) ≤ X ^ (ε ^ 3) := by
    rw [le_rpow_iff_le_mul_log hXpos (by norm_num)]
    exact hlog2ε3
  have hPp₁le : Pp₁ ≤ X ^ (ε ^ 2) :=
    le_trans (le_trans (by linarith) hTX) (rpow_mono_exp hX1 (by nlinarith [hεpos]))
  have hPp₂le : Pp₂ ≤ X ^ (ε ^ 2) :=
    le_trans (le_trans (by linarith) hTX) (rpow_mono_exp hX1 (by nlinarith [hεpos]))
  have hPp₃le : Pp₃ ≤ X ^ (ε ^ 2) :=
    le_trans (le_trans (by linarith) hTX) (rpow_mono_exp hX1 (by nlinarith [hεpos]))
  -- ================= bounds on `H` =================
  have hH1 : 1 ≤ H := le_trans (Real.one_le_rpow hX1 hθ₀.le) H_θ
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH1
  have hHnn : 0 ≤ H := le_of_lt hHpos
  have hHX : H ≤ X := by
    have h : X ^ (1 - θ) ≤ X ^ (1 : ℝ) := rpow_mono_exp hX1 (by linarith)
    rw [Real.rpow_one] at h
    linarith
  have hXHnn : 0 ≤ X / H := by positivity
  -- ================= step 1: discretisation =================
  have h_int : η * X ≤ ∫ x in X..(2 * X), weakGowersUniformityNorm k x H (fun z : ℤ ↦ f ⌊z⌋₊) := by
    rw [show (fun z : ℤ ↦ f ⌊z⌋₊) = f.intExtension from rfl]
    exact hint
  obtain ⟨S, hS1', hS2', hS3', hS4'⟩ := hdisc (f : ℕ → ℂ) hf1 X H hX1 hH1 H_θ hHX h_int
  obtain ⟨F₀, _⟩ := phaseFamily_of_discretise_exists k (f : ℕ → ℂ) c₀ X H S hX1 hH1 hHX
    hS1' hS2' hS3' hS4'
  -- ================= step 2: first scaling down =================
  have hε2le : ε ^ 2 ≤ ε := by nlinarith [hεpos, hε1]
  have hPQ : X ^ (ε ^ 2) ≤ X ^ ε := rpow_mono_exp hX1 hε2le
  have h3ε : 3 * ε ≤ θ := by linarith [hε8]
  have hQ3 : (X ^ ε) ^ 3 ≤ H := by
    have h1 : (X ^ ε) ^ 3 = X ^ (3 * ε) := by
      rw [show (X ^ ε) ^ 3 = (X ^ ε) ^ ((3 : ℕ) : ℝ) from (Real.rpow_natCast (X ^ ε) 3).symm,
        ← Real.rpow_mul hXpos.le ε ((3 : ℕ) : ℝ)]
      congr 1
      push_cast
      ring
    rw [h1]
    exact le_trans (rpow_mono_exp hX1 h3ε) H_θ
  have hrat₁ : A₁ ≤ Real.log (X ^ ε) / Real.log (X ^ (ε ^ 2)) :=
    le_log_rpow_div_log_rpow hXpos hLne hε hεA₁
  obtain ⟨a₁, b₁, F₁, ha₁P, ha₁b₁, hb₁Q, hb₁a₁, hinc₁⟩ :=
    hsd₁ (f : ℕ → ℂ) hf1 (fun m n hc => hf.2 hc) X H (X ^ (ε ^ 2)) (X ^ ε)
      hXeps hPQ hQ3 hHX hPp₁le hrat₁ F₀
  -- ================= facts about `a₁` =================
  have ha₁pos : 0 < a₁ := lt_of_lt_of_le (Real.rpow_pos_of_pos hXpos (ε ^ 2)) ha₁P
  have ha₁gt1 : 1 < a₁ := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_trans hXeps ha₁P)
  have ha₁Xε : a₁ ≤ X ^ ε := le_trans ha₁b₁ hb₁Q
  have hlogposa₁ : 0 < Real.log a₁ := Real.log_pos ha₁gt1
  have hloga₁ : Real.log a₁ ≤ ε * Real.log X := by
    have h3 := Real.log_le_log ha₁pos ha₁Xε
    rwa [Real.log_rpow hXpos ε] at h3
  have hlogXa₁2 : Real.log (X / a₁) ≤ Real.log X := by
    rw [Real.log_div (ne_of_gt hXpos) (ne_of_gt ha₁pos)]
    linarith [Real.log_nonneg (le_of_lt ha₁gt1)]
  have hXa₁gt1 : 1 < X / a₁ := by
    rw [lt_div_iff₀ ha₁pos]
    have hεlt1 : ε < 1 := by linarith
    have h3 : X ^ ε < X ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hXgt1 hεlt1
    rw [Real.rpow_one] at h3
    linarith
  have hXa₁1 : 1 ≤ X / a₁ := le_of_lt hXa₁gt1
  have hXa₁pos : 0 < X / a₁ := by positivity
  have hlogXa₁pos : 0 < Real.log (X / a₁) := Real.log_pos hXa₁gt1
  have hlogXa₁ : (3 / 4 : ℝ) * Real.log X ≤ Real.log (X / a₁) := by
    have h1 : (1 - ε) * Real.log X ≤ Real.log (X / a₁) := by
      rw [Real.log_div (ne_of_gt hXpos) (ne_of_gt ha₁pos)]
      linarith
    have h4 : (3 / 4 : ℝ) * Real.log X ≤ (1 - ε) * Real.log X := by nlinarith [hεq, hLnn]
    linarith
  -- ================= log bounds at the second scale =================
  have hlogT2 : Real.log (Pp₁ + Pp₂ + Pp₃ + 1) ≤ ε ^ 2 * Real.log (X / a₁) := by
    have h1 : ε ^ 2 / 4 * Real.log X ≤ ε ^ 2 * ((3 : ℝ) / 4 * Real.log X) := hstep4
    have h2 : ε ^ 2 * ((3 : ℝ) / 4 * Real.log X) ≤ ε ^ 2 * Real.log (X / a₁) :=
      mul_le_mul_of_nonneg_left hlogXa₁ (by positivity)
    linarith
  have hlog2b : Real.log 2 ≤ ε ^ 2 * Real.log (X / a₁) := by
    have h1 : ε ^ 2 / 4 * Real.log X ≤ ε ^ 2 * ((3 : ℝ) / 4 * Real.log X) := hstep4
    have h2 : ε ^ 2 * ((3 : ℝ) / 4 * Real.log X) ≤ ε ^ 2 * Real.log (X / a₁) :=
      mul_le_mul_of_nonneg_left hlogXa₁ (by positivity)
    linarith
  have hTXa₁ : (Pp₁ + Pp₂ + Pp₃ + 1) ≤ (X / a₁) ^ (ε ^ 2) := by
    rw [le_rpow_iff_le_mul_log hXa₁pos (by linarith [hPp₁])]
    exact hlogT2
  have h2Xa₁ : (2 : ℝ) ≤ (X / a₁) ^ (ε ^ 2) := by
    rw [le_rpow_iff_le_mul_log hXa₁pos (by norm_num)]
    exact hlog2b
  have hPp₂le' : Pp₂ ≤ (X / a₁) ^ (ε ^ 2) :=
    le_trans (by linarith : Pp₂ ≤ Pp₁ + Pp₂ + Pp₃ + 1) hTXa₁
  have hPp₃le' : Pp₃ ≤ (X / a₁) ^ (ε ^ 2) :=
    le_trans (by linarith : Pp₃ ≤ Pp₁ + Pp₂ + Pp₃ + 1) hTXa₁
  have hPp₃le_a₁ : Pp₃ ≤ a₁ := le_trans (le_trans (by linarith : Pp₃ ≤ Pp₁ + Pp₂ + Pp₃ + 1) hTX)
    (le_trans (rpow_mono_exp hX1 (by nlinarith [hεpos])) ha₁P)
  -- ================= step 3: second scaling down =================
  have hrat₂ : A₂ ≤ Real.log ((X / a₁) ^ ε) / Real.log ((X / a₁) ^ (ε ^ 2)) :=
    le_log_rpow_div_log_rpow hXa₁pos (ne_of_gt hlogXa₁pos) hε hεA₂
  have hPQI : (X / a₁) ^ (ε ^ 2) ≤ (X / a₁) ^ ε := rpow_mono_exp hXa₁1 hε2le
  have hHXI : H / a₁ ≤ X / a₁ := div_le_div_of_nonneg_right hHX (le_of_lt ha₁pos)
  have h4ε : 4 * ε ≤ θ := by linarith [hε8]
  have h3ε' : 3 * ε ≤ θ - ε := by linarith [h4ε]
  have hQ3I : ((X / a₁) ^ ε) ^ 3 ≤ H / a₁ := by
    have hHApos : 0 < H / a₁ := by positivity
    have hrw : ((X / a₁) ^ ε) ^ 3 = (X / a₁) ^ (3 * ε) := by
      rw [show ((X / a₁) ^ ε) ^ 3 = ((X / a₁) ^ ε) ^ ((3 : ℕ) : ℝ) from
            (Real.rpow_natCast ((X / a₁) ^ ε) 3).symm,
        ← Real.rpow_mul hXa₁pos.le ε ((3 : ℕ) : ℝ)]
      congr 1
      push_cast
      ring
    rw [hrw, rpow_le_iff_mul_log_le hXa₁pos hHApos]
    have hlogH : θ * Real.log X ≤ Real.log H := by
      have h3 := Real.log_le_log (Real.rpow_pos_of_pos hXpos θ) H_θ
      rwa [Real.log_rpow hXpos θ] at h3
    have hlogHa₁ : (θ - ε) * Real.log X ≤ Real.log (H / a₁) := by
      rw [Real.log_div (ne_of_gt hHpos) (ne_of_gt ha₁pos)]
      linarith
    have h3 : 3 * ε * Real.log (X / a₁) ≤ (θ - ε) * Real.log X := by
      have h4 : 3 * ε * Real.log (X / a₁) ≤ 3 * ε * Real.log X :=
        mul_le_mul_of_nonneg_left hlogXa₁2 (by positivity)
      have h5 : 3 * ε * Real.log X ≤ (θ - ε) * Real.log X :=
        mul_le_mul_of_nonneg_right h3ε' hLnn
      linarith
    linarith
  obtain ⟨a₂, b₂, F₂, ha₂, ha₂b₂, hb₂, hb₂a₂, hinc₂⟩ :=
    hsd₂ (f : ℕ → ℂ) hf1 (fun m n hc => hf.2 hc) (X / a₁) (H / a₁)
      ((X / a₁) ^ (ε ^ 2)) ((X / a₁) ^ ε)
      h2Xa₁ hPQI hQ3I hHXI hPp₂le' hrat₂ F₁
  -- ================= facts about `a₂` =================
  have ha₂pos : 0 < a₂ := lt_of_lt_of_le (Real.rpow_pos_of_pos hXa₁pos (ε ^ 2)) ha₂
  have ha₁ε : (2 : ℝ) ≤ a₁ ^ ε := by
    have h1 : (X ^ (ε ^ 2)) ^ ε ≤ a₁ ^ ε := Real.rpow_le_rpow (by positivity) ha₁P (le_of_lt hε)
    have hε3 : ε ^ 2 * ε = ε ^ 3 := by ring
    have h2 : (X ^ (ε ^ 2)) ^ ε = X ^ (ε ^ 3) := by
      rw [← hε3, ← Real.rpow_mul hXpos.le (ε ^ 2) ε]
    rw [h2] at h1
    exact le_trans hXeps3 h1
  have hfinal : 2 * (X / a₁) ^ ε ≤ X ^ ε := by
    have hApos : 0 < (X / a₁) ^ ε := Real.rpow_pos_of_pos hXa₁pos ε
    have h2 : (X / a₁) ^ ε * a₁ ^ ε = X ^ ε := by
      rw [Real.div_rpow (le_of_lt hXpos) (le_of_lt ha₁pos) ε,
        div_mul_cancel₀ (X ^ ε) (ne_of_gt (Real.rpow_pos_of_pos ha₁pos ε))]
    nlinarith [hApos, ha₁ε, h2]
  have hconv : (X / a₁) ^ (ε ^ 2) ≤ (X / a₁) ^ ε := rpow_mono_exp hXa₁1 hε2le
  have hPp₃le_a₂ : Pp₃ ≤ a₂ :=
    le_trans (le_trans (by linarith : Pp₃ ≤ Pp₁ + Pp₂ + Pp₃ + 1) hTXa₁) ha₂
  -- ================= transfer of `F₂` to the product scale =================
  have hXeq : (X / a₁) / a₂ = X / (a₁ * a₂) := by ring
  have hHeq : (H / a₁) / a₂ = H / (a₁ * a₂) := by ring
  let hF₂ : PhaseFamily k (f : ℕ → ℂ) c₂ (X / (a₁ * a₂)) (H / (a₁ * a₂)) :=
    ⟨F₂.fam, F₂.pol, hHeq ▸ hXeq ▸ F₂.isFam, hHeq ▸ hXeq ▸ F₂.card_ge, F₂.deg,
      hHeq ▸ F₂.corr_ge⟩
  -- ================= the incidence conditions with a common constant =================
  have hpi₁ : 0 ≤ pi0 a₁ := div_nonneg (le_of_lt ha₁pos) (le_of_lt hlogposa₁)
  have hinc₁' : ∀ x' ∈ F₁.fam, c₂ * pi0 a₁ ≤
      ((incPairs k (max C₁ C₂) F₀.fam a₁ b₁ H (3 * H / a₁) (H / a₁) F₀.pol (F₁.pol x') x').card : ℝ) := by
    intro x' hx'
    have hcard : ((incPairs k C₁ F₀.fam a₁ b₁ H (3 * H / a₁) (H / a₁) F₀.pol (F₁.pol x') x').card : ℝ) ≤
        ((incPairs k (max C₁ C₂) F₀.fam a₁ b₁ H (3 * H / a₁) (H / a₁) F₀.pol (F₁.pol x') x').card : ℝ) := by
      exact_mod_cast card_incPairs_mono_of_le (le_max_left _ _) hHnn (by positivity)
    have hcl : c₂ * pi0 a₁ ≤ c₁ * pi0 a₁ := mul_le_mul_of_nonneg_right hle₂ hpi₁
    exact le_trans hcl (le_trans (hinc₁ x' hx') hcard)
  have hinc₂' : ∀ x'' ∈ hF₂.fam, c₂ * pi0 a₂ ≤
      ((incPairs k (max C₁ C₂) F₁.fam a₂ b₂ (H / a₁) (3 * H / (a₁ * a₂)) (H / (a₁ * a₂))
        F₁.pol (hF₂.pol x'') x'').card : ℝ) := by
    intro x'' hx''
    have hmain : c₂ * pi0 a₂ ≤
        ((incPairs k (max C₁ C₂) F₁.fam a₂ b₂ (H / a₁) (3 * (H / a₁) / a₂) ((H / a₁) / a₂)
          F₁.pol (F₂.pol x'') x'').card : ℝ) := by
      have hcard : ((incPairs k C₂ F₁.fam a₂ b₂ (H / a₁) (3 * (H / a₁) / a₂) ((H / a₁) / a₂)
            F₁.pol (hF₂.pol x'') x'').card : ℝ) ≤
          ((incPairs k (max C₁ C₂) F₁.fam a₂ b₂ (H / a₁) (3 * (H / a₁) / a₂) ((H / a₁) / a₂)
            F₁.pol (hF₂.pol x'') x'').card : ℝ) := by
        exact_mod_cast card_incPairs_mono_of_le (le_max_right _ _) (by positivity) (by positivity)
      exact le_trans (hinc₂ x'' hx'') hcard
    have heq : (incPairs k (max C₁ C₂) F₁.fam a₂ b₂ (H / a₁) (3 * (H / a₁) / a₂) ((H / a₁) / a₂)
          F₁.pol (hF₂.pol x'') x'').card
        = (incPairs k (max C₁ C₂) F₁.fam a₂ b₂ (H / a₁) (3 * H / (a₁ * a₂)) (H / (a₁ * a₂))
          F₁.pol (hF₂.pol x'') x'').card := by
      congr 1
      exact incPairs_congr' (by ring) (by ring) rfl
    rw [heq] at hmain
    exact hmain
  -- ================= the geometric input `200 b₁² ≤ X/H` =================
  have h200 : 200 * b₁ ^ 2 ≤ X / H := by
    have hb₁pos : 0 < b₁ := lt_of_lt_of_le ha₁pos ha₁b₁
    have hsq : b₁ ^ 2 ≤ X ^ (2 * ε) := by
      calc b₁ ^ 2 ≤ (X ^ ε) ^ 2 := pow_le_pow_left₀ (le_of_lt hb₁pos) hb₁Q 2
        _ = (X ^ ε) ^ ((2 : ℕ) : ℝ) := (Real.rpow_natCast (X ^ ε) 2).symm
        _ = X ^ (ε * ((2 : ℕ) : ℝ)) := (Real.rpow_mul hXpos.le ε ((2 : ℕ) : ℝ)).symm
        _ = X ^ (2 * ε) := by congr 1; push_cast; ring
    have h200X : 200 * X ^ (2 * ε) ≤ X ^ θ := by
      have hX2ε : X ^ (2 * ε) * X ^ (θ - 2 * ε) = X ^ θ := by
        rw [← Real.rpow_add hXpos]
        congr 1
        ring
      have h200le : 200 ≤ X ^ (θ - 2 * ε) := by
        have h1 : (200 : ℝ) ≤ X ^ (3 * θ / 4) := by
          rw [le_rpow_iff_le_mul_log hXpos (by norm_num)]
          exact hlog200
        exact le_trans h1 (rpow_mono_exp hX1 (by nlinarith [hε8]))
      calc 200 * X ^ (2 * ε) ≤ X ^ (θ - 2 * ε) * X ^ (2 * ε) :=
            mul_le_mul_of_nonneg_right h200le (le_of_lt (Real.rpow_pos_of_pos hXpos (2 * ε)))
        _ = X ^ θ := by rw [mul_comm, hX2ε]
    have hXH : X ^ θ ≤ X / H := by
      rw [rpow_le_iff_mul_log_le hXpos (by positivity)]
      have hlogH : Real.log H ≤ (1 - θ) * Real.log X := by
        have h3 := Real.log_le_log hHpos H_ge
        rwa [Real.log_rpow hXpos (1 - θ)] at h3
      rw [Real.log_div (ne_of_gt hXpos) (ne_of_gt hHpos)]
      linarith
    calc 200 * b₁ ^ 2 ≤ 200 * X ^ (2 * ε) := mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ ≤ X ^ θ := h200X
      _ ≤ X / H := hXH
  -- ================= the `QuadData` =================
  let hF₀' : PhaseFamily k (f : ℕ → ℂ) c₂ X H :=
    F₀.weaken (le_trans hle₂ hle₁) hXHnn hHnn
  obtain ⟨P₁, P₂, _hprod, hP₁lo, hP₁hi, hP₂lo, hP₂hi, hQuad⟩ :=
    hqs (f : ℕ → ℂ) hf1 X H a₁ b₁ a₂ b₂ c₁ c₂ hF₀' F₁ hF₂ hle₂ (le_refl c₂)
      hPp₃le_a₁ ha₁b₁ hb₁a₁ hPp₃le_a₂ ha₂b₂ hb₂a₂ h200 hXpos hinc₁' hinc₂'
  -- ================= the two scales lie in `[X^{ε²/2}, X^ε]` =================
  refine ⟨P₁, P₂, ?_, ?_, ?_, ?_, hQuad⟩
  · have hb₁half : X ^ (ε ^ 2 / 2) ≤ b₁ / 2 := by
      have h1 : X ^ (ε ^ 2) ≤ b₁ := le_trans ha₁P ha₁b₁
      have hsq : X ^ (ε ^ 2 / 2) * X ^ (ε ^ 2 / 2) = X ^ (ε ^ 2) := by
        rw [← Real.rpow_add hXpos]
        congr 1
        ring
      nlinarith [hX2half, h1, hsq]
    exact le_trans hb₁half hP₁lo
  · exact le_trans hP₁hi (le_trans ha₁b₁ hb₁Q)
  · have hXa₁le2 : X ^ (ε ^ 2 / 2) ≤ (X / a₁) ^ (ε ^ 2) := by
      rw [rpow_le_iff_mul_log_le hXpos (Real.rpow_pos_of_pos hXa₁pos (ε ^ 2)),
        Real.log_rpow hXa₁pos]
      have h1 : ε ^ 2 * ((3 : ℝ) / 4 * Real.log X) ≤ ε ^ 2 * Real.log (X / a₁) :=
        mul_le_mul_of_nonneg_left hlogXa₁ (by positivity)
      have h2 : ε ^ 2 / 2 * Real.log X ≤ ε ^ 2 * ((3 : ℝ) / 4 * Real.log X) := hstep2
      linarith
    exact le_trans (le_trans hXa₁le2 (le_trans ha₂ ha₂b₂)) hP₂lo
  · have ha₂ε : a₂ ≤ (X / a₁) ^ ε := le_trans ha₂b₂ hb₂
    exact le_trans (le_trans hP₂hi (mul_le_mul_of_nonneg_left ha₂ε (by norm_num))) hfinal
end Work.BMF

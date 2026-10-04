import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.CSq_comp_vecarg_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Moser composition estimate for a nonlinearity depending on the point

This file proves `Work.Diff.STE.flat.CSq_comp_xperiodic_le`: for a smooth `Φ : ℝⁿ × ℂᵐ → ℂ` which
is `1`-periodic in the real variables and data `c : ℤⁿ → ℂᵐ` whose `ρ`-Sobolev norm is bounded by
`B` (with `n < 2ρ ≤ 2s`), the composed function

  `x ↦ Φ (x, fun i => seriesFun (fun k => c k i) x)`

has finite weighted `ℓ²` Fourier coefficients, controlled linearly in the top Sobolev norm
`∑ i, CSq s (fun k => c k i)` of the data — the Moser composition estimate for a nonlinearity with
an explicit spatial dependence.

The strategy is to *eliminate the spatial dependence* using the periodicity: `Φ` is a function of
the characters `x ↦ exp (2 π i x j)` alone, so

  `Φ (x, V x) = Φ' (fun i => seriesFun (fun k => C k i) x)`

where `C k` is the *appended* family with components the `n` character families
`k ↦ if k = Pi.single j 1 then 1 else 0` and the `m` components `c k i`, and `Φ'` is the smooth
function of `n + m` complex variables obtained by factoring `Φ` through the character map
(`Work.Diff.STE.flat.periodic_factor`).  The vector-valued Moser estimate
`Work.Diff.STE.CSq_comp_vecarg_le` then applies verbatim; the only bookkeeping left is that the
extra `n` character families are finitely supported, hence contribute the constant `n · 2 ^ s` to
the estimate.
-/

namespace Work.Diff.STE.flat

open scoped BigOperators

noncomputable section

/-! ## The character families -/

/-- The coefficient family of the character `x ↦ exp (2 π i x j)` on the `n`-torus: it is `1` at
the unit vector `Pi.single j 1` and `0` everywhere else. -/
def xperCharFam {n : ℕ} (j : Fin n) : (Fin n → ℤ) → ℂ :=
  fun k => if k = Pi.single j 1 then 1 else 0

/-- The vector of the `n` character families, as a family with values in `ℂⁿ`. -/
def xperCharVec {n : ℕ} (k : Fin n → ℤ) : Fin n → ℂ := fun j => xperCharFam j k

/-- The coefficient family of the composed map
`x ↦ (exp (2 π i x j))_j × (fun i => seriesFun (fun k => c k i) x)`: the first `n` components are
the character families and the last `m` are those of `c`. -/
def xperAppend {n m : ℕ} (c : (Fin n → ℤ) → (Fin m → ℂ)) : (Fin n → ℤ) → (Fin (n + m) → ℂ) :=
  fun k => Fin.append (xperCharVec k) (c k)

lemma xperWt_single {n : ℕ} (j : Fin n) : wt (Pi.single j 1 : Fin n → ℤ) = 2 := by
  rw [wt]
  have h : (∑ i, (((Pi.single j 1 : Fin n → ℤ) i : ℤ) : ℝ) ^ 2) = 1 := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb]
      simp
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [h]
  norm_num

/-- `seriesFun` of the character family is the character. -/
lemma xperSeriesFun_charFam {n : ℕ} (j : Fin n) (x : Fin n → ℝ) :
    seriesFun (xperCharFam j) x = Complex.exp (2 * Real.pi * Complex.I * (x j : ℂ)) := by
  rw [seriesFun, tsum_eq_single (Pi.single j 1)]
  · simp only [xperCharFam, ite_true]
    have h1 : (∑ i, (((Pi.single j 1 : Fin n → ℤ) i : ℤ) : ℂ) * (x i : ℂ)) = (x j : ℂ) := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb]
        simp
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [fourierExp, h1]
    simp
  · intro k hk
    simp [xperCharFam, hk]

/-- The `s`-th weighted `ℓ²` norm of a character family is `2 ^ s`. -/
lemma xperCSq_charFam {n s : ℕ} (j : Fin n) : CSq s (xperCharFam j) = 2 ^ s := by
  rw [CSq, tsum_eq_single (Pi.single j 1)]
  · simp only [xperCharFam, ite_true, norm_one, one_pow, mul_one, xperWt_single]
  · intro k hk
    simp [xperCharFam, hk]

/-! ## The appended family -/

lemma xperAppend_left {n m : ℕ} (c : (Fin n → ℤ) → (Fin m → ℂ)) (k : Fin n → ℤ) (j : Fin n) :
    xperAppend c k (Fin.castAdd m j) = xperCharFam j k :=
  Fin.append_left _ _ j

lemma xperAppend_right {n m : ℕ} (c : (Fin n → ℤ) → (Fin m → ℂ)) (k : Fin n → ℤ) (p : Fin m) :
    xperAppend c k (Fin.natAdd n p) = c k p :=
  Fin.append_right _ _ p

/-- The norm of the appended family is bounded by the sum of the norms of its two parts. -/
lemma xperNorm_append_le {n m : ℕ} (c : (Fin n → ℤ) → (Fin m → ℂ)) (k : Fin n → ℤ) :
    ‖xperAppend c k‖ ≤ ‖c k‖ + ‖xperCharVec k‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  exact Fin.addCases (motive := fun i => ‖xperAppend c k i‖ ≤ ‖c k‖ + ‖xperCharVec k‖)
    (fun j => by
      rw [xperAppend_left]
      exact (norm_le_pi_norm (xperCharVec k) j).trans
        (le_add_of_nonneg_left (norm_nonneg (c k))))
    (fun p => by
      rw [xperAppend_right]
      exact (norm_le_pi_norm (c k) p).trans
        (le_add_of_nonneg_right (norm_nonneg (xperCharVec k))))
    i

/-- Every moment of the vector of character families is summable: it is a finitely supported
family. -/
lemma xperSummable_charVec {n : ℕ} (N : ℕ) :
    Summable (fun k : Fin n → ℤ => (wt k) ^ N * ‖xperCharVec k‖) := by
  refine summable_of_ne_finset_zero
    (s := Finset.univ.image (fun j : Fin n => (Pi.single j 1 : Fin n → ℤ))) ?_
  intro k hk
  have h0 : xperCharVec k = 0 := by
    funext j
    have hne : ¬ (k = (Pi.single j 1 : Fin n → ℤ)) := by
      intro h
      exact hk (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, h.symm⟩)
    simp [xperCharVec, xperCharFam, hne]
  simp [h0]

/-- Summability of the moments of the appended family, from that of the data. -/
lemma xperSummable_append {n m : ℕ} (c : (Fin n → ℤ) → (Fin m → ℂ)) (N : ℕ)
    (hc : Summable (fun k : Fin n → ℤ => (wt k) ^ N * ‖c k‖)) :
    Summable (fun k : Fin n → ℤ => (wt k) ^ N * ‖xperAppend c k‖) := by
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (le_of_lt (wt_pos k)) N) (norm_nonneg _))
    (fun k => ?_) (hc.add (xperSummable_charVec (n := n) N))
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (xperNorm_append_le c k) (pow_nonneg (le_of_lt (wt_pos k)) N)

/-- The `s`-Sobolev norm squared of the appended family is that of the data plus the constant
contribution `n · 2 ^ s` of the character families. -/
lemma xperSum_CSq_append {n m : ℕ} (c : (Fin n → ℤ) → (Fin m → ℂ)) (s : ℕ) :
    (∑ i : Fin (n + m), CSq s (fun k : Fin n → ℤ => xperAppend c k i))
      = (∑ _j : Fin n, (2 : ℝ) ^ s)
        + ∑ p : Fin m, CSq s (fun k : Fin n → ℤ => c k p) := by
  rw [Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : (fun k : Fin n → ℤ => xperAppend c k (Fin.castAdd m j)) = xperCharFam j := by
      funext k
      exact xperAppend_left c k j
    rw [h1, xperCSq_charFam]
  · refine Finset.sum_congr rfl fun p _ => ?_
    have h1 : (fun k : Fin n → ℤ => xperAppend c k (Fin.natAdd n p)) = fun k => c k p := by
      funext k
      exact xperAppend_right c k p
    rw [h1]

lemma xperSum_const {n s : ℕ} : (∑ _j : Fin n, (2 : ℝ) ^ s) = (n : ℝ) * 2 ^ s := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## The composition estimate -/

/-- The form of the factorisation lemma `Work.Diff.STE.flat.periodic_factor` that the composition
estimate consumes: a smooth `Φ` that is `1`-periodic in its real coordinates is a smooth function
of the characters `x ↦ exp (2 π i x j)`. -/
def FactorStatement : Prop :=
  ∀ {n m : ℕ} (Φ : (Fin n → ℝ) × (Fin m → ℂ) → ℂ), ContDiff ℝ (⊤ : ℕ∞) Φ →
    (∀ (v : Fin m → ℂ) (i : Fin n) (x : Fin n → ℝ), Φ (x + Pi.single i 1, v) = Φ (x, v)) →
    ∃ Ξ : (Fin n → ℂ) × (Fin m → ℂ) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Ξ ∧
        ∀ (x : Fin n → ℝ) (v : Fin m → ℂ),
          Ξ ((fun j : Fin n => Complex.exp (2 * Real.pi * Complex.I * (x j : ℂ))), v) = Φ (x, v)

/-- **The Moser composition estimate for a `1`-periodic nonlinearity, from the factorisation.**

This is the target statement with the factorisation of a periodic smooth function through the
character map taken as a hypothesis; the target theorem below instantiates it with
`Work.Diff.STE.flat.periodic_factor`. -/
theorem CSq_comp_xperiodic_le_of_factor (hfactor : FactorStatement)
    {n m : ℕ} (s ρ : ℕ) (hρ : n < 2 * ρ) (hρs : ρ ≤ s)
    (Φ : (Fin n → ℝ) × (Fin m → ℂ) → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hper : ∀ (v : Fin m → ℂ) (i : Fin n) (x : Fin n → ℝ), Φ (x + Pi.single i 1, v) = Φ (x, v))
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : (Fin n → ℤ) → (Fin m → ℂ)),
      (∀ N : ℕ, Summable (fun k : (Fin n → ℤ) => (wt k) ^ N * ‖c k‖)) →
      (∑ i : Fin m, CSq ρ (fun k : (Fin n → ℤ) => c k i)) ≤ B ^ 2 →
      Summable (fun k : (Fin n → ℤ) => (wt k) ^ s *
        ‖fourierCoeff (fun x : Fin n → ℝ =>
          Φ (x, fun i : Fin m => seriesFun (fun k => c k i) x)) k‖ ^ 2) ∧
      CSq s (fourierCoeff (fun x : Fin n → ℝ =>
          Φ (x, fun i : Fin m => seriesFun (fun k => c k i) x)))
        ≤ C * (1 + ∑ i : Fin m, CSq s (fun k : (Fin n → ℤ) => c k i)) := by
  classical
  obtain ⟨Ξ, hΞdiff, hΞ⟩ := hfactor Φ hΦ hper
  -- the smooth function of `n + m` complex variables obtained from `Ξ`
  set Φ' : (Fin (n + m) → ℂ) → ℂ :=
    fun z => Ξ ((fun j : Fin n => z (Fin.castAdd m j)), (fun i : Fin m => z (Fin.natAdd n i)))
    with hΦ'def
  have hΦ'diff : ContDiff ℝ (⊤ : ℕ∞) Φ' := by
    rw [hΦ'def]
    refine hΞdiff.comp ?_
    set L : (Fin (n + m) → ℂ) →L[ℝ] ((Fin n → ℂ) × (Fin m → ℂ)) :=
      (ContinuousLinearMap.pi
          (fun j : Fin n => ContinuousLinearMap.proj (Fin.castAdd m j))).prod
        (ContinuousLinearMap.pi (fun i : Fin m => ContinuousLinearMap.proj (Fin.natAdd n i)))
      with hLdef
    exact L.contDiff
  -- the admissible bound `B'` for the appended family
  set B' : ℝ := Real.sqrt (B ^ 2 + (n : ℝ) * 2 ^ ρ) with hB'def
  have hB'nn : 0 ≤ B' := Real.sqrt_nonneg _
  obtain ⟨Cv, hCvnn, hCv⟩ :=
    CSq_comp_vecarg_le (ι := Fin n) s ρ (by simpa using hρ) hρs Φ' hΦ'diff B' hB'nn
  refine ⟨Cv * (1 + (n : ℝ) * 2 ^ s), by positivity, ?_⟩
  intro c hmom hCSq
  have hCmom : ∀ N : ℕ, Summable (fun k : Fin n → ℤ => (wt k) ^ N * ‖xperAppend c k‖) :=
    fun N => xperSummable_append c N (hmom N)
  have hB'sq : B' ^ 2 = B ^ 2 + (n : ℝ) * 2 ^ ρ := by
    rw [hB'def, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ B ^ 2 + (n : ℝ) * 2 ^ ρ)]
  have hCSQρ : (∑ i : Fin (n + m), CSq ρ (fun k : Fin n → ℤ => xperAppend c k i)) ≤ B' ^ 2 := by
    rw [xperSum_CSq_append, xperSum_const, hB'sq]
    linarith
  obtain ⟨hsumm, hbound⟩ := hCv (xperAppend c) hCmom hCSQρ
  -- identify the composition with `Φ (x, fun i => seriesFun (fun k => c k i) x)`
  have hfun : (fun x : Fin n → ℝ =>
        Φ' (fun i : Fin (n + m) => seriesFun (fun k : Fin n → ℤ => xperAppend c k i) x))
      = (fun x : Fin n → ℝ =>
        Φ (x, fun i : Fin m => seriesFun (fun k : Fin n → ℤ => c k i) x)) := by
    funext x
    have hchar : (fun j : Fin n =>
          seriesFun (fun k : Fin n → ℤ => xperAppend c k (Fin.castAdd m j)) x)
        = (fun j : Fin n => Complex.exp (2 * Real.pi * Complex.I * (x j : ℂ))) := by
      funext j
      have h1 : (fun k : Fin n → ℤ => xperAppend c k (Fin.castAdd m j)) = xperCharFam j :=
        funext fun k => xperAppend_left c k j
      rw [h1, xperSeriesFun_charFam]
    have hv : (fun p : Fin m =>
          seriesFun (fun k : Fin n → ℤ => xperAppend c k (Fin.natAdd n p)) x)
        = (fun p : Fin m => seriesFun (fun k : Fin n → ℤ => c k p) x) := by
      funext p
      have h1 : (fun k : Fin n → ℤ => xperAppend c k (Fin.natAdd n p)) = fun k => c k p :=
        funext fun k => xperAppend_right c k p
      rw [h1]
    rw [hΦ'def]
    show Ξ ((fun j : Fin n =>
            seriesFun (fun k : Fin n → ℤ => xperAppend c k (Fin.castAdd m j)) x),
          (fun p : Fin m =>
            seriesFun (fun k : Fin n → ℤ => xperAppend c k (Fin.natAdd n p)) x)) = _
    rw [hchar, hv, hΞ]
  refine ⟨?_, ?_⟩
  · rw [hfun] at hsumm
    exact hsumm
  · have hCSQs : (∑ i : Fin (n + m), CSq s (fun k : Fin n → ℤ => xperAppend c k i))
        = (n : ℝ) * 2 ^ s + ∑ p : Fin m, CSq s (fun k : Fin n → ℤ => c k p) := by
      rw [xperSum_CSq_append, xperSum_const]
    have hCSqnn : 0 ≤ ∑ p : Fin m, CSq s (fun k : Fin n → ℤ => c k p) :=
      Finset.sum_nonneg fun p _ => CSq_nonneg s _
    calc CSq s (fourierCoeff (fun x : Fin n → ℝ =>
            Φ (x, fun i : Fin m => seriesFun (fun k : Fin n → ℤ => c k i) x)))
        = CSq s (fourierCoeff (fun x : Fin n → ℝ =>
            Φ' (fun i : Fin (n + m) => seriesFun (fun k : Fin n → ℤ => xperAppend c k i) x))) := by
          rw [hfun]
      _ ≤ Cv * (1 + ∑ i : Fin (n + m), CSq s (fun k : Fin n → ℤ => xperAppend c k i)) := hbound
      _ = Cv * (1 + ((n : ℝ) * 2 ^ s + ∑ p : Fin m, CSq s (fun k : Fin n → ℤ => c k p))) := by
          rw [hCSQs]
      _ ≤ Cv * (1 + (n : ℝ) * 2 ^ s) * (1 + ∑ p : Fin m, CSq s (fun k : Fin n → ℤ => c k p)) := by
          have h2s : (0 : ℝ) ≤ 2 ^ s := by positivity
          have hA : (0 : ℝ) ≤ (n : ℝ) * 2 ^ s := mul_nonneg (Nat.cast_nonneg n) h2s
          have h1 : (1 : ℝ) + ((n : ℝ) * 2 ^ s + ∑ p : Fin m, CSq s (fun k : Fin n → ℤ => c k p))
              ≤ (1 + (n : ℝ) * 2 ^ s) * (1 + ∑ p : Fin m, CSq s (fun k : Fin n → ℤ => c k p)) := by
            nlinarith [mul_nonneg hA hCSqnn]
          calc Cv * (1 + ((n : ℝ) * 2 ^ s + ∑ p : Fin m, CSq s (fun k : Fin n → ℤ => c k p)))
              ≤ Cv * ((1 + (n : ℝ) * 2 ^ s) * (1 + ∑ p : Fin m, CSq s (fun k : Fin n → ℤ => c k p))) :=
                mul_le_mul_of_nonneg_left h1 hCvnn
            _ = Cv * (1 + (n : ℝ) * 2 ^ s)
                  * (1 + ∑ p : Fin m, CSq s (fun k : Fin n → ℤ => c k p)) := by ring

/-! ## A self-contained factorisation of a `1`-periodic smooth function

The construction below provides an alternative, self-contained proof of the factorisation
`FactorStatement`.  The circle is covered by the two open sets `Complex.slitPlane` (where the
principal branch `log` is smooth) and its negative `-slitPlane` (where `z ↦ log (-z)` is smooth);
for each coordinate one interpolates between the two branches using a smooth step `xpHS` of the
real part and multiplies by a radial cutoff `xpKS (z.re ^ 2 + z.im ^ 2)` which vanishes near the
origin (where the two "angle" functions fail to be smooth) and equals `1` on the unit circle. -/

section Factor

/-- Smooth step: `0` for `t ≤ -1/8`, `1` for `t ≥ 0`. -/
def xpHS (t : ℝ) : ℝ := Real.smoothTransition (8 * t + 1)

/-- Radial cutoff: `0` for `t ≤ 1/16`, `1` on `[5/16, 2]`, `0` for `t ≥ 3`. -/
def xpKS (t : ℝ) : ℝ := Real.smoothTransition (4 * t - 1 / 4) * Real.smoothTransition (3 - t)

/-- The angle read off from the principal branch of the logarithm. -/
def xpThP (z : ℂ) : ℝ := (Complex.log z).im / (2 * Real.pi)

/-- The angle read off from the branch `z ↦ log (-z)`. -/
def xpThM (z : ℂ) : ℝ := (Complex.log (-z)).im / (2 * Real.pi) + 1 / 2

/-- The angle selected by the branch `s`. -/
def xpAng : Bool → ℂ → ℝ
  | true, z => xpThP z
  | false, z => xpThM z

/-- The weight of the branch `s`. -/
def xpWt : Bool → ℂ → ℝ
  | true, z => xpHS z.re * xpKS (z.re ^ 2 + z.im ^ 2)
  | false, z => (1 - xpHS z.re) * xpKS (z.re ^ 2 + z.im ^ 2)

/-- The open set on which the branch `s` is smooth. -/
def xpGood : Bool → ℂ → Prop
  | true, z => z ∈ Complex.slitPlane
  | false, z => -z ∈ Complex.slitPlane

lemma xpHS_of_le {t : ℝ} (h : t ≤ -1 / 8) : xpHS t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma xpHS_of_nonneg {t : ℝ} (h : 0 ≤ t) : xpHS t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma xpKS_of_le {t : ℝ} (h : t ≤ 1 / 16) : xpKS t = 0 := by
  have h' : 4 * t - 1 / 4 ≤ 0 := by linarith
  rw [xpKS, Real.smoothTransition.zero_of_nonpos h', zero_mul]

lemma xpKS_of_ge {t : ℝ} (h : 3 ≤ t) : xpKS t = 0 := by
  have h' : 3 - t ≤ 0 := by linarith
  rw [xpKS, Real.smoothTransition.zero_of_nonpos h', mul_zero]

lemma xpKS_one {t : ℝ} (h₁ : 5 / 16 ≤ t) (h₂ : t ≤ 2) : xpKS t = 1 := by
  have h₁' : 1 ≤ 4 * t - 1 / 4 := by linarith
  have h₂' : 1 ≤ 3 - t := by linarith
  rw [xpKS, Real.smoothTransition.one_of_one_le h₁', Real.smoothTransition.one_of_one_le h₂',
    mul_one]

lemma xpContDiff_HS : ContDiff ℝ (⊤ : ℕ∞) xpHS :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp
    ((contDiff_const.mul contDiff_id).add contDiff_const)

lemma xpContDiff_KS : ContDiff ℝ (⊤ : ℕ∞) xpKS := by
  have h₁ : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => 4 * t - 1 / 4) :=
    (contDiff_const.mul contDiff_id).sub contDiff_const
  have h₂ : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => 3 - t) := contDiff_const.sub contDiff_id
  exact ((Real.smoothTransition.contDiff (n := ⊤)).comp h₁).mul
    ((Real.smoothTransition.contDiff (n := ⊤)).comp h₂)

lemma xpContDiff_ThP : ContDiffOn ℝ (⊤ : ℕ∞) xpThP Complex.slitPlane := by
  have hlog : ContDiffOn ℝ (⊤ : ℕ∞) Complex.log Complex.slitPlane := fun z hz =>
    ((Complex.contDiffAt_log hz).restrict_scalars ℝ).contDiffWithinAt
  have him : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℂ => (Complex.log z).im) Complex.slitPlane :=
    Complex.imCLM.contDiff.comp_contDiffOn hlog
  exact him.div_const (2 * Real.pi)

lemma xpContDiff_ThM : ContDiffOn ℝ (⊤ : ℕ∞) xpThM {z : ℂ | -z ∈ Complex.slitPlane} := by
  have hlog : ContDiffOn ℝ (⊤ : ℕ∞) Complex.log Complex.slitPlane := fun z hz =>
    ((Complex.contDiffAt_log hz).restrict_scalars ℝ).contDiffWithinAt
  have hneg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℂ => -z) {z : ℂ | -z ∈ Complex.slitPlane} :=
    contDiff_neg.contDiffOn
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℂ => Complex.log (-z))
      {z : ℂ | -z ∈ Complex.slitPlane} :=
    hlog.comp hneg fun _ hz => hz
  have him : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℂ => (Complex.log (-z)).im)
      {z : ℂ | -z ∈ Complex.slitPlane} := Complex.imCLM.contDiff.comp_contDiffOn hcomp
  exact (him.div_const (2 * Real.pi)).add contDiff_const.contDiffOn

lemma xpIsOpen_good (s : Bool) : IsOpen (xpGood s) := by
  cases s
  · show IsOpen ((fun z : ℂ => -z) ⁻¹' Complex.slitPlane)
    exact Complex.isOpen_slitPlane.preimage continuous_neg
  · exact Complex.isOpen_slitPlane

lemma xpContDiffOn_ang (s : Bool) : ContDiffOn ℝ (⊤ : ℕ∞) (xpAng s) (xpGood s) := by
  cases s
  · exact xpContDiff_ThM
  · exact xpContDiff_ThP

lemma xpContDiff_wt (s : Bool) : ContDiff ℝ (⊤ : ℕ∞) (xpWt s) := by
  have hrad : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => xpKS (z.re ^ 2 + z.im ^ 2)) :=
    xpContDiff_KS.comp
      (((Complex.reCLM.contDiff).pow 2).add ((Complex.imCLM.contDiff).pow 2))
  cases s
  · have hstep : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => 1 - xpHS z.re) :=
      contDiff_const.sub (xpContDiff_HS.comp Complex.reCLM.contDiff)
    exact hstep.mul hrad
  · have hstep : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => xpHS z.re) :=
      xpContDiff_HS.comp Complex.reCLM.contDiff
    exact hstep.mul hrad

/-- If the weight of a branch does not vanish then the branch is smooth there. -/
lemma xpGood_of_wt {s : Bool} {z : ℂ} (h : xpWt s z ≠ 0) : xpGood s z := by
  have hks : xpKS (z.re ^ 2 + z.im ^ 2) ≠ 0 := fun h0 => by
    cases s
    · exact h (by simp [xpWt, h0])
    · exact h (by simp [xpWt, h0])
  have hnorm : 1 / 4 < ‖z‖ := by
    have h2 : (1 / 4 : ℝ) ^ 2 < ‖z‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      by_contra hcon
      exact hks (xpKS_of_le (by nlinarith [hcon]))
    nlinarith [norm_nonneg z]
  cases s
  · -- the branch `log (-z)`
    have hstep : 1 - xpHS z.re ≠ 0 := fun h0 => h (by simp [xpWt, h0])
    have hre : z.re < 0 := by
      by_contra hcon
      push_neg at hcon
      exact hstep (by simp [xpHS_of_nonneg hcon])
    change -z ∈ Complex.slitPlane
    rw [Complex.mem_slitPlane_iff]
    rcases eq_or_ne z.im 0 with him | him
    · left
      have h1 : ‖z‖ = |z.re| := by
        have h2 : ‖z‖ ^ 2 = |z.re| ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply, him, sq_abs]
          ring
        nlinarith [norm_nonneg z, abs_nonneg z.re]
      have h3 : -z.re = ‖z‖ := by
        rw [h1, abs_of_neg hre]
      rw [Complex.neg_re]
      linarith
    · right
      simpa using him
  · -- the principal branch
    have hstep : xpHS z.re ≠ 0 := fun h0 => h (by simp [xpWt, h0])
    have hre : -1 / 8 < z.re := by
      by_contra hcon
      push_neg at hcon
      exact hstep (xpHS_of_le hcon)
    change z ∈ Complex.slitPlane
    rw [Complex.mem_slitPlane_iff]
    rcases eq_or_ne z.im 0 with him | him
    · left
      have h2 : z.re ^ 2 > 1 / 16 := by
        have h3 : ‖z‖ ^ 2 = z.re ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply, him]
          ring
        nlinarith [hnorm, norm_nonneg z]
      nlinarith
    · right
      exact him

/-- The weight `xpWt false` vanishes near the non-smooth locus of its branch. -/
lemma xpTS_wt_false : tsupport (xpWt false) ⊆ {z : ℂ | -z ∈ Complex.slitPlane} := by
  intro z hz
  change -z ∈ Complex.slitPlane
  rw [Complex.mem_slitPlane_iff]
  by_contra hcon
  obtain ⟨hre, him⟩ := not_or.mp hcon
  have hre' : 0 ≤ z.re := by simpa using hre
  have him' : z.im = 0 := by simpa using him
  have hnts : xpWt false =ᶠ[nhds z] 0 := by
    rcases lt_or_eq_of_le hre' with hpos | heq
    · have hopen : {y : ℂ | 0 < y.re} ∈ nhds z :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hpos
      filter_upwards [hopen] with y hy
      simp [xpWt, xpHS_of_nonneg (le_of_lt hy)]
    · have hsmall : z.re ^ 2 + z.im ^ 2 < 1 / 16 := by
        rw [him']
        nlinarith
      have hopen : {y : ℂ | y.re ^ 2 + y.im ^ 2 < 1 / 16} ∈ nhds z :=
        (isOpen_lt ((Complex.continuous_re.pow 2).add (Complex.continuous_im.pow 2))
          continuous_const).mem_nhds hsmall
      filter_upwards [hopen] with y hy
      simp [xpWt, xpKS_of_le (le_of_lt hy)]
  exact (notMem_tsupport_iff_eventuallyEq.mpr hnts) hz

/-- The weight `xpWt true` vanishes near the non-smooth locus of its branch. -/
lemma xpTS_wt_true : tsupport (xpWt true) ⊆ Complex.slitPlane := by
  intro z hz
  rw [Complex.mem_slitPlane_iff]
  by_contra hcon
  obtain ⟨hre, him⟩ := not_or.mp hcon
  have him' : z.im = 0 := not_not.mp him
  have hnts : xpWt true =ᶠ[nhds z] 0 := by
    rcases lt_or_ge z.re (-1 / 8) with hlt | hge
    · have hopen : {y : ℂ | y.re < -1 / 8} ∈ nhds z :=
        (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hlt
      filter_upwards [hopen] with y hy
      simp [xpWt, xpHS_of_le (le_of_lt hy)]
    · have hsmall : z.re ^ 2 + z.im ^ 2 < 1 / 16 := by
        rw [him']
        nlinarith
      have hopen : {y : ℂ | y.re ^ 2 + y.im ^ 2 < 1 / 16} ∈ nhds z :=
        (isOpen_lt ((Complex.continuous_re.pow 2).add (Complex.continuous_im.pow 2))
          continuous_const).mem_nhds hsmall
      filter_upwards [hopen] with y hy
      simp [xpWt, xpKS_of_le (le_of_lt hy)]
  exact (notMem_tsupport_iff_eventuallyEq.mpr hnts) hz

lemma xpTS_wt (s : Bool) : tsupport (xpWt s) ⊆ xpGood s := by
  cases s
  · exact xpTS_wt_false
  · exact xpTS_wt_true

/-- The weight of a finite product vanishes where one factor vanishes. -/
lemma xpTS_prod {E : Type*} [TopologicalSpace E] {n : ℕ} (g : Fin n → ℂ → ℝ)
    (φ : Fin n → E → ℂ) (hφ : ∀ j, Continuous (φ j)) :
    tsupport (fun p : E => ∏ j, g j (φ j p)) ⊆ {p | ∀ j, φ j p ∈ tsupport (g j)} := by
  intro p hp
  by_contra hcon
  obtain ⟨j, hj⟩ := not_forall.mp hcon
  rw [notMem_tsupport_iff_eventuallyEq] at hj
  have hzero : (fun p' : E => ∏ j', g j' (φ j' p')) =ᶠ[nhds p] 0 := by
    have hj' : ∀ᶠ p' in nhds p, g j (φ j p') = 0 := (hφ j).tendsto p |>.eventually hj
    filter_upwards [hj'] with p' hp'
    exact Finset.prod_eq_zero (Finset.mem_univ j) hp'
  exact (notMem_tsupport_iff_eventuallyEq.mpr hzero) hp

/-- `exp (2 π i ·)` of the branch angle is the point itself on the unit circle. -/
lemma xpAng_spec {s : Bool} {z : ℂ} (hz : ‖z‖ = 1) (hgood : xpGood s z) :
    Complex.exp (2 * Real.pi * Complex.I * ((xpAng s z : ℝ) : ℂ)) = z := by
  have hsq : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h := Complex.sq_norm z
    rw [Complex.normSq_apply, hz] at h
    nlinarith [h]
  cases s
  · -- the branch `log (-z)`
    have hz0 : -z ≠ 0 := by
      intro h
      have h1 : ‖(-z : ℂ)‖ = 0 := by rw [h]; simp
      rw [norm_neg, hz] at h1
      norm_num at h1
    have hre : (Complex.log (-z)).re = 0 := by
      rw [Complex.log_re, norm_neg, hz]
      simp
    have hkey : Complex.exp (((Complex.log (-z)).im : ℂ) * Complex.I) = -z := by
      have hsplit : ((Complex.log (-z)).re : ℂ) + ((Complex.log (-z)).im : ℂ) * Complex.I
          = Complex.log (-z) := Complex.re_add_im _
      have h1 : Complex.exp (((Complex.log (-z)).re : ℂ))
            * Complex.exp (((Complex.log (-z)).im : ℂ) * Complex.I)
          = Complex.exp (Complex.log (-z)) := by
        rw [← Complex.exp_add, hsplit]
      rw [Complex.exp_log hz0] at h1
      have h2 : Complex.exp (((Complex.log (-z)).re : ℂ)) = 1 := by
        rw [hre]
        simp
      rw [h2, one_mul] at h1
      exact h1
    have hreal : 2 * Real.pi * xpAng false z = (Complex.log (-z)).im + Real.pi := by
      show 2 * Real.pi * ((Complex.log (-z)).im / (2 * Real.pi) + 1 / 2) = _
      first | (field_simp; ring) | field_simp
    have harith : 2 * Real.pi * Complex.I * ((xpAng false z : ℝ) : ℂ)
        = ((Complex.log (-z)).im : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I := by
      have h1 : 2 * Real.pi * Complex.I * ((xpAng false z : ℝ) : ℂ)
          = (((2 * Real.pi * xpAng false z : ℝ)) : ℂ) * Complex.I := by
        first | (push_cast; ring) | push_cast
      rw [h1, hreal]
      first | (push_cast; ring) | push_cast
    rw [harith, Complex.exp_add, hkey, Complex.exp_pi_mul_I]
    ring
  · -- the principal branch
    have hz0 : z ≠ 0 := by
      intro h
      have h1 : ‖z‖ = 0 := by rw [h]; simp
      rw [hz] at h1
      norm_num at h1
    have hre : (Complex.log z).re = 0 := by
      rw [Complex.log_re, hz]
      simp
    have hkey : Complex.exp (((Complex.log z).im : ℂ) * Complex.I) = z := by
      have hsplit : ((Complex.log z).re : ℂ) + ((Complex.log z).im : ℂ) * Complex.I
          = Complex.log z := Complex.re_add_im _
      have h1 : Complex.exp (((Complex.log z).re : ℂ))
            * Complex.exp (((Complex.log z).im : ℂ) * Complex.I)
          = Complex.exp (Complex.log z) := by
        rw [← Complex.exp_add, hsplit]
      rw [Complex.exp_log hz0] at h1
      have h2 : Complex.exp (((Complex.log z).re : ℂ)) = 1 := by
        rw [hre]
        simp
      rw [h2, one_mul] at h1
      exact h1
    have hreal : 2 * Real.pi * xpAng true z = (Complex.log z).im := by
      show 2 * Real.pi * ((Complex.log z).im / (2 * Real.pi)) = _
      first | (field_simp; ring) | field_simp
    have harith : 2 * Real.pi * Complex.I * ((xpAng true z : ℝ) : ℂ)
        = ((Complex.log z).im : ℂ) * Complex.I := by
      have h1 : 2 * Real.pi * Complex.I * ((xpAng true z : ℝ) : ℂ)
          = (((2 * Real.pi * xpAng true z : ℝ)) : ℂ) * Complex.I := by
        first | (push_cast; ring) | push_cast
      rw [h1, hreal]
    rw [harith, hkey]

/-- The two branch weights sum to `1` on the unit circle. -/
lemma xpWt_sum {z : ℂ} (hz : ‖z‖ = 1) : xpWt true z + xpWt false z = 1 := by
  have hsq : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h := Complex.sq_norm z
    rw [Complex.normSq_apply, hz] at h
    nlinarith [h]
  have hk : xpKS (z.re ^ 2 + z.im ^ 2) = 1 := by
    rw [hsq]
    exact xpKS_one (by norm_num) (by norm_num)
  simp only [xpWt]
  rw [hk]
  ring

/-- **Smooth gluing.**  If a smooth weight `w` has its (closed) support inside the open set on
which `f` is smooth, then `z ↦ w z • f z` is smooth everywhere. -/
lemma xpContDiff_smul_of_tsupport {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (w : E → ℝ) (U : Set E) (f : E → F)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hU : IsOpen U) (hws : tsupport w ⊆ U)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => w z • f z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport w
  · exact hw.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds (hws hz)))
  · have hev : (fun _ : E => (0 : F)) =ᶠ[nhds z] (fun y => w y • f y) := by
      have hmem : (tsupport w)ᶜ ∈ nhds z := (isClosed_tsupport w).isOpen_compl.mem_nhds hz
      filter_upwards [hmem] with y hy
      have h0 : w y = 0 := Function.notMem_support.mp fun h => hy (subset_closure h)
      simp [h0]
    exact (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq hev.symm

/-- The integer by which an angle representing `z` on the unit circle differs from a real
coordinate of `z`. -/
lemma xpAng_exists_int {s : Bool} {z : ℂ} {x : ℝ} (hz : ‖z‖ = 1) (hgood : xpGood s z)
    (hexp : z = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) :
    ∃ n : ℤ, xpAng s z = x + (n : ℝ) := by
  have h1 := xpAng_spec (s := s) hz hgood
  rw [hexp] at h1 ⊢
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h1
  refine ⟨n, ?_⟩
  have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    intro h0
    rcases mul_eq_zero.mp h0 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact two_ne_zero h'
      · exact hpi h'
    · exact hI h
  have h2 : (2 * Real.pi * Complex.I) * ((xpAng s (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) : ℝ) : ℂ)
      = (2 * Real.pi * Complex.I) * ((x + (n : ℝ) : ℝ) : ℂ) := by
    rw [hn]
    first | (push_cast; ring) | push_cast
  have h3 := mul_left_cancel₀ hne h2
  exact Complex.ofReal_injective h3

end Factor

/-- **The factorisation of a `1`-periodic smooth function through the character map.** -/
theorem periodic_factor_self : FactorStatement := by
  intro n m Φ hΦ hper
  -- step 1: periodicity under integer shifts
  have hnat : ∀ (t : ℕ) (j : Fin n) (y : Fin n → ℝ) (v : Fin m → ℂ),
      Φ (y + (t : ℝ) • (Pi.single j 1 : Fin n → ℝ), v) = Φ (y, v) := by
    intro t j y v
    induction t with
    | zero => simp
    | succ t ih =>
        have h1 : y + (((t + 1 : ℕ)) : ℝ) • (Pi.single j 1 : Fin n → ℝ)
            = (y + (t : ℝ) • (Pi.single j 1 : Fin n → ℝ)) + Pi.single j 1 := by
          ext i
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_add, Nat.cast_one]
          rcases eq_or_ne i j with rfl | hne
          · simp
            ring
          · rw [Pi.single_eq_of_ne hne]
            simp
        rw [h1, hper v j (y + (t : ℝ) • (Pi.single j 1 : Fin n → ℝ)), ih]
  have hneg : ∀ (t : ℕ) (j : Fin n) (y : Fin n → ℝ) (v : Fin m → ℂ),
      Φ (y - (t : ℝ) • (Pi.single j 1 : Fin n → ℝ), v) = Φ (y, v) := by
    intro t j y v
    induction t with
    | zero => simp
    | succ t ih =>
        have hkey : Φ (y - (t : ℝ) • (Pi.single j 1 : Fin n → ℝ), v)
            = Φ (y - (((t + 1 : ℕ)) : ℝ) • (Pi.single j 1 : Fin n → ℝ), v) := by
          have h := hper v j (y - (((t + 1 : ℕ)) : ℝ) • (Pi.single j 1 : Fin n → ℝ))
          have harith : y - (((t + 1 : ℕ)) : ℝ) • (Pi.single j 1 : Fin n → ℝ) + Pi.single j 1
              = y - (t : ℝ) • (Pi.single j 1 : Fin n → ℝ) := by
            ext i
            simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_add,
              Nat.cast_one]
            rcases eq_or_ne i j with rfl | hne
            · simp
              ring
            · rw [Pi.single_eq_of_ne hne]
              simp
          rw [harith] at h
          exact h
        rw [← hkey, ih]
  have hsingle : ∀ (k : ℤ) (j : Fin n) (y : Fin n → ℝ) (v : Fin m → ℂ),
      Φ (y + (k : ℝ) • (Pi.single j 1 : Fin n → ℝ), v) = Φ (y, v) := by
    intro k j y v
    obtain ⟨t, ht | ht⟩ := Int.eq_nat_or_neg k
    · rw [ht]
      have hc : (((t : ℤ)) : ℝ) = (t : ℝ) := by push_cast; ring
      rw [hc]
      exact hnat t j y v
    · rw [ht]
      have hc : ((-(t : ℤ) : ℤ) : ℝ) = -((t : ℝ)) := by push_cast; ring
      rw [hc, neg_smul]
      simpa [sub_eq_add_neg] using hneg t j y v
  have hint : ∀ (μ : Fin n → ℤ) (y : Fin n → ℝ) (v : Fin m → ℂ),
      Φ (y + (fun j => (μ j : ℝ)), v) = Φ (y, v) := by
    intro μ y v
    have key : ∀ S : Finset (Fin n),
        Φ (y + (fun j => if j ∈ S then (μ j : ℝ) else 0), v) = Φ (y, v) := by
      intro S
      induction S using Finset.induction with
      | empty =>
          have hzero : (fun j : Fin n => if j ∈ (∅ : Finset (Fin n)) then (μ j : ℝ) else 0)
              = (0 : Fin n → ℝ) := by
            funext j
            simp
          rw [hzero, add_zero]
      | insert a S ha ih =>
          have hsplit : (fun j : Fin n => if j ∈ insert a S then (μ j : ℝ) else 0)
              = (fun j => (if j ∈ S then (μ j : ℝ) else 0))
                + (μ a : ℝ) • (Pi.single a 1 : Fin n → ℝ) := by
            funext i
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            rcases eq_or_ne i a with rfl | hne
            · simp [Finset.mem_insert, ha]
            · by_cases hS : i ∈ S <;>
                simp [Finset.mem_insert, hne, hS, Pi.single_eq_of_ne hne]
          rw [hsplit, ← add_assoc, hsingle (μ a) a _ v, ih]
    have hone : (fun j : Fin n => (μ j : ℝ))
        = fun j => if j ∈ (Finset.univ : Finset (Fin n)) then (μ j : ℝ) else 0 := by
      funext j
      simp
    rw [hone]
    exact key Finset.univ
  -- step 2: the candidate factored function
  refine ⟨fun p : (Fin n → ℂ) × (Fin m → ℂ) =>
      ∑ s : Fin n → Bool, (∏ j, xpWt (s j) (p.1 j)) •
        Φ ((fun j => xpAng (s j) (p.1 j)), p.2), ?_, ?_⟩
  · -- smoothness
    refine ContDiff.sum fun s _ => ?_
    have hprojC : ∀ a : Fin n, ContDiff ℝ (⊤ : ℕ∞)
        (fun p : (Fin n → ℂ) × (Fin m → ℂ) => p.1 a) := fun a =>
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) a).comp
        (ContinuousLinearMap.fst ℝ (Fin n → ℂ) (Fin m → ℂ))).contDiff
    have hprojcont : ∀ a : Fin n, Continuous (fun p : (Fin n → ℂ) × (Fin m → ℂ) => p.1 a) :=
      fun a =>
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) a).comp
        (ContinuousLinearMap.fst ℝ (Fin n → ℂ) (Fin m → ℂ))).continuous
    have hw : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : (Fin n → ℂ) × (Fin m → ℂ) => ∏ j, xpWt (s j) (p.1 j)) := by
      have hgen : ∀ S : Finset (Fin n), ContDiff ℝ (⊤ : ℕ∞)
          (fun p : (Fin n → ℂ) × (Fin m → ℂ) => ∏ j ∈ S, xpWt (s j) (p.1 j)) := by
        intro S
        induction S using Finset.induction with
        | empty => simpa using contDiff_const
        | insert a S ha ih =>
            have heq : (fun p : (Fin n → ℂ) × (Fin m → ℂ) =>
                  ∏ j ∈ insert a S, xpWt (s j) (p.1 j))
                = fun p => xpWt (s a) (p.1 a) * ∏ j ∈ S, xpWt (s j) (p.1 j) := by
              funext p
              rw [Finset.prod_insert ha]
            rw [heq]
            exact ((xpContDiff_wt (s a)).comp (hprojC a)).mul ih
      simpa using hgen Finset.univ
    have hU : IsOpen {p : (Fin n → ℂ) × (Fin m → ℂ) | ∀ j, xpGood (s j) (p.1 j)} := by
      have heq : {p : (Fin n → ℂ) × (Fin m → ℂ) | ∀ j, xpGood (s j) (p.1 j)}
          = ⋂ j, {p | xpGood (s j) (p.1 j)} := by
        ext p
        simp [Set.mem_iInter]
      rw [heq]
      exact isOpen_iInter_of_finite fun j =>
        (xpIsOpen_good (s j)).preimage (hprojcont j)
    have hts : tsupport (fun p : (Fin n → ℂ) × (Fin m → ℂ) => ∏ j, xpWt (s j) (p.1 j))
        ⊆ {p | ∀ j, xpGood (s j) (p.1 j)} := by
      intro p hp j
      have h1 := xpTS_prod (fun j => xpWt (s j))
        (fun j (p : (Fin n → ℂ) × (Fin m → ℂ)) => p.1 j)
        (fun j => hprojcont j) hp
      exact xpTS_wt (s j) (h1 j)
    have hf : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : (Fin n → ℂ) × (Fin m → ℂ) => Φ ((fun j => xpAng (s j) (p.1 j)), p.2))
        {p | ∀ j, xpGood (s j) (p.1 j)} := by
      refine hΦ.contDiffOn.comp ?_ fun p _ => Set.mem_univ _
      refine ContDiffOn.prodMk ?_ ?_
      · refine contDiffOn_pi.mpr fun j => ?_
        exact (xpContDiffOn_ang (s j)).comp ((hprojC j).contDiffOn) fun p hp => hp j
      · exact (ContinuousLinearMap.snd ℝ (Fin n → ℂ) (Fin m → ℂ)).contDiff.contDiffOn
    exact xpContDiff_smul_of_tsupport
      (fun p : (Fin n → ℂ) × (Fin m → ℂ) => ∏ j, xpWt (s j) (p.1 j))
      {p : (Fin n → ℂ) × (Fin m → ℂ) | ∀ j, xpGood (s j) (p.1 j)}
      (fun p => Φ ((fun j => xpAng (s j) (p.1 j)), p.2)) hw hU hts hf
  · -- the value on the character torus
    intro x v
    let Z : Fin n → ℂ := fun j => Complex.exp (2 * Real.pi * Complex.I * (x j : ℂ))
    have hzn : ∀ j, ‖Z j‖ = 1 := by
      intro j
      show ‖Complex.exp (2 * Real.pi * Complex.I * (x j : ℂ))‖ = 1
      rw [Complex.norm_exp]
      have hre : (2 * Real.pi * Complex.I * (x j : ℂ)).re = 0 := by simp
      rw [hre]
      simp
    have hterm : ∀ s : Fin n → Bool,
        (∏ j, xpWt (s j) (Z j)) • Φ ((fun j => xpAng (s j) (Z j)), v)
          = (∏ j, xpWt (s j) (Z j)) • Φ (x, v) := by
      intro s
      by_cases h0 : (∏ j, xpWt (s j) (Z j)) = 0
      · rw [h0, zero_smul, zero_smul]
      · have hall : ∀ j, xpWt (s j) (Z j) ≠ 0 := fun j hj =>
          h0 (Finset.prod_eq_zero (Finset.mem_univ j) hj)
        have hval : Φ ((fun j => xpAng (s j) (Z j)), v) = Φ (x, v) := by
          have hmod : ∀ j, ∃ n : ℤ, xpAng (s j) (Z j) = x j + (n : ℝ) := fun j =>
            xpAng_exists_int (hzn j) (xpGood_of_wt (hall j)) rfl
          choose μ hμ using hmod
          have hfun : (fun j => xpAng (s j) (Z j)) = x + (fun j => (μ j : ℝ)) := by
            funext j
            rw [hμ j]
            simp
          rw [hfun, hint μ x v]
        rw [hval]
    have hsum1 : (∑ s : Fin n → Bool, ∏ j, xpWt (s j) (Z j)) = 1 := by
      have hconv : (∑ s : Fin n → Bool, ∏ j, xpWt (s j) (Z j))
          = ∑ s ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset Bool)),
              ∏ j, xpWt (s j) (Z j) := by
        rw [Fintype.piFinset_univ]
      rw [hconv, Finset.sum_prod_piFinset (s := (Finset.univ : Finset Bool))
        (g := fun (j : Fin n) (b : Bool) => xpWt b (Z j))]
      refine Finset.prod_eq_one fun j _ => ?_
      rw [Fintype.sum_bool]
      exact xpWt_sum (hzn j)
    show (∑ s : Fin n → Bool, (∏ j, xpWt (s j) (Z j)) •
        Φ ((fun j => xpAng (s j) (Z j)), v)) = Φ (x, v)
    calc (∑ s : Fin n → Bool, (∏ j, xpWt (s j) (Z j)) • Φ ((fun j => xpAng (s j) (Z j)), v))
        = ∑ s : Fin n → Bool, (∏ j, xpWt (s j) (Z j)) • Φ (x, v) :=
          Finset.sum_congr rfl fun s _ => hterm s
      _ = (∑ s : Fin n → Bool, ∏ j, xpWt (s j) (Z j)) • Φ (x, v) := by
          rw [Finset.sum_smul]
      _ = Φ (x, v) := by rw [hsum1, one_smul]

/-- **The Moser composition estimate for a `1`-periodic nonlinearity** (the requested lemma). -/
theorem CSq_comp_xperiodic_le {n m : ℕ} (s ρ : ℕ) (hρ : n < 2 * ρ) (hρs : ρ ≤ s)
    (Φ : (Fin n → ℝ) × (Fin m → ℂ) → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hper : ∀ (v : Fin m → ℂ) (i : Fin n) (x : Fin n → ℝ), Φ (x + Pi.single i 1, v) = Φ (x, v))
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : (Fin n → ℤ) → (Fin m → ℂ)),
      (∀ N : ℕ, Summable (fun k : (Fin n → ℤ) => (Work.Diff.STE.wt k) ^ N * ‖c k‖)) →
      (∑ i : Fin m, Work.Diff.STE.CSq ρ (fun k : (Fin n → ℤ) => c k i)) ≤ B ^ 2 →
      Summable (fun k : (Fin n → ℤ) => (Work.Diff.STE.wt k) ^ s *
        ‖Work.Diff.STE.fourierCoeff (fun x : Fin n → ℝ =>
          Φ (x, fun i : Fin m => Work.Diff.STE.seriesFun (fun k => c k i) x)) k‖ ^ 2) ∧
      Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x : Fin n → ℝ =>
          Φ (x, fun i : Fin m => Work.Diff.STE.seriesFun (fun k => c k i) x)))
        ≤ C * (1 + ∑ i : Fin m, Work.Diff.STE.CSq s (fun k : (Fin n → ℤ) => c k i)) :=
  CSq_comp_xperiodic_le_of_factor periodic_factor_self s ρ hρ hρs Φ hΦ hper B hB

end

end Work.Diff.STE.flat

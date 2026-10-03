/-
# Corollary `struct-dual` of §5.2 from Proposition `lip-2` (the second dual function)

Krause--Mirek--Tao, §5.2: from Proposition `lip-2` (the alternate inverse theorem for the second
function `g`, formalised in the workspace as `Work.KMTAreas.A4Z.LipOutputGenTwo`) one deduces the
structural decomposition of the *second* dual function `Ã_N^{**}(f,h)`
(Corollary `struct-dual`), namely a decomposition

`Ã_N^{**}(f,h) = ∑_i w_i · λ_i • φ_i + E₁ + E₂`

with `φ_i` in the family `structPhiTwo` (pointwise `≤ C₁δ^{-K₁}`, `ℓ¹`-norm `≤ C₁δ^{-K₁}N^d`,
Fourier support in a major arc of scales `2^l ≤ C₁δ^{-K₁}`, `2^k ≤ C₁δ^{-K₁}/N^d`), non-negative
weights with `∑ w_i ≤ 1`, coefficients `‖λ_i‖ ≤ 4δ^{1-K₁}`, `‖E₁‖_{ℓ¹} ≤ δN^d` and
`‖E₂‖_{ℓ²} ≤ δ`.

## Structure of the proof

The paper's argument is the Hahn--Banach separation of §5 (Lemma `hahn`, formalised in the
workspace as `Work.KMTAreas.A4.hahn_decomposition`) applied to the dual function, with the inverse
theorem `lip-2` providing the "Hahn hypothesis"

  `∀ u ∈ ℓ²(ℤ), ‖u‖_∞ ≤ 1,  |⟨u, Ã_N^{**}(f,h)⟩| > δN^d  ⟹  ∃ φ ∈ Φ, |⟨u,φ⟩| > δ^{K₁}N^d/4.`

This file

* defines the second dual function as an element `ahalfStarTwoL2` of `ℓ²(ℤ)` (needed because the
  Hahn--Banach lemma is stated for `ℓ²(ℤ)`-vectors);
* isolates the above Hahn hypothesis as the predicate `HahnHypTwo`;
* proves the *assembly*: `StructDecompClaim P` from `HahnHypTwo` (a purely bookkeeping step which
  calls `Work.KMTAreas.A4.hahn_decomposition` with `A = δN^d`, `B = δ^{K₁}N^d/4`, `ε = δ`);
* states the remaining input — `HahnHypTwo` from `lip-2`, i.e. from the hypothesis `hLip` of the
  target theorem — as the theorem `hahnHypTwo_of_lipGen`, and finally derives the target from it.

The input `LipOutputGenTwo` now carries, besides the `ℓ²` tail clause with the free parameter
`R ≥ 1`, the *`ℓ¹` tail clause at the window* `∑_{|x|>AN^d}‖G x‖ ≤ δ^K N^d/2` (the analogue of
`A4.LipOutputTail`'s clause); it is exactly this clause that the Hahn--Banach step below consumes,
in the form `|Σ_{x ∉ [-AN^d,AN^d]} star(u x) G x| ≤ ∑_{|x|>AN^d}‖G x‖`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4Z.propdualSecondClaim_of_structDecompClaim
import Submission.Work.KMTAreas.A4.structATail

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger (L2Z)
open Work.Analysis.InverseTheory
open Work.Analysis.EndVar

namespace Work.KMTAreas.A4Z

open Work.KMTAreas.A4 (MemL1Ball)

/-! ## The second dual function as an element of `ℓ²(ℤ)` -/

/-- A function supported in `[-R,R]` lies in `ℓ²(ℤ)`. -/
theorem memℓp_of_supportIn_two {f : ℤ → ℂ} {R : ℕ} (hR : SupportIn f R) : Memℓp f 2 := by
  refine memℓp_gen ?_
  rw [show ((2 : ℝ≥0∞)).toReal = 2 by norm_num]
  refine summable_of_ne_finset_zero (s := Finset.Icc (-(R : ℤ)) (R : ℤ)) fun x hx => ?_
  have hx' : R < x.natAbs := by
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h <;> omega
  rw [hR x hx']
  simp

/-- The second dual function `Ã_N^{**}(f,h)` is supported in the window `N₀ + Mp·N^d`, where
`Mp = ∑_j |coeff_j|` bounds the polynomial shifts `P(n)`, `n ∈ [1,N]`. -/
theorem supportIn_AhalfTranspose₂_coeffSum (P : Polynomial ℤ) {N N₀ : ℕ} (hN : 1 ≤ N)
    {f h : ℤ → ℂ} (hhs : SupportIn h N₀) :
    SupportIn (AhalfTranspose₂ N P f h)
      (N₀ + (∑ j ∈ P.support, |P.coeff j|).natAbs * N ^ P.natDegree) :=
  supportIn_AhalfTranspose₂ P hhs fun n hn => eval_le_coeff_sum_of_mem_Icc P hN hn

/-- The second dual function `Ã_N^{**}(f,h)` as an element of `ℓ²(ℤ)`, for a window `[-R,R]`
containing its support. -/
noncomputable def ahalfStarTwoL2 (N : ℕ) (P : Polynomial ℤ) (f h : ℤ → ℂ) (R : ℕ)
    (hR : SupportIn (AhalfTranspose₂ N P f h) R) : L2Z :=
  ⟨fun x : ℤ => AhalfTranspose₂ N P f h x, memℓp_of_supportIn_two hR⟩

@[simp] theorem ahalfStarTwoL2_apply (N : ℕ) (P : Polynomial ℤ) (f h : ℤ → ℂ) (R : ℕ)
    (hR : SupportIn (AhalfTranspose₂ N P f h) R) (x : ℤ) :
    ahalfStarTwoL2 N P f h R hR x = AhalfTranspose₂ N P f h x := rfl

/-! ## The Hahn--Banach hypothesis of Corollary `struct-dual` -/

/-- **The Hahn--Banach hypothesis of Corollary `struct-dual`** (Krause--Mirek--Tao §5.2, the
content of Corollary `struct-dual` beyond the functional-analytic Lemma `hahn`): under the
hypotheses of Proposition `lip-2`, every `1`-bounded `u ∈ ℓ²(ℤ)` whose pairing with the second dual
function `Ã_N^{**}(f,h)` exceeds `δN^d` correlates with an element of the family `structPhiTwo`
beyond `δ^{K₁}N^d/4`.

Feeding this to `Work.KMTAreas.A4.hahn_decomposition` produces the paper's decomposition
`Ã_N^{**}(f,h) = ∑_i w_i · λ_i • φ_i + E₁ + E₂`. -/
def HahnHypTwo (P : Polynomial ℤ) (C₁ K₁ : ℝ) : Prop :=
  ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
  ∀ (N N₀ R : ℕ) (δ : ℝ) (f h : ℤ → ℂ), (hR : SupportIn (AhalfTranspose₂ N P f h) R) →
    1 ≤ N → 0 < δ → δ ≤ 1 →
    (N : ℝ) ^ P.natDegree / 2 ≤ (N₀ : ℝ) → (N₀ : ℝ) ≤ (N : ℝ) ^ P.natDegree →
    SupportIn f N₀ → SupportIn h N₀ →
    (∀ x : ℤ, ‖f x‖ ≤ 1) → (∀ x : ℤ, ‖h x‖ ≤ 1) →
    ∀ u : L2Z, (∀ x : ℤ, ‖u x‖ ≤ 1) →
      δ * (N : ℝ) ^ P.natDegree < ‖inner ℂ u (ahalfStarTwoL2 N P f h R hR)‖ →
      ∃ φ ∈ structPhiTwo P ρ C₁ K₁ δ N,
        δ ^ K₁ * (N : ℝ) ^ P.natDegree / 4 < ‖inner ℂ u φ‖

/-! ## The assembly of Corollary `struct-dual` -/

/-- The elementary identity `A / B = 4 δ^{1-K}` for `A = δN^d` and `B = δ^K N^d/4`. -/
theorem div_eq_four_rpow {δ Nd K : ℝ} (hδ : 0 < δ) (hNd : 0 < Nd) :
    δ * Nd / (δ ^ K * Nd / 4) = 4 * δ⁻¹ ^ (K - 1) := by
  have hdiv : δ * Nd / (δ ^ K * Nd / 4) = 4 * (δ / δ ^ K) := by
    field_simp
  have h1 : δ / δ ^ K = δ ^ (1 - K) := by
    rw [eq_comm, Real.rpow_sub hδ (1 : ℝ) K, Real.rpow_one]
  have h2 : δ ^ (1 - K) = δ⁻¹ ^ (K - 1) := by
    rw [Real.inv_rpow hδ.le (K - 1), ← Real.rpow_neg hδ.le (K - 1),
      show -(K - 1) = 1 - K by ring]
  rw [hdiv, h1, h2]

/-- **Corollary `struct-dual` from the Hahn--Banach hypothesis.**  Given the Hahn hypothesis
`HahnHypTwo P C₁ K₁`, the second dual function decomposes as in `StructDecompTwo` with the
constants `C₁, K₁`. -/
theorem structDecompClaim_of_hahnHyp (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) {C₁ K₁ : ℝ}
    (hC₁ : 0 < C₁) (hK₁ : 0 < K₁) (h : HahnHypTwo P C₁ K₁) : StructDecompClaim P := by
  refine ⟨C₁, K₁, hC₁, hK₁, ?_⟩
  intro ρ hρ0 hρ1 N N₀ δ f h₂ hN hδ0 hδ1 hN0lo hN0hi hfs hhs hf1 hh1
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hNdpos : (0 : ℝ) < (N : ℝ) ^ P.natDegree := pow_pos hNpos _
  have hApos : 0 < δ * (N : ℝ) ^ P.natDegree := mul_pos hδ0 hNdpos
  have hBpos : 0 < δ ^ K₁ * (N : ℝ) ^ P.natDegree / 4 := by
    have := Real.rpow_pos_of_pos hδ0 K₁
    positivity
  set R : ℕ := N₀ + (∑ j ∈ P.support, |P.coeff j|).natAbs * N ^ P.natDegree with hRdef
  have hR : SupportIn (AhalfTranspose₂ N P f h₂) R :=
    supportIn_AhalfTranspose₂_coeffSum P hN hhs
  have hHahn : ∀ u : L2Z, (∀ x : ℤ, ‖u x‖ ≤ 1) →
      δ * (N : ℝ) ^ P.natDegree < ‖inner ℂ u (ahalfStarTwoL2 N P f h₂ R hR)‖ →
      ∃ φ ∈ structPhiTwo P ρ C₁ K₁ δ N,
        δ ^ K₁ * (N : ℝ) ^ P.natDegree / 4 < ‖inner ℂ u φ‖ :=
    h ρ hρ0 hρ1 N N₀ R δ f h₂ hR hN hδ0 hδ1 hN0lo hN0hi hfs hhs hf1 hh1
  obtain ⟨ι, hι, s, φ, lam, w, e₁, e₂, hφmem, hlam, hw0, hwsum, he₁, he₂, hid⟩ :=
    Work.KMTAreas.A4.hahn_decomposition hApos hBpos (ahalfStarTwoL2 N P f h₂ R hR)
      (structPhiTwo P ρ C₁ K₁ δ N) hHahn hδ0
  refine ⟨ι, hι, s, φ, lam, w, e₁, e₂, hφmem, ?_, hw0, hwsum, ?_, ?_, ?_⟩
  · -- the coefficient bound
    intro i hi
    have hbound := hlam i hi
    rwa [div_eq_four_rpow hδ0 hNdpos] at hbound
  · -- the `ℓ¹`-error
    exact he₁
  · exact he₂
  · -- the pointwise identity
    intro x
    have hx := congrArg (fun v : L2Z => (v : ℤ → ℂ) x) hid
    have hsum : ((∑ i ∈ s, w i • (lam i • φ i)) + e₁ + e₂ : L2Z) x
        = (∑ i ∈ s, w i • (lam i • φ i)) x + e₁ x + e₂ x := rfl
    rw [← hsum, ← hx]
    exact (ahalfStarTwoL2_apply N P f h₂ R hR x).symm

/-! ## The remaining input: the Hahn hypothesis from Proposition `lip-2`

The two lemmas below are the proof of the isolated input `hahnHypTwo_of_lipGen`, produced by the
delegated prover of `Submission/Work/A4Z/hahnHypTwo_of_lipGen.lean` (same fleet, same workspace)
and transferred here because that module imports this one.  The `open`s of `Work.KMTAreas.A4`
provide the truncated test function `lipInputW` and its elementary properties.
-/

open Work.KMTAreas.A4 (lipInputW supportIn_lipInputW lipInputW_eq_star lipInputW_eq_zero
  norm_lipInputW_le_one norm_tsum_mul_sub_lipInputW_le memℓp_of_l1)
open Work.KMTAreas.A4Z (ahalfStarTwoL2 ahalfStarTwoL2_apply supportIn_AhalfTranspose₂
  eval_le_coeff_sum_of_mem_Icc structPhiTwo LipOutputGenTwo HahnHypTwo)

/-- **The trilinear form of the truncated conjugate is the inner product with the second dual
function**, the form of the transposition identity `(transpose)` consumed by the Hahn--Banach step
of Corollary `struct-dual`:

`⟨Ã_N(f, 1_{[-B,B]}·star∘u), h⟩ = ⟨u, Ã_N^{**}(f,h)⟩`.

The hypothesis `N₀ + Mp N^d ≤ ⌊B⌋` says that the truncation window `[-B,B]` contains the support
`[-N₀ - Mp N^d, N₀ + Mp N^d]` of `Ã_N^{**}(f,h)` (`Mp` bounding the polynomial shifts `P(n)`,
`n ≤ N`), so that the truncation is invisible to the pairing. -/
theorem bilinPair_lipInputW_eq_innerTwo (P : Polynomial ℤ) {N N₀ Mp R : ℕ} {B : ℝ}
    (hB0 : 0 ≤ B) (hMle : N₀ + Mp * N ^ P.natDegree ≤ Nat.floor B)
    (hMp : ∀ n : ℤ, n ∈ Finset.Icc (1 : ℤ) (N : ℤ) →
      |P.eval n| ≤ (Mp : ℤ) * (N : ℤ) ^ P.natDegree)
    {f h : ℤ → ℂ} (hfs : SupportIn f N₀) (hhs : SupportIn h N₀)
    {u : L2Z} (hR : SupportIn (AhalfTranspose₂ N P f h) R) :
    bilinPair (AhalfZ N P f (lipInputW P B (fun x : ℤ => u x))) h
      = inner ℂ u (ahalfStarTwoL2 N P f h R hR) := by
  rw [bilinPair_AhalfZ_eq_transpose₂ (FinSupp.of_supportIn hfs)
    (FinSupp.of_supportIn (supportIn_lipInputW P B _)) (FinSupp.of_supportIn hhs) N P]
  simp only [bilinPair, lp.inner_eq_tsum]
  refine tsum_congr fun x => ?_
  by_cases hx : (x.natAbs : ℝ) ≤ B
  · rw [lipInputW_eq_star hx, ahalfStarTwoL2_apply, RCLike.inner_apply]
    simp only [starRingEnd_apply]
  · have hxB : B < (x.natAbs : ℝ) := lt_of_not_ge hx
    have hlt : Nat.floor B < x.natAbs := (Nat.floor_lt hB0).mpr hxB
    rw [lipInputW_eq_zero hxB, ahalfStarTwoL2_apply, RCLike.inner_apply,
      supportIn_AhalfTranspose₂ P hhs hMp x (by omega)]
    simp

/-- **The Hahn--Banach hypothesis of Corollary `struct-dual` from Proposition `lip-2`** (the input
`hLip` of the target theorem): there are constants `C₁, K₁`, depending only on `P` and on the
constants supplied by `hLip`, for which `HahnHypTwo` holds.

`hLip` is applied at the fixed window `A = 2(1 + Mp)`, `Mp = ∑_j |coeff_j P|`, to the truncated
conjugate `lipInputW P (A N^d) u` of the test function `u`; the constants returned are absorbed by
`C₁ = C·A`, `K₁ = K`.  The `ℓ¹`-fringe clause of `LipOutputGenTwo` (at the same window `A N^d`)
supplies the error of the truncation. -/
theorem hahnHypTwo_of_lipGen (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) (hLip : ∀ (A : ℝ), 1 ≤ A → ∃ C K C0 K2 : ℝ, 0 < C ∧ 0 < K ∧ 0 < C0 ∧ 0 < K2 ∧ ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → Work.KMTAreas.A4Z.LipOutputGenTwo P ρ A C K C0 K2) : ∃ C₁ K₁ : ℝ, 0 < C₁ ∧ 0 < K₁ ∧ Work.KMTAreas.A4Z.HahnHypTwo P C₁ K₁ := by
  -- the support scale `Mp` of the polynomial shifts and the window `A = 2(1+Mp)`
  set Mp : ℕ := (∑ j ∈ P.support, |P.coeff j|).natAbs with hMpdef
  have hMpnn : (0 : ℝ) ≤ (Mp : ℝ) := Nat.cast_nonneg _
  set Al : ℝ := 2 * ((Mp : ℝ) + 1) with hAdef
  have hAl1 : 1 ≤ Al := by rw [hAdef]; linarith
  have hAlpos : 0 < Al := lt_of_lt_of_le zero_lt_one hAl1
  obtain ⟨C, K, C0, K2, hC, hK, hC0, hK2, hOut⟩ := hLip Al hAl1
  refine ⟨C * Al, K, mul_pos hC hAlpos, hK, ?_⟩
  intro ρ hρ0 hρ1 N N₀ R δ f h hR hN hδ0 hδ1 hN0lo hN0hi hfs hhs hf1 hh1 u hu1 hbig
  have hd1 : 1 ≤ P.natDegree := le_trans (by norm_num) hP
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hNdpos : (0 : ℝ) < (N : ℝ) ^ P.natDegree := pow_pos hNpos _
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNd1 : (1 : ℝ) ≤ (N : ℝ) ^ P.natDegree := one_le_pow₀ hN1
  -- the truncation window `B = A N^d` and its integral part
  set B : ℝ := Al * (N : ℝ) ^ P.natDegree with hBdef
  have hBpos : 0 < B := by rw [hBdef]; exact mul_pos hAlpos hNdpos
  have hB2 : 2 ≤ B := by
    rw [hBdef, hAdef]
    nlinarith [hMpnn, hNd1]
  set M : ℕ := Nat.floor B with hMdef
  have hMhi : (M : ℝ) ≤ Al * (N : ℝ) ^ P.natDegree := by
    rw [← hBdef]; exact Nat.floor_le hBpos.le
  have hMlo : Al * (N : ℝ) ^ P.natDegree / 2 ≤ (M : ℝ) := by
    have h1 : B < (M : ℝ) + 1 := Nat.lt_floor_add_one B
    rw [hBdef] at h1
    linarith
  have hN0leM : N₀ ≤ M := by
    rw [hMdef]
    apply Nat.le_floor
    rw [hBdef, hAdef]
    have h1 : (1 : ℝ) ≤ 2 * ((Mp : ℝ) + 1) := by linarith
    calc (N₀ : ℝ) ≤ (N : ℝ) ^ P.natDegree := hN0hi
      _ = 1 * (N : ℝ) ^ P.natDegree := (one_mul _).symm
      _ ≤ 2 * ((Mp : ℝ) + 1) * (N : ℝ) ^ P.natDegree :=
          mul_le_mul_of_nonneg_right h1 hNdpos.le
  have hN0Mp : N₀ + Mp * N ^ P.natDegree ≤ Nat.floor B := by
    apply Nat.le_floor
    rw [hBdef, hAdef]
    push_cast
    have h1 : (N₀ : ℝ) + (Mp : ℝ) * (N : ℝ) ^ P.natDegree
        ≤ ((Mp : ℝ) + 1) * (N : ℝ) ^ P.natDegree := by nlinarith [hN0hi]
    have h2 : ((Mp : ℝ) + 1) * (N : ℝ) ^ P.natDegree
        ≤ 2 * ((Mp : ℝ) + 1) * (N : ℝ) ^ P.natDegree := by nlinarith [hMpnn, hNdpos]
    linarith
  -- the polynomial-shift bound
  have hMpbound : ∀ n : ℤ, n ∈ Finset.Icc (1 : ℤ) (N : ℤ) →
      |P.eval n| ≤ (Mp : ℤ) * (N : ℤ) ^ P.natDegree := by
    intro n hn
    have h := eval_le_coeff_sum_of_mem_Icc P hN hn
    simpa only [hMpdef] using h
  -- the correlation hypothesis of `lip-2`, through the transposition identity
  have hkey : δ * (N : ℝ) ^ P.natDegree
      ≤ ‖bilinPair (AhalfZ N P f (lipInputW P B (fun x : ℤ => u x))) h‖ := by
    rw [bilinPair_lipInputW_eq_innerTwo P hBpos.le hN0Mp hMpbound hfs hhs hR]
    exact le_of_lt hbig
  obtain ⟨G, l, k, hGpt, hGsum, hGl1, hGsupp, hGl, hGk, hGcorr, hGtail, hGR⟩ :=
    hOut ρ hρ0 hρ1 N M δ f (lipInputW P B (fun x : ℤ => u x)) h hN hδ0 hδ1
      hMlo hMhi (hfs.mono hN0leM) (supportIn_lipInputW P B _) (hhs.mono hN0leM)
      hf1 (norm_lipInputW_le_one P B (fun x : ℤ => hu1 x)) hh1 hkey
  -- the output as an element of `ℓ²(ℤ)`
  have hBoundpos : 0 < C * Al * δ⁻¹ ^ K :=
    mul_pos (mul_pos hC hAlpos) (Real.rpow_pos_of_pos (inv_pos.mpr hδ0) K)
  set φ : L2Z := ⟨G, memℓp_of_l1 hBoundpos.le hGsum hGpt⟩ with hφdef
  have hφapply : ∀ x : ℤ, φ x = G x := fun x => rfl
  refine ⟨φ, ?_, ?_⟩
  · -- `φ` belongs to the family `Φ₂` with the constants `C₁ = C·A`, `K₁ = K`
    refine ⟨fun x => ?_, ?_, ?_, ⟨l, k, ?_, hGl, hGk⟩⟩
    · rw [hφapply]; exact hGpt x
    · simpa only [hφapply] using hGsum
    · simpa only [hφapply] using hGl1
    · simpa only [hφapply] using hGsupp
  · -- the correlation
    have hδK : 0 < δ ^ K * (N : ℝ) ^ P.natDegree :=
      mul_pos (Real.rpow_pos_of_pos hδ0 K) (pow_pos hNpos _)
    have hsumS : Summable fun x : ℤ =>
        G x * (star (u x) - lipInputW P B (fun x : ℤ => u x) x) := by
      refine Summable.of_norm ?_
      have hbS : ∀ x : ℤ, ‖star (u x) - lipInputW P B (fun x : ℤ => u x) x‖ ≤ 2 := by
        intro x
        calc ‖star (u x) - lipInputW P B (fun x : ℤ => u x) x‖
            ≤ ‖star (u x)‖ + ‖lipInputW P B (fun x : ℤ => u x) x‖ := norm_sub_le _ _
          _ ≤ 1 + 1 := by
              rw [norm_star]
              exact add_le_add (hu1 x) (norm_lipInputW_le_one P B (fun x : ℤ => hu1 x) x)
          _ = 2 := by norm_num
      refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_) (hGsum.mul_left 2)
      rw [norm_mul]
      simpa [mul_comm] using mul_le_mul_of_nonneg_right (hbS x) (norm_nonneg (G x))
    have hsumA : Summable fun x : ℤ => G x * lipInputW P B (fun x : ℤ => u x) x := by
      refine Summable.of_norm ?_
      refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_) (hGsum.mul_left 1)
      rw [norm_mul]
      simpa [mul_comm] using mul_le_mul_of_nonneg_right
        (norm_lipInputW_le_one P B (fun x : ℤ => hu1 x) x) (norm_nonneg (G x))
    have hinner : inner ℂ u φ = ∑' x : ℤ, G x * star (u x) := by
      rw [lp.inner_eq_tsum]
      refine tsum_congr fun x => ?_
      rw [RCLike.inner_apply, starRingEnd_apply, hφapply]
    have hpair : bilinPair (lipInputW P B (fun x : ℤ => u x)) G
        = ∑' x : ℤ, G x * lipInputW P B (fun x : ℤ => u x) x := by
      simp only [bilinPair]
      exact tsum_congr fun x => mul_comm _ _
    have hsplit : (∑' x : ℤ, G x * star (u x))
        = bilinPair (lipInputW P B (fun x : ℤ => u x)) G
          + ∑' x : ℤ, G x * (star (u x) - lipInputW P B (fun x : ℤ => u x) x) := by
      rw [hpair, ← hsumA.tsum_add hsumS]
      refine tsum_congr fun x => ?_
      ring
    have htail : ‖∑' x : ℤ, G x * (star (u x) - lipInputW P B (fun x : ℤ => u x) x)‖
        ≤ ∑' x : ℤ, (if B < (x.natAbs : ℝ) then ‖G x‖ else 0) :=
      norm_tsum_mul_sub_lipInputW_le (fun x : ℤ => hu1 x) hGsum
    have hGtail' : ∑' x : ℤ, (if B < (x.natAbs : ℝ) then ‖G x‖ else 0)
        ≤ δ ^ K * (N : ℝ) ^ P.natDegree / 2 := by
      have hfun : (fun x : ℤ => (if B < (x.natAbs : ℝ) then ‖G x‖ else 0))
          = fun x : ℤ => (if B < |(x : ℝ)| then ‖G x‖ else 0) := by
        funext x
        have hcast : ((x.natAbs : ℕ) : ℝ) = |(x : ℝ)| := by
          rw [← Int.cast_abs, Int.abs_eq_natAbs]; norm_num
        rw [hcast]
      rw [hfun]
      exact hGtail
    have hmain : ‖inner ℂ u φ‖
        ≥ ‖bilinPair (lipInputW P B (fun x : ℤ => u x)) G‖
          - ‖∑' x : ℤ, G x * (star (u x) - lipInputW P B (fun x : ℤ => u x) x)‖ := by
      rw [hinner, hsplit]
      have h2 : ‖bilinPair (lipInputW P B (fun x : ℤ => u x)) G‖
          ≤ ‖bilinPair (lipInputW P B (fun x : ℤ => u x)) G
              + ∑' x : ℤ, G x * (star (u x) - lipInputW P B (fun x : ℤ => u x) x)‖
            + ‖∑' x : ℤ, G x * (star (u x) - lipInputW P B (fun x : ℤ => u x) x)‖ := by
        have := norm_add_le (bilinPair (lipInputW P B (fun x : ℤ => u x)) G
          + ∑' x : ℤ, G x * (star (u x) - lipInputW P B (fun x : ℤ => u x) x))
          (-(∑' x : ℤ, G x * (star (u x) - lipInputW P B (fun x : ℤ => u x) x)))
        simpa using this
      linarith
    linarith [hGcorr, htail.trans hGtail', hmain, hδK]

theorem structDecompClaim_of_lipGen (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) (hLip : ∀ (A : ℝ), 1 ≤ A → ∃ C K C0 K2 : ℝ, 0 < C ∧ 0 < K ∧ 0 < C0 ∧ 0 < K2 ∧ ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → Work.KMTAreas.A4Z.LipOutputGenTwo P ρ A C K C0 K2) : Work.KMTAreas.A4Z.StructDecompClaim P := by
  obtain ⟨C₁, K₁, hC₁, hK₁, hHahn⟩ := hahnHypTwo_of_lipGen P hP hLip
  exact structDecompClaim_of_hahnHyp P hP hC₁ hK₁ hHahn

end Work.KMTAreas.A4Z

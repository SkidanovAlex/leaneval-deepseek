import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Core.nr_ablock
import Submission.Work.TMC16Core.Core.nr_endgame
import Submission.Work.TMC16Core.Core.Uniform_equiv
import Submission.Work.TMC16Core.NrFinal.nr_regular

/-!
# The `s = 0` branch of AJ §9 (Lemma 9.4(2)): windows and endgame

AJ's non-resonant Lemma 9.4 has two parts.  Part (1) (`s ≥ 1`) is `Assembly.nr_case1_full`.
Part (2) is the case `s = 0`, i.e. `k₀ = dist(y, qₙℤ) < q_{n-1}`: the site `y` sits within
`q_{n-1}` of a multiple `M = m qₙ` of `qₙ`, and AJ uses two windows of *total* length `H`
(`H = q_{n-1}`, or `qₙ`, or `2q_{n-1}`), at scale `K = H - 1`:

* `W₁`, of length `2U`, sitting inside `[-(1-δ)K, -δK]`; its phases are those of `A_K`, so the
  singularity of `0` bounds the continuants there (`Core.nr_ablock`);
* `W₂`, the translate by `M` of the *complementary* index interval, of length `H - 2U`.

The pairing is forced by the trigonometric-product estimate: the union must be a *shifted
block* `{k + ℓ_k qₙ}` (`ℓ_k ∈ {0, m}`), which is what AJ's `shift1` controls.  In *site*
coordinates (phases `θ + (x + (K-1)/2)α`) the two windows are therefore

`W₁ = [a, a+2U-1]`,  `W₂ = [M + a + 2U, M + a + H - 1]`.

This file proves the *endgame*: the `A`-bound on `W₁` (`Core.nr_ablock`), the non-generation
step (`NrFinal.site_step_gen_c_lt`) and the Cramér/non-`A` step (`Core.nr_endgame`) give
`IsRegularBig` at the site `y`.  In the `s = 0` case the `A`-deficit is `εsing·δ - εf` with
`δ ≈ 1/40`, so the decay rate produced is `≈ L + εf - 40(εf + εA)`, which is what makes the
weak geometry `dist(y, ∂I) ≥ K/40` sufficient (in contrast with the `s ≥ 1` branch, where the
geometry `≥ K/4` is needed).

The uniformity statement (AJ's Lemma `di`) for the three sub-cases is stated separately in
`Assembly.S0Uniform`.
-/

namespace Work.TMC16Core.Assembly

open Work.TMC16Core
open Work.TMC16Core.Core

noncomputable section

/-! ## The windows -/

/-- The first `s = 0` window, of `2U` *sites*, starting at `a`. -/
def W1s0 (a : ℤ) (U : ℕ) : Finset ℤ := Finset.Icc a (a + 2 * (U : ℤ) - 1)

/-- The second `s = 0` window: the translate by `M` of the complementary index interval,
of `H - 2U` sites. -/
def W2s0 (a : ℤ) (U H : ℕ) (M : ℤ) : Finset ℤ :=
  Finset.Icc (M + a + 2 * (U : ℤ)) (M + a + (H : ℤ) - 1)

/-! ## Window arithmetic -/

theorem s0_card {a M : ℤ} {U H : ℕ} (h2U : 2 * U ≤ H) (hM : 0 ≤ M) :
    (W1s0 a U ∪ W2s0 a U H M).card = H := by
  have hdisj : Disjoint (W1s0 a U) (W2s0 a U H M) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [W1s0, W2s0, Finset.mem_Icc] at hx1 hx2
    obtain ⟨h1, h2⟩ := hx1
    obtain ⟨h3, h4⟩ := hx2
    omega
  rw [Finset.card_union_of_disjoint hdisj]
  have h1 : (W1s0 a U).card = 2 * U := by
    rw [W1s0]
    rcases Nat.eq_zero_or_pos U with hU | hU
    · subst hU; simp
    · rw [Int.card_Icc]
      have h : ((a + 2 * (U : ℤ) - 1) + 1 - a : ℤ) = ((2 * U : ℕ) : ℤ) := by
        push_cast; ring
      rw [h, Int.toNat_natCast]
  have h2 : (W2s0 a U H M).card = H - 2 * U := by
    rw [W2s0, Int.card_Icc]
    have h : ((M + a + (H : ℤ) - 1) + 1 - (M + a + 2 * (U : ℤ)) : ℤ) =
        ((H - 2 * U : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub h2U]
      ring
    rw [h, Int.toNat_natCast]
  rw [h1, h2]
  omega

/-- Containment of the first window in the singular-point strip `[-(1-δ)K, -δK]`. -/
theorem s0_sub {a : ℤ} {U : ℕ} {δ K : ℝ}
    (h1 : -((1 - δ) * K) ≤ (a : ℝ))
    (h2 : (a : ℝ) + 2 * (U : ℝ) - 1 ≤ -(δ * K)) :
    ∀ x ∈ W1s0 a U, -((1 - δ) * K) ≤ (x : ℝ) ∧ (x : ℝ) ≤ -(δ * K) := by
  intro x hx
  simp only [W1s0, Finset.mem_Icc] at hx
  obtain ⟨hx1, hx2⟩ := hx
  constructor
  · have h : ((a : ℤ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
    linarith
  · have h : (x : ℝ) ≤ ((a : ℤ) : ℝ) + 2 * (U : ℝ) - 1 := by
      have h'' : ((x : ℤ) : ℝ) ≤ ((a + 2 * (U : ℤ) - 1 : ℤ) : ℝ) := by
        exact_mod_cast hx2
      push_cast at h''
      linarith [h'']
    linarith

/-- **Geometry of the second window.**  If `y` is at distance `≥ ⌈K/40⌉` inside `W₂` (i.e. at
distance `≥ K/40` from `∂W₂` and inside the `K`-interval starting at `min W₂`) then every site
of `W₂` witnesses `IsRegularBig`'s distance condition. -/
theorem s0_geo {a M : ℤ} {U H K : ℕ} {y : ℤ} (hKH : K = H - 1) (hH : 1 ≤ H)
    (h1 : M + a + (H : ℤ) - 1 + (((K + 39) / 40 : ℕ) : ℤ) ≤ y)
    (h2 : y ≤ M + a + 2 * (U : ℤ) + (K : ℤ) - 1 - (((K + 39) / 40 : ℕ) : ℤ)) :
    ∀ x ∈ W2s0 a U H M, x ≤ y ∧ y ≤ x + (K : ℤ) - 1 ∧
      (K : ℤ) ≤ 40 * (y - x) ∧ (K : ℤ) ≤ 40 * ((x + (K : ℤ) - 1) - y) := by
  have hKZ : (K : ℤ) = (H : ℤ) - 1 := by
    rw [hKH, Nat.cast_sub hH]
    push_cast
    ring
  have hceil : (K : ℕ) ≤ 40 * ((K + 39) / 40) := by
    have := Nat.div_mul_le_self (K + 39) 40
    omega
  have hceilZ : (K : ℤ) ≤ 40 * ((((K + 39) / 40 : ℕ)) : ℤ) := by
    exact_mod_cast hceil
  intro x hx
  simp only [W2s0, Finset.mem_Icc] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hHZ : (H : ℤ) = (K : ℤ) + 1 := by omega
  have h1K : M + a + (K : ℤ) + ((((K + 39) / 40 : ℕ)) : ℤ) ≤ y := by omega
  have h2K : y ≤ M + a + 2 * (U : ℤ) + (K : ℤ) - 1 - ((((K + 39) / 40 : ℕ)) : ℤ) := by
    omega
  have h3 : ((((K + 39) / 40 : ℕ)) : ℤ) ≤ y - x := by omega
  have h4 : ((((K + 39) / 40 : ℕ)) : ℤ) ≤ x + (K : ℤ) - 1 - y := by omega
  refine ⟨by omega, by omega, ?_, ?_⟩
  · have : 40 * ((((K + 39) / 40 : ℕ)) : ℤ) ≤ 40 * (y - x) :=
      mul_le_mul_of_nonneg_left h3 (by norm_num)
    linarith [hceilZ, this]
  · have : 40 * ((((K + 39) / 40 : ℕ)) : ℤ) ≤ 40 * (x + (K : ℤ) - 1 - y) :=
      mul_le_mul_of_nonneg_left h4 (by norm_num)
    linarith [hceilZ, this]

/-! ## The endgame of the `s = 0` branch -/

/-- **The `s = 0` endgame.**  With the `A`-bound on `W₁` coming from the singularity of `0`
(`Core.nr_ablock`), `εu`-uniformity on `W₁ ∪ W₂`, the non-generation gap `hgap` and the Cramér
arithmetic `hkey0`, the site `y` is `(L₁, K)`-regular. -/
theorem s0_case {α lam L εu εf εsing δ εA L₁ : ℝ} {H U K : ℕ} {a M : ℤ} {y : ℤ} {θ : ℝ}
    {E : ℂ}
    (hKH : K = H - 1)
    (hlam : 0 < lam) (hLlog : L = Real.log lam) (hL : 0 < L)
    (hεf : 0 < εf) (hεsing : 0 < εsing) (hεsingL : εsing ≤ L)
    (hδ1 : 1 / 40 ≤ δ) (hδ2 : δ ≤ 1 / 2)
    (hK40 : 40 ≤ K) (hKδ : 1 ≤ (K : ℝ) * (δ - 1 / 40))
    (hAeq : εA = εsing * δ - εf)
    (hbd : ∀ N : ℕ, K / 40 ≤ N → N ≤ K → ∀ ζ : ℝ,
      ‖pd α lam ζ E (N + 1)‖ ≤ Real.exp ((N : ℝ) * (L + εf)))
    (hsin : IsSingular α lam θ E (L - εsing) K 0)
    (hsub : ∀ x ∈ W1s0 a U, -((1 - δ) * (K : ℝ)) ≤ (x : ℝ) ∧
      (x : ℝ) ≤ -(δ * (K : ℝ)))
    (hεu : 0 < εu) (hεA0 : 0 < εA) (hεuA : εu < εA) (hεfA : εf < εA)
    (huni : Uniform εu (fun j : {j : ℤ // j ∈ W1s0 a U ∪ W2s0 a U H M} =>
      θ + (((j : ℤ) : ℝ) + (((K : ℝ) - 1) / 2)) * α))
    (hcard : (W1s0 a U ∪ W2s0 a U H M).card = K + 1)
    (hgap : 4 * ((K : ℝ) + 1) * Real.exp (L - εA) < Real.exp ((K : ℝ) * (εA - εu)))
    (hgeo : ∀ x ∈ W2s0 a U H M, x ≤ y ∧ y ≤ x + (K : ℤ) - 1 ∧
      (K : ℤ) ≤ 40 * (y - x) ∧ (K : ℤ) ≤ 40 * ((x + (K : ℤ) - 1) - y))
    (hL₁ : 0 < L₁) (hL₁le : L₁ ≤ L + εf)
    (hkey0 : (L + εf) * ((K : ℝ) - 1 - (K : ℝ) / 40) - ((K : ℝ) + 1) * (L - εA)
      + L₁ * ((K : ℝ) / 40) < 0) :
    IsRegularBig α lam θ E L₁ (K : ℝ) y := by
  have hK1 : 1 ≤ K := by omega
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    have : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
    linarith
  have hH1 : 1 ≤ H := by omega
  haveI : Nonempty (Fin 1) := ⟨0⟩
  -- ## 1. The `A`-bound on `W₁`, from the singularity of `0`
  have hAraw := Core.nr_ablock (α := α) (lam := lam) (E := E) (θ := θ) (L := L)
    (ε₁ := εf) (εsing := εsing) (δ := δ) (K := K) (I₁ := W1s0 a U)
    hL hεf hεsing hεsingL hδ1 hδ2 hK40 hKδ hbd hsin hsub
  have hA : ∀ x ∈ W1s0 a U, ‖pd α lam (θ + (x : ℝ) * α) E (K + 1)‖ ≤
      Real.exp (((K : ℝ) + 1) * (L - εA)) := by
    intro x hx
    refine le_trans (hAraw x hx) (Real.exp_le_exp.mpr ?_)
    have h : L - εsing * δ + εf = L - εA := by linarith [hAeq]
    rw [h]
  -- ## 2. A site of `W₂` with an exponentially large continuant
  have hthr : (K : ℝ) * (((K : ℝ) + 1) * (L - εA) / (K : ℝ))
      ≤ ((K : ℝ) + 1) * (L - εA) := by
    rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hKpos)]
  obtain ⟨x₁, hx₁, hbig⟩ :=
    NrFinal.site_step_gen_c_lt (α := α) (lam := lam) (L := L) (εA := εA) (ε₁ := εu)
      (c := ((K : ℝ) + 1) * (L - εA) / (K : ℝ)) (E := E) (θ := θ) (K := K)
      (I₁ := W1s0 a U) (I₂ := W2s0 a U H M)
      hlam hLlog hεu hεuA hεA0 hgap hthr hcard huni hA
  have hlarge : Real.exp (((K : ℝ) + 1) * (L - εA))
      < ‖pd α lam (θ + (x₁ : ℝ) * α) E (K + 1)‖ := by
    have hcK : (((K : ℝ) + 1) * (L - εA) / (K : ℝ)) * (K : ℝ)
        = ((K : ℝ) + 1) * (L - εA) := div_mul_cancel₀ _ (ne_of_gt hKpos)
    rwa [hcK] at hbig
  -- ## 3. Geometry and the Cramér bookkeeping
  obtain ⟨hx1y, hyx2, hd1, hd2⟩ := hgeo x₁ hx₁
  have hn₀ : K / 40 ≤ (y - x₁).toNat := by omega
  have hn₁ : K / 40 ≤ (x₁ + (K : ℤ) - 1 - y).toNat := by omega
  have hd1R : (K : ℝ) ≤ 40 * ((y - x₁ : ℤ) : ℝ) := by exact_mod_cast hd1
  have hd2R : (K : ℝ) ≤ 40 * (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ) := by exact_mod_cast hd2
  have hnn1 : (0 : ℝ) ≤ ((y - x₁ : ℤ) : ℝ) := by
    have : (0 : ℤ) ≤ y - x₁ := by omega
    exact_mod_cast this
  have hnn2 : (0 : ℝ) ≤ (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ) := by
    have : (0 : ℤ) ≤ x₁ + (K : ℤ) - 1 - y := by omega
    exact_mod_cast this
  have hsum : ((y - x₁ : ℤ) : ℝ) + (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ)
      = (K : ℝ) - 1 := by
    push_cast
    ring
  have hd2le : (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ) ≤ (K : ℝ) - 1 - (K : ℝ) / 40 := by
    have : (K : ℝ) / 40 ≤ ((y - x₁ : ℤ) : ℝ) := by linarith [hd1R]
    linarith
  have hd1le : ((y - x₁ : ℤ) : ℝ) ≤ (K : ℝ) - 1 - (K : ℝ) / 40 := by
    have : (K : ℝ) / 40 ≤ (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ) := by linarith [hd2R]
    linarith
  have hcoef : L₁ - L - εf ≤ 0 := by linarith [hL₁le]
  have hd1ge : (K : ℝ) / 40 ≤ ((y - x₁ : ℤ) : ℝ) := by linarith [hd1R]
  have hd2ge : (K : ℝ) / 40 ≤ (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ) := by linarith [hd2R]
  have hdec1 : (L + εf) * (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ)
      - ((K : ℝ) + 1) * (L - εA) ≤ -L₁ * ((y - x₁ : ℤ) : ℝ) := by
    have hd2eq : (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ) = (K : ℝ) - 1 - ((y - x₁ : ℤ) : ℝ) := by
      linarith [hsum]
    have h2 : ((y - x₁ : ℤ) : ℝ) * (L₁ - L - εf) ≤ ((K : ℝ) / 40) * (L₁ - L - εf) := by
      simpa only [mul_comm] using mul_le_mul_of_nonpos_left hd1ge hcoef
    rw [hd2eq]
    nlinarith [h2, hkey0]
  have hdec2 : (L + εf) * ((y - x₁ : ℤ) : ℝ) - ((K : ℝ) + 1) * (L - εA)
      ≤ -L₁ * (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ) := by
    have hd1eq : ((y - x₁ : ℤ) : ℝ) = (K : ℝ) - 1 - (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ) := by
      linarith [hsum]
    have h2 : (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ) * (L₁ - L - εf)
        ≤ ((K : ℝ) / 40) * (L₁ - L - εf) := by
      simpa only [mul_comm] using mul_le_mul_of_nonpos_left hd2ge hcoef
    rw [hd1eq]
    nlinarith [h2, hkey0]
  -- ## 4. The endgame
  exact Work.TMC16Core.Core.nr_endgame (α := α) (lam := lam) (E := E) (θ := θ) (L := L)
    (ε := εA) (ε₁ := εf) (m := L₁) (K := K) (y := y) (j₀ := x₁)
    hL hεfA hL₁ hK1 hx1y hyx2 hd1 hd2 hn₀ hn₁ hlarge hbd hdec1 hdec2

end

end Work.TMC16Core.Assembly

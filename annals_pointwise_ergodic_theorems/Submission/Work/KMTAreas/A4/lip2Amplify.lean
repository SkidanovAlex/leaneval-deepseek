/-
# `Work.KMTAreas.A4.lip2Amplify`

The "amplification" step of Krause--Mirek--Tao §5.2 (the inverse Weyl / Green--Tao
"recurrent linear functions are major arc" step):

if `T ⊆ [-N,N]` has density at least `δ₂` and every `β n` (`n ∈ T`) is within `δ₁` of an
integer, with `50 δ₁ ≤ δ₂²`, then `β` is within `2^20 δ₁ / (δ₂³(2N+1))` of a rational with
denominator at most `2^20/δ₂`.

The proof is the classical amplification: the `k`-fold sumset `kSum T k` (`k = ⌊δ₂/(64δ₁)⌋`)
sits in `[-kN,kN]`, retains density `δ₂/4` (Freiman's sumset bound, which *preserves* the
density instead of squaring it), and has all its elements within `kδ₁` of integers; applying
the Erdős--Turán engine `denseMultiples_engine` to it and dividing by the extra length `k`
gives the required quality.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.denseMultiples_engine
import Submission.Work.KMTAreas.A4.kSum_nDist

namespace Work.KMTAreas.A4

open scoped BigOperators Pointwise

/-- **The amplification step, in the general (paper) regime.**  Here the only hypothesis on the two
accuracy parameters is `16 δ₁ ≤ δ₂` (plus `δ₂ ≤ 1`); the paper's `AmplifyStatement` supplies this
from `16 δ₁ ≤ δ₂²` together with `δ₂ ≤ 1/2`, and the frozen `lip2Amplify` from `50 δ₁ ≤ δ₂²`.
Everything else in the argument (the `k`-fold sumset with `k = max 1 ⌊δ₂/(64δ₁)⌋`, the density
`δ₂/4` from Freiman's bound, and the Erdős--Turán engine) is independent of that choice. -/
theorem lip2AmplifyCore (β δ₁ δ₂ : ℝ) (N : ℕ) (T : Finset ℤ) (hN : 1 ≤ N) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₂1 : δ₂ ≤ 1) (h16 : 16 * δ₁ ≤ δ₂) (hdens : 1 ≤ δ₂ * ((N : ℝ) + 1)) (hT : ∀ n ∈ T, -(N : ℤ) ≤ n ∧ n ≤ (N : ℤ)) (hcard : δ₂ * (2 * (N : ℝ) + 1) ≤ (T.card : ℝ)) (hgood : ∀ n ∈ T, ∃ m : ℤ, |β * (n : ℝ) - (m : ℝ)| ≤ δ₁) : ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ 2 ^ 20 / δ₂ ∧ ∃ a : ℤ, |β - (a : ℝ) / (q : ℝ)| ≤ 2 ^ 20 * δ₁ / (δ₂ ^ 3 * (2 * (N : ℝ) + 1)) := by
  -- `T` is nonempty
  have hTcardpos : 0 < T.card := by
    have h1 : (0 : ℝ) < δ₂ * (2 * (N : ℝ) + 1) := by positivity
    have h2 : (0 : ℝ) < (T.card : ℝ) := lt_of_lt_of_le h1 hcard
    exact_mod_cast h2
  have hTne : T.Nonempty := Finset.card_pos.mp hTcardpos
  -- the number of summands
  set k : ℕ := max 1 ⌊δ₂ / (64 * δ₁)⌋₊ with hk
  have hk1 : 1 ≤ k := by rw [hk]; exact le_max_left _ _
  have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have hkle : (k : ℝ) ≤ max 1 (δ₂ / (64 * δ₁)) := by
    rw [hk, Nat.cast_max, Nat.cast_one]
    exact max_le_max le_rfl (Nat.floor_le (by positivity))
  -- (A) `16 k δ₁ ≤ δ₂` : the engine's `4 (k δ₁) ≤ ρ` with `ρ = δ₂/4`
  have hkA : 16 * (k : ℝ) * δ₁ ≤ δ₂ := by
    have hxle : 16 * (δ₂ / (64 * δ₁)) * δ₁ ≤ δ₂ := by
      have hcalc : 16 * (δ₂ / (64 * δ₁)) * δ₁ = δ₂ / 4 := by
        field_simp
        ring
      rw [hcalc]; linarith
    have hstep : 16 * (k : ℝ) * δ₁ ≤ 16 * (max 1 (δ₂ / (64 * δ₁))) * δ₁ := by
      nlinarith [hkle, hδ₁]
    rcases le_or_gt (δ₂ / (64 * δ₁)) 1 with hcase | hcase
    · rw [max_eq_left hcase] at hstep
      linarith
    · rw [max_eq_right (le_of_lt hcase)] at hstep
      linarith
  -- (B) `3 δ₂/512 ≤ k δ₁` : the amplification of the quality
  have hkB : 3 * δ₂ / 512 ≤ (k : ℝ) * δ₁ := by
    rcases le_or_gt (δ₂ / (64 * δ₁)) 2 with h2 | h2
    · -- x ≤ 2 forces `δ₂ ≤ 128 δ₁`, and then `3 δ₂/512 ≤ (3/4) δ₁ ≤ k δ₁`
      have hx2 : δ₂ ≤ 128 * δ₁ := by
        have h3 := (div_le_iff₀ (by positivity : (0 : ℝ) < 64 * δ₁)).mp h2
        linarith
      nlinarith [hx2, hk1R, hδ₁]
    · -- x > 2 : `k > x/2 = δ₂/(128 δ₁)`, so `k δ₁ > δ₂/128 ≥ 3δ₂/512`
      have hfl : (δ₂ / (64 * δ₁)) / 2 < ((⌊δ₂ / (64 * δ₁)⌋₊ : ℕ) : ℝ) := by
        have := Nat.lt_floor_add_one (δ₂ / (64 * δ₁))
        linarith
      have hkge' : ((⌊δ₂ / (64 * δ₁)⌋₊ : ℕ) : ℝ) ≤ (k : ℝ) := by
        rw [hk, Nat.cast_max]
        exact le_max_right _ _
      have hxhalf : δ₂ / (128 * δ₁) = (δ₂ / (64 * δ₁)) / 2 := by
        rw [div_div]; congr 1; ring
      have hkδ : δ₂ / 128 < (k : ℝ) * δ₁ := by
        have h1 : δ₂ / (128 * δ₁) < (k : ℝ) := by rw [hxhalf]; linarith
        have h2' : δ₂ / (128 * δ₁) * δ₁ = δ₂ / 128 := by field_simp
        nlinarith [h1, hδ₁, h2']
      nlinarith [hkδ]
  -- the amplified set
  set A : Finset ℤ := kSum T k with hA
  have hAsub : ∀ a ∈ A, -(((k * N : ℕ)) : ℤ) ≤ a ∧ a ≤ (((k * N : ℕ)) : ℤ) := by
    intro a ha
    exact kSum_subset_bounds N k T hT a (by rwa [hA] at ha)
  have hAgood : ∀ a ∈ A, ∃ m : ℤ, |β * (a : ℝ) - (m : ℝ)| ≤ (k : ℝ) * δ₁ := by
    intro a ha
    have ha' : a ∈ kSum T k := by rwa [hA] at ha
    have hnd := kSum_nDist_le k T β δ₁
      (fun n hn => (nDist_le_abs_sub_int _ _).trans ((hgood n hn).choose_spec)) a ha'
    exact ⟨round (β * (a : ℝ)), by simpa [nDist] using hnd⟩
  have hAcard : (δ₂ / 4) * (2 * ((k * N : ℕ) : ℝ) + 1) ≤ (A.card : ℝ) := by
    simpa [hA] using kSum_card_dens T hTne hk1 hδ₂ hδ₂1 hdens hcard
  -- the engine
  have hkN1 : 1 ≤ k * N := by
    have := Nat.mul_pos hk1 hN
    omega
  have hρδ : 4 * ((k : ℝ) * δ₁) ≤ δ₂ / 4 := by linarith [hkA]
  obtain ⟨q, hq1, hqle, a, ha⟩ :=
    denseMultiples_engine β ((k : ℝ) * δ₁) (by positivity) (k * N) hkN1 A hAsub hAgood
      (δ₂ / 4) (by linarith) hρδ hAcard
  refine ⟨q, hq1, ?_, a, ?_⟩
  · have h32 : (8 : ℝ) / (δ₂ / 4) = 32 / δ₂ := by field_simp; norm_num
    rw [h32] at hqle
    have hsub : (32 : ℝ) / δ₂ ≤ 2 ^ 20 / δ₂ := by
      apply div_le_div_of_nonneg_right _ hδ₂.le
      norm_num
    linarith
  · have hρ2 : (δ₂ / 4) ^ 2 = δ₂ ^ 2 / 16 := by ring
    have hkn : (2 * ((k * N : ℕ) : ℝ) + 1) = 2 * (k : ℝ) * (N : ℝ) + 1 := by
      rw [Nat.cast_mul]; ring
    rw [hρ2, hkn] at ha
    have hfin : 2 ^ 8 / (δ₂ ^ 2 / 16 * (2 * (k : ℝ) * (N : ℝ) + 1)) ≤
        2 ^ 20 * δ₁ / (δ₂ ^ 3 * (2 * (N : ℝ) + 1)) := by
      have h1 : (0 : ℝ) < δ₂ ^ 2 / 16 * (2 * (k : ℝ) * (N : ℝ) + 1) := by positivity
      have h2 : (0 : ℝ) < δ₂ ^ 3 * (2 * (N : ℝ) + 1) := by positivity
      rw [div_le_div_iff₀ h1 h2]
      have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := by linarith
      have hstep1 : 2 ^ 8 * (δ₂ ^ 3 * (2 * (N : ℝ) + 1)) ≤
          2 ^ 8 * (δ₂ ^ 3 * (3 * (N : ℝ))) := by nlinarith [hN1, hδ₂]
      have hstep2 : 2 ^ 20 * δ₁ * (δ₂ ^ 2 / 16 * (2 * (k : ℝ) * (N : ℝ))) ≤
          2 ^ 20 * δ₁ * (δ₂ ^ 2 / 16 * (2 * (k : ℝ) * (N : ℝ) + 1)) := by
        have : (0 : ℝ) ≤ 2 ^ 20 * δ₁ * (δ₂ ^ 2 / 16) := by positivity
        nlinarith
      have hstep3 : 2 ^ 8 * (δ₂ ^ 3 * (3 * (N : ℝ))) ≤
          2 ^ 20 * δ₁ * (δ₂ ^ 2 / 16 * (2 * (k : ℝ) * (N : ℝ))) := by
        nlinarith [hkB, hδ₂, hN0]
      linarith
    linarith [ha, hfin]

/-- **The amplification step of Krause--Mirek--Tao §5.2** (Green--Tao's `Lemma 3.1(ii)`): if
`T ⊆ [-N,N]` has density at least `δ₂` and every `β n` (`n ∈ T`) is within `δ₁` of an integer, with
`50 δ₁ ≤ δ₂²`, then `β` is within `2^20 δ₁/(δ₂³(2N+1))` of a rational of denominator `≤ 2^20/δ₂`.

This is `lip2AmplifyCore` with `16 δ₁ ≤ δ₂` deduced from `50 δ₁ ≤ δ₂²` and `δ₂ ≤ 1`. -/
theorem lip2Amplify (β δ₁ δ₂ : ℝ) (N : ℕ) (T : Finset ℤ) (hN : 1 ≤ N) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₂1 : δ₂ ≤ 1) (hsmall : 50 * δ₁ ≤ δ₂ ^ 2) (hdens : 1 ≤ δ₂ * ((N : ℝ) + 1)) (hT : ∀ n ∈ T, -(N : ℤ) ≤ n ∧ n ≤ (N : ℤ)) (hcard : δ₂ * (2 * (N : ℝ) + 1) ≤ (T.card : ℝ)) (hgood : ∀ n ∈ T, ∃ m : ℤ, |β * (n : ℝ) - (m : ℝ)| ≤ δ₁) : ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ 2 ^ 20 / δ₂ ∧ ∃ a : ℤ, |β - (a : ℝ) / (q : ℝ)| ≤ 2 ^ 20 * δ₁ / (δ₂ ^ 3 * (2 * (N : ℝ) + 1)) :=
  lip2AmplifyCore β δ₁ δ₂ N T hN hδ₁ hδ₂ hδ₂1 (by nlinarith [hsmall, hδ₂, hδ₂1]) hdens hT hcard hgood

end Work.KMTAreas.A4

import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.MMHelpers
import Submission.Work.HP.MM2.Dmix_split
import Submission.Work.HP.MM2.Sigma1mix_estimate
import Submission.Work.HP.MM2.Sigma2mix_bound
import Submission.Work.HP.MM2.Dloc_estimate

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/HP/DESIGN.md (the lead's design for Browning–Le Boudec–Sawin, with its two replacements: the ρLoc existence sandwich and the Planes44 lemma) and FEASIBILITY.md. Shared definitions: Submission/Work/HP/Defs.lean (do NOT edit). No Deligne / Lang–Weil / Poonen–Voloch needed. Siblings run in parallel.

          └──(cone version)────────────────────────── N09 moment_mix_loc ─────────────────┼─ N10 prop1 ─┐
N11 nonarch ─┬─ N13 prop2 ─────────────────────────────────────────────────────────────────────────┤
N12 arch ────┘   (N13 also uses N03 cone count)                                                     ├─ Assembly
N14 density (uses N01, N11 σ-lemmas, N12 boundary lemma) ───────────────────────────────────────────┤
N15 conics (uses N01) ──────────────────────────────────────────────────────────────────────────────┘
```

**Day 1** (no node dependencies): N01, N02, N03, N11, N12, N15, and the internal Planes44 algebra lemma of N06.
**Day 2:** N04, N14 (once the N11/N12 exports exist), N13.
**Then:** N05 → N06, N07 → N08, N09 → N10.

## Assembly (proved)

This is the proof in `Assembly.lean`.
* **hasse_most** (N10 + N13, φ = 1/η). For a ∈ LocSet(w(A/η)) with no rational zero, NV(a,A/η) = 0. So either |NV − NVloc| > φ^{2/3} or NVloc ≤ φ^{2/3}. That gives count ≤ (K₁+K₂)A^N η^{1/24n}.
* **main.**
  * **(2,2).** ρ ≤ loc ≤ ratio(∀p, zero mod p²) → 0 (N02, N15). So both → 0.
  * **Otherwise n ≥ 3.** With L from N14 (w(A) = wOf(A/η) → ∞ and ≤ A):
    * ρ ≤ loc ≤ ratio(LocSet(w(A/η))) → L;
    * ρ ≥ ratio(LocSet) − (K/c)η^κ, by N01 (c A^N ≤ #ball) and hasse_most.
    * With ε → η, both ρ → L and loc → L.
  * Finally ρLoc = limUnder loc = L (`Tendsto.limUnder_eq`), using N02(ii) to rewrite ρLoc.

## Nodes

### N01 `count_basic`  (file `Submission/Work/HP/CountBasic.lean`)

* **Depends on:** —
* **Size:** 3–4k
* **Risk:** low

```lean
/ -- N01. Height balls are finite and contain `≫ A^N` primitive vectors. - /
theorem count_basic (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) :
    (∀ (A : ℝ) (P : (Mon d n → ℤ) → Prop), (primSet d n A P).Finite) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ A in atTop, c * A ^ NN d n ≤ primCount d n A (fun _ => True) := by
  ‹proof›
```

**Route.**

**Finiteness.** `primSet ⊆ {a : ∀ m, |a m| ≤ ⌈A⌉}`, which is a finite box (Set.Finite.subset of a Fintype image).

**Lower bound.**
* Take the vectors a whose coordinate at one fixed monomial m₀ is 1 and whose other coordinates have |a_m| ≤ A/(2√N). All of these are primitive and have norm ≤ A.
* That gives ≥ (A/(2√N))^{N−1} of them, which only has exponent N−1. That is not enough.
* **Use instead** the Möbius lower bound #{prim, ‖a‖≤A} ≥ #{a ≠ 0 : ‖a‖ ≤ A} − Σ_{k≥2} #{a ≠ 0 : ‖a‖ ≤ A/k}.
* The pieces:
  * Box counts give #{‖a‖≤T} ≥ (2⌊T/√N⌋+1)^N and #{‖a‖≤T} ≤ (2T+1)^N.
  * Σ_{k≥2} k^{−N} ≤ 2^{1−N}·… < 1/2 once the box constants are handled (N ≥ 6 here, since N = C(n+d,d) ≥ C(4,2)).
  * If this is fiddly, use the owned `card_int_points_ball_le_volume` together with Mathlib's lattice-point count in balls.
* The node also provides the residue-class upper bound that N11, N13 and N14 use (keep it as an internal lemma in the same file): #{a : ‖a‖ ≤ A, a ≡ b mod q} ≤ (2A/q+1)^N.

### N02 `bridge`  (file `Submission/Work/HP/Bridge.lean`)

* **Depends on:** N01
* **Size:** 3–5k
* **Risk:** medium (adele API is thin)

```lean
/ -- N02. Bridge from the challenge's projective objects to primitive coefficient vectors. - /
-/

namespace Work.HP

/-- N09. Estimates D^mix and D^loc. -/
theorem moment_mix_loc (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (h22 : (d, n) ≠ (2, 2)) :
    ∃ K B₀ : ℝ, ∀ A B : ℝ, B₀ ≤ B → B ^ ((5 : ℝ) / 6) ≤ A → A ≤ B ^ 2 →
      |Dmix d n A B - mainTerm d n A B| ≤ K * mainTerm d n A B / Real.log A ^ ((1 : ℝ) / 2) ∧
      |Dloc d n A B - mainTerm d n A B| ≤ K * mainTerm d n A B / Real.log A ^ ((1 : ℝ) / 2) := by
  obtain ⟨K₁, B₁, hS1⟩ := MM2.Sigma1mix_estimate d n hd hdn h22
  obtain ⟨K₂, B₂, hS2⟩ := MM2.Sigma2mix_bound d n hd hdn h22
  obtain ⟨K₃, B₃, hS3⟩ := MM2.Dloc_estimate d n hd hdn h22
  refine ⟨max (max K₁ 0 + max K₂ 0) (max K₃ 0),
    max B₁ (max B₂ (max B₃ ((20:ℝ) ^ 24))), ?_⟩
  intro A B hB₀ hA₁ hA₂
  have hB1 : B₁ ≤ B := le_trans (le_trans (le_max_left _ _) hB₀) le_rfl
  have hB2 : B₂ ≤ B := le_trans (le_trans (le_max_of_le_right (le_max_left _ _)) hB₀) le_rfl
  have hB3 : B₃ ≤ B :=
    le_trans (le_trans (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))) hB₀) le_rfl
  have hBc : (20:ℝ) ^ 24 ≤ B :=
    le_trans (le_trans (le_max_of_le_right (le_max_of_le_right (le_max_right _ _))) hB₀) le_rfl
  have hB1' : (1:ℝ) ≤ B := le_trans (by norm_num : (1:ℝ) ≤ 20 ^ 24) hBc
  have hB20 : (1:ℝ) < B := lt_of_lt_of_le (by norm_num : (1:ℝ) < 20 ^ 24) hBc
  have hA20 : (20:ℝ) ^ 20 ≤ A := by
    have hb : ((20:ℝ) ^ 24) ^ ((5:ℝ)/6) ≤ A :=
      le_trans (Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 20 ^ 24) hBc (by norm_num)) hA₁
    have he : ((20:ℝ) ^ 24) ^ ((5:ℝ)/6) = (20:ℝ) ^ 20 := by
      have h1 : ((20:ℝ) ^ 24) = (20:ℝ) ^ (((24:ℕ)):ℝ) :=
        (Real.rpow_natCast (20:ℝ) 24).symm
      rw [h1, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 20)]
      norm_num
    rwa [he] at hb
  have hA0 : (0:ℝ) < A := lt_of_lt_of_le (by norm_num : (0:ℝ) < 20 ^ 20) hA20
  have hlog : 0 < Real.log A :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1:ℝ) < 20 ^ 20) hA20)
  have hsqrt : Real.sqrt (Real.log A) ≤ A ^ ((1:ℝ)/20) := sqrt_log_le_rpow A hA20
  have hrpow : Real.log A ^ ((1:ℝ)/2) = Real.sqrt (Real.log A) := (Real.sqrt_eq_rpow _).symm
  have hm : 0 ≤ mainTerm d n A B := mainTerm_nonneg d n B hA0.le
  have hs2 : 0 ≤ MM2.Sigma2mix d n A B := Sigma2mix_nonneg d n hB1'
  have hpos : 0 < Real.sqrt (Real.log A) := Real.sqrt_pos.mpr hlog
  have hApos : 0 < A ^ ((1:ℝ)/20) := Real.rpow_pos_of_pos hA0 _
  have hK1m : 0 ≤ max K₁ 0 * mainTerm d n A B := mul_nonneg (le_max_right _ _) hm
  have hK2m : 0 ≤ max K₂ 0 * mainTerm d n A B := mul_nonneg (le_max_right _ _) hm
  have hK3m : 0 ≤ max K₃ 0 * mainTerm d n A B := mul_nonneg (le_max_right _ _) hm
  have hux : 0 ≤ mainTerm d n A B / Real.sqrt (Real.log A) := div_nonneg hm hpos.le
  constructor
  · -- D^mix
    rw [MM2.Dmix_split d n A B hB20]
    have h1 := hS1 A B hB1 hA₁ hA₂
    have h2 := hS2 A B hB2 hA₁ hA₂
    rw [hrpow] at h1
    have h2' : MM2.Sigma2mix d n A B ≤ max K₂ 0 * mainTerm d n A B / Real.sqrt (Real.log A) := by
      have hstep : MM2.Sigma2mix d n A B ≤ max K₂ 0 * mainTerm d n A B / A ^ ((1:ℝ)/20) := by
        have hx : (0:ℝ) ≤ mainTerm d n A B / A ^ ((1:ℝ)/20) := div_nonneg hm hApos.le
        refine le_trans h2 ?_
        rw [show K₂ * mainTerm d n A B / A ^ ((1:ℝ)/20)
              = K₂ * (mainTerm d n A B / A ^ ((1:ℝ)/20)) by ring,
            show max K₂ 0 * mainTerm d n A B / A ^ ((1:ℝ)/20)
              = max K₂ 0 * (mainTerm d n A B / A ^ ((1:ℝ)/20)) by ring]
        exact mul_le_mul_of_nonneg_right (le_max_left K₂ 0) hx
      refine le_trans hstep ?_
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (inv_anti₀ hpos hsqrt) hK2m
    have h1' : |MM2.Sigma1mix d n A B - mainTerm d n A B| ≤
        max K₁ 0 * mainTerm d n A B / Real.sqrt (Real.log A) := by
      refine le_trans h1 ?_
      rw [show K₁ * mainTerm d n A B / Real.sqrt (Real.log A)
            = K₁ * (mainTerm d n A B / Real.sqrt (Real.log A)) by ring,
          show max K₁ 0 * mainTerm d n A B / Real.sqrt (Real.log A)
            = max K₁ 0 * (mainTerm d n A B / Real.sqrt (Real.log A)) by ring]
      exact mul_le_mul_of_nonneg_right (le_max_left K₁ 0) hux
    calc |MM2.Sigma1mix d n A B + MM2.Sigma2mix d n A B - mainTerm d n A B|
        = |(MM2.Sigma1mix d n A B - mainTerm d n A B) + MM2.Sigma2mix d n A B| := by ring_nf
      _ ≤ |MM2.Sigma1mix d n A B - mainTerm d n A B| + |MM2.Sigma2mix d n A B| := abs_add_le _ _
      _ = |MM2.Sigma1mix d n A B - mainTerm d n A B| + MM2.Sigma2mix d n A B := by
            rw [abs_of_nonneg hs2]
      _ ≤ max K₁ 0 * mainTerm d n A B / Real.sqrt (Real.log A) +
            max K₂ 0 * mainTerm d n A B / Real.sqrt (Real.log A) := add_le_add h1' h2'
      _ = (max K₁ 0 + max K₂ 0) * mainTerm d n A B / Real.sqrt (Real.log A) := by ring
      _ ≤ max (max K₁ 0 + max K₂ 0) (max K₃ 0) * mainTerm d n A B / Real.sqrt (Real.log A) := by
            rw [show (max K₁ 0 + max K₂ 0) * mainTerm d n A B / Real.sqrt (Real.log A)
                  = (max K₁ 0 + max K₂ 0) * (mainTerm d n A B / Real.sqrt (Real.log A)) by ring,
                show max (max K₁ 0 + max K₂ 0) (max K₃ 0) * mainTerm d n A B /
                    Real.sqrt (Real.log A)
                  = max (max K₁ 0 + max K₂ 0) (max K₃ 0) *
                    (mainTerm d n A B / Real.sqrt (Real.log A)) by ring]
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) hux
      _ = max (max K₁ 0 + max K₂ 0) (max K₃ 0) * mainTerm d n A B /
            Real.log A ^ ((1:ℝ)/2) := by rw [hrpow]
  · -- D^loc
    have h3 := hS3 A B hB3 hA₁ hA₂
    rw [hrpow] at h3
    have h3' : |Dloc d n A B - mainTerm d n A B| ≤
        max K₃ 0 * mainTerm d n A B / Real.sqrt (Real.log A) := by
      refine le_trans h3 ?_
      rw [show K₃ * mainTerm d n A B / Real.sqrt (Real.log A)
            = K₃ * (mainTerm d n A B / Real.sqrt (Real.log A)) by ring,
          show max K₃ 0 * mainTerm d n A B / Real.sqrt (Real.log A)
            = max K₃ 0 * (mainTerm d n A B / Real.sqrt (Real.log A)) by ring]
      exact mul_le_mul_of_nonneg_right (le_max_left K₃ 0) hux
    calc |Dloc d n A B - mainTerm d n A B|
        ≤ max K₃ 0 * mainTerm d n A B / Real.sqrt (Real.log A) := h3'
      _ ≤ max (max K₁ 0 + max K₂ 0) (max K₃ 0) * mainTerm d n A B /
            Real.sqrt (Real.log A) := by
          rw [show max K₃ 0 * mainTerm d n A B / Real.sqrt (Real.log A)
                = max K₃ 0 * (mainTerm d n A B / Real.sqrt (Real.log A)) by ring,
              show max (max K₁ 0 + max K₂ 0) (max K₃ 0) * mainTerm d n A B /
                  Real.sqrt (Real.log A)
                = max (max K₁ 0 + max K₂ 0) (max K₃ 0) *
                  (mainTerm d n A B / Real.sqrt (Real.log A)) by ring]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) hux
      _ = max (max K₁ 0 + max K₂ 0) (max K₃ 0) * mainTerm d n A B /
            Real.log A ^ ((1:ℝ)/2) := by rw [hrpow]

end Work.HP

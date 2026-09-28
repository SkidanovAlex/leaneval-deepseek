import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDCommon
import Submission.Work.HP.MDAssembly
import Submission.Work.HP.MDSplit
import Submission.Work.HP.MDBasic.nonneg_basic
import Submission.Work.HP.MDEstimates.Sigma1_estimate
import Submission.Work.HP.MDEstimates.Sigma2_bound
import Submission.Work.HP.MDEstimates.Sigma1_44
import Submission.Work.HP.MDEstimates.Sigma2_44

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/HP/DESIGN.md (the lead's design for Browning–Le Boudec–Sawin, with its two replacements: the ρLoc existence sandwich and the Planes44 lemma) and FEASIBILITY.md. Shared definitions: Submission/Work/HP/Defs.lean (do NOT edit). No Deligne / Lang–Weil / Poonen–Voloch needed. Siblings run in parallel.

          │                    └───────────────────────────────────────┼─ N08 moment_D ─┐
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
  sorry
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
-/

namespace Work.HP

open Filter

/-- N08. Estimates D and D44: the second moment of `N_V(B)` with the diagonal removed. -/
theorem moment_D (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (h22 : (d, n) ≠ (2, 2))
    (h33 : (d, n) ≠ (3, 3)) :
    ∃ K B₀ : ℝ, ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      |Dglob d n A B - mainTerm d n A B| ≤ K * mainTerm d n A B / Real.log A ^ ((1 : ℝ) / 2) := by
  have hsplit := Dglob_eq_Sigma1_add_Sigma2 d n
  have hnn : ∀ A B : ℝ, 0 ≤ A → 0 ≤ mainTerm d n A B :=
    fun A B hA => (MDBasic.nonneg_basic d n A B hA).2.2.2.2.2
  have hs2 : ∀ A B : ℝ, 0 ≤ A → 0 ≤ Sigma2 d n A B :=
    fun A B hA => (MDBasic.nonneg_basic d n A B hA).2.2.2.2.1
  by_cases h44 : (d, n) = (4, 4)
  · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h44
    exact moment_D_of_two_exponents 4 4 (1 / 4) (1 / 32) (by norm_num) (by norm_num) hsplit hnn hs2
      MDEstimates.Sigma1_44 MDEstimates.Sigma2_44
  · exact moment_D_of_two_exponents d n (1 / 4) (1 / 3) (by norm_num) (by norm_num) hsplit hnn hs2
      (MDEstimates.Sigma1_estimate d n hd hdn h22 h33 h44)
      (MDEstimates.Sigma2_bound d n hd hdn h22 h33 h44)

end Work.HP

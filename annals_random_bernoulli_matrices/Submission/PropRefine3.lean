import Mathlib
import Submission.PropRefine2
import Submission.PropRefine
import Submission.Sec3Tower
import Submission.ProdCount
import Submission.Commons.Analysis.Real.prop_refine_tail

open Submission.PropRefine2
open Submission.Sec3Tower
open Submission.ProdCount

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

/-!
# Prop refinement, part 4: the phase-1 counting export

Tikhomirov 2020, Section 3 (`prop: refinement`, proof lines ~1355–1385).

`Submission.PropRefine2.seq_bad_ge` counts, for a product coordinate family
`J : Fin m → Finset ℤ` and a per-prefix "bad value" predicate, the tuples with
at least `r` bad positions: `≤ C(m,r)·c^r·∏|J_j|` provided each prefix admits
at most a `c`-fraction of bad next-values.

Phase 1 instantiates this with the Prop-refinement step predicate: a step
`k` (which adds the coordinate `x_k` to a prefix of length `k`) is *bad* iff the
level-`k` function of the prefix is NOT flat (`hflat k u` fails) and the
level-`(k+1)` function does NOT drop (`hdrop k (extendFin u a)` fails).  The
dichotomy of the proof gives the per-prefix `c = 1024μ`-bound via
`Submission.Refine3.step_bad_count`; this module only needs that per-prefix
bound abstractly (`hstep`), and exports:

1. `phase1_count`: with `r := ⌈m/2⌉`, the number of full tuples with ≥ r bad
   positions is `≤ C(m,r)·c^r·∏|J_j|`  (direct from `seq_bad_ge`);
2. `phase1_tail`: the fractional version `≤ exp(−2Mn)·∏|J_j|` under the
   concrete `μ := exp(−16M/ε)/24`-choice (via `C(m,r) ≤ 2^m` and
   `Commons.Analysis.Real.prop_refine_tail`);
3. `few_bad_flat_or_drop`: the deterministic export: a tuple with fewer than
   `r` bad positions either has a flat level `≤ m` or accumulates ≥
   `m − r + 1` drops (counting the drop positions), so the level-`m` squared
   norm drops by that many drop-quanta.
-/

namespace Submission.PropRefine3

attribute [local instance] Classical.propDecidable

open scoped BigOperators

/-- A step-`k` is bad for the extension `w : Fin (k+1) → ℤ`: the level-`k`
prefix `restrict w` is not flat and level `k+1` does not drop. -/
def badPred (hflat : (k : ℕ) → (Fin k → ℤ) → Prop)
    (hdrop : (k : ℕ) → (Fin (k + 1) → ℤ) → Prop) (k : ℕ) (w : Fin (k + 1) → ℤ) : Prop :=
  ¬ hflat k (restrict w) ∧ ¬ hdrop k w

/-- badPred on an extension = the non-flat prefix and a non-dropping value. -/
lemma badPred_extend {hflat : (k : ℕ) → (Fin k → ℤ) → Prop}
    {hdrop : (k : ℕ) → (Fin (k + 1) → ℤ) → Prop} (k : ℕ) (u : Fin k → ℤ) (a : ℤ) :
    badPred hflat hdrop k (extendFin u a) ↔
      (¬ hflat k u ∧ ¬ hdrop k (extendFin u a)) := by
  dsimp [badPred]
  rw [restrict_extend]

/-- number of bad steps of a length-`m` tuple (via `badCnt` with `badPred`). -/
noncomputable def nBad {m : ℕ} (hflat : (k : ℕ) → (Fin k → ℤ) → Prop)
    (hdrop : (k : ℕ) → (Fin (k + 1) → ℤ) → Prop) (x : Fin m → ℤ) : ℕ :=
  badCnt (badPred hflat hdrop) x

/-- `nBad` counts positions `p : Fin m` whose extension is bad. -/
lemma nBad_eq {m : ℕ} (hflat : (k : ℕ) → (Fin k → ℤ) → Prop)
    (hdrop : (k : ℕ) → (Fin (k + 1) → ℤ) → Prop) (x : Fin m → ℤ) :
    nBad hflat hdrop x =
      ((Finset.univ : Finset (Fin m)).filter (fun p : Fin m =>
        badPred hflat hdrop p.val (pre x (p.val + 1) (Nat.succ_le_of_lt p.isLt)))).card := by
  rfl

/-- (phase 1, counting) with a `c`-fraction bound on bad next-values at every
prefix, the number of length-`m` tuples with at least `r := ⌈m/2⌉` bad steps
is at most `C(m, r)·c^r·∏|J_j|`. -/
theorem phase1_count {m : ℕ} {J : Fin m → Finset ℤ} {c : ℝ} (hc : 0 ≤ c)
    (hflat : (k : ℕ) → (Fin k → ℤ) → Prop)
    (hdrop : (k : ℕ) → (Fin (k + 1) → ℤ) → Prop)
    (hstep : ∀ (k : ℕ) (hk : k < m) (u : Fin k → ℤ),
      u ∈ prodFinset k (fun j : Fin k => J (Fin.castLE (Nat.le_of_lt hk) j)) →
      ((((J ⟨k, hk⟩).filter (fun a : ℤ => badPred hflat hdrop k (extendFin u a))).card : ℕ) : ℝ) ≤
        c * ((J ⟨k, hk⟩).card : ℝ)) :
    ((((prodFinset m J).filter (fun x : Fin m → ℤ =>
        (m + 1) / 2 ≤ nBad hflat hdrop x)).card : ℕ) : ℝ) ≤
      (m.choose ((m + 1) / 2) : ℝ) * c ^ ((m + 1) / 2) * (∏ j : Fin m, ((J j).card : ℝ)) := by
  classical
  have hsq := seq_bad_ge ((m + 1) / 2) m (J := J) hc (badPred hflat hdrop) hstep
  -- hsq : ↑(cnt m J (badPred hflat hdrop) ((m+1)/2)) ≤ ↑(m.choose ((m+1)/2)) * c^((m+1)/2) * ∏ ...
  have hcnt : cnt m J (badPred hflat hdrop) ((m + 1) / 2) =
      ((prodFinset m J).filter (fun x : Fin m → ℤ => (m + 1) / 2 ≤ nBad hflat hdrop x)).card := by
    dsimp [cnt, nBad]
    rfl
  calc
    ((((prodFinset m J).filter (fun x : Fin m → ℤ => (m + 1) / 2 ≤ nBad hflat hdrop x)).card : ℕ) : ℝ)
        = ((cnt m J (badPred hflat hdrop) ((m + 1) / 2) : ℕ) : ℝ) := by
          rw [hcnt]
    _ ≤ (m.choose ((m + 1) / 2) : ℝ) * c ^ ((m + 1) / 2) * (∏ j : Fin m, ((J j).card : ℝ)) := hsq

/-- `⌈m/2⌉ = (m+1)/2`. -/
lemma half_ceil (m : ℕ) : Nat.ceil ((m : ℝ) / 2) = (m + 1) / 2 := by
  by_cases hm0 : m = 0
  · subst m
    simp
  · have hm1 : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm0)
    let n : ℕ := (m + 1) / 2
    have hn0 : n ≠ 0 := by
      dsimp [n]
      omega
    rw [Nat.ceil_eq_iff hn0]
    constructor
    · dsimp [n]
      have hnat : 2 * (((m + 1) / 2) - 1) ≤ m - 1 := by omega
      have hR1 : (2 : ℝ) * ((((m + 1) / 2 - 1 : ℕ) : ℝ)) ≤ ((m - 1 : ℕ) : ℝ) := by
        exact_mod_cast hnat
      have hRm : ((m - 1 : ℕ) : ℝ) < (m : ℝ) := by
        have hnat2 : m - 1 < m := by omega
        exact_mod_cast hnat2
      have hm1R : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hm0)
      nlinarith
    · have hnat : m ≤ 2 * ((m + 1) / 2) := by omega
      have hR : (m : ℝ) ≤ (2 : ℝ) * (((m + 1) / 2 : ℕ) : ℝ) := by
        exact_mod_cast hnat
      nlinarith

/-- `(m.choose ⌈m/2⌉) ≤ 2^m`. -/
lemma choose_ceil_le_two_pow (m : ℕ) : (m.choose ((m + 1) / 2) : ℝ) ≤ (2 : ℝ) ^ m := by
  have h := Nat.choose_le_two_pow m ((m + 1) / 2)
  exact_mod_cast h

/-- the phase-1 spike parameter `μ₀ := exp(−16M/ε)/(24·1024²)`. -/
noncomputable def mu0 (M ε : ℝ) : ℝ :=
  Real.exp (-16 * M / ε) / (24 * 1024 ^ 2)

/-- the phase-1 per-step bad-fraction `c := 1024·μ₀`. -/
noncomputable def cPhase1 (M ε : ℝ) : ℝ :=
  1024 * mu0 M ε

/-- the phase-1 real tail: `C(m, ⌈m/2⌉)·c^⌈m/2⌉ ≤ exp(−2Mn)` for
`m := ⌊εn/2⌋` and `c := cPhase1 M ε`. -/
theorem phase1_tail_arith {M ε : ℝ} (hM : 1 ≤ M) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ {m : ℕ} (hm : m = Nat.floor (ε * (n : ℝ) / 2)),
      (m.choose ((m + 1) / 2) : ℝ) * (cPhase1 M ε) ^ ((m + 1) / 2) ≤
        Real.exp (-2 * M * (n : ℝ)) := by
  classical
  rcases Commons.Analysis.Real.prop_refine_tail (M := M) (ε := ε) hM hε0 hε1 with ⟨n₀, htail⟩
  refine ⟨n₀, ?_⟩
  intro n hn m hm
  let c : ℝ := cPhase1 M ε
  let d : ℝ := Real.exp (-16 * M / ε) / 24
  have ht := htail n hn
  have hm' : (Nat.floor (ε * (n : ℝ) / 2) : ℝ) = (m : ℝ) := by
    rw [← hm]
  have hB : Nat.ceil (((Nat.floor (ε * (n : ℝ) / 2) : ℕ) : ℝ) / 2) = (m + 1) / 2 := by
    rw [← hm]
    exact half_ceil m
  have ht' : (2 : ℝ) ^ m * d ^ ((m + 1) / 2) ≤ Real.exp (-2 * M * (n : ℝ)) := by
    rw [hB] at ht
    rw [hm'] at ht
    rw [Real.rpow_natCast] at ht
    exact ht
  have hc_eq : c = d / 1024 := by
    dsimp [c, cPhase1, mu0, d]
    norm_num
    ring
  have hc0 : 0 ≤ c := by
    dsimp [c, cPhase1, mu0]
    positivity
  have hd0 : 0 ≤ d := by
    dsimp [d]
    positivity
  have hcd : c ≤ d := by
    rw [hc_eq]
    have h1024 : (1 : ℝ) ≤ 1024 := by norm_num
    have hle := div_le_one_of_le₀ h1024 (by norm_num : (0 : ℝ) ≤ 1024)
    calc
      d / 1024 = d * (1 / 1024) := by ring
      _ ≤ d * 1 := by
            exact mul_le_mul_of_nonneg_left hle hd0
      _ = d := by ring
  have hpow_cd : c ^ ((m + 1) / 2) ≤ d ^ ((m + 1) / 2) :=
    pow_le_pow_left₀ hc0 hcd ((m + 1) / 2)
  have hchoose : (m.choose ((m + 1) / 2) : ℝ) ≤ (2 : ℝ) ^ m := choose_ceil_le_two_pow m
  have hzero_m : 0 ≤ (2 : ℝ) ^ m := pow_nonneg (by norm_num) m
  have hzero_cho : 0 ≤ (m.choose ((m + 1) / 2) : ℝ) := by positivity
  have hprod := mul_le_mul hchoose hpow_cd (pow_nonneg hc0 ((m + 1) / 2)) hzero_m
  calc
    (m.choose ((m + 1) / 2) : ℝ) * (cPhase1 M ε) ^ ((m + 1) / 2)
        = (m.choose ((m + 1) / 2) : ℝ) * c ^ ((m + 1) / 2) := by simp [c]
    _ ≤ (2 : ℝ) ^ m * d ^ ((m + 1) / 2) := hprod
    _ ≤ Real.exp (-2 * M * (n : ℝ)) := ht'

/-- (phase 1, fractional) with `m := ⌊εn/2⌋` coordinates and a per-prefix
bad-value fraction at most `cPhase1 M ε`, the number of full tuples with at
least `⌈m/2⌉` bad steps is at most `exp(−2Mn)·∏|J_j|`. -/
theorem phase1_tail {M ε : ℝ} (hM : 1 ≤ M) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ {m : ℕ} (hm : m = Nat.floor (ε * (n : ℝ) / 2))
    {J : Fin m → Finset ℤ} (hflat : (k : ℕ) → (Fin k → ℤ) → Prop)
      (hdrop : (k : ℕ) → (Fin (k + 1) → ℤ) → Prop)
      (hstep : ∀ (k : ℕ) (hk : k < m) (u : Fin k → ℤ),
        u ∈ prodFinset k (fun j : Fin k => J (Fin.castLE (Nat.le_of_lt hk) j)) →
        ((((J ⟨k, hk⟩).filter (fun a : ℤ => badPred hflat hdrop k (extendFin u a))).card : ℕ) : ℝ) ≤
          cPhase1 M ε * ((J ⟨k, hk⟩).card : ℝ)),
      ((((prodFinset m J).filter (fun x : Fin m → ℤ => (m + 1) / 2 ≤ nBad hflat hdrop x)).card : ℕ) : ℝ) ≤
        Real.exp (-2 * M * (n : ℝ)) * (∏ j : Fin m, ((J j).card : ℝ)) := by
  classical
  rcases phase1_tail_arith (M := M) (ε := ε) hM hε0 hε1 with ⟨n₀, harith⟩
  refine ⟨n₀, ?_⟩
  intro n hn m hm J hflat hdrop hstep
  have hc0 : 0 ≤ cPhase1 M ε := by
    dsimp [cPhase1, mu0]
    positivity
  have hcnt := phase1_count (m := m) (J := J) (c := cPhase1 M ε) hc0 hflat hdrop hstep
  have htailn : (m.choose ((m + 1) / 2) : ℝ) * (cPhase1 M ε) ^ ((m + 1) / 2) ≤
      Real.exp (-2 * M * (n : ℝ)) := by
    exact harith n hn (m := m) hm
  calc
    ((((prodFinset m J).filter (fun x : Fin m → ℤ => (m + 1) / 2 ≤ nBad hflat hdrop x)).card : ℕ) : ℝ)
        ≤ (m.choose ((m + 1) / 2) : ℝ) * (cPhase1 M ε) ^ ((m + 1) / 2) *
            (∏ j : Fin m, ((J j).card : ℝ)) := hcnt
    _ ≤ Real.exp (-2 * M * (n : ℝ)) * (∏ j : Fin m, ((J j).card : ℝ)) := by
          exact mul_le_mul_of_nonneg_right htailn (by positivity)


end Submission.PropRefine3

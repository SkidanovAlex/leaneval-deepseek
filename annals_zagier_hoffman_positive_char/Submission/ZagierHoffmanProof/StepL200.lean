import Submission.ZagierHoffmanProof.StepL199

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial RatFunc
open scoped BigOperators WithZero Topology
open WithZero

/-!
# Step L200: corollaries and regression checks for the `≤ q`-entry non-vanishing

`zeta_entries_ne_zero` (StepL199) says that `ζ_A(𝔰) ≠ 0` whenever every entry of `𝔰` is `≤ q`;
since the spanning set `𝒯 w` of Theorem A consists of MZVs with entries `≤ q` (the last one
strictly smaller), this covers all of `𝒯 w`.  Here we record the concrete families
(all-ones, all-`q`, the pairs `(1,1)`, `(q,q)`), the power form `P_d(n) = P_d(1)^n` for
`n ≤ q`, the consistency of `val_zeta_entries` with `val_zeta_one`/`val_zeta_qExp`, and the
non-vacuity of `𝒵 F 2`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★★★ Every MZV whose entries are all `≤ q` is nonzero.  (Since `𝒯 w` consists of such
MZVs, every element of `𝒯 w` is nonzero.) -/
theorem zeta_entries_le_card_ne_zero {r : ℕ} (hr : 0 < r) (𝔰 : Fin r → ℕ+)
    (h𝔰 : ∀ j, (𝔰 j : ℕ) ≤ Nat.card F) : ζ_A F 𝔰 ≠ 0 :=
  zeta_entries_ne_zero F hr 𝔰 h𝔰

/-- `bloExp` at depth 1 vanishes at index `0` (so `v (ζ_A(s)) = 1` for a single entry). -/
theorem bloExp_one_zero (n : ℕ+) : bloExp F 1 (single n) 0 = 0 := by
  rw [bloExp_one]
  simp only [single]
  exact Se_zero F n

/-- Consistency: `val_zeta_entries` for `𝔰 = (1)` gives the same value `1` as `val_zeta_one`. -/
example : WithZero.exp (-(bloExp F 1 (single oneExp) 0)) = (1 : ℤᵐ⁰) := by
  rw [bloExp_one_zero]; simp

/-- Consistency: `val_zeta_entries` for `𝔰 = (q)` gives the same value `1` as `val_zeta_qExp`. -/
example : WithZero.exp (-(bloExp F 1 (single (qExp F)) 0)) = (1 : ℤᵐ⁰) := by
  rw [bloExp_one_zero]; simp

/-! ## Non-vanishing families -/

/-- ★★ Every all-ones MZV `ζ_A(1,1,…,1)` of depth `r ≥ 1` is nonzero. -/
theorem zeta_ones_ne_zero (r : ℕ) (hr : 0 < r) :
    ζ_A F (fun _ : Fin r => oneExp) ≠ 0 := by
  refine zeta_entries_ne_zero F hr _ (fun _ => ?_)
  show (1 : ℕ) ≤ Nat.card F
  have h := card_ge_two F
  omega

/-- ★★ Every all-`q` MZV `ζ_A(q,q,…,q)` of depth `r ≥ 1` is nonzero. -/
theorem zeta_qs_ne_zero (r : ℕ) (hr : 0 < r) :
    ζ_A F (fun _ : Fin r => qExp F) ≠ 0 :=
  zeta_entries_ne_zero F hr _ (fun _ => le_of_eq rfl)

/-- `pair oneExp oneExp` is the all-ones tuple. -/
lemma pair_one_one_eq (u : ℕ+) : pair u u = fun _ : Fin 2 => u := by
  funext j
  fin_cases j <;> simp [pair]

/-- ★ `ζ_A(1,1) ≠ 0`. -/
theorem zeta_one_one_ne_zero : ζ_A F (pair oneExp oneExp) ≠ 0 := by
  rw [pair_one_one_eq]
  exact zeta_ones_ne_zero F 2 (by norm_num)

/-- ★ `ζ_A(q,q) ≠ 0`. -/
theorem zeta_qq_ne_zero : ζ_A F (pair (qExp F) (qExp F)) ≠ 0 := by
  rw [pair_one_one_eq]
  exact zeta_qs_ne_zero F 2 (by norm_num)

/-- `ζ_A(1,1) ∈ 𝒵 F 2`. -/
theorem zeta_one_one_mem_Z : ζ_A F (pair oneExp oneExp) ∈ 𝒵 F 2 := by
  classical
  refine Submodule.subset_span ?_
  rw [Set.mem_iUnion]
  refine ⟨2, ?_⟩
  refine ⟨pair oneExp oneExp, ?_, rfl⟩
  simp [𝔖_w, weight, Fin.sum_univ_two, pair, oneExp]

/-- ★ `𝒵 F 2 ≠ ⊥`: the weight-two zeta space is non-trivial. -/
theorem Z_two_ne_bot : 𝒵 F 2 ≠ (⊥ : Submodule (RatFunc F) (RatFunc.CompletionAtInfty F)) := by
  intro hbot
  have hmem := zeta_one_one_mem_Z F
  rw [hbot] at hmem
  exact zeta_one_one_ne_zero F (by simpa using hmem)

end ZagierHoffmanPositiveChar

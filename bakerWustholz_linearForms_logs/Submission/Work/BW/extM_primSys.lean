import Mathlib
import Submission.Work.BW.DefsMP

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW multiplicity_prop partial-degeneracy reduction; MULT_PROP_CHECK.md below). Your node is `extM_primSys`. Definitions: Submission.Work.BW.DefsMP (liftIdx, extM; imports DefsB). Import siblings; do not reprove them.

# `multiplicity_prop`: the owner's two concerns (phase 7, 2026-09-28)

**Rules followed.** Everything was read-only. The only Lean run was a scratch
`lake env lean` on 3.144 under `MemoryMax=12G`.

**Sources.** The live statement in `Submission/Work/BW/multiplicity_prop.lean` (unchanged from
bw2), and H21's probes from 0928-0805 and 0928-0905.

**New files.** `mult_prop/`: `DefsMP.lean` plus 5 statements. All elaborate against
`Submission.Work.BW.DefsMult`: 5 `sorry` warnings, no errors, no name clashes.

## (1) Do (E0)–(E3) exclude every forbidden output? Yes. There is no gap and no statement change.

**(E0)–(E3) are hypotheses of `multiplicity_prop`.** Each forbidden output of
`zero_estimate_stepwise` yields an inequality that directly contradicts one of them.

**How to read `zero_estimate_stepwise`'s output.**
* **The subgroup.** It returns `G' = G_a^ε × ker 𝒵`, with `𝒵` spanned by the rows of `M`, of rank
  `ρ` and codimension `k = [ε = false] + ρ`, together with a step `m ≤ k − 1`.
* **The inequality.** For every `J` with `Δ_J ≠ 0`,

      C(T_m + ℓ, ℓ) · card · (N+1−k)! · |Δ_J| · D₀^ε · ∏_{i∉J} D_i  ≤  (N+1)! · ∏ D.

* **Shifting the step.** The sequences are monotone, so `(Sq m, Tq m)` may be replaced by
  `(Sq(k−1), Tq(k−1))`.
* **Rounding.** `D_i = ⌊𝒟_i⌋ ≤ 𝒟_i`.
* **Minors.** `|Δ_J| ≥ 1` for the chosen `J`.
* **`W` and `ℓ`.** `W = span(∂₀, c_m)` has dimension `r` because `c` is ℚ-independent. Hence
  `ℓ ∈ {k−1, k}`, with `ℓ = k−1` exactly when `B ∈ ℚ𝒵` (H21's `ellW_dichotomy`).

| output of the zero estimate | ℓ | what the inequality becomes | contradicts |
|---|---|---|---|
| `ε = true, ρ = 0` (`G' = G`) | — | excluded by `zero_estimate_stepwise` itself (`¬(ε ∧ ρ = 0)`) | — |
| `ε = false, ρ = 0` (`0 × G_m^r`, `k = 1`) | 1 = k | `(Tq₀+1)(Sq₀+1) ≤ (r+1)·D₀` | **E1**, `m = 0`, `e = e₀` |
| any transversal case (`ℓ = k ≤ r`) | k | `C(T+k,k)(S+1) ≤ (r+1)!/(r+1−k)! · 𝒟^e`, with `e = 1_{ε=false}e₀ + 1_J` and `\|e\| = k` | **E1**, `m = k−1 < r` |
| transversal with collisions (only `ε = true`, `ρ = 1`, card ≥ 1) | 1 | `Tq₀ + 1 ≤ (r+1)·D_i/\|χ_i\|` | **E0** |
| `G_a × 1` (`ε = true, ρ = r`, `M` unimodular, `\|Δ\| = 1`, no collisions since `r ≥ 2` and `ℓ` is ℚ-independent) | r−1 = k−1 | `C(T+r−1, r−1)(S+1)·D₀ ≤ (r+1)!·D₀∏_{i≥1}D_i` | **E3** |
| `0 × 1` (`ε = false, ρ = r`, `k = r+1`) | r = k−1 | `C(T+r, r)(S+1) ≤ (r+1)!∏D` | **E2** |
| `G_a × H'` or `0 × H'`, `1 ≤ ρ ≤ r−1`, `B ∈ ℚ𝒵` | k−1 | the two cases of the conclusion (collisions excluded by `hΛ` with integral `B`) | — (legitimate output) |

**So `ρ = r` and `ρ = 0` are always contradictions,** and a countermodel of the kind H21 worried
about (say `r = 2`, `ρ = 2`) cannot satisfy E2 and E3.
* **Degenerate cases.** The fully degenerate case (`𝒟_i < 1` for all `i ≥ 1`) is H21's proved
  `not_fully_degenerate`. The partially degenerate case goes through the quotient in (2), where
  the same table applies with `N' < r`.
* **In the quotient**, the quotient's `G_a × 1` and `0 × 1` pull back to legitimate outputs with
  `ρ = N' < r` when `B` is supported off `Z`; when it is not, they are transversal and E1 excludes
  them. Its conditions are implied by E0–E1, since `(N'+1)!/(N'−m)! ≤ (r+1)!/(r−m)!`.
* **`group_reduction` supplies E0–E3 unchanged**, through `split_conditions` (numerics in bw2).

**The "only used in Philippon's proof to forestall outputs" worry is a misreading.** Nothing needs
to be derived from the zero estimate beyond the inequality above. Each exclusion is
"inequality + hypothesis ⇒ `False`". H21's planned case splits (`cardMod`, `ellW_dichotomy`) are
exactly the needed pieces.

## (2) The renaming/completion lemma for partial degeneracy

**Setup.**
* `Z = {i : 𝒟(i.succ) < 1}`. Since the degree is at most `𝒟 < 1`, `P` has degree 0 in those
  variables.
* `σ : Fin N' → Fin r` is the increasing enumeration of `Zᶜ`, e.g.
  `(univ.filter (fun i => 1 ≤ 𝒟 i.succ)).orderEmbOfFin rfl`.
* `N' = 0` is H21's `not_fully_degenerate`.

**Definitions** (`DefsMP.lean`):
* `liftIdx σ : Fin (N'+1) → Fin (r+1)`, with `0 ↦ 0` and `j.succ ↦ (σ j).succ`;
* `extM σ M'`, the extension of the rows of `M'` by zero (`Function.extend`).

**Nodes:**

| node | statement | size (k lines) |
|---|---|---|
| `zeroDeg_reduce` | `P = rename (liftIdx σ) P'`, with the same partial degrees and `eval (ptTheta θ s) (applyW w t P) = eval (ptTheta (θ∘σ) s) (applyW (w · ∘ liftIdx σ) t P')` | 0.6–1.2 |
| `extM_primSys` | `PrimSys M' → PrimSys (extM σ M')` | 0.4–0.8 |
| `extM_ellW` | `ellW w ε (extM σ M') = ellW (w · ∘ liftIdx σ) ε M'` (`Lie G'` is a preimage, and `ℓ` is unchanged) | 0.5–1 |
| `extM_cardMod` | `cardMod ε (extM σ M') θ S = cardMod ε M' (θ∘σ) S` | 0.2–0.4 |
| `extM_minorJ` | minors on `J'.map σ` agree; a nonzero minor uses only columns in `range σ` | 0.4–0.8 |

**How it plugs in** (inside `multiplicity_prop`, after `not_fully_degenerate` disposes of
`N' = 0`):
1. Get `P'` from `zeroDeg_reduce` (`P' ≠ 0` since `rename` is injective). Put `D' = ⌊𝒟 ∘ liftIdx σ⌋`,
   which is `≥ 1` by the choice of `Z`, and `ℓ' = ℓ ∘ σ`. `ze_hvan_of_hvan` then transfers to
   `P'`.
2. Apply `zero_estimate_stepwise` with `N = N'` and get `ε, ρ, M', m`. Set `M = extM σ M'`, which
   is primitive by `extM_primSys`; `ℓ`, `card` and the minors transfer by the other three lemmas.
   The factorials use `(N'+1).descFactorial k ≤ (r+1).descFactorial k`, and the products over
   `J'.map σ` stay within `Zᶜ`, where `D'_i ≤ 𝒟_i`.
3. Run the exclusion table in (1) for `r` (the conditions transfer as noted there). The `J` that
   maximises `|Δ_J|∏_J a` has a nonzero minor, so it lies in `range σ` (`extM_minorJ`, second
   part). That is the `J` `prim_basis_from_minors` needs.
-/

namespace Work.BW

/-- `extM` evaluated on a column in the range of `σ` recovers the original entry. -/
lemma extM_apply_range {r N' ρ : ℕ} (σ : Fin N' → Fin r) (hσ : Function.Injective σ)
    (M' : Fin ρ → Fin N' → ℤ) (j : Fin ρ) (k : Fin N') :
    extM σ M' j (σ k) = M' j k := by
  simp only [extM]
  exact hσ.extend_apply (M' j) 0 k

/-- `extM` vanishes on the columns that are not in the range of `σ`. -/
lemma extM_apply_notMem {r N' ρ : ℕ} (σ : Fin N' → Fin r)
    (M' : Fin ρ → Fin N' → ℤ) (j : Fin ρ) {i : Fin r} (hi : i ∉ Set.range σ) :
    extM σ M' j i = 0 := by
  simp only [extM]
  exact Function.extend_apply' _ _ _ hi

/-- Every element of the `ℤ`-span of the rows of `extM σ M'` vanishes off `Set.range σ`. -/
lemma extM_span_apply_notMem {r N' ρ : ℕ} (σ : Fin N' → Fin r)
    (M' : Fin ρ → Fin N' → ℤ) :
    ∀ z ∈ Submodule.span ℤ (Set.range (extM σ M')), ∀ i, i ∉ Set.range σ → z i = 0 := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
      intro i hi
      obtain ⟨j, rfl⟩ := hz
      exact extM_apply_notMem σ M' j hi
  | zero => intro i hi; rfl
  | add z w hz hw ihz ihw => intro i hi; simp [ihz i hi, ihw i hi]
  | smul a z hz ih => intro i hi; simp [ih i hi]

/-- Partial degeneracy, step 2a. Extending a primitive system by zero columns keeps it primitive:
independence is clear, and if `k x ∈ span_ℤ` then the zero columns force `x = 0` off `range σ`,
so saturation of `M'` applies to `x ∘ σ`. Size 0.4–0.8k. -/
theorem extM_primSys {r N' ρ : ℕ} (σ : Fin N' → Fin r) (hσ : Function.Injective σ)
    (M' : Fin ρ → Fin N' → ℤ) (hM : PrimSys M') : PrimSys (extM σ M') := by
  obtain ⟨hindep, hsat⟩ := hM
  constructor
  · -- `ℚ`-independence: restrict the relation to the columns `σ k`.
    rw [Fintype.linearIndependent_iff] at hindep ⊢
    intro g hg
    refine hindep g ?_
    funext k
    have h := congrFun hg (σ k)
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at h
    simpa [extM_apply_range σ hσ M'] using h
  · -- Saturation
    intro x m hm hx
    -- the extension vanishes off `range σ`, hence so does everything in its span
    have hxoff : ∀ i, i ∉ Set.range σ → x i = 0 := by
      intro i hi
      have h1 : m * x i = 0 := by
        have := extM_span_apply_notMem σ M' (m • x) hx i hi
        simpa using this
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hm
      · exact h
    rw [Submodule.mem_span_range_iff_exists_fun ℤ] at hx
    obtain ⟨c, hc⟩ := hx
    -- restrict the relation `m • x = ∑ c j • extM σ M' j` to `range σ`
    have hy : (m • (fun k => x (σ k))) ∈ Submodule.span ℤ (Set.range M') := by
      rw [Submodule.mem_span_range_iff_exists_fun ℤ]
      refine ⟨c, ?_⟩
      funext k
      have h := congrFun hc (σ k)
      simp only [Finset.sum_apply, Pi.smul_apply] at h
      simpa [extM_apply_range σ hσ M'] using h
    -- saturation of `M'`
    obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hsat _ m hm hy)
    rw [Submodule.mem_span_range_iff_exists_fun ℤ]
    refine ⟨c', ?_⟩
    funext i
    by_cases hi : i ∈ Set.range σ
    · obtain ⟨k, rfl⟩ := hi
      have h := congrFun hc' k
      simp only [Finset.sum_apply, Pi.smul_apply] at h ⊢
      simpa [extM_apply_range σ hσ M'] using h
    · have h1 : x i = 0 := hxoff i hi
      have h2 : (∑ j, c' j • extM σ M' j) i = 0 := by
        simp only [Finset.sum_apply, Pi.smul_apply]
        refine Finset.sum_eq_zero (fun j _ => ?_)
        simp [extM_apply_notMem σ M' j hi]
      rw [h2, h1]

end Work.BW
